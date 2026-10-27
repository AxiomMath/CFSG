module

public import CFSG.RankThree.PartOne.KF1514B.Torus4
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailFlagTransitivity
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailUnipotentInvariant
public import CFSG.RankThree.PartOne.KF1514B.Siegel

set_option linter.unusedSectionVars false

public section

namespace CFSG.RankThree.PartOne.KF1514B

open Matrix CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal QuadraticMap Module

section Vectors

variable {K : Type} [Field K]

noncomputable abbrev e2v (K : Type) [Field K] : Vt K := hypVec K (Fin 2 → K) (Sum.inl 2)

noncomputable abbrev f0v (K : Type) [Field K] : Vt K := hypVec K (Fin 2 → K) (Sum.inr 0)

theorem Xmat_e2v : Xmat (e2v K) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Xmat, hypVec]

theorem Xmat_e1v : Xmat (e1 K) = !![0, 1; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Xmat, hypVec]

theorem Xmat_f0v : Xmat (f0v K) = !![0, 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Xmat, hypVec]

theorem trFun_e2 (P S : Matrix (Fin 2) (Fin 2) K) : trFun P 1 S (e2v K) = e2v K := by
  refine Prod.ext (funext fun c => ?_) ?_
  · rcases c with i | i <;> fin_cases i <;> simp [Xmat_e2v] <;> simp [hypVec]
  · simp [hypVec]

theorem trFun_e1 (P S : Matrix (Fin 2) (Fin 2) K) :
    trFun P 1 S (e1 K) = P 0 0 • e1 K + P 1 0 • f0v K := by
  refine Prod.ext (funext fun c => ?_) ?_
  · rcases c with i | i <;> fin_cases i <;> simp [Xmat_e1v, Matrix.mul_apply, Fin.sum_univ_two] <;> simp [hypVec]
  · simp [hypVec]

theorem trFun_f0 (P S : Matrix (Fin 2) (Fin 2) K) :
    trFun P 1 S (f0v K) = P 0 1 • e1 K + P 1 1 • f0v K := by
  refine Prod.ext (funext fun c => ?_) ?_
  · rcases c with i | i <;> fin_cases i <;> simp [Xmat_f0v, Matrix.mul_apply, Fin.sum_univ_two] <;> simp [hypVec]
  · simp [hypVec]

end Vectors

section Flags

variable {K : Type} [Field K]

noncomputable def Wfl (K : Type) [Field K] (c : Fin 3 → Fin 3 ⊕ Fin 3) (i : Fin 3) :
    Submodule K (Vt K) :=
  Submodule.span K (Set.range fun j : Fin ((i : ℕ) + 1) =>
    hypVec K (Fin 2 → K) (c (Fin.castLE (Nat.succ_le_of_lt i.2) j)))

theorem hypVec_mem_Wfl {c : Fin 3 → Fin 3 ⊕ Fin 3} {i j : Fin 3} (hj : j ≤ i) :
    hypVec K (Fin 2 → K) (c j) ∈ Wfl K c i :=
  Submodule.subset_span ⟨⟨j.val, by have := Fin.le_def.1 hj; omega⟩, by
    congr 2⟩

theorem Wfl_mono (c : Fin 3 → Fin 3 ⊕ Fin 3) : Monotone (Wfl K c) := by
  intro i i' hii'
  refine Submodule.span_le.2 ?_
  rintro _ ⟨j, rfl⟩
  refine hypVec_mem_Wfl (K := K) (c := c) ?_
  have h1 := Fin.le_def.1 hii'
  have h2 := j.2
  show (Fin.castLE _ j).val ≤ i'.val
  simp only [Fin.val_castLE]
  omega

theorem linearIndependent_hypVec_comp {ι : Type*} (c : ι → Fin 3 ⊕ Fin 3)
    (hc : Function.Injective c) :
    LinearIndependent K (fun j => hypVec K (Fin 2 → K) (c j)) := by
  have h1 : LinearIndependent K (fun d : Fin 3 ⊕ Fin 3 => (Pi.single d (1 : K) : Fin 3 ⊕ Fin 3 → K)) := by
    have e : (⇑(Pi.basisFun K (Fin 3 ⊕ Fin 3))) =
        fun d : Fin 3 ⊕ Fin 3 => (Pi.single d (1 : K) : Fin 3 ⊕ Fin 3 → K) :=
      funext fun d => by simp [Pi.basisFun_apply]
    have := (Pi.basisFun K (Fin 3 ⊕ Fin 3)).linearIndependent
    rwa [e] at this
  have h2 := h1.comp c hc
  exact h2.map' (LinearMap.inl K _ (Fin 2 → K)) (LinearMap.ker_eq_bot.2 LinearMap.inl_injective)

theorem finrank_Wfl {c : Fin 3 → Fin 3 ⊕ Fin 3} (hc : Function.Injective c) (i : Fin 3) :
    finrank K (Wfl K c i) = (i : ℕ) + 1 := by
  have hli := (linearIndependent_hypVec_comp (K := K) c hc).comp
    (fun j : Fin ((i : ℕ) + 1) => Fin.castLE (Nat.succ_le_of_lt i.2) j) (Fin.castLE_injective _)
  have h := finrank_span_eq_card hli
  rw [Fintype.card_fin] at h
  exact h

theorem quadTail_eq_zero_of_mem_Wfl {c : Fin 3 → Fin 3 ⊕ Fin 3}
    (hc : ∀ i j, c i ≠ (c j).swap) (qA : QuadraticForm K (Fin 2 → K)) (i : Fin 3) :
    ∀ x ∈ Wfl K c i, quadTail 3 qA x = 0 := by
  intro x hx
  refine map_eq_zero_of_mem_span (K := K) (S := Set.range fun j : Fin ((i : ℕ) + 1) =>
    hypVec K (Fin 2 → K) (c (Fin.castLE (Nat.succ_le_of_lt i.2) j))) ?_ ?_ hx
  · rintro _ ⟨j, rfl⟩
    exact quadTail_hypVec _
  · rintro _ ⟨j, rfl⟩ _ ⟨l, rfl⟩
    rw [polar_hypVec_hypVec]
    simp [hc]

theorem Wfl_mem_singularFlags {c : Fin 3 → Fin 3 ⊕ Fin 3} (hc : Function.Injective c)
    (hc' : ∀ i j, c i ≠ (c j).swap) (qA : QuadraticForm K (Fin 2 → K)) :
    Wfl K c ∈ singularFlags (quadTail 3 qA) 3 :=
  ⟨fun i => finrank_Wfl hc i, Wfl_mono c, fun i => quadTail_eq_zero_of_mem_Wfl hc' qA i⟩

theorem map_mem_Wfl {c : Fin 3 → Fin 3 ⊕ Fin 3} {i : Fin 3} (g : Vt K ≃ₗ[K] Vt K)
    (h : ∀ j : Fin 3, j ≤ i → g (hypVec K (Fin 2 → K) (c j)) ∈ Wfl K c i) :
    ∀ w ∈ Wfl K c i, g w ∈ Wfl K c i := by
  intro w hw
  have : (Wfl K c i).map (g : Vt K →ₗ[K] Vt K) ≤ Wfl K c i := by
    rw [Wfl, Submodule.map_span_le]
    rintro _ ⟨j, rfl⟩
    exact h _ (by
      show (Fin.castLE _ j).val ≤ i.val
      simp only [Fin.val_castLE]
      have := j.2
      omega)
  exact this ⟨w, hw, rfl⟩

end Flags

section Clauses

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K} [AnisoPair b c]

def cA : Fin 3 → Fin 3 ⊕ Fin 3 := ![Sum.inl 2, Sum.inr 0, Sum.inl 1]

def cB : Fin 3 → Fin 3 ⊕ Fin 3 := ![Sum.inr 0, Sum.inl 1, Sum.inl 2]

theorem cA_injective : Function.Injective cA := by decide

theorem cB_injective : Function.Injective cB := by decide

theorem cA_noswap : ∀ i j, cA i ≠ (cA j).swap := by decide

theorem cB_noswap : ∀ i j, cB i ≠ (cB j).swap := by decide

variable (b c) in
noncomputable def elemB (g₁ g₃ : Tns b c) : Vt K ≃ₗ[K] Vt K := torusHom b c (g₁, 1, g₃)

theorem elemB_apply (g₁ g₃ : Tns b c) (v : Vt K) :
    elemB b c g₁ g₃ v = trFun ((g₁ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1
      ((g₃ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) v := by
  simp [elemB, torusHom_apply, trEquiv_apply]

theorem elemB_cA_zero (g₁ g₃ : Tns b c) :
    ∀ w ∈ Wfl K cA 0, elemB b c g₁ g₃ w ∈ Wfl K cA 0 := by
  refine map_mem_Wfl _ fun j hj => ?_
  have : j = 0 := Fin.le_zero_iff.1 hj
  subst this
  have h := hypVec_mem_Wfl (K := K) (c := cA) (i := 0) (j := 0) le_rfl
  show elemB b c g₁ g₃ (e2v K) ∈ _
  rw [elemB_apply, trFun_e2]
  exact h

theorem elemB_cA_two (g₁ g₃ : Tns b c) :
    ∀ w ∈ Wfl K cA 2, elemB b c g₁ g₃ w ∈ Wfl K cA 2 := by
  have h0 : e2v K ∈ Wfl K cA 2 := hypVec_mem_Wfl (K := K) (c := cA) (i := 2) (j := 0) (by decide)
  have h1 : f0v K ∈ Wfl K cA 2 := hypVec_mem_Wfl (K := K) (c := cA) (i := 2) (j := 1) (by decide)
  have h2 : e1 K ∈ Wfl K cA 2 := hypVec_mem_Wfl (K := K) (c := cA) (i := 2) (j := 2) (by decide)
  refine map_mem_Wfl _ fun j _ => ?_
  fin_cases j
  · show elemB b c g₁ g₃ (e2v K) ∈ _
    rw [elemB_apply, trFun_e2]
    exact h0
  · show elemB b c g₁ g₃ (f0v K) ∈ _
    rw [elemB_apply, trFun_f0]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ h2) (Submodule.smul_mem _ _ h1)
  · show elemB b c g₁ g₃ (e1 K) ∈ _
    rw [elemB_apply, trFun_e1]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ h2) (Submodule.smul_mem _ _ h1)

theorem elemB_cB_one (g₁ g₃ : Tns b c) :
    ∀ w ∈ Wfl K cB 1, elemB b c g₁ g₃ w ∈ Wfl K cB 1 := by
  have h1 : f0v K ∈ Wfl K cB 1 := hypVec_mem_Wfl (K := K) (c := cB) (i := 1) (j := 0) (by decide)
  have h2 : e1 K ∈ Wfl K cB 1 := hypVec_mem_Wfl (K := K) (c := cB) (i := 1) (j := 1) (by decide)
  refine map_mem_Wfl _ fun j hj => ?_
  fin_cases j
  · show elemB b c g₁ g₃ (f0v K) ∈ _
    rw [elemB_apply, trFun_f0]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ h2) (Submodule.smul_mem _ _ h1)
  · show elemB b c g₁ g₃ (e1 K) ∈ _
    rw [elemB_apply, trFun_e1]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ h2) (Submodule.smul_mem _ _ h1)
  · exact absurd hj (by decide)

theorem conj_stab {n g : Vt K ≃ₗ[K] Vt K} {W W' : Submodule K (Vt K)}
    (hW : W.map (n : Vt K →ₗ[K] Vt K) = W') (hg : ∀ w ∈ W, g w ∈ W) :
    ∀ w ∈ W', (n * g * n⁻¹) w ∈ W' := by
  intro w hw
  rw [← hW] at hw
  obtain ⟨u, hu, rfl⟩ := hw
  show n (g (n.symm (n u))) ∈ _
  rw [LinearEquiv.symm_apply_apply, ← hW]
  exact Submodule.mem_map_of_mem (hg u hu)

theorem exists_flag_conj {W : Fin 3 → Submodule K (Vt K)}
    (hW : W ∈ singularFlags (quadTail 3 (minusTailForm K b c)) 3) :
    ∃ n ∈ G0 b c, ∀ i : Fin 3,
      (W i).map (n : Vt K →ₗ[K] Vt K) = tailFlag K (Fin 2 → K) 3 ((i : ℕ) + 1) := by
  have hani := anisotropic_minusTailForm (AnisoPair.hirr (b := b) (c := c))
  obtain ⟨w, hw⟩ := exists_ne_zero_fin2 (K := K)
  obtain ⟨n, hn, h⟩ := (orthogonal_geometry_tail_singular_flag_transitivity (K := K)
    (A := Fin 2 → K) (r := 3) (qA := minusTailForm K b c) hani ⟨w, hw⟩).1 3 le_rfl W hW _
    (tailFlag_mem_singularFlags (K := K) (A := Fin 2 → K) (r := 3) (qA := minusTailForm K b c))
  exact ⟨n, hn, h⟩

theorem exists_B {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    (hcard : Nat.card ↥(G0 b c) = (Nat.card K) ^ 12 * ((Nat.card K) ^ 4 + 1) *
      (((Nat.card K) ^ 2 - 1) * ((Nat.card K) ^ 4 - 1) * ((Nat.card K) ^ 6 - 1)))
    (hpq : p ∣ Nat.card K + 1) {A : Subgroup (Vt K ≃ₗ[K] Vt K)} (hAG : A ≤ G0 b c)
    (hA : ∀ a ∈ A, a ^ p = 1) :
    ∃ h₀ ∈ G0 b c, ∃ B : Subgroup (Vt K ≃ₗ[K] Vt K), B ≤ A ∧ Nat.card A ≤ p * Nat.card B ∧
      ∀ y ∈ B, ∃ g₁ g₃ : Tns b c, h₀ * y * h₀⁻¹ = elemB b c g₁ g₃ := by
  obtain ⟨h₀, hh₀, hAh₀⟩ := exists_conj_le_torusHom hp5 hcard hpq hAG hA
  have : IsCyclic (Tns b c) := isCyclic_Tns
  let ψ : Tns b c × Tns b c × Tns b c →* Tns b c :=
    (MonoidHom.fst (Tns b c) (Tns b c)).comp (MonoidHom.snd (Tns b c) (Tns b c × Tns b c))
  obtain ⟨B, hBA, hBcard, hB⟩ := exists_torus_subgroup (Fact.out : p.Prime).pos (torusHom b c)
    torusHom_injective ψ hA hAh₀
  refine ⟨h₀, hh₀, B, hBA, hBcard, fun y hy => ?_⟩
  obtain ⟨⟨g₁, g₂, g₃⟩, ht, hty⟩ := hB y hy
  have h2 : g₂ = 1 := ht
  subst h2
  exact ⟨g₁, g₃, hty⟩

theorem row4_clause_one {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    (hcard : Nat.card ↥(G0 b c) = (Nat.card K) ^ 12 * ((Nat.card K) ^ 4 + 1) *
      (((Nat.card K) ^ 2 - 1) * ((Nat.card K) ^ 4 - 1) * ((Nat.card K) ^ 6 - 1)))
    (hpq : p ∣ Nat.card K + 1) {A : Subgroup (Vt K ≃ₗ[K] Vt K)} (hAG : A ≤ G0 b c)
    (hA : ∀ a ∈ A, a ^ p = 1) :
    ∃ h ∈ G0 b c, ∃ B : Subgroup (Vt K ≃ₗ[K] Vt K), B ≤ A ∧ Nat.card A ≤ p * Nat.card B ∧
      B.map (MulAut.conj h).toMonoidHom ≤
        Subgroup.normalizer (pushingUpS (U0 b c) : Set (Vt K ≃ₗ[K] Vt K)) := by
  obtain ⟨h₀, hh₀, B, hBA, hBcard, hB⟩ := exists_B hp5 hcard hpq hAG hA
  obtain ⟨n, hn, hnW⟩ := exists_flag_conj (b := b) (c := c)
    (Wfl_mem_singularFlags cA_injective cA_noswap (minusTailForm K b c))
  refine ⟨n * h₀, mul_mem hn hh₀, B, hBA, hBcard, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨g₁, g₃, hg⟩ := hB y hy
  have e : (MulAut.conj (n * h₀)).toMonoidHom y = n * elemB b c g₁ g₃ * n⁻¹ := by
    rw [← hg]
    simp [MulAut.conj_apply, mul_assoc]
  rw [e]
  refine P13_le_normalizer_pushingUpS ⟨?_, ?_, ?_⟩
  · exact mul_mem (mul_mem hn (torusHom_mem_G0 _)) (inv_mem hn)
  · have h0 := hnW 0
    simp only [Fin.val_zero, zero_add] at h0
    exact conj_stab h0 (elemB_cA_zero g₁ g₃)
  · have h2 := hnW 2
    simp only [Fin.val_two] at h2
    exact conj_stab h2 (elemB_cA_two g₁ g₃)

theorem row4_clause_two {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    (hcard : Nat.card ↥(G0 b c) = (Nat.card K) ^ 12 * ((Nat.card K) ^ 4 + 1) *
      (((Nat.card K) ^ 2 - 1) * ((Nat.card K) ^ 4 - 1) * ((Nat.card K) ^ 6 - 1)))
    (hpq : p ∣ Nat.card K + 1) {A : Subgroup (Vt K ≃ₗ[K] Vt K)} (hAG : A ≤ G0 b c)
    (hA : ∀ a ∈ A, a ^ p = 1) :
    ∃ h ∈ G0 b c, ∃ B : Subgroup (Vt K ≃ₗ[K] Vt K), B ≤ A ∧ Nat.card A ≤ p * Nat.card B ∧
      B.map (MulAut.conj h).toMonoidHom ≤
        Subgroup.centralizer ({x0 b c} : Set (Vt K ≃ₗ[K] Vt K)) := by
  obtain ⟨h₀, hh₀, B, hBA, hBcard, hB⟩ := exists_B hp5 hcard hpq hAG hA
  obtain ⟨n, hn, hnW⟩ := exists_flag_conj (b := b) (c := c)
    (Wfl_mem_singularFlags cB_injective cB_noswap (minusTailForm K b c))
  refine ⟨n * h₀, mul_mem hn hh₀, B, hBA, hBcard, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨g₁, g₃, hg⟩ := hB y hy
  have e : (MulAut.conj (n * h₀)).toMonoidHom y = n * elemB b c g₁ g₃ * n⁻¹ := by
    rw [← hg]
    simp [MulAut.conj_apply, mul_assoc]
  have hyp : ((MulAut.conj (n * h₀)).toMonoidHom y) ^ p = 1 := by
    rw [← map_pow, hA y (hBA hy), map_one]
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  rw [Set.mem_singleton_iff] at hz
  rw [hz]
  have hnO := orthElementaryGroup_le _ hn
  have hO : (MulAut.conj (n * h₀)).toMonoidHom y ∈
      TauCeti.QuadraticMap.orthogonalGroup (quadTail 3 (minusTailForm K b c)) := by
    rw [e]
    exact mul_mem (mul_mem hnO (torusHom_mem_orth _)) (inv_mem hnO)
  have hs : (MulAut.conj (n * h₀)).toMonoidHom y ∈ Stab2 K := by
    rw [e]
    have h1 := hnW 1
    simp only [Fin.val_one] at h1
    exact mem_Stab2.2 (conj_stab h1 (elemB_cB_one g₁ g₃))
  have hcop : Nat.Coprime p (Nat.card K - 1) := by
    refine (Nat.Prime.coprime_iff_not_dvd Fact.out).2 fun hd => ?_
    have h2 : p ∣ 2 := by
      have hq : 1 ≤ Nat.card K := Nat.one_le_iff_ne_zero.2 Nat.card_pos.ne'
      have := Nat.dvd_sub hpq hd
      have e2 : Nat.card K + 1 - (Nat.card K - 1) = 2 := by omega
      rwa [e2] at this
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  have hdet := det_coefMat_eq_one hs (Fact.out : p.Prime).pos hyp hcop
  exact (commute_x0_of_det hO hs hdet).symm

end Clauses

end CFSG.RankThree.PartOne.KF1514B
