module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829NKS9Kan
public import CFSG.Quasithin.Vol2.Ch8Sec2L829S9Chain5
public import CFSG.Quasithin.Vol2.Ch8Sec2L829S9Chain6

public section

namespace CFSG.Quasithin.H13.L829NK

open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.L829N CFSG.RankThree.SubgroupLists
open Matrix
open scoped MatrixGroups

theorem nk_s9c_caseB (hSch : NKLeafSchurL32) (hSL3 : NKLeafSL3Rep)
    (hConj : ∀ (X : Type) [Group X], IsPSL 3 2 1 X → ∀ a b : X, orderOf a = 2 → orderOf b = 2 →
      IsConj a b)
    {E : Type} [Field E] [Finite E] [CharP E 2] (hE2 : Nat.card E = 2 ∨ Nat.card E = 4) {e d : ℕ} (he : 1 ≤ e)
    (hE : Nat.card E = 2 ^ e)
    (t : GL (Fin d) E) (ht : IsTransvectionK t)
    (K₀ : Subgroup (GL (Fin d) E)) (N : Subgroup (GL (Fin d) E))
    (hN : N = Subgroup.closure {x | ∃ k ∈ K₀, x = k * t * k⁻¹})
    (hKN : K₀ ≤ N) (htN : t ∈ N)
    (hnorm : ∀ g ∈ N, ∀ k ∈ K₀, g * k * g⁻¹ ∈ K₀ ∧ g⁻¹ * k * g ∈ K₀)
    {Ks : Type} [Group Ks] (hKs : IsSimpleGroup Ks) (hKs3 : IsPSL 3 2 1 Ks)
    (σ : K₀ →* Ks) (hσ : Function.Surjective σ)
    (hker : ∀ M : Subgroup K₀, M.Normal → M ≠ ⊤ → M ≤ σ.ker)
    (hK₀perf : commutator ↥K₀ = ⊤)
    (hQ : ∃ Q : Subgroup (GL (Fin d) E), Q ≤ K₀ ∧ (∀ q ∈ Q, ∃ m : ℕ, q ^ 2 ^ m = 1) ∧
      (∀ q ∈ Q, ∀ x ∈ K₀, x * q * x⁻¹ ∈ Q) ∧ (∀ q ∈ Q, t * q * t⁻¹ ∈ Q) ∧
      (∃ k₀ ∈ K₀, ∀ x ∈ K₀, ∃ q ∈ Q, t * x * t⁻¹ = q * (k₀ * x * k₀⁻¹)) ∧
      (∀ z : ↥K₀, σ z = 1 → ∀ x ∈ K₀, ∃ q ∈ Q, (z : GL (Fin d) E) * x * (z : GL (Fin d) E)⁻¹ =
        q * x))
    (r : ℕ) (Y : ℕ → Submodule E (Fin d → E)) (hY0 : Y 0 = ⊥) (hYr : Y r = ⊤)
    (hmono : ∀ i j, i ≤ j → j ≤ r → Y i ≤ Y j)
    (hYinv : ∀ i, i ≤ r → S9cInv N (Y i))
    (hstep : ∀ i, i < r → Y i < Y (i + 1) ∧ ∀ W : Submodule E (Fin d → E), S9cInv N W →
      Y i ≤ W → W ≤ Y (i + 1) → W = Y i ∨ W = Y (i + 1))
    (u : Fin d → E)
    (hcov : ∀ v : Fin d → E, ∃ c : E,
      ((t : GL (Fin d) E) : Matrix (Fin d) (Fin d) E) *ᵥ v - v = c • u)
    (i₀ : ℕ) (hi₀ : i₀ < r)
    (hi₀nt : ∃ v ∈ Y (i₀ + 1), ((t : GL (Fin d) E) : Matrix (Fin d) (Fin d) E) *ᵥ v - v ∉ Y i₀)
    (hunique : ∀ i, i < r → (∃ v ∈ Y (i + 1), ((t : GL (Fin d) E) : Matrix (Fin d) (Fin d) E) *ᵥ v - v ∉ Y i) →
      i = i₀) :
    ∃ θ : K₀ →* SL(3, ZMod 2), Function.Surjective θ ∧ θ.ker = σ.ker ∧
      (∀ x : K₀, ((θ x : SL(3, ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) = s9M1 →
        (s9P1 (x : GL (Fin d) E).val).det = 0) ∧
      (∀ x : K₀, s9P2 (((θ x : SL(3, ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).map
          (fun a : ZMod 2 => ((a.val : ℕ) : E))) = 0 →
        (s9P1 (x : GL (Fin d) E).val).det ≠ 0) := by
  classical
  set n := Module.finrank E (s9cSub (Y i₀) (Y (i₀ + 1))) with hn_def
  have hAB : Y i₀ ≤ Y (i₀ + 1) := hmono i₀ (i₀ + 1) (Nat.le_succ i₀) (Nat.succ_le_of_lt hi₀)
  have hAlt : Y i₀ < Y (i₀ + 1) := (hstep i₀ hi₀).1
  have hA : S9cInv N (Y i₀) := hYinv i₀ hi₀.le
  have hB : S9cInv N (Y (i₀ + 1)) := hYinv (i₀ + 1) (Nat.succ_le_of_lt hi₀)
  have hirr := (hstep i₀ hi₀).2
  obtain ⟨huB, huA⟩ := s9c_nontriv_line N t htN Y hYinv u hcov i₀ hi₀ hi₀nt
  obtain ⟨x0, hx0⟩ := s9c_K0_nontrivial t ht K₀ N hN hKN htN hA hB hAB hirr hi₀nt
  let ρK : K₀ →* GL (Fin (Module.finrank E (s9cSub (Y i₀) (Y (i₀ + 1))))) E :=
    (s9cRep hA hB).comp (Subgroup.inclusion hKN)
  have hρK : ∀ x : K₀, ρK x = s9cRep hA hB ⟨x, hKN x.2⟩ := fun x => rfl
  have hkerρ : ρK.ker ≤ σ.ker := by
    refine hker ρK.ker inferInstance ?_
    intro htop
    apply hx0
    have hmem : x0 ∈ ρK.ker := by
      rw [htop]
      exact Subgroup.mem_top _
    exact MonoidHom.mem_ker.mp hmem
  have hτ : IsTransvectionK (s9cRep hA hB ⟨t, htN⟩ : GL (Fin (Module.finrank E (s9cSub (Y i₀) (Y (i₀ + 1))))) E) :=
    s9c_rep_isTransvection hA hB ⟨t, htN⟩ ht u huB huA hcov hi₀nt
  have hgen : GeneratedByTransvectionClass (s9cRep hA hB).range :=
    ⟨s9cRep hA hB ⟨t, htN⟩, MonoidHom.mem_range.mpr ⟨⟨t, htN⟩, rfl⟩, hτ,
      s9c_gen_range t K₀ N hN hKN htN hA hB⟩
  have hirrN : CFSG.RankThree.SubgroupLists.IsIrreducibleOn (s9cRep hA hB).range :=
    fun W hW => s9c_irred_range hA hB hAB hirr W hW
  have hle : ρK.range ≤ (s9cRep hA hB).range := by
    rintro _ ⟨x, rfl⟩
    exact ⟨⟨x, hKN x.2⟩, rfl⟩
  have hnormal : ∀ g ∈ (s9cRep hA hB).range, ∀ k ∈ ρK.range, g * k * g⁻¹ ∈ ρK.range := by
    rintro _ ⟨m, rfl⟩ _ ⟨x, rfl⟩
    refine ⟨⟨(m : GL (Fin d) E) * (x : GL (Fin d) E) * (m : GL (Fin d) E)⁻¹,
      (hnorm m.1 m.2 x.1 x.2).1⟩, ?_⟩
    have hmem : (m : GL (Fin d) E) * (x : GL (Fin d) E) * (m : GL (Fin d) E)⁻¹ ∈ N :=
      N.mul_mem (N.mul_mem m.2 (hKN x.2)) (N.inv_mem m.2)
    have e : (⟨(m : GL (Fin d) E) * (x : GL (Fin d) E) * (m : GL (Fin d) E)⁻¹, hmem⟩ : N) =
        m * ⟨(x : GL (Fin d) E), hKN x.2⟩ * m⁻¹ := by
      apply Subtype.ext
      simp [mul_assoc]
    show s9cRep hA hB ⟨(m : GL (Fin d) E) * (x : GL (Fin d) E) * (m : GL (Fin d) E)⁻¹, hmem⟩ =
      s9cRep hA hB m * s9cRep hA hB ⟨(x : GL (Fin d) E), hKN x.2⟩ * (s9cRep hA hB m)⁻¹
    rw [e, map_mul, map_mul, map_inv]
  have hcf : E1.IsCompositionFactor ↥(s9cRep hA hB).range Ks :=
    s9c_cf_of_quot σ hσ hKs ρK hkerρ (s9cRep hA hB).range hle hnormal
  obtain ⟨hn, P, hPiff⟩ := nk_s9_kantor hSch hSL3 hConj hE2 t ht K₀ N hN hKN htN hA hB hirrN hτ
    hKs3 σ hσ hkerρ hK₀perf hnorm hQ
  have hran : ∀ x : K₀, P * ρK x * P⁻¹ ∈ (s9cJ hn).range := fun x =>
    (hPiff (ρK x)).mp ⟨⟨x, hKN x.2⟩, rfl⟩
  haveI : Finite Ks := Nat.finite_of_card_ne_zero (by rw [s9c_card_of_IsPSL3 hKs3]; norm_num)
  obtain ⟨θ, hθ, hθsurj, hθker⟩ := s9c_theta_of_card σ hσ (s9c_card_of_IsPSL3 hKs3) ρK hkerρ P
    (s9cJ hn) (s9cJ_injective hn) s9_card_SL3_F2 hran
  let φ : ZMod 2 →+* E := ZMod.castHom (dvd_refl 2) E
  have hφ : ∀ a : ZMod 2, φ a = ((a.val : ℕ) : E) := fun a => by
    rw [show φ a = (ZMod.cast a : E) from rfl, ZMod.cast_eq_val]
  have hmapφ : ∀ M : Matrix (Fin 3) (Fin 3) (ZMod 2),
      M.map (fun a : ZMod 2 => ((a.val : ℕ) : E)) = RingHom.mapMatrix φ M := by
    intro M
    ext i j
    simp [RingHom.mapMatrix_apply, hφ]
  refine ⟨θ, hθsurj, hθker, ?_, ?_⟩
  · intro x hx
    have hJ1 : s9P1 ((s9cJ hn (θ x) : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = 0 := by
      simp [s9cJ_s9P1, hx, s9P1_M1]
    have hconj := congrArg Units.val (hθ x)
    rw [Units.val_mul, Units.val_mul] at hconj
    have hR0 : s9P1 ((ρK x : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = 0 := by
      apply s9c_conj_zero P
      rw [← s9c_conj_s9P1, ← hconj, hJ1]
    exact s9c_claim_i hA hB hAlt ⟨(x : GL (Fin d) E), hKN x.2⟩ hR0
  · intro x hx2
    have hz : (s9P2 ((θ x : SL(3, ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))).map
        (fun a : ZMod 2 => ((a.val : ℕ) : E)) = 0 := by
      have hr := s9c_ringhom_s9P2 (RingHom.mapMatrix φ) ((θ x : SL(3, ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))
      rw [← hmapφ, hx2] at hr
      rw [hmapφ]
      exact hr.symm
    have hP2J : s9P2 ((s9cJ hn (θ x) : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = 0 := by
      rw [s9cJ_s9P2, hz]
      simp
    have hconj := congrArg Units.val (hθ x)
    rw [Units.val_mul, Units.val_mul] at hconj
    have hPM := s9_mul_P1_of_P2 (s9c_two_matrix n) _ hP2J
    rw [hconj, s9c_conj_s9P1] at hPM
    have hinv := s9c_conj_cancel P _ _ hPM
    have htrivx : ∀ i, i < r → i ≠ i₀ → ∀ v ∈ Y (i + 1),
        ((x : GL (Fin d) E) : Matrix (Fin d) (Fin d) E) *ᵥ v - v ∈ Y i := by
      intro i hi hne v hv
      have ht' : ∀ w ∈ Y (i + 1), ((t : GL (Fin d) E) : Matrix (Fin d) (Fin d) E) *ᵥ w - w ∈ Y i := by
        intro w hw
        by_contra hnot
        exact hne (hunique i hi ⟨w, hw, hnot⟩)
      exact s9c_triv_prop K₀ N t hN hKN Y hYinv i hi ht' (x : GL (Fin d) E) (hKN x.2) v hv
    exact s9c_claim_j hA hB hAlt ⟨(x : GL (Fin d) E), hKN x.2⟩ Y hY0 hYr i₀ hi₀ rfl rfl hYinv
      htrivx hinv


theorem nk_s9_chain_main (hSch : NKLeafSchurL32) (hSL3 : NKLeafSL3Rep)
    (hConj : ∀ (X : Type) [Group X], IsPSL 3 2 1 X → ∀ a b : X, orderOf a = 2 → orderOf b = 2 →
      IsConj a b)
    {E : Type} [Field E] [Finite E] [CharP E 2] (hE2 : Nat.card E = 2 ∨ Nat.card E = 4) {e d : ℕ}
    (he : 1 ≤ e) (hE : Nat.card E = 2 ^ e)
    (t : GL (Fin d) E) (ht : IsTransvectionK t)
    (K₀ : Subgroup (GL (Fin d) E)) (htK : ∀ k ∈ K₀, t * k * t⁻¹ ∈ K₀)
    (hK₀N : K₀ ≤ Subgroup.closure {x | ∃ k ∈ K₀, x = k * t * k⁻¹})
    {Ks : Type} [Group Ks] (hKs : IsSimpleGroup Ks) (hna : ∃ a b : Ks, a * b ≠ b * a)
    (hKs3 : IsPSL 3 2 1 Ks)
    (σ : K₀ →* Ks) (hσ : Function.Surjective σ)
    (hker : ∀ M : Subgroup K₀, M.Normal → M ≠ ⊤ → M ≤ σ.ker)
    (hK₀perf : commutator ↥K₀ = ⊤)
    (hQ : ∃ Q : Subgroup (GL (Fin d) E), Q ≤ K₀ ∧ (∀ q ∈ Q, ∃ m : ℕ, q ^ 2 ^ m = 1) ∧
      (∀ q ∈ Q, ∀ x ∈ K₀, x * q * x⁻¹ ∈ Q) ∧ (∀ q ∈ Q, t * q * t⁻¹ ∈ Q) ∧
      (∃ k₀ ∈ K₀, ∀ x ∈ K₀, ∃ q ∈ Q, t * x * t⁻¹ = q * (k₀ * x * k₀⁻¹)) ∧
      (∀ z : ↥K₀, σ z = 1 → ∀ x ∈ K₀, ∃ q ∈ Q, (z : GL (Fin d) E) * x * (z : GL (Fin d) E)⁻¹ =
        q * x)) :
    ∃ θ : K₀ →* SL(3, ZMod 2), Function.Surjective θ ∧ θ.ker = σ.ker ∧
      (∀ x : K₀, ((θ x : SL(3, ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) = s9M1 →
        (s9P1 (x : GL (Fin d) E).val).det = 0) ∧
      (∀ x : K₀, s9P2 (((θ x : SL(3, ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).map
          (fun a : ZMod 2 => ((a.val : ℕ) : E))) = 0 →
        (s9P1 (x : GL (Fin d) E).val).det ≠ 0) := by
  classical
  obtain ⟨N, hN, hKN, htN, hnorm⟩ := s9c_part1 t ht K₀ htK hK₀N
  obtain ⟨r, Y, hY0, hYr, hmono, hYinv, hstep, u, hu0, hcov⟩ := s9c_part2 t ht N
  by_cases hcase : ∃ i, i < r ∧ ∃ v ∈ Y (i + 1),
      ((t : GL (Fin d) E) : Matrix (Fin d) (Fin d) E) *ᵥ v - v ∉ Y i
  · obtain ⟨i₀, hi₀, hi₀nt⟩ := hcase
    refine nk_s9c_caseB hSch hSL3 hConj hE2 he hE t ht K₀ N hN hKN htN hnorm hKs hKs3 σ hσ hker hK₀perf hQ r Y hY0 hYr
      hmono hYinv hstep u hcov i₀ hi₀ hi₀nt ?_
    intro i hi hI
    exact s9c_nontriv_unique t Y hmono u
      (fun j hj hJ => s9c_nontriv_line N t htN Y hYinv u hcov j hj hJ) i i₀ hi hi₀ hI hi₀nt
  · exfalso
    push_neg at hcase
    have hpg : ∀ x : K₀, ∃ m : ℕ, x ^ (2 ^ m) = 1 := by
      intro x
      have hnil := s9c_flag_nilpotent r Y hY0 hYr (x : GL (Fin d) E)
        (fun i hi v hv => s9c_triv_prop K₀ N t hN hKN Y hYinv i hi (hcase i hi)
          (x : GL (Fin d) E) (hKN x.2) v hv)
      obtain ⟨m, hm⟩ := s9c_pow_two_eq_one (x : GL (Fin d) E) r hnil
      refine ⟨m, Subtype.ext ?_⟩
      simpa using hm
    haveI : Finite Ks := Nat.finite_of_card_ne_zero (by rw [s9c_card_of_IsPSL3 hKs3]; norm_num)
    exact s9c_false_of_pgroup σ hσ hpg (s9c_card_of_IsPSL3 hKs3)

end CFSG.Quasithin.H13.L829NK
