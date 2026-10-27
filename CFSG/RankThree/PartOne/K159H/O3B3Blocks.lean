module

public import CFSG.RankThree.PartOne.K159H.O3Weyl
public import CFSG.RankThree.PartOne.K159H.O3Bshort
public import CFSG.RankThree.PartOne.K159H.O3Coord
public import CFSG.RankThree.PartOne.K159H.O3Blong
public import CFSG.RankThree.PartOne.KFR4.B3Refl

public noncomputable section

namespace CFSG.RankThree.PartOne.K159H

open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
  CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.LieType.Universal.Spin
  CFSG.RankThree.OrthogonalInvolutions Module CFSG.RankThree.PartOne.KFR4

variable {K : Type} [Field K] {A : Type} [AddCommGroup A] [Module K A]

@[expose] def lA : Root → Fin 3 ⊕ Fin 3
  | .m12 => Sum.inl 0
  | .m13 => Sum.inl 0
  | .m23 => Sum.inl 1
  | .p12 => Sum.inl 0
  | .p13 => Sum.inl 0
  | .p23 => Sum.inl 1
  | _ => Sum.inl 0

@[expose] def lB : Root → Fin 3 ⊕ Fin 3
  | .m12 => Sum.inl 1
  | .m13 => Sum.inl 2
  | .m23 => Sum.inl 2
  | .p12 => Sum.inr 1
  | .p13 => Sum.inr 2
  | .p23 => Sum.inr 2
  | _ => Sum.inl 1

@[expose] def shortRoot : Fin 3 → Root := ![Root.s1, Root.s2, Root.s3]

theorem shortRoot_isShort (k : Fin 3) : (shortRoot k).IsShort := by
  fin_cases k <;> simp [shortRoot, Root.IsShort]

theorem idx_shortRoot (k : Fin 3) : (shortRoot k).idx = k := by
  fin_cases k <;> simp [shortRoot, Root.idx]

theorem lA_ne_lB {ρ : Root} (h : ¬ ρ.IsShort) : coordIdx (lA ρ) ≠ coordIdx (lB ρ) := by
  cases ρ <;> simp [Root.IsShort, lA, lB] at h ⊢

variable (qA : QuadraticForm K A)

@[expose] def Bblock (ρ : Root) :
    Subgroup (((Fin 3 ⊕ Fin 3 → K) × A) ≃ₗ[K] ((Fin 3 ⊕ Fin 3 → K) × A)) :=
  if ρ.IsShort then Bshort qA ρ.idx else Blong qA (lA ρ) (lB ρ)

variable {qA}

theorem Bblock_short {ρ : Root} (h : ρ.IsShort) : Bblock qA ρ = Bshort qA ρ.idx := by
  simp [Bblock, h]

theorem Bblock_long {ρ : Root} (h : ¬ ρ.IsShort) : Bblock qA ρ = Blong qA (lA ρ) (lB ρ) := by
  simp [Bblock, h]

section Group

variable [Finite K] [CharP K 2] [FiniteDimensional K A]

theorem Blong_le_Om (hreg : (polarBilin qA).Nondegenerate) {r : ℕ} (hr : 3 ≤ r) {a b : Fin r ⊕ Fin r} :
    Blong qA a b ≤ Om qA r := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ (⟨t, rfl⟩ | ⟨t, rfl⟩)
  · exact rEl_mem_Om hreg hr t a b
  · exact rEl_mem_Om hreg hr t b a

theorem Bblock_le_Om (hreg : (polarBilin qA).Nondegenerate) (ρ : Root) : Bblock qA ρ ≤ Om qA 3 := by
  by_cases h : ρ.IsShort
  · rw [Bblock_short h]
    exact fun g hg => hg.1
  · rw [Bblock_long h]
    exact Blong_le_Om hreg le_rfl

theorem Bblock_simple (hK : 4 ≤ Nat.card K) (hreg : (polarBilin qA).Nondegenerate) (hani : qA.Anisotropic)
    (hdim : finrank K A = 2) (ρ : Root) : IsSimpleGroup ↥(Bblock qA ρ) := by
  have hK1 : ∃ u : Kˣ, u ≠ 1 := by
    by_contra hno
    push Not at hno
    have : Nat.card K ≤ 2 := by
      have hsub : Subsingleton Kˣ := ⟨fun a b => (hno a).trans (hno b).symm⟩
      have : Nat.card Kˣ = 1 := Nat.card_eq_one_iff_unique.2 ⟨hsub, ⟨1⟩⟩
      rw [Nat.card_units] at this
      omega
    omega
  by_cases h : ρ.IsShort
  · rw [Bblock_short h]
    exact isSimpleGroup_Bshort hK1 hreg hani hdim rfl _
  · rw [Bblock_long h]
    exact isSimpleGroup_Blong (lA_ne_lB h) hK

theorem Bblock_perfect (hK : 4 ≤ Nat.card K) (hreg : (polarBilin qA).Nondegenerate) (hani : qA.Anisotropic)
    (hdim : finrank K A = 2) (ρ : Root) : ⁅Bblock qA ρ, Bblock qA ρ⁆ = Bblock qA ρ := by
  have hK1 : ∃ u : Kˣ, u ≠ 1 := by
    by_contra hno
    push Not at hno
    have : Nat.card K ≤ 2 := by
      have hsub : Subsingleton Kˣ := ⟨fun a b => (hno a).trans (hno b).symm⟩
      have : Nat.card Kˣ = 1 := Nat.card_eq_one_iff_unique.2 ⟨hsub, ⟨1⟩⟩
      rw [Nat.card_units] at this
      omega
    omega
  by_cases h : ρ.IsShort
  · rw [Bblock_short h]
    exact Bshort_perfect hK1 hreg hani hdim rfl _
  · rw [Bblock_long h]
    exact Blong_perfect (lA_ne_lB h) hK

end Group


section Weights

variable {p : ℕ} [NeZero p] {ζ : Kˣ}

theorem zpowE_inj_iff (hζ : IsPrimitiveRoot ζ p) {x y : ZMod p} : zpowE p ζ x = zpowE p ζ y ↔ x = y :=
  ⟨zpowE_inj hζ, fun h => by rw [h]⟩

theorem wt_eq_iff_long (hζ : IsPrimitiveRoot ζ p) {ρ : Root} (h : ¬ ρ.IsShort) (v : Vec p) :
    wt (dOf ζ v) (lA ρ) = wt (dOf ζ v) (lB ρ) ↔ ρ.vecp p ⬝ᵥ v = 0 := by
  have hp : ζ ^ p = 1 := hζ.pow_eq_one
  cases ρ <;> simp only [Root.IsShort, not_true_eq_false] at h <;>
    simp [lA, lB, wt_dOf_inl, wt_dOf_inr hp, zpowE_inj_iff hζ, dotProduct, Fin.sum_univ_three, Root.vecp,
      Root.vec] <;> constructor <;> intro h <;> linear_combination h

theorem forall_fin3_sum {P : Fin 3 ⊕ Fin 3 → Prop} :
    (∀ c, P c) ↔ P (Sum.inl 0) ∧ P (Sum.inl 1) ∧ P (Sum.inl 2) ∧ P (Sum.inr 0) ∧ P (Sum.inr 1) ∧
      P (Sum.inr 2) := by
  constructor
  · intro h
    exact ⟨h _, h _, h _, h _, h _, h _⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5⟩ (c | c) <;> fin_cases c <;> assumption

omit [NeZero p] in
theorem exists_smul_vecp_iff (ρ : Root) (v : Vec p) :
    (∃ s : ZMod p, v = s • ρ.vecp p) ↔ v = v ρ.idx • ρ.vecp p := by
  constructor
  · rintro ⟨s, rfl⟩
    simp [vecp_idx]
  · intro h
    exact ⟨_, h⟩

theorem torH_dOf_mem_Blong_iff [CharP K 2] (hζ : IsPrimitiveRoot ζ p) {ρ : Root} (h : ¬ ρ.IsShort) (v : Vec p) :
    torH K A 3 (dOf ζ v) ∈ Blong qA (lA ρ) (lB ρ) ↔ ∃ s : ZMod p, v = s • ρ.vecp p := by
  have hp : ζ ^ p = 1 := hζ.pow_eq_one
  rw [torH_mem_Blong_iff (lA_ne_lB h), forall_fin3_sum, exists_smul_vecp_iff]
  cases ρ <;> simp only [Root.IsShort, not_true_eq_false] at h <;>
    simp [lA, lB, wt_dOf_inl, wt_dOf_inr hp, ← zpowE_add hp, zpowE_eq_one_iff hζ,
      funext_iff, Fin.forall_fin_succ, Root.vecp, Root.vec, Root.idx]
  all_goals grind

theorem wt_eq_one_iff_short (hζ : IsPrimitiveRoot ζ p) (k : Fin 3) (v : Vec p) :
    wt (dOf ζ v) (Sum.inl k) = 1 ↔ (shortRoot k).vecp p ⬝ᵥ v = 0 := by
  rw [wt_dOf_inl, zpowE_eq_one_iff hζ]
  fin_cases k <;> simp [shortRoot, dotProduct, Fin.sum_univ_three, Root.vecp, Root.vec]

theorem torH_dOf_mem_Bshort_iff [Finite K] [CharP K 2] [FiniteDimensional K A]
    (hreg : (polarBilin qA).Nondegenerate) (hζ : IsPrimitiveRoot ζ p) (k : Fin 3) (v : Vec p) :
    torH K A 3 (dOf ζ v) ∈ Bshort qA k ↔ ∃ s : ZMod p, v = s • (shortRoot k).vecp p := by
  have hp : ζ ^ p = 1 := hζ.pow_eq_one
  rw [torH_mem_Bshort_iff hreg le_rfl k, forall_fin3_sum, exists_smul_vecp_iff]
  fin_cases k <;>
    simp [shortRoot, wt_dOf_inl, wt_dOf_inr hp, zpowE_eq_one_iff hζ, funext_iff, Fin.forall_fin_succ, Root.vecp,
      Root.vec, Root.idx]
  all_goals grind

theorem shortRoot_idx {ρ : Root} (h : ρ.IsShort) : shortRoot ρ.idx = ρ := by
  cases ρ <;> simp only [Root.IsShort] at h <;> simp [shortRoot, Root.idx]

theorem torH_dOf_mem_Bblock_iff [Finite K] [CharP K 2] [FiniteDimensional K A]
    (hreg : (polarBilin qA).Nondegenerate) (hζ : IsPrimitiveRoot ζ p) (ρ : Root) (v : Vec p) :
    torH K A 3 (dOf ζ v) ∈ Bblock qA ρ ↔ ∃ s : ZMod p, v = s • ρ.vecp p := by
  by_cases h : ρ.IsShort
  · rw [Bblock_short h, torH_dOf_mem_Bshort_iff hreg hζ, shortRoot_idx h]
  · rw [Bblock_long h]
    exact torH_dOf_mem_Blong_iff hζ h v

theorem Bblock_comm_torH [Finite K] [CharP K 2] [FiniteDimensional K A] (hK : ∃ u : Kˣ, u ≠ 1)
    (hreg : (polarBilin qA).Nondegenerate) (hζ : IsPrimitiveRoot ζ p) {ρ : Root} {v : Vec p}
    (hv : ρ.vecp p ⬝ᵥ v = 0) {g : ((Fin 3 ⊕ Fin 3 → K) × A) ≃ₗ[K] ((Fin 3 ⊕ Fin 3 → K) × A)}
    (hg : g ∈ Bblock qA ρ) : g * torH K A 3 (dOf ζ v) = torH K A 3 (dOf ζ v) * g := by
  by_cases h : ρ.IsShort
  · rw [Bblock_short h] at hg
    refine Bshort_comm_torH hK hreg le_rfl ?_ hg
    have h1 := (wt_eq_one_iff_short hζ ρ.idx v).2 (by rw [shortRoot_idx h]; exact hv)
    exact h1
  · rw [Bblock_long h] at hg
    exact Blong_comm_torH ((wt_eq_iff_long hζ h v).2 hv) hg

end Weights

section Classify

theorem long_cases : ∀ j j' : Fin 3 ⊕ Fin 3, coordIdx j ≠ coordIdx j' → ∃ ρ : Root, ¬ ρ.IsShort ∧
    ((j = lA ρ ∧ j' = lB ρ) ∨ (j = lB ρ ∧ j' = lA ρ) ∨ (j = (lB ρ).swap ∧ j' = (lA ρ).swap) ∨
      (j = (lA ρ).swap ∧ j' = (lB ρ).swap)) := by
  decide

section

variable [Finite K] [CharP K 2] [FiniteDimensional K A] {p : ℕ} [NeZero p] {ζ : Kˣ}

omit [Finite K] [FiniteDimensional K A] in
theorem rEl_block (hζ : IsPrimitiveRoot ζ p) {j j' : Fin 3 ⊕ Fin 3} (h : coordIdx j ≠ coordIdx j') :
    ∃ ρ : Root, (∀ t : K, rEl qA t j j' ∈ Bblock qA ρ) ∧
      (∀ v : Vec p, wt (dOf ζ v) j = wt (dOf ζ v) j' → ρ.vecp p ⬝ᵥ v = 0) := by
  obtain ⟨ρ, hρ, hc⟩ := long_cases j j' h
  have hab := lA_ne_lB hρ
  have hba : coordIdx (lB ρ) ≠ coordIdx (lA ρ) := hab.symm
  refine ⟨ρ, fun t => ?_, fun v hv => ?_⟩
  · rw [Bblock_long hρ]
    rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact rEl_mem_Blong_left t
    · exact rEl_mem_Blong_right t
    · rw [Blong_swap hab]
      exact rEl_mem_Blong_left t
    · rw [Blong_comm, Blong_swap hba]
      exact rEl_mem_Blong_left t
  · refine (wt_eq_iff_long hζ hρ v).1 ?_
    rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hv
    · exact hv.symm
    · rw [wt_swap, wt_swap] at hv
      exact (inv_inj.1 hv).symm
    · rw [wt_swap, wt_swap] at hv
      exact inv_inj.1 hv

theorem eichler_block (hreg : (polarBilin qA).Nondegenerate) (hζ : IsPrimitiveRoot ζ p) (j : Fin 3 ⊕ Fin 3) :
    ∃ ρ : Root, (∀ a : A, eichler (quadTail 3 qA) (hypVec K A j) ((0 : Fin 3 ⊕ Fin 3 → K), a) ∈ Bblock qA ρ) ∧
      (∀ v : Vec p, wt (dOf ζ v) j = 1 → ρ.vecp p ⬝ᵥ v = 0) := by
  refine ⟨shortRoot (coordIdx j), fun a => ?_, fun v hv => ?_⟩
  · rw [Bblock_short (shortRoot_isShort _), idx_shortRoot]
    exact eichler_tail_mem_Bshort hreg le_rfl a
  · rcases j with k | k
    · exact (wt_eq_one_iff_short hζ k v).1 hv
    · have h1 : wt (dOf ζ v) (Sum.inl k) = 1 := by
        have := wt_swap (dOf ζ v) (Sum.inl k)
        rw [Sum.swap_inl] at this
        rw [hv] at this
        exact (inv_eq_one.1 this.symm)
      exact (wt_eq_one_iff_short hζ k v).1 h1

end

end Classify

section Realize

variable {p : ℕ} [NeZero p] {ζ : Kˣ}

theorem dPerm_long (hζ : IsPrimitiveRoot ζ p) {ρ : Root} (h : ¬ ρ.IsShort) (v : Vec p) :
    dPerm (πab (lA ρ) (lB ρ)) (dOf ζ v) = dOf ζ (reflLin p ρ v) := by
  have hp : ζ ^ p = 1 := hζ.pow_eq_one
  funext k
  show wt (dOf ζ v) (πab (lA ρ) (lB ρ) (Sum.inl k)) = zpowE p ζ (reflLin p ρ v k)
  rw [reflLin_apply_coord]
  cases ρ <;> simp only [Root.IsShort, not_true_eq_false] at h <;> fin_cases k <;>
    simp [πab, lA, lB, Equiv.swap_apply_def, wt_dOf_inl, wt_dOf_inr hp, dotProduct, Fin.sum_univ_three,
      Root.vecp, Root.vec, Root.corp, Root.cor]

theorem dPerm_short (hζ : IsPrimitiveRoot ζ p) (k : Fin 3) (v : Vec p) :
    dPerm (Equiv.swap (Sum.inl k) (Sum.inr k)) (dOf ζ v) = dOf ζ (reflLin p (shortRoot k) v) := by
  have hp : ζ ^ p = 1 := hζ.pow_eq_one
  funext k'
  show wt (dOf ζ v) (Equiv.swap (Sum.inl k) (Sum.inr k) (Sum.inl k')) = zpowE p ζ (reflLin p (shortRoot k) v k')
  rw [reflLin_apply_coord]
  fin_cases k <;> fin_cases k' <;>
    simp [shortRoot, Equiv.swap_apply_def, wt_dOf_inl, wt_dOf_inr hp, dotProduct, Fin.sum_univ_three,
      Root.vecp, Root.vec, Root.corp, Root.cor]
  all_goals (congr 1; ring)

section

variable [Finite K] [CharP K 2] [FiniteDimensional K A]

theorem exists_realize (hreg : (polarBilin qA).Nondegenerate) (hani : qA.Anisotropic) (hdim : finrank K A = 2)
    (hζ : IsPrimitiveRoot ζ p) (ρ : Root) :
    ∃ n : ((Fin 3 ⊕ Fin 3 → K) × A) ≃ₗ[K] ((Fin 3 ⊕ Fin 3 → K) × A), n ∈ Om qA 3 ∧ n * n = 1 ∧
      ∀ v : Vec p, n * torH K A 3 (dOf ζ v) * n = torH K A 3 (dOf ζ (reflLin p ρ v)) := by
  by_cases h : ρ.IsShort
  · obtain ⟨a₀, ha₀⟩ : ∃ a₀ : A, a₀ ≠ 0 := by
      have : 0 < finrank K A := by omega
      exact Module.finrank_pos_iff_exists_ne_zero.1 this
    refine ⟨mW qA ρ.idx a₀, ?_, mW_mul_self hani ha₀ _, fun v => ?_⟩
    · rw [Om_eq_elementary hreg le_rfl]
      exact shortWeyl_mem _ _
    · rw [conj_mW hani ha₀, dPerm_short hζ, shortRoot_idx h]
  · refine ⟨nW (K := K) (A := A) (lA_ne_lB h), ?_, nW_mul_self _, fun v => ?_⟩
    · exact Blong_le_Om hreg le_rfl (PhiH_mem_Blong (qA := qA) (lA_ne_lB h) (wSL K))
    · rw [conj_nW, dPerm_long hζ h]

end

end Realize

end CFSG.RankThree.PartOne.K159H
