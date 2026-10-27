module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmPlusCurtis
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmPlusFamRep
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmPlusFourRank
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmPlusFourTwist

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin CFSG.Quasithin.SmithCurtis

variable {F : Type} [Field F] [Finite F] [CharP F 2]

private theorem w135c2_omfP8_mu_eq_indicator (hF : Nat.card F = 2)
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) (spinGroup (quadPlus 4 F)) V} {y₀ : V}
    {χ : spinGroup (quadPlus 4 F) → ZMod 2} {μ : Fin 4 → ZMod 2}
    (ht : (omPlusCurtisDatum 4 F (by norm_num)).IsCurtisType ρ y₀ χ μ) {h : Fin 4}
    (hJ : ∀ i : Fin 4, μ i = (omPlusCurtisDatum 4 F (by norm_num)).dScalar χ i ↔ i = h) :
    ∀ s : Fin 4, μ s = if s = h then 1 else 0 := by
  intro s
  have hn3 : 3 ≤ 4 := by norm_num
  have hχ : χ 1 = 1 := ht.chi_one
  have hds : (omPlusCurtisDatum 4 F (by norm_num)).dScalar χ s = 1 :=
    omPlusCurtisDatum_two_dScalar (K := F) hF hn3 hχ s
  have hds' : (omPlusCurtisDatum 4 F (by norm_num)).d'Scalar χ s = 1 :=
    omPlusCurtisDatum_two_d'Scalar (K := F) hF hn3 hχ s
  rcases ht.mu_eq s with h0 | h1
  · rw [h0]
    by_cases hs : s = h
    · exact absurd ((hJ s).mpr hs) (by rw [h0, hds]; exact zero_ne_one)
    · rw [if_neg hs]
  · have hs : s = h := (hJ s).mp (by rw [h1, hds', hds])
    rw [h1, hds', if_pos hs]

theorem omPlus8_two_halfSpin_natural (hF : Nat.card F = 2) {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] {ρ : Representation (ZMod 2) (spinGroup (quadPlus 4 F)) V}
    (hρ : IsSimpleRep ρ) {y₀ : V} {χ : spinGroup (quadPlus 4 F) → ZMod 2} {μ : Fin 4 → ZMod 2}
    (ht : (omPlusCurtisDatum 4 F (by norm_num)).IsCurtisType ρ y₀ χ μ) {h : Fin 4}
    (hh : 2 ≤ h.val) (hμ : ∀ s, μ s = if s = h then 1 else 0) :
    ∃ (θ : MulAut (spinGroup (quadPlus 4 F))) (β : V ≃+ (Fin 4 ⊕ Fin 4 → F)),
      ∀ (g : spinGroup (quadPlus 4 F)) (v : V),
        β (ρ g v) = spinAction (quadPlus 4 F) (θ g) (β v) := by
  let D := omPlusCurtisDatum 4 F (by norm_num)
  have hn3 : 3 ≤ 4 := by norm_num
  have hχ : χ 1 = 1 := ht.chi_one
  have hds : ∀ i : Fin 4, D.dScalar χ i = 1 := fun i =>
    omPlusCurtisDatum_two_dScalar (K := F) hF hn3 hχ i
  have hJ : ∀ i : Fin 4, μ i = D.dScalar χ i ↔ i = h := by
    intro i
    constructor
    · intro hi
      by_contra hih
      have h0 : μ i = 0 := by rw [hμ i, if_neg hih]
      rw [h0, hds i] at hi
      exact absurd hi zero_ne_one
    · intro hi
      rw [hi, hμ h, if_pos rfl, hds h]
  have hi0 : h.val ≠ 1 := by omega
  obtain ⟨γ, χ', μ', ht', hJ'⟩ := exists_twist_node_zero ht hi0 hJ
  have hρ' : IsSimpleRep (ρ.comp γ.toMonoidHom) := isSimpleRep_comp_mulEquiv hρ γ
  have hμ' : μ' = fun s : Fin 4 => if s.val = 0 then 1 else 0 := by
    have hind : ∀ s : Fin 4, μ' s = if s = 0 then 1 else 0 :=
      w135c2_omfP8_mu_eq_indicator hF ht' (fun i => (hJ' i).trans Fin.val_eq_zero_iff)
    funext s
    rw [hind s]
    exact if_congr Fin.val_eq_zero_iff.symm rfl rfl
  rw [hμ'] at ht'
  obtain ⟨β, hβ⟩ := omPlus_two_natural_of_isCurtisType hF hn3 hρ' ht'
  refine ⟨γ.symm, β, fun g v => ?_⟩
  have h := hβ (γ.symm g) v
  simpa using h

private theorem w135c2_omfP8_natural_of_unique_node (hF : Nat.card F = 2)
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) (spinGroup (quadPlus 4 F)) V} (hρ : IsSimpleRep ρ)
    {y₀ : V} {χ : spinGroup (quadPlus 4 F) → ZMod 2} {μ : Fin 4 → ZMod 2}
    (ht : (omPlusCurtisDatum 4 F (by norm_num)).IsCurtisType ρ y₀ χ μ) {i0 : Fin 4}
    (hJ : ∀ i : Fin 4, μ i = (omPlusCurtisDatum 4 F (by norm_num)).dScalar χ i ↔ i = i0)
    (hi01 : i0.val ≠ 1) :
    ∃ (θ : MulAut (spinGroup (quadPlus 4 F))) (β : V ≃+ (Fin 4 ⊕ Fin 4 → F)),
      ∀ (g : spinGroup (quadPlus 4 F)) (v : V),
        β (ρ g v) = spinAction (quadPlus 4 F) (θ g) (β v) := by
  by_cases hi00 : i0.val = 0
  · have hμeq : μ = fun s : Fin 4 => if s.val = 0 then 1 else 0 := by
      have hind : ∀ s : Fin 4, μ s = if s = i0 then 1 else 0 :=
        w135c2_omfP8_mu_eq_indicator hF ht hJ
      funext s
      rw [hind s]
      exact if_congr ⟨fun h => by rw [h, hi00], fun h => Fin.ext (by rw [h, hi00])⟩
        rfl rfl
    rw [hμeq] at ht
    obtain ⟨β, hβ⟩ := omPlus_two_natural_of_isCurtisType hF (by norm_num) hρ ht
    exact ⟨MulEquiv.refl _, β, fun g v => by simpa using hβ g v⟩
  · have hμ : ∀ s : Fin 4, μ s = if s = i0 then 1 else 0 :=
      w135c2_omfP8_mu_eq_indicator hF ht hJ
    exact omPlus8_two_halfSpin_natural (h := i0) hF hρ ht (by omega) hμ

private theorem w135c2_omfP8_natural_or_four_le_curtis (hF : Nat.card F = 2)
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
    {ρ : Representation (ZMod 2) (spinGroup (quadPlus 4 F)) V} (hρ : IsSimpleRep ρ)
    {y₀ : V} {χ : spinGroup (quadPlus 4 F) → ZMod 2} {μ : Fin 4 → ZMod 2}
    (ht : (omPlusCurtisDatum 4 F (by norm_num)).IsCurtisType ρ y₀ χ μ)
    {y : spinGroup (quadPlus 4 F)} (hy : y * y = 1) (hy1 : y ≠ 1) (hρy : ρ y ≠ 1) :
    (∃ (θ : MulAut (spinGroup (quadPlus 4 F))) (β : V ≃+ (Fin 4 ⊕ Fin 4 → F)),
      ∀ (g : spinGroup (quadPlus 4 F)) (v : V),
        β (ρ g v) = spinAction (quadPlus 4 F) (θ g) (β v)) ∨
      4 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ y - 1)) := by
  let D := omPlusCurtisDatum 4 F (by norm_num)
  by_cases h1 : μ 1 = D.dScalar χ 1
  · right
    exact omq_omPlus_four_le_rank_of_node_one hρ ht h1 hy hy1
  · by_cases hpair : ∃ i j : Fin 4, i ≠ j ∧ i.val ≠ 1 ∧ j.val ≠ 1 ∧
        μ i = D.dScalar χ i ∧ μ j = D.dScalar χ j
    · right
      obtain ⟨i, j, hij, hi, hj, hsi, hsj⟩ := hpair
      exact omq_omPlus_four_le_rank_of_pair hρ ht hij hi hj hsi hsj hy hy1
    · obtain ⟨i0, hi0⟩ := omq_omPlus_exists_separating (by norm_num) hρ ht hρy
      have hi01 : i0.val ≠ 1 := fun hiv => h1 (by
        have hie : i0 = 1 := Fin.ext (by simpa using hiv)
        rw [← hie]
        exact hi0)
      have huniq : ∀ j : Fin 4, μ j = D.dScalar χ j → j = i0 := by
        intro j hj
        by_contra hji
        have hj1 : j.val ≠ 1 := fun hjv => h1 (by
          have hje : j = 1 := Fin.ext (by simpa using hjv)
          rw [← hje]
          exact hj)
        exact hpair ⟨j, i0, hji, hj1, hi01, hj, hi0⟩
      have hJ : ∀ i : Fin 4, μ i = D.dScalar χ i ↔ i = i0 :=
        fun i => ⟨fun hi => huniq i hi, fun hi => by rw [hi]; exact hi0⟩
      exact Or.inl (w135c2_omfP8_natural_of_unique_node hF hρ ht hJ hi01)

theorem omPlus8_two_natural_or_four_le (hF : Nat.card F = 2) {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
    {ρ : Representation (ZMod 2) (spinGroup (quadPlus 4 F)) V} (hρ : IsSimpleRep ρ)
    {y : spinGroup (quadPlus 4 F)} (hy : y * y = 1) (hρy : ρ y ≠ 1) :
    (∃ (θ : MulAut (spinGroup (quadPlus 4 F))) (β : V ≃+ (Fin 4 ⊕ Fin 4 → F)),
      ∀ (g : spinGroup (quadPlus 4 F)) (v : V),
        β (ρ g v) = spinAction (quadPlus 4 F) (θ g) (β v)) ∨
      4 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ y - 1)) := by
  have hn3 : 3 ≤ 4 := by norm_num
  let D := omPlusCurtisDatum 4 F hn3
  have hy1 : y ≠ 1 := fun h => hρy (by rw [h, map_one])
  have hsplit : SplitOver (ZMod 2) D.H :=
    omPlusCurtisDatum_two_splitOver (k := ZMod 2) (n := 4) (K := F) hF hn3
  have : Finite (CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartanD 4)).Group :=
    CFSG.LieType.RootSystem.finite_group (isFiniteType_cartanD 4)
  obtain ⟨y₀, χ, μ, ht⟩ := D.exists_isCurtisType hsplit hρ
  exact w135c2_omfP8_natural_or_four_le_curtis hF hρ ht hy hy1 hρy

end CFSG.LocalAnalysis.WeakClosure81
