module

public import CFSG.LocalAnalysis.StandardType.GGNsFrameCompWit

public section

namespace CFSG.StandardType

namespace NsFrameComp

open Matrix Module Polynomial CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LinearGroups SUTB NoOffOm CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.OddIso Multiplicative

theorem card_le_of_supp {G : Type} [Group G] {r p : ℕ} [NeZero p]
    (ψ : Multiplicative (Fin r → ZMod p) →* G) {H : Subgroup G} (T : Finset (Fin r))
    (hH : ∀ z ∈ H, ∃ s, ψ s = z ∧ ∀ i ∉ T, toAdd s i = 0) : Nat.card H ≤ p ^ T.card := by
  classical
  choose σ hσ using fun z : H => hH z z.2
  let F : H → (T → ZMod p) := fun z i => toAdd (σ z) i
  have hF : Function.Injective F := by
    intro z z' hzz'
    have hs : σ z = σ z' := by
      apply toAdd.injective
      funext i
      by_cases hi : i ∈ T
      · exact congrFun hzz' ⟨i, hi⟩
      · rw [(hσ z).2 i hi, (hσ z').2 i hi]
    apply Subtype.ext
    rw [← (hσ z).1, ← (hσ z').1, hs]
  have h1 := Nat.card_le_card_of_injective F hF
  rwa [Nat.card_fun, Nat.card_zmod, Nat.card_eq_finsetCard] at h1

variable {f n : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K} {p : ℕ}
  {A : Subgroup ↥(unitarySU 2 f K n)}

local notation "Xe" x:max => ((toUnitHom x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
  Module.End K (Fin n → K))

theorem eq_one_of_smul_on (hp : p.Prime) (hpq : ¬ p ∣ 2 ^ f + 1) {c : ↥(unitarySU 2 f K n)}
    (hcp : c ^ p = 1) {U : Submodule K (Fin n → K)} (hU : NondegOn (stdHermForm h n) U)
    (hU0 : U ≠ ⊥) {l : K} (hl : ∀ u ∈ U, lin c u = l • u) : l = 1 := by
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
  obtain ⟨w, hw, hwu⟩ : ∃ w ∈ U, stdHermForm h n w u ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hu0 (hU u hu hcon)
  have hpow : ∀ k : ℕ, lin (c ^ k) u = l ^ k • u := by
    intro k
    induction k with
    | zero => rw [pow_zero, lin_one, pow_zero, one_smul]; rfl
    | succ k ih =>
      rw [pow_succ', lin_mul, Module.End.mul_apply, ih, map_smul, hl u hu, smul_smul, pow_succ]
  have hlp : l ^ p = 1 := by
    have h2 := hpow p
    rw [hcp, lin_one, Module.End.one_apply] at h2
    have h3 : (l ^ p - 1) • u = 0 := by rw [sub_smul, ← h2, one_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hu0)
  have hlq : l ^ (2 ^ f + 1) = 1 := by
    have h2 := isometry_lin h c w u
    rw [hl w hw, hl u hu, LinearMap.map_smulₛₗ₂, LinearMap.map_smul, smul_eq_mul, smul_eq_mul,
      ← mul_assoc] at h2
    have h3 : h.bar l * l = 1 := by
      have h4 : (h.bar l * l - 1) * stdHermForm h n w u = 0 := by
        rw [sub_mul, h2, one_mul, sub_self]
      exact sub_eq_zero.mp ((mul_eq_zero.mp h4).resolve_right hwu)
    rw [UnitaryFieldData.bar_apply] at h3
    rw [pow_succ]
    exact h3
  have hcop : p.gcd (2 ^ f + 1) = 1 := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpq
  have h5 := pow_gcd_eq_one.mpr ⟨hlp, hlq⟩
  rwa [hcop, pow_one] at h5

theorem exists_comp_card_le [Finite K] (hA : MaxElemAb p A) (F : PieceFrame f n K h p A)
    {G : Type} [Group G] {φ : ↥(unitarySU 2 f K n) →* G} (hker : SURep.GGFrameKer φ)
    (hr : 4 ≤ F.r) {t : Fin F.r → ZMod p} (ht2 : (supp t).card ≤ 2) :
    ∃ L₂ : Subgroup G, CFSG.Assembly.IsComponentOf L₂
        (φ.range ⊓ Subgroup.centralizer {φ (F.ι (ofAdd t))}) ∧
      Nat.card ((φ.comp F.ι).range ⊓ Subgroup.centralizer (L₂ : Set G) : Subgroup G) ≤
        p ^ 2 := by
  classical
  have hp := hA.prime
  have : NeZero p := ⟨hp.ne_zero⟩
  have hιA : ∀ s, F.ι s ∈ A := fun s => by
    have h1 : F.ι s ∈ F.ι.range := ⟨s, rfl⟩
    rwa [F.ι_range] at h1
  set e := F.ι (ofAdd t) with he
  have heA : e ∈ A := hιA _
  have hep : e ^ p = 1 := hA.pow e heA
  have hcompl : 2 ≤ ((supp t)ᶜ).card := by rw [Finset.card_compl, Fintype.card_fin]; omega
  obtain ⟨k, hk, l, hl, hkl⟩ := Finset.one_lt_card.mp (by omega : 1 < ((supp t)ᶜ).card)
  have hzero : ∀ m, m ∈ (supp t)ᶜ → t m = 0 := fun m hm => by
    rw [Finset.mem_compl, mem_supp] at hm
    exact not_not.mp hm
  have hfixU : ∀ m, t m = 0 → ∀ u ∈ rng (F.y m), lin e u = u := by
    intro m hm u hu
    rw [he, F.ι_on _ m u hu, toAdd_ofAdd, hm, ZMod.val_zero, pow_zero, lin_one]
    rfl
  set Vf := primaryComponent (Xe e) (X - C 1) with hVf
  have hmemVf : ∀ v, v ∈ Vf ↔ lin e v = v := by
    intro v
    rw [hVf, primaryComponent_X_sub_C_one, LinearMap.mem_ker, LinearMap.sub_apply,
      Module.End.one_apply, sub_eq_zero]
    rfl
  have hUk : rng (F.y k) ≤ Vf := fun u hu => (hmemVf u).mpr (hfixU k (hzero k hk) u hu)
  have hUl : rng (F.y l) ≤ Vf := fun u hu => (hmemVf u).mpr (hfixU l (hzero l hl) u hu)
  have hdim : 4 ≤ finrank K Vf := by
    have hinf : rng (F.y k) ⊓ rng (F.y l) = ⊥ := by
      exact (Submodule.eq_bot_iff _).mpr fun v hv =>
        F.nondeg hA k v hv.1 fun m hm => F.orth k l hkl m hm v hv.2
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (rng (F.y k)) (rng (F.y l))
    rw [hinf, finrank_bot, add_zero] at h1
    have h2 := two_le_finrank_rng h hA (F.y_mem k) (F.y_ne_one k)
    have h3 := two_le_finrank_rng h hA (F.y_mem l) (F.y_ne_one l)
    have h4 := Submodule.finrank_mono (sup_le hUk hUl)
    omega
  have hmem : (X - C 1 : K[X]) ∈ primaryFactors (Xe e) := by
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (F.ne_bot k)
    exact mem_primaryFactors_of_ker (irreducible_X_sub_C 1) (monic_X_sub_C 1) hu0
      (mem_primaryComponent.mp (hUk hu))
  have hmult : primaryMultiplicity (Xe e) (X - C 1) = finrank K Vf :=
    primaryMultiplicity_X_sub_C_one _
  have hgood : IsGoodBlock h (toUnitHom e) ⟨X - C 1, hmem⟩ := by
    refine isGoodBlock_X_sub_C_one hmem (by omega) ?_
    rw [hmult]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq, not_or]
    exact ⟨fun h' => by have := h'.1; omega, fun h' => by have := h'.1; omega,
      fun h' => by have := h'.1; omega⟩
  refine ⟨(sb h e (X - C 1)).map φ,
    isComponentOf_map_sb hker hp hA.ne_two hA.not_dvd hep ⟨X - C 1, hmem⟩ hgood, ?_⟩
  refine (card_le_of_supp (φ.comp F.ι) (supp t) fun z hz => ?_).trans
    (Nat.pow_le_pow_right hp.pos ht2)
  obtain ⟨⟨s, rfl⟩, hzc⟩ := hz
  refine ⟨s, rfl, fun i hi => ?_⟩
  have hsC : F.ι s ∈ Subgroup.centralizer {e} := mem_centralizer_of_mem hA heA (hιA s)
  have hcomm := commute_of_map_commute hker hp hA.ne_two hep ⟨X - C 1, hmem⟩ hgood
    (y := F.ι s) fun g hg => (Subgroup.mem_centralizer_iff.mp hzc (φ g) ⟨g, hg, rfl⟩).symm
  obtain ⟨c, hc⟩ := exists_smul_of_commute_sb hp hA.ne_two hep ⟨X - C 1, hmem⟩ hgood hsC hcomm
  obtain ⟨c₀, rfl⟩ := exists_algebraMap_eq c
  have hsc : ∀ v ∈ Vf, lin (F.ι s) v = c₀ • v := fun v hv => by
    have := hc ⟨v, hv⟩
    rwa [coe_algebraMap_smul_primaryComponent] at this
  have hc₀ : c₀ = 1 := eq_one_of_smul_on hp hA.not_dvd (hA.pow _ (hιA s)) (F.nondeg hA k)
    (F.ne_bot k) fun u hu => hsc u (hUk hu)
  have hti : t i = 0 := hzero i (Finset.mem_compl.mpr hi)
  exact F.coord_eq_zero hA fun u hu => by
    rw [hsc u ((hmemVf u).mpr (hfixU i hti u hu)), hc₀, one_smul]

end NsFrameComp

end CFSG.StandardType
