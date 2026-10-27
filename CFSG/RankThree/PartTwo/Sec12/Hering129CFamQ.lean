module

public import CFSG.RankThree.PartTwo.Sec12.Hering129CFam0

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace Hering129C

section Quot

variable {Q Lb : Type} [Group Q] [Finite Q] [Group Lb] {c a : Q} {I X : Subgroup Q}
  {f : ↥I →* Lb}

theorem ppair_of_census_quot (hD : Census129 c a I X f) (N : Subgroup Q) [N.Normal]
    (hN : N ≤ Subgroup.center Q) :
    ∃ (J : Subgroup (Q ⧸ N)) (g : ↥J →* Lb), PPair (QuotientGroup.mk' N c) J g := by
  have h0 : PPair c I f := ppair_self hD
  have hinj : Set.InjOn (QuotientGroup.mk' N) I := by
    intro x hx y hy hxy
    have h1 : x⁻¹ * y ∈ N := QuotientGroup.eq.mp hxy
    have h2 : x⁻¹ * y ∈ I ⊓ Subgroup.center Q := ⟨I.mul_mem (I.inv_mem hx) hy, hN h1⟩
    rw [inf_center_eq_bot hD, Subgroup.mem_bot] at h2
    exact inv_mul_eq_one.mp h2
  have hs1 : QuotientGroup.mk' N c ≠ 1 := fun h =>
    c_not_mem_center hD (hN ((QuotientGroup.eq_one_iff c).mp h))
  obtain ⟨g, hg⟩ := h0.of_injOn _ hinj hs1
  exact ⟨_, g, hg⟩

end Quot

section Ext

variable {X Y : Type} [Group X] [Group Y]

theorem isExtOf_normal_le_center (hX : CFSG.IsQuasisimple X)
    (h : Sec4.IsExtOf X Y (Multiplicative (ZMod 3))) :
    ∃ (N : Subgroup X) (_ : N.Normal), N ≤ Subgroup.center X ∧ Nonempty (X ⧸ N ≃* Y) := by
  obtain ⟨K, hKn, ⟨eK⟩, ⟨eQ⟩⟩ := h
  have hK3 : Nat.card K = 3 := by
    rw [Nat.card_congr eK.toEquiv, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
      ZMod.card]
  refine ⟨K, hKn, ?_, ⟨eQ⟩⟩
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hX hKn with h | h
  · exfalso
    have hX3 : Nat.card X = 3 := by
      rw [← Subgroup.card_top (G := X), ← h, hK3]
    have hcyc : IsCyclic X := isCyclic_of_prime_card hX3
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    have hcomm : ∀ x y : X, x * y = y * x := fun x y => by
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg x)
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg y)
      exact zpow_mul_comm g m n
    obtain ⟨a, b, hab⟩ := hX.2.2
    induction a using QuotientGroup.induction_on with
    | H x =>
      induction b using QuotientGroup.induction_on with
      | H y => exact hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hcomm])
  · exact h

end Ext

section FromExt

variable {Q Lb : Type} [Group Q] [Finite Q] [Group Lb] {c a : Q} {I X : Subgroup Q}
  {f : ↥I →* Lb}

theorem ppair_of_census_ext (hD : Census129 c a I X f) {Y : Type} [Group Y]
    (h : Sec4.IsExtOf Q Y (Multiplicative (ZMod 3))) :
    ∃ (s : Y) (J : Subgroup Y) (g : ↥J →* Lb), PPair s J g := by
  obtain ⟨N, hN, hNz, ⟨eQ⟩⟩ := isExtOf_normal_le_center hD.quasisimple h
  obtain ⟨J, g, hg⟩ := ppair_of_census_quot hD N hNz
  obtain ⟨g', hg'⟩ := hg.map eQ
  exact ⟨_, _, g', hg'⟩

theorem finite_of_isExtOf {Y : Type} [Group Y] (h : Sec4.IsExtOf Q Y (Multiplicative (ZMod 3))) :
    Finite Y := by
  obtain ⟨K, hKn, -, ⟨eQ⟩⟩ := h
  exact Finite.of_equiv (Q ⧸ K) eQ.toEquiv

end FromExt

end Hering129C

end CFSG.RankThree.PartTwo.Sec12
