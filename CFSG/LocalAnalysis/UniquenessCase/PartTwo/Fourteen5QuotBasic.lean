module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen4Aux
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

section Quotient

variable {B : Type} [Group B] [Finite B] {N : Subgroup B} [N.Normal]

theorem normalizer_map_mk'_le_of_coprime {p : ℕ} [Fact p.Prime] {A : Subgroup B}
    (hA : IsPGroup p A) (hpN : ¬ p ∣ Nat.card N) :
    normalizer ((A.map (QuotientGroup.mk' N) : Subgroup (B ⧸ N)) : Set (B ⧸ N)) ≤
      (normalizer (A : Set B)).map (QuotientGroup.mk' N) := by
  haveI : Fact (IsPGroup p (↥A)) := ⟨hA⟩
  have hcop : Nat.Coprime p (Nat.card N) :=
    (Nat.Prime.coprime_iff_not_dvd Fact.out).2 hpN
  exact (CFSG.normalizer_map_quotient_eq_map_normalizer p A N inferInstance hcop).le

theorem isSylowOf_map_mk' {p : ℕ} [Fact p.Prime] {A C : Subgroup B}
    (h : CFSG.ABGLocalTools.IsSylowOf p A C) :
    CFSG.ABGLocalTools.IsSylowOf p (A.map (QuotientGroup.mk' N)) (C.map (QuotientGroup.mk' N)) := by
  obtain ⟨Q, rfl⟩ := h
  refine ⟨Q.mapSurjective (f := (QuotientGroup.mk' N).subgroupMap C)
    ((QuotientGroup.mk' N).subgroupMap_surjective C), ?_⟩
  rw [Sylow.coe_mapSurjective, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem eq_bot_of_normal_of_not_dvd {p : ℕ} [Fact p.Prime]
    (hN : ∀ U : Subgroup B, U.Normal → ¬ p ∣ Nat.card U → U ≤ N) (hpN : ¬ p ∣ Nat.card N)
    {U : Subgroup (B ⧸ N)} (hU : U.Normal) (hpU : ¬ p ∣ Nat.card U) : U = ⊥ := by
  let f : B →* B ⧸ N := QuotientGroup.mk' N
  let V : Subgroup B := U.comap f
  have hVN : V.Normal := hU.comap f
  have hNV : N ≤ V := by
    intro x hx
    show f x ∈ U
    rw [show f x = 1 from (QuotientGroup.eq_one_iff x).2 hx]
    exact U.one_mem
  let φ : ↥V →* ↥U :=
    { toFun := fun x => ⟨f x, x.2⟩
      map_one' := Subtype.ext (map_one f)
      map_mul' := fun x y => Subtype.ext (map_mul f (x : B) (y : B)) }
  have hker : φ.ker = N.subgroupOf V := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact Subtype.ext_iff.trans (QuotientGroup.eq_one_iff (x : B))
  have hsurj : Function.Surjective φ := by
    intro u
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective N (u : B ⧸ N)
    refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
    change (QuotientGroup.mk' N x) ∈ U
    rw [hx]
    exact u.2
  have hq : Nat.card (↥V ⧸ N.subgroupOf V) = Nat.card U := by
    rw [← hker]
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv,
      MonoidHom.range_eq_top.2 hsurj, Subgroup.card_top]
  have hcardV : Nat.card V = Nat.card U * Nat.card N := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf V), hq,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNV).toEquiv]
  have hVnot : ¬ p ∣ Nat.card V := by
    rw [hcardV]
    exact Nat.Prime.not_dvd_mul Fact.out hpU hpN
  have hVle : V ≤ N := hN V hVN hVnot
  have hmap : V.map f = U :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) U
  exact le_bot_iff.mp (calc U = V.map f := hmap.symm
    _ ≤ N.map f := Subgroup.map_mono hVle
    _ = ⊥ := QuotientGroup.map_mk'_self N)

end Quotient

namespace Fourteen5

variable {G : Type} [Group G] [Finite G] (H : Subgroup G)

@[expose] noncomputable def core : Subgroup ↥H :=
  (rankThreePrimeCore 3 H).subgroupOf H

instance core_normal : (core H).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (rankThreePrimeCore_facts H).1).2
    (rankThreePrimeCore_facts H).2.1

abbrev HStar : Type :=
  ↥H ⧸ core H

@[expose] noncomputable def star (A : Subgroup G) : Subgroup (HStar H) :=
  (A.subgroupOf H).map (QuotientGroup.mk' (core H))

end Fourteen5

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
