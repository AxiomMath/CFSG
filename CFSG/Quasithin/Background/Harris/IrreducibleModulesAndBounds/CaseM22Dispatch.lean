module

public import CFSG.Quasithin.Background.Harris.OrdinaryProofs.CentralizerOdd
public import CFSG.LocalAnalysis.SectionRank.SporadicCover
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Blueprint

theorem m22_center_card_odd_cases {L : Type*} [Group L] [Finite L]
    [Group.IsPerfect L] (hodd : Odd (Nat.card (Subgroup.center L)))
    (e : (L ⧸ Subgroup.center L) ≃* NativeSporadic.Carrier .M22) :
    Nat.card (Subgroup.center L) = 1 ∨ Nat.card (Subgroup.center L) = 3 := by
  have : Finite (NativeSporadic.Carrier .M22) := Finite.of_equiv _ e.toEquiv
  let π : L →* NativeSporadic.Carrier .M22 :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center L := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hC : π.ker ≤ Subgroup.center L := hker.le
  have hodd' : Odd (Nat.card π.ker) := by rw [hker]; exact hodd
  have hcard : Nat.card (NativeSporadic.Carrier .M22) = 443520 :=
    CFSG.Sporadic.Mathieu.card_M22
  obtain ⟨h27, hr⟩ := CFSG.SectionRank.small_sporadic_order_conditions
    (n := Nat.card (NativeSporadic.Carrier .M22)) (by rw [hcard]; exact Or.inr (Or.inl rfl))
  have := (CFSG.SectionRank.odd_cover_one_square_order_bound Nat.prime_three (by norm_num) π hπ hC
    hodd' h27 hr).1
  rwa [hker] at this

theorem odd_card_center_of_irr' {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {L : Subgroup (GLV V)} (hL : IsIrr L ⊤) : Odd (Nat.card (Subgroup.center ↥L)) := by
  have hodd := OrdinaryProofs.centralizer_card_odd hL
  have hle : (Subgroup.center ↥L).map L.subtype ≤ Subgroup.centralizer (L : Set (GLV V)) := by
    rintro _ ⟨z, hz, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have := congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨g, hg⟩)
    simpa using this
  have hdvd : Nat.card ((Subgroup.center ↥L).map L.subtype) ∣
      Nat.card (Subgroup.centralizer (L : Set (GLV V))) := Subgroup.card_dvd_of_le hle
  rw [Subgroup.card_map_of_injective L.subtype_injective] at hdvd
  exact hodd.of_dvd_nat hdvd

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

end CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds
