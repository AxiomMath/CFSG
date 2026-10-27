module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148HCensus

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148H

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped Pointwise

section Card

theorem card_X {X : Type} [Group X] [Finite X]
    (hT : Sec4.IsTripleCover X CFSG.Blueprint.NativeSporadic.ON) :
    Nat.card X = 1382446517760 := by
  obtain ⟨hZ, ⟨e⟩⟩ := hT
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X),
    Nat.card_congr e.toEquiv, CFSG.Sporadic.ON.card_ON, hZ]

end Card

section TwoRank

theorem olRow_of_E16 (S : Type) [Group S]
    (hE : ∃ E : Subgroup S, CFSG.Assembly.IsElemAbelian 2 E ∧ Nat.card E = 16) :
    OLRow (fun T _ => Nonempty (T ≃* S)) := by
  intro X _ _ P L Q hcfg ⟨e⟩
  obtain ⟨E, hE, hE16⟩ := hE
  set f : S →* X := L.subtype.comp e.symm.toMonoidHom with hf
  have hinj : Function.Injective f := L.subtype_injective.comp e.symm.injective
  have hEX : CFSG.Assembly.IsElemAbelian 2 (E.map f) := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨u, hu, hux⟩ := Subgroup.mem_map.mp x.2
      obtain ⟨v, hv, hvy⟩ := Subgroup.mem_map.mp y.2
      apply Subtype.ext
      change (x : X) * y = y * x
      rw [← hux, ← hvy, ← map_mul, ← map_mul]
      exact congrArg f (congrArg Subtype.val (hE.1.is_comm.comm (⟨u, hu⟩ : E) ⟨v, hv⟩))
    · obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
      rw [← map_pow, hE.2 u hu, map_one]
  have h8 := card_le_eight_of_isTripleCover hcfg.triple _ hEX
  rw [Subgroup.card_map_of_injective hinj, hE16] at h8
  omega

end TwoRank

section ThreeON

theorem isElemAbelian_of_isPGroup_ON {T : Subgroup CFSG.Blueprint.NativeSporadic.ON}
    (hT : IsPGroup 3 T) : CFSG.Assembly.IsElemAbelian 3 T := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E, hE, hEc⟩ := CFSG.SectionRank.ON_elementary_three_rank_four
  have hEc' : Nat.card E = 3 ^ (Nat.card CFSG.Blueprint.NativeSporadic.ON).factorization 3 := by
    rw [hEc, CFSG.RankThree.Native.factorization_card_ON]
  let Q : Sylow 3 CFSG.Blueprint.NativeSporadic.ON := Sylow.ofCard E hEc'
  have hQ : (Q : Subgroup _) = E := rfl
  obtain ⟨S, hS⟩ := hT.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq CFSG.Blueprint.NativeSporadic.ON Q S
  have hSg : (S : Subgroup CFSG.Blueprint.NativeSporadic.ON) = MulAut.conj g • E := by
    rw [← hg, Sylow.coe_subgroup_smul, hQ]
  have key : ∀ m ∈ T, ∃ x ∈ E, m = g * x * g⁻¹ := by
    intro m hm
    have hm' := hS hm
    rw [hSg] at hm'
    obtain ⟨x, hx, hxm⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).1 hm'
    refine ⟨x, hx, ?_⟩
    rw [← hxm, MulAut.smul_def, MulAut.conj_apply]
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    intro x hx y hy
    have h := congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    rwa [Subgroup.coe_mul, Subgroup.coe_mul] at h
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun a ha => ?_⟩
  · obtain ⟨x, hx, hxa⟩ := key a a.2
    obtain ⟨y, hy, hyb⟩ := key b b.2
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hxa, hyb]
    calc g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ := by group
      _ = g * (y * x) * g⁻¹ := by rw [hEcomm x hx y hy]
      _ = g * y * g⁻¹ * (g * x * g⁻¹) := by group
  · obtain ⟨x, hx, rfl⟩ := key a ha
    have h3 : x ^ 3 = 1 := hE.2 x hx
    rw [conj_pow, h3, mul_one, mul_inv_cancel]

end ThreeON

section ThreeX

theorem injective_comp_of_ker_le {X H : Type} [Group X] [Group H] {f : X →* H}
    (hf : f.ker ≤ Subgroup.center X) {L : Subgroup X} (hL : L ⊓ Subgroup.center X = ⊥) :
    Function.Injective (f.comp L.subtype) := by
  rw [injective_iff_map_eq_one]
  intro l hl
  have hlZ : (l : X) ∈ Subgroup.center X := hf hl
  have : (l : X) ∈ L ⊓ Subgroup.center X := ⟨l.2, hlZ⟩
  rw [hL, Subgroup.mem_bot] at this
  exact Subtype.ext this

theorem isElemAbelian_of_isPGroup_of_inf {X : Type} [Group X] [Finite X]
    (hT : Sec4.IsTripleCover X CFSG.Blueprint.NativeSporadic.ON) {L : Subgroup X}
    (hL : L ⊓ Subgroup.center X = ⊥) {T : Subgroup L} (hTp : IsPGroup 3 T) :
    CFSG.Assembly.IsElemAbelian 3 T := by
  obtain ⟨-, ⟨e⟩⟩ := hT
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let π : X →* CFSG.Blueprint.NativeSporadic.ON :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))
  have hker : π.ker ≤ Subgroup.center X := by
    intro x hx
    have h1 : QuotientGroup.mk' (Subgroup.center X) x = 1 := e.injective (by
      rw [map_one]; exact hx)
    exact (QuotientGroup.eq_one_iff _).mp h1
  let f := π.comp L.subtype
  have hinj : Function.Injective f := injective_comp_of_ker_le hker hL
  have hTp' : IsPGroup 3 (T.map f) := hTp.map f
  have hE := isElemAbelian_of_isPGroup_ON hTp'
  refine ⟨⟨⟨fun a b => Subtype.ext (hinj ?_)⟩⟩, fun a ha => hinj ?_⟩
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
    have h := congrArg Subtype.val (hE.1.is_comm.comm ⟨f a, a, a.2, rfl⟩ ⟨f b, b, b.2, rfl⟩)
    rwa [Subgroup.coe_mul, Subgroup.coe_mul] at h
  · rw [map_pow, map_one]
    exact hE.2 (f a) ⟨a, ha, rfl⟩

theorem inf_center_eq_bot {X : Type} [Group X] {L : Subgroup X}
    (hL : Subgroup.center L = ⊥) : L ⊓ Subgroup.center X = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxL, hxZ⟩
  have : (⟨x, hxL⟩ : L) ∈ Subgroup.center L := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext ((Subgroup.mem_center_iff.mp hxZ) g)
  rw [hL, Subgroup.mem_bot] at this
  exact (Subgroup.mem_bot).mpr (congrArg Subtype.val this)

end ThreeX

end CFSG.RankThree.PartTwo.Sec14.Ronan148H
