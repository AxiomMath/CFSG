module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.InducedQuotInfAut
import CFSG.LocalAnalysis.UniquenessCase.UC22S2113
import CFSG.GroupTheory.PermutingProducts
import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4Mul

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem uc22s2112r34_exists_innerHom_permutes {L R T : Subgroup G}
    (hZ : center (BarInf L) = ⊥) (hRN : R ≤ normalizer (L : Set G))
    (hinn : ∀ x (hx : x ∈ R),
      inducedBarInfAutHom L ⟨x, hRN hx⟩ ∈ (MulAut.conj : BarInf L →* MulAut (BarInf L)).range)
    (hTL : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ L) L) (hT : IsPGroup 2 ↥T) (hRT : Permutes R T) :
    ∃ (P : Sylow 2 (BarInf L)) (ψ : ↥R →* BarInf L),
      (∀ x : ↥R, MulAut.conj (ψ x) = inducedBarInfAutHom L ⟨x, hRN x.2⟩) ∧
      (ψ.range : Set (BarInf L)) * (P : Set (BarInf L)) = (P : Set (BarInf L)) * ψ.range := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup G := normalizer (L : Set G) with hNdef
  set φ := inducedBarInfAutHom L with hφdef
  set X : Subgroup (MulAut (BarInf L)) :=
    (MulAut.conj : BarInf L →* MulAut (BarInf L)).range with hXdef
  have hinj : Function.Injective (MulAut.conj : BarInf L →* MulAut (BarInf L)) := by
    rw [injective_iff_map_eq_one]
    intro z hz
    have hzc : z ∈ center (BarInf L) := by
      rw [mem_center_iff]
      intro w
      have h := congrArg (fun φ : MulAut (BarInf L) => φ w) hz
      simp only [MulAut.conj_apply, MulAut.one_apply] at h
      calc w * z = z * w * z⁻¹ * z := by rw [h]
        _ = z * w := by group
    rwa [hZ, mem_bot] at hzc
  let eX : BarInf L ≃* ↥X := MonoidHom.ofInjective hinj
  have : Finite ↥X := Finite.of_equiv _ eX.toEquiv
  set Rφ : Subgroup (MulAut (BarInf L)) := (R.subgroupOf N).map φ with hRφdef
  set Sφ : Subgroup (MulAut (BarInf L)) := ((T ⊓ N).subgroupOf N).map φ with hSφdef
  have hRX : Rφ ≤ X := by
    rintro _ ⟨⟨x, hxN⟩, hx, rfl⟩
    exact hinn x hx
  have hperm : (Rφ : Set (MulAut (BarInf L))) * Sφ = Sφ * Rφ := by
    have h1 := CFSG.Quasithin.H23P4.mul_comm_inf_of_le hRT.symm hRN
    exact CFSG.GroupTheory.map_permutes_map φ
      (CFSG.Quasithin.H23P4.mul_comm_subgroupOf hRN inf_le_right h1.symm)
  have hpermX := CFSG.Quasithin.H23P4.mul_comm_subgroupOf hRX inf_le_right
    (CFSG.Quasithin.H23P4.mul_comm_inf_of_le hperm.symm hRX).symm
  have hS2 : IsPGroup 2 ↥((Sφ ⊓ X).subgroupOf X) := by
    have h2 : IsPGroup 2 ↥Sφ :=
      ((hT.to_le inf_le_left).of_equiv (subgroupOfEquivOfLe inf_le_right).symm).map φ
    exact (h2.to_le inf_le_left).of_equiv (subgroupOfEquivOfLe inf_le_right).symm
  have hSidx : ¬ 2 ∣ ((Sφ ⊓ X).subgroupOf X).index := by
    let f : ↥L →* ↥X := (MulAut.conj : BarInf L →* MulAut (BarInf L)).rangeRestrict.comp
      (QuotientGroup.mk' (CFSG.solvableRadical ↥L))
    have hf : Function.Surjective f :=
      (MonoidHom.rangeRestrict_surjective _).comp (QuotientGroup.mk'_surjective _)
    have hle : ((T ⊓ L).subgroupOf L).map f ≤ (Sφ ⊓ X).subgroupOf X := by
      rintro _ ⟨⟨t, htL⟩, ht, rfl⟩
      have htT : t ∈ T := (mem_inf.mp (show t ∈ T ⊓ L from ht)).1
      rw [mem_subgroupOf]
      refine ⟨⟨⟨t, le_normalizer htL⟩, ?_, uc22s2113_inducedBarInfAutHom_of_mem htL⟩,
        (f ⟨t, htL⟩).2⟩
      show t ∈ T ⊓ N
      exact mem_inf.mpr ⟨htT, le_normalizer htL⟩
    have hidx : ¬ 2 ∣ ((T ⊓ L).subgroupOf L).index :=
      (CFSG.ABGLocalTools.isSylowOf_iff.mp hTL).2.2
    exact fun h2 => hidx
      (h2.trans ((Subgroup.index_dvd_of_le hle).trans (Subgroup.index_map_dvd _ hf)))
  let θR : ↥R →* ↥X := (φ.comp (Subgroup.inclusion hRN)).codRestrict X fun x => hinn x x.2
  let e' : ↥X →* BarInf L := eX.symm.toMonoidHom
  have he' : Function.Bijective e' := eX.symm.bijective
  have hθR : θR.range = Rφ.subgroupOf X := by
    ext z
    rw [MonoidHom.mem_range, mem_subgroupOf]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨⟨x, hRN x.2⟩, x.2, rfl⟩
    · rintro ⟨⟨y, hyN⟩, hy, hyz⟩
      exact ⟨⟨y, hy⟩, Subtype.ext hyz⟩
  have hψ : ∀ x : ↥R, MulAut.conj ((e'.comp θR) x) = φ ⟨x, hRN x.2⟩ := fun x => by
    rw [← MonoidHom.ofInjective_apply hinj]
    exact congrArg Subtype.val (eX.apply_symm_apply (θR x))
  refine ⟨(hS2.map e').toSylow ?_, e'.comp θR, hψ, ?_⟩
  · rwa [Subgroup.index_map_of_bijective he']
  · show ((e'.comp θR).range : Set (BarInf L)) *
        (((Sφ ⊓ X).subgroupOf X).map e' : Set (BarInf L)) =
      (((Sφ ⊓ X).subgroupOf X).map e' : Set (BarInf L)) * (e'.comp θR).range
    rw [MonoidHom.range_comp, hθR]
    exact CFSG.GroupTheory.map_permutes_map e' hpermX

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
