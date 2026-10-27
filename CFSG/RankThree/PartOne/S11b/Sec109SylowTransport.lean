module

public import CFSG.RankThree.PartOne.S11b.Sec109Setup
public import CFSG.RankThree.PartOne.S11b.Sec109StructureMap
import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
import CFSG.Adapters.StatedSLTwoField
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Assembly.LowTwoRank (StatedClassicalModel projectiveSpecialLinearGroupEquivStatedProj)

namespace Sec109

noncomputable def projectiveSLEquivSL_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {n : ℕ} (hn : 1 ≤ n) :
    Matrix.SpecialLinearGroup (Fin n) K ≃* projectiveSL n K := by
  have hscal : scalars n K = ⊥ := by
    have h := card_scalars_dvd (K := K) hn
    rw [hK] at h
    exact Subgroup.eq_bot_of_card_eq _ (Nat.dvd_one.mp h)
  exact MulEquiv.ofBijective (proj n K)
    ⟨(MonoidHom.ker_eq_bot_iff _).mp (by rw [ker_proj, hscal]), proj_surjective n K⟩

theorem exists_mulEquiv_sl_two {H : Type} [Group H] {n : ℕ}
    (h : StatedClassicalModel H .PSL n 2 1) :
    Nonempty (H ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :=
  CFSG.Open.StatedAPI.nonempty_mulEquiv_specialLinear_zmod_two_of_psl h

@[expose] def LnTwoSylowSevenModel : Prop :=
  ∀ n : ℕ, (n = 6 ∨ n = 7) →
    ∃ B₀ : Subgroup (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)),
      Nat.card B₀ = 49 ∧ StructureB (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin n) (ZMod 2))) B₀

theorem exists_sylow_of_card_forty_nine {M : Type} [Group M] [Finite M]
    (hM : ¬ 7 ^ 3 ∣ Nat.card M) (H : Subgroup M) (hH : Nat.card H = 49) :
    ∃ P : Sylow 7 M, (P : Subgroup M) = H := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hp : IsPGroup 7 H := IsPGroup.of_card (n := 2) (by rw [hH]; norm_num)
  obtain ⟨P, hHP⟩ := hp.exists_le_sylow
  refine ⟨P, ?_⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp P.isPGroup'
  have h1 : 7 ^ k ∣ Nat.card M := hk ▸ Subgroup.card_subgroup_dvd_card (P : Subgroup M)
  have h2 : 7 ^ 2 ∣ 7 ^ k := by
    have := Subgroup.card_dvd_of_le hHP
    rwa [hH, hk] at this
  have hk2 : 2 ≤ k := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h2
  have hk3 : k ≤ 2 := by
    by_contra hk3
    exact hM ((Nat.pow_dvd_pow 7 (by omega : 3 ≤ k)).trans h1)
  have hkk : k = 2 := le_antisymm hk3 hk2
  exact (Subgroup.eq_of_le_of_card_ge hHP (by rw [hH, hk, hkk]; norm_num)).symm

theorem map_top_of_surjective' {M N : Type} [Group M] [Group N] (f : M →* N)
    (hf : Function.Surjective f) : (⊤ : Subgroup M).map f = ⊤ := by
  rw [Subgroup.map_top, MonoidHom.range_eq_top.mpr hf]

theorem lnTwoSylowSeven_of_model (hmodel : LnTwoSylowSevenModel) : LnTwoSylowSeven := by
  classical
  intro G _ _ L B n hn hLmodel hBL _ hBcard
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨B₀, hB₀c, hB₀s⟩ := hmodel n hn
  obtain ⟨θ⟩ := exists_mulEquiv_sl_two hLmodel
  have hM : ¬ 7 ^ 3 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) := by
    rw [card_SL_eq (by omega), Nat.card_zmod]
    rcases hn with rfl | rfl <;> decide +kernel
  have hB'card : Nat.card ((B.subgroupOf L).map θ.toMonoidHom) = 49 := by
    rw [Subgroup.card_map_of_injective θ.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBL).toEquiv, hBcard]
  obtain ⟨P'', hP''⟩ := exists_sylow_of_card_forty_nine hM _ hB'card
  obtain ⟨P₀, hP₀⟩ := exists_sylow_of_card_forty_nine hM B₀ hB₀c
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) P₀ P''
  have hconj : B₀.map (MulAut.conj g).toMonoidHom = (B.subgroupOf L).map θ.toMonoidHom := by
    rw [← hP'', ← hg, ← hP₀, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  have h1 := StructureB.map (MulAut.conj g).toMonoidHom (MulAut.conj g).injective hB₀s
  rw [hconj, map_top_of_surjective' _ (MulAut.conj g).surjective] at h1
  have h2 := StructureB.map θ.symm.toMonoidHom θ.symm.injective h1
  have hB2 : ((B.subgroupOf L).map θ.toMonoidHom).map θ.symm.toMonoidHom = B.subgroupOf L := by
    ext x
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      simpa using hz
    · intro hx
      exact ⟨θ x, ⟨x, hx, rfl⟩, by simp⟩
  rw [hB2, map_top_of_surjective' _ θ.symm.surjective] at h2
  have h3 := StructureB.map L.subtype L.subtype_injective h2
  rw [Subgroup.map_subgroupOf_eq_of_le hBL] at h3
  have hL : (⊤ : Subgroup L).map L.subtype = L := by
    rw [Subgroup.map_top, Subgroup.range_subtype]
  rwa [hL] at h3

end Sec109

end CFSG.RankThree.PartOne
