module

public import CFSG.Quasithin.Background.S1567V4
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListFlag5
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem335

public section

namespace CFSG.Quasithin.H13.Ln2

open CFSG.Open hiding StatedSL StatedSp StatedProj
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem ker_eq_pCore_of_hom {Y : Subgroup G} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) {m : ℕ} (hm : 3 ≤ m) {f : ↥Y →* Matrix.SpecialLinearGroup (Fin m) K}
    (hf : Function.Surjective f) (hk : IsPGroup 2 ↥f.ker) : f.ker = CFSG.pCore 2 ↥Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin m) K) :=
    CFSG.QuasithinUnique.Vol2Native.A312L.sl_isSimple_of_card_two hK hm
  refine le_antisymm (le_sSup ⟨MonoidHom.normal_ker f, hk⟩) ?_
  have hW : (CFSG.pCore 2 ↥Y).map f = ⊥ := by
    have : ((CFSG.pCore 2 ↥Y).map f).Normal := (CFSG.pCore_normal (p := 2) (G := ↥Y)).map f hf
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((CFSG.pCore 2 ↥Y).map f) with h1 | h1
    · exact h1
    · exfalso
      have hp : IsPGroup 2 (Matrix.SpecialLinearGroup (Fin m) K) := by
        have h2 := (CFSG.pCore_isPGroup (p := 2) (G := ↥Y)).map f
        rw [h1] at h2
        exact h2.of_equiv Subgroup.topEquiv
      obtain ⟨a, b, hab⟩ :=
        CFSG.QuasithinUnique.Vol2Native.A312L.sl_nonabelian_of_card_two hK hm
      have hsol : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin m) K) := by
        have := hp.isNilpotent
        infer_instance
      exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr hsol a b)
  intro y hy
  have : f y ∈ (CFSG.pCore 2 ↥Y).map f := ⟨y, hy, rfl⟩
  rw [hW] at this
  exact this

theorem isMSPair_or {T M L D : Subgroup G} (h : Hyp331 G T M L D) {Y : Subgroup G}
    (hY : Y ∈ lFamilyOf L T) (hTY : T ≤ Subgroup.normalizer (Y : Set G))
    {α : ↥Y →* ↥(StatedSL 3 (ZMod 2))} (hα : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 ↥Y) :
    IsMSPair (Y ⊔ T) T ∨ pCoreOf 2 (Y ⊔ T ⊔ D) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hT2, hcomp, hidx, hO⟩ := hY
  by_cases hMS3 : ∀ C : Subgroup G, C ≤ T → C ≠ ⊥ → (C.subgroupOf T).Characteristic →
      ¬ Y ⊔ T ≤ Subgroup.normalizer (C : Set G)
  · left
    refine ⟨⟨sqtkGroup_of_pCoreOf_ne_bot h.qtke h.simple h.nonabelian hO,
      charTwo_of_inH' h.qtke h.sylow ⟨le_sup_right, hO⟩, Y, hcomp,
      Subgroup.coe_mul_of_right_le_normalizer_left Y T hTY,
      CFSG.Quasithin.S1567.isRankTwoLie2Derived_of_modO2 α hα hker⟩,
      Or.inl ⟨T, ?_, hidx, ?_⟩, hMS3⟩
    · refine lt_of_le_of_ne le_sup_right fun hTe => ?_
      have hYT : Y ≤ T := hTe ▸ le_sup_left
      have hsol : Group.IsSolvable ↥T := by
        have := hT2.isNilpotent
        infer_instance
      exact not_isSolvable_of_mem_cComp hcomp
        (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hYT)
          (Subgroup.inclusion_injective hYT))
    · exact (F6.pCoreOf_eq_self_of_isPGroup hT2).symm
  · right
    push Not at hMS3
    obtain ⟨C, hCT, hC, hchar, hYC⟩ := hMS3
    have hDC : D ≤ Subgroup.normalizer (C : Set G) :=
      h.DN.trans (Hyp331.normalizer_le_normalizer_of_characteristic hCT hchar)
    have hle : C ≤ pCoreOf 2 (Y ⊔ T ⊔ D) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        (hCT.trans (le_sup_right.trans le_sup_left)) (sup_le hYC hDC) (h.sylow.1.to_le hCT)
    intro hbot
    rw [hbot, le_bot_iff] at hle
    exact hC hle

end CFSG.Quasithin.H13.Ln2
