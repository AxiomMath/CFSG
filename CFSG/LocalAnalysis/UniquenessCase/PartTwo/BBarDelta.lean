module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BarSubComponent
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1FbSyl
public import CFSG.Quasithin.EmptyFaithful.S152N2Fix
public import CFSG.Quasithin.Vol2.Ch9Sec2SL
public import CFSG.Quasithin.AppendixH.H9.H92.RadCard.ElemAbelianMap
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem mem_aSet_of_le {W : Type} [CommGroup W] {k : ℕ} {A Y Y' : Subgroup (MulAut W)}
    (hA : A ∈ E3.aSet k Y) (hAY' : A ≤ Y') : A ∈ E3.aSet k Y' :=
  ⟨hAY', hA.2.1, hA.2.2.1, hA.2.2.2⟩

theorem aSet_conjAutSub {W : Type} [CommGroup W] {k : ℕ} {X A : Subgroup (MulAut W)}
    {g : MulAut W} (hA : A ∈ E3.aSet k X) :
    conjAutSub g A ∈ E3.aSet k (conjAutSub g X) := by
  refine ⟨Subgroup.map_mono hA.1, ?_, ?_, ?_⟩
  · rw [conjAutSub, Ne, Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g).injective]
    exact hA.2.1
  · exact CFSG.ASVolI.ChH.isElemAbelian2_map_of_comm_sq (MulAut.conj g).toMonoidHom A
      hA.2.2.1.1 fun a ha => by simpa [pow_two] using hA.2.2.1.2 a ha
  · intro B' hB' hm'
    let f : MulAut W →* MulAut W := (MulAut.conj g).toMonoidHom
    have hf : Function.Injective f := (MulAut.conj g).injective
    set B : Subgroup (MulAut W) := B'.comap f with hB
    have hBle : B ≤ A := by
      intro x hx
      have hx' : f x ∈ B' := hx
      have hxA' : f x ∈ conjAutSub g A := hB' hx'
      obtain ⟨a, ha, hae⟩ := (Subgroup.mem_map).1 hxA'
      have : a = x := hf hae
      simpa [← this] using ha
    have hBmap : B.map f = B' := by
      rw [hB, Subgroup.map_comap_eq,
        MonoidHom.range_eq_top.2 (MulAut.conj g).surjective]
      simp
    have hm : E3.mQuot A B < k := by
      have h := hm'
      rw [← hBmap] at h
      unfold E3.mQuot at h ⊢
      rw [conjAutSub] at h
      rwa [Subgroup.relIndex_map_map_of_injective _ _ hf] at h
    have hfix := hA.2.2.2 B hBle hm
    rw [conjAutSub, fixV_map_conj_eq A g, ← hBmap, fixV_map_conj_eq B g, hfix]

theorem isComponentOf_sup_of_normal {Γ : Type*} [Group Γ] {L Y T : Subgroup Γ}
    (hLY : L ≤ Y) (hNY : Y ≤ Subgroup.normalizer (L : Set Γ)) (hT : T ≤ Y)
    (hcomp : IsComponentOf L Y) : IsComponentOf L (L ⊔ T) := by
  have hLT : L ⊔ T ≤ Y := sup_le hLY hT
  have hN : (L.subgroupOf (L ⊔ T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2 (hLT.trans hNY)
  exact ⟨le_sup_left, IsSubnormal.step le_sup_left hN (IsSubnormal.refl (L ⊔ T)), hcomp.2.2⟩

theorem exists_conj_le_of_quasithin_isSylowIn {Γ : Type*} [Group Γ] [Finite Γ] {p : ℕ}
    [Fact p.Prime] {P Y A : Subgroup Γ} (hP : CFSG.Quasithin.IsSylowIn p P Y) (hAY : A ≤ Y)
    (hA : IsPGroup p A) : ∃ g ∈ Y, A.map (MulAut.conj g).toMonoidHom ≤ P := by
  obtain ⟨Q, hQ⟩ :=
    hA.comap_subtype (K := Y) |>.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥Y Q hP.toSylow
  refine ⟨(g : Γ), g.2, ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  have haQ : (⟨a, hAY ha⟩ : ↥Y) ∈ Q := hQ ha
  have hmem : MulAut.conj g (⟨a, hAY ha⟩ : ↥Y) ∈ ((g • Q : Sylow p ↥Y) : Subgroup ↥Y) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ haQ
  rw [hg, CFSG.Quasithin.IsSylowIn.coe_toSylow] at hmem
  simpa [MulAut.conj_apply, Subgroup.mem_subgroupOf] using hmem

theorem fixV_ne_fixV_sup {W : Type} [CommGroup W] [Finite W] (hw : ∀ w : W, w ^ 2 = 1)
    {X T : Subgroup (MulAut W)} (hX : X ≠ ⊥) (hfix : fixV X = ⊥) (hT : IsPGroup 2 T) :
    fixV T ≠ fixV (X ⊔ T) := by
  have hfix' : fixV (X ⊔ T) = ⊥ :=
    le_bot_iff.1 (hfix ▸ fixV_anti le_sup_left)
  have hWnt : Nontrivial W := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hX (Subgroup.ext fun x => by
      rw [Subgroup.mem_bot]
      constructor
      · intro _
        ext v
        exact Subsingleton.elim (x v) v
      · intro hx
        rw [hx]
        exact X.one_mem)
  have hW2 : IsPGroup 2 (⊤ : Subgroup W) := fun x => ⟨1, by
    rw [pow_one, pow_two]
    exact Subtype.ext (by simpa [pow_two] using hw (x : W))⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).1 hW2
  have hn0 : n ≠ 0 := by
    rintro rfl
    have h1 : Nat.card W = 1 := by simpa using hn
    have hlt : 1 < Nat.card W := Finite.one_lt_card
    omega
  have h2dvd : 2 ∣ Nat.card W := by
    rw [show Nat.card W = 2 ^ n from by simpa using hn]
    exact dvd_pow_self 2 hn0
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := CFSG.Quasithin.S152N2.card_modEq_card_inf_fixV (V := W) (p := 2) hT
    (W := (⊤ : Subgroup W)) (fun g _ w _ => Subgroup.mem_top (g w))
  have hmod' : Nat.card W ≡ Nat.card (fixV T) [MOD 2] := by simpa using hmod
  have hmod0 : Nat.card W ≡ 0 [MOD 2] := (Nat.modEq_zero_iff_dvd).2 h2dvd
  have hfix0 : Nat.card (fixV T) ≡ 0 [MOD 2] := hmod'.symm.trans hmod0
  have h2fix : 2 ∣ Nat.card (fixV T) := (Nat.modEq_zero_iff_dvd).1 hfix0
  have hfixT : fixV T ≠ ⊥ := by
    intro hbot
    have hc : Nat.card (fixV T) = 1 := by rw [hbot, Subgroup.card_bot]
    omega
  rwa [hfix']

theorem odd_card_center_of_mulEquiv_of_isSimpleGroup {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (hsimple : IsSimpleGroup A) (hperf : commutator A = ⊤) :
    Odd (Nat.card (Subgroup.center B)) := by
  haveI := hsimple
  have hperfect : ⁅(⊤ : Subgroup A), (⊤ : Subgroup A)⁆ = ⊤ := by
    simpa [commutator_def] using hperf
  have hcenterA : Subgroup.center A = ⊥ :=
    CFSG.Quasithin.H13.Ch9.center_eq_bot_of_commutator_eq_top hperfect
  have hcenter : Subgroup.center B = ⊥ := by
    have h := Subgroup.map_center_eq e
    rw [hcenterA, Subgroup.map_bot] at h
    exact h.symm
  rw [hcenter, Subgroup.card_bot]
  norm_num

theorem bParam_le_of_normal {W : Type} [CommGroup W] [Finite W]
    {L Y T : Subgroup (MulAut W)} (hLY : L ≤ Y)
    (hNY : Y ≤ Subgroup.normalizer (L : Set (MulAut W)))
    (hT : CFSG.Quasithin.IsSylowIn 2 T Y) : bParam L Y ≤ bParam L (L ⊔ T) := by
  classical
  unfold bParam
  by_cases hne : {k : ℕ | 0 < k ∧ ∃ A ∈ E3.aSet k Y, ⁅L, A⁆ ≠ ⊥}.Nonempty
  · refine csSup_le hne ?_
    rintro k ⟨hk0, A, hA, hneA⟩
    obtain ⟨g, hgY, hle⟩ := exists_conj_le_of_quasithin_isSylowIn hT hA.1
      (E3.isPGroup_of_isElemAbelian2 hA.2.2.1)
    have hYconj : Y.map (MulAut.conj g).toMonoidHom = Y :=
      Subgroup.mem_normalizer_iff_map_conj_eq.1 (Subgroup.le_normalizer hgY)
    have hLconj : L.map (MulAut.conj g).toMonoidHom = L :=
      Subgroup.mem_normalizer_iff_map_conj_eq.1 (hNY hgY)
    have hA'Y : A.map (MulAut.conj g).toMonoidHom ∈ E3.aSet k Y := by
      have h1 := aSet_conjAutSub (g := g) hA
      simpa only [conjAutSub, hYconj] using h1
    have hA'LT : A.map (MulAut.conj g).toMonoidHom ≤ L ⊔ T := hle.trans le_sup_right
    have hA' : A.map (MulAut.conj g).toMonoidHom ∈ E3.aSet k (L ⊔ T) :=
      mem_aSet_of_le hA'Y hA'LT
    have hne' : ⁅L, A.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ := by
      intro hbot
      apply hneA
      have hconj : conjAutSub g ⁅L, A⁆ = ⁅L, A.map (MulAut.conj g).toMonoidHom⁆ := by
        rw [conjAutSub, Subgroup.map_commutator, hLconj]
      rw [← hconj] at hbot
      exact (Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g).injective).1 hbot
    exact le_bParam hk0 hA' hne'
  · rw [Set.not_nonempty_iff_eq_empty.1 hne, csSup_empty]
    exact Nat.zero_le _

theorem bBar_le_of_sup_bound {D : Data G} {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V)
    {L : Subgroup G} (hL : L ∈ calC D.M) (hN : (L.subgroupOf D.M).Normal) {k : ℕ}
    (h : bParam (barSub V₀ V hV.isElemAbelian L)
      (barSub V₀ V hV.isElemAbelian L ⊔ barSub V₀ V hV.isElemAbelian D.T) ≤ k) :
    bBar L D.M V₀ V hV.isElemAbelian ≤ k := by
  have hV' := hV.isElemAbelian
  have hLM : L ≤ D.M := hL.1.le
  have hMN : D.M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).1 hN
  have hT : CFSG.Quasithin.IsSylowIn 2 D.T D.M :=
    (CFSG.ABGLocalTools.isSylowOf_iff (p := 2)).1 D.sylowM
  have hTsyl : CFSG.Quasithin.IsSylowIn 2 (barSub V₀ V hV' D.T) (Mbar D.M V₀ V hV') :=
    s16c1_barSub_sylow
      (le_stabTil hV.pairFacts.le_normalizer hV.pairFacts.le_normalizer₀) hT
  have hLbarM : barSub V₀ V hV' L ≤ Mbar D.M V₀ V hV' := barSub_mono V₀ V hV' hLM
  have hNbar : Mbar D.M V₀ V hV' ≤ Subgroup.normalizer
      (barSub V₀ V hV' L : Set (MulAut (Vtil V₀ V hV'))) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLbarM).1
      (barSub_subgroupOf_mbar_normal hV' hLM hMN)
  exact (bParam_le_of_normal hLbarM hNbar hTsyl).trans h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
