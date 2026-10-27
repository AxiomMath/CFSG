module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3316C
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3316D
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3316E
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3316K
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ParSp4
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ParGen
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveSp
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3316B

public section

namespace CFSG.Quasithin.H13

open CFSG.Open hiding StatedSL StatedSp StatedProj
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open CFSG.QuasithinUnique.Setup.X7a CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (unipotent)
open scoped IsMulCommutative

namespace L3316

theorem rank2Pkg_statedSp {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hf : Nat.card F = 2 ^ f) (hf2 : 2 ≤ f) :
    Rk2.Rank2Pkg (StatedSp 2 F) (unipotent 2 F) (fun j => Q2 F j) := by
  have h := (Rk2.rank2Pkg_sp4 hf hf2).map (CFSG.QuasithinUnique.Lin2.Five.projEquiv F).symm
  have hid : ∀ H : Subgroup (StatedSp 2 F),
      (H.map (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj 2 F)).map
        (CFSG.QuasithinUnique.Lin2.Five.projEquiv F).symm.toMonoidHom = H := by
    intro H
    rw [Subgroup.map_map]
    conv_rhs => rw [← Subgroup.map_id H]
    congr 1
    exact MonoidHom.ext fun g => (CFSG.QuasithinUnique.Lin2.Five.projEquiv F).symm_apply_apply g
  simp only [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.projUnipotent, hid] at h
  exact h

variable {G : Type} [Group G] [Finite G]

theorem sp4_config
    {T M L D : Subgroup G} (h : Hyp331 G T M L D) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    (h51 : AsB51) (h10 : Stmt3_3_10) (h14 : Stmt3_3_14) (h15 : Step3_3_15RB)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4)
    (e : ↥(autOn L (vPlus L T)) ≃* ↥(StatedSp 2 K)) {F : Type} [Field F] [Fintype F]
    (hF : Fintype.card F = 4) {α : ↥L →* ↥(StatedSp 2 F)} (hαs : Function.Surjective α)
    (hαk : α.ker = CFSG.pCore 2 ↥L) :
    ∃ (α₂ : ↥L →* ↥(StatedSp 2 F)) (j : Fin 2) (Kc : Subgroup G),
      Function.Surjective α₂ ∧ α₂.ker = CFSG.pCore 2 ↥L ∧
      ((T ⊓ L).subgroupOf L).map α₂ = unipotent 2 F ∧
      T ≤ Subgroup.normalizer (liftPre α₂ (Q2 F j) : Set G) ∧
      liftCore α₂ (Q2 F j) ∈ lFamilyOf L T ∧ InducesInnerOn T (liftCore α₂ (Q2 F j)) ∧
      pCoreOf 2 (liftCore α₂ (Q2 F j) ⊔ T ⊔ D) ≠ ⊥ ∧
      Kc ∈ cComp (liftCore α₂ (Q2 F j) ⊔ T ⊔ D) ∧ liftCore α₂ (Q2 F j) ≤ Kc ∧
      liftCore α₂ (Q2 F j) ⊔ T ⊔ D ≤ Subgroup.normalizer (Kc : Set G) ∧
      A312C15 (modO2Image (liftCore α₂ (Q2 F j) ⊔ T ⊔ D) (liftCore α₂ (Q2 F j)))
        (modO2Image (liftCore α₂ (Q2 F j) ⊔ T ⊔ D) Kc) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hML, hMN⟩ := h14 G T M L D h
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.TM.trans hMN
  have hred := Hyp331.vPlus_reduced h.toSetup331
  have hLTV : L ⊔ T ≤ Subgroup.normalizer (vPlus L T : Set G) := hred.2.2.2.1
  have hLV : L ≤ Subgroup.normalizer (vPlus L T : Set G) := le_sup_left.trans hLTV
  have hTV : T ≤ Subgroup.normalizer (vPlus L T : Set G) := le_sup_right.trans hLTV
  have hS₀ : IsSylowTwoOf (T ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal h.toSetup331.isSylowTwoOf le_sup_left
      (sup_le Subgroup.le_normalizer hTL)
  have hFn : Nat.card F = 2 ^ 2 := by rw [Nat.card_eq_fintype_card, hF]; norm_num
  have : CharP F 2 := SzN15.charP_two_of_card hFn
  have hF4 : ∃ s : Finset F, s.card = 4 := ⟨Finset.univ, by rw [Finset.card_univ, hF]⟩
  have hF4' : 4 ≤ Nat.card F := by rw [hFn]; norm_num
  obtain ⟨hVc, m, hmod⟩ := sp4_module h h38 h39 h51 h10 hTL hK e
  have hgood := goodCoatom_sp4 hML hLV (Setup.isSylowTwoOf_autOn hS₀ hLV) hmod
  have hlie : IsSL3Quot L ∨ IsSp4Quot L :=
    Or.inr ⟨F, inferInstance, inferInstance, hF,
      ⟨(QuotientGroup.quotientMulEquivOfEq hαk.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective α hαs)⟩⟩
  have hP₀ : IsSylowTwoOf ((T ⊓ L).subgroupOf L) ⊤ := by
    refine ⟨le_top, hS₀.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS₀.1).symm, fun h2 => ?_⟩
    apply hS₀.2.2
    rwa [show (((T ⊓ L).subgroupOf L).subgroupOf ⊤).index = ((T ⊓ L).subgroupOf L).index from
      Subgroup.relIndex_top_right _] at h2
  have hU₁ : IsSylowTwoOf (((T ⊓ L).subgroupOf L).map α) ⊤ := by
    have h1 := L3312.isSylowTwoOf_map_range α hP₀
    rwa [MonoidHom.range_eq_top.mpr hαs] at h1
  have hU₀ : IsSylowTwoOf (unipotent 2 F) ⊤ := SzN2.isSylowTwoOf_unipotent
  obtain ⟨k, -, hk⟩ := (Setup.X6.isSylowTwoOf_iff_isSylowOf.1 hU₁).exists_mem_conj
    (Setup.X6.isSylowTwoOf_iff_isSylowOf.1 hU₀)
  set α₂ : ↥L →* ↥(StatedSp 2 F) := (MulAut.conj k).toMonoidHom.comp α with hα₂def
  have hα₂ : Function.Surjective α₂ := by
    rw [hα₂def, MonoidHom.coe_comp]
    exact (MulEquiv.surjective _).comp hαs
  have hker : α₂.ker = CFSG.pCore 2 ↥L := by
    rw [hα₂def, MonoidHom.ker_comp_of_injective _ _ (MulEquiv.injective _), hαk]
  have hkp : IsPGroup 2 ↥α₂.ker := by
    rw [hker]
    exact CFSG.pCore_isPGroup
  have hmapU : ((T ⊓ L).subgroupOf L).map α₂ = unipotent 2 F := by
    rw [hα₂def, ← Subgroup.map_map]
    ext x
    rw [Subgroup.mem_map_equiv]
    simp only [MulAut.conj_symm_apply]
    exact (hk x).symm
  have hR := rank2Pkg_statedSp (F := F) hFn le_rfl
  have hP : ∀ j : Fin 2, IsMaxParabolic2 L (liftPre α₂ (Q2 F j)) ∧
      L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) ≤ liftPre α₂ (Q2 F j) := fun j =>
    isMaxParabolic2_liftPre hS₀ hα₂ (hR.covBy j) (by rw [hmapU]; exact hR.norm j)
  have hTP : ∀ j : Fin 2, T ≤ Subgroup.normalizer (liftPre α₂ (Q2 F j) : Set G) := fun j =>
    le_normalizer_parabolic hlie hS₀ hLV hTL hTV hgood (hP j).1 (hP j).2
  have hY : ∀ j : Fin 2, liftCore α₂ (Q2 F j) ∈ lFamilyOf L T := fun j =>
    liftCore_mem_lFamilyOf h.sylow h.toSetup331.pCoreOf_ne_bot hα₂ hkp (hR.levi j) (hTP j)
  have hf : ∀ j : Fin 2, ∃ f : ↥(liftCore α₂ (Q2 F j)) →* Matrix.SpecialLinearGroup (Fin 2) F,
      Function.Surjective f ∧ IsPGroup 2 ↥f.ker := fun j =>
    exists_hom_sl2_of hα₂ hkp (blkN_surjective hF4 j) (blkN_ker_isPGroup ⟨2, hFn⟩ j)
  have htype : ∀ j : Fin 2,
      L3312.Type3312R (↥(liftCore α₂ (Q2 F j)) ⧸ CFSG.pCore 2 ↥(liftCore α₂ (Q2 F j))) := by
    intro j
    obtain ⟨f, hfs, hfk⟩ := hf j
    exact Or.inl ⟨2, le_rfl, isPSL2_quot_of_hom le_rfl hFn hfs hfk⟩
  have hO : ∀ j : Fin 2, pCoreOf 2 (liftCore α₂ (Q2 F j) ⊔ T ⊔ D) ≠ ⊥ := by
    intro j
    obtain ⟨f, hfs, hfk⟩ := hf j
    exact pCoreOf_sup_ne_bot h10 h (fun t ht => mem_normalizer_perfectCore (hTP j ht))
      (hY j).2.2.2.2 hF4' hfs hfk
  have hkT : α₂.ker.map L.subtype ≤ T := by
    rw [hker]
    show pCoreOf 2 L ≤ T
    exact (EscapingLocal.pCoreOf_le_of_isSylowTwoOf hS₀).trans inf_le_left
  have hgen : perfectCore (Q2 F 0) ⊔ perfectCore (Q2 F 1) ⊔ (T.subgroupOf L).map α₂ = ⊤ := by
    rw [← Subgroup.inf_subgroupOf_right, hmapU]
    exact hR.sup_perfectCore_eq_top
  have hLT : L ⊔ T = liftCore α₂ (Q2 F 0) ⊔ liftCore α₂ (Q2 F 1) ⊔ T :=
    le_antisymm (sup_le (le_sup_liftCore hα₂ hkT hgen) le_sup_right)
      (sup_le (sup_le ((liftCore_le _ _).trans le_sup_left) ((liftCore_le _ _).trans le_sup_left))
        le_sup_right)
  obtain ⟨Y, hYY, -, -, hinn, Kc, hKc, hYK, -, hHK, hc15⟩ :=
    h15 G T M L D _ _ h (hY 0) (hY 1) hLT (hO 0) (hO 1) (htype 0) (htype 1)
  rcases hYY with rfl | rfl
  · exact ⟨α₂, 0, Kc, hα₂, hker, hmapU, hTP 0, hY 0, hinn, hO 0, hKc, hYK, hHK, hc15⟩
  · exact ⟨α₂, 1, Kc, hα₂, hker, hmapU, hTP 1, hY 1, hinn, hO 1, hKc, hYK, hHK, hc15⟩

end L3316

end CFSG.Quasithin.H13
