module

public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2Basic

public section

namespace CFSG.Quasithin.H13.L3321

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T M L D : Subgroup G}

theorem exists_alpha_ext_of_TL (h9 : Stmt3_3_9) (hGA : GriessAllModelsStatement)
    (h : Hyp331 G T M L D) (hML : mPlus L T = L) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (e : ↥(autOn L (vPlus L T)) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))
    [IsMulCommutative ↥(vPlus L T)] (hmod : Mod3321Ext T L) :
    ∃ α : ↥L →* SL4, Function.Surjective α ∧ α.ker = CFSG.pCore 2 ↥L ∧
      ((T ⊓ L).subgroupOf L).map α = FLc.Ut 4 ∧
      L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) = L3316.liftPre α P2 := by
  obtain ⟨hVe, hLV, -, -, -, -, -⟩ := setting_facts h hTL
  obtain ⟨Z₀, hZ₀, -, π, hπ⟩ := hmod
  have hV2 : ∀ w : ↥(vPlus L T), w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hVe.2 w w.2)
  obtain ⟨D₀⟩ := FLc.vmodelExtSq hπ (fun g hg z hz => (hZ₀.trans inf_le_left) hz g hg)
  have hcard : Nat.card ↥(autOn L (vPlus L T)) = 20160 := by
    rw [Nat.card_congr e.toEquiv, Ln2.card_specialLinear 4 (Or.inl rfl)]
    rfl
  have : Nontrivial ↥(autOn L (vPlus L T)) := Finite.one_lt_card_iff_nontrivial.1
    (by rw [hcard]; norm_num)
  obtain ⟨k, hk⟩ := exists_ne (1 : ↥(autOn L (vPlus L T)))
  obtain ⟨g₀, hg₀⟩ := FLc.rhoOf_surj hπ.1 k k.2
  have hne : ∃ g, FLc.rhoOf π g ≠ 1 := ⟨g₀, by rw [hg₀]; exact fun h1 => hk (Subtype.ext h1)⟩
  have hS := L3317.isSylowTwoOf_inf h hTL
  obtain ⟨h', hinj, hr1, hr2, hU⟩ := exists_normalized_eq hVe hLV hS (by norm_num)
    (FLc.rhoOf π) (FLc.rhoOf_surj hπ.1) (FLc.rhoOf_mem π) hne
  have D₁ := D₀.rtwist h'
  obtain ⟨α, hαs, hαk, hαU, hαv⟩ := exists_alpha_of_rho h hGA hTL e hinj hr1 hr2 hU
  refine ⟨α, hαs, hαk, hαU, ?_⟩
  have hP2C :
      L3316.liftPre α P2 ≤ L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
    rintro _ ⟨l, hl, rfl⟩
    refine mem_centralizer_of_fix h9 h hML l.2 fun v hvZ hvW => ?_
    have hvc : v ∈ commV (autOn L (vPlus L T)) := by
      rw [Ln2.commV_autOn_eq h]
      exact hvW
    have key := FLc.fixQ_of_model D₁ hV2 (by norm_num) (c := 2)
      (fun a ha i hi hic => FLc.fix_extSq4 a ha i hi hic) hvc
      (fun s hs => fix_of_mem_autOn_inf (by rw [← hU]; exact ⟨s, hs, rfl⟩) hvZ) (α l) hl
    rw [hαv l] at key
    exact key
  set Pz : Subgroup SL4 :=
    ((L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)).subgroupOf L).map α with hPz
  have hUPz : FLc.Ut 4 ≤ Pz := by
    rw [← hαU]
    refine Subgroup.map_mono (Subgroup.subgroupOf_mono L fun t ht => ⟨ht.2, ?_⟩)
    exact CFSG.QuasithinUnique.L246C127.le_centralizer_omegaOneCenter T ht.1
  have hP2Pz : P2 ≤ Pz := by
    intro g hg
    obtain ⟨l, rfl⟩ := hαs g
    exact ⟨l, Subgroup.mem_subgroupOf.2 (hP2C ⟨l, hg, rfl⟩), rfl⟩
  have hkerC : ∀ l : ↥L, α l = 1 →
      (l : G) ∈ L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
    intro l hl
    refine mem_centralizer_of_fix h9 h hML l.2 fun v _ _ => ?_
    have key := hαv l
    rw [hl, map_one] at key
    rw [← key, MulAut.one_apply]
  have hcuts : FLc.cuts Pz = {2} := by
    have h1 : FLc.cuts Pz ⊆ {2} := by
      have := hP2Pz
      rw [FLc.eq_QI_cuts hUPz] at this
      exact (FLc.QI_le_QI_iff fun j hj => FLc.isNode_of_mem_cuts hj).1 this
    refine Set.Subset.antisymm h1 fun i hi => ?_
    rw [Set.mem_singleton_iff] at hi
    subst hi
    by_contra h2
    have hempty : FLc.cuts Pz = ∅ := by
      ext j
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hj
      have := h1 hj
      rw [Set.mem_singleton_iff] at this
      subst this
      exact h2 hj
    apply inf_centralizer_ne hML e
    intro l hl
    have hlPz : α ⟨l, hl⟩ ∈ Pz := by
      rw [FLc.eq_QI_cuts hUPz, hempty]
      show α ⟨l, hl⟩ ∈ flagStabilizer 4 (ZMod 2) ∅
      rw [flagStabilizer_empty]
      exact Subgroup.mem_top _
    obtain ⟨c, hc, hcl⟩ := hlPz
    have h3 := hkerC (c⁻¹ * ⟨l, hl⟩) (by rw [map_mul, map_inv, hcl, inv_mul_cancel])
    have h4 : (c : G) ∈ L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
      Subgroup.mem_subgroupOf.1 hc
    have e1 : l = (c : G) * ((c⁻¹ * ⟨l, hl⟩ : ↥L) : G) := by simp
    rw [e1]
    exact (Subgroup.mul_mem _ h4 h3).2
  have hPzeq : Pz = P2 := by
    rw [FLc.eq_QI_cuts hUPz, hcuts]
  refine le_antisymm (fun x hx => ?_) hP2C
  have h1 : α ⟨x, hx.1⟩ ∈ Pz := ⟨⟨x, hx.1⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
  rw [hPzeq] at h1
  exact ⟨⟨x, hx.1⟩, h1, rfl⟩

end CFSG.Quasithin.H13.L3321

namespace CFSG.Quasithin.H13.NFa2

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Quasithin
open CFSG.Quasithin.CosetGeom CFSG.ASVolI.ChF
open CFSG.Quasithin.H13.Ch3Sec3
open CFSG.QuasithinUnique.Vol2Native (A37ForSQTKCat A38ForSQTKCat A39ForSQTKCat)
open scoped IsMulCommutative Pointwise

theorem leaf_LS1_of (h5 : Stmt3_3_5) (h9 : Stmt3_3_9)
    (hGA : GriessAllModelsStatement) (h128 : Lemma128Two) (h37 : A37ForSQTKCat)
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) : Leaf_LS1 := by
  intro G _ _ T M L D H K q c
  show (L ⊔ T) ⊓ (conjClosure K T ⊔ T) = H
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hTL, ⟨e⟩, hc, hmodE, -, -⟩ := c.site
  obtain ⟨α, hαs, hαk, hαU, hCZ⟩ :=
    L3321.exists_alpha_ext_of_TL h9 hGA c.nf.hyp c.mPlus_eq hTL e hmodE
  have hHX : H ≤ (L ⊔ T) ⊓ (conjClosure K T ⊔ T) := le_inf c.nf.HLT c.H_le_G2
  have hTH : T ≤ H := by rw [c.hH]; exact le_sup_right
  have hPH : L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤ H := by
    rw [c.hH]; exact le_sup_left
  have hTX : T ≤ (L ⊔ T) ⊓ (conjClosure K T ⊔ T) := le_inf le_sup_right le_sup_right
  have hOL : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ T) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans le_sup_left)
      (sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
        (c.TL.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
  have hkerX : ∀ l : ↥L, α l = 1 → (l : G) ∈ (L ⊔ T) ⊓ (conjClosure K T ⊔ T) := by
    intro l hl
    have hlk : l ∈ CFSG.pCore 2 ↥L := by
      have := MonoidHom.mem_ker.2 hl
      rwa [hαk] at this
    have h1 : (l : G) ∈ pCoreOf 2 (L ⊔ T) := hOL ((Lem3328.mem_pCore_iff l).1 hlk)
    exact hHX (CFSG.LieType.BorelTits.pCoreOf_le 2 H (c.Q_le_R h1))
  set Y : Subgroup ↥L := ((L ⊔ T) ⊓ (conjClosure K T ⊔ T)).subgroupOf L
  set Pz : Subgroup L3321.SL4 := Y.map α
  have hUPz : FLc.Ut 4 ≤ Pz := by
    rw [← hαU]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono L ((inf_le_left : T ⊓ L ≤ T).trans hTX))
  have hkerY : α.ker ≤ Y := fun l hl =>
    Subgroup.mem_subgroupOf.2 (hkerX l (MonoidHom.mem_ker.1 hl))
  have hP2Pz : L3321.P2 ≤ Pz := by
    intro g hg
    obtain ⟨l, rfl⟩ := hαs g
    have hlC : (l : G) ∈ L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
      rw [hCZ]; exact ⟨l, hg, rfl⟩
    exact ⟨l, Subgroup.mem_subgroupOf.2 (hHX (hPH hlC)), rfl⟩
  have hcutsSub : FLc.cuts Pz ⊆ {2} := by
    have := hP2Pz
    rw [FLc.eq_QI_cuts hUPz] at this
    exact (FLc.QI_le_QI_iff fun j hj => FLc.isNode_of_mem_cuts hj).1 this
  have hcase : Pz = L3321.P2 ∨ Pz = ⊤ := by
    by_cases h2 : (2 : ℕ) ∈ FLc.cuts Pz
    · left
      have hcut : FLc.cuts Pz = {2} :=
        Set.Subset.antisymm hcutsSub (Set.singleton_subset_iff.2 h2)
      exact (FLc.eq_QI_cuts hUPz).trans (congrArg (FLc.QI 4) hcut)
    · right
      have hempty : FLc.cuts Pz = ∅ := by
        ext j
        simp only [Set.mem_empty_iff_false, iff_false]
        intro hj
        have := hcutsSub hj
        rw [Set.mem_singleton_iff] at this
        subst this
        exact h2 hj
      rw [FLc.eq_QI_cuts hUPz, hempty]
      exact CFSG.LocalAnalysis.ComponentInitial.LinearFlag.flagStabilizer_empty 4 (ZMod 2)
  have hTop : Pz ≠ ⊤ := by
    intro htop
    have hLX : ∀ l : ↥L, (l : G) ∈ (L ⊔ T) ⊓ (conjClosure K T ⊔ T) := by
      intro l
      have hl : α l ∈ Pz := by rw [htop]; exact Subgroup.mem_top _
      obtain ⟨y, hy, hyl⟩ := Subgroup.mem_map.1 hl
      have hk : y⁻¹ * l ∈ Y :=
        hkerY (MonoidHom.mem_ker.2 (by rw [map_mul, map_inv, hyl, inv_mul_cancel]))
      have h1 := Y.mul_mem hy hk
      rw [mul_inv_cancel_left] at h1
      exact Subgroup.mem_subgroupOf.1 h1
    have hLN : L ≤ Subgroup.normalizer (conjClosure K T : Set G) := fun l hl =>
      (sup_le Subgroup.le_normalizer (le_normalizer_conjClosure K T))
        (Subgroup.mem_inf.1 (hLX ⟨l, hl⟩)).2
    refine c.nf.not_le_normalizer h5 h128 h37 h38 h39 ?_
    rw [c.mPlus_eq]
    exact sup_le hLN (le_normalizer_conjClosure K T)
  have hPzP2 : Pz = L3321.P2 := hcase.resolve_right hTop
  refine le_antisymm ?_ hHX
  intro x hx
  have hxLT : x ∈ L ⊔ T := (Subgroup.mem_inf.1 hx).1
  have hxLT' : x ∈ (L : Set G) * (T : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left L T c.TL]
    exact hxLT
  obtain ⟨l, hl, t, ht, rfl⟩ := hxLT'
  have hlX : l ∈ (L ⊔ T) ⊓ (conjClosure K T ⊔ T) := by
    have h1 := Subgroup.mul_mem _ hx (Subgroup.inv_mem _ (hTX ht))
    rwa [mul_inv_cancel_right] at h1
  have hα : α ⟨l, hl⟩ ∈ Pz :=
    Subgroup.mem_map.2 ⟨⟨l, hl⟩, Subgroup.mem_subgroupOf.2 hlX, rfl⟩
  rw [hPzP2] at hα
  have hlC : l ∈ L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
    rw [hCZ]; exact ⟨⟨l, hl⟩, hα, rfl⟩
  exact Subgroup.mul_mem _ (hPH hlC) (hTH ht)

end CFSG.Quasithin.H13.NFa2
