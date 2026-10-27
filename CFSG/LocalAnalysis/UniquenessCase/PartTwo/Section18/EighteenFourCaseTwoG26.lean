module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenFourCaseTwoDelta
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenFourCaseThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenFourCaseTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {V₀ V L K : Subgroup G}

theorem A5Data18.component_le_Opp_five {D : Data G} {V₀ V L J : Subgroup G}
    (c : A5Data18 D V₀ V L) (hJ : J ∈ calC D.M) : J ≤ Opp 5 D.M := by
  have hJM : J ≤ D.M := s13_le_of_mem_calC hJ
  have hJperf : ⁅J, J⁆ = J := hJ.2.1
  have hJcomp : CFSG.IsComponent (barImage D.M J) := s13_barImage_isComponent hJ
  have hJleO : J ≤ oTwoEOf D.M := by
    intro x hx
    have hxM : x ∈ D.M := hJM hx
    have hxbar : QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨x, hxM⟩ ∈ barImage D.M J :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hx)
    exact Subgroup.mem_map.2
      ⟨⟨x, hxM⟩, Subgroup.mem_comap.2 (CFSG.LocalCores.component_le_layer hJcomp hxbar), rfl⟩
  exact (uc22p21c_le_Hinf hJleO hJperf).trans c.hinf

theorem A5Data18.barImage_le_pElementSubgroup {D : Data G} {V₀ V L J : Subgroup G}
    (c : A5Data18 D V₀ V L) (hJ : J ∈ calC D.M) :
    barImage D.M J ≤ CFSG.RankThree.PartOne.pElementSubgroup 5
      (⊤ : Subgroup (Bar2 D.M)) := by
  calc barImage D.M J
      ≤ barImage D.M (Opp 5 D.M) := by
        change ((J.subgroupOf D.M).map _) ≤ _
        exact Subgroup.map_mono (Subgroup.subgroupOf_mono D.M (c.component_le_Opp_five hJ))
    _ = CFSG.RankThree.PartOne.pElementSubgroup 5 (⊤ : Subgroup (Bar2 D.M)) := by
        rw [s13_barImage_opp Nat.prime_five (le_refl D.M), s13_barImage_self]

theorem mem_normalizer_preTil_fixV_of_commute {V : Subgroup G} (hV : IsElemAbelian 2 V)
    {g : G} (hg : g ∈ stabTil ⊥ V) {t : MulAut (Vtil ⊥ V hV)}
    (hcomm : actTil ⊥ V hV ⟨g, hg⟩ * t = t * actTil ⊥ V hV ⟨g, hg⟩) :
    g ∈ Subgroup.normalizer
      (preTil ⊥ V hV (CFSG.Quasithin.fixV (Subgroup.zpowers t)) : Set G) := by
  have hcent : actTil ⊥ V hV ⟨g, hg⟩ ∈
      Subgroup.centralizer ({t} : Set (MulAut (Vtil ⊥ V hV))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact hcomm.symm
  have hcentZ : actTil ⊥ V hV ⟨g, hg⟩ ∈
      Subgroup.centralizer (Subgroup.zpowers t : Set (MulAut (Vtil ⊥ V hV))) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact hcent
  have hnorm : actTil ⊥ V hV ⟨g, hg⟩ ∈
      Subgroup.normalizer (Subgroup.zpowers t : Set (MulAut (Vtil ⊥ V hV))) :=
    Subgroup.centralizer_le_normalizer _ hcentZ
  have hstab : StableUnder (Mbar (Subgroup.zpowers g) ⊥ V hV)
      (CFSG.Quasithin.fixV (Subgroup.zpowers t)) := by
    intro y hy u hu
    obtain ⟨z, hz, hzy⟩ := (mem_barSub ⊥ V hV (Subgroup.zpowers g) y).1 hy
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hzk : z = ⟨g, hg⟩ ^ k := Subtype.ext (by simpa using hk.symm)
    rw [← hzy, hzk, map_zpow]
    exact CFSG.Quasithin.fixV_apply_mem_of_mem_normalizer
      (Subgroup.zpow_mem (Subgroup.normalizer (Subgroup.zpowers t))
        (x := actTil ⊥ V hV ⟨g, hg⟩) hnorm k) hu
  have hMs : Subgroup.zpowers g ≤ stabTil ⊥ V := Subgroup.zpowers_le.mpr hg
  exact TwelveSeventeen.le_normalizer_preTil hV hMs hstab (Subgroup.mem_zpowers g)

theorem A5Config18.gap_18_4_ii_G26 (c : A5Config18 D V₀ V L K)
    (hK1 : K_OmegaPlusFour_twoNat_inv) :
    Gap_18_4_ii_G26 D V c.elemAbelian
      (barSub ⊥ V c.elemAbelian L ⊔ barSub ⊥ V c.elemAbelian K) := by
  intro hp125 hX hsum hm t ht htord htquot
  have hV0 : V₀ = ⊥ := c.v0
  subst V₀
  have hV : IsElemAbelian 2 V := c.elemAbelian
  have hpF : PairFacts D.M ⊥ V := hp125.pairFacts
  have hMS : D.M ≤ stabTil (⊥ : Subgroup G) V :=
    le_stabTil hpF.le_normalizer hpF.le_normalizer₀
  have h2M : barSub (⊥ : Subgroup G) V hV (pCoreOf 2 D.M) = ⊥ :=
    barSub_pCoreOf_eq_bot_of_hyp125 hp125
  have hLM : L ≤ D.M := c.pair.mem_calC_L.1.le
  have hKM : K ≤ D.M := c.pair.mem_calC.1.le
  have hLKM : L ⊔ K ≤ D.M := sup_le hLM hKM
  have hLstab : L ≤ stabTil (⊥ : Subgroup G) V := hLM.trans hMS
  have hKstab : K ≤ stabTil (⊥ : Subgroup G) V := hKM.trans hMS
  let W := Vtil (⊥ : Subgroup G) V hV
  let Xb : Subgroup (MulAut W) := barSub ⊥ V hV L ⊔ barSub ⊥ V hV K
  let X0 : Subgroup G := L ⊔ K
  let layer : Subgroup (Bar2 D.M) := barImage D.M X0
  let Q : Subgroup (Bar2 D.M) :=
    CFSG.RankThree.PartOne.pElementSubgroup 5 (⊤ : Subgroup (Bar2 D.M))
  let φ : Bar2 D.M →* MulAut W :=
    (barSub (⊥ : Subgroup G) V hV D.M).subtype.comp (bar2ActTilHom hV hMS h2M)
  have hXbar : barSub ⊥ V hV X0 = Xb := s16c7_barSub_sup ⊥ V hV hLstab hKstab
  have hlayerQ : layer ≤ Q := by
    have hL := c.pair.data.barImage_le_pElementSubgroup c.pair.mem_calC_L
    have hK := c.pair.data.barImage_le_pElementSubgroup c.pair.mem_calC
    calc layer = barImage D.M L ⊔ barImage D.M K := s13_barImage_sup hLM hKM
      _ ≤ Q := sup_le hL hK
  have hφmk : ∀ (x : ↥D.M) (hgs : (x : G) ∈ stabTil ⊥ V),
      φ (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) x) =
        actTil ⊥ V hV ⟨(x : G), hgs⟩ := by
    intro x hgs
    have h1 : ((bar2ActTilHom hV hMS h2M
        (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) x) :
        ↥(barSub ⊥ V hV D.M)) : MulAut W) = actTil ⊥ V hV ⟨(x : G), hMS x.2⟩ := by
      change ((bar2ActTilHom hV hMS h2M (QuotientGroup.mk x) :
        ↥(barSub ⊥ V hV D.M)) : MulAut W) = actTil ⊥ V hV ⟨(x : G), hMS x.2⟩
      rw [bar2ActTilHom_mk]
    exact h1.trans (congrArg (actTil ⊥ V hV) (Subtype.ext rfl))
  have hmemL : ∀ q ∈ barImage D.M L, φ q ∈ barSub ⊥ V hV L := by
    intro q hq
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hq
    rw [hφmk x (hMS x.2)]
    exact actTil_mem_barSub ⊥ V hV (Subgroup.mem_subgroupOf.mp hx) (hMS x.2)
  have hmemK : ∀ q ∈ barImage D.M K, φ q ∈ barSub ⊥ V hV K := by
    intro q hq
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hq
    rw [hφmk x (hMS x.2)]
    exact actTil_mem_barSub ⊥ V hV (Subgroup.mem_subgroupOf.mp hx) (hMS x.2)
  have hsurjL : ∀ x ∈ barSub ⊥ V hV L, ∃ q ∈ barImage D.M L, φ q = x := by
    intro x hx
    obtain ⟨g, hgL, hgact⟩ := (mem_barSub ⊥ V hV L x).1 hx
    have hgM : (g : G) ∈ D.M := hLM hgL
    refine ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨(g : G), hgM⟩,
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hgL), ?_⟩
    rw [hφmk ⟨(g : G), hgM⟩ (hMS hgM)]
    exact hgact
  have hsurjK : ∀ x ∈ barSub ⊥ V hV K, ∃ q ∈ barImage D.M K, φ q = x := by
    intro x hx
    obtain ⟨g, hgK, hgact⟩ := (mem_barSub ⊥ V hV K x).1 hx
    have hgM : (g : G) ∈ D.M := hKM hgK
    refine ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨(g : G), hgM⟩,
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hgK), ?_⟩
    rw [hφmk ⟨(g : G), hgM⟩ (hMS hgM)]
    exact hgact
  have hlayerEq : layer = barImage D.M L ⊔ barImage D.M K := s13_barImage_sup hLM hKM
  have hXle : Xb ≤ layer.map φ := by
    refine sup_le ?_ ?_
    · intro x hx
      obtain ⟨q, hq, hqφ⟩ := hsurjL x hx
      exact Subgroup.mem_map.mpr ⟨q, by rw [hlayerEq]; exact Subgroup.mem_sup_left hq, hqφ⟩
    · intro x hx
      obtain ⟨q, hq, hqφ⟩ := hsurjK x hx
      exact Subgroup.mem_map.mpr ⟨q, by rw [hlayerEq]; exact Subgroup.mem_sup_right hq, hqφ⟩
  have hcommLayer : ∀ a ∈ barImage D.M L, ∀ b ∈ barImage D.M K, a * b = b * a :=
    modO2Image_commute c.pair.commutator_le
  have hcommBar : ∀ a ∈ barSub ⊥ V hV L, ∀ b ∈ barSub ⊥ V hV K, a * b = b * a := by
    intro a ha b hb
    obtain ⟨qa, hqa, rfl⟩ := hsurjL a ha
    obtain ⟨qb, hqb, rfl⟩ := hsurjK b hb
    rw [← map_mul, ← map_mul]
    exact congrArg φ (hcommLayer qa hqa qb hqb)
  have hLbarAlt : IsAlt ↥(barSub ⊥ V hV L) 5 :=
    isAlt_barSub_of_isAlt_bar2 hp125 c.pair.mem_calC_L c.barSubL c.pair.data.alt
  have hKbarAlt : IsAlt ↥(barSub ⊥ V hV K) 5 :=
    isAlt_barSub_of_isAlt_bar2 hp125 c.pair.mem_calC c.barSubK c.pair.alt_K
  have hAzL : Subgroup.center ↥(barSub ⊥ V hV L) = ⊥ :=
    CFSG.ABGLocalTools.center_eq_bot_of_mulEquiv hLbarAlt.some
      (alternatingGroup.center_eq_bot (by norm_num))
  have hdisjBar : barSub ⊥ V hV L ⊓ barSub ⊥ V hV K = ⊥ := by
    refine eq_bot_iff.mpr ?_
    intro z hz
    have hzcent : (⟨z, hz.1⟩ : ↥(barSub ⊥ V hV L)) ∈
        Subgroup.center ↥(barSub ⊥ V hV L) := by
      rw [Subgroup.mem_center_iff]
      intro w
      apply Subtype.ext
      exact hcommBar w w.2 z hz.2
    rw [hAzL, Subgroup.mem_bot] at hzcent
    exact Subtype.ext_iff.mp hzcent
  have hkerL : ∀ q ∈ barImage D.M L, φ q = 1 → q = 1 := by
    intro q hq hq1
    let ψL : ↥(barImage D.M L) →* ↥(barSub ⊥ V hV L) :=
      (φ.comp (barImage D.M L).subtype).codRestrict (barSub ⊥ V hV L)
        (fun q => hmemL q.val q.2)
    have hsurjψL : Function.Surjective ψL := by
      intro z
      obtain ⟨g, hgL, hgact⟩ := (mem_barSub ⊥ V hV L (z : MulAut W)).1 z.2
      have hgM : (g : G) ∈ D.M := hLM hgL
      refine ⟨⟨QuotientGroup.mk ⟨(g : G), hgM⟩,
        Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hgL)⟩, ?_⟩
      apply Subtype.ext
      change φ (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨(g : G), hgM⟩) =
        (z : MulAut W)
      rw [hφmk ⟨(g : G), hgM⟩ (hMS hgM)]
      exact hgact
    have hcardL : Nat.card ↥(barImage D.M L) = Nat.card ↥(barSub ⊥ V hV L) := by
      obtain ⟨e1⟩ := s13_bar_equiv c.pair.mem_calC_L
      obtain ⟨e2⟩ := barSubBar2Equiv_of_isSimpleGroup hp125 c.pair.mem_calC_L c.barSubL
        (CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19.isSimpleGroup_bar2_of_isAlt_five
          c.pair.data.alt)
      exact (Nat.card_congr e1.toEquiv).symm.trans (Nat.card_congr e2.toEquiv)
    have hkerψL : ψL.ker = ⊥ := by
      have hmul := Subgroup.card_ker_mul_card_range ψL
      have hrange : Nat.card ↥ψL.range = Nat.card ↥(barSub ⊥ V hV L) := by
        rw [MonoidHom.range_eq_top.2 hsurjψL, Subgroup.card_top]
      rw [hrange, hcardL] at hmul
      have hC : 0 < Nat.card ↥(barSub ⊥ V hV L) :=
        Nat.card_pos_iff.mpr ⟨⟨1, (barSub ⊥ V hV L).one_mem⟩, inferInstance⟩
      have hk : Nat.card ↥ψL.ker = 1 :=
        Nat.eq_of_mul_eq_mul_right hC (by rw [hmul, one_mul])
      exact Subgroup.eq_bot_of_card_eq _ hk
    have hmem : (⟨q, hq⟩ : ↥(barImage D.M L)) ∈ ψL.ker := by
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      exact hq1
    rw [hkerψL, Subgroup.mem_bot] at hmem
    simpa using congrArg Subtype.val hmem
  have hkerK : ∀ q ∈ barImage D.M K, φ q = 1 → q = 1 := by
    intro q hq hq1
    let ψK : ↥(barImage D.M K) →* ↥(barSub ⊥ V hV K) :=
      (φ.comp (barImage D.M K).subtype).codRestrict (barSub ⊥ V hV K)
        (fun q => hmemK q.val q.2)
    have hsurjψK : Function.Surjective ψK := by
      intro z
      obtain ⟨g, hgK, hgact⟩ := (mem_barSub ⊥ V hV K (z : MulAut W)).1 z.2
      have hgM : (g : G) ∈ D.M := hKM hgK
      refine ⟨⟨QuotientGroup.mk ⟨(g : G), hgM⟩,
        Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hgK)⟩, ?_⟩
      apply Subtype.ext
      change φ (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨(g : G), hgM⟩) =
        (z : MulAut W)
      rw [hφmk ⟨(g : G), hgM⟩ (hMS hgM)]
      exact hgact
    have hcardK : Nat.card ↥(barImage D.M K) = Nat.card ↥(barSub ⊥ V hV K) := by
      obtain ⟨e1⟩ := s13_bar_equiv c.pair.mem_calC
      obtain ⟨e2⟩ := barSubBar2Equiv_of_isSimpleGroup hp125 c.pair.mem_calC c.barSubK
        (CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19.isSimpleGroup_bar2_of_isAlt_five
          c.pair.alt_K)
      exact (Nat.card_congr e1.toEquiv).symm.trans (Nat.card_congr e2.toEquiv)
    have hkerψK : ψK.ker = ⊥ := by
      have hmul := Subgroup.card_ker_mul_card_range ψK
      have hrange : Nat.card ↥ψK.range = Nat.card ↥(barSub ⊥ V hV K) := by
        rw [MonoidHom.range_eq_top.2 hsurjψK, Subgroup.card_top]
      rw [hrange, hcardK] at hmul
      have hC : 0 < Nat.card ↥(barSub ⊥ V hV K) :=
        Nat.card_pos_iff.mpr ⟨⟨1, (barSub ⊥ V hV K).one_mem⟩, inferInstance⟩
      have hk : Nat.card ↥ψK.ker = 1 :=
        Nat.eq_of_mul_eq_mul_right hC (by rw [hmul, one_mul])
      exact Subgroup.eq_bot_of_card_eq _ hk
    have hmem : (⟨q, hq⟩ : ↥(barImage D.M K)) ∈ ψK.ker := by
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      exact hq1
    rw [hkerψK, Subgroup.mem_bot] at hmem
    simpa using congrArg Subtype.val hmem
  have hdisjLayer : barImage D.M L ⊓ barImage D.M K = ⊥ :=
    barImage_inf_eq_bot_of_calC c.pair.mem_calC_L c.pair.mem_calC c.pair.ne_L
      c.pair.data.alt hcommLayer
  have hkerLayer : ∀ q ∈ layer, φ q = 1 → q = 1 := by
    intro q hq hq1
    have hq' : q ∈ barImage D.M L ⊔ barImage D.M K := by
      rw [← s13_barImage_sup hLM hKM]
      exact hq
    let eprod := CFSG.Quasithin.Vol2.Ch10.SecE.prodEquivSup hcommLayer hdisjLayer
    let p : ↥(barImage D.M L) × ↥(barImage D.M K) := eprod.symm ⟨q, hq'⟩
    have hqeq : (p.1 : Bar2 D.M) * p.2 = q := by
      have h := CFSG.Quasithin.Vol2.Ch10.SecE.coe_prodEquivSup hcommLayer hdisjLayer p
      rw [show eprod p = ⟨q, hq'⟩ from eprod.apply_symm_apply ⟨q, hq'⟩] at h
      exact h.symm
    have h1 : φ (p.1) * φ (p.2) = 1 := by
      rw [← map_mul, hqeq, hq1]
    have hmem : φ (p.1) ∈ barSub ⊥ V hV L ⊓ barSub ⊥ V hV K := by
      refine ⟨hmemL p.1 p.1.2, ?_⟩
      have h2 : φ (p.1) = (φ (p.2))⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [h2]
      exact (barSub ⊥ V hV K).inv_mem (hmemK p.2 p.2.2)
    rw [hdisjBar, Subgroup.mem_bot] at hmem
    have hp1 : (p.1 : Bar2 D.M) = 1 := hkerL p.1 p.1.2 hmem
    have hp2 : (p.2 : Bar2 D.M) = 1 := by
      apply hkerK p.2 p.2.2
      rw [show φ (p.2) = (φ (p.1))⁻¹ from eq_inv_of_mul_eq_one_right h1, hmem, inv_one]
    calc q = (p.1 : Bar2 D.M) * p.2 := hqeq.symm
      _ = 1 := by rw [hp1, hp2, one_mul]
  obtain ⟨e, he1, ⟨m⟩⟩ := c.pair.data.shape
  let A5 := alternatingGroup (Fin 5)
  let Zc := Multiplicative (ZMod (5 ^ e))
  have hcardZc : Nat.card Zc = 5 ^ e := by
    rw [Nat.card_congr
      (Multiplicative.ofAdd : ZMod (5 ^ e) ≃ Multiplicative (ZMod (5 ^ e))).symm,
      Nat.card_zmod]
  have h5Zc : 5 ∣ Nat.card Zc := by
    rw [hcardZc]
    exact dvd_pow_self 5 (by omega)
  obtain ⟨z, hzord⟩ := exists_prime_orderOf_dvd_card' (G := Zc) 5 h5Zc
  let zQ : ↥Q := m.symm (1, 1, z)
  have hz5 : z ^ 5 = 1 := by
    have h := pow_orderOf_eq_one z
    rwa [hzord] at h
  have hzQeq : m zQ = ((1 : A5), (1 : A5), z) := by
    change m (m.symm ((1 : A5), (1 : A5), z)) = _
    exact m.apply_symm_apply _
  have hz0pow : ((1 : A5), (1 : A5), z) ^ 5 = 1 := by
    ext <;> simp [hz5]
  have hzQ5 : zQ ^ 5 = 1 := by
    apply m.injective
    rw [map_pow, hzQeq, hz0pow, map_one]
  have hzQne : zQ ≠ 1 := by
    intro h1
    have h2 : ((1 : A5), (1 : A5), z) = 1 := by
      rw [← hzQeq, h1, map_one]
    have hz1 : z = 1 := by
      simpa using congrArg (fun p : A5 × A5 × Zc => p.2.2) h2
    rw [hz1, orderOf_one] at hzord
    omega
  have hzQord : orderOf zQ = 5 :=
    orderOf_eq_prime (p := 5) (hp := ⟨Nat.prime_five⟩) hzQ5 hzQne
  have hzQcenter : zQ ∈ Subgroup.center ↥Q := by
    rw [Subgroup.mem_center_iff]
    intro w
    apply m.injective
    rw [map_mul, map_mul, hzQeq]
    rcases m w with ⟨a, b, c⟩
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · simp
    · simp
    · exact mul_comm c z
  let zbar : MulAut W := (φ (zQ : Bar2 D.M) : MulAut W)
  have hzbar_cent : zbar ∈ Subgroup.centralizer (Xb : Set (MulAut W)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp (hXle hx)
    calc φ q * φ (zQ : Bar2 D.M) = φ (q * (zQ : Bar2 D.M)) := (map_mul φ q _).symm
      _ = φ ((zQ : Bar2 D.M) * q) := by
            congr 1
            exact congrArg Subtype.val
              (Subgroup.mem_center_iff.mp hzQcenter (⟨q, hlayerQ hq⟩ : ↥Q))
      _ = φ (zQ : Bar2 D.M) * φ q := map_mul φ _ q
  have hMbarN : Mbar D.M ⊥ V hV ≤
      Subgroup.normalizer (Xb : Set (MulAut W)) := by
    have hXnorm : ((barSub ⊥ V hV X0).subgroupOf (Mbar D.M ⊥ V hV)).Normal :=
      barSub_subgroupOf_mbar_normal hV hLKM
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hLKM).1 c.pair.sup_normal)
    have h := (Subgroup.normal_subgroupOf_iff_le_normalizer
      (show barSub ⊥ V hV X0 ≤ Mbar D.M ⊥ V hV from barSub_mono ⊥ V hV hLKM)).1 hXnorm
    rwa [hXbar] at h
  have htne : t ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at htord
    omega
  have ht2 : t ^ 2 = 1 := by
    rw [← htord]
    exact pow_orderOf_eq_one t
  have hKinst := hK1 W (s15_Infra_vtil_sq_eq_one (⊥ : Subgroup G) V hV) Xb
    (Subgroup.normalizer (Xb : Set (MulAut W))) Subgroup.le_normalizer le_rfl hX hsum
    t (hMbarN ht) htne ht2 htquot
  obtain ⟨y, hyord⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(Xb ⊓ Subgroup.centralizer ({t} : Set (MulAut W)))) 5 hKinst.2.1
  have hyX : (y : MulAut W) ∈ Xb := y.2.1
  have hyC : (y : MulAut W) ∈ Subgroup.centralizer ({t} : Set (MulAut W)) := y.2.2
  have hyordM : orderOf (y : MulAut W) = 5 := by
    rw [Subgroup.orderOf_coe y]
    exact hyord
  have hycomm : (y : MulAut W) * t = t * (y : MulAut W) :=
    (Subgroup.mem_centralizer_iff.mp hyC t (by simp)).symm
  obtain ⟨q, hqLayer, hqφ⟩ := Subgroup.mem_map.mp (hXle hyX)
  obtain ⟨x, hx, hxq⟩ := Subgroup.mem_map.mp hqLayer
  have hxX0 : (x : G) ∈ X0 := Subgroup.mem_subgroupOf.mp hx
  have hxM : (x : G) ∈ D.M := x.2
  have hqφ' : φ (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) x) = (y : MulAut W) := by
    rw [hxq]
    exact hqφ
  have hact : actTil ⊥ V hV ⟨(x : G), hMS hxM⟩ = (y : MulAut W) := by
    rw [← hφmk x (hMS hxM)]
    exact hqφ'
  let H : Subgroup G := D.M ⊓ Subgroup.normalizer
    (preTil (⊥ : Subgroup G) V hV (CFSG.Quasithin.fixV (Subgroup.zpowers t)) : Set G)
  have hxnorm : (x : G) ∈ Subgroup.normalizer
      (preTil (⊥ : Subgroup G) V hV (CFSG.Quasithin.fixV (Subgroup.zpowers t)) : Set G) := by
    apply mem_normalizer_preTil_fixV_of_commute hV (hMS hxM)
    rw [hact]
    exact hycomm
  have hxH : (x : G) ∈ H := ⟨hxM, hxnorm⟩
  have hqH : (QuotientGroup.mk x : Bar2 D.M) ∈ barImage D.M H :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hxH)
  obtain ⟨zrep, hzrep⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥D.M) (zQ : Bar2 D.M)
  have hzbarM : zbar ∈ Mbar D.M ⊥ V hV := by
    change φ (zQ : Bar2 D.M) ∈ barSub ⊥ V hV D.M
    exact (bar2ActTilHom hV hMS h2M (zQ : Bar2 D.M)).2
  have hzbarComm : zbar * t = t * zbar :=
    hKinst.1 zbar ⟨hMbarN hzbarM, hzbar_cent⟩
  have hzrepAct : actTil ⊥ V hV ⟨(zrep : G), hMS zrep.2⟩ = zbar := by
    rw [← hφmk zrep (hMS zrep.2)]
    exact congrArg (fun q : Bar2 D.M => φ q) hzrep
  have hznorm : (zrep : G) ∈ Subgroup.normalizer
      (preTil (⊥ : Subgroup G) V hV (CFSG.Quasithin.fixV (Subgroup.zpowers t)) : Set G) := by
    apply mem_normalizer_preTil_fixV_of_commute hV (hMS zrep.2)
    rw [hzrepAct]
    exact hzbarComm
  have hzH : (zrep : G) ∈ H := ⟨zrep.2, hznorm⟩
  have hzQH : (zQ : Bar2 D.M) ∈ barImage D.M H := by
    have h : (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) zrep : Bar2 D.M) ∈
        barImage D.M H :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hzH)
    rwa [hzrep] at h
  have hLbarA5 : S17.IsA5xA5 ↥layer :=
    isA5xA5_barImage_sup_of_calC c.pair.mem_calC_L c.pair.mem_calC c.pair.ne_L
      c.pair.data.alt c.pair.alt_K hcommLayer
  have hy5 : (y : MulAut W) ^ 5 = 1 := by
    rw [← hyordM]
    exact pow_orderOf_eq_one _
  have hqxLayer : (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) x : Bar2 D.M) ∈ layer := by
    rw [hxq]
    exact hqLayer
  have hqx5 : (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) x : Bar2 D.M) ^ 5 = 1 := by
    apply hkerLayer _ _ _
    · exact layer.pow_mem hqxLayer 5
    · rw [map_pow, hqφ', hy5]
  have hqxne : (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) x : Bar2 D.M) ≠ 1 := by
    intro h1
    have h2 : (y : MulAut W) = 1 := by
      rw [← hqφ', h1, map_one]
    rw [h2, orderOf_one] at hyordM
    omega
  have hqxord : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) x : Bar2 D.M) = 5 :=
    orderOf_eq_prime (p := 5) (hp := ⟨Nat.prime_five⟩) hqx5 hqxne
  have hzQordM : orderOf (zQ : Bar2 D.M) = 5 := by
    rw [Subgroup.orderOf_coe (H := Q) zQ]
    exact hzQord
  have hcommqz : (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) x : Bar2 D.M) * (zQ : Bar2 D.M) =
      (zQ : Bar2 D.M) * (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) x : Bar2 D.M) := by
    exact congrArg Subtype.val
      (Subgroup.mem_center_iff.mp hzQcenter
        (⟨(QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) x : Bar2 D.M), hlayerQ hqxLayer⟩ : ↥Q))
  have hzQnot : (zQ : Bar2 D.M) ∉
      Subgroup.zpowers (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) x : Bar2 D.M) := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hzLayer : (zQ : Bar2 D.M) ∈ layer := by
      rw [← hk]
      exact layer.zpow_mem hqxLayer k
    have hcentLayer : (⟨(zQ : Bar2 D.M), hzLayer⟩ : ↥layer) ∈
        Subgroup.center ↥layer := by
      rw [Subgroup.mem_center_iff]
      intro w
      have hc := Subgroup.mem_center_iff.mp hzQcenter
        (⟨(w : Bar2 D.M), hlayerQ w.2⟩ : ↥Q)
      exact Subtype.ext (by
        change (w : Bar2 D.M) * (zQ : Bar2 D.M) = (zQ : Bar2 D.M) * (w : Bar2 D.M)
        exact congrArg (fun z : ↥Q => (z : Bar2 D.M)) hc)
    rw [S17.center_eq_bot_of_isA5xA5 hLbarA5, Subgroup.mem_bot] at hcentLayer
    have hz1 : (zQ : Bar2 D.M) = 1 := by simpa using congrArg Subtype.val hcentLayer
    rw [hz1, orderOf_one] at hzQordM
    omega
  have hqH' : (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) x : Bar2 D.M) ∈
      barImage D.M H := by
    rw [QuotientGroup.mk'_apply]
    exact hqH
  have hrk : 2 ≤ CFSG.Open.pRank 5 (barImage D.M H) :=
    @CFSG.GroupTheory.two_le_pRank_of_commute (Bar2 D.M) _ _ 5 ⟨Nat.prime_five⟩
      (barImage D.M H) _ _ hqH' hzQH hqxord hzQordM hcommqz hzQnot
  have heq : CFSG.Open.pRank 5 (barImage D.M H) = CFSG.Open.pRank 5 H :=
    s13_pRank_barImage Nat.prime_five (by norm_num) inf_le_left
  change 1 < CFSG.Open.pRank 5 H
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
