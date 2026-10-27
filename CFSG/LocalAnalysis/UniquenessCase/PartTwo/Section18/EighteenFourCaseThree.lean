module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenFourWeak
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenFourE3Cent
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.OmegaFourGen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7SixtyTwoLift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyOne

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6 CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {V₀ V : Subgroup G} {L K : Subgroup G}

@[expose] def K_OmegaFour_scalarOfLine : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (S : OmegaModel W), Nat.card S.K = 4 →
    ∀ a ∈ Subgroup.normalizer (S.omega : Set (MulAut W)), a ^ 3 = 1 →
      (∃ e : W, e ≠ 1 ∧ S.Q e = 0 ∧
        ∀ w : W, a w = w ↔ ∃ c : S.K, w = S.smul c e) →
        ∃ x ∈ S.omega, a * x⁻¹ ≠ 1 ∧ (a * x⁻¹) ^ 3 = 1 ∧
          a * x⁻¹ ∈ Subgroup.centralizer (S.omega : Set (MulAut W))

theorem A5Config18.omegaFourSetting_of_case_three (c : A5Config18 D V₀ V L K)
    (h3 : CaseThree18 D V L K c.elemAbelian) (h111 : W3Thm111 G) :
    ∃ S : OmegaModel (Vtil ⊥ V c.elemAbelian),
      OmegaFourSetting D V c.elemAbelian S ∧
        S.omega = barSub ⊥ V c.elemAbelian (L ⊔ K) := by
  have hv0 : V₀ = ⊥ := c.v0
  subst V₀
  have hV := c.elemAbelian
  have hp125 : Hyp125 D ⊥ V := c.pair.data.hyp.hyp125
  have hpF : PairFacts D.M ⊥ V := hp125.pairFacts
  have hLstab : L ≤ stabTil ⊥ V :=
    c.pair.mem_calC_L.1.le.trans (le_stabTil hpF.le_normalizer hpF.le_normalizer₀)
  have hKstab : K ≤ stabTil ⊥ V :=
    c.pair.mem_calC.1.le.trans (le_stabTil hpF.le_normalizer hpF.le_normalizer₀)
  have hsup : barSub ⊥ V hV (L ⊔ K) =
      barSub ⊥ V hV L ⊔ barSub ⊥ V hV K :=
    s16c7_barSub_sup ⊥ V hV hLstab hKstab
  have h3' : IsOmegaPlus ↥(barSub ⊥ V hV L ⊔ barSub ⊥ V hV K) 4 2 ∧
      NatOmegaPlus (barSub ⊥ V hV L ⊔ barSub ⊥ V hV K) ⊤ ⊥ 4 2 := h3
  obtain ⟨S, hSomega, hScard⟩ :=
    exists_omegaModel_of_natOmegaPlus (W := Vtil ⊥ V hV)
      (H := barSub ⊥ V hV (L ⊔ K)) (a := 2) (by norm_num) (hsup.symm ▸ h3'.2)
  refine ⟨S, ?_, hSomega⟩
  have hLKM : L ⊔ K ≤ D.M := sup_le c.pair.mem_calC_L.1.le c.pair.mem_calC.1.le
  have hbarNorm : ((barSub ⊥ V hV (L ⊔ K)).subgroupOf (Mbar D.M ⊥ V hV)).Normal :=
    barSub_subgroupOf_mbar_normal hV hLKM
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hLKM).1 c.pair.sup_normal)
  have hleNormalizer : Mbar D.M ⊥ V hV ≤
      Subgroup.normalizer (barSub ⊥ V hV (L ⊔ K) : Set (MulAut (Vtil ⊥ V hV))) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (barSub_mono ⊥ V hV hLKM)).1 hbarNorm
  have hWone : ⁅E3.wClos V 1 D.T, V⁆ = ⊥ := by
    have hm2 : MBarGT D.M ⊥ V 2 :=
      (hp125.mBarGT_iff_lt_mBar 2).2 (by rw [c.numerics.1]; norm_num)
    exact commutator_wClos_eq_bot_of_lt D h111 hp125 hm2
      (by rw [c.numerics.2.1, c.numerics.1]; norm_num)
  exact
    { hyp125 := hp125
      five_mem := c.pair.data.hyp.hp
      card_K := by rw [hScard]; norm_num
      omega_le := by
        rw [hSomega, hsup]
        exact sup_le (barSub_mono ⊥ V hV c.pair.mem_calC_L.1.le)
          (barSub_mono ⊥ V hV c.pair.mem_calC.1.le)
      le_normalizer := by rw [hSomega]; exact hleNormalizer
      wOne := hWone
      aBar_le := by rw [c.numerics.2.1]
      mBar_eq := c.numerics.1 }

@[expose] noncomputable def bar2ActTilHom {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    {M : Subgroup G} (hMS : M ≤ stabTil V₀ V)
    (h2 : barSub V₀ V hV (pCoreOf 2 M) = ⊥) :
    Bar2 M →* ↥(barSub V₀ V hV M) := by
  classical
  let φ : ↥M →* ↥(barSub V₀ V hV M) :=
    ((actTil V₀ V hV).comp (Subgroup.inclusion hMS)).codRestrict
      (barSub V₀ V hV M) (fun x => actTil_mem_barSub V₀ V hV x.2 (hMS x.2))
  have hker : CFSG.pCore 2 ↥M ≤ φ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    have hxP : (x : G) ∈ pCoreOf 2 M := ⟨x, hx, rfl⟩
    have h1 : actTil V₀ V hV ⟨(x : G), hMS x.2⟩ ∈ barSub V₀ V hV (pCoreOf 2 M) :=
      actTil_mem_barSub V₀ V hV hxP (hMS x.2)
    rw [h2, Subgroup.mem_bot] at h1
    exact Subtype.ext h1
  exact QuotientGroup.lift (CFSG.pCore 2 ↥M) φ hker

theorem bar2ActTilHom_mk {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) {M : Subgroup G}
    (hMS : M ≤ stabTil V₀ V) (h2 : barSub V₀ V hV (pCoreOf 2 M) = ⊥) (x : ↥M) :
    bar2ActTilHom hV hMS h2 (QuotientGroup.mk x) =
      ⟨actTil V₀ V hV ⟨(x : G), hMS x.2⟩,
        actTil_mem_barSub V₀ V hV x.2 (hMS x.2)⟩ := by
  rw [bar2ActTilHom, QuotientGroup.lift_mk]
  rfl

theorem bar2ActTilHom_surjective {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) {M : Subgroup G}
    (hMS : M ≤ stabTil V₀ V) (h2 : barSub V₀ V hV (pCoreOf 2 M) = ⊥) :
    Function.Surjective (bar2ActTilHom hV hMS h2) := by
  intro y
  obtain ⟨a, haM, hay⟩ := (mem_barSub V₀ V hV M (y : MulAut (Vtil V₀ V hV))).1 y.2
  refine ⟨QuotientGroup.mk ⟨(a : G), haM⟩, ?_⟩
  apply Subtype.ext
  rw [bar2ActTilHom_mk]
  simpa [show (⟨(a : G), hMS haM⟩ : ↥(stabTil V₀ V)) = a from Subtype.ext rfl] using hay

theorem A5Config18.three_dvd_cent_of_case_three
    (c : A5Config18 D V₀ V L K)
    (h3 : CaseThree18 D V L K c.elemAbelian) (hKs : K_OmegaFour_scalarOfLine)
    (h111 : W3Thm111 G) (hW612 : W3Lem612 G) (h61 : UC6.R6_1 D) (hx : DataExt D)
    (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1) :
    3 ∣ Nat.card ↥(Subgroup.centralizer
      (barImage D.M (L ⊔ K) : Set (Bar2 D.M))) := by
  have hv0 : V₀ = ⊥ := c.v0
  subst V₀
  have hV := c.elemAbelian
  have hp125 : Hyp125 D ⊥ V := c.pair.data.hyp.hyp125
  have hpF : PairFacts D.M ⊥ V := hp125.pairFacts
  have hLM : L ≤ D.M := c.pair.mem_calC_L.1.le
  have hKM : K ≤ D.M := c.pair.mem_calC.1.le
  have hLKM : L ⊔ K ≤ D.M := sup_le hLM hKM
  have hMS : D.M ≤ stabTil ⊥ V := le_stabTil hpF.le_normalizer hpF.le_normalizer₀
  have h2M : barSub ⊥ V hV (pCoreOf 2 D.M) = ⊥ := barSub_pCoreOf_eq_bot_of_hyp125 hp125
  have hLstab : L ≤ stabTil ⊥ V := hLM.trans hMS
  have hKstab : K ≤ stabTil ⊥ V := hKM.trans hMS
  have hLbarAlt : IsAlt ↥(barSub ⊥ V hV L) 5 :=
    isAlt_barSub_of_isAlt_bar2 hp125 c.pair.mem_calC_L c.barSubL c.pair.data.alt
  have hKbarAlt : IsAlt ↥(barSub ⊥ V hV K) 5 :=
    isAlt_barSub_of_isAlt_bar2 hp125 c.pair.mem_calC c.barSubK c.pair.alt_K
  have hcardLbar : Nat.card ↥(barSub ⊥ V hV L) = 60 :=
    Om8Excl.card_isAlt_five hLbarAlt
  have hcardKbar : Nat.card ↥(barSub ⊥ V hV K) = 60 :=
    Om8Excl.card_isAlt_five hKbarAlt
  have hcardBL : Nat.card ↥(barImage D.M L) = 60 := by
    rw [S17.card_barImage_eq_card_bar c.pair.mem_calC_L, Om8Excl.card_isAlt_five c.pair.data.alt]
  have hcardBK : Nat.card ↥(barImage D.M K) = 60 := by
    rw [S17.card_barImage_eq_card_bar c.pair.mem_calC, Om8Excl.card_isAlt_five c.pair.alt_K]
  have hcommB : ∀ a ∈ barImage D.M L, ∀ b ∈ barImage D.M K, a * b = b * a :=
    UC22.uc22p22l_barImage_commute c.pair.mem_calC_L c.pair.mem_calC c.pair.ne_L.symm
  have hAzBar2L : Subgroup.center (Bar2 L) = ⊥ := by
    have e5 : Bar2 L ≃* alternatingGroup (Fin 5) := c.pair.data.alt.some
    exact CFSG.ABGLocalTools.center_eq_bot_of_mulEquiv e5
      (alternatingGroup.center_eq_bot (by norm_num))
  have hAzBL : Subgroup.center ↥(barImage D.M L) = ⊥ := by
    obtain ⟨e⟩ := s13_bar_equiv c.pair.mem_calC_L
    exact CFSG.ABGLocalTools.center_eq_bot_of_mulEquiv e.symm hAzBar2L
  have hBcent : barImage D.M K ≤ Subgroup.centralizer (barImage D.M L : Set (Bar2 D.M)) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact hcommB a ha b hb
  have hdisjB : barImage D.M L ⊓ barImage D.M K = ⊥ :=
    eq_bot_iff.mpr ((inf_le_inf_left _ hBcent).trans_eq
      (CFSG.AGLEmbedding.inf_centralizer_eq_bot_of_center hAzBL))
  have hcardXbar : Nat.card ↥(barImage D.M (L ⊔ K)) = 3600 := by
    rw [s13_barImage_sup hLM hKM]
    have hprod := CFSG.Quasithin.Vol2.Ch10.SecE.prodEquivSup
      (P₁ := barImage D.M L) (P₂ := barImage D.M K) hcommB hdisjB
    rw [← Nat.card_congr hprod.toEquiv, Nat.card_prod, hcardBL, hcardBK]
  have hAzBar2K : Subgroup.center (Bar2 K) = ⊥ := by
    have e5 : Bar2 K ≃* alternatingGroup (Fin 5) := c.pair.alt_K.some
    exact CFSG.ABGLocalTools.center_eq_bot_of_mulEquiv e5
      (alternatingGroup.center_eq_bot (by norm_num))
  have hAzBK : Subgroup.center ↥(barImage D.M K) = ⊥ := by
    obtain ⟨e⟩ := s13_bar_equiv c.pair.mem_calC
    exact CFSG.ABGLocalTools.center_eq_bot_of_mulEquiv e.symm hAzBar2K
  have hcommBar : ∀ a ∈ barSub ⊥ V hV L, ∀ b ∈ barSub ⊥ V hV K, a * b = b * a := by
    intro a ha b hb
    obtain ⟨g, hgL, rfl⟩ := (mem_barSub ⊥ V hV L a).1 ha
    obtain ⟨h, hhK, rfl⟩ := (mem_barSub ⊥ V hV K b).1 hb
    have hgb : QuotientGroup.mk ⟨(g : G), hLM hgL⟩ ∈ barImage D.M L :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hgL)
    have hhb : QuotientGroup.mk ⟨(h : G), hKM hhK⟩ ∈ barImage D.M K :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hhK)
    have hgg : (⟨(g : G), hMS (hLM hgL)⟩ : ↥(stabTil ⊥ V)) = g := Subtype.ext rfl
    have hhh : (⟨(h : G), hMS (hKM hhK)⟩ : ↥(stabTil ⊥ V)) = h := Subtype.ext rfl
    have hgφ : ((bar2ActTilHom hV hMS h2M (QuotientGroup.mk ⟨(g : G), hLM hgL⟩) :
        ↥(barSub ⊥ V hV D.M)) : MulAut (Vtil ⊥ V hV)) = actTil ⊥ V hV g := by
      rw [bar2ActTilHom_mk]
    have hhφ : ((bar2ActTilHom hV hMS h2M (QuotientGroup.mk ⟨(h : G), hKM hhK⟩) :
        ↥(barSub ⊥ V hV D.M)) : MulAut (Vtil ⊥ V hV)) = actTil ⊥ V hV h := by
      rw [bar2ActTilHom_mk]
    calc actTil ⊥ V hV g * actTil ⊥ V hV h
        = ((bar2ActTilHom hV hMS h2M (QuotientGroup.mk ⟨(g : G), hLM hgL⟩) :
            ↥(barSub ⊥ V hV D.M)) : MulAut (Vtil ⊥ V hV)) *
          ((bar2ActTilHom hV hMS h2M (QuotientGroup.mk ⟨(h : G), hKM hhK⟩) :
            ↥(barSub ⊥ V hV D.M)) : MulAut (Vtil ⊥ V hV)) := by
          rw [← hgφ, ← hhφ]
      _ = ((bar2ActTilHom hV hMS h2M (QuotientGroup.mk ⟨(g : G), hLM hgL⟩ *
            QuotientGroup.mk ⟨(h : G), hKM hhK⟩) : ↥(barSub ⊥ V hV D.M)) :
            MulAut (Vtil ⊥ V hV)) := by
          rw [map_mul]
          rfl
      _ = ((bar2ActTilHom hV hMS h2M (QuotientGroup.mk ⟨(h : G), hKM hhK⟩ *
            QuotientGroup.mk ⟨(g : G), hLM hgL⟩) : ↥(barSub ⊥ V hV D.M)) :
            MulAut (Vtil ⊥ V hV)) := by rw [hcommB _ hgb _ hhb]
      _ = actTil ⊥ V hV h * actTil ⊥ V hV g := by
        rw [map_mul]
        change ((bar2ActTilHom hV hMS h2M (QuotientGroup.mk ⟨(h : G), hKM hhK⟩) :
          ↥(barSub ⊥ V hV D.M)) : MulAut (Vtil ⊥ V hV)) *
          ((bar2ActTilHom hV hMS h2M (QuotientGroup.mk ⟨(g : G), hLM hgL⟩) :
          ↥(barSub ⊥ V hV D.M)) : MulAut (Vtil ⊥ V hV)) =
          actTil ⊥ V hV h * actTil ⊥ V hV g
        rw [hhφ, hgφ]
  have hAzBarL : Subgroup.center ↥(barSub ⊥ V hV L) = ⊥ := by
    have e5 : ↥(barSub ⊥ V hV L) ≃* alternatingGroup (Fin 5) := hLbarAlt.some
    exact CFSG.ABGLocalTools.center_eq_bot_of_mulEquiv e5
      (alternatingGroup.center_eq_bot (by norm_num))
  have hBcentBar : barSub ⊥ V hV K ≤
      Subgroup.centralizer (barSub ⊥ V hV L : Set (MulAut (Vtil ⊥ V hV))) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact hcommBar a ha b hb
  have hdisjBar : barSub ⊥ V hV L ⊓ barSub ⊥ V hV K = ⊥ :=
    eq_bot_iff.mpr ((inf_le_inf_left _ hBcentBar).trans_eq
      (CFSG.AGLEmbedding.inf_centralizer_eq_bot_of_center hAzBarL))
  have hcardXcod : Nat.card ↥(barSub ⊥ V hV (L ⊔ K)) = 3600 := by
    rw [s16c7_barSub_sup ⊥ V hV hLstab hKstab]
    have hprod := CFSG.Quasithin.Vol2.Ch10.SecE.prodEquivSup
      (P₁ := barSub ⊥ V hV L) (P₂ := barSub ⊥ V hV K) hcommBar hdisjBar
    rw [← Nat.card_congr hprod.toEquiv, Nat.card_prod, hcardLbar, hcardKbar]
  have hmemX : ∀ y ∈ barImage D.M (L ⊔ K),
      ((bar2ActTilHom hV hMS h2M y : ↥(barSub ⊥ V hV D.M)) :
        MulAut (Vtil ⊥ V hV)) ∈ barSub ⊥ V hV (L ⊔ K) := by
    rintro y ⟨x, hx, rfl⟩
    change ((bar2ActTilHom hV hMS h2M (QuotientGroup.mk x) : ↥(barSub ⊥ V hV D.M)) :
      MulAut (Vtil ⊥ V hV)) ∈ barSub ⊥ V hV (L ⊔ K)
    rw [bar2ActTilHom_mk]
    exact actTil_mem_barSub ⊥ V hV (Subgroup.mem_subgroupOf.1 hx) (hMS x.2)
  let φM' : Bar2 D.M →* MulAut (Vtil ⊥ V hV) :=
    (barSub ⊥ V hV D.M).subtype.comp (bar2ActTilHom hV hMS h2M)
  let ψ : ↥(barImage D.M (L ⊔ K)) →* ↥(barSub ⊥ V hV (L ⊔ K)) :=
    (φM'.comp (barImage D.M (L ⊔ K)).subtype).codRestrict
      (barSub ⊥ V hV (L ⊔ K)) (fun y => hmemX y.val y.2)
  have hsurjψ : Function.Surjective ψ := by
    intro y
    obtain ⟨g, hgX, hgy⟩ := (mem_barSub ⊥ V hV (L ⊔ K) (y : MulAut (Vtil ⊥ V hV))).1 y.2
    have hgb : QuotientGroup.mk ⟨(g : G), hLKM hgX⟩ ∈ barImage D.M (L ⊔ K) :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hgX)
    refine ⟨⟨QuotientGroup.mk ⟨(g : G), hLKM hgX⟩, hgb⟩, ?_⟩
    apply Subtype.ext
    have hgg : (⟨(g : G), hMS (hLKM hgX)⟩ : ↥(stabTil ⊥ V)) = g := Subtype.ext rfl
    change ((bar2ActTilHom hV hMS h2M
      (QuotientGroup.mk ⟨(g : G), hLKM hgX⟩) : ↥(barSub ⊥ V hV D.M)) :
      MulAut (Vtil ⊥ V hV)) = (y : MulAut (Vtil ⊥ V hV))
    rw [bar2ActTilHom_mk]
    change actTil ⊥ V hV ⟨(g : G), hMS (hLKM hgX)⟩ = (y : MulAut (Vtil ⊥ V hV))
    rw [hgg]
    exact hgy
  have hkerψ : ψ.ker = ⊥ := by
    have hmul := Subgroup.card_ker_mul_card_range ψ
    have hrange : Nat.card ↥ψ.range = Nat.card ↥(barSub ⊥ V hV (L ⊔ K)) := by
      rw [MonoidHom.range_eq_top.2 hsurjψ]
      simp
    have hcard : Nat.card ↥ψ.ker * 3600 = 3600 := by
      rw [hrange, hcardXcod] at hmul
      rwa [hcardXbar] at hmul
    have hk : Nat.card ↥ψ.ker = 1 := by
      have h' : Nat.card ↥ψ.ker * 3600 = 1 * 3600 := by
        rw [one_mul]
        exact hcard
      exact Nat.mul_right_cancel (n := Nat.card ↥ψ.ker) (k := 1) (m := 3600)
        (by norm_num) h'
    exact Subgroup.eq_bot_of_card_eq _ hk
  have hinjψ : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).1 hkerψ
  obtain ⟨S, hS, hSomega⟩ := c.omegaFourSetting_of_case_three h3 h111
  obtain ⟨Vg, g, rfl, hO⟩ :=
    hS.calOStar_two_nonempty D h61 hx hSg h1219 hW612 c.numerics.2.2.2
  obtain ⟨a, haM, ha3, e, he1, heQ, hafix⟩ :=
    hS.exists_order_three_fix_line D h61 hx hSg h1219 hO
  obtain ⟨x, hxS, hcne, hc3, hccent⟩ :=
    hKs (Vtil ⊥ V c.elemAbelian) S hS.card_K a (hS.le_normalizer haM) ha3
      ⟨e, he1, heQ, hafix⟩
  have hxM : x ∈ Mbar D.M ⊥ V hV := hS.omega_le hxS
  have hcbarM : a * x⁻¹ ∈ Mbar D.M ⊥ V hV :=
    (Mbar D.M ⊥ V hV).mul_mem haM ((Mbar D.M ⊥ V hV).inv_mem hxM)
  have hcbarCent : a * x⁻¹ ∈ Subgroup.centralizer
      (barSub ⊥ V hV (L ⊔ K) : Set (MulAut (Vtil ⊥ V hV))) := by
    rw [← hSomega]
    exact hccent
  have hcbar3 : (a * x⁻¹) ^ 3 = 1 := hc3
  have hcbar_ne : a * x⁻¹ ≠ 1 := hcne
  obtain ⟨cstar, hcstar⟩ := bar2ActTilHom_surjective hV hMS h2M ⟨a * x⁻¹, hcbarM⟩
  have hcstarCent : cstar ∈ Subgroup.centralizer
      (barImage D.M (L ⊔ K) : Set (Bar2 D.M)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hN : (barImage D.M (L ⊔ K)).Normal := s13_barImage_normal c.pair.sup_normal
    have hzX : cstar * y * cstar⁻¹ * y⁻¹ ∈ barImage D.M (L ⊔ K) :=
      (barImage D.M (L ⊔ K)).mul_mem
        (hN.conj_mem y hy cstar)
        ((barImage D.M (L ⊔ K)).inv_mem hy)
    have hz1 : bar2ActTilHom hV hMS h2M (cstar * y * cstar⁻¹ * y⁻¹) = 1 := by
      apply Subtype.ext
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one]
      rw [show ((bar2ActTilHom hV hMS h2M) cstar : MulAut (Vtil ⊥ V hV)) =
        a * x⁻¹ from congrArg Subtype.val hcstar]
      have hyH : ((bar2ActTilHom hV hMS h2M) y : MulAut (Vtil ⊥ V hV)) ∈
          barSub ⊥ V hV (L ⊔ K) := hmemX y hy
      have hcomm := Subgroup.mem_centralizer_iff.1 hcbarCent
        ((bar2ActTilHom hV hMS h2M) y : MulAut (Vtil ⊥ V hV)) hyH
      calc (a * x⁻¹) * ((bar2ActTilHom hV hMS h2M) y : MulAut (Vtil ⊥ V hV)) *
            (a * x⁻¹)⁻¹ * (((bar2ActTilHom hV hMS h2M) y : MulAut (Vtil ⊥ V hV)))⁻¹
          = (((bar2ActTilHom hV hMS h2M) y : MulAut (Vtil ⊥ V hV)) * (a * x⁻¹)) *
              (a * x⁻¹)⁻¹ *
              (((bar2ActTilHom hV hMS h2M) y : MulAut (Vtil ⊥ V hV)))⁻¹ := by
            rw [hcomm]
        _ = 1 := by group
    have hψz : ψ ⟨cstar * y * cstar⁻¹ * y⁻¹, hzX⟩ = 1 := by
      apply Subtype.ext
      change ((bar2ActTilHom hV hMS h2M (cstar * y * cstar⁻¹ * y⁻¹) :
        ↥(barSub ⊥ V hV D.M)) : MulAut (Vtil ⊥ V hV)) = 1
      exact congrArg Subtype.val hz1
    have hz : cstar * y * cstar⁻¹ * y⁻¹ = 1 := by
      have h1 : (⟨cstar * y * cstar⁻¹ * y⁻¹, hzX⟩ : ↥(barImage D.M (L ⊔ K))) = 1 :=
        hinjψ (by rw [hψz, map_one])
      exact Subtype.ext_iff.1 h1
    have h1 : cstar * y * cstar⁻¹ = y := by
      have := congrArg (fun t => t * y) hz
      simpa [mul_assoc] using this
    have h2 : cstar * y = y * cstar := by
      have := congrArg (fun t => t * cstar) h1
      simpa [mul_assoc] using this
    exact h2.symm
  have h3order : 3 ∣ orderOf cstar := by
    have hdvd := orderOf_map_dvd (bar2ActTilHom hV hMS h2M) cstar
    rw [hcstar] at hdvd
    have hcbarord : orderOf (a * x⁻¹) = 3 := orderOf_eq_prime hcbar3 hcbar_ne
    rwa [show orderOf (⟨a * x⁻¹, hcbarM⟩ : ↥(Mbar D.M ⊥ V hV)) = 3 by
      rw [← Subgroup.orderOf_coe]; exact hcbarord] at hdvd
  have hdvdC : orderOf cstar ∣ Nat.card ↥(Subgroup.centralizer
      (barImage D.M (L ⊔ K) : Set (Bar2 D.M))) :=
    Subgroup.orderOf_dvd_natCard (Subgroup.centralizer
      (barImage D.M (L ⊔ K) : Set (Bar2 D.M))) hcstarCent
  exact h3order.trans hdvdC

theorem A5Config18.false_of_case_three
    (c : A5Config18 D V₀ V L K)
    (h3 : CaseThree18 D V L K c.elemAbelian) (hKs : K_OmegaFour_scalarOfLine)
    (h76 : UC22.F07.R76Sig D) (h614 : UC6.R6_14 D)
    (h111 : W3Thm111 G) (hW612 : W3Lem612 G) (h61 : UC6.R6_1 D) (hx : DataExt D)
    (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1) (h1768 : S17.R17_68At D V₀ V) : False := by
  have hdiv := c.three_dvd_cent_of_case_three h3 hKs h111 hW612 h61 hx hSg h1219
  have hk1 : D.k = 1 :=
    c.pair.data.k_eq_one_of_three_dvd c.pair.mem_calC c.pair.ne_L c.pair.alt_K
      c.pair.commutator_le c.pair.dichotomy h76 h614 hSg h1768 hdiv
  have hk2 : D.k = 2 := c.numerics.2.2.1
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
