module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanK9bCat
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanK2
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanKFacts
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanK12
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPFF2
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPL
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPL2
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPZ
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPZ2e
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPZ3b
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPZs
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WS6
import CFSG.Adapters.StatedSLPerfect
import CFSG.RankThree.PartTwo.Sec4.Item462AltProofModels
public import CFSG.GroupTheory.ExtraspecialThreeFive
import CFSG.RankThree.PartTwo.Sec4.Item462AltProofSetup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor)
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise
variable {G : Type} [Group G] [Finite G]
variable {D : Data G}
variable (c : Ctx82E3 D) {P A : Subgroup G} {a : G}

theorem g2_coprime_section''
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) (h7 : D.sig = {7})
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hNZ : Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) ≤ D.M)
    (haL : a ∈ P ⊓ c.L) (ha3 : orderOf a = 3) (haZ : a ∉ zSub P c.L)
    {J : Subgroup G} (hJ : J ∈ thetaComponentsAt 3 a) (h3 : 3 ∣ Nat.card J)
    {z : G} (hzZ : z ∈ zSub P c.L) (hz3 : orderOf z = 3)
    (hzN : z ∈ Subgroup.normalizer (J : Set G))
    (hK12 : K12SL)
    (hπ : thetaQuotMulAut J (J.normalizerMonoidHom ⟨z, hzN⟩) ≠ 1)
    (hiso : Nonempty (J0 J ≃* Xbar c P J))
    (hinner : thetaQuotMulAut J (J.normalizerMonoidHom ⟨z, hzN⟩) ∈
      (MulAut.conj : (Jtilde J) →* MulAut (Jtilde J)).range)
    {p f : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (hq : 3 ≤ p ^ f)
    (hmodel : CFSG.Blueprint.ChevalleyExceptionalModel (Xbar c P J) .G2 p f) :
    ∃ (S : Type) (_ : Group S) (_ : Finite S),
      IsSimpleGroup S ∧ (∃ x y : S, x * y ≠ y * x) ∧
      CFSG.SignalizerFunctorTheorem.IsSectionOf S ↥(CM c a) ∧
      ((p ^ f % 3 = 1 ∧ StatedClassicalModel S .PSL 3 p f) ∨
        (p ^ f % 3 = 2 ∧ StatedClassicalModel S .PSU 3 p f)) := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  have hK2 : K2ONanCentralizer := K2ONanCentralizer_holds
  have hK6 : K6ONanClasses := K6_of_K2 hK2
  let T : Subgroup G := P ⊓ Subgroup.centralizer ({a} : Set G)
  have hT : CFSG.ABGLocalTools.IsSylowOf 3 T (Subgroup.centralizer ({a} : Set G)) :=
    pcore_centralizer_le_theta_P1' hK2 hK6 c hON h7 hP hNZ haL ha3 haZ
  obtain ⟨wtilde, hwtilde⟩ := hinner
  let q0 : Jtilde J →* J0 J := QuotientGroup.mk' (Subgroup.center (Jtilde J))
  let qθ : ↥J →* Jtilde J := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥J)
  let q : ↥J →* J0 J := q0.comp qθ
  let w : J0 J := q0 wtilde
  obtain ⟨Syl, hwSyl, hwcenter, hword⟩ :=
    exists_w_central_sylow c hON h7 hP hNZ haL ha3 haZ hJ h3 hzZ hz3 hzN hT
      wtilde hwtilde hπ
  have hq4 : 4 ≤ p ^ f := by
    have hf : 0 < f := by
      rcases Nat.eq_zero_or_pos f with hf | hf
      · subst hf
        simp at hq
      · exact hf
    rcases Nat.lt_or_ge (p ^ f) 4 with hlt | hge
    · exfalso
      have hp2 : 2 ≤ p := hp.two_le
      have h3 : p ^ f = 3 := by omega
      have hp_dvd : p ∣ 3 := by
        rw [← h3]
        exact dvd_pow_self p hf.ne'
      exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hp_dvd)
    · exact hge
  obtain ⟨eiso⟩ := hiso
  have hmodelJ0 : CFSG.Blueprint.ChevalleyExceptionalModel (J0 J) .G2 p f :=
    CFSG.RankThree.PartOne.chevalleyExceptionalModel_congr eiso.symm hmodel
  let C : Subgroup (J0 J) := Subgroup.centralizer ({w} : Set (J0 J))
  have hSL : CFSG.RankThree.PartTwo.Sec4.IsSLThreePiAt ↥C (p ^ f) :=
    hK12 (J0 J) p f hp hp3 hq4 hmodelJ0 Syl ⟨w, hwSyl⟩ hwcenter hword
  have hfpos : 0 < f := by
    rcases Nat.eq_zero_or_pos f with hf | hf
    · subst hf
      simp at hq
    · exact hf
  have hf1 : 1 ≤ f := hfpos
  let Sq : Type := ↥C ⧸ Subgroup.center ↥C
  let qC : ↥C →* Sq := QuotientGroup.mk' (Subgroup.center ↥C)
  have hqC : Function.Surjective qC := QuotientGroup.mk'_surjective _
  have hCperf : Group.IsPerfect ↥C := by
    obtain ⟨K, hKfield, hKfin, hcase⟩ := hSL
    letI := hKfield
    letI := hKfin
    rcases hcase with ⟨hKcard, hmod1, ⟨eSL⟩⟩ | ⟨hKcard, hmod2, ⟨eSU⟩⟩
    · haveI : Group.IsPerfect ↥(CFSG.Open.StatedSL 3 K) :=
        CFSG.Open.StatedAPI.isPerfect_statedSL_of_three_le (by norm_num) K
      exact Group.IsPerfect.ofSurjective (f := eSL.symm.toMonoidHom) eSL.symm.surjective
    · haveI : Group.IsPerfect ↥(CFSG.Open.StatedSU 3 (p ^ f) K) :=
        CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hKcard (by norm_num) (by
          intro h
          have := congrArg Prod.snd h
          omega)
      exact Group.IsPerfect.ofSurjective (f := eSU.symm.toMonoidHom) eSU.symm.surjective
  have hSqperf : Group.IsPerfect Sq :=
    Group.IsPerfect.ofSurjective (f := qC) hqC
  have hIsoL : CFSG.RankThree.PartTwo.Sec4.IsoLThreePi Sq p f :=
    CFSG.RankThree.PartTwo.Sec4.Item462AltProof.isoLThreePi_quotient_center_of_isSLThreePiAt
      hf1 hSL
  have hSqsimple : IsSimpleGroup Sq := by
    rcases hIsoL with ⟨hmod, ⟨eSL⟩⟩ | ⟨hmod, ⟨eSU⟩⟩
    · letI : IsSimpleGroup (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField p f)) :=
        CFSG.PGLModel.isSimpleGroup_projSL_of_two_le (n := 3) (GaloisField p f)
          (by norm_num) (Or.inl (by norm_num)) (Or.inl (by norm_num))
      exact eSL.isSimpleGroup
    · have hadm : CFSG.Open.StatedLieAdmissible .PSU 3 p f := by
        refine ⟨hp, hf1, by norm_num, ?_⟩
        intro h
        have := congrArg Prod.snd h
        have hq2 : p ^ f ≠ 2 := by omega
        exact hq2 this
      letI : IsSimpleGroup (CFSG.Assembly.RankThreeEven.projSU 3 p f) :=
        CFSG.PGLModel.isSimpleGroup_projSU_of_admissible hadm
      exact eSU.isSimpleGroup
  have hSqnonab : ∃ x y : Sq, x * y ≠ y * x := by
    have hnc : ¬ IsMulCommutative Sq := Group.IsPerfect.not_isMulCommutative Sq
    by_contra h
    apply hnc
    refine isMulCommutative_iff.mpr ?_
    intro x y
    by_contra hxy
    exact h ⟨x, y, hxy⟩
  have hSqmodel : (p ^ f % 3 = 1 ∧ StatedClassicalModel Sq .PSL 3 p f) ∨
      (p ^ f % 3 = 2 ∧ StatedClassicalModel Sq .PSU 3 p f) := by
    rcases hIsoL with ⟨hmod, ⟨eSL⟩⟩ | ⟨hmod, ⟨eSU⟩⟩
    · left
      refine ⟨hmod, ?_⟩
      refine ⟨⟨hp, hf1, by norm_num, by simp, by simp⟩, ?_⟩
      refine ⟨GaloisField p f, inferInstance, inferInstance, ?_, ?_⟩
      · exact GaloisField.card p f (by omega)
      · exact ⟨eSL.trans (CFSG.PGLModel.projSLEquivStatedProj 3 (GaloisField p f))⟩
    · right
      have hadm : CFSG.Open.StatedLieAdmissible .PSU 3 p f := by
        refine ⟨hp, hf1, by norm_num, ?_⟩
        intro h
        have := congrArg Prod.snd h
        have hq2 : p ^ f ≠ 2 := by omega
        exact hq2 this
      refine ⟨hmod, hadm, ?_⟩
      refine ⟨GaloisField p (2 * f), inferInstance, inferInstance, ?_, ?_⟩
      · rw [GaloisField.card p (2 * f) (by omega), ← pow_mul]
        congr 1
        omega
      · exact ⟨eSU.trans (CFSG.PGLModel.projSUEquivStatedProj 3 p f)⟩
  have hz3pow : z ^ 3 = 1 := by
    rw [← hz3]
    exact pow_orderOf_eq_one z
  have hz3' : (⟨z, hzN⟩ : Subgroup.normalizer (J : Set G)) ^ 3 = 1 := by
    apply Subtype.ext
    simpa using hz3pow
  let ζ : MulAut (Jtilde J) := thetaQuotMulAut J (J.normalizerMonoidHom ⟨z, hzN⟩)
  have hsec : CFSG.SignalizerFunctorTheorem.IsSectionOf Sq ↥(CM c a) := by
    let Ctilde : Subgroup (Jtilde J) := C.comap q0
    let Cinf : Subgroup (Jtilde J) := ⁅Ctilde, Ctilde⁆
    let fixed : Subgroup (Jtilde J) :=
      MonoidHom.eqLocus ζ.toMonoidHom (MonoidHom.id (Jtilde J))
    have hζq0 : ∀ x : Jtilde J, q0 (ζ x) = w * q0 x * w⁻¹ := by
      intro x
      rw [show ζ = MulAut.conj wtilde from hwtilde.symm]
      simp [q0, w, MulAut.conj_apply, map_mul, map_inv]
    have hζC : ∀ x ∈ Ctilde, ζ x ∈ Ctilde := by
      intro x hx
      rw [Subgroup.mem_comap] at hx ⊢
      have hxw : q0 x * w = w * q0 x :=
        Subgroup.mem_centralizer_singleton_iff.mp hx
      have hfix : w * q0 x * w⁻¹ = q0 x := by
        calc w * q0 x * w⁻¹ = (q0 x * w) * w⁻¹ := by rw [hxw]
          _ = q0 x := by group
      rw [hζq0 x, hfix]
      exact hx
    let Zt : Subgroup (Jtilde J) := Subgroup.center (Jtilde J)
    have hmemZt : ∀ x : Jtilde J, q0 x = 1 → x ∈ Zt := by
      intro x hx
      exact (QuotientGroup.eq_one_iff x).mp hx
    let φfun : Ctilde → Zt := fun t =>
      ⟨(t : Jtilde J)⁻¹ * ζ (t : Jtilde J), by
        change (t : Jtilde J)⁻¹ * ζ (t : Jtilde J) ∈ Subgroup.center (Jtilde J)
        apply hmemZt
        have htC : q0 (t : Jtilde J) ∈ C := t.2
        have htw : q0 (t : Jtilde J) * w = w * q0 (t : Jtilde J) :=
          Subgroup.mem_centralizer_singleton_iff.mp htC
        have hfix : w * q0 (t : Jtilde J) * w⁻¹ = q0 (t : Jtilde J) := by
          calc w * q0 (t : Jtilde J) * w⁻¹ = (q0 (t : Jtilde J) * w) * w⁻¹ := by rw [htw]
            _ = q0 (t : Jtilde J) := by group
        rw [map_mul, map_inv, hζq0, hfix, inv_mul_cancel]
        ⟩
    have hφfun : ∀ t : Ctilde, ((φfun t : Zt) : Jtilde J) =
        (t : Jtilde J)⁻¹ * ζ (t : Jtilde J) := fun t => rfl
    let φ : Ctilde →* Zt := {
      toFun := φfun
      map_one' := by
        apply Subtype.ext
        simp [hφfun]
      map_mul' := fun s t => by
        apply Subtype.ext
        change ((φfun (s * t) : Zt) : Jtilde J) =
          ((φfun s : Zt) : Jtilde J) * ((φfun t : Zt) : Jtilde J)
        rw [hφfun, hφfun, hφfun]
        have hs : ((φfun s : Zt) : Jtilde J) ∈ Subgroup.center (Jtilde J) := (φfun s).2
        have hcomm : ((φfun s : Zt) : Jtilde J) * (t : Jtilde J) =
            (t : Jtilde J) * ((φfun s : Zt) : Jtilde J) :=
          (Subgroup.mem_center_iff.mp hs (t : Jtilde J)).symm
        have hcomm_inv : ((φfun s : Zt) : Jtilde J) * (t : Jtilde J)⁻¹ =
            (t : Jtilde J)⁻¹ * ((φfun s : Zt) : Jtilde J) :=
          (Subgroup.mem_center_iff.mp hs (t : Jtilde J)⁻¹).symm
        simp only [Subgroup.coe_mul]
        rw [map_mul, mul_inv_rev]
        calc (t : Jtilde J)⁻¹ * (s : Jtilde J)⁻¹ * (ζ (s : Jtilde J) * ζ (t : Jtilde J))
            = (t : Jtilde J)⁻¹ * ((s : Jtilde J)⁻¹ * ζ (s : Jtilde J)) *
                ζ (t : Jtilde J) := by group
          _ = (t : Jtilde J)⁻¹ * ((φfun s : Zt) : Jtilde J) * ζ (t : Jtilde J) := by
              rw [hφfun]
          _ = ((φfun s : Zt) : Jtilde J) * (t : Jtilde J)⁻¹ * ζ (t : Jtilde J) := by
              rw [← hcomm_inv]
          _ = ((φfun s : Zt) : Jtilde J) * ((t : Jtilde J)⁻¹ * ζ (t : Jtilde J)) := by group
          _ = ((φfun s : Zt) : Jtilde J) * ((φfun t : Zt) : Jtilde J) := by
              rw [hφfun]
    }
    have hCinf_le : Cinf ≤ Ctilde := by
      change ⁅Ctilde, Ctilde⁆ ≤ Ctilde
      exact (Subgroup.commutator_le_sup Ctilde Ctilde).trans (sup_le le_rfl le_rfl)
    have hZcomm : ∀ a b : Zt, a * b = b * a := by
      intro a b
      exact Subtype.ext (by
        show (a : Jtilde J) * (b : Jtilde J) = (b : Jtilde J) * (a : Jtilde J)
        exact (Subgroup.mem_center_iff.mp a.2 (b : Jtilde J)).symm)
    letI : CommMagma Zt := { mul_comm := hZcomm }
    have hCinf_ker : Cinf ≤ (φ.ker).map Ctilde.subtype := by
      change ⁅Ctilde, Ctilde⁆ ≤ (φ.ker).map Ctilde.subtype
      rw [Subgroup.commutator_le]
      intro h hh k hk
      refine Subgroup.mem_map.mpr
        ⟨(⟨⁅h, k⁆, hCinf_le (Subgroup.commutator_mem_commutator hh hk)⟩ : ↥Ctilde), ?_, rfl⟩
      · have hsub : (⟨⁅h, k⁆, hCinf_le (Subgroup.commutator_mem_commutator hh hk)⟩ : ↥Ctilde) =
            ⁅(⟨h, hh⟩ : ↥Ctilde), (⟨k, hk⟩ : ↥Ctilde)⁆ := rfl
        rw [hsub, MonoidHom.mem_ker, map_commutatorElement]
        exact (commutatorElement_eq_one_iff_mul_comm (G := Zt)).mpr (mul_comm _ _)
    have hCinf_fixed : Cinf ≤ fixed := by
      intro x hx
      obtain ⟨y, hyker, rfl⟩ := hCinf_ker hx
      have hval : (y : Jtilde J)⁻¹ * ζ (y : Jtilde J) = 1 := congrArg Subtype.val hyker
      show ζ (y : Jtilde J) = (y : Jtilde J)
      calc ζ (y : Jtilde J) = (y : Jtilde J) * ((y : Jtilde J)⁻¹ * ζ (y : Jtilde J)) := by
            group
        _ = (y : Jtilde J) := by rw [hval, mul_one]
    have hmapCtilde : Ctilde.map q0 = C := by
      change (C.comap q0).map q0 = C
      rw [Subgroup.map_comap_eq]
      have htop : q0.range = ⊤ :=
        MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective (Subgroup.center (Jtilde J)))
      rw [htop, top_inf_eq]
    have hmapCinf : Cinf.map q0 = C := by
      change (⁅Ctilde, Ctilde⁆).map q0 = C
      rw [Subgroup.map_commutator, hmapCtilde, ← Subgroup.map_subtype_commutator C,
        hCperf.commutator_eq_top, Subgroup.map_top, Subgroup.range_subtype]
    let CJ : Subgroup G := J ⊓ Subgroup.centralizer ({z} : Set G)
    let qJ : ↥CJ →* Jtilde J := qθ.comp (Subgroup.inclusion (inf_le_left : CJ ≤ J))
    have hqJ_le_fixed : qJ.range ≤ fixed := by
      rintro x ⟨u, rfl⟩
      have hzu : z * (u : G) * z⁻¹ = (u : G) := by
        have hcomm : z * (u : G) = (u : G) * z :=
          (Subgroup.mem_centralizer_singleton_iff.mp u.2.2).symm
        calc z * (u : G) * z⁻¹ = ((u : G) * z) * z⁻¹ := by rw [hcomm]
          _ = (u : G) := by group
      change ζ (qθ (Subgroup.inclusion (inf_le_left : CJ ≤ J) u)) =
        qθ (Subgroup.inclusion (inf_le_left : CJ ≤ J) u)
      change thetaQuotMulAut J (J.normalizerMonoidHom ⟨z, hzN⟩)
        ((Subgroup.inclusion (inf_le_left : CJ ≤ J) u : ↥J) : Jtilde J) =
          ((Subgroup.inclusion (inf_le_left : CJ ≤ J) u : ↥J) : Jtilde J)
      rw [thetaQuotMulAut_mk]
      have hconj : J.normalizerMonoidHom ⟨z, hzN⟩
          (Subgroup.inclusion (inf_le_left : CJ ≤ J) u) =
            Subgroup.inclusion (inf_le_left : CJ ≤ J) u := by
        apply Subtype.ext
        rw [normalizerMonoidHom_apply_coe]
        exact hzu
      rw [hconj]
    have hfixed_le_qJ : fixed ≤ qJ.range := by
      intro x hx
      obtain ⟨l, hl⟩ :=
        QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 ↥J) x
      have hxζ : ζ (qθ l) = qθ l := by rw [hl]; exact hx
      let α : MulAut ↥J := J.normalizerMonoidHom ⟨z, hzN⟩
      have hα3 : α ^ 3 = 1 := by
        change (J.normalizerMonoidHom ⟨z, hzN⟩) ^ 3 = 1
        rw [show (J.normalizerMonoidHom ⟨z, hzN⟩) ^ 3 =
          J.normalizerMonoidHom (⟨z, hzN⟩ ^ 3) from (map_pow _ _ _).symm]
        rw [hz3', map_one]
      have hNchar : (aschbacherSolvableCore 3 ↥J).Characteristic :=
        aschbacherSolvableCore_characteristic ↥J
      have hNstable : ∀ n ∈ aschbacherSolvableCore 3 ↥J,
          α n ∈ aschbacherSolvableCore 3 ↥J := by
        intro n hn
        have hmap : (aschbacherSolvableCore 3 ↥J).map α.toMonoidHom =
            aschbacherSolvableCore 3 ↥J :=
          (Subgroup.characteristic_iff_map_eq.mp hNchar) α
        rw [← hmap]
        exact Subgroup.mem_map_of_mem α.toMonoidHom hn
      have hr : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 ↥J) :=
        three_not_dvd_card_aschbacherSolvableCore
      have hqker : qθ (α l * l⁻¹) = 1 := by
        rw [map_mul, map_inv]
        have h1 : qθ (α l) = ζ (qθ l) := rfl
        rw [h1, hxζ, mul_inv_cancel]
      have hmemθ : α l * l⁻¹ ∈ aschbacherSolvableCore 3 ↥J :=
        (QuotientGroup.eq_one_iff (α l * l⁻¹)).mp hqker
      obtain ⟨y, hyN, hyfix⟩ :=
        CFSG.GroupTheory.CoprimeActionSupport.CoprimeAutomorphismFixedQuotientLift.fixed_lift
          α hα3 (aschbacherSolvableCore 3 ↥J) inferInstance hNstable hr l hmemθ
      have hzy : z * (y : G) * z⁻¹ = (y : G) := by
        have := congrArg Subtype.val hyfix
        simpa [α, normalizerMonoidHom_apply_coe] using this
      have hyz : (y : G) * z = z * (y : G) := by
        calc (y : G) * z = (z * (y : G) * z⁻¹) * z := by rw [hzy]
          _ = z * (y : G) := by group
      have hyCJ : (y : G) ∈ CJ := by
        refine ⟨y.2, ?_⟩
        exact Subgroup.mem_centralizer_singleton_iff.mpr hyz
      refine ⟨⟨(y : G), hyCJ⟩, ?_⟩
      change qθ y = x
      have hyq : qθ y = qθ l := by
        have h : qθ (y * l⁻¹) = 1 := by
          change (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥J)) (y * l⁻¹) = 1
          exact (QuotientGroup.eq_one_iff (y * l⁻¹)).mpr hyN
        have h' : qθ y * (qθ l)⁻¹ = 1 := by
          simpa [map_mul, map_inv] using h
        exact mul_inv_eq_one.mp h'
      rw [hyq, hl]
    have hqJrange : qJ.range = fixed := le_antisymm hqJ_le_fixed hfixed_le_qJ
    have hJleCJ : Cinf ≤ qJ.range := hCinf_fixed.trans (le_of_eq hqJrange.symm)
    have hJleC : J ≤ Subgroup.centralizer ({a} : Set G) :=
      (CFSG.RankThree.PartOne.mem_thetaComponentsAt_iff.mp hJ).1
    have hCJleC : CJ ≤ Subgroup.centralizer ({a} : Set G) :=
      inf_le_left.trans hJleC
    have hzM : Subgroup.centralizer ({z} : Set G) ≤ D.M := by
      have hZcard : Nat.card (zSub P c.L) = 3 := c.card_inf_centralizer_of_onan hON hP
      have hZeq' : Subgroup.zpowers z = zSub P c.L := by
        refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzZ) ?_
        rw [Nat.card_zpowers, hz3, hZcard]
      have hZeq : zSub P c.L = Subgroup.zpowers z := hZeq'.symm
      have hCz : Subgroup.centralizer ({z} : Set G) ≤
          Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) := by
        rw [hZeq]
        have heq : Subgroup.centralizer ({z} : Set G) =
            Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
          rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
        rw [heq]
        exact Subgroup.centralizer_le_normalizer ((Subgroup.zpowers z : Subgroup G) : Set G)
      exact hCz.trans hNZ
    have hCJleM : CJ ≤ D.M := inf_le_right.trans hzM
    have hCJleCM : CJ ≤ CM c a := le_inf hCJleM hCJleC
    have hsec1 : CFSG.SignalizerFunctorTheorem.IsSectionOf Sq ↥C :=
      CFSG.SignalizerFunctorTheorem.IsSectionOf.of_surjective qC hqC
    have hsec2 : CFSG.SignalizerFunctorTheorem.IsSectionOf ↥C ↥Cinf := by
      let qinf : ↥Cinf →* ↥C :=
        (MulEquiv.subgroupCongr hmapCinf).toMonoidHom.comp (q0.subgroupMap Cinf)
      have hqinf : Function.Surjective qinf :=
        (MulEquiv.subgroupCongr hmapCinf).surjective.comp
          (q0.subgroupMap_surjective Cinf)
      exact CFSG.SignalizerFunctorTheorem.IsSectionOf.of_surjective qinf hqinf
    have hsec3 : CFSG.SignalizerFunctorTheorem.IsSectionOf ↥Cinf ↥CJ := by
      let KJ : Subgroup ↥CJ := Cinf.comap qJ
      have hKJmap : KJ.map qJ = Cinf := by
        change (Cinf.comap qJ).map qJ = Cinf
        rw [Subgroup.map_comap_eq, hqJrange]
        exact inf_eq_right.mpr hCinf_fixed
      let qK : ↥KJ →* ↥Cinf :=
        (MulEquiv.subgroupCongr hKJmap).toMonoidHom.comp (qJ.subgroupMap KJ)
      have hqK : Function.Surjective qK :=
        (MulEquiv.subgroupCongr hKJmap).surjective.comp (qJ.subgroupMap_surjective KJ)
      exact (CFSG.SignalizerFunctorTheorem.IsSectionOf.of_surjective qK hqK).trans
        (CFSG.SignalizerFunctorTheorem.IsSectionOf.of_subgroup KJ)
    have hsec4 : CFSG.SignalizerFunctorTheorem.IsSectionOf ↥CJ ↥(CM c a) :=
      (CFSG.SignalizerFunctorTheorem.IsSectionOf.refl ↥CJ).of_injective
        (Subgroup.inclusion hCJleCM) (Subgroup.inclusion_injective hCJleCM)
    exact hsec1.trans (hsec2.trans (hsec3.trans hsec4))
  exact ⟨Sq, inferInstance, inferInstance, hSqsimple, hSqnonab, hsec, hSqmodel⟩

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
