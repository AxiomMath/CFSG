module

public import CFSG.LocalAnalysis.UniquenessCase.UC22KPkg
public import CFSG.LocalAnalysis.UniquenessCase.UC22KHi2g
public import CFSG.LocalAnalysis.UniquenessCase.UC22KHi2b
public import CFSG.LocalAnalysis.UniquenessCase.UC22KHi2s
import CFSG.LocalAnalysis.UniquenessCase.UC22P22sl
import CFSG.LocalAnalysis.UniquenessCase.UC22P22v
import CFSG.Milestones.ASVolI.B6Baumann
import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Milestones.ASVolI.B2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (InClassG InClassX oResidualTwo omegaOneCenterIn)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (jOf)
open P22x P22s P22k2
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace P22k2

theorem hi2_exists_r (D : Data G) (h118U : C118 D ⊥ D.U) {Y : Subgroup (MBar D.M D.U)} {V₀ : Subgroup G}
    {K₃ : Subgroup (MBar D.M D.U)} (kp : KleinPkg D Y V₀ K₃) :
    ∃ r : G, r ∈ rad118 D ∧ r ∈ preMbar D Y ∧ ActsOrdThree V₀ r := by
  have hV := uc22p22xf_hV D
  obtain ⟨y, hyN, hyM, hyK, hy1⟩ := kp.gen
  have hyMM : y ∈ ⁅D.M, D.M⁆ := Subgroup.commutator_mono (preN_le_M D Y) (preN_le_M D Y) hyN
  obtain ⟨r, hrR, c, hcc, hyrc⟩ := rad118_lift D h118U y hyMM
  have hrM : r ∈ D.M := rad118_le_M D hrR
  have hcM : c ∈ D.M := hcc.1
  have hc1 : (QuotientGroup.mk ⟨c, hcM⟩ : MBar D.M D.U) = 1 :=
    (uc22br_gt_mk_eq_one_iff hV ⟨c, hcM⟩).2 hcc.2
  have hrbar : (QuotientGroup.mk ⟨r, hrM⟩ : MBar D.M D.U) = QuotientGroup.mk ⟨y, hyM⟩ := by
    have e : (⟨y, hyM⟩ : ↥D.M) = ⟨r, hrM⟩ * ⟨c, hcM⟩ := Subtype.ext hyrc
    rw [e, QuotientGroup.mk_mul, hc1, mul_one]
  refine ⟨r, hrR, (mem_preMbar D).2 ⟨hrM, ?_⟩, ?_⟩
  · rw [hrbar]
    exact kp.K3_le hyK
  · exact kp.ord3 r hrM (by rw [hrbar]; exact hyK) (by rw [hrbar]; exact hy1)

theorem hi2_not_inClassX (D : Data G) (h640 : UC6.R6_40_1 D) {Y : Subgroup (MBar D.M D.U)} {V₀ : Subgroup G}
    {K₃ : Subgroup (MBar D.M D.U)} (kp : KleinPkg D Y V₀ K₃) (hY : Y ≤ mbarImage D.M D.U (proofN D))
    {H : Subgroup G} (hHR : H ≤ (rad118 D ⊓ preMbar D Y) ⊔ T1 D Y)
    (hQn : pCoreOf 2 D.M ≤ normalizer (H : Set G)) : ¬ InClassX ↥(oResidualTwo ↥H) := by
  intro hX
  set K : Subgroup G := (oResidualTwo ↥H).map H.subtype with hK
  have hKR : K ≤ rad118 D ⊓ preMbar D K₃ := by
    have hN : ((rad118 D ⊓ preMbar D K₃).subgroupOf H).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer fun x hx => gl_le_normalizer_rK3 D kp hY (hHR hx)
    have hle := oResidualTwo_le hN fun x => by
      obtain ⟨k, hk⟩ := gl_exists_pow_mem_rK3 D kp hY (hHR x.2)
      exact ⟨k, by simpa [Subgroup.mem_subgroupOf] using hk⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hle hy
  set K'' : Subgroup G := K ⊔ pCoreOf 2 D.M with hK''
  have hK''R : K'' ≤ rad118 D := sup_le (hKR.trans inf_le_left) (pCoreOf_le_rad118 D)
  have hK''Θ : K'' ≤ preMbar D (pCoreOf 3 (mbarImage D.M D.U (proofN D))) :=
    sup_le ((hKR.trans inf_le_right).trans (fr_preMbar_mono D kp.K3_pcore)) (fr_pCoreOf_le_preMbar D _)
  have hsub'' : (K''.subgroupOf D.M).IsSubnormal := rad118_subnormal D K'' le_sup_right hK''R hK''Θ
  have hK''n : K'' ≤ normalizer (K : Set G) :=
    sup_le Subgroup.le_normalizer fun q hq => gl_normalizer_le_map_oResidualTwo H (hQn hq)
  have hKK'' : (K.subgroupOf K'').Normal := Subgroup.normal_subgroupOf_of_le_normalizer hK''n
  have hK''M : K'' ≤ D.M := hK''R.trans (rad118_le_M D)
  have hKM : K ≤ D.M := le_sup_left.trans hK''M
  have hsub : (K.subgroupOf D.M).IsSubnormal := isSubnormal_subgroupOf_step le_sup_left hK''M hKK'' hsub''
  have hKX : InClassX ↥(K.subgroupOf D.M) := by
    have e1 : ↥(oResidualTwo ↥H) ≃* ↥K :=
      (oResidualTwo ↥H).equivMapOfInjective H.subtype H.subtype_injective
    have e2 : ↥(K.subgroupOf D.M) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKM
    exact CFSG.CGT.PushingUpLit.InClassX.of_mulEquiv (e1.trans e2.symm) hX
  exact h640 D.M D.maxLocal (K.subgroupOf D.M) ⟨hsub, hKX⟩

end P22k2

theorem uc22k_Hi_exists_two (D : Data G) (Ch : Choice2011 G) (h2 : S22_3_2 D Ch) (h3 : S22_3_3 D Ch)
    (h51 : S22_5_1 D Ch) (h640 : UC6.R6_40_1 D) (h118U : C118 D ⊥ D.U) (hH : H1930 D) (c : Ctx22c D Ch)
    {m : ℕ} {Nb : Fin m → Subgroup (MBar D.M D.U)} (hNb : NbarSplit D Nb) (i : Fin m)
    (hS3 : IsL2Ev ↥(Nb i) 1) : ∃ H : Subgroup G, HiPkgK D (Nb i) H := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨V₀, K₃, kp⟩ := uc22k_klein_exists D Ch h2 h3 h51 hH c hNb i hS3
  set Y : Subgroup (MBar D.M D.U) := Nb i with hYdef
  set S : Subgroup G := proofS D with hSdef
  set T₁ : Subgroup G := T1 D Y with hT₁def
  have hY : Y ≤ mbarImage D.M D.U (proofN D) := (le_iSup Nb i).trans hNb.1.1.le
  have hNY : ∀ g ∈ mbarImage D.M D.U (proofN D), g ∈ normalizer (Y : Set (MBar D.M D.U)) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro z
    refine ⟨fun hz => uc22p22v_internalDirect_conj hNb.1 i g hg z hz, fun hz => ?_⟩
    have := uc22p22v_internalDirect_conj hNb.1 i g⁻¹ (inv_mem hg) _ hz
    simpa [mul_assoc] using this
  have hY6 : Nat.card ↥Y = 6 := P22y.card_of_isL2Ev_one hS3
  have hV₀U : V₀ ≤ D.U := kp.le_Ii.trans (proofIi_le D (preN_le_M D Y))
  have hST : S ≤ T₁ := proofS_le_T1 D Ch h2 h3 h51 hH c m Nb hNb i
  have hJS : jOf D.T ≤ S := P22s.jOf_le_proofS D
  have hSact : ¬ S ≤ centralizer (V₀ : Set G) := by
    intro hle
    apply kp.hat_ne
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    exact (Subgroup.mem_centralizer_iff.1 (hle (hJS hj)) v hv).symm
  obtain ⟨r, hrR, hrY, hr3⟩ := hi2_exists_r D h118U kp
  obtain ⟨P, hF, hPR⟩ := exists_s3Frame D hY hNY hV₀U kp.elem kp.card kp.norm hST hSact hrR hrY hr3
  have hSn : T₁ ≤ normalizer (S : Set G) := T1_le_normalizer_proofS D Y
  obtain ⟨⟨hSH, hLH, hHP, hPn⟩, hPH, hO2, hfs, hOC, hV₀L, hSCO, hSidx, hsup, hA6, hsurj⟩ :=
    hF.package hST hSn hSact
  set H : Subgroup G := hGen P S with hHdef
  have hHR : H ≤ (rad118 D ⊓ preMbar D Y) ⊔ T₁ := hHP.trans hPR
  have hHM : H ≤ D.M := hHR.trans (sup_le (inf_le_left.trans (rad118_le_M D)) (T1_le_M D Y))
  have hHN : H ≤ normalizer (V₀ : Set G) := hHP.trans hF.norm
  have hS2 : IsPGroup 2 ↥S := D.sylowM.isPGroup.to_le inf_le_left
  have hidx : ¬ 2 ∣ S.relIndex H := by
    have hLsub : CFSG.Open.IsSubnormal (CFSG.Quasithin.twoResidual P) P :=
      CFSG.Open.IsSubnormal.step (CFSG.Quasithin.twoResidual_le P)
        (Subgroup.normal_subgroupOf_of_le_normalizer (CFSG.Quasithin.le_normalizer_twoResidual P))
        (CFSG.Open.IsSubnormal.refl P)
    have hLP : CFSG.Quasithin.twoResidual P ≤ P := CFSG.Quasithin.twoResidual_le P
    have hLK3 : CFSG.Quasithin.twoResidual P ≤ preMbar D K₃ :=
      ((gl_twoResidual_le_rK3 D kp hY hPR).trans inf_le_right).trans inf_le_right
    have hLM : CFSG.Quasithin.twoResidual P ≤ D.M := hLH.trans hHM
    obtain ⟨y₀, hy₀L, hy₀⟩ := hF.s3_exists_twoResidual_actsOrdThree
    have hnat : CFSG.Quasithin.IsNaturalL2Prime 1 (CFSG.Quasithin.twoResidual P) V₀ :=
      kp.nat _ hLM hLK3 (hLP.trans hF.norm) ⟨y₀, hy₀L, hy₀⟩
    have hJ : ⁅V₀, CFSG.ASVolI.ChB.Jj T₁ 0⁆ ≠ ⊥ := by
      rw [Jj_zero, thompsonJ_T1 D hST, ← uc22p22se_jOf_eq]
      exact kp.hat_ne
    obtain ⟨-, hB2, -⟩ := CFSG.ASVolI.as_B_6_10 G P T₁ ((P ⊓ centralizer (V₀ : Set G)) ⊔ T₁) V₀
      (CFSG.Quasithin.twoResidual P) 1 hF.minParabolic
      ((CFSG.Quasithin.quasithinGenFitting_eq_pCoreOf_iff P 2).2 hF.fstar) hF.isTwoReduced hLsub hnat hJ
    rw [baumOf_eq, baum_T1 D hST] at hB2
    exact hB2.2.2
  set ψH : ↥H →* MulAut ↥V₀ := s3_psi hHN with hψH
  have hψs : Function.Surjective ψH := by
    intro g
    obtain ⟨h, hh, hg⟩ := hsurj g
    refine ⟨⟨h, hh⟩, ?_⟩
    ext v
    rw [s3_psi_coe]
    exact (hg v).symm
  obtain ⟨eAut⟩ := gl_exists_mulEquiv_aut D kp hY hY6 hA6
  obtain ⟨eY⟩ := exists_mulEquiv_projSL hS3 le_rfl
  have hKmap : ψH.ker.map H.subtype = H ⊓ centralizer (V₀ : Set G) := by
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, (s3_psi_eq_one_iff hHN x).1 hx⟩
    · rintro ⟨hgH, hgC⟩
      exact ⟨⟨g, hgH⟩, (s3_psi_eq_one_iff hHN ⟨g, hgH⟩).2 hgC, rfl⟩
  have hsup' : ∀ X : Subgroup ↥H, X ⊔ ψH.ker = ⊤ → CFSG.pCore 2 ↥H ≤ X → X = ⊤ := by
    intro X hXK hQX
    have h1 : X.map H.subtype ≤ H := Subgroup.map_subtype_le X
    have h2' : pCoreOf 2 H ≤ X.map H.subtype := Subgroup.map_mono hQX
    have h3' : (X.map H.subtype) ⊔ (H ⊓ centralizer (V₀ : Set G)) = H := by
      rw [← hKmap, ← Subgroup.map_sup, hXK, Subgroup.map_top, Subgroup.range_subtype]
    have h4 : X.map H.subtype = H := hsup (X.map H.subtype) h1 h2' h3'
    refine eq_top_iff.2 fun x _ => ?_
    have hx : (x : G) ∈ X.map H.subtype := by
      rw [h4]
      exact x.2
    obtain ⟨x', hx', hxx'⟩ := hx
    have : x' = x := Subtype.ext hxx'
    rwa [← this]
  have hG : InClassG ↥S ↥H (Subgroup.inclusion hSH) :=
    gl_inClassG_of_supplement hSH hS2 hidx hfs ψH.ker
      (((QuotientGroup.quotientKerEquivOfSurjective ψH hψs).trans eAut.symm).trans eY) hsup'
  have hV₀Q : V₀ ≤ pCoreOf 2 P :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hF.v₀le hF.norm
      (IsPGroup.of_card (p := 2) (n := 2) (by rw [kp.card]; norm_num))
  have hRP : pCoreOf 2 H ≤ pCoreOf 2 P := by
    rw [hO2]
    exact inf_le_right
  have hRC : pCoreOf 2 H ≤ centralizer (V₀ : Set G) := hRP.trans hOC
  have hV₀R : V₀ ≤ pCoreOf 2 H := by
    rw [hO2]
    exact le_inf (hV₀L.trans hLH) hV₀Q
  have hSCR : S ⊓ centralizer (V₀ : Set G) ≤ pCoreOf 2 H := by
    rw [hO2]
    exact le_inf (inf_le_left.trans hSH) hSCO
  have hRS : pCoreOf 2 H ≤ S := P22k.pCoreOf_le_of_inClassG hSH hG
  have hAS : ∀ A : Subgroup G, CFSG.Quasithin.IsMaxElemAbelian D.T A → A ≤ S := fun A hA =>
    P22k.isMax_le_proofS D hA
  have hÊcomm : ∀ a ∈ jOf D.T, ∀ z ∈ ⁅V₀, jOf D.T⁆, a * z = z * a := by
    intro a ha z hz
    rw [kp.hat] at hz
    have hzE : z ∈ proofE D := uc22p22sb_proofEiHat_le_proofE D Ch h2 h3 h51 hH c m Nb hNb i hz
    exact (uc22p22e_mem_omegaZJ.1 hzE).2.1 a ha
  have hEq : ⁅jOf D.T, omegaZJ22 (pCoreOf 2 H)⁆ = proofEiHat D (preN D Y) := by
    rw [Subgroup.commutator_comm,
      lemma25_klein inf_le_left hAS hRS hV₀R kp.elem kp.card hRC hSCR hSidx hÊcomm, kp.hat]
  have hhat : proofEiHat D (preN D Y) ≤ ⁅H, omegaZJ22 (pCoreOf 2 H)⁆ ⊓ centralizer (S : Set G) := by
    refine le_inf ?_ ?_
    · rw [← hEq]
      exact Subgroup.commutator_mono (hJS.trans hSH) le_rfl
    · intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      exact ((Subgroup.mem_centralizer_iff.1
        (uc22p22sb_proofS_le_centralizer D Ch h2 h3 h51 hH c m Nb hNb i hs)) z hz).symm
  have hnc : ¬ H ≤ centralizer (proofEiHat D (preN D Y) : Set G) := by
    intro hle
    haveI := hF.s3_isKleinFour
    obtain ⟨y₀, hy₀L, hy₀⟩ := hF.s3_exists_twoResidual_actsOrdThree
    have hy₀P : y₀ ∈ P := CFSG.Quasithin.twoResidual_le P hy₀L
    have hy₀H : y₀ ∈ H := hLH hy₀L
    have hJN : jOf D.T ≤ normalizer (V₀ : Set G) := (hJS.trans (hST.trans hF.le)).trans hF.norm
    have hÊV : proofEiHat D (preN D Y) ≤ V₀ := by
      rw [← kp.hat]
      exact Subgroup.le_normalizer_iff_commutator_le_left.mp hJN
    have hÊne : proofEiHat D (preN D Y) ≠ ⊥ := kp.hat ▸ kp.hat_ne
    obtain ⟨⟨v, hvÊ⟩, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hÊne
    have hvV : v ∈ V₀ := hÊV hvÊ
    have hcomm : v * y₀ = y₀ * v := Subgroup.mem_centralizer_iff.1 (hle hy₀H) v hvÊ
    have hσv : s3_psi hF.norm ⟨y₀, hy₀P⟩ ⟨v, hvV⟩ = ⟨v, hvV⟩ := by
      apply Subtype.ext
      rw [s3_psi_coe]
      change y₀ * v * y₀⁻¹ = v
      rw [← hcomm]
      group
    have := s3_mulAut_fixed ↥V₀ (s3_psi hF.norm ⟨y₀, hy₀P⟩) (hF.s3_psi_pow_three_of_acts hy₀P hy₀)
      (hF.s3_psi_ne_one_of_acts hy₀P hy₀) ⟨v, hvV⟩ hσv
    have hv : v = 1 := congrArg Subtype.val this
    exact hv1 (Subtype.ext hv)
  have hZ : ¬ H ≤ centralizer (omegaOneCenterIn S : Set G) := fun hle =>
    hnc (hle.trans (Subgroup.centralizer_le
      (uc22p22sb_proofEiHat_le_omegaOneCenterIn D Ch h2 h3 h51 hH c m Nb hNb i)))
  have hX : ¬ InClassX ↥(oResidualTwo ↥H) :=
    hi2_not_inClassX D h640 kp hY hHR fun q hq => hPn (hF.le (pCoreOf_le_T1 D Y hq))
  have hodd : ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ Nat.card ↥Y → p ∣ Nat.card ↥H := by
    intro p hp hp2 hpY
    rw [hY6] at hpY
    have h6 : 6 ∣ Nat.card ↥H := hA6 ▸ Subgroup.card_dvd_of_surjective hψs
    have hp3 : p = 3 := by
      rcases (Nat.Prime.dvd_mul hp).1 (show p ∣ 2 * 3 from hpY) with h | h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h) hp2
      · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h
    exact (hp3 ▸ (by norm_num : 3 ∣ 6)).trans h6
  have hV₀E : V₀ ≤ omegaZJ22 (pCoreOf 2 H) := fun v hv =>
    uc22p22e_mem_omegaZJ'.2 ⟨hV₀R hv, fun j hj =>
      (Subgroup.mem_centralizer_iff.1 (hRC (uc22p22e_jOf_le_self _ hj)) v hv).symm, kp.elem.2 v hv⟩
  refine ⟨H, ?_⟩
  unfold HiPkgK
  exact ⟨hSH, hG, hZ, hX, hEq, hhat, hHM, hodd, hnc, V₀, hV₀E, hRC, hSCR,
    lemma49_klein hAS ((hV₀R.trans hRS).trans inf_le_left) kp.elem kp.card hSidx, hV₀U,
    fun x hx => kp.faith x hx.1 hx.2⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
