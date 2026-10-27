module

public import CFSG.RankThree.PartTwo.Sec8.Hering611SJ3Bridge
public import CFSG.RankThree.PartTwo.Sec8.Hering611S3Step1
public import CFSG.RankThree.PartTwo.Sec8.Hering611S3J3
public import CFSG.RankThree.PartTwo.Sec8.Hering611S3K1
public import CFSG.RankThree.PartTwo.Sec8.Hering611S3K3
public import CFSG.RankThree.PartTwo.Sec8.Hering611S3K4
public import CFSG.RankThree.PartTwo.Sec8.Hering611S3K5
public import CFSG.RankThree.PartTwo.Sec8.Hering611S3K6
public import CFSG.RankThree.PartTwo.Sec8.Hering611S3Step3
public import CFSG.RankThree.PartTwo.Sec8.Hering611S3Step4
public import CFSG.RankThree.PartTwo.Sec8.Hering611S3Step5
public import CFSG.RankThree.PartTwo.Sec8.Hering611S3Step7
public import CFSG.RankThree.PartTwo.Sec8.Hering611S3Frame
public import CFSG.RankThree.PartTwo.Sec8.Hering611S3GlueA
public import CFSG.RankThree.PartTwo.Sec8.Hering611S3GlueB
public import CFSG.RankThree.PartTwo.Sec8.Hering611S3GlueC
public import CFSG.RankThree.PartTwo.Sec8.Hering611S3GlueD
public import CFSG.RankThree.PartTwo.Sec8.Hering611S3GlueE
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerGaussUnitary
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4

section J3Main


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L E T : Subgroup G} {d : G}
  {S K : Subgroup G}

theorem exists_Pb (h45 : Sec4.Item4_5) (C : Cfg611 G A c L E T d S K) {k : K}
    (hkact : MulAut.conj (QuotientGroup.mk' (aschbacherSolvableCore 3 K) k) =
      thetaQuotMulAut K (compAction K ⟨c, C.A_le_normalizer_K h45 C.c_mem⟩)) :
    Group.IsPerfect (imageSub K (Sec11.sec11K L d)) ∧
      (∀ p ∈ imageSub K (Sec11.sec11K L d),
        p * QuotientGroup.mk' (aschbacherSolvableCore 3 K) k =
          QuotientGroup.mk' (aschbacherSolvableCore 3 K) k * p) ∧
      360 ∣ Nat.card (imageSub K (Sec11.sec11K L d)) ∧
      imageSub K (A ⊓ L) ≤ imageSub K (Sec11.sec11K L d) := by
  obtain ⟨hcN, -, -, hPcomp0, hP60⟩ := exists_bridge_image h45 C
  have hPcomp : imageSub K (Sec11.sec11K L d) ∈
      thetaComponentsIn (Item426.fixSub (Item426.thetaAut K hcN)) := hPcomp0
  have hP6 : Nonempty (imageSub K (Sec11.sec11K L d) ⧸
      aschbacherSolvableCore 3 (imageSub K (Sec11.sec11K L d)) ≃* alternatingGroup (Fin 6)) :=
    hP60
  have hPperf := isPerfect_of_mem_thetaComponentsIn hPcomp
  have hPle := le_of_mem_thetaComponentsIn hPcomp
  refine ⟨hPperf, ?_, ?_, imageSub_mono C.toFrame611.inf_L_le_sec11K⟩
  · intro p hp
    have h1 : thetaQuotMulAut K (compAction K ⟨c, hcN⟩) p = p := hPle hp
    have h2 : (MulAut.conj (QuotientGroup.mk' (aschbacherSolvableCore 3 K) k)) p = p := by
      rw [hkact]
      exact h1
    have h3 : QuotientGroup.mk' (aschbacherSolvableCore 3 K) k * p *
        (QuotientGroup.mk' (aschbacherSolvableCore 3 K) k)⁻¹ = p := h2
    calc p * QuotientGroup.mk' (aschbacherSolvableCore 3 K) k
        = (QuotientGroup.mk' (aschbacherSolvableCore 3 K) k * p *
          (QuotientGroup.mk' (aschbacherSolvableCore 3 K) k)⁻¹) *
          QuotientGroup.mk' (aschbacherSolvableCore 3 K) k := by rw [h3]
      _ = QuotientGroup.mk' (aschbacherSolvableCore 3 K) k * p := by group
  · obtain ⟨ψ⟩ := hP6
    have h1 : Nat.card (imageSub K (Sec11.sec11K L d) ⧸
        aschbacherSolvableCore 3 (imageSub K (Sec11.sec11K L d))) = 360 := by
      rw [Nat.card_congr ψ.toEquiv, nat_card_alternatingGroup]
      simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
      decide
    rw [← h1]
    exact Subgroup.card_quotient_dvd_card _

theorem kF611J3_of (h45 : Sec4.Item4_5) (hJ3 : J3TwoLocalInput) : KF611J3 := by
  intro G _ _ A c L E T d S K C he
  obtain ⟨e⟩ := he
  exfalso
  have hF := C.toFrame611
  have hbig : NoBig3 G := noBig3_of_evenRank hF.standing.evenRank_eq
  have hchar : CFSG.Assembly.IsCharTwoType G := hF.standing.charTwoType
  have hAe := hF.isElemAbelian
  have hA27 : 27 < Nat.card A := by rw [hF.card_A]; norm_num
  have hAK := C.A_le_normalizer_K h45
  have hAL := hF.A_le_normalizer_L h45
  have hdA := hF.d_mem_A
  have hd3 := hF.d_pow_three
  have hd1 := hF.d_ne_one
  have hKd := C.K_le_centralizer
  have hKcomp := C.mem_thetaComponentsAt_K
  have hZ : Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) = ⊥ :=
    center_eq_bot_of_mulEquiv_J3 e
  have hin : ∀ γ : MulAut (K ⧸ aschbacherSolvableCore 3 K), γ ^ 3 = 1 → KFacts.IsInnerAut γ :=
    fun γ hγ => exists_conj_of_pow_three_J3 e γ hγ
  obtain ⟨k, j, hkA, hck, hk1, hk3, hkact⟩ := step1_general h45 C hZ hin
  have hAdec : ∀ x ∈ A, ∃ k' ∈ A ⊓ K, x * k'⁻¹ ∈ Subgroup.zpowers d := by
    intro x hx
    obtain ⟨k', hk'A, hk'd, -⟩ := exists_mul_mem_zpowers_d h45 C hZ hin hx
    exact ⟨(k' : G), ⟨hk'A, k'.2⟩, hk'd⟩
  have hθodd := theta_K_odd hbig hAe hA27 hAK
  have hDodd := kernel_odd hbig hAe hA27 hdA hAK hAdec hKd
  obtain ⟨a, haAL, ha1⟩ : ∃ a ∈ A ⊓ L, a ≠ 1 := by
    have h1 : 1 < Nat.card (A ⊓ L : Subgroup G) := by rw [hF.card_inf_L h45]; norm_num
    haveI : Nontrivial (A ⊓ L : Subgroup G) := Finite.one_lt_card_iff_nontrivial.mp h1
    obtain ⟨a, ha⟩ := exists_ne (1 : (A ⊓ L : Subgroup G))
    exact ⟨a, a.2, fun h => ha (Subtype.ext h)⟩
  have haA : a ∈ A := haAL.1
  have haL : a ∈ L := haAL.2
  have haK : a ∈ K := C.inf_L_le_K haAL
  have ha3 : a ^ 3 = 1 := hAe.2 a haA
  obtain ⟨hPperf, hPc, h360, hEP⟩ := exists_Pb h45 C hkact
  have haK3 : (⟨a, haK⟩ : K) ^ 3 = 1 := Subtype.ext (by simpa using ha3)
  have haK1 : (⟨a, haK⟩ : K) ≠ 1 := fun h => ha1 (congrArg Subtype.val h)
  have hab3 : (QuotientGroup.mk' (aschbacherSolvableCore 3 K) ⟨a, haK⟩) ^ 3 = 1 := by
    rw [← map_pow, haK3, map_one]
  have hab1 : QuotientGroup.mk' (aschbacherSolvableCore 3 K) ⟨a, haK⟩ ≠ 1 := fun h =>
    Hering611S3Step4bProof.not_mem_aschbacherSolvableCore_of_pow_three haK3 haK1
      ((QuotientGroup.eq_one_iff _).mp h)
  have hkab : QuotientGroup.mk' (aschbacherSolvableCore 3 K) k *
      QuotientGroup.mk' (aschbacherSolvableCore 3 K) ⟨a, haK⟩ =
      QuotientGroup.mk' (aschbacherSolvableCore 3 K) ⟨a, haK⟩ *
      QuotientGroup.mk' (aschbacherSolvableCore 3 K) k := by
    rw [← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext (hF.comm_of_mem hkA haA))
  have hJ : J3TwoLocalFacts (K ⧸ aschbacherSolvableCore 3 K)
      (QuotientGroup.mk' (aschbacherSolvableCore 3 K) k)
      (QuotientGroup.mk' (aschbacherSolvableCore 3 K) ⟨a, haK⟩) :=
    hJ3 _ ⟨e⟩ _ _ (orderOf_eq_prime hk3 hk1) (orderOf_eq_prime hab3 hab1) hkab
      ⟨imageSub K (Sec11.sec11K L d), hPperf,
        fun p hp => Subgroup.mem_centralizer_singleton_iff.mpr (hPc p hp),
        hEP (mk_mem_imageSub (x := ⟨a, haK⟩) haAL), h360⟩
  obtain ⟨Vb, hVb⟩ := hJ.pair
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAcomm : ∀ x ∈ A, ∀ z ∈ A, x * z = z * x := fun x hx z hz => hF.comm_of_mem hx hz
  have hcA := hF.c_mem
  have hc3 : c ^ 3 = 1 := hF.c_pow_three
  have hc1 := hF.c_ne_one
  have hLcomp : L ∈ thetaComponentsAt 3 c := hF.mem_thetaComponentsAt_L
  have hcd := hF.cd_inf_L
  have hcd9 := hF.card_cd
  have hAdecL : A ≤ Subgroup.zpowers c ⊔ Subgroup.zpowers d ⊔ (A ⊓ L) := (hF.A_eq_sup h45).le
  have hθ3 : ¬ 3 ∣ Nat.card (inSubgroup (aschbacherSolvableCore 3) K) :=
    Sec11.not_three_dvd_card_inSubgroup_theta K
  set E' : Subgroup G := Subgroup.zpowers c ⊔ Subgroup.zpowers d ⊔ Subgroup.zpowers a with hE'
  have hE'A : E' ≤ A := sup_le (sup_le (Subgroup.zpowers_le.mpr hcA)
    (Subgroup.zpowers_le.mpr hdA)) (Subgroup.zpowers_le.mpr haA)
  have hE'3 : IsPGroup 3 E' := Sec5.isPGroup_of_isElemAbelian (Sec5.isElemAbelian_of_le hAe hE'A)
  have hE'K : E' ≤ Subgroup.normalizer (K : Set G) := hE'A.trans hAK
  have hcE' : c ∈ E' := Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers c))
  have hdE' : d ∈ E' := Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers d))
  have haE' : a ∈ E' := Subgroup.mem_sup_right (Subgroup.mem_zpowers a)
  have hinv : ∀ i, ∀ (x : G) (hx : x ∈ E'), ∀ w ∈ Vb i,
      Sec12.thetaBarAct K ⟨x, hE'K hx⟩ w ∈ Vb i := fun i =>
    C.invariant_of_gens h45 hkA hck haA haK (hVb.inv i).1 (hVb.inv i).2 hE'K
  have hW2 : IsPGroup 2 (Vb 0 ⊔ Vb 1 : Subgroup (K ⧸ aschbacherSolvableCore 3 K)) :=
    IsPGroup.of_card (n := 6) (by rw [hVb.card]; norm_num)
  have hWinv : ∀ (x : G) (hx : x ∈ E'), ∀ w ∈ Vb 0 ⊔ Vb 1,
      Sec12.thetaBarAct K ⟨x, hE'K hx⟩ w ∈ Vb 0 ⊔ Vb 1 := by
    intro x hx w hw
    have h0 : Vb 0 ≤ (Vb 0 ⊔ Vb 1).comap (Sec12.thetaBarAct K ⟨x, hE'K hx⟩).toMonoidHom :=
      fun z hz => Subgroup.mem_sup_left (hinv 0 x hx z hz)
    have h1 : Vb 1 ≤ (Vb 0 ⊔ Vb 1).comap (Sec12.thetaBarAct K ⟨x, hE'K hx⟩).toMonoidHom :=
      fun z hz => Subgroup.mem_sup_right (hinv 1 x hx z hz)
    exact sup_le h0 h1 hw
  obtain ⟨P, hPK, hP2, hE'P, hPimg⟩ := exists_two_lift hθodd hE'3 hE'K hW2 hWinv
  have hVbP : ∀ i, Vb i ≤ imageSub K P := by
    rw [hPimg]
    exact Fin.forall_fin_two.mpr ⟨le_sup_left, le_sup_right⟩
  have hsub := fun i => sub_lift hθodd hE'K hPK hP2 hE'P (hVbP i) (hinv i)
  obtain ⟨V, hVP, hVimg, hE'V, hVsat⟩ : ∃ V : Fin 2 → Subgroup G, (∀ i, V i ≤ P) ∧
      (∀ i, imageSub K (V i) = Vb i) ∧ (∀ i, E' ≤ Subgroup.normalizer (V i : Set G)) ∧
      (∀ i, P ⊓ preimageSub K (Vb i) ≤ V i) :=
    ⟨fun i => P ⊓ preimageSub K (Vb i), fun i => inf_le_left, fun i => (hsub i).2.1,
      fun i => (hsub i).2.2, fun i => le_rfl⟩
  have hVK : ∀ i, V i ≤ K := fun i => (hVP i).trans hPK
  have hV2 : ∀ i, IsPGroup 2 (V i) := fun i => hP2.to_le (hVP i)
  have hVb1 : ∀ i, Vb i ≠ ⊥ := by
    intro i h
    have := (hVb.elem i).2
    rw [h, Subgroup.card_bot] at this
    omega
  have hV1' : ∀ i, imageSub K (V i) ≠ ⊥ := fun i => by rw [hVimg i]; exact hVb1 i
  have hV1 : ∀ i, V i ≠ ⊥ := fun i h => hV1' i (by rw [h]; simp [imageSub])
  have hVc : ∀ i, ∀ x ∈ V i, ∀ y ∈ V i, x * y = y * x := fun i =>
    comm_of_imageSub_comm hθodd hP2 (hVP i) hPK (by
      rw [hVimg i]
      intro x hx y hy
      exact congrArg Subtype.val ((hVb.elem i).1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
  have hVnorm : ∀ i j, V j ≤ Subgroup.normalizer (V i : Set G) := fun i j =>
    le_normalizer_of_image hθodd hP2 hPK (hVP i) (hVP j)
      (by rw [hVimg i]; exact hVsat i) (by rw [hVimg i, hVimg j]; exact hVb.norm i j)
  have hPeq : V 0 ⊔ V 1 = P := eq_of_imageSub_eq hθodd hP2 (sup_le (hVP 0) (hVP 1)) hPK
    (by rw [imageSub_sup (hVK 0) (hVK 1), hVimg 0, hVimg 1, hPimg])
  have hPN : ∀ i, P ≤ Subgroup.normalizer (V i : Set G) := fun i => by
    rw [← hPeq]
    exact sup_le (hVnorm i 0) (hVnorm i 1)
  have hdcent : ∀ i, d ∈ Subgroup.centralizer (V i : Set G) := fun i =>
    Subgroup.mem_centralizer_iff.mpr fun v hv =>
      Subgroup.mem_centralizer_singleton_iff.mp (hKd (hVK i hv))
  have hJ5 : ∀ i, ∀ σ : MulAut (K ⧸ aschbacherSolvableCore 3 K),
      (∀ v ∈ imageSub K (V i), σ v = v) → ∃ v ∈ imageSub K (V i), σ = MulAut.conj v := by
    intro i σ hσ
    rw [hVimg i] at hσ ⊢
    exact hVb.aut i σ hσ
  have hsyl : ∀ i, ∀ T : Subgroup G, IsPGroup 2 T →
      T ≤ Subgroup.centralizer (V i : Set G) ⊓ Subgroup.centralizer ({d} : Set G) →
      V i ≤ T → T ≤ V i := fun i =>
    V_sylow hKcomp hZ hDodd (hVK i) (hV2 i) (hV1' i) (hJ5 i)
  obtain ⟨U, hUdef⟩ : ∃ U : Fin 2 → Subgroup G,
      U = fun i => CFSG.Assembly.pCoreOf 2 (Subgroup.centralizer (V i : Set G)) := ⟨_, rfl⟩
  have hUi : ∀ i, U i = CFSG.Assembly.pCoreOf 2 (Subgroup.centralizer (V i : Set G)) :=
    fun i => by rw [hUdef]
  have hU2 : ∀ i, IsPGroup 2 (U i) := fun i => by
    rw [hUi]
    exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hUle : ∀ i, U i ≤ Subgroup.centralizer (V i : Set G) := fun i => by
    rw [hUi]
    exact CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hVU : ∀ i, V i ≤ U i := fun i => by
    rw [hUi]
    exact le_pCoreOf_centralizer (hV2 i) (hVc i)
  have hUd : ∀ i, ¬ U i ≤ Subgroup.centralizer ({d} : Set G) := fun i => by
    rw [hUi]
    exact step3_not_le_centralizer hchar (hV2 i) (hV1 i) (hVc i) hd3 hd1 (hdcent i)
  have hUfix : ∀ i, ∀ u ∈ U i, d * u = u * d → u ∈ V i := by
    intro i u hu hdu
    have hT : U i ⊓ Subgroup.centralizer ({d} : Set G) ≤ V i := hsyl i _
      ((hU2 i).to_le inf_le_left) (fun x hx => ⟨hUle i hx.1, hx.2⟩)
      (le_inf (hVU i) (fun v hv => hKd (hVK i hv)))
    exact hT ⟨hu, Subgroup.mem_centralizer_singleton_iff.mpr hdu.symm⟩
  have hUnorm : ∀ i, Subgroup.normalizer (V i : Set G) ≤ Subgroup.normalizer (U i : Set G) :=
    fun i => by
      rw [hUi]
      exact normalizer_le_normalizer_pCoreOf_centralizer (V i)
  have hy3 : ∀ m : ℕ, (c * a ^ m) ^ 3 = 1 := fun m => by
    have hcm : Commute c (a ^ m) := hAcomm c hcA (a ^ m) (A.pow_mem haA m)
    rw [hcm.mul_pow, hc3, one_mul, ← pow_mul, mul_comm, pow_mul, ha3, one_pow]
  have hB0 := C.imageSub_inf_K_eq hkA k.2 haA haK (C.card_inf_K hZ hAdec) hJ.B0.2
  have hstep4 : ∀ i : Fin 2, ∀ m : ℕ, m < 3 → ∀ u ∈ U i,
      (c * a ^ m) * u = u * (c * a ^ m) → d * u = u * d := by
    intro i m hm u hu hyu
    obtain ⟨g, hgK, hgA, hgd, hgc⟩ : ∃ g ∈ K, g ∈ Subgroup.normalizer (A : Set G) ∧
        g * d * g⁻¹ = d ∧ g * c * g⁻¹ = c * a ^ m := by
      interval_cases m
      · exact ⟨1, K.one_mem, Subgroup.one_mem _, by group, by simp⟩
      · exact C.exists_conj_g hkA hck haA haK hAdec hB0 (hJ.fuse 1 (Or.inl rfl))
      · exact C.exists_conj_g hkA hck haA haK hAdec hB0 (hJ.fuse 2 (Or.inr rfl))
    obtain ⟨hL'c, hAL'⟩ := conj_config hLcomp hgA hAL
    rw [hgc] at hL'c
    obtain ⟨eL'⟩ := thetaQuot_conj_equiv L g
    obtain ⟨φ⟩ := hF.iso_L
    have hdec' := conj_dec hgA hgd hAdecL
    rw [hgc] at hdec'
    have hna := not_mem_cd_fm hAe hcA hdA haA haL ha1 hcd hcd9 m
    have hyA : c * a ^ m ∈ A := A.mul_mem hcA (A.pow_mem haA m)
    have hyE' : c * a ^ m ∈ E' := E'.mul_mem hcE' (E'.pow_mem haE' m)
    obtain ⟨b, hbAL', hb1, hbE, habE⟩ := exists_b hAcomm hyA hdA haA hdec' hna
    have hbE' : b ∈ E' := (sup_le (sup_le (Subgroup.zpowers_le.mpr hyE')
      (Subgroup.zpowers_le.mpr hdE')) (Subgroup.zpowers_le.mpr haE')) hbE
    have hPU : P ≤ Subgroup.normalizer (U i : Set G) := (hPN i).trans (hUnorm i)
    have hR2 : IsPGroup 2 (U i ⊔ P : Subgroup G) := isPGroup_sup_of_le_normalizer (hU2 i) hP2 hPU
    have hE'R : ∀ x ∈ E', ∀ r ∈ (U i ⊔ P : Subgroup G), x * r * x⁻¹ ∈ (U i ⊔ P : Subgroup G) :=
      fun x hx r hr => (Subgroup.mem_normalizer_iff.mp
        (mem_normalizer_sup (hUnorm i (hE'V i hx)) (hE'P hx)) r).mp hr
    have hyN : c * a ^ m ∈ Subgroup.normalizer (K : Set G) := hAK hyA
    have hyP : c * a ^ m ∈ Subgroup.normalizer (P : Set G) := hE'P hyE'
    have haP : a ∈ Subgroup.normalizer (P : Set G) := hE'P haE'
    obtain ⟨-, w, hw, hwa⟩ := hVb.four m hm
    have hwP : w ∈ imageSub K P := by rw [hPimg]; exact hw.2
    have hwy : QuotientGroup.mk' (aschbacherSolvableCore 3 K) k *
        (QuotientGroup.mk' (aschbacherSolvableCore 3 K) ⟨a, haK⟩) ^ m * w *
        (QuotientGroup.mk' (aschbacherSolvableCore 3 K) k *
        (QuotientGroup.mk' (aschbacherSolvableCore 3 K) ⟨a, haK⟩) ^ m)⁻¹ = w :=
      mul_inv_eq_iff_eq_mul.mpr (Subgroup.mem_centralizer_singleton_iff.mp hw.1).symm
    obtain ⟨s, hsP, hsy, hsa⟩ := exists_fixed_moved hθodd hP2 hPK hyN hyP
      (C.thetaBarAct_y h45 hkA hck haA haK m hyN) haK haP hwP hwy hwa
    have hsd : d * s = s * d := (Subgroup.mem_centralizer_singleton_iff.mp (hKd (hPK hsP))).symm
    have hsb : b * s ≠ s * b := by
      intro hbs
      apply hsa
      have hcent : Subgroup.zpowers (c * a ^ m) ⊔ Subgroup.zpowers d ⊔ Subgroup.zpowers b ≤
          Subgroup.centralizer ({s} : Set G) :=
        sup_le (sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hsy))
          (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hsd)))
          (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hbs))
      exact Subgroup.mem_centralizer_singleton_iff.mp (hcent habE)
    have key := step4_core hbig hAe hA27 hAL' hyA hdA hbAL'.1 hL'c
      (eL'.trans (φ.trans (Sec4.projSLEquivPSL (GaloisField 3 (3 * 2))))) hdec' hbAL'.2 hb1
      (hy3 m) hd3 (hAe.2 b hbAL'.1) hR2 (hE'R d hdE') (hE'R b hbE') (Subgroup.mem_sup_right hsP) hsy
      hsd hsb
    exact key u (Subgroup.mem_sup_left hu) hyu
  have hfix4 : ∀ i, ∀ m : ℕ, m < 3 → ∀ u ∈ U i, (c * a ^ m) * u = (u * (c * a ^ m)) → u ∈ V i :=
    fun i m hm u hu hyu => hUfix i u hu (hstep4 i m hm u hu hyu)
  have hnc : a ∉ Subgroup.zpowers c := fun h => ha1 (by
    have h1 : a ∈ (Subgroup.zpowers c ⊔ Subgroup.zpowers d) ⊓ L :=
      ⟨Subgroup.mem_sup_left h, haL⟩
    rw [hcd] at h1
    exact Subgroup.mem_bot.mp h1)
  have hac : a * c = c * a := hAcomm a haA c hcA
  have h5a : ∀ i, ∀ u ∈ U i, a * u * a⁻¹ * u⁻¹ ∈ V i := fun i =>
    centralizes_quotient_of_four (hU2 i) (hVU i)
      (fun u hu v hv => by
        have h1 : v * u = u * v := Subgroup.mem_centralizer_iff.mp (hUle i hu) v hv
        have h2 : u * v * u⁻¹ = v := by rw [← h1]; group
        rw [h2]
        exact hv)
      hac ha3 hc3 hc1 hnc (hUnorm i (hE'V i haE')) (hE'V i haE') (hUnorm i (hE'V i hcE'))
      (hE'V i hcE') (fun m hm u hu hyu =>
        hfix4 i m hm u hu (mul_inv_eq_iff_eq_mul.mp hyu))
  obtain ⟨X, hXdef⟩ : ∃ X : Fin 2 → Subgroup G, X = fun i => Xsub K (V i) := ⟨_, rfl⟩
  have hXi : ∀ i, X i = Xsub K (V i) := fun i => by rw [hXdef]
  have hXperf : ∀ i, Group.IsPerfect (X i) := fun i => by
    rw [hXi]
    exact Xsub_perfect K (V i)
  have hXK : ∀ i, X i ≤ K := fun i => by
    rw [hXi]
    exact Xsub_le_K K (V i)
  have hXN : ∀ i, X i ≤ Subgroup.normalizer (V i : Set G) := fun i => by
    rw [hXi]
    exact Xsub_le_normalizer K (V i)
  have hXd : ∀ i, X i ≤ Subgroup.centralizer ({d} : Set G) := fun i => (hXK i).trans hKd
  have himX : ∀ i, imageSub K (X i) = inSubgroup perfectResidual (Subgroup.normalizer (Vb i :
      Set (K ⧸ aschbacherSolvableCore 3 K))) := fun i => by
    rw [hXi, imageSub_Xsub hθodd (hVK i) (hV2 i), hVimg i]
  have hVX : ∀ i j, V j ≤ X i := by
    intro i j v hv
    rw [hXi]
    refine mem_Xsub_of_mk_mem (p := 2) hθodd (hVK j hv) (hVnorm i j hv) ?_ ?_
    · obtain ⟨n, hn⟩ := hV2 j ⟨v, hv⟩
      exact ⟨n, by simpa using congrArg Subtype.val hn⟩
    · rw [← hXi, himX i]
      have h1 := mk_mem_imageSub (K := K) (D := V j) (x := ⟨v, hVK j hv⟩) hv
      rw [hVimg j] at h1
      exact hVb.le_res i j h1
  have haX : ∀ i, a ∈ X i := fun i => by
    rw [hXi]
    refine mem_Xsub_of_mk_mem (p := 3) hθ3 haK (hE'V i haE') ⟨1, by simpa using ha3⟩ ?_
    rw [← hXi, himX i]
    exact hVb.ab_mem i
  have hXcl : ∀ i, X i ≤ Subgroup.closure {z : G | ∃ x ∈ X i, z = x * a * x⁻¹} := fun i => by
    rw [hXi]
    refine Xsub_le_closure haK (by rw [← hXi]; exact haX i) ?_
    rw [← hXi, himX i]
    exact hVb.closure i
  have hUX : ∀ i, ⁅CFSG.Assembly.pCoreOf 2 (Subgroup.centralizer (V i : Set G)), X i⁆ ≤ V i :=
    fun i => by
      rw [← hUi i]
      exact commutator_le_of_closure ((hXN i).trans (hUnorm i)) (hXN i) (haX i) (h5a i) (hXcl i)
  have hUd' : ∀ i, ¬ CFSG.Assembly.pCoreOf 2 (Subgroup.centralizer (V i : Set G)) ≤
      Subgroup.centralizer ({d} : Set G) := fun i => by
    rw [← hUi i]
    exact hUd i
  have hXXK : X 0 ⊔ X 1 ≤ K := sup_le (hXK 0) (hXK 1)
  have himgX : imageSub K (X 0 ⊔ X 1) = ⊤ := by
    rw [imageSub_sup (hXK 0) (hXK 1), himX 0, himX 1]
    exact hVb.gen
  obtain ⟨B, hBle, hBe, hB27⟩ := exists_E27_in_join hXXK himgX e
  have hdK : d ∉ K := C.d_not_mem_K hZ
  exact false_of_steps hchar hbig hd3 hV2 hV1 hVc hXperf hXd hXN hVX hUX hUd'
    ⟨B, hBle, hBe, hB27, disjoint_zpowers_of_not_mem hd3 hd1 hdK (hBle.trans hXXK)⟩

end J3Main

end CFSG.RankThree.PartTwo.Sec8.Hering611
