module

public import CFSG.RankThree.PartTwo.Sec8.Item86ResProofCenter
public import CFSG.RankThree.PartTwo.Sec8.Item86Res2ProofField
public import CFSG.RankThree.PartTwo.Sec8.Item87Proof84
import CFSG.RankThree.PartTwo.Sec8.Item87ProofOrders
import CFSG.RankThree.PartTwo.Sec6.Item65Tools
import CFSG.RankThree.PartOne.S10.FiveSuccessorTheta
public import CFSG.RankThree.Asc83Table.E9
public import CFSG.RankThree.PartTwo.Sec13.Item13SetupAt
public import CFSG.RankThree.PartTwo.Sec8.Item86ResProofChoice
public import CFSG.RankThree.PartTwo.Sec8.Item86ResProofOmega
public import CFSG.RankThree.PartTwo.Sec8.Standing

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item86ResProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec8.Item83Proof
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

@[expose] def Pair84PartnerU : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a d : G) (n : ℕ),
    Sec8Std G A c L a d n → ∀ (b : G) (X : Subgroup G), b ∈ Subgroup.closure ({c, d} : Set G) →
      PairRel A c L b X →
        (b, X) ∈ pairOmega A ∧ ((∃ m : ℕ, IsUnitaryTwo (X ⧸ aschbacherSolvableCore 3 X) m) →
          IsGammaIndex A X c n ∧
            (KFacts.InducesStdKind X a .field ∨ KFacts.InducesStdKind X a .graphField) ∧
            PairRel A b X c L)

@[expose] def Pair84GammaU : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a d : G) (n : ℕ),
    Sec8Std G A c L a d n → ∀ (b : G) (X : Subgroup G), b ∈ Subgroup.closure ({c, d} : Set G) →
      PairRel A c L b X → (∃ m : ℕ, IsUnitaryTwo (X ⧸ aschbacherSolvableCore 3 X) m) →
        IsGammaIndex A X c n

@[expose] def Pair84GammaNonempty : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a d : G) (n : ℕ),
    Sec8Std G A c L a d n → ∀ (b : G) (X : Subgroup G), b ∈ Subgroup.closure ({c, d} : Set G) →
      PairRel A c L b X → (∀ m : ℕ, ¬ IsUnitaryTwo (X ⧸ aschbacherSolvableCore 3 X) m) →
        (gammaSet A X).Nonempty

section Proof

variable {G : Type} [Group G] [Finite G]

theorem partner_data {A : Subgroup G} {c : G} {L : Subgroup G} {a d : G} {n : ℕ}
    (h : Sec8Std G A c L a d n) {b : G} (hb : b ∈ Subgroup.closure ({c, d} : Set G))
    {X : Subgroup G} (hrel : PairRel A c L b X) :
    IsGammaIndex A L b n ∧ b ∉ Subgroup.zpowers c ∧
      L ⊓ Subgroup.centralizer ({b} : Set G) = L ⊓ Subgroup.centralizer ({d} : Set G) := by
  have hd := h.data83
  have hn1 : 1 ≤ n := hd.odd.pos
  have hAe := h.mem_partTwoF.1
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have h3 : ∀ y ∈ A, y ^ 3 = 1 := hAe.2
  have hdΓ := isGammaIndex_of_data83 hd
  have hbΓ : IsGammaIndex A L b n := by
    obtain ⟨m, hm⟩ := hrel.2.1
    have hmn := eq_of_isGammaType (one_le_of_isGammaIndex hm) hn1
      (isGammaType_of_isGammaIndex hm) (isGammaType_of_isGammaIndex hdΓ)
    rwa [hmn] at hm
  have hbc : b ∉ Subgroup.zpowers c :=
    not_mem_zpowers_of_isGammaIndex h.mem_thetaComponentsAt hbΓ
  have hcL := Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt
  have hcy : ∀ y ∈ L, c * y = y * c := fun y hy =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hcL hy)).symm
  obtain ⟨i, j, -, hj, hbij⟩ := KFacts.exists_pow_mul_pow_of_mem_closure_pair
    (hcomm c h.mem_A d hd.d_mem) (h3 c h.mem_A) (h3 d hd.d_mem) hb
  have hj0 : j ≠ 0 := by
    rintro rfl
    apply hbc
    rw [hbij, pow_zero, mul_one]
    exact Subgroup.npow_mem_zpowers c i
  refine ⟨hbΓ, hbc, ?_⟩
  rw [hbij]
  exact inf_centralizer_mul_pow_eq hcy (h3 d hd.d_mem) i (by omega)

theorem mem_pairOmega_of_partner (hKB : KF83KBarTwo) (hInd : KF83Indep) {A : Subgroup G} {c : G}
    {L : Subgroup G} {a d : G} {n : ℕ} (h : Sec8Std G A c L a d n) {b : G}
    (hb : b ∈ Subgroup.closure ({c, d} : Set G)) {X : Subgroup G} (hrel : PairRel A c L b X)
    (hkind : KFacts.InducesStdKind X a .field ∨ KFacts.InducesStdKind X a .graphField)
    (hΓ : (gammaSet A X).Nonempty) : (b, X) ∈ pairOmega A := by
  obtain ⟨hbΓ, -, hLb⟩ := partner_data h hb hrel
  obtain ⟨T, hT, hT1, hTK⟩ := exists_invariant_two_of_sec8Std hKB h
  have hKX : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ≤ X := by
    have h1 := hrel.2.2.2.1
    rwa [hLb] at h1
  refine ⟨hbΓ.1, hbΓ.2.1, hrel.2.2.1, ⟨a, h.a_mem, hkind⟩,
    ⟨Subgroup.closure ({c, a, d} : Set G), closure_le_of_sec8Std h, ?_, T,
      ⟨hTK.trans hKX, hT.2⟩, hT1⟩, hΓ⟩
  rw [card_closure_of_sec8Std hInd h, h.data83.card_eq]

theorem kinds_of_partner (h418 : Item418Theta) (hF : KF84FieldStd) {A : Subgroup G} {c : G}
    {L : Subgroup G} {a d : G} {n : ℕ} (h : Sec8Std G A c L a d n) {b : G}
    (hb : b ∈ Subgroup.closure ({c, d} : Set G)) {X : Subgroup G} (hrel : PairRel A c L b X) :
    (KFacts.InducesStdKind X a .field ∨ KFacts.InducesStdKind X a .graphField) ∧
      ¬ (KFacts.InducesStdKind X c .field ∨ KFacts.InducesStdKind X c .graphField) := by
  have hG : TheoremFourHyp G := h.toTheoremFourHyp
  have hAel := h.mem_partTwoF.1
  have hcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hAel.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  obtain ⟨hbΓ, -, hLb⟩ := partner_data h hb hrel
  obtain ⟨hbA, hb1, hn, -⟩ := Item87Proof.isGammaIndex_cases hbΓ
  have hb3 : b ^ 3 = 1 := hAel.2 b hbA
  have ha3 : a ^ 3 = 1 := hAel.2 a h.a_mem
  have hc3 : c ^ 3 = 1 := hAel.2 c h.mem_A
  have haC : a ∈ Subgroup.centralizer ({b} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm a h.a_mem b hbA)
  have hcC : c ∈ Subgroup.centralizer ({b} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm c h.mem_A b hbA)
  have hX : X ∈ thetaComponentsAt 3 b := hrel.2.2.1
  have hXb : X ≤ Subgroup.centralizer ({b} : Set G) :=
    (PartOne.mem_thetaComponentsAt_iff.mp hX).1
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    (PartOne.mem_thetaComponentsAt_iff.mp h.mem_thetaComponentsAt).1
  obtain ⟨hKmem, htype, -⟩ :=
    Item87Proof.residual_of_isGammaIndex h.mem_thetaComponentsAt hbΓ
  set K := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) with hK
  have hKX : K ≤ X := hrel.2.2.2.1
  have hKc : K ≤ Subgroup.centralizer ({c} : Set G) :=
    (Item87Proof.residual_le _).trans (inf_le_left.trans hLc)
  have hK' : K ∈ thetaComponentsIn (X ⊓ Subgroup.centralizer {c}) := by
    obtain ⟨-, hK''⟩ := mem_thetaComponentsIn_iff.mp hKmem
    refine mem_thetaComponentsIn_iff.mpr ⟨le_inf hKX hKc, ?_⟩
    exact PartOne.subgroupOf_mem_thetaComponents_of_le Nat.prime_three (le_inf hKX hKc)
      (le_inf inf_le_right (inf_le_left.trans hXb)) hK''
  have hac : a ∉ Subgroup.zpowers c := a_not_mem_zpowers h.toHyp81
  have hKa : KFacts.InducesStdKind K a .field := by
    have h1 := hF G A c L a A d n h.toHyp81 (lt_card_of_sec8Std h) h.data83
    rw [← hLb] at h1
    exact h1
  exact Item87Proof.item418_centralizer h418 hG hb3 hb1 haC hcC ha3 hc3
    (hcomm a h.a_mem c h.mem_A) h.ne_one hac hX hK' hn htype hKa

theorem pairRel_symm_of_partner {A : Subgroup G} {c : G} {L : Subgroup G} {a d : G} {n : ℕ}
    (h : Sec8Std G A c L a d n) {b : G} (hb : b ∈ Subgroup.closure ({c, d} : Set G))
    {X : Subgroup G} (hrel : PairRel A c L b X) (hΩ : (b, X) ∈ pairOmega A) {m : ℕ}
    (hcΓ : IsGammaIndex A X c m) : PairRel A b X c L := by
  obtain ⟨hbΓ, -, -⟩ := partner_data h hb hrel
  have hX : X ∈ thetaComponentsAt 3 b := hrel.2.2.1
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    (PartOne.mem_thetaComponentsAt_iff.mp h.mem_thetaComponentsAt).1
  obtain ⟨hKe, -, hKe1⟩ := Item87Proof.residual_of_isGammaIndex h.mem_thetaComponentsAt hbΓ
  obtain ⟨hKb, -, -⟩ := Item87Proof.residual_of_isGammaIndex hX hcΓ
  set Ke := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) with hKedef
  set Kb := inSubgroup perfectResidual (X ⊓ Subgroup.centralizer ({c} : Set G)) with hKbdef
  have hKeL : Ke ≤ L := (Item87Proof.residual_le _).trans inf_le_left
  have hKeKb : Ke ≤ Kb :=
    KFacts.le_inSubgroup_perfectResidual (Item87Proof.isPerfect_residual _)
      (le_inf hrel.2.2.2.1 (hKeL.trans hLc))
  have hKb' : Kb ∈ thetaComponentsIn
      (Subgroup.centralizer {c} ⊓ Subgroup.centralizer {b}) := by
    rwa [inf_comm] at hKb
  have heq : Ke = Kb := Sec6.eq_of_mem_thetaComponentsIn_of_le hKe hKb'
    (Item87Proof.isPerfect_residual _) hKe1 le_rfl hKeKb
  refine ⟨hΩ, ⟨m, hcΓ⟩, h.mem_thetaComponentsAt, ?_, ?_⟩
  · show Kb ≤ L
    rw [← heq]
    exact hKeL
  · show L ≠ Kb ⊔ inSubgroup (aschbacherSolvableCore 3) L
    rw [← heq]
    intro hsup
    have htop := Item87Proof.imageModTheta_eq_top_of_eq_sup hKeL hsup
    let ι : L ⧸ aschbacherSolvableCore 3 L ≃* imageModTheta L Ke :=
      Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr htop.symm)
    obtain ⟨-, -, hm, hcases⟩ := Item87Proof.isGammaIndex_cases hbΓ
    rcases hcases with ⟨hRee, F, hF', hFf, hFc, ⟨φ⟩⟩ | ⟨hL2, ⟨φ⟩⟩
    · exact (kF84Proper _ n hm).1 hRee ⟨F, hF', hFf, hFc, ⟨ι.trans φ⟩⟩
    · exact (kF84Proper _ n hm).2 hL2 ⟨ι.trans φ⟩

end Proof

theorem pair84PartnerU_of (h418 : Item418Theta) (hKB : KF83KBarTwo) (hInd : KF83Indep)
    (hF : KF84FieldStd) (hU : Pair84GammaU) (hN : Pair84GammaNonempty) : Pair84PartnerU := by
  intro G _ _ A c L a d n h b X hb hrel
  obtain ⟨hkind, -⟩ := kinds_of_partner h418 hF h hb hrel
  by_cases hXU : ∃ m : ℕ, IsUnitaryTwo (X ⧸ aschbacherSolvableCore 3 X) m
  · have hcΓ := hU G A c L a d n h b X hb hrel hXU
    have hΩ := mem_pairOmega_of_partner hKB hInd h hb hrel hkind ⟨c, n, hcΓ⟩
    exact ⟨hΩ, fun _ => ⟨hcΓ, hkind, pairRel_symm_of_partner h hb hrel hΩ hcΓ⟩⟩
  · exact ⟨mem_pairOmega_of_partner hKB hInd h hb hrel hkind
      (hN G A c L a d n h b X hb hrel fun m hm => hXU ⟨m, hm⟩), fun h' => absurd h' hXU⟩

theorem pair86Center_ofU (h45 : Sec4.Item4_5) (h84 : Pair84PartnerU) (hKB : KF83KBarTwo)
    (hG2 : KF83IndepGTwo) : Pair86Center := by
  intro G _ _ A c L a d n h b X hb hrel hLU hXU x hx
  by_contra hxb
  have hd := h.data83
  have hn1 : 1 ≤ n := hd.odd.pos
  have hA81 : Nat.card A = 81 := hd.card_eq
  have hAe := h.mem_partTwoF.1
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have h3 : ∀ y ∈ A, y ^ 3 = 1 := hAe.2
  have ha := h.a_mem_normalizer
  have hcL := Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt
  have hcy : ∀ y ∈ L, c * y = y * c := fun y hy =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hcL hy)).symm
  have hdΓ := isGammaIndex_of_data83 hd
  have hbΓ : IsGammaIndex A L b n := by
    obtain ⟨m, hm⟩ := hrel.2.1
    have hmn := eq_of_isGammaType (one_le_of_isGammaIndex hm) hn1
      (isGammaType_of_isGammaIndex hm) (isGammaType_of_isGammaIndex hdΓ)
    rwa [hmn] at hm
  have hbA : b ∈ A := hbΓ.1
  have hb1 : b ≠ 1 := hbΓ.2.1
  have hbc : b ∉ Subgroup.zpowers c :=
    not_mem_zpowers_of_isGammaIndex h.mem_thetaComponentsAt hbΓ
  obtain ⟨hcγ, -, -⟩ := (h84 G A c L a d n h b X hb hrel).2 hXU
  have hX := hrel.2.2.1
  obtain ⟨m, hXm⟩ := hXU
  have hA3 : IsPGroup 3 A := fun u => ⟨1, Subtype.ext (by simpa using h3 u u.2)⟩
  have hAb : A ≤ Subgroup.centralizer ({b} : Set G) := fun z hz =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm z hz b hbA)
  have hAN : A ≤ Subgroup.normalizer (X : Set G) :=
    Sec11.le_normalizer_of_isPGroup_of_le_centralizer h45 h.toTheoremFourHyp (h3 b hbA) hb1
      hA3 hAb X hX
  have hsec := Sec13.sectionCentralizer_eq_inf hAN
  set C := A ⊓ Sec4.thetaQuotCentralizer X with hCdef
  have hxC : x ∈ C := by
    have h1 : x ∈ ((C : Subgroup G) : Set G) := hsec ▸ hx
    exact h1
  have hbC : b ∈ C := by
    have h1 := zpowers_subset_sectionCentralizer hbA
      (Sec6.le_centralizer_of_mem_thetaComponentsAt hX) (Subgroup.mem_zpowers b)
    have h2 : b ∈ ((C : Subgroup G) : Set G) := hsec ▸ h1
    exact h2
  have hcd : c * d = d * c := hcomm c h.mem_A d hd.d_mem
  obtain ⟨i, j, -, hj, hbij⟩ :=
    KFacts.exists_pow_mul_pow_of_mem_closure_pair hcd (h3 c h.mem_A) (h3 d hd.d_mem) hb
  have hj0 : j ≠ 0 := by
    rintro rfl
    apply hbc
    rw [hbij, pow_zero, mul_one]
    exact Subgroup.npow_mem_zpowers c i
  have hLbd : L ⊓ Subgroup.centralizer ({b} : Set G) =
      L ⊓ Subgroup.centralizer ({d} : Set G) := by
    rw [hbij]
    exact inf_centralizer_mul_pow_eq hcy (h3 d hd.d_mem) i (by omega)
  set K := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) with hKdef
  have hKX : K ≤ X := by
    have h1 := hrel.2.2.2.1
    rwa [hLbd] at h1
  have hKL : K ≤ L := (Subgroup.map_subtype_le _).trans inf_le_left
  have hKM : K ≤ inSubgroup perfectResidual (X ⊓ Subgroup.centralizer ({c} : Set G)) :=
    KFacts.le_inSubgroup_perfectResidual (isPerfect_inSubgroup_perfectResidual' _)
      (le_inf hKX (hKL.trans hcL))
  have hL2 := projSL_of_isGammaIndex_of_isUnitaryTwo hcγ hXm
  have hKL2 : Nonempty (imageModTheta L K ≃* projSL 2 (GaloisField 2 (3 * n))) := by
    rcases hd.cases with ⟨-, hK, -⟩ | ⟨-, -, hKSU⟩ | ⟨-, -, hK⟩ | ⟨-, -, hK⟩ | ⟨-, -, hK⟩
    · exact hK
    · exact (false_of_isoSUThree_le_projSL hKL hKM
        ((Subgroup.map_subtype_le _).trans inf_le_left) hd.odd hKSU hL2).elim
    · exact hK
    · exact hK
    · exact hK
  obtain ⟨eK⟩ := hKL2
  have hθ := theta_inf_le_theta hKL hKX (m := 3 * n) (by omega) eK
  have hXperf : Group.IsPerfect (X ⧸ aschbacherSolvableCore 3 X) :=
    (Sec6.isQuasisimple_of_mem_thetaComponentsAt hX).1
  have hcC : c ∉ C := fun hc => false_of_isGammaIndex_of_card_eq hcγ
    (card_imageModTheta_eq_of_mem_thetaQuotCentralizer hc.2 (h3 c h.mem_A) hXperf)
  have hda : d * a = a * d := hcomm d hd.d_mem a h.a_mem
  have haLd : a ∈ Subgroup.normalizer ((L ⊓ Subgroup.centralizer {d} : Subgroup G) : Set G) := by
    have haC : a ∈ Subgroup.normalizer (Subgroup.centralizer ({d} : Set G) : Set G) :=
      Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr hda.symm)
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [Subgroup.mem_inf, Subgroup.mem_inf, (Subgroup.mem_normalizer_iff.mp ha y),
      (Subgroup.mem_normalizer_iff.mp haC y)]
  have haK : a ∈ Subgroup.normalizer (K : Set G) :=
    CFSG.RankThree.GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual
      _ haLd
  have haC : ∀ k : ℕ, a * c ^ k ∉ C := by
    intro k hk
    obtain ⟨-, hkθ⟩ := Sec6.mem_thetaQuotCentralizer_iff.mp hk.2
    refine false_of_imageModTheta_le_barCentralizer hG2 hd ?_
    rintro _ ⟨κ, hκ, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hκ
    have hκX : (κ : G) ∈ X := hKX hκ
    have hck : c ^ k * (κ : G) = κ * c ^ k := (Commute.pow_left (hcy κ κ.2) k).eq
    have hv : (κ : G)⁻¹ * (a * κ * a⁻¹) ∈
        (aschbacherSolvableCore 3 X).map X.subtype ⊓ K := by
      refine ⟨?_, K.mul_mem (K.inv_mem hκ) ((Subgroup.mem_normalizer_iff.mp haK κ).mp hκ)⟩
      have h1 := hkθ κ hκX
      have e : (a * c ^ k) * (κ : G) * (a * c ^ k)⁻¹ = a * κ * a⁻¹ := by
        calc (a * c ^ k) * (κ : G) * (a * c ^ k)⁻¹ = a * (c ^ k * κ) * (c ^ k)⁻¹ * a⁻¹ := by
              group
          _ = a * κ * a⁻¹ := by rw [hck]; group
      rwa [e] at h1
    obtain ⟨w, hw, hwv⟩ := hθ hv
    rw [KFacts.mem_barCentralizer_zpowers_iff ha, QuotientGroup.mk'_apply,
      Sec4.thetaQuotMulAut_mk, QuotientGroup.eq]
    have e2 : (Sec4.compAction L ⟨a, ha⟩ κ)⁻¹ * κ = w⁻¹ := by
      apply Subtype.ext
      change (a * (κ : G) * a⁻¹)⁻¹ * κ = (w : G)⁻¹
      rw [show (w : G) = (κ : G)⁻¹ * (a * κ * a⁻¹) from hwv]
      group
    rw [e2]
    exact (aschbacherSolvableCore 3 L).inv_mem hw
  have hca : c * a = a * c := hcomm c h.mem_A a h.a_mem
  have hc3 := h3 c h.mem_A
  have ha3 := h3 a h.a_mem
  have hdisjC : ∀ y ∈ Subgroup.closure ({c, a} : Set G), y ∈ C → y = 1 := by
    intro y hy hyC
    obtain ⟨i', j', hi', hj', rfl⟩ := KFacts.exists_pow_mul_pow_of_mem_closure_pair hca hc3 ha3 hy
    have hcomm' : ∀ s t : ℕ, Commute (c ^ s) (a ^ t) := fun s t => (Commute.pow_pow hca s t)
    rcases (show j' = 0 ∨ j' = 1 ∨ j' = 2 by omega) with rfl | rfl | rfl
    · rcases (show i' = 0 ∨ i' = 1 ∨ i' = 2 by omega) with rfl | rfl | rfl
      · simp
      · exact absurd (by simpa using hyC) hcC
      · exfalso
        apply hcC
        have e : c = (c ^ 2 * a ^ 0) ^ 2 := by
          rw [pow_zero, mul_one, ← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hc3,
            one_mul, pow_one]
        rw [e]
        exact C.pow_mem hyC 2
    · exfalso
      apply haC i'
      have e : a * c ^ i' = c ^ i' * a ^ 1 := by
        rw [pow_one]
        exact ((Commute.pow_left hca i').eq).symm
      rw [e]
      exact hyC
    · exfalso
      apply haC (2 * i')
      have e : a * c ^ (2 * i') = (c ^ i' * a ^ 2) ^ 2 := by
        rw [(hcomm' i' 2).mul_pow, ← pow_mul, ← pow_mul, show 2 * 2 = 3 + 1 by norm_num,
          pow_add, ha3, one_mul, pow_one, mul_comm i' 2]
        exact ((Commute.pow_right hca.symm (2 * i')).eq)
      rw [e]
      exact C.pow_mem hyC 2
  have hxA : x ∈ A := hxC.1
  have hac : a ∉ Subgroup.zpowers c := a_not_mem_zpowers h.toHyp81
  set D := Subgroup.closure ({c, a} : Set G) with hD
  set B := Subgroup.closure ({b, x} : Set G) with hB
  have hD9 : Nat.card D = 9 :=
    CFSG.RankThree.Asc83Table.card_closure_pair_eq_nine hc3 ha3 hca h.ne_one hac
  have hB9 : Nat.card B = 9 :=
    CFSG.RankThree.Asc83Table.card_closure_pair_eq_nine (h3 b hbA) (h3 x hxA)
      (hcomm b hbA x hxA) hb1 hxb
  have hBC : B ≤ C := by
    rw [hB, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact hbC
    · exact hxC
  have hDA : D ≤ A := by
    rw [hD, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact h.mem_A
    · exact h.a_mem
  have hBA : B ≤ A := hBC.trans inf_le_left
  have hdisj : Disjoint D B := by
    rw [Subgroup.disjoint_def]
    intro y hyD hyB
    exact hdisjC y hyD (hBC hyB)
  have hBN : B ≤ Subgroup.normalizer (D : Set G) := fun y hy =>
    Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun z hz => hcomm z (hDA hz) y (hBA hy))
  have hDB : D ⊔ B = A := by
    apply Subgroup.eq_of_le_of_card_ge (sup_le hDA hBA)
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer D B hBN hdisj, hD9,
      hB9, hA81]
  obtain ⟨T, hT, hT1, hTK⟩ := exists_invariant_two_of_sec8Std hKB h
  have hT2 : IsPGroup 2 T := (isPiSubgroup_piOf_iff Nat.prime_two T).mp hT.2.1
  have hTX : T ≤ X := hTK.trans hKX
  have hET : Subgroup.closure ({c, a, d} : Set G) ≤ Subgroup.normalizer (T : Set G) := hT.2.2
  have hcT : c ∈ Subgroup.normalizer (T : Set G) := hET (Subgroup.subset_closure (by simp))
  have haT : a ∈ Subgroup.normalizer (T : Set G) := hET (Subgroup.subset_closure (by simp))
  set P := preimageTheta X T with hP
  have hAP : A ≤ Subgroup.normalizer (P : Set G) := by
    rw [← hDB]
    refine sup_le ?_ ?_
    · rw [hD, Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact mem_normalizer_preimageTheta hTX (hAN h.mem_A) hcT
      · exact mem_normalizer_preimageTheta hTX (hAN h.a_mem) haT
    · rw [hB, Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact mem_normalizer_preimageTheta_of_mem hTX hbC.2
      · exact mem_normalizer_preimageTheta_of_mem hTX hxC.2
  have hodd := odd_card_of_le_normalizer h.toTheoremFourHyp.localRank_three.le hAe hA81
    (not_three_dvd_card_preimageTheta hTX hT2) hAP
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hT2
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact hT1 (Subgroup.eq_bot_of_card_eq T hk)
  have h2T : 2 ∣ Nat.card T := by
    rw [hk]
    exact dvd_pow_self 2 hk0
  have h2P : 2 ∣ Nat.card P := h2T.trans (Subgroup.card_dvd_of_le (le_preimageTheta hTX))
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2P)

theorem choice86Var_of_narrowU (h84 : Pair84PartnerU) (h85 : Pair85Exists)
    (h86 : Pair86Exists) (hC : Pair86Center) (hGN : Pair86GTwoN) : Choice86Var := by
  intro G _ _ A c L a d n h
  have hd := h.data83
  have hn1 : 1 ≤ n := hd.odd.pos
  have hA81 : Nat.card A = 81 := hd.card_eq
  have hdΓ : IsGammaIndex A L d n := isGammaIndex_of_data83 hd
  have hLtype := isGammaType_of_isGammaIndex hdΓ
  have hcL : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt
  have hγn : ∀ b ∈ gammaSet A L, IsGammaIndex A L b n := by
    rintro b ⟨m, hm⟩
    have hmn := eq_of_isGammaType (one_le_of_isGammaIndex hm) hn1
      (isGammaType_of_isGammaIndex hm) hLtype
    rwa [hmn] at hm
  have mkPair : ∀ (a' b : G) (X : Subgroup G), Hyp81 G A c L a' →
      b ∈ Subgroup.closure ({c, d} : Set G) → PairRel A c L b X →
      (∀ m : ℕ, ¬ IsUnitaryTwo (X ⧸ aschbacherSolvableCore 3 X) m) →
      ((∃ m : ℕ, IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) m) →
        IsoGTwoEven (barCentralizer (Subgroup.zpowers a') X) n ∨
          Nonempty (barCentralizer (Subgroup.zpowers a') X ≃* projSp 2 (GaloisField 2 n))) →
      Sec8PairGTwo L a' n → (∀ m : ℕ, Sec8PairGTwo X a' m) → Sec8Pair G A c L a' b X n :=
    fun a' b X h81 hb hrel hXU hcent hg hgX =>
    { toHyp81 := h81
      card_eq := hA81
      pairRel := hrel
      isGammaIndex := hγn b hrel.2.1
      mem_pairOmega := (h84 G A c L a d n h b X hb hrel).1
      not_unitary := hXU
      centralizer_of_unitary := hcent
      gTwo := hg
      gTwoPartner := hgX }
  by_cases hLU : ∃ m : ℕ, IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) m
  ·
    have hLU3 : IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) (3 * n) := by
      obtain ⟨m, hm⟩ := hLU
      rcases hd.cases with ⟨hD | hG, -, -⟩ | ⟨hR, -, -⟩ | ⟨hS, -, -⟩ | ⟨hU, -, -⟩ | ⟨⟨e⟩, -, -⟩
      · exact ((sigD4_of_isoTrialityD4 hn1 hD).not_isUnitaryTwo hn1 m hm).elim
      · exact ((sigG2_of_isoGTwo hn1 (isoGTwo_of_isoGTwoEven (by omega) hG)).not_isUnitaryTwo
          hn1 m hm).elim
      · obtain ⟨k, hk, hkn, he⟩ := reeF4_of_isoReeF4 (by omega) hR
        exact ((sigF4_of_reeF4 hn1 ⟨k, hk, hkn, he⟩).not_isUnitaryTwo hn1 m hm).elim
      · exact Or.inr hS
      · exact Or.inl hU
      · exact ((sigSp4_of_projSp hn1 e).not_isUnitaryTwo hn1 m hm).elim
    obtain ⟨b, hb, -, X, hrel, hlist, halt⟩ := h86 G A c L a d n h hLU3
    have hXU := not_isUnitaryTwo_of_isList86 hn1 hlist
    have hg : ∀ a' : G, Sec8PairGTwo L a' n := fun _ => sec8PairGTwo_of_isUnitaryTwo hn1 hLU3
    rcases halt with hG2 | ⟨ε, -, hG2'⟩ | hSpC
    · exact ⟨c, L, a, b, X, Or.inl ⟨rfl, rfl⟩, ⟨0, by rw [zpow_zero, mul_one]⟩,
        mkPair a b X h.toHyp81 hb hrel hXU (fun _ => Or.inl hG2) (hg a)
          (sec8PairGTwo_forall_of_isList86 hn1 hlist hG2)⟩
    · exact ⟨c, L, a * c ^ ε, b, X, Or.inl ⟨rfl, rfl⟩, ⟨ε, rfl⟩,
        mkPair (a * c ^ ε) b X (hyp81_mul_zpow h.toHyp81 ε (mul_zpow_ne_one h.toHyp81 ε)) hb
          hrel hXU (fun _ => Or.inl hG2') (hg (a * c ^ ε))
          (sec8PairGTwo_forall_of_isList86 hn1 hlist hG2')⟩
    · exact ⟨c, L, a, b, X, Or.inl ⟨rfl, rfl⟩, ⟨0, by rw [zpow_zero, mul_one]⟩,
        mkPair a b X h.toHyp81 hb hrel hXU (fun _ => Or.inr hSpC) (hg a)
          (sec8PairGTwo_forall_of_projSp hd.odd hlist hSpC)⟩
  ·
    have hLU' : ∀ m : ℕ, ¬ IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) m :=
      fun m hm => hLU ⟨m, hm⟩
    obtain ⟨b, hb, hb1, X, hrel⟩ := h85 G A c L a d n h hLU'
    by_cases hXU : ∃ m : ℕ, IsUnitaryTwo (X ⧸ aschbacherSolvableCore 3 X) m
    ·
      obtain ⟨hΩX, hU⟩ := h84 G A c L a d n h b X hb hrel
      obtain ⟨hcγ, hkind, hrel'⟩ := hU hXU
      have hbΓ := hγn b hrel.2.1
      have hcentL : IsoGTwoEven (barCentralizer (Subgroup.zpowers a) L) n ∨
          Nonempty (barCentralizer (Subgroup.zpowers a) L ≃* projSp 2 (GaloisField 2 n)) := by
        rcases hd.cases with ⟨hL1, -, -⟩ | ⟨hR, -, -⟩ | ⟨hS, -, -⟩ | ⟨hU, -, -⟩ | ⟨-, hSpC, -⟩
        · exact Or.inl (h.gTwo hL1)
        · exfalso
          obtain ⟨k, hk, hkn, he⟩ := reeF4_of_isoReeF4 (by omega) hR
          have hF := sigF4_of_reeF4 hn1 ⟨k, hk, hkn, he⟩
          have hSU := isoSUThree_of_isGammaIndex_of_sigF4 hbΓ hF
          obtain ⟨m, hm⟩ := hXU
          have hL2 := projSL_of_isGammaIndex_of_isUnitaryTwo hcγ hm
          have hKL : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) ≤ L :=
            (Subgroup.map_subtype_le _).trans inf_le_left
          have hKM : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) ≤
              inSubgroup perfectResidual (X ⊓ Subgroup.centralizer ({c} : Set G)) :=
            KFacts.le_inSubgroup_perfectResidual (isPerfect_inSubgroup_perfectResidual' _)
              (le_inf hrel.2.2.2.1 (hKL.trans hcL))
          exact false_of_isoSUThree_le_projSL hKL hKM
            ((Subgroup.map_subtype_le _).trans inf_le_left) hd.odd hSU hL2
        · exact absurd (Or.inr hS) (hLU' (3 * n))
        · exact absurd (Or.inl hU) (hLU' (3 * n))
        · exact Or.inr hSpC
      have h81 : Hyp81 G A b X a :=
        hyp81_of_partner h.toHyp81 hA81 hbΓ.1 hb1 hrel.2.2.1 hΩX hkind
          (hC G A c L a d n h b X hb hrel hLU' hXU)
      have hgX : Sec8PairGTwo X a n := by
        obtain ⟨k, hk⟩ := hXU
        exact sec8PairGTwo_of_isUnitaryTwo hn1 hk
      exact ⟨b, X, a, c, L, Or.inr hrel, ⟨0, by rw [zpow_zero, mul_one]⟩,
        { toHyp81 := h81
          card_eq := hA81
          pairRel := hrel'
          isGammaIndex := hcγ
          mem_pairOmega := hrel.1
          not_unitary := hLU'
          centralizer_of_unitary := fun _ => hcentL
          gTwo := hgX
          gTwoPartner := sec8PairGTwo_forall hn1 hLtype h.gTwo }⟩
    ·
      have hXU' : ∀ m : ℕ, ¬ IsUnitaryTwo (X ⧸ aschbacherSolvableCore 3 X) m :=
        fun m hm => hXU ⟨m, hm⟩
      obtain ⟨k, hk⟩ := hGN G A c L a d n h hLU' b X hb hrel hXU'
      exact ⟨c, L, a * c ^ k, b, X, Or.inl ⟨rfl, rfl⟩, ⟨k, rfl⟩,
        mkPair (a * c ^ k) b X (hyp81_mul_zpow h.toHyp81 k (mul_zpow_ne_one h.toHyp81 k)) hb
          hrel hXU' (fun hU => absurd hU hLU) (sec8PairGTwo_mul_zpow h.toHyp81 h.gTwo k) hk⟩

theorem choice86Var_of_narrowU_item45 (h45 : Sec4.Item4_5) (h84 : Pair84PartnerU)
    (h85 : Pair85Exists) (h86 : Pair86Exists) (hKB : KF83KBarTwo) (hG2 : KF83IndepGTwo)
    (hGN : Pair86GTwoN) : Choice86Var :=
  choice86Var_of_narrowU h84 h85 h86 (pair86Center_ofU h45 h84 hKB hG2) hGN

end CFSG.RankThree.PartTwo.Sec8.Item86ResProof
