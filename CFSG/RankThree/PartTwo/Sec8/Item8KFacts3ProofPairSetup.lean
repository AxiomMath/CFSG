module

public import CFSG.RankThree.PartTwo.Sec8.Item86ResProofTwo
import CFSG.RankThree.PartTwo.Sec8.Item812Res7ProofD4N
import CFSG.RankThree.PartTwo.Sec8.Item812Res8ProofOmegaCent
import CFSG.RankThree.PartTwo.Sec6.Item65Tools
public import CFSG.RankThree.PartTwo.Sec8.Item86Res2Proof84

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item8KFacts3

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec8.Item83Proof CFSG.RankThree.PartTwo.Sec8.Item86ResProof
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

section Theta

variable {G : Type} [Group G] [Finite G]

theorem theta_inf_le_theta_of_noThetaNormal {L X K : Subgroup G} (hKL : K ≤ L) (hKX : K ≤ X)
    (hN : NoThetaNormal (imageModTheta L K)) :
    (aschbacherSolvableCore 3 X).map X.subtype ⊓ K ≤
      (aschbacherSolvableCore 3 L).map L.subtype := by
  set θX := (aschbacherSolvableCore 3 X).map X.subtype with hθX
  set N := θX ⊓ K with hNdef
  set Kb := imageModTheta L K with hKb
  set Nb := imageModTheta L N with hNb
  have hNK : N ≤ K := inf_le_right
  have hNL : N ≤ L := hNK.trans hKL
  have hNbKb : Nb ≤ Kb := Subgroup.map_mono (fun y hy => hNK hy)
  have hnorm : (Nb.subgroupOf Kb).Normal := by
    constructor
    intro u hu g
    rw [Subgroup.mem_subgroupOf] at hu ⊢
    obtain ⟨κ, hκ, hκg⟩ := g.2
    obtain ⟨ν, hν, hνu⟩ := hu
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hκ hν
    have hκX : (κ : G) ∈ X := hKX hκ
    have hmem : (κ : G) * ν * (κ : G)⁻¹ ∈ N := by
      refine ⟨?_, K.mul_mem (K.mul_mem hκ (hNK hν)) (K.inv_mem hκ)⟩
      exact (Subgroup.mem_normalizer_iff.mp
        (KFacts.normalizer_le_normalizer_theta X (Subgroup.le_normalizer hκX)) _).mp hν.1
    refine ⟨κ * ν * κ⁻¹, hmem, ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hκg, hνu]
  have hθs : Group.IsSolvable (aschbacherSolvableCore 3 X) :=
    (solvable_prime_complement_core_characterization (H := X) Nat.prime_three).1
  have hθXs : Group.IsSolvable θX :=
    Group.isSolvable_of_surjective (f := X.subtype.subgroupMap (aschbacherSolvableCore 3 X))
      (X.subtype.subgroupMap_surjective _)
  have hNs : Group.IsSolvable N :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion (inf_le_left : N ≤ θX))
      (Subgroup.inclusion_injective _)
  have hNLs : Group.IsSolvable (N.subgroupOf L) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hNL).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hNL).injective
  have hNbs : Group.IsSolvable Nb :=
    Group.isSolvable_of_surjective
      (f := (QuotientGroup.mk' (aschbacherSolvableCore 3 L)).subgroupMap (N.subgroupOf L))
      ((QuotientGroup.mk' _).subgroupMap_surjective _)
  have hsol : Group.IsSolvable (Nb.subgroupOf Kb) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hNbKb).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hNbKb).injective
  have h3 : ¬ 3 ∣ Nat.card (Nb.subgroupOf Kb) := by
    intro h3
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNbKb).toEquiv] at h3
    have h1 : Nat.card Nb ∣ Nat.card N := card_imageModTheta_dvd hNL
    have h2 : Nat.card N ∣ Nat.card (aschbacherSolvableCore 3 X) := by
      have := Subgroup.card_dvd_of_le (inf_le_left : N ≤ θX)
      rwa [hθX, Subgroup.card_map_of_injective X.subtype_injective] at this
    exact KFacts.not_three_dvd_card_aschbacherSolvableCore X ((h3.trans h1).trans h2)
  have hbot := hN _ hnorm hsol h3
  have hNb1 : Nb = ⊥ := by
    rw [Subgroup.subgroupOf_eq_bot] at hbot
    exact le_bot_iff.mp (fun y hy => hbot.le_bot (Subgroup.mem_inf.mpr ⟨hy, hNbKb hy⟩))
  intro ν hν
  have hmem : QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨ν, hNL hν⟩ ∈ Nb :=
    ⟨⟨ν, hNL hν⟩, hν, rfl⟩
  rw [hNb1, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
  exact ⟨_, hmem, rfl⟩

end Theta

section Center


variable {G : Type} [Group G] [Finite G]

theorem noThetaNormal_of_data83 {c : G} {L : Subgroup G} {a : G} {A₀ : Subgroup G} {d : G}
    {n : ℕ} (hd : Data83 G c L a A₀ d n) :
    NoThetaNormal (imageModTheta L
      (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)))) := by
  have hn1 : 1 ≤ n := hd.odd.pos
  rcases hd.cases with ⟨-, ⟨φ⟩, -⟩ | ⟨-, -, F, _, _, hFc, ⟨φ⟩⟩ | ⟨-, -, ⟨φ⟩⟩ | ⟨-, -, ⟨φ⟩⟩ |
      ⟨-, -, ⟨φ⟩⟩
  · exact Item87Proof.NoThetaNormal.of_mulEquiv φ
      (Item87Proof.noThetaNormal_projSL_two (by omega))
  · exact Item87Proof.NoThetaNormal.of_mulEquiv φ
      (Item87Proof.noThetaNormal_statedSU hFc (by omega))
  · exact Item87Proof.NoThetaNormal.of_mulEquiv φ
      (Item87Proof.noThetaNormal_projSL_two (by omega))
  · exact Item87Proof.NoThetaNormal.of_mulEquiv φ
      (Item87Proof.noThetaNormal_projSL_two (by omega))
  · exact Item87Proof.NoThetaNormal.of_mulEquiv φ
      (Item87Proof.noThetaNormal_projSL_two (by omega))


theorem le_normalizer_of_partner (h45 : Sec4.Item4_5) {A : Subgroup G} {c : G}
    {L : Subgroup G} {a d : G} {n : ℕ} (h : Sec8Std G A c L a d n) {b : G}
    (hb : b ∈ Subgroup.closure ({c, d} : Set G)) {X : Subgroup G} (hrel : PairRel A c L b X) :
    A ≤ Subgroup.normalizer (X : Set G) := by
  have hAe := h.mem_partTwoF.1
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have h3 : ∀ y ∈ A, y ^ 3 = 1 := hAe.2
  obtain ⟨hbΓ, -, -⟩ := partner_data h hb hrel
  have hbA : b ∈ A := hbΓ.1
  have hA3 : IsPGroup 3 A := fun u => ⟨1, Subtype.ext (by simpa using h3 u u.2)⟩
  have hAb : A ≤ Subgroup.centralizer ({b} : Set G) := fun z hz =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm z hz b hbA)
  exact Sec11.le_normalizer_of_isPGroup_of_le_centralizer h45 h.toTheoremFourHyp (h3 b hbA)
    hbΓ.2.1 hA3 hAb X hrel.2.2.1

theorem sectionCentralizer_subset_of_partner (h45 : Sec4.Item4_5) (hKB : KF83KBarTwo)
    (hG2 : KF83IndepGTwo) {A : Subgroup G} {c : G} {L : Subgroup G} {a d : G} {n : ℕ}
    (h : Sec8Std G A c L a d n) {b : G} (hb : b ∈ Subgroup.closure ({c, d} : Set G))
    {X : Subgroup G} (hrel : PairRel A c L b X) :
    Late.sectionCentralizer A X ((aschbacherSolvableCore 3 X).map X.subtype) ⊆
      (Subgroup.zpowers b : Set G) := by
  intro x hx
  by_contra hxb
  have hd := h.data83
  have hA81 : Nat.card A = 81 := hd.card_eq
  have hAe := h.mem_partTwoF.1
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have h3 : ∀ y ∈ A, y ^ 3 = 1 := hAe.2
  have ha := h.a_mem_normalizer
  have hcL := Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt
  have hcy : ∀ y ∈ L, c * y = y * c := fun y hy =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hcL hy)).symm
  obtain ⟨hbΓ, -, hLbd⟩ := partner_data h hb hrel
  have hbA : b ∈ A := hbΓ.1
  have hb1 : b ≠ 1 := hbΓ.2.1
  have hX := hrel.2.2.1
  have hAN : A ≤ Subgroup.normalizer (X : Set G) := le_normalizer_of_partner h45 h hb hrel
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
  set K := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) with hKdef
  have hKX : K ≤ X := by
    have h1 := hrel.2.2.2.1
    rwa [hLbd] at h1
  have hKL : K ≤ L := (Subgroup.map_subtype_le _).trans inf_le_left
  have hθ := theta_inf_le_theta_of_noThetaNormal hKL hKX (noThetaNormal_of_data83 hd)
  have hcC : c ∉ C := by
    intro hc
    have hc' : c ∈ Late.sectionCentralizer A X ((aschbacherSolvableCore 3 X).map X.subtype) := by
      rw [hsec]
      exact hc
    exact Item812Res7.ne_one_of_partner h hb hrel (hAN h.mem_A)
      (Item812Res8.thetaQuotMulAut_eq_one_of_mem_sectionCentralizer hc' (hAN h.mem_A))
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

theorem hyp81_of_partner' (h45 : Sec4.Item4_5) (h418 : Item418Theta) (hF : KF84FieldStd)
    (hKB : KF83KBarTwo) (hInd : KF83Indep) (hG2 : KF83IndepGTwo) {A : Subgroup G} {c : G}
    {L : Subgroup G} {a d : G} {n : ℕ} (h : Sec8Std G A c L a d n) {b : G}
    (hb : b ∈ Subgroup.closure ({c, d} : Set G)) {X : Subgroup G} (hrel : PairRel A c L b X) :
    Hyp81 G A b X a := by
  obtain ⟨hbΓ, -, hLb⟩ := partner_data h hb hrel
  have hX := hrel.2.2.1
  have hA81 := h.data83.card_eq
  obtain ⟨T, hT, hT1, hTK⟩ := exists_invariant_two_of_sec8Std hKB h
  have hKX : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ≤ X := by
    have h1 := hrel.2.2.2.1
    rwa [hLb] at h1
  exact
  { toPartTwoStanding := h.toPartTwoStanding
    mem_partTwoF := h.mem_partTwoF
    mem_A := hbΓ.1
    ne_one := hbΓ.2.1
    mem_thetaComponentsAt := hX
    sectionCentralizer_eq := subset_antisymm
      (sectionCentralizer_subset_of_partner h45 hKB hG2 h hb hrel)
      (zpowers_subset_sectionCentralizer hbΓ.1 (Sec6.le_centralizer_of_mem_thetaComponentsAt hX))
    a_mem := h.a_mem
    a_ne_one := h.a_ne_one
    inducesStdKind := (kinds_of_partner h418 hF h hb hrel).1
    exists_invariant_two := fun _ => ⟨Subgroup.closure ({c, a, d} : Set G),
      ⟨isElemAbelian_of_le h.mem_partTwoF.1 (closure_le_of_sec8Std h),
        card_closure_of_sec8Std hInd h, T, hT1,
        (isPiSubgroup_piOf_iff Nat.prime_two T).mp hT.2.1, hT.2.2⟩,
      closure_le_of_sec8Std h, T, ⟨hTK.trans hKX, hT.2⟩, hT1⟩
    partTwoE_eq := fun h27 => absurd (h27.symm.trans hA81) (by norm_num) }

theorem isList82Two_of_partner (hL : Item82TwoList) (h45 : Sec4.Item4_5) (h418 : Item418Theta)
    (hF : KF84FieldStd) (hKB : KF83KBarTwo) (hInd : KF83Indep) (hG2 : KF83IndepGTwo)
    {A : Subgroup G} {c : G} {L : Subgroup G} {a d : G} {n : ℕ} (h : Sec8Std G A c L a d n)
    {b : G} (hb : b ∈ Subgroup.closure ({c, d} : Set G)) {X : Subgroup G}
    (hrel : PairRel A c L b X) : IsList82Two (X ⧸ aschbacherSolvableCore 3 X) :=
  hL G A b X a (hyp81_of_partner' h45 h418 hF hKB hInd hG2 h hb hrel) h.data83.card_eq

theorem residual_eq_of_isQuasisimple {A : Subgroup G} {c : G} {L : Subgroup G} {a d : G}
    {n : ℕ} (h : Sec8Std G A c L a d n) {b : G} (hb : b ∈ Subgroup.closure ({c, d} : Set G))
    {X : Subgroup G} (hrel : PairRel A c L b X)
    (hq : IsQuasisimple (imageModTheta X
      (inSubgroup perfectResidual (X ⊓ Subgroup.centralizer ({c} : Set G))))) :
    inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) =
      inSubgroup perfectResidual (X ⊓ Subgroup.centralizer ({c} : Set G)) := by
  obtain ⟨hbΓ, -, -⟩ := partner_data h hb hrel
  have hX : X ∈ thetaComponentsAt 3 b := hrel.2.2.1
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    (PartOne.mem_thetaComponentsAt_iff.mp h.mem_thetaComponentsAt).1
  obtain ⟨hKmem, -, hK1⟩ := Item87Proof.residual_of_isGammaIndex h.mem_thetaComponentsAt hbΓ
  set K := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) with hKdef
  set M := inSubgroup perfectResidual (X ⊓ Subgroup.centralizer ({c} : Set G)) with hMdef
  have hKL : K ≤ L := (Item87Proof.residual_le _).trans inf_le_left
  have hKX : K ≤ X := hrel.2.2.2.1
  have hMX : M ≤ X := (Item87Proof.residual_le _).trans inf_le_left
  have hKM : K ≤ M := KFacts.le_inSubgroup_perfectResidual (Item87Proof.isPerfect_residual _)
    (le_inf hKX (hKL.trans hLc))
  have hMq := Item87Proof.isQuasisimple_quot_of_imageModTheta hMX hq
  have hMmem := Item87Proof.mem_thetaComponentsIn_residual hX hMq
  rw [inf_comm] at hMmem
  exact Sec6.eq_of_mem_thetaComponentsIn_of_le hKmem hMmem (Item87Proof.isPerfect_residual _)
    hK1 le_rfl hKM

end Center

theorem two_pow_three_mul_mod_three' {m : ℕ} (hm : Odd m) : 2 ^ (3 * m) % 3 = 2 := by
  obtain ⟨k, rfl⟩ := hm
  rw [show 3 * (2 * k + 1) = 6 * k + 3 by ring, pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem nonUnitary_cases {X : Type} [Group X] (h : IsList82Two X)
    (hU : ∀ k : ℕ, ¬ IsUnitaryTwo X k) :
    ∃ m : ℕ, Odd m ∧ (IsoTrialityD4 X m ∨
      (∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 3 * m ∧ Sec4.IsoGTwo X q) ∨
      IsGammaTypeRee X m ∨ Nonempty (X ≃* projSp 2 (GaloisField 2 (3 * m)))) := by
  obtain ⟨m, hm, hD | hG | hR | hSp | hPSU | hSL⟩ := h
  · exact ⟨m, hm, Or.inl hD⟩
  · exact ⟨m, hm, Or.inr (Or.inl hG)⟩
  · exact ⟨m, hm, Or.inr (Or.inr (Or.inl hR))⟩
  · exact ⟨m, hm, Or.inr (Or.inr (Or.inr hSp))⟩
  · exact (hU (3 * m) (Or.inl hPSU)).elim
  · obtain ⟨K, _, _, ⟨-, h1, -⟩ | ⟨hK, -, he⟩⟩ := hSL
    · rw [two_pow_three_mul_mod_three' hm] at h1
      exact absurd h1 (by norm_num)
    · exact (hU (3 * m) (Or.inr ⟨K, inferInstance, inferInstance, hK, he⟩)).elim

end CFSG.RankThree.PartTwo.Sec8.Item8KFacts3
