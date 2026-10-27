module

public import CFSG.RankThree.PartTwo.Sec8.HeringBMemDefs
public import CFSG.RankThree.PartTwo.Sec8.HeringBMemLift
public import CFSG.RankThree.PartTwo.Sec8.HeringBMemQ8
public import CFSG.RankThree.PartTwo.Sec8.Item812Res11ProofBMemY
public import CFSG.RankThree.PartTwo.Sec8.Item812Res12ProofIrred
import CFSG.RankThree.PartTwo.Sec8.HeringU38MFinal
import CFSG.RankThree.PartTwo.Sec8.Item812Res6ProofPaExp
import CFSG.RankThree.PartTwo.Sec11.Item113
import CFSG.RankThree.PartOne.N143.SectionGroup
import CFSG.RankThree.PartTwo.Sec6.Item65Tools
import CFSG.RankThree.PartTwo.Sec6.Item612
import CFSG.RankThree.PartTwo.KFacts.K72LStar

public section

namespace CFSG.RankThree.PartTwo.Sec8.HeringBMem

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec8
open CFSG.RankThree.PartTwo.Sec4 (InducesOuterTheta thetaQuotMulAut compAction)
open scoped commutatorElement

section Norm

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_imageModTheta {Y H : Subgroup G} {s : Y}
    (hs : (s : G) ∈ Subgroup.normalizer (H : Set G)) :
    QuotientGroup.mk' (aschbacherSolvableCore 3 Y) s ∈
      Subgroup.normalizer ((imageModTheta Y H : Subgroup (Y ⧸ aschbacherSolvableCore 3 Y)) :
        Set (Y ⧸ aschbacherSolvableCore 3 Y)) :=
  Subgroup.le_normalizer_map (QuotientGroup.mk' (aschbacherSolvableCore 3 Y))
    ⟨s, Item812Res12.mem_normalizer_subgroupOf hs, rfl⟩

end Norm

section Data

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a b : G}
  {X Y : Subgroup G} {n : ℕ}

theorem dataU (h84 : Pair84A) (h : Sec8Final G A c L a b X Y n) (hbY : b ∉ Y) :
    ∃ (yb zb : G) (hyb : yb ∈ A ⊓ Y), zb ∈ Subgroup.zpowers a ∧ zb * yb = b ∧
      ∃ S H : Subgroup (Y ⧸ aschbacherSolvableCore 3 Y),
        S ≤ imageModTheta Y (A ⊓ Y) ∧ Nat.card S = 9 ∧
        S ≤ imageModTheta Y (sec8B A X ⊓ (A ⊓ Y)) ∧
        QuotientGroup.mk' (aschbacherSolvableCore 3 Y) ⟨yb, hyb.2⟩ ∉ S ∧
        Group.IsPerfect H ∧ S ≤ H ∧
        H ≤ Subgroup.centralizer
          ({QuotientGroup.mk' (aschbacherSolvableCore 3 Y) ⟨yb, hyb.2⟩} :
            Set (Y ⧸ aschbacherSolvableCore 3 Y)) := by
  classical
  have hAab := h.mem_partTwoF.1
  have hAc : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hAab.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have h3A : ∀ u ∈ A, u ^ 3 = 1 := hAab.2
  have haA : a ∈ A := h.a_mem
  have ha3 : a ^ 3 = 1 := h3A a haA
  have hbA : b ∈ A := h.isGammaIndex.1
  have hb1 : b ≠ 1 := h.isGammaIndex.2.1
  have hXb : X ∈ thetaComponentsAt 3 b := h.pairRel.2.2.1
  have h3G := h.toTheoremFourHyp.localRank_three.le
  have haX : InducesOuterTheta a X := by
    rcases h84 G A c L a b X n h.toSec8Pair with hk | hk
    · exact KFacts.InducesStdKind.inducesOuterTheta X hk (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta X hk (by decide)
  obtain ⟨S₀, hS₀A, hS₀9, -, -, -, hBS⟩ := Item812Res2.sec8B_structure_of_projSp h3G
    h.mem_partTwoF h.card_eq hbA hb1 hXb h.item89_X haA haX
  have hS0card : Nat.card (S₀.map X.subtype) = 9 := by
    rw [Subgroup.card_map_of_injective X.subtype_injective, hS₀9]
  have hS0B : S₀.map X.subtype ≤ sec8B A X := by rw [hBS]; exact le_sup_right
  have hbB : b ∈ sec8B A X := by rw [hBS]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers b)
  have hJ : S₀.map X.subtype ≤ sec8J X a :=
    Item812Res11.map_le_perfectResidual hAab haA haX h.item89_X hS₀A
  have hJY : sec8J X a ≤ Y := le_sup_right.trans h.le_Y
  have hBY9 : Nat.card (sec8B A X ⊓ Y : Subgroup G) ≤ 9 := by
    have hdvd : Nat.card (sec8B A X ⊓ Y : Subgroup G) ∣ 3 ^ 3 := by
      rw [show (3 : ℕ) ^ 3 = Nat.card (sec8B A X) by rw [Item812Res8.card_sec8B h]; norm_num]
      exact Subgroup.card_dvd_of_le inf_le_left
    have hne : Nat.card (sec8B A X ⊓ Y : Subgroup G) ≠ 27 := by
      intro h27
      have heq : sec8B A X ⊓ Y = sec8B A X :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h27, Item812Res8.card_sec8B h])
      exact hbY (heq.symm ▸ hbB : b ∈ sec8B A X ⊓ Y).2
    obtain ⟨i, hi, hieq⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    rw [hieq] at hne ⊢
    interval_cases i <;> simp_all
  have hS0eq : S₀.map X.subtype = sec8B A X ⊓ Y :=
    Subgroup.eq_of_le_of_card_ge (le_inf hS0B (hJ.trans hJY)) (by rw [hS0card]; exact hBY9)
  have hS0A : S₀.map X.subtype ≤ A ⊓ Y := hS0eq ▸ inf_le_inf_right Y inf_le_left
  have hAeq := Item812Res6.zpowers_sup_inf_eq h
  have hset := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (Subgroup.zpowers a) (A ⊓ Y)
    (fun x hx y hy => hAc x ((Subgroup.zpowers_le).mpr haA hx) y hy.1)).2
  have hdec : ∀ g ∈ A, ∃ z ∈ Subgroup.zpowers a, ∃ y ∈ A ⊓ Y, z * y = g := by
    intro g hg
    have hg' : g ∈ ((Subgroup.zpowers a ⊔ A ⊓ Y : Subgroup G) : Set G) := by
      rw [hAeq]
      exact hg
    rw [hset] at hg'
    obtain ⟨z, hz, y, hy, hzy⟩ := hg'
    exact ⟨z, hz, y, hy, hzy⟩
  obtain ⟨zb, hzb, yb, hyb, hbe⟩ := hdec b hbA
  have hzbA : zb ∈ A := (Subgroup.zpowers_le).mpr haA hzb
  set φ := QuotientGroup.mk' (aschbacherSolvableCore 3 Y) with hφ
  refine ⟨yb, zb, hyb, hzb, hbe, imageModTheta Y (S₀.map X.subtype),
    imageModTheta Y (sec8J X a), Item812Res11.imageModTheta_mono hS0A, ?_,
    Item812Res11.imageModTheta_mono (le_inf hS0B hS0A), ?_, ?_,
    Item812Res11.imageModTheta_mono hJ, ?_⟩
  · rw [Item812Res11.card_imageModTheta_of_pow (hS0A.trans inf_le_right)
      (fun x hx => h3A x (hS0A hx).1), hS0card]
  ·
    intro hmem
    obtain ⟨s, hs, hse⟩ := hmem
    have hsA : (s : G) ∈ A := (hS0A (Subgroup.mem_subgroupOf.mp hs)).1
    have hys : (s : G) = yb := by
      refine Item812Res11.eq_of_mk_eq s.2 hyb.2 (h3A _ (A.mul_mem (A.inv_mem hsA) hyb.1)) ?_
      rw [← hse]
    have hybS : yb ∈ S₀.map X.subtype := by
      rw [← hys]
      exact Subgroup.mem_subgroupOf.mp hs
    have hybX : yb ∈ X := (Subgroup.map_subtype_le _) hybS
    have hzb1 : zb = 1 := by
      refine Item812Res11.eq_one_of_mem_zpowers_of_mem_sup ha3 haX hzb ?_
      have e : zb = b * yb⁻¹ := by rw [← hbe, mul_inv_cancel_right]
      rw [e]
      exact Subgroup.mul_mem _ hbB.2 (Subgroup.mem_sup_left (X.inv_mem hybX))
    apply hbY
    rw [← hbe, hzb1, one_mul]
    exact hyb.2
  · exact Item812Res11.isPerfect_imageModTheta hJY (Item87Proof.isPerfect_residual _)
  ·
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    have hxXa : (x : G) ∈ X ⊓ Subgroup.centralizer ({a} : Set G) :=
      (Subgroup.map_subtype_le _) (Subgroup.mem_subgroupOf.mp hx)
    have hxb : (x : G) * b = b * x := Subgroup.mem_centralizer_singleton_iff.mp
      (le_centralizer_of_mem_thetaComponentsAt_three hXb hxXa.1)
    have hxz : (x : G) * zb = zb * x := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hzb
      exact (Commute.zpow_right
        (Subgroup.mem_centralizer_singleton_iff.mp hxXa.2 : (x : G) * a = a * x) k)
    have e : yb = zb⁻¹ * b := by rw [← hbe, inv_mul_cancel_left]
    apply Subtype.ext
    show (x : G) * yb = yb * x
    rw [e]
    have h1 : Commute (x : G) zb := hxz
    have h2 : Commute (x : G) b := hxb
    exact (h1.inv_right.mul_right h2).eq

theorem card_imageModTheta_of_isPGroup_two {Y H : Subgroup G} (hHY : H ≤ Y) (hH : IsPGroup 2 H)
    (hθodd : Odd (Nat.card ((aschbacherSolvableCore 3 Y).map Y.subtype))) :
    Nat.card (imageModTheta Y H) = Nat.card H := by
  rw [imageModTheta, CFSG.RankThree.PartOne.N143.card_map_of_disjoint_ker]
  · exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHY).toEquiv
  · rw [Subgroup.disjoint_def]
    intro x hx hxk
    have hxθ : x ∈ aschbacherSolvableCore 3 Y := by
      rw [MonoidHom.mem_ker, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hxk
      exact hxk
    obtain ⟨k, hk⟩ := hH ⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩
    have hxk' : (x : G) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact Subtype.ext (eq_one_of_mem_theta_of_two_pow hθodd ⟨x, hxθ, rfl⟩ hxk')

theorem dataV (h45 : Sec4.Item4_5) (h : Sec8Final G A c L a b X Y n)
    (hU : IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) 3)
    {yb zb : G} (hyb : yb ∈ A ⊓ Y) (hzb : zb ∈ Subgroup.zpowers a) (hbe : zb * yb = b) :
    ∃ (yc zc : G) (hyc : yc ∈ A ⊓ Y), zc ∈ Subgroup.zpowers a ∧ zc * yc = c ∧
      QuotientGroup.mk' (aschbacherSolvableCore 3 Y) ⟨yc, hyc.2⟩ ≠ 1 ∧
      ∃ Q : Subgroup (Y ⧸ aschbacherSolvableCore 3 Y),
        Q ≤ Subgroup.centralizer
          ({QuotientGroup.mk' (aschbacherSolvableCore 3 Y) ⟨yc, hyc.2⟩} :
            Set (Y ⧸ aschbacherSolvableCore 3 Y)) ∧
        Nat.card Q = 8 ∧
        (∀ q ∈ Q, QuotientGroup.mk' (aschbacherSolvableCore 3 Y) ⟨yb, hyb.2⟩ * q *
          (QuotientGroup.mk' (aschbacherSolvableCore 3 Y) ⟨yb, hyb.2⟩)⁻¹ ∈ Q) ∧
        ⁅Q, Subgroup.zpowers (QuotientGroup.mk' (aschbacherSolvableCore 3 Y) ⟨yb, hyb.2⟩)⁆ = Q := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hG := h.toTheoremFourHyp
  have hAab := h.mem_partTwoF.1
  have hAc : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hAab.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have haA : a ∈ A := h.a_mem
  have hbA : b ∈ A := h.isGammaIndex.1
  have hcA : c ∈ A := h.mem_A
  have hc1 : c ≠ 1 := h.ne_one
  have ha3 : a ^ 3 = 1 := hAab.2 a haA
  have hb3 : b ^ 3 = 1 := hAab.2 b hbA
  have hc3 : c ^ 3 = 1 := hAab.2 c hcA
  have hAp : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hAab.2 g g.2)⟩
  have hAcC : A ≤ Subgroup.centralizer ({c} : Set G) := fun u hu =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hAc u hu c hcA)
  have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
    Sec11.le_normalizer_of_isPGroup_of_le_centralizer h45 hG hc3 hc1 hAp hAcC L
      h.mem_thetaComponentsAt
  have hcN : c ∈ Subgroup.normalizer (L : Set G) := hAL hcA
  obtain ⟨haN, hbN, -, -, hab, haL, hCa, hu4, hβ1, h7, hθodd⟩ :=
    u38_pair_data h45 h.toSec8Pair hU
  have hac : a * c = c * a := hAc a haA c hcA
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    le_centralizer_of_mem_thetaComponentsAt_three h.mem_thetaComponentsAt
  have hcc : compAction L ⟨c, hcN⟩ = 1 := by
    refine MulEquiv.ext fun x => Subtype.ext ?_
    have := Subgroup.mem_centralizer_singleton_iff.mp (hLc x.2)
    show c * (x : G) * c⁻¹ = (x : G)
    rw [← this, mul_inv_cancel_right]
  have hcL : thetaQuotMulAut L (compAction L ⟨c, hcN⟩) = 1 := by rw [hcc, map_one]
  have hBA : Subgroup.closure ({b, c} : Set G) ≤ A := by
    rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    exacts [hbA, hcA]
  obtain ⟨T, hTα, hT8, hTβ, hTc⟩ := HeringU38M.u38SylModel_holds
    (L ⧸ aschbacherSolvableCore 3 L) hU
    (thetaQuotMulAut L (compAction L ⟨a, haN⟩)) (thetaQuotMulAut L (compAction L ⟨b, hbN⟩))
    (u38_pow_eq_one haN ha3) (u38_pow_eq_one hbN hb3) (u38_mul_comm haN hbN hab)
    (by obtain ⟨hx, hnot⟩ := haL; exact fun hin => hnot hin)
    (by rw [← barCentralizer_eq_u38Fix haN]; exact hCa)
    (by
      obtain ⟨u, hu, h4, h2⟩ := hu4
      exact ⟨u, by rwa [barCentralizer_eq_u38Fix haN] at hu, h4, h2⟩)
    hβ1 (by rw [← barCentralizer_eq_u38Fix hbN]; exact h7)
  obtain ⟨Q, hQC, hQ2, hQ8, hBQ, hQb⟩ := exists_B0_syl haN hbN hcN ha3 hb3 hc3 hab hac hcL
    (hAp.to_le hBA) hθodd T
    (by rw [barCentralizer_eq_u38Fix haN]; exact hTα) hT8 hCa hTβ hTc
  have hQa : Q ≤ Subgroup.centralizer ({a} : Set G) := hQC.trans inf_le_right
  have hIdef : sec8I L a = Subgroup.closure
      {y | y ∈ L ⊓ Subgroup.centralizer {a} ∧ ∃ k : ℕ, y ^ 2 ^ k = 1} := by
    simp only [sec8I, hU, ↓reduceIte]
  have hQI : Q ≤ sec8I L a := by
    intro q hq
    obtain ⟨k, hk⟩ := hQ2 ⟨q, hq⟩
    rw [hIdef]
    exact Subgroup.subset_closure ⟨hQC hq, k, by simpa using congrArg Subtype.val hk⟩
  have hQY : Q ≤ Y := hQI.trans (le_sup_left.trans h.le_Y)
  have hAH : A ≤ Subgroup.centralizer ({a} : Set G) :=
    Item87Proof.le_centralizer_of_isElemAbelian hAab haA
  have hAfix : ∀ Z ∈ thetaComponentsAt 3 a, A ≤ Subgroup.normalizer (Z : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsIn_of_item4_5 h45
      (hG.sectionFourHyp (Sec6.centralizer_ne_top_of_ne_one hG h.a_ne_one)) hAH hAab
      ⟨4, by norm_num, by rw [h.card_eq]; norm_num⟩
  have hθ3 : ¬ 3 ∣ Nat.card ((aschbacherSolvableCore 3 Y).map Y.subtype) := by
    rw [Subgroup.card_map_of_injective Y.subtype_injective]
    exact KFacts.not_three_dvd_card_aschbacherSolvableCore Y
  have hθYodd : Odd (Nat.card ((aschbacherSolvableCore 3 Y).map Y.subtype)) :=
    odd_card_of_le_normalizer hG.localRank_three.le hAab h.card_eq hθ3
      ((hAfix Y h.mem_thetaComponentsAt_Y).trans (KFacts.normalizer_le_normalizer_theta Y))
  have hAeq := Item812Res6.zpowers_sup_inf_eq h
  have hset := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (Subgroup.zpowers a) (A ⊓ Y)
    (fun x hx y hy => hAc x ((Subgroup.zpowers_le).mpr haA hx) y hy.1)).2
  have hdec : ∀ g ∈ A, ∃ z ∈ Subgroup.zpowers a, ∃ y ∈ A ⊓ Y, z * y = g := by
    intro g hg
    have hg' : g ∈ ((Subgroup.zpowers a ⊔ A ⊓ Y : Subgroup G) : Set G) := by
      rw [hAeq]
      exact hg
    rw [hset] at hg'
    obtain ⟨z, hz, y, hy, hzy⟩ := hg'
    exact ⟨z, hz, y, hy, hzy⟩
  obtain ⟨zc, hzc, yc, hyc, hce⟩ := hdec c hcA
  have hQz : ∀ z ∈ Subgroup.zpowers a, ∀ x ∈ Q, x * z = z * x := by
    intro z hz x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact (Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp (hQa hx) :
      x * a = a * x) k)
  have hybQ : yb ∈ Subgroup.normalizer (Q : Set G) := by
    have hbQN : b ∈ Subgroup.normalizer (Q : Set G) :=
      hBQ (Subgroup.subset_closure (by simp))
    have hzbN : zb⁻¹ ∈ Subgroup.normalizer (Q : Set G) := by
      refine Subgroup.mem_normalizer_fintype fun x hx => ?_
      have := hQz zb⁻¹ (Subgroup.inv_mem _ hzb) x hx
      have e : zb⁻¹ * x * zb⁻¹⁻¹ = x := by rw [← this]; group
      rw [e]
      exact hx
    have e : yb = zb⁻¹ * b := by rw [← hbe, inv_mul_cancel_left]
    rw [e]
    exact Subgroup.mul_mem _ hzbN hbQN
  refine ⟨yc, zc, hyc, hzc, hce, ?_, imageModTheta Y Q, ?_, ?_, ?_, ?_⟩
  ·
    intro h1
    have hyc1 : yc = 1 := by
      refine Item812Res6.eq_one_of_mem_theta_of_pow (k := 1)
        ⟨⟨yc, hyc.2⟩, ?_, rfl⟩ ?_
      · rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      · rw [pow_one]
        exact hAab.2 yc hyc.1
    have hcz : c = zc := by rw [← hce, hyc1, mul_one]
    apply hc1
    rw [hcz]
    refine Item812Res11.eq_one_of_mem_zpowers_of_mem_sup ha3 haL hzc ?_
    rw [← hcz]
    exact Subgroup.mem_sup_right (Sec6.mem_thetaQuotCentralizer_of_mem_thetaComponentsAt
      h.mem_thetaComponentsAt)
  ·
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    have hxQ : (x : G) ∈ Q := Subgroup.mem_subgroupOf.mp hx
    have hxc : (x : G) * c = c * x := Subgroup.mem_centralizer_singleton_iff.mp
      (le_centralizer_of_mem_thetaComponentsAt_three h.mem_thetaComponentsAt (hQC hxQ).1)
    have hxz : (x : G) * zc = zc * x := hQz zc hzc x hxQ
    have e : yc = zc⁻¹ * c := by rw [← hce, inv_mul_cancel_left]
    apply Subtype.ext
    show (x : G) * yc = yc * x
    rw [e]
    have h1 : Commute (x : G) zc := hxz
    have h2 : Commute (x : G) c := hxc
    exact (h1.inv_right.mul_right h2).eq
  · rw [card_imageModTheta_of_isPGroup_two hQY hQ2 hθYodd, hQ8]
  ·
    rintro _ ⟨x, hx, rfl⟩
    have hxQ : (x : G) ∈ Q := Subgroup.mem_subgroupOf.mp hx
    have hyx : yb * x * yb⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hybQ _).mp hxQ
    refine ⟨⟨yb, hyb.2⟩ * x * ⟨yb, hyb.2⟩⁻¹, Subgroup.mem_subgroupOf.mpr hyx, ?_⟩
    simp only [map_mul, map_inv]
  ·
    have hzbA : zb ∈ A := (Subgroup.zpowers_le).mpr haA hzb
    have hzyc : Commute zb yb := hAc zb hzbA yb hyb.1
    have hcom1 : ⁅Q, Subgroup.zpowers b⁆ ≤ ⁅Q, Subgroup.zpowers yb⁆ := by
      rw [Subgroup.commutator_le]
      intro q hq g hg
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      have hbk : b ^ k = zb ^ k * yb ^ k := by rw [← hbe, hzyc.mul_zpow]
      have hqz : q * zb ^ k = zb ^ k * q := hQz (zb ^ k) (Subgroup.zpow_mem _ hzb k) q hq
      have hzq : Commute (zb ^ k) q := (show Commute q (zb ^ k) from hqz).symm
      have hzy : Commute (zb ^ k) (yb ^ k) := hzyc.zpow_zpow k k
      have e : ⁅q, zb ^ k * yb ^ k⁆ = ⁅q, yb ^ k⁆ := by
        have h1 : q * (zb ^ k * yb ^ k) * q⁻¹ * (zb ^ k * yb ^ k)⁻¹ =
            zb ^ k * (q * yb ^ k * q⁻¹ * (yb ^ k)⁻¹) * (zb ^ k)⁻¹ := by
          rw [← mul_assoc q (zb ^ k) (yb ^ k), hqz]
          group
        have h2 : Commute (zb ^ k) (q * yb ^ k * q⁻¹ * (yb ^ k)⁻¹) :=
          (((hzq.mul_right hzy).mul_right hzq.inv_right).mul_right hzy.inv_right)
        rw [commutatorElement_def, commutatorElement_def, h1, h2.eq, mul_inv_cancel_right]
      rw [hbk, e]
      exact Subgroup.commutator_mem_commutator hq (Subgroup.zpow_mem _ (Subgroup.mem_zpowers yb) k)
    have hcom2 : ⁅Q, Subgroup.zpowers yb⁆ ≤ Q := by
      rw [Subgroup.commutator_le]
      intro x hx y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [commutatorElement_def]
      have hbk : yb ^ k ∈ Subgroup.normalizer (Q : Set G) := Subgroup.zpow_mem _ hybQ k
      have h1 : yb ^ k * x⁻¹ * (yb ^ k)⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp hbk _).mp (Subgroup.inv_mem _ hx)
      have : x * yb ^ k * x⁻¹ * (yb ^ k)⁻¹ = x * (yb ^ k * x⁻¹ * (yb ^ k)⁻¹) := by group
      rw [this]
      exact Subgroup.mul_mem _ hx h1
    have hQeq : ⁅Q, Subgroup.zpowers yb⁆ = Q := le_antisymm hcom2 (hQb.ge.trans hcom1)
    set π := QuotientGroup.mk' (aschbacherSolvableCore 3 Y) with hπ
    have hQ'comm : ⁅Q.subgroupOf Y, Subgroup.zpowers (⟨yb, hyb.2⟩ : Y)⁆ = Q.subgroupOf Y := by
      apply Subgroup.map_injective Y.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hQY, MonoidHom.map_zpowers]
      exact hQeq
    show ⁅(Q.subgroupOf Y).map π, Subgroup.zpowers (π ⟨yb, hyb.2⟩)⁆ = (Q.subgroupOf Y).map π
    rw [← MonoidHom.map_zpowers, ← Subgroup.map_commutator, hQ'comm]

end Data

section Lifts

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a b : G}
  {X Y : Subgroup G} {n : ℕ}

theorem mem_normalizer_zpowers_of_commute {g b : G} (h : g * b = b * g) :
    g ∈ Subgroup.normalizer (Subgroup.zpowers b : Set G) :=
  Subgroup.mem_normalizer_fintype fun x hx => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have : g * b ^ k * g⁻¹ = b ^ k := by
      have h1 : g * b ^ k = b ^ k * g := (Commute.zpow_right (show Commute g b from h) k).eq
      rw [h1]
      group
    rw [this]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers b) k

theorem mem_normalizer_of_centralizes_u (h : Sec8Final G A c L a b X Y n) {yb zb : G}
    (hyb : yb ∈ A ⊓ Y) (hzb : zb ∈ Subgroup.zpowers a) (hbe : zb * yb = b)
    {s : Y ⧸ aschbacherSolvableCore 3 Y}
    (hs : s ∈ Subgroup.normalizer
      ((imageModTheta Y (A ⊓ Y) : Subgroup (Y ⧸ aschbacherSolvableCore 3 Y)) :
        Set (Y ⧸ aschbacherSolvableCore 3 Y)))
    (hsu : s * QuotientGroup.mk' (aschbacherSolvableCore 3 Y) ⟨yb, hyb.2⟩ =
      QuotientGroup.mk' (aschbacherSolvableCore 3 Y) ⟨yb, hyb.2⟩ * s) :
    s ∈ Subgroup.normalizer
      ((imageModTheta Y (sec8B A X ⊓ (A ⊓ Y)) : Subgroup (Y ⧸ aschbacherSolvableCore 3 Y)) :
        Set (Y ⧸ aschbacherSolvableCore 3 Y)) := by
  classical
  have hAab := h.mem_partTwoF.1
  have hEab : CFSG.Assembly.IsElemAbelian 3 (A ⊓ Y : Subgroup G) :=
    Item812Res4.isElemAbelian_of_le hAab inf_le_left
  have hEp : IsPGroup 3 ((A ⊓ Y : Subgroup G).subgroupOf Y) :=
    (Item812Res4.isPGroup_of_isElemAbelian hEab).comap_subtype
  obtain ⟨t, htN, hts⟩ := exists_lift_of_mem_normalizer
    (Item812Res4.not_dvd_card_core Y) hEp hs
  have htE : (t : G) ∈ Subgroup.normalizer ((A ⊓ Y : Subgroup G) : Set G) :=
    Item812Res12.mem_normalizer_of_subgroupOf inf_le_right htN
  have hta : (t : G) * a = a * t := Subgroup.mem_centralizer_singleton_iff.mp
    (le_centralizer_of_mem_thetaComponentsAt_three h.mem_thetaComponentsAt_Y t.2)
  have htz : (t : G) * zb = zb * t := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hzb
    exact Commute.zpow_right (show Commute (t : G) a from hta) k
  have htyb : (t : G) * yb = yb * t := by
    have hxY : (t : G) * yb * (t : G)⁻¹ ∈ Y := Y.mul_mem (Y.mul_mem t.2 hyb.2) (Y.inv_mem t.2)
    have hxE : (t : G) * yb * (t : G)⁻¹ ∈ A ⊓ Y := (Subgroup.mem_normalizer_iff.mp htE yb).mp hyb
    have hxy3 : (((t : G) * yb * (t : G)⁻¹)⁻¹ * yb) ^ 3 = 1 :=
      hAab.2 _ (A.mul_mem (A.inv_mem hxE.1) hyb.1)
    have hmk : QuotientGroup.mk' (aschbacherSolvableCore 3 Y)
        ⟨(t : G) * yb * (t : G)⁻¹, hxY⟩ =
        QuotientGroup.mk' (aschbacherSolvableCore 3 Y) ⟨yb, hyb.2⟩ := by
      have : (⟨(t : G) * yb * (t : G)⁻¹, hxY⟩ : Y) = t * ⟨yb, hyb.2⟩ * t⁻¹ := rfl
      rw [this, map_mul, map_mul, map_inv, hts, hsu, mul_inv_cancel_right]
    have h1 := Item812Res11.eq_of_mk_eq hxY hyb.2 hxy3 hmk
    calc (t : G) * yb = ((t : G) * yb * (t : G)⁻¹) * t := by group
      _ = yb * t := by rw [h1]
  have htb : (t : G) * b = b * t := by
    rw [← hbe]
    exact (Commute.mul_right (show Commute (t : G) zb from htz)
      (show Commute (t : G) yb from htyb)).eq
  have htX : (t : G) ∈ Subgroup.normalizer (X : Set G) :=
    fin812XNormal G A c L a b X Y n h (mem_normalizer_zpowers_of_commute htb)
  have htA : (t : G) ∈ Subgroup.normalizer (A : Set G) := by
    have := mem_normalizer_zpowers_sup htE hta
    rwa [Item812Res6.zpowers_sup_inf_eq h] at this
  have htB := mem_normalizer_sec8B htA htX
  have htBE := mem_normalizer_inf htB htE
  rw [← hts]
  exact mem_normalizer_imageModTheta htBE

theorem mem_normalizer_of_centralizes_v (h45 : Sec4.Item4_5) (h : Sec8Final G A c L a b X Y n)
    {yc zc : G} (hyc : yc ∈ A ⊓ Y) (hzc : zc ∈ Subgroup.zpowers a) (hce : zc * yc = c)
    {g : Y ⧸ aschbacherSolvableCore 3 Y}
    (hg : g ∈ Subgroup.normalizer
      ((imageModTheta Y (A ⊓ Y) : Subgroup (Y ⧸ aschbacherSolvableCore 3 Y)) :
        Set (Y ⧸ aschbacherSolvableCore 3 Y)))
    (hgv : g * QuotientGroup.mk' (aschbacherSolvableCore 3 Y) ⟨yc, hyc.2⟩ =
      QuotientGroup.mk' (aschbacherSolvableCore 3 Y) ⟨yc, hyc.2⟩ * g)
    (hg3 : ∃ k : ℕ, g ^ 3 ^ k = 1) :
    g ∈ Subgroup.normalizer
      ((imageModTheta Y (sec8B A X ⊓ (A ⊓ Y)) : Subgroup (Y ⧸ aschbacherSolvableCore 3 Y)) :
        Set (Y ⧸ aschbacherSolvableCore 3 Y)) := by
  classical
  have hG := h.toTheoremFourHyp
  have hAab := h.mem_partTwoF.1
  have hEab : CFSG.Assembly.IsElemAbelian 3 (A ⊓ Y : Subgroup G) :=
    Item812Res4.isElemAbelian_of_le hAab inf_le_left
  have hEp : IsPGroup 3 ((A ⊓ Y : Subgroup G).subgroupOf Y) :=
    (Item812Res4.isPGroup_of_isElemAbelian hEab).comap_subtype
  obtain ⟨t₀, ht₀N, ht₀s⟩ := exists_lift_of_mem_normalizer
    (Item812Res4.not_dvd_card_core Y) hEp hg
  obtain ⟨k, hk⟩ := hg3
  obtain ⟨p, ⟨e, hpe⟩, hpφ, u, hpu⟩ := exists_three_pow_lift
    (QuotientGroup.mk' (aschbacherSolvableCore 3 Y)) (x := t₀) (k := k)
    (by rw [ht₀s]; exact hk)
  have htN : p ∈ Subgroup.normalizer (((A ⊓ Y : Subgroup G).subgroupOf Y : Subgroup Y) : Set Y) :=
    hpu ▸ Subgroup.pow_mem _ ht₀N u
  have htE : (p : G) ∈ Subgroup.normalizer ((A ⊓ Y : Subgroup G) : Set G) :=
    Item812Res12.mem_normalizer_of_subgroupOf inf_le_right htN
  have hpa : (p : G) * a = a * p := Subgroup.mem_centralizer_singleton_iff.mp
    (le_centralizer_of_mem_thetaComponentsAt_three h.mem_thetaComponentsAt_Y p.2)
  have hpz : (p : G) * zc = zc * p := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hzc
    exact Commute.zpow_right (show Commute (p : G) a from hpa) k
  have hpyc : (p : G) * yc = yc * p := by
    have hxY : (p : G) * yc * (p : G)⁻¹ ∈ Y := Y.mul_mem (Y.mul_mem p.2 hyc.2) (Y.inv_mem p.2)
    have hxE : (p : G) * yc * (p : G)⁻¹ ∈ A ⊓ Y := (Subgroup.mem_normalizer_iff.mp htE yc).mp hyc
    have hxy3 : (((p : G) * yc * (p : G)⁻¹)⁻¹ * yc) ^ 3 = 1 :=
      hAab.2 _ (A.mul_mem (A.inv_mem hxE.1) hyc.1)
    have hmk : QuotientGroup.mk' (aschbacherSolvableCore 3 Y)
        ⟨(p : G) * yc * (p : G)⁻¹, hxY⟩ =
        QuotientGroup.mk' (aschbacherSolvableCore 3 Y) ⟨yc, hyc.2⟩ := by
      have : (⟨(p : G) * yc * (p : G)⁻¹, hxY⟩ : Y) = p * ⟨yc, hyc.2⟩ * p⁻¹ := rfl
      rw [this, map_mul, map_mul, map_inv, hpφ, ht₀s, hgv, mul_inv_cancel_right]
    have h1 := Item812Res11.eq_of_mk_eq hxY hyc.2 hxy3 hmk
    calc (p : G) * yc = ((p : G) * yc * (p : G)⁻¹) * p := by group
      _ = yc * p := by rw [h1]
  have hpc : (p : G) * c = c * p := by
    rw [← hce]
    exact (Commute.mul_right (show Commute (p : G) zc from hpz)
      (show Commute (p : G) yc from hpyc)).eq
  have hp3 : IsPGroup 3 (Subgroup.zpowers (p : G)) := by
    intro x
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp x.2
    refine ⟨e, Subtype.ext ?_⟩
    have hpe' : (p : G) ^ 3 ^ e = 1 := by simpa using congrArg Subtype.val hpe
    show (x : G) ^ 3 ^ e = 1
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hpe', one_zpow]
  have hc1 : c ≠ 1 := h.ne_one
  have hc3 : c ^ 3 = 1 := hAab.2 c h.mem_A
  have hpC : Subgroup.zpowers (p : G) ≤ Subgroup.centralizer ({c} : Set G) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_singleton_iff.mpr hpc
  have hpL : (p : G) ∈ Subgroup.normalizer (L : Set G) :=
    Sec11.le_normalizer_of_isPGroup_of_le_centralizer h45 hG hc3 hc1 hp3 hpC L
      h.mem_thetaComponentsAt (Subgroup.mem_zpowers _)
  have htA : (p : G) ∈ Subgroup.normalizer (A : Set G) := by
    have := mem_normalizer_zpowers_sup htE hpa
    rwa [Item812Res6.zpowers_sup_inf_eq h] at this
  have htB : (p : G) ∈ Subgroup.normalizer ((sec8B A X : Subgroup G) : Set G) := by
    rw [h.item811 c L h.pairRel]
    exact mem_normalizer_sec8B htA hpL
  have htBE := mem_normalizer_inf htB htE
  have hpg : QuotientGroup.mk' (aschbacherSolvableCore 3 Y) p = g := by rw [hpφ, ht₀s]
  rw [← hpg]
  exact mem_normalizer_imageModTheta htBE

end Lifts

theorem fin812BMemYU_of_k (h45 : Sec4.Item4_5) (h84 : Pair84A) (hC : KF812U3Cent)
    (hI : KF812U3Irred) : Fin812BMemYU := by
  intro G _ _ A c L a b X Y n h hU
  classical
  by_contra hbY
  obtain ⟨yb, zb, hyb, hzb, hbe, S, H, hSE, hS9, hSU, hub, hHperf, hSH, hHu⟩ :=
    dataU h84 h hbY
  obtain ⟨yc, zc, hyc, hzc, hce, hv1, Q, hQv, hQ8, hQu, hQc⟩ := dataV h45 h hU hyb hzb hbe
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 Y) with hπ
  have hAab := h.mem_partTwoF.1
  have hEabG : CFSG.Assembly.IsElemAbelian 3 (A ⊓ Y : Subgroup G) :=
    Item812Res4.isElemAbelian_of_le hAab inf_le_left
  have hEab : CFSG.Assembly.IsElemAbelian 3 (imageModTheta Y (A ⊓ Y)) :=
    Item812Res11.isElemAbelian_map' (Item812Res4.isElemAbelian_subgroupOf Y hEabG) _
  have hE27 : Nat.card (imageModTheta Y (A ⊓ Y)) = 27 := by
    rw [Item812Res11.card_imageModTheta_of_pow inf_le_right (fun x hx => hAab.2 x hx.1),
      Item812Res8.card_inf_Y h]
  have hubE : π ⟨yb, hyb.2⟩ ∈ imageModTheta Y (A ⊓ Y) :=
    ⟨⟨yb, hyb.2⟩, Subgroup.mem_subgroupOf.mpr hyb, rfl⟩
  have hvcE : π ⟨yc, hyc.2⟩ ∈ imageModTheta Y (A ⊓ Y) :=
    ⟨⟨yc, hyc.2⟩, Subgroup.mem_subgroupOf.mpr hyc, rfl⟩
  have hub3 : (π ⟨yb, hyb.2⟩) ^ 3 = 1 := hEab.2 _ hubE
  obtain ⟨hSp, g, hgN, hgv, hg3, e, heE, hge⟩ := hC _ h.item89_Y (imageModTheta Y (A ⊓ Y)) Q
    (π ⟨yc, hyc.2⟩) hEab hE27 hvcE hv1 hQv hQ8 (quatLike_of_commutator hQ8 hub3 hQu hQc)
  have hUE : imageModTheta Y (sec8B A X ⊓ (A ⊓ Y)) ≤ imageModTheta Y (A ⊓ Y) :=
    Item812Res11.imageModTheta_mono inf_le_right
  have hirr := hI _ hSp (imageModTheta Y (A ⊓ Y)) S H (π ⟨yb, hyb.2⟩) g hEab hE27 hSE hS9
    hubE hub hHperf hSH hHu hgN hg3 ⟨e, heE, hge⟩ (imageModTheta Y (sec8B A X ⊓ (A ⊓ Y))) hUE
    (fun s hs hsu => mem_normalizer_of_centralizes_u h hyb hzb hbe hs hsu)
    (mem_normalizer_of_centralizes_v h45 h hyc hzc hce hgN hgv hg3)
  have hcardU : Nat.card (imageModTheta Y (sec8B A X ⊓ (A ⊓ Y))) =
      Nat.card (sec8B A X ⊓ (A ⊓ Y) : Subgroup G) :=
    Item812Res11.card_imageModTheta_of_pow (inf_le_right.trans inf_le_right)
      (fun x hx => hAab.2 x hx.2.1)
  rcases hirr with h0 | hEq
  · have h1 := Subgroup.card_le_of_le (hSU.trans h0.le)
    rw [hS9, Subgroup.card_bot] at h1
    omega
  · have h27 : Nat.card (sec8B A X ⊓ (A ⊓ Y) : Subgroup G) = 27 := by
      rw [← hcardU, hEq, hE27]
    have hBeq : sec8B A X ⊓ (A ⊓ Y) = sec8B A X :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h27, Item812Res8.card_sec8B h])
    have hXb : X ∈ thetaComponentsAt 3 b := h.pairRel.2.2.1
    have hbB : b ∈ sec8B A X :=
      ⟨h.isGammaIndex.1,
        Subgroup.mem_sup_right (Sec6.mem_thetaQuotCentralizer_of_mem_thetaComponentsAt hXb)⟩
    rw [← hBeq] at hbB
    exact hbY hbB.2.2

end CFSG.RankThree.PartTwo.Sec8.HeringBMem
