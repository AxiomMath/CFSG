module

public import CFSG.RankThree.PartTwo.Sec8.Item812Res10ProofBEq
import CFSG.RankThree.PartTwo.Sec8.Item812Res2ProofGen
import CFSG.RankThree.PartTwo.Sec8.Item812Res6ProofPaExp
import CFSG.RankThree.PartTwo.Sec8.Item812Res8ProofBNotCent
import CFSG.RankThree.PartTwo.Sec8.Item812Res8ProofGammaInner
import CFSG.RankThree.PartTwo.Sec8.Item87ProofOrders
import CFSG.RankThree.PartTwo.Sec8.Item812Res10ProofR
import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofLink
import CFSG.RankThree.PartTwo.Sec6.Item612
import CFSG.RankThree.PartOne.N143.SectionGroup
public import CFSG.RankThree.PartTwo.KFacts.K71Lift

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 (InducesOuterTheta thetaQuotMulAut compAction)
open CFSG.Assembly.RankThreeEven (projSp projSL)

@[expose] def KF812E27PerfCent : Prop :=
  ∀ (M : Type) [Group M] [Finite M],
    (Nonempty (M ≃* alternatingGroup (Fin 9)) ∨ Nonempty (M ≃* projSp 3 (GaloisField 2 1))) →
    ∀ (E S H₁ H₂ : Subgroup M) (u v : M),
      CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 27 → S ≤ E → Nat.card S = 9 →
      u ∈ E → v ∈ E → u ∉ S → v ∉ S →
      Group.IsPerfect H₁ → Group.IsPerfect H₂ → S ≤ H₁ → S ≤ H₂ →
      H₁ ≤ Subgroup.centralizer {u} → H₂ ≤ Subgroup.centralizer {v} →
      v ∈ Subgroup.zpowers u


namespace Item812Res11

variable {G : Type} [Group G] [Finite G]

theorem eq_one_of_mem_zpowers_of_mem_sup {L : Subgroup G} {a z : G} (ha3 : a ^ 3 = 1)
    (haout : InducesOuterTheta a L) (hz : z ∈ Subgroup.zpowers a)
    (hzL : z ∈ L ⊔ Sec4.thetaQuotCentralizer L) : z = 1 := by
  obtain ⟨haN, hnot⟩ := haout
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, a ^ k = z :=
    (Submonoid.mem_powers_iff _ _).mp ((isOfFinOrder_of_finite a).mem_powers_iff_mem_zpowers.mpr hz)
  have hk : a ^ k = a ^ (k % 3) := by
    conv_lhs => rw [← Nat.mod_add_div k 3, pow_add, pow_mul, ha3, one_pow, mul_one]
  rw [hk] at hzL ⊢
  have hk3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  have haL : a ∉ L ⊔ Sec4.thetaQuotCentralizer L := fun h =>
    hnot ((Item812Res2.mem_sup_thetaQuotCentralizer_iff haN).mp h)
  rcases hk3 with h0 | h1 | h2
  · rw [h0, pow_zero]
  · rw [h1, pow_one] at hzL
    exact absurd hzL haL
  · rw [h2] at hzL
    exfalso
    apply haL
    have e : a = (a ^ 2) ^ 2 := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 by rfl, pow_succ, ha3, one_mul]
    rw [e]
    exact Subgroup.pow_mem _ hzL 2

theorem card_imageModTheta_of_pow {Y H : Subgroup G} (hHY : H ≤ Y)
    (hH3 : ∀ x ∈ H, x ^ 3 = 1) : Nat.card (imageModTheta Y H) = Nat.card H := by
  rw [imageModTheta, CFSG.RankThree.PartOne.N143.card_map_of_disjoint_ker]
  · exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHY).toEquiv
  · rw [Subgroup.disjoint_def]
    intro x hx hxk
    have hx1 : (x : G) = 1 := by
      refine Item812Res6.eq_one_of_mem_theta_of_pow (k := 1) ⟨x, ?_, rfl⟩ ?_
      · rw [MonoidHom.mem_ker, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hxk
        exact hxk
      · rw [pow_one]
        exact hH3 _ (Subgroup.mem_subgroupOf.mp hx)
    exact Subtype.ext hx1

theorem eq_of_mk_eq {Y : Subgroup G} {x y : G} (hxY : x ∈ Y) (hyY : y ∈ Y)
    (hxy3 : (x⁻¹ * y) ^ 3 = 1)
    (h : (QuotientGroup.mk' (aschbacherSolvableCore 3 Y) ⟨x, hxY⟩ :
        Y ⧸ aschbacherSolvableCore 3 Y) = QuotientGroup.mk' _ ⟨y, hyY⟩) : x = y := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h
  have h1 : ((⟨x, hxY⟩ : Y)⁻¹ * ⟨y, hyY⟩ : Y) = ⟨x⁻¹ * y, Y.mul_mem (Y.inv_mem hxY) hyY⟩ := rfl
  rw [h1] at h
  have h2 : x⁻¹ * y = 1 := by
    refine Item812Res6.eq_one_of_mem_theta_of_pow (k := 1) ⟨_, h, rfl⟩ ?_
    rw [pow_one]
    exact hxy3
  calc x = x * (x⁻¹ * y) := by rw [h2, mul_one]
    _ = y := by group

theorem isElemAbelian_map' {H K : Type*} [Group H] [Group K] {p : ℕ} {S : Subgroup H}
    (hS : CFSG.Assembly.IsElemAbelian p S) (f : H →* K) :
    CFSG.Assembly.IsElemAbelian p (S.map f) := CFSG.Open.IsElemAbelian.map hS _

theorem isPerfect_imageModTheta {Y H : Subgroup G} (hHY : H ≤ Y) (hH : Group.IsPerfect H) :
    Group.IsPerfect (imageModTheta Y H) := by
  have : Group.IsPerfect (H.subgroupOf Y) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hHY).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hHY).symm.surjective
  exact Group.IsPerfect.ofSurjective
    (f := (QuotientGroup.mk' (aschbacherSolvableCore 3 Y)).subgroupMap (H.subgroupOf Y))
    ((QuotientGroup.mk' _).subgroupMap_surjective _)

theorem imageModTheta_mono {Y H H' : Subgroup G} (h : H ≤ H') :
    imageModTheta Y H ≤ imageModTheta Y H' := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, Subgroup.mem_subgroupOf.mpr (h (Subgroup.mem_subgroupOf.mp hx)), rfl⟩

end Item812Res11


namespace Item812Res11

variable {G : Type} [Group G] [Finite G]

theorem map_le_perfectResidual {A Lf : Subgroup G} (hAab : CFSG.Assembly.IsElemAbelian 3 A)
    {a : G} (haA : a ∈ A) (haout : InducesOuterTheta a Lf)
    (hLf : Nonempty (Lf ⧸ aschbacherSolvableCore 3 Lf ≃* projSp 2 (GaloisField 2 3)))
    {S₀ : Subgroup Lf} (hS₀A : S₀.map Lf.subtype ≤ A) :
    S₀.map Lf.subtype ≤ inSubgroup perfectResidual (Lf ⊓ Subgroup.centralizer ({a} : Set G)) := by
  have ha3 : a ^ 3 = 1 := hAab.2 a haA
  obtain ⟨-, ⟨ι⟩⟩ := KFacts.barCentralizer_mulEquiv_projSp (n := 1) one_ne_zero ha3 haout hLf
  have hRF := Item8KFacts2Proof.ResidualFacts.of_mulEquiv ι
    (Item8KFacts2Proof.residualFacts_projSp (m := 1) le_rfl)
  rintro _ ⟨s, hs, rfl⟩
  have hsA : (s : G) ∈ A := hS₀A ⟨s, hs, rfl⟩
  have hsa : (s : G) ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hAab.1.is_comm.comm ⟨_, hsA⟩ ⟨a, haA⟩))
  exact Item8KFacts2Proof.mem_inSubgroup_perfectResidual_of_pow_three haout.1 ha3 hRF.1 s.2 hsa
    (hAab.2 _ hsA)

end Item812Res11

@[expose] def Fin812BMemYU : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X Y : Subgroup G) (n : ℕ), Sec8Final G A c L a b X Y n →
    IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) 3 → b ∈ Y

open Item812Res11 in
theorem fin812BMemY_of
    (h84 : Pair84A) (hK : KF812E27PerfCent) (hU : Fin812BMemYU) :
    Fin812BMemY := by
  intro G _ _ A c L a b X Y n h
  classical
  rcases h.item89_omega (c, L) h.pairRel.1 with hLU | hLSp
  · exact hU G A c L a b X Y n h hLU
  by_contra hbY
  have hAab := h.mem_partTwoF.1
  have hAc : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hAab.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have h3A : ∀ u ∈ A, u ^ 3 = 1 := hAab.2
  have haA : a ∈ A := h.a_mem
  have ha3 : a ^ 3 = 1 := h3A a haA
  have hbA : b ∈ A := h.isGammaIndex.1
  have hb1 : b ≠ 1 := h.isGammaIndex.2.1
  have hb3 : b ^ 3 = 1 := h3A b hbA
  have hcA : c ∈ A := h.mem_A
  have hc1 : c ≠ 1 := h.ne_one
  have hXb : X ∈ thetaComponentsAt 3 b := h.pairRel.2.2.1
  have hLc : L ∈ thetaComponentsAt 3 c := h.mem_thetaComponentsAt
  have h3G := h.toTheoremFourHyp.localRank_three.le
  have haX : InducesOuterTheta a X := by
    rcases h84 G A c L a b X n h.toSec8Pair with hk | hk
    · exact KFacts.InducesStdKind.inducesOuterTheta X hk (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta X hk (by decide)
  have haL : InducesOuterTheta a L := by
    rcases h.inducesStdKind with hk | hk
    · exact KFacts.InducesStdKind.inducesOuterTheta L hk (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta L hk (by decide)
  obtain ⟨S₀, hS₀A, hS₀9, -, -, -, hBS⟩ := Item812Res2.sec8B_structure_of_projSp h3G
    h.mem_partTwoF h.card_eq hbA hb1 hXb h.item89_X haA haX
  obtain ⟨S₀', hS₀'A, hS₀'9, -, -, -, hBS'⟩ := Item812Res2.sec8B_structure_of_projSp h3G
    h.mem_partTwoF h.card_eq hcA hc1 hLc hLSp haA haL
  have hBL : sec8B A X = sec8B A L := h.item811 c L h.pairRel
  have hS0card : Nat.card (S₀.map X.subtype) = 9 := by
    rw [Subgroup.card_map_of_injective X.subtype_injective, hS₀9]
  have hS0'card : Nat.card (S₀'.map L.subtype) = 9 := by
    rw [Subgroup.card_map_of_injective L.subtype_injective, hS₀'9]
  have hS0B : S₀.map X.subtype ≤ sec8B A X := by rw [hBS]; exact le_sup_right
  have hS0'B : S₀'.map L.subtype ≤ sec8B A X := by rw [hBL, hBS']; exact le_sup_right
  have hbB : b ∈ sec8B A X := by rw [hBS]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers b)
  have hJ : S₀.map X.subtype ≤ sec8J X a := map_le_perfectResidual hAab haA haX h.item89_X hS₀A
  have hLnU : ¬ IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) 3 := by
    intro hU3
    obtain ⟨e⟩ := hLSp
    have e' : L ⧸ aschbacherSolvableCore 3 L ≃* projSp 2 (GaloisField 2 (3 * 1)) := e
    exact (Item86ResProof.sigSp4_of_projSp le_rfl e').not_isUnitaryTwo le_rfl 3 hU3
  have hIdef : sec8I L a =
      inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({a} : Set G)) := by
    simp only [sec8I, hLnU, ↓reduceIte]
  have hI : S₀'.map L.subtype ≤ sec8I L a := by
    rw [hIdef]
    exact map_le_perfectResidual hAab haA haL hLSp hS₀'A
  have hJY : sec8J X a ≤ Y := le_sup_right.trans h.le_Y
  have hIY : sec8I L a ≤ Y := le_sup_left.trans h.le_Y
  have hcY : c ∉ Y := by
    intro hcY
    apply hbY
    have hBY : sec8B A X ≤ Y := by
      rw [hBL, hBS']
      exact sup_le ((Subgroup.zpowers_le).mpr hcY) (hI.trans hIY)
    exact hBY hbB
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
  have hS0'eq : S₀'.map L.subtype = sec8B A X ⊓ Y :=
    Subgroup.eq_of_le_of_card_ge (le_inf hS0'B (hI.trans hIY)) (by rw [hS0'card]; exact hBY9)
  have hSS : S₀.map X.subtype = S₀'.map L.subtype := hS0eq.trans hS0'eq.symm
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
  obtain ⟨zc, hzc, yc, hyc, hce⟩ := hdec c hcA
  have hzbA : zb ∈ A := (Subgroup.zpowers_le).mpr haA hzb
  have hzcA : zc ∈ A := (Subgroup.zpowers_le).mpr haA hzc
  set φ := QuotientGroup.mk' (aschbacherSolvableCore 3 Y) with hφ
  set u : Y ⧸ aschbacherSolvableCore 3 Y := φ ⟨yb, hyb.2⟩ with hu
  set v : Y ⧸ aschbacherSolvableCore 3 Y := φ ⟨yc, hyc.2⟩ with hv
  have hAYab : CFSG.Assembly.IsElemAbelian 3 ((A ⊓ Y).subgroupOf Y) := by
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => Subtype.ext ?_⟩
    · obtain ⟨x, hx⟩ := x
      obtain ⟨y, hy⟩ := y
      exact Subtype.ext (hAc _ (Subgroup.mem_subgroupOf.mp hx).1 _
        (Subgroup.mem_subgroupOf.mp hy).1)
    · simpa using h3A _ (Subgroup.mem_subgroupOf.mp hx).1
  have hEab : CFSG.Assembly.IsElemAbelian 3 (imageModTheta Y (A ⊓ Y)) :=
    isElemAbelian_map' hAYab _
  have hE27 : Nat.card (imageModTheta Y (A ⊓ Y)) = 27 := by
    rw [card_imageModTheta_of_pow inf_le_right (fun x hx => h3A x hx.1), Item812Res8.card_inf_Y h]
  have hS0A : S₀.map X.subtype ≤ A ⊓ Y := hS0eq ▸ inf_le_inf_right Y inf_le_left
  have hSE : imageModTheta Y (S₀.map X.subtype) ≤ imageModTheta Y (A ⊓ Y) :=
    imageModTheta_mono hS0A
  have hS9 : Nat.card (imageModTheta Y (S₀.map X.subtype)) = 9 := by
    rw [card_imageModTheta_of_pow (hS0A.trans inf_le_right) (fun x hx => h3A x (hS0A hx).1),
      hS0card]
  have huE : u ∈ imageModTheta Y (A ⊓ Y) := ⟨⟨yb, hyb.2⟩, Subgroup.mem_subgroupOf.mpr hyb, rfl⟩
  have hvE : v ∈ imageModTheta Y (A ⊓ Y) := ⟨⟨yc, hyc.2⟩, Subgroup.mem_subgroupOf.mpr hyc, rfl⟩
  have hmemS : ∀ {y : G} (hy : y ∈ A ⊓ Y), φ ⟨y, hy.2⟩ ∈ imageModTheta Y (S₀.map X.subtype) →
      y ∈ S₀.map X.subtype := by
    intro y hy hmem
    obtain ⟨s, hs, hse⟩ := hmem
    have hsA : (s : G) ∈ A := (hS0A (Subgroup.mem_subgroupOf.mp hs)).1
    have hys : (s : G) = y := by
      refine eq_of_mk_eq s.2 hy.2 (h3A _ (A.mul_mem (A.inv_mem hsA) hy.1)) ?_
      rw [← hse]
    rw [← hys]
    exact Subgroup.mem_subgroupOf.mp hs
  have huS : u ∉ imageModTheta Y (S₀.map X.subtype) := by
    intro hmem
    have hybS := hmemS hyb hmem
    have hybX : yb ∈ X := (Subgroup.map_subtype_le _) hybS
    have hzb1 : zb = 1 := by
      refine eq_one_of_mem_zpowers_of_mem_sup ha3 haX hzb ?_
      have e : zb = b * yb⁻¹ := by rw [← hbe, mul_inv_cancel_right]
      rw [e]
      exact Subgroup.mul_mem _ hbB.2 (Subgroup.mem_sup_left (X.inv_mem hybX))
    apply hbY
    rw [← hbe, hzb1, one_mul]
    exact hyb.2
  have hvS : v ∉ imageModTheta Y (S₀.map X.subtype) := by
    intro hmem
    have hycS := hmemS hyc hmem
    rw [hSS] at hycS
    have hycL : yc ∈ L := (Subgroup.map_subtype_le _) hycS
    have hzc1 : zc = 1 := by
      refine eq_one_of_mem_zpowers_of_mem_sup ha3 haL hzc ?_
      have e : zc = c * yc⁻¹ := by rw [← hce, mul_inv_cancel_right]
      rw [e]
      exact Subgroup.mul_mem _
        (Subgroup.mem_sup_right (Sec6.mem_thetaQuotCentralizer_of_mem_thetaComponentsAt hLc))
        (Subgroup.mem_sup_left (L.inv_mem hycL))
    apply hcY
    rw [← hce, hzc1, one_mul]
    exact hyc.2
  have hJperf : Group.IsPerfect (imageModTheta Y (sec8J X a)) :=
    isPerfect_imageModTheta hJY (Item87Proof.isPerfect_residual _)
  have hIperf : Group.IsPerfect (imageModTheta Y (sec8I L a)) := by
    refine isPerfect_imageModTheta hIY ?_
    rw [hIdef]
    exact Item87Proof.isPerfect_residual _
  have hcommY : ∀ {H : Subgroup G} (hHY : H ≤ Y) {y : G} (hyY : y ∈ Y),
      (∀ x ∈ H, x * y = y * x) →
      imageModTheta Y H ≤ Subgroup.centralizer {φ ⟨y, hyY⟩} := by
    intro H hHY y hyY hcomm
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcomm _ (Subgroup.mem_subgroupOf.mp hx))
  have hza : ∀ {z x : G}, z ∈ Subgroup.zpowers a → x ∈ Subgroup.centralizer ({a} : Set G) →
      x * z = z * x := by
    intro z x hz hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact ((Commute.zpow_right
      (Subgroup.mem_centralizer_singleton_iff.mp hx : x * a = a * x) k))
  have hJu : imageModTheta Y (sec8J X a) ≤ Subgroup.centralizer {u} := by
    refine hcommY hJY hyb.2 fun x hx => ?_
    have hxXa : x ∈ X ⊓ Subgroup.centralizer ({a} : Set G) := (Subgroup.map_subtype_le _) hx
    have hxb : x * b = b * x := Subgroup.mem_centralizer_singleton_iff.mp
      (le_centralizer_of_mem_thetaComponentsAt_three hXb hxXa.1)
    have hxz : x * zb = zb * x := hza hzb hxXa.2
    have e : yb = zb⁻¹ * b := by rw [← hbe, inv_mul_cancel_left]
    rw [e]
    have h1 : Commute x zb := hxz
    have h2 : Commute x b := hxb
    exact (h1.inv_right.mul_right h2).eq
  have hIv : imageModTheta Y (sec8I L a) ≤ Subgroup.centralizer {v} := by
    refine hcommY hIY hyc.2 fun x hx => ?_
    have hxLa : x ∈ L ⊓ Subgroup.centralizer ({a} : Set G) := Item812Res7.sec8I_le L a hx
    have hxc : x * c = c * x := Subgroup.mem_centralizer_singleton_iff.mp
      (le_centralizer_of_mem_thetaComponentsAt_three hLc hxLa.1)
    have hxz : x * zc = zc * x := hza hzc hxLa.2
    have e : yc = zc⁻¹ * c := by rw [← hce, inv_mul_cancel_left]
    rw [e]
    have h1 : Commute x zc := hxz
    have h2 : Commute x c := hxc
    exact (h1.inv_right.mul_right h2).eq
  have hSJ : imageModTheta Y (S₀.map X.subtype) ≤ imageModTheta Y (sec8J X a) :=
    imageModTheta_mono hJ
  have hSI : imageModTheta Y (S₀.map X.subtype) ≤ imageModTheta Y (sec8I L a) :=
    imageModTheta_mono (hSS ▸ hI)
  have hvu := hK _ h.item89_Y _ _ _ _ u v hEab hE27 hSE hS9 huE hvE huS hvS hJperf hIperf
    hSJ hSI hJu hIv
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hvu
  have hybk : yb ^ k ∈ A ⊓ Y := Subgroup.zpow_mem _ hyb k
  have hyck : yb ^ k = yc := by
    refine eq_of_mk_eq hybk.2 hyc.2 (h3A _ (A.mul_mem (A.inv_mem hybk.1) hyc.1)) ?_
    have e1 : (⟨yb ^ k, hybk.2⟩ : Y) = (⟨yb, hyb.2⟩ : Y) ^ k := Subtype.ext (by simp)
    rw [e1, map_zpow]
    exact hk
  have hcab : c = (zc * zb⁻¹ ^ k) * b ^ k := by
    have e : yb = zb⁻¹ * b := by rw [← hbe, inv_mul_cancel_left]
    have hcomm : Commute zb⁻¹ b := hAc _ (A.inv_mem hzbA) _ hbA
    rw [← hce, ← hyck, e, hcomm.mul_zpow, mul_assoc]
  have hz1 : zc * zb⁻¹ ^ k = 1 := by
    refine eq_one_of_mem_zpowers_of_mem_sup ha3 haL
      (Subgroup.mul_mem _ hzc (Subgroup.zpow_mem _ (Subgroup.inv_mem _ hzb) k)) ?_
    have e : zc * zb⁻¹ ^ k = c * (b ^ k)⁻¹ := by
      rw [hcab, mul_inv_cancel_right]
    rw [e]
    have hbL : b ∈ L ⊔ Sec4.thetaQuotCentralizer L := by
      have := hbB
      rw [hBL] at this
      exact this.2
    exact Subgroup.mul_mem _
      (Subgroup.mem_sup_right (Sec6.mem_thetaQuotCentralizer_of_mem_thetaComponentsAt hLc))
      (Subgroup.inv_mem _ (Subgroup.zpow_mem _ hbL k))
  rw [hz1, one_mul] at hcab
  have hbc : b ∈ Subgroup.zpowers c := by
    have hcb : c ∈ Subgroup.zpowers b := ⟨k, hcab.symm⟩
    have hb3' : orderOf b = 3 := orderOf_eq_prime hb3 hb1
    have hzpow : Subgroup.zpowers c = Subgroup.zpowers b := by
      refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hcb) ?_
      rw [Nat.card_zpowers, Nat.card_zpowers, hb3']
      have hc3 : c ^ 3 = 1 := h3A c hcA
      rw [orderOf_eq_prime hc3 hc1]
    rw [hzpow]
    exact Subgroup.mem_zpowers b
  have hbLc : ∀ y ∈ L, b * y = y * b := by
    intro y hy
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hbc
    exact (Commute.zpow_left
      ((Subgroup.mem_centralizer_singleton_iff.mp
        (le_centralizer_of_mem_thetaComponentsAt_three hLc hy)).symm) j)
  have hbN : b ∈ Subgroup.normalizer (L : Set G) := by
    have hbL' : b ∈ L ⊔ Sec4.thetaQuotCentralizer L := by
      have := hbB
      rw [hBL] at this
      exact this.2
    exact Item812Res10.sup_le_normalizer L hbL'
  have h1 : thetaQuotMulAut L (compAction L ⟨b, hbN⟩) = 1 :=
    KFacts.thetaQuotMulAut_compAction_eq_one hbN hbLc
  have htop : barCentralizer (Subgroup.zpowers b) L = ⊤ := by
    ext z
    simp only [Subgroup.mem_top, iff_true]
    rw [KFacts.mem_barCentralizer_zpowers_iff hbN, h1, MulAut.one_apply]
  have himgB := KFacts.imageModTheta_perfectResidual_centralizer_eq hbN
    ⟨1, by rw [pow_one]; exact hb3⟩
  have hle : inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers a) L) ≤
      imageModTheta L (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G))) := by
    rw [himgB, htop]
    exact KFacts.le_inSubgroup_perfectResidual (Item87Proof.isPerfect_residual _) le_top
  obtain ⟨-, ⟨ιa⟩⟩ := KFacts.barCentralizer_mulEquiv_projSp (n := 1) one_ne_zero ha3 haL hLSp
  have hK504 : Nat.card (imageModTheta L
      (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)))) =
      2 ^ (3 * 1) * ((2 ^ (3 * 1)) ^ 2 - 1) := by
    obtain ⟨-, -, hn1, hcase⟩ := Item87Proof.isGammaIndex_cases h.isGammaIndex
    obtain ⟨e⟩ := hLSp
    have e' : L ⧸ aschbacherSolvableCore 3 L ≃* projSp 2 (GaloisField 2 (3 * 1)) := e
    have hSig := Item86ResProof.sigSp4_of_projSp le_rfl e'
    rcases hcase with ⟨hRee, -⟩ | ⟨hL2, ⟨ι⟩⟩
    · exact ((Item86ResProof.sigF4_of_reeF4 hn1 hRee).false_of_sigSp4 hSig hn1).elim
    · have hn : n = 1 := Item86ResProof.eq_of_isGammaType hn1 le_rfl (Or.inr hL2)
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e'⟩)))))
      subst hn
      rw [Nat.card_congr ι.toEquiv, Item87Proof.card_projSL_two_three le_rfl]
  apply Item812Res8.not_dvd_card_perfectResidual_projSp (m := 1) le_rfl
  rw [← hK504, ← Item812Res8.card_inSubgroup_perfectResidual_eq ιa]
  exact Subgroup.card_dvd_of_le hle

end CFSG.RankThree.PartTwo.Sec8
