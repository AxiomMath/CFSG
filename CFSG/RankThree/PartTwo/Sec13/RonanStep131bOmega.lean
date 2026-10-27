module

import CFSG.RankThree.LocalRank.ThetaPlaneExactQuotients
import CFSG.RankThree.PartTwo.Sec4.Item422Proof
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartTwo.Sec21.Implications
public import CFSG.RankThree.PartTwo.Sec6.Item612Basic

public section

namespace CFSG.RankThree.PartTwo.Sec13.RonanStep131b

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem mem_sup_of_forall_comm {H : Type*} [Group H] {S T : Subgroup H}
    (hcomm : ∀ s ∈ S, ∀ t ∈ T, s * t = t * s) {x : H} (hx : x ∈ S ⊔ T) :
    ∃ y ∈ S, ∃ z ∈ T, y * z = x := by
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨x, hx, 1, T.one_mem, mul_one x⟩
    · exact ⟨1, S.one_mem, x, hx, one_mul x⟩
  | one => exact ⟨1, S.one_mem, 1, T.one_mem, mul_one 1⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨y1, hy1, z1, hz1, rfl⟩ := ihx
    obtain ⟨y2, hy2, z2, hz2, rfl⟩ := ihy
    have h := hcomm y2 hy2 z1 hz1
    refine ⟨y1 * y2, S.mul_mem hy1 hy2, z1 * z2, T.mul_mem hz1 hz2, ?_⟩
    calc y1 * y2 * (z1 * z2) = y1 * (y2 * z1) * z2 := by simp only [mul_assoc]
      _ = y1 * (z1 * y2) * z2 := by rw [h]
      _ = y1 * z1 * (y2 * z2) := by simp only [mul_assoc]
  | inv x _ ih =>
    obtain ⟨y, hy, z, hz, rfl⟩ := ih
    refine ⟨y⁻¹, S.inv_mem hy, z⁻¹, T.inv_mem hz, ?_⟩
    rw [hcomm y hy z hz, mul_inv_rev]

theorem sup_zpowers_eq_of_card {G : Type} [Group G] [Finite G] {F K : Subgroup G} {b : G}
    (hKF : K ≤ F) (hF : Nat.card F = 27) (hK : Nat.card K = 9) (hbF : b ∈ F) (hbK : b ∉ K) :
    K ⊔ Subgroup.zpowers b = F := by
  have hHF : K ⊔ Subgroup.zpowers b ≤ F := sup_le hKF (Subgroup.zpowers_le.mpr hbF)
  have hdvd1 : Nat.card K ∣ Nat.card ↥(K ⊔ Subgroup.zpowers b) :=
    Subgroup.card_dvd_of_le le_sup_left
  have hdvd2 : Nat.card ↥(K ⊔ Subgroup.zpowers b) ∣ 27 := by
    rw [← hF]; exact Subgroup.card_dvd_of_le hHF
  have hne : Nat.card ↥(K ⊔ Subgroup.zpowers b) ≠ 9 := by
    intro h9
    apply hbK
    have heq : K = K ⊔ Subgroup.zpowers b :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (le_of_eq (by rw [h9, hK]))
    rw [heq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
  have hpos : 0 < Nat.card ↥(K ⊔ Subgroup.zpowers b) := Nat.card_pos
  rw [hK] at hdvd1
  have hn : Nat.card ↥(K ⊔ Subgroup.zpowers b) = 27 := by
    generalize Nat.card ↥(K ⊔ Subgroup.zpowers b) = n at hdvd1 hdvd2 hne hpos ⊢
    have hle : n ≤ 27 := Nat.le_of_dvd (by norm_num) hdvd2
    interval_cases n <;> omega
  exact Subgroup.eq_of_le_of_card_ge hHF (le_of_eq (by rw [hn, hF]))

noncomputable abbrev ronan131bPiece {G : Type} [Group G] (a b : G) : Subgroup G :=
  inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G)) ⊓
    Subgroup.centralizer ({b} : Set G)

theorem ronan131b_piece_solvable {G : Type} [Group G] [Finite G] (a b : G) :
    Group.IsSolvable ↥(ronan131bPiece a b) ∧ ¬ 3 ∣ Nat.card ↥(ronan131bPiece a b) := by
  obtain ⟨hsol, h3⟩ := Sec4.Item422Proof.inSubgroup_theta_solvable_coprime
    (Subgroup.centralizer ({a} : Set G))
  refine ⟨?_, fun h => h3 (h.trans (Subgroup.card_dvd_of_le inf_le_left))⟩
  haveI := hsol
  exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective inf_le_left)

theorem ronan131b_normalizes_piece {G : Type} [Group G] {a b m : G}
    (hma : m ∈ Subgroup.centralizer ({a} : Set G)) (hmb : m ∈ Subgroup.centralizer ({b} : Set G))
    (h : G) :
    h ∈ ronan131bPiece a b ↔ m * h * m⁻¹ ∈ ronan131bPiece a b := by
  unfold ronan131bPiece
  rw [Subgroup.mem_inf, Subgroup.mem_inf]
  have h1 := Subgroup.mem_normalizer_iff.mp
    (Sec6.le_normalizer_theta (Subgroup.centralizer ({a} : Set G)) hma) h
  have h2 := Subgroup.mem_normalizer_iff.mp
    (Subgroup.le_normalizer (H := Subgroup.centralizer ({b} : Set G)) hmb) h
  exact and_congr h1 h2

theorem ronan131b_R_le_theta {G : Type} [Group G] [Finite G] {R : Subgroup G} {a b : G}
    (hRa : R ≤ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G)))
    (hRb : R ≤ Subgroup.centralizer ({b} : Set G))
    (aC : ↥(Subgroup.centralizer ({b} : Set G))) (haCe : (aC : G) = a) :
    R.subgroupOf (Subgroup.centralizer ({b} : Set G)) ≤
      inSubgroup (aschbacherSolvableCore 3)
        (Subgroup.centralizer ({aC} : Set ↥(Subgroup.centralizer ({b} : Set G)))) := by
  obtain ⟨hsol, hS3⟩ := ronan131b_piece_solvable a b
  have hPC : ronan131bPiece a b ≤ Subgroup.centralizer ({b} : Set G) := inf_le_right
  have hPsol : Group.IsSolvable ↥((ronan131bPiece a b).subgroupOf
      (Subgroup.centralizer ({b} : Set G))) := by
    haveI := hsol
    exact Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hPC).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hPC).symm.surjective
  have hP3 : ¬ 3 ∣ Nat.card ↥((ronan131bPiece a b).subgroupOf
      (Subgroup.centralizer ({b} : Set G))) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPC).toEquiv]
    exact hS3
  have hSM : (ronan131bPiece a b).subgroupOf (Subgroup.centralizer ({b} : Set G)) ≤
      Subgroup.centralizer ({aC} : Set ↥(Subgroup.centralizer ({b} : Set G))) := by
    intro x hx
    have hxa : (x : G) ∈ Subgroup.centralizer ({a} : Set G) :=
      Sec6.theta_le _ (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hx)).1
    apply Subgroup.mem_centralizer_iff.mpr
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
    apply Subtype.ext
    show (aC : G) * (x : G) = (x : G) * (aC : G)
    rw [haCe]
    exact Subgroup.mem_centralizer_iff.mp hxa a (Set.mem_singleton a)
  have hMN : Subgroup.centralizer ({aC} : Set ↥(Subgroup.centralizer ({b} : Set G))) ≤
      Subgroup.normalizer
        (((ronan131bPiece a b).subgroupOf (Subgroup.centralizer ({b} : Set G)) :
          Subgroup ↥(Subgroup.centralizer ({b} : Set G))) : Set ↥(Subgroup.centralizer ({b} : Set G))) := by
    intro m hm
    have hmC : aC * m = m * aC := Subgroup.mem_centralizer_iff.mp hm aC (Set.mem_singleton aC)
    have hma : (m : G) ∈ Subgroup.centralizer ({a} : Set G) := by
      apply Subgroup.mem_centralizer_iff.mpr
      intro h hh
      rw [Set.mem_singleton_iff.mp hh, ← haCe]
      exact congrArg Subtype.val hmC
    rw [Subgroup.mem_normalizer_iff]
    intro h
    simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact ronan131b_normalizes_piece hma m.2 (h : G)
  have hSnorm := (Subgroup.normal_subgroupOf_iff_le_normalizer hSM).mpr hMN
  have hθ := Sec4.Item422Proof.le_inSubgroup_theta_of_normal hSM hSnorm hPsol hP3
  have hRS : R.subgroupOf (Subgroup.centralizer ({b} : Set G)) ≤
      (ronan131bPiece a b).subgroupOf (Subgroup.centralizer ({b} : Set G)) := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨hRa (Subgroup.mem_subgroupOf.mp hx), x.2⟩)
  exact hRS.trans hθ

theorem ronan131b_centralizes {X : Type} [Group X] [Finite X] {Rp Bc : Subgroup X} {aX cX : X}
    (hRp2 : IsPGroup 2 Rp) (haBc : aX ∈ Bc) (haX1 : aX ≠ 1) (hcBc : cX ∈ Bc)
    (hcN : cX ∈ Subgroup.normalizer (Rp : Set X))
    (hθ : Rp ≤ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({aX} : Set X)))
    (H1 : thetaAlpha 3 Bc ≤ aschbacherSolvableCore 3 X)
    (hodd : Odd (Nat.card (aschbacherSolvableCore 3 X))) :
    ∀ r ∈ Rp, cX * r = r * cX := by
  have hzc : Subgroup.zpowers cX ≤ Bc := Subgroup.zpowers_le.mpr hcBc
  have hcR : Subgroup.zpowers cX ≤ Subgroup.normalizer (Rp : Set X) :=
    Subgroup.zpowers_le.mpr hcN
  have hQle : ⁅Rp, Subgroup.zpowers cX⁆ ≤ Rp :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hcR
  have hQθ : ⁅Rp, Subgroup.zpowers cX⁆ ≤ aschbacherSolvableCore 3 X := by
    have h1 : ⁅Rp, Subgroup.zpowers cX⁆ ≤
        ⁅inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({aX} : Set X)), Bc⁆ :=
      Subgroup.commutator_mono hθ hzc
    have h2 : ⁅inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({aX} : Set X)),
        Bc⁆ ≤ thetaJ 3 Bc :=
      le_iSup_of_le aX (le_iSup_of_le haBc (le_iSup_of_le haX1 le_rfl))
    have h3 : thetaJ 3 Bc ≤ thetaAlpha 3 Bc := by
      unfold thetaAlpha; exact le_sup_left
    exact h1.trans (h2.trans (h3.trans H1))
  have hQodd : Odd (Nat.card ↥(⁅Rp, Subgroup.zpowers cX⁆)) :=
    Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le hQθ)
  have hQbot : ⁅Rp, Subgroup.zpowers cX⁆ = ⊥ :=
    CFSG.RankThree.PartTwo.Sec21.eq_bot_of_isPGroup_two_of_odd (hRp2.to_le hQle) hQodd
  have hcent := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hQbot
  intro r hr
  exact Subgroup.mem_centralizer_iff.mp (hcent hr) cX (Subgroup.mem_zpowers cX)

theorem ronan131b_H1 {G : Type} [Group G] [Finite G] {F Bs : Subgroup G} {b : G}
    (hFe : CFSG.Assembly.IsElemAbelian 3 F) (hBsF : Bs ≤ F)
    (hFsup : Bs ⊔ Subgroup.zpowers b = F) (hbF : b ∈ F) (hb1 : b ≠ 1)
    (hBs : Nat.card Bs = 9) (hbB : b ∉ Bs)
    (hstar : thetaAlpha 3 ((F.subgroupOf (Subgroup.centralizer ({b} : Set G))).map
        (QuotientGroup.mk' (centralLine b))) ≤
      aschbacherSolvableCore 3 (Subgroup.centralizer ({b} : Set G) ⧸ centralLine b)) :
    thetaAlpha 3 (Bs.subgroupOf (Subgroup.centralizer ({b} : Set G))) ≤
      aschbacherSolvableCore 3 (Subgroup.centralizer ({b} : Set G)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hFcomm : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hFe.1.is_comm.comm (⟨x, hx⟩ : F) ⟨y, hy⟩)
  have hF3 : ∀ x ∈ F, x ^ 3 = 1 := hFe.2
  have hbC : b ∈ Subgroup.centralizer ({b} : Set G) :=
    Subgroup.mem_centralizer_iff.mpr (fun h hh => by rw [Set.mem_singleton_iff.mp hh])
  have hFC : F ≤ Subgroup.centralizer ({b} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr (fun h hh => by
      rw [Set.mem_singleton_iff.mp hh]; exact hFcomm b hbF x hx)
  have hBsC : Bs ≤ Subgroup.centralizer ({b} : Set G) := hBsF.trans hFC
  have hbZF : Subgroup.zpowers b ≤ F := Subgroup.zpowers_le.mpr hbF
  have hbZC : Subgroup.zpowers b ≤ Subgroup.centralizer ({b} : Set G) :=
    Subgroup.zpowers_le.mpr hbC
  have hdec : ∀ f ∈ F, ∃ x ∈ Bs, ∃ z ∈ Subgroup.zpowers b, x * z = f := by
    intro f hf
    rw [← hFsup] at hf
    exact mem_sup_of_forall_comm (fun s hs t ht => hFcomm s (hBsF hs) t (hbZF ht)) hf
  obtain ⟨bC, hbCdef⟩ : ∃ x : ↥(Subgroup.centralizer ({b} : Set G)), (x : G) = b :=
    ⟨⟨b, hbC⟩, rfl⟩
  have hNdef : centralLine b = Subgroup.zpowers bC := by
    have hbC' : bC = ⟨b, hbC⟩ := Subtype.ext hbCdef
    rw [hbC']
    rfl
  have hbC3 : bC ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, hbCdef]
    exact hF3 b hbF
  have hbC1 : bC ≠ 1 := by
    intro h
    apply hb1
    rw [← hbCdef, h, Subgroup.coe_one]
  have hord : orderOf bC = 3 := orderOf_eq_prime hbC3 hbC1
  have hNcard : Nat.card (centralLine b) = 3 := by
    rw [hNdef, Nat.card_zpowers, hord]
  have hNp : IsPGroup 3 (centralLine b) :=
    IsPGroup.of_card (n := 1) (by rw [hNcard, pow_one])
  have hNc : centralLine b ≤ Subgroup.center (Subgroup.centralizer ({b} : Set G)) :=
    centralLine_le_center b
  have hNB : centralLine b ⊓ (Bs.subgroupOf (Subgroup.centralizer ({b} : Set G))) = ⊥ := by
    have hdvd : Nat.card ↥(centralLine b ⊓ (Bs.subgroupOf (Subgroup.centralizer ({b} : Set G))))
        ∣ 3 := by
      rw [← hNcard]; exact Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact Subgroup.card_eq_one.mp h1
    · exfalso
      have hK : centralLine b ⊓ (Bs.subgroupOf (Subgroup.centralizer ({b} : Set G))) =
          centralLine b :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (le_of_eq (by rw [h3, hNcard]))
      have hbN : bC ∈ centralLine b := by
        rw [hNdef]; exact Subgroup.mem_zpowers bC
      have hbBc : bC ∈ Bs.subgroupOf (Subgroup.centralizer ({b} : Set G)) := by
        have hmem : bC ∈ centralLine b ⊓ (Bs.subgroupOf (Subgroup.centralizer ({b} : Set G))) := by
          rw [hK]; exact hbN
        exact hmem.2
      apply hbB
      rw [← hbCdef]
      exact Subgroup.mem_subgroupOf.mp hbBc
  have hBcard : Nat.card (Bs.subgroupOf (Subgroup.centralizer ({b} : Set G))) = 3 ^ 2 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBsC).toEquiv).trans (hBs.trans (by norm_num))
  have hcomm : ∀ x ∈ Bs.subgroupOf (Subgroup.centralizer ({b} : Set G)),
      ∀ y ∈ Bs.subgroupOf (Subgroup.centralizer ({b} : Set G)), x * y = y * x := by
    intro x hx y hy
    apply Subtype.ext
    exact hFcomm _ (hBsF (Subgroup.mem_subgroupOf.mp hx)) _
      (hBsF (Subgroup.mem_subgroupOf.mp hy))
  have hexp : ∀ x ∈ Bs.subgroupOf (Subgroup.centralizer ({b} : Set G)), x ^ 3 = 1 := by
    intro x hx
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hF3 _ (hBsF (Subgroup.mem_subgroupOf.mp hx))
  have hBel : CFSG.Assembly.IsElemAbelian 3
      (Bs.subgroupOf (Subgroup.centralizer ({b} : Set G))) :=
    ⟨⟨⟨fun x y => Subtype.ext (hcomm x.1 x.2 y.1 y.2)⟩⟩, fun x hx => hexp x hx⟩
  have hc := (theta_plane_alpha_exact_prime_kernel_quotients Nat.prime_three
    (Bs.subgroupOf (Subgroup.centralizer ({b} : Set G))) hBel hBcard (centralLine b)
    (Or.inr ⟨hNc, hNp, hNB⟩)).2.2.2.2
  have hmapEq : (F.subgroupOf (Subgroup.centralizer ({b} : Set G))).map
      (QuotientGroup.mk' (centralLine b)) =
      (Bs.subgroupOf (Subgroup.centralizer ({b} : Set G))).map
        (QuotientGroup.mk' (centralLine b)) := by
    apply le_antisymm
    · intro w hw
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hw
      obtain ⟨x, hx, z, hz, hxz⟩ := hdec (y : G) (Subgroup.mem_subgroupOf.mp hy)
      have hzC : z ∈ Subgroup.centralizer ({b} : Set G) := hbZC hz
      have hxC : x ∈ Subgroup.centralizer ({b} : Set G) := hBsC hx
      refine Subgroup.mem_map.mpr ⟨⟨x, hxC⟩, Subgroup.mem_subgroupOf.mpr hx, ?_⟩
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply]
      apply QuotientGroup.eq.mpr
      have hyz : (⟨x, hxC⟩ : ↥(Subgroup.centralizer ({b} : Set G)))⁻¹ * y = ⟨z, hzC⟩ := by
        apply Subtype.ext
        show x⁻¹ * (y : G) = z
        rw [← hxz, inv_mul_cancel_left]
      rw [hyz, hNdef]
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
      apply Subtype.ext
      rw [Subgroup.coe_zpow, hbCdef]
      exact hk
    · exact Subgroup.map_mono (fun x hx =>
        Subgroup.mem_subgroupOf.mpr (hBsF (Subgroup.mem_subgroupOf.mp hx)))
  have hstar' : thetaAlpha 3 ((Bs.subgroupOf (Subgroup.centralizer ({b} : Set G))).map
      (QuotientGroup.mk' (centralLine b))) ≤
      aschbacherSolvableCore 3 (Subgroup.centralizer ({b} : Set G) ⧸ centralLine b) := by
    rw [← hmapEq]
    exact hstar
  exact (hc hNc hNp hNB).mpr hstar'

theorem not_starConditionAt {G : Type} [Group G] [Finite G] {F R : Subgroup G} {a b c : G}
    (hFe : CFSG.Assembly.IsElemAbelian 3 F) (hF27 : Nat.card F = 27)
    (haF : a ∈ F) (hbF : b ∈ F) (hcF : c ∈ F) (hb1 : b ≠ 1)
    (hB9 : Nat.card (Subgroup.zpowers a ⊔ Subgroup.zpowers c : Subgroup G) = 9)
    (hbB : b ∉ Subgroup.zpowers a ⊔ Subgroup.zpowers c)
    (hR1 : R ≠ ⊥) (hR2 : IsPGroup 2 R)
    (hRa : R ≤ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G)))
    (hRb : R ≤ Subgroup.centralizer ({b} : Set G))
    (hFR : F ≤ Subgroup.normalizer (R : Set G))
    (hRc : ∀ r ∈ R, c * r * c⁻¹ = r → r = 1)
    (hodd : Odd (Nat.card
      (inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set G))))) :
    ¬ StarConditionAt F b := by
  intro hstar
  unfold StarConditionAt at hstar
  have hFcomm : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hFe.1.is_comm.comm (⟨x, hx⟩ : F) ⟨y, hy⟩)
  have hF3 : ∀ x ∈ F, x ^ 3 = 1 := hFe.2
  have hFC : F ≤ Subgroup.centralizer ({b} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr (fun h hh => by
      rw [Set.mem_singleton_iff.mp hh]; exact hFcomm b hbF x hx)
  have haF' : Subgroup.zpowers a ⊔ Subgroup.zpowers c ≤ F :=
    sup_le (Subgroup.zpowers_le.mpr haF) (Subgroup.zpowers_le.mpr hcF)
  have hFsup := sup_zpowers_eq_of_card haF' hF27 hB9 hbF hbB
  have hH1 := ronan131b_H1 hFe haF' hFsup hbF hb1 hB9 hbB hstar
  obtain ⟨aC, haCe⟩ : ∃ x : ↥(Subgroup.centralizer ({b} : Set G)), (x : G) = a :=
    ⟨⟨a, hFC haF⟩, rfl⟩
  obtain ⟨cC, hcCe⟩ : ∃ x : ↥(Subgroup.centralizer ({b} : Set G)), (x : G) = c :=
    ⟨⟨c, hFC hcF⟩, rfl⟩
  have haBc : aC ∈ (Subgroup.zpowers a ⊔ Subgroup.zpowers c).subgroupOf
      (Subgroup.centralizer ({b} : Set G)) :=
    Subgroup.mem_subgroupOf.mpr (by
      rw [haCe]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers a))
  have hcBc : cC ∈ (Subgroup.zpowers a ⊔ Subgroup.zpowers c).subgroupOf
      (Subgroup.centralizer ({b} : Set G)) :=
    Subgroup.mem_subgroupOf.mpr (by
      rw [hcCe]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers c))
  have haC1 : aC ≠ 1 := by
    intro h
    have ha1 : a = 1 := by rw [← haCe, h, Subgroup.coe_one]
    have hBs_eq : Subgroup.zpowers a ⊔ Subgroup.zpowers c = Subgroup.zpowers c := by
      rw [ha1, Subgroup.zpowers_one_eq_bot, bot_sup_eq]
    have hB9' := hB9
    rw [hBs_eq, Nat.card_zpowers] at hB9'
    have hdv : orderOf c ∣ 3 := orderOf_dvd_of_pow_eq_one (hF3 c hcF)
    have hle := Nat.le_of_dvd (by norm_num) hdv
    omega
  have hθ := ronan131b_R_le_theta hRa hRb aC haCe
  have hcN : cC ∈ Subgroup.normalizer
      ((R.subgroupOf (Subgroup.centralizer ({b} : Set G)) :
        Subgroup ↥(Subgroup.centralizer ({b} : Set G))) :
        Set ↥(Subgroup.centralizer ({b} : Set G))) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hc := Subgroup.mem_normalizer_iff.mp (hFR hcF) (h : G)
    simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv,
      hcCe]
    exact hc
  have hRp2 : IsPGroup 2 (R.subgroupOf (Subgroup.centralizer ({b} : Set G))) :=
    IsPGroup.comap_subtype hR2
  have hΘodd : Odd (Nat.card (aschbacherSolvableCore 3 (Subgroup.centralizer ({b} : Set G)))) := by
    have hc : Nat.card (inSubgroup (aschbacherSolvableCore 3)
        (Subgroup.centralizer ({b} : Set G))) =
        Nat.card (aschbacherSolvableCore 3 (Subgroup.centralizer ({b} : Set G))) :=
      Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
    rw [← hc]
    exact hodd
  have hcent := ronan131b_centralizes hRp2 haBc haC1 hcBc hcN hθ hH1 hΘodd
  apply hR1
  rw [eq_bot_iff]
  intro r hr
  have hrC : r ∈ Subgroup.centralizer ({b} : Set G) := hRb hr
  have hrR : (⟨r, hrC⟩ : ↥(Subgroup.centralizer ({b} : Set G))) ∈
      R.subgroupOf (Subgroup.centralizer ({b} : Set G)) := Subgroup.mem_subgroupOf.mpr hr
  have hcomm := hcent _ hrR
  have hG : c * r = r * c := by
    have h := congrArg Subtype.val hcomm
    simp only [Subgroup.coe_mul, hcCe] at h
    exact h
  exact Subgroup.mem_bot.mpr (hRc r hr (by rw [hG, mul_inv_cancel_right]))

end CFSG.RankThree.PartTwo.Sec13.RonanStep131b
