module

public import CFSG.RankThree.PartTwo.Sec8.Item812Res4ProofLocal
import CFSG.RankThree.PartTwo.Sec8.Item812Res6ProofPaExp
import CFSG.RankThree.PartTwo.Sec8.Item812Res3ProofSU
import CFSG.RankThree.PartTwo.Sec11.Item113
import CFSG.RankThree.PartTwo.Sec6.Item612

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 (thetaQuotMulAut compAction InducesOuterTheta)
open CFSG.RankThree.PartTwo.KFacts (IsInnerAut isInnerAut_congr)
open CFSG.Assembly.RankThreeEven (projSp)
open CFSG.Assembly.LowTwoRank (StatedProj StatedSp)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open Item812Res3 (IsMaxPSub)

@[expose] noncomputable def sec8R {G : Type} [Group G] [Finite G] (Q X : Subgroup G) :
    Subgroup G :=
  Q ⊓ (X ⊔ Sec4.thetaQuotCentralizer X)

namespace Item812Res8

variable {G : Type} [Group G] [Finite G]

theorem card_inf_Y {A : Subgroup G} {c : G} {L : Subgroup G} {a b : G} {X Y : Subgroup G}
    {n : ℕ} (h : Sec8Final G A c L a b X Y n) : Nat.card (A ⊓ Y : Subgroup G) = 27 := by
  have hAab := h.mem_partTwoF.1
  have haA : a ∈ A := h.a_mem
  have ha1 : a ≠ 1 := h.a_ne_one
  have ha3 : a ^ 3 = 1 := hAab.2 a haA
  have hA81 : Nat.card A = 81 := h.card_eq
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAab.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have haY : a ∉ Y := Item812Res4.not_mem_of_mem_thetaComponentsAt ha3 ha1
    h.mem_thetaComponentsAt_Y h.item89_Y
  have hcomm : ∀ u ∈ Subgroup.zpowers a, ∀ v ∈ A ⊓ Y, u * v = v * u := by
    intro u hu v hv
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    exact hAc _ (A.zpow_mem haA j) v hv.1
  obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm
  have hinf : Subgroup.zpowers a ⊓ (A ⊓ Y) = ⊥ := by
    have hao : orderOf a = 3 := orderOf_eq_prime ha3 ha1
    have hdvd : Nat.card (Subgroup.zpowers a ⊓ (A ⊓ Y) : Subgroup G) ∣ 3 := by
      have := Subgroup.card_dvd_of_le (inf_le_left : Subgroup.zpowers a ⊓ (A ⊓ Y) ≤ _)
      rwa [Nat.card_zpowers, hao] at this
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have heq : Subgroup.zpowers a ⊓ (A ⊓ Y) = Subgroup.zpowers a :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, Nat.card_zpowers, hao])
      have : a ∈ Subgroup.zpowers a ⊓ (A ⊓ Y) := by
        rw [heq]
        exact Subgroup.mem_zpowers a
      exact haY this.2.2
  rw [Item812Res6.zpowers_sup_inf_eq h, hinf, Subgroup.card_bot, mul_one, hA81,
    Nat.card_zpowers, orderOf_eq_prime ha3 ha1] at hcard
  omega

theorem card_sec8B {A : Subgroup G} {c : G} {L : Subgroup G} {a b : G} {X Y : Subgroup G}
    {n : ℕ} (h : Sec8Final G A c L a b X Y n) : Nat.card (sec8B A X) = 27 := by
  obtain ⟨x, hxA, hxk⟩ := h.mem_pairOmega.2.2.2.1
  have hxout : InducesOuterTheta x X := by
    rcases hxk with hk | hk
    · exact KFacts.InducesStdKind.inducesOuterTheta X hk (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta X hk (by decide)
  exact Item812Res3.card_sec8B_eq_of_projSp h.toTheoremFourHyp.localRank_three.le
    h.mem_partTwoF h.card_eq h.isGammaIndex.1 h.isGammaIndex.2.1 h.pairRel.2.2.1 h.item89_X
    hxA hxout

end Item812Res8

open Item812Res8

@[expose] def Fin812RStruct : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X Y : Subgroup G) (n : ℕ), Sec8Final G A c L a b X Y n →
    ∀ Pa Q : Subgroup G, IsMaxPSub 3 Pa (Subgroup.centralizer ({a} : Set G)) → A ≤ Pa →
      Subgroup.zpowers a ⊔ (Pa ⊓ Y) = Pa → sec8B A X = A ⊓ Y →
      IsMaxPSub 3 Q (Subgroup.centralizer (sec8B A X : Set G)) →
      Pa ≤ Subgroup.normalizer (Q : Set G) →
      (∀ x ∈ sec8R Q X, ∀ y ∈ sec8R Q X, x * y = y * x) ∧ Nat.card (sec8R Q X) = 3 ^ 6 ∧
        ∀ x ∈ sec8R Q X, x ^ 9 = 1

@[expose] def Fin812QOmega : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X Y : Subgroup G) (n : ℕ), Sec8Final G A c L a b X Y n →
    ∀ Pa Q : Subgroup G, IsMaxPSub 3 Pa (Subgroup.centralizer ({a} : Set G)) → A ≤ Pa →
      Subgroup.zpowers a ⊔ (Pa ⊓ Y) = Pa → sec8B A X = A ⊓ Y →
      IsMaxPSub 3 Q (Subgroup.centralizer (sec8B A X : Set G)) →
      Pa ≤ Subgroup.normalizer (Q : Set G) →
      ∀ x ∈ Q, x ^ 3 = 1 → x ∈ A

@[expose] def Fin812RWeak : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X Y : Subgroup G) (n : ℕ), Sec8Final G A c L a b X Y n →
    ∀ Pa Q : Subgroup G, IsMaxPSub 3 Pa (Subgroup.centralizer ({a} : Set G)) → A ≤ Pa →
      Subgroup.zpowers a ⊔ (Pa ⊓ Y) = Pa → sec8B A X = A ⊓ Y →
      IsMaxPSub 3 Q (Subgroup.centralizer (sec8B A X : Set G)) →
      Pa ≤ Subgroup.normalizer (Q : Set G) →
      ∀ g : G, (sec8R Q X).map (MulAut.conj g).toMonoidHom ≤ Q →
        (sec8R Q X).map (MulAut.conj g).toMonoidHom = sec8R Q X

theorem fin812QR_of (h45 : Sec4.Item4_5) (h84 : Pair84A) (hS : Fin812RStruct)
    (hO : Fin812QOmega) (hWk : Fin812RWeak) : Fin812QR := by
  intro G _ _ A c L a b X Y n h Pa Q hPa hAPa hpaeq hBeq hQ hPaQ
  classical
  obtain ⟨hRc, hRcard, hRpow⟩ := hS G A c L a b X Y n h Pa Q hPa hAPa hpaeq hBeq hQ hPaQ
  have hOm := hO G A c L a b X Y n h Pa Q hPa hAPa hpaeq hBeq hQ hPaQ
  have hRw := hWk G A c L a b X Y n h Pa Q hPa hAPa hpaeq hBeq hQ hPaQ
  refine ⟨sec8R Q X, ?_, hRc, hRcard, hRpow, ?_, ?_, hOm, hRw⟩
  rotate_left
  ·
    have hAab := h.mem_partTwoF.1
    have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
      congrArg Subtype.val (hAab.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    have hAB : A ≤ Subgroup.centralizer (sec8B A X : Set G) := fun x hx =>
      Subgroup.mem_centralizer_iff.mpr fun y hy => hAc y (Item812Res4.b_le_a hy) x hx
    have hQA := hQ.2.2 _ (Item812Res4.isPGroup_sup hQ.2.1
      (Item812Res4.isPGroup_of_isElemAbelian hAab) (hAPa.trans hPaQ)) le_sup_left
      (sup_le hQ.1 hAB)
    have hAQ : A ≤ Q := hQA ▸ le_sup_right
    exact le_inf (Item812Res4.b_le_a.trans hAQ) inf_le_right
  ·
    intro x hx hx3
    exact ⟨hOm x hx.1 hx3, hx.2⟩
  ·
    have hAab := h.mem_partTwoF.1
    have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
      congrArg Subtype.val (hAab.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    have haA : a ∈ A := h.a_mem
    have hAB : A ≤ Subgroup.centralizer (sec8B A X : Set G) := fun x hx =>
      Subgroup.mem_centralizer_iff.mpr fun y hy => hAc y (Item812Res4.b_le_a hy) x hx
    have hQA := hQ.2.2 _ (Item812Res4.isPGroup_sup hQ.2.1
      (Item812Res4.isPGroup_of_isElemAbelian hAab) (hAPa.trans hPaQ)) le_sup_left
      (sup_le hQ.1 hAB)
    have hAQ : A ≤ Q := hQA ▸ le_sup_right
    have haQ : a ∈ Q := hAQ haA
    have hbA : b ∈ A := h.isGammaIndex.1
    have hb1 : b ≠ 1 := h.isGammaIndex.2.1
    have hb3 : b ^ 3 = 1 := hAab.2 b hbA
    have hXb : X ∈ thetaComponentsAt 3 b := h.pairRel.2.2.1
    have hbB : b ∈ sec8B A X :=
      ⟨hbA, Subgroup.mem_sup_right (Sec6.mem_thetaQuotCentralizer_of_mem_thetaComponentsAt hXb)⟩
    have hQb : Q ≤ Subgroup.centralizer ({b} : Set G) := fun g hg =>
      Subgroup.mem_centralizer_singleton_iff.mpr
        ((Subgroup.mem_centralizer_iff.mp (hQ.1 hg) b hbB).symm)
    have hQN : Q ≤ Subgroup.normalizer (X : Set G) :=
      Sec11.le_normalizer_of_isPGroup_of_le_centralizer h45 h.toTheoremFourHyp hb3 hb1 hQ.2.1
        hQb X hXb
    have haout : InducesOuterTheta a X := by
      rcases h84 G A c L a b X n h.toSec8Pair with hk | hk
      · exact KFacts.InducesStdKind.inducesOuterTheta X hk (by decide)
      · exact KFacts.InducesStdKind.inducesOuterTheta X hk (by decide)
    have haR : a ∉ sec8R Q X := by
      rintro ⟨-, haXC⟩
      exact haout.2 ((Item812Res2.mem_sup_thetaQuotCentralizer_iff haout.1).mp haXC)
    set F := GaloisField 2 3 with hFdef
    set P := StatedProj (StatedSp 2 F) with hPdef
    set e : X ⧸ aschbacherSolvableCore 3 X ≃* P :=
      h.item89_X.some.trans (Sec4.projSpEquivStatedProj 2 F) with he
    set φ : Q →* CFSG.ComponentClassification.OuterAutomorphisms.Outer P :=
      (QuotientGroup.mk' (inner P)).comp ((KFacts.inducedAutHom X e).comp
        (Subgroup.inclusion hQN)) with hφ
    have hφker : ∀ g : Q, φ g = 1 ↔ (g : G) ∈ X ⊔ Sec4.thetaQuotCentralizer X := by
      intro g
      rw [Item812Res2.mem_sup_thetaQuotCentralizer_iff (hQN g.2), hφ, MonoidHom.comp_apply,
        QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      change IsInnerAut (MulAut.congr e (thetaQuotMulAut X (compAction X ⟨g, hQN g.2⟩))) ↔ _
      exact isInnerAut_congr e _
    have hRker : sec8R Q X = φ.ker.map Q.subtype := by
      ext x
      constructor
      · rintro ⟨hxQ, hxXC⟩
        exact ⟨⟨x, hxQ⟩, (hφker ⟨x, hxQ⟩).mpr hxXC, rfl⟩
      · rintro ⟨g, hg, rfl⟩
        exact ⟨g.2, (hφker g).mp hg⟩
    have hRcard' : Nat.card (sec8R Q X) = Nat.card φ.ker := by
      rw [hRker, Subgroup.card_map_of_injective Q.subtype_injective]
    have hK : Nat.card F = 2 ^ 3 := GaloisField.card 2 3 (by norm_num)
    have : CharP F 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
        (by norm_num) hK
    obtain ⟨Fr, hFr, hord, hzp, -, -⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
        Nat.prime_two (by norm_num) hK
    obtain ⟨-, -, -, -, -, hcardOut, -⟩ :=
      CFSG.ComponentClassification.UnbalancedCatalog.SpChain.exceptionalAut_structure
        (by norm_num) hFr hord hzp
    have hrange3 : Nat.card φ.range ≤ 3 := by
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hp : IsPGroup 3 φ.range :=
        hQ.2.1.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
      have h6 : Nat.card φ.range ∣ 6 := by
        have := Subgroup.card_subgroup_dvd_card φ.range
        rwa [hcardOut] at this
      rw [hk] at h6 ⊢
      rcases k with _ | _ | k
      · norm_num
      · norm_num
      · exfalso
        have h9 : 9 ∣ 3 ^ (k + 2) := ⟨3 ^ k, by ring⟩
        have := h9.trans h6
        norm_num at this
    have hQcard : Nat.card Q ≤ 3 * Nat.card (sec8R Q X) := by
      have h1 := Subgroup.card_mul_index φ.ker
      rw [Subgroup.index_ker] at h1
      rw [hRcard', ← h1]
      nlinarith [Nat.card_pos (α := φ.ker)]
    have hRQ : sec8R Q X ≤ Q := inf_le_left
    have hle : sec8R Q X ⊔ Subgroup.zpowers a ≤ Q := sup_le hRQ ((Subgroup.zpowers_le).mpr haQ)
    have hlt : sec8R Q X < sec8R Q X ⊔ Subgroup.zpowers a :=
      lt_of_le_of_ne le_sup_left fun heq =>
        haR (heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers a))
    obtain ⟨i, hi⟩ := IsPGroup.iff_card.mp (hQ.2.1.to_le hRQ)
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp (hQ.2.1.to_le hle)
    have hdvd : Nat.card (sec8R Q X) ∣ Nat.card (sec8R Q X ⊔ Subgroup.zpowers a : Subgroup G) :=
      Subgroup.card_dvd_of_le le_sup_left
    have hne : Nat.card (sec8R Q X) ≠
        Nat.card (sec8R Q X ⊔ Subgroup.zpowers a : Subgroup G) := fun hc =>
      (ne_of_lt hlt) (Subgroup.eq_of_le_of_card_ge le_sup_left hc.symm.le)
    rw [hi, hj] at hdvd hne
    have hij : i < j := by
      have := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 3)).mp hdvd
      rcases this.lt_or_eq with h' | h'
      · exact h'
      · exact absurd (by rw [h']) hne
    have hge : 3 * Nat.card (sec8R Q X) ≤
        Nat.card (sec8R Q X ⊔ Subgroup.zpowers a : Subgroup G) := by
      rw [hi, hj]
      calc 3 * 3 ^ i = 3 ^ (i + 1) := by ring
        _ ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) hij
    exact Subgroup.eq_of_le_of_card_ge hle (hQcard.trans hge)

end CFSG.RankThree.PartTwo.Sec8
