module

import CFSG.RankThree.GroupTheory.ComponentCubeObstruction
import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowAmbient
import CFSG.RankThree.GroupTheory.ThetaQuotientTransport
public import CFSG.RankThree.PartTwo.Sec12.Item125Act

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def KS125TypeCInvol : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X → Sec4.IsSLThreePi X →
    ∀ x : X, x ∉ Subgroup.center X → x ^ 3 = 1 →
    ∀ Y : Subgroup (MulAut X), CFSG.Assembly.IsElemAbelian 3 Y → Nat.card Y = 9 →
      MulAut.conj x ∈ Y → (∀ σ ∈ Y, σ x = x) →
      ∃ σ ∈ Y, σ ≠ 1 ∧ ∃ P : Subgroup X, P ≠ ⊥ ∧ IsPGroup 2 P ∧ ∀ p ∈ P, σ p ∈ P

namespace Item125Diag

variable {G : Type} [Group G] [Finite G]

theorem false_of_E27_le_of_le_card (hFE : partTwoF G = partTwoE G) {L : Subgroup G}
    (hperf : commutator (L ⧸ aschbacherSolvableCore 3 L) = ⊤)
    (hZ : Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) = 3)
    (hev : 2 ∣ Nat.card (L ⧸ aschbacherSolvableCore 3 L)) {X : Subgroup G}
    (hX : CFSG.Assembly.IsElemAbelian 3 X) (h27 : 27 ≤ Nat.card X)
    (hXC : X ≤ Sec4.thetaQuotCentralizer L) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hX3 : IsPGroup 3 X := fun x => ⟨1, Subtype.ext (by simpa using hX.2 x x.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hX3
  have hk3 : 3 ≤ k := by
    by_contra h
    push Not at h
    have : 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hdvd : 3 ^ 3 ∣ Nat.card X := hk ▸ Nat.pow_dvd_pow 3 hk3
  obtain ⟨D, hD27, -, hDX⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_three
    (H := ⊥) (by rw [Subgroup.card_bot]; exact one_dvd _) hdvd bot_le
  have hDe : CFSG.Assembly.IsElemAbelian 3 D := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => hX.2 x (hDX hx)⟩
    have h := congrArg Subtype.val (hX.1.is_comm.comm ⟨a, hDX a.2⟩ ⟨b, hDX b.2⟩)
    simpa using h
  exact false_of_E27_le_thetaQuotCentralizer hFE hperf hZ hev hDe (by rw [hD27]; norm_num)
    (hDX.trans hXC)

theorem false_of_E81 (hK : KS125TypeCInvol) (hFE : partTwoF G = partTwoE G) {c : G}
    {L : Subgroup G} (hL : L ∈ thetaComponentsAt 3 c)
    (hZ : Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) = 3)
    (hSL : Sec4.IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L))
    {F : Subgroup G} (hF : CFSG.Assembly.IsElemAbelian 3 F) (hF81 : Nat.card F = 81)
    (hFN : F ≤ Subgroup.normalizer (L : Set G)) {y : L} (hyF : (y : G) ∈ F)
    (hyZ : QuotientGroup.mk' (aschbacherSolvableCore 3 L) y ∉
      Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) (hy3 : (y : G) ^ 3 = 1)
    (hcF : c ∈ F) (hcC : c ∈ Sec4.thetaQuotCentralizer L) (hc3 : orderOf c = 3) {z : G}
    (hzF : z ∈ F) (hzC : z ∈ Sec4.thetaQuotCentralizer L) (hz : z ∉ Subgroup.zpowers c) :
    False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := aschbacherSolvableCore 3 L with hN
  set π := QuotientGroup.mk' N with hπ
  have hq := isQuasisimple_thetaQuot_of_mem hL
  have hperf : commutator (L ⧸ N) = ⊤ := by
    have h1 := hq.1
    rwa [Group.isPerfect_def] at h1
  have hev := KFacts.two_dvd_card_of_item122_type (Or.inl hSL)
  have hcomm : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hF.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  set B := F ⊓ Sec4.thetaQuotCentralizer L with hB
  have hBe : CFSG.Assembly.IsElemAbelian 3 B :=
    ⟨⟨⟨fun a b => Subtype.ext (hcomm _ a.2.1 _ b.2.1)⟩⟩, fun x hx => hF.2 x hx.1⟩
  have hB3 : IsPGroup 3 B := fun x => ⟨1, Subtype.ext (by simpa using hBe.2 x x.2)⟩
  have hzo : orderOf z = 3 :=
    orderOf_eq_prime (hF.2 z hzF) fun h => hz (h ▸ Subgroup.one_mem _)
  have hcz : Nat.card (Subgroup.zpowers c ⊔ Subgroup.zpowers z : Subgroup G) = 9 := by
    have hcen : z ∈ Subgroup.centralizer ((Subgroup.zpowers c : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      exact (Commute.zpow_left (hcomm c hcF z hzF : Commute c z) k).eq
    obtain ⟨h9, -, -⟩ := card_sup_zpowers_of_disjoint hcen inferInstance
      (fun w hw => by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hF.2 c hcF, one_zpow])
      hzo (inf_zpowers_eq_bot_of_not_mem hzo hz)
    rwa [Nat.card_zpowers, hc3] at h9
  have hBle : Subgroup.zpowers c ⊔ Subgroup.zpowers z ≤ B :=
    sup_le (Subgroup.zpowers_le.mpr ⟨hcF, hcC⟩) (Subgroup.zpowers_le.mpr ⟨hzF, hzC⟩)
  have hB9 : Nat.card B = 9 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hB3
    have hdvd : Nat.card B ∣ 81 := hF81 ▸ Subgroup.card_dvd_of_le inf_le_left
    have h9 : 9 ≤ Nat.card B := hcz ▸ Subgroup.card_le_of_le hBle
    have hlt : Nat.card B < 27 := by
      by_contra h
      push Not at h
      exact false_of_E27_le_of_le_card hFE hperf hZ hev hBe h inf_le_right
    rw [hk] at h9 hlt ⊢
    have h1 : 3 ^ 2 ≤ 3 ^ k := by simpa using h9
    have h2 : 3 ^ k < 3 ^ 3 := by simpa using hlt
    have h3 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h1
    have h4 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).mp h2
    have hk2 : k = 2 := by omega
    rw [hk2]
    norm_num
  set Y : Subgroup (MulAut (L ⧸ N)) :=
    (F.subgroupOf (Subgroup.normalizer (L : Set G))).map (thetaBarAct L) with hY
  have hmemY : ∀ f (hf : f ∈ F), thetaBarAct L ⟨f, hFN hf⟩ ∈ Y := fun f hf =>
    ⟨⟨f, hFN hf⟩, Subgroup.mem_subgroupOf.mpr hf, rfl⟩
  have hYe : CFSG.Assembly.IsElemAbelian 3 Y := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun σ hσ => ?_⟩
    · obtain ⟨a', ha', ha⟩ := a.2
      obtain ⟨b', hb', hb⟩ := b.2
      apply Subtype.ext
      change (a : MulAut (L ⧸ N)) * b = b * a
      rw [← ha, ← hb, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hcomm _ (Subgroup.mem_subgroupOf.mp ha') _
        (Subgroup.mem_subgroupOf.mp hb'))
    · obtain ⟨a', ha', rfl⟩ := hσ
      rw [← map_pow]
      have h3 : a' ^ 3 = 1 := Subtype.ext (by simpa using hF.2 _ (Subgroup.mem_subgroupOf.mp ha'))
      rw [h3, map_one]
  have hYcard : Nat.card Y = 9 := by
    set K := F.subgroupOf (Subgroup.normalizer (L : Set G)) with hK
    have h1 : (thetaBarAct L).ker.relIndex K = Nat.card Y := Subgroup.relIndex_ker K _
    have h2 : (thetaBarAct L).ker.relIndex K *
        Nat.card ((thetaBarAct L).ker ⊓ K : Subgroup _) = Nat.card K :=
      Subgroup.relIndex_mul_card _ _
    have h3 : Nat.card ((thetaBarAct L).ker ⊓ K : Subgroup _) = 9 := by
      have hmap : ((thetaBarAct L).ker ⊓ K).map (Subgroup.normalizer (L : Set G)).subtype = B := by
        ext g
        constructor
        · rintro ⟨g', ⟨hg'k, hg'F⟩, rfl⟩
          exact ⟨Subgroup.mem_subgroupOf.mp hg'F,
            (mem_thetaQuotCentralizer_iff_thetaBarAct g'.2).mpr hg'k⟩
        · rintro ⟨hgF, hgC⟩
          exact ⟨⟨g, hFN hgF⟩, ⟨(mem_thetaQuotCentralizer_iff_thetaBarAct (hFN hgF)).mp hgC,
            Subgroup.mem_subgroupOf.mpr hgF⟩, rfl⟩
      rw [← hB9, ← hmap,
        Subgroup.card_map_of_injective (Subgroup.normalizer (L : Set G)).subtype_injective]
    have h4 : Nat.card K = 81 := by
      rw [← hF81]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFN).toEquiv
    rw [h1, h3, h4] at h2
    omega
  have hconjY : MulAut.conj (π y) ∈ Y := by
    have h := hmemY _ hyF
    rwa [thetaBarAct_of_mem y.2] at h
  have hfixY : ∀ σ ∈ Y, σ (π y) = π y := by
    rintro σ ⟨f, hf, rfl⟩
    have hfF : (f : G) ∈ F := Subgroup.mem_subgroupOf.mp hf
    rw [thetaBarAct_mk]
    congr 1
    apply Subtype.ext
    rw [Sec4.normalizerMonoidHom_apply_coe, hcomm _ hfF _ hyF, mul_inv_cancel_right]
  have hy3' : π y ^ 3 = 1 := by
    rw [← map_pow]
    have h3 : y ^ 3 = 1 := Subtype.ext (by simpa using hy3)
    rw [h3, map_one]
  obtain ⟨σ, hσY, hσ1, P, hP1, hP2, hPσ⟩ := hK _ hq hSL (π y) hyZ hy3' Y hYe hYcard hconjY hfixY
  obtain ⟨f₀', hf₀', rfl⟩ := hσY
  set f₀ : G := (f₀' : G) with hf₀def
  have hf₀F : f₀ ∈ F := Subgroup.mem_subgroupOf.mp hf₀'
  have hf₀B : f₀ ∉ B := fun h => hσ1 ((mem_thetaQuotCentralizer_iff_thetaBarAct f₀'.2).mp h.2)
  have hf₀o : orderOf f₀ = 3 :=
    orderOf_eq_prime (hF.2 f₀ hf₀F) fun h => hf₀B (h ▸ Subgroup.one_mem _)
  have hf₀cen : f₀ ∈ Subgroup.centralizer (B : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact hcomm _ hh.1 _ hf₀F
  obtain ⟨hF₀27, hF₀c, hF₀e⟩ := card_sup_zpowers_of_disjoint hf₀cen hBe.1 hBe.2 hf₀o
    (inf_zpowers_eq_bot_of_not_mem hf₀o hf₀B)
  set F₀ := B ⊔ Subgroup.zpowers f₀ with hF₀
  have hF₀F : F₀ ≤ F := sup_le inf_le_left (Subgroup.zpowers_le.mpr hf₀F)
  have hF₀N : F₀ ≤ Subgroup.normalizer (L : Set G) := hF₀F.trans hFN
  have hσk : ∀ k : ℕ, ∀ p ∈ P, (thetaBarAct L f₀' ^ k) p ∈ P := by
    intro k
    induction k with
    | zero => intro p hp; simpa using hp
    | succ k ih =>
      intro p hp
      rw [pow_succ, MulAut.mul_apply]
      exact ih _ (hPσ p hp)
  have hBN : Subgroup.zpowers f₀ ≤ Subgroup.normalizer (B : Set G) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_normalizer_fintype fun b hb => by
      rw [hcomm _ hf₀F _ hb.1, mul_inv_cancel_right]
      exact hb
  have hF₀P : ∀ g (hg : g ∈ F₀), ∀ p ∈ P, thetaBarAct L ⟨g, hF₀N hg⟩ p ∈ P := by
    intro g hg p hp
    have hg' : g ∈ ((B ⊔ Subgroup.zpowers f₀ : Subgroup G) : Set G) := hg
    rw [Subgroup.coe_mul_of_right_le_normalizer_left B _ hBN] at hg'
    obtain ⟨b, hb, w, hw, hbw⟩ := hg'
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hw)
    have hbN : b ∈ Subgroup.normalizer (L : Set G) := hFN hb.1
    have e1 : (⟨g, hF₀N hg⟩ : Subgroup.normalizer (L : Set G)) = ⟨b, hbN⟩ * f₀' ^ k := by
      apply Subtype.ext
      change g = b * (f₀' : G) ^ k
      rw [← hbw, ← hk]
    rw [e1, map_mul, map_pow, (mem_thetaQuotCentralizer_iff_thetaBarAct hbN).mp hb.2, one_mul]
    exact hσk k p hp
  set Phat : Subgroup G := (P.comap π).map L.subtype with hPhat
  have hPhatcard : Nat.card Phat = Nat.card N * Nat.card P := by
    rw [hPhat, Subgroup.card_map_of_injective L.subtype_injective]
    exact QuotientGroup.card_preimage_mk N (P : Set (L ⧸ N))
  have hPhatN : F₀ ≤ Subgroup.normalizer (Phat : Set G) := by
    intro g hg
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨x₀, hx₀, rfl⟩ := hx
    have hgx : g * (x₀ : G) * g⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hF₀N hg) _).mp x₀.2
    refine ⟨⟨_, hgx⟩, Subgroup.mem_comap.mpr ?_, rfl⟩
    have h1 : π ⟨_, hgx⟩ = thetaBarAct L ⟨g, hF₀N hg⟩ (π x₀) := by
      rw [thetaBarAct_mk]
      rfl
    rw [h1]
    exact hF₀P g hg _ (Subgroup.mem_comap.mp hx₀)
  have h2P : 2 ∣ Nat.card P := by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hP2
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [pow_zero, Subgroup.card_eq_one] at hm
      exact hP1 hm
    rw [hm]
    exact dvd_pow_self 2 hm0
  have hcop : Nat.Coprime 3 (Nat.card Phat) := by
    rw [hPhatcard]
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hP2
    rw [hm]
    exact Nat.Coprime.mul_right ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      three_not_dvd_card_aschbacherSolvableCore) (Nat.Coprime.pow_right m (by norm_num))
  have h2 : 2 ∣ Nat.card Phat := by
    rw [hPhatcard]
    exact h2P.mul_left _
  have hF₀3 : IsPGroup 3 F₀ := fun x => ⟨1, Subtype.ext (by simpa using hF₀e x x.2)⟩
  obtain ⟨S, hSN, hS0⟩ :=
    CFSG.SignalizerFunctor.Helpers.normalized_subgroup_invariant_sylow_nontrivial 3 2
      Nat.prime_three Nat.prime_two F₀ Phat hF₀3 hPhatN hcop h2
  obtain ⟨w, hwF, hwF₀⟩ : ∃ w ∈ F, w ∉ F₀ := by
    by_contra hcon
    push Not at hcon
    have h := Subgroup.card_le_of_le (show F ≤ F₀ from hcon)
    rw [hF81, hF₀27, hB9] at h
    omega
  have hwo : orderOf w = 3 :=
    orderOf_eq_prime (hF.2 w hwF) fun h => hwF₀ (h ▸ Subgroup.one_mem _)
  have hwc : w ∈ Subgroup.centralizer (F₀ : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact hcomm _ (hF₀F hh) _ hwF
  exact false_of_le_E81 hFE ⟨hF₀c, hF₀e⟩ (by rw [hF₀27, hB9]) hS0
    (S.isPGroup'.map Phat.subtype) hSN hwc hwo hwF₀

end Item125Diag

end CFSG.RankThree.PartTwo.Sec12
