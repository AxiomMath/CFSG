module

public import CFSG.RankThree.PartTwo.Sec11.KS11Lie3ProofThree
public import CFSG.RankThree.PartTwo.Sec12.Item125Act
public import CFSG.RankThree.PartTwo.Sec11.Item1115Proof
public import CFSG.RankThree.PartTwo.Sec11.Item1117ProofBasic
public import CFSG.RankThree.PartTwo.Sec11.Item119K

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4

@[expose] def InvElt1118For (F : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (Z : Type) [Group Z] [Finite Z],
    (∃ (X : Type) (_ : Group X), F X ∧ Nonempty (Z ≃* _root_.commutator X)) →
    ∀ (z v g : Z) (J : Subgroup Z), MulAut.conj z ^ 3 = 1 →
      J ∈ thetaComponentsIn (Item426.fixSub (MulAut.conj z)) →
      IsType424 (J ⧸ aschbacherSolvableCore 3 J) →
      v ∈ J → v ^ 3 = 1 → v ≠ 1 →
      (∃ k : ℕ, g ^ 3 ^ k = 1) → g * v = v * g →
      g * z * g⁻¹ * z⁻¹ ∈ Subgroup.zpowers v → g * z ≠ z * g →
        ∃ n : Z, n ^ 3 = 1 ∧ n * z * n⁻¹ = g * z * g⁻¹ ∧ n * v = v * n

@[expose] def InvElt1118G2Ss : Prop :=
  InvElt1118For fun X _ => ∃ (q : TauCeti.PrimePower)
    (hq : (TauCeti.LieTypeIndex.G2 q).Valid), q.p ≠ 3 ∧
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group)

@[expose] def InvElt1118D4Even : Prop :=
  InvElt1118For fun X _ => ∃ (q : TauCeti.PrimePower)
    (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid), q.p = 2 ∧
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group)

namespace Item1117Res3Proof

section Generic

theorem pow_conj_eq_of_conj_eq {G : Type*} [Group G] {w c u : G} (hwc : w * c * w⁻¹ = u * c)
    (hwu : w * u = u * w) (k : ℕ) : w ^ k * c * (w ^ k)⁻¹ = u ^ k * c := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hwu' : Commute w (u ^ k) := (Commute.pow_right hwu k)
    calc w ^ (k + 1) * c * (w ^ (k + 1))⁻¹ = w * (w ^ k * c * (w ^ k)⁻¹) * w⁻¹ := by
          rw [pow_succ']; group
      _ = w * u ^ k * w⁻¹ * (w * c * w⁻¹) := by rw [ih]; group
      _ = u ^ k * (u * c) := by rw [hwc, hwu'.eq, mul_inv_cancel_right]
      _ = u ^ (k + 1) * c := by rw [pow_succ, mul_assoc]

end Generic

section Lift

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d x s r g : G}

theorem exists_orderOf_eq_three_of_lift (h117 : Item117) (h : Sec11Data G A c L a R Y d x s r g)
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) {u : Y ⧸ aschbacherSolvableCore 3 Y}
    (hu : ∀ e (he : e ∈ A), Sec12.thetaBarAct Y ⟨e, hAY he⟩ u = u)
    (hgu : (QuotientGroup.mk' (aschbacherSolvableCore 3 Y) ⟨g, h.g_mem.1⟩ * u) ^ 3 = 1) :
    ∃ g₀ ∈ Y ⊓ Subgroup.normalizer (A : Set G), orderOf g₀ = 3 ∧ ∃ z ∈ A, g₀ * z * g₀⁻¹ ≠ z := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA3 : IsPGroup 3 A := fun z => ⟨1, Subtype.ext (by
    simpa using h.mem_partTwoF.1.2 z z.2)⟩
  obtain ⟨y, hy, hyA⟩ := Sec12.exists_lift_fixed hA3 hAY u hu
  have hgY : g ∈ Y := h.g_mem.1
  have hgW : g ∈ Subgroup.normalizer (A : Set G) := h.g_mem.2
  set w : G := g * y with hw
  have hwY : w ∈ Y := Y.mul_mem hgY y.2
  have hyc : ∀ e ∈ A, e * (y : G) = y * e := fun e he => by
    calc e * (y : G) = (e * y * e⁻¹) * e := by group
      _ = y * e := by rw [hyA e he]
  have hyW : (y : G) ∈ Subgroup.normalizer (A : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun z hz => ?_
    rw [← hyc z hz, mul_inv_cancel_right]
    exact hz
  have hwW : w ∈ Subgroup.normalizer (A : Set G) := mul_mem hgW hyW
  have hw3 : (⟨w, hwY⟩ : Y) ^ 3 ∈ aschbacherSolvableCore 3 Y := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    have e1 : ((⟨w, hwY⟩ : Y) : Y ⧸ aschbacherSolvableCore 3 Y) =
        QuotientGroup.mk' (aschbacherSolvableCore 3 Y) ⟨g, hgY⟩ * u := by
      rw [← hy, ← map_mul]
      rfl
    rw [e1]
    exact hgu
  set t := orderOf ((⟨w, hwY⟩ : Y) ^ 3) with ht
  have ht3 : ¬ 3 ∣ t := by
    intro h3
    have h1 : t ∣ Nat.card (aschbacherSolvableCore 3 Y) := by
      rw [ht, ← Subgroup.orderOf_mk _ hw3]
      exact orderOf_dvd_natCard _
    exact three_not_dvd_card_aschbacherSolvableCore (dvd_trans h3 h1)
  have hwt : w ^ (3 * t) = 1 := by
    have h1 := pow_orderOf_eq_one ((⟨w, hwY⟩ : Y) ^ 3)
    rw [← ht, ← pow_mul] at h1
    simpa using congrArg Subtype.val h1
  have hAe := h.mem_partTwoF.1
  have hcA : c ∈ A := h.mem_A
  have hdA : d ∈ A := Item1117Proof.d_mem_A h
  set u₀ := g * c * g⁻¹ * c⁻¹ with hu₀
  have hu₀d : u₀ ∈ Subgroup.zpowers d := Item1117Proof.conj_g_c_mem h117 h
  have hd3o : orderOf d = 3 := Item1117Proof.orderOf_d h
  obtain ⟨k, hk⟩ := h.pow_eq_one
  have hgd : g * d = d * g := Sec12.commute_of_conj_mem_zpowers hd3o
    ((Subgroup.mem_normalizer_iff.mp (Item1115Proof.W_le_normalizer_d h117 h hgW) d).mp
      (Subgroup.mem_zpowers d)) hk
  have hwd : w * d = d * w := by
    rw [hw, mul_assoc, ← hyc d hdA, ← mul_assoc, hgd, mul_assoc]
  have hwc : w * c * w⁻¹ = u₀ * c := by
    have hyc' : (y : G) * c * (y : G)⁻¹ = c := by
      rw [← hyc c hcA, mul_inv_cancel_right]
    calc w * c * w⁻¹ = g * ((y : G) * c * (y : G)⁻¹) * g⁻¹ := by rw [hw]; group
      _ = g * c * g⁻¹ := by rw [hyc']
      _ = u₀ * c := by rw [hu₀]; group
  have hwu₀ : w * u₀ = u₀ * w := by
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hu₀d
    rw [← hn]
    exact (Commute.zpow_right hwd n).eq
  have hmove : w ^ t * c * (w ^ t)⁻¹ ≠ c := by
    intro heq
    rw [pow_conj_eq_of_conj_eq hwc hwu₀ t, mul_eq_right] at heq
    have hu₀1 : u₀ ≠ 1 := by
      intro h1
      apply h.g_not_mem
      apply Sec10.mem_normalizer_zpowers_of_conj_mem
      have : g * c * g⁻¹ = c := by
        calc g * c * g⁻¹ = u₀ * c := by rw [hu₀]; group
          _ = c := by rw [h1, one_mul]
      rw [this]
      exact Subgroup.mem_zpowers c
    have hu₀3 : orderOf u₀ = 3 := by
      have h1 := orderOf_dvd_of_mem_zpowers hu₀d
      rw [hd3o] at h1
      rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h1 | h1
      · exact absurd (orderOf_eq_one_iff.mp h1) hu₀1
      · exact h1
    exact ht3 (hu₀3 ▸ orderOf_dvd_of_pow_eq_one heq)
  refine ⟨w ^ t, ⟨Y.pow_mem hwY t, pow_mem hwW t⟩, ?_, c, hcA, hmove⟩
  refine orderOf_eq_prime ?_ ?_
  · rw [← pow_mul, mul_comm, hwt]
  · intro h1
    apply hmove
    rw [h1, one_mul, inv_one, mul_one]

theorem exists_orderOf_eq_three_of_family (h45 : Sec4.Item4_5) (h117 : Item117)
    (h : Sec11Data G A c L a R Y d x s r g) {F : ∀ (X : Type) [Group X], Prop}
    (hNo : NoOuterType424For F) (hK : InvElt1118For F)
    (hZ : ∃ (X : Type) (_ : Group X), F X ∧
      Nonempty ((Y ⧸ aschbacherSolvableCore 3 Y) ≃* _root_.commutator X))
    (hcen : Subgroup.center (Y ⧸ aschbacherSolvableCore 3 Y) = ⊥) :
    ∃ g₀ ∈ Y ⊓ Subgroup.normalizer (A : Set G), orderOf g₀ = 3 ∧ ∃ z ∈ A, g₀ * z * g₀⁻¹ ≠ z := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe := h.mem_partTwoF.1
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 h.toTheoremFourHyp hAe h.a_mem h.a_ne_one Y
      h.mem_thetaComponentsAt_Y
  have hcA : c ∈ A := h.mem_A
  have hcN : c ∈ Subgroup.normalizer (Y : Set G) := hAY hcA
  have hc3 : c ^ 3 = 1 := hAe.2 c hcA
  have hdA : d ∈ A := Item1117Proof.d_mem_A h
  have hd3 : d ^ 3 = 1 := hAe.2 d hdA
  have hgY : g ∈ Y := h.g_mem.1
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 Y) with hπ
  have hK' := mem_thetaComponentsIn_sec11K_inf h.toSec11Std
  have hT := kType119 G A c L a R Y h.toSec11Std d h.inf_eq h.closure_eq
  have hKY : sec11K L a ≤ Y := h.sec11K_le
  set J := ((sec11K L a).subgroupOf Y).map π with hJdef
  have hJα : J ∈ thetaComponentsIn (Item426.fixSub (Item426.thetaAut Y hcN)) :=
    Item426.map_mem_thetaComponentsIn_fixSub Y hcN hc3 hK'
  obtain ⟨eK⟩ := Item426.nonempty_quotTheta_map_equiv Y hKY
  have hJT : IsType424 (J ⧸ aschbacherSolvableCore 3 J) := isType424_of_mulEquiv eK.symm hT
  have hα3 : Item426.thetaAut Y hcN ^ 3 = 1 := Item426.thetaAut_pow_eq_one Y hcN hc3
  have hin : Item426.thetaAut Y hcN ∈
      (MulAut.conj : (Y ⧸ aschbacherSolvableCore 3 Y) →* MulAut _).range := by
    by_contra hnot
    exact hNo _ hZ _ J hα3 hnot hJα hJT
  obtain ⟨z, hz⟩ := hin
  have hz3 : MulAut.conj z ^ 3 = 1 := by rw [hz]; exact hα3
  have hJ : J ∈ thetaComponentsIn (Item426.fixSub (MulAut.conj z)) := by rw [hz]; exact hJα
  have hdK := h.toSec11Std.d_mem_sec11K h.inf_eq
  have hdY : d ∈ Y := hKY hdK
  obtain ⟨-, -, hd1⟩ := h.toSec11Std.not_mem_facts h.inf_eq h.closure_eq
  set v := π ⟨d, hdY⟩ with hv
  have hvJ : v ∈ J := ⟨⟨d, hdY⟩, Subgroup.mem_subgroupOf.mpr hdK, rfl⟩
  have hdY3 : (⟨d, hdY⟩ : Y) ^ 3 = 1 := Subtype.ext (by simpa using hd3)
  have hv3 : v ^ 3 = 1 := by rw [hv, ← map_pow, hdY3, map_one]
  have hdpow : ∀ n : ℤ, π ⟨d ^ n, Y.zpow_mem hdY n⟩ = 1 → d ^ n = 1 := by
    intro n h1
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have h2 := eq_one_of_mem_theta_of_pow_eq_one h1 (k := 1) (by
      apply Subtype.ext
      simp only [pow_one, SubgroupClass.coe_pow, Subgroup.coe_one]
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hd3, one_zpow])
    simpa using congrArg Subtype.val h2
  have hv1 : v ≠ 1 := by
    intro h1
    apply hd1
    have := hdpow 1 (by simpa using h1)
    simpa using this
  set gb := π ⟨g, hgY⟩ with hgb
  obtain ⟨k, hk⟩ := h.pow_eq_one
  have hgb3 : ∃ k : ℕ, gb ^ 3 ^ k = 1 := by
    refine ⟨k, ?_⟩
    rw [hgb, ← map_pow]
    have : (⟨g, hgY⟩ : Y) ^ 3 ^ k = 1 := Subtype.ext (by simpa using hk)
    rw [this, map_one]
  have hd3o : orderOf d = 3 := Item1117Proof.orderOf_d h
  have hgd : g * d = d * g := Sec12.commute_of_conj_mem_zpowers hd3o
    ((Subgroup.mem_normalizer_iff.mp (Item1115Proof.W_le_normalizer_d h117 h h.g_mem.2) d).mp
      (Subgroup.mem_zpowers d)) hk
  have hgbv : gb * v = v * gb := by
    rw [hgb, hv, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hgd
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (Item1117Proof.conj_g_c_mem h117 h)
  have hgN : g ∈ Subgroup.normalizer (Y : Set G) := Subgroup.le_normalizer hgY
  have hconjg : MulAut.conj gb = Sec12.thetaBarAct Y ⟨g, hgN⟩ :=
    (Sec12.thetaBarAct_of_mem hgY).symm
  have hconjd : ∀ n : ℤ, MulAut.conj (v ^ n) =
      Sec12.thetaBarAct Y ⟨d ^ n, Subgroup.le_normalizer (Y.zpow_mem hdY n)⟩ := by
    intro n
    rw [Sec12.thetaBarAct_of_mem (Y.zpow_mem hdY n), hv, ← map_zpow]
    rfl
  have hcomm : MulAut.conj (gb * z * gb⁻¹ * z⁻¹) = MulAut.conj (v ^ j) := by
    rw [hconjd j, map_mul, map_mul, map_mul, map_inv, map_inv, hconjg, hz]
    change Sec12.thetaBarAct Y ⟨g, hgN⟩ * Sec12.thetaBarAct Y ⟨c, hcN⟩ *
      (Sec12.thetaBarAct Y ⟨g, hgN⟩)⁻¹ * (Sec12.thetaBarAct Y ⟨c, hcN⟩)⁻¹ = _
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (by simp [hj])
  have hcomm' : gb * z * gb⁻¹ * z⁻¹ = v ^ j := by
    have h1 : MulAut.conj ((v ^ j)⁻¹ * (gb * z * gb⁻¹ * z⁻¹)) = 1 := by
      rw [map_mul, map_inv, hcomm, inv_mul_cancel]
    have h2 := Sec12.mem_center_of_conj_eq_one h1
    rw [hcen, Subgroup.mem_bot] at h2
    calc gb * z * gb⁻¹ * z⁻¹ = v ^ j * ((v ^ j)⁻¹ * (gb * z * gb⁻¹ * z⁻¹)) := by group
      _ = v ^ j := by rw [h2, mul_one]
  have hgbzv : gb * z * gb⁻¹ * z⁻¹ ∈ Subgroup.zpowers v := by
    rw [hcomm']
    exact Subgroup.zpow_mem_zpowers v j
  have hgbz : gb * z ≠ z * gb := by
    intro h1
    have h2 : v ^ j = 1 := by rw [← hcomm', h1]; group
    have h3 : π ⟨d ^ j, Y.zpow_mem hdY j⟩ = 1 := by
      rw [← h2, hv, ← map_zpow]
      rfl
    have h4 := hdpow j h3
    apply h.g_not_mem
    apply Sec10.mem_normalizer_zpowers_of_conj_mem
    have : g * c * g⁻¹ = c := by
      calc g * c * g⁻¹ = g * c * g⁻¹ * c⁻¹ * c := by group
        _ = c := by rw [← hj, h4, one_mul]
    rw [this]
    exact Subgroup.mem_zpowers c
  obtain ⟨n, hn3, hnz, hnv⟩ :=
    hK _ hZ z v gb J hz3 hJ hJT hvJ hv3 hv1 hgb3 hgbv hgbzv hgbz
  have hYa : Y ≤ Subgroup.centralizer ({a} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt_Y
  have hfix : ∀ e (he : e ∈ A), Sec12.thetaBarAct Y ⟨e, hAY he⟩ (gb⁻¹ * n) = gb⁻¹ * n := by
    intro e he
    have hmem : e ∈ Subgroup.closure ({c, a, d} : Set G) := h.closure_eq ▸ he
    have hcl : Subgroup.closure ({c, a, d} : Set G) ≤ Subgroup.normalizer (Y : Set G) :=
      h.closure_eq ▸ hAY
    suffices hs : ∀ e (he : e ∈ Subgroup.closure ({c, a, d} : Set G)),
        Sec12.thetaBarAct Y ⟨e, hcl he⟩ (gb⁻¹ * n) = gb⁻¹ * n from hs e hmem
    intro e he
    induction he using Subgroup.closure_induction with
    | mem y hy =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with h1 | h1 | h1 <;> subst y
      ·
        change Item426.thetaAut Y hcN (gb⁻¹ * n) = gb⁻¹ * n
        rw [← hz, MulAut.conj_apply]
        have e1 : n * z = gb * z * gb⁻¹ * n := by
          calc n * z = (n * z * n⁻¹) * n := by group
            _ = gb * z * gb⁻¹ * n := by rw [hnz]
        calc z * (gb⁻¹ * n) * z⁻¹ = gb⁻¹ * (gb * z * gb⁻¹ * n) * z⁻¹ := by group
          _ = gb⁻¹ * (n * z) * z⁻¹ := by rw [e1]
          _ = gb⁻¹ * n := by group
      ·
        obtain ⟨y₀, hy₀⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 Y)
          (gb⁻¹ * n)
        rw [← hy₀, Sec12.thetaBarAct_mk]
        congr 1
        apply Subtype.ext
        change a * (y₀ : G) * a⁻¹ = y₀
        rw [← Subgroup.mem_centralizer_singleton_iff.mp (hYa y₀.2), mul_inv_cancel_right]
      ·
        have e1 : ∀ hy' : d ∈ Subgroup.normalizer (Y : Set G),
            Sec12.thetaBarAct Y ⟨d, hy'⟩ = MulAut.conj v := fun _ =>
          Sec12.thetaBarAct_of_mem hdY
        rw [e1, MulAut.conj_apply]
        have hgbv' : gb⁻¹ * v = v * gb⁻¹ := by
          calc gb⁻¹ * v = gb⁻¹ * (v * gb) * gb⁻¹ := by group
            _ = gb⁻¹ * (gb * v) * gb⁻¹ := by rw [hgbv]
            _ = v * gb⁻¹ := by group
        calc v * (gb⁻¹ * n) * v⁻¹ = (v * gb⁻¹) * n * v⁻¹ := by group
          _ = gb⁻¹ * (v * n) * v⁻¹ := by rw [← hgbv']; group
          _ = gb⁻¹ * n := by rw [← hnv]; group
    | one =>
      have e1 : (⟨1, hcl (Subgroup.one_mem _)⟩ : Subgroup.normalizer (Y : Set G)) = 1 := rfl
      rw [e1, map_one, MulAut.one_apply]
    | mul y w hy hw ihy ihw =>
      have e1 : (⟨y * w, hcl (Subgroup.mul_mem _ hy hw)⟩ : Subgroup.normalizer (Y : Set G)) =
          ⟨y, hcl hy⟩ * ⟨w, hcl hw⟩ := rfl
      rw [e1, (Sec12.thetaBarAct Y).map_mul, MulAut.mul_apply, ihw, ihy]
    | inv y hy ihy =>
      have e1 : (⟨y⁻¹, hcl (Subgroup.inv_mem _ hy)⟩ : Subgroup.normalizer (Y : Set G)) =
          (⟨y, hcl hy⟩)⁻¹ := rfl
      rw [e1, (Sec12.thetaBarAct Y).map_inv]
      conv_lhs => rw [← ihy]
      exact MulAut.inv_apply_self _ _ _
  refine exists_orderOf_eq_three_of_lift h117 h hAY hfix ?_
  rw [← hgb, mul_inv_cancel_left, hn3]

end Lift

section Transfer

variable {F F' : ∀ (X : Type) [Group X], Prop}

theorem invElt1118For_of_split (hs : KS11Lie3Proof.SplitFamily F F') (h : InvElt1118For F') :
    InvElt1118For F := by
  intro Z _ _ hZ z v g J hz3 hJ hJT hvJ hv3 hv1 hgk hgv hgz hgz'
  rcases hs Z hZ with hZ' | hno
  · exact h Z hZ' z v g J hz3 hJ hJT hvJ hv3 hv1 hgk hgv hgz hgz'
  · exact (hno z J hz3 hJ hJT).elim

end Transfer

end Item1117Res3Proof

end CFSG.RankThree.PartTwo.Sec11
