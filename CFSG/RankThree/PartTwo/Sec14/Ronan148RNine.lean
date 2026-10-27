module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148RNineK
public import CFSG.RankThree.PartTwo.Sec14.Ronan148WU3Nine
public import CFSG.RankThree.PartTwo.Sec13.Ronan138P5Lift
import CFSG.RankThree.PartTwo.Sec8.Hering88FCoprime
import CFSG.RankThree.PartTwo.Sec14.Item1413Res3ProofTools
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148R

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank
open CFSG.RankThree.PartTwo.Sec13.Ronan138P5 (rho false_of_mem_partTwoE_lt
  exists_pow_lift_three mem_normalizer_inf_centralizer)
open CFSG.Assembly.RankThreeEven (projSU)
open scoped Pointwise

section Aut

variable {X : Type*} [Group X]

theorem eq_zpow_of_conj_eq (hZ : Subgroup.center X = ⊥) {ψ : MulAut X} (hψ3 : ψ ^ 3 = 1)
    (hout : ∀ x : X, MulAut.conj x ≠ ψ) {u d : X} {i k : ℤ}
    (h : MulAut.conj d = ψ ^ i * MulAut.conj u ^ k) : d = u ^ k := by
  have hinj := Sec4.RonanKChevTwo.conj_injective_of_center_eq_bot hZ
  have hψi : ψ ^ i = MulAut.conj (d * (u ^ k)⁻¹) := by
    rw [map_mul, map_inv, map_zpow, h, mul_inv_cancel_right]
  have hi : ψ ^ i = 1 := by
    have e3 : ((3 : ℕ) : ℤ) = 3 := by norm_num
    have hred : ψ ^ i = ψ ^ (i % 3) := by rw [zpow_eq_zpow_emod' i hψ3, e3]
    have h3 : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
    rcases h3 with h0 | h1 | h2
    · rw [hred, h0, zpow_zero]
    · exfalso
      apply hout (d * (u ^ k)⁻¹)
      rw [← hψi, hred, h1, zpow_one]
    · exfalso
      apply hout ((d * (u ^ k)⁻¹) ^ 2)
      rw [map_pow, ← hψi, hred, h2, ← zpow_natCast, ← zpow_mul]
      have : (2 : ℤ) * ((2 : ℕ) : ℤ) = ((3 : ℕ) : ℤ) + 1 := by norm_num
      rw [this, zpow_add, zpow_one, zpow_natCast, hψ3, one_mul]
  rw [hi, one_mul, ← map_zpow] at h
  exact hinj h

end Aut

section Join

variable {G : Type*} [Group G]

theorem exists_zpow_of_mem_sup {a b x : G} (hab : a * b = b * a)
    (hx : x ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b) : ∃ i j : ℤ, x = a ^ i * b ^ j := by
  have hN : Subgroup.zpowers b ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact (Commute.zpow_left (show Commute a b from hab) k).eq
  have hmem : x ∈ ((Subgroup.zpowers a : Set G) * (Subgroup.zpowers b : Set G)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ hN]
    exact hx
  obtain ⟨p, hp, q, hq, rfl⟩ := hmem
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
  exact ⟨i, j, rfl⟩

theorem exists_mul_zpow_of_mem_sup {H : Subgroup G} {c x : G}
    (hc : ∀ h ∈ H, h * c = c * h) (hx : x ∈ H ⊔ Subgroup.zpowers c) :
    ∃ p ∈ H, ∃ k : ℤ, x = p * c ^ k := by
  have hN : Subgroup.zpowers c ≤ Subgroup.normalizer (H : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact hc z hz
  have hmem : x ∈ ((H : Set G) * (Subgroup.zpowers c : Set G)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ hN]
    exact hx
  obtain ⟨p, hp, q, hq, rfl⟩ := hmem
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
  exact ⟨p, hp, k, rfl⟩

end Join

section Lift

variable {G : Type} [Group G] [Finite G]

theorem false_of_e27_lift (hEF : partTwoF G = partTwoE G) {L B : Subgroup G}
    (hBN : B ≤ Subgroup.normalizer (L : Set G)) (hB : CFSG.Assembly.IsElemAbelian 3 B)
    (hB27 : Nat.card B = 27) {V : Subgroup (L ⧸ aschbacherSolvableCore 3 L)} (hV : V ≠ ⊥)
    (hV2 : IsPGroup 2 V)
    (hBV : ∀ (b : G) (hb : b ∈ B), ∀ v ∈ V,
      Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨b, hBN hb⟩) v ∈ V)
    {dt : G} (hdt3 : dt ^ 3 = 1) (hdtB : ∀ b ∈ B, b * dt = dt * b) (hdtn : dt ∉ B) : False := by
  have hB3 : IsPGroup 3 B := fun g => ⟨1, Subtype.ext (by simpa using hB.2 g g.2)⟩
  obtain ⟨S, hS, hS2, hBS⟩ := Ronan148W.exists_two_subgroup_of_preserves hBN hB3 hV hV2 hBV
  have hBE : B ∈ partTwoE G := ⟨hB, hB27, S, hS, hS2, hBS⟩
  have hBdt : ∀ b ∈ B, ∀ z ∈ Subgroup.zpowers dt, b * z = z * b := by
    intro b hb z hz
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact (Commute.zpow_right (show Commute b dt from hdtB b hb) j).eq
  have hB'e : CFSG.Assembly.IsElemAbelian 3 (B ⊔ Subgroup.zpowers dt) :=
    CFSG.Open.IsElemAbelian.sup_of_commute hB (CFSG.Open.isElemAbelian_zpowers hdt3) hBdt
  refine false_of_mem_partTwoE_lt hEF hBE hB'e le_sup_left fun hBB' => hdtn ?_
  rw [hBB']
  exact (le_sup_right : Subgroup.zpowers dt ≤ B ⊔ Subgroup.zpowers dt) (Subgroup.mem_zpowers dt)

theorem exists_lift_three {L M : Subgroup G} (hML : M ≤ L) {y : G}
    (hyL : y ∈ Subgroup.normalizer (L : Set G)) (hyM : y ∈ Subgroup.normalizer (M : Set G))
    (hy3 : y ^ 3 = 1) {m : G} (hm : m ∈ M)
    (hm3 : ((⟨m, hML hm⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) ^ 3 = 1)
    (hfix : rho L ⟨y, hyL⟩ ((⟨m, hML hm⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) =
      ((⟨m, hML hm⟩ : L) : L ⧸ aschbacherSolvableCore 3 L)) :
    ∃ w ∈ M, w * y = y * w ∧ w ^ 3 = 1 ∧ ∃ hwL : w ∈ L,
      ((⟨w, hwL⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) =
        ((⟨m, hML hm⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) := by
  obtain ⟨m₁, hm₁y, hm₁⟩ :=
    Sec8.Hering88F.exists_mem_centralizer_of_fixed hML hyL hyM hy3 hm hfix
  obtain ⟨k, hk, hk3⟩ := exists_pow_lift_three (⟨m₁, hML m₁.2⟩ : L) hm₁ hm3
  have hm₁y' : (m₁ : G) * y = y * m₁ := Subgroup.mem_centralizer_singleton_iff.mp hm₁y
  refine ⟨(m₁ : G) ^ k, M.pow_mem m₁.2 k, (Commute.pow_left (show Commute (m₁ : G) y from hm₁y')
    k).eq, ?_, L.pow_mem (hML m₁.2) k, ?_⟩
  · have := congrArg Subtype.val hk3
    simpa only [Subgroup.coe_pow, OneMemClass.coe_one, ← pow_mul] using this
  · rw [← hk]
    rfl

theorem card_sup_zpowers_of_not_mem {H : Subgroup G} {x : G} (hx3 : x ^ 3 = 1) (hxH : x ∉ H)
    (hN : Subgroup.zpowers x ≤ Subgroup.normalizer (H : Set G)) :
    Nat.card (H ⊔ Subgroup.zpowers x : Subgroup G) = 3 * Nat.card H := by
  have hx1 : x ≠ 1 := fun h => hxH (h ▸ H.one_mem)
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hinf : Subgroup.zpowers x ⊓ H = ⊥ := by
    have hdvd : Nat.card (Subgroup.zpowers x ⊓ H : Subgroup G) ∣ 3 := by
      have := Subgroup.card_dvd_of_le (inf_le_left : Subgroup.zpowers x ⊓ H ≤ Subgroup.zpowers x)
      rwa [Nat.card_zpowers, hxo] at this
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have heq : Subgroup.zpowers x ⊓ H = Subgroup.zpowers x :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, Nat.card_zpowers, hxo])
      have hxm : x ∈ Subgroup.zpowers x ⊓ H := by
        rw [heq]
        exact Subgroup.mem_zpowers x
      exact hxH hxm.2
  have h := Sec6.card_sup_mul_card_inf hN
  rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, hxo, sup_comm] at h
  exact h

theorem rho_zpow_mul {L : Subgroup G} {a b c : G} (ha : a ∈ Subgroup.normalizer (L : Set G))
    (hb : b ∈ Subgroup.normalizer (L : Set G)) (hc : c ∈ Subgroup.normalizer (L : Set G))
    (i j k : ℤ) (hx : a ^ i * b ^ j * c ^ k ∈ Subgroup.normalizer (L : Set G)) :
    rho L ⟨a ^ i * b ^ j * c ^ k, hx⟩ =
      rho L ⟨a, ha⟩ ^ i * rho L ⟨b, hb⟩ ^ j * rho L ⟨c, hc⟩ ^ k := by
  have hm : (⟨a ^ i * b ^ j * c ^ k, hx⟩ : Subgroup.normalizer (L : Set G)) =
      ⟨a, ha⟩ ^ i * ⟨b, hb⟩ ^ j * ⟨c, hc⟩ ^ k :=
    Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_zpow])
  rw [hm, map_mul, map_mul, map_zpow, map_zpow, map_zpow]

end Lift

section Main


theorem step148OmegaRankThreeNineU_of (hb : KF148PGUFieldCent) :
    Ronan148W.Step148OmegaRankThreeNineU := by
  intro G _ _ A c L h e he heΩ Le hLeA f hf _ hiso h8 F heF hF hF81 hP
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEF : partTwoF G = partTwoE G := (h.toTheoremFourHyp.partTwoF_eq_partTwoE h.partTwoS_eq).1
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := h.mem_partTwoF.1.2
  have he3 : e ^ 3 = 1 := hA3 e he
  have he1 : e ≠ 1 := by
    intro h1
    obtain ⟨-, hcard, -⟩ := heΩ
    rw [h1, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at hcard
    norm_num at hcard
  have hLeC : Le ≤ Subgroup.centralizer ({e} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hLeA.1
  have h3 : 3 ∣ Nat.card Le :=
    (Sec19.Step1914TriProof.three_dvd_card_of_isoLThreePi hf hiso).trans
      (Subgroup.card_quotient_dvd_card _)
  have hFC : F ≤ Subgroup.centralizer ({e} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hF.1.is_comm.comm ⟨x, hx⟩ ⟨e, heF⟩))
  have hFN : F ≤ Subgroup.normalizer (Le : Set G) :=
    hFC.trans (Proof1413Res3.centralizer_le_normalizer_of_mem_lA h heΩ hLeA h3)
  have heN : e ∈ Subgroup.normalizer (Le : Set G) := hFN heF
  set φ := (Sec4.thetaQuotMulAut ↥Le).comp Le.normalizerMonoidHom with hφ
  set F' := F.subgroupOf (Subgroup.normalizer (Le : Set G)) with hF'
  set ψ := φ.comp F'.subtype with hψ
  have hF'card : Nat.card F' = 81 := by
    rw [hF', ← hF81]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFN).toEquiv
  have hF'ab : CFSG.Open.IsElemAbelian 3 F' := by
    refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun y hy => Subtype.ext ?_⟩
    · exact (show ((a : Subgroup.normalizer (Le : Set G)) : G) * b = b * a from
        congrArg Subtype.val (hF.1.is_comm.comm ⟨_, Subgroup.mem_subgroupOf.mp a.2⟩
          ⟨_, Subgroup.mem_subgroupOf.mp b.2⟩))
    · exact hF.2 _ (Subgroup.mem_subgroupOf.mp hy)
  have hmem : ∀ x : ψ.ker, (((x : F') : Subgroup.normalizer (Le : Set G)) : G) ∈
      Subgroup.zpowers e := by
    intro x
    apply hP
    refine ⟨Subgroup.mem_subgroupOf.mp (x : F').2, ⟨(x : F'), ?_, rfl⟩⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    exact MonoidHom.mem_ker.mp x.2
  have hker3 : Nat.card ψ.ker ≤ 3 := by
    calc Nat.card ψ.ker ≤ Nat.card (Subgroup.zpowers e) :=
          Nat.card_le_card_of_injective (fun x => ⟨_, hmem x⟩) (by
            intro x y hxy
            have h1 := congrArg (fun z : Subgroup.zpowers e => (z : G)) hxy
            simp only at h1
            exact Subtype.ext (Subtype.ext (Subtype.ext h1)))
      _ ≤ 3 := by
        rw [Nat.card_zpowers]
        exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one he3)
  have hnm : Le.normalizerMonoidHom ⟨e, heN⟩ = 1 := by
    refine MulEquiv.ext fun l => Subtype.ext ?_
    rw [Sec4.coe_normalizerMonoidHom, MulAut.one_apply]
    show e * (l : G) * e⁻¹ = l
    rw [(Subgroup.mem_centralizer_singleton_iff.mp (hLeC l.2)).symm, mul_inv_cancel_right]
  set e' : F' := ⟨⟨e, heN⟩, Subgroup.mem_subgroupOf.mpr heF⟩ with he'def
  have he'k : e' ∈ ψ.ker := by
    rw [MonoidHom.mem_ker]
    show (Sec4.thetaQuotMulAut ↥Le) (Le.normalizerMonoidHom ⟨e, heN⟩) = 1
    rw [hnm, map_one]
  have he'3 : e' ^ 3 = 1 := Subtype.ext (Subtype.ext he3)
  have he'1 : e' ≠ 1 := fun h1 => he1 (congrArg Subtype.val (congrArg Subtype.val h1))
  have hker3' : 3 ≤ Nat.card ψ.ker := by
    calc 3 = Nat.card (Subgroup.zpowers e') := by
          rw [Nat.card_zpowers, orderOf_eq_prime he'3 he'1]
      _ ≤ Nat.card ψ.ker := Subgroup.card_le_of_le (Subgroup.zpowers_le.mpr he'k)
  have hkerc : Nat.card ψ.ker = 3 := le_antisymm hker3 hker3'
  have hcard : Nat.card F' = Nat.card ψ.ker * Nat.card ψ.range := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv, mul_comm]
  have hrange27 : Nat.card ψ.range = 27 := by
    rw [hF'card, hkerc] at hcard
    omega
  have hrangeab : CFSG.Open.IsElemAbelian 3 ψ.range := by
    rw [hψ, MonoidHom.range_comp, Subgroup.range_subtype]
    exact Ronan148W.isElemAbelian_map _ hF'ab
  have hXiso : Nonempty (↥Le ⧸ aschbacherSolvableCore 3 ↥Le ≃* projSU 3 2 f) := by
    rcases hiso with ⟨h1, -⟩ | ⟨-, hi⟩
    · omega
    · exact hi
  have hZ : Subgroup.center (↥Le ⧸ aschbacherSolvableCore 3 ↥Le) = ⊥ := by
    obtain ⟨eX⟩ := hXiso
    have hq2 : 2 < 2 ^ f := by
      have h1 := Nat.mod_le (2 ^ f) 9
      rw [h8] at h1
      omega
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact Sec4.RonanK429.center_eq_bot_of_mulEquiv eX
      (Sec13.isPerfect_center_projSU 2 f hf (by omega) hq2).2
  have hinj := Sec4.RonanKChevTwo.conj_injective_of_center_eq_bot hZ
  obtain ⟨ψ₀, hψ₀, hout, u, d, t, hu1, hu3, hd3, hud, hdu, ht1, ht2, hut, hψu, hψd, hψt⟩ :=
    exists_fixed_e9 hb h8 hXiso hrangeab hrange27
  obtain ⟨y₀, rfl⟩ := hψ₀
  set y : G := ((y₀ : Subgroup.normalizer (Le : Set G)) : G) with hydef
  have hyN : y ∈ Subgroup.normalizer (Le : Set G) := (y₀ : Subgroup.normalizer (Le : Set G)).2
  have hyF : y ∈ F := Subgroup.mem_subgroupOf.mp y₀.2
  have hy3 : y ^ 3 = 1 := hF.2 y hyF
  have hρy : rho Le ⟨y, hyN⟩ = ψ y₀ := rfl
  have hρe : rho Le ⟨e, heN⟩ = 1 := by
    change Sec4.thetaQuotMulAut ↥Le (Le.normalizerMonoidHom ⟨e, heN⟩) = 1
    rw [hnm, map_one]
  have hψ3 : ψ y₀ ^ 3 = 1 := hrangeab.2 _ ⟨y₀, rfl⟩
  obtain ⟨m₀, hm₀⟩ := QuotientGroup.mk_surjective u
  have hm₀' : ((⟨(m₀ : G), m₀.2⟩ : Le) : ↥Le ⧸ aschbacherSolvableCore 3 ↥Le) = u := hm₀
  obtain ⟨y', hy'L, hy'y, hy'3, hy'L', hy'u⟩ := exists_lift_three (L := Le) (M := Le) le_rfl hyN
    hyN hy3 m₀.2 (by rw [hm₀']; exact hu3) (by rw [hm₀', hρy]; exact hψu)
  have hy'N : y' ∈ Subgroup.normalizer (Le : Set G) := Subgroup.le_normalizer hy'L
  have hy'img : ((⟨y', hy'L⟩ : Le) : ↥Le ⧸ aschbacherSolvableCore 3 ↥Le) = u := hy'u.trans hm₀'
  have hρy' : rho Le ⟨y', hy'N⟩ = MulAut.conj u := by
    have := KFacts.thetaQuotMulAut_compAction_of_mem hy'L hy'N
    change Sec4.thetaQuotMulAut Le (Sec4.compAction Le ⟨y', hy'N⟩) = _
    rw [this]
    congr 1
  obtain ⟨n₀, hn₀⟩ := QuotientGroup.mk_surjective d
  have hn₀' : ((⟨(n₀ : G), n₀.2⟩ : Le) : ↥Le ⧸ aschbacherSolvableCore 3 ↥Le) = d := hn₀
  have hfixd : rho Le ⟨y', hy'N⟩ d = d := by
    rw [hρy', MulAut.conj_apply, hud, mul_inv_cancel_right]
  obtain ⟨n₁, hn₁L, hn₁y', -, hn₁L', hn₁d⟩ := exists_lift_three (L := Le) (M := Le) le_rfl hy'N
    hy'N hy'3 n₀.2 (by rw [hn₀']; exact hd3) (by rw [hn₀']; exact hfixd)
  have hn₁img : ((⟨n₁, hn₁L⟩ : Le) : ↥Le ⧸ aschbacherSolvableCore 3 ↥Le) = d := hn₁d.trans hn₀'
  have hn₁M : n₁ ∈ Le ⊓ Subgroup.centralizer ({y'} : Set G) :=
    ⟨hn₁L, Subgroup.mem_centralizer_singleton_iff.mpr hn₁y'⟩
  have hn₁img' : ((⟨n₁, (inf_le_left : Le ⊓ Subgroup.centralizer ({y'} : Set G) ≤ Le) hn₁M⟩ :
      Le) : ↥Le ⧸ aschbacherSolvableCore 3 ↥Le) = d := hn₁img
  obtain ⟨dt, hdtM, hdty, hdt3, hdtL, hdtd⟩ := exists_lift_three
    (L := Le) (M := Le ⊓ Subgroup.centralizer ({y'} : Set G)) inf_le_left hyN
    (mem_normalizer_inf_centralizer hyN hy'y) hy3 hn₁M (by rw [hn₁img']; exact hd3)
    (by rw [hn₁img', hρy]; exact hψd)
  have hdtN : dt ∈ Subgroup.normalizer (Le : Set G) := Subgroup.le_normalizer hdtL
  have hdtimg : ((⟨dt, hdtL⟩ : Le) : ↥Le ⧸ aschbacherSolvableCore 3 ↥Le) = d :=
    hdtd.trans hn₁img'
  have hρdt : rho Le ⟨dt, hdtN⟩ = MulAut.conj d := by
    have := KFacts.thetaQuotMulAut_compAction_of_mem hdtL hdtN
    change Sec4.thetaQuotMulAut Le (Sec4.compAction Le ⟨dt, hdtN⟩) = _
    rw [this]
    congr 1
  have hdty' : dt * y' = y' * dt := Subgroup.mem_centralizer_singleton_iff.mp hdtM.2
  have hey : e * y = y * e := (Subgroup.mem_centralizer_singleton_iff.mp (hFC hyF)).symm
  have hey' : e * y' = y' * e := (Subgroup.mem_centralizer_singleton_iff.mp (hLeC hy'L)).symm
  have hedt : e * dt = dt * e := (Subgroup.mem_centralizer_singleton_iff.mp (hLeC hdtL)).symm
  set B₁ : Subgroup G := Subgroup.zpowers e ⊔ Subgroup.zpowers y with hB₁
  set B : Subgroup G := B₁ ⊔ Subgroup.zpowers y' with hB
  have hB₁y' : ∀ p ∈ B₁, p * y' = y' * p := by
    have hle : B₁ ≤ Subgroup.centralizer ({y'} : Set G) := sup_le
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hey'))
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hy'y.symm))
    exact fun p hp => Subgroup.mem_centralizer_singleton_iff.mp (hle hp)
  have hBN : B ≤ Subgroup.normalizer (Le : Set G) :=
    sup_le (sup_le (Subgroup.zpowers_le.mpr heN) (Subgroup.zpowers_le.mpr hyN))
      (Subgroup.zpowers_le.mpr hy'N)
  have hρB : ∀ (i j k : ℤ) (hx : e ^ i * y ^ j * y' ^ k ∈ Subgroup.normalizer (Le : Set G)),
      rho Le ⟨e ^ i * y ^ j * y' ^ k, hx⟩ = ψ y₀ ^ j * MulAut.conj u ^ k := by
    intro i j k hx
    rw [rho_zpow_mul heN hyN hy'N i j k hx, hρe, hρy, hρy', one_zpow, one_mul]
  have hmemB : ∀ x ∈ B, ∃ i j k : ℤ, x = e ^ i * y ^ j * y' ^ k := by
    intro x hx
    obtain ⟨p, hp, k, rfl⟩ := exists_mul_zpow_of_mem_sup hB₁y' hx
    obtain ⟨i, j, rfl⟩ := exists_zpow_of_mem_sup hey hp
    exact ⟨i, j, k, rfl⟩
  have hye : y ∉ Subgroup.zpowers e := by
    intro hm
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hm
    have hm' : (⟨y, hyN⟩ : Subgroup.normalizer (Le : Set G)) = ⟨e, heN⟩ ^ k :=
      Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk.symm)
    apply hout 1
    rw [map_one, ← hρy, hm', map_zpow, hρe, one_zpow]
  have hy'B₁ : y' ∉ B₁ := by
    intro hm
    obtain ⟨i, j, hij⟩ := exists_zpow_of_mem_sup hey hm
    have hm' : (⟨y', hy'N⟩ : Subgroup.normalizer (Le : Set G)) = ⟨e, heN⟩ ^ i * ⟨y, hyN⟩ ^ j :=
      Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_zpow, Subgroup.coe_zpow]; exact hij)
    have h3 : MulAut.conj u = ψ y₀ ^ j *
        MulAut.conj (1 : ↥Le ⧸ aschbacherSolvableCore 3 ↥Le) ^ (0 : ℤ) := by
      rw [zpow_zero, mul_one, ← hρy', hm', map_mul, map_zpow, map_zpow, hρe, hρy, one_zpow,
        one_mul]
    have := eq_zpow_of_conj_eq hZ hψ3 hout h3
    rw [zpow_zero] at this
    exact hu1 this
  have hdtB : dt ∉ B := by
    intro hm
    obtain ⟨i, j, k, hijk⟩ := hmemB dt hm
    have hm' : (⟨dt, hdtN⟩ : Subgroup.normalizer (Le : Set G)) =
        ⟨e, heN⟩ ^ i * ⟨y, hyN⟩ ^ j * ⟨y', hy'N⟩ ^ k :=
      Subtype.ext (by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_zpow, Subgroup.coe_zpow,
          Subgroup.coe_zpow]
        exact hijk)
    have h3 : MulAut.conj d = ψ y₀ ^ j * MulAut.conj u ^ k := by
      rw [← hρdt, hm', map_mul, map_mul, map_zpow, map_zpow, map_zpow, hρe, hρy, hρy',
        one_zpow, one_mul]
    exact hdu (Subgroup.mem_zpowers_iff.mpr ⟨k, (eq_zpow_of_conj_eq hZ hψ3 hout h3).symm⟩)
  have hB₁e : CFSG.Assembly.IsElemAbelian 3 B₁ :=
    CFSG.Open.IsElemAbelian.sup_of_commute (CFSG.Open.isElemAbelian_zpowers he3)
      (CFSG.Open.isElemAbelian_zpowers hy3) fun a ha b hb => by
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
        exact (Commute.zpow_zpow (show Commute e y from hey) i j).eq
  have hBe : CFSG.Assembly.IsElemAbelian 3 B :=
    CFSG.Open.IsElemAbelian.sup_of_commute hB₁e (CFSG.Open.isElemAbelian_zpowers hy'3)
      fun a ha b hb => by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
        exact (Commute.zpow_right (show Commute a y' from hB₁y' a ha) k).eq
  have hcentr : ∀ {a b : G}, a * b = b * a →
      Subgroup.zpowers b ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G) := by
    intro a b hab
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact (Commute.zpow_left (show Commute a b from hab) k).eq
  have hB₁9 : Nat.card B₁ = 9 := by
    rw [hB₁, card_sup_zpowers_of_not_mem hy3 hye (hcentr hey), Nat.card_zpowers,
      orderOf_eq_prime he3 he1]
  have hB27 : Nat.card B = 27 := by
    have hN : Subgroup.zpowers y' ≤ Subgroup.normalizer (B₁ : Set G) := by
      rw [Subgroup.zpowers_le]
      refine Subgroup.centralizer_le_normalizer _ ?_
      rw [Subgroup.mem_centralizer_iff]
      exact fun z hz => hB₁y' z hz
    rw [hB, card_sup_zpowers_of_not_mem hy'3 hy'B₁ hN, hB₁9]
  have hfixB : ∀ (b : G) (hb : b ∈ B), rho Le ⟨b, hBN hb⟩ t = t := by
    intro b hb
    obtain ⟨i, j, k, rfl⟩ := hmemB b hb
    rw [hρB]
    have hst : ∀ σ : MulAut (↥Le ⧸ aschbacherSolvableCore 3 ↥Le),
        σ ∈ MulAction.stabilizer (MulAut (↥Le ⧸ aschbacherSolvableCore 3 ↥Le)) t ↔ σ t = t :=
      fun σ => MulAction.mem_stabilizer_iff
    rw [← hst]
    refine mul_mem (zpow_mem ((hst _).mpr hψt) j) (zpow_mem ((hst _).mpr ?_) k)
    rw [MulAut.conj_apply, hut, mul_inv_cancel_right]
  set V : Subgroup (↥Le ⧸ aschbacherSolvableCore 3 ↥Le) := Subgroup.zpowers t with hV
  have hVne : V ≠ ⊥ := by
    intro hV0
    apply ht1
    have : t ∈ V := Subgroup.mem_zpowers t
    rw [hV0, Subgroup.mem_bot] at this
    exact this
  have hV2 : IsPGroup 2 V := by
    intro v
    refine ⟨1, Subtype.ext ?_⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp v.2
    rw [pow_one, Subgroup.coe_pow, OneMemClass.coe_one, ← hk, ← zpow_natCast, ← zpow_mul,
      mul_comm, zpow_mul, zpow_natCast, ht2, one_zpow]
  have hBV : ∀ (b : G) (hb : b ∈ B), ∀ v ∈ V,
      Sec4.thetaQuotMulAut ↥Le (Le.normalizerMonoidHom ⟨b, hBN hb⟩) v ∈ V := by
    intro b hb v hv
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    change rho Le ⟨b, hBN hb⟩ (t ^ k) ∈ V
    rw [map_zpow, hfixB b hb]
    exact Subgroup.zpow_mem_zpowers t k
  have hdtc : ∀ b ∈ B, b * dt = dt * b := by
    have hle : B ≤ Subgroup.centralizer ({dt} : Set G) := sup_le
      (sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hedt))
        (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hdty.symm)))
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hdty'.symm))
    exact fun b hb => Subgroup.mem_centralizer_singleton_iff.mp (hle hb)
  exact false_of_e27_lift hEF hBN hBe hB27 hVne hV2 hBV hdt3 hdtc hdtB

end Main

end CFSG.RankThree.PartTwo.Sec14.Ronan148R

end
