module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34FiveNQ
public import CFSG.Quasithin.Vol2.Ch9Sec3TNU35
public import CFSG.Quasithin.Vol2.Ch9Sec3FFBRank
public import CFSG.LinearAlgebra.SL2MinimalFaithfulSection

public section

namespace CFSG.Quasithin.H13.Ch9.TN

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.RankThree.PartTwo.Census.Carrier (ThreeRankLeOne)
open scoped Pointwise

variable {Y : Type} [Group Y] [Finite Y]

omit [Finite Y] in
theorem le_normalizer_of_three_inner_sub {W B D : Subgroup Y}
    (hinn : ∀ α : MulAut ↥W, α ^ 3 = 1 → ∃ x : ↥W, α = MulAut.conj x)
    (hrk : ThreeRankLeOne ↥W) (hZ2 : ∀ w ∈ Subgroup.center ↥W, w * w = 1)
    (hBW : B ≤ W) (hDW : D ≤ Subgroup.normalizer (W : Set Y)) (hD3e : ∀ x ∈ D, x ^ 3 = 1)
    {b : Y} (hbB : b ∈ B) (hbD : ∀ d ∈ D, d * b = b * d) (hb1 : b ≠ 1) (hb3 : b ^ 3 = 1) :
    D ≤ Subgroup.normalizer (B : Set Y) := by
  intro d hd
  set α := CFSG.SL2MinimalFaithful.conjAction hDW ⟨d, hd⟩ with hαdef
  have hα3 : α ^ 3 = 1 := by
    have h : (⟨d, hd⟩ : ↥D) ^ 3 = 1 := Subtype.ext (by simpa using hD3e d hd)
    rw [hαdef, ← map_pow, h, map_one]
  obtain ⟨x, hx⟩ := hinn α hα3
  have hxw : ∀ w : ↥W, d * (w : Y) * d⁻¹ = (x : Y) * w * (x : Y)⁻¹ := by
    intro w
    have h := congrArg (fun β : MulAut ↥W => ((β w : ↥W) : Y)) hx
    simpa [hαdef, CFSG.SL2MinimalFaithful.conjAction_apply] using h
  have hu : x ^ 3 ∈ Subgroup.center ↥W := by
    rw [Subgroup.mem_center_iff]
    intro w
    have h1 : MulAut.conj (x ^ 3) = 1 := by rw [map_pow, ← hx, hα3]
    have h2 := congrArg (fun β : MulAut ↥W => β w) h1
    simp only [MulAut.conj_apply, MulAut.one_apply] at h2
    calc w * x ^ 3 = x ^ 3 * w * (x ^ 3)⁻¹ * x ^ 3 := by rw [h2]
      _ = x ^ 3 * w := by group
  have hu2 := hZ2 _ hu
  set y : ↥W := x ^ 4 with hydef
  have hy3 : y ^ 3 = 1 := by
    calc y ^ 3 = x ^ 3 * x ^ 3 * (x ^ 3 * x ^ 3) := by rw [hydef]; group
      _ = 1 := by rw [hu2, one_mul]
  have hyw : ∀ w : ↥W, (y : Y) * w * (y : Y)⁻¹ = (x : Y) * w * (x : Y)⁻¹ := by
    intro w
    have hc : w * x ^ 3 = x ^ 3 * w := Subgroup.mem_center_iff.mp hu w
    have h : y * w * y⁻¹ = x * w * x⁻¹ := by
      calc y * w * y⁻¹ = x * (x ^ 3 * w) * (x ^ 3)⁻¹ * x⁻¹ := by rw [hydef]; group
        _ = x * (w * x ^ 3) * (x ^ 3)⁻¹ * x⁻¹ := by rw [hc]
        _ = x * w * x⁻¹ := by group
    simpa using congrArg Subtype.val h
  set b' : ↥W := ⟨b, hBW hbB⟩ with hb'
  have hyb : b' * y = y * b' := by
    have h1 : d * b * d⁻¹ = b := by rw [hbD d hd, mul_inv_cancel_right]
    have h2 : (y : Y) * b * (y : Y)⁻¹ = b := by
      have e1 : (y : Y) * b * (y : Y)⁻¹ = (x : Y) * b * (x : Y)⁻¹ := hyw b'
      have e2 : d * b * d⁻¹ = (x : Y) * b * (x : Y)⁻¹ := hxw b'
      rw [e1, ← e2, h1]
    apply Subtype.ext
    show b * (y : Y) = (y : Y) * b
    calc b * (y : Y) = (y : Y) * b * (y : Y)⁻¹ * y := by rw [h2]
      _ = (y : Y) * b := by group
  have hb'1 : b' ≠ 1 := fun h => hb1 (congrArg Subtype.val h)
  have hb'3 : b' ^ 3 = 1 := Subtype.ext (by simpa [hb'] using hb3)
  have hyB : (y : Y) ∈ B := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hrk b' y hb'3 hy3 hyb hb'1)
    rw [← hk, Subgroup.coe_zpow]
    exact B.zpow_mem hbB k
  have hcW : ∀ w ∈ W, w * (d * (y : Y)⁻¹) = d * (y : Y)⁻¹ * w := by
    intro w hw
    have hm : (y : Y)⁻¹ * w * y ∈ W := W.mul_mem (W.mul_mem (W.inv_mem y.2) hw) y.2
    have h : d * ((y : Y)⁻¹ * w * y) * d⁻¹ =
        (x : Y) * ((y : Y)⁻¹ * w * y) * (x : Y)⁻¹ := hxw ⟨_, hm⟩
    have h' : (y : Y) * ((y : Y)⁻¹ * w * y) * (y : Y)⁻¹ =
        (x : Y) * ((y : Y)⁻¹ * w * y) * (x : Y)⁻¹ := hyw ⟨_, hm⟩
    have e : d * ((y : Y)⁻¹ * w * y) * d⁻¹ = w := by
      rw [h, ← h']
      group
    calc w * (d * (y : Y)⁻¹) = d * ((y : Y)⁻¹ * w * y) * d⁻¹ * (d * (y : Y)⁻¹) := by rw [e]
      _ = d * (y : Y)⁻¹ * w := by group
  have hcN : d * (y : Y)⁻¹ ∈ Subgroup.normalizer (B : Set Y) :=
    Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun g hg => hcW g (hBW hg))
  have e : d = d * (y : Y)⁻¹ * y := by group
  rw [e]
  exact Subgroup.mul_mem _ hcN (Subgroup.le_normalizer hyB)

theorem three_inner_of_sl2 {X : Type} [Group X] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (e : X ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) :
    ∀ α : MulAut X, α ^ 3 = 1 → ∃ x : X, α = MulAut.conj x := by
  have : Fact p.Prime := ⟨hp⟩
  have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) := A313.isPerfect_sl2 hp hp5
  have hX : Group.IsPerfect X :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card (ZMod p)) :=
    ⟨p, 1, hp, hp.odd_of_ne_two (by omega), le_rfl, by rw [Nat.card_zmod, pow_one]⟩
  exact three_inner_of_quot hX
    (QuotientGroup.congr (Subgroup.center X) _ e (Subgroup.map_center_eq e))
    (NQCat.T513.inner_of_odd_psl2 hodd
      (NQCat.T513.ringAut_mul_self hp le_rfl (by norm_num) (by rw [Nat.card_zmod, pow_one])))

theorem mem_of_sl2_hom {L T N : Subgroup Y} (hT2 : IsPGroup 2 ↥T) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (χ : ↥L →* Matrix.SpecialLinearGroup (Fin 2) (ZMod r))
    (hχ : Odd (Nat.card χ.ker)) {z : Y} (hzT : z ∈ T) (hzL : z ∈ L) (hz2 : z * z = 1)
    (hz1 : z ≠ 1) (hN : N ≤ T ⊓ L) (hN1 : N ≠ ⊥) : z ∈ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact r.Prime := ⟨hr⟩
  have hk : ringChar (ZMod r) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hr2
  have hinv : ∀ y : ↥L, y * y = 1 → y ≠ 1 → χ y = -1 := by
    intro y hy hy1
    have h1 : χ y ^ 2 = 1 := by rw [sq, ← map_mul, hy, map_one]
    rcases (CFSG.LocalAnalysis.ComponentInitial.sl2_sq_eq_one_iff hk _).mp h1 with h | h
    · exact absurd (eq_one_of_mul_self_of_odd hχ (MonoidHom.mem_ker.mpr h) hy) hy1
    · exact h
  have hNp : IsPGroup 2 ↥N := hT2.to_le (hN.trans inf_le_left)
  obtain ⟨n, hn⟩ := hNp.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    exact hN1 (Subgroup.eq_bot_of_card_eq N hn)
  obtain ⟨y, hy⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥N) 2 (by rw [hn]; exact dvd_pow_self 2 hn0)
  have hy2 : (y : Y) * y = 1 := by
    have h := pow_orderOf_eq_one y
    rw [hy, sq] at h
    simpa using congrArg Subtype.val h
  have hy1 : (y : Y) ≠ 1 := by
    intro h
    have : y = 1 := Subtype.ext h
    rw [this, orderOf_one] at hy
    omega
  have hyT : (y : Y) ∈ T := (hN y.2).1
  have hyL : (y : Y) ∈ L := (hN y.2).2
  have hχy := hinv ⟨y, hyL⟩ (Subtype.ext hy2) (fun h => hy1 (congrArg Subtype.val h))
  have hχz := hinv ⟨z, hzL⟩ (Subtype.ext hz2) (fun h => hz1 (congrArg Subtype.val h))
  have hmem : (⟨y, hyL⟩ : ↥L) * (⟨z, hzL⟩ : ↥L)⁻¹ ∈ χ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hχy, hχz, mul_inv_cancel]
  obtain ⟨k, hk'⟩ := hT2 ⟨(y : Y) * z⁻¹, T.mul_mem hyT (T.inv_mem hzT)⟩
  have hk2 : ((⟨y, hyL⟩ : ↥L) * (⟨z, hzL⟩ : ↥L)⁻¹) ^ 2 ^ k = 1 :=
    Subtype.ext (by simpa using congrArg Subtype.val hk')
  have hcop : Nat.Coprime (2 ^ k) (Nat.card χ.ker) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hχ)
  have h1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop
    (orderOf_dvd_of_pow_eq_one hk2) (Subgroup.orderOf_dvd_natCard χ.ker hmem))
  have hyz : (y : Y) = z := by
    have h2 : (y : Y) * z⁻¹ = 1 := by simpa using congrArg Subtype.val h1
    exact mul_inv_eq_one.mp h2
  rw [← hyz]
  exact y.2

theorem commutator_le_of_thirteen {B L : Subgroup Y} (h34 : A36Case3 ↥L ∨ A36Case4 ↥L)
    (hE : A36Extra ↥L) (hFO : CFSG.fittingSubgroup ↥L = CFSG.oddCore ↥L)
    (hOB : CFSG.oddCore ↥B = ⊥) (hBL : B ≤ L) (hBp : ⁅B, B⁆ = B) {z : Y} (hzB : z ∈ B)
    (hz2 : z * z = 1) (hz1 : z ≠ 1) (hzc : ∀ r ∈ B, r * z = z * r) {a a' : Y} (ha : a ∈ B)
    (ha' : a' ∈ B) (haa : a * a' ≠ a' * a) (hLBO : L = B ⊔ oddCoreSub L) :
    ⁅L ⊓ Subgroup.centralizer ({z} : Set Y), L ⊓ Subgroup.centralizer ({z} : Set Y)⁆ ≤ B := by
  have hzL : z ∈ L := hBL hzB
  set w : ↥L := ⟨z, hzL⟩ with hwdef
  have hw2 : w * w = 1 := Subtype.ext hz2
  have hw1 : w ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have hwF : w ∉ CFSG.fittingSubgroup ↥L := by
    rw [hFO]
    exact fun h => hw1 (eq_one_of_mul_self_of_odd CFSG.ABGLocalTools.odd_card_oddCore h hw2)
  set FA := (CFSG.fittingSubgroup ↥L).map L.subtype with hFA
  have hFAo : Odd (Nat.card FA) := by
    rw [hFA, Subgroup.card_map_of_injective L.subtype_injective, hFO]
    exact CFSG.ABGLocalTools.odd_card_oddCore
  have hBF : B ≤ Subgroup.normalizer (FA : Set Y) :=
    hBL.trans (Subgroup.le_normalizer.trans
      (SteinbergBS.normalizer_le_normalizer_map_characteristic L _))
  have hBz : B ≤ Subgroup.centralizer ({z} : Set Y) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hzc x hx)
  have hC : oddCoreSub L = FA := by
    show (CFSG.oddCore ↥L).map L.subtype = _
    rw [hFA, hFO]
  rw [hC] at hLBO
  have hKF : B.subgroupOf L ⊓ CFSG.fittingSubgroup ↥L = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxB', hxF⟩ := Subgroup.mem_inf.mp hx
    have hxB : (x : Y) ∈ B := Subgroup.mem_subgroupOf.mp hxB'
    have hN : ((FA ⊓ B).subgroupOf B).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right]
      intro t ht
      exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hBF ht, Subgroup.le_normalizer ht⟩
    have hNo : Odd (Nat.card ((FA ⊓ B).subgroupOf B)) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv]
      exact hFAo.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
    have hle := CFSG.ABGLocalTools.le_oddCore_of_normal hN hNo
    rw [hOB] at hle
    have hxm : (⟨(x : Y), hxB⟩ : ↥B) ∈ (FA ⊓ B).subgroupOf B :=
      Subgroup.mem_subgroupOf.mpr ⟨⟨x, hxF, rfl⟩, hxB⟩
    have h1 := hle hxm
    rw [Subgroup.mem_bot] at h1
    have h2 : (x : Y) = 1 := congrArg Subtype.val h1
    exact Subgroup.mem_bot.mpr (Subtype.ext h2)
  have hKp : ⁅B.subgroupOf L, B.subgroupOf L⁆ = B.subgroupOf L := by
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hBL]
    exact hBp
  have hwK : ∀ k ∈ B.subgroupOf L, k * w = w * k := fun k hk =>
    Subtype.ext (hzc _ (Subgroup.mem_subgroupOf.mp hk))
  have hk : (⟨a, hBL ha⟩ : ↥L) * ⟨a', hBL ha'⟩ ≠ ⟨a', hBL ha'⟩ * ⟨a, hBL ha⟩ :=
    fun h => haa (congrArg Subtype.val h)
  have hcp : ∀ c ∈ FA ⊓ Subgroup.centralizer ({z} : Set Y),
      (∀ x ∈ B, c * x = x * c) ∧
        ∀ c' ∈ FA ⊓ Subgroup.centralizer ({z} : Set Y), c * c' = c' * c := by
    rintro c ⟨⟨u, hu, rfl⟩, hcz⟩
    have hwu : w * u = u * w :=
      Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hcz).symm
    obtain ⟨h1, h2⟩ := Vol2.Ch10.SecB.SL2Inv.commute_props h34 hE hKF hKp
      (Subgroup.mem_subgroupOf.mpr ha) (Subgroup.mem_subgroupOf.mpr ha') hk hw2 hwF hwK hu hwu
    refine ⟨fun x hx =>
      congrArg Subtype.val (h1 ⟨x, hBL hx⟩ (Subgroup.mem_subgroupOf.mpr hx)), ?_⟩
    rintro _ ⟨⟨u', hu', rfl⟩, hcz'⟩
    have hwu' : w * u' = u' * w :=
      Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hcz').symm
    exact congrArg Subtype.val (h2 u' hu' hwu')
  refine commutator_le_of_forall_eq_mul (C := FA ⊓ Subgroup.centralizer ({z} : Set Y))
    (fun x hx => ?_) (fun c hc x hx => (hcp c hc).1 x hx)
    (fun c hc c' hc' => (hcp c hc).2 c' hc')
  have hx' : x ∈ ((B ⊔ FA : Subgroup Y) : Set Y) := by
    rw [← hLBO]
    exact hx.1
  rw [Subgroup.coe_mul_of_left_le_normalizer_right B FA hBF] at hx'
  obtain ⟨t, ht, c, hc, rfl⟩ := hx'
  refine ⟨t, ht, c, ⟨hc, ?_⟩, rfl⟩
  have h1 : t⁻¹ * (t * c) ∈ Subgroup.centralizer ({z} : Set Y) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (hBz ht)) hx.2
  rwa [inv_mul_cancel_left] at h1

theorem le_normalizer_of_case34 (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup Y) ≤ 2)
    {T B L D : Subgroup Y} (h34 : A36Case3 ↥L ∨ A36Case4 ↥L) (hE : A36Extra ↥L)
    (hFO : CFSG.fittingSubgroup ↥L = CFSG.oddCore ↥L) (hOB : CFSG.oddCore ↥B = ⊥)
    (hT : IsSylowTwoOf T ⊤) (hBL : B ≤ L) (hBp : ⁅B, B⁆ = B) (hLn : L.Normal)
    (hD3 : IsPGroup 3 D) (hDab : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x)
    (hDT : (D : Set Y) * (T : Set Y) = (T : Set Y) * (D : Set Y)) (hDL : ¬ D ≤ L)
    (hD3e : ∀ x ∈ D, x ^ 3 = 1) {z : Y} (hzB : z ∈ B) (hzT : z ∈ T) (hz2 : z * z = 1)
    (hz1 : z ≠ 1) (hzc : ∀ r ∈ B, r * z = z * r) (hTz : ∀ t ∈ T, t * z = z * t) {a a' : Y}
    (ha : a ∈ B) (ha' : a' ∈ B) (haa : a * a' ≠ a' * a)
    (hcase : (IsSL2 5 (↥B ⧸ CFSG.oddCore ↥B) ∧ L = B ⊔ oddCoreSub L) ∨
      (IsSL2 5 (↥B ⧸ CFSG.oddCore ↥B) ∧ ∃ p : ℕ, p.Prime ∧ p ^ 2 % 5 = 1 ∧
        (p % 8 = 3 ∨ p % 8 = 5) ∧ IsSL2 p (↥L ⧸ CFSG.oddCore ↥L)))
    {b : Y} (hbB : b ∈ B) (hbD : b ∈ D) (hb1 : b ≠ 1) (hb3 : b ^ 3 = 1) :
    D ≤ Subgroup.normalizer (B : Set Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzL : z ∈ L := hBL hzB
  obtain ⟨r, hr, hr5, χ, -, hχk⟩ := exists_sl2_surjection_of_case34 h34
  have hχo : Odd (Nat.card χ.ker) := by
    rw [hχk, hFO]
    exact CFSG.ABGLocalTools.odd_card_oddCore
  have hzT' : ∃ zT : Y, zT ≠ 1 ∧ ∀ N : Subgroup Y, N ≤ T ⊓ L →
      T ⊓ L ≤ Subgroup.normalizer (N : Set Y) → N ≠ ⊥ → zT ∈ N :=
    ⟨z, hz1, fun N hN _ hN1 => mem_of_sl2_hom hT.2.1 hr (by omega) χ hχo hzT hzL hz2 hz1 hN hN1⟩
  have hzo : orderOf z = 2 := orderOf_eq_prime (by rw [sq]; exact hz2) hz1
  have hDz := commute_of_unique_involution hrank hLn hT hzT' hBL hzo hzB hzc hTz hD3 hDab hD3e
    hDL hDT hbB hbD hb1
  set W := L ⊓ Subgroup.centralizer ({z} : Set Y) with hWdef
  have hBW : B ≤ W := le_inf hBL fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hzc x hx)
  have hDW : D ≤ Subgroup.normalizer (W : Set Y) := by
    intro d hd
    have := hLn
    refine Subgroup.inf_normalizer_le_normalizer_inf ⟨?_, Subgroup.le_normalizer
      (Subgroup.mem_centralizer_singleton_iff.mpr (hDz d hd))⟩
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top d
  rcases hcase with ⟨-, hLBO⟩ | ⟨-, p, hp, hp5, -, hLp⟩
  ·
    have hWB := commutator_le_of_thirteen h34 hE hFO hOB hBL hBp hzB hz2 hz1 hzc ha ha' haa hLBO
    exact fun d hd => mem_normalizer_of_commutator_le hBW hWB hBp (hDW hd)
  · have : Fact p.Prime := ⟨hp⟩
    have hp5' : 5 ≤ p := by
      have h2 := hp.two_le
      by_contra hlt
      have h4 : p ≤ 4 := by omega
      interval_cases p
      · norm_num at hp5
      · norm_num at hp5
      · norm_num at hp
    rcases h34 with h3 | h4
    ·
      have hw2 : (⟨z, hzL⟩ : ↥L) * ⟨z, hzL⟩ = 1 := Subtype.ext hz2
      have hwF : (⟨z, hzL⟩ : ↥L) ∉ CFSG.fittingSubgroup ↥L := by
        rw [hFO]
        exact fun h => hz1 (congrArg Subtype.val
          (eq_one_of_mul_self_of_odd CFSG.ABGLocalTools.odd_card_oddCore h hw2))
      have hFo : Odd (Nat.card (CFSG.fittingSubgroup ↥L)) := by
        rw [hFO]
        exact CFSG.ABGLocalTools.odd_card_oddCore
      have hbij := centralizer_bijective_of_case_three h3 hFo hw2 hwF
      have hcent : Subgroup.centralizer ({⟨z, hzL⟩} : Set ↥L) =
          (Subgroup.centralizer ({z} : Set Y)).subgroupOf L := by
        ext x
        rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf,
          Subgroup.mem_centralizer_singleton_iff]
        exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
      obtain ⟨eL⟩ := hLp
      have e1 : ↥W ≃* ↥(Subgroup.centralizer ({⟨z, hzL⟩} : Set ↥L)) :=
        (Subgroup.subgroupOfEquivOfLe (inf_le_left : W ≤ L)).symm.trans
          (MulEquiv.subgroupCongr (by rw [Subgroup.inf_subgroupOf_left, ← hcent]))
      have eW : ↥W ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod p) :=
        ((e1.trans (MulEquiv.ofBijective _ hbij)).trans
          (QuotientGroup.quotientMulEquivOfEq hFO)).trans eL
      have hZ2 : ∀ w ∈ Subgroup.center ↥W, w * w = 1 := by
        intro w hw
        have hc := A313.IsSL2.card_center hp (by omega) ⟨eW⟩
        have h := pow_card_eq_one' (G := ↥(Subgroup.center ↥W)) (x := ⟨w, hw⟩)
        rw [hc] at h
        rw [← sq]
        simpa using congrArg Subtype.val h
      have h3ne : (3 : ZMod p) ≠ 0 := by
        have h : ((3 : ℕ) : ZMod p) ≠ 0 := by
          rw [Ne, ZMod.natCast_eq_zero_iff]
          intro hd
          have := Nat.le_of_dvd (by norm_num) hd
          omega
        exact_mod_cast h
      exact le_normalizer_of_three_inner_sub (three_inner_of_sl2 hp hp5' eW)
        (ThreeRankLeOne.of_mulEquiv eW (FFB.threeRankLeOne_SL2_of_three_ne_zero h3ne)) hZ2 hBW
        hDW hD3e hbB (fun d hd => hDab d hd b hbD) hb1 hb3
    ·
      exfalso
      obtain ⟨-, -, h5, -⟩ := h4
      have h5' : IsSL2 5 (↥L ⧸ CFSG.oddCore ↥L) := by
        obtain ⟨e5⟩ := h5
        exact ⟨(QuotientGroup.quotientMulEquivOfEq hFO.symm).trans e5⟩
      have := A313.IsSL2.eq_of_isSL2 (by norm_num) hp h5' hLp
      subst this
      norm_num at hp5

theorem le_normalizer_of_nq (h36 : A36ForSQTK) (hY : SQTKHyp Y)
    (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup Y) ≤ 2) {T B L D : Subgroup Y}
    (hT : IsSylowTwoOf T ⊤) (hB : B ∈ lFamily T) (hA5 : IsAlt 5 (ModO2 B))
    (hL : L ∈ cComp ⊤) (hBL : B < L) (hLn : L.Normal) (hD3 : IsPGroup 3 D)
    (hDab : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x)
    (hDT : (D : Set Y) * (T : Set Y) = (T : Set Y) * (D : Set Y)) (hDL : ¬ D ≤ L)
    (hTB : T ≤ Subgroup.normalizer (B : Set Y)) (hD3e : ∀ x ∈ D, x ^ 3 = 1)
    (hcase : (IsSL2 5 (↥B ⧸ CFSG.oddCore ↥B) ∧ L = B ⊔ oddCoreSub L) ∨
      (IsSL2 5 (↥B ⧸ CFSG.oddCore ↥B) ∧ ∃ p : ℕ, p.Prime ∧ p ^ 2 % 5 = 1 ∧
        (p % 8 = 3 ∨ p % 8 = 5) ∧ IsSL2 p (↥L ⧸ CFSG.oddCore ↥L)))
    {b : Y} (hbB : b ∈ B) (hbD : b ∈ D) (hb3 : orderOf b = 3) :
    D ≤ Subgroup.normalizer (B : Set Y) := by
  have hBL' : B ≤ L := hBL.le
  have hBp : ⁅B, B⁆ = B := perfect_of_mem_cComp hB
  have hsylB : IsSylowTwoOf (T ⊓ B) B :=
    A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp hB)
      (A4.isSylowTwoOf_mono hT le_sup_right le_top)
  have hR5 : IsSL2 5 (↥B ⧸ CFSG.oddCore ↥B) := by rcases hcase with h | h <;> exact h.1
  have hOB := FiveNorm.oddCore_eq_bot_of_alt5 hA5 hR5
  obtain ⟨z, hzB, hz2, hz1, hzc, huniq, hzP, a, ha, a', ha', haa⟩ :=
    exists_central_involution_sl25 (isSL2_of_oddCore_eq_bot hOB hR5) hsylB
  have hPP : ⁅T ⊓ B, T ⊓ B⁆ ≤ T ⊓ B := Subgroup.commutator_le.mpr fun x hx y hy => by
    rw [commutatorElement_def]
    exact (T ⊓ B).mul_mem ((T ⊓ B).mul_mem ((T ⊓ B).mul_mem hx hy) ((T ⊓ B).inv_mem hx))
      ((T ⊓ B).inv_mem hy)
  have hzT : z ∈ T := (hPP hzP).1
  have hTz : ∀ s ∈ T, s * z = z * s := by
    intro s hs
    have hszB : s * z * s⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp (hTB hs) z).mp hzB
    have h2 : s * z * s⁻¹ * (s * z * s⁻¹) = 1 := by
      calc s * z * s⁻¹ * (s * z * s⁻¹) = s * (z * z) * s⁻¹ := by group
        _ = 1 := by rw [hz2, mul_one, mul_inv_cancel]
    rcases huniq _ hszB h2 with h | h
    · exfalso
      apply hz1
      calc z = s⁻¹ * (s * z * s⁻¹) * s := by group
        _ = 1 := by rw [h, mul_one, inv_mul_cancel]
    · calc s * z = s * z * s⁻¹ * s := by group
        _ = z * s := by rw [h]
  have hb1 : b ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hb3
    omega
  have hb3' : b ^ 3 = 1 := by rw [← hb3]; exact pow_orderOf_eq_one b
  obtain ⟨hconc, hcom, hextra⟩ := h36 Y hY L hL
  rcases hconc with ⟨hc, hs, -⟩ | ⟨hc, hZ3, -⟩ | h3 | h4
  ·
    refine (FiveNorm.false_of_quasisimple_nq hBL hc.1 ?_ (hBL' hzB) hz2 hz1 hcase).elim
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥L) with h | h
    · rw [h, Subgroup.card_bot]
      exact odd_one
    · exfalso
      obtain ⟨u, v, huv⟩ := hc.1.2.2
      apply huv
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective u
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective v
      have hx : (x : ↥L ⧸ Subgroup.center ↥L) = 1 :=
        (QuotientGroup.eq_one_iff x).mpr (by rw [h]; exact Subgroup.mem_top x)
      have hy : (y : ↥L ⧸ Subgroup.center ↥L) = 1 :=
        (QuotientGroup.eq_one_iff y).mpr (by rw [h]; exact Subgroup.mem_top y)
      rw [hx, hy]
  ·
    exact (FiveNorm.false_of_quasisimple_nq hBL hc.1 (by rw [hZ3]; decide) (hBL' hzB) hz2 hz1
      hcase).elim
  · exact le_normalizer_of_case34 hrank (Or.inl h3) (hextra (Or.inl h3)) hcom.1 hOB hT hBL' hBp
      hLn hD3 hDab hDT hDL hD3e hzB hzT hz2 hz1 hzc hTz ha ha' haa hcase hbB hbD hb1 hb3'
  · exact le_normalizer_of_case34 hrank (Or.inr h4) (hextra (Or.inr h4)) hcom.1 hOB hT hBL' hBp
      hLn hD3 hDab hDT hDL hD3e hzB hzT hz2 hz1 hzc hTz ha ha' haa hcase hbB hbD hb1 hb3'

end CFSG.Quasithin.H13.Ch9.TN
