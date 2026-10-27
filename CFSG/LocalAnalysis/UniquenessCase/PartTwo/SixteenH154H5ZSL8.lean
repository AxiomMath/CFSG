module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5Quot
public import CFSG.Quasithin.MS93.S32Nat
public import CFSG.Milestones.ASVolI.A3Aut.L2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5Cfg

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open Matrix

variable {W : Type} [CommGroup W]

private theorem s16h_commSub_stab_normalizer {L : Subgroup (MulAut W)} {g : MulAut W}
    (hg : g ∈ normalizer (L : Set (MulAut W))) : g ∈ stabSub (commSub ⊤ L) := by
  rw [mem_stabSub]
  have hnorm : ∀ x ∈ L, g * x * g⁻¹ ∈ L :=
    fun x hx => (Subgroup.mem_normalizer_iff.mp hg x).mp hx
  have hgNinv : g⁻¹ ∈ normalizer (L : Set (MulAut W)) :=
    (normalizer (L : Set (MulAut W))).inv_mem hg
  have hnorminv : ∀ x ∈ L, g⁻¹ * x * (g⁻¹)⁻¹ ∈ L :=
    fun x hx => (Subgroup.mem_normalizer_iff.mp hgNinv x).mp hx
  intro u
  constructor
  · intro hu
    have hmem : g⁻¹ (g u) ∈ commSub (⊤ : Subgroup W) L :=
      commSub_top_stable151b hnorminv (g u) hu
    simpa using hmem
  · intro hu
    exact commSub_top_stable151b hnorm u hu

private theorem s16h_fixV_stab_normalizer {L : Subgroup (MulAut W)} {g : MulAut W}
    (hg : g ∈ normalizer (L : Set (MulAut W))) : g ∈ stabSub (fixV L) := by
  rw [mem_stabSub]
  have hnorm : ∀ x ∈ L, g * x * g⁻¹ ∈ L :=
    fun x hx => (Subgroup.mem_normalizer_iff.mp hg x).mp hx
  have hgNinv : g⁻¹ ∈ normalizer (L : Set (MulAut W)) :=
    (normalizer (L : Set (MulAut W))).inv_mem hg
  have hnorminv : ∀ x ∈ L, g⁻¹ * x * (g⁻¹)⁻¹ ∈ L :=
    fun x hx => (Subgroup.mem_normalizer_iff.mp hgNinv x).mp hx
  intro u
  constructor
  · intro hu
    rw [mem_fixV] at hu ⊢
    intro l hl
    have h := hnorm l hl
    have h2 : (g * l * g⁻¹) (g u) = g u := hu (g * l * g⁻¹) h
    have h3 : g (l u) = (g * l * g⁻¹) (g u) := by simp [MulAut.mul_apply]
    exact g.injective (h3.trans h2)
  · intro hu
    rw [mem_fixV] at hu ⊢
    intro l hl
    have h := hnorminv l hl
    have h2 : (g⁻¹ * l * g) u = u := hu (g⁻¹ * l * g) h
    have h3 : l (g u) = g ((g⁻¹ * l * g) u) := by simp [MulAut.mul_apply]
    rw [h3, h2]

private theorem s16h_sl2_mulVec_e0_eq_of_ne_zero {K : Type} [Field K] {u : Fin 2 → K}
    (hu : u ≠ 0) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) K,
      (g : Matrix (Fin 2) (Fin 2) K).mulVec ![1, 0] = u := by
  by_cases h0 : u 0 = 0
  · have h1 : u 1 ≠ 0 := by
      intro h1
      exact hu (by ext i; fin_cases i <;> simp [h0, h1])
    refine ⟨⟨!![u 0, -(u 1)⁻¹; u 1, 0], ?_⟩, ?_⟩
    · simp [Matrix.det_fin_two, h1]
    · ext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · refine ⟨⟨!![u 0, 0; u 1, (u 0)⁻¹], ?_⟩, ?_⟩
    · simp [Matrix.det_fin_two, h0]
    · ext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private theorem s16h_sl2_mulVec_eq_of_ne_zero {K : Type} [Field K] {u v : Fin 2 → K}
    (hu : u ≠ 0) (hv : v ≠ 0) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) K,
      (g : Matrix (Fin 2) (Fin 2) K).mulVec u = v := by
  obtain ⟨a, ha⟩ := s16h_sl2_mulVec_e0_eq_of_ne_zero hu
  obtain ⟨b, hb⟩ := s16h_sl2_mulVec_e0_eq_of_ne_zero hv
  refine ⟨b * a⁻¹, ?_⟩
  have h1 : ((a⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K).mulVec u = ![1, 0] := by
    rw [← ha, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul,
      inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, h1, hb]

private theorem s16h_isTransNZ_statedSL_two (K : Type) [Field K] :
    CFSG.Quasithin.MS93.S32.IsTransNZ (CFSG.Open.StatedSL 2 K) := by
  intro x y hx hy
  obtain ⟨g, hg⟩ := s16h_sl2_mulVec_eq_of_ne_zero (K := K) hx hy
  refine ⟨CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K g, ?_⟩
  rw [CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe]
  exact hg

private theorem s16h_H5_SL8_odd [Finite W] {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t)
    (h : s16h_H5RowSL2 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 3)
    {y : MulAut W} (hyN : y ∈ A ⊓ normalizer (L : Set (MulAut W)))
    (hyc : ∀ l ∈ L, l * y = y * l) :
    ∃ c : ℕ, Odd c ∧ y ^ c ∈ centSub (commSub ⊤ L ⊓ fixV L) := by
  set U : Subgroup W := commSub ⊤ L with hU
  set Z : Subgroup W := commSub ⊤ L ⊓ fixV L with hZ
  have hyNorm : y ∈ normalizer (L : Set (MulAut W)) := (Subgroup.mem_inf.mp hyN).2
  set N : Subgroup (MulAut W) := A ⊓ normalizer (L : Set (MulAut W)) with hN
  obtain ⟨K, hKf, hKfin, hKcard, π, hπ⟩ := h.2
  letI : Field K := hKf
  letI : Finite K := hKfin
  have htrans : CFSG.Quasithin.MS93.S32.IsTransNZ (CFSG.Open.StatedSL 2 K) :=
    s16h_isTransNZ_statedSL_two K
  have hirr : ∀ J : Subgroup W, (∀ x ∈ L, ∀ w ∈ J, x w ∈ J) → Z ≤ J → J ≤ U →
      J = Z ∨ J = U :=
    fun J hJ hZJ hJU => CFSG.Quasithin.MS93.S32.natReal_inv_eq htrans hπ hJ hZJ hJU
  have hZU : Z < U :=
    lt_of_le_of_ne inf_le_left (Ne.symm (CFSG.Quasithin.MS93.S32.natReal_ne (π := π) hπ))
  have hLU : L ≤ stabSub U := fun l hl => s16h_commSub_stab_normalizer (Subgroup.le_normalizer hl)
  have hLZ : L ≤ stabSub Z := fun l hl =>
    centSub_le_stabSub Z (mem_centSub.mpr fun z hz => mem_fixV.mp hz.2 l hl)
  have hNU : N ≤ stabSub U := fun g hg => s16h_commSub_stab_normalizer hg.2
  have hNZ : N ≤ stabSub Z := by
    intro g hg
    rw [mem_stabSub]
    intro z
    constructor
    · intro hz
      exact ⟨(mem_stabSub.mp (s16h_commSub_stab_normalizer hg.2) z).1 hz.1,
        (mem_stabSub.mp (s16h_fixV_stab_normalizer hg.2) z).1 hz.2⟩
    · intro hz
      exact ⟨(mem_stabSub.mp (s16h_commSub_stab_normalizer hg.2) z).2 hz.1,
        (mem_stabSub.mp (s16h_fixV_stab_normalizer hg.2) z).2 hz.2⟩
  have hLN : L ≤ N := fun l hl => ⟨hc.comp.1 hl, Subgroup.le_normalizer hl⟩
  have hisec : XMod.IsIrrSec ↥(autSec L U Z) (⊥ : Subgroup (Sec U Z)) ⊤ :=
    B5.isIrrSec_autSec (L := L) (W := U) (C := Z) hZU hirr hLU hLZ
  have hSecSq : ∀ w : Sec U Z, w * w = 1 := by
    intro w
    induction w using QuotientGroup.induction_on with
    | H u =>
      change QuotientGroup.mk u * QuotientGroup.mk u = 1
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_one]
      exact congrArg QuotientGroup.mk
        (Subtype.ext (by rw [← pow_two]; exact hc.elem (u : W)))
  have hirrOn : CFSG.QuasithinUnique.Setup.X1.IsIrrOn (autSec L U Z) := by
    refine ⟨?_, fun J hJ => hisec.2 J (fun a u hu => hJ a a.2 u hu) bot_le le_top⟩
    rw [_root_.nontrivial_iff]
    have hnt : Nontrivial ↥(⊤ : Subgroup (Sec U Z)) :=
      (Subgroup.nontrivial_iff_ne_bot ⊤).mpr (bot_lt_iff_ne_bot.mp hisec.1)
    rw [_root_.nontrivial_iff] at hnt
    obtain ⟨a, b, hab⟩ := hnt
    exact ⟨Subgroup.topEquiv a, Subgroup.topEquiv b,
      fun h => hab (Subgroup.topEquiv.injective h)⟩
  let cy : MulAut (Sec U Z) := B5.secHom N hNU hNZ ⟨y, hyN⟩
  have hcomm : ∀ l ∈ autSec L U Z, l * cy = cy * l := by
    intro l hl
    rw [← B5.map_secHom_eq_autSec (X := N) hNU hNZ (hLX := hLN)] at hl
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hl
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hyc (a.1 : MulAut W) (Subgroup.mem_subgroupOf.mp ha))
  have hodd : Odd (orderOf cy) :=
    CFSG.QuasithinUnique.Setup.X1.odd_orderOf_of_commutes hSecSq hirrOn hcomm
  refine ⟨orderOf cy, hodd, ?_⟩
  have hker : (⟨y, hyN⟩ : ↥N) ^ orderOf cy ∈ (B5.secHom N hNU hNZ).ker := by
    rw [MonoidHom.mem_ker, map_pow]
    change cy ^ orderOf cy = 1
    exact pow_orderOf_eq_one cy
  have hcent : y ^ orderOf cy ∈ centSec U Z := by
    have h := (B5.mem_ker_secHom N hNU hNZ ((⟨y, hyN⟩ : ↥N) ^ orderOf cy)).mp hker
    simpa only [Subgroup.coe_pow] using h
  intro z hz
  exact s16h_H5_triv_of_triv_quot hc.comp
    ((normalizer (L : Set (MulAut W))).pow_mem hyNorm (orderOf cy))
      (mem_centSec.mp hcent).2 z hz.1

private theorem s16h_psl2_cube_mem_inner {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ 3) {β : MulAut (CFSG.GorensteinWalter.PSL2 K)}
    (hβ : β ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
        (CFSG.GorensteinWalter.PSL2 K) ⊔ (CFSG.GorensteinWalter.psl2FieldAut K).range) :
    β ^ 3 ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (CFSG.GorensteinWalter.PSL2 K) := by
  let INN := CFSG.ComponentClassification.OuterAutomorphisms.inner (CFSG.GorensteinWalter.PSL2 K)
  let Φ := (CFSG.GorensteinWalter.psl2FieldAut K).range
  haveI : INN.Normal := CFSG.ComponentClassification.OuterAutomorphisms.innerNormal _
  let q : MulAut (CFSG.GorensteinWalter.PSL2 K) →*
      MulAut (CFSG.GorensteinWalter.PSL2 K) ⧸ INN := QuotientGroup.mk' INN
  have hmapbot : INN.map q = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    intro x hx
    rw [QuotientGroup.ker_mk']
    exact hx
  have hqβ : q β ∈ Φ.map q := by
    have h : q β ∈ (INN ⊔ Φ).map q := Subgroup.mem_map_of_mem q hβ
    rwa [Subgroup.map_sup, hmapbot, bot_sup_eq] at h
  have hΦcard : Nat.card Φ = 3 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective
      (CFSG.GorensteinWalter.psl2FieldAut_injective K)).toEquiv]
    exact (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic
      Nat.prime_two K hK).1
  have hz3 : (q β) ^ 3 = 1 := by
    have hdiv : orderOf (q β) ∣ Nat.card (Φ.map q) :=
      Subgroup.orderOf_dvd_natCard (Φ.map q) hqβ
    have hdiv' : Nat.card (Φ.map q) ∣ 3 := by
      rw [← hΦcard]
      exact Subgroup.card_map_dvd Φ q
    exact orderOf_dvd_iff_pow_eq_one.mp (hdiv.trans hdiv')
  have hq3 : q (β ^ 3) = 1 := by
    rw [map_pow]
    exact hz3
  change β ^ 3 ∈ INN
  rw [← QuotientGroup.ker_mk' INN, MonoidHom.mem_ker]
  exact hq3

theorem s16h_H5_zcond_SL8_cube_inner [Finite W] {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t)
    (h : s16h_H5RowSL2 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 3) :
    ∀ x ∈ A ⊓ normalizer (L : Set (MulAut W)),
      ∃ l₀ ∈ L, ∀ l ∈ L, x ^ 3 * l * (x ^ 3)⁻¹ = l₀ * l * l₀⁻¹ := by
  intro x hxN
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e₁⟩⟩ := h.1
  letI : Field K := hKf
  letI : Finite K := hKfin
  letI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP K 2 :=
    charP_of_card_eq_prime_pow (by rw [Fintype.card_eq_nat_card, hKcard])
  letI : CharP K 2 := hchar
  have hcenter := CFSG.Walter.sl2_center_eq_bot_of_charTwo (K := K)
  let slEquiv : Matrix.SpecialLinearGroup (Fin 2) K ≃* CFSG.GorensteinWalter.PSL2 K :=
    ((QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot).symm
  let e : ↥L ≃* CFSG.GorensteinWalter.PSL2 K :=
    e₁.trans ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K).symm.trans slEquiv)
  let α : MulAut ↥L := L.normalizerMonoidHom ⟨x, hxN.2⟩
  have hβmem : MulAut.congr e α ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner (CFSG.GorensteinWalter.PSL2 K) ⊔
        (CFSG.GorensteinWalter.psl2FieldAut K).range :=
    CFSG.ASVolI.burnsideAut_psl2_aut_mem (K := K) (MulAut.congr e α)
  have hβ3 : (MulAut.congr e α) ^ 3 ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner
        (CFSG.GorensteinWalter.PSL2 K) :=
    s16h_psl2_cube_mem_inner hKcard hβmem
  have hα3 : α ^ 3 ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥L := by
    have h1 : MulAut.congr e (α ^ 3) ∈
        (CFSG.ComponentClassification.OuterAutomorphisms.inner ↥L).map
          (MulAut.congr e).toMonoidHom := by
      rw [CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr e, map_pow]
      exact hβ3
    obtain ⟨b, hb, hbe⟩ := Subgroup.mem_map.mp h1
    have hb' : b = α ^ 3 := (MulAut.congr e).injective hbe
    rwa [hb'] at hb
  rw [CFSG.ComponentClassification.OuterAutomorphisms.inner] at hα3
  obtain ⟨l₀, hl₀⟩ := hα3
  refine ⟨l₀, l₀.2, fun l hl => ?_⟩
  have hαpow : ∀ (k : ℕ) (a : ↥L),
      ((α ^ k) a : MulAut W) = x ^ k * (a : MulAut W) * (x ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro a; simp
    | succ k ih =>
      intro a
      rw [pow_succ, pow_succ]
      change ((α ^ k) (α a) : MulAut W) = x ^ k * x * (a : MulAut W) * (x ^ k * x)⁻¹
      rw [ih (α a)]
      have hαa : (α a : MulAut W) = x * (a : MulAut W) * x⁻¹ :=
        Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨x, hxN.2⟩ a
      rw [hαa]
      group
  have hconjapply : (MulAut.conj l₀ ⟨l, hl⟩ : MulAut W) =
      (l₀ : MulAut W) * l * (l₀ : MulAut W)⁻¹ := by
    simp [MulAut.conj_apply]
  have hfinal := congrArg (fun φ : MulAut ↥L => (φ ⟨l, hl⟩ : MulAut W)) hl₀
  rw [hconjapply, hαpow 3 ⟨l, hl⟩] at hfinal
  simpa using hfinal.symm

theorem s16h_H5_zcond_SL8 [Finite W] {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t)
    (h : s16h_H5RowSL2 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 3) :
    ∀ x ∈ A ⊓ normalizer (L : Set (MulAut W)),
      (∃ n : ℕ, x ^ 2 ^ n ∈ centSub (commSub ⊤ L ⊓ fixV L)) →
        x ∈ centSub (commSub ⊤ L ⊓ fixV L) := by
  intro x hxN hx2
  set Z : Subgroup W := commSub ⊤ L ⊓ fixV L with hZ
  obtain ⟨n, hn⟩ := hx2
  obtain ⟨l₀, hl₀, hconj⟩ := s16h_H5_zcond_SL8_cube_inner hc h x hxN
  set y : MulAut W := (l₀ : MulAut W)⁻¹ * x ^ 3 with hy
  have hyN : y ∈ A ⊓ normalizer (L : Set (MulAut W)) :=
    (A ⊓ normalizer (L : Set (MulAut W))).mul_mem
      ((A ⊓ normalizer (L : Set (MulAut W))).inv_mem
        ⟨hc.comp.1 hl₀, Subgroup.le_normalizer hl₀⟩)
      ⟨A.pow_mem hxN.1 3, (normalizer (L : Set (MulAut W))).pow_mem hxN.2 3⟩
  have hyc : ∀ l ∈ L, l * y = y * l := by
    intro l hl
    have h := hconj l hl
    have hconj' : y * l * y⁻¹ = l := by
      rw [hy]
      calc (l₀ : MulAut W)⁻¹ * x ^ 3 * l * ((l₀ : MulAut W)⁻¹ * x ^ 3)⁻¹ =
          (l₀ : MulAut W)⁻¹ * (x ^ 3 * l * (x ^ 3)⁻¹) * (l₀ : MulAut W) := by group
        _ = (l₀ : MulAut W)⁻¹ * ((l₀ : MulAut W) * l * (l₀ : MulAut W)⁻¹) *
              (l₀ : MulAut W) := by rw [h]
        _ = l := by group
    calc l * y = (y * l * y⁻¹) * y := by rw [hconj']
      _ = y * l := by group
  obtain ⟨c, hcodd, hycZ⟩ := s16h_H5_SL8_odd hc h hyN hyc
  have hx3c : x ^ (3 * c) ∈ centSub Z := by
    have hx3 : x ^ 3 = (l₀ : MulAut W) * y := by rw [hy]; group
    have hcomm : Commute (l₀ : MulAut W) y := hyc (l₀ : MulAut W) hl₀
    have hpow : x ^ (3 * c) = (l₀ : MulAut W) ^ c * y ^ c := by
      rw [pow_mul, hx3, hcomm.mul_pow]
    rw [hpow]
    exact (centSub Z).mul_mem
      ((centSub Z).pow_mem
        (mem_centSub.mpr fun z hz => mem_fixV.mp hz.2 (l₀ : MulAut W) hl₀) c)
      hycZ
  obtain ⟨k, hk⟩ := hcodd
  have h3codd : Odd (3 * c) := ⟨3 * k + 1, by rw [hk]; ring⟩
  have hcop : Nat.Coprime (2 ^ n) (3 * c) :=
    (Nat.coprime_two_left.mpr h3codd).pow_left n
  have hexp : (1 : ℤ) = (2 ^ n : ℤ) * Nat.gcdA (2 ^ n) (3 * c) +
      (3 * c : ℤ) * Nat.gcdB (2 ^ n) (3 * c) := by
    have h := Nat.gcd_eq_gcd_ab (2 ^ n) (3 * c)
    rw [hcop.gcd_eq_one] at h
    simpa using h
  have hx : x = (x ^ 2 ^ n) ^ (Nat.gcdA (2 ^ n) (3 * c)) *
      (x ^ (3 * c)) ^ (Nat.gcdB (2 ^ n) (3 * c)) := by
    conv_lhs => rw [← zpow_one x, hexp]
    rw [_root_.zpow_add, _root_.zpow_mul, _root_.zpow_mul]
    rw [show (3 : ℤ) * (c : ℤ) = ((3 * c : ℕ) : ℤ) by push_cast; ring]
    rfl
  rw [hx]
  exact (centSub Z).mul_mem ((centSub Z).zpow_mem hn _) ((centSub Z).zpow_mem hx3c _)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
