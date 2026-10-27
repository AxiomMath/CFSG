module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34FiveMain
public import CFSG.Quasithin.Vol2.Ch5Sec1L34FiveL2Z
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113NQBase
public import CFSG.LieType.Simplicity.Basic
public import CFSG.Quasithin.Background.C1GNC124
public import CFSG.Quasithin.Background.C1PackSolvBasic
public import CFSG.Quasithin.Background.E2Statements
public import CFSG.Quasithin.Vol2.Ch10SecA1011
public import CFSG.Quasithin.Vol2.Ch10SecA1012Three
public import CFSG.Quasithin.Vol2.Ch10SecC8Main12
public import CFSG.Quasithin.Vol2.Ch10SecC9Entry
public import CFSG.Quasithin.Vol2.Ch10SecC9L32
public import CFSG.Quasithin.Vol2.Ch10SecC9S5c
public import CFSG.Quasithin.Vol2.Ch10SecEE3ProdC
public import CFSG.Quasithin.Vol2.Ch10SecQ9G10
public import CFSG.Quasithin.Vol2.Ch10SecQ9G11
public import CFSG.Quasithin.Vol2.Ch10SecQ9H9
public import CFSG.Quasithin.Vol2.Ch11SecAFacts12b

public section

namespace CFSG.Quasithin.H13.FiveNorm

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank
open CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

theorem oddCore_eq_bot_of_alt5 {R : Type} [Group R] [Finite R]
    (h1 : IsAlt 5 (R ⧸ CFSG.pCore 2 R)) (h2 : IsSL2 5 (R ⧸ CFSG.oddCore R)) :
    CFSG.oddCore R = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨e5⟩ := h1
  have hs : IsSimpleGroup (R ⧸ CFSG.pCore 2 R) := e5.isSimpleGroup
  have hN : ((CFSG.oddCore R).map (QuotientGroup.mk' (CFSG.pCore 2 R))).Normal :=
    (CFSG.oddCore_normal (G := R)).map _ (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((CFSG.oddCore R).map (QuotientGroup.mk' (CFSG.pCore 2 R))) with h | h
  · rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    have hp : IsPGroup 2 ↥(CFSG.oddCore R) := CFSG.pCore_isPGroup.to_le h
    have ho := CFSG.ABGLocalTools.odd_card_oddCore (H := R)
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
    rw [hk] at ho
    have hk0 : k = 0 := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · exact h0
      · exact absurd (Nat.even_pow.mpr ⟨even_two, h0.ne'⟩) (Nat.not_even_iff_odd.mpr ho)
    rw [hk0, pow_zero] at hk
    exact Subgroup.eq_bot_of_card_eq _ hk
  · exfalso
    have hsup : CFSG.oddCore R ⊔ CFSG.pCore 2 R = ⊤ := by
      have := Subgroup.comap_map_eq (QuotientGroup.mk' (CFSG.pCore 2 R)) (CFSG.oddCore R)
      rw [h, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
      exact this.symm
    have hmap : (CFSG.pCore 2 R).map (QuotientGroup.mk' (CFSG.oddCore R)) = ⊤ := by
      have h1 := congrArg (Subgroup.map (QuotientGroup.mk' (CFSG.oddCore R))) hsup
      rw [Subgroup.map_sup, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h1
      have h0 : (CFSG.oddCore R).map (QuotientGroup.mk' (CFSG.oddCore R)) = ⊥ := by
        rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
      rw [h0, bot_sup_eq] at h1
      exact h1
    have hp : IsPGroup 2 (R ⧸ CFSG.oddCore R) := by
      have := (CFSG.pCore_isPGroup (p := 2) (G := R)).map (QuotientGroup.mk' (CFSG.oddCore R))
      rw [hmap] at this
      exact this.of_equiv Subgroup.topEquiv
    obtain ⟨e⟩ := h2
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hp.of_equiv e)
    rw [SL2MinimalFaithful.card_specialLinearGroup_fin_two, Nat.card_zmod] at hk
    have h3 : 3 ∣ 2 ^ k := by rw [← hk]; norm_num
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)

theorem isPGroup_center_of_sl2 {W : Type} [Group W] {p : ℕ}
    (e : W ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) : IsPGroup 2 (Subgroup.center W) := by
  intro g
  refine ⟨1, ?_⟩
  have hg : e (g : W) ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) := by
    rw [← Subgroup.map_center_eq e]
    exact ⟨g, g.2, rfl⟩
  obtain ⟨c, hc2, hcA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hg
  have hc : c * c = 1 := by
    rw [← sq]
    simpa using hc2
  have h1 : e ((g : W) * g) = 1 := by
    rw [map_mul]
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, ← hcA, ← map_mul, hc, map_one,
      Matrix.SpecialLinearGroup.coe_one]
  have h2 : (g : W) * g = 1 := e.injective (by rw [h1, map_one])
  apply Subtype.ext
  rw [pow_one, sq, Subgroup.coe_mul, h2, Subgroup.coe_one]

variable {Y : Type} [Group Y] [Finite Y]

theorem false_of_quasisimple_nq {B L : Subgroup Y} (hBL : B < L) (hLq : CFSG.IsQuasisimple ↥L)
    (hZ : Odd (Nat.card (Subgroup.center ↥L))) {z : Y} (hzL : z ∈ L) (hz2 : z * z = 1)
    (hz1 : z ≠ 1)
    (hcase : (IsSL2 5 (↥B ⧸ CFSG.oddCore ↥B) ∧ L = B ⊔ oddCoreSub L) ∨
      (IsSL2 5 (↥B ⧸ CFSG.oddCore ↥B) ∧ ∃ p : ℕ, p.Prime ∧ p ^ 2 % 5 = 1 ∧
        (p % 8 = 3 ∨ p % 8 = 5) ∧ IsSL2 p (↥L ⧸ CFSG.oddCore ↥L))) : False := by
  have hw2 : (⟨z, hzL⟩ : ↥L) * ⟨z, hzL⟩ = 1 := Subtype.ext hz2
  have hwO : (⟨z, hzL⟩ : ↥L) ∉ CFSG.oddCore ↥L := fun h =>
    hz1 (congrArg Subtype.val
      (eq_one_of_mul_self_of_odd CFSG.ABGLocalTools.odd_card_oddCore h hw2))
  have hOZ : CFSG.oddCore ↥L ≤ Subgroup.center ↥L := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hLq (CFSG.oddCore_normal (G := ↥L)) with
      h | h
    · exfalso
      apply hwO
      rw [h]
      exact Subgroup.mem_top _
    · exact h
  have hZO : Subgroup.center ↥L ≤ CFSG.oddCore ↥L :=
    CFSG.ABGLocalTools.le_oddCore_of_normal inferInstance hZ
  rcases hcase with ⟨-, hLBO⟩ | ⟨-, p, hp, -, hp8, ⟨eL⟩⟩
  ·
    have hcen : ∀ c ∈ oddCoreSub L, ∀ x ∈ L, c * x = x * c := by
      rintro _ ⟨u, hu, rfl⟩ x hx
      have h := Subgroup.mem_center_iff.mp (hOZ hu) ⟨x, hx⟩
      exact (congrArg Subtype.val h).symm
    have hCL : oddCoreSub L ≤ L := by
      rintro _ ⟨u, -, rfl⟩
      exact u.2
    have hBN : B ≤ Subgroup.normalizer (oddCoreSub L : Set Y) := by
      intro r hr
      rw [Subgroup.mem_normalizer_iff]
      intro c
      have hrL : r ∈ L := hBL.le hr
      constructor
      · intro hc
        have e1 : r * c * r⁻¹ = c := by rw [← hcen c hc r hrL]; group
        rw [e1]
        exact hc
      · intro hc
        have h1 := hcen _ hc r⁻¹ (L.inv_mem hrL)
        have e1 : c = r * c * r⁻¹ := by
          calc c = r⁻¹ * (r * c * r⁻¹) * r := by group
            _ = r * c * r⁻¹ * r⁻¹ * r := by rw [← h1]
            _ = r * c * r⁻¹ := by group
        rw [e1]
        exact hc
    have hLB : L ≤ B := by
      have hperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp hLq.1
      rw [← hperf]
      refine commutator_le_of_forall_eq_mul (C := oddCoreSub L) (fun x hx => ?_)
        (fun c hc r hr => hcen c hc r (hBL.le hr)) (fun c hc c' hc' => hcen c hc c' (hCL hc'))
      have hx' : x ∈ ((B ⊔ oddCoreSub L : Subgroup Y) : Set Y) := by
        rw [← hLBO]
        exact hx
      rw [Subgroup.coe_mul_of_left_le_normalizer_right B (oddCoreSub L) hBN] at hx'
      obtain ⟨r, hr, c, hc, rfl⟩ := hx'
      exact ⟨r, hr, c, hc, rfl⟩
    exact absurd hLB (not_le_of_gt hBL)
  ·
    have hOeq : CFSG.oddCore ↥L = Subgroup.center ↥L := le_antisymm hOZ hZO
    have : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hLq.2.1
    have hs : IsSimpleGroup (↥L ⧸ CFSG.oddCore ↥L) :=
      (QuotientGroup.quotientMulEquivOfEq hOeq).isSimpleGroup
    have hsl : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) :=
      eL.symm.isSimpleGroup
    have : Fact p.Prime := ⟨hp⟩
    exact not_isSimpleGroup_sl2_of_ringChar (k := ZMod p) (by rw [ZMod.ringChar_zmod_n]; omega) hsl

theorem le_normalizer_of_case34
    {T B L D : Subgroup Y} (h34 : A36Case3 ↥L ∨ A36Case4 ↥L)
    (hE : A36Extra ↥L) (hFO : CFSG.fittingSubgroup ↥L = CFSG.oddCore ↥L)
    (hOB : CFSG.oddCore ↥B = ⊥) (hT : IsSylowTwoOf T ⊤) (hBL : B ≤ L) (hBp : ⁅B, B⁆ = B)
    (hA5 : IsAlt 5 (ModO2 B)) (hsylB : IsSylowTwoOf (T ⊓ B) B) (hD : Nat.card D = 5)
    (hDN : D ≤ Subgroup.normalizer (L : Set Y)) (hTN : T ≤ Subgroup.normalizer (L : Set Y))
    (hDT : (D : Set Y) * (T : Set Y) = (T : Set Y) * (D : Set Y)) {z : Y} (hzB : z ∈ B)
    (hz2 : z * z = 1) (hz1 : z ≠ 1) (hzc : ∀ r ∈ B, r * z = z * r)
    (hTz : T ≤ Subgroup.centralizer ({z} : Set Y)) (hzP : z ∈ ⁅T ⊓ B, T ⊓ B⁆) {a a' : Y}
    (ha : a ∈ B) (ha' : a' ∈ B) (haa : a * a' ≠ a' * a)
    (hcase : (IsSL2 5 (↥B ⧸ CFSG.oddCore ↥B) ∧ L = B ⊔ oddCoreSub L) ∨
      (IsSL2 5 (↥B ⧸ CFSG.oddCore ↥B) ∧ ∃ p : ℕ, p.Prime ∧ p ^ 2 % 5 = 1 ∧
        (p % 8 = 3 ∨ p % 8 = 5) ∧ IsSL2 p (↥L ⧸ CFSG.oddCore ↥L)))
    {b : Y} (hbB : b ∈ B) (hb3 : orderOf b = 3)
    (hbT : b ∈ Subgroup.normalizer ((T ⊓ B : Subgroup Y) : Set Y))
    (hbD : ∀ d ∈ D, d * b = b * d) : D ≤ Subgroup.normalizer (B : Set Y) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
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
  have hNF : Subgroup.normalizer (L : Set Y) ≤ Subgroup.normalizer (FA : Set Y) :=
    SteinbergBS.normalizer_le_normalizer_map_characteristic L _
  have hDF : D ≤ Subgroup.normalizer (FA : Set Y) := hDN.trans hNF
  have hTF : T ≤ Subgroup.normalizer (FA : Set Y) := hTN.trans hNF
  have hBF : B ≤ Subgroup.normalizer (FA : Set Y) :=
    hBL.trans (Subgroup.le_normalizer.trans hNF)
  obtain ⟨r, hr, hr5, χ, -, hχk⟩ := exists_sl2_surjection_of_case34 h34
  have : Fact r.Prime := ⟨hr⟩
  have hkr : ringChar (ZMod r) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; omega
  have hχinv : ∀ y : ↥L, y * y = 1 → y ∉ CFSG.fittingSubgroup ↥L → χ y = -1 := by
    intro y hy hyF
    have h1 : χ y ^ 2 = 1 := by rw [sq, ← map_mul, hy, map_one]
    rcases (LocalAnalysis.ComponentInitial.sl2_sq_eq_one_iff hkr _).mp h1 with h | h
    · exact absurd (hχk ▸ MonoidHom.mem_ker.mpr h) hyF
    · exact h
  have hdz : ∀ d ∈ D, d * z * d⁻¹ * z⁻¹ ∈ FA := by
    intro d hd
    have hdzL : d * z * d⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hDN hd) z).mp hzL
    set y : ↥L := ⟨d * z * d⁻¹, hdzL⟩ with hydef
    have hy2 : y * y = 1 := by
      apply Subtype.ext
      show d * z * d⁻¹ * (d * z * d⁻¹) = 1
      calc d * z * d⁻¹ * (d * z * d⁻¹) = d * (z * z) * d⁻¹ := by group
        _ = 1 := by rw [hz2, mul_one, mul_inv_cancel]
    have hyF : y ∉ CFSG.fittingSubgroup ↥L := by
      intro hy
      have h1 : d * z * d⁻¹ ∈ FA := ⟨y, hy, rfl⟩
      have h2 : d⁻¹ * (d * z * d⁻¹) * d⁻¹⁻¹ ∈ FA :=
        (Subgroup.mem_normalizer_iff.mp (hDF (D.inv_mem hd)) _).mp h1
      have h3 : d⁻¹ * (d * z * d⁻¹) * d⁻¹⁻¹ = z := by group
      rw [h3] at h2
      obtain ⟨u, hu, hu'⟩ := h2
      apply hwF
      have hu2 : u = w := Subtype.ext hu'
      rw [← hu2]
      exact hu
    have hyw : χ y = χ w := by rw [hχinv y hy2 hyF, hχinv w hw2 hwF]
    have hmem : y * w⁻¹ ∈ CFSG.fittingSubgroup ↥L := by
      rw [← hχk, MonoidHom.mem_ker, map_mul, map_inv, hyw, mul_inv_cancel]
    exact ⟨y * w⁻¹, hmem, rfl⟩
  have hDc : IsCyclic ↥D := isCyclic_of_prime_card hD
  have hDo : Odd (Nat.card D) := by rw [hD]; decide
  have hDz : D ≤ Subgroup.centralizer ({z} : Set Y) := fun d hd =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (commute_of_commutator_mem hDc hDo hT.2.1 hDT hFAo hDF hTF inf_le_left hzP hz2 hd
        (hdz d hd))
  set W := L ⊓ Subgroup.centralizer ({z} : Set Y) with hWdef
  have hBz : B ≤ Subgroup.centralizer ({z} : Set Y) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hzc x hx)
  have hBW : B ≤ W := le_inf hBL hBz
  have hDW : D ≤ Subgroup.normalizer (W : Set Y) := fun d hd =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hDN hd, Subgroup.le_normalizer (hDz hd)⟩
  rcases hcase with ⟨-, hLBO⟩ | ⟨-, p, hp, hp5, hp8, hLp⟩
  ·
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
    have hWB : ⁅W, W⁆ ≤ B := by
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
    exact fun d hd => mem_normalizer_of_commutator_le hBW hWB hBp (hDW hd)
  ·
    rcases h34 with h3 | h4
    ·
      have hFo : Odd (Nat.card (CFSG.fittingSubgroup ↥L)) := by
        rw [hFO]
        exact CFSG.ABGLocalTools.odd_card_oddCore
      have hbij := centralizer_bijective_of_case_three h3 hFo hw2 hwF
      have hcent : Subgroup.centralizer ({w} : Set ↥L) =
          (Subgroup.centralizer ({z} : Set Y)).subgroupOf L := by
        ext x
        rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf,
          Subgroup.mem_centralizer_singleton_iff]
        exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
      obtain ⟨eL⟩ := hLp
      have e1 : ↥W ≃* ↥(Subgroup.centralizer ({w} : Set ↥L)) :=
        (Subgroup.subgroupOfEquivOfLe (inf_le_left : W ≤ L)).symm.trans
          (MulEquiv.subgroupCongr (by rw [Subgroup.inf_subgroupOf_left, ← hcent]))
      have eW : ↥W ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod p) :=
        ((e1.trans (MulEquiv.ofBijective _ hbij)).trans
          (QuotientGroup.quotientMulEquivOfEq hFO)).trans eL
      have : Fact p.Prime := ⟨hp⟩
      have hTW : T ≤ Subgroup.normalizer (W : Set Y) := fun t ht =>
        Subgroup.inf_normalizer_le_normalizer_inf ⟨hTN ht, Subgroup.le_normalizer (hTz ht)⟩
      exact le_normalizer_of_psl2_prime_two (K := ZMod p) hp (Nat.card_zmod p) hp5 hp8
        (QuotientGroup.congr (Subgroup.center ↥W) _ eW (Subgroup.map_center_eq eW))
        (isPGroup_center_of_sl2 eW) hT hTW hD hDW hDT hBW hBp hA5 hsylB hbB hb3 hbT hbD
    ·
      exfalso
      obtain ⟨-, -, ⟨e5⟩, -⟩ := h4
      obtain ⟨ep⟩ := hLp
      have : Fact p.Prime := ⟨hp⟩
      have hc : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) =
          Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) :=
        (Nat.card_congr e5.toEquiv).symm.trans
          ((Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hFO).toEquiv).trans
            (Nat.card_congr ep.toEquiv))
      rw [SL2MinimalFaithful.card_specialLinearGroup_fin_two,
        SL2MinimalFaithful.card_specialLinearGroup_fin_two, Nat.card_zmod, Nat.card_zmod] at hc
      have h5 := Vol2.Ch11.SecA.eq_of_mul_sq_sub_one (by norm_num) hp.one_lt.le hc
      subst h5
      norm_num at hp5

theorem le_normalizer_of_nq
    (h36 : A36ForSQTK) (hY : SQTKHyp Y) {T B L D : Subgroup Y}
    (hT : IsSylowTwoOf T ⊤) (hB : B ∈ lFamily T) (hA5 : IsAlt 5 (ModO2 B))
    (hL : L ∈ cComp ⊤) (hBL : B < L)
    (hcase : (IsSL2 5 (↥B ⧸ CFSG.oddCore ↥B) ∧ L = B ⊔ oddCoreSub L) ∨
      (IsSL2 5 (↥B ⧸ CFSG.oddCore ↥B) ∧ ∃ p : ℕ, p.Prime ∧ p ^ 2 % 5 = 1 ∧
        (p % 8 = 3 ∨ p % 8 = 5) ∧ IsSL2 p (↥L ⧸ CFSG.oddCore ↥L)))
    (hD : Nat.card D = 5) (hDN : D ≤ Subgroup.normalizer (L : Set Y))
    (hTN : T ≤ Subgroup.normalizer (L : Set Y)) (hTB : T ≤ Subgroup.normalizer (B : Set Y))
    (hDT : (D : Set Y) * (T : Set Y) = (T : Set Y) * (D : Set Y)) {b : Y} (hbB : b ∈ B)
    (hb3 : orderOf b = 3) (hbT : b ∈ Subgroup.normalizer ((T ⊓ B : Subgroup Y) : Set Y))
    (hbD : ∀ d ∈ D, d * b = b * d) : D ≤ Subgroup.normalizer (B : Set Y) := by
  have hBL' : B ≤ L := hBL.le
  have hBp : ⁅B, B⁆ = B := perfect_of_mem_cComp hB
  have hsylB : IsSylowTwoOf (T ⊓ B) B :=
    A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp hB)
      (A4.isSylowTwoOf_mono hT le_sup_right le_top)
  have hR5 : IsSL2 5 (↥B ⧸ CFSG.oddCore ↥B) := by rcases hcase with h | h <;> exact h.1
  have hOB := oddCore_eq_bot_of_alt5 hA5 hR5
  obtain ⟨z, hzB, hz2, hz1, hzc, huniq, hzP, a, ha, a', ha', haa⟩ :=
    exists_central_involution_sl25 (isSL2_of_oddCore_eq_bot hOB hR5) hsylB
  have hTz : T ≤ Subgroup.centralizer ({z} : Set Y) := by
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
    · rw [Subgroup.mem_centralizer_singleton_iff]
      calc s * z = s * z * s⁻¹ * s := by group
        _ = z * s := by rw [h]
  obtain ⟨hconc, hcom, hextra⟩ := h36 Y hY L hL
  rcases hconc with ⟨hc, hs, -⟩ | ⟨hc, hZ3, -⟩ | h3 | h4
  ·
    refine (false_of_quasisimple_nq hBL hc.1 ?_ (hBL' hzB) hz2 hz1 hcase).elim
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
    exact (false_of_quasisimple_nq hBL hc.1 (by rw [hZ3]; decide) (hBL' hzB) hz2 hz1
      hcase).elim
  · exact le_normalizer_of_case34 (Or.inl h3) (hextra (Or.inl h3)) hcom.1 hOB hT hBL' hBp hA5
      hsylB hD hDN hTN hDT hzB hz2 hz1 hzc hTz hzP ha ha' haa hcase hbB hb3 hbT hbD
  · exact le_normalizer_of_case34 (Or.inr h4) (hextra (Or.inr h4)) hcom.1 hOB hT hBL' hBp hA5
      hsylB hD hDN hTN hDT hzB hz2 hz1 hzc hTz hzP ha ha' haa hcase hbB hb3 hbT hbD

theorem a314FiveNormNQ_of
    (h36 : A36ForSQTK) : A314FiveNormNQ :=
  fun _ _ _ hY _ _ _ _ hT hB hA5 hL hBL hcase hD hDN hTN hTB hDT ⟨_, hbB, hb3, hbT, hbD⟩ =>
    le_normalizer_of_nq h36 hY hT hB hA5 hL hBL hcase hD hDN hTN hTB hDT hbB hb3 hbT hbD

end CFSG.Quasithin.H13.FiveNorm
