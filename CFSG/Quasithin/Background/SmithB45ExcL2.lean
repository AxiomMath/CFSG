module

public import CFSG.Quasithin.Background.SmithB45ExcEngine
public import CFSG.Quasithin.Background.SmithB45ExcL2Rot
public import CFSG.Quasithin.Background.SmithB45ExcOrbit
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyP2Cover

public section

namespace CFSG.Quasithin.B45Exc

open Matrix Module CFSG CFSG.GorensteinWalter CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.QuasithinUnique.Setup.Family
  CFSG.QuasithinUnique.Setup.X3 CFSG.SectionRank.OddCover

section Elements

variable {K : Type*} [Field K]

theorem proj_eq_one_iff_two {M : SpecialLinearGroup (Fin 2) K} :
    proj 2 K M = 1 ↔ (M : Matrix (Fin 2) (Fin 2) K) = 1 ∨ (M : Matrix (Fin 2) (Fin 2) K) = -1 := by
  rw [proj_eq_one_iff]
  constructor
  · rintro ⟨c, hc, hM⟩
    have hc' : ((c : K) - 1) * ((c : K) + 1) = 0 := by
      have : (c : K) ^ 2 = 1 := by rw [← Units.val_pow_eq_pow_val, hc, Units.val_one]
      linear_combination this
    rcases mul_eq_zero.1 hc' with h | h
    · left
      rw [hM, sub_eq_zero.1 h, map_one]
    · right
      rw [hM, eq_neg_of_add_eq_zero_left h, map_neg, map_one]
  · rintro (h | h)
    · exact ⟨1, one_pow 2, by rw [h, Units.val_one, map_one]⟩
    · refine ⟨-1, by norm_num, ?_⟩
      rw [h, Units.val_neg, Units.val_one, map_neg, map_one]

@[expose] noncomputable def pU (K : Type*) [Field K] : projectiveSL 2 K := proj 2 K (slU 1)

@[expose] noncomputable def pA (K : Type*) [Field K] : projectiveSL 2 K := proj 2 K slA

theorem pU_pow_natCast (n : ℕ) : pU K ^ n = proj 2 K (slU (n : K)) := by
  rw [pU, proj_slU_natCast]

theorem pU_pow_char {p : ℕ} [CharP K p] : pU K ^ p = 1 := by
  rw [pU_pow_natCast, CharP.cast_eq_zero, slU_zero, map_one]

theorem pU_ne_one (h2 : (2 : K) ≠ 0) : pU K ≠ 1 := by
  rw [pU, Ne, proj_eq_one_iff_two]
  rintro (h | h)
  · have := congrFun (congrFun h 0) 1
    simp [coe_slU] at this
  · have := congrFun (congrFun h 0) 0
    simp [coe_slU] at this
    apply h2
    linear_combination this

theorem pD_conj_pU (c : Kˣ) (n : ℕ) (hn : ((n : ℕ) : K) = (c : K) ^ 2) :
    proj 2 K (slD c) * pU K * (proj 2 K (slD c))⁻¹ = pU K ^ n := by
  rw [pU_pow_natCast, hn, pU, ← map_mul, ← map_inv, ← map_mul, slD_mul_slU, mul_one,
    mul_inv_cancel_right]

theorem pA_mul_self : pA K * pA K = 1 := by
  rw [pA, ← map_mul, proj_eq_one_iff_two]
  right
  show ((slA * slA : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = -1
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_slA]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem pA_ne_one : pA K ≠ 1 := by
  rw [pA, Ne, proj_eq_one_iff_two]
  rintro (h | h)
  · have := congrFun (congrFun h 0) 0
    simp [coe_slA] at this
  · have := congrFun (congrFun h 0) 1
    simp [coe_slA] at this

end Elements

section Rep

variable {p : ℕ} [hpf : Fact p.Prime] {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  [Module.Finite (ZMod 2) E]

theorem p2_finrank_le_three_mul (hp5 : 5 ≤ p) (ρ : projectiveSL 2 (ZMod p) →* (E ≃ₗ[ZMod 2] E))
    (hE : QuasithinUnique.Setup.Family.commSub ρ ⊤ = ⊤) {a : projectiveSL 2 (ZMod p)} (ha1 : a ≠ 1) (ha2 : a * a = 1) :
    finrank (ZMod 2) E ≤ 3 * finrank (ZMod 2) (LinearMap.range (disp ρ a)) := by
  obtain ⟨a₁, a₂, a₃, h1, h2, h3, hgen⟩ := p2_three_involution_generation hp5 ha1 ha2
  obtain ⟨g₁, rfl⟩ := isConj_iff.1 h1
  obtain ⟨g₂, rfl⟩ := isConj_iff.1 h2
  obtain ⟨g₃, rfl⟩ := isConj_iff.1 h3
  set D := LinearMap.range (disp ρ (g₁ * a * g₁⁻¹)) ⊔ LinearMap.range (disp ρ (g₂ * a * g₂⁻¹)) ⊔
    LinearMap.range (disp ρ (g₃ * a * g₃⁻¹)) with hD
  have hgens : ∀ g ∈ ({g₁ * a * g₁⁻¹, g₂ * a * g₂⁻¹, g₃ * a * g₃⁻¹} :
      Set (projectiveSL 2 (ZMod p))), ∀ v, ρ g v - v ∈ D := by
    intro g hg v
    have hv : ρ g v - v = disp ρ g v := rfl
    rw [hv]
    rcases hg with rfl | rfl | rfl
    · exact Submodule.mem_sup_left (Submodule.mem_sup_left ⟨v, rfl⟩)
    · exact Submodule.mem_sup_left (Submodule.mem_sup_right ⟨v, rfl⟩)
    · exact Submodule.mem_sup_right ⟨v, rfl⟩
  have hDtop : D = ⊤ := by
    have hle : QuasithinUnique.Setup.Family.commSub ρ ⊤ ≤ D := commSub_le_of_closure ρ D hgens (by rw [hgen])
    rw [hE] at hle
    exact top_le_iff.1 hle
  have hD1 : finrank (ZMod 2) D ≤
      finrank (ZMod 2) (LinearMap.range (disp ρ (g₁ * a * g₁⁻¹))) +
        finrank (ZMod 2) (LinearMap.range (disp ρ (g₂ * a * g₂⁻¹))) +
        finrank (ZMod 2) (LinearMap.range (disp ρ (g₃ * a * g₃⁻¹))) :=
    ((Submodule.finrank_add_le_finrank_add_finrank _ _).trans
      (Nat.add_le_add_right (Submodule.finrank_add_le_finrank_add_finrank _ _) _))
  rw [finrank_range_disp_conj, finrank_range_disp_conj, finrank_range_disp_conj] at hD1
  have hDE : finrank (ZMod 2) D = finrank (ZMod 2) E := by
    rw [hDtop]
    exact finrank_top (ZMod 2) E
  omega

omit [Module.Finite (ZMod 2) E] in
theorem p2_injective (hp5 : 5 ≤ p) [Nontrivial E] (ρ : projectiveSL 2 (ZMod p) →* (E ≃ₗ[ZMod 2] E))
    (hE : QuasithinUnique.Setup.Family.commSub ρ ⊤ = ⊤) : Function.Injective ρ := by
  have := p2_isSimpleGroup hp5 (p := p)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ρ.ker with h | h
  · exact (MonoidHom.ker_eq_bot_iff ρ).1 h
  · exfalso
    obtain ⟨x, hx⟩ := exists_ne (0 : E)
    have hxm : x ∈ QuasithinUnique.Setup.Family.commSub ρ ⊤ := by rw [hE]; trivial
    have hle : QuasithinUnique.Setup.Family.commSub ρ ⊤ ≤ ⊥ := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨s, -, e, rfl⟩
      have hs : s ∈ ρ.ker := by rw [h]; trivial
      rw [MonoidHom.mem_ker] at hs
      rw [hs]
      simp
    exact hx (Submodule.mem_bot _ |>.1 (hle hxm))

omit [Module.Finite (ZMod 2) E] in
theorem p2_rank_eq (hp5 : 5 ≤ p) (ρ : projectiveSL 2 (ZMod p) →* (E ≃ₗ[ZMod 2] E))
    {a b : projectiveSL 2 (ZMod p)} (ha1 : a ≠ 1) (ha2 : a * a = 1) (hb1 : b ≠ 1)
    (hb2 : b * b = 1) :
    finrank (ZMod 2) (LinearMap.range (disp ρ b)) =
      finrank (ZMod 2) (LinearMap.range (disp ρ a)) := by
  obtain ⟨g, hg⟩ := (p2_involution_structure hp5).1 a b ha1 ha2 hb1 hb2
  rw [← hg]
  exact finrank_range_disp_conj ρ a g

theorem orderOf_two_dvd_rank {G : Type*} [Group G] (ρ : G →* (E ≃ₗ[ZMod 2] E)) {q : ℕ}
    [Fact q.Prime] (hq2 : q ≠ 2) {y : G} (hy : y ^ q = 1) :
    orderOf (2 : ZMod q) ∣ finrank (ZMod 2) (LinearMap.range (disp ρ y)) := by
  have hyq : (ρ y) ^ q = 1 := by rw [← map_pow, hy, map_one]
  exact orderOf_two_dvd_finrank_range_sub1 hq2 hyq

theorem rank_pos_of_ne (ρ : projectiveSL 2 (ZMod p) →* (E ≃ₗ[ZMod 2] E)) (hρ : Function.Injective ρ)
    {y : projectiveSL 2 (ZMod p)} (hy : y ≠ 1) :
    0 < finrank (ZMod 2) (LinearMap.range (disp ρ y)) := by
  have hne : LinearMap.range (disp ρ y) ≠ ⊥ := by
    intro h0
    apply hy
    apply hρ
    rw [map_one]
    ext v
    have h1 : disp ρ y v ∈ LinearMap.range (disp ρ y) := ⟨v, rfl⟩
    rw [h0, Submodule.mem_bot, disp_apply, sub_eq_zero] at h1
    exact h1
  exact Submodule.one_le_finrank_iff.2 hne

end Rep

section Bound

theorem fact_prime_thirteen : Fact (Nat.Prime 13) := ⟨by norm_num⟩

theorem fact_prime_twentythree : Fact (Nat.Prime 23) := ⟨by norm_num⟩

theorem fact_prime_eleven : Fact (Nat.Prime 11) := ⟨by norm_num⟩

theorem fact_prime_seventeen : Fact (Nat.Prime 17) := ⟨by norm_num⟩

theorem orderOf_two_zmod_13 : orderOf (2 : ZMod 13) = 12 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm0 => ?_⟩
  interval_cases m <;> decide

variable {p : ℕ} [hpf : Fact p.Prime] {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  [Module.Finite (ZMod 2) E]

theorem exists_unit_orderOf_eq : ∃ c : (ZMod p)ˣ, orderOf c = p - 1 := by
  obtain ⟨c, hc⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  refine ⟨c, ?_⟩
  rw [orderOf_eq_card_of_forall_mem_zpowers hc, Nat.card_eq_fintype_card,
    ZMod.card_units_eq_totient, Nat.totient_prime hpf.out]

theorem p2_half_dvd_rank (hp2 : p ≠ 2) (ρ : projectiveSL 2 (ZMod p) →* (E ≃ₗ[ZMod 2] E)) :
    (p - 1) / 2 ∣ finrank (ZMod 2) (LinearMap.range (disp ρ (pU (ZMod p)))) := by
  obtain ⟨c, hc⟩ := exists_unit_orderOf_eq (p := p)
  set k := ((c : ZMod p) ^ 2).val with hk
  have hkc : ((k : ℕ) : ZMod p) = (c : ZMod p) ^ 2 := ZMod.natCast_zmod_val _
  have hconj := pD_conj_pU (K := ZMod p) c k hkc
  have hy : (ρ (pU (ZMod p))) ^ p = 1 := by rw [← map_pow, pU_pow_char, map_one]
  have hgy : ρ (proj 2 (ZMod p) (slD c)) * ρ (pU (ZMod p)) * (ρ (proj 2 (ZMod p) (slD c)))⁻¹ =
      ρ (pU (ZMod p)) ^ k := by
    rw [← map_inv, ← map_mul, ← map_mul, hconj, map_pow]
  have h1 := orderOf_dvd_finrank_range_sub1 hp2 hy hgy
  have hord : orderOf ((k : ℕ) : ZMod p) = (p - 1) / 2 := by
    rw [hkc, ← Units.val_pow_eq_pow_val, orderOf_units, orderOf_pow' c two_ne_zero, hc]
    have hodd : Odd p := hpf.out.odd_of_ne_two hp2
    rw [gcd_sub_one_two_of_odd' hodd]
  rw [hord] at h1
  exact h1

theorem p2_context (hp5 : 5 ≤ p) [Nontrivial E]
    (ρ : projectiveSL 2 (ZMod p) →* (E ≃ₗ[ZMod 2] E)) (hE : QuasithinUnique.Setup.Family.commSub ρ ⊤ = ⊤)
    {a : projectiveSL 2 (ZMod p)} (ha1 : a ≠ 1) (ha2 : a * a = 1)
    (hrk : finrank (ZMod 2) (LinearMap.range (disp ρ a)) ≤ 4) :
    Function.Injective ρ ∧ finrank (ZMod 2) E ≤ 12 ∧
      (∀ b : projectiveSL 2 (ZMod p), b ≠ 1 → b * b = 1 →
        finrank (ZMod 2) (LinearMap.range (disp ρ b)) ≤ 4) ∧
      0 < finrank (ZMod 2) (LinearMap.range (disp ρ (pU (ZMod p)))) ∧
      finrank (ZMod 2) (LinearMap.range (disp ρ (pU (ZMod p)))) ≤ 12 ∧
      orderOf (2 : ZMod p) ∣ finrank (ZMod 2) (LinearMap.range (disp ρ (pU (ZMod p)))) ∧
      (p - 1) / 2 ∣ finrank (ZMod 2) (LinearMap.range (disp ρ (pU (ZMod p)))) := by
  have hp2 : p ≠ 2 := by omega
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hpf.out Nat.prime_two).1 h')
  have hinj := p2_injective hp5 ρ hE
  have hdim : finrank (ZMod 2) E ≤ 12 := by
    have := p2_finrank_le_three_mul hp5 ρ hE ha1 ha2
    omega
  refine ⟨hinj, hdim, fun b hb1 hb2 => (p2_rank_eq hp5 ρ ha1 ha2 hb1 hb2).le.trans hrk,
    rank_pos_of_ne ρ hinj (pU_ne_one h2), (LinearMap.finrank_range_le _).trans hdim,
    orderOf_two_dvd_rank ρ hp2 pU_pow_char, p2_half_dvd_rank hp2 ρ⟩

attribute [local instance] fact_prime_thirteen fact_prime_twentythree in
theorem p2_not_thirteen [Nontrivial E]
    (ρ : projectiveSL 2 (ZMod 13) →* (E ≃ₗ[ZMod 2] E)) (hE : QuasithinUnique.Setup.Family.commSub ρ ⊤ = ⊤)
    {a : projectiveSL 2 (ZMod 13)} (ha1 : a ≠ 1) (ha2 : a * a = 1)
    (hrk : finrank (ZMod 2) (LinearMap.range (disp ρ a)) ≤ 4) : False := by
  obtain ⟨-, -, hrkall, hd0, hdE, h2d, -⟩ := p2_context (by norm_num) ρ hE ha1 ha2 hrk
  rw [orderOf_two_zmod_13] at h2d
  have hd12 : finrank (ZMod 2) (LinearMap.range (disp ρ (pU (ZMod 13)))) = 12 := by
    obtain ⟨j, hj⟩ := h2d
    rcases Nat.lt_or_ge j 2 with h | h
    · interval_cases j <;> omega
    · omega
  set c : (ZMod 13)ˣ := Units.mk0 5 (by decide) with hc
  set s := proj 2 (ZMod 13) (slD c) with hs
  have hs2 : s * s = 1 := by
    rw [hs, ← map_mul, proj_eq_one_iff_two]
    right
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_slD]
    have hci : ((c⁻¹ : (ZMod 13)ˣ) : ZMod 13) = 8 := by
      rw [Units.val_inv_eq_inv_val, hc, Units.val_mk0]
      exact inv_eq_of_mul_eq_one_right (by decide)
    rw [hci, hc, Units.val_mk0]
    decide
  have hs1 : s ≠ 1 := by
    rw [hs, Ne, proj_eq_one_iff_two, coe_slD, hc, Units.val_mk0]
    rintro (h | h)
    · have := congrFun (congrFun h 0) 0
      simp at this
      exact absurd this (by decide)
    · have := congrFun (congrFun h 0) 0
      simp at this
      exact absurd this (by decide)
  have hconj := pD_conj_pU (K := ZMod 13) c 12 (by rw [hc, Units.val_mk0]; decide)
  set y := ρ (pU (ZMod 13)) with hy
  set g := ρ s with hg
  have hu13 : pU (ZMod 13) ^ 13 = 1 := pU_pow_char
  have hy13 : y ^ 13 = 1 := by rw [hy, ← map_pow, hu13, map_one]
  have hgy : g * y * g⁻¹ = y ^ 12 := by
    rw [hg, hy, ← map_inv, ← map_mul, ← map_mul, hs, hconj, map_pow]
  have hgg : g * g = 1 := by rw [hg, ← map_mul, hs2, map_one]
  have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hgg
  have hyinv : y⁻¹ = y ^ 12 := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ']
    exact hy13
  have hsv : g * y * g = y⁻¹ := by rw [hyinv, ← hgy, hginv]
  have hhalfM := finrank_half (LinearMap.range (sub1 y)) hgg hsv (by decide : Odd 13) hy13
    (fun x hx => conj_apply_mem_range_sub1 hgy hx) (fun x hx => apply_mem_range_sub1 y hx)
    (fun x hx hfx => eq_zero_of_mem_range_sub1 (by decide : Odd 13) hy13 hx hfx)
  have hMd : finrank (ZMod 2) (LinearMap.range (sub1 y)) =
      finrank (ZMod 2) (LinearMap.range (disp ρ (pU (ZMod 13)))) := rfl
  have hmap : finrank (ZMod 2) ((LinearMap.range (sub1 y)).map (sub1 g)) ≤
      finrank (ZMod 2) (LinearMap.range (disp ρ s)) := by
    apply Submodule.finrank_mono
    rintro _ ⟨x, -, rfl⟩
    exact ⟨x, rfl⟩
  have := hrkall s hs1 hs2
  omega

theorem p2_not_nineteen [Fact (Nat.Prime 19)] [Nontrivial E]
    (ρ : projectiveSL 2 (ZMod 19) →* (E ≃ₗ[ZMod 2] E)) (hE : QuasithinUnique.Setup.Family.commSub ρ ⊤ = ⊤)
    {a : projectiveSL 2 (ZMod 19)} (ha1 : a ≠ 1) (ha2 : a * a = 1)
    (hrk : finrank (ZMod 2) (LinearMap.range (disp ρ a)) ≤ 4) : False := by
  obtain ⟨-, -, -, hd0, hdE, h2d, -⟩ := p2_context (by norm_num) ρ hE ha1 ha2 hrk
  rw [CFSG.QuasithinUnique.Setup.X1.orderOf_two_zmod_19] at h2d
  have := Nat.le_of_dvd hd0 h2d
  omega

attribute [local instance] fact_prime_twentythree in
theorem p2_not_twentythree [Nontrivial E]
    (ρ : projectiveSL 2 (ZMod 23) →* (E ≃ₗ[ZMod 2] E)) (hE : QuasithinUnique.Setup.Family.commSub ρ ⊤ = ⊤)
    {a : projectiveSL 2 (ZMod 23)} (ha1 : a ≠ 1) (ha2 : a * a = 1)
    (hrk : finrank (ZMod 2) (LinearMap.range (disp ρ a)) ≤ 4) : False := by
  obtain ⟨hinj, -, hrkall, -, -, -, -⟩ := p2_context (by norm_num) ρ hE ha1 ha2 hrk
  have h12 : (2 : ZMod 23) * 12 - 0 * 0 = 1 := by decide
  set t := proj 2 (ZMod 23) (slMk 2 0 0 12 h12) with ht
  set w := pA (ZMod 23) with hw
  have ht11 : t ^ 11 = 1 := by
    rw [ht, ← map_pow, proj_eq_one_iff_two]
    left
    rw [Matrix.SpecialLinearGroup.coe_pow, coe_slMk]
    decide
  have ht1 : t ≠ 1 := by
    rw [ht, Ne, proj_eq_one_iff_two, coe_slMk]
    decide
  have htw2 : (t * w) * (t * w) = 1 := by
    rw [ht, hw, pA, ← map_mul, ← map_mul, proj_eq_one_iff_two]
    right
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_slMk, coe_slA]
    decide
  have htw1 : t * w ≠ 1 := by
    rw [ht, hw, pA, ← map_mul, Ne, proj_eq_one_iff_two, Matrix.SpecialLinearGroup.coe_mul,
      coe_slMk, coe_slA]
    decide
  have hprod : (t * w) * w = t := by rw [hw, mul_assoc, pA_mul_self, mul_one]
  have hle := finrank_range_disp_mul_le ρ (t * w) w
  rw [hprod] at hle
  have h1 := hrkall (t * w) htw1 htw2
  have h2' := hrkall w pA_ne_one pA_mul_self
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have h10 := orderOf_two_dvd_rank ρ (q := 11) (by norm_num) ht11
  rw [CFSG.QuasithinUnique.Setup.X1.orderOf_two_zmod_11] at h10
  have hpos := rank_pos_of_ne ρ hinj ht1
  have := Nat.le_of_dvd hpos h10
  omega

theorem prime_cases_25 (hp : p.Prime) (h11 : 11 ≤ p) (h25 : (p - 1) / 2 ≤ 12) :
    p = 11 ∨ p = 13 ∨ p = 17 ∨ p = 19 ∨ p = 23 := by
  have hp26 : p ≤ 26 := by omega
  interval_cases p <;> first | decide | (exfalso; norm_num at hp)

theorem p2_eleven_or_seventeen (hp11 : 11 ≤ p) [Nontrivial E]
    (ρ : projectiveSL 2 (ZMod p) →* (E ≃ₗ[ZMod 2] E)) (hE : QuasithinUnique.Setup.Family.commSub ρ ⊤ = ⊤)
    {a : projectiveSL 2 (ZMod p)} (ha1 : a ≠ 1) (ha2 : a * a = 1)
    (hrk : finrank (ZMod 2) (LinearMap.range (disp ρ a)) ≤ 4) : p = 11 ∨ p = 17 := by
  obtain ⟨-, -, -, hd0, hdE, -, hhalf⟩ := p2_context (by omega) ρ hE ha1 ha2 hrk
  have h25 : (p - 1) / 2 ≤ 12 := (Nat.le_of_dvd hd0 hhalf).trans hdE
  rcases prime_cases_25 hpf.out hp11 h25 with rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact (p2_not_thirteen ρ hE ha1 ha2 hrk).elim
  · exact Or.inr rfl
  · exact (p2_not_nineteen ρ hE ha1 ha2 hrk).elim
  · exact (p2_not_twentythree ρ hE ha1 ha2 hrk).elim

end Bound

section Fixed

variable {G : Type*} [Group G] {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

theorem mem_ker_disp {ρ : G →* (E ≃ₗ[ZMod 2] E)} {g : G} {x : E} :
    x ∈ LinearMap.ker (disp ρ g) ↔ ρ g x = x := by
  rw [LinearMap.mem_ker, disp_apply, sub_eq_zero]

theorem ker_disp_conj_le {ρ : G →* (E ≃ₗ[ZMod 2] E)} {a v : G} (h : G)
    (hker : LinearMap.ker (disp ρ a) ≤ LinearMap.ker (disp ρ v)) :
    LinearMap.ker (disp ρ (h * a * h⁻¹)) ≤ LinearMap.ker (disp ρ (h * v * h⁻¹)) := by
  intro x hx
  rw [mem_ker_disp] at hx ⊢
  have hinv : ∀ y : E, ρ h (ρ h⁻¹ y) = y := fun y => by
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
  have hinv' : ∀ y : E, ρ h⁻¹ (ρ h y) = y := fun y => by
    rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl
  have h1 : ρ a (ρ h⁻¹ x) = ρ h⁻¹ x := by
    have := congrArg (ρ h⁻¹) hx
    simpa [map_mul, LinearEquiv.mul_apply, hinv'] using this
  have h2 : ρ v (ρ h⁻¹ x) = ρ h⁻¹ x := mem_ker_disp.1 (hker (mem_ker_disp.2 h1))
  simp only [map_mul, LinearEquiv.mul_apply, h2, hinv]

theorem ker_disp_le_rot (ρ : G →* (E ≃ₗ[ZMod 2] E)) {a v g : G} (hv2 : v * v = 1)
    (hvg : v * g * v = g⁻¹) (hga : g * a = a * g)
    (hker : LinearMap.ker (disp ρ a) ≤ LinearMap.ker (disp ρ v)) :
    LinearMap.ker (disp ρ a) ≤ LinearMap.ker (disp ρ (g⁻¹ * g⁻¹)) := by
  intro x hx
  have hax : ρ a x = x := mem_ker_disp.1 hx
  have hvx : ρ v x = x := mem_ker_disp.1 (hker hx)
  have hag : a * g⁻¹ = g⁻¹ * a := by
    calc a * g⁻¹ = g⁻¹ * (g * a) * g⁻¹ := by group
      _ = g⁻¹ * (a * g) * g⁻¹ := by rw [hga]
      _ = g⁻¹ * a := by group
  have h1 : ρ a (ρ g⁻¹ x) = ρ g⁻¹ x := by
    rw [← LinearEquiv.mul_apply, ← map_mul, hag, map_mul, LinearEquiv.mul_apply, hax]
  have h2 : ρ v (ρ g⁻¹ x) = ρ g⁻¹ x := mem_ker_disp.1 (hker (mem_ker_disp.2 h1))
  have hw : g⁻¹ * g⁻¹ = v * (g * (v * g⁻¹)) := by
    have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
    calc g⁻¹ * g⁻¹ = (v * g * v) * g⁻¹ := by rw [hvg]
      _ = v * (g * (v * g⁻¹)) := by group
  rw [mem_ker_disp, hw, map_mul, LinearEquiv.mul_apply, map_mul, LinearEquiv.mul_apply,
    map_mul, LinearEquiv.mul_apply, h2]
  have h3 : ρ g (ρ g⁻¹ x) = x := by
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
  rw [h3, hvx]

theorem rank_le_of_ker_le [Module.Finite (ZMod 2) E] {ρ : G →* (E ≃ₗ[ZMod 2] E)} {a x : G}
    (hker : LinearMap.ker (disp ρ a) ≤ LinearMap.ker (disp ρ x)) :
    finrank (ZMod 2) (LinearMap.range (disp ρ x)) ≤
      finrank (ZMod 2) (LinearMap.range (disp ρ a)) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (disp ρ a)
  have h2 := LinearMap.finrank_range_add_finrank_ker (disp ρ x)
  have h3 := Submodule.finrank_mono hker
  omega

theorem eq_one_of_ker_sub1_eq {T : E ≃ₗ[ZMod 2] E} (h4 : T ^ 4 = 1)
    (hk : ∀ v : E, T (T v) = v → T v = v) : T = 1 := by
  have hD : ∀ v : E, sub1 T (sub1 T v) = sub1 (T ^ 2) v := by
    intro v
    simp only [sub1_apply', map_add, pow_two, LinearEquiv.mul_apply]
    rw [add_assoc, ← add_assoc (T v), e_add_self, zero_add]
  have hK : ∀ v : E, sub1 T (sub1 T v) = 0 → sub1 T v = 0 := by
    intro v hv
    rw [hD, sub1_apply, sub_eq_zero, pow_two, LinearEquiv.mul_apply] at hv
    rw [sub1_apply, sub_eq_zero]
    exact hk v hv
  have h4' : ∀ v : E, sub1 T (sub1 T (sub1 T (sub1 T v))) = 0 := by
    intro v
    rw [hD, hD]
    have h1 : (T ^ 2) ((T ^ 2) v) = v := by
      rw [← LinearEquiv.mul_apply, ← pow_add, h4]; rfl
    have h2 : ∀ x y : E, x - y - (y - x) = (x + x) - (y + y) := by intro x y; abel
    rw [sub1_apply, sub1_apply, map_sub, h1, h2, e_add_self, e_add_self, sub_zero]
  ext v
  have := hK v (hK _ (hK _ (h4' v)))
  rw [sub1_apply, sub_eq_zero] at this
  exact this

end Fixed

section ElevenSeventeen

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [Module.Finite (ZMod 2) E]

attribute [local instance] fact_prime_eleven fact_prime_seventeen

theorem p2_rank_ge_four_eleven [Nontrivial E] (ρ : projectiveSL 2 (ZMod 11) →* (E ≃ₗ[ZMod 2] E))
    (hE : QuasithinUnique.Setup.Family.commSub ρ ⊤ = ⊤) {b : projectiveSL 2 (ZMod 11)} (hb1 : b ≠ 1) (hb2 : b * b = 1) :
    4 ≤ finrank (ZMod 2) (LinearMap.range (disp ρ b)) := by
  have hinj := p2_injective (by norm_num) ρ hE
  have hd0 := rank_pos_of_ne ρ hinj (pU_ne_one (K := ZMod 11) (by decide))
  have h10 := orderOf_two_dvd_rank ρ (q := 11) (by norm_num) (pU_pow_char (K := ZMod 11))
  rw [CFSG.QuasithinUnique.Setup.X1.orderOf_two_zmod_11] at h10
  have hd10 := Nat.le_of_dvd hd0 h10
  have hdE := LinearMap.finrank_range_le (disp ρ (pU (ZMod 11)))
  have h3 := p2_finrank_le_three_mul (by norm_num) ρ hE hb1 hb2
  omega

theorem p2_rank_ge_four_seventeen [Nontrivial E]
    (ρ : projectiveSL 2 (ZMod 17) →* (E ≃ₗ[ZMod 2] E))
    (hE : QuasithinUnique.Setup.Family.commSub ρ ⊤ = ⊤) {b : projectiveSL 2 (ZMod 17)} (hb1 : b ≠ 1) (hb2 : b * b = 1) :
    4 ≤ finrank (ZMod 2) (LinearMap.range (disp ρ b)) := by
  have hinj := p2_injective (by norm_num) ρ hE
  have hd0 := rank_pos_of_ne ρ hinj (pU_ne_one (K := ZMod 17) (by decide))
  have h8 := orderOf_two_dvd_rank ρ (q := 17) (by norm_num) (pU_pow_char (K := ZMod 17))
  rw [CFSG.QuasithinUnique.Setup.X1.orderOf_two_zmod_17] at h8
  have hd8 := Nat.le_of_dvd hd0 h8
  set c : (ZMod 17)ˣ := Units.mk0 4 (by decide) with hc
  set s := proj 2 (ZMod 17) (slD c) with hs
  have hci : ((c⁻¹ : (ZMod 17)ˣ) : ZMod 17) = 13 := by
    rw [Units.val_inv_eq_inv_val, hc, Units.val_mk0]
    exact inv_eq_of_mul_eq_one_right (by decide)
  have hs2 : s * s = 1 := by
    rw [hs, ← map_mul, proj_eq_one_iff_two]
    right
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_slD, hci, hc, Units.val_mk0]
    decide
  have hs1 : s ≠ 1 := by
    rw [hs, Ne, proj_eq_one_iff_two, coe_slD, hci, hc, Units.val_mk0]
    decide
  have hconj := pD_conj_pU (K := ZMod 17) c 16 (by rw [hc, Units.val_mk0]; decide)
  set y := ρ (pU (ZMod 17)) with hy
  set g := ρ s with hg
  have hy17 : y ^ 17 = 1 := by rw [hy, ← map_pow, pU_pow_char, map_one]
  have hgy : g * y * g⁻¹ = y ^ 16 := by
    rw [hg, hy, ← map_inv, ← map_mul, ← map_mul, hs, hconj, map_pow]
  have hgg : g * g = 1 := by rw [hg, ← map_mul, hs2, map_one]
  have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hgg
  have hyinv : y⁻¹ = y ^ 16 := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ']
    exact hy17
  have hsv : g * y * g = y⁻¹ := by rw [hyinv, ← hgy, hginv]
  have hhalfM := finrank_half (LinearMap.range (sub1 y)) hgg hsv (by decide : Odd 17) hy17
    (fun x hx => conj_apply_mem_range_sub1 hgy hx) (fun x hx => apply_mem_range_sub1 y hx)
    (fun x hx hfx => eq_zero_of_mem_range_sub1 (by decide : Odd 17) hy17 hx hfx)
  have hMd : finrank (ZMod 2) (LinearMap.range (sub1 y)) =
      finrank (ZMod 2) (LinearMap.range (disp ρ (pU (ZMod 17)))) := rfl
  have hmap : finrank (ZMod 2) ((LinearMap.range (sub1 y)).map (sub1 g)) ≤
      finrank (ZMod 2) (LinearMap.range (disp ρ s)) := by
    apply Submodule.finrank_mono
    rintro _ ⟨x, -, rfl⟩
    exact ⟨x, rfl⟩
  have hsb := p2_rank_eq (by norm_num) ρ hs1 hs2 hb1 hb2
  omega

theorem rot11_det : (3 : ZMod 11) * 3 - 5 * -5 = 1 := by decide

theorem rot17_det : (4 : ZMod 17) * 4 - 6 * -6 = 1 := by decide

@[expose] noncomputable def rot11 : projectiveSL 2 (ZMod 11) :=
  proj 2 (ZMod 11) (slMk 3 5 (-5) 3 rot11_det)

@[expose] noncomputable def rot17 : projectiveSL 2 (ZMod 17) :=
  proj 2 (ZMod 17) (slMk 4 6 (-6) 4 rot17_det)

theorem p2_final_eleven [Nontrivial E] (ρ : projectiveSL 2 (ZMod 11) →* (E ≃ₗ[ZMod 2] E))
    (hE : QuasithinUnique.Setup.Family.commSub ρ ⊤ = ⊤) (hrk : finrank (ZMod 2) (LinearMap.range (disp ρ (pA (ZMod 11)))) ≤ 4)
    (hker : LinearMap.ker (disp ρ (pA (ZMod 11))) ≤
      LinearMap.ker (disp ρ (rot11⁻¹ * rot11⁻¹))) : False := by
  have hinj := p2_injective (by norm_num) ρ hE
  set X := slMk (6 : ZMod 11) 3 8 6 (by decide) with hX
  set H := slMk (0 : ZMod 11) 1 10 4 (by decide) with hH
  set H' := slMk (4 : ZMod 11) 10 1 0 (by decide) with hH'
  have hxX : rot11⁻¹ * rot11⁻¹ = proj 2 (ZMod 11) X := by
    have h1 : rot11 * rot11 * proj 2 (ZMod 11) X = 1 := by
      rw [rot11, ← map_mul, ← map_mul, proj_eq_one_iff_two]
      left
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_slMk, hX,
        coe_slMk]
      decide
    rw [← _root_.mul_inv_rev]
    exact (eq_inv_of_mul_eq_one_right h1).symm
  have hHH : proj 2 (ZMod 11) H * proj 2 (ZMod 11) H' = 1 := by
    rw [← map_mul, proj_eq_one_iff_two]
    left
    rw [Matrix.SpecialLinearGroup.coe_mul, hH, hH', coe_slMk, coe_slMk]
    decide
  have hHinv : (proj 2 (ZMod 11) H)⁻¹ = proj 2 (ZMod 11) H' :=
    (eq_inv_of_mul_eq_one_right hHH).symm
  rw [hxX] at hker
  have hrX := (rank_le_of_ker_le hker).trans hrk
  set y := proj 2 (ZMod 11) X * (proj 2 (ZMod 11) H * proj 2 (ZMod 11) X *
    (proj 2 (ZMod 11) H)⁻¹) with hy
  have hyrk : finrank (ZMod 2) (LinearMap.range (disp ρ y)) ≤ 8 := by
    rw [hy]
    have h1 := finrank_range_disp_mul_le ρ (proj 2 (ZMod 11) X)
      (proj 2 (ZMod 11) H * proj 2 (ZMod 11) X * (proj 2 (ZMod 11) H)⁻¹)
    rw [finrank_range_disp_conj] at h1
    omega
  have hyM : y = proj 2 (ZMod 11) (X * H * X * H') := by
    rw [hy, hHinv, map_mul, map_mul, map_mul]
    group
  have hy11 : y ^ 11 = 1 := by
    rw [hyM, ← map_pow, proj_eq_one_iff_two]
    right
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hX, hH, hH',
      coe_slMk, coe_slMk, coe_slMk]
    decide
  have hy1 : y ≠ 1 := by
    rw [hyM, Ne, proj_eq_one_iff_two, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hX, hH, hH',
      coe_slMk, coe_slMk, coe_slMk]
    decide
  have h10 := orderOf_two_dvd_rank ρ (q := 11) (by norm_num) hy11
  rw [CFSG.QuasithinUnique.Setup.X1.orderOf_two_zmod_11] at h10
  have hpos := rank_pos_of_ne ρ hinj hy1
  have := Nat.le_of_dvd hpos h10
  omega

omit [Module.Finite (ZMod 2) E] in
theorem p2_final_seventeen [Nontrivial E] (ρ : projectiveSL 2 (ZMod 17) →* (E ≃ₗ[ZMod 2] E))
    (hE : QuasithinUnique.Setup.Family.commSub ρ ⊤ = ⊤)
    (hker : LinearMap.ker (disp ρ (pA (ZMod 17))) ≤
      LinearMap.ker (disp ρ (rot17⁻¹ * rot17⁻¹))) : False := by
  have hinj := p2_injective (by norm_num) ρ hE
  have hr4 : rot17 ^ 4 = pA (ZMod 17) := by
    rw [rot17, pA, ← map_pow, proj_eq_proj_iff]
    refine ⟨-1, by norm_num, ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
      Matrix.SpecialLinearGroup.coe_pow, coe_slMk, coe_slA]
    decide
  set x := rot17⁻¹ * rot17⁻¹ with hx
  have hpAinv : (pA (ZMod 17))⁻¹ = pA (ZMod 17) := inv_eq_of_mul_eq_one_right pA_mul_self
  have hxx : x * x = pA (ZMod 17) := by
    rw [hx, ← hpAinv, ← hr4]
    group
  set T := ρ x with hT
  have hT4 : T ^ 4 = 1 := by
    rw [hT, ← map_pow, show x ^ 4 = (x * x) * (x * x) by
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two], hxx, pA_mul_self, map_one]
  have hk : ∀ v : E, T (T v) = v → T v = v := by
    intro v hv
    have h1 : v ∈ LinearMap.ker (disp ρ (pA (ZMod 17))) := by
      rw [mem_ker_disp, ← hxx, map_mul, LinearEquiv.mul_apply]
      exact hv
    exact mem_ker_disp.1 (hker h1)
  have hT1 := eq_one_of_ker_sub1_eq hT4 hk
  have hx1 : x = 1 := hinj (by rw [← hT, hT1, map_one])
  apply pA_ne_one (K := ZMod 17)
  rw [← hxx, hx1, mul_one]

end ElevenSeventeen

section Core

variable {p : ℕ} [hpf : Fact p.Prime] {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  [Module.Finite (ZMod 2) E]

theorem p2_contra_core (hp11 : 11 ≤ p) [Nontrivial E] {G : Type*} [Group G]
    (ι : projectiveSL 2 (ZMod p) →* G) (ρG : G →* (E ≃ₗ[ZMod 2] E))
    (hE : QuasithinUnique.Setup.Family.commSub (ρG.comp ι) ⊤ = ⊤)
    (hinv : ∀ w : G, w * w = 1 → w ≠ 1 → w ≠ ι (pA (ZMod p)) → w * ι (pA (ZMod p)) =
      ι (pA (ZMod p)) * w → ∀ (c d : ZMod p) (h : c * c - d * -d = 1),
        w * ι (proj 2 (ZMod p) (slMk c d (-d) c h)) * w =
          (ι (proj 2 (ZMod p) (slMk c d (-d) c h)))⁻¹)
    {a : projectiveSL 2 (ZMod p)} (ha1 : a ≠ 1) (ha2 : a * a = 1)
    (hrk : finrank (ZMod 2) (LinearMap.range (disp (ρG.comp ι) a)) ≤ 4)
    {v : G} (hv2 : v * v = 1) (hv1 : v ≠ 1) (hva : v ≠ ι a) (hvc : v * ι a = ι a * v)
    (hker : LinearMap.ker (disp ρG (ι a)) ≤ LinearMap.ker (disp ρG v)) : False := by
  have hp5 : 5 ≤ p := by omega
  have hp := p2_eleven_or_seventeen hp11 (ρG.comp ι) hE ha1 ha2 hrk
  obtain ⟨h, hh⟩ := (p2_involution_structure hp5).1 a (pA (ZMod p)) ha1 ha2 pA_ne_one
    pA_mul_self
  set v' := ι h * v * (ι h)⁻¹ with hv'
  have hιA : ι (pA (ZMod p)) = ι h * ι a * (ι h)⁻¹ := by rw [← hh, map_mul, map_mul, map_inv]
  have hker' : LinearMap.ker (disp ρG (ι (pA (ZMod p)))) ≤ LinearMap.ker (disp ρG v') := by
    rw [hιA, hv']
    exact ker_disp_conj_le (ι h) hker
  have hv'2 : v' * v' = 1 := by
    rw [hv']
    calc ι h * v * (ι h)⁻¹ * (ι h * v * (ι h)⁻¹) = ι h * (v * v) * (ι h)⁻¹ := by group
      _ = 1 := by rw [hv2]; group
  have hv'1 : v' ≠ 1 := by
    rw [hv']
    intro h1
    apply hv1
    calc v = (ι h)⁻¹ * (ι h * v * (ι h)⁻¹) * ι h := by group
      _ = 1 := by rw [h1]; group
  have hv'a : v' ≠ ι (pA (ZMod p)) := by
    rw [hv', hιA]
    intro h1
    apply hva
    calc v = (ι h)⁻¹ * (ι h * v * (ι h)⁻¹) * ι h := by group
      _ = (ι h)⁻¹ * (ι h * ι a * (ι h)⁻¹) * ι h := by rw [h1]
      _ = ι a := by group
  have hv'c : v' * ι (pA (ZMod p)) = ι (pA (ZMod p)) * v' := by
    rw [hv', hιA]
    calc ι h * v * (ι h)⁻¹ * (ι h * ι a * (ι h)⁻¹) = ι h * (v * ι a) * (ι h)⁻¹ := by group
      _ = ι h * (ι a * v) * (ι h)⁻¹ := by rw [hvc]
      _ = ι h * ι a * (ι h)⁻¹ * (ι h * v * (ι h)⁻¹) := by group
  have hrkA : finrank (ZMod 2) (LinearMap.range (disp (ρG.comp ι) (pA (ZMod p)))) ≤ 4 :=
    (p2_rank_eq hp5 (ρG.comp ι) ha1 ha2 pA_ne_one pA_mul_self).le.trans hrk
  have hrot : ∀ (c d : ZMod p) (hcd : c * c - d * -d = 1),
      LinearMap.ker (disp (ρG.comp ι) (pA (ZMod p))) ≤ LinearMap.ker (disp (ρG.comp ι)
        ((proj 2 (ZMod p) (slMk c d (-d) c hcd))⁻¹ *
          (proj 2 (ZMod p) (slMk c d (-d) c hcd))⁻¹)) := by
    intro c d hcd
    have hga : ι (proj 2 (ZMod p) (slMk c d (-d) c hcd)) * ι (pA (ZMod p)) =
        ι (pA (ZMod p)) * ι (proj 2 (ZMod p) (slMk c d (-d) c hcd)) := by
      rw [pA, ← map_mul, ← map_mul, ← map_mul, ← map_mul]
      exact congrArg (fun M => ι (proj 2 (ZMod p) M)) (slMk_rot_mul_slA c d hcd)
    have h1 := ker_disp_le_rot ρG hv'2 (hinv v' hv'2 hv'1 hv'a hv'c c d hcd) hga hker'
    show LinearMap.ker (disp ρG (ι (pA (ZMod p)))) ≤ LinearMap.ker (disp ρG
      (ι ((proj 2 (ZMod p) (slMk c d (-d) c hcd))⁻¹ * (proj 2 (ZMod p) (slMk c d (-d) c hcd))⁻¹)))
    rw [map_mul, map_inv]
    exact h1
  rcases hp with rfl | rfl
  · exact p2_final_eleven (ρG.comp ι) hE hrkA (hrot 3 5 rot11_det)
  · exact p2_final_seventeen (ρG.comp ι) hE (hrot 4 6 rot17_det)

end Core

section Offender

variable {p : ℕ} [hpf : Fact p.Prime] {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  [Module.Finite (ZMod 2) E]

theorem p2_rank_ge_four (hp : p = 11 ∨ p = 17) [Nontrivial E]
    (ρ : projectiveSL 2 (ZMod p) →* (E ≃ₗ[ZMod 2] E)) (hE : QuasithinUnique.Setup.Family.commSub ρ ⊤ = ⊤)
    {b : projectiveSL 2 (ZMod p)} (hb1 : b ≠ 1) (hb2 : b * b = 1) :
    4 ≤ finrank (ZMod 2) (LinearMap.range (disp ρ b)) := by
  rcases hp with rfl | rfl
  · exact p2_rank_ge_four_eleven ρ hE hb1 hb2
  · exact p2_rank_ge_four_seventeen ρ hE hb1 hb2

theorem fixedSub_eq_ker_disp {G : Type*} [Group G] (ρ : G →* (E ≃ₗ[ZMod 2] E))
    {B : Subgroup G} {a : G} (ha : a ∈ B)
    (h : finrank (ZMod 2) E - finrank (ZMod 2) (fixedSub ρ B) ≤
      finrank (ZMod 2) (LinearMap.range (disp ρ a))) :
    fixedSub ρ B = LinearMap.ker (disp ρ a) := by
  have hle := fixedSub_le_ker_disp ρ ha
  refine Submodule.eq_of_le_of_finrank_le hle ?_
  have h1 := LinearMap.finrank_range_add_finrank_ker (disp ρ a)
  have h2 := Submodule.finrank_le (fixedSub ρ B)
  omega

theorem p2_internal_offender2F (hp11 : 11 ≤ p) [Nontrivial E]
    (ρ : projectiveSL 2 (ZMod p) →* (E ≃ₗ[ZMod 2] E)) (hE : QuasithinUnique.Setup.Family.commSub ρ ⊤ = ⊤)
    {B : Subgroup (projectiveSL 2 (ZMod p))} (hB1 : B ≠ ⊥)
    (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hB2 : ∀ a ∈ B, a * a = 1)
    (hoff : finrank (ZMod 2) E - finrank (ZMod 2) (fixedSub ρ B) ≤
      2 * Nat.log 2 (Nat.card B)) : False := by
  have hp5 : 5 ≤ p := by omega
  have hp2 : p ≠ 2 := by omega
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hpf.out Nat.prime_two).1 h')
  have h4 : Nat.card B ≤ 4 := (p2_involution_structure hp5).2 B hBc hB2
  obtain ⟨⟨a, haB⟩, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hB1
  have ha1 : a ≠ 1 := fun h => ha (Subtype.ext h)
  by_cases hsmall : Nat.card B ≤ 2
  · have hlog : 2 * Nat.log 2 (Nat.card B) ≤ 2 :=
      Nat.mul_le_mul_left 2 ((Nat.log_mono_right hsmall).trans (by decide : Nat.log 2 2 ≤ 1))
    have hrk := finrank_range_disp_le_of_offender ρ haB (hoff.trans hlog)
    have := (p2_actor_of_low_rank_involution hp5 ρ hE ha1 (hB2 a haB) hrk).2.2
    omega
  have hlog : 2 * Nat.log 2 (Nat.card B) ≤ 4 :=
    Nat.mul_le_mul_left 2 ((Nat.log_mono_right h4).trans (by decide : Nat.log 2 4 ≤ 2))
  have hrkB : ∀ b ∈ B, finrank (ZMod 2) (LinearMap.range (disp ρ b)) ≤ 4 :=
    fun b hb => finrank_range_disp_le_of_offender ρ hb (hoff.trans hlog)
  have hp := p2_eleven_or_seventeen hp11 ρ hE ha1 (hB2 a haB) (hrkB a haB)
  have hge := p2_rank_ge_four hp ρ hE ha1 (hB2 a haB)
  have hfix := fixedSub_eq_ker_disp ρ haB (hoff.trans (hlog.trans hge))
  obtain ⟨t, htB, u, huB, ht1, hu1, htu⟩ := exists_two_ne_one hsmall
  obtain ⟨v, hvB, hv1, hva⟩ : ∃ v ∈ B, v ≠ 1 ∧ v ≠ a := by
    by_cases hta : t = a
    · exact ⟨u, huB, hu1, fun h => htu (hta.trans h.symm)⟩
    · exact ⟨t, htB, ht1, hta⟩
  have hker : LinearMap.ker (disp ρ a) ≤ LinearMap.ker (disp ρ v) := by
    rw [← hfix]
    exact fixedSub_le_ker_disp ρ hvB
  have hE' : QuasithinUnique.Setup.Family.commSub (ρ.comp (MonoidHom.id _)) ⊤ = ⊤ := by rw [MonoidHom.comp_id]; exact hE
  refine p2_contra_core hp11 (MonoidHom.id _) ρ hE' ?_ ha1 (hB2 a haB) (hrkB a haB)
    (hB2 v hvB) hv1 hva (hBc v hvB a haB) hker
  intro w hw2 hw1 hwa hwc c d hcd
  exact p2_conj_rotation h2 hw2 hw1 hwa hwc hcd

theorem pgl2_hinv (hp2 : p ≠ 2) (w : PGL2 (ZMod p)) (hw2 : w * w = 1) (hw1 : w ≠ 1)
    (hwa : w ≠ p2PGL (ZMod p) (pA (ZMod p)))
    (hwc : w * p2PGL (ZMod p) (pA (ZMod p)) = p2PGL (ZMod p) (pA (ZMod p)) * w)
    (c d : ZMod p) (hcd : c * c - d * -d = 1) :
    w * p2PGL (ZMod p) (proj 2 (ZMod p) (slMk c d (-d) c hcd)) * w =
      (p2PGL (ZMod p) (proj 2 (ZMod p) (slMk c d (-d) c hcd)))⁻¹ := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hpf.out Nat.prime_two).1 h')
  obtain ⟨V, rfl⟩ := ProjGenLinGroup.mk_surjective w
  rw [p2PGL_proj]
  have hA : p2PGL (ZMod p) (pA (ZMod p)) = ProjGenLinGroup.mk glA := rfl
  rw [hA] at hwa hwc
  refine pgl2_conj_rotation h2 hw2 hw1 hwa hwc ?_ ?_
  · simp [coe_slMk]
  · simp [coe_slMk]
    rfl

theorem pgl2_offender2F
    (hp11 : 11 ≤ p) [Nontrivial E]
    (ρ : PGL2 (ZMod p) →* (E ≃ₗ[ZMod 2] E)) (hE : QuasithinUnique.Setup.Family.commSub ρ (pglS (ZMod p)) = ⊤)
    {B : Subgroup (PGL2 (ZMod p))} (hB1 : B ≠ ⊥) (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hB2 : ∀ a ∈ B, a * a = 1)
    (hoff : finrank (ZMod 2) E - finrank (ZMod 2) (fixedSub ρ B) ≤
      2 * Nat.log 2 (Nat.card B)) : False := by
  have hp5 : 5 ≤ p := by omega
  have hp2 : p ≠ 2 := by omega
  have hK : ringChar (ZMod p) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
  obtain ⟨-, hidx, -, -, hpair⟩ := projective_involution_pairing (ZMod p) hK
  have : CFSG.IsElementaryAbelian 2 B := isElementaryAbelian_two_of hBc hB2
  have h4 : Nat.card B ≤ 4 := card_le_four_of_elementaryAbelian hK B
  have : Finite (PGL2 (ZMod p)) := Finite.of_surjective _ ProjGenLinGroup.mk_surjective
  set ρ₀ := ρ.comp (p2PGL (ZMod p)) with hρ₀
  have hE₀ : QuasithinUnique.Setup.Family.commSub ρ₀ ⊤ = ⊤ := by
    rw [← hE]
    apply le_antisymm
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨s, -, e, rfl⟩
      exact Submodule.subset_span ⟨p2PGL (ZMod p) s, mem_pglS_iff_p2PGL.2 ⟨s, rfl⟩, e, rfl⟩
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨x, hx, e, rfl⟩
      obtain ⟨s, rfl⟩ := mem_pglS_iff_p2PGL.1 hx
      exact Submodule.subset_span ⟨s, trivial, e, rfl⟩
  have hhinv := pgl2_hinv (p := p) hp2
  have hlog4 : 2 * Nat.log 2 (Nat.card B) ≤ 4 :=
    Nat.mul_le_mul_left 2 ((Nat.log_mono_right h4).trans (by decide : Nat.log 2 4 ≤ 2))
  by_cases hcase : ∃ a ∈ B, a ∈ pglS (ZMod p) ∧ a ≠ 1
  · obtain ⟨a, haB, haS, ha1⟩ := hcase
    obtain ⟨a₀, rfl⟩ := mem_pglS_iff_p2PGL.1 haS
    have ha₀1 : a₀ ≠ 1 := fun h => ha1 (by rw [h, map_one])
    have ha₀2 : a₀ * a₀ = 1 := p2PGL_injective (by rw [map_mul, map_one]; exact hB2 _ haB)
    have hrk : finrank (ZMod 2) (LinearMap.range (disp ρ₀ a₀)) ≤ 4 :=
      finrank_range_disp_le_of_offender ρ haB (hoff.trans hlog4)
    have hp := p2_eleven_or_seventeen hp11 ρ₀ hE₀ ha₀1 ha₀2 hrk
    have hge := p2_rank_ge_four hp ρ₀ hE₀ ha₀1 ha₀2
    by_cases hsmall : Nat.card B ≤ 2
    · have hlog : 2 * Nat.log 2 (Nat.card B) ≤ 2 :=
        Nat.mul_le_mul_left 2 ((Nat.log_mono_right hsmall).trans (by decide : Nat.log 2 2 ≤ 1))
      have := finrank_range_disp_le_of_offender ρ haB (hoff.trans hlog)
      have hge' : 4 ≤ finrank (ZMod 2) (LinearMap.range (disp ρ (p2PGL (ZMod p) a₀))) := hge
      omega
    have hfix := fixedSub_eq_ker_disp ρ haB (hoff.trans (hlog4.trans hge))
    obtain ⟨t, htB, u, huB, ht1, hu1, htu⟩ := exists_two_ne_one hsmall
    obtain ⟨v, hvB, hv1, hva⟩ : ∃ v ∈ B, v ≠ 1 ∧ v ≠ p2PGL (ZMod p) a₀ := by
      by_cases hta : t = p2PGL (ZMod p) a₀
      · exact ⟨u, huB, hu1, fun h => htu (hta.trans h.symm)⟩
      · exact ⟨t, htB, ht1, hta⟩
    have hker : LinearMap.ker (disp ρ (p2PGL (ZMod p) a₀)) ≤ LinearMap.ker (disp ρ v) := by
      rw [← hfix]
      exact fixedSub_le_ker_disp ρ hvB
    exact p2_contra_core hp11 (p2PGL (ZMod p)) ρ hE₀ hhinv ha₀1 ha₀2 hrk (hB2 v hvB) hv1 hva
      (hBc v hvB _ haB) hker
  ·
    push Not at hcase
    obtain ⟨t, htB, ht1⟩ : ∃ t ∈ B, t ≠ 1 := by
      obtain ⟨t, ht⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hB1
      exact ⟨t, t.2, fun h => ht (Subtype.ext h)⟩
    have ht2 : t * t = 1 := hB2 t htB
    have htS : t ∉ pglS (ZMod p) := fun h => ht1 (hcase t htB h)
    have hBsub : ∀ b ∈ B, b = 1 ∨ b = t := by
      intro b hb
      by_cases hb1 : b = 1
      · exact Or.inl hb1
      · right
        have hbS : b ∉ pglS (ZMod p) := fun h => hb1 (hcase b hb h)
        have hmem : b * t⁻¹ ∈ pglS (ZMod p) := by
          rw [Subgroup.mul_mem_iff_of_index_two hidx]
          simp [hbS, htS]
        have : b * t⁻¹ = 1 := hcase _ (B.mul_mem hb (B.inv_mem htB)) hmem
        exact mul_inv_eq_one.1 this
    have hcardB : Nat.card B ≤ 2 := by
      have hsub : (B : Set (PGL2 (ZMod p))) ⊆ {1, t} := fun b hb => by
        rcases hBsub b hb with h | h
        · exact Or.inl h
        · exact Or.inr h
      calc Nat.card B = Set.ncard (B : Set (PGL2 (ZMod p))) := (Nat.card_coe_set_eq _).symm
        _ ≤ Set.ncard ({1, t} : Set (PGL2 (ZMod p))) := Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ Set.ncard ({t} : Set (PGL2 (ZMod p))) + 1 := Set.ncard_insert_le _ _
        _ = 2 := by rw [Set.ncard_singleton]
    have hlog : 2 * Nat.log 2 (Nat.card B) ≤ 2 :=
      Nat.mul_le_mul_left 2 ((Nat.log_mono_right hcardB).trans (by decide : Nat.log 2 2 ≤ 1))
    have hrt : finrank (ZMod 2) (LinearMap.range (disp ρ t)) ≤ 2 :=
      finrank_range_disp_le_of_offender ρ htB (hoff.trans hlog)
    obtain ⟨s, hsS, hst, hcomm⟩ := hpair t ht2 ht1
    set t' := s⁻¹ * t * s with ht'
    have hrt' : finrank (ZMod 2) (LinearMap.range (disp ρ t')) ≤ 2 := by
      have := finrank_range_disp_conj ρ t s⁻¹
      rw [inv_inv] at this
      rw [ht', this]
      exact hrt
    have ht'S : t' ∉ pglS (ZMod p) := by
      intro h
      apply htS
      have hs' : s⁻¹ ∈ pglS (ZMod p) := (pglS (ZMod p)).inv_mem hsS
      have : t = s * t' * s⁻¹ := by rw [ht']; group
      rw [this]
      exact (pglS (ZMod p)).mul_mem ((pglS (ZMod p)).mul_mem hsS h) hs'
    have hasS : t * t' ∈ pglS (ZMod p) := by
      rw [Subgroup.mul_mem_iff_of_index_two hidx]
      simp [htS, ht'S]
    obtain ⟨a₀, ha₀⟩ := mem_pglS_iff_p2PGL.1 hasS
    have hc : t * t' = t' * t := hcomm.eq
    have hsq' : t' * t' = 1 := by
      rw [ht']
      calc s⁻¹ * t * s * (s⁻¹ * t * s) = s⁻¹ * (t * t) * s := by group
        _ = 1 := by rw [ht2]; group
    have ha1 : t * t' ≠ 1 := by
      intro h
      apply hst
      have h1 : t' = t⁻¹ := eq_inv_of_mul_eq_one_right h
      have h2 : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
      rw [h1, h2]
    have ha2 : (t * t') * (t * t') = 1 := by
      calc (t * t') * (t * t') = t * (t' * t) * t' := by group
        _ = t * (t * t') * t' := by rw [← hc]
        _ = (t * t) * (t' * t') := by group
        _ = 1 := by rw [hsq', ht2, mul_one]
    have ha₀1 : a₀ ≠ 1 := fun h => ha1 (by rw [← ha₀, h, map_one])
    have ha₀2 : a₀ * a₀ = 1 := p2PGL_injective (by rw [map_mul, ha₀, map_one]; exact ha2)
    have hrka : finrank (ZMod 2) (LinearMap.range (disp ρ (t * t'))) ≤ 4 :=
      (finrank_range_disp_mul_le ρ t t').trans (by omega)
    have hrk : finrank (ZMod 2) (LinearMap.range (disp ρ₀ a₀)) ≤ 4 := by
      have e1 : disp ρ₀ a₀ = disp ρ (t * t') := by rw [← ha₀]; rfl
      rw [e1]
      exact hrka
    have hp := p2_eleven_or_seventeen hp11 ρ₀ hE₀ ha₀1 ha₀2 hrk
    have hge := p2_rank_ge_four hp ρ₀ hE₀ ha₀1 ha₀2
    have hge' : 4 ≤ finrank (ZMod 2) (LinearMap.range (disp ρ (t * t'))) := by
      have e1 : disp ρ₀ a₀ = disp ρ (t * t') := by rw [← ha₀]; rfl
      rw [← e1]
      exact hge
    have hker : LinearMap.ker (disp ρ (p2PGL (ZMod p) a₀)) ≤ LinearMap.ker (disp ρ t) := by
      rw [ha₀]
      have hle : LinearMap.ker (disp ρ t) ⊓ LinearMap.ker (disp ρ t') ≤
          LinearMap.ker (disp ρ (t * t')) := by
        intro x hx
        obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.1 hx
        rw [mem_ker_disp, map_mul, LinearEquiv.mul_apply, mem_ker_disp.1 hx2, mem_ker_disp.1 hx1]
      have h1 := LinearMap.finrank_range_add_finrank_ker (disp ρ t)
      have h2 := LinearMap.finrank_range_add_finrank_ker (disp ρ t')
      have h3 := LinearMap.finrank_range_add_finrank_ker (disp ρ (t * t'))
      have h4 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker (disp ρ t))
        (LinearMap.ker (disp ρ t'))
      have h5 := Submodule.finrank_le (LinearMap.ker (disp ρ t) ⊔ LinearMap.ker (disp ρ t'))
      have heq : LinearMap.ker (disp ρ t) ⊓ LinearMap.ker (disp ρ t') =
          LinearMap.ker (disp ρ (t * t')) :=
        Submodule.eq_of_le_of_finrank_le hle (by omega)
      rw [← heq]
      exact inf_le_left
    have hta : t * p2PGL (ZMod p) a₀ = p2PGL (ZMod p) a₀ * t := by
      rw [ha₀]
      calc t * (t * t') = t' := by rw [← mul_assoc, ht2, one_mul]
        _ = t * t' * t := by rw [hc, mul_assoc, ht2, mul_one]
    have htne : t ≠ p2PGL (ZMod p) a₀ := fun h => htS (h ▸ mem_pglS_iff_p2PGL.2 ⟨a₀, rfl⟩)
    exact p2_contra_core hp11 (p2PGL (ZMod p)) ρ hE₀ hhinv ha₀1 ha₀2 hrk ht2 ht1 htne hta hker

end Offender

section Cover

theorem finrank_sub_le_two_log_of_card_le {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    [Finite E] (F : Submodule (ZMod 2) E) {n k : ℕ} (hn : n = 2 ^ k)
    (h : Nat.card E ≤ n ^ 2 * Nat.card F) :
    finrank (ZMod 2) E - finrank (ZMod 2) F ≤ 2 * Nat.log 2 n := by
  have hE : Nat.card E = 2 ^ finrank (ZMod 2) E := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hF : Nat.card F = 2 ^ finrank (ZMod 2) F := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  rw [hE, hF, hn, ← pow_mul, ← pow_add] at h
  have h2 : finrank (ZMod 2) E ≤ k * 2 + finrank (ZMod 2) F :=
    (Nat.pow_le_pow_iff_right (by norm_num)).1 h
  rw [hn, Nat.log_pow (by norm_num)]
  omega

variable {p : ℕ} [hpf : Fact p.Prime]

section Transport

variable {Hg G' E : Type*} [Group Hg] [Group G'] [AddCommGroup E] [Module (ZMod 2) E]

theorem transport_offender2 [Module.Finite (ZMod 2) E] (e' : Hg ≃* G')
    (ρH : Hg →* (E ≃ₗ[ZMod 2] E)) {B : Subgroup Hg} (hB1 : B ≠ ⊥)
    (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hB2 : ∀ a ∈ B, a * a = 1)
    (hoff : finrank (ZMod 2) E - finrank (ZMod 2) (fixedSub ρH B) ≤
      2 * Nat.log 2 (Nat.card B)) :
    B.map e'.toMonoidHom ≠ ⊥ ∧ (∀ a ∈ B.map e'.toMonoidHom, ∀ b ∈ B.map e'.toMonoidHom,
      a * b = b * a) ∧ (∀ a ∈ B.map e'.toMonoidHom, a * a = 1) ∧
      finrank (ZMod 2) E - finrank (ZMod 2)
        (fixedSub (ρH.comp e'.symm.toMonoidHom) (B.map e'.toMonoidHom)) ≤
        2 * Nat.log 2 (Nat.card (B.map e'.toMonoidHom)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _
      (show Function.Injective e'.toMonoidHom from e'.injective)]
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    show e' a * e' b = e' b * e' a
    rw [← map_mul, ← map_mul, hBc a ha b hb]
  · rintro _ ⟨a, ha, rfl⟩
    show e' a * e' a = 1
    rw [← map_mul, hB2 a ha, map_one]
  · rwa [fixedSub_comp_equiv, natCard_map_equiv]

end Transport

theorem p2_module_data2F
    (hp11 : 11 ≤ p) {E : Type*} [AddCommGroup E]
    [Module (ZMod 2) E] [Module.Finite (ZMod 2) E] [Nontrivial E] {Hg : Type*} [Group Hg]
    (ρH : Hg →* (E ≃ₗ[ZMod 2] E)) {N : Subgroup Hg} {Y : Subgroup (PGL2 (ZMod p))}
    (e : Hg ≃* Y) (hY : Y = pglS (ZMod p) ∨ Y = ⊤)
    (hN : ∀ n ∈ N, ((e n : Y) : PGL2 (ZMod p)) ∈ pglS (ZMod p)) (hcomm : QuasithinUnique.Setup.Family.commSub ρH N = ⊤)
    {B : Subgroup Hg} (hB1 : B ≠ ⊥) (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hB2 : ∀ a ∈ B, a * a = 1)
    (hoff : finrank (ZMod 2) E - finrank (ZMod 2) (fixedSub ρH B) ≤
      2 * Nat.log 2 (Nat.card B)) : False := by
  rcases hY with hY | hY
  · have hrange : (p2PGL (ZMod p)).range = pglS (ZMod p) := by
      ext x
      rw [MonoidHom.mem_range]
      exact mem_pglS_iff_p2PGL.symm
    let e' : Hg ≃* projectiveSL 2 (ZMod p) :=
      e.trans ((MulEquiv.subgroupCongr (hY.trans hrange.symm)).trans
        (MonoidHom.ofInjective (p2PGL_injective (K := ZMod p))).symm)
    obtain ⟨hB1', hBc', hB2', hoff'⟩ := transport_offender2 e' ρH hB1 hBc hB2 hoff
    have hE : QuasithinUnique.Setup.Family.commSub (ρH.comp e'.symm.toMonoidHom) ⊤ = ⊤ := by
      rw [eq_top_iff, ← hcomm, ← commSub_comp_equiv e' ρH N]
      exact QuasithinUnique.Setup.Family.commSub_mono _ le_top
    exact p2_internal_offender2F hp11 (ρH.comp e'.symm.toMonoidHom) hE hB1' hBc' hB2' hoff'
  · let e' : Hg ≃* PGL2 (ZMod p) := e.trans ((MulEquiv.subgroupCongr hY).trans Subgroup.topEquiv)
    obtain ⟨hB1', hBc', hB2', hoff'⟩ := transport_offender2 e' ρH hB1 hBc hB2 hoff
    have hE : QuasithinUnique.Setup.Family.commSub (ρH.comp e'.symm.toMonoidHom) (pglS (ZMod p)) = ⊤ := by
      rw [eq_top_iff, ← hcomm, ← commSub_comp_equiv e' ρH N]
      refine QuasithinUnique.Setup.Family.commSub_mono _ ?_
      rintro _ ⟨n, hn, rfl⟩
      exact hN n hn
    exact pgl2_offender2F hp11 (ρH.comp e'.symm.toMonoidHom) hE hB1' hBc' hB2' hoff'

end Cover

end CFSG.Quasithin.B45Exc
