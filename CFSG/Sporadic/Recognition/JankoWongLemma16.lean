module

public import CFSG.Sporadic.Recognition.JankoWongLemma15
import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCoreQuotient

public section

namespace CFSG.Sporadic.Recognition.JankoWong

open Equiv Equiv.Perm Subgroup CFSG.GH74 CFSG.GH74.GLS CFSG.Open

section Abstract

theorem closure_eq_top_of_card_twelve {D : Type*} [Group D] [Finite D] (hD : Nat.card D = 12)
    {x y : D} (hx : orderOf x = 3) (hy : orderOf y = 3) (hne : zpowers x ≠ zpowers y) :
    closure ({x, y} : Set D) = ⊤ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set E := closure ({x, y} : Set D) with hE
  have hxE : zpowers x ≤ E := Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
  have hyE : zpowers y ≤ E := Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
  have hEdvd : Nat.card E ∣ 12 := hD ▸ Subgroup.card_subgroup_dvd_card E
  have h3E : 3 ∣ Nat.card E := by
    have := Subgroup.card_dvd_of_le hxE
    rwa [Nat.card_zpowers, hx] at this
  have hcases : Nat.card E = 3 ∨ Nat.card E = 6 ∨ Nat.card E = 12 := by
    have hle : Nat.card E ≤ 12 := Nat.le_of_dvd (by norm_num) hEdvd
    have hpos : 0 < Nat.card E := Nat.card_pos
    generalize Nat.card E = n at hle hpos h3E hEdvd ⊢
    obtain ⟨k, hk⟩ := h3E
    subst hk
    have hk4 : k ≤ 4 := by omega
    interval_cases k <;> simp at hEdvd ⊢
  rcases hcases with h | h | h
  · exfalso
    have e1 : zpowers x = E := Subgroup.eq_of_le_of_card_ge hxE (by rw [h, Nat.card_zpowers, hx])
    have e2 : zpowers y = E := Subgroup.eq_of_le_of_card_ge hyE (by rw [h, Nat.card_zpowers, hy])
    exact hne (e1.trans e2.symm)
  · exfalso
    have hf3 : (Nat.card E).factorization 3 = 1 := by
      rw [h]
      have : (6 : ℕ) = 3 ^ 1 * 2 := by norm_num
      rw [this, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
        Nat.Prime.factorization_pow Nat.prime_three]
      have h2 : (2 : ℕ).factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd (by norm_num)
      simp [h2]
    have hXc : Nat.card ((zpowers x).subgroupOf E) = 3 ^ (Nat.card E).factorization 3 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hxE).toEquiv, Nat.card_zpowers, hx, hf3]
      norm_num
    have hYc : Nat.card ((zpowers y).subgroupOf E) = 3 ^ (Nat.card E).factorization 3 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyE).toEquiv, Nat.card_zpowers, hy, hf3]
      norm_num
    let X : Sylow 3 E := Sylow.ofCard _ hXc
    let Y : Sylow 3 E := Sylow.ofCard _ hYc
    have hmod := card_sylow_modEq_one 3 E
    have hidx : Nat.card (Sylow 3 E) = (Subgroup.normalizer (X : Set E)).index := by
      rw [Sylow.card_eq_index_normalizer X]
    have hdvd : (Subgroup.normalizer (X : Set E)).index ∣ 2 := by
      have h1 := Subgroup.card_mul_index (Subgroup.normalizer (X : Set E))
      have h3 : 3 ∣ Nat.card (Subgroup.normalizer (X : Set E)) := by
        have : Nat.card X ∣ Nat.card (Subgroup.normalizer (X : Set E)) :=
          Subgroup.card_dvd_of_le Subgroup.le_normalizer
        simpa [X, hXc, hf3] using this
      obtain ⟨m, hm⟩ := h3
      rw [hm, h] at h1
      have hmi : m * (Subgroup.normalizer (X : Set E)).index = 2 := by
        apply Nat.eq_of_mul_eq_mul_left (show 0 < 3 by norm_num)
        rw [← mul_assoc, h1]
      exact Dvd.intro_left m hmi
    have hn1 : Nat.card (Sylow 3 E) = 1 := by
      rw [hidx] at hmod ⊢
      unfold Nat.ModEq at hmod
      have := Nat.le_of_dvd (by norm_num) hdvd
      have hpos : 0 < (Subgroup.normalizer (X : Set E)).index := by
        rcases Nat.eq_zero_or_pos (Subgroup.normalizer (X : Set E)).index with h0 | h0
        · rw [h0] at hdvd; simp at hdvd
        · exact h0
      omega
    have hsub : Subsingleton (Sylow 3 E) := (Nat.card_eq_one_iff_unique.mp hn1).1
    have hXY : X = Y := Subsingleton.elim X Y
    have : (X : Subgroup E) = Y := congrArg (fun S : Sylow 3 E => (S : Subgroup E)) hXY
    simp only [X, Y, Sylow.coe_ofCard] at this
    apply hne
    have := congrArg (Subgroup.map E.subtype) this
    rwa [Subgroup.map_subgroupOf_eq_of_le hxE, Subgroup.map_subgroupOf_eq_of_le hyE] at this
  · exact Subgroup.eq_top_of_card_eq E (h.trans hD.symm)

theorem nine_le_card_inf {G : Type*} [Group G] {A R R₁ : Subgroup G} (hA : Nat.card A = 81)
    (hR : R ≤ A) (hR₁ : R₁ ≤ A) (h27 : Nat.card R = 27) (h27' : Nat.card R₁ = 27) :
    9 ≤ Nat.card ↥(R ⊓ R₁) := by
  have e1 : R.relIndex A * Nat.card R = Nat.card A := by
    have := Subgroup.relIndex_mul_card R A
    rwa [inf_eq_left.mpr hR] at this
  have e2 : R₁.relIndex A * Nat.card R₁ = Nat.card A := by
    have := Subgroup.relIndex_mul_card R₁ A
    rwa [inf_eq_left.mpr hR₁] at this
  have e3 : (R ⊓ R₁).relIndex A * Nat.card (R ⊓ R₁ : Subgroup G) = Nat.card A := by
    have := Subgroup.relIndex_mul_card (R ⊓ R₁) A
    rwa [inf_eq_left.mpr (inf_le_left.trans hR)] at this
  have h1 : R.relIndex A = 3 := by rw [h27, hA] at e1; omega
  have h2 : R₁.relIndex A = 3 := by rw [h27', hA] at e2; omega
  have h3 : (R ⊓ R₁).relIndex A ≤ R.relIndex A * R₁.relIndex A := Subgroup.relIndex_inf_le
  rw [h1, h2] at h3
  rw [hA] at e3
  by_contra hlt
  push Not at hlt
  have : (R ⊓ R₁).relIndex A * Nat.card (R ⊓ R₁ : Subgroup G) < 9 * 9 := by nlinarith
  omega

end Abstract

namespace Setup

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {S : Setup G} (c : Ctx S)

theorem mem_oddCore_Cg_iff
    (y : ↥c.Cg) :
    y ∈ CFSG.oddCore ↥c.Cg ↔ (y : G) ∈ c.OG := by
  rw [← c.oddCore_Cg_map]
  constructor
  · intro h; exact ⟨y, h, rfl⟩
  · rintro ⟨o, ho, hoy⟩
    have : o = y := Subtype.ext hoy
    rwa [this] at ho

theorem card_CBar
    :
    Nat.card (↥c.Cg ⧸ CFSG.oddCore ↥c.Cg) = 12 := by
  obtain ⟨-, hCg, -, -⟩ := c.lemma14
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.oddCore ↥c.Cg)
  rw [c.card_oddCore_Cg, c.card_OG_eq_81, hCg] at h
  omega

theorem card_centralizer_le_nine_of_mem_Cg
    {x : G}
    (hxC : x ∈ c.Cg) (hx3 : ∃ n : ℕ, x ^ (3 ^ n) = 1) (hxN : x ∉ c.OG) :
    Nat.card ↥(c.OG ⊓ centralizer ({x} : Set G)) ≤ 9 := by
  by_contra hgt
  push Not at hgt
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h81 := c.card_OG_eq_81
  obtain ⟨n, hn⟩ := hx3
  have hOGo := c.odd_card_OG
  have hdvd : Nat.card ↥(c.OG ⊓ centralizer ({x} : Set G)) ∣ 3 ^ 4 := by
    rw [show (3 : ℕ) ^ 4 = 81 by norm_num, ← h81]; exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨j, hj, hj3⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  have hj34 : j = 3 ∨ j = 4 := by
    rw [hj3] at hgt
    interval_cases j <;> simp at hgt ⊢
  have hR27 : Nat.card ↥(c.OG ⊓ centralizer ({x} : Set G)) = 27 := by
    rcases hj34 with h3 | h4
    · rw [hj3, h3]; norm_num
    · exfalso
      have hfull : c.OG ⊓ centralizer ({x} : Set G) = c.OG := by
        refine Subgroup.eq_of_le_of_card_ge inf_le_left ?_
        rw [hj3, h4, h81]; norm_num
      exact hxN (c.centralizer_OG_le x (fun y hy => by
        have : y ∈ c.OG ⊓ centralizer ({x} : Set G) := by rw [hfull]; exact hy
        exact Subgroup.mem_centralizer_singleton_iff.mp this.2))
  have hbot : CFSG.oddCore (↥c.Cg ⧸ CFSG.oddCore ↥c.Cg) = ⊥ :=
    CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_quotient_eq_bot
  let xC : ↥c.Cg := ⟨x, hxC⟩
  let xb : ↥c.Cg ⧸ CFSG.oddCore ↥c.Cg := QuotientGroup.mk xC
  have hxb1 : xb ≠ 1 := fun e =>
    hxN ((c.mem_oddCore_Cg_iff xC).mp ((QuotientGroup.eq_one_iff xC).mp e))
  have hxb3 : orderOf xb = 3 := by
    have h1 : xb ^ (3 ^ n) = 1 := by
      show (QuotientGroup.mk xC : ↥c.Cg ⧸ CFSG.oddCore ↥c.Cg) ^ (3 ^ n) = 1
      rw [← QuotientGroup.mk_pow]
      have : xC ^ (3 ^ n) = 1 := Subtype.ext (by simpa [xC] using hn)
      rw [this, QuotientGroup.mk_one]
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one h1)
    have hk0 : k ≠ 0 := fun e => hxb1 (by rw [e, pow_zero] at hk; exact orderOf_eq_one_iff.mp hk)
    have h12 : orderOf xb ∣ 12 := by
      have := orderOf_dvd_natCard xb
      rwa [c.card_CBar] at this
    rw [hk] at h12 ⊢
    have hk1 : k = 1 := by
      by_contra hne
      have : 3 ^ 2 ∣ 3 ^ k := pow_dvd_pow 3 (by omega)
      have := this.trans h12
      norm_num at this
    rw [hk1]; norm_num
  have hnn : ∃ gb : ↥c.Cg ⧸ CFSG.oddCore ↥c.Cg, gb * xb * gb⁻¹ ∉ zpowers xb := by
    by_contra hall
    push Not at hall
    have hnorm : (zpowers xb).Normal := ⟨fun n hn g => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
      have : g * xb ^ k * g⁻¹ = (g * xb * g⁻¹) ^ k := conj_zpow.symm
      rw [this]; exact Subgroup.zpow_mem _ (hall g) k⟩
    have hodd : Odd (Nat.card (zpowers xb)) := by rw [Nat.card_zpowers, hxb3]; decide
    have hle := le_oddCore_of_normal_odd _ hnorm hodd
    rw [hbot] at hle
    have : xb ∈ (⊥ : Subgroup (↥c.Cg ⧸ CFSG.oddCore ↥c.Cg)) := hle (Subgroup.mem_zpowers xb)
    exact hxb1 (Subgroup.mem_bot.mp this)
  obtain ⟨gb, hgb⟩ := hnn
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective gb
  have hx₁C : (h : G) * x * (h : G)⁻¹ ∈ c.Cg := c.conj_mem_Cg (c.cg_le_ng h.2) hxC
  let x₁ : G := (h : G) * x * (h : G)⁻¹
  let x₁C : ↥c.Cg := ⟨x₁, hx₁C⟩
  have hx₁Ceq : x₁C = h * xC * h⁻¹ := rfl
  let x₁b : ↥c.Cg ⧸ CFSG.oddCore ↥c.Cg := QuotientGroup.mk x₁C
  have hx₁b : x₁b = (QuotientGroup.mk h : ↥c.Cg ⧸ CFSG.oddCore ↥c.Cg) * xb *
      (QuotientGroup.mk h : ↥c.Cg ⧸ CFSG.oddCore ↥c.Cg)⁻¹ := by
    show (QuotientGroup.mk x₁C : ↥c.Cg ⧸ CFSG.oddCore ↥c.Cg) = _
    rw [hx₁Ceq]; simp [xb]
  have hx₁b3 : orderOf x₁b = 3 := by
    have h1 := orderOf_injective
      (MulAut.conj (QuotientGroup.mk h : ↥c.Cg ⧸ CFSG.oddCore ↥c.Cg)).toMonoidHom
      (MulAut.conj _).injective xb
    rw [← hxb3, ← h1, hx₁b]; simp
  have hne : zpowers xb ≠ zpowers x₁b := fun e => hgb (by
    rw [← hx₁b, e]; exact Subgroup.mem_zpowers x₁b)
  have hD : Subgroup.closure ({xb, x₁b} : Set (↥c.Cg ⧸ CFSG.oddCore ↥c.Cg)) = ⊤ :=
    closure_eq_top_of_card_twelve c.card_CBar hxb3 hx₁b3 hne
  have hmap : (Subgroup.closure ({xC, x₁C} : Set ↥c.Cg)).map
      (QuotientGroup.mk' (CFSG.oddCore ↥c.Cg)) = ⊤ := by
    rw [MonoidHom.map_closure, Set.image_pair]; exact hD
  have hgen : ∀ u : ↥c.Cg, ∃ w ∈ Subgroup.closure ({x, x₁} : Set G), w⁻¹ * (u : G) ∈ c.OG := by
    intro u
    have hu : QuotientGroup.mk' (CFSG.oddCore ↥c.Cg) u ∈ (Subgroup.closure
        ({xC, x₁C} : Set ↥c.Cg)).map (QuotientGroup.mk' (CFSG.oddCore ↥c.Cg)) := by
      rw [hmap]; exact Subgroup.mem_top _
    obtain ⟨w, hw, hwu⟩ := Subgroup.mem_map.mp hu
    refine ⟨(w : G), ?_, ?_⟩
    · have : (w : G) ∈ (Subgroup.closure ({xC, x₁C} : Set ↥c.Cg)).map c.Cg.subtype := ⟨w, hw, rfl⟩
      rwa [MonoidHom.map_closure, Set.image_pair] at this
    · have h1 : w⁻¹ * u ∈ CFSG.oddCore ↥c.Cg := (QuotientGroup.eq).mp hwu
      exact (c.mem_oddCore_Cg_iff _).mp h1
  have hNGh : ∀ y ∈ c.OG, (h : G) * y * (h : G)⁻¹ ∈ c.OG := fun y hy =>
    c.OG_normalized _ (c.cg_le_ng h.2) y hy
  have hNGh' : ∀ y ∈ c.OG, (h : G)⁻¹ * y * (h : G) ∈ c.OG := fun y hy => by
    simpa using c.OG_normalized _ (c.Ng.inv_mem (c.cg_le_ng h.2)) y hy
  have hR₁27 : Nat.card ↥(c.OG ⊓ centralizer ({x₁} : Set G)) = 27 := by
    have := card_inf_centralizer_conj_of_normalizes (A := c.OG) hNGh hNGh' x
    exact this.trans hR27
  have h9 : 9 ≤ Nat.card ↥(c.OG ⊓ centralizer ({x} : Set G) ⊓
      (c.OG ⊓ centralizer ({x₁} : Set G))) :=
    nine_le_card_inf (by rw [h81]) inf_le_left inf_le_left hR27 hR₁27
  have hcomm : ∀ u : ↥c.Cg, ∀ y ∈ c.OG ⊓ centralizer ({x} : Set G) ⊓
      (c.OG ⊓ centralizer ({x₁} : Set G)), (u : G) * y = y * (u : G) := by
    intro u y hy
    obtain ⟨w, hw, hwo⟩ := hgen u
    have hyx : y * x = x * y := Subgroup.mem_centralizer_singleton_iff.mp hy.1.2
    have hyx₁ : y * x₁ = x₁ * y := Subgroup.mem_centralizer_singleton_iff.mp hy.2.2
    have hle : Subgroup.closure ({x, x₁} : Set G) ≤ centralizer ({y} : Set G) := by
      rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hyx.symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hyx₁.symm
    have hwy : w * y = y * w := Subgroup.mem_centralizer_singleton_iff.mp (hle hw)
    have hny : (w⁻¹ * (u : G)) * y = y * (w⁻¹ * (u : G)) := c.OG_comm _ hwo y hy.1.1
    calc (u : G) * y = w * (w⁻¹ * (u : G)) * y := by group
      _ = w * ((w⁻¹ * (u : G)) * y) := by group
      _ = w * (y * (w⁻¹ * (u : G))) := by rw [hny]
      _ = (w * y) * (w⁻¹ * (u : G)) := by group
      _ = (y * w) * (w⁻¹ * (u : G)) := by rw [hwy]
      _ = y * (u : G) := by group
  have hle : c.OG ⊓ centralizer ({x} : Set G) ⊓ (c.OG ⊓ centralizer ({x₁} : Set G)) ≤
      zpowers c.s := fun y hy =>
    c.mem_zpowers_s_of_commute hy.1.1 (hcomm ⟨S.z, c.z_mem_cg⟩ y hy).symm
      (hcomm ⟨(c.t : G), c.tC_mem⟩ y hy).symm
  have h3 := Subgroup.card_le_of_le hle
  rw [Nat.card_zpowers, c.orderOf_s] at h3
  omega

theorem ocl_disjoint_a_s
    :
    Disjoint (c.ocl (c.a : G)) (c.ocl c.s) := by
  rw [Set.disjoint_left]
  rintro y ⟨g, hg, hy1⟩ ⟨h, hh, hy2⟩
  refine S.not_isConj_type3_type33 c.ha3 c.x_cube c.cycleType_a c.x_type
    (isConj_iff.mpr ⟨h⁻¹ * g, ?_⟩)
  have hgh : g * (c.a : G) * g⁻¹ = h * c.s * h⁻¹ := hy1.symm.trans hy2
  show h⁻¹ * g * (c.a : G) * (h⁻¹ * g)⁻¹ = c.s
  calc h⁻¹ * g * (c.a : G) * (h⁻¹ * g)⁻¹ = h⁻¹ * (g * (c.a : G) * g⁻¹) * h := by group
    _ = h⁻¹ * (h * c.s * h⁻¹) * h := by rw [hgh]
    _ = c.s := by group

theorem OG_sdiff_one_eq
    :
    (c.OG : Set G) \ {1} = c.ocl c.s ∪ c.ocl (c.a : G) := by
  have hsub : c.ocl c.s ∪ c.ocl (c.a : G) ⊆ (c.OG : Set G) \ {1} := by
    rintro y (hy | hy)
    · exact ⟨c.ocl_s_subset_OG hy, c.ne_one_of_mem_ocl c.s_ne_one hy⟩
    · exact ⟨c.ocl_a_subset_OG hy, c.ne_one_of_mem_ocl c.aG_ne_one hy⟩
  have h80 : ((c.OG : Set G) \ {1}).ncard = 80 := by
    rw [Set.ncard_sdiff_singleton_of_mem c.OG.one_mem]
    have h81 := c.card_OG_eq_81
    have : (c.OG : Set G).ncard = 81 := by rw [← Nat.card_coe_set_eq]; exact h81
    omega
  have hun : (c.ocl c.s ∪ c.ocl (c.a : G)).ncard = 80 := by
    rw [Set.ncard_union_eq c.ocl_disjoint_a_s.symm (Set.toFinite _) (Set.toFinite _),
      ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq (c.ocl (c.a : G)), c.card_ocl_s,
      c.card_ocl_a]
  exact (Set.eq_of_subset_of_ncard_le hsub (by omega) (Set.toFinite _)).symm

theorem card_centralizer_le_nine
    {x : G}
    (hx3 : ∃ n : ℕ, x ^ (3 ^ n) = 1) (hxN : x ∉ c.OG) :
    Nat.card ↥(c.OG ⊓ centralizer ({x} : Set G)) ≤ 9 := by
  by_contra hgt
  push Not at hgt
  have h81 := c.card_OG_eq_81
  obtain ⟨n, hn⟩ := hx3
  by_cases hs : ∃ y ∈ c.OG ⊓ centralizer ({x} : Set G), y ∈ c.ocl c.s
  · obtain ⟨y, hyR, g, hg, rfl⟩ := hs
    have hgi : g⁻¹ ∈ c.NG := c.NG.inv_mem hg
    have hxy : x * (g * c.s * g⁻¹) = (g * c.s * g⁻¹) * x :=
      (Subgroup.mem_centralizer_singleton_iff.mp hyR.2).symm
    have hx'C : g⁻¹ * x * g ∈ c.Cg := by
      rw [c.mem_cg_iff]
      calc g⁻¹ * x * g * c.s * (g⁻¹ * x * g)⁻¹ = g⁻¹ * (x * (g * c.s * g⁻¹) * x⁻¹) * g := by group
        _ = g⁻¹ * (g * c.s * g⁻¹) * g := by rw [hxy]; group
        _ = c.s := by group
    have hx'3 : ∃ m : ℕ, (g⁻¹ * x * g) ^ (3 ^ m) = 1 := ⟨n, by
      have : (g⁻¹ * x * g) ^ (3 ^ n) = g⁻¹ * x ^ (3 ^ n) * g := by
        simpa using conj_pow (a := g⁻¹) (b := x) (i := 3 ^ n)
      rw [this, hn]; group⟩
    have hx'N : g⁻¹ * x * g ∉ c.OG := fun h => hxN (by
      have := c.conj_mem_OG_of_mem_NG hg h
      simpa [mul_assoc] using this)
    have h1 := c.card_centralizer_le_nine_of_mem_Cg hx'C hx'3 hx'N
    have hOG1 : ∀ y ∈ c.OG, g⁻¹ * y * g⁻¹⁻¹ ∈ c.OG := fun y hy => c.conj_mem_OG_of_mem_NG hgi hy
    have hOG2 : ∀ y ∈ c.OG, g⁻¹⁻¹ * y * g⁻¹ ∈ c.OG := fun y hy => by
      simpa using c.conj_mem_OG_of_mem_NG hg hy
    have h2 := card_inf_centralizer_conj_of_normalizes (A := c.OG) (g := g⁻¹)
      hOG1 hOG2 x
    have e : g⁻¹ * x * g⁻¹⁻¹ = g⁻¹ * x * g := by simp
    rw [e] at h2
    omega
  · push Not at hs
    set R : Subgroup G := c.OG ⊓ centralizer ({x} : Set G) with hR
    have hsub : ((R : Set G) \ {1}) ⊆ c.ocl (c.a : G) := by
      rintro y ⟨hyR, hy1⟩
      have hyOG : y ∈ (c.OG : Set G) \ {1} := ⟨hyR.1, hy1⟩
      rw [c.OG_sdiff_one_eq] at hyOG
      rcases hyOG with hy | hy
      · exact absurd hy (hs y hyR)
      · exact hy
    have hR20 : ((R : Set G) \ {1}).ncard ≤ 20 := by
      have := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [← Nat.card_coe_set_eq (c.ocl (c.a : G)), c.card_ocl_a] at this
      exact this
    have hRcard : ((R : Set G) \ {1}).ncard = Nat.card R - 1 := by
      rw [Set.ncard_sdiff_singleton_of_mem R.one_mem, ← Nat.card_coe_set_eq]
      rfl
    have hdvd : Nat.card R ∣ 3 ^ 4 := by
      rw [show (3 : ℕ) ^ 4 = 81 by norm_num, ← h81]; exact Subgroup.card_dvd_of_le inf_le_left
    obtain ⟨j, hj, hj3⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    rw [hj3] at hgt hRcard
    interval_cases j <;> simp at hgt <;> omega

end Ctx

end Setup

end CFSG.Sporadic.Recognition.JankoWong
