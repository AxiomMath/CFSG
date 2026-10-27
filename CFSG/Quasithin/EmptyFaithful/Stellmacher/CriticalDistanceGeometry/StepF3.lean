module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.StepF1
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.StepE

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S152X CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53
open Equiv (Perm)

set_option linter.unusedSectionVars false

section Finite

open Equiv in
theorem tabF3_nat_stab : ∀ σ : Perm (Fin 5),
    (∀ b ∈ S5TF, ∀ w : nat.W, nat.act σ (nat.act b w * w⁻¹) = nat.act b w * w⁻¹) → σ ∈ S5TF := by
  decide +kernel

open Equiv in
theorem tabF3_orth_stab_That : ∀ σ : Perm (Fin 5),
    (∀ b ∈ S5ThatF, ∀ w : orth.W, orth.act σ (orth.act b w * w⁻¹) = orth.act b w * w⁻¹) →
      σ ∈ S5ThatF := by
  decide +kernel

theorem tabF3_T_sub : ∀ x ∈ S5TF, x ∈ S5SylF := by decide +kernel

theorem tabF3_That_sub : ∀ x ∈ S5ThatF, x ∈ S5SylF := by decide +kernel

open Equiv in
def tabF3_C (t : Perm (Fin 5)) : Finset (Perm (Fin 5)) :=
  Finset.univ.filter fun σ => σ ^ 8 = 1 ∧
    ∀ w : orth.W, orth.act σ (orth.act t w * w⁻¹) = orth.act t w * w⁻¹

open Equiv in
theorem tabF3_orth_t02 : ∀ x ∈ tabF3_C (swap 0 2), ∀ y ∈ tabF3_C (swap 0 2),
    (x * y) ^ 8 = 1 → x ∈ S5SylF ∨ y ∈ S5SylF ∨ x * y ∈ S5SylF := by decide +kernel

open Equiv in
theorem tabF3_orth_t13 : ∀ x ∈ tabF3_C (swap 1 3), ∀ y ∈ tabF3_C (swap 1 3),
    (x * y) ^ 8 = 1 → x ∈ S5SylF ∨ y ∈ S5SylF ∨ x * y ∈ S5SylF := by decide +kernel

end Finite

section Algebra

variable {G : Type} [Group G]

theorem relIndex_inf_le_two_of_three {A N : Subgroup G}
    (h : ∀ x ∈ A, ∀ y ∈ A, x ∈ N ∨ y ∈ N ∨ x * y ∈ N) : (A ⊓ N).relIndex A ≤ 2 := by
  by_cases hAN : A ≤ N
  · rw [inf_eq_left.mpr hAN, Subgroup.relIndex_self]; norm_num
  · obtain ⟨x, hxA, hxN⟩ := IsConcreteLE.not_le_iff_exists.mp hAN
    let f : Bool → ↥A ⧸ (A ⊓ N).subgroupOf A := fun b =>
      if b then QuotientGroup.mk (⟨x⁻¹, A.inv_mem hxA⟩ : ↥A) else QuotientGroup.mk 1
    have hsurj : Function.Surjective f := by
      intro q
      induction q using QuotientGroup.induction_on with
      | H a =>
        rcases h x hxA a a.2 with h1 | h1 | h1
        · exact absurd h1 hxN
        · refine ⟨false, ?_⟩
          show (QuotientGroup.mk 1 : ↥A ⧸ (A ⊓ N).subgroupOf A) = QuotientGroup.mk a
          rw [QuotientGroup.eq]
          exact Subgroup.mem_subgroupOf.mpr ⟨by simp, by simpa using h1⟩
        · refine ⟨true, ?_⟩
          show (QuotientGroup.mk (⟨x⁻¹, A.inv_mem hxA⟩ : ↥A) : ↥A ⧸ (A ⊓ N).subgroupOf A) =
            QuotientGroup.mk a
          rw [QuotientGroup.eq]
          exact Subgroup.mem_subgroupOf.mpr ⟨by simpa using A.mul_mem hxA a.2, by simpa using h1⟩
    have := Nat.card_le_card_of_surjective f hsurj
    simpa [Subgroup.relIndex, Subgroup.index] using this

theorem pow_eight_of_pow_two_pow {K : Type*} [Group K] (φ : K →* Perm (Fin 5)) {x : K} {k : ℕ}
    (h : x ^ (2 ^ k) = 1) : φ x ^ 8 = 1 := by
  have h1 : φ x ^ (2 ^ k) = 1 := by rw [← map_pow, h, map_one]
  have h2 : orderOf (φ x) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h1
  have h3 : orderOf (φ x) ∣ 120 := F53.card_perm5 ▸ orderOf_dvd_natCard (φ x)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
  have hj3 : j ≤ 3 := by
    by_contra hcon
    push Not at hcon
    have h4 : 2 ^ 4 ∣ 2 ^ j := pow_dvd_pow 2 hcon
    rw [hj] at h3
    have := h4.trans h3
    omega
  have h8 : orderOf (φ x) ∣ 8 := by
    rw [hj]
    exact (pow_dvd_pow 2 hj3 : 2 ^ j ∣ 2 ^ 3)
  exact orderOf_dvd_iff_pow_eq_one.mp h8

theorem pow_eight_of_isPGroup {K B : Subgroup G} (hBK : B ≤ K) (hB : IsPGroup 2 B)
    (Ψ : ↥K →* Perm (Fin 5)) {x : G} (hx : x ∈ B) : Ψ ⟨x, hBK hx⟩ ^ 8 = 1 := by
  obtain ⟨k, hk⟩ := hB ⟨x, hx⟩
  refine pow_eight_of_pow_two_pow Ψ (x := ⟨x, hBK hx⟩) (k := k) ?_
  have : (x : G) ^ (2 ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  exact Subtype.ext (by simpa using this)

end Algebra

section Bridge

variable {G : Type} [Group G]

theorem pointwise_bridge {M5 : Model 5} {K L X : Subgroup G} [(L.subgroupOf X).Normal]
    {Ψ : ↥K →* Perm (Fin 5)} {β : M5.W →* ↥X ⧸ L.subgroupOf X}
    (hsd : SecData M5 K L X Ψ β) {A R : Subgroup G}
    (hAR : ∀ a ∈ A, ∀ x ∈ X, a * x * a⁻¹ * x⁻¹ ∈ R) {g : G} (hgK : g ∈ K)
    (hg : ∀ r ∈ R, g * r = r * g) :
    ∀ b ∈ (A.subgroupOf K).map Ψ, ∀ w : M5.W,
      M5.act (Ψ ⟨g, hgK⟩) (M5.act b w * w⁻¹) = M5.act b w * w⁻¹ := by
  rintro _ ⟨a', ha', rfl⟩ w
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (β w)
  obtain ⟨hax, h1⟩ := hsd.beta_comm a'.2 hx.symm
  set w' : M5.W := M5.act (Ψ a') w * w⁻¹ with hw'
  have hyR : (a' : G) * (x : G) * (a' : G)⁻¹ * (x : G)⁻¹ ∈ R :=
    hAR a' (Subgroup.mem_subgroupOf.mp ha') x x.2
  obtain ⟨hgy, h2⟩ := hsd.beta_comm hgK
    (u := w') (x := ⟨(a' : G) * (x : G) * (a' : G)⁻¹ * (x : G)⁻¹, hax⟩) h1
  have h3 : M5.act (Ψ ⟨g, hgK⟩) w' * w'⁻¹ = 1 := by
    apply hsd.inj
    rw [h2, map_one, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    have : g * ((a' : G) * (x : G) * (a' : G)⁻¹ * (x : G)⁻¹) * g⁻¹ *
        ((a' : G) * (x : G) * (a' : G)⁻¹ * (x : G)⁻¹)⁻¹ = 1 := by
      rw [hg _ hyR]; group
    show g * ((a' : G) * (x : G) * (a' : G)⁻¹ * (x : G)⁻¹) * g⁻¹ *
        ((a' : G) * (x : G) * (a' : G)⁻¹ * (x : G)⁻¹)⁻¹ ∈ L
    rw [this]
    exact L.one_mem
  exact mul_inv_eq_one.mp h3

end Bridge

section Cases

variable {G : Type} [Group G]

theorem swap_mem_syl_cases {t : Perm (Fin 5)} (ht : t.IsSwap) (htS : t ∈ S5Syl) :
    t = Equiv.swap 0 2 ∨ t = Equiv.swap 1 3 := by
  obtain ⟨h1, h2, h3⟩ := (isSwap_iff t).mp ht
  exact (tabF_swap_that t ((mem_S5Syl_iff t).mp htS) (by rwa [← pow_two]) h3).1

theorem stab_of_case_nat {M5 : Model 5} (hM : M5 = nat) {σ : Perm (Fin 5)}
    (h : ∀ b ∈ S5T, ∀ w : M5.W, M5.act σ (M5.act b w * w⁻¹) = M5.act b w * w⁻¹) :
    σ ∈ S5Syl := by
  subst hM
  rw [mem_S5Syl_iff]
  exact tabF3_T_sub σ (tabF3_nat_stab σ fun b hb w => h b ((mem_S5T_iff b).mpr hb) w)

theorem stab_of_case_That {M5 : Model 5} (hM : M5 = orth) {σ : Perm (Fin 5)}
    (h : ∀ b ∈ S5That, ∀ w : M5.W, M5.act σ (M5.act b w * w⁻¹) = M5.act b w * w⁻¹) :
    σ ∈ S5Syl := by
  subst hM
  rw [mem_S5Syl_iff]
  exact tabF3_That_sub σ (tabF3_orth_stab_That σ fun b hb w => h b ((mem_S5That_iff b).mpr hb) w)

theorem three_of_case_t {M5 : Model 5} (hM : M5 = orth) {t : Perm (Fin 5)} (ht : t.IsSwap)
    (htS : t ∈ S5Syl) {x y : Perm (Fin 5)}
    (hx : ∀ w : M5.W, M5.act x (M5.act t w * w⁻¹) = M5.act t w * w⁻¹)
    (hy : ∀ w : M5.W, M5.act y (M5.act t w * w⁻¹) = M5.act t w * w⁻¹)
    (hx8 : x ^ 8 = 1) (hy8 : y ^ 8 = 1) (hxy8 : (x * y) ^ 8 = 1) :
    x ∈ S5Syl ∨ y ∈ S5Syl ∨ x * y ∈ S5Syl := by
  subst hM
  simp only [mem_S5Syl_iff]
  rcases swap_mem_syl_cases ht htS with rfl | rfl
  · exact tabF3_orth_t02 x (by rw [tabF3_C, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hx8, hx⟩) y
      (by rw [tabF3_C, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hy8, hy⟩) hxy8
  · exact tabF3_orth_t13 x (by rw [tabF3_C, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hx8, hx⟩) y
      (by rw [tabF3_C, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hy8, hy⟩) hxy8

theorem two_elements_of_index_le_two {B : Subgroup (Perm (Fin 5))} (h : (fixW orth B).index ≤ 2) :
    ∀ x ∈ B, ∀ y ∈ B, x = 1 ∨ y = 1 ∨ x = y := by
  have hidx : ∀ z ∈ B, idx orth z ≤ 2 := by
    intro z hz
    refine le_trans ?_ h
    refine Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) ?_
    refine Subgroup.index_dvd_of_le ?_
    intro w hw b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact hw _ (B.zpow_mem hz k)
  intro x hx y hy
  by_contra hcon
  push Not at hcon
  obtain ⟨hx1, hy1, hxy⟩ := hcon
  have hxs := tabE_hM_orth x hx1 (hidx x hx)
  have hys := tabE_hM_orth y hy1 (hidx y hy)
  by_cases hxy1 : x * y = 1
  · apply hxy
    obtain ⟨-, h2, -⟩ := (isSwap_iff y).mp hys
    have hyy : y * y = 1 := by rwa [← pow_two]
    calc x = x * (y * y) := by rw [hyy, mul_one]
      _ = (x * y) * y := by rw [mul_assoc]
      _ = y := by rw [hxy1, one_mul]
  · exact tabE_swap_mul_not_swap hxs hys hxy1
      (tabE_hM_orth (x * y) hxy1 (hidx _ (B.mul_mem hx hy)))

end Cases

section Vu

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem stab_of_Psi_mem {u μ : Geo H M} (V : VuModule u μ) (hQ : Qv u ≤ stab μ) {g : G}
    (hg : g ∈ stab u) (h : V.Ψ ⟨g, hg⟩ ∈ S5Syl) : g ∈ stab μ := by
  rw [← V.sylow] at h
  obtain ⟨d, hd, hdg⟩ := h
  have hker : V.Ψ (d⁻¹ * ⟨g, hg⟩) = 1 := by rw [map_mul, map_inv, hdg, inv_mul_cancel]
  have hq : ((d⁻¹ * ⟨g, hg⟩ : ↥(stab u)) : G) ∈ Qv u := (V.ker _).mp hker
  have hdμ : (d : G) ∈ stab μ := (Subgroup.mem_subgroupOf.mp hd).2
  have : g = (d : G) * ((d⁻¹ * ⟨g, hg⟩ : ↥(stab u)) : G) := by simp
  rw [this]
  exact (stab μ).mul_mem hdμ (hQ hq)

theorem D1_cases {u μ : Geo H M} (V : VuModule u μ) (hQ : Qv u ≤ stab μ)
    {Zs R : Subgroup G}
    (hAR : ∀ a ∈ Zs, ∀ x ∈ Zv u, a * x * a⁻¹ * x⁻¹ ∈ R)
    (hcases : (V.M5 = nat ∧ (Zs.subgroupOf (stab u)).map V.Ψ = S5T) ∨
      (V.M5 = orth ∧ ∃ t : Perm (Fin 5), t.IsSwap ∧ t ∈ S5Syl ∧
        (Zs.subgroupOf (stab u)).map V.Ψ = Subgroup.zpowers t) ∨
      (V.M5 = orth ∧ (Zs.subgroupOf (stab u)).map V.Ψ = S5That))
    {B : Subgroup G} (hBK : B ≤ stab u) (hB2 : IsPGroup 2 B)
    (hBR : ∀ g ∈ B, ∀ r ∈ R, g * r = r * g) :
    B ≤ stab μ ∨ (V.M5 = orth ∧
      ∀ x ∈ B, ∀ y ∈ B, x ∈ stab μ ∨ y ∈ stab μ ∨ x * y ∈ stab μ) := by
  have := V.norm
  have key : ∀ g (hg : g ∈ B), ∀ b ∈ (Zs.subgroupOf (stab u)).map V.Ψ, ∀ w : V.M5.W,
      V.M5.act (V.Ψ ⟨g, hBK hg⟩) (V.M5.act b w * w⁻¹) = V.M5.act b w * w⁻¹ :=
    fun g hg => pointwise_bridge V.secData hAR (hBK hg) (hBR g hg)
  rcases hcases with ⟨hM, hZ⟩ | ⟨hM, t, ht, htS, hZ⟩ | ⟨hM, hZ⟩
  · left
    intro g hg
    refine stab_of_Psi_mem V hQ (hBK hg) (stab_of_case_nat hM fun b hb w => ?_)
    exact key g hg b (hZ ▸ hb) w
  · right
    refine ⟨hM, fun x hx y hy => ?_⟩
    have hxy : x * y ∈ B := B.mul_mem hx hy
    have hmul : V.Ψ ⟨x * y, hBK hxy⟩ = V.Ψ ⟨x, hBK hx⟩ * V.Ψ ⟨y, hBK hy⟩ := by
      rw [← map_mul]; rfl
    have h8 := pow_eight_of_isPGroup hBK hB2 V.Ψ hxy
    rw [hmul] at h8
    have := three_of_case_t hM ht htS
      (fun w => key x hx t (hZ ▸ Subgroup.mem_zpowers t) w)
      (fun w => key y hy t (hZ ▸ Subgroup.mem_zpowers t) w)
      (pow_eight_of_isPGroup hBK hB2 V.Ψ hx) (pow_eight_of_isPGroup hBK hB2 V.Ψ hy) h8
    rcases this with h | h | h
    · exact Or.inl (stab_of_Psi_mem V hQ (hBK hx) h)
    · exact Or.inr (Or.inl (stab_of_Psi_mem V hQ (hBK hy) h))
    · exact Or.inr (Or.inr (stab_of_Psi_mem V hQ (hBK hxy) (by rw [hmul]; exact h)))
  · left
    intro g hg
    refine stab_of_Psi_mem V hQ (hBK hg) (stab_of_case_That hM fun b hb w => ?_)
    exact key g hg b (hZ ▸ hb) w

theorem D1_two_elements {u μ : Geo H M} (V : VuModule u μ) (hM : V.M5 = orth)
    (hLX : Nu u ≤ Zv u) {B : Subgroup G} (hBK : B ≤ stab u)
    (h : (fixSecIn B (Nu u) (Zv u)).relIndex (Zv u) ≤ 2) :
    ∀ x (hx : x ∈ B) y (hy : y ∈ B), V.Ψ ⟨x, hBK hx⟩ = 1 ∨ V.Ψ ⟨y, hBK hy⟩ = 1 ∨
      V.Ψ ⟨x, hBK hx⟩ = V.Ψ ⟨y, hBK hy⟩ := by
  have := V.norm
  have h1 := V.secData.relIndex_fixSecIn hLX hBK
  rw [h1] at h
  have h3 : (fixW orth ((B.subgroupOf (stab u)).map V.Ψ)).index ≤ 2 := by rw [← hM]; exact h
  intro x hx y hy
  exact two_elements_of_index_le_two h3 _ ⟨⟨x, hBK hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩ _
    ⟨⟨y, hBK hy⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩

end Vu

end F53.Stellmacher

end CFSG.Quasithin
