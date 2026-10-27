module

public import CFSG.RankThree.PartOne.SP4C.GAL
public import CFSG.RankThree.PartOne.NF7H.FieldSq
public import CFSG.RankThree.PartOne.KF.R7Final

public section

namespace CFSG.RankThree.PartOne.NF7H

open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.SP4C
  CFSG.LieType.Universal.Unitary Matrix
open CFSG.Assembly.LowTwoRank
open CFSG.QuasithinUnique.Lin2.Five (tauAut)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.RankThree.PartTwo.KFacts

section Torus

variable {p : ℕ} {K : Type} [Field K]

theorem d8Mod_pow_p (w : D8Mod p K) : w ^ p = 1 := by
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · have h := (mem_rootsOfUnity p _).1 w.1.2
    simpa using h
  · have h := (mem_rootsOfUnity p _).1 w.2.2
    simpa using h

theorem d8Mod_zpow_eq_of_dvd (w : D8Mod p K) {m n : ℤ} (h : (p : ℤ) ∣ n - m) : w ^ m = w ^ n := by
  obtain ⟨t, ht⟩ := h
  have hn : n = m + (p : ℤ) * t := by linarith
  have hwp : w ^ (p : ℤ) = 1 := by rw [zpow_natCast]; exact d8Mod_pow_p w
  rw [hn, _root_.zpow_add, _root_.zpow_mul, hwp, _root_.one_zpow, mul_one]

theorem d8Act_axis_pair (γ : DihedralGroup 4) (x : rootsOfUnity p K) :
    (d8Act γ (x, 1) = (x, 1) ∨ d8Act γ (x, 1) = (x⁻¹, 1)) ∨
      (d8Act γ (x, 1) = (1, x) ∨ d8Act γ (x, 1) = (1, x⁻¹)) := by
  rcases γ with i | i
  · have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by revert i; decide
    rcases hi with rfl | rfl | rfl | rfl
    · rw [d8Act_r_zero]; simp
    · rw [d8Act_r_one]; simp
    · rw [d8Act_r_two]; simp
    · rw [d8Act_r_three]; simp
  · have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by revert i; decide
    rcases hi with rfl | rfl | rfl | rfl
    · rw [d8Act_sr_zero]; simp
    · rw [d8Act_sr_one]; simp
    · rw [d8Act_sr_two]; simp
    · rw [d8Act_sr_three]; simp

theorem pow_sq_eq_of_d8Act_eq (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) {γ γ₁ : DihedralGroup 4}
    {k k₁ : ℤ} (h : ∀ w : D8Mod p K, d8Act γ (w ^ k) = d8Act γ₁ (w ^ k₁)) :
    ∀ w : D8Mod p K, w ^ (k * k) = w ^ (k₁ * k₁) := by
  obtain ⟨ζ, hζ⟩ := hζ
  let a : rootsOfUnity p K := ⟨ζ, (mem_rootsOfUnity p _).mpr hζ.pow_eq_one⟩
  have ha : ∀ n : ℤ, a ^ n = 1 ↔ (p : ℤ) ∣ n := by
    intro n
    rw [← hζ.zpow_eq_one_iff_dvd]
    constructor
    · intro h1
      have := congrArg Subtype.val h1
      simpa [a] using this
    · intro h1
      apply Subtype.ext
      simpa [a] using h1
  have hδ : ∀ w : D8Mod p K, d8Act (γ₁⁻¹ * γ) (w ^ k) = w ^ k₁ := by
    intro w
    rw [map_mul, MulAut.mul_apply, h w, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  have hak : ((a, 1) : D8Mod p K) ^ k = (a ^ k, 1) := Prod.ext (by simp) (by simp)
  have hak1 : ((a, 1) : D8Mod p K) ^ k₁ = (a ^ k₁, 1) := Prod.ext (by simp) (by simp)
  have hmain : (p : ℤ) ∣ k₁ * k₁ - k * k := by
    have h0 := hδ (a, 1)
    rw [hak, hak1] at h0
    rcases d8Act_axis_pair (γ₁⁻¹ * γ) (a ^ k) with (h1 | h1) | (h1 | h1)
    · rw [h1] at h0
      have h2 : a ^ k = a ^ k₁ := congrArg Prod.fst h0
      have h3 : a ^ (k₁ - k) = 1 := by rw [_root_.zpow_sub, ← h2, mul_inv_cancel]
      have h4 := (ha _).1 h3
      have : k₁ * k₁ - k * k = (k₁ - k) * (k₁ + k) := by ring
      rw [this]
      exact dvd_mul_of_dvd_left h4 _
    · rw [h1] at h0
      have h2 : (a ^ k)⁻¹ = a ^ k₁ := congrArg Prod.fst h0
      have h3 : a ^ (k₁ + k) = 1 := by rw [_root_.zpow_add, ← h2, inv_mul_cancel]
      have h4 := (ha _).1 h3
      have : k₁ * k₁ - k * k = (k₁ - k) * (k₁ + k) := by ring
      rw [this]
      exact dvd_mul_of_dvd_right h4 _
    · rw [h1] at h0
      have h2 : a ^ k₁ = 1 := (congrArg Prod.fst h0).symm
      have h2' : a ^ k = 1 := congrArg Prod.snd h0
      exact dvd_sub (dvd_mul_of_dvd_left ((ha _).1 h2) _) (dvd_mul_of_dvd_left ((ha _).1 h2') _)
    · rw [h1] at h0
      have h2 : a ^ k₁ = 1 := (congrArg Prod.fst h0).symm
      have h2' : (a ^ k)⁻¹ = 1 := congrArg Prod.snd h0
      have h2'' : a ^ k = 1 := inv_eq_one.1 h2'
      exact dvd_sub (dvd_mul_of_dvd_left ((ha _).1 h2) _) (dvd_mul_of_dvd_left ((ha _).1 h2'') _)
  intro w
  exact d8Mod_zpow_eq_of_dvd w hmain

end Torus

section Main

variable {G : Type} [Group G]

theorem row7_scalar_involution [Finite G] {p : ℕ} {L A₀ F : Subgroup G}
    (h : Table123Core p L A₀ F) (hmodel : RowModel p L 7) {v : G}
    (hvL : v ∈ Subgroup.normalizer (L : Set G)) (hvF : v ∈ Subgroup.normalizer (F : Set G))
    (hv2 : v * v = 1) {h' : G} (hh'L : h' ∈ L) (hh'F : h' ∈ Subgroup.normalizer (F : Set G))
    {k : ℤ} (hk : ∀ f ∈ F, v * f * v⁻¹ = h' * f ^ k * h'⁻¹) :
    ∀ f ∈ F, f ^ (k * k) = f := by
  classical
  obtain ⟨f, K, hKf, hKfin, hf1, hpq, hK, hζ, hchar, ε, hε, hFT₁, hFT₂⟩ :=
    exists_r7frame h hmodel
  have hp := h.prime
  have hp2 : p ≠ 2 := by have := h.five_le; omega
  have : Fact p.Prime := ⟨hp⟩
  have hFL : F ≤ L := h.F_le
  let T : TFrame p L F K := ⟨hFL, ε, hε, hFT₁, hFT₂, h.F_exp⟩
  let c : MulAut ↥L := L.normalizerMonoidHom ⟨v, hvL⟩
  obtain ⟨α, hα⟩ := exists_induced_aut hε c
  have hT : ∀ t ∈ Tsub p K, toRev α t ∈ Tsub p K := by
    intro t ht
    obtain ⟨f₀, hf₀⟩ := T.h₁ t ht
    have hmem : v * f₀ * v⁻¹ ∈ F := (Subgroup.mem_normalizer_iff.1 hvF f₀).1 f₀.2
    obtain ⟨t', ht', hf'⟩ := T.h₂ ⟨v * f₀ * v⁻¹, hmem⟩
    have hc : c (Subgroup.inclusion hFL f₀) =
        Subgroup.inclusion hFL ⟨v * f₀ * v⁻¹, hmem⟩ := Subtype.ext rfl
    have : toRev α t = t' := by
      apply (spQe K).injective
      rw [spQe_toRev, ← hf₀, hα, hc, hf']
    rw [this]
    exact ht'
  have htor : ∃ γ : DihedralGroup 4, ∀ w : D8Mod p K,
      toRev α (torC p K w) = torC p K (d8Act γ (w ^ k)) := by
    set u : ↥L := ⟨h', hh'L⟩ with hu
    set m : ↥(spRev K) := (spQe K).symm (ε u) with hm
    have hεu : ε u = spQe K m := by rw [hm, MulEquiv.apply_symm_apply]
    have hnorm : m ∈ Subgroup.normalizer (Tsub p K : Set ↥(spRev K)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro t
      constructor
      · intro ht
        exact T.conj_mem (u := u) hh'F t ht
      · intro ht
        have hinvF : ((u⁻¹ : ↥L) : G) ∈ Subgroup.normalizer (F : Set G) :=
          (Subgroup.normalizer (F : Set G)).inv_mem hh'F
        have := T.conj_mem (u := u⁻¹) hinvF (m * t * m⁻¹) ht
        have hmi : (spQe K).symm (ε u⁻¹) = m⁻¹ := by rw [map_inv, map_inv]
        rw [hmi] at this
        simpa [mul_assoc] using this
    obtain ⟨γ, hγ⟩ := exists_weyl hp hp2 hζ hnorm
    refine ⟨γ, fun w => ?_⟩
    obtain ⟨f₀, hf₀⟩ := T.h₁ (torC p K w) (torC_mem w)
    have h1 : c (Subgroup.inclusion hFL f₀) = u * Subgroup.inclusion hFL f₀ ^ k * u⁻¹ := by
      apply Subtype.ext
      show v * (f₀ : G) * v⁻¹ = ((u * Subgroup.inclusion hFL f₀ ^ k * u⁻¹ : ↥L) : G)
      simp only [Subgroup.coe_mul, Subgroup.coe_zpow, Subgroup.coe_inv, Subgroup.coe_inclusion, hu]
      exact hk f₀ f₀.2
    apply (spQe K).injective
    rw [spQe_toRev, ← hf₀, hα, h1, map_mul, map_mul, map_inv, map_zpow, hf₀, hεu, ← hγ (w ^ k),
      map_mul, map_mul, map_inv, map_zpow, map_zpow]
  have hcc : c * c = 1 := by
    have h1 : (⟨v, hvL⟩ : ↥(Subgroup.normalizer (L : Set G))) * ⟨v, hvL⟩ = 1 :=
      Subtype.ext (by simpa using hv2)
    show L.normalizerMonoidHom ⟨v, hvL⟩ * L.normalizerMonoidHom ⟨v, hvL⟩ = 1
    rw [← map_mul, h1, map_one]
  have hα2 : α * α = 1 := by
    ext q
    obtain ⟨x, rfl⟩ := hε.surjective q
    have hcx : c (c x) = x := by
      have := congrArg (fun φ : MulAut ↥L => φ x) hcc
      simpa using this
    simp only [MulAut.mul_apply, MulAut.one_apply, hα, hcx]
  obtain ⟨γ0, hγ0⟩ := htor
  obtain ⟨A, σ, hα'⟩ := (ga_core hp hp2 hζ α hT).1 ⟨γ0, k, hγ0⟩
  have hσ : σ * σ = 1 := sq_eq_one_of_conj_mul_field hα' hα2
  obtain ⟨x, hx⟩ := conjAut_mem_inner_of_charTwo A
  obtain ⟨m, rfl⟩ := (spQe K).surjective x
  have hconj : ∀ t : ↥(spRev K), conjAut 2 K A (spQe K t) = spQe K (m * t * m⁻¹) := by
    intro t
    rw [← hx]
    exact conj_spQe m t
  have hθ : ∀ t : ↥(spRev K), toRev α t = m * fieldRev σ t * m⁻¹ := by
    intro t
    apply (spQe K).injective
    rw [spQe_toRev, hα']
    simp only [MulAut.mul_apply]
    rw [← spQe_fieldRev, hconj]
  have hmemT : ∀ t ∈ Tsub p K, ∃ w : D8Mod p K, t = torC p K w := fun t ht =>
    exists_torC_of_mem t ht
  have hnormm : m ∈ Subgroup.normalizer (Tsub p K : Set ↥(spRev K)) := by
    refine mem_normalizer_of (fieldRev σ) (fun t ht => ?_) (fun t ht => ?_)
    · obtain ⟨w, rfl⟩ := hmemT t ht
      rw [fieldRev_torC]
      exact torC_mem _
    · rw [← hθ]
      exact hT t ht
  obtain ⟨γ₁, hγ₁⟩ := exists_weyl hp hp2 hζ hnormm
  obtain ⟨kσ, hkσ⟩ := sigVec_pow (K := K) (p := p) σ
  have hrev : ∀ w : D8Mod p K,
      toRev α (torC p K w) = torC p K (d8Act γ₁ (w ^ kσ)) := by
    intro w
    rw [hθ, fieldRev_torC, hγ₁, hkσ]
  have hEq : ∀ w : D8Mod p K, d8Act γ0 (w ^ k) = d8Act γ₁ (w ^ kσ) := fun w =>
    torC_injective ((hγ0 w).symm.trans (hrev w))
  have hkk : ∀ w : D8Mod p K, w ^ (k * k) = w := fun w =>
    (pow_sq_eq_of_d8Act_eq hζ hEq w).trans (pow_sq_of_sq_eq_one hσ hkσ w)
  intro f₀ hf₀
  obtain ⟨t, ht, hft⟩ := T.h₂ ⟨f₀, hf₀⟩
  obtain ⟨w, rfl⟩ := hmemT t ht
  set a : ↥L := Subgroup.inclusion hFL ⟨f₀, hf₀⟩ with ha
  have hap : a ^ p = 1 := Subtype.ext (h.F_exp f₀ hf₀)
  have hakp : (a ^ (k * k)) ^ p = 1 := by
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hap,
      _root_.one_zpow]
  have key : a = a ^ (k * k) := by
    apply hε.eq_of_map_eq hap hakp
    rw [map_zpow, hft, ← map_zpow, ← map_zpow, hkk w]
  have := congrArg (fun y : ↥L => (y : G)) key
  simpa [ha] using this.symm

end Main

end CFSG.RankThree.PartOne.NF7H
