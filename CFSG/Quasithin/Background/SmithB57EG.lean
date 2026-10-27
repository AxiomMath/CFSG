module

public import CFSG.Quasithin.Background.SmithB57EF

public section

namespace CFSG.Quasithin

namespace SmithB57E

open CFSG.Open CFSG.QuasithinUnique FFC CFSG.Quasithin.S143 Equiv
open scoped commutatorElement

section Arith

theorem arith_offender {a f c y y₀ w w₀ u₀ s : ℕ} (hc : 0 < c) (hy₀ : 0 < y₀) (hw₀ : 0 < w₀)
    (hu₀ : 0 < u₀) (hs : 0 < s) (h1 : y * w ≤ a * (y₀ * w₀)) (h2 : 2 * y₀ ≤ y)
    (h3 : s * u₀ = 16 * c * w₀) (h4 : s ≤ w) (h5 : u₀ ≤ c * f) (h6 : a * f ≤ 32) :
    a * f = 32 ∧ y = 2 * y₀ ∧ s = w ∧ u₀ = c * f := by
  have hP : 0 < c * y₀ * w₀ := by positivity
  have e1 : 32 * (c * y₀ * w₀) ≤ y * w * u₀ :=
    calc 32 * (c * y₀ * w₀) = (2 * y₀) * (s * u₀) := by rw [h3]; ring
      _ ≤ y * (w * u₀) := Nat.mul_le_mul h2 (Nat.mul_le_mul_right _ h4)
      _ = y * w * u₀ := by ring
  have e2 : y * w * u₀ ≤ a * (y₀ * w₀) * u₀ := Nat.mul_le_mul_right _ h1
  have e3 : a * (y₀ * w₀) * u₀ ≤ a * (y₀ * w₀) * (c * f) := Nat.mul_le_mul_left _ h5
  have e4 : a * (y₀ * w₀) * (c * f) = (a * f) * (c * y₀ * w₀) := by ring
  have haf : a * f = 32 := by
    refine le_antisymm h6 (Nat.le_of_mul_le_mul_right ?_ hP)
    calc 32 * (c * y₀ * w₀) ≤ a * (y₀ * w₀) * (c * f) := e1.trans (e2.trans e3)
      _ = (a * f) * (c * y₀ * w₀) := e4
  have ha : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · rw [h, zero_mul] at haf
      exact absurd haf (by norm_num)
    · exact h
  have hu : u₀ = c * f := by
    refine le_antisymm h5 (Nat.le_of_mul_le_mul_left ?_ (by positivity : 0 < a * (y₀ * w₀)))
    calc a * (y₀ * w₀) * (c * f) = 32 * (c * y₀ * w₀) := by rw [e4, haf]
      _ ≤ a * (y₀ * w₀) * u₀ := e1.trans e2
  have e5 : 2 * y₀ * s * u₀ = 32 * (c * y₀ * w₀) := by rw [mul_assoc (2 * y₀), h3]; ring
  have hyw : y * w = 2 * y₀ * s := by
    refine Nat.eq_of_mul_eq_mul_right hu₀ (le_antisymm ?_ ?_)
    · calc y * w * u₀ ≤ a * (y₀ * w₀) * (c * f) := e2.trans e3
        _ = 32 * (c * y₀ * w₀) := by rw [e4, haf]
        _ = 2 * y₀ * s * u₀ := e5.symm
    · rw [e5]
      exact e1
  have hy : y = 2 * y₀ := by
    refine le_antisymm ?_ h2
    by_contra hlt
    have hlt' : 2 * y₀ < y := lt_of_not_ge hlt
    have : 2 * y₀ * s < y * w :=
      calc 2 * y₀ * s < y * s := Nat.mul_lt_mul_of_pos_right hlt' hs
        _ ≤ y * w := Nat.mul_le_mul_left _ h4
    omega
  refine ⟨haf, hy, ?_, hu⟩
  rw [hy] at hyw
  exact (Nat.eq_of_mul_eq_mul_left (by positivity) hyw).symm

end Arith

variable {V : Type} [CommGroup V] [Finite V]

section Counting

theorem two_mul_card_le {K Y : Subgroup V} (hKY : K ≤ Y) (hne : ¬ Y ≤ K) :
    2 * Nat.card K ≤ Nat.card Y := by
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hKY
  have hk1 : k ≠ 1 := by
    rintro rfl
    rw [mul_one] at hk
    exact hne (Subgroup.eq_of_le_of_card_ge hKY hk.le).ge
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hk
    exact absurd hk (Nat.card_pos (α := Y)).ne'
  rw [hk, mul_comm 2]
  exact Nat.mul_le_mul_left _ (by omega)

theorem mem_or_mul_mem_of_card (hV : ∀ v : V, v ^ 2 = 1) {K Y : Subgroup V} (hKY : K ≤ Y)
    (hcard : Nat.card Y ≤ 2 * Nat.card K) {z : V} (hz : z ∈ Y) (hzK : z ∉ K) {y : V}
    (hy : y ∈ Y) : y ∈ K ∨ y * z ∈ K := by
  have hle : K ⊔ Subgroup.zpowers z ≤ Y := sup_le hKY (Subgroup.zpowers_le.2 hz)
  have hne : ¬ K ⊔ Subgroup.zpowers z ≤ K := fun h =>
    hzK (h (Subgroup.mem_sup_right (Subgroup.mem_zpowers z)))
  have h2 := two_mul_card_le (le_sup_left : K ≤ K ⊔ Subgroup.zpowers z) hne
  have heq : K ⊔ Subgroup.zpowers z = Y :=
    Subgroup.eq_of_le_of_card_ge hle (hcard.trans h2)
  rw [← heq] at hy
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 hy
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
  have hz2 : z ^ (2 : ℤ) = 1 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast]
    exact hV z
  rcases Int.even_or_odd' n with ⟨m, rfl | rfl⟩
  · left
    rw [zpow_mul, hz2, one_zpow, mul_one]
    exact ha
  · right
    rw [zpow_add, zpow_mul, hz2, one_zpow, one_mul, zpow_one, mul_assoc, ← sq, hV, mul_one]
    exact ha

theorem eq_of_card_le_two {H : Subgroup V} (h : Nat.card H ≤ 2) {a b : V} (ha : a ∈ H)
    (hb : b ∈ H) (ha1 : a ≠ 1) (hb1 : b ≠ 1) : a = b := by
  classical
  by_contra hab
  have := Fintype.ofFinite H
  have h3 : ({1, ⟨a, ha⟩, ⟨b, hb⟩} : Finset H).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair]
    · intro h
      exact hab (congrArg Subtype.val h)
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => ha1 (congrArg Subtype.val h).symm,
        fun h => hb1 (congrArg Subtype.val h).symm⟩
  have : 3 ≤ Nat.card H := by
    rw [← h3, Nat.card_eq_fintype_card]
    exact Finset.card_le_univ _
  omega

omit [Finite V] in
theorem comm_mul (g : MulAut V) (y y' : V) :
    g (y * y') * (y * y')⁻¹ = (g y * y⁻¹) * (g y' * y'⁻¹) := by
  rw [map_mul, mul_inv_rev, mul_comm y'⁻¹, mul_mul_mul_comm]

omit [Finite V] in
theorem eq_of_fix_q (hV : ∀ v : V, v ^ 2 = 1) {c : MulAut V} (hc3 : c ^ 3 = 1) {y : V}
    (h : c (c⁻¹ y * (c y)⁻¹) = c⁻¹ y * (c y)⁻¹) : c y = y := by
  have hinv : ∀ v : V, v⁻¹ = v := fun v =>
    inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hV v)
  have hc2 : c⁻¹ y = c (c y) := by
    have : c⁻¹ = c * c := inv_eq_of_mul_eq_one_right (by rw [← pow_three]; exact hc3)
    rw [this, MulAut.mul_apply]
  rw [map_mul, map_inv, MulAut.apply_inv_self, hc2, hinv, hinv, mul_comm (c (c y))] at h
  exact (mul_right_cancel h).symm

end Counting

section Invariance

variable (G : Subgroup (MulAut V))

omit [Finite V] in
theorem commV_X_invariant {g : MulAut V} (hg : g ∈ G) {v : V}
    (hv : v ∈ commV (pCoreOf 3 G)) : g v ∈ commV (pCoreOf 3 G) :=
  FFC.commV_invariant (fun x hx => (Subgroup.mem_normalizer_iff.1
    ((le_normalizer_pCore3 G) hg) x).1 hx) hv

omit [Finite V] in
theorem fixV_X_invariant {g : MulAut V} (hg : g ∈ G) {v : V}
    (hv : v ∈ fixV (pCoreOf 3 G)) : g v ∈ fixV (pCoreOf 3 G) := by
  refine FFC.fixV_invariant (fun x hx => ?_) hv
  have h := (Subgroup.mem_normalizer_iff.1 ((le_normalizer_pCore3 G) (G.inv_mem hg)) x).1 hx
  rwa [inv_inv] at h

end Invariance

namespace SixData

variable {G L A : Subgroup (MulAut V)} {S : Hyp G L} (D : SixData S A)
include D

noncomputable def theta : ↥(commV L) →* N6 := Classical.choose D.exists_theta

theorem theta_eq_one_iff (u : ↥(commV L)) : D.theta u = 1 ↔ (u : V) ∈ fixV L ⊓ commV L :=
  (Classical.choose_spec D.exists_theta).2.1 u

theorem theta_equiv (σ : Perm (Fin 6)) (u : ↥(commV L)) (hu : D.f σ u ∈ commV L) :
    D.theta ⟨D.f σ u, hu⟩ = n6Act σ (D.theta u) :=
  (Classical.choose_spec D.exists_theta).2.2 σ u hu

def abar : Subgroup (Perm (Fin 6)) where
  carrier := {σ | D.f σ ∈ A}
  mul_mem' {σ τ} hσ hτ := by
    show D.f (σ * τ) ∈ A
    rw [D.f_mul]
    exact A.mul_mem hσ hτ
  one_mem' := by
    show D.f 1 ∈ A
    rw [D.f_one]
    exact A.one_mem
  inv_mem' {σ} hσ := by
    show D.f σ⁻¹ ∈ A
    rw [D.f_inv]
    exact A.inv_mem hσ

theorem mem_abar {σ : Perm (Fin 6)} : σ ∈ D.abar ↔ D.f σ ∈ A := Iff.rfl

theorem abar_sq : ∀ σ ∈ D.abar, σ * σ = 1 := by
  intro σ hσ
  apply D.f_injective
  rw [D.f_mul, D.f_one]
  simpa [sq] using D.hA.2.2.1.2 _ ((D.mem_abar).1 hσ)

theorem abar_comm : ∀ σ ∈ D.abar, ∀ τ ∈ D.abar, σ * τ = τ * σ := by
  intro σ hσ τ hτ
  apply D.f_injective
  rw [D.f_mul, D.f_mul]
  exact D.hA.2.2.1.1 _ ((D.mem_abar).1 hσ) _ ((D.mem_abar).1 hτ)

theorem card_abar : Nat.card D.abar = Nat.card A := by
  refine Nat.card_congr (Equiv.ofBijective (fun σ => ⟨D.f σ, σ.2⟩) ⟨?_, ?_⟩)
  · intro σ τ h
    have h' := congrArg Subtype.val h
    exact Subtype.ext (D.f_injective h')
  · intro a
    obtain ⟨σ, hσ⟩ := D.f_surj ((le_sup_right : A ≤ L ⊔ A) a.2)
    refine ⟨⟨σ, ?_⟩, Subtype.ext hσ⟩
    rw [D.mem_abar, hσ]
    exact a.2

theorem theta_mem_fixN6 (u : ↥(commV L)) (hu : (u : V) ∈ fixV A) :
    D.theta u ∈ fixN6 D.abar := by
  rw [mem_fixN6]
  intro σ hσ
  have hfu : D.f σ u = u := hu _ ((D.mem_abar).1 hσ)
  have hmem : D.f σ u ∈ commV L := by rw [hfu]; exact u.2
  calc n6Act σ (D.theta u) = D.theta ⟨D.f σ u, hmem⟩ := (D.theta_equiv σ u hmem).symm
    _ = D.theta u := by congr 1; exact Subtype.ext hfu

theorem card_UA :
    Nat.card ↥(commV L ⊓ fixV A) ≤ Nat.card ↥(fixV L ⊓ commV L) * Nat.card ↥(fixN6 D.abar) ∧
    (Nat.card ↥(commV L ⊓ fixV A) = Nat.card ↥(fixV L ⊓ commV L) * Nat.card ↥(fixN6 D.abar) →
      ∀ a ∈ fixN6 D.abar, ∃ u : ↥(commV L), (u : V) ∈ fixV A ∧ D.theta u = a) := by
  set Θ' : ↥(commV L ⊓ fixV A) →* N6 :=
    D.theta.comp (Subgroup.inclusion (inf_le_left : commV L ⊓ fixV A ≤ commV L)) with hΘ'
  have hrange : Θ'.range ≤ fixN6 D.abar := by
    rintro _ ⟨x, rfl⟩
    exact D.theta_mem_fixN6 _ x.2.2
  have hker : Nat.card Θ'.ker ≤ Nat.card ↥(fixV L ⊓ commV L) := by
    refine Nat.card_le_card_of_injective
      (fun x => ⟨((x : ↥(commV L ⊓ fixV A)) : V), ?_⟩) ?_
    · exact (D.theta_eq_one_iff _).1 ((MonoidHom.mem_ker).1 x.2)
    · intro x y h
      have h' := congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext h')
  have hmul := Subgroup.card_ker_mul_card_range Θ'
  have hr := Subgroup.card_le_of_le hrange
  constructor
  · rw [← hmul]
    exact Nat.mul_le_mul hker hr
  · intro heq a ha
    have hcpos : 0 < Nat.card ↥(fixV L ⊓ commV L) := Nat.card_pos
    have hr' : Nat.card ↥(fixN6 D.abar) ≤ Nat.card Θ'.range := by
      by_contra hlt
      have hlt' : Nat.card Θ'.range < Nat.card ↥(fixN6 D.abar) := lt_of_not_ge hlt
      have : Nat.card Θ'.ker * Nat.card Θ'.range <
          Nat.card ↥(fixV L ⊓ commV L) * Nat.card ↥(fixN6 D.abar) :=
        calc _ ≤ Nat.card ↥(fixV L ⊓ commV L) * Nat.card Θ'.range :=
              Nat.mul_le_mul_right _ hker
          _ < _ := Nat.mul_lt_mul_of_pos_left hlt' hcpos
      omega
    have heqr := Subgroup.eq_of_le_of_card_ge hrange hr'
    have ha' : a ∈ Θ'.range := by rw [heqr]; exact ha
    obtain ⟨x, rfl⟩ := ha'
    exact ⟨⟨x, x.2.1⟩, x.2.2, rfl⟩

theorem card_U : Nat.card ↥(commV L) = 16 * Nat.card ↥(fixV L ⊓ commV L) := by
  have h6 : Nat.card (FFModel.symDn 6).Mod = 16 := by
    have := G64.card_symDn_mod (n := 6) (by norm_num)
    rw [ite_eq_left_iff.mpr (fun h => absurd (by decide) h)] at this
    simpa using this
  rw [G64.RealizesVia.card_eq D.real, h6]

theorem not_fix_Y : ¬ commV (pCoreOf 3 G) ≤ fixV A := by
  intro h
  apply D.hAX
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact (S.commute_X_of_trivial_commV (D.hA.1 ha) (fun y hy => h hy a ha) x hx).symm

theorem offender_eq : Nat.card A = 8 ∧ Nat.card ↥(fixN6 D.abar) = 4 ∧
    Nat.card ↥(commV (pCoreOf 3 G)) = 2 * Nat.card ↥(commV (pCoreOf 3 G) ⊓ fixV A) ∧
    commV L ⊔ (fixV (pCoreOf 3 G) ⊓ fixV A) = fixV (pCoreOf 3 G) ∧
    ∀ a ∈ fixN6 D.abar, ∃ u : ↥(commV L), (u : V) ∈ fixV A ∧ D.theta u = a := by
  set X := pCoreOf 3 G with hX
  set Y := commV X with hY
  set W := fixV X with hW
  obtain ⟨hsup, hinf⟩ := isDirectSum_commV_fixV S.hV G
  have hVc : Nat.card V = Nat.card Y * Nat.card W := by
    have h := card_sup_mul_card_inf Y W
    rw [hsup, hinf, Subgroup.card_top, Subgroup.card_bot, mul_one] at h
    exact h
  have hFc : Nat.card (fixV A) = Nat.card ↥(Y ⊓ fixV A) * Nat.card ↥(W ⊓ fixV A) :=
    card_fixV_of_decomp hsup hinf (fun b hb v hv => commV_X_invariant G (D.hA.1 hb) hv)
      (fun b hb v hv => fixV_X_invariant G (D.hA.1 hb) hv)
  have hoff := SmithB57.card_le_of_offender D.hA
  have hY2 : 2 * Nat.card ↥(Y ⊓ fixV A) ≤ Nat.card Y :=
    two_mul_card_le inf_le_left fun h => D.not_fix_Y (h.trans inf_le_right)
  have hUW : commV L ≤ W := D.U_le_W
  have hinfU : commV L ⊓ (W ⊓ fixV A) = commV L ⊓ fixV A := by
    rw [← inf_assoc, inf_eq_left.2 hUW]
  have h3 := card_sup_mul_card_inf (commV L) (W ⊓ fixV A)
  rw [hinfU, D.card_U] at h3
  have hsW : commV L ⊔ (W ⊓ fixV A) ≤ W := sup_le hUW inf_le_left
  have h4 := Subgroup.card_le_of_le hsW
  obtain ⟨h5, h5eq⟩ := D.card_UA
  have h6 := (card_mul_fixN6_le D.abar_sq).1
  rw [D.card_abar] at h6
  obtain ⟨haf, hy, hs, hu⟩ := arith_offender (a := Nat.card A) (f := Nat.card ↥(fixN6 D.abar))
    (c := Nat.card ↥(fixV L ⊓ commV L)) (y := Nat.card Y) (y₀ := Nat.card ↥(Y ⊓ fixV A))
    (w := Nat.card W) (w₀ := Nat.card ↥(W ⊓ fixV A)) (u₀ := Nat.card ↥(commV L ⊓ fixV A))
    (s := Nat.card ↥(commV L ⊔ (W ⊓ fixV A))) Nat.card_pos Nat.card_pos Nat.card_pos
    Nat.card_pos Nat.card_pos (by rw [← hVc, ← hFc]; exact hoff) hY2 h3 h4 h5 h6
  have h8 := (card_mul_fixN6_le D.abar_sq).2 (by rw [D.card_abar]; exact haf)
  rw [D.card_abar] at h8
  exact ⟨h8.1, h8.2, hy, Subgroup.eq_of_le_of_card_ge hsW hs.ge, h5eq hu⟩

theorem card_Y : Nat.card ↥(commV (pCoreOf 3 G)) = 4 := by
  obtain ⟨-, -, hYA, -, -⟩ := D.offender_eq
  obtain ⟨t, htA, htX⟩ := D.exists_t
  set X := pCoreOf 3 G with hX
  set Y := commV X with hY
  have hV := S.hV
  have htt : t * t = 1 := D.t_sq htA
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have htG : t ∈ G := D.hA.1 htA
  obtain ⟨-, hinf⟩ := isDirectSum_commV_fixV hV G
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hXne : X ≠ ⊥ := by
    intro h
    apply S.hO3
    rw [hX] at h
    rw [h]
    exact bot_le
  obtain ⟨k, hk⟩ := (pCore3_isPGroup G).exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, Subgroup.card_eq_one] at hk
    exact hXne hk
  obtain ⟨x₀, hx₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) 3
    (by rw [hk]; exact dvd_pow_self 3 hk0)
  set c : MulAut V := ((x₀ : ↥X) : MulAut V) with hc
  have hcX : c ∈ X := x₀.2
  have hcG : c ∈ G := pCore3_le G hcX
  have hord : orderOf c = 3 := by rw [hc, Subgroup.orderOf_coe]; exact hx₀
  have hc3 : c ^ 3 = 1 := by rw [← hord]; exact pow_orderOf_eq_one c
  have htc : t * c = c⁻¹ * t := by
    have h := D.conj_inv htA htX c hcX
    calc t * c = t * c * t⁻¹ * t := by group
      _ = c⁻¹ * t := by rw [h]
  have htc' : t * c⁻¹ = c * t := by
    have h := D.conj_inv htA htX c⁻¹ (X.inv_mem hcX)
    rw [inv_inv] at h
    calc t * c⁻¹ = t * c⁻¹ * t⁻¹ * t := by group
      _ = c * t := by rw [h]
  have hYG : ∀ g ∈ G, ∀ y ∈ Y, g y ∈ Y := fun g hg y hy => commV_X_invariant G hg hy
  set K := Y ⊓ fixV (Subgroup.zpowers t) with hK
  have hKY : K ≤ Y := inf_le_left
  have hcardK : Nat.card Y = 2 * Nat.card K := by
    have hle : Y ⊓ fixV A ≤ K :=
      inf_le_inf_left _ (B1.fixV_le_fixV (Subgroup.zpowers_le.2 htA))
    have h1 := Subgroup.card_le_of_le hle
    have h2 : 2 * Nat.card K ≤ Nat.card Y := by
      refine two_mul_card_le hKY fun h => htX ?_
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (S.commute_X_of_trivial_commV htG
        (fun y hy => mem_fixV_zpowers_iff.1 (h hy).2) x hx).symm
    omega
  have hc1 : c ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hord
    norm_num at hord
  have htY0 : ∀ z ∈ Y, c z = z → t z = z := by
    intro z hzY hcz
    by_contra htz
    have hzK : z ∉ K := fun h => htz (mem_fixV_zpowers_iff.1 h.2)
    have hcinv : c⁻¹ z = z := by
      conv_lhs => rw [← hcz]
      exact MulAut.inv_apply_self _ c z
    have hctz : c (t z) = t z := by
      rw [← MulAut.mul_apply, ← htc', MulAut.mul_apply, hcinv]
    have hpz : c (t z * z⁻¹) = t z * z⁻¹ := by rw [map_mul, map_inv, hctz, hcz]
    have hp : ∀ y ∈ Y, c (t y * y⁻¹) = t y * y⁻¹ := by
      intro y hy
      rcases mem_or_mul_mem_of_card hV hKY hcardK.le hzY hzK hy with h | h
      · rw [mem_fixV_zpowers_iff.1 h.2, mul_inv_cancel, map_one]
      · have h1 : t (y * z) * (y * z)⁻¹ = 1 := by
          rw [mem_fixV_zpowers_iff.1 h.2, mul_inv_cancel]
        rw [comm_mul] at h1
        rw [eq_inv_of_mul_eq_one_left h1, map_inv, hpz]
    have hcY : ∀ y ∈ Y, c y = y := by
      intro y hy
      have hcy : c y ∈ Y := hYG c hcG y hy
      refine eq_of_fix_q hV hc3 ?_
      have h1 : c⁻¹ (t y * y⁻¹) = t y * y⁻¹ := by
        conv_lhs => rw [← hp y hy]
        exact MulAut.inv_apply_self _ c _
      have h2 : t (c y) = (t y * y⁻¹) * c⁻¹ y := by
        calc t (c y) = c⁻¹ (t y) := by rw [← MulAut.mul_apply, htc, MulAut.mul_apply]
          _ = c⁻¹ (t y * y⁻¹ * y) := by rw [inv_mul_cancel_right]
          _ = (t y * y⁻¹) * c⁻¹ y := by rw [map_mul, h1]
      have h3 := hp (c y) hcy
      rw [h2, mul_assoc, map_mul, hp y hy] at h3
      exact mul_left_cancel h3
    exact hc1 (S.eq_one_of_trivial_commV hcX hcY)
  have hY0 : ∀ z ∈ Y, c z = z → z = 1 := by
    intro z hzY hcz
    have hzW : z ∈ fixV X := by
      intro x hx
      have hxz : x z ∈ Y := hYG x (pCore3_le G hx) z hzY
      have hcxz : c (x z) = x z := by
        rw [← MulAut.mul_apply, ← D.commute_X htA htX x hx c hcX, MulAut.mul_apply, hcz]
      have h1 : t (x z) = x z := htY0 _ hxz hcxz
      have h2 : t (x z) = x⁻¹ z := by
        have hxt : t * x = x⁻¹ * t := by
          have h := D.conj_inv htA htX x hx
          calc t * x = t * x * t⁻¹ * t := by group
            _ = x⁻¹ * t := by rw [h]
        rw [← MulAut.mul_apply, hxt, MulAut.mul_apply, htY0 z hzY hcz]
      have e : x z = x⁻¹ z := h1.symm.trans h2
      have h3 : (x * x) z = z := by
        rw [MulAut.mul_apply, e, MulAut.apply_inv_self]
      have hodd : Odd (orderOf x) := by
        obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.1 (pCore3_isPGroup G)) ⟨x, hx⟩
        rw [Subgroup.orderOf_mk] at hn
        rw [hn]
        exact Odd.pow (by decide)
      obtain ⟨m, hm⟩ := hodd
      have hx1 : x ^ (2 * m + 1) = 1 := by rw [← hm]; exact pow_orderOf_eq_one x
      have hxe : x = (x * x) ^ (m + 1) := by
        rw [← sq, ← pow_mul, show 2 * (m + 1) = 2 * m + 1 + 1 by ring, pow_succ, hx1, one_mul]
      have hfix : z ∈ fixV (Subgroup.zpowers (x * x)) := mem_fixV_zpowers_iff.2 h3
      rw [hxe]
      exact hfix _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _)
    have : z ∈ Y ⊓ fixV X := ⟨hzY, hzW⟩
    rw [hinf, Subgroup.mem_bot] at this
    exact this
  have hKK : Nat.card K * Nat.card K ≤ Nat.card Y := by
    rw [← Nat.card_prod]
    refine Nat.card_le_card_of_injective (fun p : K × K => (⟨(p.1 : V) * c p.2,
      Y.mul_mem (hKY p.1.2) (hYG c hcG _ (hKY p.2.2))⟩ : Y)) ?_
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have h' : (a : V) * c b = a' * c b' := congrArg Subtype.val h
    set w := (a : V)⁻¹ * a' with hw
    have hwK : w ∈ K := K.mul_mem (K.inv_mem a.2) a'.2
    have hwc : w = c ((b : V) * (b' : V)⁻¹) := by
      rw [map_mul, map_inv, hw, eq_mul_inv_iff_mul_eq, mul_assoc, inv_mul_eq_iff_eq_mul]
      exact h'.symm
    have hcw : c⁻¹ w ∈ K := by
      rw [hwc, MulAut.inv_apply_self]
      exact K.mul_mem b.2 (K.inv_mem b'.2)
    have h1 : t w = w := mem_fixV_zpowers_iff.1 hwK.2
    have h2 : t (c⁻¹ w) = c⁻¹ w := mem_fixV_zpowers_iff.1 hcw.2
    have e : c w = c⁻¹ w :=
      calc c w = c (t w) := by rw [h1]
        _ = (t * c⁻¹) w := by rw [htc']; rfl
        _ = c⁻¹ w := h2
    have h3 : c w = w := by
      have e2 : c (c w) = w := by rw [e, MulAut.apply_inv_self]
      have hc3' : c (c (c w)) = w := by
        have : (c ^ 3) w = w := by rw [hc3]; rfl
        rwa [pow_three, MulAut.mul_apply, MulAut.mul_apply] at this
      rw [e2] at hc3'
      exact hc3'
    have hw1 : w = 1 := hY0 w (hKY hwK) h3
    have haa : a = a' := by
      apply Subtype.ext
      rw [hw, inv_mul_eq_one] at hw1
      exact hw1
    subst haa
    have hbb : c b = c b' := mul_left_cancel h'
    exact Prod.ext rfl (Subtype.ext (c.injective hbb))
  have hKpos : 0 < Nat.card K := Nat.card_pos
  have hK2 : Nat.card K ≤ 2 := by
    have h := hKK
    rw [hcardK] at h
    exact Nat.le_of_mul_le_mul_right h hKpos
  have hK1 : Nat.card K ≠ 1 := by
    intro h1
    have hYc : Nat.card Y = 2 := by rw [hcardK, h1]
    have hYne : Y ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hYc
      norm_num at hYc
    obtain ⟨⟨y, hy⟩, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hYne
    have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
    have hcy1 : c y ≠ 1 := fun h => hy1' (c.injective (h.trans (map_one c).symm))
    have := eq_of_card_le_two hYc.le (hYG c hcG y hy) hy hcy1 hy1'
    exact hy1' (hY0 y hy this)
  omega

theorem card_X : Nat.card ↥(pCoreOf 3 G) = 3 := by
  have hU : ∀ x ∈ pCoreOf 3 G, ∀ y ∈ commV (pCoreOf 3 G), x y ∈ commV (pCoreOf 3 G) :=
    fun x hx y hy => commV_X_invariant G (pCore3_le G hx) hy
  let ρ : ↥(pCoreOf 3 G) →* Perm ↥(commV (pCoreOf 3 G)) :=
    (MulAut.toPerm ↥(commV (pCoreOf 3 G))).comp (H13.VolI.resHom (pCoreOf 3 G) _ hU)
  have hinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    apply Subtype.ext
    refine S.eq_one_of_trivial_commV x.2 fun y hy => ?_
    have := congrArg (fun π : Perm ↥(commV (pCoreOf 3 G)) =>
      ((π ⟨y, hy⟩ : ↥(commV (pCoreOf 3 G))) : V)) hx
    exact this
  have hdvd := Subgroup.card_dvd_of_injective ρ hinj
  rw [Nat.card_perm, D.card_Y, show Nat.factorial 4 = 24 from rfl] at hdvd
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := (pCore3_isPGroup G).exists_card_eq
  rw [hk] at hdvd ⊢
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, Subgroup.card_eq_one] at hk
    apply S.hO3
    rw [hk]
    exact bot_le
  have hk1 : k < 2 := by
    by_contra h2
    have h9 : 3 ^ 2 ∣ 3 ^ k := pow_dvd_pow 3 (by omega)
    have := h9.trans hdvd
    norm_num at this
  obtain rfl : k = 1 := by omega
  norm_num

end SixData

end SmithB57E

end CFSG.Quasithin
