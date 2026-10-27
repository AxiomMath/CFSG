module

public import CFSG.Quasithin.Background.D2Z4

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits
open scoped commutatorElement

variable {V : Type*} [CommGroup V] [Finite V]

theorem kap_mono (A : Subgroup (MulAut V)) {W W' : Subgroup V} (h : W' ≤ W) :
    kap A W' ≤ kap A W := by
  unfold kap
  set C : Subgroup V := W ⊓ fixV A with hC
  have h1 := rk_sup_add_rk_inf W' C
  have h2 : rk (W' ⊔ C : Subgroup V) ≤ rk W := rk_mono (sup_le h inf_le_left)
  have h3 : W' ⊓ C = W' ⊓ fixV A := by
    rw [hC, ← inf_assoc, inf_eq_left.mpr h]
  rw [h3] at h1
  have h4 := rk_mono (inf_le_left : W' ⊓ fixV A ≤ W')
  have h5 := rk_mono (inf_le_left : C ≤ W)
  omega

theorem kap_top (A : Subgroup (MulAut V)) : kap A ⊤ = rkIdx (fixV A) := by
  have h := rk_add_rkIdx (fixV A)
  unfold kap
  rw [top_inf_eq, rk_top]
  omega

theorem kap_ge_rk_commSub {A : Subgroup (MulAut V)} {t : MulAut V} (ht : t ∈ A) {W : Subgroup V}
    (hW : ∀ x ∈ Subgroup.zpowers t, ∀ w ∈ W, x w ∈ W) :
    rk (commSub W (Subgroup.zpowers t)) ≤ kap A W := by
  have h1 := rk_commSub_add_rk_inf_fixV hW
  have h2 : rk (W ⊓ fixV A : Subgroup V) ≤ rk (W ⊓ fixV (Subgroup.zpowers t) : Subgroup V) :=
    rk_mono (inf_le_inf le_rfl (fixV_anti (Subgroup.zpowers_le.mpr ht)))
  unfold kap
  omega

section D214

variable {X A : Subgroup (MulAut V)} {r : ℚ}

theorem rkIdx_fixV_eq (hV : ∀ v : V, v ^ 2 = 1) (h : D214Hyp X A r) :
    (rkIdx (fixV A) : ℚ) = 2 * r := by
  obtain ⟨r', hr', hr2, ⟨⟨hA2, hrA⟩, hA3⟩, hmin⟩ := QhatStar_spec h.mem
  have hrr : r' = r := by
    have := hr'.symm.trans h.qhat
    exact_mod_cast this
  subst hrr
  have hrk : rk A = 2 := D2_14_4 hV h
  have := hA2.rAV_mul
  rw [hrA, hrk] at this
  rw [← this]
  push_cast
  ring

theorem le_two_of_D214Hyp (h : D214Hyp X A r) : r ≤ 2 := by
  obtain ⟨r', hr', hr2, -, -⟩ := QhatStar_spec h.mem
  have hrr : r' = r := by
    have := hr'.symm.trans h.qhat
    exact_mod_cast this
  rwa [← hrr]

theorem one_lt_of_D214Hyp (hV : ∀ v : V, v ^ 2 = 1) (h : D214Hyp X A r) : 1 < r := by
  by_contra hle
  push Not at hle
  obtain ⟨a, b, k⟩ := h.exists_klein hV
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hrkA : rk A = 2 := D2_14_4 hV h
  obtain ⟨y, hy⟩ : ∃ y ∈ pCoreOf 3 X, a * y ≠ y * a := by
    by_contra hcon
    push Not at hcon
    exact k.ha1 (faithful_pCore_three hV h a k.ha fun y hy => hcon y hy)
  have hD : ⁅pCoreOf 3 X, A⁆ ≠ ⊥ := commutator_ne_bot_iff.mpr ⟨y, hy.1, a, k.ha, hy.2⟩
  have h4 := (D2_13 hV h.qhat h.mem (p := 3) (by norm_num) (D := ⁅pCoreOf 3 X, A⁆) rfl hD).2.2.2.1 hle
  omega

theorem rkIdx_fixV_bounds (hV : ∀ v : V, v ^ 2 = 1) (h : D214Hyp X A r) :
    3 ≤ rkIdx (fixV A) ∧ rkIdx (fixV A) ≤ 4 := by
  have h1 := rkIdx_fixV_eq hV h
  have h2 := one_lt_of_D214Hyp hV h
  have h3 := le_two_of_D214Hyp h
  constructor
  · by_contra hlt
    push Not at hlt
    have : (rkIdx (fixV A) : ℚ) ≤ 2 := by exact_mod_cast (by omega : rkIdx (fixV A) ≤ 2)
    linarith
  · have : (rkIdx (fixV A) : ℚ) ≤ 4 := by linarith
    exact_mod_cast this

theorem rk_commV_gt (hV : ∀ v : V, v ^ 2 = 1) (h : D214Hyp X A r) {t : MulAut V} (ht : t ∈ A)
    (ht1 : t ≠ 1) : r < (rk (commV (Subgroup.zpowers t)) : ℚ) := by
  obtain ⟨r', hr', hr2, ⟨⟨hA2, hrA⟩, hA3⟩, hmin⟩ := QhatStar_spec h.mem
  have hrr : r' = r := by
    have := hr'.symm.trans h.qhat
    exact_mod_cast this
  have hrr' := hrr.symm
  subst hrr'
  by_contra hle
  push Not at hle
  have ht2 : t ^ 2 = 1 := hA2.isElemAbelian2.2 t ht
  have hBX : Subgroup.zpowers t ≤ X := Subgroup.zpowers_le.mpr (hA2.le ht)
  have hB2 : IsA2 X (Subgroup.zpowers t) :=
    ⟨hBX, fun hbot => ht1 (by rwa [Subgroup.zpowers_eq_bot] at hbot),
      ⟨fun a ha b hb => by
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
        exact ((Commute.refl t).zpow_zpow i j).eq,
        fun a ha => by
          obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
          rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
          simp [ht2]⟩⟩
  have hB3 : commSeries (Subgroup.zpowers t) 3 = ⊥ :=
    commSeries_eq_bot_of_le (by norm_num)
      ((isQuadratic_iff_commSeries_two _).mp (isQuadratic_zpowers hV ht2))
  have hrB : rAV (Subgroup.zpowers t) ≤ r := by
    rw [rAV_zpowers ht1 ht2]; exact hle
  have hmem : Subgroup.zpowers t ∈ kRle X 3 r := ⟨⟨hB2, hrB⟩, hB3⟩
  have heq := hmin _ hmem (Subgroup.zpowers_le.mpr ht)
  have hcardB : Nat.card (Subgroup.zpowers t) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [Nat.card_zpowers, orderOf_eq_prime ht2 ht1]
  have hcardA := h.card_A hV
  rw [heq] at hcardB
  omega

theorem Nt_data (hV : ∀ v : V, v ^ 2 = 1) (h : D214Hyp X A r) {t u : MulAut V}
    (k : KleinData A t u) (hne : centR X t ≠ ⊥) :
    ∃ y : MulAut V, y ∈ centR X t ∧ Subgroup.zpowers y = centR X t ∧
      commV (centR X t) ⊓ fixV (Subgroup.zpowers y) = ⊥ ∧ u * y * u⁻¹ = y⁻¹ ∧
      (∀ g ∈ Subgroup.zpowers u, ∀ w ∈ commV (centR X t), g w ∈ commV (centR X t)) ∧
      (∀ g ∈ Subgroup.zpowers y, ∀ w ∈ commV (centR X t), g w ∈ commV (centR X t)) := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨hcard, -⟩ := centR_data hV h k hne
  obtain ⟨y, hyQ, hy1, hyz, -⟩ := exists_generator_of_prime_card (p := 3) hcard
  have hcomm := pCoreOf_comm hV h
  refine ⟨y, hyQ, hyz, ?_, inverts_centR hV h k y hyQ, ?_, ?_⟩
  · rw [hyz]
    exact (commV_card_three hV hcard).2.1
  · intro g hg w hw
    exact Nt_inv_A h k.ha (Subgroup.zpowers_le.mpr k.hb hg) w hw
  · intro g hg w hw
    rw [hyz] at hg
    exact Nt_inv_P hcomm t (centR_le_pCoreOf X t hg) w hw

theorem rk_Nt_eq_two_mul (hV : ∀ v : V, v ^ 2 = 1) (h : D214Hyp X A r) {t u : MulAut V}
    (k : KleinData A t u) (hne : centR X t ≠ ⊥) :
    rk (commV (centR X t)) = 2 * rk (commSub (commV (centR X t)) (Subgroup.zpowers u)) := by
  obtain ⟨y, -, -, hfix, hinv, hWu, hWy⟩ := Nt_data hV h k hne
  exact rk_eq_two_mul_sub hV k.hb2 hinv hWu hWy hfix

theorem rk_commSub_Nt_self (hV : ∀ v : V, v ^ 2 = 1) (h : D214Hyp X A r) {t u : MulAut V}
    (k : KleinData A t u) (hne : centR X t ≠ ⊥) :
    rk (commSub (commV (centR X t)) (Subgroup.zpowers t)) + 2 = rk (commV (centR X t)) := by
  have hinv : ∀ x ∈ Subgroup.zpowers t, ∀ w ∈ commV (centR X t), x w ∈ commV (centR X t) :=
    fun x hx w hw => Nt_inv_A h k.ha (Subgroup.zpowers_le.mpr k.ha hx) w hw
  have h1 := rk_commSub_add_rk_inf_fixV hinv
  have h2 := (commV_centR_facts hV h k hne).1
  omega

theorem rk_Nt_fixV_A (hV : ∀ v : V, v ^ 2 = 1) (h : D214Hyp X A r) {t u : MulAut V}
    (k : KleinData A t u) (hne : centR X t ≠ ⊥) :
    rk (commV (centR X t) ⊓ fixV A : Subgroup V) = 1 := by
  obtain ⟨y, hyQ, hyz, hfix, hinv, hWu, hWy⟩ := Nt_data hV h k hne
  have hcomm := pCoreOf_comm hV h
  set E : Subgroup V := commV (centR X t) ⊓ fixV (Subgroup.zpowers t) with hEdef
  have hE2 : rk E = 2 := (commV_centR_facts hV h k hne).1
  have hEu : ∀ g ∈ Subgroup.zpowers u, ∀ w ∈ E, g w ∈ E := by
    intro g hg w hw
    have hgc : g * t = t * g := by
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      exact (Commute.zpow_left (show Commute u t from k.comm.symm) j).eq
    exact ⟨hWu g hg w hw.1, fixV_inv_comm hgc w hw.2⟩
  have hEy : ∀ g ∈ Subgroup.zpowers y, ∀ w ∈ E, g w ∈ E := by
    intro g hg w hw
    have hgQ : g ∈ centR X t := hyz ▸ hg
    have hgc : g * t = t * g := (mem_centR.mp hgQ).2
    exact ⟨hWy g hg w hw.1, fixV_inv_comm hgc w hw.2⟩
  have hEfix : E ⊓ fixV (Subgroup.zpowers y) = ⊥ :=
    eq_bot_iff.mpr fun w hw => by
      have : w ∈ commV (centR X t) ⊓ fixV (Subgroup.zpowers y) := ⟨hw.1.1, hw.2⟩
      rwa [hfix, Subgroup.mem_bot] at this
  have hrkE := rk_eq_two_mul_sub hV (W := E) k.hb2 hinv hEu hEy hEfix
  have hsum := rk_commSub_add_rk_inf_fixV hEu
  have heq : commV (centR X t) ⊓ fixV A = E ⊓ fixV (Subgroup.zpowers u) := by
    rw [fixV_klein k, hEdef, inf_assoc]
  rw [heq]
  omega

end D214

end CFSG.Quasithin
