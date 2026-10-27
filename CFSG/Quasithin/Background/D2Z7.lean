module

public import CFSG.Quasithin.Background.D2Z6

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits
open scoped commutatorElement

variable {V : Type*} [CommGroup V] [Finite V]

omit [Finite V] in
theorem mem_sup_of_forall_commute {G : Type*} [Group G] {H K : Subgroup G}
    (hcomm : ∀ a ∈ H, ∀ b ∈ K, a * b = b * a) {x : G} (hx : x ∈ H ⊔ K) :
    ∃ a ∈ H, ∃ b ∈ K, x = a * b := by
  let S : Subgroup G :=
    { carrier := {x | ∃ a ∈ H, ∃ b ∈ K, x = a * b}
      one_mem' := ⟨1, H.one_mem, 1, K.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', H.mul_mem ha ha', b * b', K.mul_mem hb hb', ?_⟩
        calc a * b * (a' * b') = a * (b * a') * b' := by group
          _ = a * (a' * b) * b' := by rw [← hcomm a' ha' b hb]
          _ = a * a' * (b * b') := by group
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, H.inv_mem ha, b⁻¹, K.inv_mem hb, ?_⟩
        calc (a * b)⁻¹ = b⁻¹ * a⁻¹ := mul_inv_rev a b
          _ = a⁻¹ * b⁻¹ := by
            have h1 : b * a = a * b := (hcomm a ha b hb).symm
            have : (b * a)⁻¹ = (a * b)⁻¹ := by rw [h1]
            rw [mul_inv_rev, mul_inv_rev] at this
            exact this.symm ▸ rfl }
  have hHS : H ≤ S := fun a ha => ⟨a, ha, 1, K.one_mem, by simp⟩
  have hKS : K ≤ S := fun b hb => ⟨1, H.one_mem, b, hb, by simp⟩
  exact (sup_le hHS hKS) hx

omit [Finite V] in
theorem pow_eq_one_of_mem_sup_of_commute {G : Type*} [Group G] {H K : Subgroup G} {n : ℕ}
    (hcomm : ∀ a ∈ H, ∀ b ∈ K, a * b = b * a) (hH : ∀ x ∈ H, x ^ n = 1)
    (hK : ∀ x ∈ K, x ^ n = 1) {x : G} (hx : x ∈ H ⊔ K) : x ^ n = 1 := by
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_forall_commute hcomm hx
  rw [(show Commute a b from hcomm a ha b hb).mul_pow, hH a ha, hK b hb, mul_one]

omit [Finite V] in
theorem commV_bot : commV (⊥ : Subgroup (MulAut V)) = ⊥ :=
  CFSG.Quasithin.FixVLat.commV_bot

section Triple

variable {X A : Subgroup (MulAut V)} {r : ℚ}

theorem pCoreOf_eq_sup_centR (hV : ∀ v : V, v ^ 2 = 1) (h : D214Hyp X A r) {a b : MulAut V}
    (k : KleinData A a b) :
    pCoreOf 3 X = centR X a ⊔ centR X b ⊔ centR X (a * b) :=
  le_antisymm (pCoreOf_le_sup_centR hV h k)
    (sup_le (sup_le (centR_le_pCoreOf X a) (centR_le_pCoreOf X b)) (centR_le_pCoreOf X (a * b)))

theorem centR_comm (hV : ∀ v : V, v ^ 2 = 1) (h : D214Hyp X A r) (s s' : MulAut V) :
    ∀ x ∈ centR X s, ∀ y ∈ centR X s', x * y = y * x := fun x hx y hy =>
  pCoreOf_comm hV h x (centR_le_pCoreOf X s hx) y (centR_le_pCoreOf X s' hy)

theorem centR_actions (hV : ∀ v : V, v ^ 2 = 1) (h : D214Hyp X A r) {t u : MulAut V}
    (k : KleinData A t u) {y : MulAut V} (hy : y ∈ centR X t) :
    t * y * t⁻¹ = y ∧ u * y * u⁻¹ = y⁻¹ ∧ (t * u) * y * (t * u)⁻¹ = y⁻¹ := by
  refine ⟨?_, inverts_centR hV h k y hy, inverts_centR hV h k.third y hy⟩
  have : y * t = t * y := (mem_centR.mp hy).2
  rw [← this, mul_inv_cancel_right]

theorem eq_one_of_eq_inv_of_mem_pCoreOf {z : MulAut V} (hz : z ∈ pCoreOf 3 X) (h : z = z⁻¹) :
    z = 1 := by
  apply eq_one_of_sq_eq_one_of_mem_pCoreOf hz
  rw [pow_two]
  exact mul_eq_one_iff_eq_inv.mpr h

theorem centR_inf_sup_eq_bot (hV : ∀ v : V, v ^ 2 = 1) (h : D214Hyp X A r) {t u w : MulAut V}
    (ku : KleinData A u t) (kw : KleinData A w t) :
    centR X t ⊓ (centR X u ⊔ centR X w) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxt, hx⟩
  obtain ⟨y, hy, z, hz, rfl⟩ := mem_sup_of_forall_commute (centR_comm hV h u w) hx
  have e1 : t * (y * z) * t⁻¹ = y * z := by
    have : (y * z) * t = t * (y * z) := (mem_centR.mp hxt).2
    rw [← this, mul_inv_cancel_right]
  have e2 : t * (y * z) * t⁻¹ = (y * z)⁻¹ := by
    have hy' : t * y * t⁻¹ = y⁻¹ := inverts_centR hV h ku y hy
    have hz' : t * z * t⁻¹ = z⁻¹ := inverts_centR hV h kw z hz
    have hc : y * z = z * y := centR_comm hV h u w y hy z hz
    calc t * (y * z) * t⁻¹ = (t * y * t⁻¹) * (t * z * t⁻¹) := by group
      _ = y⁻¹ * z⁻¹ := by rw [hy', hz']
      _ = (z * y)⁻¹ := by rw [mul_inv_rev]
      _ = (y * z)⁻¹ := by rw [← hc]
  have := eq_one_of_eq_inv_of_mem_pCoreOf (centR_le_pCoreOf X t hxt) (e1.symm.trans e2)
  rw [this]
  exact Subgroup.one_mem _

theorem pCoreOf_pow_three (hV : ∀ v : V, v ^ 2 = 1) (h : D214Hyp X A r) :
    ∀ y ∈ pCoreOf 3 X, y ^ 3 = 1 := by
  obtain ⟨a, b, k⟩ := h.exists_klein hV
  intro y hy
  rw [pCoreOf_eq_sup_centR hV h k] at hy
  refine pow_eq_one_of_mem_sup_of_commute (n := 3) (H := centR X a ⊔ centR X b)
    (K := centR X (a * b)) ?_ ?_ (fun x hx => centR_pow_three hV h k.third.symm hx) hy
  · intro x hx z hz
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := mem_sup_of_forall_commute (centR_comm hV h a b) hx
    have c1 := centR_comm hV h a (a * b) x₁ hx₁ z hz
    have c2 := centR_comm hV h b (a * b) x₂ hx₂ z hz
    calc x₁ * x₂ * z = x₁ * (x₂ * z) := by group
      _ = x₁ * (z * x₂) := by rw [c2]
      _ = (x₁ * z) * x₂ := by group
      _ = (z * x₁) * x₂ := by rw [c1]
      _ = z * (x₁ * x₂) := by group
  · intro x hx
    exact pow_eq_one_of_mem_sup_of_commute (n := 3) (H := centR X a) (K := centR X b)
      (centR_comm hV h a b) (fun x hx => centR_pow_three hV h k hx)
      (fun x hx => centR_pow_three hV h k.symm hx) hx

theorem isDirectSum_commV_fixV (hV : ∀ v : V, v ^ 2 = 1) (X : Subgroup (MulAut V)) :
    IsDirectSum ⊤ (commV (pCoreOf 3 X)) (fixV (pCoreOf 3 X)) := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hPodd : Odd (Nat.card (pCoreOf 3 X)) :=
    odd_card_of_isPGroup_odd (by norm_num) (pCoreOf_isPGroup 3 X)
  obtain ⟨hsup, hinf⟩ := coprime_decomp hPodd hV (W := ⊤) (fun _ _ w _ => Subgroup.mem_top w)
  rw [← commV_eq_commSub, top_inf_eq] at hsup hinf
  exact ⟨hsup, hinf⟩

theorem kap_commV_pCoreOf (hV : ∀ v : V, v ^ 2 = 1) (h : D214Hyp X A r) :
    kap A (commV (pCoreOf 3 X)) = rkIdx (fixV A) := by
  have hdir := isDirectSum_commV_fixV hV X
  have hAU : ∀ g ∈ A, ∀ w ∈ commV (pCoreOf 3 X), g w ∈ commV (pCoreOf 3 X) := fun g hg w hw =>
    commV_smul_mem (fun p hp => h.conj_mem hg hp) hw
  have hAW : ∀ g ∈ A, ∀ w ∈ fixV (pCoreOf 3 X), g w ∈ fixV (pCoreOf 3 X) := fun g hg w hw =>
    fixV_smul_mem (fun p hp => by
      have := h.conj_mem (A.inv_mem hg) hp
      simpa using this) hw
  have hkap := kap_add hdir hAU hAW
  rw [kap_top] at hkap
  have hW0 : fixV (pCoreOf 3 X) ≤ fixV A := commSub_eq_bot_iff.mp (D2_14_5 hV h)
  have : kap A (fixV (pCoreOf 3 X)) = 0 := by
    unfold kap
    rw [inf_eq_left.mpr hW0]
    omega
  omega

theorem commV_zpowers_eq_commSub (hV : ∀ v : V, v ^ 2 = 1) (h : D214Hyp X A r) {x : MulAut V}
    (hx : x ∈ A) :
    commV (Subgroup.zpowers x) = commSub (commV (pCoreOf 3 X)) (Subgroup.zpowers x) := by
  have hdir := isDirectSum_commV_fixV hV X
  have hW0 : fixV (pCoreOf 3 X) ≤ fixV (Subgroup.zpowers x) :=
    (commSub_eq_bot_iff.mp (D2_14_5 hV h)).trans (fixV_anti (Subgroup.zpowers_le.mpr hx))
  rw [commV_eq_commSub, ← hdir.1, commSub_sup_left, commSub_eq_bot_iff.mpr hW0, sup_bot_eq]

end Triple

end CFSG.Quasithin
