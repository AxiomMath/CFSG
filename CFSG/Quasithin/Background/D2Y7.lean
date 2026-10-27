module

public import CFSG.Quasithin.Background.D2Y6

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

variable {V : Type*} [CommGroup V] [Finite V]

structure Good (X : Subgroup (MulAut V)) (t x z : MulAut V) : Prop where
  card : Nat.card (centR X x) = 9
  comm : ∀ a ∈ centR X x, ∀ b ∈ centR X x, a * b = b * a
  cube : ∀ a ∈ centR X x, a ^ 3 = 1
  hz : z ∈ centR X x
  hz1 : z ≠ 1
  rk6 : rk (commV (Subgroup.zpowers z)) = 6
  tz : t * z = z * t
  rk4 : ∀ w ∈ centR X x, w ≠ 1 → Subgroup.zpowers w ≠ Subgroup.zpowers z →
    rk (commV (Subgroup.zpowers w)) = 4
  hU : commV (centR X x) = commV (Subgroup.zpowers z)

section Main

variable {X : Subgroup (MulAut V)}

theorem D2_28 (hV : ∀ v : V, v ^ 2 = 1) (c : CycCtx X) (hX1 : ∀ Y ∈ Xk X 1, False)
    {t x y : MulAut V} (d : EData X t x y) : ∃ z, Good X t x z := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hxo := d.orderOf_x hV c hX1
  have hyo := d.orderOf_y
  have hrkx := d.rk_x hV c hX1
  have hrky := d.rk_y hV c hX1
  rcases pattern_E9 hV c hX1 d.h.hx d.hyR hxo hyo d.comm d.hne hrkx hrky with
    ⟨h6, hcases⟩ | ⟨h8, h8ab, h8abb⟩
  swap
  · exact (pattern8_false hV c hX1 d h8 h8ab h8abb).elim
  have hP := centR_eq_E hV c hX1 d h6
  obtain ⟨hEcard, hEcomm, hform⟩ := E9_data hxo hyo d.comm d.hne
  obtain ⟨hxyo, hxyyo⟩ := E9_orders hxo hyo d.comm d.hne
  have hxE : x ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers y :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
  have hyE : y ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers y :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have hxyE : x * y ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers y := Subgroup.mul_mem _ hxE hyE
  have hxyyE : x * y * y ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers y := Subgroup.mul_mem _ hxyE hyE
  obtain ⟨z, hzE, hzo, hz6, hothers⟩ : ∃ z ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers y,
      orderOf z = 3 ∧ rk (commV (Subgroup.zpowers z)) = 6 ∧
      ∀ w ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers y, w ≠ 1 →
        Subgroup.zpowers w ≠ Subgroup.zpowers z → rk (commV (Subgroup.zpowers w)) = 4 := by
    rcases hcases with ⟨h4, h6'⟩ | ⟨h6', h4⟩
    · refine ⟨x * y * y, hxyyE, hxyyo, h6', fun w hw hw1 hne => ?_⟩
      rcases sub_E_cases hxo hyo d.comm d.hne hw hw1 with e | e | e | e
      · rw [e]; exact hrkx
      · rw [e]; exact hrky
      · rw [e]; exact h4
      · exact absurd e hne
    · refine ⟨x * y, hxyE, hxyo, h6', fun w hw hw1 hne => ?_⟩
      rcases sub_E_cases hxo hyo d.comm d.hne hw hw1 with e | e | e | e
      · rw [e]; exact hrkx
      · rw [e]; exact hrky
      · exact absurd e hne
      · rw [e]; exact h4
  have hz3 : z ^ 3 = 1 := by rw [← hzo]; exact pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := fun e => by rw [e, orderOf_one] at hzo; omega
  have hzR : z ∈ pCoreOf 3 X := by
    have : z ∈ centR X x := by rw [hP]; exact hzE
    exact (mem_centR.mp this).1
  refine ⟨z, ?_⟩
  have htz : t * z * t⁻¹ = z := by
    have hg : ∀ p ∈ centR X x, t * p * t⁻¹ ∈ centR X x := fun p hp =>
      conj_mem_centR d.h.ht d.h.hinv hp
    have hz'E := conj_mem_E hV c hX1 d hg hzE
    have hz'1 : t * z * t⁻¹ ≠ 1 := by
      intro e
      apply hz1
      have : z = t⁻¹ * (t * z * t⁻¹) * t := by group
      rw [this, e]
      group
    have hz'r : rk (commV (Subgroup.zpowers (t * z * t⁻¹))) = 6 := by
      rw [rk_commV_zpowers_conj]; exact hz6
    have hzz' : Subgroup.zpowers (t * z * t⁻¹) = Subgroup.zpowers z := by
      by_contra hne
      have := hothers _ hz'E hz'1 hne
      omega
    have hmem : t * z * t⁻¹ ∈ Subgroup.zpowers z := by
      rw [← hzz']
      exact Subgroup.mem_zpowers _
    rcases eq_of_mem_zpowers_cube hz3 hmem with e | e | e
    · exact absurd e hz'1
    · exact e
    · exfalso
      have hp : InvPair X t z := ⟨d.h.ht, hzR, hz1, e⟩
      have := (inverted_data hV c hX1 hp.ht hp.hx hp.hx1 hp.hinv).2.1
      omega
  refine ⟨?_, ?_, ?_, ?_, hz1, hz6, ?_, ?_, ?_⟩
  · rw [hP]; exact hEcard
  · rw [hP]; exact hEcomm
  · intro a ha
    rw [hP] at ha
    obtain ⟨i, j, hij⟩ := hform a ha
    exact cube_eq_one_of_mem_E (d.hx3 hV c hX1) d.hy3 d.comm hij
  · rw [hP]; exact hzE
  · exact mul_inv_eq_iff_eq_mul.mp htz
  · intro w hw hw1 hne
    rw [hP] at hw
    exact hothers w hw hw1 hne
  · rw [hP]
    refine (eq_of_le_of_rk_le hV (commV_mono ((Subgroup.zpowers_le.mpr hzE))) ?_).symm
    rw [h6, hz6]

end Main

end CFSG.Quasithin
