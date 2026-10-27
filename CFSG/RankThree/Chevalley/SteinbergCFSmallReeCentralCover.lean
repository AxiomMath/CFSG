module

public import CFSG.Walter.Ree.Model.PSL2
public import CFSG.LocalAnalysis.SectionRank.OddCover.AltForm
public import CFSG.RankThree.Classical2.UnitarySplitPrimeRank

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.Assembly CFSG.Assembly.RankThreeEven
open CFSG.Walter.Ree.Model
open scoped commutatorElement

section Commutators

variable {G : Type*} [Group G]

theorem commutatorElement_mul_left_of_mem_center {a b c : G} (hb : ⁅b, c⁆ ∈ Subgroup.center G) :
    ⁅a * b, c⁆ = ⁅a, c⁆ * ⁅b, c⁆ := by
  have hbc : b * c = ⁅b, c⁆ * c * b := by rw [commutatorElement_def]; group
  have hac : a * c = ⁅a, c⁆ * c * a := by rw [commutatorElement_def]; group
  have hk := Subgroup.mem_center_iff.1 hb
  generalize ⁅b, c⁆ = k at hbc hk ⊢
  have e : ⁅a * b, c⁆ * (c * (a * b)) = (a * b) * c := by rw [commutatorElement_def]; group
  have e' : (a * b) * c = (k * ⁅a, c⁆) * (c * (a * b)) := by
    calc (a * b) * c = a * (b * c) := by group
      _ = a * (k * c * b) := by rw [hbc]
      _ = (a * k) * c * b := by group
      _ = (k * a) * c * b := by rw [hk a]
      _ = k * ((a * c) * b) := by group
      _ = k * (⁅a, c⁆ * c * a * b) := by rw [hac]
      _ = (k * ⁅a, c⁆) * (c * (a * b)) := by group
  rw [e'] at e
  rw [mul_right_cancel e, ← hk]

theorem commutatorElement_mul_right_of_mem_center {a b c : G} (hc : ⁅a, c⁆ ∈ Subgroup.center G) :
    ⁅a, b * c⁆ = ⁅a, b⁆ * ⁅a, c⁆ := by
  have hac : a * c = ⁅a, c⁆ * c * a := by rw [commutatorElement_def]; group
  have hab : a * b = ⁅a, b⁆ * b * a := by rw [commutatorElement_def]; group
  have hk := Subgroup.mem_center_iff.1 hc
  generalize ⁅a, c⁆ = k at hac hk ⊢
  have e : ⁅a, b * c⁆ * ((b * c) * a) = a * (b * c) := by rw [commutatorElement_def]; group
  have e' : a * (b * c) = ⁅a, b⁆ * k * ((b * c) * a) := by
    calc a * (b * c) = (a * b) * c := by group
      _ = ⁅a, b⁆ * b * (a * c) := by rw [hab]; group
      _ = ⁅a, b⁆ * b * (k * c * a) := by rw [hac]
      _ = ⁅a, b⁆ * (b * k) * c * a := by group
      _ = ⁅a, b⁆ * (k * b) * c * a := by rw [hk b]
      _ = ⁅a, b⁆ * k * ((b * c) * a) := by group
  rw [e'] at e
  exact mul_right_cancel e

theorem commutatorElement_mul_center {a b z z' : G} (hz : z ∈ Subgroup.center G)
    (hz' : z' ∈ Subgroup.center G) : ⁅a * z, b * z'⁆ = ⁅a, b⁆ := by
  have h1 := Subgroup.mem_center_iff.1 hz
  have h2 := Subgroup.mem_center_iff.1 hz'
  have hz1 : ⁅z, b * z'⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 (h1 _).symm
  have hz2 : ⁅a, z'⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 (h2 a)
  rw [commutatorElement_mul_left_of_mem_center (hz1 ▸ one_mem _), hz1, mul_one,
    commutatorElement_mul_right_of_mem_center (hz2 ▸ one_mem _), hz2, mul_one]

end Commutators

section SmallRee

variable {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.G2.prime]

theorem exists_smallRee_root_data (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    ∃ (x : K → ReeTag.G2.reeGamma K a) (d : Kˣ → ReeTag.G2.reeGamma K a)
      (t : ReeTag.G2.reeGamma K a),
      (∀ c c', x (c + c') = x c * x c') ∧ Function.Injective x ∧
      (∀ (r : Kˣ) c, d r * x c * (d r)⁻¹ = x ((r : K) ^ 2 * c)) ∧
      orderOf t = 2 ∧ ∀ c, t * x c = x c * t := by
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem ReeTag.G2.tag).length
  obtain ⟨ψ, hψC, -, -, -, hψ1, -⟩ := small_Ree_involution_centralizer_PSL2_structure a K hK w₀ hw₀
  have hψΓ : ∀ g, ψ g ∈ ReeTag.G2.reeGamma K a := fun g => (Subgroup.mem_inf.1 (hψC g)).1
  have hψt : ∀ g, ψ g * smallReeH a K (-1) = smallReeH a K (-1) * ψ g := fun g =>
    Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (hψC g)).2
  have huadd : ∀ c c' : K, uSL (c + c') = uSL c * uSL c' := fun c c' =>
    SL2_ext (by simp [coe_uSL, Matrix.mul_apply, Fin.sum_univ_two])
      (by simp [coe_uSL, Matrix.mul_apply, Fin.sum_univ_two, add_comm])
      (by simp [coe_uSL, Matrix.mul_apply, Fin.sum_univ_two])
      (by simp [coe_uSL, Matrix.mul_apply, Fin.sum_univ_two])
  have hconj : ∀ (r : Kˣ) (c : K), HSL r * uSL c * (HSL r)⁻¹ = uSL ((r : K) ^ 2 * c) := by
    intro r c
    have hr : (r : K) ≠ 0 := r.ne_zero
    refine SL2_ext ?_ ?_ ?_ ?_ <;>
      simp [coe_HSL, coe_uSL, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
        Matrix.mul_apply, Fin.sum_univ_two]
    field_simp
  have h2 : (2 : K) ≠ 0 := by
    have : ringChar K = 3 := ringChar.eq K 3
    exact Ring.two_ne_zero (by rw [this]; decide)
  refine ⟨fun c => ⟨ψ (uSL c), hψΓ _⟩, fun r => ⟨ψ (HSL r), hψΓ _⟩,
    ⟨smallReeH a K (-1), (Subgroup.mem_inf.1 (smallReeH_mem hK (-1))).2⟩,
    fun c c' => Subtype.ext (by simp only [huadd, map_mul, Subgroup.coe_mul]),
    fun c c' hcc => ?_, fun r c => Subtype.ext ?_, ?_, fun c => Subtype.ext ?_⟩
  ·
    have h : ψ (uSL (c - c')) = 1 := by
      have e : uSL (c - c') = uSL c * (uSL c')⁻¹ := by
        rw [eq_mul_inv_iff_mul_eq, ← huadd, sub_add_cancel]
      rw [e, map_mul, map_inv, show ψ (uSL c) = ψ (uSL c') from congrArg Subtype.val hcc,
        mul_inv_cancel]
    rcases (hψ1 _).1 h with h1 | h1
    · have := congrArg (fun g : SL2 K => (g : Matrix (Fin 2) (Fin 2) K) 0 1) h1
      simp only [coe_uSL, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
        Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply] at this
      simp at this
      exact sub_eq_zero.1 this
    · exfalso
      have := congrArg (fun g : SL2 K => (g : Matrix (Fin 2) (Fin 2) K) 0 0) h1
      simp only [coe_uSL, Matrix.SpecialLinearGroup.coe_neg,
        Matrix.SpecialLinearGroup.coe_one] at this
      simp at this
      exact h2 (by linear_combination this)
  · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← map_inv, ← map_mul, ← map_mul, hconj]
  · refine orderOf_eq_prime (Subtype.ext ?_) fun h => ?_
    · simp only [sq, Subgroup.coe_mul, OneMemClass.coe_one]
      exact smallReeH_neg_one_mul_self
    · have h' : smallReeH a K (-1) = smallReeH a K 1 := by
        rw [smallReeH_one]
        exact congrArg Subtype.val h
      have := congrArg Units.val (smallReeH_injective h')
      simp only [Units.val_neg, Units.val_one] at this
      exact h2 (by linear_combination -this)
  · simp only [Subgroup.coe_mul]
    exact (hψt _).symm

open CFSG.RankThree.Classical2 (exists_involution_elemAbelian_of_cover
  le_localRank_of_involution_elemAbelian)

open scoped IsMulCommutative in
theorem small_Ree_actual_central_cover_two_local_three_rank {X : Type*} [Group X] [Finite X]
    (Y : Subgroup X) (a : ℕ) (K : Type) [Field K] [Finite K] [CharP K ReeTag.G2.prime]
    (hK : Nat.card K = 3 ^ (2 * a + 1)) (φ : Y →* ReeTag.G2.reeGamma K a)
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center Y) :
    (∃ u ∈ Y, orderOf u = 2 ∧ ∃ V : Subgroup X, V ≤ Y ⊓ Subgroup.centralizer {u} ∧
      IsElemAbelian 3 V ∧ Nat.card V = 3 ^ (2 * a + 1)) ∧ 2 * a + 1 ≤ localRank 3 X := by
  obtain ⟨x, d, t, hxadd, hxinj, hdx, ht2, htx⟩ := exists_smallRee_root_data (a := a) hK
  have h3 : (3 : K) = 0 := by
    have : CharP K 3 := ‹_›
    exact_mod_cast CharP.cast_eq_zero K 3
  have hx0 : x 0 = 1 := by
    have h := hxadd 0 0
    rw [add_zero] at h
    exact mul_eq_left.1 h.symm
  have hxcomm : ∀ c c', x c * x c' = x c' * x c := fun c c' => by
    rw [← hxadd, ← hxadd, add_comm]
  have hx3 : ∀ c, x c ^ 3 = 1 := fun c => by
    rw [pow_three, ← hxadd, ← hxadd, ← hx0]
    congr 1
    linear_combination c * h3
  set ℓ : K → Y := fun c => Function.surjInv hφ (x c)
  have hℓ : ∀ c, φ (ℓ c) = x c := fun c => Function.surjInv_eq hφ _
  have hlift : ∀ v w : Y, φ v = φ w → ∃ z ∈ Subgroup.center Y, w = v * z := fun v w h =>
    ⟨v⁻¹ * w, hker (by rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]),
      by rw [mul_inv_cancel_left]⟩
  have hℓcen : ∀ c c', ⁅ℓ c, ℓ c'⁆ ∈ Subgroup.center Y := fun c c' => hker (by
    rw [MonoidHom.mem_ker, map_commutatorElement, hℓ, hℓ, commutatorElement_eq_one_iff_mul_comm]
    exact hxcomm c c')
  have hadd1 : ∀ c c' e, ⁅ℓ (c + c'), ℓ e⁆ = ⁅ℓ c, ℓ e⁆ * ⁅ℓ c', ℓ e⁆ := fun c c' e => by
    obtain ⟨z, hz, hzeq⟩ := hlift (ℓ c * ℓ c') (ℓ (c + c')) (by rw [map_mul, hℓ, hℓ, hℓ, hxadd])
    have h := commutatorElement_mul_center (a := ℓ c * ℓ c') (b := ℓ e) hz (one_mem _)
    rw [mul_one] at h
    rw [hzeq, h, commutatorElement_mul_left_of_mem_center (hℓcen c' e)]
  have hadd2 : ∀ c e e', ⁅ℓ c, ℓ (e + e')⁆ = ⁅ℓ c, ℓ e⁆ * ⁅ℓ c, ℓ e'⁆ := fun c e e' => by
    obtain ⟨z, hz, hzeq⟩ := hlift (ℓ e * ℓ e') (ℓ (e + e')) (by rw [map_mul, hℓ, hℓ, hℓ, hxadd])
    have h := commutatorElement_mul_center (a := ℓ c) (b := ℓ e * ℓ e') (one_mem _) hz
    rw [mul_one] at h
    rw [hzeq, h, commutatorElement_mul_right_of_mem_center (hℓcen c e')]
  have hsq : ∀ r : K, r ≠ 0 → ∀ c c', ⁅ℓ (r ^ 2 * c), ℓ (r ^ 2 * c')⁆ = ⁅ℓ c, ℓ c'⁆ := by
    intro r hr c c'
    obtain ⟨D, hD⟩ := hφ (d (Units.mk0 r hr))
    have hconj : ∀ e, φ (D * ℓ e * D⁻¹) = φ (ℓ (r ^ 2 * e)) := fun e => by
      rw [map_mul, map_mul, map_inv, hD, hℓ, hℓ, hdx, Units.val_mk0]
    obtain ⟨z, hz, hzeq⟩ := hlift _ _ (hconj c)
    obtain ⟨z', hz', hzeq'⟩ := hlift _ _ (hconj c')
    rw [hzeq, hzeq', commutatorElement_mul_center hz hz']
    have h := map_commutatorElement (MulAut.conj D) (ℓ c) (ℓ c')
    simp only [MulAut.conj_apply] at h
    rw [← h, Subgroup.mem_center_iff.1 (hℓcen c c') D, mul_inv_cancel_right]
  have h9 : 3 ^ (2 * a + 1) ≠ 9 := fun h => by
    have := Nat.pow_right_injective (by norm_num : 2 ≤ 3) (h.trans (by norm_num : 9 = 3 ^ 2))
    omega
  have hb0 : ∀ c c', ⁅ℓ c, ℓ c'⁆ = 1 := fun c c' => by
    have h := CFSG.SectionRank.OddCover.square_invariant_alternating_eq_zero (p := 3) (by norm_num)
      hK (fun c c' => Additive.ofMul (⟨⁅ℓ c, ℓ c'⁆, hℓcen c c'⟩ : Subgroup.center Y))
      (fun c c' e => by rw [← ofMul_mul]; exact congrArg _ (Subtype.ext (hadd1 c c' e)))
      (fun c e e' => by rw [← ofMul_mul]; exact congrArg _ (Subtype.ext (hadd2 c e e')))
      (fun c => ofMul_eq_zero.2 (Subtype.ext (commutatorElement_self _)))
      (fun r hr c c' => congrArg _ (Subtype.ext (hsq r hr c c'))) h9 c c'
    exact congrArg Subtype.val (ofMul_eq_zero.1 h)
  let U : Subgroup (ReeTag.G2.reeGamma K a) :=
    { carrier := Set.range x
      mul_mem' := by rintro _ _ ⟨c, rfl⟩ ⟨c', rfl⟩; exact ⟨c + c', hxadd c c'⟩
      one_mem' := ⟨0, hx0⟩
      inv_mem' := by
        rintro _ ⟨c, rfl⟩
        exact ⟨-c, by rw [eq_inv_iff_mul_eq_one, ← hxadd, neg_add_cancel, hx0]⟩ }
  have hF : ∀ v ∈ U.comap φ, ∀ w ∈ U.comap φ, v * w = w * v := by
    rintro v ⟨c, hc⟩ w ⟨c', hc'⟩
    obtain ⟨z, hz, rfl⟩ := hlift (ℓ c) v (by rw [hℓ, hc])
    obtain ⟨z', hz', rfl⟩ := hlift (ℓ c') w (by rw [hℓ, hc'])
    rw [← commutatorElement_eq_one_iff_mul_comm, commutatorElement_mul_center hz hz', hb0]
  have hU3 : ∀ g ∈ U, g ^ 3 = 1 := by
    rintro _ ⟨c, rfl⟩
    exact hx3 c
  have hUcard : 3 ^ (2 * a + 1) ≤ Nat.card U := by
    rw [← hK]
    exact (Nat.card_range_of_injective hxinj).ge
  have ht1 : t ≠ 1 := fun h => by
    rw [h, orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  have htU : ∀ g ∈ U, Commute t g := by
    rintro _ ⟨c, rfl⟩
    exact htx c
  obtain ⟨u, huY, hu, V, hV, hVab, hVcard⟩ := exists_involution_elemAbelian_of_cover Y hφ hker
    Nat.prime_three (by norm_num) hU3 hF hUcard ht1 (by rw [← ht2, pow_orderOf_eq_one]) htU
  exact ⟨⟨u, huY, hu, V, hV, hVab, hVcard⟩,
    le_localRank_of_involution_elemAbelian Nat.prime_three hu (hV.trans inf_le_right) hVab hVcard⟩

end SmallRee

end CFSG.RankThree.Chevalley
