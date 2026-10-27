module

public import CFSG.Quasithin.H13.U3S1347N
public import CFSG.Quasithin.H13.U3S1347Y

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits

theorem card_mul_card_le_of_inf_eq_bot {W : Type*} [Group W] [Finite W] {A B : Subgroup W}
    (hAB : A ⊓ B = ⊥) : Nat.card A * Nat.card B ≤ Nat.card W := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective (fun p => (p.1 : W) * p.2) fun p q hpq => ?_
  have h1 : (q.1 : W)⁻¹ * p.1 = q.2 * (p.2 : W)⁻¹ := by
    have hpq' : (p.1 : W) * p.2 = q.1 * q.2 := hpq
    calc (q.1 : W)⁻¹ * p.1 = (q.1 : W)⁻¹ * (p.1 * p.2) * (p.2 : W)⁻¹ := by group
      _ = (q.1 : W)⁻¹ * (q.1 * q.2) * (p.2 : W)⁻¹ := by rw [hpq']
      _ = q.2 * (p.2 : W)⁻¹ := by group
  have hmem : (q.1 : W)⁻¹ * p.1 ∈ A ⊓ B :=
    ⟨A.mul_mem (A.inv_mem q.1.2) p.1.2, by rw [h1]; exact B.mul_mem q.2.2 (B.inv_mem p.2.2)⟩
  rw [hAB, mem_bot] at hmem
  have e1 : (p.1 : W) = q.1 := (inv_mul_eq_one.1 hmem).symm
  have e2 : (p.2 : W) = q.2 := by
    have := h1
    rw [hmem] at this
    exact (mul_inv_eq_one.1 this.symm).symm
  exact Prod.ext (Subtype.ext e1) (Subtype.ext e2)

theorem card_fixAutU3_le_sixteen {W : Type*} [Group W] [Finite W]
    (hW2 : ∀ w : W, w ^ 2 = 1) (hW : Nat.card W = 2 ^ 6) {z α : MulAut W} (hz3 : z ^ 3 = 1)
    (hzfix : fixAutU3 z = ⊥) (hα1 : α ≠ 1) (hα2 : α ^ 2 = 1)
    (hαz : α * z * α⁻¹ = z ∨ α * z * α⁻¹ = z⁻¹) : Nat.card (fixAutU3 α) ≤ 16 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hW2g : IsPGroup 2 W := fun w => ⟨1, by rw [pow_one, hW2]⟩
  obtain ⟨j, hj, hj6⟩ := exists_card_lt_of_ne_top hW2g hW
    (fun h => hα1 (eq_one_of_fixAutU3_eq_top h))
  rcases hαz with e | e
  ·
    have hcomm : z * α = α * z := by
      calc z * α = (α * z * α⁻¹) * α := by rw [e]
        _ = α * z := by group
    have h1 := card_modEq_fixAutU3 (q := 3) (α := z) (β := α) hz3 hcomm
    rw [hzfix, inf_bot_eq, card_bot, hj] at h1
    rw [hj]
    interval_cases j <;> first | (exfalso; revert h1; decide) | norm_num
  ·
    have hαinv : α⁻¹ = α := inv_eq_of_mul_eq_one_right (by rw [← sq, hα2])
    have hinter : fixAutU3 α ⊓ fixAutU3 (z * α * z⁻¹) = ⊥ := by
      rw [eq_bot_iff]
      intro w hw
      obtain ⟨hw1, hw2⟩ := mem_inf.1 hw
      have hw1' : α w = w := hw1
      have hw2' : (z * α * z⁻¹) w = w := hw2
      have hz' : α⁻¹ * (z * α * z⁻¹) = z := by
        have h1 : α⁻¹ * z * α = z⁻¹ := by
          rw [hαinv]
          calc α * z * α = α * z * α⁻¹ := by rw [hαinv]
            _ = z⁻¹ := e
        calc α⁻¹ * (z * α * z⁻¹) = (α⁻¹ * z * α) * z⁻¹ := by group
          _ = z⁻¹ * z⁻¹ := by rw [h1]
          _ = z ^ 3 * z⁻¹ * z⁻¹ := by rw [hz3, one_mul]
          _ = z := by group
      have hzw : z w = w := by
        rw [← hz', MulAut.mul_apply, hw2', hαinv]
        exact hw1'
      have : w ∈ fixAutU3 z := hzw
      rwa [hzfix] at this
    have hcard : Nat.card (fixAutU3 α) ≤ Nat.card (fixAutU3 (z * α * z⁻¹)) := by
      refine Nat.card_le_card_of_injective (fun w => ⟨z w, ?_⟩) fun u v huv => ?_
      · show (z * α * z⁻¹) (z w) = z w
        rw [MulAut.mul_apply, MulAut.mul_apply, ← MulAut.mul_apply _ z⁻¹ z, inv_mul_cancel,
          MulAut.one_apply, show α w = w from w.2]
      · exact Subtype.ext (z.injective (congrArg Subtype.val huv))
    have h1 := card_mul_card_le_of_inf_eq_bot hinter
    rw [hW] at h1
    have h2 : Nat.card (fixAutU3 α) * Nat.card (fixAutU3 α) ≤ 2 ^ 6 :=
      (Nat.mul_le_mul_left _ hcard).trans h1
    rw [hj] at h2 ⊢
    rw [← pow_add] at h2
    have : j + j ≤ 6 := (Nat.pow_le_pow_iff_right (by norm_num)).1 h2
    calc 2 ^ j ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 16 := by norm_num

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem s1347_thompsonJ (S : A6.Setting134 G T L V) {H₁ H₂ : Subgroup G} (h : Hyp1347 T H₁ H₂)
    (hH₀ : InH T (H₁ ⊔ H₂)) (hc₁ : Nat.card ↥(cZ T H₁) = 2)
    (hT4 : Nat.card ↥T = 4 * Nat.card ↥(pCoreOf 2 (H₁ ⊔ H₂)))
    (hV64 : Nat.card ↥(v0Of T H₁ H₂) = 2 ^ 6) {z : MulAut ↥(v0Of T H₁ H₂)} (hz3 : z ^ 3 = 1)
    (hzfix : fixAutU3 z = ⊥)
    (hzn : ∀ β ∈ autOn (H₁ ⊔ H₂) (v0Of T H₁ H₂), β * z * β⁻¹ = z ∨ β * z * β⁻¹ = z⁻¹) :
    H₁ ⊔ H₂ ≤ normalizer (thompsonJ T : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hred := s1347_reduced S hH₀
  have hP : H₁ ⊔ H₂ ≤ normalizer (v0Of T H₁ H₂ : Set G) := hred.2.1
  have hW2 : ∀ w : ↥(v0Of T H₁ H₂), w ^ 2 = 1 := fun w => Subtype.ext (hred.2.2.1.2 w w.2)
  have hsyl₀ := A5.isSylowTwoOf_of_le S.h13.sylow hH₀.1
  have hTC := s1347_T_inf_centralizer S h hH₀
  have hVT : v0Of T H₁ H₂ ≤ T := s1347_V0_le_T S hH₀
  have hCZ : v0Of T H₁ H₂ ⊓ centralizer (T : Set G) ≤ quasithinOmegaOneCenter T :=
    fun x hx => subset_closure ⟨⟨hVT (mem_inf.1 hx).1, (mem_inf.1 hx).2⟩,
      hred.2.2.1.2 x (mem_inf.1 hx).1⟩
  have hZ4 : Nat.card ↥(quasithinOmegaOneCenter T) = 4 := by rw [h.index₁, hc₁]
  have hS4 : Nat.card ↥(autOn T (v0Of T H₁ H₂)) = 4 := by
    rw [card_autOn_eq_relIndex (hH₀.1.trans hP), hTC]
    have h1 := relIndex_mul_card (pCoreOf 2 (H₁ ⊔ H₂)) T
    rw [inf_eq_left.2 (pCoreOf_two_le_of_isSylowTwoOf hsyl₀), hT4] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  have hmod : ∀ A : Subgroup G, IsMaxElemAbelian T A →
      A ≤ centralizer (v0Of T H₁ H₂ : Set G) := by
    intro A hA
    by_contra hAC
    have hAH : A ≤ H₁ ⊔ H₂ := hA.1.trans hH₀.1
    have hineq := card_le_relIndex_mul_card hred.2.2.1 hVT hA
    rw [← card_autOn_eq_relIndex (hAH.trans hP), hV64] at hineq
    have hAS : autOn A (v0Of T H₁ H₂) ≤ autOn T (v0Of T H₁ H₂) := fun φ hφ => by
      obtain ⟨g, hg, rfl⟩ := Setup.mem_autOn_iff.1 hφ
      exact Setup.mem_autOn_iff.2 ⟨g, hA.1 hg, rfl⟩
    have hdvd : Nat.card ↥(autOn A (v0Of T H₁ H₂)) ∣ 4 := by
      rw [← hS4]
      exact card_dvd_of_le hAS
    have hρA : ∀ a (ha : a ∈ A), Setup.rho (v0Of T H₁ H₂) (H₁ ⊔ H₂) hP ⟨a, hAH ha⟩ ∈
        autOn A (v0Of T H₁ H₂) := fun a ha =>
      (Setup.mem_autOn_iff_rho hP hAH).2 ⟨⟨a, hAH ha⟩, ha, rfl⟩
    obtain ⟨a, ha, haC⟩ := IsConcreteLE.not_le_iff_exists.1 hAC
    have hα1 : Setup.rho (v0Of T H₁ H₂) (H₁ ⊔ H₂) hP ⟨a, hAH ha⟩ ≠ 1 := fun h1 =>
      haC ((Setup.rho_eq_one_iff hP _).1 h1)
    have hA1 : Nat.card ↥(autOn A (v0Of T H₁ H₂)) ≠ 1 := fun h1 => by
      have := hρA a ha
      rw [card_eq_one.1 h1, mem_bot] at this
      exact hα1 this
    rcases (Nat.dvd_prime_pow Nat.prime_two).1 (show Nat.card ↥(autOn A (v0Of T H₁ H₂)) ∣ 2 ^ 2
      from hdvd) with ⟨e, he, hce⟩
    interval_cases e
    · exact hA1 (by rw [hce, pow_zero])
    ·
      rw [pow_one] at hce
      set α := Setup.rho (v0Of T H₁ H₂) (H₁ ⊔ H₂) hP ⟨a, hAH ha⟩ with hαdef
      have hα2 : α ^ 2 = 1 := sq_eq_one_of_card_le_two hce.le (hρA a ha)
      have hαX : α ∈ autOn (H₁ ⊔ H₂) (v0Of T H₁ H₂) :=
        (Setup.mem_autOn_self_iff hP).2 ⟨_, rfl⟩
      have h16 := card_fixAutU3_le_sixteen hW2 hV64 hz3 hzfix hα1 hα2 (hzn α hαX)
      have hle : v0Of T H₁ H₂ ⊓ centralizer (A : Set G) ≤
          (fixAutU3 α).map (v0Of T H₁ H₂).subtype := by
        intro v hv
        obtain ⟨hvV, hvA⟩ := mem_inf.1 hv
        refine ⟨⟨v, hvV⟩, ?_, rfl⟩
        show α ⟨v, hvV⟩ = ⟨v, hvV⟩
        apply Subtype.ext
        rw [hαdef, Setup.rho_apply_coe]
        show a * v * a⁻¹ = v
        rw [(mem_centralizer_iff.1 hvA) a ha, mul_inv_cancel_right]
      have h1 : Nat.card ↥(v0Of T H₁ H₂ ⊓ centralizer (A : Set G)) ≤ 16 := by
        refine (card_le_of_le hle).trans ?_
        rw [card_map_of_injective (v0Of T H₁ H₂).subtype_injective]
        exact h16
      rw [hce] at hineq
      have : 2 ^ 6 ≤ 2 * 16 := hineq.trans (Nat.mul_le_mul_left _ h1)
      norm_num at this
    ·
      have hAeq : autOn A (v0Of T H₁ H₂) = autOn T (v0Of T H₁ H₂) :=
        eq_of_le_of_card_ge hAS (by rw [hS4, hce]; norm_num)
      have hle : v0Of T H₁ H₂ ⊓ centralizer (A : Set G) ≤
          v0Of T H₁ H₂ ⊓ centralizer (T : Set G) := by
        intro v hv
        obtain ⟨hvV, hvA⟩ := mem_inf.1 hv
        refine mem_inf.2 ⟨hvV, mem_centralizer_iff.2 fun t ht => ?_⟩
        have htA : Setup.rho (v0Of T H₁ H₂) (H₁ ⊔ H₂) hP ⟨t, hH₀.1 ht⟩ ∈
            autOn A (v0Of T H₁ H₂) := by
          rw [hAeq]
          exact (Setup.mem_autOn_iff_rho hP hH₀.1).2 ⟨⟨t, hH₀.1 ht⟩, ht, rfl⟩
        obtain ⟨b, hbA, hbt⟩ := (Setup.mem_autOn_iff_rho hP hAH).1 htA
        have h1 : (b : G) * v * (b : G)⁻¹ = t * v * t⁻¹ := by
          have := congrArg (fun φ : MulAut ↥(v0Of T H₁ H₂) =>
            ((φ ⟨v, hvV⟩ : ↥(v0Of T H₁ H₂)) : G)) hbt
          simpa only [Setup.rho_apply_coe] using this
        have h2 := (mem_centralizer_iff.1 hvA) (b : G) hbA
        have h3 : t * v * t⁻¹ = v := by
          rw [← h1, h2, mul_inv_cancel_right]
        calc t * v = (t * v * t⁻¹) * t := by group
          _ = v * t := by rw [h3]
      have h1 := (card_le_of_le (hle.trans hCZ)).trans hZ4.le
      rw [hce] at hineq
      have : 2 ^ 6 ≤ 2 ^ 2 * 4 := hineq.trans (Nat.mul_le_mul_left _ h1)
      norm_num at this
  have hJ : thompsonJ T ≤ pCoreOf 2 (H₁ ⊔ H₂) := by
    rw [← hTC]
    exact iSup₂_le fun A hA => le_inf hA.1 (hmod A hA)
  have hJeq := B6.thompsonJ_eq_of_le hJ (pCoreOf_two_le_of_isSylowTwoOf hsyl₀)
  rw [← hJeq]
  exact (le_normalizer_pCoreOf 2 (H₁ ⊔ H₂)).trans (normalizer_le_normalizer_thompsonJ _)

end CFSG.Quasithin.H13.U3
