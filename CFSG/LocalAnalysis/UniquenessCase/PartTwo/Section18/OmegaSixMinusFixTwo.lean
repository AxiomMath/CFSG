module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16OFixW

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup
open scoped Pointwise commutatorElement Matrix

open CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.LocalAnalysis.RankThreeUC
open TauCeti.QuadraticMap (orthogonalGroup)
open CFSG.LieType.Universal.Spin
  (quadMinus coe_quadMinus nondegenerate_polarBilin_quadMinus_of_finite)

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}

theorem exists_order_p_fix_std (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n) {p : ℕ} (hp : p.Prime)
    (hpq : p ∣ Nat.card F + 1) :
    ∃ g₀ ∈ StatedOmega (StatedQuadMinus 3 F b c), orderOf g₀ = p ∧
      ∀ w : OW F, w (Sum.inr (Sum.inr 0)) = 0 → w (Sum.inr (Sum.inr 1)) = 0 →
        ((g₀ : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
          Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ w =
            w := by
  have hb : b ≠ 0 := ne_zero_of_irred hirr
  have : Fact (∀ r : F, r ^ 2 ≠ -c + b * r) := factRoot hirr
  have : Finite (QA b c) := Finite.of_equiv (F × F) (QuadraticAlgebra.equivProd (-c) b).symm
  have : Fact p.Prime := ⟨hp⟩
  have hodd : Odd (Nat.card F + 1) := by
    rw [hF]
    exact Even.add_one (Nat.even_pow.mpr ⟨even_two, by omega⟩)
  have hcardQA : Nat.card (QA b c) = Nat.card F ^ 2 := by
    rw [Nat.card_congr (QuadraticAlgebra.equivProd (-c) b), Nat.card_prod, _root_.sq]
  have hq : 1 ≤ Nat.card F := Nat.card_pos
  have hdvd : p ∣ Nat.card (QA b c)ˣ := by
    rw [Nat.card_units, hcardQA, CFSG.ClassicalGroups.Unitary.sq_sub_one_eq (Nat.card F) hq]
    exact Dvd.dvd.mul_right hpq _
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := (QA b c)ˣ) p hdvd
  have hζmem : ζ ∈ Mu b c := by
    rw [mem_rootsOfUnity]
    exact orderOf_dvd_iff_pow_eq_one.mp (hζ ▸ hpq)
  let t : ↥(Mu b c) × ↥(Mu b c) × ↥(Mu b c) := (1, 1, ⟨ζ, hζmem⟩)
  have hinj : Function.Injective (tauGL (c := c) hb) := by
    intro s s' h
    apply Tau_injective hb
    exact (toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F).symm.injective h
  have hot : orderOf (tauGL hb t) = p := by
    rw [orderOf_injective _ hinj t]
    simp only [t, Prod.orderOf_mk, orderOf_one, Nat.lcm_one_left, Subgroup.orderOf_mk, hζ]
  refine ⟨tauGL hb t, ?_, hot, ?_⟩
  · refine odd_isometry_mem_omega hirr (fun v => ?_) (hot ▸ Odd.of_dvd_nat hodd hpq)
    rw [tauGL_mulVec, ← coe_quadMinus 3 F b c]
    exact quad_Tau hb t v
  · intro w h0 h1
    rw [tauGL_mulVec]
    apply (Tequiv (c := c) hb).injective
    rw [Tequiv_Tau]
    have h2 : Tequiv (c := c) hb w 2 = 0 := by
      show (⟨w (Sum.inr (Sum.inr 0)), w (Sum.inr (Sum.inr 1))⟩ : QA b c) = 0
      rw [h0, h1]
      rfl
    funext i
    fin_cases i <;> simp [t, triMul_apply, h2]

theorem conj_mulVec_fix {ι : Type} [Fintype ι] [DecidableEq ι] {G₀ g₀ : GL ι F} {x' x : ι → F}
    (hG : (G₀ : Matrix ι ι F) *ᵥ x' = x) (hg : (g₀ : Matrix ι ι F) *ᵥ x' = x') :
    ((G₀ * g₀ * G₀⁻¹ : GL ι F) : Matrix ι ι F) *ᵥ x = x := by
  have h1 : ((G₀⁻¹ : GL ι F) : Matrix ι ι F) * (G₀ : Matrix ι ι F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [← hG, Matrix.mulVec_mulVec, Units.val_mul, Units.val_mul, Matrix.mul_assoc, Matrix.mul_assoc,
    h1, Matrix.mul_one, ← Matrix.mulVec_mulVec, hg]

@[expose] def stdOne (a : F) : OW F :=
  Sum.elim (Pi.single idx0 1) (Sum.elim (Pi.single idx0 a) 0)

@[expose] def stdTwo (d a : F) : OW F :=
  Sum.elim (Pi.single idx1 1) (Sum.elim (fun j => if j = idx0 then d else a) 0)

theorem quad_stdOne (a : F) : StatedQuadMinus 3 F b c (stdOne a) = a := by
  rw [← quadMinus_eq_stated, CFSG.LieType.Universal.Spin.quadMinus_apply,
    Fin.sum_univ_two (fun i : Fin 2 => stdOne a (Sum.inl i) * stdOne a (Sum.inr (Sum.inl i)))]
  simp [stdOne, idx0, Pi.single_apply]

theorem quad_stdTwo (d a : F) : StatedQuadMinus 3 F b c (stdTwo d a) = a := by
  rw [← quadMinus_eq_stated, CFSG.LieType.Universal.Spin.quadMinus_apply,
    Fin.sum_univ_two (fun i : Fin 2 => stdTwo d a (Sum.inl i) * stdTwo d a (Sum.inr (Sum.inl i)))]
  simp [stdTwo, idx0, idx1, Pi.single_apply]

theorem polar_stdOne_stdTwo (a d a' : F) :
    polar (quadMinus 3 F b c) (stdOne a) (stdTwo d a') = d := by
  rw [CFSG.LieType.Universal.Spin.polar_quadMinus,
    Fin.sum_univ_two (fun i : Fin 2 => stdOne a (Sum.inl i) * stdTwo d a' (Sum.inr (Sum.inl i)) +
      stdTwo d a' (Sum.inl i) * stdOne a (Sum.inr (Sum.inl i)))]
  simp [stdOne, stdTwo, idx0, idx1, Pi.single_apply]

theorem stdOne_ne_zero (a : F) : stdOne a ≠ 0 := by
  intro h
  have := congrFun h (Sum.inl idx0)
  simp [stdOne] at this

theorem linearIndependent_std (a d a' : F) :
    LinearIndependent F ![stdOne a, stdTwo d a'] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h0 := congrFun hst (Sum.inl idx0)
  have h1 := congrFun hst (Sum.inl idx1)
  simp [stdOne, stdTwo, idx0, idx1, Pi.single_apply] at h0 h1
  exact ⟨h0, h1⟩

theorem stdOne_inr_inr (a : F) (j : Fin 2) : stdOne a (Sum.inr (Sum.inr j)) = 0 := rfl

theorem stdTwo_inr_inr (d a : F) (j : Fin 2) : stdTwo d a (Sum.inr (Sum.inr j)) = 0 := rfl

theorem conj_mem_order (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {h : OW F ≃ₗ[F] OW F} (hh : h ∈ orthogonalGroup (quadMinus 3 F b c))
    {g₀ : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F}
    (hg₀ : g₀ ∈ StatedOmega (StatedQuadMinus 3 F b c)) :
    let G₀ := (toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F).symm h
    G₀ * g₀ * G₀⁻¹ ∈ StatedOmega (StatedQuadMinus 3 F b c) ∧
      orderOf (G₀ * g₀ * G₀⁻¹) = orderOf g₀ ∧
      ∀ v, ((G₀ : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
        Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ v =
          h v := by
  intro G₀
  refine ⟨conj_mem_statedOmega hirr (by simp only [G₀, MulEquiv.apply_symm_apply]; exact hh)
    hg₀, ?_, fun v => ?_⟩
  · rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
  · rw [← toLinEquiv_apply, MulEquiv.apply_symm_apply]

theorem exists_fix_two (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n) {p : ℕ} (hp : p.Prime)
    (hpq : p ∣ Nat.card F + 1) (x y : OW F) :
    ∃ g ∈ StatedOmega (StatedQuadMinus 3 F b c), orderOf g = p ∧
      ((g : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
          Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ x =
            x ∧
      ((g : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
          Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ y =
            y := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hQn := nondegenerate_polarBilin_quadMinus_of_finite 3 F hirr
  obtain ⟨g₀, hg₀Ω, hg₀p, hg₀fix⟩ := exists_order_p_fix_std hirr hF hn hp hpq
  have hone : ∀ z : OW F, ∃ g ∈ StatedOmega (StatedQuadMinus 3 F b c), orderOf g = p ∧
      ((g : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
        Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ z =
          z := by
    intro z
    by_cases hz : z = 0
    · exact ⟨g₀, hg₀Ω, hg₀p, by rw [hz, Matrix.mulVec_zero]⟩
    obtain ⟨h, hh, hhz⟩ := exists_isometry_apply_eq hirr (stdOne_ne_zero _) hz
      (quad_stdOne (b := b) (c := c) (StatedQuadMinus 3 F b c z)).symm
    obtain ⟨hmem, hord, happ⟩ := conj_mem_order hirr hh hg₀Ω
    exact ⟨_, hmem, hord.trans hg₀p, conj_mulVec_fix ((happ _).trans hhz)
      (hg₀fix _ (stdOne_inr_inr _ 0) (stdOne_inr_inr _ 1))⟩
  by_cases hli : LinearIndependent F ![x, y]
  · obtain ⟨h, hh, hhu⟩ := CFSG.RankThree.OrthogonalInvolutions.exists_mem_orthogonalGroup_apply_eq
      hQn (k := 2) ![stdOne (StatedQuadMinus 3 F b c x),
        stdTwo (polar (quadMinus 3 F b c) x y) (StatedQuadMinus 3 F b c y)] ![x, y]
      (linearIndependent_std _ _ _) hli
      (fun i => by
        fin_cases i
        · show quadMinus 3 F b c x = quadMinus 3 F b c (stdOne (StatedQuadMinus 3 F b c x))
          rw [quadMinus_eq_stated, quadMinus_eq_stated, quad_stdOne]
        · show quadMinus 3 F b c y = quadMinus 3 F b c
            (stdTwo (polar (quadMinus 3 F b c) x y) (StatedQuadMinus 3 F b c y))
          rw [quadMinus_eq_stated, quadMinus_eq_stated, quad_stdTwo])
      (fun i j => by
        fin_cases i <;> fin_cases j
        · show polar (quadMinus 3 F b c) x x =
            polar (quadMinus 3 F b c) (stdOne _) (stdOne _)
          rw [polar_self_eq_two_mul, polar_self_eq_two_mul, h2, zero_mul, zero_mul]
        · show polar (quadMinus 3 F b c) x y =
            polar (quadMinus 3 F b c) (stdOne _) (stdTwo _ _)
          rw [polar_stdOne_stdTwo]
        · show polar (quadMinus 3 F b c) y x =
            polar (quadMinus 3 F b c) (stdTwo _ _) (stdOne _)
          rw [polar_comm (quadMinus 3 F b c) (stdTwo _ _), polar_stdOne_stdTwo, polar_comm]
        · show polar (quadMinus 3 F b c) y y =
            polar (quadMinus 3 F b c) (stdTwo _ _) (stdTwo _ _)
          rw [polar_self_eq_two_mul, polar_self_eq_two_mul, h2, zero_mul, zero_mul])
    have hx' : h (stdOne (StatedQuadMinus 3 F b c x)) = x := hhu 0
    have hy' : h (stdTwo (polar (quadMinus 3 F b c) x y) (StatedQuadMinus 3 F b c y)) = y :=
      hhu 1
    obtain ⟨hmem, hord, happ⟩ := conj_mem_order hirr hh hg₀Ω
    refine ⟨_, hmem, hord.trans hg₀p, ?_, ?_⟩
    · exact conj_mulVec_fix ((happ _).trans hx')
        (hg₀fix _ (stdOne_inr_inr _ 0) (stdOne_inr_inr _ 1))
    · exact conj_mulVec_fix ((happ _).trans hy')
        (hg₀fix _ (stdTwo_inr_inr _ _ 0) (stdTwo_inr_inr _ _ 1))
  · rw [LinearIndependent.pair_iff] at hli
    push Not at hli
    obtain ⟨s, t, hst, hne⟩ := hli
    by_cases ht : t = 0
    · have hs : s ≠ 0 := fun h => hne h ht
      have hx0 : x = 0 := by
        rw [ht, zero_smul, add_zero] at hst
        exact (smul_eq_zero.mp hst).resolve_left hs
      obtain ⟨g, hg, hgo, hgy⟩ := hone y
      exact ⟨g, hg, hgo, by rw [hx0, Matrix.mulVec_zero], hgy⟩
    · have hy : y = (-(t⁻¹ * s)) • x := by
        have h' : t • y = -(s • x) := eq_neg_of_add_eq_zero_right hst
        calc y = t⁻¹ • (t • y) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
          _ = (-(t⁻¹ * s)) • x := by rw [h', smul_neg, smul_smul, neg_smul]
      obtain ⟨g, hg, hgo, hgx⟩ := hone x
      exact ⟨g, hg, hgo, hgx, by rw [hy, Matrix.mulVec_smul, hgx]⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
