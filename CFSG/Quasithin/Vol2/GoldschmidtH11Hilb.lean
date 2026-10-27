module

public import CFSG.Quasithin.Vol2.GoldschmidtH11Tau

public section

open scoped Matrix MatrixGroups

namespace CFSG.Quasithin.H11

variable {F : Type} [Field F] [Finite F] [CharP F 2] {a : ℕ}

theorem isCyclic_ringEquiv : IsCyclic (F ≃+* F) := by
  have : Fintype F := Fintype.ofFinite F
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let e : (F ≃+* F) ≃* (F ≃ₐ[ZMod 2] F) :=
    { toFun := fun sigma => AlgEquiv.ofRingEquiv (f := sigma) (by
        intro x
        have h : (sigma.toRingHom.comp (algebraMap (ZMod 2) F) : ZMod 2 →+* F) =
            algebraMap (ZMod 2) F := RingHom.ext_zmod _ _
        exact DFunLike.congr_fun h x)
      invFun := fun sigma => sigma.toRingEquiv
      left_inv := by intro sigma; ext x; rfl
      right_inv := by intro sigma; ext x; rfl
      map_mul' := by intro sigma tau; ext x; rfl }
  exact e.isCyclic.mpr inferInstance

theorem eq_one_or_eq_sgEquiv (ha : 0 < a) (h : Nat.card F = 2 ^ (2 * a)) (ψ : F ≃+* F)
    (hψ : ψ * ψ = 1) : ψ = 1 ∨ ψ = sgEquiv a h := by
  classical
  have hcyc : IsCyclic (F ≃+* F) := isCyclic_ringEquiv
  have hσ2 : sgEquiv a h * sgEquiv a h = 1 :=
    RingEquiv.ext fun x => sg_sg a h x
  have hσ1 : sgEquiv a h ≠ 1 := by
    obtain ⟨x, hx⟩ := exists_sg_ne a ha h
    intro h1
    exact hx (by simpa [sgEquiv_apply] using congrArg (fun e : F ≃+* F => e x) h1)
  have hfin : Finite (F ≃+* F) :=
    Finite.of_injective (fun e : F ≃+* F => (e : F → F)) DFunLike.coe_injective
  have : Fintype (F ≃+* F) := Fintype.ofFinite _
  by_contra hcon
  push Not at hcon
  have hsub : ({1, sgEquiv a h, ψ} : Finset (F ≃+* F)) ⊆
      Finset.univ.filter (fun x : F ≃+* F => x ^ 2 = 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl | rfl
    · simp
    · simpa [pow_two] using hσ2
    · simpa [pow_two] using hψ
  have h3 := Finset.card_le_card hsub
  have h2 := IsCyclic.card_pow_eq_one_le (α := F ≃+* F) (n := 2) (by norm_num)
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton] at h3
  · omega
  · simpa using hcon.2.symm
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hσ1.symm, hcon.1.symm⟩

theorem sgMap_apply (h : Nat.card F = 2 ^ (2 * a)) (γ : SL(2, F)) (i j : Fin 2) :
    (sgMap h γ : Matrix (Fin 2) (Fin 2) F) i j = sg a ((γ : Matrix (Fin 2) (Fin 2) F) i j) := rfl

theorem hilbert90 (ha : 0 < a) (h : Nat.card F = 2 ^ (2 * a)) (g : SL(2, F))
    (hg : g * sgMap h g = 1) : ∃ k : SL(2, F), g = k * (sgMap h k)⁻¹ := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hinv : sgMap h g = g⁻¹ := eq_inv_of_mul_eq_one_right hg
  have hadj : ((g⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      !![(g : Matrix (Fin 2) (Fin 2) F) 1 1, -(g : Matrix (Fin 2) (Fin 2) F) 0 1;
        -(g : Matrix (Fin 2) (Fin 2) F) 1 0, (g : Matrix (Fin 2) (Fin 2) F) 0 0] := by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  have e00 : sg a ((g : Matrix (Fin 2) (Fin 2) F) 0 0) = (g : Matrix (Fin 2) (Fin 2) F) 1 1 := by
    have := congrFun (congrFun (congrArg Subtype.val hinv) 0) 0
    rw [sgMap_apply, hadj] at this
    simpa using this
  have e11 : sg a ((g : Matrix (Fin 2) (Fin 2) F) 1 1) = (g : Matrix (Fin 2) (Fin 2) F) 0 0 := by
    have := congrFun (congrFun (congrArg Subtype.val hinv) 1) 1
    rw [sgMap_apply, hadj] at this
    simpa using this
  have e01 : sg a ((g : Matrix (Fin 2) (Fin 2) F) 0 1) = (g : Matrix (Fin 2) (Fin 2) F) 0 1 := by
    have := congrFun (congrFun (congrArg Subtype.val hinv) 0) 1
    rw [sgMap_apply, hadj] at this
    simp at this
    linear_combination this - (g : Matrix (Fin 2) (Fin 2) F) 0 1 * h2
  have e10 : sg a ((g : Matrix (Fin 2) (Fin 2) F) 1 0) = (g : Matrix (Fin 2) (Fin 2) F) 1 0 := by
    have := congrFun (congrFun (congrArg Subtype.val hinv) 1) 0
    rw [sgMap_apply, hadj] at this
    simp at this
    linear_combination this - (g : Matrix (Fin 2) (Fin 2) F) 1 0 * h2
  have hdet := g.2
  rw [Matrix.det_fin_two] at hdet
  set p := (g : Matrix (Fin 2) (Fin 2) F) 0 0 with hp
  set q := (g : Matrix (Fin 2) (Fin 2) F) 0 1 with hq
  set r := (g : Matrix (Fin 2) (Fin 2) F) 1 0 with hr
  set s := (g : Matrix (Fin 2) (Fin 2) F) 1 1 with hs
  have hex : ∃ c : F, c ^ 2 + c * sg a c * (p + s) + sg a c ^ 2 ≠ 0 := by
    by_cases hT : p + s = 0
    · obtain ⟨x, hx⟩ := exists_sg_ne a ha h
      refine ⟨x, ?_⟩
      rw [hT, mul_zero, add_zero]
      intro h0
      apply hx
      have h3 : (x + sg a x) ^ 2 = 0 := by linear_combination h0 + (x * sg a x) * h2
      have h4 := pow_eq_zero_iff (two_ne_zero) |>.mp h3
      linear_combination h4 - x * h2
    · refine ⟨1, ?_⟩
      simp only [map_one, one_pow, mul_one, one_mul]
      intro h0
      apply hT
      linear_combination h0 - h2
  obtain ⟨c, hc⟩ := hex
  have hσD : sg a (c ^ 2 + c * sg a c * (p + s) + sg a c ^ 2) =
      c ^ 2 + c * sg a c * (p + s) + sg a c ^ 2 := by
    simp only [map_add, map_mul, map_pow, sg_sg a h, e00, e11]
    ring
  obtain ⟨ρ, hρσ, hρ⟩ : ∃ ρ : F, sg a ρ = ρ ∧
      ρ ^ 2 * (c ^ 2 + c * sg a c * (p + s) + sg a c ^ 2) = 1 := by
    set D := c ^ 2 + c * sg a c * (p + s) + sg a c ^ 2 with hD
    have hD0 : D ≠ 0 := hc
    have hsq : (D ^ 2 ^ (a - 1)) ^ 2 = D := by
      rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel ha]
      exact hσD
    have hσr : sg a (D ^ 2 ^ (a - 1)) = D ^ 2 ^ (a - 1) := by rw [map_pow, hσD]
    have hr0 : D ^ 2 ^ (a - 1) ≠ 0 := pow_ne_zero _ hD0
    refine ⟨(D ^ 2 ^ (a - 1))⁻¹, by rw [map_inv₀, hσr], ?_⟩
    rw [inv_pow, hsq, inv_mul_cancel₀ hD0]
  have hk₁ : (!![ρ * (c + sg a c * p), ρ * (sg a c * q); ρ * (sg a c * r),
      ρ * (c + sg a c * s)] : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    rw [Matrix.det_fin_two_of]
    linear_combination hρ + (ρ ^ 2 * sg a c ^ 2) * hdet
  obtain ⟨k, hkc⟩ : ∃ k : SL(2, F), (k : Matrix (Fin 2) (Fin 2) F) =
      !![ρ * (c + sg a c * p), ρ * (sg a c * q); ρ * (sg a c * r), ρ * (c + sg a c * s)] :=
    ⟨⟨_, hk₁⟩, rfl⟩
  refine ⟨k, ?_⟩
  rw [eq_mul_inv_iff_mul_eq]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, sgMap_apply, hkc, map_mul, map_add, sg_sg a h, hρσ,
      e00, e11, e01, e10]
  · linear_combination (ρ * c) * hdet + (ρ * c * q * r) * h2
  · linear_combination (ρ * c * p * q) * h2
  · linear_combination (ρ * c * r * s) * h2
  · linear_combination (ρ * c) * hdet + (ρ * c * q * r) * h2

end CFSG.Quasithin.H11
