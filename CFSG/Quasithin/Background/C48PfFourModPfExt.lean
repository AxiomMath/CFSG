module

public import CFSG.Quasithin.Background.C48PfFourModPfMat
public import CFSG.Quasithin.Background.C48PfFourModPfSub

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.C48Pf.FMod

open Matrix CFSG.QuasithinUnique.Vol2Native.A312L

theorem altVec3_congr_adj (g : Matrix (Fin 3) (Fin 3) (ZMod 2))
    {N : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hN : N ∈ altMat 3) :
    altVec3 (g * N * gᵀ) = (adjugate g)ᵀ *ᵥ altVec3 N := by
  rw [Matrix.adjugate_fin_three, alt3_eq hN]
  ext i
  fin_cases i <;>
  · simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    simp [altVec3, Matrix.mul_apply, Fin.sum_univ_three, Matrix.mulVec, dotProduct]
    simp only [CharTwo.sub_eq_add]
    ring

variable {W : Type*} [CommGroup W] {n : ℕ} {ρ : SpecialLinearGroup (Fin n) (ZMod 2) →* MulAut W}
  {J : Subgroup W} {Φ : ↥J →* Multiplicative (Matrix (Fin n) (Fin n) (ZMod 2))}

theorem extSq_coord_fixed
    (hΦ : ∀ (h : SpecialLinearGroup (Fin n) (ZMod 2)) (u : ↥J) (hu : ρ h u ∈ J),
      Multiplicative.toAdd (Φ ⟨ρ h u, hu⟩) = (h : Matrix (Fin n) (Fin n) (ZMod 2)) *
        Multiplicative.toAdd (Φ u) * (h : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ)
    {k l : Fin n} (hkl : k ≠ l) (u : ↥J)
    (hfix : ρ (SpecialLinearGroup.transvection hkl (1 : ZMod 2)) u = u) :
    tvM k l * Multiplicative.toAdd (Φ u) * (tvM k l)ᵀ = Multiplicative.toAdd (Φ u) := by
  have h1 := hΦ (SpecialLinearGroup.transvection hkl (1 : ZMod 2)) u (by rw [hfix]; exact u.2)
  have h2 : (⟨ρ (SpecialLinearGroup.transvection hkl (1 : ZMod 2)) u, by rw [hfix]; exact u.2⟩ :
      ↥J) = u := Subtype.ext hfix
  rw [h2, CFSG.LinearGroups.coe_transvection] at h1
  exact h1.symm

section Main

variable (hΦalt : ∀ u, Multiplicative.toAdd (Φ u) ∈ altMat n)
  (hΦinj : Function.Injective Φ)
  (hΦ : ∀ (h : SpecialLinearGroup (Fin n) (ZMod 2)) (u : ↥J) (hu : ρ h u ∈ J),
    Multiplicative.toAdd (Φ ⟨ρ h u, hu⟩) = (h : Matrix (Fin n) (Fin n) (ZMod 2)) *
      Multiplicative.toAdd (Φ u) * (h : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ)
  {A : Subgroup (SpecialLinearGroup (Fin n) (ZMod 2))} {V : Subgroup W} (hVJ : V ≤ J)

include hΦalt hΦinj hΦ hVJ

theorem extSq_zero_three (h0 : 0 + 3 ≤ n)
    (hcross : ∀ (k l : Fin n) (hc : IsCross 0 3 k l), ∀ v ∈ V,
      ρ (SpecialLinearGroup.transvection hc.ne (1 : ZMod 2)) v = v) :
    ∃ Ψ : ↥V →* Multiplicative (Fin 1 → Fin 3 → ZMod 2), Function.Injective Ψ ∧
      ∀ t ∈ A, ∀ (v : ↥V) (hv : ρ t v ∈ V),
        Multiplicative.toAdd (Ψ ⟨ρ t v, hv⟩) =
          diagAct (adjugate (blkAt 0 3 h0 (t : Matrix (Fin n) (Fin n) (ZMod 2))))ᵀ
            (Multiplicative.toAdd (Ψ v)) := by
  let ι : ↥V →* ↥J := Subgroup.inclusion hVJ
  let M : ↥V → Matrix (Fin n) (Fin n) (ZMod 2) := fun v => Multiplicative.toAdd (Φ (ι v))
  have hsupp : ∀ (v : ↥V) (i j : Fin n), (3 ≤ (i : ℕ) ∨ 3 ≤ (j : ℕ)) → M v i j = 0 :=
    fun v => alt_support_zero (by norm_num) (hΦalt _) fun k l hc =>
      extSq_coord_fixed hΦ hc.ne (ι v) (hcross k l hc v v.2)
  have hblkalt : ∀ v : ↥V, blkAt 0 3 h0 (M v) ∈ altMat 3 := fun v =>
    ⟨by ext i j; exact (alt_symm (hΦalt (ι v)) _ _), fun i => (hΦalt (ι v)).2 _⟩
  refine ⟨{ toFun := fun v => Multiplicative.ofAdd fun _ => altVec3 (blkAt 0 3 h0 (M v))
            map_one' := by
              apply Multiplicative.toAdd.injective
              funext i j
              fin_cases j <;> simp [M, altVec3, blkAt_apply]
            map_mul' := fun u v => by
              apply Multiplicative.toAdd.injective
              funext i j
              fin_cases j <;> simp [M, altVec3, blkAt_apply, map_mul] }, ?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro v hv
    have hv' := congrFun (congrArg Multiplicative.toAdd hv) 0
    simp only [MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd, toAdd_one, Pi.zero_apply] at hv'
    have hb : blkAt 0 3 h0 (M v) = 0 := by
      have e : ∀ i, altVec3 (blkAt 0 3 h0 (M v)) i = 0 := fun i => congrFun hv' i
      have e0 : blkAt 0 3 h0 (M v) 1 2 = 0 := e 0
      have e1 : blkAt 0 3 h0 (M v) 0 2 = 0 := e 1
      have e2 : blkAt 0 3 h0 (M v) 0 1 = 0 := e 2
      rw [alt3_eq (hblkalt v), e0, e1, e2]
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    have hM0 : M v = 0 := by
      ext i j
      by_cases hij : 3 ≤ (i : ℕ) ∨ 3 ≤ (j : ℕ)
      · exact hsupp v i j hij
      · have := congrFun (congrFun hb ⟨i, by omega⟩) ⟨j, by omega⟩
        simpa [blkAt_apply] using this
    have h1 : Φ (ι v) = 1 := Multiplicative.toAdd.injective hM0
    have h2 : ι v = 1 := hΦinj (by rw [h1, map_one])
    apply Subtype.ext
    simpa [ι] using congrArg Subtype.val h2
  · intro t ht v hv
    funext i
    show altVec3 (blkAt 0 3 h0 (M ⟨ρ t v, hv⟩)) = (adjugate (blkAt 0 3 h0
      (t : Matrix (Fin n) (Fin n) (ZMod 2))))ᵀ *ᵥ altVec3 (blkAt 0 3 h0 (M v))
    have hMt : M ⟨ρ t v, hv⟩ = (t : Matrix (Fin n) (Fin n) (ZMod 2)) * M v *
        (t : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ := hΦ t (ι v) (hVJ hv)
    rw [hMt, blkAt_congr_of_support h0 _ (hsupp v)]
    exact altVec3_congr_adj _ (hblkalt v)

theorem extSq_zero_four (h0 : 0 + 4 ≤ n)
    (hcross : ∀ (k l : Fin n) (hc : IsCross 0 4 k l), ∀ v ∈ V,
      ρ (SpecialLinearGroup.transvection hc.ne (1 : ZMod 2)) v = v) :
    ∃ Ψ : ↥V →* Multiplicative (Fin 6 → ZMod 2), Function.Injective Ψ ∧
      ∀ t ∈ A, ∀ (v : ↥V) (hv : ρ t v ∈ V),
        Multiplicative.toAdd (Ψ ⟨ρ t v, hv⟩) =
          minors4 (blkAt 0 4 h0 (t : Matrix (Fin n) (Fin n) (ZMod 2))) *ᵥ
            Multiplicative.toAdd (Ψ v) := by
  let ι : ↥V →* ↥J := Subgroup.inclusion hVJ
  let M : ↥V → Matrix (Fin n) (Fin n) (ZMod 2) := fun v => Multiplicative.toAdd (Φ (ι v))
  have hsupp : ∀ (v : ↥V) (i j : Fin n), (4 ≤ (i : ℕ) ∨ 4 ≤ (j : ℕ)) → M v i j = 0 :=
    fun v => alt_support_zero (by norm_num) (hΦalt _) fun k l hc =>
      extSq_coord_fixed hΦ hc.ne (ι v) (hcross k l hc v v.2)
  have hblkalt : ∀ v : ↥V, blkAt 0 4 h0 (M v) ∈ altMat 4 := fun v =>
    ⟨by ext i j; exact (alt_symm (hΦalt (ι v)) _ _), fun i => (hΦalt (ι v)).2 _⟩
  refine ⟨{ toFun := fun v => Multiplicative.ofAdd (altCoords4 (blkAt 0 4 h0 (M v)))
            map_one' := by
              apply Multiplicative.toAdd.injective
              funext k
              simp [M, altCoords4, blkAt_apply]
            map_mul' := fun u v => by
              apply Multiplicative.toAdd.injective
              funext k
              simp [M, altCoords4, blkAt_apply, map_mul] }, ?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro v hv
    have hv' := congrArg Multiplicative.toAdd hv
    simp only [MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd, toAdd_one] at hv'
    have hb : blkAt 0 4 h0 (M v) = 0 := by
      have hc : ∀ k : Fin 6, altCoords4 (blkAt 0 4 h0 (M v)) k = 0 := fun k => congrFun hv' k
      have e0 : blkAt 0 4 h0 (M v) 0 1 = 0 := hc 0
      have e1 : blkAt 0 4 h0 (M v) 0 2 = 0 := hc 1
      have e2 : blkAt 0 4 h0 (M v) 0 3 = 0 := hc 2
      have e3 : blkAt 0 4 h0 (M v) 1 2 = 0 := hc 3
      have e4 : blkAt 0 4 h0 (M v) 1 3 = 0 := hc 4
      have e5 : blkAt 0 4 h0 (M v) 2 3 = 0 := hc 5
      rw [alt4_eq (hblkalt v), e0, e1, e2, e3, e4, e5]
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    have hM0 : M v = 0 := by
      ext i j
      by_cases hij : 4 ≤ (i : ℕ) ∨ 4 ≤ (j : ℕ)
      · exact hsupp v i j hij
      · have := congrFun (congrFun hb ⟨i, by omega⟩) ⟨j, by omega⟩
        simpa [blkAt_apply] using this
    have h1 : Φ (ι v) = 1 := Multiplicative.toAdd.injective hM0
    have h2 : ι v = 1 := hΦinj (by rw [h1, map_one])
    apply Subtype.ext
    simpa [ι] using congrArg Subtype.val h2
  · intro t ht v hv
    show altCoords4 (blkAt 0 4 h0 (M ⟨ρ t v, hv⟩)) = minors4 (blkAt 0 4 h0
      (t : Matrix (Fin n) (Fin n) (ZMod 2))) *ᵥ altCoords4 (blkAt 0 4 h0 (M v))
    have hMt : M ⟨ρ t v, hv⟩ = (t : Matrix (Fin n) (Fin n) (ZMod 2)) * M v *
        (t : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ := hΦ t (ι v) (hVJ hv)
    rw [hMt, blkAt_congr_of_support h0 _ (hsupp v)]
    exact altCoords4_congr _ (hblkalt v)

theorem extSq_one {m : ℕ} (hm2 : 2 ≤ m) (h : 1 + m ≤ n)
    (hA : ∀ t ∈ A, BlockForm 1 m (t : Matrix (Fin n) (Fin n) (ZMod 2)))
    (hcross : ∀ (k l : Fin n) (hc : IsCross 1 m k l), ∀ v ∈ V,
      ρ (SpecialLinearGroup.transvection hc.ne (1 : ZMod 2)) v = v) :
    ∃ Ψ : ↥V →* Multiplicative (Fin 1 → Fin m → ZMod 2), Function.Injective Ψ ∧
      ∀ t ∈ A, ∀ (v : ↥V) (hv : ρ t v ∈ V),
        Multiplicative.toAdd (Ψ ⟨ρ t v, hv⟩) =
          diagAct (blkAt 1 m h (t : Matrix (Fin n) (Fin n) (ZMod 2)))
            (Multiplicative.toAdd (Ψ v)) := by
  let ι : ↥V →* ↥J := Subgroup.inclusion hVJ
  let M : ↥V → Matrix (Fin n) (Fin n) (ZMod 2) := fun v => Multiplicative.toAdd (Φ (ι v))
  have hsupp := fun v : ↥V => alt_support_one hm2 (hΦalt (ι v)) fun k l hc =>
    extSq_coord_fixed hΦ hc.ne (ι v) (hcross k l hc v v.2)
  let col : ↥V → Fin m → ZMod 2 := fun v j => M v ⟨1 + j, by have := j.isLt; omega⟩ ⟨0, by omega⟩
  refine ⟨{ toFun := fun v => Multiplicative.ofAdd fun _ => col v
            map_one' := by
              apply Multiplicative.toAdd.injective
              funext i j
              simp [col, M]
            map_mul' := fun u v => by
              apply Multiplicative.toAdd.injective
              funext i j
              simp [col, M, map_mul] }, ?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro v hv
    have hv' := congrFun (congrArg Multiplicative.toAdd hv) 0
    simp only [MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd, toAdd_one, Pi.zero_apply] at hv'
    have hM0 : M v = 0 := by
      ext i j
      by_cases hij : ((i : ℕ) = 0 ∧ 1 ≤ (j : ℕ) ∧ (j : ℕ) < 1 + m) ∨
          ((j : ℕ) = 0 ∧ 1 ≤ (i : ℕ) ∧ (i : ℕ) < 1 + m)
      · rcases hij with ⟨hi, hj1, hj2⟩ | ⟨hj, hi1, hi2⟩
        · have := congrFun hv' ⟨(j : ℕ) - 1, by omega⟩
          have e1 : (⟨1 + ((j : ℕ) - 1), by omega⟩ : Fin n) = j := Fin.ext (by simp; omega)
          have e2 : (⟨0, by omega⟩ : Fin n) = i := Fin.ext (by simp; omega)
          simp only [col, e1, e2, Pi.zero_apply] at this
          exact (alt_symm (hΦalt (ι v)) j i).trans this
        · have := congrFun hv' ⟨(i : ℕ) - 1, by omega⟩
          have e1 : (⟨1 + ((i : ℕ) - 1), by omega⟩ : Fin n) = i := Fin.ext (by simp; omega)
          have e2 : (⟨0, by omega⟩ : Fin n) = j := Fin.ext (by simp; omega)
          simp only [col, e1, e2, Pi.zero_apply] at this
          exact this
      · exact hsupp v i j hij
    have h1 : Φ (ι v) = 1 := Multiplicative.toAdd.injective hM0
    have h2 : ι v = 1 := hΦinj (by rw [h1, map_one])
    apply Subtype.ext
    simpa [ι] using congrArg Subtype.val h2
  · intro t ht v hv
    funext i
    show col ⟨ρ t v, hv⟩ = blkAt 1 m h (t : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ col v
    have hMt : M ⟨ρ t v, hv⟩ = (t : Matrix (Fin n) (Fin n) (ZMod 2)) * M v *
        (t : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ := hΦ t (ι v) (hVJ hv)
    simp only [col, hMt]
    exact col_congr_of_support h (hA t ht) (hsupp v)

theorem extSq_two {m : ℕ} (hm2 : 2 ≤ m)
    (hA : ∀ t ∈ A, BlockForm 2 m (t : Matrix (Fin n) (Fin n) (ZMod 2)))
    (hVA : ∀ t ∈ A, ∀ v ∈ V, ρ t v ∈ V)
    (hcross : ∀ (k l : Fin n) (hc : IsCross 2 m k l), ∀ v ∈ V,
      ρ (SpecialLinearGroup.transvection hc.ne (1 : ZMod 2)) v = v) :
    ∀ t ∈ A, ∀ v ∈ V, ρ t v = v := by
  intro t ht v hv
  have hsupp := alt_support_two hm2 (hΦalt ⟨v, hVJ hv⟩) fun k l hc =>
    extSq_coord_fixed hΦ hc.ne ⟨v, hVJ hv⟩ (hcross k l hc v hv)
  have h1 := hΦ t ⟨v, hVJ hv⟩ (hVJ (hVA t ht v hv))
  rw [congr_eq_self_of_support_two (hA t ht) hsupp] at h1
  have h2 := hΦinj (Multiplicative.toAdd.injective h1)
  exact congrArg Subtype.val h2

end Main

end CFSG.Quasithin.C48Pf.FMod
