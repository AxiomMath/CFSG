module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionSLRest
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotInvolutionCentralizerOTwo
public import CFSG.LocalAnalysis.StandardType.GGLinearFusionSLCent
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionAlpha

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank Matrix

namespace SLAlpha

section Isotropic

variable {F : Type} [Field F] [Fintype F]

theorem card_le_of_isotropic {W : AddSubgroup ((Fin 4 → F) × (Fin 4 → F))}
    (hW : ∀ w ∈ W, ∀ w' ∈ W, w.1 ⬝ᵥ w'.2 = w'.1 ⬝ᵥ w.2) :
    Nat.card W ≤ Fintype.card F ^ 4 := by
  classical
  set B := Matrix.toBilin' (1 : Matrix (Fin 4) (Fin 4) F) with hBdef
  have hB : B.Nondegenerate := by
    rw [hBdef, Matrix.nondegenerate_toBilin'_iff]
    exact Matrix.nondegenerate_of_det_ne_zero (by simp)
  have hBapp : ∀ a b, B a b = a ⬝ᵥ b := fun a b => by simp [hBdef, Matrix.toBilin'_apply']
  set fstW : W →+ (Fin 4 → F) := (AddMonoidHom.fst _ _).comp W.subtype with hfst
  set U : Submodule F (Fin 4 → F) := Submodule.span F (fstW.range : Set (Fin 4 → F)) with hU
  have hsplit := AddSubgroup.card_ker_mul_card_range fstW
  have h1 : Nat.card fstW.range ≤ Nat.card U := by
    refine Nat.card_le_card_of_injective (fun x => ⟨x.1, Submodule.subset_span x.2⟩) ?_
    intro x y hxy
    have h' := congrArg Subtype.val hxy
    exact Subtype.ext h'
  have hker : ∀ x : fstW.ker, ((x : W) : (Fin 4 → F) × (Fin 4 → F)).2 ∈ B.orthogonal U := by
    intro x
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro u hu
    have hle : U ≤ LinearMap.ker (B.flip (((x : W) : (Fin 4 → F) × (Fin 4 → F)).2)) := by
      rw [hU, Submodule.span_le]
      rintro _ ⟨w', rfl⟩
      have hx0 : ((x : W) : (Fin 4 → F) × (Fin 4 → F)).1 = 0 := x.2
      have := hW _ (x : W).2 _ w'.2
      rw [hx0, zero_dotProduct] at this
      change B (fstW w') _ = 0
      rw [hBapp]
      exact this.symm
    have := hle hu
    rw [LinearMap.mem_ker, LinearMap.BilinForm.flip_apply] at this
    exact this
  have h2 : Nat.card fstW.ker ≤ Nat.card (B.orthogonal U) := by
    refine Nat.card_le_card_of_injective (fun x => ⟨_, hker x⟩) ?_
    intro x y hxy
    have h2' : ((x : W) : (Fin 4 → F) × (Fin 4 → F)).2 = ((y : W) : (Fin 4 → F) × (Fin 4 → F)).2 :=
      congrArg Subtype.val hxy
    have hx0 : ((x : W) : (Fin 4 → F) × (Fin 4 → F)).1 = 0 := x.2
    have hy0 : ((y : W) : (Fin 4 → F) × (Fin 4 → F)).1 = 0 := y.2
    exact Subtype.ext (Subtype.ext (Prod.ext (hx0.trans hy0.symm) h2'))
  have h3 : Nat.card U * Nat.card (B.orthogonal U) = Fintype.card F ^ 4 := by
    have hU4 : Module.finrank F U ≤ 4 := by
      have := Submodule.finrank_le U
      rwa [Module.finrank_fin_fun] at this
    have hO := LinearMap.BilinForm.finrank_orthogonal hB U
    rw [Module.finrank_fin_fun] at hO
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := F),
      Module.card_eq_pow_finrank (K := F) (V := B.orthogonal U), hO, ← pow_add,
      Nat.add_sub_cancel' hU4]
  calc Nat.card W = Nat.card fstW.ker * Nat.card fstW.range := hsplit.symm
    _ ≤ Nat.card (B.orthogonal U) * Nat.card U := Nat.mul_le_mul h2 h1
    _ = Fintype.card F ^ 4 := by rw [mul_comm, h3]

end Isotropic

section Transfer

theorem odd_card_of_forall_sq_eq_one {Y : Type*} [Group Y] [Finite Y]
    (h : ∀ y : Y, y ^ 2 = 1 → y = 1) : Odd (Nat.card Y) := by
  by_contra hodd
  rw [Nat.not_odd_iff_even, even_iff_two_dvd] at hodd
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := Y) 2 hodd
  have h1 : y = 1 := h y (by rw [← hy]; exact pow_orderOf_eq_one y)
  rw [h1, orderOf_one] at hy
  exact absurd hy (by norm_num)

theorem ordProj_two_card_eq_one {Y : Type*} [Group Y] [Finite Y]
    (h : ∀ y : Y, y ^ 2 = 1 → y = 1) : ordProj[2] (Nat.card Y) = 1 := by
  have hodd := odd_card_of_forall_sq_eq_one h
  rw [Nat.factorization_eq_zero_of_not_dvd
    (fun h2 => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)), pow_zero]

variable {F : Type} [Field F] [CharP F 2] {n : ℕ} {G : Type} [Group G]
  {ψ : SpecialLinearGroup (Fin n) F →* G}

theorem eq_one_of_mem_center_of_two_pow {z : SpecialLinearGroup (Fin n) F}
    (hz : z ∈ Subgroup.center (SpecialLinearGroup (Fin n) F)) {k : ℕ} (hk : z ^ 2 ^ k = 1) :
    z = 1 :=
  eq_one_of_pow_two_pow_eq_one_of_forall (K := Subgroup.center (SpecialLinearGroup (Fin n) F))
    (fun _ hz hz2 => eq_one_of_mem_center_of_sq_eq_one hz hz2) k z hz hk

theorem commute_of_map_commute
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin n) F))
    {u g : SpecialLinearGroup (Fin n) F} (hu : u * u = 1) (h : ψ g * ψ u = ψ u * ψ g) :
    g * u = u * g := by
  set z := g * u * g⁻¹ * u⁻¹ with hz
  have hzk : z ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, hz, map_mul, map_mul, map_mul, map_inv, map_inv]
    calc ψ g * ψ u * (ψ g)⁻¹ * (ψ u)⁻¹ = (ψ g * ψ u) * (ψ g)⁻¹ * (ψ u)⁻¹ := rfl
      _ = (ψ u * ψ g) * (ψ g)⁻¹ * (ψ u)⁻¹ := by rw [h]
      _ = 1 := by group
  have hzc := hker hzk
  have hzu : u * z = z * u := Subgroup.mem_center_iff.mp hzc u
  have h1 : g * u * g⁻¹ = z * u := by rw [hz]; group
  have h2 : z ^ 2 = 1 := by
    calc z ^ 2 = z * z * (u * u) := by rw [hu, mul_one, sq]
      _ = (z * u) * (z * u) := by
          rw [show (z * u) * (z * u) = z * (u * z) * u by group, hzu]; group
      _ = (g * u * g⁻¹) * (g * u * g⁻¹) := by rw [h1]
      _ = g * (u * u) * g⁻¹ := by group
      _ = 1 := by rw [hu]; group
  have hz1 : z = 1 := eq_one_of_mem_center_of_sq_eq_one hzc h2
  rw [hz] at hz1
  calc g * u = g * u * g⁻¹ * u⁻¹ * (u * g) := by group
    _ = u * g := by rw [hz1, one_mul]

theorem ordProj_two_card_map [Finite F]
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin n) F))
    (X : Subgroup (SpecialLinearGroup (Fin n) F)) :
    ordProj[2] (Nat.card (X.map ψ)) = ordProj[2] (Nat.card X) := by
  set f := ψ.comp X.subtype with hf
  have hrange : f.range = X.map ψ := by rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
  have hsplit := Subgroup.card_ker_mul_card_range f
  have hk1 : ordProj[2] (Nat.card f.ker) = 1 := by
    refine ordProj_two_card_eq_one fun y hy => ?_
    have hy' : ((y : X) : SpecialLinearGroup (Fin n) F) ^ 2 = 1 := by
      have := congrArg (fun t : f.ker => ((t : X) : SpecialLinearGroup (Fin n) F)) hy
      simpa using this
    have hyk : ((y : X) : SpecialLinearGroup (Fin n) F) ∈ ψ.ker := y.2
    exact Subtype.ext (Subtype.ext (eq_one_of_mem_center_of_sq_eq_one (hker hyk) hy'))
  have hX0 : Nat.card X ≠ 0 := Nat.card_pos.ne'
  have h0 : Nat.card f.range ≠ 0 := fun h => hX0 (by rw [← hsplit, h, mul_zero])
  have h0' : Nat.card f.ker ≠ 0 := fun h => hX0 (by rw [← hsplit, h, zero_mul])
  rw [← hrange, ← hsplit, Nat.ordProj_mul 2 h0' h0, hk1, one_mul]

end Transfer

section RadicalOne

open CFSG.SeitzReduction.LinearPilot

variable {F : Type} [Field F]

noncomputable abbrev placeOne : InvPlacement (5 + 1) 1 := LinFusion.ggTransPlacement (by norm_num)

@[expose] def mid (k : Fin 4) : Fin (5 + 1) := k.castSucc.succ

theorem val_mid (k : Fin 4) : (mid k : ℕ) = k + 1 := rfl

theorem level_one_zero : placeOne.level 0 = 2 := by
  have := placeOne.level_w 0
  rwa [LinFusion.ggTransPlacement_w] at this

theorem level_one_last : placeOne.level 5 = 0 := by
  have := placeOne.level_u 0
  rwa [LinFusion.ggTransPlacement_u] at this

theorem level_one_mid (k : Fin 4) : placeOne.level (mid k) = 1 := by
  rw [InvPlacement.level_eq_one_iff]
  refine ⟨fun a h => ?_, fun a h => ?_⟩
  · rw [LinFusion.ggTransPlacement_u] at h
    have := congrArg Fin.val h
    simp only [Fin.val_last, val_mid] at this
    omega
  · rw [LinFusion.ggTransPlacement_w] at h
    have := congrArg Fin.val h
    simp only [Fin.val_zero, val_mid] at this
    omega

theorem mid_injective : Function.Injective mid := by
  intro k k' h
  have := congrArg Fin.val h
  rw [val_mid, val_mid] at this
  exact Fin.ext (by omega)

theorem mid_ne_zero (k : Fin 4) : mid k ≠ 0 := by
  intro h
  have := congrArg Fin.val h
  rw [val_mid] at this
  simp at this

theorem mid_ne_last (k : Fin 4) : mid k ≠ 5 := by
  intro h
  have := congrArg Fin.val h
  rw [val_mid] at this
  have h5 : ((5 : Fin (5 + 1)) : ℕ) = 5 := rfl
  omega

theorem level_one_mid_le (k k' : Fin 4) : placeOne.level (mid k') ≤ placeOne.level (mid k) := by
  rw [level_one_mid, level_one_mid]

theorem sum_fin_six {M : Type*} [AddCommMonoid M] (f : Fin (5 + 1) → M) :
    ∑ l, f l = f 0 + ∑ k : Fin 4, f (mid k) + f 5 := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc, add_assoc]
  rfl

variable {B B' : SpecialLinearGroup (Fin (5 + 1)) F}

theorem radOne_apply (hB : B ∈ placeOne.radical F) {i j : Fin (5 + 1)}
    (h : placeOne.level j ≤ placeOne.level i) :
    (B : Matrix (Fin (5 + 1)) (Fin (5 + 1)) F) i j = (1 : Matrix (Fin (5 + 1)) (Fin (5 + 1)) F) i j :=
  hB i j h

theorem radOne_mid_mid (hB : B ∈ placeOne.radical F) (k k' : Fin 4) :
    (B : Matrix (Fin (5 + 1)) (Fin (5 + 1)) F) (mid k) (mid k') = if k = k' then 1 else 0 := by
  rw [radOne_apply hB (level_one_mid_le k k')]
  by_cases h : k = k'
  · rw [h, one_apply_eq, ite_eq_left rfl]
  · rw [one_apply_ne (fun e => h (mid_injective e)), ite_eq_right h]

theorem radOne_mul_last_mid (hB : B ∈ placeOne.radical F) (hB' : B' ∈ placeOne.radical F)
    (j : Fin 4) :
    ((B * B' : SpecialLinearGroup (Fin (5 + 1)) F) : Matrix (Fin (5 + 1)) (Fin (5 + 1)) F) 5 (mid j) =
      (B : Matrix (Fin (5 + 1)) (Fin (5 + 1)) F) 5 (mid j) +
        (B' : Matrix (Fin (5 + 1)) (Fin (5 + 1)) F) 5 (mid j) := by
  have h0 : (B' : Matrix (Fin (5 + 1)) (Fin (5 + 1)) F) 0 (mid j) = 0 := by
    rw [radOne_apply hB' (i := 0) (j := mid j) (by rw [level_one_zero, level_one_mid]; omega),
      one_apply_ne (mid_ne_zero j).symm]
  have h5 : (B : Matrix (Fin (5 + 1)) (Fin (5 + 1)) F) 5 5 = 1 := by
    rw [radOne_apply hB (i := 5) (j := 5) le_rfl, one_apply_eq]
  have hsum : ∑ k : Fin 4, (B : Matrix (Fin (5 + 1)) (Fin (5 + 1)) F) 5 (mid k) *
      (B' : Matrix (Fin (5 + 1)) (Fin (5 + 1)) F) (mid k) (mid j) =
      (B : Matrix (Fin (5 + 1)) (Fin (5 + 1)) F) 5 (mid j) := by
    simp only [radOne_mid_mid hB', mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, sum_fin_six, h0, h5, mul_zero, zero_add,
    one_mul, hsum]

theorem radOne_mul_mid_zero (hB : B ∈ placeOne.radical F) (hB' : B' ∈ placeOne.radical F)
    (i : Fin 4) :
    ((B * B' : SpecialLinearGroup (Fin (5 + 1)) F) : Matrix (Fin (5 + 1)) (Fin (5 + 1)) F) (mid i) 0 =
      (B : Matrix (Fin (5 + 1)) (Fin (5 + 1)) F) (mid i) 0 +
        (B' : Matrix (Fin (5 + 1)) (Fin (5 + 1)) F) (mid i) 0 := by
  have h0 : (B' : Matrix (Fin (5 + 1)) (Fin (5 + 1)) F) 0 0 = 1 := by
    rw [radOne_apply hB' (i := 0) (j := 0) le_rfl, one_apply_eq]
  have h5 : (B : Matrix (Fin (5 + 1)) (Fin (5 + 1)) F) (mid i) 5 = 0 := by
    rw [radOne_apply hB (i := mid i) (j := 5) (by rw [level_one_last]; omega),
      one_apply_ne (mid_ne_last i)]
  have hsum : ∑ k : Fin 4, (B : Matrix (Fin (5 + 1)) (Fin (5 + 1)) F) (mid i) (mid k) *
      (B' : Matrix (Fin (5 + 1)) (Fin (5 + 1)) F) (mid k) 0 =
      (B' : Matrix (Fin (5 + 1)) (Fin (5 + 1)) F) (mid i) 0 := by
    simp only [radOne_mid_mid hB, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true]
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, sum_fin_six, h0, h5, mul_one, zero_mul,
    add_zero, hsum, add_comm]

theorem radOne_mul_last_zero (hB : B ∈ placeOne.radical F) (hB' : B' ∈ placeOne.radical F) :
    ((B * B' : SpecialLinearGroup (Fin (5 + 1)) F) : Matrix (Fin (5 + 1)) (Fin (5 + 1)) F) 5 0 =
      (B : Matrix (Fin (5 + 1)) (Fin (5 + 1)) F) 5 0 +
        ∑ k : Fin 4, (B : Matrix (Fin (5 + 1)) (Fin (5 + 1)) F) 5 (mid k) *
          (B' : Matrix (Fin (5 + 1)) (Fin (5 + 1)) F) (mid k) 0 +
        (B' : Matrix (Fin (5 + 1)) (Fin (5 + 1)) F) 5 0 := by
  have h0 : (B' : Matrix (Fin (5 + 1)) (Fin (5 + 1)) F) 0 0 = 1 := by
    rw [radOne_apply hB' (i := 0) (j := 0) le_rfl, one_apply_eq]
  have h5 : (B : Matrix (Fin (5 + 1)) (Fin (5 + 1)) F) 5 5 = 1 := by
    rw [radOne_apply hB (i := 5) (j := 5) le_rfl, one_apply_eq]
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, sum_fin_six, h0, h5, mul_one, one_mul]

theorem fin_six_cases (i : Fin (5 + 1)) : i = 0 ∨ (∃ k, i = mid k) ∨ i = 5 := by
  obtain ⟨v, hv⟩ := i
  rcases (by omega : v = 0 ∨ (1 ≤ v ∧ v ≤ 4) ∨ v = 5) with rfl | ⟨h1, h4⟩ | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl ⟨⟨v - 1, by omega⟩, Fin.ext (by rw [val_mid]; simp only; omega)⟩)
  · exact Or.inr (Or.inr rfl)

@[expose] def radOneVec (B : SpecialLinearGroup (Fin (5 + 1)) F) : (Fin 4 → F) × (Fin 4 → F) :=
  (fun k => (B : Matrix (Fin (5 + 1)) (Fin (5 + 1)) F) 5 (mid k),
    fun k => (B : Matrix (Fin (5 + 1)) (Fin (5 + 1)) F) (mid k) 0)

theorem radOneVec_mul (hB : B ∈ placeOne.radical F) (hB' : B' ∈ placeOne.radical F) :
    radOneVec (B * B') = radOneVec B + radOneVec B' := by
  ext k
  · exact radOne_mul_last_mid hB hB' k
  · exact radOne_mul_mid_zero hB hB' k

theorem radOneVec_one : radOneVec (1 : SpecialLinearGroup (Fin (5 + 1)) F) = 0 := by
  ext k
  · change ((1 : SpecialLinearGroup (Fin (5 + 1)) F) : Matrix (Fin (5 + 1)) (Fin (5 + 1)) F) 5
      (mid k) = 0
    rw [Matrix.SpecialLinearGroup.coe_one, one_apply_ne (mid_ne_last k).symm]
  · change ((1 : SpecialLinearGroup (Fin (5 + 1)) F) : Matrix (Fin (5 + 1)) (Fin (5 + 1)) F) (mid k)
      0 = 0
    rw [Matrix.SpecialLinearGroup.coe_one, one_apply_ne (mid_ne_zero k)]

theorem eq_of_radOneVec_eq (hB : B ∈ placeOne.radical F) (hB' : B' ∈ placeOne.radical F)
    (hv : radOneVec B = radOneVec B')
    (h50 : (B : Matrix (Fin (5 + 1)) (Fin (5 + 1)) F) 5 0 =
      (B' : Matrix (Fin (5 + 1)) (Fin (5 + 1)) F) 5 0) : B = B' := by
  have hv1 : ∀ k, (B : Matrix (Fin (5 + 1)) (Fin (5 + 1)) F) 5 (mid k) =
      (B' : Matrix (Fin (5 + 1)) (Fin (5 + 1)) F) 5 (mid k) := fun k => congrFun (congrArg Prod.fst hv) k
  have hv2 : ∀ k, (B : Matrix (Fin (5 + 1)) (Fin (5 + 1)) F) (mid k) 0 =
      (B' : Matrix (Fin (5 + 1)) (Fin (5 + 1)) F) (mid k) 0 := fun k => congrFun (congrArg Prod.snd hv) k
  have hlev : ∀ i j, placeOne.level j ≤ placeOne.level i →
      (B : Matrix (Fin (5 + 1)) (Fin (5 + 1)) F) i j =
        (B' : Matrix (Fin (5 + 1)) (Fin (5 + 1)) F) i j := fun i j h => by
    rw [radOne_apply hB h, radOne_apply hB' h]
  apply Subtype.ext
  ext i j
  rcases fin_six_cases i with rfl | ⟨k, rfl⟩ | rfl <;> rcases fin_six_cases j with rfl | ⟨k', rfl⟩ | rfl
  · exact hlev _ _ le_rfl
  · exact hlev _ _ (by rw [level_one_zero, level_one_mid]; omega)
  · exact hlev _ _ (by rw [level_one_zero, level_one_last]; omega)
  · exact hv2 k
  · exact hlev _ _ (level_one_mid_le k k')
  · exact hlev _ _ (by rw [level_one_mid, level_one_last]; omega)
  · exact h50
  · exact hv1 k'
  · exact hlev _ _ le_rfl

theorem radOneVec_isotropic (hB : B ∈ placeOne.radical F) (hB' : B' ∈ placeOne.radical F)
    (hc : B * B' = B' * B) :
    (radOneVec B).1 ⬝ᵥ (radOneVec B').2 = (radOneVec B').1 ⬝ᵥ (radOneVec B).2 := by
  have h := congrArg (fun X : SpecialLinearGroup (Fin (5 + 1)) F =>
    (X : Matrix (Fin (5 + 1)) (Fin (5 + 1)) F) 5 0) hc
  rw [radOne_mul_last_zero hB hB', radOne_mul_last_zero hB' hB] at h
  simp only [radOneVec, dotProduct]
  linear_combination h

theorem card_le_of_abelian_radOne [Fintype F] {A : Subgroup (SpecialLinearGroup (Fin (5 + 1)) F)}
    (hA : A ≤ placeOne.radical F) (hc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) :
    Nat.card A ≤ Fintype.card F ^ 5 := by
  classical
  let f : A →* Multiplicative ((Fin 4 → F) × (Fin 4 → F)) :=
    { toFun := fun x => Multiplicative.ofAdd (radOneVec (x : SpecialLinearGroup (Fin (5 + 1)) F))
      map_one' := by rw [Subgroup.coe_one, radOneVec_one]; rfl
      map_mul' := fun x y => by
        rw [Subgroup.coe_mul, radOneVec_mul (hA x.2) (hA y.2)]
        rfl }
  have hsplit := Subgroup.card_ker_mul_card_range f
  let W : AddSubgroup ((Fin 4 → F) × (Fin 4 → F)) := Subgroup.toAddSubgroup' f.range
  have hWmem : ∀ v, v ∈ W ↔ ∃ x : A, radOneVec (x : SpecialLinearGroup (Fin (5 + 1)) F) = v := by
    intro v
    change Multiplicative.ofAdd v ∈ f.range ↔ _
    rw [MonoidHom.mem_range]
    exact ⟨fun ⟨x, hx⟩ => ⟨x, hx⟩, fun ⟨x, hx⟩ => ⟨x, congrArg Multiplicative.ofAdd hx⟩⟩
  have hiso : ∀ w ∈ W, ∀ w' ∈ W, w.1 ⬝ᵥ w'.2 = w'.1 ⬝ᵥ w.2 := by
    intro w hw w' hw'
    obtain ⟨x, rfl⟩ := (hWmem w).mp hw
    obtain ⟨y, rfl⟩ := (hWmem w').mp hw'
    exact radOneVec_isotropic (hA x.2) (hA y.2) (hc _ x.2 _ y.2)
  have hW := card_le_of_isotropic hiso
  have hrange : Nat.card f.range = Nat.card W := Nat.card_congr (Equiv.subtypeEquiv
    Multiplicative.toAdd fun _ => Iff.rfl)
  have hker : Nat.card f.ker ≤ Fintype.card F := by
    rw [← Nat.card_eq_fintype_card]
    refine Nat.card_le_card_of_injective (fun x =>
      (((x : A) : SpecialLinearGroup (Fin (5 + 1)) F) : Matrix (Fin (5 + 1)) (Fin (5 + 1)) F) 5 0)
      fun x y hxy => ?_
    have hx : radOneVec ((x : A) : SpecialLinearGroup (Fin (5 + 1)) F) = 0 :=
      congrArg Multiplicative.toAdd x.2
    have hy : radOneVec ((y : A) : SpecialLinearGroup (Fin (5 + 1)) F) = 0 :=
      congrArg Multiplicative.toAdd y.2
    exact Subtype.ext (Subtype.ext (eq_of_radOneVec_eq (hA (x : A).2) (hA (y : A).2)
      (hx.trans hy.symm) hxy))
  calc Nat.card A = Nat.card f.ker * Nat.card f.range := hsplit.symm
    _ ≤ Fintype.card F * Fintype.card F ^ 4 := Nat.mul_le_mul hker (hrange ▸ hW)
    _ = Fintype.card F ^ 5 := by ring

@[expose] def midInv (i : Fin (5 + 1)) : Fin 4 := ⟨((i : ℕ) - 1) % 4, Nat.mod_lt _ (by norm_num)⟩

theorem val_mid_ne_five (k : Fin 4) : (mid k : ℕ) ≠ 5 := by
  rw [val_mid]
  have := k.2
  omega

theorem val_mid_ne_zero (k : Fin 4) : (mid k : ℕ) ≠ 0 := by
  rw [val_mid]
  omega

theorem midInv_mid (k : Fin 4) : midInv (mid k) = k := by
  apply Fin.ext
  simp only [midInv, val_mid]
  have := k.2
  omega

@[expose] def radOneMat (a b : Fin 4 → F) (c : F) : Matrix (Fin (5 + 1)) (Fin (5 + 1)) F :=
  Matrix.of fun i j => if i = j then 1 else if (i : ℕ) = 5 ∧ (j : ℕ) = 0 then c else
    if (i : ℕ) = 5 then a (midInv j) else if (j : ℕ) = 0 then b (midInv i) else 0

theorem radOneMat_lowerTriangular (a b : Fin 4 → F) (c : F) :
    (radOneMat a b c).BlockTriangular OrderDual.toDual := by
  intro i j hij
  have hij' : (i : ℕ) < j := hij
  simp only [radOneMat, of_apply]
  rw [ite_eq_right (fun h => by rw [h] at hij'; omega)]
  have hj := j.2
  rw [ite_eq_right (fun h => by omega), ite_eq_right (fun h => by omega),
    ite_eq_right (fun h => by omega)]

theorem det_radOneMat (a b : Fin 4 → F) (c : F) : (radOneMat a b c).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular _ (radOneMat_lowerTriangular a b c)]
  exact Finset.prod_eq_one fun i _ => by simp [radOneMat]

@[expose] def radOneSL (a b : Fin 4 → F) (c : F) : SpecialLinearGroup (Fin (5 + 1)) F :=
  ⟨radOneMat a b c, det_radOneMat a b c⟩

theorem radOneSL_mem (a b : Fin 4 → F) (c : F) : radOneSL a b c ∈ placeOne.radical F := by
  intro i j hij
  change radOneMat a b c i j = _
  by_cases hij' : i = j
  · subst hij'
    simp [radOneMat]
  rw [one_apply_ne hij']
  simp only [radOneMat, of_apply, ite_eq_right hij']
  rcases fin_six_cases i with rfl | ⟨k, rfl⟩ | rfl <;> rcases fin_six_cases j with rfl | ⟨k', rfl⟩ | rfl
  · exact absurd rfl hij'
  · simp [mid_ne_zero]
  · simp
  · rw [level_one_zero, level_one_mid] at hij
    omega
  · simp [val_mid_ne_five, mid_ne_zero]
  · simp [val_mid_ne_five]
  · rw [level_one_zero, level_one_last] at hij
    omega
  · rw [level_one_mid, level_one_last] at hij
    omega
  · exact absurd rfl hij'

theorem card_radOne_ge [Fintype F] :
    Fintype.card F ^ 9 ≤ Nat.card (placeOne.radical F) := by
  classical
  have hinj : Function.Injective (fun x : (Fin 4 → F) × (Fin 4 → F) × F =>
      (⟨radOneSL x.1 x.2.1 x.2.2, radOneSL_mem _ _ _⟩ : placeOne.radical F)) := by
    rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
    have hm : radOneMat a b c = radOneMat a' b' c' := congrArg (fun X : placeOne.radical F =>
      ((X : SpecialLinearGroup (Fin (5 + 1)) F) : Matrix (Fin (5 + 1)) (Fin (5 + 1)) F)) h
    have ha : a = a' := funext fun k => by
      have := congrFun (congrFun hm 5) (mid k)
      simpa [radOneMat, val_mid_ne_five, val_mid_ne_zero, midInv_mid, (mid_ne_last k).symm,
        mid_ne_zero k] using this
    have hb : b = b' := funext fun k => by
      have := congrFun (congrFun hm (mid k)) 0
      simpa [radOneMat, val_mid_ne_five, val_mid_ne_zero, midInv_mid, mid_ne_zero k,
        mid_ne_last k] using this
    have hc : c = c' := by
      have := congrFun (congrFun hm 5) 0
      simpa [radOneMat] using this
    rw [ha, hb, hc]
  have := Nat.card_le_card_of_injective _ hinj
  have hc : Nat.card ((Fin 4 → F) × (Fin 4 → F) × F) = Fintype.card F ^ 9 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_prod, Fintype.card_fun,
      Fintype.card_fin]
    ring
  rwa [hc] at this

end RadicalOne

section RadicalThree

open CFSG.SeitzReduction.LinearPilot

variable {F : Type} [Field F]

@[expose] def placeThree : InvPlacement (5 + 1) 3 where
  u b := ⟨b + 3, by have := b.2; omega⟩
  w b := ⟨b, by have := b.2; omega⟩
  u_injective a b h := Fin.ext (by have := congrArg Fin.val h; simp only at this; omega)
  w_injective a b h := Fin.ext (by have := congrArg Fin.val h; simp only at this; omega)
  u_ne_w a b h := by have := congrArg Fin.val h; simp only at this; have := b.2; omega

theorem placeThree_mat : placeThree.mat F = ggInvSL (5 + 1) 3 F := by
  apply Subtype.ext
  rw [InvPlacement.coe_mat, coe_ggInvSL, ggInvMatrix]
  congr 1
  ext i j
  simp only [InvPlacement.nil, of_apply, ggInvNil_apply]
  congr 1
  apply propext
  constructor
  · rintro ⟨a, ha, hb⟩
    have hi : (i : ℕ) = a + 3 := by rw [← ha]; rfl
    have hj : (j : ℕ) = a := by rw [← hb]; rfl
    have := a.2
    omega
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨j, h1⟩, Fin.ext (by show (j : ℕ) + 3 = i; omega), rfl⟩

theorem level_three_high {i : Fin (5 + 1)} (hi : 3 ≤ (i : ℕ)) : placeThree.level i = 0 := by
  have := placeThree.level_u ⟨(i : ℕ) - 3, by have := i.2; omega⟩
  have he : placeThree.u ⟨(i : ℕ) - 3, by have := i.2; omega⟩ = i :=
    Fin.ext (by simp only [placeThree]; omega)
  rwa [he] at this

theorem level_three_low {i : Fin (5 + 1)} (hi : (i : ℕ) < 3) : placeThree.level i = 2 := by
  have := placeThree.level_w ⟨(i : ℕ), hi⟩
  have he : placeThree.w ⟨(i : ℕ), hi⟩ = i := Fin.ext rfl
  rwa [he] at this

theorem level_three_eq (i : Fin (5 + 1)) :
    placeThree.level i = if 3 ≤ (i : ℕ) then 0 else 2 := by
  split_ifs with h
  · exact level_three_high h
  · exact level_three_low (by omega)

theorem radThree_mul_coe {r r' : SpecialLinearGroup (Fin (5 + 1)) F}
    (hr : r ∈ placeThree.radical F) (hr' : r' ∈ placeThree.radical F) :
    ((r * r' : SpecialLinearGroup (Fin (5 + 1)) F) : Matrix (Fin (5 + 1)) (Fin (5 + 1)) F) =
      (r : Matrix (Fin (5 + 1)) (Fin (5 + 1)) F) + r' - 1 := by
  ext i j
  rw [Matrix.sub_apply, Matrix.add_apply]
  by_cases hle : placeThree.level j ≤ placeThree.level i
  · rw [(mul_mem hr hr') i j hle, hr i j hle, hr' i j hle]
    ring
  · have hij : i ≠ j := by
      rintro rfl
      exact hle le_rfl
    rw [level_three_eq, level_three_eq] at hle
    rw [Matrix.SpecialLinearGroup.coe_mul, mul_apply, Finset.sum_eq_add i j hij,
      one_apply_ne hij]
    · rw [hr i i le_rfl, hr' j j le_rfl, one_apply_eq, one_apply_eq, one_mul, mul_one]
      ring
    · intro l _ hl
      by_cases h1 : placeThree.level l ≤ placeThree.level i
      · rw [hr i l h1, one_apply_ne (Ne.symm hl.1), zero_mul]
      · rw [level_three_eq, level_three_eq] at h1
        rw [hr' l j (by rw [level_three_eq, level_three_eq]; split_ifs at h1 hle ⊢ <;> omega),
          one_apply_ne hl.2, mul_zero]
    · intro h'
      exact absurd (Finset.mem_univ i) h'
    · intro h'
      exact absurd (Finset.mem_univ j) h'

theorem radThree_comm {r r' : SpecialLinearGroup (Fin (5 + 1)) F}
    (hr : r ∈ placeThree.radical F) (hr' : r' ∈ placeThree.radical F) : r * r' = r' * r := by
  apply Subtype.ext
  rw [radThree_mul_coe hr hr', radThree_mul_coe hr' hr]
  abel

@[expose] def radThreeMat (c : Fin 3 → Fin 3 → F) : Matrix (Fin (5 + 1)) (Fin (5 + 1)) F :=
  Matrix.of fun i j => if i = j then 1 else if 3 ≤ (i : ℕ) ∧ (j : ℕ) < 3 then
    c ⟨((i : ℕ) - 3) % 3, Nat.mod_lt _ (by norm_num)⟩ ⟨(j : ℕ) % 3, Nat.mod_lt _ (by norm_num)⟩
    else 0

theorem radThreeMat_lowerTriangular (c : Fin 3 → Fin 3 → F) :
    (radThreeMat c).IsLowerTriangular := by
  intro i j hij
  have hij' : (i : ℕ) < j := hij
  simp only [radThreeMat, of_apply]
  rw [ite_eq_right (fun h => by rw [h] at hij'; omega), ite_eq_right (fun h => by omega)]

@[expose] def radThreeSL (c : Fin 3 → Fin 3 → F) : SpecialLinearGroup (Fin (5 + 1)) F :=
  ⟨radThreeMat c, by
    rw [Matrix.det_of_isLowerTriangular _ (radThreeMat_lowerTriangular c)]
    exact Finset.prod_eq_one fun i _ => by simp [radThreeMat]⟩

theorem radThreeSL_mem (c : Fin 3 → Fin 3 → F) : radThreeSL c ∈ placeThree.radical F := by
  intro i j hij
  change radThreeMat c i j = _
  by_cases hij' : i = j
  · subst hij'
    simp [radThreeMat]
  rw [one_apply_ne hij']
  simp only [radThreeMat, of_apply, ite_eq_right hij']
  rw [level_three_eq, level_three_eq] at hij
  rw [ite_eq_right]
  intro h
  split_ifs at hij <;> omega

theorem card_radThree_ge [Fintype F] :
    Fintype.card F ^ 9 ≤ Nat.card (placeThree.radical F) := by
  classical
  have hinj : Function.Injective (fun c : Fin 3 → Fin 3 → F =>
      (⟨radThreeSL c, radThreeSL_mem c⟩ : placeThree.radical F)) := by
    intro c c' h
    have hm : radThreeMat c = radThreeMat c' := congrArg (fun X : placeThree.radical F =>
      ((X : SpecialLinearGroup (Fin (5 + 1)) F) : Matrix (Fin (5 + 1)) (Fin (5 + 1)) F)) h
    funext a b
    have := congrFun (congrFun hm ⟨a + 3, by have := a.2; omega⟩) ⟨b, by have := b.2; omega⟩
    have hab : (⟨a + 3, by have := a.2; omega⟩ : Fin (5 + 1)) ≠ ⟨b, by have := b.2; omega⟩ := by
      intro h'
      have := congrArg Fin.val h'
      simp only at this
      have := b.2
      omega
    have ha3 : (⟨((a : ℕ) + 3 - 3) % 3, Nat.mod_lt _ (by norm_num)⟩ : Fin 3) = a :=
      Fin.ext (by simp only; have := a.2; omega)
    have hb3 : (⟨(b : ℕ) % 3, Nat.mod_lt _ (by norm_num)⟩ : Fin 3) = b :=
      Fin.ext (by simp only; have := b.2; omega)
    simp only [radThreeMat, of_apply, ite_eq_right hab] at this
    rw [ite_eq_left (by have := b.2; omega), ite_eq_left (by have := b.2; omega), ha3, hb3] at this
    exact this
  have := Nat.card_le_card_of_injective _ hinj
  have hc : Nat.card (Fin 3 → Fin 3 → F) = Fintype.card F ^ 9 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fun, Fintype.card_fin]
    ring
  rwa [hc] at this

end RadicalThree

section HSide

open CFSG.SeitzReduction.LinearPilot

variable {F : Type} [Field F] [Finite F] [CharP F 2] {G : Type} [Group G]
  {ψ : SpecialLinearGroup (Fin (5 + 1)) F →* G}

theorem placeThree_free : placeThree.free = (∅ : Finset (Fin (5 + 1))) := by
  rw [← Finset.card_eq_zero, InvPlacement.card_free]

omit [Finite F] [CharP F 2] in
theorem det_free_placeThree (B : SpecialLinearGroup (Fin (5 + 1)) F) :
    ((B : Matrix (Fin (5 + 1)) (Fin (5 + 1)) F).submatrix
      (Subtype.val : placeThree.free → Fin (5 + 1)) (Subtype.val : placeThree.free → Fin (5 + 1))).det
      = 1 := by
  have : IsEmpty placeThree.free := by
    rw [placeThree_free]
    infer_instance
  exact Matrix.det_isEmpty

omit [Finite F] [CharP F 2] in
theorem eq_one_of_mem_blockSpecialLinear_free {A : SpecialLinearGroup (Fin (5 + 1)) F}
    (hA : A ∈ blockSpecialLinear (K := F) placeThree.free) : A = 1 := by
  apply Subtype.ext
  ext i j
  exact hA i j (Or.inl (by rw [placeThree_free]; exact Finset.notMem_empty i))

omit [Finite F] in
theorem det_u_of_mem_center {z : SpecialLinearGroup (Fin (5 + 1)) F}
    (hz : z ∈ Subgroup.center (SpecialLinearGroup (Fin (5 + 1)) F)) :
    ((z : Matrix (Fin (5 + 1)) (Fin (5 + 1)) F).submatrix placeThree.u placeThree.u).det = 1 := by
  obtain ⟨r, hr, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  rw [Fintype.card_fin] at hr
  rw [← hrz, Matrix.scalar_apply, submatrix_diagonal _ _ placeThree.u_injective, det_diagonal]
  simp only [Function.comp_apply, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have h2 : (r ^ 3) ^ 2 ^ 1 = 1 ^ 2 ^ 1 := by rw [← pow_mul]; simpa using hr
  exact InvPlacement.eq_of_pow_two_pow_eq h2

omit [Finite F] in
theorem ggCentOTwoPrime_three_le_map_core
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (5 + 1)) F)) :
    ggCentOTwoPrime ψ.range (ψ (ggInvSL (5 + 1) 3 F)) ≤ (placeThree.core F).map ψ := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro y ⟨⟨g, rfl⟩, hys, k, hyk⟩
  rw [← placeThree_mat] at hys
  have hgc : g * placeThree.mat F = placeThree.mat F * g :=
    commute_of_map_commute hker (placeThree.mat_mul_self) hys
  have hgC : g ∈ Subgroup.centralizer {placeThree.mat F} :=
    Subgroup.mem_centralizer_singleton_iff.mpr hgc
  have hgP : g ∈ placeThree.parabolic F := placeThree.centralizer_le_parabolic hgC
  have hgk : g ^ 2 ^ k ∈ Subgroup.center (SpecialLinearGroup (Fin (5 + 1)) F) :=
    hker (by rw [MonoidHom.mem_ker, map_pow, hyk])
  have hdet : ((g : Matrix (Fin (5 + 1)) (Fin (5 + 1)) F).submatrix placeThree.u
      placeThree.u).det = 1 := by
    have h1 : (placeThree.detU F ⟨g, hgP⟩) ^ 2 ^ k = 1 ^ 2 ^ k := by
      rw [← map_pow, one_pow]
      exact det_u_of_mem_center hgk
    exact InvPlacement.eq_of_pow_two_pow_eq h1
  exact ⟨g, placeThree.mem_core_of_det hgC hdet (det_free_placeThree g), rfl⟩

omit [Finite F] in
theorem map_core_le_ggCentOTwoPrime_three :
    (placeThree.core F).map ψ ≤ ggCentOTwoPrime ψ.range (ψ (ggInvSL (5 + 1) 3 F)) := by
  have hgen : ∀ g ∈ Subgroup.centralizer {placeThree.mat F}, ∀ k : ℕ, g ^ 2 ^ k = 1 →
      ψ g ∈ ggCentOTwoPrime ψ.range (ψ (ggInvSL (5 + 1) 3 F)) := by
    intro g hg k hgk
    refine Subgroup.subset_closure ⟨⟨g, rfl⟩, ?_, k, by rw [← map_pow, hgk, map_one]⟩
    rw [← placeThree_mat, ← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp hg]
  rw [InvPlacement.core, Subgroup.map_sup, Subgroup.map_sup]
  refine sup_le ?_ (sup_le ?_ ?_)
  · rintro _ ⟨r, hr, rfl⟩
    exact hgen r (placeThree.radical_le_centralizer hr) 2 (by
      rw [show 2 ^ 2 = 4 by norm_num]
      exact placeThree.radical_pow_four hr)
  · have hL : placeThree.leviOne F ≤
        (ggCentOTwoPrime ψ.range (ψ (ggInvSL (5 + 1) 3 F))).comap ψ := by
      rw [InvPlacement.leviOne, MonoidHom.range_eq_map,
        ← Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field,
        MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
      refine hgen _ (placeThree.leviOne_le_centralizer ⟨_, rfl⟩) 1 ?_
      rw [pow_one, sq, ← map_mul, Matrix.TransvectionStruct.toSpecialLinearGroup_def,
        InvPlacement.transvection_mul_self, map_one]
    exact Subgroup.map_le_iff_le_comap.mpr hL
  · rintro _ ⟨A, hA, rfl⟩
    rw [eq_one_of_mem_blockSpecialLinear_free hA, map_one]
    exact Subgroup.one_mem _

@[expose] def scalarSix {r : F} (hr : r ^ 3 = 1) : SpecialLinearGroup (Fin (5 + 1)) F :=
  ⟨Matrix.scalar (Fin (5 + 1)) r, by
    rw [Matrix.scalar_apply, det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      show 5 + 1 = 3 * 2 by norm_num, pow_mul, hr, one_pow]⟩

omit [Finite F] [CharP F 2] in
theorem scalarSix_mem_center {r : F} (hr : r ^ 3 = 1) :
    scalarSix hr ∈ Subgroup.center (SpecialLinearGroup (Fin (5 + 1)) F) :=
  Matrix.SpecialLinearGroup.mem_center_iff.mpr ⟨r, by
    rw [Fintype.card_fin, show 5 + 1 = 3 * 2 by norm_num, pow_mul, hr, one_pow], rfl⟩

omit [Finite F] [CharP F 2] in
theorem coreU_mem_center {D : placeThree.core F}
    (hD : (D : SpecialLinearGroup (Fin (5 + 1)) F) ∈
      Subgroup.center (SpecialLinearGroup (Fin (5 + 1)) F)) :
    placeThree.coreU F D ∈ Subgroup.center (SpecialLinearGroup (Fin 3) F) := by
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hD
  have hmat : ((placeThree.coreU F D : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      Matrix.scalar (Fin 3) r := by
    change ((D : SpecialLinearGroup (Fin (5 + 1)) F) : Matrix (Fin (5 + 1)) (Fin (5 + 1)) F).submatrix
      placeThree.u placeThree.u = _
    rw [← hr, Matrix.scalar_apply, Matrix.scalar_apply,
      submatrix_diagonal _ _ placeThree.u_injective]
    rfl
  have hdet := (placeThree.coreU F D).2
  rw [hmat, Matrix.scalar_apply, det_diagonal, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] at hdet
  exact Matrix.SpecialLinearGroup.mem_center_iff.mpr ⟨r, by rw [Fintype.card_fin]; exact hdet,
    hmat.symm⟩

theorem commute_of_normal_isPGroup_three (h4 : 4 ≤ Nat.card F)
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (5 + 1)) F)) {H : Subgroup G}
    (hHC : H ≤ (placeThree.core F).map ψ) (hCH : (placeThree.core F).map ψ ≤ H)
    (N : Subgroup H) (hN : N.Normal) (hN2 : IsPGroup 2 N) : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x := by
  let N' : Subgroup G := N.map H.subtype
  let Nt : Subgroup (placeThree.core F) := N'.comap (ψ.comp (placeThree.core F).subtype)
  let X : Subgroup (SpecialLinearGroup (Fin 3) F) := Nt.map (placeThree.coreU F)
  have hmemN' : ∀ {g : G} (hg : g ∈ H), g ∈ N' ↔ (⟨g, hg⟩ : H) ∈ N := by
    intro g hg
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact hn
    · intro h
      exact ⟨_, h, rfl⟩
  have hN'H : ∀ {g : G}, g ∈ N' → g ∈ H := by
    rintro _ ⟨n, -, rfl⟩
    exact n.2
  have hXn : X.Normal := by
    refine ⟨fun a ha g => ?_⟩
    obtain ⟨B, hB, rfl⟩ := ha
    obtain ⟨c, rfl⟩ := placeThree.coreU_surjective (K := F) g
    refine ⟨c * B * c⁻¹, ?_, by simp only [map_mul, map_inv]⟩
    have hcH : ψ (c : SpecialLinearGroup (Fin (5 + 1)) F) ∈ H := hCH ⟨c, c.2, rfl⟩
    have hBN : ψ (B : SpecialLinearGroup (Fin (5 + 1)) F) ∈ N' := hB
    have hBH := hN'H hBN
    have hconj := hN.conj_mem _ ((hmemN' hBH).mp hBN) ⟨_, hcH⟩
    have hval : ψ ((c * B * c⁻¹ : placeThree.core F) : SpecialLinearGroup (Fin (5 + 1)) F) ∈ H := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
      exact H.mul_mem (H.mul_mem hcH hBH) (H.inv_mem hcH)
    change ψ ((c * B * c⁻¹ : placeThree.core F) : SpecialLinearGroup (Fin (5 + 1)) F) ∈ N'
    rw [hmemN' hval]
    convert hconj using 1
    apply Subtype.ext
    simp [map_mul, map_inv]
  have hX2 : ∀ a ∈ X, ∃ e : ℕ, a ^ 2 ^ e ∈ Subgroup.center (SpecialLinearGroup (Fin 3) F) := by
    rintro _ ⟨B, hB, rfl⟩
    have hBN : ψ (B : SpecialLinearGroup (Fin (5 + 1)) F) ∈ N' := hB
    obtain ⟨n, hn, hnB⟩ := hBN
    obtain ⟨e, he⟩ := hN2 ⟨n, hn⟩
    have he' : (ψ (B : SpecialLinearGroup (Fin (5 + 1)) F)) ^ 2 ^ e = 1 := by
      have := congrArg (fun t : N => ((t : H) : G)) he
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at this
      rw [← hnB]
      exact this
    refine ⟨e, ?_⟩
    rw [← map_pow]
    apply coreU_mem_center
    rw [Subgroup.coe_pow]
    exact hker (by rw [MonoidHom.mem_ker, map_pow, he'])
  have hXc := InvPlacement.le_center_of_normal_of_two_pow (K := F) h4 X hX2
  have hform : ∀ x ∈ N, ∃ z ∈ Subgroup.center (SpecialLinearGroup (Fin (5 + 1)) F),
      ∃ r ∈ placeThree.radical F, ((x : H) : G) = ψ (z * r) := by
    intro x hx
    obtain ⟨B, hB, hBx⟩ := hHC x.2
    have hBt : (⟨B, hB⟩ : placeThree.core F) ∈ Nt := by
      change ψ B ∈ N'
      rw [hBx]
      exact ⟨x, hx, rfl⟩
    have hcen := hXc ⟨_, hBt, rfl⟩
    obtain ⟨r, hr3, hrB⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hcen
    rw [Fintype.card_fin] at hr3
    have hBu : ∀ a b, (B : Matrix (Fin (5 + 1)) (Fin (5 + 1)) F) (placeThree.u a) (placeThree.u b)
        = Matrix.scalar (Fin 3) r a b := by
      intro a b
      have := congrFun (congrFun hrB a) b
      exact this.symm
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [zero_pow (by norm_num)] at hr3
      exact zero_ne_one hr3
    refine ⟨scalarSix hr3, scalarSix_mem_center hr3, (scalarSix hr3)⁻¹ * B, ?_, ?_⟩
    · have hBC : B ∈ Subgroup.centralizer {placeThree.mat F} := placeThree.core_le_centralizer hB
      have hzC : (scalarSix hr3)⁻¹ ∈ Subgroup.centralizer {placeThree.mat F} :=
        Subgroup.center_le_centralizer _ (Subgroup.inv_mem _ (scalarSix_mem_center hr3))
      refine placeThree.mem_radical_of_blocks (mul_mem hzC hBC) (fun a b => ?_) (fun i j hi _ => ?_)
      · have hr3' : r⁻¹ ^ 3 = 1 := by rw [inv_pow, hr3, inv_one]
        have h1 : scalarSix hr3 * scalarSix hr3' = 1 := by
          apply Subtype.ext
          change Matrix.scalar (Fin (5 + 1)) r * Matrix.scalar (Fin (5 + 1)) r⁻¹ = 1
          rw [← map_mul, mul_inv_cancel₀ hr0, map_one]
        have hT := eq_inv_of_mul_eq_one_right h1
        rw [← hT, Matrix.SpecialLinearGroup.coe_mul]
        change (Matrix.scalar (Fin (5 + 1)) r⁻¹ * (B : Matrix (Fin (5 + 1)) (Fin (5 + 1)) F))
          (placeThree.u a) (placeThree.u b) = _
        rw [Matrix.scalar_apply, Matrix.diagonal_mul, hBu, Matrix.scalar_apply, diagonal_apply,
          InvPlacement.one_apply_of_injective placeThree.u_injective]
        rw [Matrix.one_apply]
        split_ifs
        · exact inv_mul_cancel₀ hr0
        · exact mul_zero _
      · rw [placeThree_free] at hi
        exact absurd hi (Finset.notMem_empty i)
    · rw [← hBx, mul_inv_cancel_left]
  intro x hx y hy
  obtain ⟨z, hz, r, hr, hxr⟩ := hform x hx
  obtain ⟨z', hz', r', hr', hyr⟩ := hform y hy
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, hxr, hyr, ← map_mul, ← map_mul]
  congr 1
  have hzc := Subgroup.mem_center_iff.mp hz
  have hzc' := Subgroup.mem_center_iff.mp hz'
  calc z * r * (z' * r') = z * (r * z') * r' := by group
    _ = z * (z' * r) * r' := by rw [hzc' r]
    _ = z * z' * (r * r') := by group
    _ = z' * z * (r' * r) := by rw [hzc z', radThree_comm hr hr']
    _ = z' * (z * r') * r := by group
    _ = z' * (r' * z) * r := by rw [← hzc r']
    _ = z' * r' * (z * r) := by group
omit [Finite F] [CharP F 2] in
theorem ordProj_two_card_of_isPGroup {Y : Type*} [Group Y] [Finite Y] (hY : IsPGroup 2 Y) :
    ordProj[2] (Nat.card Y) = Nat.card Y := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp hY
  rw [hk, Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_two,
    smul_eq_mul, mul_one]

omit [CharP F 2] in
theorem ordProj_two_card_SL {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : 1 ≤ f) (d : ℕ) [NeZero d] :
    ordProj[2] (Nat.card (SpecialLinearGroup (Fin d) F)) = 2 ^ (f * (d * (d - 1) / 2)) := by
  rw [Nat.factorization_def _ Nat.prime_two, SLRest.padicValNat_two_card_SL hF hf d]

theorem ordProj_card_core_three_ge {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : 1 ≤ f) :
    2 ^ (12 * f) ≤ ordProj[2] (Nat.card (placeThree.core F)) := by
  classical
  have : Fintype F := Fintype.ofFinite F
  set c := placeThree.coreU F with hc
  have hsplit := Subgroup.card_ker_mul_card_range c
  have hrange : Nat.card c.range = Nat.card (SpecialLinearGroup (Fin 3) F) := by
    rw [MonoidHom.range_eq_top.mpr (placeThree.coreU_surjective (K := F))]
    exact Nat.card_congr Subgroup.topEquiv.toEquiv
  have hR : (placeThree.radical F).subgroupOf (placeThree.core F) ≤ c.ker := by
    intro r hr
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    exact placeThree.submatrix_u_eq_one_of_mem_radical hr
  have hdvd : Nat.card (placeThree.radical F) ∣ Nat.card c.ker := by
    have h1 := Subgroup.card_dvd_of_le hR
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe placeThree.radical_le_core).toEquiv] at h1
  have hRp : IsPGroup 2 (placeThree.radical F) := placeThree.isPGroup_radical
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := 2)).mp hRp
  have hq9 := card_radThree_ge (F := F)
  rw [Fintype.card_eq_nat_card, hF, ← pow_mul, ha] at hq9
  have h9a : 9 * f ≤ a := by
    rw [show f * 9 = 9 * f by ring] at hq9
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hq9
  have hker0 : Nat.card c.ker ≠ 0 := Nat.card_pos.ne'
  have hran0 : Nat.card c.range ≠ 0 := Nat.card_pos.ne'
  have hk : 2 ^ (9 * f) ≤ ordProj[2] (Nat.card c.ker) := by
    have h2 : 2 ^ (9 * f) ∣ Nat.card c.ker :=
      (pow_dvd_pow 2 h9a).trans (ha ▸ hdvd)
    have h3 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hker0).mp h2
    exact Nat.pow_le_pow_right (by norm_num) h3
  rw [← hsplit, Nat.ordProj_mul 2 hker0 hran0, hrange, ordProj_two_card_SL hF hf 3]
  calc 2 ^ (12 * f) = 2 ^ (9 * f) * 2 ^ (f * (3 * (3 - 1) / 2)) := by
        rw [← pow_add]; congr 1; norm_num; ring
    _ ≤ _ := Nat.mul_le_mul_right _ hk

end HSide

section KSide

open CFSG.SeitzReduction.LinearPilot

variable {F : Type} [Field F] [Finite F] [CharP F 2] {G : Type} [Group G]
  {ψ : SpecialLinearGroup (Fin (5 + 1)) F →* G}

omit [Finite F] [CharP F 2] in
theorem placeOne_mat : placeOne.mat F = ggInvSL (5 + 1) 1 F :=
  LinFusion.ggTransPlacement_mat (by norm_num)

omit [CharP F 2] in
theorem finite_of_le_range {K : Subgroup G} (hK : K ≤ ψ.range) : Finite K := by
  have : Finite ψ.range := Finite.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
  exact Finite.of_injective (Subgroup.inclusion hK) (Subgroup.inclusion_injective hK)

omit [Finite F] in
theorem ggCentOTwoPrime_one_le_map_centralizer
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (5 + 1)) F)) :
    ggCentOTwoPrime ψ.range (ψ (ggInvSL (5 + 1) 1 F)) ≤
      (Subgroup.centralizer {placeOne.mat F}).map ψ := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro y ⟨⟨g, rfl⟩, hys, -⟩
  rw [← placeOne_mat] at hys
  exact ⟨g, Subgroup.mem_centralizer_singleton_iff.mpr
    (commute_of_map_commute hker placeOne.mat_mul_self hys), rfl⟩

omit [Finite F] in
theorem map_radOne_le_ggCentOTwoPrime :
    (placeOne.radical F).map ψ ≤ ggCentOTwoPrime ψ.range (ψ (ggInvSL (5 + 1) 1 F)) := by
  rintro _ ⟨r, hr, rfl⟩
  refine Subgroup.subset_closure ⟨⟨r, rfl⟩, ?_, 2, ?_⟩
  · rw [← placeOne_mat, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.mp (placeOne.radical_le_centralizer hr)]
  · rw [← map_pow, show 2 ^ 2 = 4 by norm_num, placeOne.radical_pow_four hr, map_one]

omit [Finite F] in
theorem conj_mem_map_radOne
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (5 + 1)) F)) {k x : G}
    (hk : k ∈ ggCentOTwoPrime ψ.range (ψ (ggInvSL (5 + 1) 1 F)))
    (hx : x ∈ (placeOne.radical F).map ψ) : k * x * k⁻¹ ∈ (placeOne.radical F).map ψ := by
  obtain ⟨c, hc, rfl⟩ := ggCentOTwoPrime_one_le_map_centralizer hker hk
  obtain ⟨r, hr, rfl⟩ := hx
  exact ⟨c * r * c⁻¹, placeOne.conj_mem_radical (placeOne.centralizer_le_parabolic hc) hr,
    by simp only [map_mul, map_inv]⟩

omit [Finite F] in
theorem isPGroup_map_radOne : IsPGroup 2 ((placeOne.radical F).map ψ) :=
  placeOne.isPGroup_radical.map ψ

theorem card_map_radOne (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (5 + 1)) F)) :
    Nat.card ((placeOne.radical F).map ψ) = Nat.card (placeOne.radical F) := by
  have h1 := ordProj_two_card_map hker (placeOne.radical F)
  have : Finite ((placeOne.radical F).map ψ) := finite_of_le_range (Subgroup.map_le_range ψ _)
  rwa [ordProj_two_card_of_isPGroup isPGroup_map_radOne,
    ordProj_two_card_of_isPGroup placeOne.isPGroup_radical] at h1

theorem card_le_of_abelian_map_radOne [Fintype F]
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (5 + 1)) F)) {A : Subgroup G}
    (hA : A ≤ (placeOne.radical F).map ψ) (hc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) :
    Nat.card A ≤ Fintype.card F ^ 5 := by
  set At : Subgroup (SpecialLinearGroup (Fin (5 + 1)) F) := A.comap ψ ⊓ placeOne.radical F
    with hAt
  have hmap : At.map ψ = A := by
    apply le_antisymm
    · rintro _ ⟨r, hr, rfl⟩
      exact hr.1
    · intro a ha
      obtain ⟨r, hr, rfl⟩ := hA ha
      exact ⟨r, ⟨ha, hr⟩, rfl⟩
  have hinj : ∀ x ∈ placeOne.radical F, ∀ y ∈ placeOne.radical F, ψ x = ψ y → x = y := by
    intro x hx y hy hxy
    have hm : x * y⁻¹ ∈ placeOne.radical F := mul_mem hx (inv_mem hy)
    have hk : x * y⁻¹ ∈ ψ.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, mul_inv_cancel]
    have h4 : (x * y⁻¹) ^ 2 ^ 2 = 1 := by
      rw [show 2 ^ 2 = 4 by norm_num]
      exact placeOne.radical_pow_four hm
    have := eq_one_of_mem_center_of_two_pow (hker hk) h4
    exact mul_inv_eq_one.mp this
  have hAtc : ∀ x ∈ At, ∀ y ∈ At, x * y = y * x := fun x hx y hy =>
    hinj _ (mul_mem hx.2 hy.2) _ (mul_mem hy.2 hx.2) (by rw [map_mul, map_mul, hc _ hx.1 _ hy.1])
  have hAp : IsPGroup 2 A := isPGroup_map_radOne.to_le hA
  have hAtp : IsPGroup 2 At := placeOne.isPGroup_radical.to_le inf_le_right
  have : Finite ((placeOne.radical F).map ψ) := finite_of_le_range (Subgroup.map_le_range ψ _)
  have : Finite A := Finite.of_injective (Subgroup.inclusion hA) (Subgroup.inclusion_injective hA)
  have hcard : Nat.card A = Nat.card At := by
    have h1 := ordProj_two_card_map hker At
    rw [hmap] at h1
    rwa [ordProj_two_card_of_isPGroup hAp, ordProj_two_card_of_isPGroup hAtp] at h1
  rw [hcard]
  exact card_le_of_abelian_radOne inf_le_right hAtc

theorem ordProj_card_le_of_le_range
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (5 + 1)) F)) {f : ℕ}
    (hF : Nat.card F = 2 ^ f) (hf : 1 ≤ f) {K : Subgroup G} (hK : K ≤ ψ.range) :
    ordProj[2] (Nat.card K) ≤ 2 ^ (15 * f) := by
  have : Finite ψ.range := Finite.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
  have hdvd : Nat.card K ∣ Nat.card ψ.range := Subgroup.card_dvd_of_le hK
  have h0 : Nat.card ψ.range ≠ 0 := Nat.card_pos.ne'
  have h1 := Nat.ordProj_dvd_ordProj_of_dvd h0 hdvd 2
  have h2 : ordProj[2] (Nat.card ψ.range) = 2 ^ (15 * f) := by
    rw [MonoidHom.range_eq_map, ordProj_two_card_map hker ⊤,
      Nat.card_congr Subgroup.topEquiv.toEquiv, ordProj_two_card_SL hF hf (5 + 1)]
    congr 1
    ring
  rw [h2] at h1
  exact Nat.le_of_dvd (by positivity) h1

end KSide

end SLAlpha

open CFSG.SeitzReduction.LinearPilot SLAlpha in
theorem ggSLSixAlphaInput_holds : GGSLSixAlphaInput := by
  intro F _ _ _ h4 G _ ψ hker
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨f', -, hcard⟩ := FiniteField.card F 2
  set f : ℕ := (f' : ℕ) with hfdef
  have hf : 1 ≤ f := f'.2
  have hF : Nat.card F = 2 ^ f := by rw [Nat.card_eq_fintype_card, hcard]
  show ¬ ∃ φ : ↥(ggCentOTwoPrime ψ.range (ψ (ggInvSL (5 + 1) 3 F))) →*
    ↥(ggCentOTwoPrime ψ.range (ψ (ggInvSL (5 + 1) 1 F))), Function.Injective φ
  set Hs := ggCentOTwoPrime ψ.range (ψ (ggInvSL (5 + 1) 3 F)) with hHs
  set Ks := ggCentOTwoPrime ψ.range (ψ (ggInvSL (5 + 1) 1 F)) with hKs
  have hKr : Ks ≤ ψ.range := (Subgroup.closure_le _).mpr fun y hy => hy.1
  have hHr : Hs ≤ ψ.range := (Subgroup.closure_le _).mpr fun y hy => hy.1
  have : Finite Ks := finite_of_le_range hKr
  have : Finite Hs := finite_of_le_range hHr
  set R := (placeOne.radical F).map ψ with hR
  have hRK : R ≤ Ks := map_radOne_le_ggCentOTwoPrime
  set Q : Subgroup Ks := R.subgroupOf Ks with hQ
  have hQn : Q.Normal := ⟨fun n hn k => by
    rw [hQ, Subgroup.mem_subgroupOf] at hn ⊢
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact conj_mem_map_radOne hker k.2 hn⟩
  have hQ2 : IsPGroup 2 Q := isPGroup_map_radOne.comap_of_injective Ks.subtype Ks.subtype_injective
  have hab : ∀ A : Subgroup Ks, A ≤ Q → (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) →
      Nat.card A ≤ Fintype.card F ^ 5 := by
    intro A hAQ hAc
    have := card_le_of_abelian_map_radOne hker (A := A.map Ks.subtype)
      (by rintro _ ⟨a, ha, rfl⟩; exact hAQ ha)
      (by
        rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
        rw [← map_mul, ← map_mul, hAc a ha b hb])
    rwa [Subgroup.card_map_of_injective Ks.subtype_injective] at this
  have hHeq : Hs = (placeThree.core F).map ψ :=
    le_antisymm (ggCentOTwoPrime_three_le_map_core hker) map_core_le_ggCentOTwoPrime_three
  have hH : ∀ N : Subgroup Hs, N.Normal → IsPGroup 2 N → ∀ x ∈ N, ∀ y ∈ N, x * y = y * x :=
    fun N hN hN2 => commute_of_normal_isPGroup_three h4 hker hHeq.le hHeq.ge N hN hN2
  have hHq : 2 ^ (12 * f) ≤ ordProj[2] (Nat.card Hs) := by
    rw [hHeq, ordProj_two_card_map hker]
    exact ordProj_card_core_three_ge hF hf
  have hQcard : 2 ^ (9 * f) ≤ Nat.card Q := by
    rw [hQ, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRK).toEquiv, hR, card_map_radOne hker]
    have := card_radOne_ge (F := F)
    rwa [Fintype.card_eq_nat_card, hF, ← pow_mul, mul_comm] at this
  have hKq : ordProj[2] (Nat.card Ks) ≤ 2 ^ (15 * f) := ordProj_card_le_of_le_range hker hF hf hKr
  have hsplit := Subgroup.card_eq_card_quotient_mul_card_subgroup Q
  have hKQ0 : Nat.card (Ks ⧸ Q) ≠ 0 := Nat.card_pos.ne'
  have hQ0 : Nat.card Q ≠ 0 := Nat.card_pos.ne'
  have hmul : ordProj[2] (Nat.card Ks) = ordProj[2] (Nat.card (Ks ⧸ Q)) * Nat.card Q := by
    rw [hsplit, Nat.ordProj_mul 2 hKQ0 hQ0, ordProj_two_card_of_isPGroup hQ2]
  have hquot : ordProj[2] (Nat.card (Ks ⧸ Q)) ≤ 2 ^ (6 * f) := by
    have h1 : ordProj[2] (Nat.card (Ks ⧸ Q)) * 2 ^ (9 * f) ≤ 2 ^ (6 * f) * 2 ^ (9 * f) := by
      calc ordProj[2] (Nat.card (Ks ⧸ Q)) * 2 ^ (9 * f)
          ≤ ordProj[2] (Nat.card (Ks ⧸ Q)) * Nat.card Q := Nat.mul_le_mul_left _ hQcard
        _ = ordProj[2] (Nat.card Ks) := hmul.symm
        _ ≤ 2 ^ (15 * f) := hKq
        _ = 2 ^ (6 * f) * 2 ^ (9 * f) := by rw [← pow_add]; congr 1; ring
    exact Nat.le_of_mul_le_mul_right h1 (by positivity)
  have hq5 : Fintype.card F ^ 5 = 2 ^ (5 * f) := by
    rw [Fintype.card_eq_nat_card, hF, ← pow_mul, mul_comm]
  have hlt : Fintype.card F ^ 5 * ordProj[2] (Nat.card (Ks ⧸ Q)) < ordProj[2] (Nat.card Hs) := by
    rw [hq5]
    calc 2 ^ (5 * f) * ordProj[2] (Nat.card (Ks ⧸ Q)) ≤ 2 ^ (5 * f) * 2 ^ (6 * f) :=
          Nat.mul_le_mul_left _ hquot
      _ = 2 ^ (11 * f) := by rw [← pow_add]; congr 1; ring
      _ < 2 ^ (12 * f) := Nat.pow_lt_pow_right (by norm_num) (by omega)
      _ ≤ _ := hHq
  exact not_exists_injective_of_ordProj_two_lt Q hQ2 hab hH hlt

section Inputs

theorem ggSixRootFusionSLRepResidualInput_holds : GGSixRootFusionSLRepResidualInput :=
  ggSixRootFusionSLRepResidualInput_of_alpha ggSLSixAlphaInput_holds

theorem ggSixRootFusionSLRepInput_of_nonsplit (hN : GGSixRootFusionSLRepNonsplitInput) :
    GGSixRootFusionSLRepInput :=
  ggSixRootFusionSLRepInput_of_nonsplit_alpha hN ggSLSixAlphaInput_holds

end Inputs

end CFSG.StandardType
