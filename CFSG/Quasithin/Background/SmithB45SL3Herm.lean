module

public import CFSG.Quasithin.Background.SmithB45SL3Move
public import CFSG.Quasithin.Background.HL3NineComm
public import CFSG.Quasithin.Background.SmithB45SL3Fix

public section

namespace CFSG.Quasithin

namespace B45SL3

open CFSG.QuasithinUnique.Setup.X7a CFSG.Quasithin.B42SL3
open CFSG.QuasithinUnique.Setup.X7 (matRep matRep_apply matMap matMap_apply)
open CFSG.QuasithinUnique.Setup.X7b (toMatRep)
open scoped MatrixGroups Matrix

section Positions

variable {f : ℕ}

theorem shiftPair_injective : Function.Injective (shiftPair f) := by
  have hb : ∀ {u v : Fin f → Bool}, shiftBits f u = shiftBits f v → u = v := by
    intro u v h
    funext p
    have := congrFun h (finRotate f p)
    simp only [shiftBits, Equiv.symm_apply_apply] at this
    exact this
  intro x y hxy
  exact Prod.ext (hb (congrArg Prod.fst hxy)) (hb (congrArg Prod.snd hxy))

theorem exists_period (c : (Fin f → Bool) × (Fin f → Bool)) (hlt : (pairOrbit f c).card < f) :
    ∃ d, 0 < d ∧ d < f ∧ (shiftPair f)^[d] c = c := by
  classical
  by_contra hcon
  push Not at hcon
  have key : ∀ s₁ s₂, s₁ < s₂ → s₂ < f → (shiftPair f)^[s₁] c = (shiftPair f)^[s₂] c → False := by
    intro s₁ s₂ h h2 h12
    apply hcon (s₂ - s₁) (by omega) (by omega)
    apply (shiftPair_injective).iterate s₁
    rw [← Function.iterate_add_apply, Nat.add_sub_cancel' h.le]
    exact h12.symm
  apply (lt_irrefl f)
  calc f = (Finset.range f).card := (Finset.card_range f).symm
    _ = (pairOrbit f c).card := by
      refine (Finset.card_image_of_injOn ?_).symm
      intro s₁ hs₁ s₂ hs₂ h12
      simp only [Finset.coe_range, Set.mem_Iio] at hs₁ hs₂
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · exact key s₁ s₂ h hs₂ h12
      · exact key s₂ s₁ h hs₁ h12.symm
    _ < f := hlt

theorem add_mod_of_lt {i d : ℕ} (hi : i < f) (hd : d < f) :
    (i + d) % f = i + d ∧ i + d < f ∨ (i + d) % f = i + d - f ∧ f ≤ i + d := by
  rcases Nat.lt_or_ge (i + d) f with h | h
  · exact Or.inl ⟨Nat.mod_eq_of_lt h, h⟩
  · refine Or.inr ⟨?_, h⟩
    rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]

theorem fst_ne_snd_of_isSingle {ℓ : Bool × Bool} (h : IsSingle ℓ) : ℓ.1 ≠ ℓ.2 := by
  rcases h with rfl | rfl <;> decide

theorem exists_row_pos {a b : Fin f → Bool} (hS : cntS a b = 2) (hH : cntH a b = 0)
    (hlt : (pairOrbit f (a, b)).card < f) :
    ∃ (m : ℕ) (i i' : Fin f), f = 2 * m ∧ i ≠ i' ∧ (i' : ℕ) = ((i : ℕ) + m) % f ∧
      IsSingle (a i, b i) ∧ (a i', b i') = (a i, b i) ∧
      ∀ p, p ≠ i → p ≠ i' → (a p, b p) = (false, false) := by
  classical
  obtain ⟨i, i', hii', hsi, hsi', hrest⟩ := exists_two_pos hS hH
  obtain ⟨d, hd0, hdf, hdc⟩ := exists_period (a, b) hlt
  rw [shiftPair_iterate, shiftBits_iterate_eq, shiftBits_iterate_eq, Prod.mk.injEq] at hdc
  obtain ⟨hda, hdb⟩ := hdc
  set r := ((finRotate f).symm)^[d] with hr
  have hfix : ∀ p, (a (r p), b (r p)) = (a p, b p) := fun p => by
    rw [show a (r p) = (a ∘ r) p from rfl, hda, show b (r p) = (b ∘ r) p from rfl, hdb]
  have hrot : ∀ p, (finRotate f)^[d] (r p) = p := fun p =>
    Function.RightInverse.iterate (Equiv.apply_symm_apply (finRotate f)) d p
  have hS2 : ∀ p, a p ≠ b p → p = i ∨ p = i' := by
    intro p hp
    by_contra hcon
    push Not at hcon
    have := hrest p hcon.1 hcon.2
    simp only [Prod.mk.injEq] at this
    exact hp (this.1.trans this.2.symm)
  have hmove : ∀ p, r p ≠ p := by
    intro p h
    have h1 := hrot p
    rw [h] at h1
    have hv := congrArg Fin.val h1
    rw [finRotate_iterate_val] at hv
    rcases add_mod_of_lt p.isLt hdf with ⟨h2, -⟩ | ⟨h2, h3⟩ <;> omega
  have hri : r i = i' := by
    have hsr : a (r i) ≠ b (r i) := by
      have h1 := hfix i
      simp only [Prod.mk.injEq] at h1
      rw [h1.1, h1.2]
      exact fst_ne_snd_of_isSingle hsi
    rcases hS2 _ hsr with h | h
    · exact absurd h (hmove i)
    · exact h
  have hri' : r i' = i := by
    have hsr : a (r i') ≠ b (r i') := by
      have h1 := hfix i'
      simp only [Prod.mk.injEq] at h1
      rw [h1.1, h1.2]
      exact fst_ne_snd_of_isSingle hsi'
    rcases hS2 _ hsr with h | h
    · exact h
    · exact absurd h (hmove i')
  have e1 := congrArg Fin.val (hrot i')
  rw [hri', finRotate_iterate_val] at e1
  have e2 := congrArg Fin.val (hrot i)
  rw [hri, finRotate_iterate_val] at e2
  have hii'v : (i : ℕ) ≠ (i' : ℕ) := fun h => hii' (Fin.ext h)
  have hf2 : f = 2 * d := by
    rcases add_mod_of_lt i.isLt hdf with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;>
      rcases add_mod_of_lt i'.isLt hdf with ⟨h2, h2'⟩ | ⟨h2, h2'⟩ <;> omega
  refine ⟨d, i, i', hf2, hii', e1.symm, hsi, ?_, hrest⟩
  rw [← hri]
  exact hfix i


end Positions

section Kron

variable {F : Type} [Field F] [CharP F 2]

theorem locRep_eq_twistMat {ℓ : Bool × Bool} (hℓ : IsSingle ℓ) :
    ∃ ψ : SL(3, F) →* SL(3, F), (∀ g, ψ (ψ g) = g) ∧ ∃ h3 : locDim ℓ.1 ℓ.2 = 3,
      ∀ (j : ℕ) (g : SL(3, F)) (c d : Fin (locDim ℓ.1 ℓ.2)),
        locRep F ℓ.1 ℓ.2 j g c d = twistMat F j (ψ g) (Fin.cast h3 c) (Fin.cast h3 d) := by
  rcases hℓ with rfl | rfl
  · exact ⟨MonoidHom.id _, fun g => rfl, rfl, fun j g c d => rfl⟩
  · refine ⟨tauSL F, tauSL_tauSL, rfl, fun j g c d => ?_⟩
    show (twistMat F j g⁻¹)ᵀ c d = twistMat F j (tauSL F g) c d
    rw [twistMat_tauSL]

theorem locRep_cast {ℓ ℓ' : Bool × Bool} (h : ℓ = ℓ') (j : ℕ) (g : SL(3, F))
    (c d : Fin (locDim ℓ.1 ℓ.2)) :
    locRep F ℓ.1 ℓ.2 j g c d =
      locRep F ℓ'.1 ℓ'.2 j g (Fin.cast (by rw [h]) c) (Fin.cast (by rw [h]) d) := by
  subst h
  rfl

end Kron

section Embed

variable {F : Type} [Field F] [CharP F 2] {f : ℕ}

theorem exists_kron_embed {a b : Fin f → Bool} {i i' : Fin f} (hii' : i ≠ i')
    (hsi : IsSingle (a i, b i)) (hsame : (a i', b i') = (a i, b i))
    (hrest : ∀ p, p ≠ i → p ≠ i' → (a p, b p) = (false, false)) :
    ∃ ψ : SL(3, F) →* SL(3, F), (∀ g, ψ (ψ g) = g) ∧
      ∃ v : Matrix (Fin 3) (Fin 3) F →ₗ[F] (TIdx f a b → F), Function.Injective v ∧
        ∀ g X, tensorRep (F := F) F a b g *ᵥ v X =
          v (twistMat F i (ψ g) * X * (twistMat F i' (ψ g))ᵀ) := by
  classical
  obtain ⟨ψ, hψ, h3, hloc⟩ := locRep_eq_twistMat (F := F) hsi
  have h3' : locDim (a i') (b i') = 3 := by
    have := congrArg (fun ℓ : Bool × Bool => locDim ℓ.1 ℓ.2) hsame
    simp only at this
    rw [this]
    exact h3
  let τ : Fin f → Bool × Bool := fun p => (a p, b p)
  let v : Matrix (Fin 3) (Fin 3) F →ₗ[F] (TIdx f a b → F) :=
    { toFun := fun X y => X (Fin.cast h3 (y i)) (Fin.cast h3' (y i'))
      map_add' := fun X Y => rfl
      map_smul' := fun c X => rfl }
  refine ⟨ψ, hψ, v, ?_, fun g X => ?_⟩
  · intro X Y hXY
    ext r s
    obtain ⟨y, hy⟩ := (bijective_pair τ hii' hrest).2 (Fin.cast h3.symm r, Fin.cast h3'.symm s)
    simp only [Prod.mk.injEq] at hy
    have := congrFun hXY y
    change X (Fin.cast h3 (y i)) (Fin.cast h3' (y i')) =
      Y (Fin.cast h3 (y i)) (Fin.cast h3' (y i')) at this
    rw [hy.1, hy.2] at this
    simpa using this
  · funext y
    have hm := mulVec_lift_two (F := F) τ (fun p => (p : ℕ)) hii' hrest g
      (fun c c' => X (Fin.cast h3 c) (Fin.cast h3' c')) y
    show (tensorRepGen F τ (fun p => (p : ℕ)) g *ᵥ fun z => X (Fin.cast h3 (z i))
      (Fin.cast h3' (z i'))) y = _
    rw [hm]
    have hli : ∀ c, locRep F (τ i).1 (τ i).2 (i : ℕ) g (y i) c =
        twistMat F i (ψ g) (Fin.cast h3 (y i)) (Fin.cast h3 c) := fun c => hloc i g (y i) c
    have hli' : ∀ c', locRep F (τ i').1 (τ i').2 (i' : ℕ) g (y i') c' =
        twistMat F i' (ψ g) (Fin.cast h3' (y i')) (Fin.cast h3' c') := by
      intro c'
      rw [locRep_cast (F := F) hsame (i' : ℕ) g (y i') c', hloc]
      rfl
    simp_rw [hli, hli']
    show _ = (twistMat F i (ψ g) * X * (twistMat F i' (ψ g))ᵀ) (Fin.cast h3 (y i))
      (Fin.cast h3' (y i'))
    rw [Matrix.mul_apply]
    simp_rw [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Fintype.sum_equiv (finCongr h3') _ _ fun c' => ?_
    refine Fintype.sum_equiv (finCongr h3) _ _ fun c => ?_
    simp only [finCongr_apply]
    ring

end Embed

section Irr

open CFSG.Quasithin.H.L3Nine CFSG.Quasithin.H.SU3 CFSG.Quasithin.H.Tri

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

omit [Finite K] [CharP K 2] in
theorem toGL_up3_01 (a : K) :
    Matrix.SpecialLinearGroup.toGL (up3 (0 : K) 0 a) = trGL (0 : Fin 3) 1 (by decide) a := by
  apply Units.ext
  rw [coe_trGL]
  show upMat (0 : K) 0 a = Matrix.transvection 0 1 a
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upMat, Matrix.transvection, Matrix.single]

omit [Finite K] [CharP K 2] in
theorem toGL_up3_02 (a : K) :
    Matrix.SpecialLinearGroup.toGL (up3 (0 : K) a 0) = trGL (0 : Fin 3) 2 (by decide) a := by
  apply Units.ext
  rw [coe_trGL]
  show upMat (0 : K) a 0 = Matrix.transvection 0 2 a
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upMat, Matrix.transvection, Matrix.single]

theorem eq_bot_or_eq_top_of_stable (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (Z : Subgroup (HMod n K))
    (hZ : ∀ (g : SL(3, K)) (X : HMod n K), X ∈ Z → rho hK g X ∈ Z) : Z = ⊥ ∨ Z = ⊤ := by
  classical
  by_cases hbot : Z = ⊥
  · exact Or.inl hbot
  right
  have hK2 : Nat.card K = 2 ^ (2 * n) := by rw [hK, ← pow_mul, mul_comm]
  have hP := isPGroup_upperUni (F := K) hK2
  let _ : MulAction ↥(upperUni K) ↥Z :=
    { smul := fun u X => ⟨rho hK (u : SL(3, K)) X, hZ _ _ X.2⟩
      one_smul := fun X => Subtype.ext (by
        show rho hK ((1 : ↥(upperUni K)) : SL(3, K)) X = X
        rw [Subgroup.coe_one, map_one, MulAut.one_apply])
      mul_smul := fun u v X => Subtype.ext (by
        show rho hK ((u * v : ↥(upperUni K)) : SL(3, K)) X =
          rho hK (u : SL(3, K)) (rho hK (v : SL(3, K)) X)
        rw [Subgroup.coe_mul, map_mul, MulAut.mul_apply]) }
  have hsmul : ∀ (u : ↥(upperUni K)) (X : ↥Z), ((u • X : ↥Z) : HMod n K) =
      rho hK (u : SL(3, K)) X := fun u X => rfl
  have h2 : 2 ∣ Nat.card ↥Z := by
    obtain ⟨X, hX1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hbot
    have hXX : X * X = 1 := by
      apply Subtype.ext
      apply mat_injective
      rw [Subgroup.coe_mul, mat_mul, Subgroup.coe_one, mat_one, CharTwo.add_self_eq_zero]
    have hord : orderOf X = 2 := orderOf_eq_prime (by rw [sq]; exact hXX) hX1
    rw [← hord]
    exact orderOf_dvd_natCard X
  have h1 : (1 : ↥Z) ∈ MulAction.fixedPoints ↥(upperUni K) ↥Z := fun u =>
    Subtype.ext (by rw [hsmul, Subgroup.coe_one, map_one])
  obtain ⟨X, hX, hX1⟩ := hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point (α := ↥Z) h2 h1
  have hfix1 : ∀ a : K, rhoT hK (trGL (0 : Fin 3) 1 (by decide) a) (X : HMod n K) = X := by
    intro a
    have := congrArg Subtype.val (hX ⟨up3 0 0 a, mem_upperUni.mpr ⟨0, 0, a, rfl⟩⟩)
    rw [hsmul] at this
    rw [← toGL_up3_01]
    exact this
  have hfix2 : ∀ a : K, rhoT hK (trGL (0 : Fin 3) 2 (by decide) a) (X : HMod n K) = X := by
    intro a
    have := congrArg Subtype.val (hX ⟨up3 0 a 0, mem_upperUni.mpr ⟨0, a, 0, rfl⟩⟩)
    rw [hsmul] at this
    rw [← toGL_up3_02]
    exact this
  have hent := eq_zero_of_fix hn hK hfix1 hfix2
  set c := mat (X : HMod n K) 0 0 with hc
  have hc0 : c ≠ 0 := by
    intro h0
    have hX1' : (X : HMod n K) = 1 := by
      apply mat_injective
      ext i j
      rw [mat_one]
      by_cases hij : i = 0 ∧ j = 0
      · obtain ⟨rfl, rfl⟩ := hij
        exact h0
      · exact hent i j hij
    exact hX1 (Subtype.ext hX1'.symm)
  have hcbar : bar n c = c := herm_apply (X : HMod n K) 0 0
  obtain ⟨l, hl⟩ := exists_norm_eq hK hcbar hc0
  have hpt : ∀ v : Fin 3 → K, pt hK v ∈ Z := by
    intro v
    by_cases hv : v = 0
    · rw [hv, pt_zero]
      exact Z.one_mem
    have hw : (l : K)⁻¹ • v ≠ 0 := smul_ne_zero (inv_ne_zero l.ne_zero) hv
    obtain ⟨g, hgdet, hg⟩ := exists_det_one_mulVec hw
    have hmem := hZ ⟨g, hgdet⟩ X X.2
    have heq : rho hK ⟨g, hgdet⟩ (X : HMod n K) = pt hK v := by
      apply mat_injective
      have hXm : mat (X : HMod n K) = c • rk1 n (Pi.single 0 1) := by
        ext i j
        by_cases hij : i = 0 ∧ j = 0
        · obtain ⟨rfl, rfl⟩ := hij
          simp [rk1_apply, hc]
        · rw [hent i j hij, Matrix.smul_apply, rk1_apply]
          rcases not_and_or.mp hij with hi | hj
          · simp [Pi.single_apply, hi]
          · simp [Pi.single_apply, hj]
      have h1 : tw n (g : Matrix (Fin 3) (Fin 3) K) (rk1 n (Pi.single 0 1)) =
          rk1 n ((l : K)⁻¹ • v) := by
        have := congrArg mat (rhoT_pt hK g (Pi.single 0 1))
        rw [mat_rhoT, mat_pt, mat_pt, hg] at this
        exact this
      have h2 : rk1 n v = c • rk1 n ((l : K)⁻¹ • v) := by
        rw [rk1_smul, smul_smul, ← hl, map_inv₀]
        have : (l : K) * bar n (l : K) * ((l : K)⁻¹ * (bar n (l : K))⁻¹) = 1 := by
          have hb : bar n (l : K) ≠ 0 := (map_ne_zero (bar n)).mpr l.ne_zero
          field_simp
        rw [this, one_smul]
      show tw n (g : Matrix (Fin 3) (Fin 3) K) (mat (X : HMod n K)) = rk1 n v
      rw [hXm, tw_smul, h1, h2]
    rw [← heq]
    exact hmem
  rw [eq_top_iff]
  intro Y _
  obtain ⟨l₀, l₁, l₂, hY⟩ := exists_eq_pts hK Y
  rw [hY]
  refine Z.mul_mem (Z.mul_mem (Z.mul_mem (Z.mul_mem (Z.mul_mem (hpt _) (hpt _)) (hpt _))
    ?_) ?_) ?_ <;>
    exact Z.mul_mem (Z.mul_mem (hpt _) (Z.inv_mem (hpt _))) (Z.inv_mem (hpt _))

end Irr


section Ident

open CFSG.Quasithin.H.L3Nine CFSG.Quasithin.H.SU3

variable {F : Type} [Field F] [Fintype F] [CharP F 2] {f : ℕ}
  {U : Type} [AddCommGroup U] [Module (ZMod 2) U]

omit [CharP F 2] in
theorem pow_two_pow_mod (hF : Fintype.card F = 2 ^ f) (x : F) (j : ℕ) :
    x ^ 2 ^ j = x ^ 2 ^ (j % f) := by
  conv_lhs => rw [← Nat.mod_add_div j f, pow_add, pow_mul]
  rw [pow_mul]
  induction j / f with
  | zero => simp
  | succ q ih => rw [pow_succ, pow_mul, ih, ← hF, FiniteField.pow_card]

theorem twistMat_mul_mul (hF : Fintype.card F = 2 ^ f) {m : ℕ} {i i' : ℕ}
    (hi' : i' = (i + m) % f) (h : SL(3, F)) (Y : Matrix (Fin 3) (Fin 3) F) :
    twistMat F i h * (frK F i).mapMatrix Y * (twistMat F i' h)ᵀ =
      (frK F i).mapMatrix (tw m (h : Matrix (Fin 3) (Fin 3) F) Y) := by
  have h1 : twistMat F i' h = (frK F i).mapMatrix (conjM m (h : Matrix (Fin 3) (Fin 3) F)) := by
    ext r s
    simp only [twistMat_apply, RingHom.mapMatrix_apply, Matrix.map_apply, conjM, frK_apply,
      Algebra.algebraMap_self, RingHom.id_apply, bar_apply]
    rw [← pow_mul, ← pow_add, hi', ← pow_two_pow_mod hF, add_comm]
  rw [h1, tw, map_mul, map_mul]
  simp only [RingHom.mapMatrix_apply, Matrix.transpose_map]
  rfl

theorem exists_herm_equiv (hF : Fintype.card F = 2 ^ f) {m : ℕ} (hm : 1 ≤ m)
    (hK : Nat.card F = (2 ^ m) ^ 2) {n : ℕ} (ρ : Representation (ZMod 2) SL(3, F) U)
    (bas : Module.Basis (Fin n) (ZMod 2) U) (hirr : ρ.IsIrreducible) {a b : Fin f → Bool}
    {i i' : Fin f} (hii' : i ≠ i') (hi' : (i' : ℕ) = ((i : ℕ) + m) % f)
    (hsi : IsSingle (a i, b i)) (hsame : (a i', b i') = (a i, b i))
    (hrest : ∀ p, p ≠ i → p ≠ i' → (a p, b p) = (false, false))
    (W₀ : Subrepresentation (matRep (matMap (ZMod.castHom (dvd_refl 2) F) (toMatRep ρ bas))))
    (e₀ : W₀.toRepresentation.Equiv (matRep (tensorRep (F := F) F a b))) :
    ∃ ψ : SL(3, F) →* SL(3, F), (∀ g, ψ (ψ g) = g) ∧
      ∃ E : Multiplicative U ≃* HMod m F, ∀ g u,
        E (Multiplicative.ofAdd (ρ g u)) = rho hK (ψ g) (E (Multiplicative.ofAdd u)) := by
  classical
  obtain ⟨ψ, hψ, v, hvinj, hv⟩ := exists_kron_embed (F := F) hii' hsi hsame hrest
  let PF := matMap (ZMod.castHom (dvd_refl 2) F) (toMatRep ρ bas)
  let ι : Matrix (Fin 3) (Fin 3) F →ₗ[F] (Fin n → F) :=
    W₀.toSubmodule.subtype ∘ₗ e₀.symm.toLinearMap ∘ₗ v
  have hιinj : Function.Injective ι := by
    intro X Y h
    exact hvinj (e₀.symm.injective (Subtype.ext h))
  have hι : ∀ g X, ι (twistMat F i (ψ g) * X * (twistMat F i' (ψ g))ᵀ) = PF g *ᵥ ι X := by
    intro g X
    show ((e₀.symm (v (twistMat F i (ψ g) * X * (twistMat F i' (ψ g))ᵀ)) : W₀.toSubmodule) :
      Fin n → F) = PF g *ᵥ ((e₀.symm (v X) : W₀.toSubmodule) : Fin n → F)
    rw [← hv]
    have h1 := Representation.IntertwiningMap.isIntertwining _ _ e₀.symm.toIntertwiningMap g (v X)
    have h2 : e₀.symm (matRep (tensorRep (F := F) F a b) g (v X)) =
        W₀.toRepresentation g (e₀.symm (v X)) := h1
    rw [show tensorRep (F := F) F a b g *ᵥ v X = matRep (tensorRep (F := F) F a b) g (v X) from rfl,
      h2]
    rfl
  let κ : Matrix (Fin 3) (Fin 3) F →+* Matrix (Fin 3) (Fin 3) F := (frK F i).mapMatrix
  have hκinj : Function.Injective κ := fun X Y h => by
    ext r s
    have := congrFun (congrFun h r) s
    exact frK_injective (F := F) i this
  have hι' : ∀ g Y, ι (κ (tw m ((ψ g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) Y)) =
      PF g *ᵥ ι (κ Y) := by
    intro g Y
    rw [← hι, twistMat_mul_mul hF hi' (ψ g) Y]
  have hκsmul : ∀ (μ : F) Y, κ (μ • Y) = frK F i μ • κ Y := fun μ Y => by
    ext r s
    simp [κ, RingHom.mapMatrix_apply, Matrix.map_apply, map_mul]
  let H : Matrix (Fin 3) (Fin 3) F →+ U :=
    { toFun := fun Y => bas.equivFun.symm (fun k => trZ f (ι (κ Y) k))
      map_zero' := by
        rw [map_zero, map_zero]
        have : (fun k : Fin n => trZ f ((0 : Fin n → F) k)) = 0 := by
          funext k
          simp [trZ_zero hF]
        rw [this, map_zero]
      map_add' := fun X Y => by
        show bas.equivFun.symm (fun k => trZ f (ι (κ (X + Y)) k)) =
          bas.equivFun.symm (fun k => trZ f (ι (κ X) k)) +
            bas.equivFun.symm (fun k => trZ f (ι (κ Y) k))
        rw [← map_add]
        congr 1
        funext k
        rw [map_add, map_add, Pi.add_apply, trZ_add hF]
        rfl }
  have hH : ∀ g Y, H (tw m ((ψ g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) Y) = ρ g (H Y) := by
    intro g Y
    show bas.equivFun.symm (fun k => trZ f (ι (κ (tw m _ Y)) k)) =
      ρ g (bas.equivFun.symm (fun k => trZ f (ι (κ Y) k)))
    rw [hι']
    have hmat : (fun k => trZ f ((PF g *ᵥ ι (κ Y)) k)) =
        toMatRep ρ bas g *ᵥ fun k => trZ f (ι (κ Y) k) := by
      funext k
      simp only [PF, matMap_apply, Matrix.mulVec, dotProduct, Matrix.map_apply]
      rw [trZ_sum hF]
      exact Finset.sum_congr rfl fun l _ => trZ_cast_mul hF _ _
    rw [hmat]
    apply bas.equivFun.injective
    rw [LinearEquiv.apply_symm_apply]
    have := Representation.IntertwiningMap.isIntertwining _ _
      (CFSG.QuasithinUnique.Setup.X7b.matRepEquiv ρ bas).toIntertwiningMap g
      (bas.equivFun.symm (fun k => trZ f (ι (κ Y) k)))
    have e1 : (CFSG.QuasithinUnique.Setup.X7b.matRepEquiv ρ bas).toIntertwiningMap
        (bas.equivFun.symm (fun k => trZ f (ι (κ Y) k))) = fun k => trZ f (ι (κ Y) k) := by
      show bas.equivFun (bas.equivFun.symm _) = _
      rw [LinearEquiv.apply_symm_apply]
    rw [e1] at this
    exact this.symm
  set E00 : Matrix (Fin 3) (Fin 3) F := mat (e00 hK) with hE00
  have hE0 : E00 ≠ 0 := by
    intro h
    have := congrFun (congrFun h 0) 0
    simp [hE00, mat_pt, rk1_apply] at this
  obtain ⟨μ₀, hμ₀⟩ : ∃ μ₀ : F, H (μ₀ • E00) ≠ 0 := by
    obtain ⟨b₀, hb₀⟩ := trace_exists hF
    have hne : ι (κ E00) ≠ 0 := by
      intro h0
      have h1 : ι (κ E00) = ι (κ 0) := by rw [h0, map_zero, map_zero]
      exact hE0 (hκinj (hιinj h1))
    obtain ⟨k, hk⟩ : ∃ k, ι (κ E00) k ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hne (funext hcon)
    obtain ⟨μ₀, hμ₀⟩ := frK_surjective (F := F) i (b₀ / ι (κ E00) k)
    refine ⟨μ₀, fun h0 => ?_⟩
    have h1 : (fun k => trZ f (ι (κ (μ₀ • E00)) k)) = 0 := by
      apply bas.equivFun.symm.injective
      rw [map_zero]
      exact h0
    have h2 := congrFun h1 k
    simp only [hκsmul, map_smul, Pi.smul_apply, smul_eq_mul, hμ₀, Pi.zero_apply,
      div_mul_cancel₀ b₀ hk] at h2
    apply hb₀
    rw [← cast_trZ hF, h2, map_zero]
  let Hm : HMod m F →* Multiplicative U :=
    { toFun := fun X => Multiplicative.ofAdd (H (μ₀ • mat X))
      map_one' := by
        rw [mat_one, smul_zero, map_zero]
        rfl
      map_mul' := fun X Y => by
        rw [mat_mul, smul_add, map_add]
        rfl }
  have hHm : ∀ g X, Hm (rho hK (ψ g) X) =
      Multiplicative.ofAdd (ρ g (Multiplicative.toAdd (Hm X))) := by
    intro g X
    show Multiplicative.ofAdd (H (μ₀ • tw m ((ψ g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)
      (mat X))) =
      Multiplicative.ofAdd (ρ g (H (μ₀ • mat X)))
    rw [← tw_smul, hH]
  have hHm0 : Hm (e00 hK) ≠ 1 := fun h => hμ₀ (Multiplicative.ofAdd.injective h)
  have hinj : Function.Injective Hm := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases eq_bot_or_eq_top_of_stable hm hK Hm.ker (fun h X hX => by
        rw [MonoidHom.mem_ker] at hX ⊢
        have := hHm (ψ h) X
        rw [hψ, hX] at this
        rw [this]
        simp) with h0 | htop
    · exact h0
    · exact absurd (show e00 hK ∈ Hm.ker by rw [htop]; trivial) hHm0
  have hsurj : Function.Surjective Hm := by
    let R : Submodule (ZMod 2) U :=
      { carrier := {u | ∃ X, Hm X = Multiplicative.ofAdd u}
        add_mem' := by
          rintro _ _ ⟨X, hX⟩ ⟨Y, hY⟩
          exact ⟨X * Y, by rw [map_mul, hX, hY]; rfl⟩
        zero_mem' := ⟨1, by rw [map_one]; rfl⟩
        smul_mem' := by
          rintro c u ⟨X, hX⟩
          fin_cases c
          · refine ⟨1, ?_⟩
            rw [map_one]
            show (1 : Multiplicative U) = Multiplicative.ofAdd ((0 : ZMod 2) • u)
            rw [zero_smul]
            rfl
          · refine ⟨X, ?_⟩
            show Hm X = Multiplicative.ofAdd ((1 : ZMod 2) • u)
            rw [one_smul]
            exact hX }
    have hR : ∀ g, ∀ u ∈ R, ρ g u ∈ R := by
      rintro g u ⟨X, hX⟩
      refine ⟨rho hK (ψ g) X, ?_⟩
      rw [hHm, hX]
      rfl
    rcases ((CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff ρ).mp hirr).2 R hR with h0 | h1
    · exfalso
      have hmem : Multiplicative.toAdd (Hm (e00 hK)) ∈ R := ⟨e00 hK, rfl⟩
      rw [h0, Submodule.mem_bot] at hmem
      exact hHm0 (Multiplicative.toAdd.injective (hmem.trans rfl))
    · intro u
      have hu : Multiplicative.toAdd u ∈ R := by rw [h1]; exact Submodule.mem_top
      obtain ⟨X, hX⟩ := hu
      exact ⟨X, hX⟩
  let E := (MulEquiv.ofBijective Hm ⟨hinj, hsurj⟩).symm
  refine ⟨ψ, hψ, E, fun g u => ?_⟩
  apply (MulEquiv.ofBijective Hm ⟨hinj, hsurj⟩).injective
  rw [MulEquiv.apply_symm_apply]
  show Multiplicative.ofAdd (ρ g u) = Hm (rho hK (ψ g) (E (Multiplicative.ofAdd u)))
  rw [hHm]
  congr 2
  show u = Multiplicative.toAdd ((MulEquiv.ofBijective Hm ⟨hinj, hsurj⟩)
    ((MulEquiv.ofBijective Hm ⟨hinj, hsurj⟩).symm (Multiplicative.ofAdd u)))
  rw [MulEquiv.apply_symm_apply]
  rfl

end Ident

section Row

open CFSG.Quasithin.H.L3Nine

variable {F : Type} [Field F] [Fintype F] [CharP F 2] {f : ℕ}
  {U : Type} [AddCommGroup U] [Module (ZMod 2) U]

theorem not_exists_swap_of_row {a b : Fin f → Bool} (hS : cntS a b = 2) (hH : cntH a b = 0)
    (hlt : (pairOrbit f (a, b)).card < f) :
    ¬ ∃ j₀ : ℕ, (shiftBits f)^[j₀] a = b ∧ (shiftBits f)^[j₀] b = a := by
  rintro ⟨j₀, h1, h2⟩
  obtain ⟨m, i, i', -, hii', -, hsi, hsame, hrest⟩ := exists_row_pos hS hH hlt
  simp only [Prod.mk.injEq] at hsame hrest
  rcases hsi with h | h <;> simp only [Prod.mk.injEq] at h
  ·
    have hb : b = zeros f := by
      funext p
      by_cases hpi : p = i
      · rw [hpi, h.2]; rfl
      by_cases hpi' : p = i'
      · rw [hpi', hsame.2, h.2]; rfl
      · rw [(hrest p hpi hpi').2]; rfl
    rw [hb, shiftBits_iterate_zeros] at h2
    have := congrFun h2 i
    rw [h.1] at this
    exact Bool.false_ne_true this
  ·
    have ha : a = zeros f := by
      funext p
      by_cases hpi : p = i
      · rw [hpi, h.1]; rfl
      by_cases hpi' : p = i'
      · rw [hpi', hsame.1, h.1]; rfl
      · rw [(hrest p hpi hpi').1]; rfl
    rw [ha, shiftBits_iterate_zeros] at h1
    have := congrFun h1 i
    rw [h.2] at this
    exact Bool.false_ne_true this

theorem exists_herm_of_row (hF : Fintype.card F = 2 ^ f) {n : ℕ}
    (ρ : Representation (ZMod 2) SL(3, F) U) (bas : Module.Basis (Fin n) (ZMod 2) U)
    (hirr : ρ.IsIrreducible) {a b : Fin f → Bool} (hS : cntS a b = 2) (hH : cntH a b = 0)
    (hlt : (pairOrbit f (a, b)).card < f)
    (W₀ : Subrepresentation (matRep (matMap (ZMod.castHom (dvd_refl 2) F) (toMatRep ρ bas))))
    (e₀ : W₀.toRepresentation.Equiv (matRep (tensorRep (F := F) F a b))) :
    ∃ m : ℕ, 1 ≤ m ∧ f = 2 * m ∧ ∃ hK : Nat.card F = (2 ^ m) ^ 2,
      ∃ ψ : SL(3, F) →* SL(3, F), (∀ g, ψ (ψ g) = g) ∧
        ∃ E : Multiplicative U ≃* HMod m F, ∀ g u,
          E (Multiplicative.ofAdd (ρ g u)) = rho hK (ψ g) (E (Multiplicative.ofAdd u)) := by
  obtain ⟨m, i, i', hfm, hii', hi', hsi, hsame, hrest⟩ := exists_row_pos hS hH hlt
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h
      exact absurd i.isLt (by omega)
    · exact h
  have hK : Nat.card F = (2 ^ m) ^ 2 := by
    rw [Nat.card_eq_fintype_card, hF, hfm, ← pow_mul, mul_comm]
  exact ⟨m, hm, hfm, hK, exists_herm_equiv hF hm hK ρ bas hirr hii' hi' hsi hsame hrest W₀ e₀⟩

end Row

end B45SL3

end CFSG.Quasithin
