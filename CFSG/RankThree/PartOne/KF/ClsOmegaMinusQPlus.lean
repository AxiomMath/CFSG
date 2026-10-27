module

public import CFSG.RankThree.PartOne.KF.OrthChar2Plane
public import CFSG.RankThree.PartOne.KF.ClsOmegaMinusFinal

public section

namespace CFSG.RankThree.PartOne.KFU.QPlus

open Matrix CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.KFacts.KS21LocalRank
  CFSG.Assembly.RankThreeEven
  CFSG.RankThree.PartOne.KFU.OrthChar2 CFSG.LieType.BorelTits
open scoped commutatorElement

variable {K : Type} [Field K]

@[expose] def detSpace (h2 : (2 : K) = 0) : QSpace K (Matrix (Fin 2) (Fin 2) K) where
  Q := Matrix.det
  B := LinearMap.mk₂ K
    (fun W W' => W 0 0 * W' 1 1 + W 1 1 * W' 0 0 + W 0 1 * W' 1 0 + W 1 0 * W' 0 1)
    (fun W₁ W₂ W' => by simp only [Matrix.add_apply]; ring)
    (fun r W W' => by simp only [Matrix.smul_apply, smul_eq_mul]; ring)
    (fun W W₁ W₂ => by simp only [Matrix.add_apply]; ring)
    (fun r W W' => by simp only [Matrix.smul_apply, smul_eq_mul]; ring)
  Q_smul r W := by simp
  Q_add W W' := by
    simp only [Matrix.det_fin_two, Matrix.add_apply, LinearMap.mk₂_apply]
    linear_combination (-(W 0 1 * W' 1 0 + W 1 0 * W' 0 1)) * h2

variable (b c : K) (h2 : (2 : K) = 0)

@[expose] noncomputable def space : QSpace K (Matrix (Fin 2) (Fin 2) K × (Fin 2 → K)) :=
  (detSpace h2).prod (planeSpace b c h2)

theorem space_Q (x : Matrix (Fin 2) (Fin 2) K × (Fin 2 → K)) :
    (space b c h2).Q x = x.1.det + Nf b c x.2 := rfl

@[expose] noncomputable def decomp :
    (Om → K) ≃ₗ[K] K × K × (Matrix (Fin 2) (Fin 2) K × (Fin 2 → K)) where
  toFun v := (v (.inl 0), v (.inr (.inl 0)),
    !![v (.inl 1), v (.inl 2); v (.inr (.inl 2)), v (.inr (.inl 1))],
    ![v (.inr (.inr 0)), v (.inr (.inr 1))])
  invFun d := Sum.elim ![d.1, d.2.2.1 0 0, d.2.2.1 0 1]
    (Sum.elim ![d.2.1, d.2.2.1 1 1, d.2.2.1 1 0] d.2.2.2)
  map_add' v v' := by
    refine Prod.ext rfl (Prod.ext rfl (Prod.ext ?_ ?_))
    · ext i j
      fin_cases i <;> fin_cases j <;> rfl
    · ext i
      fin_cases i <;> rfl
  map_smul' c v := by
    refine Prod.ext rfl (Prod.ext rfl (Prod.ext ?_ ?_))
    · ext i j
      fin_cases i <;> fin_cases j <;> rfl
    · ext i
      fin_cases i <;> rfl
  left_inv v := by
    funext j
    rcases j with j | j | j <;> fin_cases j <;> rfl
  right_inv d := by
    refine Prod.ext rfl (Prod.ext rfl (Prod.ext ?_ ?_))
    · ext i j
      fin_cases i <;> fin_cases j <;> rfl
    · ext i
      fin_cases i <;> rfl

theorem quad_decomp (v : Om → K) :
    StatedQuadMinus 4 K b c v = Qh (space b c h2) (decomp v) := by
  rw [quadMinus_apply]
  simp only [Qh, space_Q, decomp, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.det_fin_two_of, Matrix.cons_val_zero, Matrix.cons_val_one, Nf]
  linear_combination (v (.inl 2) * v (.inr (.inl 2))) * h2

section Transport

abbrev DS (K : Type) [Field K] : Type := K × K × (Matrix (Fin 2) (Fin 2) K × (Fin 2 → K))

@[expose] noncomputable def evHom : Module.End K (DS K) →* Matrix Om Om K where
  toFun e := Matrix.toLin'.symm (decomp.symm.toLinearMap ∘ₗ e ∘ₗ decomp.toLinearMap)
  map_one' := by
    apply Matrix.toLin'.injective
    rw [LinearEquiv.apply_symm_apply, Matrix.toLin'_one]
    ext v
    simp
  map_mul' e f := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply]
    ext v
    simp

theorem evHom_mulVec (e : Module.End K (DS K)) (v : Om → K) :
    evHom e *ᵥ v = decomp.symm (e (decomp v)) := by
  have h := congrArg (fun F : (Om → K) →ₗ[K] (Om → K) => F v)
    (LinearEquiv.apply_symm_apply Matrix.toLin'
      (decomp.symm.toLinearMap ∘ₗ e ∘ₗ decomp.toLinearMap))
  simp only [Matrix.toLin'_apply] at h
  exact h

@[expose] noncomputable def toGL : (Module.End K (DS K))ˣ →* GL Om K := Units.map evHom

theorem coe_toGL (e : (Module.End K (DS K))ˣ) : ((toGL e : GL Om K) : Matrix Om Om K) =
    evHom (e : Module.End K (DS K)) := rfl

theorem toGL_mem_orthGroup (e : (Module.End K (DS K))ˣ)
    (he : ∀ d, Qh (space b c h2) ((e : Module.End K (DS K)) d) = Qh (space b c h2) d) :
    toGL e ∈ orthGroup (StatedQuadMinus 4 K b c) := by
  refine Subgroup.subset_closure ?_
  intro v
  rw [coe_toGL, evHom_mulVec, quad_decomp b c h2, quad_decomp b c h2, LinearEquiv.apply_symm_apply,
    he]

end Transport

section Ops

abbrev XS (K : Type) [Field K] : Type := Matrix (Fin 2) (Fin 2) K × (Fin 2 → K)

@[expose] def lX (g : Matrix (Fin 2) (Fin 2) K) : Module.End K (XS K) where
  toFun x := (g * x.1, x.2)
  map_add' x y := by simp [Matrix.mul_add]
  map_smul' r x := by simp

@[expose] def rX (g : Matrix (Fin 2) (Fin 2) K) : Module.End K (XS K) where
  toFun x := (x.1 * gᵀ, x.2)
  map_add' x y := by simp [Matrix.add_mul]
  map_smul' r x := by simp

@[expose] def aX (g : Matrix (Fin 2) (Fin 2) K) : Module.End K (XS K) where
  toFun x := (x.1, g *ᵥ x.2)
  map_add' x y := by simp [Matrix.mulVec_add]
  map_smul' r x := by simp [Matrix.mulVec_smul]

theorem lX_apply (g : Matrix (Fin 2) (Fin 2) K) (x : XS K) : lX g x = (g * x.1, x.2) := rfl

theorem rX_apply (g : Matrix (Fin 2) (Fin 2) K) (x : XS K) : rX g x = (x.1 * gᵀ, x.2) := rfl

theorem aX_apply (g : Matrix (Fin 2) (Fin 2) K) (x : XS K) : aX g x = (x.1, g *ᵥ x.2) := rfl

@[expose] def lHom : Matrix (Fin 2) (Fin 2) K →* Module.End K (XS K) where
  toFun := lX
  map_one' := LinearMap.ext fun x => by simp [lX_apply]
  map_mul' g h := LinearMap.ext fun x => by simp [lX_apply, Matrix.mul_assoc]

@[expose] def rHom : Matrix (Fin 2) (Fin 2) K →* Module.End K (XS K) where
  toFun := rX
  map_one' := LinearMap.ext fun x => by simp [rX_apply]
  map_mul' g h := LinearMap.ext fun x => by simp [rX_apply, Matrix.mul_assoc]

@[expose] def aHom : Matrix (Fin 2) (Fin 2) K →* Module.End K (XS K) where
  toFun := aX
  map_one' := LinearMap.ext fun x => by simp [aX_apply]
  map_mul' g h := LinearMap.ext fun x => by
    simp only [aX_apply, Module.End.mul_apply, Matrix.mulVec_mulVec]

theorem commute_lX_rX (g h : Matrix (Fin 2) (Fin 2) K) : Commute (lX g) (rX h) :=
  LinearMap.ext fun x => by simp [lX_apply, rX_apply, Module.End.mul_apply, Matrix.mul_assoc]

theorem commute_lX_aX (g h : Matrix (Fin 2) (Fin 2) K) : Commute (lX g) (aX h) :=
  LinearMap.ext fun x => by simp [lX_apply, aX_apply, Module.End.mul_apply]

theorem commute_rX_aX (g h : Matrix (Fin 2) (Fin 2) K) : Commute (rX g) (aX h) :=
  LinearMap.ext fun x => by simp [rX_apply, aX_apply, Module.End.mul_apply]

theorem Q_lX {g : Matrix (Fin 2) (Fin 2) K} (hg : g.det = 1) (x : XS K) :
    (space b c h2).Q (lX g x) = (space b c h2).Q x := by
  simp [space_Q, lX_apply, Matrix.det_mul, hg]

theorem Q_rX {g : Matrix (Fin 2) (Fin 2) K} (hg : g.det = 1) (x : XS K) :
    (space b c h2).Q (rX g x) = (space b c h2).Q x := by
  simp [space_Q, rX_apply, Matrix.det_mul, hg]

theorem Q_aX {g : Matrix (Fin 2) (Fin 2) K} (hg : g * Cm b c = Cm b c * g) (hdet : g.det = 1)
    (x : XS K) : (space b c h2).Q (aX g x) = (space b c h2).Q x := by
  simp only [space_Q, aX_apply]
  rw [Nf_mulVec b c h2 g hg, hdet, one_mul]

theorem Q_tau (x : XS K) : (space b c h2).Q (aX (tauM b) x) = (space b c h2).Q x := by
  simp only [space_Q, aX_apply]
  rw [Nf_tau b c h2]

end Ops

section Homs

@[expose] noncomputable def ΘH (H : Matrix (Fin 2) (Fin 2) K →* Module.End K (XS K)) :
    (Matrix (Fin 2) (Fin 2) K)ˣ →* GL Om K :=
  toGL.comp ((Units.map Gend).comp (Units.map H))

theorem ΘH_mulVec (H : Matrix (Fin 2) (Fin 2) K →* Module.End K (XS K))
    (g : (Matrix (Fin 2) (Fin 2) K)ˣ) (v : Om → K) :
    ((ΘH H g : GL Om K) : Matrix Om Om K) *ᵥ v =
      decomp.symm (Gend (H (g : Matrix (Fin 2) (Fin 2) K)) (decomp v)) :=
  evHom_mulVec _ _

theorem ΘH_mem_orthGroup {H : Matrix (Fin 2) (Fin 2) K →* Module.End K (XS K)}
    {g : (Matrix (Fin 2) (Fin 2) K)ˣ}
    (hg : ∀ x : XS K, (space b c h2).Q (H (g : Matrix (Fin 2) (Fin 2) K) x) =
      (space b c h2).Q x) :
    ΘH H g ∈ orthGroup (StatedQuadMinus 4 K b c) :=
  toGL_mem_orthGroup b c h2 _ (fun d => Qh_Gend (space b c h2) hg d)

@[expose] def tauU : (Matrix (Fin 2) (Fin 2) K)ˣ :=
  ⟨tauM b, tauM b, tauM_mul_self b h2, tauM_mul_self b h2⟩

@[expose] def IsoOn (H : Matrix (Fin 2) (Fin 2) K →* Module.End K (XS K)) : Prop :=
  (∀ x : XS K, (space b c h2).Q (H (tauM b) x) = (space b c h2).Q x) ∧
    ∀ g : Matrix (Fin 2) (Fin 2) K, g * Cm b c = Cm b c * g → g.det = 1 →
      ∀ x : XS K, (space b c h2).Q (H g x) = (space b c h2).Q x

theorem isoOn_lHom : IsoOn b c h2 (lHom (K := K)) :=
  ⟨fun x => Q_lX b c h2 (tauM_det b) x, fun _ _ hdet x => Q_lX b c h2 hdet x⟩

theorem isoOn_rHom : IsoOn b c h2 (rHom (K := K)) :=
  ⟨fun x => Q_rX b c h2 (tauM_det b) x, fun _ _ hdet x => Q_rX b c h2 hdet x⟩

theorem isoOn_aHom : IsoOn b c h2 (aHom (K := K)) :=
  ⟨fun x => Q_tau b c h2 x, fun _ hg hdet x => Q_aX b c h2 hg hdet x⟩

theorem ΘH_mem_Ω {H : Matrix (Fin 2) (Fin 2) K →* Module.End K (XS K)}
    (hH : IsoOn b c h2 H) {ζ : (Matrix (Fin 2) (Fin 2) K)ˣ}
    (hC : (ζ : Matrix (Fin 2) (Fin 2) K) * Cm b c = Cm b c * ζ)
    (hdet : (ζ : Matrix (Fin 2) (Fin 2) K).det = 1) {n : ℕ} (hn : ζ ^ (2 * n + 1) = 1) :
    ΘH H ζ ∈ StatedOmega (StatedQuadMinus 4 K b c) := by
  set g : (Matrix (Fin 2) (Fin 2) K)ˣ := ζ ^ (n + 1) with hg
  have hgC : (g : Matrix (Fin 2) (Fin 2) K) * Cm b c = Cm b c * g := by
    have := (Commute.pow_left (show Commute (ζ : Matrix (Fin 2) (Fin 2) K) (Cm b c) from hC)
      (n + 1)).eq
    simpa [hg, Units.val_pow_eq_pow_val] using this
  have hgdet : (g : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    simp [hg, Units.val_pow_eq_pow_val, Matrix.det_pow, hdet]
  have hτ := tau_conj_mul b c h2 g hgC hgdet
  have hτU : tauU b h2 * g * tauU b h2 * g = 1 := Units.ext (by simpa [tauU] using hτ)
  have hinv : (tauU b h2)⁻¹ = tauU b h2 :=
    inv_eq_of_mul_eq_one_right (Units.ext (by simpa [tauU] using tauM_mul_self b h2))
  have h1 : tauU b h2 * g * tauU b h2 = g⁻¹ := eq_inv_of_mul_eq_one_left hτU
  have hcomm : ⁅tauU b h2, g⁆ = ζ⁻¹ := by
    rw [commutatorElement_def, hinv, h1, ← _root_.mul_inv_rev]
    congr 1
    rw [hg, ← pow_add, show n + 1 + (n + 1) = (2 * n + 1) + 1 by ring, pow_succ, hn, one_mul]
  have hmem : ΘH H ζ⁻¹ ∈ StatedOmega (StatedQuadMinus 4 K b c) := by
    rw [← hcomm, map_commutatorElement]
    exact Subgroup.commutator_mem_commutator (ΘH_mem_orthGroup b c h2 hH.1)
      (ΘH_mem_orthGroup b c h2 (hH.2 _ hgC hgdet))
  rw [map_inv] at hmem
  exact (inv_mem_iff).1 hmem

end Homs

section Triple

variable {G : Type*} [Group G]

@[expose] noncomputable def zmodPow (p : ℕ) (x : G) (hx : x ^ p = 1) :
    Multiplicative (ZMod p) →* G :=
  AddMonoidHom.toMultiplicativeLeft
    (ZMod.lift p ⟨zmultiplesHom (Additive G) (Additive.ofMul x), by
      simp only [zmultiplesHom_apply, natCast_zsmul]
      exact congrArg Additive.ofMul hx⟩)

theorem zmodPow_natCast (p : ℕ) (x : G) (hx : x ^ p = 1) (n : ℕ) :
    zmodPow p x hx (Multiplicative.ofAdd (n : ZMod p)) = x ^ n := by
  have h : (n : ZMod p) = ((n : ℤ) : ZMod p) := (Int.cast_natCast n).symm
  change Additive.toMul (ZMod.lift p _ (n : ZMod p)) = x ^ n
  rw [h, ZMod.lift_coe]
  simp

theorem zmodPow_apply (p : ℕ) [NeZero p] (x : G) (hx : x ^ p = 1) (a : Multiplicative (ZMod p)) :
    zmodPow p x hx a = x ^ (Multiplicative.toAdd a).val := by
  have h : a = Multiplicative.ofAdd (((Multiplicative.toAdd a).val : ℕ) : ZMod p) := by
    rw [ZMod.natCast_zmod_val]
    rfl
  conv_lhs => rw [h]
  exact zmodPow_natCast p x hx _

theorem zmodPow_commute (p : ℕ) [NeZero p] {x y : G} (hx : x ^ p = 1) (hy : y ^ p = 1)
    (hxy : Commute x y) (a b : Multiplicative (ZMod p)) :
    Commute (zmodPow p x hx a) (zmodPow p y hy b) := by
  rw [zmodPow_apply, zmodPow_apply]
  exact hxy.pow_pow _ _

@[expose] noncomputable def tripleHom (p : ℕ) [NeZero p] (x y z : G) (hx : x ^ p = 1)
    (hy : y ^ p = 1) (hz : z ^ p = 1) (hxy : Commute x y) (hxz : Commute x z)
    (hyz : Commute y z) :
    (Multiplicative (ZMod p) × Multiplicative (ZMod p)) × Multiplicative (ZMod p) →* G :=
  MonoidHom.noncommCoprod
    (MonoidHom.noncommCoprod (zmodPow p x hx) (zmodPow p y hy) (zmodPow_commute p hx hy hxy))
    (zmodPow p z hz) (fun m a => by
      rw [MonoidHom.noncommCoprod_apply]
      exact (zmodPow_commute p hx hz hxz _ a).mul_left (zmodPow_commute p hy hz hyz _ a))

theorem tripleHom_apply (p : ℕ) [NeZero p] {x y z : G} (hx : x ^ p = 1) (hy : y ^ p = 1)
    (hz : z ^ p = 1) (hxy : Commute x y) (hxz : Commute x z) (hyz : Commute y z)
    (a b c : Multiplicative (ZMod p)) :
    tripleHom p x y z hx hy hz hxy hxz hyz ((a, b), c) =
      x ^ (Multiplicative.toAdd a).val * y ^ (Multiplicative.toAdd b).val *
        z ^ (Multiplicative.toAdd c).val := by
  simp only [tripleHom, MonoidHom.noncommCoprod_apply, zmodPow_apply]

theorem tripleHom_mem (p : ℕ) [NeZero p] {x y z : G} (hx : x ^ p = 1) (hy : y ^ p = 1)
    (hz : z ^ p = 1) (hxy : Commute x y) (hxz : Commute x z) (hyz : Commute y z)
    (S : Submonoid G) (hxS : x ∈ S) (hyS : y ∈ S) (hzS : z ∈ S)
    (a : (Multiplicative (ZMod p) × Multiplicative (ZMod p)) × Multiplicative (ZMod p)) :
    tripleHom p x y z hx hy hz hxy hxz hyz a ∈ S := by
  obtain ⟨⟨a₁, a₂⟩, a₃⟩ := a
  rw [tripleHom_apply]
  exact S.mul_mem (S.mul_mem (S.pow_mem hxS _) (S.pow_mem hyS _)) (S.pow_mem hzS _)

theorem triple_pow_eq_one (p : ℕ)
    (a : (Multiplicative (ZMod p) × Multiplicative (ZMod p)) × Multiplicative (ZMod p)) :
    a ^ p = 1 := by
  have h : ∀ m : Multiplicative (ZMod p), m ^ p = 1 := by
    intro m
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  obtain ⟨⟨a₁, a₂⟩, a₃⟩ := a
  exact Prod.ext (Prod.ext (h a₁) (h a₂)) (h a₃)

theorem card_triple (p : ℕ) [NeZero p] :
    Nat.card ((Multiplicative (ZMod p) × Multiplicative (ZMod p)) × Multiplicative (ZMod p)) =
      p ^ 3 := by
  have h : Nat.card (Multiplicative (ZMod p)) = p := by
    rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod p) ≃ ZMod p), Nat.card_zmod]
  rw [Nat.card_prod, Nat.card_prod, h]
  ring

end Triple

section Eval

@[expose] noncomputable def vecX (x : XS K) : Om → K := decomp.symm (0, 0, x)

theorem vecX_injective : Function.Injective (vecX (K := K)) := by
  intro x y h
  have := decomp.symm.injective h
  simpa using this

theorem lHom_apply (g : Matrix (Fin 2) (Fin 2) K) : lHom g = lX g := rfl

theorem rHom_apply (g : Matrix (Fin 2) (Fin 2) K) : rHom g = rX g := rfl

theorem aHom_apply (g : Matrix (Fin 2) (Fin 2) K) : aHom g = aX g := rfl

theorem mulVec_ΘH_vecX (H : Matrix (Fin 2) (Fin 2) K →* Module.End K (XS K))
    (g : (Matrix (Fin 2) (Fin 2) K)ˣ) (x : XS K) :
    ((ΘH H g : GL Om K) : Matrix Om Om K) *ᵥ vecX x =
      vecX (H (g : Matrix (Fin 2) (Fin 2) K) x) := by
  rw [ΘH_mulVec, vecX, LinearEquiv.apply_symm_apply]
  rfl

theorem mulVec_triple (g h k : (Matrix (Fin 2) (Fin 2) K)ˣ) (W : Matrix (Fin 2) (Fin 2) K)
    (w : Fin 2 → K) :
    ((ΘH lHom g * ΘH rHom h * ΘH aHom k : GL Om K) : Matrix Om Om K) *ᵥ vecX (W, w) =
      vecX ((g : Matrix (Fin 2) (Fin 2) K) * (W * (h : Matrix (Fin 2) (Fin 2) K)ᵀ),
        (k : Matrix (Fin 2) (Fin 2) K) *ᵥ w) := by
  rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    mulVec_ΘH_vecX, mulVec_ΘH_vecX, mulVec_ΘH_vecX]
  rfl

include h2 in
theorem eq_one_of_sq {a : K} (h : a * a = 1) : a = 1 := by
  have h1 : (a - 1) ^ 2 = 0 := by linear_combination h + (1 - a) * h2
  have h3 := (pow_eq_zero_iff two_ne_zero).1 h1
  linear_combination h3

theorem eq_one_of_mulVec_e0 {k : Matrix (Fin 2) (Fin 2) K} (hk : k * Cm b c = Cm b c * k)
    (h : k *ᵥ ![1, 0] = ![1, 0]) : k = 1 := by
  obtain ⟨e01, e11⟩ := entries_of_comm b c hk
  have h0 : k 0 0 = 1 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun h 0
  have h1 : k 1 0 = 0 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun h 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h0, h1, e01, e11]

include h2 in
theorem eq_one_of_sandwich {g h : Matrix (Fin 2) (Fin 2) K} (hg : g * Cm b c = Cm b c * g)
    (hh : h * Cm b c = Cm b c * h) (hgd : g.det = 1) (hhd : h.det = 1)
    (e : g * (!![1, 0; 0, 0] * hᵀ) = !![1, 0; 0, 0]) : g = 1 ∧ h = 1 := by
  obtain ⟨g01, g11⟩ := entries_of_comm b c hg
  obtain ⟨h01, h11⟩ := entries_of_comm b c hh
  have e00 := congrFun (congrFun e 0) 0
  have e01 := congrFun (congrFun e 0) 1
  have e10 := congrFun (congrFun e 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one] at e00 e01 e10
  have E1 : g 0 0 * h 0 0 = 1 := by linear_combination e00
  have E2 : g 0 0 * h 1 0 = 0 := by linear_combination e01
  have E3 : g 1 0 * h 0 0 = 0 := by linear_combination e10
  have ha : g 0 0 ≠ 0 := fun h0 => by rw [h0, zero_mul] at E1; exact zero_ne_one E1
  have ha' : h 0 0 ≠ 0 := fun h0 => by rw [h0, mul_zero] at E1; exact zero_ne_one E1
  have hγ' : h 1 0 = 0 := (mul_eq_zero.1 E2).resolve_left ha
  have hγ : g 1 0 = 0 := (mul_eq_zero.1 E3).resolve_right ha'
  have hg11 : g 1 1 = g 0 0 := by rw [g11, hγ]; ring
  have hh11 : h 1 1 = h 0 0 := by rw [h11, hγ']; ring
  have hg01 : g 0 1 = 0 := by rw [g01, hγ]; ring
  have hh01 : h 0 1 = 0 := by rw [h01, hγ']; ring
  have hgd' : g 0 0 * g 0 0 = 1 := by
    have := hgd
    rw [Matrix.det_fin_two, hg11, hg01, hγ] at this
    linear_combination this
  have hhd' : h 0 0 * h 0 0 = 1 := by
    have := hhd
    rw [Matrix.det_fin_two, hh11, hh01, hγ'] at this
    linear_combination this
  have hga := eq_one_of_sq h2 hgd'
  have hha := eq_one_of_sq h2 hhd'
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [hga, hg01, hγ, hg11]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [hha, hh01, hγ', hh11]

include h2 in
theorem triple_eq_one {g h k : (Matrix (Fin 2) (Fin 2) K)ˣ}
    (hg : (g : Matrix (Fin 2) (Fin 2) K) * Cm b c = Cm b c * g)
    (hh : (h : Matrix (Fin 2) (Fin 2) K) * Cm b c = Cm b c * h)
    (hk : (k : Matrix (Fin 2) (Fin 2) K) * Cm b c = Cm b c * k)
    (hgd : (g : Matrix (Fin 2) (Fin 2) K).det = 1) (hhd : (h : Matrix (Fin 2) (Fin 2) K).det = 1)
    (e : (ΘH lHom g * ΘH rHom h * ΘH aHom k : GL Om K) = 1) : g = 1 ∧ h = 1 ∧ k = 1 := by
  have h0 := mulVec_triple g h k !![1, 0; 0, 0] ![1, 0]
  rw [e, Units.val_one, Matrix.one_mulVec] at h0
  have h' := vecX_injective h0
  obtain ⟨h1, h3⟩ := Prod.ext_iff.1 h'
  obtain ⟨hg1, hh1⟩ := eq_one_of_sandwich b c h2 hg hh hgd hhd h1.symm
  have hk1 := eq_one_of_mulVec_e0 b c hk h3.symm
  exact ⟨Units.ext hg1, Units.ext hh1, Units.ext hk1⟩

end Eval

section TopPlane

@[expose] noncomputable def topH : Multiplicative (Fin 2 → K) →* GL Om K :=
  toGL.comp (((Tend (space b c h2)).comp (AddMonoidHom.toMultiplicative
    (AddMonoidHom.inr (Matrix (Fin 2) (Fin 2) K) (Fin 2 → K)))).toHomUnits)

theorem topH_mulVec (w : Multiplicative (Fin 2 → K)) (v : Om → K) :
    ((topH b c h2 w : GL Om K) : Matrix Om Om K) *ᵥ v =
      decomp.symm (Top (space b c h2) ((0 : Matrix (Fin 2) (Fin 2) K), Multiplicative.toAdd w)
        (decomp v)) :=
  evHom_mulVec _ _

theorem topH_mem_orthGroup (w : Multiplicative (Fin 2 → K)) :
    topH b c h2 w ∈ orthGroup (StatedQuadMinus 4 K b c) :=
  toGL_mem_orthGroup b c h2 _ (fun d => Qh_Top (space b c h2) h2 _ d)

theorem ΘH_mul_topH {H : Matrix (Fin 2) (Fin 2) K →* Module.End K (XS K)}
    {g : (Matrix (Fin 2) (Fin 2) K)ˣ}
    (hg : ∀ x : XS K, (space b c h2).Q (H (g : Matrix (Fin 2) (Fin 2) K) x) =
      (space b c h2).Q x) (w w' : Fin 2 → K)
    (hw : H (g : Matrix (Fin 2) (Fin 2) K) (0, w) = (0, w')) :
    ΘH H g * topH b c h2 (Multiplicative.ofAdd w) =
      topH b c h2 (Multiplicative.ofAdd w') * ΘH H g := by
  have key := Gend_mul_Top (space b c h2) hg ((0 : Matrix (Fin 2) (Fin 2) K), w)
  rw [hw] at key
  simp only [ΘH, topH, MonoidHom.comp_apply]
  rw [← map_mul, ← map_mul]
  congr 1
  exact Units.ext key

theorem topH_sub_eq_commutator {ζ : (Matrix (Fin 2) (Fin 2) K)ˣ}
    (hC : (ζ : Matrix (Fin 2) (Fin 2) K) * Cm b c = Cm b c * ζ)
    (hdet : (ζ : Matrix (Fin 2) (Fin 2) K).det = 1) (w : Fin 2 → K) :
    topH b c h2 (Multiplicative.ofAdd ((ζ : Matrix (Fin 2) (Fin 2) K) *ᵥ w - w)) =
      ⁅ΘH aHom ζ, topH b c h2 (Multiplicative.ofAdd w)⁆ := by
  have h := ΘH_mul_topH b c h2 (H := aHom) (g := ζ)
    (fun x => Q_aX b c h2 hC hdet x) w ((ζ : Matrix (Fin 2) (Fin 2) K) *ᵥ w)
    (by rw [aHom_apply, aX_apply])
  rw [commutatorElement_def, h, mul_inv_cancel_right, ← map_inv, ← map_mul, ofAdd_sub,
    div_eq_mul_inv]

theorem topH_mem_Ω {ζ : (Matrix (Fin 2) (Fin 2) K)ˣ}
    (hC : (ζ : Matrix (Fin 2) (Fin 2) K) * Cm b c = Cm b c * ζ)
    (hdet : (ζ : Matrix (Fin 2) (Fin 2) K).det = 1) (w : Fin 2 → K) :
    topH b c h2 (Multiplicative.ofAdd (((ζ : Matrix (Fin 2) (Fin 2) K) - 1) *ᵥ w)) ∈
      StatedOmega (StatedQuadMinus 4 K b c) := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, topH_sub_eq_commutator b c h2 hC hdet]
  exact Subgroup.commutator_mem_commutator
    (ΘH_mem_orthGroup b c h2 (H := aHom) (g := ζ) ((isoOn_aHom b c h2).2 _ hC hdet))
    (topH_mem_orthGroup b c h2 _)

theorem topH_injective : Function.Injective (topH b c h2) := by
  rw [injective_iff_map_eq_one]
  intro w hw
  have h1 := congrArg (fun A : GL Om K => (A : Matrix Om Om K) *ᵥ decomp.symm (0, 1, 0)) hw
  simp only [topH_mulVec, LinearEquiv.apply_symm_apply, Units.val_one, Matrix.one_mulVec] at h1
  have h3 := decomp.symm.injective h1
  have h4 := congrArg (fun d : K × K × XS K => d.2.2.2) h3
  simpa [Top_apply] using h4

end TopPlane

section Witness

theorem pow_comm_det {ζ : (Matrix (Fin 2) (Fin 2) K)ˣ}
    (hC : (ζ : Matrix (Fin 2) (Fin 2) K) * Cm b c = Cm b c * ζ)
    (hdet : (ζ : Matrix (Fin 2) (Fin 2) K).det = 1) (i : ℕ) :
    ((ζ ^ i : (Matrix (Fin 2) (Fin 2) K)ˣ) : Matrix (Fin 2) (Fin 2) K) * Cm b c =
        Cm b c * ((ζ ^ i : (Matrix (Fin 2) (Fin 2) K)ˣ) : Matrix (Fin 2) (Fin 2) K) ∧
      ((ζ ^ i : (Matrix (Fin 2) (Fin 2) K)ˣ) : Matrix (Fin 2) (Fin 2) K).det = 1 := by
  refine ⟨?_, ?_⟩
  · have := (Commute.pow_left (show Commute (ζ : Matrix (Fin 2) (Fin 2) K) (Cm b c) from hC)
      i).eq
    simpa [Units.val_pow_eq_pow_val] using this
  · simp [Units.val_pow_eq_pow_val, Matrix.det_pow, hdet]

theorem commute_ΘH {H H' : Matrix (Fin 2) (Fin 2) K →* Module.End K (XS K)}
    (g g' : (Matrix (Fin 2) (Fin 2) K)ˣ)
    (h : Commute (H (g : Matrix (Fin 2) (Fin 2) K)) (H' (g' : Matrix (Fin 2) (Fin 2) K))) :
    Commute (ΘH H g) (ΘH H' g') := by
  have h' : Commute (Units.map H g) (Units.map H' g') := Units.ext h.eq
  exact (h'.map (Units.map Gend)).map toGL

variable [Finite K] [CharP K 2]

theorem three_le_localRank_statedProj_statedOmegaMinus
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K + 1) :
    3 ≤ localRank p (StatedProj (StatedOmega (StatedQuadMinus 4 K b c))) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  rw [← CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv
    (equivProjOfScalarsBot _ (statedScalars_subgroupOf_statedOmega_quadMinus_eq_bot (K := K)
      (b := b) (c := c))) hp]
  obtain ⟨ζ, hζo, hζC, hζdet⟩ := exists_order_centralizer b c h2 hirr hp hp2 hpq
  set Ω : Subgroup (GL Om K) := StatedOmega (StatedQuadMinus 4 K b c) with hΩ
  obtain ⟨n, hn⟩ := hp.odd_of_ne_two hp2
  have hζp : ζ ^ p = 1 := by
    rw [← hζo]
    exact pow_orderOf_eq_one ζ
  have hζn : ζ ^ (2 * n + 1) = 1 := by
    rw [← hn]
    exact hζp
  have hL : ΘH lHom ζ ∈ Ω := ΘH_mem_Ω b c h2 (isoOn_lHom b c h2) hζC hζdet hζn
  have hR : ΘH rHom ζ ∈ Ω := ΘH_mem_Ω b c h2 (isoOn_rHom b c h2) hζC hζdet hζn
  have hA : ΘH aHom ζ ∈ Ω := ΘH_mem_Ω b c h2 (isoOn_aHom b c h2) hζC hζdet hζn
  let gL : Ω := ⟨ΘH lHom ζ, hL⟩
  let gR : Ω := ⟨ΘH rHom ζ, hR⟩
  let gA : Ω := ⟨ΘH aHom ζ, hA⟩
  have hgL : gL ^ p = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    change (ΘH lHom ζ) ^ p = 1
    rw [← map_pow, hζp, map_one])
  have hgR : gR ^ p = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    change (ΘH rHom ζ) ^ p = 1
    rw [← map_pow, hζp, map_one])
  have hgA : gA ^ p = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    change (ΘH aHom ζ) ^ p = 1
    rw [← map_pow, hζp, map_one])
  have cLR : Commute gL gR :=
    Subtype.ext (commute_ΘH (H := lHom) (H' := rHom) ζ ζ (commute_lX_rX _ _)).eq
  have cLA : Commute gL gA :=
    Subtype.ext (commute_ΘH (H := lHom) (H' := aHom) ζ ζ (commute_lX_aX _ _)).eq
  have cRA : Commute gR gA :=
    Subtype.ext (commute_ΘH (H := rHom) (H' := aHom) ζ ζ (commute_rX_aX _ _)).eq
  let ψ := tripleHom p gL gR gA hgL hgR hgA cLR cLA cRA
  have key : ∀ a : Multiplicative (ZMod p), ζ ^ (Multiplicative.toAdd a).val = 1 → a = 1 := by
    intro a ha
    have h1 : orderOf ζ ∣ (Multiplicative.toAdd a).val := orderOf_dvd_of_pow_eq_one ha
    rw [hζo] at h1
    have h3 : (Multiplicative.toAdd a).val = 0 := Nat.eq_zero_of_dvd_of_lt h1 (ZMod.val_lt _)
    exact toAdd_eq_zero.1 ((ZMod.val_eq_zero _).1 h3)
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨⟨a₁, a₂⟩, a₃⟩ h
    have h' := congrArg Subtype.val h
    simp only [ψ, tripleHom_apply, Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_one] at h'
    change (ΘH lHom ζ) ^ (Multiplicative.toAdd a₁).val *
      (ΘH rHom ζ) ^ (Multiplicative.toAdd a₂).val *
      (ΘH aHom ζ) ^ (Multiplicative.toAdd a₃).val = 1 at h'
    rw [← map_pow, ← map_pow, ← map_pow] at h'
    obtain ⟨h₁, h₂, h₃⟩ := triple_eq_one b c h2 (pow_comm_det b c hζC hζdet _).1
      (pow_comm_det b c hζC hζdet _).1 (pow_comm_det b c hζC hζdet _).1
      (pow_comm_det b c hζC hζdet _).2 (pow_comm_det b c hζC hζdet _).2 h'
    exact Prod.ext (Prod.ext (key _ h₁) (key _ h₂)) (key _ h₃)
  have hc : Nat.card ψ.range = p ^ 3 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv]
    exact card_triple p
  have hE : CFSG.Assembly.IsElemAbelian p ψ.range :=
    CFSG.RankThree.PartTwo.Census.isElemAbelian_range (fun a => triple_pow_eq_one p a) ψ
  let dz : (Fin 2 → K) →+ (Fin 2 → K) :=
    (Matrix.mulVecLin ((ζ : Matrix (Fin 2) (Fin 2) K) - 1)).toAddMonoidHom
  let ρ : Multiplicative (Fin 2 → K) →* Ω :=
    ((topH b c h2).comp (AddMonoidHom.toMultiplicative dz)).codRestrict Ω
      (fun w => topH_mem_Ω b c h2 hζC hζdet (Multiplicative.toAdd w))
  have hsq : ∀ z : Multiplicative (Fin 2 → K), z * z = 1 := by
    intro z
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_one]
    funext i
    simp only [Pi.add_apply, Pi.zero_apply]
    linear_combination (Multiplicative.toAdd z i) * h2
  have hP2 : IsPGroup 2 ρ.range := by
    intro y
    obtain ⟨x, hx⟩ := y.2
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one, pow_two, ← hx, ← map_mul, hsq, map_one]
  have hP0 : ρ.range ≠ ⊥ := by
    intro h
    have hw : ((ζ : Matrix (Fin 2) (Fin 2) K) - 1) *ᵥ ![1, 0] ≠ 0 := by
      intro h0
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h0
      have h1 := eq_one_of_mulVec_e0 b c hζC h0
      have h3 : ζ = 1 := Units.ext h1
      rw [h3, orderOf_one] at hζo
      exact hp.one_lt.ne hζo
    have hmem : ρ (Multiplicative.ofAdd ![1, 0]) ∈ ρ.range := ⟨_, rfl⟩
    rw [h, Subgroup.mem_bot] at hmem
    have h3 : topH b c h2
        (Multiplicative.ofAdd (((ζ : Matrix (Fin 2) (Fin 2) K) - 1) *ᵥ ![1, 0])) = 1 :=
      congrArg Subtype.val hmem
    have h4 := topH_injective b c h2 (h3.trans (map_one _).symm)
    exact hw (ofAdd_eq_one.1 h4)
  have hcomm : ∀ w : Fin 2 → K,
      (ζ : Matrix (Fin 2) (Fin 2) K) *ᵥ (((ζ : Matrix (Fin 2) (Fin 2) K) - 1) *ᵥ w) =
      ((ζ : Matrix (Fin 2) (Fin 2) K) - 1) *ᵥ ((ζ : Matrix (Fin 2) (Fin 2) K) *ᵥ w) := by
    intro w
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_sub, Matrix.sub_mul, mul_one,
      one_mul]
  let Nm : Submonoid Ω :=
    { carrier := {x | ∀ y ∈ ρ.range, x * y * x⁻¹ ∈ ρ.range}
      one_mem' := fun y hy => by simpa using hy
      mul_mem' := fun {x x'} hx hx' y hy => by
        have := hx _ (hx' y hy)
        simpa [mul_assoc] using this }
  have hNL : gL ∈ Nm := by
    rintro _ ⟨x, rfl⟩
    have h1 : gL * ρ x = ρ x * gL := Subtype.ext (ΘH_mul_topH b c h2 (H := lHom) (g := ζ)
      (fun w => Q_lX b c h2 hζdet w) (dz (Multiplicative.toAdd x)) (dz (Multiplicative.toAdd x))
      (by rw [lHom_apply, lX_apply]; simp))
    rw [mul_inv_eq_of_eq_mul h1]
    exact ⟨x, rfl⟩
  have hNR : gR ∈ Nm := by
    rintro _ ⟨x, rfl⟩
    have h1 : gR * ρ x = ρ x * gR := Subtype.ext (ΘH_mul_topH b c h2 (H := rHom) (g := ζ)
      (fun w => Q_rX b c h2 hζdet w) (dz (Multiplicative.toAdd x)) (dz (Multiplicative.toAdd x))
      (by rw [rHom_apply, rX_apply]; simp))
    rw [mul_inv_eq_of_eq_mul h1]
    exact ⟨x, rfl⟩
  have hcomm' : ∀ w : Fin 2 → K, (ζ : Matrix (Fin 2) (Fin 2) K) *ᵥ dz w =
      dz ((ζ : Matrix (Fin 2) (Fin 2) K) *ᵥ w) := fun w => hcomm w
  have hNA : gA ∈ Nm := by
    rintro _ ⟨x, rfl⟩
    have h1 : gA * ρ x = ρ (Multiplicative.ofAdd ((ζ : Matrix (Fin 2) (Fin 2) K) *ᵥ
        Multiplicative.toAdd x)) * gA := by
      refine Subtype.ext ?_
      have := ΘH_mul_topH b c h2 (H := aHom) (g := ζ) (fun w => Q_aX b c h2 hζC hζdet w)
        (dz (Multiplicative.toAdd x)) ((ζ : Matrix (Fin 2) (Fin 2) K) *ᵥ
          dz (Multiplicative.toAdd x)) (by rw [aHom_apply, aX_apply])
      rw [hcomm'] at this
      exact this
    rw [mul_inv_eq_of_eq_mul h1]
    exact ⟨_, rfl⟩
  have hEP : ψ.range ≤ Subgroup.normalizer (ρ.range : Set Ω) := by
    refine CFSG.RankThree.PartTwo.Census.le_normalizer_of_conj_mem ?_
    rintro _ ⟨a, rfl⟩ y hy
    exact tripleHom_mem p hgL hgR hgA cLR cLA cRA Nm hNL hNR hNA a y hy
  exact CFSG.RankThree.PartTwo.Census.le_localRank_of_le_normalizer hp hP0 hP2 hE hc hEP

end Witness

end CFSG.RankThree.PartOne.KFU.QPlus

namespace CFSG.RankThree.PartOne

theorem omegaEightMinusQPlus : OmegaEightMinusQPlus :=
  fun _ _ _ _ b c hirr _ hp hp2 hpq =>
    KFU.QPlus.three_le_localRank_statedProj_statedOmegaMinus b c hirr hp hp2 hpq

theorem omegaEightMinusNotTwo : OmegaEightMinusNotTwo :=
  omegaEightMinusNotTwo_of_qPlus omegaEightMinusQPlus

end CFSG.RankThree.PartOne
