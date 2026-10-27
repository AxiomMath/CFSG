module

public import CFSG.Quasithin.H13.A6S1372L76N3b
public import CFSG.Quasithin.H13.Sp62Over

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge CFSG.Assembly.LowTwoRank
open scoped Pointwise IsMulCommutative Matrix

namespace A6L76N3

section Matrix

open A6L76Of

theorem exists_natHom_eq (f : MulAut (Multiplicative (Fin 3 → ZMod 2))) :
    ∃ γ : ↥(StatedSL 3 (ZMod 2)), natHom γ = f := by
  let g : (Fin 3 → ZMod 2) →+ (Fin 3 → ZMod 2) :=
    { toFun := fun v => Multiplicative.toAdd (f (Multiplicative.ofAdd v))
      map_zero' := by simp
      map_add' := fun v w => by simp }
  let g' : (Fin 3 → ZMod 2) →+ (Fin 3 → ZMod 2) :=
    { toFun := fun v => Multiplicative.toAdd (f⁻¹ (Multiplicative.ofAdd v))
      map_zero' := by simp
      map_add' := fun v w => by simp }
  have key : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  let gl : (Fin 3 → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2) :=
    { toFun := g
      map_add' := g.map_add
      map_smul' := fun c v => by rcases key c with rfl | rfl <;> simp }
  let gl' : (Fin 3 → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2) :=
    { toFun := g'
      map_add' := g'.map_add
      map_smul' := fun c v => by rcases key c with rfl | rfl <;> simp }
  set A := LinearMap.toMatrix' gl with hA
  set B := LinearMap.toMatrix' gl' with hB
  have hAv : ∀ v, A *ᵥ v = g v := fun v => LinearMap.toMatrix'_mulVec gl v
  have hBv : ∀ v, B *ᵥ v = g' v := fun v => LinearMap.toMatrix'_mulVec gl' v
  have hgg' : ∀ v, g (g' v) = v := fun v => by
    show Multiplicative.toAdd (f (Multiplicative.ofAdd (Multiplicative.toAdd
      (f⁻¹ (Multiplicative.ofAdd v))))) = v
    rw [ofAdd_toAdd, MulAut.apply_inv_self]
    rfl
  have hg'g : ∀ v, g' (g v) = v := fun v => by
    show Multiplicative.toAdd (f⁻¹ (Multiplicative.ofAdd (Multiplicative.toAdd
      (f (Multiplicative.ofAdd v))))) = v
    rw [ofAdd_toAdd, MulAut.inv_apply_self]
    rfl
  have hAB : A * B = 1 := by
    refine Matrix.ext_of_mulVec_single fun j => ?_
    rw [← Matrix.mulVec_mulVec, hBv, hAv, hgg', Matrix.one_mulVec]
  have hBA : B * A = 1 := by
    refine Matrix.ext_of_mulVec_single fun j => ?_
    rw [← Matrix.mulVec_mulVec, hAv, hBv, hg'g, Matrix.one_mulVec]
  have hdet : A.det = 1 := by
    have h1 : A.det * B.det = 1 := by rw [← Matrix.det_mul, hAB, Matrix.det_one]
    have h2 : A.det ≠ 0 := fun h => by rw [h, zero_mul] at h1; exact zero_ne_one h1
    rcases key A.det with h | h
    · exact absurd h h2
    · exact h
  refine ⟨⟨⟨A, B, hAB, hBA⟩, Subgroup.subset_closure hdet⟩, ?_⟩
  refine MulEquiv.ext fun m => ?_
  apply Multiplicative.toAdd.injective
  rw [natHom_apply]
  exact hAv _

@[expose] noncomputable def natHomEquiv :
    ↥(StatedSL 3 (ZMod 2)) ≃* MulAut (Multiplicative (Fin 3 → ZMod 2)) :=
  MulEquiv.ofBijective natHom ⟨natHom_injective, fun f => exists_natHom_eq f⟩

theorem natHomEquiv_apply (γ : ↥(StatedSL 3 (ZMod 2))) : natHomEquiv γ = natHom γ := rfl

@[expose] noncomputable def toSL : MulAut (Multiplicative (Fin 3 → ZMod 2)) ≃* SL3.S :=
  natHomEquiv.symm.trans (specialLinearGroupEquivStatedSL 3 (ZMod 2)).symm

theorem toSL_mulVec (f : MulAut (Multiplicative (Fin 3 → ZMod 2))) (v : Fin 3 → ZMod 2) :
    ((toSL f : SL3.S) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v =
      Multiplicative.toAdd (f (Multiplicative.ofAdd v)) := by
  have h1 := specialLinearGroupEquivStatedSL_coe 3 (ZMod 2) (toSL f)
  have h2 : specialLinearGroupEquivStatedSL 3 (ZMod 2) (toSL f) = natHomEquiv.symm f :=
    (specialLinearGroupEquivStatedSL 3 (ZMod 2)).apply_symm_apply (natHomEquiv.symm f)
  have h3 : natHom (natHomEquiv.symm f) = f := natHomEquiv.apply_symm_apply f
  rw [← h1, h2]
  calc _ = Multiplicative.toAdd (natHom (natHomEquiv.symm f) (Multiplicative.ofAdd v)) := by
          rw [natHom_apply, toAdd_ofAdd]
    _ = _ := by rw [h3]

end Matrix

section Lift

variable {W : Type*} [CommGroup W] {Y : Subgroup (MulAut W)} {M : Type*} [CommGroup M]
  {β : ↥(commV Y) →* M}

theorem conj_mem_of_normalizer {b : MulAut W}
    (hb : b ∈ Subgroup.normalizer (Y : Set (MulAut W))) : ∀ y ∈ Y, b * y * b⁻¹ ∈ Y :=
  fun y hy => (Subgroup.mem_normalizer_iff.mp hb y).mp hy

theorem conj_inv_mem_of_normalizer {b : MulAut W}
    (hb : b ∈ Subgroup.normalizer (Y : Set (MulAut W))) : ∀ y ∈ Y, b⁻¹ * y * b ∈ Y := by
  intro y hy
  have h := conj_mem_of_normalizer (Subgroup.inv_mem _ hb) y hy
  rwa [inv_inv] at h

@[expose] noncomputable def liftFun (hβs : Function.Surjective β)
    (b : ↥(Subgroup.normalizer (Y : Set (MulAut W)))) (m : M) : M :=
  β ⟨(b : MulAut W) ((Function.surjInv hβs m : ↥(commV Y)) : W),
    A6L76Of.apply_mem_commV_of_conj (conj_mem_of_normalizer b.2) (Function.surjInv hβs m).2⟩

theorem liftFun_apply (hβs : Function.Surjective β)
    (hβk : ∀ u, β u = 1 ↔ (u : W) ∈ fixV Y ⊓ commV Y)
    (b : ↥(Subgroup.normalizer (Y : Set (MulAut W)))) (u : ↥(commV Y)) :
    liftFun hβs b (β u) = β ⟨(b : MulAut W) (u : W),
      A6L76Of.apply_mem_commV_of_conj (conj_mem_of_normalizer b.2) u.2⟩ := by
  unfold liftFun
  set s := Function.surjInv hβs (β u) with hs
  have hsu : β s = β u := Function.surjInv_eq hβs _
  have h1 : β (s * u⁻¹) = 1 := by rw [map_mul, map_inv, hsu, mul_inv_cancel]
  rw [← mul_inv_eq_one, ← map_inv, ← map_mul, hβk]
  show (b : MulAut W) (s : W) * ((b : MulAut W) (u : W))⁻¹ ∈ fixV Y ⊓ commV Y
  rw [← map_inv, ← map_mul]
  obtain ⟨hf, hc⟩ := (hβk _).1 h1
  exact ⟨A6L76Of.apply_mem_fixV_of_conj (conj_inv_mem_of_normalizer b.2) hf,
    A6L76Of.apply_mem_commV_of_conj (conj_mem_of_normalizer b.2) hc⟩

@[expose] noncomputable def liftHom (hβs : Function.Surjective β)
    (hβk : ∀ u, β u = 1 ↔ (u : W) ∈ fixV Y ⊓ commV Y) :
    ↥(Subgroup.normalizer (Y : Set (MulAut W))) →* MulAut M where
  toFun b :=
    { toFun := liftFun hβs b
      invFun := liftFun hβs b⁻¹
      left_inv := fun m => by
        obtain ⟨u, rfl⟩ := hβs m
        rw [liftFun_apply hβs hβk, liftFun_apply hβs hβk]
        congr 1
        apply Subtype.ext
        show ((b⁻¹ : ↥(Subgroup.normalizer (Y : Set (MulAut W)))) : MulAut W)
          ((b : MulAut W) (u : W)) = u
        rw [Subgroup.coe_inv, MulAut.inv_apply_self]
      right_inv := fun m => by
        obtain ⟨u, rfl⟩ := hβs m
        rw [liftFun_apply hβs hβk, liftFun_apply hβs hβk]
        congr 1
        apply Subtype.ext
        show (b : MulAut W) (((b⁻¹ : ↥(Subgroup.normalizer (Y : Set (MulAut W)))) : MulAut W)
          (u : W)) = u
        rw [Subgroup.coe_inv, MulAut.apply_inv_self]
      map_mul' := fun m m' => by
        obtain ⟨u, rfl⟩ := hβs m
        obtain ⟨u', rfl⟩ := hβs m'
        rw [← map_mul, liftFun_apply hβs hβk, liftFun_apply hβs hβk, liftFun_apply hβs hβk,
          ← map_mul]
        congr 1
        apply Subtype.ext
        simp }
  map_one' := by
    refine MulEquiv.ext fun m => ?_
    obtain ⟨u, rfl⟩ := hβs m
    show liftFun hβs 1 (β u) = β u
    rw [liftFun_apply hβs hβk]
    rfl
  map_mul' b c := by
    refine MulEquiv.ext fun m => ?_
    obtain ⟨u, rfl⟩ := hβs m
    show liftFun hβs (b * c) (β u) = liftFun hβs b (liftFun hβs c (β u))
    rw [liftFun_apply hβs hβk, liftFun_apply hβs hβk, liftFun_apply hβs hβk]
    rfl

theorem liftHom_apply (hβs : Function.Surjective β)
    (hβk : ∀ u, β u = 1 ↔ (u : W) ∈ fixV Y ⊓ commV Y)
    (b : ↥(Subgroup.normalizer (Y : Set (MulAut W)))) (u : ↥(commV Y)) :
    liftHom hβs hβk b (β u) = β ⟨(b : MulAut W) (u : W),
      A6L76Of.apply_mem_commV_of_conj (conj_mem_of_normalizer b.2) u.2⟩ :=
  liftFun_apply hβs hβk b u

end Lift

section LiftNat

open A6L76Of

variable {W : Type*} [CommGroup W] {Y : Subgroup (MulAut W)} {F : Type} [Field F]

theorem liftHom_of_mem {π : ↥(StatedSL 3 F) →* ↥Y}
    {β : ↥(commV Y) →* Multiplicative (Fin 3 → F)} (hβs : Function.Surjective β)
    (hβk : ∀ u, β u = 1 ↔ (u : W) ∈ fixV Y ⊓ commV Y)
    (hβe : ∀ (γ : ↥(StatedSL 3 F)) (u : ↥(commV Y))
      (hu : ((π γ : ↥Y) : MulAut W) (u : W) ∈ commV Y), β ⟨_, hu⟩ = natHom γ (β u))
    (γ : ↥(StatedSL 3 F))
    (hγ : ((π γ : ↥Y) : MulAut W) ∈ Subgroup.normalizer (Y : Set (MulAut W))) :
    liftHom hβs hβk ⟨_, hγ⟩ = natHom γ := by
  refine MulEquiv.ext fun m => ?_
  obtain ⟨u, rfl⟩ := hβs m
  rw [liftHom_apply]
  exact hβe γ u _

end LiftNat

end A6L76N3

end CFSG.Quasithin.H13.A6
