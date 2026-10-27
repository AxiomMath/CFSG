module

public import CFSG.Quasithin.H13.A6S1372L76Of2

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative Matrix

namespace A6L76Oh

open A6L76Of

section Nat

variable {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]

@[expose] def glMulAutG (g : GL ι F) : MulAut (Multiplicative (ι → F)) where
  toFun v := Multiplicative.ofAdd ((g : Matrix ι ι F) *ᵥ v.toAdd)
  invFun v := Multiplicative.ofAdd (((g⁻¹ : GL ι F) : Matrix ι ι F) *ᵥ v.toAdd)
  left_inv v := by
    simp only [toAdd_ofAdd, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec, ofAdd_toAdd]
  right_inv v := by
    simp only [toAdd_ofAdd, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec, ofAdd_toAdd]
  map_mul' v w := by
    simp only [toAdd_mul, Matrix.mulVec_add, ofAdd_add]

@[expose] def glHomG : GL ι F →* MulAut (Multiplicative (ι → F)) where
  toFun := glMulAutG
  map_one' := by
    ext v
    simp [glMulAutG]
  map_mul' g h := by
    ext v
    simp [glMulAutG, Matrix.mulVec_mulVec]

theorem natRealizes_clean {W : Type*} [CommGroup W] {Y : Subgroup (MulAut W)} {U Z : Subgroup W}
    {Γ : Subgroup (GL ι F)} {π : ↥Γ →* ↥Y} (h : (FFModel.nat Γ).RealizesVia Y U Z π) :
    Function.Surjective π ∧ (∀ y : ↥Y, ∀ u ∈ U, (y : MulAut W) u ∈ U) ∧
      ∃ β : ↥U →* Multiplicative (ι → F), Function.Surjective β ∧
        (∀ u, β u = 1 ↔ (u : W) ∈ Z) ∧
        ∀ (γ : ↥Γ) (u : ↥U) (hu : ((π γ : ↥Y) : MulAut W) (u : W) ∈ U),
          β ⟨_, hu⟩ = glHomG (γ : GL ι F) (β u) := by
  obtain ⟨hs, -, -, hU, -, -, -, β, hβs, hβk, hβe⟩ := h
  let e : (↥(FFModel.nat Γ).sec ⧸ (FFModel.nat Γ).ker.subgroupOf (FFModel.nat Γ).sec) ≃*
      Multiplicative (ι → F) :=
    ((QuotientGroup.quotientMulEquivOfEq (show (FFModel.nat Γ).ker.subgroupOf
        (FFModel.nat Γ).sec = ⊥ from Subgroup.bot_subgroupOf _)).trans
          QuotientGroup.quotientBot).trans Subgroup.topEquiv
  refine ⟨hs, hU, e.toMonoidHom.comp β, e.surjective.comp hβs, fun u => ?_, fun γ u hu => ?_⟩
  · show e (β u) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff]
    exact hβk u
  · obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β u)
    have h1 := hβe γ u m hu (Subgroup.mem_top _) hm.symm
    show e (β ⟨_, hu⟩) = glHomG (γ : GL ι F) (e (β u))
    refine (congrArg e h1).trans ?_
    rw [← hm]
    rfl

end Nat

section Lift

variable {W : Type*} [CommGroup W] {Y : Subgroup (MulAut W)} {M : Type*} [CommGroup M]
  {β : ↥(commV Y) →* M}

theorem exists_lift (hβs : Function.Surjective β)
    (hβk : ∀ u, β u = 1 ↔ (u : W) ∈ fixV Y ⊓ commV Y) {b : MulAut W}
    (hb : ∀ y ∈ Y, b * y * b⁻¹ ∈ Y) (hb' : ∀ y ∈ Y, b⁻¹ * y * b ∈ Y) :
    ∃ f : M →* M, ∀ (u : ↥(commV Y)) (hu : b (u : W) ∈ commV Y), f (β u) = β ⟨b u, hu⟩ := by
  let bU : ↥(commV Y) →* ↥(commV Y) :=
    (b.toMonoidHom.comp (commV Y).subtype).codRestrict (commV Y) fun u =>
      apply_mem_commV_of_conj hb u.2
  have hker : β.ker ≤ (β.comp bU).ker := by
    intro u hu
    rw [MonoidHom.mem_ker] at hu ⊢
    rw [MonoidHom.comp_apply, hβk]
    have h1 := (hβk u).1 hu
    exact ⟨apply_mem_fixV_of_conj hb' h1.1, apply_mem_commV_of_conj hb h1.2⟩
  exact ⟨(β.liftOfRightInverse (Function.surjInv hβs) (Function.rightInverse_surjInv hβs))
    ⟨β.comp bU, hker⟩, fun u _ => MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ u⟩

variable {Γ : Type*} [Group Γ] {π : Γ →* ↥Y} {ρ : Γ →* MulAut M} {b : MulAut W} {f : M →* M}

variable (hβe : ∀ (γ : Γ) (u : ↥(commV Y))
  (hu : ((π γ : ↥Y) : MulAut W) (u : W) ∈ commV Y), β ⟨_, hu⟩ = ρ γ (β u))
include hβe

theorem lift_hom (hβs : Function.Surjective β) (hb : ∀ y ∈ Y, b * y * b⁻¹ ∈ Y)
    (hf : ∀ (u : ↥(commV Y)) (hu : b (u : W) ∈ commV Y), f (β u) = β ⟨b u, hu⟩)
    {γ γ' : Γ} (hγ : ((π γ' : ↥Y) : MulAut W) * b = b * ((π γ : ↥Y) : MulAut W)) (m : M) :
    f (ρ γ m) = ρ γ' (f m) := by
  obtain ⟨u, rfl⟩ := hβs m
  have hu1 : ((π γ : ↥Y) : MulAut W) (u : W) ∈ commV Y := A6L76Oe.apply_mem_commV (π γ).2 u.2
  have hu2 : b (u : W) ∈ commV Y := apply_mem_commV_of_conj hb u.2
  have hu3 : b (((π γ : ↥Y) : MulAut W) (u : W)) ∈ commV Y := apply_mem_commV_of_conj hb hu1
  have hu4 : ((π γ' : ↥Y) : MulAut W) (b (u : W)) ∈ commV Y :=
    A6L76Oe.apply_mem_commV (π γ').2 hu2
  have e : (⟨b (((π γ : ↥Y) : MulAut W) (u : W)), hu3⟩ : ↥(commV Y)) = ⟨_, hu4⟩ :=
    Subtype.ext (by
      show b (((π γ : ↥Y) : MulAut W) (u : W)) = ((π γ' : ↥Y) : MulAut W) (b (u : W))
      rw [← MulAut.mul_apply, ← hγ, MulAut.mul_apply])
  calc f (ρ γ (β u)) = f (β ⟨_, hu1⟩) := by rw [hβe γ u hu1]
    _ = β ⟨_, hu3⟩ := hf _ hu3
    _ = β ⟨_, hu4⟩ := by rw [e]
    _ = ρ γ' (β ⟨_, hu2⟩) := hβe γ' ⟨_, hu2⟩ hu4
    _ = ρ γ' (f (β u)) := by rw [hf u hu2]

theorem cocyc_lift (hs : Function.Surjective π) (hβs : Function.Surjective β)
    (hb : ∀ y ∈ Y, b * y * b⁻¹ ∈ Y) (hb' : ∀ y ∈ Y, b⁻¹ * y * b ∈ Y)
    (hf : ∀ (u : ↥(commV Y)) (hu : b (u : W) ∈ commV Y), f (β u) = β ⟨b u, hu⟩)
    {v : W} {m : M} (hv : ∀ γ, cocyc π β v γ = ρ γ m * m⁻¹) (γ' : Γ) :
    cocyc π β (b v) γ' = ρ γ' (f m) * (f m)⁻¹ := by
  obtain ⟨γ, hγ⟩ := hs ⟨_, hb' _ (π γ').2⟩
  have hγ1 : ((π γ : ↥Y) : MulAut W) = b⁻¹ * ((π γ' : ↥Y) : MulAut W) * b :=
    congrArg Subtype.val hγ
  have hγ' : ((π γ' : ↥Y) : MulAut W) * b = b * ((π γ : ↥Y) : MulAut W) := by
    rw [hγ1]
    group
  have hmem := A6L76Oe.gen_mem_commV (π γ).2 v
  have hmem' := apply_mem_commV_of_conj hb hmem
  have e : (⟨((π γ' : ↥Y) : MulAut W) (b v) * (b v)⁻¹,
      A6L76Oe.gen_mem_commV (π γ').2 (b v)⟩ : ↥(commV Y)) =
      ⟨b (((π γ : ↥Y) : MulAut W) v * v⁻¹), hmem'⟩ := Subtype.ext (by
    show ((π γ' : ↥Y) : MulAut W) (b v) * (b v)⁻¹ = b (((π γ : ↥Y) : MulAut W) v * v⁻¹)
    rw [map_mul, map_inv, ← MulAut.mul_apply, hγ', MulAut.mul_apply])
  calc cocyc π β (b v) γ' = β ⟨_, hmem'⟩ := by unfold cocyc; rw [e]
    _ = f (cocyc π β v γ) := (hf ⟨_, hmem⟩ hmem').symm
    _ = f (ρ γ m * m⁻¹) := by rw [hv γ]
    _ = ρ γ' (f m) * (f m)⁻¹ := by rw [map_mul, map_inv, lift_hom hβe hβs hb hf hγ']

end Lift

theorem eq_of_coboundary_eq {Γ : Type*} [Group Γ] {M : Type*} [CommGroup M]
    {ρ : Γ →* MulAut M} (hfix : ∀ m : M, (∀ γ, ρ γ m = m) → m = 1) {m m' : M}
    (h : ∀ γ : Γ, ρ γ m * m⁻¹ = ρ γ m' * m'⁻¹) : m = m' := by
  have h1 : m * m'⁻¹ = 1 := by
    refine hfix _ fun γ => ?_
    have h2 := h γ
    rw [map_mul, map_inv]
    have e1 : ρ γ m = (ρ γ m' * m'⁻¹) * m := by
      rw [← h2]
      group
    rw [e1, mul_inv_eq_iff_eq_mul]
    ac_rfl
  exact mul_inv_eq_one.1 h1

end A6L76Oh

end CFSG.Quasithin.H13.A6
