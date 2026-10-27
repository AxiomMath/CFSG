module

public import CFSG.Quasithin.H13.A6S1372L76Of1
public import CFSG.Quasithin.H13.A6S1372L76Oe1

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge CFSG.Assembly.LowTwoRank
open scoped Pointwise IsMulCommutative Matrix

namespace A6L76Of

section Cocycle

variable {W : Type*} [CommGroup W] {Γ : Type*} [Group Γ] {M : Type*} [CommGroup M]
  {Y : Subgroup (MulAut W)} (π : Γ →* ↥Y) (β : ↥(commV Y) →* M)

@[expose] noncomputable def cocyc (v : W) (γ : Γ) : M :=
  β ⟨((π γ : ↥Y) : MulAut W) v * v⁻¹, A6L76Oe.gen_mem_commV (π γ).2 v⟩

theorem cocyc_mul_left (v v' : W) (γ : Γ) :
    cocyc π β (v * v') γ = cocyc π β v γ * cocyc π β v' γ := by
  unfold cocyc
  rw [← map_mul]
  congr 1
  apply Subtype.ext
  simp only [Subgroup.coe_mul, map_mul, mul_inv_rev]
  ac_rfl

theorem cocyc_eq_one_of_fix {v : W} {γ : Γ} (h : ((π γ : ↥Y) : MulAut W) v = v) :
    cocyc π β v γ = 1 := by
  unfold cocyc
  have e : (⟨((π γ : ↥Y) : MulAut W) v * v⁻¹, A6L76Oe.gen_mem_commV (π γ).2 v⟩ :
      ↥(commV Y)) = 1 := Subtype.ext (by simp [h])
  rw [e, map_one]

variable {π β}

theorem mem_fixV_of_cocyc_eq_one (hY : Group.IsPerfect ↥Y) (hπ : Function.Surjective π)
    (hβk : ∀ u : ↥(commV Y), β u = 1 → (u : W) ∈ fixV Y) {v : W}
    (hv : ∀ γ, cocyc π β v γ = 1) : v ∈ fixV Y := by
  have hmem : ∀ y : ↥Y, (y : MulAut W) v * v⁻¹ ∈ fixV Y := by
    intro y
    obtain ⟨γ, rfl⟩ := hπ y
    exact hβk _ (hv γ)
  let f : ↥Y →* ↥(fixV Y) :=
    { toFun := fun y => ⟨(y : MulAut W) v * v⁻¹, hmem y⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => by
        apply Subtype.ext
        have hb := hmem b
        set w := (b : MulAut W) v * v⁻¹ with hw
        have hbw : (b : MulAut W) v = w * v := by rw [hw]; group
        have haw : (a : MulAut W) w = w := hb a a.2
        show ((a * b : ↥Y) : MulAut W) v * v⁻¹ = ((a : MulAut W) v * v⁻¹) * w
        rw [Subgroup.coe_mul, MulAut.mul_apply, hbw, map_mul, haw]
        ac_rfl }
  intro y hy
  have h1 : f ⟨y, hy⟩ = 1 := by
    have htop : commutator ↥Y = ⊤ := Group.isPerfect_def.1 hY
    have hle : commutator ↥Y ≤ f.ker := Abelianization.commutator_subset_ker f
    rw [htop] at hle
    exact hle (Subgroup.mem_top _)
  have h2 : y v * v⁻¹ = 1 := congrArg Subtype.val h1
  exact mul_inv_eq_one.1 h2

variable {ρ : Γ →* MulAut M} (hβe : ∀ (γ : Γ) (u : ↥(commV Y))
  (hu : ((π γ : ↥Y) : MulAut W) (u : W) ∈ commV Y), β ⟨_, hu⟩ = ρ γ (β u))
include hβe

theorem cocyc_mul (v : W) (γ γ' : Γ) :
    cocyc π β v (γ * γ') = cocyc π β v γ * ρ γ (cocyc π β v γ') := by
  unfold cocyc
  have hu1 : ((π γ : ↥Y) : MulAut W) (((π γ' : ↥Y) : MulAut W) v * v⁻¹) ∈ commV Y :=
    A6L76Oe.apply_mem_commV (π γ).2 (A6L76Oe.gen_mem_commV (π γ').2 v)
  have e : (⟨((π (γ * γ') : ↥Y) : MulAut W) v * v⁻¹,
      A6L76Oe.gen_mem_commV (π (γ * γ')).2 v⟩ : ↥(commV Y)) =
      ⟨_, hu1⟩ * ⟨((π γ : ↥Y) : MulAut W) v * v⁻¹, A6L76Oe.gen_mem_commV (π γ).2 v⟩ := by
    apply Subtype.ext
    simp only [map_mul, Subgroup.coe_mul, MulAut.mul_apply, map_inv]
    group
  rw [e, map_mul, hβe γ ⟨_, A6L76Oe.gen_mem_commV (π γ').2 v⟩ hu1, mul_comm]

theorem cocyc_conj (v : W) (δ γ : Γ) :
    cocyc π β (((π δ : ↥Y) : MulAut W) v) γ = ρ δ (cocyc π β v (δ⁻¹ * γ * δ)) := by
  unfold cocyc
  have hu1 : ((π δ : ↥Y) : MulAut W) (((π (δ⁻¹ * γ * δ) : ↥Y) : MulAut W) v * v⁻¹) ∈
      commV Y :=
    A6L76Oe.apply_mem_commV (π δ).2 (A6L76Oe.gen_mem_commV (π (δ⁻¹ * γ * δ)).2 v)
  have e : (⟨((π γ : ↥Y) : MulAut W) (((π δ : ↥Y) : MulAut W) v) *
      (((π δ : ↥Y) : MulAut W) v)⁻¹, A6L76Oe.gen_mem_commV (π γ).2 _⟩ :
        ↥(commV Y)) = ⟨_, hu1⟩ := by
    apply Subtype.ext
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, MulAut.mul_apply,
      MulAut.inv_apply, MulEquiv.apply_symm_apply]
  rw [e, hβe δ ⟨_, A6L76Oe.gen_mem_commV (π (δ⁻¹ * γ * δ)).2 v⟩ hu1]

end Cocycle

section Nat

variable {F : Type} [Field F]

@[expose] def glMulAut (g : GL (Fin 3) F) : MulAut (Multiplicative (Fin 3 → F)) where
  toFun v := Multiplicative.ofAdd ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ v.toAdd)
  invFun v := Multiplicative.ofAdd
    (((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v.toAdd)
  left_inv v := by
    simp only [toAdd_ofAdd, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec, ofAdd_toAdd]
  right_inv v := by
    simp only [toAdd_ofAdd, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec, ofAdd_toAdd]
  map_mul' v w := by
    simp only [toAdd_mul, Matrix.mulVec_add, ofAdd_add]

@[expose] def glHom : GL (Fin 3) F →* MulAut (Multiplicative (Fin 3 → F)) where
  toFun := glMulAut
  map_one' := by
    ext v
    simp [glMulAut]
  map_mul' g h := by
    ext v
    simp [glMulAut, Matrix.mulVec_mulVec]

@[expose] def natHom : ↥(StatedSL 3 F) →* MulAut (Multiplicative (Fin 3 → F)) :=
  glHom.comp (StatedSL 3 F).subtype

theorem natHom_apply (γ : ↥(StatedSL 3 F)) (m : Multiplicative (Fin 3 → F)) :
    Multiplicative.toAdd (natHom γ m) =
      ((γ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ Multiplicative.toAdd m := rfl

theorem natHom_smul (γ : ↥(StatedSL 3 F)) (μ : F) (x : Fin 3 → F) :
    Multiplicative.toAdd (natHom γ (Multiplicative.ofAdd (μ • x))) =
      μ • Multiplicative.toAdd (natHom γ (Multiplicative.ofAdd x)) := by
  rw [natHom_apply, natHom_apply, toAdd_ofAdd, toAdd_ofAdd, Matrix.mulVec_smul]

theorem exists_transvection {i j : Fin 3} (hij : i ≠ j) (c : F) :
    ∃ γ : ↥(StatedSL 3 F), ((γ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      Matrix.transvection i j c :=
  ⟨⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.transvection i j c)
      (by rw [Matrix.det_transvection_of_ne _ _ hij]; exact one_ne_zero),
      Subgroup.subset_closure (Matrix.det_transvection_of_ne i j hij c :)⟩, rfl⟩

theorem natHom_fixed {m : Multiplicative (Fin 3 → F)} (h : ∀ γ, natHom γ m = m) : m = 1 := by
  have key : ∀ i j : Fin 3, i ≠ j → Multiplicative.toAdd m j = 0 := by
    intro i j hij
    obtain ⟨γ, hγ⟩ := exists_transvection hij (1 : F)
    have h1 := congrArg Multiplicative.toAdd (h γ)
    rw [natHom_apply, hγ, Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec,
      Matrix.single_mulVec] at h1
    have h2 := congrFun h1 i
    simpa using h2
  apply Multiplicative.toAdd.injective
  funext j
  obtain ⟨i, hij⟩ : ∃ i : Fin 3, i ≠ j := ⟨j + 1, by fin_cases j <;> decide⟩
  exact key i j hij

theorem eq_of_natCoboundary_eq {m m' : Multiplicative (Fin 3 → F)}
    (h : ∀ γ : ↥(StatedSL 3 F), natHom γ m * m⁻¹ = natHom γ m' * m'⁻¹) : m = m' := by
  have h1 : m * m'⁻¹ = 1 := by
    refine natHom_fixed fun γ => ?_
    have h2 := h γ
    rw [map_mul, map_inv]
    have e1 : natHom γ m = (natHom γ m' * m'⁻¹) * m := by
      rw [← h2]
      group
    rw [e1]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  exact mul_inv_eq_one.1 h1

theorem natHom_conj (s γ : ↥(StatedSL 3 F)) (x : Multiplicative (Fin 3 → F)) :
    natHom s (natHom (s⁻¹ * γ * s) x) = natHom γ (natHom s x) := by
  rw [← MulAut.mul_apply, ← map_mul, ← MulAut.mul_apply, ← map_mul]
  congr 2
  group

end Nat

section Lift

variable {W : Type*} [CommGroup W] {Y : Subgroup (MulAut W)}

theorem apply_mem_commV_of_conj {b : MulAut W} (hb : ∀ y ∈ Y, b * y * b⁻¹ ∈ Y) {u : W}
    (hu : u ∈ commV Y) : b u ∈ commV Y :=
  CFSG.Quasithin.commV_apply_mem_of_normalizes hb hu

theorem apply_mem_fixV_of_conj {b : MulAut W} (hb' : ∀ y ∈ Y, b⁻¹ * y * b ∈ Y) {c : W}
    (hc : c ∈ fixV Y) : b c ∈ fixV Y := by
  intro y hy
  calc y (b c) = b ((b⁻¹ * y * b) c) := by
        rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self]
    _ = b c := by rw [hc _ (hb' y hy)]

theorem inv_conj_mem [Finite ↥Y] {b : MulAut W} (hb : ∀ y ∈ Y, b * y * b⁻¹ ∈ Y) :
    ∀ y ∈ Y, b⁻¹ * y * b ∈ Y := by
  intro y hy
  let f : ↥Y → ↥Y := fun z => ⟨b * z * b⁻¹, hb z z.2⟩
  have hf : Function.Injective f := fun z z' h => by
    have h1 : b * (z : MulAut W) * b⁻¹ = b * z' * b⁻¹ := congrArg Subtype.val h
    exact Subtype.ext (by simpa using h1)
  obtain ⟨z, hz⟩ := (Finite.injective_iff_surjective.1 hf) ⟨y, hy⟩
  have h1 : b * (z : MulAut W) * b⁻¹ = y := congrArg Subtype.val hz
  rw [← h1, show b⁻¹ * (b * (z : MulAut W) * b⁻¹) * b = z by group]
  exact z.2

variable {F : Type} [Field F] {π : ↥(StatedSL 3 F) →* ↥Y}
  {β : ↥(commV Y) →* Multiplicative (Fin 3 → F)}

theorem exists_lift (hβs : Function.Surjective β)
    (hβk : ∀ u, β u = 1 ↔ (u : W) ∈ fixV Y ⊓ commV Y) {b : MulAut W}
    (hb : ∀ y ∈ Y, b * y * b⁻¹ ∈ Y) (hb' : ∀ y ∈ Y, b⁻¹ * y * b ∈ Y) :
    ∃ f : Multiplicative (Fin 3 → F) →* Multiplicative (Fin 3 → F),
      ∀ (u : ↥(commV Y)) (hu : b (u : W) ∈ commV Y), f (β u) = β ⟨b u, hu⟩ := by
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

variable {b : MulAut W} {f : Multiplicative (Fin 3 → F) →* Multiplicative (Fin 3 → F)}

theorem lift_eq_one (hβs : Function.Surjective β)
    (hβk : ∀ u, β u = 1 ↔ (u : W) ∈ fixV Y ⊓ commV Y) (hb : ∀ y ∈ Y, b * y * b⁻¹ ∈ Y)
    (hf : ∀ (u : ↥(commV Y)) (hu : b (u : W) ∈ commV Y), f (β u) = β ⟨b u, hu⟩)
    {m : Multiplicative (Fin 3 → F)} (h : f m = 1) : m = 1 := by
  obtain ⟨u, rfl⟩ := hβs m
  rw [hf u (apply_mem_commV_of_conj hb u.2), hβk] at h
  rw [hβk]
  refine ⟨fun y hy => ?_, u.2⟩
  have h1 := h.1 _ (hb y hy)
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self] at h1
  exact b.injective h1

variable (hβe : ∀ (γ : ↥(StatedSL 3 F)) (u : ↥(commV Y))
  (hu : ((π γ : ↥Y) : MulAut W) (u : W) ∈ commV Y), β ⟨_, hu⟩ = natHom γ (β u))
include hβe

theorem lift_natHom (hβs : Function.Surjective β) (hb : ∀ y ∈ Y, b * y * b⁻¹ ∈ Y)
    (hf : ∀ (u : ↥(commV Y)) (hu : b (u : W) ∈ commV Y), f (β u) = β ⟨b u, hu⟩)
    {γ γ' : ↥(StatedSL 3 F)}
    (hγ : ((π γ' : ↥Y) : MulAut W) * b = b * ((π γ : ↥Y) : MulAut W))
    (m : Multiplicative (Fin 3 → F)) : f (natHom γ m) = natHom γ' (f m) := by
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
  calc f (natHom γ (β u)) = f (β ⟨_, hu1⟩) := by rw [hβe γ u hu1]
    _ = β ⟨_, hu3⟩ := hf _ hu3
    _ = β ⟨_, hu4⟩ := by rw [e]
    _ = natHom γ' (β ⟨_, hu2⟩) := hβe γ' ⟨_, hu2⟩ hu4
    _ = natHom γ' (f (β u)) := by rw [hf u hu2]

theorem cocyc_lift (hs : Function.Surjective π) (hβs : Function.Surjective β)
    (hb : ∀ y ∈ Y, b * y * b⁻¹ ∈ Y) (hb' : ∀ y ∈ Y, b⁻¹ * y * b ∈ Y)
    (hf : ∀ (u : ↥(commV Y)) (hu : b (u : W) ∈ commV Y), f (β u) = β ⟨b u, hu⟩)
    {v : W} {m : Multiplicative (Fin 3 → F)} (hv : ∀ γ, cocyc π β v γ = natHom γ m * m⁻¹)
    (γ' : ↥(StatedSL 3 F)) : cocyc π β (b v) γ' = natHom γ' (f m) * (f m)⁻¹ := by
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
    _ = f (natHom γ m * m⁻¹) := by rw [hv γ]
    _ = natHom γ' (f m) * (f m)⁻¹ := by rw [map_mul, map_inv, lift_natHom hβe hβs hb hf hγ']

theorem lift_semilinear [Finite F] (hs : Function.Surjective π) (hβs : Function.Surjective β)
    (hβk : ∀ u, β u = 1 ↔ (u : W) ∈ fixV Y ⊓ commV Y)
    (hb : ∀ y ∈ Y, b * y * b⁻¹ ∈ Y) (hb' : ∀ y ∈ Y, b⁻¹ * y * b ∈ Y)
    (hf : ∀ (u : ↥(commV Y)) (hu : b (u : W) ∈ commV Y), f (β u) = β ⟨b u, hu⟩) :
    ∃ σ : F →+* F, ∀ (μ : F) (x : Fin 3 → F),
      Multiplicative.toAdd (f (Multiplicative.ofAdd (μ • x))) =
        σ μ • Multiplicative.toAdd (f (Multiplicative.ofAdd x)) := by
  classical
  let fA : (Fin 3 → F) →+ (Fin 3 → F) := AddMonoidHom.toMultiplicative.symm f
  have hfA : ∀ x, fA x = Multiplicative.toAdd (f (Multiplicative.ofAdd x)) := fun x => rfl
  have hinj : Function.Injective fA := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    rw [hfA, toAdd_eq_zero] at hx
    exact ofAdd_eq_one.1 (lift_eq_one hβs hβk hb hf hx)
  have hint : ∀ γ' : ↥(StatedSL 3 F), ∃ γ : ↥(StatedSL 3 F), ∀ x,
      fA (((γ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x) =
        ((γ' : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ fA x := by
    intro γ'
    obtain ⟨γ, hγ⟩ := hs ⟨_, hb' _ (π γ').2⟩
    have hγ' : ((π γ' : ↥Y) : MulAut W) * b = b * ((π γ : ↥Y) : MulAut W) := by
      rw [congrArg Subtype.val hγ]
      group
    exact ⟨γ, fun x => congrArg Multiplicative.toAdd
      (lift_natHom hβe hβs hb hf hγ' (Multiplicative.ofAdd x))⟩
  let e : (Fin 3 → F) ≃+ (Fin 3 → F) :=
    AddEquiv.ofBijective fA ⟨hinj, Finite.injective_iff_surjective.1 hinj⟩
  have he : ∀ x, e x = fA x := fun x => rfl
  have hsc : ∀ μ : F, ∃ c : F, ∀ x, fA (μ • x) = c • fA x := by
    intro μ
    let h : (Fin 3 → F) →+ (Fin 3 → F) :=
      { toFun := fun w => fA (μ • e.symm w)
        map_zero' := by rw [map_zero, smul_zero, map_zero]
        map_add' := fun w w' => by rw [map_add, smul_add, map_add] }
    have hh : ∀ w, h w = fA (μ • e.symm w) := fun w => rfl
    have htr : ∀ i j : Fin 3, i ≠ j → ∀ (c : F) (w : Fin 3 → F),
        h (Matrix.transvection i j c *ᵥ w) = Matrix.transvection i j c *ᵥ h w := by
      intro i j hij c w
      obtain ⟨γ', hγ'⟩ := exists_transvection hij c
      obtain ⟨γ, hγ⟩ := hint γ'
      have h1 : e.symm (Matrix.transvection i j c *ᵥ w) =
          ((γ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ e.symm w := by
        rw [AddEquiv.symm_apply_eq, he, hγ, hγ', ← he, AddEquiv.apply_symm_apply]
      rw [hh, hh, h1, ← Matrix.mulVec_smul, hγ, hγ']
    obtain ⟨c, hc⟩ := eq_smul_of_commute_transvection h htr
    refine ⟨c, fun x => ?_⟩
    have h2 := hc (fA x)
    rw [hh] at h2
    have h3 : e.symm (fA x) = x := by rw [← he, AddEquiv.symm_apply_apply]
    rwa [h3] at h2
  have hx₀ : fA (Pi.single 0 1) ≠ 0 := fun h => by
    have h1 := congrFun (hinj (h.trans (map_zero fA).symm)) 0
    simp at h1
  exact exists_ringHom_of_smul fA hx₀ hsc

end Lift

end A6L76Of

end CFSG.Quasithin.H13.A6
