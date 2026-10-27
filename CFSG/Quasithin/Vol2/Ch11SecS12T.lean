module

public import CFSG.Quasithin.Vol2.Ch11SecS12P
public import CFSG.Quasithin.Vol2.Ch11SecQ9aL3I

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12

open CFSG.Open hiding StatedSL
open CFSG.Quasithin CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A
open CFSG.Assembly.LowTwoRank (StatedSL)
open Matrix
open scoped MatrixGroups

section Image

variable {G : Type} [Group G] {R : Type} [Group R] {Γ L X : Subgroup G}

theorem mem_normalizer_of_comm (hXL : ∀ y ∈ X, ∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ pCoreOf 2 L)
    {y : G} (hyX : y ∈ X) : y ∈ Subgroup.normalizer (L : Set G) := by
  have key : ∀ z ∈ X, ∀ l ∈ L, z * l * z⁻¹ ∈ L := fun z hz l hl => by
    have h := CFSG.LieType.BorelTits.pCoreOf_le 2 L (hXL z hz l hl)
    have e : z * l * z⁻¹ = (z * l * z⁻¹ * l⁻¹) * l := by group
    rw [e]
    exact L.mul_mem h hl
  refine Subgroup.mem_normalizer_iff.mpr fun l => ⟨key y hyX l, fun h => ?_⟩
  have h2 := key y⁻¹ (X.inv_mem hyX) _ h
  simpa [mul_assoc] using h2

variable (α : ↥Γ →* R)

theorem map_mem_normalizer (K : Subgroup G) {y : ↥Γ}
    (hy : (y : G) ∈ Subgroup.normalizer (K : Set G)) :
    α y ∈ Subgroup.normalizer (((K.subgroupOf Γ).map α : Subgroup R) : Set R) := by
  have hy' : y ∈ Subgroup.normalizer ((K.subgroupOf Γ : Subgroup ↥Γ) : Set ↥Γ) := by
    rw [Subgroup.mem_normalizer_iff]
    intro l
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.mem_normalizer_iff.mp hy (l : G)
  exact Subgroup.le_normalizer_map α ⟨y, hy', rfl⟩

theorem map_pCoreOf_le [Finite G] (hLΓ : L ≤ Γ) :
    ((pCoreOf 2 L).subgroupOf Γ).map α ≤ pCoreOf 2 ((L.subgroupOf Γ).map α) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOΓ : pCoreOf 2 L ≤ Γ := (CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans hLΓ
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ ?_ ?_
  · exact Subgroup.map_mono fun γ hγ => Subgroup.mem_subgroupOf.mpr
      (CFSG.LieType.BorelTits.pCoreOf_le 2 L (Subgroup.mem_subgroupOf.mp hγ))
  · rintro _ ⟨l, hl, rfl⟩
    exact map_mem_normalizer α (pCoreOf 2 L)
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L (Subgroup.mem_subgroupOf.mp hl))
  · exact ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).of_equiv
      (Subgroup.subgroupOfEquivOfLe hOΓ).symm).map α

theorem map_mem_sectionCentralizer [Finite G] (hLΓ : L ≤ Γ) {y : ↥Γ}
    (hyL : (y : G) ∈ Subgroup.normalizer (L : Set G))
    (hy : ∀ l ∈ L, (y : G) * l * (y : G)⁻¹ * l⁻¹ ∈ pCoreOf 2 L) :
    α y ∈ sectionCentralizer ((L.subgroupOf Γ).map α) (pCoreOf 2 ((L.subgroupOf Γ).map α)) := by
  have hN := map_mem_normalizer α L hyL
  refine ⟨hN, CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ hN, ?_⟩
  rintro _ ⟨l, hl, rfl⟩
  have h2 : y * l * y⁻¹ * l⁻¹ ∈ (pCoreOf 2 L).subgroupOf Γ := by
    rw [Subgroup.mem_subgroupOf]
    simpa using hy _ (Subgroup.mem_subgroupOf.mp hl)
  have h3 := map_pCoreOf_le α hLΓ ⟨_, h2, rfl⟩
  simpa only [map_mul, map_inv] using h3

theorem map_pow_three {y : ↥Γ} (hyX : (y : G) ∈ X)
    (h3 : Nat.card ↥((X.subgroupOf Γ).map α) = 3) : α y ^ 3 = 1 := by
  have hm : α y ∈ (X.subgroupOf Γ).map α := ⟨y, Subgroup.mem_subgroupOf.mpr hyX, rfl⟩
  have h := pow_card_eq_one' (G := ↥((X.subgroupOf Γ).map α)) (x := ⟨α y, hm⟩)
  rw [h3] at h
  simpa using congrArg Subtype.val h

end Image

theorem exists_mulEquiv_of_ker_eq {Γ' R' : Type} [Group Γ'] [Group R'] (α₁ α₂ : Γ' →* R')
    (h₁ : Function.Surjective α₁) (h₂ : Function.Surjective α₂) (hk : α₁.ker = α₂.ker) :
    ∃ φ : R' ≃* R', ∀ γ, α₂ γ = φ (α₁ γ) := by
  let e₁ := QuotientGroup.quotientKerEquivOfSurjective α₁ h₁
  let e₂ := QuotientGroup.quotientKerEquivOfSurjective α₂ h₂
  refine ⟨e₁.symm.trans ((QuotientGroup.quotientMulEquivOfEq hk).trans e₂), fun γ => ?_⟩
  have e : e₁.symm (α₁ γ) = (γ : Γ' ⧸ α₁.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [MulEquiv.trans_apply, e, MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

section PGL

variable {F : Type} [Field F] [Finite F]

theorem exists_conj_Ptheta [CharP F 2] (hF : Nat.card F = 4) {A S : Subgroup (PGL3 F)}
    (hS : QuasithinUnique.IsSylowTwoOf S ⊤) (hSA : S ≤ Subgroup.normalizer (A : Set (PGL3 F)))
    (h1 : A ≠ ⊥) (hp : ⁅A, A⁆ = A)
    (hc : A ≠ ⁅(⊤ : Subgroup (PGL3 F)), (⊤ : Subgroup (PGL3 F))⁆) :
    ∃ c : PGL3 F, ∃ j : Fin 2, QuasithinUnique.IsSylowTwoOf (S0P F) ⊤ ∧
      A.map (MulAut.conj c).toMonoidHom = Ptheta F j := by
  obtain ⟨c, hc'⟩ := exists_conj_S0P hF hS
  have h2 : (MulAut.conj c⁻¹).toMonoidHom.comp (MulAut.conj c).toMonoidHom =
      MonoidHom.id (PGL3 F) := by
    ext x
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulAut.conj_apply, MonoidHom.id_apply]
    group
  have he : S.map (MulAut.conj c⁻¹).toMonoidHom = S0P F := by
    rw [hc', Subgroup.map_map, h2, Subgroup.map_id]
  have hS0 : QuasithinUnique.IsSylowTwoOf (S0P F) ⊤ := he ▸ isSylowTwoOf_map (MulAut.conj c⁻¹) hS
  rcases map_eq_Ptheta hF (MulAut.conj c⁻¹) he h1 hp hc hSA with h | h
  · exact ⟨c⁻¹, 0, hS0, h⟩
  · exact ⟨c⁻¹, 1, hS0, h⟩

variable {G : Type} [Group G] [Finite G]

theorem exists_levi (hF : Nat.card F = 4) {Γ L : Subgroup G} (hLΓ : L ≤ Γ)
    (α : ↥Γ →* PGL3 F) {A : Subgroup (PGL3 F)} (hA : (L.subgroupOf Γ).map α = A)
    (hperf : ⁅A, A⁆ = A) (hne : A ≠ ⊥) (α₀ : ↥L →* ↥(StatedSL 2 F))
    (hα₀ : Function.Surjective α₀) (hker : α₀.ker = (pCoreOf 2 L).subgroupOf L) :
    ∃ α₀' : ↥A →* ↥(StatedSL 2 F), Function.Surjective α₀' ∧
      α₀'.ker = (pCoreOf 2 A).subgroupOf A ∧
      ∀ (l : ↥L) (γ : ↥Γ) (p : ↥A), (γ : G) = l → (p : PGL3 F) = α γ → α₀ l = α₀' p := by
  subst hA
  exact exists_levi' hF hLΓ α hperf hne α₀ hα₀ hker

theorem pCoreOf_le_map (hF : Nat.card F = 4) {Γ L : Subgroup G} (hLΓ : L ≤ Γ)
    (α : ↥Γ →* PGL3 F)
    (hperf : ⁅(L.subgroupOf Γ).map α, (L.subgroupOf Γ).map α⁆ = (L.subgroupOf Γ).map α)
    (hne : (L.subgroupOf Γ).map α ≠ ⊥) (α₀ : ↥L →* ↥(StatedSL 2 F))
    (hα₀ : Function.Surjective α₀) (hker : α₀.ker = (pCoreOf 2 L).subgroupOf L) :
    pCoreOf 2 ((L.subgroupOf Γ).map α) ≤ ((pCoreOf 2 L).subgroupOf Γ).map α := by
  obtain ⟨α₀', -, hk', hc'⟩ := exists_levi' hF hLΓ α hperf hne α₀ hα₀ hker
  intro p hp
  have hpA : p ∈ (L.subgroupOf Γ).map α := CFSG.LieType.BorelTits.pCoreOf_le 2 _ hp
  obtain ⟨γ, hγ, hγp⟩ := hpA
  have hγL : (γ : G) ∈ L := Subgroup.mem_subgroupOf.mp hγ
  have h1 := hc' ⟨γ, hγL⟩ γ ⟨p, CFSG.LieType.BorelTits.pCoreOf_le 2 _ hp⟩ rfl hγp.symm
  have h2 : α₀' ⟨p, CFSG.LieType.BorelTits.pCoreOf_le 2 _ hp⟩ = 1 := by
    rw [← MonoidHom.mem_ker, hk', Subgroup.mem_subgroupOf]
    exact hp
  have h3 : (⟨(γ : G), hγL⟩ : ↥L) ∈ α₀.ker := by rw [MonoidHom.mem_ker, h1, h2]
  rw [hker, Subgroup.mem_subgroupOf] at h3
  exact ⟨γ, Subgroup.mem_subgroupOf.mpr h3, hγp⟩

end PGL

section Conj

variable {G : Type} [Group G] {V : Subgroup G} {F : Type} [Field F]

@[expose] def conjM (c : GL (Fin 3) F) (M : Matrix (Fin 3) (Fin 3) F) :
    Matrix (Fin 3) (Fin 3) F :=
  (c : Matrix (Fin 3) (Fin 3) F) * M * ((c⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)

@[expose] def conjβ (c : GL (Fin 3) F) (β : ↥V →* Multiplicative (Matrix (Fin 3) (Fin 3) F)) :
    ↥V →* Multiplicative (Matrix (Fin 3) (Fin 3) F) where
  toFun v := Multiplicative.ofAdd (conjM c (Multiplicative.toAdd (β v)))
  map_one' := by
    show Multiplicative.ofAdd (conjM c (Multiplicative.toAdd (β 1))) = 1
    rw [map_one, toAdd_one, conjM, Matrix.mul_zero, Matrix.zero_mul, ofAdd_zero]
  map_mul' v w := by
    show Multiplicative.ofAdd (conjM c (Multiplicative.toAdd (β (v * w)))) =
      Multiplicative.ofAdd (conjM c (Multiplicative.toAdd (β v))) *
        Multiplicative.ofAdd (conjM c (Multiplicative.toAdd (β w)))
    rw [← ofAdd_add, MonoidHom.map_mul β v w, toAdd_mul, conjM, conjM, conjM, Matrix.mul_add,
      Matrix.add_mul]

theorem toAdd_conjβ (c : GL (Fin 3) F) (β : ↥V →* Multiplicative (Matrix (Fin 3) (Fin 3) F))
    (v : ↥V) : Multiplicative.toAdd (conjβ c β v) = (c : Matrix (Fin 3) (Fin 3) F) *
      Multiplicative.toAdd (β v) * ((c⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := rfl

theorem trace_conj (c : GL (Fin 3) F) (M : Matrix (Fin 3) (Fin 3) F) :
    ((c : Matrix (Fin 3) (Fin 3) F) * M * ((c⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)).trace =
      M.trace := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]

theorem conj_inv_conj (c : GL (Fin 3) F) (M : Matrix (Fin 3) (Fin 3) F) :
    ((c⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * ((c : Matrix (Fin 3) (Fin 3) F) * M *
      ((c⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) * (c : Matrix (Fin 3) (Fin 3) F) = M := by
  simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one, Units.inv_mul_cancel_left]

theorem conj_conj_inv (c : GL (Fin 3) F) (M : Matrix (Fin 3) (Fin 3) F) :
    (c : Matrix (Fin 3) (Fin 3) F) * (((c⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * M *
      (c : Matrix (Fin 3) (Fin 3) F)) * ((c⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = M := by
  simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, Units.mul_inv_cancel_left]

variable (c : GL (Fin 3) F) (β : ↥V →* Multiplicative (Matrix (Fin 3) (Fin 3) F))

theorem trace_conjβ (hβsl : ∀ v, (Multiplicative.toAdd (β v)).trace = 0) (v : ↥V) :
    (Multiplicative.toAdd (conjβ c β v)).trace = 0 := by
  rw [toAdd_conjβ, trace_conj, hβsl]

theorem conjβ_surj
    (hβon : ∀ M : Matrix (Fin 3) (Fin 3) F, M.trace = 0 → ∃ v, Multiplicative.toAdd (β v) = M)
    (M : Matrix (Fin 3) (Fin 3) F) (hM : M.trace = 0) :
    ∃ v, Multiplicative.toAdd (conjβ c β v) = M := by
  have ht : (((c⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * M *
      (c : Matrix (Fin 3) (Fin 3) F)).trace = 0 := by
    have := trace_conj c⁻¹ M
    rw [inv_inv] at this
    rw [this, hM]
  obtain ⟨v, hv⟩ := hβon _ ht
  exact ⟨v, by rw [toAdd_conjβ, hv, conj_conj_inv]⟩

theorem conjβ_eq_one_iff (v : ↥V) : conjβ c β v = 1 ↔ β v = 1 := by
  rw [← toAdd_eq_zero, ← toAdd_eq_zero, toAdd_conjβ]
  constructor
  · intro h
    have h1 := conj_inv_conj c (Multiplicative.toAdd (β v))
    rw [h, Matrix.mul_zero, Matrix.zero_mul] at h1
    exact h1.symm
  · intro h
    rw [h, Matrix.mul_zero, Matrix.zero_mul]

theorem conjβ_rel {Γ : Subgroup G} (α : ↥Γ →* PGL3 F)
    (hact : ∀ (γ : ↥Γ) (u v : ↥V), (v : G) = γ * u * γ⁻¹ → ∀ g : GL (Fin 3) F,
      ProjGenLinGroup.mk g = α γ → Multiplicative.toAdd (β v) =
        (g : Matrix (Fin 3) (Fin 3) F) * Multiplicative.toAdd (β u) *
          ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))
    (γ : ↥Γ) (u v : ↥V) (huv : (v : G) = γ * u * γ⁻¹) (g : GL (Fin 3) F)
    (hg : ProjGenLinGroup.mk g = MulAut.conj (ProjGenLinGroup.mk c) (α γ)) :
    Multiplicative.toAdd (conjβ c β v) = (g : Matrix (Fin 3) (Fin 3) F) *
      Multiplicative.toAdd (conjβ c β u) * ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
  have hg' : ProjGenLinGroup.mk (c⁻¹ * g * c) = α γ := by
    rw [map_mul, map_mul, hg, MulAut.conj_apply, map_inv]
    group
  have h := hact γ u v huv _ hg'
  have e1 : (c : Matrix (Fin 3) (Fin 3) F) * ((c⁻¹ * g * c : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) =
      (g : Matrix (Fin 3) (Fin 3) F) * (c : Matrix (Fin 3) (Fin 3) F) := by
    rw [← Units.val_mul, ← Units.val_mul]
    congr 1
    group
  have e2 : (((c⁻¹ * g * c)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      ((c⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((c⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    rw [← Units.val_mul, ← Units.val_mul]
    congr 1
    group
  rw [toAdd_conjβ, toAdd_conjβ, h]
  calc (c : Matrix (Fin 3) (Fin 3) F) * (((c⁻¹ * g * c : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) * Multiplicative.toAdd (β u) *
        (((c⁻¹ * g * c)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) *
        ((c⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
      = ((c : Matrix (Fin 3) (Fin 3) F) * ((c⁻¹ * g * c : GL (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F)) * Multiplicative.toAdd (β u) *
          ((((c⁻¹ * g * c)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
            ((c⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) := by
        simp only [Matrix.mul_assoc]
    _ = ((g : Matrix (Fin 3) (Fin 3) F) * (c : Matrix (Fin 3) (Fin 3) F)) *
          Multiplicative.toAdd (β u) * (((c⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
            ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) := by rw [e1, e2]
    _ = (g : Matrix (Fin 3) (Fin 3) F) * ((c : Matrix (Fin 3) (Fin 3) F) *
          Multiplicative.toAdd (β u) * ((c⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) *
          ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by simp only [Matrix.mul_assoc]

end Conj

end CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12
