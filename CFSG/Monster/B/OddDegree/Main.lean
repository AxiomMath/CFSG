module

public import CFSG.Monster.B.OddDegree.Section
public import CFSG.Monster.B.OddDegree.Lattice
public import CFSG.Monster.B.OddDegree.Form
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Polynomial.Basic

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.OddDegree

open Module Matrix

section Section

variable {G W : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : G →* Module.End (ZMod 2) W) {U' U : Submodule (ZMod 2) W} (hU' : Invariant ρ U')
  (hU : Invariant ρ U)

@[expose] noncomputable def secEnd (g : G) :
    Module.End (ZMod 2) (U ⧸ U'.comap U.subtype) :=
  (U'.comap U.subtype).mapQ (U'.comap U.subtype) ((ρ g).restrict (hU g))
    (fun x hx => hU' g x hx)

theorem secEnd_mk (g : G) (u : U) :
    secEnd ρ hU' hU g (Submodule.Quotient.mk u) =
      Submodule.Quotient.mk ⟨ρ g u, hU g u u.2⟩ := rfl

@[expose] noncomputable def secRep : G →* Module.End (ZMod 2) (U ⧸ U'.comap U.subtype) where
  toFun := secEnd ρ hU' hU
  map_one' := by
    refine LinearMap.ext fun x => ?_
    induction x using Submodule.Quotient.induction_on with
    | H u =>
      rw [secEnd_mk, Module.End.one_apply]
      congr 1
      apply Subtype.ext
      show (ρ 1) (u : W) = u
      rw [map_one, Module.End.one_apply]
  map_mul' g h := by
    refine LinearMap.ext fun x => ?_
    induction x using Submodule.Quotient.induction_on with
    | H u =>
      rw [Module.End.mul_apply, secEnd_mk, secEnd_mk, secEnd_mk]
      congr 1
      apply Subtype.ext
      show (ρ (g * h)) (u : W) = (ρ g) ((ρ h) u)
      rw [map_mul, Module.End.mul_apply]

theorem secRep_apply_mk (g : G) (u : U) :
    secRep ρ hU' hU g (Submodule.Quotient.mk u) = Submodule.Quotient.mk ⟨ρ g u, hU g u u.2⟩ :=
  rfl

theorem secRep_eq_one_iff (g : G) : secRep ρ hU' hU g = 1 ↔ g ∈ secKer ρ U' U hU' hU := by
  rw [mem_secKer]
  constructor
  · intro h u hu
    have h1 := LinearMap.congr_fun h (Submodule.Quotient.mk ⟨u, hu⟩)
    rw [secRep_apply_mk, Module.End.one_apply, Submodule.Quotient.eq] at h1
    exact h1
  · intro h
    refine LinearMap.ext fun x => ?_
    induction x using Submodule.Quotient.induction_on with
    | H u =>
      rw [secRep_apply_mk, Module.End.one_apply, Submodule.Quotient.eq]
      exact h u u.2

theorem secRep_injective [IsSimpleGroup G] (hnt : ¬ TrivialOn ρ U' U) :
    Function.Injective (secRep ρ hU' hU) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  have hker : (secRep ρ hU' hU).ker = secKer ρ U' U hU' hU := by
    ext g
    rw [MonoidHom.mem_ker, secRep_eq_one_iff]
  rw [hker]
  have := secKer_normal ρ U' U hU' hU
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (secKer ρ U' U hU' hU) with h | h
  · exact h
  · exact absurd ((trivialOn_iff_secKer_eq_top hU' hU).2 h) hnt

theorem finrank_sec [FiniteDimensional (ZMod 2) W] (hle : U' ≤ U) :
    finrank (ZMod 2) (U ⧸ U'.comap U.subtype) = finrank (ZMod 2) U - finrank (ZMod 2) U' := by
  have h := Submodule.finrank_quotient_add_finrank (U'.comap U.subtype)
  have h2 : finrank (ZMod 2) (U'.comap U.subtype) = finrank (ZMod 2) U' :=
    LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hle)
  omega

theorem secRep_irreducible (hle : U' ≤ U)
    (hirr : ∀ X, Invariant ρ X → U' ≤ X → X ≤ U → X = U' ∨ X = U)
    (Y : Submodule (ZMod 2) (U ⧸ U'.comap U.subtype))
    (hY : ∀ g, ∀ y ∈ Y, secRep ρ hU' hU g y ∈ Y) : Y = ⊥ ∨ Y = ⊤ := by
  set X : Submodule (ZMod 2) W := (Y.comap (U'.comap U.subtype).mkQ).map U.subtype with hX
  have hmemX : ∀ w, w ∈ X ↔ ∃ hw : w ∈ U, Submodule.Quotient.mk ⟨w, hw⟩ ∈ Y := by
    intro w
    rw [hX, Submodule.mem_map]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u.2, hu⟩
    · rintro ⟨hw, hy⟩
      exact ⟨⟨w, hw⟩, hy, rfl⟩
  have hXinv : Invariant ρ X := by
    intro g w hw
    obtain ⟨hwU, hy⟩ := (hmemX w).1 hw
    exact (hmemX _).2 ⟨hU g w hwU, by
      have := hY g _ hy
      rwa [secRep_apply_mk] at this⟩
  have hU'X : U' ≤ X := by
    intro w hw
    refine (hmemX w).2 ⟨hle hw, ?_⟩
    have h0 : (Submodule.Quotient.mk (⟨w, hle hw⟩ : U) : U ⧸ U'.comap U.subtype) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 hw
    rw [h0]
    exact Y.zero_mem
  have hXU : X ≤ U := fun w hw => ((hmemX w).1 hw).1
  rcases hirr X hXinv hU'X hXU with h | h
  · left
    rw [eq_bot_iff]
    intro y hy
    induction y using Submodule.Quotient.induction_on with
    | H u =>
      rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
      have : (u : W) ∈ X := (hmemX u).2 ⟨u.2, hy⟩
      rw [h] at this
      exact this
  · right
    rw [eq_top_iff]
    intro y _
    induction y using Submodule.Quotient.induction_on with
    | H u =>
      have : (u : W) ∈ X := by rw [h]; exact u.2
      obtain ⟨_, hy⟩ := (hmemX u).1 this
      exact hy

end Section

section Matrices

variable {G Q : Type*} [Group G] [AddCommGroup Q] [Module (ZMod 2) Q] {d : ℕ}
  (b : Module.Basis (Fin d) (ZMod 2) Q) (σ : G →* Module.End (ZMod 2) Q)

@[expose] noncomputable def matRep : G →* GL (Fin d) (ZMod 2) :=
  ((LinearMap.toMatrixAlgEquiv b).toRingEquiv.toMonoidHom.comp σ).toHomUnits

theorem coe_matRep (g : G) :
    ((matRep b σ g : GL (Fin d) (ZMod 2)) : Matrix (Fin d) (Fin d) (ZMod 2)) =
      LinearMap.toMatrixAlgEquiv b (σ g) := rfl

theorem matRep_injective (hσ : Function.Injective σ) : Function.Injective (matRep b σ) := by
  intro g h hgh
  apply hσ
  have h1 : LinearMap.toMatrixAlgEquiv b (σ g) = LinearMap.toMatrixAlgEquiv b (σ h) := by
    rw [← coe_matRep, ← coe_matRep, hgh]
  exact (LinearMap.toMatrixAlgEquiv b).injective h1

theorem matRep_mulVec (g : G) (q : Q) :
    ((matRep b σ g : GL (Fin d) (ZMod 2)) : Matrix (Fin d) (Fin d) (ZMod 2)) *ᵥ b.equivFun q =
      b.equivFun (σ g q) := by
  rw [coe_matRep]
  change LinearMap.toMatrix b b (σ g) *ᵥ b.equivFun q = _
  rw [Module.Basis.equivFun_apply, Module.Basis.equivFun_apply, LinearMap.toMatrix_mulVec_repr]

theorem matRep_irreducible
    (hirr : ∀ Y : Submodule (ZMod 2) Q, (∀ g, ∀ y ∈ Y, σ g y ∈ Y) → Y = ⊥ ∨ Y = ⊤)
    (Y : Submodule (ZMod 2) (Fin d → ZMod 2))
    (hY : ∀ g, ∀ y ∈ Y, ((matRep b σ g : GL (Fin d) (ZMod 2)) :
      Matrix (Fin d) (Fin d) (ZMod 2)) *ᵥ y ∈ Y) : Y = ⊥ ∨ Y = ⊤ := by
  set Y' := Y.comap b.equivFun.toLinearMap
  have hY' : ∀ g, ∀ y ∈ Y', σ g y ∈ Y' := by
    intro g y hy
    change b.equivFun (σ g y) ∈ Y
    rw [← matRep_mulVec]
    exact hY g _ hy
  have hmap : Y = Y'.map b.equivFun.toLinearMap := by
    rw [Submodule.map_comap_eq_of_surjective b.equivFun.surjective]
  rcases hirr Y' hY' with h | h
  · left
    rw [hmap, h, Submodule.map_bot]
  · right
    rw [hmap, h, Submodule.map_top, LinearMap.range_eq_top.2 b.equivFun.surjective]

end Matrices

section Padding

variable {G : Type*} [Group G] {d m N : ℕ} (hN : d + m = N)

@[expose] noncomputable def padHom :
    Matrix (Fin d) (Fin d) (ZMod 2) →* Matrix (Fin N) (Fin N) (ZMod 2) :=
  (Matrix.reindexAlgEquiv (ZMod 2) (ZMod 2) (finSumFinEquiv.trans (finCongr hN))).toRingEquiv
    |>.toMonoidHom.comp
    { toFun := fun A => Matrix.fromBlocks A 0 0 (1 : Matrix (Fin m) (Fin m) (ZMod 2))
      map_one' := Matrix.fromBlocks_one
      map_mul' := fun A B => by rw [Matrix.fromBlocks_multiply]; simp }

theorem padHom_injective : Function.Injective (padHom hN) := by
  intro A B h
  have h1 : Matrix.fromBlocks A 0 0 (1 : Matrix (Fin m) (Fin m) (ZMod 2)) =
      Matrix.fromBlocks B 0 0 1 :=
    (Matrix.reindexAlgEquiv (ZMod 2) (ZMod 2) (finSumFinEquiv.trans (finCongr hN))).injective h
  have := congrArg Matrix.toBlocks₁₁ h1
  simpa using this

@[expose] noncomputable def padRep (τ : G →* GL (Fin d) (ZMod 2)) : G →* GL (Fin N) (ZMod 2) :=
  ((padHom hN).comp ((Units.coeHom _).comp τ)).toHomUnits

theorem padRep_injective (τ : G →* GL (Fin d) (ZMod 2)) (hτ : Function.Injective τ) :
    Function.Injective (padRep hN τ) := by
  intro g h hgh
  apply hτ
  apply Units.ext
  apply padHom_injective hN
  have := congrArg (fun x : GL (Fin N) (ZMod 2) => (x : Matrix (Fin N) (Fin N) (ZMod 2))) hgh
  exact this

end Padding

section Generic

variable {G W : Type*} [Group G] [IsSimpleGroup G] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

theorem exists_faithful_irreducible_rep (hnonab : ∃ a b : G, a * b ≠ b * a)
    (ρ : G →* Module.End (ZMod 2) W) (hρ : ¬ TrivialOn ρ ⊥ ⊤)
    (hred : ∃ X, Invariant ρ X ∧ X ≠ ⊥ ∧ X ≠ ⊤) :
    ∃ d, 1 ≤ d ∧ d < finrank (ZMod 2) W ∧ ∃ τ : G →* GL (Fin d) (ZMod 2),
      Function.Injective τ ∧ ∀ Y : Submodule (ZMod 2) (Fin d → ZMod 2),
        (∀ g, ∀ y ∈ Y, ((τ g : GL (Fin d) (ZMod 2)) : Matrix (Fin d) (Fin d) (ZMod 2)) *ᵥ y ∈ Y) →
          Y = ⊥ ∨ Y = ⊤ := by
  obtain ⟨U', U, ⟨hU', hU, hle, hnt⟩, hirr, -, hlt⟩ := exists_irreducible_section hnonab ρ hρ
  have hdim := hlt hred
  have hd' := finrank_sec hle
  set d := finrank (ZMod 2) (U ⧸ U'.comap U.subtype) with hd
  have hd1 : 1 ≤ d := by
    by_contra h0
    apply hnt
    have hUU' : U' = U := Submodule.eq_of_le_of_finrank_le hle (by omega)
    intro g u hu
    rw [hUU']
    exact U.sub_mem (hU g u hu) hu
  let bQ : Module.Basis (Fin d) (ZMod 2) (U ⧸ U'.comap U.subtype) :=
    Module.finBasisOfFinrankEq _ _ rfl
  exact ⟨d, hd1, by omega, matRep bQ (secRep ρ hU' hU),
    matRep_injective bQ _ (secRep_injective ρ hU' hU hnt),
    matRep_irreducible bQ (secRep ρ hU' hU) (secRep_irreducible ρ hU' hU hle hirr)⟩

end Generic

@[expose] noncomputable def endRep {G : Type*} [Group G] {n : ℕ} (σ : G →* GL (Fin n) (ZMod 2)) :
    G →* Module.End (ZMod 2) (Fin n → ZMod 2) :=
  (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) (ZMod 2) ≃ₐ[ZMod 2] _).toRingEquiv.toMonoidHom.comp
    ((Units.coeHom _).comp σ)

theorem endRep_apply {G : Type*} [Group G] {n : ℕ} (σ : G →* GL (Fin n) (ZMod 2)) (g : G)
    (v : Fin n → ZMod 2) :
    endRep σ g v = ((σ g : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v := rfl

theorem simple_odd_rational_degree_binary_bound {G : Type*} [Group G] [Finite G]
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) {n : ℕ} (hn3 : 3 ≤ n) (hodd : Odd n)
    (ρ : G →* GL (Fin n) ℚ) (hρ : ρ ≠ 1) :
    (∃ d, 1 ≤ d ∧ d ≤ n - 1 ∧ ∃ σ : G →* GL (Fin d) (ZMod 2), Function.Injective σ ∧
      ∀ Y : Submodule (ZMod 2) (Fin d → ZMod 2),
        (∀ g, ∀ y ∈ Y, ((σ g : GL (Fin d) (ZMod 2)) : Matrix (Fin d) (Fin d) (ZMod 2)) *ᵥ y ∈ Y) →
          Y = ⊥ ∨ Y = ⊤) ∧
    ∃ τ : G →* GL (Fin (n - 1)) (ZMod 2), Function.Injective τ := by
  classical
  have := Fintype.ofFinite G
  have hρinj : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ρ.ker with h | h
    · exact h
    · exfalso
      apply hρ
      ext g : 1
      exact (MonoidHom.mem_ker).1 (h ▸ Subgroup.mem_top g)
  set σ := modRep ρ
  have hσ : Function.Injective σ := modRep_injective ρ hnonab hρinj
  obtain ⟨M', hM'sym, hM'inv, hM'0⟩ := exists_primitive_invariant_form (intRep ρ) (by omega)
  set B := M'.map (Int.castRingHom (ZMod 2))
  have hBsym : Bᵀ = B := by
    show (M'.map (Int.castRingHom (ZMod 2)))ᵀ = M'.map (Int.castRingHom (ZMod 2))
    rw [← Matrix.transpose_map, hM'sym]
  have hBinv : ∀ g, ((σ g : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ * B * (σ g) = B := by
    intro g
    have h := congrArg (fun X => X.map (Int.castRingHom (ZMod 2))) (hM'inv g)
    simp only [Matrix.map_mul, Matrix.transpose_map] at h
    exact h
  obtain ⟨X, hXinv, hX0, hX1⟩ := exists_invariant_of_form σ hodd (by omega) B hBsym hM'0 hBinv
  have hntriv : ¬ TrivialOn (endRep σ) ⊥ ⊤ := by
    intro htr
    obtain ⟨a, b, hab⟩ := hnonab
    have h1 : ∀ g, σ g = 1 := by
      intro g
      apply Units.ext
      rw [Units.val_one]
      ext i j
      have h0 : endRep σ g (Pi.single j 1) - Pi.single j 1 = 0 :=
        (Submodule.mem_bot (ZMod 2)).1 (htr g (Pi.single j 1) Submodule.mem_top)
      rw [sub_eq_zero, endRep_apply] at h0
      have hij := congrFun h0 i
      have hcol : ((σ g : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
          Pi.single j 1 = fun k => ((σ g : GL (Fin n) (ZMod 2)) :
            Matrix (Fin n) (Fin n) (ZMod 2)) k j := by
        funext k
        simp [Matrix.mulVec, dotProduct, Pi.single_apply]
      rw [hcol] at hij
      have hij' : ((σ g : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) i j =
          (Pi.single j (1 : ZMod 2) : Fin n → ZMod 2) i := hij
      rw [hij', Matrix.one_apply, Pi.single_apply]
    exact hab (hσ ((h1 _).trans ((h1 _).symm)))
  obtain ⟨d, hd1, hdlt, τ, hτ, hτirr⟩ :=
    exists_faithful_irreducible_rep hnonab (endRep σ) hntriv ⟨X, hXinv, hX0, hX1⟩
  rw [Module.finrank_fin_fun] at hdlt
  have hdn : d ≤ n - 1 := by omega
  exact ⟨⟨d, hd1, hdn, τ, hτ, hτirr⟩, padRep (Nat.add_sub_cancel' hdn) τ,
    padRep_injective _ τ hτ⟩

end CFSG.Monster.B.OddDegree
