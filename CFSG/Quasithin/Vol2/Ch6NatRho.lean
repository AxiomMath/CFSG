module

public import CFSG.Quasithin.Vol2.Ch6NatFacts

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

variable {G : Type} [Group G] {L V : Subgroup G} {n : ℕ}

namespace NatL2Data

variable (D : NatL2Data L V n)

theorem π_injective : Function.Injective D.π := by
  rw [injective_iff_map_eq_one]
  intro γ hγ
  have hfix : ∀ w : Fin 2 → D.K,
      ((γ : Matrix.GeneralLinearGroup (Fin 2) D.K) : Matrix (Fin 2) (Fin 2) D.K).mulVec w = w := by
    intro w
    obtain ⟨v, rfl⟩ : ∃ v : ↥V, Multiplicative.toAdd (D.E v) = w :=
      ⟨D.E.symm (Multiplicative.ofAdd w), by simp⟩
    rw [← D.inter γ v, hγ]
    rfl
  have hm : ((γ : Matrix.GeneralLinearGroup (Fin 2) D.K) : Matrix (Fin 2) (Fin 2) D.K) = 1 :=
    matrix_eq_of_mulVec_eq fun w => by rw [hfix, Matrix.one_mulVec]
  apply Subtype.ext
  exact Units.ext hm

@[expose] noncomputable def toAut : ↥L →* ↥(autOn L V) where
  toFun ℓ := ⟨conjAct V ⟨ℓ, D.le_normalizer ℓ.2⟩, mem_autOn_iff.mpr ⟨_, ℓ.2, rfl⟩⟩
  map_one' := Subtype.ext (map_one (conjAct V))
  map_mul' ℓ ℓ' := Subtype.ext
    (map_mul (conjAct V) ⟨ℓ, D.le_normalizer ℓ.2⟩ ⟨ℓ', D.le_normalizer ℓ'.2⟩)

@[expose]
noncomputable def toSLHom :
    ↥(Assembly.LowTwoRank.StatedSL 2 D.K) →* Matrix.SpecialLinearGroup (Fin 2) D.K where
  toFun := D.toSL
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

@[expose] noncomputable def rho : ↥L →* Matrix.SpecialLinearGroup (Fin 2) D.K :=
  D.toSLHom.comp
    ((MulEquiv.ofBijective D.π ⟨D.π_injective, D.surj⟩).symm.toMonoidHom.comp D.toAut)

theorem conj_eq_rho (ℓ : ↥L) (w : Fin 2 → D.K) :
    D.conj ⟨ℓ, D.le_normalizer ℓ.2⟩ w = ((D.rho ℓ : Matrix.SpecialLinearGroup (Fin 2) D.K) :
      Matrix (Fin 2) (Fin 2) D.K).mulVec w := by
  obtain ⟨v, rfl⟩ : ∃ v : ↥V, Multiplicative.toAdd (D.E v) = w :=
    ⟨D.E.symm (Multiplicative.ofAdd w), by simp⟩
  rw [D.conj_apply]
  set γ := (MulEquiv.ofBijective D.π ⟨D.π_injective, D.surj⟩).symm (D.toAut ℓ) with hγ
  have hπγ : D.π γ = D.toAut ℓ := by
    rw [hγ]
    exact (MulEquiv.ofBijective D.π ⟨D.π_injective, D.surj⟩).apply_symm_apply _
  have := D.inter γ v
  rw [hπγ] at this
  exact this

theorem rho_surjective : Function.Surjective D.rho := by
  intro A
  obtain ⟨g, hgL, hg⟩ := D.exists_mem_of_matrix A
  refine ⟨⟨g, hgL⟩, Subtype.ext ?_⟩
  apply matrix_eq_of_mulVec_eq
  intro w
  rw [← D.conj_eq_rho]
  exact hg w

theorem mem_ker_rho_iff (ℓ : ↥L) :
    ℓ ∈ D.rho.ker ↔ (ℓ : G) ∈ Subgroup.centralizer (V : Set G) := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    apply D.mem_centralizer_of_conj_eq ⟨ℓ, D.le_normalizer ℓ.2⟩
    intro w
    rw [D.conj_eq_rho, h]
    simp
  · intro h
    apply Subtype.ext
    apply matrix_eq_of_mulVec_eq
    intro w
    rw [← D.conj_eq_rho, D.conj_eq_of_mem_centralizer _ h]
    simp

theorem fixed_iff {X : Subgroup G} (hXL : X ≤ L) (v : ↥V) :
    (v : G) ∈ Subgroup.centralizer (X : Set G) ↔
      ∀ x : ↥L, (x : G) ∈ X → ((D.rho x : Matrix.SpecialLinearGroup (Fin 2) D.K) :
        Matrix (Fin 2) (Fin 2) D.K).mulVec (Multiplicative.toAdd (D.E v)) =
          Multiplicative.toAdd (D.E v) := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h x hx
    rw [← D.conj_eq_rho, D.conj_apply]
    congr 2
    apply Subtype.ext
    rw [conjAct_apply_coe]
    have := h x hx
    calc (x : G) * v * (x : G)⁻¹ = v * x * (x : G)⁻¹ := by rw [this]
      _ = v := by group
  · intro h x hx
    have h1 := h ⟨x, hXL hx⟩ hx
    rw [← D.conj_eq_rho, D.conj_apply] at h1
    have h2 := congrArg Subtype.val (D.E.injective (Multiplicative.toAdd.injective h1))
    rw [conjAct_apply_coe] at h2
    calc x * (v : G) = (x * v * x⁻¹) * x := by group
      _ = v * x := by rw [h2]

end NatL2Data

end CFSG.Quasithin.H13
