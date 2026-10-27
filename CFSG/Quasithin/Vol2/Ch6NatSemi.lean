module

public import CFSG.Quasithin.Vol2.Ch6NatMod

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

variable {G : Type} [Group G]

structure NatL2Data (L V : Subgroup G) (n : ℕ) : Type 1 where
  K : Type
  [instField : Field K]
  [instFinite : Finite K]
  E : ↥V ≃* Multiplicative (Fin 2 → K)
  card : Nat.card K = 2 ^ n
  π : ↥(Assembly.LowTwoRank.StatedSL 2 K) →* ↥(autOn L V)
  surj : Function.Surjective π
  le_normalizer : L ≤ Subgroup.normalizer (V : Set G)
  inter : ∀ (γ : ↥(Assembly.LowTwoRank.StatedSL 2 K)) (v : ↥V),
    Multiplicative.toAdd (E (((π γ : ↥(autOn L V)) : MulAut ↥V) v)) =
      ((γ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).mulVec
        (Multiplicative.toAdd (E v))

attribute [instance] NatL2Data.instField NatL2Data.instFinite

variable {L V : Subgroup G} {n : ℕ}

theorem IsNatModCh5.nonempty_data (h : IsNatModCh5 L V n) : Nonempty (NatL2Data L V n) := by
  obtain ⟨_, K, _, _, π, E, hcard, hsurj, hE⟩ := h.exists_equiv
  exact ⟨⟨K, E, hcard, π, hsurj, h.1, hE⟩⟩

noncomputable def IsNatModCh5.data (h : IsNatModCh5 L V n) : NatL2Data L V n :=
  Classical.choice h.nonempty_data

namespace NatL2Data

variable (D : NatL2Data L V n)

@[expose]
noncomputable def conj (g : Subgroup.normalizer (V : Set G)) : (Fin 2 → D.K) ≃+ (Fin 2 → D.K) :=
  MulEquiv.toAdditive ((D.E.symm.trans (conjAct V g)).trans D.E)

theorem conj_apply (g : Subgroup.normalizer (V : Set G)) (v : ↥V) :
    D.conj g (Multiplicative.toAdd (D.E v)) = Multiplicative.toAdd (D.E (conjAct V g v)) := by
  change Additive.ofMul (D.E (conjAct V g (D.E.symm (D.E v)))) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

theorem det_eq_one (γ : ↥(Assembly.LowTwoRank.StatedSL 2 D.K)) :
    ((γ : Matrix.GeneralLinearGroup (Fin 2) D.K) : Matrix (Fin 2) (Fin 2) D.K).det = 1 := by
  have hγ := γ.2
  unfold Assembly.LowTwoRank.StatedSL at hγ
  refine Subgroup.closure_induction (p := fun x _ =>
    ((x : Matrix.GeneralLinearGroup (Fin 2) D.K) : Matrix (Fin 2) (Fin 2) D.K).det = 1)
    (fun x hx => hx) (by simp) (fun x y _ _ hx hy => by simp [Matrix.det_mul, hx, hy])
    (fun x _ hx => ?_) hγ
  have h1 := Matrix.det_mul (x : Matrix (Fin 2) (Fin 2) D.K)
    ((x⁻¹ : Matrix.GeneralLinearGroup (Fin 2) D.K) : Matrix (Fin 2) (Fin 2) D.K)
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, hx, one_mul] at h1
  exact h1.symm

@[expose] noncomputable def toSL (γ : ↥(Assembly.LowTwoRank.StatedSL 2 D.K)) :
    Matrix.SpecialLinearGroup (Fin 2) D.K :=
  ⟨((γ : Matrix.GeneralLinearGroup (Fin 2) D.K) : Matrix (Fin 2) (Fin 2) D.K), D.det_eq_one γ⟩

theorem exists_matrix_of_mem (g : Subgroup.normalizer (V : Set G)) (hg : (g : G) ∈ L) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) D.K,
      ∀ w, D.conj g w = (A : Matrix (Fin 2) (Fin 2) D.K).mulVec w := by
  obtain ⟨γ, hγ⟩ := D.surj ⟨conjAct V g, mem_autOn_iff.mpr ⟨g, hg, rfl⟩⟩
  refine ⟨D.toSL γ, fun w => ?_⟩
  obtain ⟨v, rfl⟩ := (Multiplicative.toAdd.trans D.E.toEquiv.symm).symm.surjective w
  have hv : (Multiplicative.toAdd.trans D.E.toEquiv.symm).symm v =
      Multiplicative.toAdd (D.E v) := rfl
  rw [hv, D.conj_apply]
  have := D.inter γ v
  rw [hγ] at this
  exact this

theorem exists_mem_of_matrix (A : Matrix.SpecialLinearGroup (Fin 2) D.K) :
    ∃ g : Subgroup.normalizer (V : Set G), (g : G) ∈ L ∧
      ∀ w, D.conj g w = (A : Matrix (Fin 2) (Fin 2) D.K).mulVec w := by
  obtain ⟨g, hgL, hg⟩ := mem_autOn_iff.mp (D.π (slToStated A)).2
  refine ⟨g, hgL, fun w => ?_⟩
  obtain ⟨v, rfl⟩ := (Multiplicative.toAdd.trans D.E.toEquiv.symm).symm.surjective w
  have hv : (Multiplicative.toAdd.trans D.E.toEquiv.symm).symm v =
      Multiplicative.toAdd (D.E v) := rfl
  rw [hv, D.conj_apply, hg]
  exact D.inter (slToStated A) v

theorem conj_mul (g h : Subgroup.normalizer (V : Set G)) (w : Fin 2 → D.K) :
    D.conj (g * h) w = D.conj g (D.conj h w) := by
  change Additive.ofMul (D.E (conjAct V (g * h) (D.E.symm (Additive.toMul w)))) =
    Additive.ofMul (D.E (conjAct V g (D.E.symm (D.E (conjAct V h
      (D.E.symm (Additive.toMul w)))))))
  rw [MulEquiv.symm_apply_apply, map_mul]
  rfl

theorem normalizesSL2 (m : Subgroup.normalizer (V : Set G))
    (hm : (m : G) ∈ Subgroup.normalizer (L : Set G)) : NormalizesSL2 (D.conj m) := by
  intro A
  obtain ⟨g, hgL, hg⟩ := D.exists_mem_of_matrix A
  have hmg : (m * g * m⁻¹ : Subgroup.normalizer (V : Set G)) ∈
      (L.subgroupOf (Subgroup.normalizer (V : Set G))) := by
    rw [Subgroup.mem_subgroupOf]
    simpa using (Subgroup.mem_normalizer_iff.mp hm g).mp hgL
  obtain ⟨B, hB⟩ := D.exists_matrix_of_mem (m * g * m⁻¹) hmg
  refine ⟨B, fun v => ?_⟩
  rw [← hg, ← hB, ← D.conj_mul, ← D.conj_mul]
  congr 2
  group

theorem exists_semilinear (m : Subgroup.normalizer (V : Set G))
    (hm : (m : G) ∈ Subgroup.normalizer (L : Set G)) :
    ∃ σ : D.K ≃+* D.K, ∀ (a : D.K) (w : Fin 2 → D.K), D.conj m (a • w) = σ a • D.conj m w :=
  (D.normalizesSL2 m hm).exists_semilinear

end NatL2Data

end CFSG.Quasithin.H13
