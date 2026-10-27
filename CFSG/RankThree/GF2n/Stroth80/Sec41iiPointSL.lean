module

public import CFSG.RankThree.GF2n.Stroth80.Sec41iiTensorNat
public import CFSG.ClassicalGroups.PCoreSection

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.Open CFSG.Open.StatedAPI CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

private noncomputable def pointStabSL {m : ℕ} {K : Type} [Field K] (u : Fin m → K) :
    Subgroup (GL (Fin m) K) where
  carrier := {g | g ∈ StatedSL m K ∧
    ∃ c : K, c ≠ 0 ∧ (g : Matrix (Fin m) (Fin m) K) *ᵥ u = c • u}
  mul_mem' := by
    rintro g h ⟨hg, c, hc0, hc⟩ ⟨hh, d, hd0, hd⟩
    refine ⟨mul_mem hg hh, d * c, mul_ne_zero hd0 hc0, ?_⟩
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hd, Matrix.mulVec_smul, hc, smul_smul]
  one_mem' := ⟨one_mem _, 1, one_ne_zero, by rw [Units.val_one, Matrix.one_mulVec, one_smul]⟩
  inv_mem' := by
    rintro g ⟨hg, c, hc0, hc⟩
    refine ⟨inv_mem hg, c⁻¹, inv_ne_zero hc0, ?_⟩
    calc ((g⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ u
        = ((g⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ
            (c⁻¹ • ((g : Matrix (Fin m) (Fin m) K) *ᵥ u)) := by
          rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
      _ = c⁻¹ • u := by
          rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]

private theorem mem_pointStabSL {m : ℕ} {K : Type} [Field K] {u : Fin m → K}
    {g : GL (Fin m) K} :
    g ∈ pointStabSL u ↔
      g ∈ StatedSL m K ∧ ∃ c : K, c ≠ 0 ∧ (g : Matrix (Fin m) (Fin m) K) *ᵥ u = c • u :=
  Iff.rfl

private def transvectionMat {m : ℕ} {K : Type} [Field K] (w r : Fin m → K) :
    Matrix (Fin m) (Fin m) K :=
  1 + Matrix.replicateCol Unit w * Matrix.replicateRow Unit r

private theorem transvectionMat_mulVec {m : ℕ} {K : Type} [Field K] (w r v : Fin m → K) :
    transvectionMat w r *ᵥ v = v + (r ⬝ᵥ v) • w := by
  unfold transvectionMat
  rw [Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec]
  congr 1
  ext i
  simp [Matrix.mulVec, dotProduct, Matrix.replicateCol, Matrix.replicateRow, mul_comm]

private theorem det_transvectionMat {m : ℕ} {K : Type} [Field K] (w r : Fin m → K) :
    (transvectionMat w r).det = 1 + r ⬝ᵥ w :=
  Matrix.det_one_add_replicateCol_mul_replicateRow (ι := Unit) w r

private noncomputable def transvectionGL {m : ℕ} {K : Type} [Field K] (w r : Fin m → K)
    (h : r ⬝ᵥ w = 0) : GL (Fin m) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (transvectionMat w r)
    (by rw [det_transvectionMat, h, add_zero]; exact one_ne_zero)

private theorem transvectionGL_val {m : ℕ} {K : Type} [Field K] (w r : Fin m → K)
    (h : r ⬝ᵥ w = 0) :
    ((transvectionGL w r h : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) = transvectionMat w r :=
  rfl

private theorem transvectionGL_mem {m : ℕ} {K : Type} [Field K] {u : Fin m → K}
    (w r : Fin m → K) (hw : r ⬝ᵥ w = 0) (hu : r ⬝ᵥ u = 0) :
    transvectionGL w r hw ∈ pointStabSL u := by
  have hdet : ((transvectionGL w r hw : GL (Fin m) K) : Matrix (Fin m) (Fin m) K).det = 1 := by
    rw [transvectionGL_val, det_transvectionMat, hw, add_zero]
  refine mem_pointStabSL.mpr ⟨mem_statedSL_of_det hdet, 1, one_ne_zero, ?_⟩
  rw [transvectionGL_val, transvectionMat_mulVec, hu, zero_smul, add_zero, one_smul]

private theorem exists_row_of_not_mem_span {m : ℕ} {K : Type} [Field K] {u x : Fin m → K}
    (hx : x ∉ Submodule.span K {u}) : ∃ r : Fin m → K, r ⬝ᵥ u = 0 ∧ r ⬝ᵥ x = 1 := by
  obtain ⟨f, hfx, hfu⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance
  have hf0 : f u = 0 := by
    have h : f u ∈ (Submodule.span K {u}).map f :=
      Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self u)
    rwa [hfu, Submodule.mem_bot] at h
  obtain ⟨g, hgx, hgu⟩ : ∃ g : Module.Dual K (Fin m → K), g x = 1 ∧ g u = 0 :=
    ⟨(f x)⁻¹ • f, by rw [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hfx],
      by rw [LinearMap.smul_apply, hf0, smul_zero]⟩
  obtain ⟨r, hr⟩ : ∃ r : Fin m → K, ∀ w : Fin m → K, g w = r ⬝ᵥ w := by
    refine ⟨fun i => g (fun j => if i = j then 1 else 0), fun w => ?_⟩
    rw [LinearMap.pi_apply_eq_sum_univ g w]
    simp [dotProduct, mul_comm]
  exact ⟨r, by rw [← hr, hgu], by rw [← hr, hgx]⟩

private theorem eq_top_of_stable {m : ℕ} {K : Type} [Field K] {u : Fin m → K}
    (X : Submodule K (Fin m → K)) {x : Fin m → K} (hx : x ∈ X)
    (hxL : x ∉ Submodule.span K {u})
    (hX : ∀ s ∈ pointStabSL u, ∀ y ∈ X, (s : Matrix (Fin m) (Fin m) K) *ᵥ y ∈ X) :
    X = ⊤ := by
  obtain ⟨r, hru, hrx⟩ := exists_row_of_not_mem_span hxL
  have hker : ∀ v : Fin m → K, r ⬝ᵥ v = 0 → v ∈ X := by
    intro v hv
    have hg := hX _ (transvectionGL_mem v r hv hru) x hx
    rw [transvectionGL_val, transvectionMat_mulVec, hrx, one_smul] at hg
    have h' := X.sub_mem hg hx
    rwa [add_sub_cancel_left] at h'
  rw [eq_top_iff]
  intro y _
  have hmem : y - (r ⬝ᵥ y) • x ∈ X := by
    refine hker _ ?_
    rw [dotProduct_sub, dotProduct_smul, hrx, smul_eq_mul, mul_one, sub_self]
  have h' := X.add_mem hmem (X.smul_mem (r ⬝ᵥ y) hx)
  rwa [sub_add_cancel] at h'

private theorem card_le_pow_of_fixed_line {K : Type} [Field K] [Finite K] {m : ℕ}
    {u : Fin m → K} (hu : u ≠ 0) (P : Subgroup (GL (Fin m) K))
    (hPu : ∀ p ∈ P, (p : Matrix (Fin m) (Fin m) K) *ᵥ u = u)
    (key : ∀ p ∈ P, ∀ x : Fin m → K,
      (p : Matrix (Fin m) (Fin m) K) *ᵥ x - x ∈ Submodule.span K {u}) :
    Nat.card P ≤ Nat.card K ^ (m - 1) := by
  obtain ⟨i0, hi0⟩ : ∃ i, u i ≠ 0 := Function.ne_iff.mp hu
  let ψ : Module.Dual K (Fin m → K) := (u i0)⁻¹ • LinearMap.proj i0
  let Φ : P → Module.Dual K (Fin m → K) := fun p =>
    ψ.comp (Matrix.toLin' ((p : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) - LinearMap.id)
  have hΦ : ∀ (p : P) (w : Fin m → K),
      ((p : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ w - w = Φ p w • u := by
    intro p w
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (key p p.2 w)
    have hval : Φ p w = a := by
      simp only [Φ, ψ, LinearMap.comp_apply, LinearMap.sub_apply, Matrix.toLin'_apply,
        LinearMap.id_apply, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]
      rw [← ha, Pi.smul_apply, smul_eq_mul, mul_left_comm, inv_mul_cancel₀ hi0, mul_one]
    rw [hval, ← ha]
  have hΦu : ∀ p : P, Φ p u = 0 := by
    intro p
    have h := hΦ p u
    rw [hPu p p.2, sub_self] at h
    exact (smul_eq_zero.mp h.symm).resolve_right hu
  have hmem : ∀ p : P, Φ p ∈ (Submodule.span K {u}).dualAnnihilator := by
    intro p
    rw [Submodule.mem_dualAnnihilator]
    intro w hw
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [map_smul, hΦu p, smul_zero]
  let Ψ : P → (Submodule.span K {u}).dualAnnihilator := fun p => ⟨Φ p, hmem p⟩
  have hΨ : Function.Injective Ψ := by
    intro p q hpq
    have hΦeq : Φ p = Φ q := congrArg Subtype.val hpq
    have hM : Matrix.toLin' ((p : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) =
        Matrix.toLin' ((q : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) := by
      apply LinearMap.ext
      intro w
      have h1 := hΦ p w
      have h2 := hΦ q w
      rw [hΦeq] at h1
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
      exact sub_left_inj.mp (h1.trans h2.symm)
    exact Subtype.ext (Units.ext (Matrix.toLin'.injective hM))
  have hdim : Module.finrank K (Submodule.span K {u}).dualAnnihilator = m - 1 := by
    have h1 := Subspace.finrank_add_finrank_dualAnnihilator_eq (Submodule.span K {u})
    rw [finrank_span_singleton hu, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h1
    omega
  haveI : Module.Finite K (Module.Dual K (Fin m → K)) := inferInstance
  haveI : Module.Finite K (Submodule.span K {u}).dualAnnihilator := inferInstance
  haveI : Finite (Submodule.span K {u}).dualAnnihilator := Module.finite_of_finite (R := K)
  calc Nat.card P ≤ Nat.card (Submodule.span K {u}).dualAnnihilator :=
        Nat.card_le_card_of_injective Ψ hΨ
    _ = Nat.card K ^ (m - 1) := by
        rw [Module.natCard_eq_pow_finrank (K := K) (V := (Submodule.span K {u}).dualAnnihilator),
          hdim]

theorem classicalPointSL : ClassicalPointSLStatement := by
  intro K _ _ _ _ m _
  intro u hu P hPX hP2 hPu hPnorm
  have hlin : CFSG.ClassicalGroups.PCoreSection.IsLinearAction K
      (fun (g : GL (Fin m) K) (x : Fin m → K) => (g : Matrix (Fin m) (Fin m) K) *ᵥ x) :=
    { one := fun x => by simp
      mul := fun g h x => by simp [← Matrix.mulVec_mulVec]
      add := fun g x y => Matrix.mulVec_add _ _ _
      smul := fun g c x => Matrix.mulVec_smul _ _ _ }
  have hPS : P ≤ pointStabSL u := fun p hp =>
    mem_pointStabSL.mpr ⟨hPX hp, 1, one_ne_zero, by rw [hPu p hp, one_smul]⟩
  have hT : IsPGroup 2 P := by
    intro g
    refine ⟨1, ?_⟩
    rw [pow_one, pow_two]
    exact Subtype.ext (hP2 g g.2)
  have hTn : ∀ s ∈ pointStabSL u, ∀ t ∈ P, s * t * s⁻¹ ∈ P := by
    intro s hs t ht
    obtain ⟨hs1, c, -, hc⟩ := mem_pointStabSL.mp hs
    exact hPnorm s hs1 ⟨c, hc⟩ t ht
  have hL : ∀ s ∈ pointStabSL u, ∀ y ∈ Submodule.span K {u},
      (s : Matrix (Fin m) (Fin m) K) *ᵥ y ∈ Submodule.span K {u} := by
    intro s hs y hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
    obtain ⟨-, c, -, hc⟩ := mem_pointStabSL.mp hs
    rw [Matrix.mulVec_smul, hc, smul_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)
  have hPtop : ∀ s ∈ pointStabSL u, ∀ y ∈ (⊤ : Submodule K (Fin m → K)),
      (s : Matrix (Fin m) (Fin m) K) *ᵥ y ∈ (⊤ : Submodule K (Fin m → K)) :=
    fun _ _ _ _ => Submodule.mem_top
  have hirr : ∀ X : Submodule K (Fin m → K), Submodule.span K {u} ≤ X → X ≤ ⊤ →
      (∀ s ∈ pointStabSL u, ∀ y ∈ X, (s : Matrix (Fin m) (Fin m) K) *ᵥ y ∈ X) →
        X = Submodule.span K {u} ∨ X = ⊤ := by
    intro X hLX _ hXinv
    by_cases hX : X ≤ Submodule.span K {u}
    · exact Or.inl (le_antisymm hX hLX)
    · obtain ⟨x, hxX, hxL⟩ := SetLike.not_le_iff_exists.mp hX
      exact Or.inr (eq_top_of_stable X hxX hxL hXinv)
  have key : ∀ p ∈ P, ∀ x : Fin m → K,
      (p : Matrix (Fin m) (Fin m) K) *ᵥ x - x ∈ Submodule.span K {u} :=
    fun p hp x => CFSG.ClassicalGroups.PCoreSection.apply_sub_mem_of_isPGroup hlin hPS hT hTn
      le_top hPtop hL hirr p hp x Submodule.mem_top
  refine ⟨?_, fun _ p hp v => key p hp v⟩
  rw [Fintype.card_fin]
  exact card_le_pow_of_fixed_line hu P hPu key

end CFSG.RankThree.GF2n.Stroth80
