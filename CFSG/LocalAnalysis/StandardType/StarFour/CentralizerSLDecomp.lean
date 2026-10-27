module

public import CFSG.LocalAnalysis.StandardType.StarFour.CentralizerSLBlock
public import CFSG.RankThree.PartOne.KC.LinearCommutantPiGL

public section

namespace CFSG.StandardType.StarFour

variable {F : Type} [Field F] {P : Type} [CommGroup P] {V : Type} [AddCommGroup V]
  [Module F V]

variable {ρ : P →* (V ≃ₗ[F] V)}

namespace SemiFrame

variable (fr : SemiFrame F ρ)

@[expose] noncomputable def blockHomFun (i : Fin fr.r) :
    SpecialLinearGroup (fr.E i) (Fin (fr.m i) → fr.E i) → fr.slOnBlock i :=
  fun B => ⟨blockSpecialLinear fr i B,
    show blockSpecialLinear fr i B ∈ fr.slOnBlock i from ⟨B, blockSpecialLinear_apply fr i B⟩⟩

@[expose] noncomputable def blockWitness (i : Fin fr.r) (g : fr.slOnBlock i) :
    SpecialLinearGroup (fr.E i) (Fin (fr.m i) → fr.E i) :=
  Classical.choose (show ∃ B : SpecialLinearGroup (fr.E i) (Fin (fr.m i) → fr.E i),
      ∀ v, fr.Φ ((g : SpecialLinearGroup F V) v) = Function.update (fr.Φ v) i (B (fr.Φ v i))
      from g.2)

theorem blockWitness_spec (i : Fin fr.r) (g : fr.slOnBlock i) (v : V) :
    fr.Φ ((g : SpecialLinearGroup F V) v) =
      Function.update (fr.Φ v) i (blockWitness fr i g (fr.Φ v i)) :=
  Classical.choose_spec (show ∃ B : SpecialLinearGroup (fr.E i) (Fin (fr.m i) → fr.E i),
      ∀ v, fr.Φ ((g : SpecialLinearGroup F V) v) = Function.update (fr.Φ v) i (B (fr.Φ v i))
      from g.2) v

@[expose] noncomputable def blockMulEquiv (i : Fin fr.r) :
    SpecialLinearGroup (fr.E i) (Fin (fr.m i) → fr.E i) ≃* fr.slOnBlock i where
  toFun := blockHomFun fr i
  invFun g := blockWitness fr i g
  left_inv B := by
    change blockWitness fr i (blockHomFun fr i B) = B
    exact (blockUpdate_witness_unique fr i (blockSpecialLinear fr i B)
      (blockWitness fr i (blockHomFun fr i B)) B
      (blockWitness_spec fr i (blockHomFun fr i B))
      (blockSpecialLinear_apply fr i B))
  right_inv g := by
    apply Subtype.ext
    apply SpecialLinearGroup.ext
    intro v
    change blockSpecialLinear fr i (blockWitness fr i g) v = (g : SpecialLinearGroup F V) v
    apply fr.Φ.injective
    rw [blockSpecialLinear_apply fr i (blockWitness fr i g) v]
    exact (blockWitness_spec fr i g v).symm
  map_mul' B₁ B₂ := by
    apply Subtype.ext
    exact blockSpecialLinear_mul fr i B₁ B₂

theorem blockLin_exists (h : repCentSL ρ) (j : Fin fr.r) :
    ∃ B : (Fin (fr.m j) → fr.E j) →ₗ[fr.E j] (Fin (fr.m j) → fr.E j),
      ∀ v, fr.Φ ((h : V ≃ₗ[F] V) v) j = B (fr.Φ v j) :=
  ((fr.comm (h : V ≃ₗ[F] V)).mp fun p =>
    (Subgroup.mem_centralizer_iff.mp h.2 (ρ p) ⟨p, rfl⟩).symm) j

@[expose] noncomputable def blockLin (h : repCentSL ρ) (j : Fin fr.r) :
    (Fin (fr.m j) → fr.E j) →ₗ[fr.E j] (Fin (fr.m j) → fr.E j) :=
  Classical.choose (blockLin_exists fr h j)

theorem blockLin_spec (h : repCentSL ρ) (j : Fin fr.r) (v : V) :
    fr.Φ ((h : V ≃ₗ[F] V) v) j = blockLin fr h j (fr.Φ v j) :=
  (Classical.choose_spec (blockLin_exists fr h j)) v

theorem blockLin_unique (h : repCentSL ρ) (j : Fin fr.r)
    (B : (Fin (fr.m j) → fr.E j) →ₗ[fr.E j] (Fin (fr.m j) → fr.E j))
    (hB : ∀ v, fr.Φ ((h : V ≃ₗ[F] V) v) j = B (fr.Φ v j)) :
    B = blockLin fr h j := by
  apply LinearMap.ext
  intro x
  obtain ⟨v, hv⟩ := exists_phi_eq fr j x
  rw [← hv, ← hB v]
  exact blockLin_spec fr h j v

theorem repCentSL_mul_apply (h₁ h₂ : repCentSL ρ) (v : V) :
    ((h₁ * h₂ : repCentSL ρ) : V ≃ₗ[F] V) v =
      (h₁ : V ≃ₗ[F] V) ((h₂ : V ≃ₗ[F] V) v) := by
  rw [show ((h₁ * h₂ : repCentSL ρ) : V ≃ₗ[F] V) =
    (h₁ : V ≃ₗ[F] V) * (h₂ : V ≃ₗ[F] V) from rfl, LinearEquiv.mul_apply]

theorem blockLin_inv_comp (h : repCentSL ρ) (j : Fin fr.r) (x) :
    blockLin fr h⁻¹ j (blockLin fr h j x) = x := by
  obtain ⟨v, hv⟩ := exists_phi_eq fr j x
  rw [← hv, ← blockLin_spec fr h j v,
    ← blockLin_spec fr h⁻¹ j ((h : V ≃ₗ[F] V) v)]
  have h1 : ((h⁻¹ : repCentSL ρ) : V ≃ₗ[F] V) ((h : V ≃ₗ[F] V) v) = v := by
    change ((h⁻¹ * h : repCentSL ρ) : V ≃ₗ[F] V) v = v
    rw [inv_mul_cancel]
    rfl
  rw [h1]

theorem blockLin_comp_inv (h : repCentSL ρ) (j : Fin fr.r) (x) :
    blockLin fr h j (blockLin fr h⁻¹ j x) = x := by
  have h' := blockLin_inv_comp fr h⁻¹ j x
  rwa [inv_inv] at h'

@[expose] noncomputable def blockEquiv (h : repCentSL ρ) (j : Fin fr.r) :
    (Fin (fr.m j) → fr.E j) ≃ₗ[fr.E j] (Fin (fr.m j) → fr.E j) where
  toFun := blockLin fr h j
  map_add' := (blockLin fr h j).map_add
  map_smul' := (blockLin fr h j).map_smul
  invFun := blockLin fr h⁻¹ j
  left_inv := blockLin_inv_comp fr h j
  right_inv := blockLin_comp_inv fr h j

theorem blockLin_mul (h₁ h₂ : repCentSL ρ) (j : Fin fr.r) :
    blockLin fr (h₁ * h₂) j = (blockLin fr h₁ j).comp (blockLin fr h₂ j) := by
  symm
  apply blockLin_unique
  intro v
  rw [LinearMap.comp_apply, ← blockLin_spec fr h₂ j v,
    ← blockLin_spec fr h₁ j ((h₂ : V ≃ₗ[F] V) v)]
  exact congrArg (fun w => fr.Φ w j) (repCentSL_mul_apply h₁ h₂ v)

theorem blockLin_one (j : Fin fr.r) :
    blockLin fr (1 : repCentSL ρ) j = LinearMap.id := by
  symm
  apply blockLin_unique
  intro v
  rw [LinearMap.id_apply]
  rfl

theorem blockEquiv_one (j : Fin fr.r) :
    blockEquiv fr (1 : repCentSL ρ) j = 1 := by
  apply LinearEquiv.ext
  intro x
  change blockLin fr (1 : repCentSL ρ) j x = x
  rw [blockLin_one, LinearMap.id_apply]

theorem blockEquiv_mul (h₁ h₂ : repCentSL ρ) (j : Fin fr.r) :
    blockEquiv fr (h₁ * h₂) j = blockEquiv fr h₁ j * blockEquiv fr h₂ j := by
  apply LinearEquiv.ext
  intro x
  change blockLin fr (h₁ * h₂) j x = blockLin fr h₁ j (blockLin fr h₂ j x)
  rw [blockLin_mul, LinearMap.comp_apply]

@[expose] noncomputable def linEquivToGL {E : Type} [Field E] {n : ℕ} :
    ((Fin n → E) ≃ₗ[E] (Fin n → E)) ≃* GL (Fin n) E :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv E (Fin n → E)).symm.trans
    (Matrix.GeneralLinearGroup.toLin (n := Fin n) (R := E)).symm

theorem linEquivToGL_toLin' {E : Type} [Field E] {n : ℕ}
    (s : Matrix.SpecialLinearGroup (Fin n) E) :
    linEquivToGL (((Matrix.SpecialLinearGroup.toLin'_equiv s : SpecialLinearGroup E (Fin n → E)) :
      (Fin n → E) ≃ₗ[E] (Fin n → E))) = Matrix.SpecialLinearGroup.toGL s := by
  apply (Matrix.GeneralLinearGroup.toLin (n := Fin n) (R := E)).injective
  change (Matrix.GeneralLinearGroup.toLin (n := Fin n) (R := E))
      ((Matrix.GeneralLinearGroup.toLin (n := Fin n) (R := E)).symm
        ((LinearMap.GeneralLinearGroup.generalLinearEquiv E (Fin n → E)).symm
          ((Matrix.SpecialLinearGroup.toLin'_equiv s : SpecialLinearGroup E (Fin n → E)) :
            (Fin n → E) ≃ₗ[E] (Fin n → E)))) =
    (Matrix.GeneralLinearGroup.toLin (n := Fin n) (R := E))
      (Matrix.SpecialLinearGroup.toGL s)
  rw [MulEquiv.apply_symm_apply]
  apply Units.ext
  rfl

@[expose] noncomputable def blockPiGL :
    repCentSL ρ →* (∀ j, GL (Fin (fr.m j)) (fr.E j)) where
  toFun h := fun j => linEquivToGL (blockEquiv fr h j)
  map_one' := by
    funext j
    rw [blockEquiv_one]
    exact map_one _
  map_mul' h₁ h₂ := by
    funext j
    rw [blockEquiv_mul]
    exact map_mul _ _ _

@[expose] noncomputable def slOnBlockWitness (h : repCentSL ρ) (b : Fin fr.r)
    (hh : (h : SpecialLinearGroup F V) ∈ fr.slOnBlock b) :
    SpecialLinearGroup (fr.E b) (Fin (fr.m b) → fr.E b) :=
  Classical.choose (show ∃ B : SpecialLinearGroup (fr.E b) (Fin (fr.m b) → fr.E b),
      ∀ v, fr.Φ ((h : V ≃ₗ[F] V) v) = Function.update (fr.Φ v) b (B (fr.Φ v b)) from hh)

theorem slOnBlockWitness_spec (h : repCentSL ρ) (b : Fin fr.r)
    (hh : (h : SpecialLinearGroup F V) ∈ fr.slOnBlock b) (v : V) :
    fr.Φ ((h : V ≃ₗ[F] V) v) =
      Function.update (fr.Φ v) b (slOnBlockWitness fr h b hh (fr.Φ v b)) :=
  Classical.choose_spec (show ∃ B : SpecialLinearGroup (fr.E b) (Fin (fr.m b) → fr.E b),
      ∀ v, fr.Φ ((h : V ≃ₗ[F] V) v) = Function.update (fr.Φ v) b (B (fr.Φ v b)) from hh) v

theorem blockEquiv_eq_of_mem (h : repCentSL ρ) {b : Fin fr.r}
    (hh : (h : SpecialLinearGroup F V) ∈ fr.slOnBlock b) :
    blockEquiv fr h b = ((slOnBlockWitness fr h b hh : SpecialLinearGroup (fr.E b)
      (Fin (fr.m b) → fr.E b)) :
      (Fin (fr.m b) → fr.E b) ≃ₗ[fr.E b] (Fin (fr.m b) → fr.E b)) := by
  have hlin : blockLin fr h b = ((slOnBlockWitness fr h b hh : SpecialLinearGroup (fr.E b)
      (Fin (fr.m b) → fr.E b)) : (Fin (fr.m b) → fr.E b) →ₗ[fr.E b]
        (Fin (fr.m b) → fr.E b)) := by
    symm
    apply blockLin_unique
    intro v
    have := congrFun (slOnBlockWitness_spec fr h b hh v) b
    simpa [Function.update_self] using this
  apply LinearEquiv.ext
  intro x
  change blockLin fr h b x = _
  rw [hlin]
  rfl

theorem blockEquiv_eq_one_of_mem (h : repCentSL ρ) {b j : Fin fr.r} (hj : j ≠ b)
    (hh : (h : SpecialLinearGroup F V) ∈ fr.slOnBlock b) :
    blockEquiv fr h j = 1 := by
  have hlin : blockLin fr h j = LinearMap.id := by
    symm
    apply blockLin_unique
    intro v
    have := congrFun (slOnBlockWitness_spec fr h b hh v) j
    simpa [Function.update_of_ne hj] using this
  apply LinearEquiv.ext
  intro x
  change blockLin fr h j x = x
  rw [hlin]
  rfl

theorem mem_slOnBlock_iff_mem_comap (h : repCentSL ρ) (b : Fin fr.r) :
    (h : SpecialLinearGroup F V) ∈ fr.slOnBlock b ↔
      blockPiGL fr h ∈ CFSG.RankThree.PartOne.KCLinComm.blockSL fr.E fr.m b := by
  constructor
  · intro hh
    refine ⟨(Matrix.SpecialLinearGroup.toLin'_equiv).symm (slOnBlockWitness fr h b hh), ?_⟩
    funext j
    by_cases hj : j = b
    · rw [hj]
      rw [CFSG.RankThree.PartOne.KCLinComm.blockEmbed_apply_self]
      have hB : blockEquiv fr h b = Matrix.SpecialLinearGroup.toLin'_equiv
          ((Matrix.SpecialLinearGroup.toLin'_equiv).symm (slOnBlockWitness fr h b hh)) := by
        rw [MulEquiv.apply_symm_apply]
        exact blockEquiv_eq_of_mem fr h hh
      change Matrix.SpecialLinearGroup.toGL
        (Matrix.SpecialLinearGroup.toLin'_equiv.symm (slOnBlockWitness fr h b hh)) =
        linEquivToGL (blockEquiv fr h b)
      rw [hB]
      exact (linEquivToGL_toLin' _).symm
    · rw [CFSG.RankThree.PartOne.KCLinComm.blockEmbed_apply_of_ne hj]
      change (1 : GL (Fin (fr.m j)) (fr.E j)) = linEquivToGL (blockEquiv fr h j)
      rw [blockEquiv_eq_one_of_mem fr h hj hh, map_one]
  · rintro ⟨s, hs⟩
    refine ⟨Matrix.SpecialLinearGroup.toLin'_equiv s, fun v => ?_⟩
    funext j
    by_cases hj : j = b
    · rw [hj, Function.update_self, blockLin_spec fr h b v]
      have hBeq : blockEquiv fr h b = Matrix.SpecialLinearGroup.toLin'_equiv s := by
        have hb := congrFun hs b
        rw [CFSG.RankThree.PartOne.KCLinComm.blockEmbed_apply_self] at hb
        apply linEquivToGL.injective
        rw [linEquivToGL_toLin' s]
        exact hb.symm
      have hlin : blockLin fr h b = ((Matrix.SpecialLinearGroup.toLin'_equiv s :
          SpecialLinearGroup (fr.E b) (Fin (fr.m b) → fr.E b)) :
            (Fin (fr.m b) → fr.E b) ≃ₗ[fr.E b] (Fin (fr.m b) → fr.E b)).toLinearMap := by
        rw [← hBeq]
        rfl
      rw [hlin]
      rfl
    · rw [Function.update_of_ne hj, blockLin_spec fr h j v]
      have hb := congrFun hs j
      rw [CFSG.RankThree.PartOne.KCLinComm.blockEmbed_apply_of_ne hj] at hb
      have hjeq : blockEquiv fr h j = 1 := by
        apply linEquivToGL.injective
        rw [map_one]
        exact hb.symm
      have hlin : blockLin fr h j = LinearMap.id := by
        rw [show blockLin fr h j = (blockEquiv fr h j).toLinearMap from rfl, hjeq]
        rfl
      rw [hlin]
      rfl

end SemiFrame

end CFSG.StandardType.StarFour
