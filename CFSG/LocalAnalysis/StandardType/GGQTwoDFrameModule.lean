module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDFrameRigid
public import CFSG.LocalAnalysis.StandardType.GGQTwoDFrameStd
public import CFSG.LocalAnalysis.StandardType.GGReflShape
public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl
public import CFSG.LocalAnalysis.StandardType.GGQTwoDCoxRefl

public section

namespace CFSG.StandardType.QTwo

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.StandardType CFSG.Assembly

theorem ggCoxeterMatrixD_M_le_three (m : ℕ) (i j : Fin m) (hij : i ≠ j) :
    (ggCoxeterMatrixD m).M i j ≤ 3 := by
  rw [show (ggCoxeterMatrixD m).M i j = ggCoxeterMatrixD m i j from rfl,
    ggCoxeterMatrixD_apply, if_neg hij]
  split_ifs <;> omega

theorem reindexD_M_le_three {m : ℕ} {ι : Type} (e' : Fin m ≃ ι) (i j : ι) (hij : i ≠ j) :
    ((ggCoxeterMatrixD m).reindex e').M i j ≤ 3 := by
  rw [show ((ggCoxeterMatrixD m).reindex e').M i j = ((ggCoxeterMatrixD m).reindex e') i j
      from rfl,
    CoxeterMatrix.reindex_apply]
  exact ggCoxeterMatrixD_M_le_three m (e'.symm i) (e'.symm j)
    (fun h => hij (e'.symm.injective h))

section Module

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def qtwoE0 {Bs : Subgroup G} {A : Subgroup (MulAut ↥Bs)} {m : ℕ}
    {ι : Type} (e' : Fin m ≃ ι) (e : ((ggCoxeterMatrixD m).reindex e').Group ≃* ↥A) :
    (ggCoxeterMatrixD m).Group ≃* ↥A :=
  ((ggCoxeterMatrixD m).reindexGroupEquiv e').symm.trans e

theorem qtwoE0_simple {Bs : Subgroup G} {A : Subgroup (MulAut ↥Bs)} {m : ℕ} {ι : Type}
    (e' : Fin m ≃ ι) (e : ((ggCoxeterMatrixD m).reindex e').Group ≃* ↥A) (i : Fin m) :
    qtwoE0 e' e ((ggCoxeterMatrixD m).simple i) =
      e (((ggCoxeterMatrixD m).reindex e').simple (e' i)) := by
  show e (((ggCoxeterMatrixD m).reindexGroupEquiv e').symm
      ((ggCoxeterMatrixD m).simple i)) = e (((ggCoxeterMatrixD m).reindex e').simple (e' i))
  rw [CoxeterMatrix.reindexGroupEquiv_symm_apply_simple]

theorem ggQTwoDFrame_shape {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) {m : ℕ} (hm : 4 ≤ m)
    {ι : Type} (e' : Fin m ≃ ι)
    {e : ((ggCoxeterMatrixD m).reindex e').Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres 3 (ggAutomizerJoin L Bs 𝒦) ((ggCoxeterMatrixD m).reindex e') e)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V] (ι' : Additive ↥Bs ≃+ V) :
    ∃ (h : Fin m → V) (f : Fin m → Module.Dual (ZMod 3) V),
      (∀ i j, f i (h j) = ((CartanMatrix.D m i j : ℤ) : ZMod 3)) ∧
      ∀ (i : Fin m) (v : V),
        ggLin (p := 3) ι' ((qtwoE0 e' e ((ggCoxeterMatrixD m).simple i) :
          ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) v = v - f i v • h i := by
  classical
  haveI : Fintype ι := Fintype.ofEquiv (Fin m) e'
  obtain ⟨h, f, hpair, hform⟩ :=
    ggRefl_shape (p := 3) (by decide) hpres.1 (reindexD_M_le_three e') hpres.2
      (ggNoTransvection_of_le_automizer (ggRouteCfg_noTransvection hcfg)
        (ggAutomizerJoin_le_top L Bs 𝒦))
      (hC := (ggIntCartan_D m).reindex e') ι'
  refine ⟨fun i => h (e' i), fun i => f (e' i), ?_, ?_⟩
  · intro i j
    have hh := hpair (e' i) (e' j)
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply] at hh
    exact hh
  · intro i v
    rw [qtwoE0_simple e' e i]
    exact hform (e' i) v

theorem qtwo_intertwine_of_simple {m : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (Φ₁ : (ggCoxeterMatrixD m).Group →* (V ≃ₗ[ZMod 3] V))
    (Φ₂ : (ggCoxeterMatrixD m).Group →* (DVec m ≃ₗ[ZMod 3] DVec m))
    (Θ : DVec m ≃ₗ[ZMod 3] V)
    (hsimple : ∀ (i : Fin m) (v : DVec m),
      Φ₁ ((ggCoxeterMatrixD m).simple i) (Θ v) = Θ (Φ₂ ((ggCoxeterMatrixD m).simple i) v)) :
    ∀ (w : (ggCoxeterMatrixD m).Group) (v : DVec m), Φ₁ w (Θ v) = Θ (Φ₂ w v) := by
  intro w
  refine (ggCoxeterMatrixD m).toCoxeterSystem.simple_induction_left
    (p := fun w => ∀ v : DVec m, Φ₁ w (Θ v) = Θ (Φ₂ w v)) w ?_ ?_
  · intro v
    simp
  · intro w i ih v
    calc Φ₁ ((ggCoxeterMatrixD m).toCoxeterSystem.simple i * w) (Θ v)
        = (Φ₁ ((ggCoxeterMatrixD m).toCoxeterSystem.simple i) * Φ₁ w) (Θ v) := by
          rw [map_mul]
      _ = Φ₁ ((ggCoxeterMatrixD m).toCoxeterSystem.simple i) (Φ₁ w (Θ v)) := by
          rw [LinearEquiv.mul_apply]
      _ = Φ₁ ((ggCoxeterMatrixD m).toCoxeterSystem.simple i) (Θ (Φ₂ w v)) := by rw [ih v]
      _ = Θ (Φ₂ ((ggCoxeterMatrixD m).toCoxeterSystem.simple i) (Φ₂ w v)) :=
          hsimple i (Φ₂ w v)
      _ = Θ ((Φ₂ ((ggCoxeterMatrixD m).toCoxeterSystem.simple i) * Φ₂ w) v) := by
          rw [LinearEquiv.mul_apply]
      _ = Θ (Φ₂ ((ggCoxeterMatrixD m).toCoxeterSystem.simple i * w) v) := by rw [map_mul]

theorem ggQTwoDFrame_ker_eq_zero {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} {m : ℕ} {ι : Type} (e' : Fin m ≃ ι)
    {e : ((ggCoxeterMatrixD m).reindex e').Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] (ι' : Additive ↥Bs ≃+ V)
    (h : Fin m → V) (f : Fin m → Module.Dual (ZMod 3) V)
    (hh : ∀ (i : Fin m) (v : V),
      ggLin (p := 3) ι' ((qtwoE0 e' e ((ggCoxeterMatrixD m).simple i) :
        ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) v = v - f i v • h i)
    (hfix : ∀ b : ↥Bs, (∀ φ ∈ ggAutomizerJoin L Bs 𝒦, φ b = b) → b = 1) :
    ∀ v : V, (∀ i, f i v = 0) → v = 0 := by
  intro v hv
  let Φ : (ggCoxeterMatrixD m).Group →* (V ≃ₗ[ZMod 3] V) :=
    (ggLin (p := 3) ι').comp
      ((ggAutomizerJoin L Bs 𝒦).subtype.comp (qtwoE0 e' e).toMonoidHom)
  have hΦsimple : ∀ i : Fin m, Φ ((ggCoxeterMatrixD m).simple i) v = v := by
    intro i
    have hh' := hh i v
    rw [hv i, zero_smul, sub_zero] at hh'
    exact hh'
  have hgen : ∀ w : (ggCoxeterMatrixD m).Group, Φ w v = v := by
    intro w
    refine (ggCoxeterMatrixD m).toCoxeterSystem.simple_induction_left
      (p := fun w => Φ w v = v) w ?_ ?_
    · rw [map_one]; rfl
    · intro w i ih
      rw [map_mul, LinearEquiv.mul_apply, ih]
      exact hΦsimple i
  have hfixv : ∀ φ ∈ ggAutomizerJoin L Bs 𝒦,
      φ (Additive.toMul (ι'.symm v)) = Additive.toMul (ι'.symm v) := by
    intro φ hφ
    set w : (ggCoxeterMatrixD m).Group := (qtwoE0 e' e).symm ⟨φ, hφ⟩ with hw
    have hw' : (qtwoE0 e' e w : ↥(ggAutomizerJoin L Bs 𝒦)) = ⟨φ, hφ⟩ := by
      rw [hw]; exact (qtwoE0 e' e).apply_symm_apply ⟨φ, hφ⟩
    have hcoe : ((qtwoE0 e' e w : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) = φ := by
      rw [hw']
    rw [← hcoe]
    refine (ggLin_fix_iff (p := 3) ι'
      ((qtwoE0 e' e w : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)
      (Additive.toMul (ι'.symm v))).2 ?_
    rw [show ι' (Additive.ofMul (Additive.toMul (ι'.symm v))) = v from by
      rw [ofMul_toMul, AddEquiv.apply_symm_apply]]
    exact hgen w
  have hb : Additive.toMul (ι'.symm v) = 1 := hfix _ hfixv
  have hv0 : v = 0 := by
    have h := congrArg (fun b : ↥Bs => ι' (Additive.ofMul b)) hb
    rw [ofMul_toMul, AddEquiv.apply_symm_apply, ofMul_one, map_zero] at h
    exact h
  exact hv0

theorem ggQTwoDFrame_module {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) {m : ℕ} (hm : 4 ≤ m)
    {ι : Type} (e' : Fin m ≃ ι)
    {e : ((ggCoxeterMatrixD m).reindex e').Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres 3 (ggAutomizerJoin L Bs 𝒦) ((ggCoxeterMatrixD m).reindex e') e)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V] (ι' : Additive ↥Bs ≃+ V)
    (hfix : ∀ b : ↥Bs, (∀ φ ∈ ggAutomizerJoin L Bs 𝒦, φ b = b) → b = 1) :
    ∃ (Θ : DVec m ≃ₗ[ZMod 3] V) (ϑ : (ggCoxeterMatrixD m).Group ≃* dEven m), IsDEquiv m ϑ ∧
      ∀ (w : (ggCoxeterMatrixD m).Group) (v : DVec m),
        ggLin (p := 3) ι' ((qtwoE0 e' e w : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) (Θ v) =
          Θ (((ϑ w : dEven m) : DVec m ≃ₗ[ZMod 3] DVec m) v) := by
  classical
  obtain ⟨h, f, hpair, hform⟩ := ggQTwoDFrame_shape hcfg hm e' hpres ι'
  obtain ⟨ϑ, hϑ⟩ := dEven_equiv hm
  have hker : ∀ v : V, (∀ i, f i v = 0) → v = 0 :=
    ggQTwoDFrame_ker_eq_zero (B := B) (x := x) (D := D) (J := J) (e := e) e' ι' h f hform hfix
  have hker' : ∀ v : DVec m, (∀ i, dRootForm m i v = 0) → v = 0 :=
    eq_zero_of_dRootForm_eq_zero m hm
  have hpair' : ∀ i j, f i (h j) = dRootForm m i (dRoot m j) := by
    intro i j
    rw [hpair i j, dRootForm_dRoot m hm i j]
  obtain ⟨Θ, -, hΘrefl⟩ := ggQTwoDFrame_rigid h f (dRoot m) (dRootForm m) hpair'
    (dRoot_linearIndependent m hm) hker hker'
  let Φ₁ : (ggCoxeterMatrixD m).Group →* (V ≃ₗ[ZMod 3] V) :=
    (ggLin (p := 3) ι').comp
      ((ggAutomizerJoin L Bs 𝒦).subtype.comp (qtwoE0 e' e).toMonoidHom)
  let Φ₂ : (ggCoxeterMatrixD m).Group →* (DVec m ≃ₗ[ZMod 3] DVec m) :=
    (dEven m).subtype.comp ϑ.toMonoidHom
  have hsimple : ∀ (i : Fin m) (v : DVec m),
      Φ₁ ((ggCoxeterMatrixD m).simple i) (Θ v) =
        Θ (Φ₂ ((ggCoxeterMatrixD m).simple i) v) := by
    intro i v
    show ggLin (p := 3) ι' (((qtwoE0 e' e ((ggCoxeterMatrixD m).simple i) :
        ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)) (Θ v) =
      Θ (((ϑ ((ggCoxeterMatrixD m).simple i) : dEven m) :
        DVec m ≃ₗ[ZMod 3] DVec m) v)
    rw [hform i (Θ v), hϑ i, dTau_simple_apply m hm i v, hΘrefl i v]
  refine ⟨Θ, ϑ, hϑ, ?_⟩
  intro w v
  exact qtwo_intertwine_of_simple Φ₁ Φ₂ Θ hsimple w v

end Module

end CFSG.StandardType.QTwo

end
