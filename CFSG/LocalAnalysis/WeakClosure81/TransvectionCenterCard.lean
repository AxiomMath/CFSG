module

public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenInputs
public import CFSG.CGT.Timmesfeld75.ListWCLinBasic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.Open.StatedAPI Matrix

variable {m : ℕ} {F : Type} [Field F]

noncomputable def transvectionCenterSL (a f : Fin m → F) (hf : f ⬝ᵥ a = 0) :
    ↥(StatedSL m F) :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (1 + vecMulVec a f)
      (by
        rw [CFSG.CGT.Timmesfeld75.det_one_add_vecMulVec_of_dot hf]
        exact one_ne_zero),
    mem_statedSL_of_det (by
      rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero,
        CFSG.CGT.Timmesfeld75.det_one_add_vecMulVec_of_dot hf])⟩

@[simp] theorem transvectionCenterSL_coe (a f : Fin m → F) (hf : f ⬝ᵥ a = 0) :
    (((transvectionCenterSL a f hf : ↥(StatedSL m F)) : GL (Fin m) F) :
      Matrix (Fin m) (Fin m) F) = 1 + vecMulVec a f := by
  simp [transvectionCenterSL]

noncomputable def transvectionCenterPoint (a f : Fin m → F) (hf : f ⬝ᵥ a = 0) :
    StatedProj (StatedSL m F) :=
  QuotientGroup.mk (transvectionCenterSL a f hf)

theorem transvectionCenterMatrix_mulVec (a f : Fin m → F) (hf : f ⬝ᵥ a = 0) :
    (1 + vecMulVec a f : Matrix (Fin m) (Fin m) F) *ᵥ a = a := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul, hf,
    zero_smul, add_zero]

theorem ncard_transvectionCenterSet (m : ℕ) (F : Type) [Field F] [Finite F]
    (hm : 2 ≤ m) (a : Fin m → F) (ha : a ≠ 0) :
    (transvectionCenterSet m F a).ncard = Nat.card F ^ (m - 1) := by
  classical
  obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
  have hi' : a i ≠ 0 := by simpa using hi
  let H : Type := {f : Fin m → F // f ⬝ᵥ a = 0}
  let x : H → StatedProj (StatedSL m F) := fun f => transvectionCenterPoint a f.1 f.2
  have hrange : Set.range x = transvectionCenterSet m F a := by
    ext y
    constructor
    · rintro ⟨f, rfl⟩
      exact ⟨transvectionCenterSL a f.1 f.2, rfl, f.1, f.2,
        transvectionCenterSL_coe a f.1 f.2⟩
    · rintro ⟨g, hgy, f, hf, hg⟩
      refine ⟨⟨f, hf⟩, ?_⟩
      rw [← hgy]
      refine (statedProj_mk_eq_iff (StatedSL m F) (transvectionCenterSL a f hf) g).mpr
        ⟨1, ?_⟩
      rw [Units.val_one, one_smul, Matrix.mul_one, transvectionCenterSL_coe]
      exact hg
  have hinj : Function.Injective x := by
    rintro ⟨f, hf⟩ ⟨g, hg⟩ heq
    have heq' : (QuotientGroup.mk (transvectionCenterSL a f hf) :
        StatedProj (StatedSL m F)) =
        QuotientGroup.mk (transvectionCenterSL a g hg) := heq
    obtain ⟨u, hu⟩ := (statedProj_mk_eq_iff (StatedSL m F)
      (transvectionCenterSL a f hf) (transvectionCenterSL a g hg)).mp heq'
    have hmat_g : (((transvectionCenterSL a g hg : ↥(StatedSL m F)) : GL (Fin m) F) :
        Matrix (Fin m) (Fin m) F) = 1 + vecMulVec a g :=
      transvectionCenterSL_coe a g hg
    have hmat_f : (((transvectionCenterSL a f hf : ↥(StatedSL m F)) : GL (Fin m) F) :
        Matrix (Fin m) (Fin m) F) = 1 + vecMulVec a f :=
      transvectionCenterSL_coe a f hf
    have hu' : (1 + vecMulVec a g : Matrix (Fin m) (Fin m) F) =
        (1 + vecMulVec a f) * ((u : F) • (1 : Matrix (Fin m) (Fin m) F)) := by
      rw [← hmat_g, hu, hmat_f]
    have hact_f := transvectionCenterMatrix_mulVec a f hf
    have hact_g := transvectionCenterMatrix_mulVec a g hg
    have hscal : (u : F) • a = a := by
      calc
        (u : F) • a = (u : F) • ((1 + vecMulVec a f : Matrix (Fin m) (Fin m) F) *ᵥ a) := by
          rw [hact_f]
        _ = ((u : F) • (1 + vecMulVec a f : Matrix (Fin m) (Fin m) F)) *ᵥ a :=
          (Matrix.smul_mulVec (u : F) (1 + vecMulVec a f : Matrix (Fin m) (Fin m) F) a).symm
        _ = ((1 + vecMulVec a f : Matrix (Fin m) (Fin m) F) *
              ((u : F) • (1 : Matrix (Fin m) (Fin m) F))) *ᵥ a := by
          rw [Matrix.mul_smul, Matrix.mul_one]
        _ = (1 + vecMulVec a g : Matrix (Fin m) (Fin m) F) *ᵥ a := by rw [← hu']
        _ = a := hact_g
    have hui : (u : F) * a i = a i := by
      have := congrFun hscal i
      simpa [Pi.smul_apply, smul_eq_mul] using this
    have hu1 : (u : F) = 1 := by
      refine mul_right_cancel₀ hi' ?_
      simpa using hui
    have hM : (1 + vecMulVec a g : Matrix (Fin m) (Fin m) F) = 1 + vecMulVec a f := by
      rw [← hmat_g, hu, hu1, hmat_f]
      simp
    have hvec : vecMulVec a g = vecMulVec a f := add_left_cancel hM
    have hfg : f = g := by
      funext j
      have h := congrFun (congrFun hvec i) j
      have h' : a i * g j = a i * f j := by simpa [Matrix.vecMulVec_apply] using h
      exact (mul_left_cancel₀ hi' h').symm
    exact Subtype.ext hfg
  have hcard : Nat.card H = Nat.card F ^ (m - 1) := by
    let L : Module.Dual F (Fin m → F) :=
      { toFun := fun f => f ⬝ᵥ a
        map_add' := fun f g => add_dotProduct f g a
        map_smul' := fun c f => smul_dotProduct c f a }
    have hL : L ≠ 0 := by
      intro h
      have h1 : L (Pi.single i 1) = a i := by
        simp [L, single_dotProduct]
      have h0 : L (Pi.single i 1) = 0 := by
        rw [h]
        rfl
      rw [h1] at h0
      exact hi' h0
    have hfin : Module.finrank F ↥(LinearMap.ker L) = m - 1 := by
      have hfd := Module.Dual.finrank_ker_add_one_of_ne_zero (f := L) hL
      rw [Module.finrank_fin_fun] at hfd
      omega
    haveI : Module.Finite F ↥(LinearMap.ker L) := inferInstance
    have hker : Nat.card ↥(LinearMap.ker L) = Nat.card F ^ (m - 1) := by
      rw [Module.natCard_eq_pow_finrank (K := F) (V := ↥(LinearMap.ker L)), hfin]
    have e : H ≃ ↥(LinearMap.ker L) :=
      Equiv.subtypeEquivRight (fun f => by
        change (f ⬝ᵥ a = 0) ↔ L f = 0
        rfl)
    rw [Nat.card_congr e, hker]
  rw [← hrange, Set.ncard_range_of_injective hinj, hcard]
