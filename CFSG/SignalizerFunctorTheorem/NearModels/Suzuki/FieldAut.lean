module

public import CFSG.LieType.BorelTits.Suzuki
public import CFSG.LieType.Ree.SuzukiOvoidWeyl
public import CFSG.LieType.Ree.SuzukiUnipotentStructure

public section

open scoped MatrixGroups

namespace CFSG.SignalizerFunctorTheorem.NearModels.Suzuki

open CFSG.Blueprint CFSG.LieType.Ree CFSG.ShultStronglyClosedTI

variable {a : ℕ} {K : Type} [Field K]

theorem map_suzukiS {L : Type} [Field L] {F : Type*} [FunLike F K L] [RingHomClass F K L] (f : F)
    (u v : K) : (suzukiS a u v).map f = suzukiS a (f u) (f v) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [suzukiS, suzukiN]

theorem map_suzukiD {L : Type} [Field L] {F : Type*} [FunLike F K L] [RingHomClass F K L] (f : F)
    (l : Kˣ) : (suzukiD a l).map f = suzukiD a (Units.map (f : K →* L) l) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [suzukiD]

theorem map_suzukiW {L : Type} [Field L] {F : Type*} [FunLike F K L] [RingHomClass F K L]
    (f : F) : (suzukiW K).map f = suzukiW L := by
  ext i j
  simp only [suzukiW, Matrix.map_apply, Matrix.of_apply]
  split_ifs <;> simp

theorem map_mem_suzukiGroup (σ : RingAut K) {g : GL (Fin 4) K} (hg : g ∈ suzukiGroup a K) :
    glFieldEquiv σ g ∈ suzukiGroup a K := by
  have h := CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a K
  rw [h] at hg ⊢
  rw [← map_glaSzGroup σ a]
  exact Subgroup.mem_map_of_mem (glFieldEquiv σ).toMonoidHom hg

@[expose] def szFieldEquiv (σ : RingAut K) : suzukiGroup a K ≃* suzukiGroup a K where
  toFun g := ⟨glFieldEquiv σ (g : GL (Fin 4) K), map_mem_suzukiGroup σ g.2⟩
  invFun g := ⟨glFieldEquiv σ.symm (g : GL (Fin 4) K), map_mem_suzukiGroup σ.symm g.2⟩
  left_inv g := Subtype.ext ((glFieldEquiv σ).symm_apply_apply (g : GL (Fin 4) K))
  right_inv g := Subtype.ext ((glFieldEquiv σ).apply_symm_apply (g : GL (Fin 4) K))
  map_mul' g h := Subtype.ext (map_mul (glFieldEquiv σ) (g : GL (Fin 4) K) h)

variable (a K) in
@[expose] def szFieldAut : RingAut K →* MulAut (suzukiGroup a K) where
  toFun σ := szFieldEquiv σ
  map_one' := MulEquiv.ext fun g => Subtype.ext (Units.ext (by ext i j; rfl))
  map_mul' σ τ := MulEquiv.ext fun g => Subtype.ext (Units.ext (by ext i j; rfl))

theorem coe_szFieldAut (σ : RingAut K) (g : suzukiGroup a K) :
    (((szFieldAut a K σ g : suzukiGroup a K) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map σ :=
  rfl

theorem szFieldAut_S (σ : RingAut K) (u v : K) :
    szFieldAut a K σ (suzukiSElt a K u v) = suzukiSElt a K (σ u) (σ v) := by
  refine suzukiSElt_ext ?_
  rw [coe_szFieldAut, coe_suzukiSElt, coe_suzukiSElt, map_suzukiS]

theorem szFieldAut_D (σ : RingAut K) (l : Kˣ) :
    szFieldAut a K σ (suzukiDElt a K l) = suzukiDElt a K (Units.map (σ : K →* K) l) := by
  refine suzukiSElt_ext ?_
  rw [coe_szFieldAut, coe_suzukiDElt, coe_suzukiDElt, map_suzukiD]

theorem szFieldAut_W (σ : RingAut K) :
    szFieldAut a K σ (suzukiWElt a K) = suzukiWElt a K := by
  refine suzukiSElt_ext ?_
  rw [coe_szFieldAut, coe_suzukiWElt, map_suzukiW]

theorem szFieldAut_injective :
    Function.Injective (szFieldAut a K) := by
  intro σ τ h
  refine RingEquiv.ext fun u => ?_
  have h1 := congrArg (fun f : MulAut (suzukiGroup a K) => f (suzukiSElt a K u 0)) h
  simp only [szFieldAut_S] at h1
  exact (suzukiSElt_inj.1 h1).1

end CFSG.SignalizerFunctorTheorem.NearModels.Suzuki
