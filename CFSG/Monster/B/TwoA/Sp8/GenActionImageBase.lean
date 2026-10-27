
module

public import CFSG.Monster.B.TwoA.Sp8.GenActionOrbitBase
public import CFSG.Monster.B.TwoA.Sp8.NormalizerDataBase
public import CFSG.Monster.B.TwoA.Co2Inv.KernelBase
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public meta import CFSG.Monster.B.TwoA.Sp8.GenActionOrbitBase
public import CFSG.Monster.B.TwoA.Sp8.GenActionHomBase
public import CFSG.Monster.B.TwoA.Sp8.LiftsInputs
public import CFSG.Monster.B.TwoA.Sp8.A8Inputs
public import CFSG.Monster.B.TwoA.Sp8.GenActionLiftsInputs
public import CFSG.Monster.B.TwoA.Sp8.GenActionDiffInputs
public import CFSG.Monster.B.TwoA.Sp8.GenActionConjInputs
public import CFSG.Monster.B.TwoA.Sp8.GenActionConjBase
public import CFSG.Monster.B.TwoA.Sp8.GenActionOrbitInputs
public import Certificates.Data.CFSGNative.MonsterB.Short
public import Certificates.Data.CFSGNative.Mathieu.M24
public import CFSG.Certificates.Kernel.AxisPlane.Orbit
public import Certificates.Data.Kernel.VisFrame.Gens
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
public import CFSG.Monster.B.TwoA.Co2Inv.ConjCertInputs
public import CFSG.Monster.B.TwoA.Co2Inv.FrameCertInputs
public import CFSG.Monster.B.TwoA.Co2Inv.SixCertInputs
public import CFSG.Monster.B.Rep4371.SmallFaithfulBase
public import CFSG.Monster.B.Gen.Max2AssemblyBase
public import CFSG.Monster.B.Gen.PacketGenerationBase
public import CFSG.Monster.B.Gen.EbarPairing
public import CFSG.Monster.B.Cbar.SimpleAux
public import CFSG.Monster.B.Rep4371.FaithfulImageInputs
public import CFSG.Monster.B.TwoA.Base.WCls
public import CFSG.Monster.B.TwoA.Census.PermBFS
public import CFSG.Monster.B.TwoA.Co2Inv.Data
public import CFSG.Monster.B.TwoA.Co2Inv.RowsInputs
public import CFSG.Monster.B.TwoA.Sp8.A8Base
public import CFSG.Monster.B.TwoA.Co2Inv.SixActionBase
public import CFSG.Monster.B.TwoA.Base.Space34ABase
public import CFSG.Monster.B.TwoA.Sp8.PsiInputs
public import CFSG.Monster.B.TwoA.Base.PairSpace
public import CFSG.Monster.B.TwoA.Base.Space34AInputs
public import CFSG.Monster.B.TwoA.Co2Inv.KerDataBase
public import CFSG.Monster.B.TwoA.Co2Inv.KerFixBase

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.B CFSG.Monster.B.Short CFSG.Monster.B.TwoA
  CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA.Co2Inv

@[expose] def b0GramInvRows : List ℕ := [194, 65, 56, 52, 44, 28, 3, 1]

@[expose] def b0GramInv : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  Matrix.of fun i j => bvec 8 (b0GramInvRows.getD i 0) j

theorem gram0_mul_inv : gram0 * b0GramInv = 1 := by decide +kernel

theorem gram0_det_ne_zero : gram0.det ≠ 0 := by
  intro h
  have := congrArg Matrix.det gram0_mul_inv
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

theorem b0_nondegenerate : b0.Nondegenerate :=
  Matrix.nondegenerate_toBilin'_iff.2 (Matrix.Nondegenerate.of_det_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero gram0_det_ne_zero))

theorem finrank_V8 : Module.finrank (ZMod 2) V8 = 2 * 4 := by
  rw [Module.finrank_fin_fun]

abbrev e0 : V8 := Pi.single 0 1

@[expose] def SpX : Subgroup (V8 ≃ₗ[ZMod 2] V8) :=
  TauCeti.BilinForm.isometryGroup b0 ⊓ MulAction.stabilizer (V8 ≃ₗ[ZMod 2] V8) e0

instance finite_GLV8 : Finite (V8 ≃ₗ[ZMod 2] V8) :=
  Finite.of_injective (fun f : V8 ≃ₗ[ZMod 2] V8 => (f : V8 → V8))
    fun _ _ h => LinearEquiv.ext (congrFun h)

theorem mem_SpX {f : V8 ≃ₗ[ZMod 2] V8} :
    f ∈ SpX ↔ f ∈ TauCeti.BilinForm.isometryGroup b0 ∧ f e0 = e0 := by
  rw [SpX, Subgroup.mem_inf, MulAction.mem_stabilizer_iff, LinearEquiv.smul_def]

theorem ncard_nonzero : {v : V8 | v ≠ 0}.ncard = 255 := by
  have h1 : {v : V8 | v ≠ 0} = Set.univ \ {0} := by
    ext v
    simp
  have h2 := Set.ncard_sdiff_singleton_add_one (Set.mem_univ (0 : V8))
  rw [Set.ncard_univ, Nat.card_fun, Nat.card_zmod, Nat.card_fin] at h2
  rw [h1]
  omega

theorem mem_stab_Sp {g : TauCeti.BilinForm.isometryGroup b0} :
    g ∈ MulAction.stabilizer (TauCeti.BilinForm.isometryGroup b0) e0 ↔
      (g : V8 ≃ₗ[ZMod 2] V8) e0 = e0 := by
  rw [MulAction.mem_stabilizer_iff, Submonoid.smul_def, LinearEquiv.smul_def]

theorem SpX_eq_map :
    SpX = (MulAction.stabilizer (TauCeti.BilinForm.isometryGroup b0) e0).map
      (TauCeti.BilinForm.isometryGroup b0).subtype := by
  ext f
  constructor
  · intro hf
    obtain ⟨h1, h2⟩ := mem_SpX.1 hf
    exact ⟨⟨f, h1⟩, mem_stab_Sp.2 h2, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact mem_SpX.2 ⟨g.2, mem_stab_Sp.1 hg⟩

theorem card_quot {a b c : ℕ} (h : a * b = c) (hb : b = 255) (hc : c = 47377612800) :
    a = 185794560 := by
  subst hb
  subst hc
  omega

theorem card_split {a b c d e f : ℕ} (h1 : a * b = c) (h2 : d * f = c) (h3 : a * e = d)
    (ha : 0 < a) : b = e * f :=
  Nat.eq_of_mul_eq_mul_left ha (by rw [h1, ← h2, ← h3, mul_assoc])

end CFSG.Monster.B.TwoA.Sp8
