
module

public import CFSG.Monster.B.TwoA.Unitary.SemilinearBase
public import CFSG.Monster.B.TwoA.Unitary.TwentyAlg
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.AbsolutelyIrreducible
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.JacobsonDensity
public meta import CFSG.Monster.B.TwoA.Unitary.TwentyData
public import Certificates.Certificate3083
public import CFSG.Monster.B.TwoA.Unitary.TwentyAlgInputs
public import Certificates.Data.CFSGNative.MonsterB.Short
public import Certificates.Data.CFSGNative.Mathieu.M24
public import CFSG.Certificates.Kernel.AxisPlane.Orbit
public import Certificates.Data.Kernel.VisFrame.Gens
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
public import CFSG.Monster.B.TwoA.Unitary.Bridge
public import CFSG.Monster.B.TwoA.Unitary.ActionInputs

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Unitary

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.VisCert CFSG.Monster.SpinLattice
  CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA

attribute [local irreducible] decW u20RecRows u20Gens u20Words u20Basis

open scoped TensorProduct

theorem bW_self (x : Wv v0) : bW x x = 0 := by
  change QuadraticMap.polar qWv x x = 0
  rw [QuadraticMap.polar_self, two_smul, CharTwo.add_self_eq_zero]

theorem sigmaW_mem_sigmaPerp :
    sigmaW ∈ sigmaPerp := bW_self sigmaW

def sigmaP :
    sigmaPerp := ⟨sigmaW, sigmaW_mem_sigmaPerp⟩

def sigLine :
    Submodule (ZMod 2) sigmaPerp := Submodule.span (ZMod 2)
    {sigmaP}

abbrev W20 :
    Type := sigmaPerp ⧸ sigLine

theorem sigmaP_ne_zero :
    sigmaP ≠ 0 := fun h => sigmaW_ne_zero (congrArg Subtype.val h)

theorem finrank_sigLine :
    Module.finrank (ZMod 2) sigLine = 1 :=
  finrank_span_singleton sigmaP_ne_zero

theorem finrank_W20 :
    Module.finrank (ZMod 2) W20 = 20 := by
  have h := Submodule.finrank_quotient_add_finrank sigLine
  rw [finrank_sigLine, finrank_sigmaPerp] at h
  change Module.finrank (ZMod 2) (sigmaPerp ⧸ sigLine) = 20
  omega

theorem wAct_mem_sigmaPerp
    (u : Usig) {x : Wv v0} (hx : x ∈ sigmaPerp) :
    wAct v0 u x ∈ sigmaPerp := by
  change bW sigmaW (wAct v0 u x) = 0
  rw [← (mem_Usig.1 u.2 : wAct v0 u sigmaW = sigmaW), bW_wAct]
  exact hx

def perpEnd
    (u : Usig) : Module.End (ZMod 2) sigmaPerp :=
  (wAct v0 u).restrict fun _ hx => wAct_mem_sigmaPerp u hx

theorem perpEnd_apply
    (u : Usig) (x : sigmaPerp) : (perpEnd u x : Wv v0) = wAct v0 u
    x := rfl

theorem perpEnd_sigmaP
    (u : Usig) : perpEnd u sigmaP = sigmaP :=
  Subtype.ext ((perpEnd_apply u sigmaP).trans (mem_Usig.1 u.2))

theorem perpEnd_mul
    (u u' : Usig) : perpEnd (u * u') = perpEnd u' * perpEnd u :=
  LinearMap.ext fun x => Subtype.ext ((perpEnd_apply (u * u') x).trans
    (LinearMap.congr_fun (wAct_mul (u : Kstab v0) u') (x : Wv v0)))

theorem perpEnd_one :
    perpEnd 1 = 1 :=
  LinearMap.ext fun x => Subtype.ext ((perpEnd_apply 1 x).trans
    (LinearMap.congr_fun wAct_one (x : Wv v0)))

theorem sigLine_le_comap
    (u : Usig) : sigLine ≤ sigLine.comap (perpEnd u) := by
  rw [sigLine, Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Submodule.mem_comap,
    perpEnd_sigmaP]
  exact Submodule.mem_span_singleton_self _

def w20End
    (u : Usig) : Module.End (ZMod 2) W20 :=
  Submodule.mapQ sigLine sigLine (perpEnd u) (sigLine_le_comap u)

theorem w20End_mk
    (u : Usig) (x : sigmaPerp) :
    w20End u (Submodule.Quotient.mk x) = Submodule.Quotient.mk (perpEnd u x) := rfl

theorem w20End_mul
    (u u' : Usig) : w20End (u * u') = w20End u' * w20End u := by
  refine LinearMap.ext fun x => ?_
  induction x using Submodule.Quotient.induction_on with
  | H x => exact congrArg Submodule.Quotient.mk (LinearMap.congr_fun (perpEnd_mul u u') x)

theorem w20End_one :
    w20End 1 = 1 := by
  refine LinearMap.ext fun x => ?_
  induction x using Submodule.Quotient.induction_on with
  | H x => exact congrArg Submodule.Quotient.mk (LinearMap.congr_fun perpEnd_one x)

def rep20 :
    Representation (ZMod 2) Usig W20 where
  toFun u := w20End u⁻¹
  map_one' := (congrArg w20End inv_one).trans w20End_one
  map_mul' u u' := (congrArg w20End (_root_.mul_inv_rev u u')).trans (w20End_mul _ _)

theorem rep20_apply
    (u : Usig) : rep20 u = w20End u⁻¹ := rfl

theorem sigmaCls_eq_ellCls : sigmaCls = ellCls 12 + ellCls 14 := by
  rw [sigmaCls_eq_dec, show (20480 : ℕ) = (1 <<< ((12 : Fin 24) : ℕ)) ^^^
    (1 <<< ((14 : Fin 24) : ℕ)) from rfl, dec_xor, dec_one_shiftLeft, dec_one_shiftLeft]

theorem bW_sigmaW_decW
    (c : ℕ) :
    bW sigmaW (decW c) = (popc 24 (Native.actD 22 Native.quotientBasis c &&& gramRow 12) : ZMod 2) +
      (popc 24 (Native.actD 22 Native.quotientBasis c &&& gramRow 14) : ZMod 2) := by
  obtain ⟨hm, he⟩ := decW_eq_mk c
  rw [bW_comm, he, sigmaW, polarBilin_qW_mk]
  change bL (dec (Native.actD 22 Native.quotientBasis c)) sigmaCls = _
  rw [sigmaCls_eq_ellCls, map_add, bL_dec, bL_dec]
  rfl

theorem u20Basis_perp_check : ∀ t : Fin 20,
    (popc 24 (Native.actD 22 Native.quotientBasis u20Basis[(t : ℕ)]! &&& gramRow 12) : ZMod 2) +
      (popc 24 (Native.actD 22 Native.quotientBasis u20Basis[(t : ℕ)]! &&& gramRow 14) : ZMod 2) =
        0 := by
  decide +kernel

theorem u20Basis_mem
    (t : Fin 20) : decW u20Basis[(t : ℕ)]! ∈ sigmaPerp :=
  (bW_sigmaW_decW _).trans (u20Basis_perp_check t)

def q20P
    (t : Fin 20) : sigmaPerp := ⟨_, u20Basis_mem t⟩

def b20v
    (t : Fin 20) : W20 := Submodule.Quotient.mk (q20P t)

def u20Dual : Fin 20 → ℕ :=
  ![1, 2, 4, 8, 16, 32, 128, 256, 512, 1024, 6144, 8192, 16384, 32768, 65536, 131072, 262144,
    524288, 1048576, 2097152]

theorem u20Dual_check : ∀ s t : Fin 20,
    bvec 22 (u20Dual s) ⬝ᵥ bvec 22 u20Basis[(t : ℕ)]! = if s = t then 1 else 0 := by decide +kernel

theorem u20Dual_sigma : ∀ s : Fin 20, bvec 22 (u20Dual s) ⬝ᵥ bvec 22 6144 = 0 := by decide +kernel

def dualW (s : Fin 20) : Wv v0 →ₗ[ZMod 2] ZMod 2 :=
  ∑ r : Fin 22, bvec 22 (u20Dual s) r • qbWBasis.coord r

theorem dualW_decW (s : Fin 20) (c : ℕ) : dualW s (decW c) = bvec 22 (u20Dual s) ⬝ᵥ bvec 22 c := by
  rw [dualW, LinearMap.sum_apply, dotProduct]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [LinearMap.smul_apply, Module.Basis.coord_apply, decW_eq_equivFun, smul_eq_mul]
  congr 1
  have := congrFun (qbWBasis.equivFun.apply_symm_apply (bvec 22 c)) r
  rwa [Module.Basis.equivFun_apply] at this

theorem dualW_q20P
    (s t : Fin 20) : dualW s (q20P t : Wv v0) = if s = t then 1 else
    0 :=
  (dualW_decW s _).trans (u20Dual_check s t)

theorem dualW_sigmaP
    (s : Fin 20) : dualW s (sigmaP : Wv v0) = 0 := by
  change dualW s sigmaW = 0
  rw [sigmaW_eq_decW, dualW_decW, u20Dual_sigma]

theorem linearIndependent_of_dual {ι M : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup M]
    [Module (ZMod 2) M] (v : ι → M) (φ : ι → M →ₗ[ZMod 2] ZMod 2)
    (h : ∀ s t, φ s (v t) = if s = t then 1 else 0) : LinearIndependent (ZMod 2) v := by
  rw [Fintype.linearIndependent_iff]
  intro g hg s
  have := congrArg (φ s) hg
  simpa [map_sum, h] using this

theorem sigLine_le_ker
    (s : Fin 20) :
    sigLine ≤ LinearMap.ker ((dualW s).comp sigmaPerp.subtype) := by
  rw [sigLine, Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker]
  exact dualW_sigmaP s

def dualQ
    (s : Fin 20) : W20 →ₗ[ZMod 2] ZMod 2 :=
  sigLine.liftQ ((dualW s).comp sigmaPerp.subtype) (sigLine_le_ker s)

theorem dualQ_b20v
    (s t : Fin 20) : dualQ s (b20v t) = if s = t then 1 else 0 :=
  dualW_q20P s t

theorem linearIndependent_b20v :
    LinearIndependent (ZMod 2) b20v :=
  linearIndependent_of_dual b20v dualQ dualQ_b20v

def b20 :
    Module.Basis (Fin 20) (ZMod 2) W20 :=
  basisOfLinearIndependentOfCardEqFinrank linearIndependent_b20v
    (by rw [Fintype.card_fin, finrank_W20])

theorem b20_apply
    (t : Fin 20) : b20 t = b20v t :=
  congrFun (coe_basisOfLinearIndependentOfCardEqFinrank _ _) t

theorem decW_actD (d : ℕ) (rows : Array ℕ) (c : ℕ) :
    decW (Native.actD d rows c) =
      ∑ i ∈ Finset.range d, if c.testBit i then decW rows[i]! else 0 := by
  rw [Native.actD, xorHom_actGo decW decW_xor, decW_zero, zero_add]

def comb20
    (r : ℕ) : sigmaPerp := ∑ s : Fin 20, bvec 20 r s • q20P s

theorem coe_comb20
    (r : ℕ) : (comb20 r : Wv v0) = decW
    (Native.actD 20 u20Basis r) := by
  rw [comb20, decW_actD, Submodule.coe_sum,
    ← Fin.sum_univ_eq_sum_range (fun i => if r.testBit i then decW u20Basis[i]! else 0) 20]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Submodule.coe_smul, bvec_apply]
  split_ifs
  · rw [one_smul]
    rfl
  · rw [zero_smul]

theorem decB_b20
    (r : ℕ) : decB b20 r = Submodule.Quotient.mk (comb20 r) :=
  (Finset.sum_congr rfl fun t _ => (congrArg (bvec 20 r t • ·) (b20_apply t)).trans
    (map_smul sigLine.mkQ (bvec 20 r t) (q20P t)).symm).trans
    (map_sum sigLine.mkQ (fun t => bvec 20 r t • q20P t) Finset.univ).symm

theorem neg_W (x : Wv v0) : -x = x := by
  have h : x + x = 0 := by rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]
  exact neg_eq_of_add_eq_zero_right h

theorem mk_eq_of_xor
    {x : ℕ} {y : sigmaPerp} (hx : decW x ∈ sigmaPerp) {y' : ℕ}
    (hy : (y : Wv v0) = decW y') (h : x ^^^ y' = 0 ∨ x ^^^ y' = 6144) :
    (Submodule.Quotient.mk ⟨decW x, hx⟩ : W20) = Submodule.Quotient.mk y := by
  rw [Submodule.Quotient.eq]
  have hd : ((⟨decW x, hx⟩ - y : sigmaPerp) : Wv v0) = decW (x ^^^ y') := by
    rw [Submodule.coe_sub, hy, decW_xor, sub_eq_add_neg, neg_W]
  rcases h with h | h
  · have e : (⟨decW x, hx⟩ - y : sigmaPerp) = 0 :=
      Subtype.ext (by rw [hd, h, decW_zero]; rfl)
    rw [e]
    exact zero_mem _
  · have e : (⟨decW x, hx⟩ - y : sigmaPerp) = sigmaP :=
      Subtype.ext (by rw [hd, h, ← sigmaW_eq_decW]; rfl)
    rw [e]
    exact Submodule.mem_span_singleton_self _

theorem genRows20_ok : ∀ k : Fin 17, ∀ t : Fin 20,
    Native.actD 22 n6RowArr[(k : ℕ)]! u20Basis[(t : ℕ)]! ^^^
        Native.actD 20 u20Basis (u20Gens[(k : ℕ)]!)[(t : ℕ)]! = 0 ∨
      Native.actD 22 n6RowArr[(k : ℕ)]! u20Basis[(t : ℕ)]! ^^^
        Native.actD 20 u20Basis (u20Gens[(k : ℕ)]!)[(t : ℕ)]! = 6144 := by
  decide +kernel

theorem u20Words_lt : ∀ j < 400, ∀ k ∈ u20Words[j]!, k < 17 :=
  Certificates.certificate3083

theorem range_rep20 :
    Set.range rep20 = Set.range w20End := by
  ext f
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨u⁻¹, rfl⟩
  · rintro ⟨u, rfl⟩
    exact ⟨u⁻¹, congrArg w20End (inv_inv u)⟩

theorem b20_eq_mk
    (t : Fin 20) :
    ∃ h : decW u20Basis[(t : ℕ)]! ∈ sigmaPerp, b20 t = Submodule.Quotient.mk ⟨_, h⟩ :=
  ⟨u20Basis_mem t, b20_apply t⟩

instance finiteDimensional_W20 :
    FiniteDimensional (ZMod 2) W20 :=
  Module.finite_of_finrank_eq_succ finrank_W20

instance nontrivial_W20 :
    Nontrivial W20 := Module.nontrivial_of_finrank_eq_succ
    finrank_W20

end CFSG.Monster.B.TwoA.Unitary
