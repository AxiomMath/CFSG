module

public import CFSG.LocalAnalysis.StandardType.GGResJUnitaryPairedBlock
public import CFSG.LocalAnalysis.StandardType.GGResF4ExactTwo

public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenCore
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenOver
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerLinearNsFrame
public import CFSG.LocalAnalysis.StandardType.GGResILineInputs
public import CFSG.LocalAnalysis.StandardType.GGResIPumpLineTransfer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAReciprocalFusion
public import CFSG.Adapters.SpecialLinearPerfect
public import CFSG.GroupTheory.ConjKerCenter
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.LocalAnalysis.StandardType.GGTableBLinTwoTvFrame
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeALift
public import CFSG.LinearAlgebra.LinearGroups.SLConjugationKer
public import CFSG.LinearAlgebra.MatrixPlanes
public import CFSG.LocalAnalysis.StandardType.GGKGForkLinNsB
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUSigned
public import CFSG.LocalAnalysis.StandardType.GGSignedPermCount
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerLinearNonsplit
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27QuotientIndex
public import CFSG.RankThree.PartTwo.KFacts.K72L3Linear
public import CFSG.RankThree.PartTwo.KFacts.K72SylowL3
public import CFSG.RankThree.PartTwo.KFacts.K72Centralizer
public import CFSG.RankThree.PartTwo.KFacts.K72List
public import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeLeviSmall
public import CFSG.GroupTheory.AbelianPAutomizer
public import CFSG.Adapters.CatalogueFieldBridges.Linear
public import CFSG.LocalAnalysis.StandardType.GGAssemblyThreeHypSix
public import CFSG.RankThree.PartTwo.Sec4.RonanEpsCube
public import CFSG.RankThree.PartTwo.Sec11.Omega
public import CFSG.LocalAnalysis.ComponentClassification.OddSelector
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63Q2ProofOne
public import CFSG.LocalAnalysis.StandardType.GGF4AutWeyl
public import CFSG.LocalAnalysis.StandardType.GGResJUnitaryCubicBlock
public import CFSG.Open.StatedDefs
public import CFSG.Alternating.Multipliers.Main
public import CFSG.OddTranspositions.PartThree.Twelve.TenFiveMultRows
public import CFSG.LocalAnalysis.StandardType.AlternatingEightNormalizerAction
public import CFSG.CGT.PushingUpLit.CGT6.SixFourA8
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.LThreeEpsMat
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.I1435Chev.Exc
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.CrossPSU
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureThree.LieCrossPSU
public import CFSG.RankThree.PartTwo.Sec4.Item41NarrowGriess
public import CFSG.RankThree.PartTwo.Sec4.RonanEpsCfgForward
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowsS

public section

namespace CFSG.StandardType
namespace ResJPairedBlock

open Polynomial Module Matrix
open CFSG.Assembly
open Multiplicative
open SpCoord

theorem galExp_neg_one {K : Type} [Field K] [Finite K] [CharP K 2]
    (g : K[X]) [Fact (Irreducible g)] (_hgd : g ∣ cyclotomic 3 K)
    (hpK : ¬ 3 ∣ Nat.card K - 1) (hζ : AdjoinRoot.root g ^ 3 = 1) :
    ((-1 : (ZMod 3)ˣ) ∈ CoordSL.galExp g hζ) := by
  have hne : CoordSL.galExp g hζ ≠ ⊥ :=
    galExp_ne_bot Nat.prime_three
      (OrdPNS.natCast_ne_zero_of_charTwo Nat.prime_three (by norm_num)) hpK g hζ
  have hcard2 : Nat.card ((ZMod 3)ˣ) = 2 := by
    rw [Nat.card_units, Nat.card_zmod]
  have hdvd : Nat.card (CoordSL.galExp g hζ) ∣ Nat.card ((ZMod 3)ˣ) :=
    Subgroup.card_subgroup_dvd_card _
  rw [hcard2] at hdvd
  have hne1 : Nat.card (CoordSL.galExp g hζ) ≠ 1 := by
    intro h1
    exact hne (Subgroup.eq_bot_of_card_eq _ h1)
  have hcard : Nat.card (CoordSL.galExp g hζ) = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd h hne1
    · exact h
  have htop : CoordSL.galExp g hζ = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (by rw [hcard, hcard2])
  rw [htop]
  exact Subgroup.mem_top _

def flipSign {s : ℕ} (i : Fin s) : Fin s → (ZMod 3)ˣ :=
  fun j => if j = i then -1 else 1

@[simp] theorem flipSign_self {s : ℕ} (i : Fin s) : flipSign i i = -1 := by
  simp [flipSign]

@[simp] theorem flipSign_of_ne {s : ℕ} {i j : Fin s} (h : j ≠ i) : flipSign i j = 1 := by
  simp [flipSign, h]

theorem flipSign_mul_self {s : ℕ} (i : Fin s) : flipSign i * flipSign i = 1 := by
  funext j
  by_cases h : j = i <;> simp [flipSign, h]

theorem neg_one_ne_one_zmod3 : (-1 : ZMod 3) ≠ 1 := by decide

section Model

variable {G : Type} [Group G] [Finite G]
  {K : Type} [Field K] [Finite K] [CharP K 2]
  {n : ℕ} {φ : Matrix.SpecialLinearGroup (Fin n) K →* G}
  {Bs J : Subgroup G}
  {g : K[X]} [Fact (Irreducible g)]
  {s r : ℕ} {ε : Fin n ≃ (Fin (CoordSL.rootPB g).dim × Fin s) ⊕ Fin r}
  {A₀ : Matrix.SpecialLinearGroup (Fin n) K}
  (hC : (CoordSL.rootMat g).det = 1) (hCp : CoordSL.rootMat g ^ 3 = 1)

omit [Finite G] in
theorem exists_flip
    (hJ : φ.range = J)
    (hgd : g ∣ cyclotomic 3 K) (hpK : ¬ 3 ∣ Nat.card K - 1)
    (hζ : AdjoinRoot.root g ^ 3 = 1)
    (hrange : (CoordSL.frameHom φ A₀ ε hC hCp).range = Bs) (i : Fin s) :
    ∃ w ∈ J, ∃ (hw : w ∈ Subgroup.normalizer (Bs : Set G)),
      (∀ t : Fin s → ZMod 3,
        w⁻¹ * CoordSL.frameHom φ A₀ ε hC hCp (ofAdd t) * w =
          CoordSL.frameHom φ A₀ ε hC hCp (ofAdd fun j => (flipSign i j : ZMod 3) * t j)) ∧
      ggConjAut Bs hw ∈ ggAutomizer J Bs := by
  have hη : ∀ j, flipSign i j ∈ CoordSL.galExp g hζ := by
    intro j
    by_cases h : j = i
    · subst h
      rw [flipSign_self]
      exact galExp_neg_one g hgd hpK hζ
    · rw [flipSign_of_ne h]
      exact (CoordSL.galExp g hζ).one_mem
  obtain ⟨w, hw, hwconj⟩ :=
    CoordSL.exists_move_mem (g := g) φ A₀ ε hC hCp hζ hrange (Equiv.refl (Fin s))
      (flipSign i) hη
  obtain ⟨hwJ, hwN⟩ := Subgroup.mem_inf.mp hw
  have hwJ' : w ∈ J := hJ ▸ hwJ
  refine ⟨w, hwJ', hwN, ?_, ggConjAut_mem_ggAutomizer hwJ' hwN⟩
  intro t
  simpa using hwconj t

variable (hBs : IsElemAbelian 3 Bs)
  (hSC : ∀ x ∈ Subgroup.centralizer (Bs : Set G), x ^ 3 = 1 → x ∈ Bs)

omit [Finite G] [Finite K] [CharP K 2] in
theorem ggConjAut_apply_frameHom
    (hrange : (CoordSL.frameHom φ A₀ ε hC hCp).range = Bs)
    {w : G} (hw : w ∈ Subgroup.normalizer (Bs : Set G))
    {η : Fin s → (ZMod 3)ˣ} (hη2 : ∀ j, η j * η j = 1)
    (hwconj : ∀ t : Fin s → ZMod 3,
      w⁻¹ * CoordSL.frameHom φ A₀ ε hC hCp (ofAdd t) * w =
        CoordSL.frameHom φ A₀ ε hC hCp (ofAdd fun j => (η j : ZMod 3) * t j))
    (t : Fin s → ZMod 3) :
    ggConjAut Bs hw
        ⟨CoordSL.frameHom φ A₀ ε hC hCp (ofAdd t), hrange ▸ ⟨ofAdd t, rfl⟩⟩ =
      ⟨CoordSL.frameHom φ A₀ ε hC hCp (ofAdd fun j => (η j : ZMod 3) * t j),
        hrange ▸ ⟨ofAdd _, rfl⟩⟩ := by
  apply Subtype.ext
  rw [ggConjAut_apply]
  have h1 := hwconj (fun j => (η j : ZMod 3) * t j)
  have h2 : (fun j => (η j : ZMod 3) * ((η j : ZMod 3) * t j)) = t := by
    funext j
    rw [← mul_assoc, ← Units.val_mul, hη2 j, Units.val_one, one_mul]
  rw [h2] at h1
  have h3 : CoordSL.frameHom φ A₀ ε hC hCp (ofAdd fun j => (η j : ZMod 3) * t j) =
      w * CoordSL.frameHom φ A₀ ε hC hCp (ofAdd t) * w⁻¹ := by
    rw [← h1]
    group
  exact h3.symm

omit [Finite G] [Finite K] [CharP K 2] in
theorem ext_frameHom
    (hrange : (CoordSL.frameHom φ A₀ ε hC hCp).range = Bs)
    {c d : MulAut ↥Bs}
    (h : ∀ t : Fin s → ZMod 3,
      c ⟨CoordSL.frameHom φ A₀ ε hC hCp (ofAdd t), hrange ▸ ⟨ofAdd t, rfl⟩⟩ =
        d ⟨CoordSL.frameHom φ A₀ ε hC hCp (ofAdd t), hrange ▸ ⟨ofAdd t, rfl⟩⟩) :
    c = d := by
  apply MulEquiv.ext
  intro x
  have hx : ((x : G)) ∈ (CoordSL.frameHom φ A₀ ε hC hCp).range := by
    rw [hrange]
    exact x.2
  obtain ⟨y, hy⟩ := hx
  let t := Multiplicative.toAdd y
  have hx' : x = ⟨CoordSL.frameHom φ A₀ ε hC hCp (ofAdd t), hrange ▸ ⟨ofAdd t, rfl⟩⟩ := by
    apply Subtype.ext
    exact hy.symm
  rw [hx']
  exact h t


end Model

namespace ActualA

open CFSG.Assembly Multiplicative

variable {G : Type} [Group G] [Finite G]
  {K : Type} [Field K] [Finite K] [CharP K 2]
  {n : ℕ} {Bs J : Subgroup G}
  {g : K[X]} [Fact (Irreducible g)]
  {s r : ℕ} {ε : Fin n ≃ (Fin (CoordSL.rootPB g).dim × Fin s) ⊕ Fin r}
  {A₀ : Matrix.SpecialLinearGroup (Fin n) K}

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

omit [Finite G] [Finite K] [CharP K 2] in
@[expose] noncomputable def psi (φ : Matrix.SpecialLinearGroup (Fin n) K →* ↥J) :
    Matrix.SpecialLinearGroup (Fin n) K →* MulAut ↥J :=
  (MulAut.conj : ↥J →* MulAut ↥J).comp φ

omit [Finite G] [Finite K] [CharP K 2] in
theorem psi_apply (φ : Matrix.SpecialLinearGroup (Fin n) K →* ↥J)
    (X : Matrix.SpecialLinearGroup (Fin n) K) :
    psi φ X = MulAut.conj (φ X) := rfl

theorem exists_center_mul_of_conj_eq {L : Type} [Group L] {x y : L}
    (h : MulAut.conj x = MulAut.conj y) : ∃ z ∈ Subgroup.center L, x = y * z := by
  refine ⟨y⁻¹ * x, ?_, by group⟩
  rw [Subgroup.mem_center_iff]
  intro l
  have h1 : MulAut.conj (y⁻¹ * x) = 1 := by
    rw [map_mul, map_inv, h, inv_mul_cancel]
  have h2 : y⁻¹ * x * l * (y⁻¹ * x)⁻¹ = l := by
    have h' : y⁻¹ * (x * l * x⁻¹) * y = l := by
      have := congrArg (fun f : MulAut L => f l) h1
      simpa [MulAut.conj_apply] using this
    calc y⁻¹ * x * l * (y⁻¹ * x)⁻¹ = y⁻¹ * (x * l * x⁻¹) * y := by group
      _ = l := h'
  have h3 : (y⁻¹ * x) * l = l * (y⁻¹ * x) := by
    calc (y⁻¹ * x) * l = (y⁻¹ * x) * l * (y⁻¹ * x)⁻¹ * (y⁻¹ * x) := by group
      _ = l * (y⁻¹ * x) := by rw [h2]
  exact h3.symm

theorem comm_mul_center {L : Type} [Group L] {a b za zb : L}
    (hza : za ∈ Subgroup.center L) (hzb : zb ∈ Subgroup.center L)
    (hab : a * b = b * a) : (a * za) * (b * zb) = (b * zb) * (a * za) := by
  have hz : za * zb = zb * za := (Subgroup.mem_center_iff.mp hza zb).symm
  have hza_b : za * b = b * za := (Subgroup.mem_center_iff.mp hza b).symm
  have hzb_a : zb * a = a * zb := (Subgroup.mem_center_iff.mp hzb a).symm
  calc (a * za) * (b * zb) = a * (za * b) * zb := by group
    _ = a * (b * za) * zb := by rw [hza_b]
    _ = (a * b) * (za * zb) := by group
    _ = (b * a) * (zb * za) := by rw [hab, hz]
    _ = b * (a * zb) * za := by group
    _ = b * (zb * a) * za := by rw [hzb_a]
    _ = (b * zb) * (a * za) := by group

section Frame

variable (hN : Bs ≤ Subgroup.normalizer (J : Set G))
  (φ : Matrix.SpecialLinearGroup (Fin n) K →* ↥J)
  (hC : (CoordSL.rootMat g).det = 1) (hCp : (CoordSL.rootMat g) ^ 3 = 1)
  (hζ : AdjoinRoot.root g ^ 3 = 1)

omit [Finite G] [Finite K] [CharP K 2] in
theorem frameHom_psi_apply (t : Fin s → ZMod 3) :
    CoordSL.frameHom (psi φ) A₀ ε hC hCp (ofAdd t) =
      MulAut.conj (φ (A₀ * SLNS.nsSL ε hC (fun i => (t i).val) * A₀⁻¹)) := by
  rw [CoordSL.frameHom_apply]
  rfl

omit [Finite G] [Finite K] [CharP K 2] in
private theorem frameHom_psi_comm (t u : Fin s → ZMod 3) :
    CoordSL.frameHom (psi φ) A₀ ε hC hCp (ofAdd t) *
        CoordSL.frameHom (psi φ) A₀ ε hC hCp (ofAdd u) =
      CoordSL.frameHom (psi φ) A₀ ε hC hCp (ofAdd u) *
        CoordSL.frameHom (psi φ) A₀ ε hC hCp (ofAdd t) := by
  calc CoordSL.frameHom (psi φ) A₀ ε hC hCp (ofAdd t) *
        CoordSL.frameHom (psi φ) A₀ ε hC hCp (ofAdd u)
      = CoordSL.frameHom (psi φ) A₀ ε hC hCp (ofAdd t * ofAdd u) :=
        (map_mul _ _ _).symm
    _ = CoordSL.frameHom (psi φ) A₀ ε hC hCp (ofAdd (t + u)) := by rw [ofAdd_add]
    _ = CoordSL.frameHom (psi φ) A₀ ε hC hCp (ofAdd (u + t)) := by rw [add_comm]
    _ = CoordSL.frameHom (psi φ) A₀ ε hC hCp (ofAdd u * ofAdd t) := by rw [ofAdd_add]
    _ = CoordSL.frameHom (psi φ) A₀ ε hC hCp (ofAdd u) *
        CoordSL.frameHom (psi φ) A₀ ε hC hCp (ofAdd t) := map_mul _ _ _

omit [Finite G] [Finite K] [CharP K 2] in
theorem isElemAbelian_gammaRange
    (hframeA : (CoordSL.frameHom (psi φ) A₀ ε hC hCp).range = (ggGamma J hN).range) :
    IsElemAbelian 3 (ggGamma J hN).range := by
  rw [← hframeA]
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
  · obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 a.2
    obtain ⟨z, hz⟩ := MonoidHom.mem_range.1 b.2
    apply Subtype.ext
    change (a : MulAut ↥J) * (b : MulAut ↥J) = (b : MulAut ↥J) * (a : MulAut ↥J)
    rw [← hx, ← hz, ← map_mul, ← map_mul, mul_comm]
  · obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hy
    rw [← map_pow]
    have hx3 : x ^ 3 = 1 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one]
      funext i
      simp only [Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul, Pi.zero_apply]
    rw [hx3, map_one]

omit [Finite G] [Finite K] [CharP K 2] in
theorem exists_conj_of_mem_gammaRange
    (hframeA : (CoordSL.frameHom (psi φ) A₀ ε hC hCp).range = (ggGamma J hN).range)
    {a : MulAut ↥J} (ha : a ∈ (ggGamma J hN).range) :
    ∃ x : ↥J, a = MulAut.conj x := by
  have ha' : a ∈ (CoordSL.frameHom (psi φ) A₀ ε hC hCp).range := by
    rw [hframeA]
    exact ha
  obtain ⟨t, ht⟩ := ha'
  let u : Fin s → ZMod 3 := Multiplicative.toAdd t
  refine ⟨φ (A₀ * SLNS.nsSL ε hC (fun i => (u i).val) * A₀⁻¹), ?_⟩
  rw [← ht]
  exact frameHom_psi_apply φ hC hCp u

omit [Finite G] [Finite K] [CharP K 2] in
theorem comm_of_conj_mem_gammaRange
    (hframeA : (CoordSL.frameHom (psi φ) A₀ ε hC hCp).range = (ggGamma J hN).range)
    {x y : ↥J}
    (hx : MulAut.conj x ∈ (ggGamma J hN).range)
    (hy : MulAut.conj y ∈ (ggGamma J hN).range) :
    x * y = y * x := by
  have hx' : MulAut.conj x ∈ (CoordSL.frameHom (psi φ) A₀ ε hC hCp).range := by
    rw [hframeA]; exact hx
  have hy' : MulAut.conj y ∈ (CoordSL.frameHom (psi φ) A₀ ε hC hCp).range := by
    rw [hframeA]; exact hy
  obtain ⟨tx, htx⟩ := hx'
  obtain ⟨ty, hty⟩ := hy'
  let ux : Fin s → ZMod 3 := Multiplicative.toAdd tx
  let uy : Fin s → ZMod 3 := Multiplicative.toAdd ty
  let Xx : Matrix.SpecialLinearGroup (Fin n) K :=
    A₀ * SLNS.nsSL ε hC (fun i => (ux i).val) * A₀⁻¹
  let Xy : Matrix.SpecialLinearGroup (Fin n) K :=
    A₀ * SLNS.nsSL ε hC (fun i => (uy i).val) * A₀⁻¹
  have hxconj : MulAut.conj x = MulAut.conj (φ Xx) := by
    rw [← htx]
    exact frameHom_psi_apply φ hC hCp ux
  have hyconj : MulAut.conj y = MulAut.conj (φ Xy) := by
    rw [← hty]
    exact frameHom_psi_apply φ hC hCp uy
  obtain ⟨zx, hzx, hxeq⟩ := exists_center_mul_of_conj_eq hxconj
  obtain ⟨zy, hzy, hyeq⟩ := exists_center_mul_of_conj_eq hyconj
  have hXY : Xx * Xy = Xy * Xx := by
    dsimp [Xx, Xy]
    calc A₀ * SLNS.nsSL ε hC (fun i => (ux i).val) * A₀⁻¹ *
          (A₀ * SLNS.nsSL ε hC (fun i => (uy i).val) * A₀⁻¹)
        = A₀ * (SLNS.nsSL ε hC (fun i => (ux i).val) *
            SLNS.nsSL ε hC (fun i => (uy i).val)) * A₀⁻¹ := by group
      _ = A₀ * (SLNS.nsSL ε hC (fun i => (uy i).val) *
            SLNS.nsSL ε hC (fun i => (ux i).val)) * A₀⁻¹ := by
              rw [SLNS.nsSL_comm]
      _ = A₀ * SLNS.nsSL ε hC (fun i => (uy i).val) * A₀⁻¹ *
          (A₀ * SLNS.nsSL ε hC (fun i => (ux i).val) * A₀⁻¹) := by group
  have hphicomm : φ Xx * φ Xy = φ Xy * φ Xx := by
    rw [← map_mul, ← map_mul, hXY]
  rw [hxeq, hyeq]
  exact comm_mul_center hzx hzy hphicomm

omit [Finite G] [Finite K] [CharP K 2] in
theorem psi_ker_le_center
    (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K))
    (hperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin n) K)) :
    (psi φ).ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K) := by
  have hcomp : (psi φ).ker =
      (MulAut.conj : ↥J →* MulAut ↥J).ker.comap φ := by
    rw [psi]
    exact (MonoidHom.comap_ker (MulAut.conj : ↥J →* MulAut ↥J) φ).symm
  rw [hcomp, CFSG.GroupTheory.ker_conj_eq_center,
    CFSG.LocalCores.comap_center_eq_of_perfect hperf φ hφ hker]

theorem eq_of_conj_phi_eq
    (hφc : ∀ x, φ x ∈ Subgroup.center ↥J →
      x ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K))
    (hpK : ¬ 3 ∣ Nat.card K - 1)
    {a b : Matrix.SpecialLinearGroup (Fin n) K} (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (h : MulAut.conj (φ a) = MulAut.conj (φ b)) : a = b := by
  have hz : a * b⁻¹ ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K) := by
    refine hφc _ (Subgroup.mem_center_iff.mpr fun y => ?_)
    have h2 : MulAut.conj (φ (a * b⁻¹)) y = y := by
      rw [map_mul, map_inv, map_mul, map_inv, h, mul_inv_cancel]
      rfl
    rw [MulAut.conj_apply] at h2
    calc y * φ (a * b⁻¹) =
          φ (a * b⁻¹) * y * (φ (a * b⁻¹))⁻¹ * φ (a * b⁻¹) := by rw [h2]
      _ = φ (a * b⁻¹) * y := by group
  have hc : Commute a b⁻¹ := by
    have h1 := Subgroup.mem_center_iff.mp hz b
    calc a * b⁻¹ = b⁻¹ * (b * (a * b⁻¹)) := by group
      _ = b⁻¹ * (a * b⁻¹ * b) := by rw [h1]
      _ = b⁻¹ * a := by group
  have hzp : (a * b⁻¹) ^ 3 = 1 := by
    rw [hc.mul_pow, ha, inv_pow, hb, inv_one, one_mul]
  obtain ⟨c, -, hcz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  rw [← mul_inv_eq_one]
  ext i j
  have h1 := congrArg (fun y : Matrix.SpecialLinearGroup (Fin n) K =>
    ((Matrix.SpecialLinearGroup.toGL y : Matrix.GeneralLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) i i) hzp
  simp only [map_pow, map_one, Units.val_pow_eq_pow_val, Units.val_one, one_apply_eq] at h1
  have h3 : ((Matrix.SpecialLinearGroup.toGL (a * b⁻¹) :
      Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      scalar (Fin n) c := hcz.symm
  rw [h3, ← map_pow, scalar_apply, diagonal_apply_eq] at h1
  rw [← hcz, OrdPNS.eq_one_of_pow_eq_one Nat.prime_three hpK h1, map_one]
  rfl

theorem isPerfect_SL_of_frame
    (ε' : Fin n ≃ (Fin (CoordSL.rootPB g).dim × Fin s) ⊕ Fin r)
    (hgd : g ∣ cyclotomic 3 K) (hpK : ¬ 3 ∣ Nat.card K - 1) (hs : 2 ≤ s) :
    Group.IsPerfect (Matrix.SpecialLinearGroup (Fin n) K) := by
  have hcard : n = (CoordSL.rootPB g).dim * s + r := by
    simpa using Fintype.card_congr ε'
  have hpK' : (3 : K) ≠ 0 := by
    intro h
    have h' : (2 : ℕ) ∣ 3 := (CharP.cast_eq_zero_iff K 2 3).mp h
    norm_num at h'
  have he : 2 ≤ (CoordSL.rootPB g).dim :=
    LinTwoTv.two_le_rootPB_dim (g := g) (fun c =>
      CoordSL.isUnit_rootMat_pow_sub Nat.prime_three hpK hpK' hgd 1 (by decide) c)
  have hes : 2 * 2 ≤ (CoordSL.rootPB g).dim * s := Nat.mul_le_mul he hs
  have hn3 : 3 ≤ n := by
    rw [hcard]
    exact le_trans (by norm_num) (le_trans hes (Nat.le_add_right _ _))
  exact CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (K := K) hn3

omit [Finite G] in
theorem frameHom_psi_injective
    (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K))
    (hgd : g ∣ cyclotomic 3 K) (hpK : ¬ 3 ∣ Nat.card K - 1)
    (hs : 2 ≤ s) :
    Function.Injective (CoordSL.frameHom (psi φ) A₀ ε hC hCp) := by
  have hperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin n) K) :=
    isPerfect_SL_of_frame (ε' := ε) hgd hpK hs
  have hkerPsi : (psi φ).ker ≤
      Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K) :=
    psi_ker_le_center (φ := φ) hφ hker hperf
  have hpK' : (3 : K) ≠ 0 := by
    intro h
    have h' : (2 : ℕ) ∣ 3 := (CharP.cast_eq_zero_iff K 2 3).mp h
    norm_num at h'
  exact CoordSL.frameHom_injective (ψ := psi φ) (A₀ := A₀) (ε := ε)
    (C := CoordSL.rootMat g) (hC := hC) (p := 3) hCp hkerPsi
    (CoordSL.rootPB_dim_pos g)
    (CoordSL.isUnit_rootMat_pow_sub Nat.prime_three hpK hpK' hgd)

end Frame

section Flips

variable (hN : Bs ≤ Subgroup.normalizer (J : Set G))
  (φ : Matrix.SpecialLinearGroup (Fin n) K →* ↥J)
  (hC : (CoordSL.rootMat g).det = 1) (hCp : (CoordSL.rootMat g) ^ 3 = 1)

omit [Finite G] in
private theorem exists_flip_at_A
    (hframeA : (CoordSL.frameHom (psi φ) A₀ ε hC hCp).range = (ggGamma J hN).range)
    (hgd : g ∣ cyclotomic 3 K) (hpK : ¬ 3 ∣ Nat.card K - 1)
    (hζ : AdjoinRoot.root g ^ 3 = 1) (i : Fin s) :
    ∃ (w : ↥J)
      (_hn : MulAut.conj w ∈
        Subgroup.normalizer ((ggGamma J hN).range : Set (MulAut ↥J))),
      GGTorusWeylElt 3 ((ggGamma J hN).range) w ∧
      (∀ t : Fin s → ZMod 3,
        (MulAut.conj w)⁻¹ * CoordSL.frameHom (psi φ) A₀ ε hC hCp (ofAdd t) *
            (MulAut.conj w) =
          CoordSL.frameHom (psi φ) A₀ ε hC hCp
            (ofAdd fun j => (flipSign i j : ZMod 3) * t j)) := by
  have hη : ∀ j, flipSign i j ∈ CoordSL.galExp g hζ := by
    intro j
    by_cases h : j = i
    · subst h
      rw [flipSign_self]
      exact galExp_neg_one g hgd hpK hζ
    · rw [flipSign_of_ne h]
      exact (CoordSL.galExp g hζ).one_mem
  obtain ⟨v, hv, hvconj⟩ :=
    CoordSL.exists_move_mem (g := g) (ψ := psi φ) A₀ ε hC hCp hζ hframeA
      (Equiv.refl (Fin s)) (flipSign i) hη
  obtain ⟨hvrange, hvN⟩ := Subgroup.mem_inf.mp hv
  obtain ⟨W, hW⟩ := hvrange
  let w : ↥J := φ W
  have hv_eq : v = MulAut.conj w := by rw [← hW]; rfl
  have hn : MulAut.conj w ∈
      Subgroup.normalizer ((ggGamma J hN).range : Set (MulAut ↥J)) := by
    rwa [← hv_eq]
  refine ⟨w, hn, ?_, ?_⟩
  · exact ggTorusWeylElt_of_conj_mem_normalizer
      (isElemAbelian_gammaRange hN φ hC hCp hframeA)
      (fun a ha => exists_conj_of_mem_gammaRange hN φ hC hCp hframeA ha)
      (fun x y hx hy => comm_of_conj_mem_gammaRange hN φ hC hCp hframeA hx hy) hn
  · intro t
    rw [← hv_eq]
    simpa using hvconj t

private theorem exists_kleinFour_weylAut_at_A
    (hframeA : (CoordSL.frameHom (psi φ) A₀ ε hC hCp).range = (ggGamma J hN).range)
    (hgd : g ∣ cyclotomic 3 K) (hpK : ¬ 3 ∣ Nat.card K - 1)
    (hζ : AdjoinRoot.root g ^ 3 = 1)
    (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K))
    (hs : 2 ≤ s) :
    ∃ a0 a1 : MulAut ↥((ggGamma J hN).range),
      a0 ∈ ggTorusWeylAut 3 ((ggGamma J hN).range) ∧
      a1 ∈ ggTorusWeylAut 3 ((ggGamma J hN).range) ∧
      a0 * a0 = 1 ∧ a1 * a1 = 1 ∧ a0 * a1 = a1 * a0 ∧
      a0 ≠ 1 ∧ a1 ≠ 1 ∧ a0 ≠ a1 ∧
      Nat.card (Subgroup.closure ({a0, a1} :
        Set (MulAut ↥((ggGamma J hN).range)))) = 4 := by
  have hinj : Function.Injective (CoordSL.frameHom (psi φ) A₀ ε hC hCp) :=
    frameHom_psi_injective (φ := φ) (hC := hC) (hCp := hCp) (A₀ := A₀) (ε := ε)
      hφ hker hgd hpK hs
  let i0 : Fin s := ⟨0, by omega⟩
  let i1 : Fin s := ⟨1, by omega⟩
  have hi01 : i0 ≠ i1 := by
    intro h
    have h' := congrArg Fin.val h
    simp [i0, i1] at h'
  obtain ⟨w0, hn0, hW0, hconj0⟩ :=
    exists_flip_at_A (hN := hN) (φ := φ) (hC := hC) (hCp := hCp)
      (hframeA := hframeA) (hgd := hgd) (hpK := hpK) (hζ := hζ) i0
  obtain ⟨w1, hn1, hW1, hconj1⟩ :=
    exists_flip_at_A (hN := hN) (φ := φ) (hC := hC) (hCp := hCp)
      (hframeA := hframeA) (hgd := hgd) (hpK := hpK) (hζ := hζ) i1
  let a0 : MulAut ↥((ggGamma J hN).range) := ggConjAut _ hn0
  let a1 : MulAut ↥((ggGamma J hN).range) := ggConjAut _ hn1
  have hA0 : a0 ∈ ggTorusWeylAut 3 ((ggGamma J hN).range) := ⟨w0, hn0, hW0, rfl⟩
  have hA1 : a1 ∈ ggTorusWeylAut 3 ((ggGamma J hN).range) := ⟨w1, hn1, hW1, rfl⟩
  have ha0_apply : ∀ t : Fin s → ZMod 3,
      a0 ⟨CoordSL.frameHom (psi φ) A₀ ε hC hCp (ofAdd t),
        hframeA ▸ ⟨ofAdd t, rfl⟩⟩ =
        ⟨CoordSL.frameHom (psi φ) A₀ ε hC hCp
          (ofAdd fun j => (flipSign i0 j : ZMod 3) * t j),
          hframeA ▸ ⟨ofAdd _, rfl⟩⟩ :=
    fun t => ggConjAut_apply_frameHom (hC := hC) (hCp := hCp) hframeA hn0
      (fun j => congrFun (flipSign_mul_self i0) j) hconj0 t
  have ha1_apply : ∀ t : Fin s → ZMod 3,
      a1 ⟨CoordSL.frameHom (psi φ) A₀ ε hC hCp (ofAdd t),
        hframeA ▸ ⟨ofAdd t, rfl⟩⟩ =
        ⟨CoordSL.frameHom (psi φ) A₀ ε hC hCp
          (ofAdd fun j => (flipSign i1 j : ZMod 3) * t j),
          hframeA ▸ ⟨ofAdd _, rfl⟩⟩ :=
    fun t => ggConjAut_apply_frameHom (hC := hC) (hCp := hCp) hframeA hn1
      (fun j => congrFun (flipSign_mul_self i1) j) hconj1 t
  have ha0_sq : a0 * a0 = 1 := by
    apply ext_frameHom (hC := hC) (hCp := hCp) hframeA
    intro t
    simp only [MulAut.mul_apply, MulAut.one_apply]
    rw [ha0_apply, ha0_apply]
    have hfix : (fun j => (flipSign i0 j : ZMod 3) *
        ((flipSign i0 j : ZMod 3) * t j)) = t := by
      funext j
      have hsq : (↑(flipSign i0 j) : ZMod 3) * ↑(flipSign i0 j) = 1 := by
        by_cases hj : j = i0
        · subst hj; simp [flipSign_self]
        · rw [flipSign_of_ne hj]; simp
      rw [← mul_assoc, hsq, one_mul]
    rw [hfix]
  have ha1_sq : a1 * a1 = 1 := by
    apply ext_frameHom (hC := hC) (hCp := hCp) hframeA
    intro t
    simp only [MulAut.mul_apply, MulAut.one_apply]
    rw [ha1_apply, ha1_apply]
    have hfix : (fun j => (flipSign i1 j : ZMod 3) *
        ((flipSign i1 j : ZMod 3) * t j)) = t := by
      funext j
      have hsq : (↑(flipSign i1 j) : ZMod 3) * ↑(flipSign i1 j) = 1 := by
        by_cases hj : j = i1
        · subst hj; simp [flipSign_self]
        · rw [flipSign_of_ne hj]; simp
      rw [← mul_assoc, hsq, one_mul]
    rw [hfix]
  have ha_comm : a0 * a1 = a1 * a0 := by
    apply ext_frameHom (hC := hC) (hCp := hCp) hframeA
    intro t
    simp only [MulAut.mul_apply]
    rw [ha1_apply, ha0_apply, ha0_apply, ha1_apply]
    apply Subtype.ext
    dsimp only [Subtype.coe_mk]
    congr 1
    funext j
    change (flipSign i0 j : ZMod 3) * ((flipSign i1 j : ZMod 3) * t j) =
      (flipSign i1 j : ZMod 3) * ((flipSign i0 j : ZMod 3) * t j)
    ring
  let e0 : Fin s → ZMod 3 := Pi.single i0 1
  let e1 : Fin s → ZMod 3 := Pi.single i1 1
  let bElt : (Fin s → ZMod 3) → ↥((ggGamma J hN).range) := fun t =>
    ⟨CoordSL.frameHom (psi φ) A₀ ε hC hCp (ofAdd t), hframeA ▸ ⟨ofAdd t, rfl⟩⟩
  have hb_inj : Function.Injective bElt := by
    intro t u h
    have h' : CoordSL.frameHom (psi φ) A₀ ε hC hCp (ofAdd t) =
        CoordSL.frameHom (psi φ) A₀ ε hC hCp (ofAdd u) := congrArg Subtype.val h
    exact Multiplicative.ofAdd.injective (hinj h')
  have hframe_zero : bElt 0 = 1 := by
    apply Subtype.ext
    change CoordSL.frameHom (psi φ) A₀ ε hC hCp
      (1 : Multiplicative (Fin s → ZMod 3)) = 1
    exact map_one _
  have he0_ne_zero : e0 ≠ 0 := by
    intro h
    have h' := congrFun h i0
    simp [e0] at h'
  have he1_ne_zero : e1 ≠ 0 := by
    intro h
    have h' := congrFun h i1
    simp [e1] at h'
  have hb0_ne_one : bElt e0 ≠ 1 := by
    intro h
    exact he0_ne_zero (hb_inj (h.trans hframe_zero.symm))
  have hb1_ne_one : bElt e1 ≠ 1 := by
    intro h
    exact he1_ne_zero (hb_inj (h.trans hframe_zero.symm))
  have hne0 : (fun j => (flipSign i0 j : ZMod 3) * e0 j) ≠ e0 := by
    intro h
    have h' := congrFun h i0
    simp [flipSign_self, e0] at h'
    exact neg_one_ne_one_zmod3 h'
  have hne1 : (fun j => (flipSign i1 j : ZMod 3) * e1 j) ≠ e1 := by
    intro h
    have h' := congrFun h i1
    simp [flipSign_self, e1] at h'
    exact neg_one_ne_one_zmod3 h'
  have ha0_ne_one : a0 ≠ 1 := by
    intro h
    have h1 : a0 (bElt e0) = bElt e0 := by
      simpa using congrArg (fun f : MulAut ↥((ggGamma J hN).range) => f (bElt e0)) h
    rw [ha0_apply] at h1
    exact hne0 (hb_inj h1)
  have ha1_ne_one : a1 ≠ 1 := by
    intro h
    have h1 : a1 (bElt e1) = bElt e1 := by
      simpa using congrArg (fun f : MulAut ↥((ggGamma J hN).range) => f (bElt e1)) h
    rw [ha1_apply] at h1
    exact hne1 (hb_inj h1)
  have hη1_e0 : (fun j => (flipSign i1 j : ZMod 3) * e0 j) = e0 := by
    funext j
    by_cases hj : j = i1
    · subst hj
      have h0 : e0 i1 = 0 := by simp [e0, Pi.single_eq_of_ne (Ne.symm hi01)]
      rw [flipSign_self, h0, mul_zero]
    · rw [flipSign_of_ne hj, Units.val_one, one_mul]
  have ha0_ne_a1 : a0 ≠ a1 := by
    intro h
    have h1 : a0 (bElt e0) = a1 (bElt e0) := by rw [h]
    rw [ha0_apply, ha1_apply, hη1_e0] at h1
    exact hne0 (hb_inj h1)
  have ha0_order : orderOf a0 = 2 :=
    orderOf_eq_prime (by simpa [pow_two] using ha0_sq) ha0_ne_one
  have ha1_order : orderOf a1 = 2 :=
    orderOf_eq_prime (by simpa [pow_two] using ha1_sq) ha1_ne_one
  have hK : IsKleinFour (Subgroup.closure ({a0, a1} :
      Set (MulAut ↥((ggGamma J hN).range)))) :=
    CFSG.ComponentClassification.UnbalancedGS.ReciprocalFusion.isKleinFour_closure_pair
      ha0_order ha1_order ha_comm ha0_ne_a1
  have hcard : Nat.card (Subgroup.closure ({a0, a1} :
      Set (MulAut ↥((ggGamma J hN).range)))) = 4 :=
    @IsKleinFour.card_four (Subgroup.closure ({a0, a1} :
      Set (MulAut ↥((ggGamma J hN).range)))) _ hK
  exact ⟨a0, a1, hA0, hA1, ha0_sq, ha1_sq, ha_comm, ha0_ne_one, ha1_ne_one,
    ha0_ne_a1, hcard⟩

end Flips

section Inversion

variable (hN : Bs ≤ Subgroup.normalizer (J : Set G))
  (φ : Matrix.SpecialLinearGroup (Fin n) K →* ↥J)
  (hC : (CoordSL.rootMat g).det = 1) (hCp : (CoordSL.rootMat g) ^ 3 = 1)

omit [Finite G] in
private theorem exists_inversion_mem_ggTorusWeylAut_at_A
    (hframeA : (CoordSL.frameHom (psi φ) A₀ ε hC hCp).range = (ggGamma J hN).range)
    (hgd : g ∣ cyclotomic 3 K) (hpK : ¬ 3 ∣ Nat.card K - 1)
    (hζ : AdjoinRoot.root g ^ 3 = 1) :
    ∃ Φ ∈ ggTorusWeylAut 3 ((ggGamma J hN).range),
      ∀ a : ↥(ggGamma J hN).range, Φ a = a⁻¹ := by
  classical
  have hη : ∀ j : Fin s, (-1 : (ZMod 3)ˣ) ∈ CoordSL.galExp g hζ :=
    fun _ => galExp_neg_one g hgd hpK hζ
  obtain ⟨v, hv, hvconj⟩ :=
    CoordSL.exists_move_mem (g := g) (ψ := psi φ) A₀ ε hC hCp hζ hframeA
      (Equiv.refl (Fin s)) (fun _ => (-1 : (ZMod 3)ˣ)) hη
  obtain ⟨hvrange, hvN⟩ := Subgroup.mem_inf.mp hv
  obtain ⟨W, hW⟩ := hvrange
  let w : ↥J := φ W
  have hv_eq : v = MulAut.conj w := by rw [← hW]; rfl
  let n : ↥J := w⁻¹
  have hn_eq : MulAut.conj n = v⁻¹ := by
    dsimp [n]
    rw [map_inv, ← hv_eq]
  have hn : MulAut.conj n ∈
      Subgroup.normalizer ((ggGamma J hN).range : Set (MulAut ↥J)) := by
    rw [hn_eq]
    exact Subgroup.inv_mem _ hvN
  have hWeyl : GGTorusWeylElt 3 ((ggGamma J hN).range) n :=
    ggTorusWeylElt_of_conj_mem_normalizer
      (isElemAbelian_gammaRange (hN := hN) (φ := φ) (hC := hC) (hCp := hCp) hframeA)
      (fun a ha => exists_conj_of_mem_gammaRange (hN := hN) (φ := φ) (hC := hC)
        (hCp := hCp) hframeA ha)
      (fun x y hx hy => comm_of_conj_mem_gammaRange (hN := hN) (φ := φ) (hC := hC)
        (hCp := hCp) hframeA hx hy) hn
  refine ⟨ggConjAut ((ggGamma J hN).range) hn, ⟨n, hn, hWeyl, rfl⟩, ?_⟩
  intro a
  have hmem : (a : MulAut ↥J) ∈
      (CoordSL.frameHom (psi φ) A₀ ε hC hCp).range := by
    rw [hframeA]
    exact a.2
  obtain ⟨t, ht⟩ := hmem
  let u : Fin s → ZMod 3 := Multiplicative.toAdd t
  have ht' : a = ⟨CoordSL.frameHom (psi φ) A₀ ε hC hCp (Multiplicative.ofAdd u),
      hframeA ▸ ⟨Multiplicative.ofAdd u, rfl⟩⟩ := by
    apply Subtype.ext
    have hcoe : CoordSL.frameHom (psi φ) A₀ ε hC hCp (Multiplicative.ofAdd u) =
        (a : MulAut ↥J) := by
      simpa [u] using ht
    exact hcoe.symm
  rw [ht']
  apply Subtype.ext
  rw [ggConjAut_apply, Subgroup.coe_inv]
  change (MulAut.conj n) *
      CoordSL.frameHom (psi φ) A₀ ε hC hCp (Multiplicative.ofAdd u) *
      (MulAut.conj n)⁻¹ =
    (CoordSL.frameHom (psi φ) A₀ ε hC hCp (Multiplicative.ofAdd u))⁻¹
  rw [hn_eq, inv_inv, hvconj u]
  simp only [Equiv.refl_apply]
  have hneg : (fun j => ((-1 : (ZMod 3)ˣ) : ZMod 3) * u j) = -u := by
    funext j
    simp only [Units.val_neg, Units.val_one, Pi.neg_apply, neg_mul, one_mul]
  rw [hneg, ofAdd_neg, map_inv]

end Inversion

section Transport

variable (hN : Bs ≤ Subgroup.normalizer (J : Set G))

private theorem card_four_dvd_automizer_actualA
    (hBs : IsElemAbelian 3 Bs)
    (hSC : ∀ x ∈ Subgroup.centralizer (Bs : Set G), x ^ 3 = 1 → x ∈ Bs)
    (hNoTr : GGNoTransvection 3 Bs)
    (hZ : Nat.card ↥(Bs ⊓ J ⊓ Subgroup.centralizer (J : Set G)) ≤ 3)
    (φ : Matrix.SpecialLinearGroup (Fin n) K →* ↥J)
    (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K))
    (hC : (CoordSL.rootMat g).det = 1) (hCp : (CoordSL.rootMat g) ^ 3 = 1)
    (hgd : g ∣ cyclotomic 3 K) (hpK : ¬ 3 ∣ Nat.card K - 1)
    (hζ : AdjoinRoot.root g ^ 3 = 1)
    (hframeA : (CoordSL.frameHom (psi φ) A₀ ε hC hCp).range = (ggGamma J hN).range)
    (hs : 2 ≤ s) :
    4 ∣ Nat.card (ggAutomizer J Bs) := by
  have hinj : Function.Injective (CoordSL.frameHom (psi φ) A₀ ε hC hCp) :=
    frameHom_psi_injective (φ := φ) (hC := hC) (hCp := hCp) (A₀ := A₀) (ε := ε)
      hφ hker hgd hpK hs
  obtain ⟨a0, a1, hA0, hA1, ha0sq, ha1sq, hacomm, ha0ne, ha1ne, ha0nea1, _hcard⟩ :=
    exists_kleinFour_weylAut_at_A (hN := hN) (φ := φ) (hC := hC) (hCp := hCp)
      (hframeA := hframeA) (hgd := hgd) (hpK := hpK) (hζ := hζ)
      (hφ := hφ) (hker := hker) (hs := hs)
  let A : Subgroup (MulAut ↥J) := (ggGamma J hN).range
  let Gcod := ggAutomizer (MulAut.conj : ↥J →* MulAut ↥J).range A
  let f := ggAutomizerGammaHom hN
  have hinjGamma : Function.Injective f :=
    ggAutomizerGammaHom_injective (p := 3) Nat.prime_three hBs hNoTr hN hZ
  have exists_preimage : ∀ (a : MulAut ↥A), a ∈ ggTorusWeylAut 3 A →
      ∃ d : ggAutomizer J Bs, ((f d : Gcod) : MulAut ↥A) = a := by
    intro a ha
    have hmem : a ∈ (f.range.map Gcod.subtype : Set (MulAut ↥A)) := by
      rw [ggAutomizerGammaHom_range (p := 3) hBs hSC hN]
      exact ha
    obtain ⟨c, hc, hca⟩ := Subgroup.mem_map.mp hmem
    obtain ⟨d, hd⟩ := MonoidHom.mem_range.mp hc
    refine ⟨d, ?_⟩
    rw [hd]
    exact hca
  obtain ⟨d0, hd0⟩ := exists_preimage a0 hA0
  obtain ⟨d1, hd1⟩ := exists_preimage a1 hA1
  have hd0sq : d0 * d0 = 1 := by
    apply hinjGamma
    apply Subtype.ext
    rw [map_mul, map_one]
    change ((f d0 : Gcod) : MulAut ↥A) * ((f d0 : Gcod) : MulAut ↥A) = 1
    rw [hd0, ha0sq]
  have hd1sq : d1 * d1 = 1 := by
    apply hinjGamma
    apply Subtype.ext
    rw [map_mul, map_one]
    change ((f d1 : Gcod) : MulAut ↥A) * ((f d1 : Gcod) : MulAut ↥A) = 1
    rw [hd1, ha1sq]
  have hdcomm : d0 * d1 = d1 * d0 := by
    apply hinjGamma
    apply Subtype.ext
    rw [map_mul, map_mul]
    change ((f d0 : Gcod) : MulAut ↥A) * ((f d1 : Gcod) : MulAut ↥A) =
      ((f d1 : Gcod) : MulAut ↥A) * ((f d0 : Gcod) : MulAut ↥A)
    rw [hd0, hd1, hacomm]
  have hd0ne : d0 ≠ 1 := by
    intro h
    apply ha0ne
    have h' : ((f d0 : Gcod) : MulAut ↥A) = 1 := by
      rw [h, map_one]
      rfl
    rw [hd0] at h'
    exact h'
  have hd1ne : d1 ≠ 1 := by
    intro h
    apply ha1ne
    have h' : ((f d1 : Gcod) : MulAut ↥A) = 1 := by
      rw [h, map_one]
      rfl
    rw [hd1] at h'
    exact h'
  have hd0ne1 : d0 ≠ d1 := by
    intro h
    apply ha0nea1
    have h' : ((f d0 : Gcod) : MulAut ↥A) = ((f d1 : Gcod) : MulAut ↥A) := by rw [h]
    rw [hd0, hd1] at h'
    exact h'
  have hd0order : orderOf d0 = 2 :=
    orderOf_eq_prime (by simpa [pow_two] using hd0sq) hd0ne
  have hd1order : orderOf d1 = 2 :=
    orderOf_eq_prime (by simpa [pow_two] using hd1sq) hd1ne
  have hK : IsKleinFour (Subgroup.closure ({d0, d1} : Set ↥(ggAutomizer J Bs))) :=
    CFSG.ComponentClassification.UnbalancedGS.ReciprocalFusion.isKleinFour_closure_pair
      hd0order hd1order hdcomm hd0ne1
  have hcard : Nat.card (Subgroup.closure ({d0, d1} : Set ↥(ggAutomizer J Bs))) = 4 :=
    @IsKleinFour.card_four (Subgroup.closure ({d0, d1} : Set ↥(ggAutomizer J Bs))) _ hK
  have hdvd : 4 ∣ Nat.card (ggAutomizer J Bs) := by
    have h := Subgroup.card_dvd_of_le
      (le_top : Subgroup.closure ({d0, d1} : Set ↥(ggAutomizer J Bs)) ≤ ⊤)
    rw [hcard] at h
    simpa using h
  exact hdvd

private theorem not_lineJDatum_A2_actualA
    [Fact (Nat.Prime 3)]
    (hBs : IsElemAbelian 3 Bs)
    (hSC : ∀ x ∈ Subgroup.centralizer (Bs : Set G), x ^ 3 = 1 → x ∈ Bs)
    (hNoTr : GGNoTransvection 3 Bs)
    (hZ : Nat.card ↥(Bs ⊓ J ⊓ Subgroup.centralizer (J : Set G)) ≤ 3)
    (φ : Matrix.SpecialLinearGroup (Fin n) K →* ↥J)
    (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K))
    (hC : (CoordSL.rootMat g).det = 1) (hCp : (CoordSL.rootMat g) ^ 3 = 1)
    (hgd : g ∣ cyclotomic 3 K) (hpK : ¬ 3 ∣ Nat.card K - 1)
    (hζ : AdjoinRoot.root g ^ 3 = 1)
    (hframeA : (CoordSL.frameHom (psi φ) A₀ ε hC hCp).range = (ggGamma J hN).range)
    (hs : 2 ≤ s)
    (hD : GGResLineJDatum 3 Bs J .A2) : False := by
  have h4 : 4 ∣ Nat.card (ggAutomizer J Bs) :=
    card_four_dvd_automizer_actualA (hN := hN) (hBs := hBs) (hSC := hSC)
      (hNoTr := hNoTr) (hZ := hZ) (φ := φ) (hφ := hφ) (hker := hker)
      (hC := hC) (hCp := hCp) (hgd := hgd) (hpK := hpK) (hζ := hζ)
      (hframeA := hframeA) (hs := hs)
  have h6 : Nat.card (ggAutomizer J Bs) = 6 :=
    ggAutomizer_card_of_lineJDatum_A2 (p := 3) rfl hD
  rw [h6] at h4
  norm_num at h4

private theorem not_lineJDatum_A3_actualA
    [Fact (Nat.Prime 3)]
    (hBs : IsElemAbelian 3 Bs)
    (hSC : ∀ x ∈ Subgroup.centralizer (Bs : Set G), x ^ 3 = 1 → x ∈ Bs)
    (hNoTr : GGNoTransvection 3 Bs)
    (hZ : Nat.card ↥(Bs ⊓ J ⊓ Subgroup.centralizer (J : Set G)) ≤ 3)
    (φ : Matrix.SpecialLinearGroup (Fin n) K →* ↥J)
    (hC : (CoordSL.rootMat g).det = 1) (hCp : (CoordSL.rootMat g) ^ 3 = 1)
    (hgd : g ∣ cyclotomic 3 K) (hpK : ¬ 3 ∣ Nat.card K - 1)
    (hζ : AdjoinRoot.root g ^ 3 = 1)
    (hframeA : (CoordSL.frameHom (psi φ) A₀ ε hC hCp).range = (ggGamma J hN).range)
    (hA2 : 2 ≤ Nat.card (ggGamma J hN).range)
    (hD : GGResLineJDatum 3 Bs J .A3) : False := by
  obtain ⟨Φ, hΦ, hΦinv⟩ :=
    exists_inversion_mem_ggTorusWeylAut_at_A (hN := hN) (φ := φ) (hC := hC) (hCp := hCp)
      hframeA hgd hpK hζ
  exact CFSG.StandardType.not_exists_inversion_mem_ggTorusWeylAut_of_lineJDatum_A3
    hN hBs hSC hNoTr hZ rfl hA2 hD ⟨Φ, hΦ, hΦinv⟩

end Transport

section FrameConstruction

open CFSG.ComponentClassification

variable (hN : Bs ≤ Subgroup.normalizer (J : Set G))
  (hBs : IsElemAbelian 3 Bs)
  (hSC : ∀ x ∈ Subgroup.centralizer (Bs : Set G), x ^ 3 = 1 → x ∈ Bs)
  (φ : Matrix.SpecialLinearGroup (Fin n) K →* ↥J)
  (hφ : Function.Surjective φ)
  (hker : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K))
  (hn3 : 3 ≤ n)
  (hpK : ¬ 3 ∣ Nat.card K - 1)

omit [Finite G] in
private theorem isElemAbelian_gammaRange_of_bs
    (hBs : IsElemAbelian 3 Bs) :
    IsElemAbelian 3 (ggGamma J hN).range := by
  exact isElemAbelian_range
    (fun a b : ↥Bs => (@IsMulCommutative.is_comm ↥Bs _ hBs.1).comm a b)
    (fun b : ↥Bs => Subtype.ext (by simpa using hBs.2 b b.2))
    (ggGamma J hN)

omit [Finite G] [Finite K] [CharP K 2] in
private theorem exists_slLift_of_action
    (hBs : IsElemAbelian 3 Bs)
    (hker : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K))
    (hY : ∀ a ∈ (ggGamma J hN).range, ∃ Y : Matrix.GeneralLinearGroup (Fin n) K,
      ∀ g : Matrix.SpecialLinearGroup (Fin n) K,
        a (φ g) = φ (CatalogueBHigherLinearAction.slConjugation n K Y g))
    (hn3 : 3 ≤ n) (hpK : ¬ 3 ∣ Nat.card K - 1)
    {a : MulAut ↥J} (ha : a ∈ (ggGamma J hN).range) :
    ∃ g : Matrix.SpecialLinearGroup (Fin n) K,
      g ^ 3 = 1 ∧
      (∀ x : Matrix.SpecialLinearGroup (Fin n) K,
        a (φ x) = φ (g * x * g⁻¹)) := by
  classical
  obtain ⟨Y, hY'⟩ := hY a ha
  let X : MulAut (Matrix.SpecialLinearGroup (Fin n) K) :=
    CatalogueBHigherLinearAction.slConjugation n K Y
  have hX : ∀ x, a (φ x) = φ (X x) := hY'
  have hperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin n) K) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (K := K) hn3
  have hS : commutator (Matrix.SpecialLinearGroup (Fin n) K) = ⊤ :=
    hperf.commutator_eq_top
  have hAcube : a ^ 3 = 1 := (isElemAbelian_gammaRange_of_bs hN hBs).2 a ha
  have hact : ∀ k : ℕ, ∀ x : Matrix.SpecialLinearGroup (Fin n) K,
      (a ^ k) (φ x) = φ ((X ^ k) x) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
        intro x
        calc (a ^ (k + 1)) (φ x) = (a ^ k) (a (φ x)) := by
              rw [pow_succ, MulAut.mul_apply]
          _ = (a ^ k) (φ (X x)) := congrArg (fun y => (a ^ k) y) (hX x)
          _ = φ ((X ^ k) (X x)) := ih (X x)
          _ = φ ((X ^ (k + 1)) x) := by rw [pow_succ, MulAut.mul_apply]
  have hXcube : X ^ 3 = 1 := by
    have hmem : ∀ x : Matrix.SpecialLinearGroup (Fin n) K,
        ((X ^ 3) x)⁻¹ * x ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K) := by
      intro x
      have h1 : φ ((X ^ 3) x) = φ x := by
        have h := hact 3 x
        rw [hAcube] at h
        simpa using h.symm
      have h2 : φ (((X ^ 3) x) * x⁻¹) = 1 := by
        rw [map_mul, h1, map_inv]
        exact mul_inv_cancel (φ x)
      have h4 : ((X ^ 3) x) * x⁻¹ ∈
          Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K) :=
        hker (MonoidHom.mem_ker.mpr h2)
      have h5 : ((X ^ 3) x)⁻¹ * x = (((X ^ 3) x) * x⁻¹)⁻¹ := by
        set z := ((X ^ 3) x) * x⁻¹ with hz
        have hzg : z * x = x * z := (Subgroup.mem_center_iff.mp h4 x).symm
        have hcomm : Commute z x := hzg
        have hcomm_inv : Commute z⁻¹ x := hcomm.inv_left
        calc ((X ^ 3) x)⁻¹ * x = (z * x)⁻¹ * x := by rw [hz]; group
          _ = x⁻¹ * z⁻¹ * x := by rw [mul_inv_rev (a := z) (b := x)]
          _ = x⁻¹ * (z⁻¹ * x) := by group
          _ = x⁻¹ * (x * z⁻¹) := by rw [hcomm_inv.eq]
          _ = z⁻¹ := by group
      rw [h5]
      exact Subgroup.inv_mem _ h4
    have hEq : (X ^ 3).toMonoidHom =
        MonoidHom.id (Matrix.SpecialLinearGroup (Fin n) K) :=
      CFSG.StandardType.TypeA.eq_of_inv_mul_mem_center hS (X ^ 3).toMonoidHom
        (MonoidHom.id _) hmem
    apply MulEquiv.ext
    intro x
    exact DFunLike.congr_fun hEq x
  have hYcube : Y ^ 3 ∈ (CatalogueBHigherLinearAction.slConjugation n K).ker := by
    rw [MonoidHom.mem_ker, map_pow, hXcube]
  have hYcenter : Y ^ 3 ∈ Subgroup.center (Matrix.GeneralLinearGroup (Fin n) K) := by
    rwa [CFSG.LinearGroups.ker_slConjugation n K] at hYcube
  have hYscalar : Y ^ 3 ∈
      (Matrix.GeneralLinearGroup.scalar (Fin n) : Kˣ →* Matrix.GeneralLinearGroup (Fin n) K).range := by
    rw [← Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact hYcenter
  obtain ⟨c, hc⟩ := hYscalar
  have hcop : (Nat.card Kˣ).Coprime 3 := by
    rw [Nat.card_units]
    exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hpK).symm
  obtain ⟨s, hs⟩ := (powCoprime (G := Kˣ) (n := 3) hcop).surjective c⁻¹
  rw [powCoprime_apply] at hs
  let G : Matrix.GeneralLinearGroup (Fin n) K :=
    Matrix.GeneralLinearGroup.scalar (Fin n) s * Y
  have hcomm : Commute (Matrix.GeneralLinearGroup.scalar (Fin n) s) Y :=
    CFSG.StandardType.TypeA.commute_scalar_GL s Y
  have hGcube : G ^ 3 = 1 := by
    dsimp [G]
    calc (Matrix.GeneralLinearGroup.scalar (Fin n) s * Y) ^ 3 =
          (Matrix.GeneralLinearGroup.scalar (Fin n) s) ^ 3 * Y ^ 3 := hcomm.mul_pow 3
      _ = Matrix.GeneralLinearGroup.scalar (Fin n) (s ^ 3) * Y ^ 3 := by rw [map_pow]
      _ = Matrix.GeneralLinearGroup.scalar (Fin n) (s ^ 3) *
            Matrix.GeneralLinearGroup.scalar (Fin n) c := by rw [← hc]
      _ = Matrix.GeneralLinearGroup.scalar (Fin n) (s ^ 3 * c) := by rw [← map_mul]
      _ = Matrix.GeneralLinearGroup.scalar (Fin n) (c⁻¹ * c) := by rw [hs]
      _ = 1 := by rw [inv_mul_cancel, map_one]
  have hdet3 : (Matrix.GeneralLinearGroup.det G) ^ 3 = 1 := by
    rw [← map_pow, hGcube, map_one]
  have hdet1 : Matrix.GeneralLinearGroup.det G = 1 := by
    apply (powCoprime (G := Kˣ) (n := 3) hcop).injective
    rw [powCoprime_apply, hdet3, powCoprime_apply, one_pow]
  have hdet1' : (G : Matrix (Fin n) (Fin n) K).det = 1 := by
    have h := congrArg Units.val hdet1
    rwa [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] at h
  let g : Matrix.SpecialLinearGroup (Fin n) K :=
    ⟨(G : Matrix (Fin n) (Fin n) K), hdet1'⟩
  have hgG : (g : Matrix (Fin n) (Fin n) K) = (G : Matrix (Fin n) (Fin n) K) := rfl
  have hg3 : g ^ 3 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, hgG, ← Units.val_pow_eq_pow_val, hGcube, Units.val_one]
    rfl
  have hscalar : CatalogueBHigherLinearAction.slConjugation n K
      (Matrix.GeneralLinearGroup.scalar (Fin n) s) = 1 := by
    rw [← MonoidHom.mem_ker, CFSG.LinearGroups.ker_slConjugation n K]
    show Matrix.GeneralLinearGroup.scalar (Fin n) s ∈
      Subgroup.center (Matrix.GeneralLinearGroup (Fin n) K)
    exact (Matrix.GeneralLinearGroup.center_eq_range_scalar (n := Fin n) (R := K)).symm ▸ ⟨s, rfl⟩
  have htoGL : Matrix.SpecialLinearGroup.toGL g = G := by
    apply Units.ext
    rfl
  have hsl : CatalogueBHigherLinearAction.slConjugation n K
      (Matrix.SpecialLinearGroup.toGL g) = X := by
    rw [htoGL]
    dsimp [G, X]
    rw [map_mul, hscalar, one_mul]
  have hconj : ∀ x : Matrix.SpecialLinearGroup (Fin n) K,
      CatalogueBHigherLinearAction.slConjugation n K
        (Matrix.SpecialLinearGroup.toGL g) x = g * x * g⁻¹ := by
    intro x
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [CatalogueBHigherLinearAction.toGL_slConjugation]
    rw [map_mul, map_mul, map_inv]
  refine ⟨g, hg3, ?_⟩
  intro x
  rw [hX x, ← hsl, hconj x]


omit [Finite G] in
private theorem comm_gammaRange
    (hBs : IsElemAbelian 3 Bs) {a b : MulAut ↥J}
    (ha : a ∈ (ggGamma J hN).range) (hb : b ∈ (ggGamma J hN).range) :
    a * b = b * a := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  rw [← map_mul, ← map_mul]
  congr 1
  exact (@IsMulCommutative.is_comm ↥Bs _ hBs.1).comm x y

omit [Finite G] [Finite K] [CharP K 2] in
private theorem commute_of_slLift_hpK
    (hBs : IsElemAbelian 3 Bs)
    (hperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin n) K))
    (hker : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K))
    (hpK : ¬ 3 ∣ Nat.card K - 1) (hn3 : 3 ≤ n)
    {a b : MulAut ↥J} (ha : a ∈ (ggGamma J hN).range)
    (hb : b ∈ (ggGamma J hN).range)
    {u v : Matrix.SpecialLinearGroup (Fin n) K} (_hu : u ^ 3 = 1) (hv : v ^ 3 = 1)
    (hau : ∀ x, a (φ x) = φ (u * x * u⁻¹))
    (hbv : ∀ x, b (φ x) = φ (v * x * v⁻¹)) :
    u * v = v * u := by
  classical
  have hab : a * b = b * a := comm_gammaRange (hN := hN) (hBs := hBs) ha hb
  let σu : MulAut (Matrix.SpecialLinearGroup (Fin n) K) := MulAut.conj u
  let σv : MulAut (Matrix.SpecialLinearGroup (Fin n) K) := MulAut.conj v
  have hσu : CatalogueBHigherLinearAction.slConjugation n K
      (Matrix.SpecialLinearGroup.toGL u) = σu := by
    apply MulEquiv.ext
    intro y
    apply Matrix.SpecialLinearGroup.toGL_injective
    simp only [CatalogueBHigherLinearAction.toGL_slConjugation, σu, MulAut.conj_apply,
      map_mul, map_inv]
  have hσv : CatalogueBHigherLinearAction.slConjugation n K
      (Matrix.SpecialLinearGroup.toGL v) = σv := by
    apply MulEquiv.ext
    intro y
    apply Matrix.SpecialLinearGroup.toGL_injective
    simp only [CatalogueBHigherLinearAction.toGL_slConjugation, σv, MulAut.conj_apply,
      map_mul, map_inv]
  have hc : σu * σv = σv * σu := by
    have hα : (σu * σv).toMonoidHom = (σv * σu).toMonoidHom := by
      apply CFSG.StandardType.TypeA.eq_of_inv_mul_mem_center hperf.commutator_eq_top
        (σu * σv).toMonoidHom (σv * σu).toMonoidHom
      intro x
      have hu' : ∀ y, φ (σu y) = a (φ y) := by
        intro y
        have hy : σu y = u * y * u⁻¹ := rfl
        rw [hy]
        exact (hau y).symm
      have hv' : ∀ y, φ (σv y) = b (φ y) := by
        intro y
        have hy : σv y = v * y * v⁻¹ := rfl
        rw [hy]
        exact (hbv y).symm
      have h1 : φ ((σu * σv) x) = φ ((σv * σu) x) := by
        calc φ ((σu * σv) x) = φ (σu (σv x)) := rfl
          _ = a (φ (σv x)) := hu' _
          _ = a (b (φ x)) := by rw [hv']
          _ = (a * b) (φ x) := rfl
          _ = (b * a) (φ x) := by rw [hab]
          _ = b (a (φ x)) := rfl
          _ = b (φ (σu x)) := by rw [← hu']
          _ = φ (σv (σu x)) := (hv' _).symm
          _ = φ ((σv * σu) x) := rfl
      have h2 : φ (((σu * σv) x)⁻¹ * ((σv * σu) x)) = 1 := by
        rw [map_mul, map_inv, h1, inv_mul_cancel]
      exact hker (MonoidHom.mem_ker.mpr h2)
    exact MulEquiv.ext (fun x => DFunLike.congr_fun hα x)
  let z : Matrix.SpecialLinearGroup (Fin n) K := u * v * u⁻¹ * v⁻¹
  have hz1 : CatalogueBHigherLinearAction.slConjugation n K
      (Matrix.SpecialLinearGroup.toGL z) = 1 := by
    have hto : Matrix.SpecialLinearGroup.toGL z =
        Matrix.SpecialLinearGroup.toGL u * Matrix.SpecialLinearGroup.toGL v *
          (Matrix.SpecialLinearGroup.toGL u)⁻¹ *
          (Matrix.SpecialLinearGroup.toGL v)⁻¹ := by
      dsimp [z]
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    rw [hto, map_mul, map_mul, map_mul, map_inv, map_inv,
      hσu, hσv]
    rw [hc]
    group
  have hzcenter_GL : Matrix.SpecialLinearGroup.toGL z ∈
      Subgroup.center (Matrix.GeneralLinearGroup (Fin n) K) := by
    rw [← CFSG.LinearGroups.ker_slConjugation n K]
    exact MonoidHom.mem_ker.mpr hz1
  have hzcenter : z ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K) :=
    (Matrix.SpecialLinearGroup.toGL_mem_center_iff z).mp hzcenter_GL
  have hz3 : z ^ 3 = 1 := by
    have hconj : u * v * u⁻¹ = z * v := by dsimp [z]; group
    have h3 : (u * v * u⁻¹) ^ 3 = 1 := by
      rw [conj_pow, hv, mul_one, mul_inv_cancel]
    have h4 : (z * v) ^ 3 = z ^ 3 * v ^ 3 :=
      Commute.mul_pow (Subgroup.mem_center_iff.mp hzcenter v).symm 3
    rw [← hconj, h3, hv, mul_one] at h4
    exact h4.symm
  have hz_one : z = 1 := by
    have hz_scalar : Matrix.SpecialLinearGroup.toGL z ∈
        (Matrix.GeneralLinearGroup.scalar (Fin n) : Kˣ →*
          Matrix.GeneralLinearGroup (Fin n) K).range := by
      rw [← Matrix.GeneralLinearGroup.center_eq_range_scalar (n := Fin n) (R := K)]
      exact hzcenter_GL
    obtain ⟨c, hc_scalar⟩ := hz_scalar
    let hne : Nonempty (Fin n) :=
      ⟨(⟨0, Nat.lt_of_lt_of_le (by norm_num) hn3⟩ : Fin n)⟩
    have hc3 : c ^ 3 = 1 := by
      apply @CFSG.LinearAlgebra.generalLinearGroup_scalar_injective (Fin n) K _ _ hne _
      rw [map_pow, hc_scalar, ← map_pow, hz3, map_one, map_one]
    have hcop : (Nat.card Kˣ).Coprime 3 := by
      rw [Nat.card_units]
      exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hpK).symm
    have hc1 : c = 1 := by
      apply (powCoprime (G := Kˣ) (n := 3) hcop).injective
      rw [powCoprime_apply, hc3, powCoprime_apply, one_pow]
    have hzGL1 : Matrix.SpecialLinearGroup.toGL z = 1 := by
      rw [← hc_scalar, hc1, map_one]
    apply Subtype.ext
    have h := congrArg Units.val hzGL1
    simpa using h
  dsimp [z] at hz_one
  calc u * v = (u * v * u⁻¹ * v⁻¹) * (v * u) := by group
    _ = v * u := by rw [hz_one]; group



omit [Finite G] in
theorem exists_frame_range_eq_gamma
    (hBs : IsElemAbelian 3 Bs)
    (hSC : ∀ x ∈ Subgroup.centralizer (Bs : Set G), x ^ 3 = 1 → x ∈ Bs)
    (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K))
    (hCardA : 9 ≤ Nat.card (ggGamma J hN).range)
    (hY : ∀ a ∈ (ggGamma J hN).range, ∃ Y : Matrix.GeneralLinearGroup (Fin n) K,
      ∀ g : Matrix.SpecialLinearGroup (Fin n) K,
        a (φ g) = φ (CatalogueBHigherLinearAction.slConjugation n K Y g))
    (hn3 : 3 ≤ n) (hpK : ¬ 3 ∣ Nat.card K - 1)
    (hC : (CoordSL.rootMat g).det = 1) (hCp : (CoordSL.rootMat g) ^ 3 = 1)
    (hgd : g ∣ cyclotomic 3 K) :
    ∃ (s r : ℕ)
      (ε : Fin n ≃ (Fin (CoordSL.rootPB g).dim × Fin s) ⊕ Fin r)
      (A₀ : Matrix.SpecialLinearGroup (Fin n) K),
      2 ≤ s ∧ (CoordSL.frameHom (psi φ) A₀ ε hC hCp).range =
        (ggGamma J hN).range := by
  classical
  let A : Subgroup (MulAut ↥J) := (ggGamma J hN).range
  have hAe : IsElemAbelian 3 A :=
    isElemAbelian_gammaRange_of_bs (hN := hN) (hBs := hBs)
  choose gLift hgLift3 hLiftAct using fun a : A =>
    exists_slLift_of_action (hN := hN) (φ := φ) (hBs := hBs) (hker := hker)
      (hY := hY) (hn3 := hn3) (hpK := hpK) (a := a.1) (ha := a.2)
  let S : Set (Matrix (Fin n) (Fin n) K) :=
    Set.range (fun a : A => ((gLift a : Matrix.SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K))
  have hperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin n) K) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (K := K) hn3
  have hSc : ∀ x ∈ S, ∀ y ∈ S, Commute x y := by
    rintro x ⟨a, rfl⟩ y ⟨b, rfl⟩
    have h := commute_of_slLift_hpK (hN := hN) (φ := φ) (hBs := hBs)
      (hperf := hperf) (hker := hker) (hpK := hpK) (hn3 := hn3)
      (ha := a.2) (hb := b.2) (_hu := hgLift3 a) (hv := hgLift3 b)
      (hau := hLiftAct a) (hbv := hLiftAct b)
    exact congrArg (fun z : Matrix.SpecialLinearGroup (Fin n) K =>
      ((z : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)) h
  have hSp : ∀ x ∈ S, x ^ 3 = 1 := by
    rintro x ⟨a, rfl⟩
    have h := congrArg (fun z : Matrix.SpecialLinearGroup (Fin n) K =>
      ((z : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)) (hgLift3 a)
    simpa [Matrix.SpecialLinearGroup.coe_pow] using h
  have hpK' : (3 : K) ≠ 0 := by
    intro h
    have h' : (2 : ℕ) ∣ 3 := (CharP.cast_eq_zero_iff K 2 3).mp h
    norm_num at h'
  obtain ⟨s, r, ε, A₀, hframe⟩ :=
    CoordSL.exists_frame (g := g) Nat.prime_three hpK' hgd S hSc hSp
  have hrepr : ∀ b ∈ A, ∃ k : Fin s → ℕ,
      b = SLRep.ggFrame (psi φ) A₀ (SLNS.nsSL ε hC k) := by
    intro b hb
    let a : A := ⟨b, hb⟩
    obtain ⟨k, hk⟩ := hframe (gLift a) (Set.mem_range_self a)
    have hkSL : gLift a * A₀ = A₀ * SLNS.nsSL ε hC k := by
      apply Subtype.ext
      change (gLift a : Matrix (Fin n) (Fin n) K) * (A₀ : Matrix (Fin n) (Fin n) K) =
        (A₀ : Matrix (Fin n) (Fin n) K) * (SLNS.nsSL ε hC k : Matrix (Fin n) (Fin n) K)
      exact hk
    have hgeq : gLift a = A₀ * SLNS.nsSL ε hC k * A₀⁻¹ := by
      rw [← hkSL]; group
    have haeq : b = MulAut.conj (φ (gLift a)) := by
      apply MulEquiv.ext
      intro y
      obtain ⟨x, rfl⟩ := hφ y
      rw [hLiftAct a x, MulAut.conj_apply]
      simp only [map_mul, map_mul, map_inv]
    refine ⟨k, ?_⟩
    rw [haeq, hgeq, SLRep.ggFrame_apply]
    rfl
  have hrange_ge : A ≤ (CoordSL.frameHom (psi φ) A₀ ε hC hCp).range := by
    intro a ha
    obtain ⟨k, hk⟩ := hrepr a ha
    refine ⟨Multiplicative.ofAdd (fun i => (k i : ZMod 3)), ?_⟩
    rw [CoordSL.frameHom_natCast]
    exact hk.symm
  have hrange_le : (CoordSL.frameHom (psi φ) A₀ ε hC hCp).range ≤ A := by
    rintro _ ⟨t, rfl⟩
    let k : Fin s → ℕ := fun i => (Multiplicative.toAdd t i).val
    let x : Matrix.SpecialLinearGroup (Fin n) K :=
      A₀ * SLNS.nsSL ε hC k * A₀⁻¹
    have hfx : CoordSL.frameHom (psi φ) A₀ ε hC hCp t = MulAut.conj (φ x) := by
      conv_lhs => rw [show t = Multiplicative.ofAdd (Multiplicative.toAdd t) from rfl]
      rw [CoordSL.frameHom_apply]
      change (psi φ) (A₀ * SLNS.nsSL ε hC k * A₀⁻¹) = MulAut.conj (φ x)
      rfl
    rw [hfx]
    refine (ggTorusSelfCent_ggGamma (p := 3) hN hSC) (φ x) ?_ ?_
    · intro a ha
      obtain ⟨ka, hka⟩ := hrepr a ha
      let y : Matrix.SpecialLinearGroup (Fin n) K :=
        A₀ * SLNS.nsSL ε hC ka * A₀⁻¹
      have haeq : a = MulAut.conj (φ y) := by
        rw [hka, SLRep.ggFrame_apply]
        rfl
      have hyx : y * x = x * y := by
        have hns : SLNS.nsSL ε hC ka * SLNS.nsSL ε hC k =
            SLNS.nsSL ε hC k * SLNS.nsSL ε hC ka :=
          SLNS.nsSL_comm (ε := ε) (hC := hC) ka k
        dsimp [x, y]
        calc (A₀ * SLNS.nsSL ε hC ka * A₀⁻¹) *
              (A₀ * SLNS.nsSL ε hC k * A₀⁻¹)
            = A₀ * (SLNS.nsSL ε hC ka * SLNS.nsSL ε hC k) * A₀⁻¹ := by group
          _ = A₀ * (SLNS.nsSL ε hC k * SLNS.nsSL ε hC ka) * A₀⁻¹ := by rw [hns]
          _ = (A₀ * SLNS.nsSL ε hC k * A₀⁻¹) *
              (A₀ * SLNS.nsSL ε hC ka * A₀⁻¹) := by group
      rw [haeq, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
      have hxeq : y * x * y⁻¹ = x := by
        rw [hyx]
        group
      rw [hxeq]
    · have hx3 : x ^ 3 = 1 := by
        have hN3 : SLNS.nsSL ε hC k ^ 3 = 1 :=
          SLNS.nsSL_pow_p (ε := ε) (hC := hC) (p := 3) hCp k
        dsimp [x]
        rw [conj_pow, hN3, mul_one, mul_inv_cancel]
      rw [← map_pow, hx3, map_one]
  have hrange : (CoordSL.frameHom (psi φ) A₀ ε hC hCp).range = A :=
    le_antisymm hrange_le hrange_ge
  have hs2 : 2 ≤ s := by
    by_contra hs
    have hs1 : s ≤ 1 := by omega
    let Dom := Multiplicative (Fin s → ZMod 3)
    let f : Dom → A := fun t =>
      ⟨CoordSL.frameHom (psi φ) A₀ ε hC hCp t, by
        have hmem : CoordSL.frameHom (psi φ) A₀ ε hC hCp t ∈
            (CoordSL.frameHom (psi φ) A₀ ε hC hCp).range := ⟨t, rfl⟩
        rwa [hrange] at hmem⟩
    have hsurj : Function.Surjective f := by
      intro a
      have hmem : (a : MulAut ↥J) ∈ (CoordSL.frameHom (psi φ) A₀ ε hC hCp).range := by
        rw [hrange]
        exact a.2
      obtain ⟨t, ht⟩ := hmem
      exact ⟨t, Subtype.ext ht⟩
    have hcard_le : Nat.card A ≤ Nat.card Dom :=
      Nat.card_le_card_of_surjective f hsurj
    have hdom : Nat.card Dom = 3 ^ s := by
      dsimp [Dom]
      simp
    have h3s : 3 ^ s ≤ 3 := by
      calc 3 ^ s ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hs1
        _ = 3 := by norm_num
    have h9 : 9 ≤ 3 ^ s := by
      calc 9 ≤ Nat.card A := hCardA
        _ ≤ Nat.card Dom := hcard_le
        _ = 3 ^ s := hdom
    omega
  exact ⟨s, r, ε, A₀, hs2, hrange⟩


section BoundaryA2

variable (hN : Bs ≤ Subgroup.normalizer (J : Set G))
  (hBs : IsElemAbelian 3 Bs)
  (hSC : ∀ x ∈ Subgroup.centralizer (Bs : Set G), x ^ 3 = 1 → x ∈ Bs)
  (φ : Matrix.SpecialLinearGroup (Fin n) K →* ↥J)
  (hφ : Function.Surjective φ)
  (hker : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K))
  (hn3 : 3 ≤ n) (hpK : ¬ 3 ∣ Nat.card K - 1)
  {g : K[X]} [Fact (Irreducible g)]
  (hC : (CoordSL.rootMat g).det = 1) (hCp : (CoordSL.rootMat g) ^ 3 = 1)
  (hgd : g ∣ cyclotomic 3 K) (hζ : AdjoinRoot.root g ^ 3 = 1)
  (hNoTr : GGNoTransvection 3 Bs)
  (hZ : Nat.card ↥(Bs ⊓ J ⊓ Subgroup.centralizer (J : Set G)) ≤ 3)
  [Fact (Nat.Prime 3)]

private theorem not_lineJDatum_A2_actualA_of_boundary
    (hBs : IsElemAbelian 3 Bs)
    (hSC : ∀ x ∈ Subgroup.centralizer (Bs : Set G), x ^ 3 = 1 → x ∈ Bs)
    (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K))
    (hn3 : 3 ≤ n) (hpK : ¬ 3 ∣ Nat.card K - 1)
    (hC : (CoordSL.rootMat g).det = 1) (hCp : (CoordSL.rootMat g) ^ 3 = 1)
    (hgd : g ∣ cyclotomic 3 K) (hζ : AdjoinRoot.root g ^ 3 = 1)
    (hNoTr : GGNoTransvection 3 Bs)
    (hZ : Nat.card ↥(Bs ⊓ J ⊓ Subgroup.centralizer (J : Set G)) ≤ 3)
    (hY : ∀ a ∈ (ggGamma J hN).range, ∃ Y : Matrix.GeneralLinearGroup (Fin n) K,
      ∀ g : Matrix.SpecialLinearGroup (Fin n) K,
        a (φ g) = φ (CatalogueBHigherLinearAction.slConjugation n K Y g))
    (hCardA : 9 ≤ Nat.card (ggGamma J hN).range)
    (hD : GGResLineJDatum 3 Bs J .A2) : False := by
  obtain ⟨s, r, ε, A₀, hs2, hrange⟩ :=
    exists_frame_range_eq_gamma (hN := hN) (hBs := hBs) (hSC := hSC)
      (φ := φ) (hφ := hφ) (hker := hker) (hn3 := hn3) (hpK := hpK)
      (hC := hC) (hCp := hCp) (hgd := hgd) (hCardA := hCardA)
      (hY := hY)
  exact not_lineJDatum_A2_actualA (hN := hN) (hBs := hBs) (hSC := hSC)
    (hNoTr := hNoTr) (hZ := hZ) (φ := φ) (hφ := hφ) (hker := hker)
    (hC := hC) (hCp := hCp) (hgd := hgd) (hpK := hpK) (hζ := hζ)
    (A₀ := A₀) (ε := ε) (s := s) (r := r)
    (hframeA := hrange) (hs := hs2) hD

private theorem not_lineJDatum_A3_actualA_of_boundary
    (hBs : IsElemAbelian 3 Bs)
    (hSC : ∀ x ∈ Subgroup.centralizer (Bs : Set G), x ^ 3 = 1 → x ∈ Bs)
    (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K))
    (hn3 : 3 ≤ n) (hpK : ¬ 3 ∣ Nat.card K - 1)
    (hC : (CoordSL.rootMat g).det = 1) (hCp : (CoordSL.rootMat g) ^ 3 = 1)
    (hgd : g ∣ cyclotomic 3 K) (hζ : AdjoinRoot.root g ^ 3 = 1)
    (hNoTr : GGNoTransvection 3 Bs)
    (hZ : Nat.card ↥(Bs ⊓ J ⊓ Subgroup.centralizer (J : Set G)) ≤ 3)
    (hY : ∀ a ∈ (ggGamma J hN).range, ∃ Y : Matrix.GeneralLinearGroup (Fin n) K,
      ∀ g : Matrix.SpecialLinearGroup (Fin n) K,
        a (φ g) = φ (CatalogueBHigherLinearAction.slConjugation n K Y g))
    (hD : GGResLineJDatum 3 Bs J .A3) : False := by
  have h27 := GGResLineJDatum.cube_le_card_gamma_of_A3 hN hD
  have hCardA : 9 ≤ Nat.card (ggGamma J hN).range := by omega
  obtain ⟨s, r, ε, A₀, hs2, hrange⟩ :=
    exists_frame_range_eq_gamma (hN := hN) (hBs := hBs) (hSC := hSC)
      (φ := φ) (hφ := hφ) (hker := hker) (hn3 := hn3) (hpK := hpK)
      (hC := hC) (hCp := hCp) (hgd := hgd) (hCardA := hCardA)
      (hY := hY)
  have hinj : Function.Injective (CoordSL.frameHom (psi φ) A₀ ε hC hCp) :=
    frameHom_psi_injective (φ := φ) (hC := hC) (hCp := hCp) (A₀ := A₀) (ε := ε)
      hφ hker hgd hpK hs2
  have hcardA : Nat.card (ggGamma J hN).range = 3 ^ s := by
    rw [← hrange]
    calc
      Nat.card ↥(CoordSL.frameHom (psi φ) A₀ ε hC hCp).range =
          Nat.card ↥(⊤ : Subgroup (Multiplicative (Fin s → ZMod 3))) := by
        rw [MonoidHom.range_eq_map]
        exact Subgroup.card_map_of_injective (K := ⊤) hinj
      _ = 3 ^ s := by
        rw [Subgroup.card_top]
        dsimp [Multiplicative]
        simp
  have hs3 : 3 ≤ s := by
    rw [hcardA] at h27
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h27
  have hA2 : 2 ≤ Nat.card (ggGamma J hN).range := by
    rw [hcardA]
    calc 2 ≤ 3 ^ 3 := by norm_num
      _ ≤ 3 ^ s := Nat.pow_le_pow_right (by norm_num) hs3
  exact not_lineJDatum_A3_actualA (hN := hN) (hBs := hBs) (hSC := hSC)
    (hNoTr := hNoTr) (hZ := hZ) (φ := φ)
    (hC := hC) (hCp := hCp) (hgd := hgd) (hpK := hpK) (hζ := hζ)
    (A₀ := A₀) (ε := ε) (s := s) (r := r)
    (hframeA := hrange) (hA2 := hA2) hD



theorem not_lineJDatum_A2_of_paired_gl_action
    (hBs : IsElemAbelian 3 Bs)
    (hSC : ∀ x ∈ Subgroup.centralizer (Bs : Set G), x ^ 3 = 1 → x ∈ Bs)
    (hNoTr : GGNoTransvection 3 Bs)
    (hZ : Nat.card ↥(Bs ⊓ J ⊓ Subgroup.centralizer (J : Set G)) ≤ 3)
    (φ : Matrix.SpecialLinearGroup (Fin n) K →* ↥J)
    (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K))
    (hn3 : 3 ≤ n) (hpK : ¬ 3 ∣ Nat.card K - 1)
    (hC : (CoordSL.rootMat g).det = 1) (hCp : (CoordSL.rootMat g) ^ 3 = 1)
    (hgd : g ∣ cyclotomic 3 K) (hζ : AdjoinRoot.root g ^ 3 = 1)
    (hYact : ∀ b : ↥Bs, ∃ Y : Matrix.GeneralLinearGroup (Fin n) K,
      ∀ g : Matrix.SpecialLinearGroup (Fin n) K,
        (b : G) * ((φ g : ↥J) : G) * (b : G)⁻¹ =
          ((φ (CatalogueBHigherLinearAction.slConjugation n K Y g) : ↥J) : G))
    (hCardA : 9 ≤ Nat.card (ggGamma J hN).range)
    (hD : GGResLineJDatum 3 Bs J .A2) : False := by
  have hY : ∀ a ∈ (ggGamma J hN).range, ∃ Y : Matrix.GeneralLinearGroup (Fin n) K,
      ∀ g : Matrix.SpecialLinearGroup (Fin n) K,
        a (φ g) = φ (CatalogueBHigherLinearAction.slConjugation n K Y g) := by
    rintro a ⟨b, rfl⟩
    obtain ⟨Y, hYb⟩ := hYact b
    refine ⟨Y, fun g => ?_⟩
    apply Subtype.ext
    change (b : G) * ((φ g : ↥J) : G) * (b : G)⁻¹ =
      ((φ (CatalogueBHigherLinearAction.slConjugation n K Y g) : ↥J) : G)
    exact hYb g
  exact not_lineJDatum_A2_actualA_of_boundary (hN := hN) (hBs := hBs) (hSC := hSC)
    (hNoTr := hNoTr) (hZ := hZ) (φ := φ) (hφ := hφ) (hker := hker)
    (hC := hC) (hCp := hCp) (hgd := hgd) (hpK := hpK) (hζ := hζ)
    (hn3 := hn3) (hY := hY) (hCardA := hCardA) (hD := hD)

theorem not_lineJDatum_A3_of_paired_gl_action
    (hN : Bs ≤ Subgroup.normalizer (J : Set G))
    (hBs : IsElemAbelian 3 Bs)
    (hSC : ∀ x ∈ Subgroup.centralizer (Bs : Set G), x ^ 3 = 1 → x ∈ Bs)
    (hNoTr : GGNoTransvection 3 Bs)
    (hZ : Nat.card ↥(Bs ⊓ J ⊓ Subgroup.centralizer (J : Set G)) ≤ 3)
    (φ : Matrix.SpecialLinearGroup (Fin n) K →* ↥J)
    (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K))
    (hn3 : 3 ≤ n) (hpK : ¬ 3 ∣ Nat.card K - 1)
    (hC : (CoordSL.rootMat g).det = 1) (hCp : (CoordSL.rootMat g) ^ 3 = 1)
    (hgd : g ∣ cyclotomic 3 K) (hζ : AdjoinRoot.root g ^ 3 = 1)
    (hYact : ∀ b : ↥Bs, ∃ Y : Matrix.GeneralLinearGroup (Fin n) K,
      ∀ g : Matrix.SpecialLinearGroup (Fin n) K,
        (b : G) * ((φ g : ↥J) : G) * (b : G)⁻¹ =
          ((φ (CatalogueBHigherLinearAction.slConjugation n K Y g) : ↥J) : G))
    (hD : GGResLineJDatum 3 Bs J .A3) : False := by
  have hY : ∀ a ∈ (ggGamma J hN).range, ∃ Y : Matrix.GeneralLinearGroup (Fin n) K,
      ∀ g : Matrix.SpecialLinearGroup (Fin n) K,
        a (φ g) = φ (CatalogueBHigherLinearAction.slConjugation n K Y g) := by
    rintro a ⟨b, rfl⟩
    obtain ⟨Y, hYb⟩ := hYact b
    refine ⟨Y, fun g => ?_⟩
    apply Subtype.ext
    change (b : G) * ((φ g : ↥J) : G) * (b : G)⁻¹ =
      ((φ (CatalogueBHigherLinearAction.slConjugation n K Y g) : ↥J) : G)
    exact hYb g
  exact not_lineJDatum_A3_actualA_of_boundary (hN := hN) (hBs := hBs) (hSC := hSC)
    (hNoTr := hNoTr) (hZ := hZ) (φ := φ) (hφ := hφ) (hker := hker)
    (hC := hC) (hCp := hCp) (hgd := hgd) (hpK := hpK) (hζ := hζ)
    (hn3 := hn3) (hY := hY) (hD := hD)


omit [Fact (Nat.Prime 3)] in
theorem card_gamma_nine_of_GGResHyp
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (J : Set G))
    (hH : GGResHyp 3 B Bs x L D J y K) :
    9 ≤ Nat.card (ggGamma J hN).range := by
  have h := GGResHyp.sq_le_card_gamma_J (p := 3) hH
  have hN' : Bs ≤ Subgroup.normalizer (J : Set G) := GGResHyp.Bs_le_normalizer_J hH
  have hsub : ggGamma J hN = ggGamma J hN' := by
    ext b
    rfl
  rw [hsub]
  simpa using h

theorem exists_actual_oppositeLinear_cover_of_marking_of_sections
    {B : Subgroup G} {x : G} {L D : Subgroup G} {y : G} {Ksub : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y Ksub)
    {r f : ℕ}
    (hMark : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.A, r, f⟩) 3 Bs J)
    (h3f : 3 ∣ 2 ^ f + 1)
    (hd3 : 3 ≤ r + 1)
    (hsec : ∀ (F : Type) [Field F] [Finite F], Nat.card F = 2 ^ f →
      CFSG.StandardType.TypeA.SLHasSections (r + 1) F) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
      Nat.card F = 2 ^ f ∧ ¬ 3 ∣ Nat.card F - 1 ∧
      ∃ φ : Matrix.SpecialLinearGroup (Fin (r + 1)) F →* ↥J,
        Function.Surjective φ ∧
        φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (r + 1)) F) ∧
        (∀ b : ↥Bs, ∃ Y : Matrix.GeneralLinearGroup (Fin (r + 1)) F,
          ∀ h : Matrix.SpecialLinearGroup (Fin (r + 1)) F,
            (b : G) * ((φ h : ↥J) : G) * (b : G)⁻¹ =
              ((φ (CatalogueBHigherLinearAction.slConjugation
                (r + 1) F Y h) : ↥J) : G)) ∧
        GGHasLabel ⟨.A, r, f⟩ (J ⧸ Subgroup.center J) := by
  classical
  have hN : Bs ≤ Subgroup.normalizer (J : Set G) := GGResHyp.Bs_le_normalizer_J hH
  obtain ⟨hperfJ, lab, _hΛ, hraw⟩ := hMark
  have hlab : lab = (⟨.A, r, f⟩ : LargeEvenLabel) := by
    obtain ⟨R, _, I, F, _hs, _hna, _θ, hEq, -⟩ := largeEvenRawDatum_exists hraw
    exact hEq
  subst lab
  have hraw0 := hraw
  dsimp only [LargeEvenRawDatum] at hraw
  obtain ⟨F, hFfield, hFfinite, hFcard, _hsimple, _hna, θ, _hEq, _hBsN, hAI⟩ := hraw
  letI : Field F := hFfield
  letI : Finite F := hFfinite
  haveI : CharP F 2 := by
    haveI : Fintype F := Fintype.ofFinite F
    refine charP_of_card_eq_prime_pow (p := 2) (f := f) ?_
    rwa [← Nat.card_eq_fintype_card]
  let d : ℕ := r + 1
  have hsecF : CFSG.StandardType.TypeA.SLHasSections d F := by
    dsimp [d]
    exact hsec F hFcard
  let e : LargeEvenProj (LargeEvenSLGroup (Fin d) F) ≃*
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL d F :=
    CFSG.StandardType.TypeA.recipeEquiv d F
  let ψ : ↥J →* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL d F :=
    e.toMonoidHom.comp (ggQuotHom θ)
  have hψ : Function.Surjective ψ :=
    e.surjective.comp (ggQuotHom_surjective θ)
  have hψker : ψ.ker ≤ Subgroup.center ↥J := by
    rw [show ψ.ker = (ggQuotHom θ).ker from
      MonoidHom.ker_comp_of_injective (ggQuotHom θ) e.toMonoidHom e.injective]
    rw [ker_ggQuotHom]
  obtain ⟨φ, hφsurj, hφcomp⟩ :=
    CFSG.StandardType.TypeA.exists_sl_cover hsecF ψ hψ hψker hperfJ
  have hkerφ : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin d) F) := by
    intro g hg
    rw [← CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center]
    have h1 := hφcomp g
    rw [MonoidHom.mem_ker] at hg
    rw [hg, map_one] at h1
    exact (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj_eq_one_iff).mp h1.symm
  have hYact : ∀ b : ↥Bs, ∃ Y : Matrix.GeneralLinearGroup (Fin d) F,
      ∀ h : Matrix.SpecialLinearGroup (Fin d) F,
        (b : G) * ((φ h : ↥J) : G) * (b : G)⁻¹ =
          ((φ (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation
              d F Y h) : ↥J) : G) := by
    intro b
    obtain ⟨φb, hφbI, hφbind⟩ := hAI (b⁻¹) (inv_mem b.2)
    obtain ⟨Y, hY⟩ := CFSG.StandardType.TypeA.congr_recipeEquiv_mem (d := d) (K := F) hφbI
    refine ⟨Y, fun h => ?_⟩
    let bN : Subgroup.normalizer (J : Set G) := ⟨b, hN b.2⟩
    let a : MulAut ↥J := J.normalizerMonoidHom bN
    let γ : MulAut (Matrix.SpecialLinearGroup (Fin d) F) :=
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d F Y
    let ψA : MulAut (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL d F) :=
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut d F Y
    have hψA : ∀ s : Matrix.SpecialLinearGroup (Fin d) F,
        ψA (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj d F s) =
          CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj d F (γ s) :=
      fun s => CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut_proj Y s
    have hind : ∀ l : ↥J, ψA (ψ l) = ψ (a l) := by
      intro l
      have hrel : ((a l : ↥J) : G) =
          ((b : ↥Bs) : G)⁻¹⁻¹ * (l : G) * ((b : ↥Bs) : G)⁻¹ := by
        simp [a, bN, normalizerMonoidHom_coe]
      have hstep : φb (θ (QuotientGroup.mk l)) = θ (QuotientGroup.mk (a l)) :=
        hφbind l (a l) hrel
      calc
        ψA (ψ l) = MulAut.congr e φb (ψ l) := by
          dsimp [ψA]
          rw [hY]
        _ = e (φb (e.symm (ψ l))) := rfl
        _ = e (φb (ggQuotHom θ l)) := by
          congr 1
          dsimp [ψ]
          rw [MulEquiv.symm_apply_apply]
        _ = e (θ (QuotientGroup.mk (a l))) := by
          rw [ggQuotHom_apply, hstep]
        _ = ψ (a l) := by
          dsimp [ψ]
          rw [ggQuotHom_apply]
    have hact : ∀ s : Matrix.SpecialLinearGroup (Fin d) F, a (φ s) = φ (γ s) :=
      CFSG.StandardType.TypeA.act_of_lift_of_mulAut (L' := ↥J) (φ := φ) (ψ := ψ)
        (hperfSL := (CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le
          (K := F) (n := d) (by dsimp [d]; exact hd3)).commutator_eq_top)
        (hker := hψker) (hφ := hφcomp) (a := a) (γ := γ) (ψA := ψA)
        (hψ := hψA) (hind := hind)
    simpa [a, bN, γ, normalizerMonoidHom_coe] using congrArg Subtype.val (hact h)
  have hFsign : ¬ 3 ∣ Nat.card F - 1 := by
    rw [hFcard]
    exact fun hdiv => not_dvd_two_pow_sub_add (by norm_num) Nat.prime_three hdiv h3f
  have hHas : GGHasLabel ⟨.A, r, f⟩ (J ⧸ Subgroup.center J) := by
    unfold GGHasLabel
    refine largeEvenRawDatum_mono ?_ hraw0
    intro R' _ I' F' hQ'
    obtain ⟨-, -, θ', -⟩ := hQ'
    exact ⟨θ'⟩
  exact ⟨F, hFfield, hFfinite, inferInstance, hFcard, hFsign, φ, hφsurj, hkerφ, hYact, hHas⟩

theorem exists_actual_oppositeLinear_cover_of_marking
    {B : Subgroup G} {x : G} {L D : Subgroup G} {y : G} {Ksub : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y Ksub)
    {r f : ℕ}
    (hMark : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.A, r, f⟩) 3 Bs J)
    (h3f : 3 ∣ 2 ^ f + 1)
    (h5 : 5 ≤ r + 1) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
      Nat.card F = 2 ^ f ∧ ¬ 3 ∣ Nat.card F - 1 ∧
      ∃ φ : Matrix.SpecialLinearGroup (Fin (r + 1)) F →* ↥J,
        Function.Surjective φ ∧
        φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (r + 1)) F) ∧
        (∀ b : ↥Bs, ∃ Y : Matrix.GeneralLinearGroup (Fin (r + 1)) F,
          ∀ h : Matrix.SpecialLinearGroup (Fin (r + 1)) F,
            (b : G) * ((φ h : ↥J) : G) * (b : G)⁻¹ =
              ((φ (CatalogueBHigherLinearAction.slConjugation
                (r + 1) F Y h) : ↥J) : G)) ∧
        GGHasLabel ⟨.A, r, f⟩ (J ⧸ Subgroup.center J) :=
  exists_actual_oppositeLinear_cover_of_marking_of_sections
    (hH := hH) (hMark := hMark) (h3f := h3f) (hd3 := by omega)
    (hsec := fun F _ _ _ => CFSG.StandardType.TypeA.slHasSections_of_five_le
      (d := r + 1) (K := F) (by omega))

section OriginalConfigurationCertificates



theorem not_lineJDatum_A2_of_GGResHyp_of_paired_gl_action_of_root_data
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {Ksub : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y Ksub)
    (φ : Matrix.SpecialLinearGroup (Fin n) K →* ↥J)
    (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K))
    (hn3 : 3 ≤ n) (hpK : ¬ 3 ∣ Nat.card K - 1)
    (hC : (CoordSL.rootMat g).det = 1) (hCp : (CoordSL.rootMat g) ^ 3 = 1)
    (hgd : g ∣ cyclotomic 3 K) (hζ : AdjoinRoot.root g ^ 3 = 1)
    (hYact : ∀ b : ↥Bs, ∃ Y : Matrix.GeneralLinearGroup (Fin n) K,
      ∀ h : Matrix.SpecialLinearGroup (Fin n) K,
        (b : G) * ((φ h : ↥J) : G) * (b : G)⁻¹ =
          ((φ (CatalogueBHigherLinearAction.slConjugation n K Y h) : ↥J) : G))
    (hD : GGResLineJDatum 3 Bs J .A2) : False := by
  have hN : Bs ≤ Subgroup.normalizer (J : Set G) := GGResHyp.Bs_le_normalizer_J hH
  exact not_lineJDatum_A2_of_paired_gl_action (hN := hN)
    (hBs := hH.1.2.1.2.1) (hSC := hH.1.2.1.2.2.2) (hNoTr := hH.2.2.2.1)
    (hZ := GGResHyp.card_bstar_inf_center_J_le hH)
    (φ := φ) (hφ := hφ) (hker := hker) (hn3 := hn3) (hpK := hpK)
    (hC := hC) (hCp := hCp) (hgd := hgd) (hζ := hζ)
    (hYact := hYact) (hCardA := card_gamma_nine_of_GGResHyp hN hH) (hD := hD)


theorem not_lineJDatum_A2_of_GGResHyp_of_paired_gl_action
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {Ksub : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y Ksub)
    (φ : Matrix.SpecialLinearGroup (Fin n) K →* ↥J)
    (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K))
    (hn3 : 3 ≤ n) (hpK : ¬ 3 ∣ Nat.card K - 1)
    (hYact : ∀ b : ↥Bs, ∃ Y : Matrix.GeneralLinearGroup (Fin n) K,
      ∀ h : Matrix.SpecialLinearGroup (Fin n) K,
        (b : G) * ((φ h : ↥J) : G) * (b : G)⁻¹ =
          ((φ (CatalogueBHigherLinearAction.slConjugation n K Y h) : ↥J) : G))
    (hD : GGResLineJDatum 3 Bs J .A2) : False := by
  obtain ⟨g', hg', hgd'⟩ := LineL2.exists_irreducible_factor_cyclotomic_three K
  let : Fact (Irreducible g') := ⟨hg'⟩
  have hp3 : ((3 : ℕ) : K) ≠ 0 :=
    TableBSymp.natCast_ne_zero_of_charTwo Nat.prime_three (by norm_num)
  have hC' : (CoordSL.rootMat g').det = 1 :=
    CoordSL.det_rootMat Nat.prime_three hpK hp3 hgd'
  have hCp' : CoordSL.rootMat g' ^ 3 = 1 :=
    CoordSL.rootMat_pow_eq_one Nat.prime_three hp3 hgd'
  have hζ' : AdjoinRoot.root g' ^ 3 = 1 :=
    (CoordSL.root_isPrimitiveRoot Nat.prime_three hp3 hgd').pow_eq_one
  exact not_lineJDatum_A2_of_GGResHyp_of_paired_gl_action_of_root_data
    (g := g') (hC := hC') (hCp := hCp') (hgd := hgd') (hζ := hζ')
    (hH := hH) (φ := φ) (hφ := hφ) (hker := hker) (hn3 := hn3)
    (hpK := hpK) (hYact := hYact) (hD := hD)

theorem not_lineJDatum_A3_of_GGResHyp_of_paired_gl_action_of_root_data
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {Ksub : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y Ksub)
    (φ : Matrix.SpecialLinearGroup (Fin n) K →* ↥J)
    (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K))
    (hn3 : 3 ≤ n) (hpK : ¬ 3 ∣ Nat.card K - 1)
    (hC : (CoordSL.rootMat g).det = 1) (hCp : (CoordSL.rootMat g) ^ 3 = 1)
    (hgd : g ∣ cyclotomic 3 K) (hζ : AdjoinRoot.root g ^ 3 = 1)
    (hYact : ∀ b : ↥Bs, ∃ Y : Matrix.GeneralLinearGroup (Fin n) K,
      ∀ h : Matrix.SpecialLinearGroup (Fin n) K,
        (b : G) * ((φ h : ↥J) : G) * (b : G)⁻¹ =
          ((φ (CatalogueBHigherLinearAction.slConjugation n K Y h) : ↥J) : G))
    (hD : GGResLineJDatum 3 Bs J .A3) : False := by
  have hN : Bs ≤ Subgroup.normalizer (J : Set G) := GGResHyp.Bs_le_normalizer_J hH
  exact not_lineJDatum_A3_of_paired_gl_action (hN := hN)
    (hBs := hH.1.2.1.2.1) (hSC := hH.1.2.1.2.2.2) (hNoTr := hH.2.2.2.1)
    (hZ := GGResHyp.card_bstar_inf_center_J_le hH)
    (φ := φ) (hφ := hφ) (hker := hker) (hn3 := hn3) (hpK := hpK)
    (hC := hC) (hCp := hCp) (hgd := hgd) (hζ := hζ)
    (hYact := hYact) (hD := hD)

theorem not_lineJDatum_A3_of_GGResHyp_of_paired_gl_action
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {Ksub : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y Ksub)
    (φ : Matrix.SpecialLinearGroup (Fin n) K →* ↥J)
    (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K))
    (hn3 : 3 ≤ n) (hpK : ¬ 3 ∣ Nat.card K - 1)
    (hYact : ∀ b : ↥Bs, ∃ Y : Matrix.GeneralLinearGroup (Fin n) K,
      ∀ h : Matrix.SpecialLinearGroup (Fin n) K,
        (b : G) * ((φ h : ↥J) : G) * (b : G)⁻¹ =
          ((φ (CatalogueBHigherLinearAction.slConjugation n K Y h) : ↥J) : G))
    (hD : GGResLineJDatum 3 Bs J .A3) : False := by
  obtain ⟨g', hg', hgd'⟩ := LineL2.exists_irreducible_factor_cyclotomic_three K
  let : Fact (Irreducible g') := ⟨hg'⟩
  have hp3 : ((3 : ℕ) : K) ≠ 0 :=
    TableBSymp.natCast_ne_zero_of_charTwo Nat.prime_three (by norm_num)
  have hC' : (CoordSL.rootMat g').det = 1 :=
    CoordSL.det_rootMat Nat.prime_three hpK hp3 hgd'
  have hCp' : CoordSL.rootMat g' ^ 3 = 1 :=
    CoordSL.rootMat_pow_eq_one Nat.prime_three hp3 hgd'
  have hζ' : AdjoinRoot.root g' ^ 3 = 1 :=
    (CoordSL.root_isPrimitiveRoot Nat.prime_three hp3 hgd').pow_eq_one
  exact not_lineJDatum_A3_of_GGResHyp_of_paired_gl_action_of_root_data
    (g := g') (hC := hC') (hCp := hCp') (hgd := hgd') (hζ := hζ')
    (hH := hH) (φ := φ) (hφ := hφ) (hker := hker) (hn3 := hn3)
    (hpK := hpK) (hYact := hYact) (hD := hD)

theorem _root_.CFSG.StandardType.GGResHyp.actual_J_not_oppositeLinear_for_A3
    {B : Subgroup G} {x : G} {L D : Subgroup G} {y : G} {Ksub : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y Ksub)
    (hD : GGResLineJDatum 3 Bs J .A3)
    (hMark : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .A ∧ 3 ∣ 2 ^ lab.n + 1) 3 Bs J) : False := by
  classical
  obtain ⟨hperfJ, lab, hΛ, hraw⟩ := hMark
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨_, _, _, _, hQ₀⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨-, -, _, hP₀⟩ := hQ₀
  have htag : tag = .A := hP₀.1.1
  have h3n : 3 ∣ 2 ^ n + 1 := hP₀.1.2
  subst htag
  have hHas : GGHasLabel ⟨.A, rank, n⟩ (J ⧸ Subgroup.center J) := by
    unfold GGHasLabel
    refine largeEvenRawDatum_mono ?_ hraw
    intro R' _ I' F' hQ'
    obtain ⟨-, -, θ', -⟩ := hQ'
    exact ⟨θ'⟩
  obtain ⟨E, hEa, hEcard⟩ := GGResHyp.exists_coroot_quotient_of_A3 hH hD
  haveI : Group.IsPerfect ↥J := ⟨hperfJ⟩
  have h3rank : 3 ≤ rank :=
    ggSmallThreeRank_linear_rank_three_of_elemAbelian (H := ↥J)
      (lab := ⟨.A, rank, n⟩) hΛ hHas hEa (by simpa [hEcard]) (Or.inl rfl)
  have hrank5 : 5 ≤ rank := by
    by_contra h
    have hrankle : rank ≤ 4 := by omega
    have hpe : ∀ j, 0 < j →
        3 * j ≤ (if (⟨.A, rank, n⟩ : LargeEvenLabel).tag = .D then 4
          else (⟨.A, rank, n⟩ : LargeEvenLabel).rank + 1) →
        ¬ 3 ∣ (2 ^ (⟨.A, rank, n⟩ : LargeEvenLabel).n) ^ j - 1 := by
      intro j hj hdj
      have hdj' : 3 * j ≤ rank + 1 := by simpa using hdj
      have hj1 : j = 1 := by omega
      subst hj1
      have hsub : ¬ 3 ∣ 2 ^ n - 1 :=
        fun hdiv => not_dvd_two_pow_sub_add (by norm_num) Nat.prime_three hdiv h3n
      simpa using hsub
    have hall := largeEvenLabelAll_card_lt_linear_of_ord (p := 3) Nat.prime_three (by norm_num)
      (lab := ⟨.A, rank, n⟩) (Or.inl ⟨rfl, le_trans (by norm_num : 2 ≤ 3) h3rank⟩) hpe
    exact not_ggHasLabel_of_elemAbelian_of_labelAll_bound
      (H := ↥J) (lab := ⟨.A, rank, n⟩)
      hHas hall hEa (by simpa [hEcard])
  have hMarkLab : GGInnerDiagOnLabel
      (fun _ l => l = (⟨.A, rank, n⟩ : LargeEvenLabel)) 3 Bs J := by
    refine ⟨hperfJ, ⟨.A, rank, n⟩, hΛ, ?_⟩
    refine largeEvenRawDatum_mono (lab := (⟨.A, rank, n⟩ : LargeEvenLabel))
      (fun R _ I F hQ => ?_) hraw
    obtain ⟨hs, hna, θ, hP⟩ := hQ
    exact ⟨hs, hna, θ, ⟨rfl, hP.2.1, hP.2.2⟩⟩
  obtain ⟨F, hFfield, hFfinite, hFchar, hFcard, hFsign, φ, hφsurj, hkerφ, hYact, _hHas'⟩ :=
    CFSG.StandardType.ResJPairedBlock.ActualA.exists_actual_oppositeLinear_cover_of_marking
      (hH := hH) (hMark := hMarkLab) (h3f := h3n) (h5 := by omega)
  letI : Field F := hFfield
  letI : Finite F := hFfinite
  letI : CharP F 2 := hFchar
  exact CFSG.StandardType.ResJPairedBlock.ActualA.not_lineJDatum_A3_of_GGResHyp_of_paired_gl_action
    (K := F) (n := rank + 1) hH φ hφsurj hkerφ (by omega) hFsign hYact hD



end OriginalConfigurationCertificates

end BoundaryA2

section ExactSigned

variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {n : ℕ} {G : Type} [Group G] [Finite G]
  {J Bs : Subgroup G}

private theorem not_three_dvd_center_specialLinear
    (hn3 : 3 ≤ n) (hpK : ¬ 3 ∣ Nat.card K - 1) :
    ¬ 3 ∣ Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K)) := by
  intro h
  exact hpK (h.trans (card_center_specialLinear_dvd (K := K) (d := n) (by omega)))

theorem not_three_dvd_center_J_of_pairedCover
    (φ : Matrix.SpecialLinearGroup (Fin n) K →* ↥J)
    (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K))
    (hn3 : 3 ≤ n) (hpK : ¬ 3 ∣ Nat.card K - 1) :
    ¬ 3 ∣ Nat.card (Subgroup.center ↥J) := by
  have hperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin n) K) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (K := K) hn3
  have hcomap : (Subgroup.center ↥J).comap φ =
      Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K) :=
    CFSG.LocalCores.comap_center_eq_of_perfect hperf φ hφ hker
  have hmap : (Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K)).map φ =
      Subgroup.center ↥J := by
    rw [← hcomap]
    exact Subgroup.map_comap_eq_self_of_surjective hφ (Subgroup.center ↥J)
  have hcard := CFSG.GorensteinWalter.card_map_eq_card_mul_card_ker φ
    (Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K))
  rw [hmap] at hcard
  have hdvd : Nat.card (Subgroup.center ↥J) ∣
      Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K)) :=
    ⟨_, hcard⟩
  intro h
  exact (not_three_dvd_center_specialLinear hn3 hpK) (h.trans hdvd)

theorem three_dvd_card_add_one_exact
    (hpK : ¬ 3 ∣ Nat.card K - 1) : 3 ∣ Nat.card K + 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨m, -, hm⟩ := FiniteField.card K 2
  have hsplit : 3 ∣ 2 ^ (m : ℕ) - 1 ∨ 3 ∣ 2 ^ (m : ℕ) + 1 := by
    have h1 : 1 ≤ 2 ^ (m : ℕ) := Nat.one_le_two_pow
    have hm3 := Nat.mod_lt (2 ^ (m : ℕ)) (show 0 < 3 by norm_num)
    have h0 : 2 ^ (m : ℕ) % 3 ≠ 0 := fun h0 =>
      absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three (Nat.dvd_of_mod_eq_zero h0))
        (by norm_num)
    omega
  rcases hsplit with h | h
  · exact absurd (by simpa [hm] using h) hpK
  · simpa [hm] using h

private theorem signedEltSC_J_of_pairedCover_exact
    (φ : Matrix.SpecialLinearGroup (Fin n) K →* ↥J)
    (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K))
    (hn3 : 3 ≤ n) (hpK : ¬ 3 ∣ Nat.card K - 1) :
    GGTorusSignedEltSC 3 ↥J := by
  have hp3 : ((3 : ℕ) : K) ≠ 0 :=
    TableBSymp.natCast_ne_zero_of_charTwo Nat.prime_three (by norm_num)
  have hpq : 3 ∣ Nat.card K + 1 := three_dvd_card_add_one_exact hpK
  have hSL : GGTorusSignedEltSC 3 (Matrix.SpecialLinearGroup (Fin n) K) :=
    ggKGLn_signedEltSC_specialLinear (K := K) (d := n) (p := 3)
      Nat.prime_three (by norm_num) hp3 hpq
  exact ggKGLn_signedEltSC_of_centralQuotient Nat.prime_three φ hφ hker
    (not_three_dvd_center_specialLinear hn3 hpK) hSL

theorem weylAut_eq_automizer_of_weyl
    {A : Subgroup (MulAut ↥J)}
    (hW : ∀ n : ↥J, MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut ↥J)) →
      GGTorusWeylElt 3 A n) :
    (ggAutomizer (MulAut.conj : ↥J →* MulAut ↥J).range A : Set (MulAut ↥A)) =
      ggTorusWeylAut 3 A := by
  ext w
  constructor
  · intro hw
    obtain ⟨c, ⟨n, rfl⟩, hcN, hvc⟩ := mem_ggAutomizer_iff.mp hw
    exact ⟨n, hcN, hW n hcN, MulEquiv.ext fun a => Subtype.ext (hvc a)⟩
  · rintro ⟨n, hn, -, rfl⟩
    exact ggConjAut_mem_ggAutomizer (MonoidHom.mem_range.mpr ⟨n, rfl⟩) hn

theorem exact_automizer_of_frame
    (hN : Bs ≤ Subgroup.normalizer (J : Set G))
    (hBs : IsElemAbelian 3 Bs)
    (hSC : ∀ x ∈ Subgroup.centralizer (Bs : Set G), x ^ 3 = 1 → x ∈ Bs)
    (hNoTr : GGNoTransvection 3 Bs)
    (hZ : Nat.card ↥(Bs ⊓ J ⊓ Subgroup.centralizer (J : Set G)) ≤ 3)
    (φ : Matrix.SpecialLinearGroup (Fin n) K →* ↥J)
    (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K))
    (hn3 : 3 ≤ n) (hpK : ¬ 3 ∣ Nat.card K - 1)
    (hJperf : commutator ↥J = ⊤)
    {g : K[X]} [Fact (Irreducible g)]
    (hC : (CoordSL.rootMat g).det = 1) (hCp : CoordSL.rootMat g ^ 3 = 1)
    (hgd : g ∣ cyclotomic 3 K)
    {s r : ℕ} {ε : Fin n ≃ (Fin (CoordSL.rootPB g).dim × Fin s) ⊕ Fin r}
    {A₀ : Matrix.SpecialLinearGroup (Fin n) K}
    (hframeA : (CoordSL.frameHom (psi φ) A₀ ε hC hCp).range =
      (ggGamma J hN).range)
    (hs3 : 3 ≤ s) :
    ∃ Θ : (Fin s → Multiplicative (ZMod 3)) ≃* ↥(ggGamma J hN).range,
      (∀ (n : ↥J) (hn : MulAut.conj n ∈
          Subgroup.normalizer ((ggGamma J hN).range : Set (MulAut ↥J))),
        SpCoord.IsSignedPerm ⇑((MulAut.congr Θ).symm (ggConjAut (ggGamma J hN).range hn))) ∧
      (∀ i : Fin s, ∃ (n : ↥J) (hn : MulAut.conj n ∈
          Subgroup.normalizer ((ggGamma J hN).range : Set (MulAut ↥J))),
        ggConjAut (ggGamma J hN).range hn = MulAut.congr Θ (sgnAut i)) ∧
      (∀ σ : Equiv.Perm (Fin s), ∃ (n : ↥J) (hn : MulAut.conj n ∈
          Subgroup.normalizer ((ggGamma J hN).range : Set (MulAut ↥J))),
        ggConjAut (ggGamma J hN).range hn = MulAut.congr Θ (permAut σ)) ∧
      Nat.card (ggAutomizer J Bs) = 2 ^ s * s.factorial := by
  classical
  let A : Subgroup (MulAut ↥J) := (ggGamma J hN).range
  let Z : Subgroup ↥J := Subgroup.center ↥J
  let R : Type := ↥J ⧸ Z
  let qZ : ↥J →* R := QuotientGroup.mk' Z
  have hqZ : Function.Surjective qZ := QuotientGroup.mk'_surjective Z
  have hkerZ : qZ.ker ≤ Subgroup.center ↥J := by
    calc qZ.ker = Z := QuotientGroup.ker_mk' Z
      _ ≤ Subgroup.center ↥J := le_rfl
  have hcpJ : ¬ 3 ∣ Nat.card Z :=
    not_three_dvd_center_J_of_pairedCover (J := J) φ hφ hker hn3 hpK
  have hSignedJ : GGTorusSignedEltSC 3 ↥J :=
    signedEltSC_J_of_pairedCover_exact (J := J) φ hφ hker hn3 hpK
  have hSignedR : GGTorusSignedEltSC 3 R :=
    ggKGLn_signedEltSC_of_centralQuotient Nat.prime_three qZ hqZ hkerZ hcpJ hSignedJ
  haveI : Group.IsPerfect ↥J := ⟨hJperf⟩
  have hZR : Subgroup.center R = ⊥ := by
    dsimp [R]
    exact Group.IsPerfect.center_quotient_center_eq_bot ↥J
  have hs2 : 2 ≤ s := by omega
  have hfinj : Function.Injective (CoordSL.frameHom (psi φ) A₀ ε hC hCp) :=
    frameHom_psi_injective (φ := φ) (hC := hC) (hCp := hCp) (A₀ := A₀) (ε := ε)
      hφ hker hgd hpK hs2
  let F : (Fin s → Multiplicative (ZMod 3)) →* ↥A :=
    (CoordSL.frameHom (psi φ) A₀ ε hC hCp).codRestrict A (fun t => by
      change (CoordSL.frameHom (psi φ) A₀ ε hC hCp t) ∈ (ggGamma J hN).range
      rw [← hframeA]
      exact ⟨t, rfl⟩)
  have hFbij : Function.Bijective F := by
    refine ⟨fun a b hab => hfinj (congrArg Subtype.val hab), fun a => ?_⟩
    have ha : (a : MulAut ↥J) ∈ (CoordSL.frameHom (psi φ) A₀ ε hC hCp).range := by
      rw [hframeA]
      exact a.2
    obtain ⟨t, ht⟩ := ha
    exact ⟨t, Subtype.ext ht⟩
  let Θframe : (Fin s → Multiplicative (ZMod 3)) ≃* ↥A :=
    MulEquiv.ofBijective F hFbij
  have hcardA : Nat.card ↥A = 3 ^ s := by
    rw [← Nat.card_congr Θframe.toEquiv]
    simp [Nat.card_fun, Nat.card_zmod]
  have hA : IsElemAbelian 3 A :=
    isElemAbelian_gammaRange (hN := hN) (φ := φ) (A₀ := A₀) (ε := ε)
      (hC := hC) (hCp := hCp) hframeA
  have hsc : GGTorusSelfCent 3 A :=
    ggTorusSelfCent_ggGamma hN hSC
  have hAI : ∀ a ∈ A, ∃ φa ∈ Set.range (MulAut.conj : R →* MulAut R),
      ∀ l : ↥J, φa (qZ l) = qZ (a l) := by
    intro a ha
    obtain ⟨x, hx⟩ := exists_conj_of_mem_gammaRange (hN := hN) (φ := φ)
      (hC := hC) (hCp := hCp) (A₀ := A₀) (ε := ε) hframeA ha
    refine ⟨MulAut.conj (qZ x), ⟨x, rfl⟩, fun l => ?_⟩
    rw [hx]
    change qZ x * qZ l * (qZ x)⁻¹ = qZ (x * l * x⁻¹)
    rw [← map_inv, ← map_mul, ← map_mul]
  have h3 : 3 ^ 3 ≤ Nat.card ↥A := by
    rw [hcardA]
    exact Nat.pow_le_pow_right (by norm_num) hs3
  obtain ⟨k, Θ, hk, hW, hS, hP, hNsp⟩ :=
    exists_signedModelSC_of_centerPrime (p := 3) (R := R)
      (I := Set.range (MulAut.conj : R →* MulAut R))
      Nat.prime_three (by norm_num) (by intro x hx; exact hx) hZR hSignedR
      (L' := ↥J) hqZ hkerZ hJperf hcpJ hA hAI h3 hsc
  have hcardAk : Nat.card ↥A = 3 ^ k := by
    rw [← Nat.card_congr Θ.toEquiv]
    simp [Nat.card_fun, Nat.card_zmod]
  have hpow : 3 ^ k = 3 ^ s := by rw [← hcardAk, hcardA]
  have hks : k = s := Nat.pow_right_injective (by norm_num : 2 ≤ 3) hpow
  subst k
  let W := ggAutomizer (MulAut.conj : ↥J →* MulAut ↥J).range A
  have hcardW : Nat.card W = 2 ^ s * s.factorial :=
    SignedPermCount.ggAutomizer_card_eq_signed_of_model (p := 3) Nat.prime_three (by norm_num)
      (L' := ↥J) (A := A) Θ hNsp hS hP
  have hWset : (W : Set (MulAut ↥A)) = ggTorusWeylAut 3 A :=
    weylAut_eq_automizer_of_weyl (A := A) hW
  let f := ggAutomizerGammaHom hN
  have hfinjGamma : Function.Injective f :=
    ggAutomizerGammaHom_injective (p := 3) Nat.prime_three hBs hNoTr hN hZ
  have hrange := ggAutomizerGammaHom_range (p := 3) hBs hSC hN
  have hsurj : Function.Surjective f := by
    intro w
    have hw : (w : MulAut ↥A) ∈ ggTorusWeylAut 3 A := by
      rw [← hWset]
      exact w.2
    have hmem : (w : MulAut ↥A) ∈ (f.range.map W.subtype : Set (MulAut ↥A)) := by
      rw [hrange]
      exact hw
    obtain ⟨c, hc, hcw⟩ := Subgroup.mem_map.mp hmem
    obtain ⟨d, hd⟩ := MonoidHom.mem_range.mp hc
    exact ⟨d, by rw [hd, Subtype.ext hcw]⟩
  have hcardOrig : Nat.card (ggAutomizer J Bs) = Nat.card W :=
    Nat.card_congr (Equiv.ofBijective f ⟨hfinjGamma, hsurj⟩)
  exact ⟨Θ, hNsp, hS, hP, hcardOrig.trans hcardW⟩

end ExactSigned

end FrameConstruction

section A2OppositeLinear

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GorensteinWalter CFSG.StandardType.Line63.H5 CFSG.Open

theorem not_lineJDatum_A2_of_actual_oppositeLinear_cover
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {Ksub : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y Ksub)
    (hD : GGResLineJDatum 3 Bs J .A2)
    {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    (φ : Matrix.SpecialLinearGroup (Fin n) F →* ↥J)
    (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) F))
    (hn3 : 3 ≤ n) (hpK : ¬ 3 ∣ Nat.card F - 1)
    (hYact : ∀ b : ↥Bs, ∃ Y : Matrix.GeneralLinearGroup (Fin n) F,
      ∀ h : Matrix.SpecialLinearGroup (Fin n) F,
        (b : G) * ((φ h : ↥J) : G) * (b : G)⁻¹ =
          ((φ (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n F Y h) : ↥J) : G))
    (hCardA : 9 ≤ Nat.card (ggGamma J (GGResHyp.Bs_le_normalizer_J hH)).range) : False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hN : Bs ≤ Subgroup.normalizer (J : Set G) := GGResHyp.Bs_le_normalizer_J hH
  have hZ : Nat.card ↥(Bs ⊓ J ⊓ Subgroup.centralizer (J : Set G)) ≤ 3 := by
    let E : Subgroup G := Bs ⊓ J ⊓ Subgroup.centralizer (J : Set G)
    have hEBs : E ≤ Bs := inf_le_left.trans inf_le_left
    have hEJ : E ≤ J := inf_le_left.trans inf_le_right
    have hcenter3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥J) :=
      not_three_dvd_center_J_of_pairedCover (J := J) (n := n) (K := F)
        φ hφ hker hn3 hpK
    let E' : Subgroup ↥J := E.subgroupOf J
    have hE'le : E' ≤ Subgroup.center ↥J := by
      intro x hx
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      have hxE : (x : G) ∈ E := Subgroup.mem_subgroupOf.mp hx
      have hxC : (x : G) ∈ Subgroup.centralizer (J : Set G) := (Subgroup.mem_inf.mp hxE).2
      exact Subgroup.mem_centralizer_iff.mp hxC (y : G) y.2
    have hE'card : Nat.card E' = Nat.card E :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEJ).toEquiv
    have hcarddvd : Nat.card E ∣ Nat.card (Subgroup.center ↥J) := by
      rw [← hE'card]
      exact Subgroup.card_dvd_of_le hE'le
    have hE3 : IsPGroup 3 E := (hH.1.2.1.2.1.mono hEBs).isPGroup
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hE3
    have hk0 : k = 0 := by
      by_contra hkne
      have hkpos : 0 < k := Nat.pos_of_ne_zero hkne
      have h3dvdE : 3 ∣ Nat.card E := by
        rw [hk]
        exact dvd_pow_self 3 (Nat.pos_iff_ne_zero.mp hkpos)
      exact hcenter3 (h3dvdE.trans hcarddvd)
    have hEcard : Nat.card E = 1 := by
      rw [hk, hk0, pow_zero]
    change Nat.card E ≤ 3
    omega
  obtain ⟨g, hg, hgd⟩ := LineL2.exists_irreducible_factor_cyclotomic_three F
  letI : Fact (Irreducible g) := ⟨hg⟩
  have hp3 : ((3 : ℕ) : F) ≠ 0 :=
    TableBSymp.natCast_ne_zero_of_charTwo Nat.prime_three (by norm_num)
  have hC : (CoordSL.rootMat g).det = 1 :=
    CoordSL.det_rootMat Nat.prime_three hpK hp3 hgd
  have hCp : (CoordSL.rootMat g) ^ 3 = 1 :=
    CoordSL.rootMat_pow_eq_one Nat.prime_three hp3 hgd
  have hζ : AdjoinRoot.root g ^ 3 = 1 :=
    (CoordSL.root_isPrimitiveRoot Nat.prime_three hp3 hgd).pow_eq_one
  exact not_lineJDatum_A2_of_paired_gl_action (hN := hN)
    (hBs := hH.1.2.1.2.1) (hSC := hH.1.2.1.2.2.2) (hNoTr := hH.2.2.2.1)
    (hZ := hZ) (φ := φ) (hφ := hφ) (hker := hker)
    (hn3 := hn3) (hpK := hpK) (hC := hC) (hCp := hCp) (hgd := hgd) (hζ := hζ)
    (hYact := hYact) (hCardA := hCardA) (hD := hD)

theorem actual_J_not_opposite_linear_for_A2_highDegree
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {Ksub : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y Ksub)
    (hD : GGResLineJDatum 3 Bs J .A2)
    {rank n : ℕ}
    (hMark : GGInnerDiagOnLabel (fun _ lab => lab = (⟨.A, rank, n⟩ : LargeEvenLabel)) 3 Bs J)
    (h3n : 3 ∣ 2 ^ n + 1) (h5 : 5 ≤ rank + 1) : False := by
  classical
  obtain ⟨F, hFfield, hFfinite, hFchar, _hFcard, hFsign, φ, hφsurj, hkerφ, hYact, _hHas⟩ :=
    exists_actual_oppositeLinear_cover_of_marking (hH := hH) (hMark := hMark)
      (h3f := h3n) (h5 := h5)
  letI : Field F := hFfield
  letI : Finite F := hFfinite
  letI : CharP F 2 := hFchar
  have hN : Bs ≤ Subgroup.normalizer (J : Set G) := GGResHyp.Bs_le_normalizer_J hH
  have hCardA : 9 ≤ Nat.card (ggGamma J hN).range := card_gamma_nine_of_GGResHyp hN hH
  exact not_lineJDatum_A2_of_actual_oppositeLinear_cover hH hD φ hφsurj hkerφ
    (by omega) hFsign hYact hCardA

theorem actual_J_not_opposite_linear_for_A2_degree4_gt_two
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {Ksub : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y Ksub)
    (hD : GGResLineJDatum 3 Bs J .A2)
    {n : ℕ}
    (hMark : GGInnerDiagOnLabel (fun _ lab => lab = (⟨.A, 3, n⟩ : LargeEvenLabel)) 3 Bs J)
    (h3n : 3 ∣ 2 ^ n + 1) (hn2 : 2 ≤ n) : False := by
  classical
  obtain ⟨F, hFfield, hFfinite, hFchar, hFcard, hFsign, φ, hφsurj, hkerφ, hYact, _hHas⟩ :=
    exists_actual_oppositeLinear_cover_of_marking_of_sections
      (hH := hH) (hMark := hMark) (h3f := h3n) (hd3 := by omega)
      (hsec := fun F _ _ hFcard => by
        refine CFSG.StandardType.TypeA.slHasSections_of_card (d := 4) (K := F)
          (by norm_num) ?_ ?_ ?_
        · intro h2
          rw [hFcard] at h2
          have h4 : 4 ≤ 2 ^ n := by
            calc 4 = 2 ^ 2 := by norm_num
              _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
          omega
        · rintro ⟨h, -⟩; omega
        · rintro ⟨-, h3⟩
          rw [hFcard] at h3
          have h2dvd : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
          omega)
  letI : Field F := hFfield
  letI : Finite F := hFfinite
  letI : CharP F 2 := hFchar
  have hN : Bs ≤ Subgroup.normalizer (J : Set G) := GGResHyp.Bs_le_normalizer_J hH
  have hCardA : 9 ≤ Nat.card (ggGamma J hN).range := card_gamma_nine_of_GGResHyp hN hH
  exact not_lineJDatum_A2_of_actual_oppositeLinear_cover hH hD φ hφsurj hkerφ
    (by omega) hFsign hYact hCardA

theorem rank_ge_three_of_oppositeLinear_of_marking
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {Ksub : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y Ksub)
    {rank n : ℕ}
    (hMark : GGInnerDiagOnLabel
      (fun _ lab => lab = (⟨.A, rank, n⟩ : LargeEvenLabel)) 3 Bs J)
    (h3n : 3 ∣ 2 ^ n + 1) : 3 ≤ rank := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hrank3
  have hrankle : rank ≤ 2 := by omega
  obtain ⟨hJperf, lab, hΛ, hraw⟩ := hMark
  obtain ⟨_, _, _, _, _, _, _, hPlab⟩ := largeEvenRawDatum_exists hraw
  have hlab : lab = (⟨.A, rank, n⟩ : LargeEvenLabel) := hPlab.1
  subst hlab
  dsimp only [LargeEvenInLambda2] at hΛ
  dsimp only [LargeEvenRawDatum] at hraw
  obtain ⟨K, hKfield, hKfinite, hKcard, hQ⟩ := hraw
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  haveI : CharP K 2 := by
    haveI : Fintype K := Fintype.ofFinite K
    refine charP_of_card_eq_prime_pow (p := 2) (f := n) ?_
    rw [← Nat.card_eq_fintype_card]
    exact hKcard
  have h3n' : 3 ∣ 2 ^ n + 1 := by
    change 3 ∣ 2 ^ n + 1 at h3n
    exact h3n
  have hKcard' : Nat.card K = 2 ^ n := by
    change Nat.card K = 2 ^ n at hKcard
    exact hKcard
  have hKmod : Nat.card K % 3 = 2 := by
    rw [hKcard']
    omega
  obtain ⟨hs, hna, θ, hP⟩ := hQ
  have hN : Bs ≤ Subgroup.normalizer (J : Set G) := hP.2.1
  have hBBs : B ≤ Bs := hH.1.2.1.1
  have hBN : B ≤ Subgroup.normalizer (J : Set G) := hBBs.trans hN
  let A : Subgroup (MulAut ↥J) := (ggGamma J hBN).range
  let R : Type := LargeEvenProj (LargeEvenSLGroup (Fin (rank + 1)) K)
  let E : Subgroup (MulAut R) := A.map (ggInducedAut θ)
  have hBea : IsElemAbelian 3 B := hH.1.2.1.2.1.mono hBBs
  have hAea : IsElemAbelian 3 A := by
    dsimp [A]
    exact isElemAbelian_range
      (fun a b : ↥B => hBea.1.is_comm.comm a b)
      (fun b : ↥B => Subtype.ext (by simpa using hBea.2 b b.2))
      (ggGamma J hBN)
  have hEea : IsElemAbelian 3 E := hAea.map (ggInducedAut θ)
  have hEcard : Nat.card E = Nat.card A := by
    dsimp [E]
    exact Subgroup.card_map_of_injective (ggInducedAut_injective_of_perfect hJperf θ)
  have hAcard : Nat.card A = 3 ^ (LargeEvenTwoLocalRank 3 G - 2) := by
    simpa [A] using hH.1.card_range_gamma_B_J hBN
  have hm4 : 4 ≤ LargeEvenTwoLocalRank 3 G :=
    hH.1.1.2.2.2.2.2.1.2.2.2
  have h9E : 9 ≤ Nat.card E := by
    rw [hEcard, hAcard]
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ (LargeEvenTwoLocalRank 3 G - 2) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
  have hEI : (E : Set (MulAut R)) ⊆
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin (rank + 1)) K)) Set.univ := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨b, rfl⟩ := ha
    have hmem := ggBeta_mem J θ hBN (fun b hb => hP.2.2 b (hBBs hb)) b
    have hbeta : ggBeta J θ hBN b = ggInducedAut θ (ggGamma J hBN b) := by
      rw [ggBeta_eq, ggLAut_eq_ggInducedAut]
      rfl
    rwa [hbeta] at hmem
  let eR : R ≃* projectiveSL (rank + 1) K := TypeA.recipeEquiv (rank + 1) K
  let E' : Subgroup (MulAut (projectiveSL (rank + 1) K)) :=
    E.map (MulAut.congr eR).toMonoidHom
  have hE'ea : IsElemAbelian 3 E' := hEea.map (MulAut.congr eR).toMonoidHom
  have hE'card : Nat.card E' = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.congr eR).injective
  have hE'range : (E' : Set (MulAut (projectiveSL (rank + 1) K))) ⊆
      Set.range (conjAut (rank + 1) K) := by
    rintro _ ⟨φ, hφE, rfl⟩
    exact TypeA.congr_recipeEquiv_mem (hEI hφE)
  have hE'9 : 9 ≤ Nat.card E' := by rw [hE'card]; exact h9E
  have hE'exp : ∀ x ∈ E', x ^ 3 = 1 := hE'ea.2
  rcases Nat.lt_or_ge rank 2 with hlt | hge
  · have hrank1 : rank = 1 := by
      have h1 : 1 ≤ rank := hΛ.2.1
      omega
    have hn2' : rank = 1 → 2 ≤ n := hΛ.2.2
    subst hrank1
    have hn2 : 2 ≤ n := hn2' rfl
    have hK4 : 4 ≤ Nat.card K := by
      rw [hKcard']
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    let ePSL : PSL2 K ≃* projectiveSL 2 K :=
      CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 2 K
    have hcyc : ∀ Q : Sylow 3 (projectiveSL 2 K), IsCyclic Q :=
      CFSG.RankThree.PartTwo.Sec11.isCyclic_sylow_of_mulEquiv_of_isCyclic
        ePSL.symm (CFSG.RankThree.PartTwo.KFacts.isCyclic_sylow_three_psl2
          (F := K) (by rw [ringChar.eq K 2]; norm_num) hK4)
    have hZ : Subgroup.center (projectiveSL 2 K) = ⊥ :=
      CFSG.ComponentClassification.OddSelector.center_projectiveSL_two_eq_bot hK4
    have hE'le : E' ≤ (MulAut.conj : projectiveSL 2 K →* MulAut (projectiveSL 2 K)).range := by
      intro x hx
      have hxlin : x ∈ linearAutGroup 2 K := by
        rw [linearAutGroup_eq_range]
        exact hE'range hx
      exact mem_range_conj_of_mem_linearAutGroup_of_coprime
        hxlin (by norm_num) (hE'exp x hx)
    have hle : Nat.card E' ≤ 3 :=
      CFSG.RankThree.PartTwo.Sec4.RonanEps.card_le_three_of_le_inn
        (X := projectiveSL 2 K) hcyc hZ hE'le hE'exp
    omega
  · have hrank2 : rank = 2 := by omega
    subst hrank2
    obtain ⟨eP⟩ := CFSG.RankThree.PartTwo.KFacts.nonempty_projSL_mulEquiv 3 K
    have hcyc : ∀ Q : Sylow 3 (projectiveSL 3 K), IsCyclic Q := by
      intro Q
      exact CFSG.RankThree.PartTwo.KFacts.isCyclic_sylow_three_of_mulEquiv_projSL
        (K := K) hKmod eP.symm Q
    have hZ : Subgroup.center (projectiveSL 3 K) = ⊥ :=
      CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot (k := K) (n := 3) (by norm_num)
    have hE'le : E' ≤ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range := by
      intro x hx
      have hxlin : x ∈ linearAutGroup 3 K := by
        rw [linearAutGroup_eq_range]
        exact hE'range hx
      exact CFSG.RankThree.PartTwo.Sec4.RonanEps.mem_range_conj_of_mem_linearAutGroup
        (F := K) hKmod hxlin
    have hle : Nat.card E' ≤ 3 :=
      CFSG.RankThree.PartTwo.Sec4.RonanEps.card_le_three_of_le_inn
        (X := projectiveSL 3 K) hcyc hZ hE'le hE'exp
    omega


theorem actual_J_not_opposite_linear_for_A2_except_qTwo
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {Ksub : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y Ksub)
    (hD : GGResLineJDatum 3 Bs J .A2)
    {r n : ℕ}
    (hMark : GGInnerDiagOnLabel
      (fun _ lab => lab = (⟨.A, r, n⟩ : LargeEvenLabel)) 3 Bs J)
    (h3n : 3 ∣ 2 ^ n + 1)
    (hnot : ¬ (r = 3 ∧ n = 1)) : False := by
  classical
  have hMarkKeep := hMark
  obtain ⟨hperf, lab, hΛ, hraw⟩ := hMark
  obtain ⟨_, _, _, _, _, _, _, hPlab⟩ := largeEvenRawDatum_exists hraw
  have hlab : lab = (⟨.A, r, n⟩ : LargeEvenLabel) := hPlab.1
  subst hlab
  dsimp only [LargeEvenInLambda2] at hΛ
  have h3r : 3 ≤ r :=
    rank_ge_three_of_oppositeLinear_of_marking hH hMarkKeep h3n
  rcases Nat.lt_or_ge r 3 with hlt | hge
  · omega
  rcases Nat.lt_or_ge r 4 with hlt4 | hge4
  · have hr3 : r = 3 := by omega
    subst hr3
    have hn1 : n ≠ 1 := by
      intro hn
      exact hnot ⟨rfl, hn⟩
    have hn2 : 2 ≤ n := by
      have h1 : 1 ≤ n := hΛ.1
      omega
    exact actual_J_not_opposite_linear_for_A2_degree4_gt_two hH hD hMarkKeep h3n hn2
  · exact actual_J_not_opposite_linear_for_A2_highDegree hH hD hMarkKeep h3n (by omega)


private theorem exists_alt8_and_center_two_of_A3_one
    {Bs : Subgroup G} {J : Subgroup G}
    (hMark : GGInnerDiagOnLabel
      (fun _ lab => lab = (⟨.A, 3, 1⟩ : LargeEvenLabel)) 3 Bs J) :
    ∃ eJ : (↥J ⧸ Subgroup.center ↥J) ≃* alternatingGroup (Fin 8),
      IsPGroup 2 (Subgroup.center ↥J) := by
  classical
  obtain ⟨hperfJ, lab, hΛ, hraw⟩ := hMark
  have hlab : lab = (⟨.A, 3, 1⟩ : LargeEvenLabel) := by
    obtain ⟨R, _, I, F, _hs, _hna, _θ, hEq, -⟩ := largeEvenRawDatum_exists hraw
    exact hEq
  subst hlab
  have hΛ3 : LargeEvenInLambda2 (⟨.A, 3, 1⟩ : LargeEvenLabel) := hΛ
  have hHas : GGHasLabel (⟨.A, 3, 1⟩ : LargeEvenLabel)
      (↥J ⧸ Subgroup.center ↥J) := by
    unfold GGHasLabel
    refine largeEvenRawDatum_mono ?_ hraw
    intro R' _ I' F' hQ'
    obtain ⟨-, -, θ', -⟩ := hQ'
    exact ⟨θ'⟩
  have hmodel : StatedClassicalModel (↥J ⧸ Subgroup.center ↥J) .PSL 4 2 1 :=
    statedClassicalModel_of_hasLabel_typeA (n := 3) (f := 1) hΛ3 hHas
  obtain ⟨eQ⟩ := CFSG.CGT.PushingUpLit.CGT6.nonempty_mulEquiv_alt_eight_of_psl_four_two hmodel
  refine ⟨eQ, ?_⟩
  let A8 := alternatingGroup (Fin 8)
  have hcardH : Nat.card
      (CFSG.RankThree.PerfectCover.hopfMultiplier A8) = 2 :=
    CFSG.Alternating.Multipliers.card_hopfMultiplier_alternatingGroup (n := 8) (by norm_num)
  have hcardG : Nat.card (CFSG.Open.griessHopfMultiplier A8) = 2 := by
    rw [Nat.card_congr
      (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess A8).toEquiv]
    exact hcardH
  have hcommA8 : commutator A8 = ⊤ := by
    haveI : Group.IsPerfect A8 :=
      ⟨commutator_alternatingGroup_eq_top (by norm_num)⟩
    exact Group.IsPerfect.commutator_eq_top
  have hTwo : CFSG.OddTranspositions.PartThree.CentralKernelTwoGroup A8 :=
    CFSG.OddTranspositions.PartThree.centralKernelTwoGroup_of_hopfMultiplier
      (X := A8) hcommA8 (m := 1) (by rw [hcardG]; norm_num)
  let q : ↥J →* (↥J ⧸ Subgroup.center ↥J) :=
    QuotientGroup.mk' (Subgroup.center ↥J)
  let φ : ↥J →* A8 := eQ.toMonoidHom.comp q
  have hφsurj : Function.Surjective φ :=
    eQ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hφker : φ.ker = Subgroup.center ↥J := by
    rw [MonoidHom.ker_comp_of_injective q eQ.toMonoidHom eQ.injective]
    exact QuotientGroup.ker_mk' _
  have hker2 : IsPGroup 2 φ.ker :=
    hTwo ↥J φ hφsurj (by rw [hφker])
      (by rw [hφker, hperfJ]; exact le_top)
  rwa [hφker] at hker2


private theorem center_le_twoCenter_of_isPGroup_two
    (hZ : IsPGroup 2 (Subgroup.center ↥J)) :
    (Subgroup.center ↥J).map J.subtype ≤ twoCenter J := by
  rintro z ⟨c, hc, rfl⟩
  refine ⟨c.2, ?_, ?_⟩
  · intro l hl
    have h := Subgroup.mem_center_iff.mp hc ⟨l, hl⟩
    exact (congrArg Subtype.val h).symm
  · obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hZ ⟨c, hc⟩
    have hk' : orderOf c = 2 ^ k := by
      rw [← Subgroup.orderOf_mk c hc]
      exact hk
    haveI : Fintype ↥J := Fintype.ofFinite _
    have hdvdJ : orderOf c ∣ Nat.card ↥J := by
      simpa only [Nat.card_eq_fintype_card] using
        orderOf_dvd_card (G := ↥J) (x := c)
    have hleJ : orderOf c ≤ Nat.card ↥J := Nat.le_of_dvd Nat.card_pos hdvdJ
    have hleG : orderOf c ≤ Nat.card G :=
      hleJ.trans (Subgroup.card_le_card_group J)
    have hkG : k ≤ Nat.card G := by
      rw [hk'] at hleG
      have hklt : k < 2 ^ k := Nat.lt_two_pow_self
      omega
    have hdvd : orderOf c ∣ 2 ^ Nat.card G := by
      rw [hk']
      exact pow_dvd_pow 2 hkG
    have hdvdG : orderOf (J.subtype c) ∣ 2 ^ Nat.card G := by
      show orderOf (c : G) ∣ 2 ^ Nat.card G
      rw [Subgroup.orderOf_coe]
      exact hdvd
    exact orderOf_dvd_iff_pow_eq_one.mp hdvdG


theorem actual_J_not_opposite_linear_for_A2_qTwo
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {Ksub : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y Ksub)
    (hD : GGResLineJDatum 3 Bs J .A2)
    (hMark : GGInnerDiagOnLabel
      (fun _ lab => lab = (⟨.A, 3, 1⟩ : LargeEvenLabel)) 3 Bs J) : False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨eJ, hZ2⟩ := exists_alt8_and_center_two_of_A3_one hMark
  let N : Subgroup G := Subgroup.normalizer (J : Set G)
  have hN : Bs ≤ N := GGResHyp.Bs_le_normalizer_J hH
  let Bbar : Subgroup (RedGrp J) := (redMkB hN).range
  let Jbar : Subgroup (RedGrp J) := (redMkL J).range
  have hDbar : GGResLineJDatum 3 Bbar Jbar .A2 :=
    GGResHyp.lineJDatum_red hH hD
  have hcardA : Nat.card (ggAutomizer Jbar Bbar) = 6 :=
    ggAutomizer_card_of_lineJDatum_A2 (p := 3) rfl hDbar
  have hBsE : CFSG.Open.IsElemAbelian 3 Bbar :=
    isElemAbelian_redB hN hH.1.2.1.2.1
  have hBsP : IsPGroup 3 Bbar := hBsE.isPGroup
  have hNoTr : GGNoTransvection 3 Bbar :=
    noTransvection_red hN hH.1.2.1.2.1 hH.2.2.2.1
  let qbar : ↥J →* Jbar := (redMkL J).rangeRestrict
  have hqbar : Function.Surjective qbar := MonoidHom.rangeRestrict_surjective _
  have hker : qbar.ker = Subgroup.center ↥J := by
    rw [MonoidHom.ker_rangeRestrict]
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      exact mem_center_of_mem_twoCenter ((redMkL_eq_one_iff J x).mp hx)
    · intro hx
      exact (redMkL_eq_one_iff J x).mpr
        (center_le_twoCenter_of_isPGroup_two hZ2 ⟨x, hx, rfl⟩)
  let eZ : (↥J ⧸ Subgroup.center ↥J) ≃* Jbar :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective qbar hqbar)
  let eJbar : Jbar ≃* alternatingGroup (Fin 8) := eZ.symm.trans eJ
  have hZbot : Subgroup.center Jbar = ⊥ :=
    CFSG.Quasithin.H13.Lem8.center_eq_bot_of_mulEquiv eJbar
      (CFSG.Quasithin.H13.Lem8.center_alternatingGroup_eq_bot (by norm_num))
  have hNbar : Bbar ≤ Subgroup.normalizer (Jbar : Set (RedGrp J)) := by
    haveI : Jbar.Normal := redL_normal (L := J)
    intro z _
    rw [Subgroup.normalizer_eq_top Jbar]
    exact Subgroup.mem_top z
  have hZ : Nat.card ↥(Bbar ⊓ Jbar ⊓
      Subgroup.centralizer (Jbar : Set (RedGrp J))) ≤ 3 := by
    have hbot : Bbar ⊓ Jbar ⊓ Subgroup.centralizer (Jbar : Set (RedGrp J)) = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      obtain ⟨hzBJ, hzC⟩ := Subgroup.mem_inf.mp hz
      obtain ⟨-, hzJ⟩ := Subgroup.mem_inf.mp hzBJ
      have hzZ : (⟨z, hzJ⟩ : Jbar) ∈ Subgroup.center Jbar := by
        rw [Subgroup.mem_center_iff]
        intro y
        apply Subtype.ext
        exact Subgroup.mem_centralizer_iff.mp hzC (y : RedGrp J) y.2
      rw [hZbot] at hzZ
      have hz1 : (⟨z, hzJ⟩ : Jbar) = 1 := by simpa using hzZ
      exact Subtype.ext_iff.mp hz1
    rw [hbot]
    simp
  let InnJ : Subgroup (MulAut Jbar) := (MulAut.conj : Jbar →* MulAut Jbar).range
  let A : Subgroup (MulAut Jbar) := (ggGamma Jbar hNbar).range
  let H : Subgroup (MulAut Jbar) :=
    Subgroup.normalizer (A : Set (MulAut Jbar)) ⊓ InnJ
  have hAinn : A ≤ InnJ := by
    rintro φ ⟨b, rfl⟩
    have hb3 : b ^ 3 = 1 := by
      apply Subtype.ext
      simpa using hBsE.2 (b : RedGrp J) b.2
    have hφ3 : ggGamma Jbar hNbar b ^ 3 = 1 := by
      calc ggGamma Jbar hNbar b ^ 3 = ggGamma Jbar hNbar (b ^ 3) := (map_pow _ b 3).symm
        _ = ggGamma Jbar hNbar 1 := by rw [hb3]
        _ = 1 := map_one _
    exact CFSG.HardMathSupport.Dickson.Sec6.I1431.isInnerAut_of_alt
      (by simp : 5 ≤ Nat.card (Fin 8)) eJbar hφ3
  have hA3P : IsPGroup 3 A := by
    have h := (hBsP.to_subgroup (⊤ : Subgroup Bbar)).map (ggGamma Jbar hNbar)
    have hAeq : Subgroup.map (ggGamma Jbar hNbar) (⊤ : Subgroup Bbar) = A := by
      change Subgroup.map (ggGamma Jbar hNbar) ⊤ = (ggGamma Jbar hNbar).range
      exact (MonoidHom.range_eq_map _).symm
    rwa [hAeq] at h
  have hA_H : A ≤ H := le_inf (Subgroup.le_normalizer) hAinn
  have hconj_ker : (MulAut.conj : Jbar →* MulAut Jbar).ker = Subgroup.center Jbar := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
    constructor
    · intro h z
      have hz := congrArg (fun φ : MulAut Jbar => φ z) h
      rw [MulAut.conj_apply, MulAut.one_apply] at hz
      have hgz : g * z = z * g := by
        calc g * z = (g * z * g⁻¹) * g := by group
          _ = z * g := by rw [hz]
      exact hgz.symm
    · intro h
      apply MulEquiv.ext
      intro z
      rw [MulAut.conj_apply, MulAut.one_apply]
      have hz : z * g = g * z := h z
      calc g * z * g⁻¹ = (z * g) * g⁻¹ := by rw [← hz]
        _ = z := by group
  have hconj_inj : Function.Injective (MulAut.conj : Jbar →* MulAut Jbar) :=
    (MonoidHom.ker_eq_bot_iff _).mp (by rw [hconj_ker, hZbot])
  let eInn : InnJ ≃* alternatingGroup (Fin 8) :=
    (MonoidHom.ofInjective hconj_inj).symm.trans eJbar
  have hAbH : ∀ P : Subgroup ↥H, IsPGroup 3 P → IsMulCommutative P := by
    intro P hP
    let ψ : ↥H →* alternatingGroup (Fin 8) :=
      eInn.toMonoidHom.comp (Subgroup.inclusion (show H ≤ InnJ from inf_le_right))
    have hψinj : Function.Injective ψ :=
      eInn.injective.comp (Subgroup.inclusion_injective (show H ≤ InnJ from inf_le_right))
    let P' : Subgroup (alternatingGroup (Fin 8)) := P.map ψ
    have hP' : IsPGroup 3 P' := hP.map ψ
    have hea : IsElemAbelian 3 P' := CFSG.AGLEmbedding.isElemAbelian_alt_eight P' hP'
    let eP : P ≃* P' := Subgroup.equivMapOfInjective P ψ hψinj
    exact IsMulCommutative.of_comm fun a b =>
      eP.injective (by
        rw [map_mul, map_mul]
        exact hea.1.is_comm.comm (eP a) (eP b))
  let EH : Subgroup ↥H := A.subgroupOf H
  have hEH3 : IsPGroup 3 EH := hA3P.comap_subtype
  have hEHnormal : EH.Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hA_H]
    exact inf_le_left
  have : EH.Normal := hEHnormal
  let incl : ↥H →* ↥(Subgroup.normalizer (EH : Set ↥H)) :=
    { toFun := fun h =>
        ⟨h, Subgroup.le_normalizer_of_normal (H := EH) (K := ⊤) (Subgroup.mem_top h)⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl }
  let f : ↥H →* MulAut ↥EH := EH.normalizerMonoidHom.comp incl
  have hf : ∀ (h : ↥H) (z : ↥EH), ((f h z : ↥EH) : ↥H) = h * z * h⁻¹ := by
    intro h z
    change ((EH.normalizerMonoidHom (incl h) z : ↥EH) : ↥H) = h * z * h⁻¹
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    rfl
  have hndvd : ¬ 3 ∣ Nat.card f.range :=
    CFSG.GroupTheory.not_dvd_card_range_of_conj_action hEH3 hAbH f hf
  have hfrange : f.range = ggAutomizer (⊤ : Subgroup ↥H) EH := by
    rw [ggAutomizer_eq]
    ext φ
    constructor
    · rintro ⟨h, rfl⟩
      refine ⟨(h : ↥H), Subgroup.mem_top _, ?_, ?_⟩
      · exact Subgroup.le_normalizer_of_normal (H := EH) (K := ⊤) (Subgroup.mem_top h)
      · intro z
        exact hf h z
    · rintro ⟨g, -, hgN, hφ⟩
      refine ⟨g, ?_⟩
      apply MulEquiv.ext
      intro z
      apply Subtype.ext
      rw [hf]
      exact (hφ z).symm
  have hInd : ggInduced H A = ggInduced InnJ A := by
    ext φ
    constructor
    · rintro ⟨g, hgH, hgN, hφ⟩
      exact ⟨g, (Subgroup.mem_inf.mp hgH).2, hgN, hφ⟩
    · rintro ⟨g, hgInn, hgN, hφ⟩
      exact ⟨g, Subgroup.mem_inf.mpr ⟨hgN, hgInn⟩, hgN, hφ⟩
  have hAutoHA : ggAutomizer H A = ggAutomizer InnJ A := by
    rw [ggAutomizer_eq, ggAutomizer_eq]
    exact Subgroup.ext fun φ => by
      change φ ∈ ggInduced H A ↔ φ ∈ ggInduced InnJ A
      rw [hInd]
  have hmapEH : EH.map H.subtype = A := by
    ext a
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact hu
    · intro ha
      exact ⟨⟨a, hA_H ha⟩, ha, rfl⟩
  have htopmap : (⊤ : Subgroup ↥H).map H.subtype = H := by
    ext a
    constructor
    · rintro ⟨u, -, rfl⟩
      exact u.2
    · intro ha
      exact ⟨⟨a, ha⟩, Subgroup.mem_top _, rfl⟩
  have hmapAuto :=
    CFSG.StandardType.F4AutWeyl.ggAutomizer_map_eq (f := H.subtype) H.subtype_injective
      (⊤ : Subgroup ↥H) EH hmapEH
  rw [htopmap] at hmapAuto
  have hcard : Nat.card (ggAutomizer InnJ A) =
      Nat.card ((ggAutomizer (⊤ : Subgroup ↥H) EH).map
        (MulAut.congr ((EH.equivMapOfInjective H.subtype H.subtype_injective).trans
          (MulEquiv.subgroupCongr hmapEH))).toMonoidHom) := by
    rw [← hAutoHA, hmapAuto]
  have hdvd : Nat.card (ggAutomizer Jbar Bbar) ∣ Nat.card (ggAutomizer InnJ A) :=
    card_ggAutomizer_dvd_gamma (p := 3) Nat.prime_three hBsE hNoTr hNbar hZ
  have h3AJ : 3 ∣ Nat.card (ggAutomizer Jbar Bbar) := by
    rw [hcardA]
    norm_num
  have h3AInn : 3 ∣ Nat.card (ggAutomizer InnJ A) := h3AJ.trans hdvd
  rw [hcard] at h3AInn
  rw [Subgroup.card_map_of_injective (MulAut.congr _).injective] at h3AInn
  rw [← hfrange] at h3AInn
  exact hndvd h3AInn


private theorem exists_exactMarking_of_A_marking
    {Bs : Subgroup G} {J : Subgroup G}
    (hMark : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .A ∧ 3 ∣ 2 ^ lab.n + 1) 3 Bs J) :
    ∃ r n, GGInnerDiagOnLabel
      (fun _ lab => lab = (⟨.A, r, n⟩ : LargeEvenLabel)) 3 Bs J ∧
      3 ∣ 2 ^ n + 1 := by
  classical
  obtain ⟨hperf, lab, hΛ, hraw⟩ := hMark
  obtain ⟨R, hR, I, F, hsimple, hna, θ, hS, hN, hAI⟩ := largeEvenRawDatum_exists hraw
  cases lab with
  | mk tag rank nn =>
    obtain ⟨htag, hdiv⟩ := hS
    subst htag
    let r := rank
    let n := nn
    refine ⟨r, n, ?_, hdiv⟩
    refine ⟨hperf, (⟨.A, r, n⟩ : LargeEvenLabel), hΛ, ?_⟩
    have hrawC : LargeEvenRawDatum (⟨.A, r, n⟩ : LargeEvenLabel) _ := hraw
    refine largeEvenRawDatum_mono (Q' := fun R _ I F =>
      IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        ∃ θ : (↥J ⧸ Subgroup.center ↥J) ≃* R,
          ((⟨.A, r, n⟩ : LargeEvenLabel) = ⟨.A, r, n⟩) ∧
            Bs ≤ Subgroup.normalizer (J : Set G) ∧
            ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ
              (fun l l' => (l' : G) = b⁻¹ * l * b) φ) ?_ hrawC
    intro R _ I F hP
    obtain ⟨hs, hna, θ, hPold⟩ := hP
    exact ⟨hs, hna, θ, rfl, hPold.2.1, hPold.2.2⟩

theorem actual_J_not_opposite_linear_for_A2
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {Ksub : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y Ksub)
    (hD : GGResLineJDatum 3 Bs J .A2)
    (hMark : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .A ∧ 3 ∣ 2 ^ lab.n + 1) 3 Bs J) : False := by
  obtain ⟨r, n, hMarkExact, h3n⟩ := exists_exactMarking_of_A_marking hMark
  by_cases hq : r = 3 ∧ n = 1
  · obtain ⟨rfl, rfl⟩ := hq
    exact actual_J_not_opposite_linear_for_A2_qTwo hH hD hMarkExact
  · exact actual_J_not_opposite_linear_for_A2_except_qTwo hH hD hMarkExact h3n hq

end A2OppositeLinear

end ActualA

end ResJPairedBlock
end CFSG.StandardType

namespace CFSG.StandardType

open CFSG.Assembly

section Certificates


private theorem a3MarkingMono {G : Type} [Group G] {Bs J : Subgroup G}
    {lab0 : LargeEvenLabel}
    (hMark : GGInnerDiagOnLabel (fun _ lab => lab = lab0) 3 Bs J)
    {S : ℕ → LargeEvenLabel → Prop} (hS : S 3 lab0) :
    GGInnerDiagOnLabel S 3 Bs J :=
  GGInnerDiagOnLabel.mono_label (S := fun _ lab => lab = lab0) (T := S)
    (fun lab hlab => by rw [hlab]; exact hS) hMark

private theorem exists_lineJLabel_A3_of_actual_label
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    [Fact (Nat.Prime 3)]
    (hH : GGResHyp 3 B Bs x L D J y K) (hD : GGResLineJDatum 3 Bs J .A3)
    (lab0 : LargeEvenLabel) (hΛ0 : LargeEvenInLambda2 lab0)
    (hHas0 : GGHasLabel lab0 (J ⧸ Subgroup.center J))
    (hMark0 : GGInnerDiagOnLabel (fun _ lab => lab = lab0) 3 Bs J) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧
      ggResLineJLabel .A3 lab ∧ GGHasLabel lab (J ⧸ Subgroup.center J) := by
  classical
  obtain ⟨tag, rank, n⟩ := lab0
  have hΛ0' : LargeEvenInLambda2 (⟨tag, rank, n⟩ : LargeEvenLabel) := hΛ0
  cases tag
  ·
    rcases ggThree_dvd_two_pow_sub_or_add n with hminus | hplus
    · by_cases hrank3 : rank = 3
      · subst hrank3
        exact ⟨⟨.A, 3, n⟩, hΛ0', Or.inl ⟨Or.inl rfl, rfl, hminus⟩, hHas0⟩
      · exact ResJCubicBlock.GGResHyp.exists_lineJLabel_A3_of_compatible_splitLinear_marking hH hD
          (a3MarkingMono hMark0
            (S := fun _ lab => lab.tag = .A ∧ 3 ∣ 2 ^ lab.n - 1) ⟨rfl, hminus⟩)
    · exact False.elim (GGResHyp.actual_J_not_oppositeLinear_for_A3 hH hD
        (a3MarkingMono hMark0
          (S := fun _ lab => lab.tag = .A ∧ 3 ∣ 2 ^ lab.n + 1) ⟨rfl, hplus⟩))
  ·
    have h3rank : 3 ≤ rank :=
      GGResHyp.rank_ge_three_of_A3_label hH hD hΛ0' hHas0 (Or.inr rfl)
    rcases ggThree_dvd_two_pow_sub_or_add n with hminus | hplus
    · exact False.elim (GGResHyp.actual_J_not_opposite_unitary_for_A3 hH hD
        (a3MarkingMono hMark0
          (S := fun _ lab => lab.tag = .twA ∧ 3 ∣ 2 ^ lab.n - 1) ⟨rfl, hminus⟩))
    · by_cases hrank3 : rank = 3
      · subst hrank3
        exact ⟨⟨.twA, 3, n⟩, hΛ0', Or.inr ⟨Or.inl rfl, rfl, hplus⟩, hHas0⟩
      · have hrank4 : 4 ≤ rank := by omega
        by_cases hdiv : 3 ∣ rank + 1
        · by_cases hrank5 : rank = 5
          · subst hrank5
            by_cases hn1 : n = 1
            · subst hn1
              exact False.elim (GGResHyp.actual_J_not_unitary_six_two_for_A3 hH hD
                (a3MarkingMono hMark0
                  (S := fun _ lab => lab = (⟨.twA, 5, 1⟩ : LargeEvenLabel)) rfl))
            · exact False.elim (GGResHyp.actual_J_not_unitary_six_for_A3_qplus_large hH hD
                (a3MarkingMono hMark0
                  (S := fun _ lab => lab.tag = .twA ∧ lab.rank = 5 ∧
                    3 ∣ 2 ^ lab.n + 1 ∧ lab.n ≠ 1) ⟨rfl, rfl, hplus, hn1⟩))
          · have h9 : 9 ≤ rank + 1 := by
              obtain ⟨k, hk⟩ := hdiv
              have hk3 : 3 ≤ k := by
                rcases k with _ | _ | _ | k
                · omega
                · omega
                · omega
                · omega
              omega
            exact False.elim (GGResHyp.actual_J_not_unitary_highDiv_for_A3 hH hD
              (a3MarkingMono hMark0
                (S := fun _ lab => lab.tag = .twA ∧ 3 ∣ 2 ^ lab.n + 1 ∧
                  3 ∣ lab.rank + 1 ∧ 9 ≤ lab.rank + 1) ⟨rfl, hplus, hdiv, h9⟩))
        · exact GGResHyp.exists_lineJLabel_A3_of_compatible_unitary_marking_coprime hH hD
            (a3MarkingMono hMark0
              (S := fun _ lab => lab.tag = .twA ∧ 3 ∣ 2 ^ lab.n + 1 ∧
                ¬ 3 ∣ lab.rank + 1) ⟨rfl, hplus, hdiv⟩)
  ·
    exact False.elim (GGResHyp.actual_J_not_B_or_C_for_A3 hH hD
      (a3MarkingMono hMark0
        (S := fun _ lab => lab.tag = .B ∨ lab.tag = .C) (Or.inl rfl)))
  ·
    exact False.elim (GGResHyp.actual_J_not_B_or_C_for_A3 hH hD
      (a3MarkingMono hMark0
        (S := fun _ lab => lab.tag = .B ∨ lab.tag = .C) (Or.inr rfl)))
  ·
    rcases ggThree_dvd_two_pow_sub_or_add n with hminus | hplus
    · by_cases hrank3 : rank = 3
      · subst hrank3
        exact ⟨⟨.D, 3, n⟩, hΛ0', Or.inl ⟨Or.inr rfl, rfl, hminus⟩, hHas0⟩
      · have hrank4 : 4 ≤ rank := by
          have h3rank : 3 ≤ rank := by
            simpa only [LargeEvenInLambda2] using hΛ0'.2
          omega
        exact False.elim (GGResHyp.actual_J_not_D_high_or_twD_split_for_A3 hH hD
          (a3MarkingMono hMark0
            (S := fun _ lab => 3 ∣ 2 ^ lab.n - 1 ∧
              ((lab.tag = .D ∧ 4 ≤ lab.rank) ∨ (lab.tag = .twD ∧ 4 ≤ lab.rank)))
            ⟨hminus, Or.inl ⟨rfl, hrank4⟩⟩))
    · by_cases hrank3 : rank = 3
      · subst hrank3
        have hMarkA : GGInnerDiagOnLabel
            (fun _ lab => lab.tag = .A ∧ 3 ∣ 2 ^ lab.n + 1) 3 Bs J := by
          have hD3 : GGInnerDiagOnLabel
              (fun _ lab => lab.tag = .D ∧ lab.rank = 3 ∧ 3 ∣ 2 ^ lab.n + 1) 3 Bs J :=
            a3MarkingMono hMark0 ⟨rfl, rfl, hplus⟩
          exact GGInnerDiagOnLabel.mono_label
            (S := fun _ lab => lab.tag = .A ∧ lab.rank = 3 ∧ 3 ∣ 2 ^ lab.n + 1)
            (T := fun _ lab => lab.tag = .A ∧ 3 ∣ 2 ^ lab.n + 1)
            (fun lab h => ⟨h.1, h.2.2⟩)
            (ggInnerDiagOnLabel_D3_to_A3 (S := fun n => 3 ∣ 2 ^ n + 1) hD3)
        exact False.elim (GGResHyp.actual_J_not_oppositeLinear_for_A3 hH hD hMarkA)
      · have hrank4 : 4 ≤ rank := by
          have h3rank : 3 ≤ rank := by
            simpa only [LargeEvenInLambda2] using hΛ0'.2
          omega
        exact False.elim (GGResHyp.actual_J_not_D_high_or_twD_nonsplit_for_A3 hH hD
          (a3MarkingMono hMark0
            (S := fun _ lab => 3 ∣ 2 ^ lab.n + 1 ∧
              ((lab.tag = .D ∧ 4 ≤ lab.rank) ∨ (lab.tag = .twD ∧ 4 ≤ lab.rank)))
            ⟨hplus, Or.inl ⟨rfl, hrank4⟩⟩))
  ·
    by_cases hrank2 : rank = 2
    · subst hrank2
      exact False.elim (GGResHyp.not_twD_rank_two_of_A3 hH hD hΛ0' hHas0 rfl rfl)
    · have h3rank : 3 ≤ rank := by
        have h2rank : 2 ≤ rank := by
          simpa only [LargeEvenInLambda2] using hΛ0'.2
        omega
      by_cases hrank3 : rank = 3
      · subst hrank3
        rcases ggThree_dvd_two_pow_sub_or_add n with hminus | hplus
        · have hMarkA : GGInnerDiagOnLabel
              (fun _ lab => lab.tag = .twA ∧ 3 ∣ 2 ^ lab.n - 1) 3 Bs J := by
            have hTwD3 : GGInnerDiagOnLabel
                (fun _ lab => lab.tag = .twD ∧ lab.rank = 3 ∧ 3 ∣ 2 ^ lab.n - 1) 3 Bs J :=
              a3MarkingMono hMark0 ⟨rfl, rfl, hminus⟩
            exact GGInnerDiagOnLabel.mono_label
              (S := fun _ lab => lab.tag = .twA ∧ lab.rank = 3 ∧ 3 ∣ 2 ^ lab.n - 1)
              (T := fun _ lab => lab.tag = .twA ∧ 3 ∣ 2 ^ lab.n - 1)
              (fun lab h => ⟨h.1, h.2.2⟩)
              (ggInnerDiagOnLabel_twD_to_twA (S := fun n => 3 ∣ 2 ^ n - 1) hTwD3)
          exact False.elim (GGResHyp.actual_J_not_opposite_unitary_for_A3 hH hD hMarkA)
        · exact ⟨⟨.twD, 3, n⟩, hΛ0', Or.inr ⟨Or.inr rfl, rfl, hplus⟩, hHas0⟩
      · have hrank4 : 4 ≤ rank := by omega
        rcases ggThree_dvd_two_pow_sub_or_add n with hminus | hplus
        · exact False.elim (GGResHyp.actual_J_not_D_high_or_twD_split_for_A3 hH hD
            (a3MarkingMono hMark0
              (S := fun _ lab => 3 ∣ 2 ^ lab.n - 1 ∧
                ((lab.tag = .D ∧ 4 ≤ lab.rank) ∨ (lab.tag = .twD ∧ 4 ≤ lab.rank)))
              ⟨hminus, Or.inr ⟨rfl, hrank4⟩⟩))
        · exact False.elim (GGResHyp.actual_J_not_D_high_or_twD_nonsplit_for_A3 hH hD
            (a3MarkingMono hMark0
              (S := fun _ lab => 3 ∣ 2 ^ lab.n + 1 ∧
                ((lab.tag = .D ∧ 4 ≤ lab.rank) ∨ (lab.tag = .twD ∧ 4 ≤ lab.rank)))
              ⟨hplus, Or.inr ⟨rfl, hrank4⟩⟩))
  ·
    rcases ggThree_dvd_two_pow_sub_or_add n with hminus | hplus
    · exact False.elim (GGResHyp.actual_J_not_E6_split_for_A3 hH hD
        (a3MarkingMono hMark0
          (S := fun _ lab => lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n - 1) ⟨rfl, hminus⟩))
    · exact False.elim (GGResHyp.actual_J_not_E6_qplus_for_A3 hH hD
        (a3MarkingMono hMark0
          (S := fun _ lab => lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n + 1) ⟨rfl, hplus⟩))
  ·
    exact False.elim (GGResHyp.actual_J_not_E7_or_E8_for_A3 hH hD
      (a3MarkingMono hMark0
        (S := fun _ lab => lab.tag = .E7 ∨ lab.tag = .E8) (Or.inl rfl)))
  ·
    exact False.elim (GGResHyp.actual_J_not_E7_or_E8_for_A3 hH hD
      (a3MarkingMono hMark0
        (S := fun _ lab => lab.tag = .E7 ∨ lab.tag = .E8) (Or.inr rfl)))
  ·
    exact False.elim (GGResHyp.actual_J_not_F4_for_A3 hH hD
      (a3MarkingMono hMark0 (S := fun _ lab => lab.tag = .F4) rfl))
  ·
    rcases ggThree_dvd_two_pow_sub_or_add n with hminus | hplus
    · exact False.elim (GGResHyp.actual_J_not_twE6_split_for_A3 hH hD
        (a3MarkingMono hMark0
          (S := fun _ lab => lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n - 1) ⟨rfl, hminus⟩))
    · exact False.elim (GGResHyp.actual_J_not_twE6_qplus_for_A3 hH hD
        (a3MarkingMono hMark0
          (S := fun _ lab => lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1) ⟨rfl, hplus⟩))
  ·
    exact False.elim (GGResHyp.not_small_J_label_of_A3 hH hD hΛ0' hHas0
      (Or.inr (Or.inl rfl)))
  ·
    exact False.elim (GGResHyp.not_small_J_label_of_A3 hH hD hΛ0' hHas0
      (Or.inl rfl))
  ·
    exact False.elim (GGResHyp.not_small_J_label_of_A3 hH hD hΛ0' hHas0
      (Or.inr (Or.inr (Or.inl rfl))))
  ·
    exact False.elim (GGResHyp.not_small_J_label_of_A3 hH hD hΛ0' hHas0
      (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  ·
    exact False.elim (GGResHyp.not_small_J_label_of_A3 hH hD hΛ0' hHas0
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  ·
    exact False.elim (GGResHyp.not_small_J_label_of_A3 hH hD hΛ0' hHas0
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  ·
    exact False.elim (GGResHyp.not_small_J_label_of_A3 hH hD hΛ0' hHas0
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))

theorem ggResLineJLabelInput_A3 :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
      (L D J : Subgroup G) (y : G) (K : Subgroup G),
      GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime], p = 3 →
      GGResLineJDatum p Bs J .A3 →
      ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧
        ggResLineJLabel .A3 lab ∧ GGHasLabel lab (J ⧸ Subgroup.center J) := by
  intro G _instG _finG p B Bs x L D J y K hH hFact hp hD
  subst hp
  letI : Fact (Nat.Prime 3) := hFact
  obtain ⟨lab0, hΛ0, hHas0, hMark0⟩ := GGResHyp.exists_J_compatible_marking hH
  exact exists_lineJLabel_A3_of_actual_label hH hD lab0 hΛ0 hHas0 hMark0

end Certificates

end CFSG.StandardType

end
