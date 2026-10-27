module

public import Mathlib
public import CFSG.Foundations.Basic
public import CFSG.Open.QuasithinDefs
public import CFSG.Open.QuasithinH1NaturalModulesMilestoneDefs
public import CFSG.LocalAnalysis.SectionRank.NativeKGroup
public import CFSG.Blueprint.Catalog
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Quasithin.Background.ASVolIRegistered
public import CFSG.Milestones.CL_LIT_SQTK_simple_list
public import CFSG.LocalAnalysis.SectionRank.QTK.Main
public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalLinearFourTwo
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms
public import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix
public import CFSG.Adapters.LinearSmallCatalog
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.TrivialRows
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ProvedRows
public import CFSG.GH74.Exceptional.UnitaryFourTwo
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.RankThree.PartOne.LIT.RankPSL3
public import CFSG.RankThree.PartOne.S12.ModelTransport
public import CFSG.ClassicalInvolution.Orders.Classical
public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.LieType.Ree.SuzukiOrder
public import CFSG.Sporadic.Mathieu.M22
public import CFSG.LocalAnalysis.SectionRank.SQTKTransport
public import CFSG.Sporadic.J2
public import CFSG.Sporadic.HS
public import CFSG.Sporadic.Ru
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J2Local
public import CFSG.LocalAnalysis.SectionRank.Sporadic.HSLocal
public import CFSG.LocalAnalysis.SectionRank.Sporadic.RuLocal
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocal
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434RemG24
public import CFSG.RankThree.Chevalley.EvenRealThreeCentralizingInvolution
public import CFSG.RankThree.PerfectCover.HopfFormula
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.Sporadic.Recognition.HNMultiplier
public import Certificates.Certificate1004
public import Certificates.Certificate1011
public import Certificates.Certificate1018
public import Certificates.Certificate1018Base
public import Certificates.Certificate8086
public import Certificates.Certificate8087
public import Certificates.Certificate8088
public import Certificates.Certificate8089
public import Certificates.Certificate8090
public import Certificates.Certificate8091
public import Certificates.Certificate8092
public import Certificates.Certificate8126
public import Certificates.Certificate8152

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI.ChIJK

open CFSG.Open CFSG.Blueprint
open scoped MatrixGroups

@[expose] noncomputable def h1Dim {G V : Type} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) : ℕ :=
  Module.finrank (ZMod 2) (groupCohomology (Rep.of ρ) 1)

@[expose] noncomputable def permRepF2 (n : ℕ) :
    Representation (ZMod 2) (Equiv.Perm (Fin n)) (Fin n → ZMod 2) where
  toFun σ := LinearMap.funLeft (ZMod 2) (ZMod 2) (σ.symm : Fin n → Fin n)
  map_one' := by
    refine LinearMap.ext fun v => funext fun i => ?_
    simp [LinearMap.funLeft]
    rfl
  map_mul' σ τ := by
    refine LinearMap.ext fun v => funext fun i => ?_
    simp [LinearMap.funLeft, Equiv.Perm.mul_def]

@[expose] def evenWeight (n : ℕ) : Submodule (ZMod 2) (Fin n → ZMod 2) where
  carrier := {v | ∑ i, v i = 0}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, Pi.add_apply, Finset.sum_add_distrib] at ha hb ⊢
    rw [ha, hb, add_zero]
  zero_mem' := by simp
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum] at hx ⊢
    rw [hx, mul_zero]

theorem evenWeight_inv (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    evenWeight n ≤ (evenWeight n).comap (permRepF2 n σ) := by
  intro v hv
  have hv' : ∑ i, v i = 0 := hv
  show ∑ i, (permRepF2 n σ v) i = 0
  have : (∑ i : Fin n, (permRepF2 n σ v) i) = ∑ i : Fin n, v i := by
    simp only [permRepF2, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.funLeft_apply]
    exact Equiv.sum_comp σ.symm v
  rw [this]; exact hv'

@[expose] noncomputable def evenWeightRep (n : ℕ) :
    Representation (ZMod 2) (Equiv.Perm (Fin n)) (evenWeight n) :=
  (permRepF2 n).subrepresentation (evenWeight n) (evenWeight_inv n)

@[expose] def constInEven (n : ℕ) : Submodule (ZMod 2) (evenWeight n) :=
  (Submodule.span (ZMod 2) {fun _ : Fin n => (1 : ZMod 2)}).comap (evenWeight n).subtype

theorem constInEven_inv (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    constInEven n ≤ (constInEven n).comap (evenWeightRep n σ) := by
  intro v hv
  have hv' : (v : Fin n → ZMod 2) ∈
      Submodule.span (ZMod 2) {fun _ : Fin n => (1 : ZMod 2)} := hv
  rw [Submodule.mem_span_singleton] at hv'
  obtain ⟨c, hc⟩ := hv'
  show ((evenWeightRep n σ v : evenWeight n) : Fin n → ZMod 2) ∈
    Submodule.span (ZMod 2) {fun _ : Fin n => (1 : ZMod 2)}
  rw [Submodule.mem_span_singleton]
  refine ⟨c, ?_⟩
  funext i
  have := congrFun hc (σ.symm i)
  simpa [evenWeightRep, permRepF2, LinearMap.funLeft] using this

@[expose] noncomputable def symNaturalRep (n : ℕ) :
    Representation (ZMod 2) (Equiv.Perm (Fin n)) (evenWeight n ⧸ constInEven n) :=
  (evenWeightRep n).quotient (constInEven n) (constInEven_inv n)

@[expose] noncomputable def altNaturalRep (n : ℕ) :
    Representation (ZMod 2) (alternatingGroup (Fin n)) (evenWeight n ⧸ constInEven n) :=
  (symNaturalRep n).comp (alternatingGroup (Fin n)).subtype

@[expose] noncomputable def slNaturalRep (n : ℕ) (K : Type) [Field K] [Algebra (ZMod 2) K] :
    Representation (ZMod 2) SL(n, K) (Fin n → K) :=
  quasithinH1MatrixRep (quasithinH1SLMatrix n K)

@[expose] def sp4Derived (K : Type) [Field K] : Subgroup (Matrix.symplecticGroup (Fin 2) K) :=
  commutator (Matrix.symplecticGroup (Fin 2) K)

@[expose] noncomputable def sp4NaturalRep (K : Type) [Field K] [Algebra (ZMod 2) K] :
    Representation (ZMod 2) (sp4Derived K) (Fin 2 ⊕ Fin 2 → K) :=
  quasithinH1MatrixRep ((Matrix.symplecticGroup (Fin 2) K).subtype.comp (sp4Derived K).subtype)

@[expose] noncomputable def orthMinusRep (K : Type) [Field K] [Algebra (ZMod 2) K] (b c : K) :
    Representation (ZMod 2) (StatedOmega (StatedQuadMinus 2 K b c))
      (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K) :=
  quasithinH1MatrixRep ((Units.coeHom _).comp (StatedOmega (StatedQuadMinus 2 K b c)).subtype)

section Zorn

variable (K : Type) [Field K]

@[expose] def zornOne : quasithinZorn K := (1, 0, 0, 1)

@[expose] def zornTrace (x : quasithinZorn K) : K := x.1 + x.2.2.2

@[expose] def zornNorm (x : quasithinZorn K) : K := x.1 * x.2.2.2 - ∑ i, x.2.1 i * x.2.2.1 i

theorem cross_zero_right (u : Fin 3 → K) : quasithinCross u 0 = 0 := by
  ext i; fin_cases i <;> simp [quasithinCross]

theorem cross_zero_left (u : Fin 3 → K) : quasithinCross 0 u = 0 := by
  ext i; fin_cases i <;> simp [quasithinCross]

theorem cross_self (u : Fin 3 → K) : quasithinCross u u = 0 := by
  ext i; fin_cases i <;> simp [quasithinCross] <;> ring

theorem zornMul_one_left (y : quasithinZorn K) : quasithinZornMul (zornOne K) y = y := by
  obtain ⟨a, u, v, b⟩ := y
  simp [zornOne, quasithinZornMul, cross_zero_left]

theorem zornMul_one_right (y : quasithinZorn K) : quasithinZornMul y (zornOne K) = y := by
  obtain ⟨a, u, v, b⟩ := y
  simp [zornOne, quasithinZornMul, cross_zero_right]

theorem zornMul_self (x : quasithinZorn K) :
    quasithinZornMul x x = zornTrace K x • x - zornNorm K x • zornOne K := by
  obtain ⟨a, u, v, b⟩ := x
  simp only [zornOne, zornTrace, zornNorm, quasithinZornMul, cross_self]
  ext i <;> simp [mul_comm] <;> ring

theorem g2_gen (g : quasithinZorn K ≃ₗ[K] quasithinZorn K)
    (hg : ∀ x y, g (quasithinZornMul x y) = quasithinZornMul (g x) (g y)) :
    g (zornOne K) = zornOne K ∧ ∀ x, zornTrace K (g x) = zornTrace K x := by
  have h1 : g (zornOne K) = zornOne K := by
    obtain ⟨y, hy⟩ := g.surjective (zornOne K)
    have := hg (zornOne K) y
    rw [zornMul_one_left, hy, zornMul_one_right] at this
    exact this.symm
  refine ⟨h1, fun x => ?_⟩
  by_contra hne
  have e1 : quasithinZornMul (g x) (g x) =
      zornTrace K x • g x - zornNorm K x • zornOne K := by
    rw [← hg, zornMul_self, map_sub, map_smul, map_smul, h1]
  have e2 := zornMul_self K (g x)
  have hne' : zornTrace K (g x) - zornTrace K x ≠ 0 := sub_ne_zero.mpr hne
  have e3 : (zornTrace K (g x) - zornTrace K x) • g x =
      (zornNorm K (g x) - zornNorm K x) • zornOne K := by
    rw [sub_smul, sub_smul]
    exact sub_eq_sub_iff_sub_eq_sub.mp (e2.symm.trans e1)
  set c : K := (zornTrace K (g x) - zornTrace K x)⁻¹ * (zornNorm K (g x) - zornNorm K x) with hc
  have e4 : g x = c • zornOne K := by
    have := congrArg (fun z => (zornTrace K (g x) - zornTrace K x)⁻¹ • z) e3
    simp only [smul_smul, inv_mul_cancel₀ hne', one_smul] at this
    rw [this, hc]
  have e5 : x = c • zornOne K := by
    apply g.injective
    rw [e4, map_smul, h1]
  apply hne
  rw [e4]
  conv_rhs => rw [e5]

theorem g2_inv (g : quasithinZorn K ≃ₗ[K] quasithinZorn K) (hg : g ∈ quasithinG2 K) :
    g (zornOne K) = zornOne K ∧ ∀ x, zornTrace K (g x) = zornTrace K x := by
  induction hg using Subgroup.closure_induction with
  | mem g hg' => exact g2_gen K g hg'
  | one => exact ⟨rfl, fun x => rfl⟩
  | mul g h _ _ ihg ihh =>
    refine ⟨?_, fun x => ?_⟩
    · show g (h (zornOne K)) = zornOne K
      rw [ihh.1, ihg.1]
    · show zornTrace K (g (h x)) = zornTrace K x
      rw [ihg.2, ihh.2]
  | inv g _ ihg =>
    refine ⟨?_, fun x => ?_⟩
    · have := ihg.1
      apply g.injective
      simp [this]
    · have := ihg.2 (g⁻¹ x)
      simpa using this.symm

end Zorn

section G2Module

variable (K : Type) [Field K] [Algebra (ZMod 2) K]

@[expose] noncomputable def zornRep :
    Representation (ZMod 2) ↥(quasithinG2 K) (quasithinZorn K) where
  toFun g := (((g : quasithinZorn K ≃ₗ[K] quasithinZorn K) :
    quasithinZorn K →ₗ[K] quasithinZorn K)).restrictScalars (ZMod 2)
  map_one' := LinearMap.ext fun _ => rfl
  map_mul' _ _ := LinearMap.ext fun _ => rfl

@[expose] def zornTraceZero : Submodule (ZMod 2) (quasithinZorn K) where
  carrier := {x | zornTrace K x = 0}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, zornTrace, Prod.fst_add, Prod.snd_add] at ha hb ⊢
    calc a.1 + b.1 + (a.2.2.2 + b.2.2.2) = (a.1 + a.2.2.2) + (b.1 + b.2.2.2) := by ring
      _ = 0 := by rw [ha, hb, add_zero]
  zero_mem' := by simp [zornTrace]
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_ofPred_eq, zornTrace, Prod.smul_fst, Prod.smul_snd] at hx ⊢
    rw [← smul_add, hx, smul_zero]

theorem zornTraceZero_inv (g : ↥(quasithinG2 K)) :
    zornTraceZero K ≤ (zornTraceZero K).comap (zornRep K g) := by
  intro x hx
  have hx' : zornTrace K x = 0 := hx
  show zornTrace K (((g : quasithinZorn K ≃ₗ[K] quasithinZorn K)) x) = 0
  rw [(g2_inv K g g.2).2 x, hx']

@[expose] noncomputable def zornTraceZeroRep :
    Representation (ZMod 2) ↥(quasithinG2 K) (zornTraceZero K) :=
  (zornRep K).subrepresentation (zornTraceZero K) (zornTraceZero_inv K)

@[expose] def zornLine : Submodule (ZMod 2) (zornTraceZero K) :=
  ((Submodule.span K {zornOne K}).restrictScalars (ZMod 2)).comap (zornTraceZero K).subtype

theorem zornLine_inv (g : ↥(quasithinG2 K)) :
    zornLine K ≤ (zornLine K).comap (zornTraceZeroRep K g) := by
  intro x hx
  have hx' : (x : quasithinZorn K) ∈ Submodule.span K {zornOne K} := hx
  rw [Submodule.mem_span_singleton] at hx'
  obtain ⟨c, hc⟩ := hx'
  show ((zornTraceZeroRep K g x : zornTraceZero K) : quasithinZorn K) ∈
    Submodule.span K {zornOne K}
  rw [Submodule.mem_span_singleton]
  refine ⟨c, ?_⟩
  have h1 := (g2_inv K g g.2).1
  have : ((zornTraceZeroRep K g x : zornTraceZero K) : quasithinZorn K) =
      ((g : quasithinZorn K ≃ₗ[K] quasithinZorn K)) (x : quasithinZorn K) := rfl
  rw [this, ← hc, map_smul, h1]

@[expose] noncomputable def g2NaturalRep :
    Representation (ZMod 2) ↥(quasithinG2 K) (zornTraceZero K ⧸ zornLine K) :=
  (zornTraceZeroRep K).quotient (zornLine K) (zornLine_inv K)

@[expose] noncomputable def g2DerivedNaturalRep :
    Representation (ZMod 2) ↥(commutator ↥(quasithinG2 K)) (zornTraceZero K ⧸ zornLine K) :=
  (g2NaturalRep K).comp (commutator ↥(quasithinG2 K)).subtype

end G2Module

@[expose] def IsHatCover (X : Type) [Group X] (S : Type) [Group S] : Prop :=
  CFSG.IsQuasisimple X ∧ Nat.card (Subgroup.center X) = 3 ∧
    Nonempty (X ⧸ Subgroup.center X ≃* S)

@[expose] def ListedI13D2 (G : Type) [Group G] : Prop :=
  StatedClassicalModel G .PSL 4 2 1 ∨ ChevalleyExceptionalModel G .G2 2 2 ∨
    NativeSporadic.IsSporadic G .M12 ∨ NativeSporadic.IsSporadic G .J2 ∨
    NativeSporadic.IsSporadic G .HS ∨ NativeSporadic.IsSporadic G .Ru ∨
    ∃ p f : ℕ, p ≠ 2 ∧ 1 ≤ f ∧ p ^ f ≠ 9 ∧ StatedClassicalModel G .PSL 2 p f

@[expose] def ListedI13D3 (G : Type) [Group G] : Prop :=
  (∃ p f : ℕ, (p ^ f % 3 = 1 ∧ StatedClassicalModel G .PSL 3 p f) ∨
      (p ^ f % 3 = 2 ∧ StatedClassicalModel G .PSU 3 p f)) ∧
    ¬ StatedClassicalModel G .PSL 3 2 2

@[expose] def ListedI13D6 (G : Type) [Group G] : Prop :=
  Nonempty (G ≃* alternatingGroup (Fin 6)) ∨ Nonempty (G ≃* alternatingGroup (Fin 7))

@[expose] def ListedI14D2 (G : Type) [Group G] : Prop :=
  Nonempty (G ≃* alternatingGroup (Fin 9)) ∨ StatedClassicalModel G .PSU 4 2 1 ∨
    StatedClassicalModel G .PSL 4 3 1 ∨
    ∃ p f : ℕ, p ≠ 2 ∧ 1 ≤ f ∧ 9 < p ^ f ∧ StatedClassicalModel G .PSL 2 p f

@[expose] def ListedI14D3 (G : Type) [Group G] : Prop :=
  NativeSporadic.IsSporadic G .J3 ∨ NativeSporadic.IsSporadic G .McL ∨
    ChevalleyExceptionalModel G .G2 3 1 ∨
    ∃ p f : ℕ, p ≠ 2 ∧ ((p ^ f % 3 = 1 ∧ StatedClassicalModel G .PSL 3 p f) ∨
      (p ^ f % 3 = 2 ∧ StatedClassicalModel G .PSU 3 p f))

@[expose] def ListedI14D4 (G : Type) [Group G] : Prop :=
  (∃ r m : ℕ, r.Prime ∧ r = 2 ^ 2 ^ m + 1 ∧ 3 < r ∧ StatedClassicalModel G .PSL 4 r 1) ∨
    (∃ s m : ℕ, s.Prime ∧ s = 2 ^ m - 1 ∧ 3 < s ∧ StatedClassicalModel G .PSU 4 s 1)

end CFSG.ASVolI.ChIJK

namespace CFSG.ASVolI

open CFSG.Open CFSG.Blueprint CFSG.ASVolI.ChIJK
open scoped MatrixGroups

@[expose] def I_1_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (r : ℕ), r.Prime → r ≠ 2 → Group.IsPerfect G →
    CFSG.pRank r G ≤ 1 → ∀ x : quasithinHopfMultiplier G, Nat.Coprime (orderOf x) r

section BurnsideI12

private theorem burnsideI12_isCyclic_of_pRank_le_one {G : Type} [Group G] [Finite G] {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hrk : CFSG.pRank r G ≤ 1) {P : Subgroup G}
    (hP : IsPGroup r P) : IsCyclic P := by
  by_contra hnc
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : Fact (IsPGroup r P) := ⟨hP⟩
  obtain ⟨S, -, hScard, hSel⟩ := CFSG.lemma_4_5_a hr2 hnc
  haveI := hSel
  have hSm : CFSG.IsElementaryAbelian r (S.map P.subtype) :=
    CFSG.IsElementaryAbelian.map_subtype
  have hcard : Nat.card (S.map P.subtype) = r ^ 2 := by
    rw [← hScard]
    exact (Nat.card_congr (S.equivMapOfInjective P.subtype P.subtype_injective).toEquiv).symm
  have h2 := CFSG.SectionRank.le_pRank hr.one_lt (le_top : S.map P.subtype ≤ ⊤)
    ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian r _).mp hSm) hcard
  rw [← CFSG.SectionRank.pRank_eq_open_pRank_top] at h2
  omega

private theorem burnsideI12_pow_index_eq_one {E G : Type*} [Group E] [Group G] [Group.IsPerfect E]
    (π : E →* G) (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center E)
    (P : Subgroup G) [P.FiniteIndex] [IsCyclic P] {z : E} (hz : z ∈ π.ker) :
    z ^ P.index = 1 := by
  set H : Subgroup E := P.comap π
  have hidx : H.index = P.index := Subgroup.index_comap_of_surjective P hπ
  let f : H →* P := (π.comp H.subtype).codRestrict P fun x => x.2
  have hfker : f.ker ≤ Subgroup.center H := by
    intro x hx
    have hxπ : π x = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
    have hxc : (x : E) ∈ Subgroup.center E := hker (MonoidHom.mem_ker.2 hxπ)
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.1 hxc y)
  haveI : IsMulCommutative H := f.isMulCommutative_of_isCyclic_of_ker_le_center hfker
  letI : CommGroup H := IsMulCommutative.instCommGroup
  have hzc : z ∈ Subgroup.center E := hker hz
  have key : ∀ (k : ℕ) (g₀ : E), g₀⁻¹ * z ^ k * g₀ ∈ H → g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro k g₀ _
    have hc : z ^ k ∈ Subgroup.center E := Subgroup.pow_mem _ hzc k
    rw [Subgroup.mem_center_iff] at hc
    rw [mul_assoc, ← hc g₀, inv_mul_cancel_left]
  have hV := MonoidHom.transfer_eq_pow (MonoidHom.id H) z key
  have hV1 : MonoidHom.transfer (MonoidHom.id H) z = 1 := by
    have hle : commutator E ≤ (MonoidHom.transfer (MonoidHom.id H) : E →* H).ker := by
      rw [_root_.commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact mul_comm _ _
    exact MonoidHom.mem_ker.1 (hle Group.IsPerfect.mem_commutator)
  rw [hV1] at hV
  have := congrArg Subtype.val hV.symm
  rw [← hidx]
  simpa using this

end BurnsideI12

theorem as_I_1_2 : I_1_2 := by
  intro G _ _ r hr hr2 hperf hrk x
  haveI : Fact r.Prime := ⟨hr⟩
  let P : Sylow r G := default
  haveI : IsCyclic (P : Subgroup G) :=
    burnsideI12_isCyclic_of_pRank_le_one hr hr2 hrk P.isPGroup'
  haveI : Group.IsPerfect (CFSG.RankThree.PerfectCover.HopfCover G) :=
    CFSG.RankThree.PerfectCover.hopfCover_isPerfect
  let e := CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess G
  have hpow := burnsideI12_pow_index_eq_one (CFSG.RankThree.PerfectCover.hopfCoverMap G)
    (CFSG.RankThree.PerfectCover.hopfCoverMap_surjective)
    (CFSG.RankThree.PerfectCover.hopfMultiplier_le_center (S := G)) (P : Subgroup G)
    (z := (e x : CFSG.RankThree.PerfectCover.HopfCover G)) (e x).2
  have hdvd : orderOf x ∣ (P : Subgroup G).index := by
    rw [← MulEquiv.orderOf_eq e x, ← Subgroup.orderOf_coe]
    exact orderOf_dvd_of_pow_eq_one hpow
  exact Nat.Coprime.coprime_dvd_left hdvd
    ((Nat.Prime.coprime_iff_not_dvd hr).2 P.not_dvd_index).symm

@[expose] def I_1_3 : Prop :=
  (∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → CFSG.SectionRank.IsSQTKCat G →
    Nontrivial (quasithinHopfMultiplier G) →
    ListedI13D2 G ∨ ListedI13D3 G ∨ ListedI13D6 G ∨ NativeSporadic.IsSporadic G .M22 ∨
      SuzukiModel G 2 3 ∨ StatedClassicalModel G .PSL 3 2 2) ∧
  (∀ (G : Type) [Group G] [Finite G], ListedI13D2 G → quasithinMultiplierCyclic G 2) ∧
  (∀ (G : Type) [Group G] [Finite G], ListedI13D3 G → quasithinMultiplierCyclic G 3) ∧
  (∀ (G : Type) [Group G] [Finite G], ListedI13D6 G → quasithinMultiplierCyclic G 6) ∧
  (∀ (G : Type) [Group G] [Finite G], NativeSporadic.IsSporadic G .M22 →
    quasithinMultiplierCyclic G 12) ∧
  (∀ (G : Type) [Group G] [Finite G], SuzukiModel G 2 3 →
    Nonempty (quasithinHopfMultiplier G ≃* Multiplicative (ZMod 2 × ZMod 2))) ∧
  (∀ (G : Type) [Group G] [Finite G], StatedClassicalModel G .PSL 3 2 2 →
    Nonempty (quasithinHopfMultiplier G ≃* Multiplicative (ZMod 4 × ZMod 4 × ZMod 3)))

section BurnsideI13_only13

@[expose] def burnsideI13_Row (X : Type) [Group X] (t : StatedLieTag) (n p f : ℕ) : Prop :=
  Nonempty (griessHopfMultiplier X ≃*
    (Multiplicative (ZMod (CFSG.Blueprint.Multiplier.genericOrders t n p f).1) ×
      Multiplicative (ZMod (CFSG.Blueprint.Multiplier.genericOrders t n p f).2)) ×
    (Multiplicative (ZMod (CFSG.Blueprint.Multiplier.exceptionalOrders t n p f).1) ×
      Multiplicative (ZMod (CFSG.Blueprint.Multiplier.exceptionalOrders t n p f).2)))

@[expose] def burnsideI13_Griess : Prop :=
  ∀ (X : Type) [Group X] (t : StatedLieTag) (n p f : ℕ),
    CFSG.Blueprint.LieModel X t n p f → burnsideI13_Row X t n p f

private theorem burnsideI13_sub_of_row {X : Type} [Group X] {t : StatedLieTag} {n p f : ℕ}
    (hX : burnsideI13_Row X t n p f)
    (hg : CFSG.Blueprint.Multiplier.genericOrders t n p f = (1, 1))
    (he : CFSG.Blueprint.Multiplier.exceptionalOrders t n p f = (1, 1)) :
    Subsingleton (quasithinHopfMultiplier X) := by
  obtain ⟨e⟩ := hX
  rw [hg, he] at e
  haveI : Subsingleton (Multiplicative (ZMod 1)) := inferInstanceAs (Subsingleton (ZMod 1))
  exact e.toEquiv.subsingleton

open scoped commutatorElement in
private theorem burnsideI13_sub_cyclic {G : Type} [Group G] [IsCyclic G] :
    Subsingleton (quasithinHopfMultiplier G) := by
  set R : Subgroup (FreeGroup G) := quasithinHopfRelations G with hR
  have hRn : R.Normal := MonoidHom.normal_ker _
  set N : Subgroup (FreeGroup G) := ⁅(⊤ : Subgroup (FreeGroup G)), R⁆ with hN
  have hNn : N.Normal := Subgroup.commutator_normal _ _
  have hNR : N ≤ R := Subgroup.commutator_le_right _ _
  let f : FreeGroup G ⧸ N →* G := QuotientGroup.lift N (FreeGroup.lift id) (fun x hx => hNR hx)
  have hker : f.ker ≤ Subgroup.center (FreeGroup G ⧸ N) := by
    intro y hy
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    have hyR : y ∈ R := by
      have : f (QuotientGroup.mk y) = 1 := hy
      exact MonoidHom.mem_ker.2 (by simpa [f] using this)
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective z
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have h := Subgroup.commutator_mem_commutator (Subgroup.mem_top z⁻¹) (R.inv_mem hyR)
    have h' : ((z * y)⁻¹ * (y * z)) = (⁅z⁻¹, y⁻¹⁆)⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [h']
    exact N.inv_mem h
  haveI : IsMulCommutative (FreeGroup G ⧸ N) := f.isMulCommutative_of_isCyclic_of_ker_le_center hker
  have hcomm : commutator (FreeGroup G) ≤ N := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    have h1 : (QuotientGroup.mk' N) ⁅a, b⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.2
        (IsMulCommutative.is_comm.comm (QuotientGroup.mk a : FreeGroup G ⧸ N) (QuotientGroup.mk b))
    exact (QuotientGroup.eq_one_iff _).1 h1
  have htop : N.subgroupOf (R ⊓ commutator (FreeGroup G)) = ⊤ :=
    Subgroup.subgroupOf_eq_top.2 (inf_le_right.trans hcomm)
  show Subsingleton (↥(R ⊓ commutator (FreeGroup G)) ⧸ N.subgroupOf (R ⊓ commutator (FreeGroup G)))
  rw [htop]
  exact QuotientGroup.subsingleton_quotient_top


@[expose] def burnsideI13_Goal (G : Type) [Group G] : Prop :=
  ChIJK.ListedI13D2 G ∨ ChIJK.ListedI13D3 G ∨ ChIJK.ListedI13D6 G ∨
    CFSG.Blueprint.NativeSporadic.IsSporadic G .M22 ∨ CFSG.Blueprint.SuzukiModel G 2 3 ∨
    StatedClassicalModel G .PSL 3 2 2

private theorem burnsideI13_D2_psl4 {G : Type} [Group G] (h : StatedClassicalModel G .PSL 4 2 1) :
    ChIJK.ListedI13D2 G := Or.inl h

private theorem burnsideI13_D2_g2 {G : Type} [Group G] (h :
    CFSG.Blueprint.ChevalleyExceptionalModel G .G2 2 2) :
    ChIJK.ListedI13D2 G := Or.inr (Or.inl h)

private theorem burnsideI13_D2_M12 {G : Type} [Group G] (h :
    CFSG.Blueprint.NativeSporadic.IsSporadic G .M12) :
    ChIJK.ListedI13D2 G := Or.inr (Or.inr (Or.inl h))

private theorem burnsideI13_D2_J2 {G : Type} [Group G] (h :
    CFSG.Blueprint.NativeSporadic.IsSporadic G .J2) :
    ChIJK.ListedI13D2 G := Or.inr (Or.inr (Or.inr (Or.inl h)))

private theorem burnsideI13_D2_HS {G : Type} [Group G] (h :
    CFSG.Blueprint.NativeSporadic.IsSporadic G .HS) :
    ChIJK.ListedI13D2 G := Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

private theorem burnsideI13_D2_Ru {G : Type} [Group G] (h :
    CFSG.Blueprint.NativeSporadic.IsSporadic G .Ru) :
    ChIJK.ListedI13D2 G := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))

private theorem burnsideI13_D2_psl2 {G : Type} [Group G] {p f : ℕ} (hp : p ≠ 2) (hf : 1 ≤ f)
    (h9 : p ^ f ≠ 9) (h : StatedClassicalModel G .PSL 2 p f) : ChIJK.ListedI13D2 G :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨p, f, hp, hf, h9, h⟩)))))

private theorem burnsideI13_D3_psl {G : Type} [Group G] {p f : ℕ} (hq : p ^ f % 3 = 1)
    (h : StatedClassicalModel G .PSL 3 p f) (h34 : ¬ StatedClassicalModel G .PSL 3 2 2) :
    ChIJK.ListedI13D3 G := ⟨⟨p, f, Or.inl ⟨hq, h⟩⟩, h34⟩

private theorem burnsideI13_D3_psu {G : Type} [Group G] {p f : ℕ} (hq : p ^ f % 3 = 2)
    (h : StatedClassicalModel G .PSU 3 p f) (h34 : ¬ StatedClassicalModel G .PSL 3 2 2) :
    ChIJK.ListedI13D3 G := ⟨⟨p, f, Or.inr ⟨hq, h⟩⟩, h34⟩

private theorem burnsideI13_exc_psl2 (p f : ℕ) (hp : p ≠ 2) (h9 : p ^ f ≠ 9) :
    CFSG.Blueprint.Multiplier.exceptionalOrders .PSL 2 p f = (1, 1) := by
  unfold CFSG.Blueprint.Multiplier.exceptionalOrders
  split <;> first | rfl | (exfalso; simp_all)

private theorem burnsideI13_exc_psl2_two (f : ℕ) (hf : 3 ≤ f) :
    CFSG.Blueprint.Multiplier.exceptionalOrders .PSL 2 2 f = (1, 1) := by
  unfold CFSG.Blueprint.Multiplier.exceptionalOrders
  split <;> first | rfl | (exfalso; simp_all <;> omega)

private theorem burnsideI13_exc_psl3 (p f : ℕ) (h1 : ¬ (p = 2 ∧ f = 1)) (h2 : ¬ (p = 2 ∧ f = 2)) :
    CFSG.Blueprint.Multiplier.exceptionalOrders .PSL 3 p f = (1, 1) := by
  unfold CFSG.Blueprint.Multiplier.exceptionalOrders
  split <;> first | rfl | (exfalso; simp_all)

private theorem burnsideI13_exc_psu3 (p f : ℕ) :
    CFSG.Blueprint.Multiplier.exceptionalOrders .PSU 3 p f = (1, 1) := by
  unfold CFSG.Blueprint.Multiplier.exceptionalOrders
  split <;> first | rfl | (exfalso; simp_all)

private theorem burnsideI13_exc_psp2 (p f : ℕ) :
    CFSG.Blueprint.Multiplier.exceptionalOrders .PSp 2 p f = (1, 1) := by
  unfold CFSG.Blueprint.Multiplier.exceptionalOrders
  split <;> first | rfl | (exfalso; simp_all)

private theorem burnsideI13_exc_g2_two (f : ℕ) (hf : 3 ≤ f) :
    CFSG.Blueprint.Multiplier.exceptionalOrders .G2 0 2 f = (1, 1) := by
  unfold CFSG.Blueprint.Multiplier.exceptionalOrders
  split <;> first | rfl | (exfalso; simp_all <;> omega)

private theorem burnsideI13_exc_suzuki (f : ℕ) (hf : 5 ≤ f) :
    CFSG.Blueprint.Multiplier.exceptionalOrders .twistedB2 0 2 f = (1, 1) := by
  unfold CFSG.Blueprint.Multiplier.exceptionalOrders
  split <;> first | rfl | (exfalso; simp_all <;> omega)

private theorem burnsideI13_exc_psl5 :
    CFSG.Blueprint.Multiplier.exceptionalOrders .PSL 5 2 1 = (1, 1) := by
  unfold CFSG.Blueprint.Multiplier.exceptionalOrders
  split <;> first | rfl | (exfalso; simp_all)

private theorem burnsideI13_gcd_three {m : ℕ} (h : ¬ 3 ∣ m) : Nat.gcd 3 m = 1 :=
  (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h

private theorem burnsideI13_gcd_two {m : ℕ} (h : ¬ 2 ∣ m) : Nat.gcd 2 m = 1 :=
  (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 h


private theorem burnsideI13_psl25_of_alt5 {G : Type} [Group G]
    (e : Nonempty (G ≃* alternatingGroup (Fin 5))) : StatedClassicalModel G .PSL 2 5 1 := by
  obtain ⟨e⟩ := e
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨e5⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five (ZMod 5)
    (Or.inr (by rw [Nat.card_zmod]))
  exact ⟨⟨by norm_num, le_rfl, by norm_num, by decide, by decide⟩, ZMod 5, inferInstance,
    inferInstance, by rw [Nat.card_zmod, pow_one], ⟨e.trans e5.symm⟩⟩

private theorem burnsideI13_psl25_of_psl24 {G : Type} [Group G]
    (h : StatedClassicalModel G .PSL 2 2 2) : StatedClassicalModel G .PSL 2 5 1 := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  obtain ⟨e5⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five K
    (Or.inl (by rw [hK]; norm_num))
  exact burnsideI13_psl25_of_alt5 ⟨e.trans e5⟩

private theorem burnsideI13_alt6_of_psl29 {G : Type} [Group G] (h : StatedClassicalModel G .PSL
    2 3 2) :
    Nonempty (G ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have : Fintype K := Fintype.ofFinite K
  have hK9 : Fintype.card K = 9 := by rw [← Nat.card_eq_fintype_card, hK]; norm_num
  obtain ⟨e6⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.unique_field_nine_projective_linear_alternating_six_isomorphism
      K hK9
  exact ⟨e.trans
    ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm.trans e6)⟩

private theorem burnsideI13_psl42_of_alt8 {G : Type} [Group G]
    (e : Nonempty (G ≃* alternatingGroup (Fin 8))) : StatedClassicalModel G .PSL 4 2 1 :=
  CFSG.Blueprint.LieModel.statedClassicalModel
    ((CFSG.ComponentClassification.SymmetricLocal.lie_model_linear_four_two_iff G).2 e) (by decide)

private theorem burnsideI13_psl27_of_psl32 {G : Type} [Group G] (h : StatedClassicalModel G
    .PSL 3 2 1) :
    StatedClassicalModel G .PSL 2 7 1 :=
  CFSG.Blueprint.LieModel.statedClassicalModel
    (CFSG.LocalAnalysis.ComponentInitial.PSL3_two_PSL2_seven_paired_isomorphism G
      (Or.inl ⟨by decide, h⟩)) (by decide)


private theorem burnsideI13_table1 (hGr : burnsideI13_Griess)
    (hM12 : quasithinMultiplierCyclic (CFSG.Blueprint.NativeSporadic.Carrier .M12) 2)
    (hJ2 : quasithinMultiplierCyclic (CFSG.Blueprint.NativeSporadic.Carrier .J2) 2)
    (hHS : quasithinMultiplierCyclic (CFSG.Blueprint.NativeSporadic.Carrier .HS) 2)
    (hRu : quasithinMultiplierCyclic (CFSG.Blueprint.NativeSporadic.Carrier .Ru) 2)
    (G : Type) [Group G] (h : ChIJK.ListedI13D2 G) : quasithinMultiplierCyclic G 2 := by
  rcases h with h | h | h | h | h | h | ⟨p, f, hp, hf, h9, h⟩
  · exact ASVolIRegistered.multCyc_exc (hGr G .PSL 4 2 1 (Or.inl ⟨by decide, h⟩)) (by decide)
      (by decide)
  · exact ASVolIRegistered.multCyc_exc (hGr G .G2 0 2 2 (Or.inr (Or.inl ⟨rfl, by decide, h⟩)))
      (by decide) (by decide)
  · obtain ⟨e⟩ := h
    exact ASVolIRegistered.multCyc_congr e hM12
  · obtain ⟨e⟩ := h
    exact ASVolIRegistered.multCyc_congr e hJ2
  · obtain ⟨e⟩ := h
    exact ASVolIRegistered.multCyc_congr e hHS
  · obtain ⟨e⟩ := h
    exact ASVolIRegistered.multCyc_congr e hRu
  · have hpp : p.Prime := h.1.1
    have hodd := ASVolIRegistered.odd_pow_of_ne_two (k := f) hpp hp
    refine ASVolIRegistered.multCyc_gen (hGr G .PSL 2 p f (Or.inl ⟨by decide, h⟩)) ?_
      (burnsideI13_exc_psl2 p f hp h9)
    show (Nat.gcd 2 (p ^ f - 1), 1) = (2, 1)
    rw [ASVolIRegistered.gcd_two_odd hodd]

private theorem burnsideI13_table2 (hGr : burnsideI13_Griess) (G : Type) [Group G]
    (h : ChIJK.ListedI13D3 G) : quasithinMultiplierCyclic G 3 := by
  obtain ⟨⟨p, f, h | h⟩, h34⟩ := h
  · obtain ⟨hq, hm⟩ := h
    have h3 : 3 ∣ p ^ f - 1 := by omega
    refine ASVolIRegistered.multCyc_gen (hGr G .PSL 3 p f (Or.inl ⟨by decide, hm⟩)) ?_ ?_
    · show (Nat.gcd 3 (p ^ f - 1), 1) = (3, 1)
      rw [Nat.gcd_eq_left h3]
    · apply burnsideI13_exc_psl3
      · rintro ⟨rfl, rfl⟩
        omega
      · rintro ⟨rfl, rfl⟩
        exact h34 hm
  · obtain ⟨hq, hm⟩ := h
    have h3 : 3 ∣ p ^ f + 1 := by omega
    refine ASVolIRegistered.multCyc_gen (hGr G .PSU 3 p f (Or.inl ⟨by decide, hm⟩)) ?_
      (burnsideI13_exc_psu3 p f)
    show (Nat.gcd 3 (p ^ f + 1), 1) = (3, 1)
    rw [Nat.gcd_eq_left h3]

private theorem burnsideI13_table3 (hA6 : quasithinMultiplierCyclic (alternatingGroup (Fin 6)) 6)
    (hA7 : quasithinMultiplierCyclic (alternatingGroup (Fin 7)) 6) (G : Type) [Group G]
    (h : ChIJK.ListedI13D6 G) : quasithinMultiplierCyclic G 6 := by
  rcases h with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact ASVolIRegistered.multCyc_congr e hA6
  · exact ASVolIRegistered.multCyc_congr e hA7

private theorem burnsideI13_table4
    (hM22 : quasithinMultiplierCyclic (CFSG.Blueprint.NativeSporadic.Carrier .M22) 12)
    (G : Type) [Group G] (h : CFSG.Blueprint.NativeSporadic.IsSporadic G .M22) :
    quasithinMultiplierCyclic G 12 := by
  obtain ⟨e⟩ := h
  exact ASVolIRegistered.multCyc_congr e hM22

private theorem burnsideI13_table5 (hGr : burnsideI13_Griess) (G : Type) [Group G]
    (h : CFSG.Blueprint.SuzukiModel G 2 3) :
    Nonempty (quasithinHopfMultiplier G ≃* Multiplicative (ZMod 2 × ZMod 2)) :=
  ASVolIRegistered.hopf_of_table (a := 1) (b := 1) (c := 2) (d := 2)
    (hGr G .twistedB2 0 2 3 (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, h⟩)))) (by decide) (by decide)
    (by
      letI : Unique (Multiplicative (ZMod 1)) := inferInstanceAs (Unique (Multiplicative (Fin 1)))
      letI : Unique (Multiplicative (ZMod 1) × Multiplicative (ZMod 1)) :=
        { default := (default, default),
          uniq := fun _ => Prod.ext (Unique.uniq _ _) (Unique.uniq _ _) }
      exact MulEquiv.uniqueProd.trans (MulEquiv.prodMultiplicative _ _).symm)

private theorem burnsideI13_table6 (hGr : burnsideI13_Griess) (G : Type) [Group G]
    (h : StatedClassicalModel G .PSL 3 2 2) :
    Nonempty (quasithinHopfMultiplier G ≃* Multiplicative (ZMod 4 × ZMod 4 × ZMod 3)) :=
  ASVolIRegistered.hopf_of_table (a := 3) (b := 1) (c := 4) (d := 4)
    (hGr G .PSL 3 2 2 (Or.inl ⟨by decide, h⟩)) (by decide) (by decide)
    (by
      letI : Unique (Multiplicative (ZMod 1)) := inferInstanceAs (Unique (Multiplicative (Fin 1)))
      exact (MulEquiv.prodCongr MulEquiv.prodUnique (MulEquiv.refl _)).trans
        (MulEquiv.prodComm.trans (MulEquiv.prodAssoc.trans
          ((MulEquiv.prodCongr (MulEquiv.refl _) (MulEquiv.prodMultiplicative _ _).symm).trans
            (MulEquiv.prodMultiplicative _ _).symm))))


private theorem burnsideI13_not_two_dvd (f : ℕ) (hf : 1 ≤ f) : ¬ 2 ∣ 2 ^ f - 1 := by
  obtain ⟨m, hm⟩ : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
  have h2 : 0 < 2 ^ f := by positivity
  omega

private theorem burnsideI13_false_of_row {X : Type} [Group X] {t : StatedLieTag} {n p f : ℕ}
    (hX : burnsideI13_Row X t n p f)
    (hg : CFSG.Blueprint.Multiplier.genericOrders t n p f = (1, 1))
    (he : CFSG.Blueprint.Multiplier.exceptionalOrders t n p f = (1, 1))
    (hn : Nontrivial (quasithinHopfMultiplier X)) : False := by
  haveI := burnsideI13_sub_of_row hX hg he
  exact false_of_nontrivial_of_subsingleton (quasithinHopfMultiplier X)

private theorem burnsideI13_false_of_iso {G S : Type} [Group G] [Group S] (e : G ≃* S)
    (hS : Subsingleton (quasithinHopfMultiplier S))
    (hn : Nontrivial (quasithinHopfMultiplier G)) : False := by
  haveI : Subsingleton (quasithinHopfMultiplier G) :=
    (CFSG.LieType.Steinberg.CentralExt.griessHopfMultiplierCongr e).toEquiv.subsingleton
  exact false_of_nontrivial_of_subsingleton (quasithinHopfMultiplier G)

private theorem burnsideI13_sub_of_simple_abelian {G : Type} [Group G] [IsSimpleGroup G]
    (hab : ∀ a b : G, a * b = b * a) : Subsingleton (quasithinHopfMultiplier G) := by
  haveI : IsCyclic G := by
    letI : CommGroup G := { ‹Group G› with mul_comm := hab }
    exact IsSimpleGroup.isCyclic
  exact burnsideI13_sub_cyclic

private theorem burnsideI13_goal_D2 {G : Type} [Group G] (h : ChIJK.ListedI13D2 G) :
    burnsideI13_Goal G := Or.inl h

private theorem burnsideI13_goal_D3 {G : Type} [Group G] (h : ChIJK.ListedI13D3 G) :
    burnsideI13_Goal G := Or.inr (Or.inl h)

private theorem burnsideI13_goal_D6 {G : Type} [Group G] (h : ChIJK.ListedI13D6 G) :
    burnsideI13_Goal G := Or.inr (Or.inr (Or.inl h))

private theorem burnsideI13_goal_L34 {G : Type} [Group G] (h : StatedClassicalModel G .PSL 3 2 2) :
    burnsideI13_Goal G := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

private theorem burnsideI13_goal_Sz8 {G : Type} [Group G] (h : CFSG.Blueprint.SuzukiModel G 2 3) :
    burnsideI13_Goal G := Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

private theorem burnsideI13_goal_M22 {G : Type} [Group G]
    (h : CFSG.Blueprint.NativeSporadic.IsSporadic G .M22) : burnsideI13_Goal G :=
  Or.inr (Or.inr (Or.inr (Or.inl h)))

private theorem burnsideI13_goal_alt {G : Type} [Group G] {n : ℕ}
    (h5 : 5 ≤ n) (h8 : n ≤ 8) (e : Nonempty (G ≃* alternatingGroup (Fin n))) :
    burnsideI13_Goal G := by
  interval_cases n
  · exact burnsideI13_goal_D2 (burnsideI13_D2_psl2 (p := 5) (f := 1) (by norm_num) le_rfl
      (by norm_num) (burnsideI13_psl25_of_alt5 e))
  · exact burnsideI13_goal_D6 (Or.inl e)
  · exact burnsideI13_goal_D6 (Or.inr e)
  · exact burnsideI13_goal_D2 (burnsideI13_D2_psl4 (burnsideI13_psl42_of_alt8 e))

private theorem burnsideI13_goal_psl2_odd {G : Type} [Group G] {p f : ℕ} (hp : p ≠ 2) (hf : 1 ≤ f)
    (h : StatedClassicalModel G .PSL 2 p f) : burnsideI13_Goal G := by
  by_cases h9 : p ^ f = 9
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
    have : Fintype K := Fintype.ofFinite K
    have hK9 : Fintype.card K = 9 := by rw [← Nat.card_eq_fintype_card, hK, h9]
    obtain ⟨e6⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.unique_field_nine_projective_linear_alternating_six_isomorphism
        K hK9
    exact burnsideI13_goal_D6 (Or.inl ⟨e.trans
      ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm.trans e6)⟩)
  · exact burnsideI13_goal_D2 (burnsideI13_D2_psl2 hp hf h9 h)

private theorem burnsideI13_goal_psl3 (hGr : burnsideI13_Griess) {G : Type} [Group G] {p f : ℕ}
    (h1 : ¬ (p = 2 ∧ f = 1)) (h34 : ¬ StatedClassicalModel G .PSL 3 2 2)
    (hn : Nontrivial (quasithinHopfMultiplier G)) (h : StatedClassicalModel G .PSL 3 p f) :
    burnsideI13_Goal G := by
  have h2 : ¬ (p = 2 ∧ f = 2) := by
    rintro ⟨rfl, rfl⟩
    exact h34 h
  by_cases hq : p ^ f % 3 = 1
  · exact burnsideI13_goal_D3 (burnsideI13_D3_psl hq h h34)
  · exfalso
    have hpos : 0 < p ^ f := pow_pos h.1.1.pos f
    refine burnsideI13_false_of_row (hGr G .PSL 3 p f (Or.inl ⟨by decide, h⟩)) ?_
      (burnsideI13_exc_psl3 p f h1 h2) hn
    show (Nat.gcd 3 (p ^ f - 1), 1) = (1, 1)
    rw [burnsideI13_gcd_three (by omega)]

private theorem burnsideI13_goal_psu3 (hGr : burnsideI13_Griess) {G : Type} [Group G] {p f : ℕ}
    (h34 : ¬ StatedClassicalModel G .PSL 3 2 2) (hn : Nontrivial (quasithinHopfMultiplier G))
    (h : StatedClassicalModel G .PSU 3 p f) : burnsideI13_Goal G := by
  by_cases hq : p ^ f % 3 = 2
  · exact burnsideI13_goal_D3 (burnsideI13_D3_psu hq h h34)
  · exfalso
    refine burnsideI13_false_of_row (hGr G .PSU 3 p f (Or.inl ⟨by decide, h⟩)) ?_
      (burnsideI13_exc_psu3 p f) hn
    show (Nat.gcd 3 (p ^ f + 1), 1) = (1, 1)
    rw [burnsideI13_gcd_three (by omega)]


private theorem burnsideI13_goal_char2 (hGr : burnsideI13_Griess)
    {G : Type} [Group G] (h34 : ¬ StatedClassicalModel G .PSL 3 2 2)
    (hn : Nontrivial (quasithinHopfMultiplier G)) {f : ℕ}
    (h : (2 ≤ f ∧ StatedClassicalModel G .PSL 2 2 f) ∨ (1 ≤ f ∧ StatedClassicalModel G .PSL 3 2 f) ∨
      (2 ≤ f ∧ StatedClassicalModel G .PSU 3 2 f) ∨ (2 ≤ f ∧ StatedClassicalModel G .PSp 2 2 f) ∨
      (2 ≤ f ∧ CFSG.Blueprint.ChevalleyExceptionalModel G .G2 2 f) ∨
      (1 ≤ f ∧ CFSG.Blueprint.ChevalleyExceptionalModel G .trialityD4 2 f) ∨
      (Odd f ∧ 3 ≤ f ∧ CFSG.Blueprint.ReeTitsModel G .twistedF4 2 f) ∨
      (Odd f ∧ 3 ≤ f ∧ CFSG.Blueprint.SuzukiModel G 2 f)) :
    burnsideI13_Goal G := by
  rcases h with ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨hodd, hf, h⟩ |
    ⟨hodd, hf, h⟩
  ·
    by_cases hf2 : f = 2
    · subst hf2
      exact burnsideI13_goal_D2 (burnsideI13_D2_psl2 (p := 5) (f := 1) (by norm_num) le_rfl
        (by norm_num) (burnsideI13_psl25_of_psl24 h))
    · exfalso
      refine burnsideI13_false_of_row (hGr G .PSL 2 2 f (Or.inl ⟨by decide, h⟩)) ?_
        (burnsideI13_exc_psl2_two f (by omega)) hn
      show (Nat.gcd 2 (2 ^ f - 1), 1) = (1, 1)
      rw [burnsideI13_gcd_two (burnsideI13_not_two_dvd f (by omega))]
  ·
    by_cases hf1 : f = 1
    · subst hf1
      exact burnsideI13_goal_D2 (burnsideI13_D2_psl2 (p := 7) (f := 1) (by norm_num) le_rfl
        (by norm_num) (burnsideI13_psl27_of_psl32 h))
    · exact burnsideI13_goal_psl3 hGr (fun h' => hf1 h'.2) h34 hn h
  ·
    exact burnsideI13_goal_psu3 hGr h34 hn h
  ·
    exfalso
    refine burnsideI13_false_of_row (hGr G .PSp 2 2 f (Or.inl ⟨by decide, h⟩)) ?_
      (burnsideI13_exc_psp2 2 f) hn
    show (Nat.gcd 2 (2 ^ f - 1), 1) = (1, 1)
    rw [burnsideI13_gcd_two (burnsideI13_not_two_dvd f (by omega))]
  ·
    by_cases hf2 : f = 2
    · subst hf2
      exact burnsideI13_goal_D2 (burnsideI13_D2_g2 h)
    · exfalso
      exact burnsideI13_false_of_row (hGr G .G2 0 2 f (Or.inr (Or.inl ⟨rfl, by decide, h⟩))) rfl
        (burnsideI13_exc_g2_two f (by omega)) hn
  ·
    exfalso
    exact burnsideI13_false_of_row (hGr G .trialityD4 0 2 f (Or.inr (Or.inl ⟨rfl, by decide, h⟩)))
      rfl rfl hn
  ·
    exfalso
    exact burnsideI13_false_of_row
      (hGr G .twistedF4 0 2 f (Or.inr (Or.inr (Or.inl ⟨rfl, by decide, h⟩)))) rfl rfl hn
  ·
    by_cases hf3 : f = 3
    · subst hf3
      exact burnsideI13_goal_Sz8 h
    · exfalso
      obtain ⟨k, hk⟩ := hodd
      exact burnsideI13_false_of_row
        (hGr G .twistedB2 0 2 f (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, h⟩)))) rfl
        (burnsideI13_exc_suzuki f (by omega)) hn


private theorem burnsideI13_goal_spor
    (hT : ∀ s : TauCeti.SporadicName,
      (s = .M11 ∨ s = .M23 ∨ s = .M24 ∨ s = .J1 ∨ s = .J4 ∨ s = .He) →
        Subsingleton (quasithinHopfMultiplier (CFSG.Blueprint.NativeSporadic.Carrier s)))
    {G : Type} [Group G] (hn : Nontrivial (quasithinHopfMultiplier G)) {s : TauCeti.SporadicName}
    (hs : s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24 ∨ s = .J1 ∨ s = .J2 ∨ s = .J4 ∨
      s = .HS ∨ s = .He ∨ s = .Ru)
    (e : Nonempty (G ≃* CFSG.Blueprint.NativeSporadic.Carrier s)) : burnsideI13_Goal G := by
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (burnsideI13_false_of_iso e.some (hT _ (by simp)) hn).elim
  · exact burnsideI13_goal_D2 (burnsideI13_D2_M12 e)
  · exact burnsideI13_goal_M22 e
  · exact (burnsideI13_false_of_iso e.some (hT _ (by simp)) hn).elim
  · exact (burnsideI13_false_of_iso e.some (hT _ (by simp)) hn).elim
  · exact (burnsideI13_false_of_iso e.some (hT _ (by simp)) hn).elim
  · exact burnsideI13_goal_D2 (burnsideI13_D2_J2 e)
  · exact (burnsideI13_false_of_iso e.some (hT _ (by simp)) hn).elim
  · exact burnsideI13_goal_D2 (burnsideI13_D2_HS e)
  · exact (burnsideI13_false_of_iso e.some (hT _ (by simp)) hn).elim
  · exact burnsideI13_goal_D2 (burnsideI13_D2_Ru e)

private theorem burnsideI13_complete (hGr : burnsideI13_Griess)
    (hC : ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], (∃ a b : S, a * b ≠ b * a) →
      CFSG.SectionRank.IsSQTKCat S → CFSG.Milestones.SQTKSimpleList S)
    (hT : ∀ s : TauCeti.SporadicName,
      (s = .M11 ∨ s = .M23 ∨ s = .M24 ∨ s = .J1 ∨ s = .J4 ∨ s = .He) →
        Subsingleton (quasithinHopfMultiplier (CFSG.Blueprint.NativeSporadic.Carrier s)))
    (G : Type) [Group G] [Finite G] (hs : IsSimpleGroup G) (hK : CFSG.SectionRank.IsSQTKCat G)
    (hn : Nontrivial (quasithinHopfMultiplier G)) : burnsideI13_Goal G := by
  haveI := hs
  by_cases hab : ∃ a b : G, a * b ≠ b * a
  · by_cases h34 : StatedClassicalModel G .PSL 3 2 2
    · exact burnsideI13_goal_L34 h34
    rcases hC G hab hK with ⟨n, h5, h8, e⟩ | ⟨p, hp, hp2, ⟨f, hf, h⟩ | h | h⟩ | (⟨f, h⟩ | h) |
      ⟨n, hn45, h⟩ | ⟨s, hs, e⟩
    · exact burnsideI13_goal_alt h5 h8 e
    · exact burnsideI13_goal_psl2_odd hp2 (by omega) h
    · exact burnsideI13_goal_psl3 hGr (fun h' => hp2 h'.1) h34 hn h
    · exact burnsideI13_goal_psu3 hGr h34 hn h
    · exact burnsideI13_goal_char2 hGr h34 hn h
    ·
      exfalso
      exact burnsideI13_false_of_row (hGr G .Tits 0 2 1 (Or.inr (Or.inr (Or.inl ⟨rfl, by decide, h⟩))))
        rfl rfl hn
    · rcases hn45 with rfl | rfl
      · exact burnsideI13_goal_D2 (burnsideI13_D2_psl4 h)
      · exfalso
        refine burnsideI13_false_of_row (hGr G .PSL 5 2 1 (Or.inl ⟨by decide, h⟩)) ?_
          burnsideI13_exc_psl5 hn
        decide
    · exact burnsideI13_goal_spor hT hn hs e
  · exfalso
    haveI := burnsideI13_sub_of_simple_abelian fun a b => by
      by_contra h
      exact hab ⟨a, b, h⟩
    exact false_of_nontrivial_of_subsingleton (quasithinHopfMultiplier G)



private theorem burnsideI13_sub_of_card {S : Type} [Group S]
    (h : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier S) = 1) :
    Subsingleton (quasithinHopfMultiplier S) := by
  haveI := (Nat.card_eq_one_iff_unique.1 h).1
  exact (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess S).toEquiv.subsingleton

private theorem burnsideI13_trivRows :
    ∀ s : TauCeti.SporadicName, (s = .M11 ∨ s = .M23 ∨ s = .M24 ∨ s = .J1 ∨ s = .J4 ∨ s = .He) →
      Subsingleton (quasithinHopfMultiplier (CFSG.Blueprint.NativeSporadic.Carrier s)) := by
  intro s hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
  · exact burnsideI13_sub_of_card
      ((CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.nativeRow_M11).trans
        (by decide))
  · exact burnsideI13_sub_of_card
      ((CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.nativeRow_M23).trans
        (by decide))
  · exact burnsideI13_sub_of_card
      ((CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.nativeRow_M24).trans
        (by decide))
  · exact burnsideI13_sub_of_card
      ((CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.nativeRow_J1).trans
        (by decide))
  · exact burnsideI13_sub_of_card
      ((CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.nativeRow_J4).trans
        (by decide))
  · exact burnsideI13_sub_of_card
      ((CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.nativeRow_He).trans
        (by decide))

end BurnsideI13_only13

section

theorem as_I_1_3
    : I_1_3 := by
  have hGr : burnsideI13_Griess := fun X _ t n p f h => ASVolIRegistered.griess h
  have hC : ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], (∃ a b : S, a * b ≠ b * a) →
      CFSG.SectionRank.IsSQTKCat S → CFSG.Milestones.SQTKSimpleList S :=
    fun S _ _ _ hn hK => CFSG.Milestones.cl_lit_sqtk_simple_list_simple S hn hK
  have hT := burnsideI13_trivRows
  have hM12 : quasithinMultiplierCyclic (CFSG.Blueprint.NativeSporadic.Carrier .M12) 2 :=
    ASVolIRegistered.multCyc_of_hopf_prime Nat.prime_two
      CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.nativeRow_M12
  have hJ2 : quasithinMultiplierCyclic (CFSG.Blueprint.NativeSporadic.Carrier .J2) 2 :=
    ASVolIRegistered.multCyc_of_hopf_prime Nat.prime_two
      CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.nativeRow_J2
  have hHS : quasithinMultiplierCyclic (CFSG.Blueprint.NativeSporadic.Carrier .HS) 2 :=
    ASVolIRegistered.multCyc_of_hopf_prime Nat.prime_two
      CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.nativeRow_HS
  have hRu : quasithinMultiplierCyclic (CFSG.Blueprint.NativeSporadic.Carrier .Ru) 2 :=
    ASVolIRegistered.multCyc_of_hopf_prime Nat.prime_two
      CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.nativeRow_Ru
  have hM22 : quasithinMultiplierCyclic (CFSG.Blueprint.NativeSporadic.Carrier .M22) 12 :=
    ASVolIRegistered.multCyc_M22
  refine ⟨fun G _ _ hs hK hn => burnsideI13_complete hGr hC hT G hs hK hn,
    fun G _ _ h => burnsideI13_table1 hGr hM12 hJ2 hHS hRu G h,
    fun G _ _ h => burnsideI13_table2 hGr G h,
    fun G _ _ h => burnsideI13_table3 ASVolIRegistered.multCyc_A6 ASVolIRegistered.multCyc_A7 G h,
    fun G _ _ h => burnsideI13_table4 hM22 G h,
    fun G _ _ h => burnsideI13_table5 hGr G h,
    fun G _ _ h => burnsideI13_table6 hGr G h⟩

end

@[expose] def I_1_4 : Prop :=
  (∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → CFSG.SectionRank.IsKGroupCat G →
    CFSG.Quasithin.IsQuasithin G → ¬ CFSG.IsStronglyQuasithin G →
    Nontrivial (quasithinHopfMultiplier G) →
    ListedI14D2 G ∨ ListedI14D3 G ∨ ListedI14D4 G ∨ StatedClassicalModel G .PSU 5 2 2 ∨
      StatedClassicalModel G .PSU 4 3 1 ∨
      StatedClassicalModel G .PSp 3 2 1 ∨
      (∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ StatedClassicalModel G .PSp 2 p 1)) ∧
  (∀ (G : Type) [Group G] [Finite G], ListedI14D2 G → quasithinMultiplierCyclic G 2) ∧
  (∀ (G : Type) [Group G] [Finite G], ListedI14D3 G → quasithinMultiplierCyclic G 3) ∧
  (∀ (G : Type) [Group G] [Finite G], ListedI14D4 G → quasithinMultiplierCyclic G 4) ∧
  (∀ (G : Type) [Group G] [Finite G], StatedClassicalModel G .PSU 5 2 2 →
    quasithinMultiplierCyclic G 5) ∧
  (∀ (G : Type) [Group G] [Finite G], StatedClassicalModel G .PSU 4 3 1 →
    Nonempty (quasithinHopfMultiplier G ≃* Multiplicative (ZMod 3 × ZMod 3 × ZMod 4))) ∧
  (∀ (G : Type) [Group G] [Finite G], StatedClassicalModel G .PSp 3 2 1 →
    quasithinMultiplierCyclic G 2) ∧
  (∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → 5 ≤ p →
    StatedClassicalModel G .PSp 2 p 1 → quasithinMultiplierCyclic G 2)

private theorem burnsideI13_i14_exc_psl4_odd (p f : ℕ) (hp : p ≠ 2) :
    CFSG.Blueprint.Multiplier.exceptionalOrders .PSL 4 p f = (1, 1) := by
  unfold CFSG.Blueprint.Multiplier.exceptionalOrders
  split <;> first | rfl | (exfalso; simp_all)

private theorem burnsideI13_i14_exc_psu4_odd (p f : ℕ) (hp : p ≠ 2) (h3 : ¬ (p = 3 ∧ f = 1)) :
    CFSG.Blueprint.Multiplier.exceptionalOrders .PSU 4 p f = (1, 1) := by
  unfold CFSG.Blueprint.Multiplier.exceptionalOrders
  split <;> first | rfl | (exfalso; simp_all)

private theorem burnsideI13_i14_exc_psu4_two (f : ℕ) (hf : 2 ≤ f) :
    CFSG.Blueprint.Multiplier.exceptionalOrders .PSU 4 2 f = (1, 1) := by
  unfold CFSG.Blueprint.Multiplier.exceptionalOrders
  split <;> first | rfl | (exfalso; simp_all <;> omega)

private theorem burnsideI13_i14_exc_g2_odd (p : ℕ) (hp : p ≠ 2) (h3 : p ≠ 3) :
    CFSG.Blueprint.Multiplier.exceptionalOrders .G2 0 p 1 = (1, 1) := by
  unfold CFSG.Blueprint.Multiplier.exceptionalOrders
  split <;> first | rfl | (exfalso; simp_all)

private theorem burnsideI13_i14_sqt_of_card {G : Type} [Group G] [Finite G]
    (h : ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ^ 3 ∣ Nat.card G) : CFSG.IsStronglyQuasithin G := by
  intro p hp hp2
  unfold CFSG.pRank
  refine csSup_le' ?_
  rintro r ⟨A, -, hcard⟩
  by_contra hr
  have hr3 : 3 ≤ r := by omega
  have h1 : p ^ 3 ∣ p ^ r := pow_dvd_pow p hr3
  rw [← hcard] at h1
  exact h p hp hp2 (h1.trans (Subgroup.card_subgroup_dvd_card A))

private theorem burnsideI13_i14_no_cube {N B : ℕ} (hN : 0 < N) (hB : N < (B + 1) ^ 3)
    (h : ∀ p < B + 1, p.Prime → p ≠ 2 → ¬ p ^ 3 ∣ N) :
    ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ^ 3 ∣ N := by
  intro p hp hp2 hd
  have hle : p ^ 3 ≤ N := Nat.le_of_dvd hN hd
  have hpB : p < B + 1 := by
    by_contra hc
    have : (B + 1) ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left (by omega) 3
    omega
  exact h p hpB hp hp2 hd

private theorem burnsideI13_i14_sqt_60 {G : Type} [Group G] [Finite G] (h : Nat.card G = 60) :
    CFSG.IsStronglyQuasithin G := by
  refine burnsideI13_i14_sqt_of_card ?_
  rw [h]
  exact burnsideI13_i14_no_cube (B := 3) (by norm_num) (by norm_num) (by decide)

private theorem burnsideI13_i14_sqt_168 {G : Type} [Group G] [Finite G] (h : Nat.card G = 168) :
    CFSG.IsStronglyQuasithin G := by
  refine burnsideI13_i14_sqt_of_card ?_
  rw [h]
  exact burnsideI13_i14_no_cube (B := 5) (by norm_num) (by norm_num) (by decide)

private theorem burnsideI13_i14_sqt_360 {G : Type} [Group G] [Finite G] (h : Nat.card G = 360) :
    CFSG.IsStronglyQuasithin G := by
  refine burnsideI13_i14_sqt_of_card ?_
  rw [h]
  exact burnsideI13_i14_no_cube (B := 7) (by norm_num) (by norm_num) (by decide)

private theorem burnsideI13_i14_sqt_2520 {G : Type} [Group G] [Finite G] (h : Nat.card G = 2520) :
    CFSG.IsStronglyQuasithin G := by
  refine burnsideI13_i14_sqt_of_card ?_
  rw [h]
  exact burnsideI13_i14_no_cube (B := 13) (by norm_num) (by norm_num) (by decide)

private theorem burnsideI13_i14_sqt_20160 {G : Type} [Group G] [Finite G] (h : Nat.card G = 20160) :
    CFSG.IsStronglyQuasithin G := by
  refine burnsideI13_i14_sqt_of_card ?_
  rw [h]
  exact burnsideI13_i14_no_cube (B := 27) (by norm_num) (by norm_num) (by decide)

private theorem burnsideI13_i14_sqt_29120 {G : Type} [Group G] [Finite G] (h : Nat.card G = 29120) :
    CFSG.IsStronglyQuasithin G := by
  refine burnsideI13_i14_sqt_of_card ?_
  rw [h]
  exact burnsideI13_i14_no_cube (B := 30) (by norm_num) (by norm_num) (by decide)

private theorem burnsideI13_i14_sqt_443520 {G : Type} [Group G] [Finite G] (h : Nat.card G = 443520) :
    CFSG.IsStronglyQuasithin G := by
  refine burnsideI13_i14_sqt_of_card ?_
  rw [h]
  exact burnsideI13_i14_no_cube (B := 76) (by norm_num) (by norm_num) (by decide)

private theorem burnsideI13_i14_table1 (hGr : burnsideI13_Griess)
    (hA9 : quasithinMultiplierCyclic (alternatingGroup (Fin 9)) 2)
    (G : Type) [Group G] (h : ChIJK.ListedI14D2 G) : quasithinMultiplierCyclic G 2 := by
  rcases h with ⟨⟨e⟩⟩ | h | h | ⟨p, f, hp, hf, h9, h⟩
  · exact ASVolIRegistered.multCyc_congr e hA9
  · exact ASVolIRegistered.multCyc_exc (hGr G .PSU 4 2 1 (Or.inl ⟨by decide, h⟩)) (by decide)
      (by decide)
  · exact ASVolIRegistered.multCyc_gen (hGr G .PSL 4 3 1 (Or.inl ⟨by decide, h⟩)) (by decide)
      (by decide)
  · have hpp : p.Prime := h.1.1
    have hodd := ASVolIRegistered.odd_pow_of_ne_two (k := f) hpp hp
    refine ASVolIRegistered.multCyc_gen (hGr G .PSL 2 p f (Or.inl ⟨by decide, h⟩)) ?_
      (burnsideI13_exc_psl2 p f hp (by omega))
    show (Nat.gcd 2 (p ^ f - 1), 1) = (2, 1)
    rw [ASVolIRegistered.gcd_two_odd hodd]

private theorem burnsideI13_i14_table2 (hGr : burnsideI13_Griess)
    (hJ3 : quasithinMultiplierCyclic (CFSG.Blueprint.NativeSporadic.Carrier .J3) 3)
    (hMcL : quasithinMultiplierCyclic (CFSG.Blueprint.NativeSporadic.Carrier .McL) 3)
    (G : Type) [Group G] (h : ChIJK.ListedI14D3 G) : quasithinMultiplierCyclic G 3 := by
  rcases h with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | h | ⟨p, f, hp, h | h⟩
  · exact ASVolIRegistered.multCyc_congr e hJ3
  · exact ASVolIRegistered.multCyc_congr e hMcL
  · exact ASVolIRegistered.multCyc_exc (hGr G .G2 0 3 1 (Or.inr (Or.inl ⟨rfl, by decide, h⟩)))
      rfl (by decide)
  · obtain ⟨hq, hm⟩ := h
    have h3 : 3 ∣ p ^ f - 1 := by omega
    refine ASVolIRegistered.multCyc_gen (hGr G .PSL 3 p f (Or.inl ⟨by decide, hm⟩)) ?_
      (burnsideI13_exc_psl3 p f (fun h' => hp h'.1) (fun h' => hp h'.1))
    show (Nat.gcd 3 (p ^ f - 1), 1) = (3, 1)
    rw [Nat.gcd_eq_left h3]
  · obtain ⟨hq, hm⟩ := h
    have h3 : 3 ∣ p ^ f + 1 := by omega
    refine ASVolIRegistered.multCyc_gen (hGr G .PSU 3 p f (Or.inl ⟨by decide, hm⟩)) ?_
      (burnsideI13_exc_psu3 p f)
    show (Nat.gcd 3 (p ^ f + 1), 1) = (3, 1)
    rw [Nat.gcd_eq_left h3]

private theorem burnsideI13_i14_table3 (hGr : burnsideI13_Griess) (G : Type) [Group G]
    (h : ChIJK.ListedI14D4 G) : quasithinMultiplierCyclic G 4 := by
  rcases h with ⟨r, m, hrp, hr, h3, h⟩ | ⟨s, m, hsp, hs, h3, h⟩
  · have hm : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with rfl | h'
      · simp at hr; omega
      · exact h'
    have h4 : 4 ∣ r - 1 := by
      have h2m : 2 ≤ 2 ^ m := Nat.one_lt_two_pow_iff.2 (by omega)
      rw [hr, Nat.add_sub_cancel]
      exact dvd_trans (by norm_num) (pow_dvd_pow 2 h2m)
    refine ASVolIRegistered.multCyc_gen (hGr G .PSL 4 r 1 (Or.inl ⟨by decide, h⟩)) ?_
      (burnsideI13_i14_exc_psl4_odd r 1 (by omega))
    show (Nat.gcd 4 (r ^ 1 - 1), 1) = (4, 1)
    rw [pow_one, Nat.gcd_eq_left h4]
  · have h4 : 4 ∣ s + 1 := by
      have hpos : 1 ≤ 2 ^ m := Nat.one_le_two_pow
      have hm : 2 ≤ m := by
        by_contra hlt
        interval_cases m <;> simp at hs <;> omega
      rw [hs, Nat.sub_add_cancel hpos]
      exact dvd_trans (by norm_num) (pow_dvd_pow 2 hm)
    refine ASVolIRegistered.multCyc_gen (hGr G .PSU 4 s 1 (Or.inl ⟨by decide, h⟩)) ?_
      (burnsideI13_i14_exc_psu4_odd s 1 (by omega) (by omega))
    show (Nat.gcd 4 (s ^ 1 + 1), 1) = (4, 1)
    rw [pow_one, Nat.gcd_eq_left h4]

private theorem burnsideI13_i14_table4 (hGr : burnsideI13_Griess) (G : Type) [Group G]
    (h : StatedClassicalModel G .PSU 5 2 2) : quasithinMultiplierCyclic G 5 :=
  ASVolIRegistered.multCyc_gen (hGr G .PSU 5 2 2 (Or.inl ⟨by decide, h⟩)) (by decide)
    (by decide)

private theorem burnsideI13_i14_table5 (hGr : burnsideI13_Griess) (G : Type) [Group G]
    (h : StatedClassicalModel G .PSU 4 3 1) :
    Nonempty (quasithinHopfMultiplier G ≃* Multiplicative (ZMod 3 × ZMod 3 × ZMod 4)) :=
  ASVolIRegistered.hopf_of_table (a := 4) (b := 1) (c := 3) (d := 3)
    (hGr G .PSU 4 3 1 (Or.inl ⟨by decide, h⟩)) (by decide) (by decide)
    (by
      letI : Unique (Multiplicative (ZMod 1)) := inferInstanceAs (Unique (Multiplicative (Fin 1)))
      exact (MulEquiv.prodCongr MulEquiv.prodUnique (MulEquiv.refl _)).trans
        (MulEquiv.prodComm.trans (MulEquiv.prodAssoc.trans
          ((MulEquiv.prodCongr (MulEquiv.refl _) (MulEquiv.prodMultiplicative _ _).symm).trans
            (MulEquiv.prodMultiplicative _ _).symm))))

private theorem burnsideI13_i14_table6 (hGr : burnsideI13_Griess) (G : Type) [Group G]
    (h : StatedClassicalModel G .PSp 3 2 1) : quasithinMultiplierCyclic G 2 :=
  ASVolIRegistered.multCyc_exc (hGr G .PSp 3 2 1 (Or.inl ⟨by decide, h⟩)) (by decide)
    (by decide)

private theorem burnsideI13_i14_table7 (hGr : burnsideI13_Griess) (G : Type) [Group G] (p : ℕ)
    (hp : p.Prime) (hp5 : 5 ≤ p) (h : StatedClassicalModel G .PSp 2 p 1) :
    quasithinMultiplierCyclic G 2 := by
  have hodd : Odd (p ^ 1) := by
    rw [pow_one]
    exact hp.odd_of_ne_two (by omega)
  refine ASVolIRegistered.multCyc_gen (hGr G .PSp 2 p 1 (Or.inl ⟨by decide, h⟩)) ?_
    (burnsideI13_exc_psp2 p 1)
  show (Nat.gcd 2 (p ^ 1 - 1), 1) = (2, 1)
  rw [ASVolIRegistered.gcd_two_odd hodd]

private def burnsideI13_i14_Goal (G : Type) [Group G] : Prop :=
  ChIJK.ListedI14D2 G ∨ ChIJK.ListedI14D3 G ∨ ChIJK.ListedI14D4 G ∨
    StatedClassicalModel G .PSU 5 2 2 ∨ StatedClassicalModel G .PSU 4 3 1 ∨
    StatedClassicalModel G .PSp 3 2 1 ∨
    (∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ StatedClassicalModel G .PSp 2 p 1)

private theorem burnsideI13_i14_D2_alt9 {G : Type} [Group G] (h : Nonempty (G ≃* alternatingGroup (Fin 9))) :
    ChIJK.ListedI14D2 G := Or.inl h

private theorem burnsideI13_i14_D2_psu42 {G : Type} [Group G] (h : StatedClassicalModel G .PSU 4 2 1) :
    ChIJK.ListedI14D2 G := Or.inr (Or.inl h)

private theorem burnsideI13_i14_D2_psl43 {G : Type} [Group G] (h : StatedClassicalModel G .PSL 4 3 1) :
    ChIJK.ListedI14D2 G := Or.inr (Or.inr (Or.inl h))

private theorem burnsideI13_i14_D2_psl2 {G : Type} [Group G] {p f : ℕ} (hp : p ≠ 2) (hf : 1 ≤ f)
    (h9 : 9 < p ^ f) (h : StatedClassicalModel G .PSL 2 p f) : ChIJK.ListedI14D2 G :=
  Or.inr (Or.inr (Or.inr ⟨p, f, hp, hf, h9, h⟩))

private theorem burnsideI13_i14_D3_J3 {G : Type} [Group G]
    (h : CFSG.Blueprint.NativeSporadic.IsSporadic G .J3) : ChIJK.ListedI14D3 G := Or.inl h

private theorem burnsideI13_i14_D3_McL {G : Type} [Group G]
    (h : CFSG.Blueprint.NativeSporadic.IsSporadic G .McL) : ChIJK.ListedI14D3 G :=
  Or.inr (Or.inl h)

private theorem burnsideI13_i14_D3_g2 {G : Type} [Group G]
    (h : CFSG.Blueprint.ChevalleyExceptionalModel G .G2 3 1) : ChIJK.ListedI14D3 G :=
  Or.inr (Or.inr (Or.inl h))

private theorem burnsideI13_i14_D3_psl {G : Type} [Group G] {p f : ℕ} (hp : p ≠ 2) (hq : p ^ f % 3 = 1)
    (h : StatedClassicalModel G .PSL 3 p f) : ChIJK.ListedI14D3 G :=
  Or.inr (Or.inr (Or.inr ⟨p, f, hp, Or.inl ⟨hq, h⟩⟩))

private theorem burnsideI13_i14_D3_psu {G : Type} [Group G] {p f : ℕ} (hp : p ≠ 2) (hq : p ^ f % 3 = 2)
    (h : StatedClassicalModel G .PSU 3 p f) : ChIJK.ListedI14D3 G :=
  Or.inr (Or.inr (Or.inr ⟨p, f, hp, Or.inr ⟨hq, h⟩⟩))

private theorem burnsideI13_i14_psu42_of_psp23 {G : Type} [Group G] (h : StatedClassicalModel G .PSp 2 3 1) :
    StatedClassicalModel G .PSU 4 2 1 := by
  have hP : StatedClassicalModel CFSG.GH74.Exceptional.PSp43 .PSp 2 3 1 :=
    ⟨h.1, ZMod 3, inferInstance, inferInstance, by simp, ⟨MulEquiv.refl _⟩⟩
  obtain ⟨e⟩ := CFSG.Blueprint.EvenSource.nonempty_mulEquiv_of_statedClassicalModel h hP
  exact ⟨⟨Nat.prime_two, le_rfl, by norm_num, by decide⟩, CFSG.Blueprint.Fischer.K,
    inferInstance, inferInstance, CFSG.Fischer.Classification.Unitary.card_K,
    ⟨e.trans (CFSG.GH74.Exceptional.psp43EquivU2.trans CFSG.GH74.Exceptional.u2FourEquiv)⟩⟩

private theorem burnsideI13_i14_sqt_psl3_two {G : Type} [Group G] [Finite G] {f : ℕ}
    (h : StatedClassicalModel G .PSL 3 2 f) : CFSG.IsStronglyQuasithin G := by
  obtain ⟨e⟩ := CFSG.RankThree.PartOne.projSL_of_statedClassicalModel h
  have hf : 1 ≤ f := h.1.2.1
  rw [CFSG.SectionRank.isStronglyQuasithin_iff]
  intro r hr hr2
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hr.one_lt e]
  exact CFSG.RankThree.PartOne.LIT.pRank_projSL_three_le (K := GaloisField 2 f) hf
    (GaloisField.card 2 f (by omega)) hr hr2

private theorem burnsideI13_i14_sqt_psu3_two {G : Type} [Group G] [Finite G] {f : ℕ}
    (h : StatedClassicalModel G .PSU 3 2 f) : CFSG.IsStronglyQuasithin G := by
  obtain ⟨e⟩ := CFSG.RankThree.PartOne.projSU_of_statedClassicalModel h
  have hf : 1 ≤ f := h.1.2.1
  rw [CFSG.SectionRank.isStronglyQuasithin_iff]
  intro r hr hr2
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hr.one_lt e]
  exact CFSG.RankThree.PartOne.LIT.pRank_projSU_three_le hf hr hr2

private theorem burnsideI13_i14_sqt_psl2_small {G : Type} [Group G] [Finite G] {p f : ℕ} (hp : p ≠ 2)
    (hq : p ^ f ≤ 9) (h : StatedClassicalModel G .PSL 2 p f) : CFSG.IsStronglyQuasithin G := by
  have hcard : Nat.card G = ordA 1 (p ^ f) :=
    (CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two hp h).1 rfl
  have hpp : p.Prime := h.1.1
  have hf1 : 1 ≤ f := h.1.2.1
  have h3 : 3 ≤ p := by
    have := hpp.two_le
    omega
  have hle : p ≤ p ^ f := Nat.le_self_pow (by omega) p
  have hodd : p ^ f % 2 = 1 := Nat.odd_iff.1 (ASVolIRegistered.odd_pow_of_ne_two hpp hp)
  have hne3 : p ^ f ≠ 3 := fun h3' => h.1.2.2.2.2 (by rw [h3'])
  have hq5 : p ^ f = 5 ∨ p ^ f = 7 ∨ p ^ f = 9 := by omega
  rcases hq5 with hq5 | hq5 | hq5 <;> rw [hq5] at hcard
  · exact burnsideI13_i14_sqt_60 (hcard.trans (by decide))
  · exact burnsideI13_i14_sqt_168 (hcard.trans (by decide))
  · exact burnsideI13_i14_sqt_360 (hcard.trans (by decide))

private theorem burnsideI13_i14_sqt_psl24 {G : Type} [Group G] [Finite G]
    (h : StatedClassicalModel G .PSL 2 2 2) : CFSG.IsStronglyQuasithin G :=
  burnsideI13_i14_sqt_60 (((CFSG.Timmesfeld.card_statedClassicalModel_two h).1 rfl).trans (by decide))

private theorem burnsideI13_i14_sqt_psl42 {G : Type} [Group G] [Finite G]
    (h : StatedClassicalModel G .PSL 4 2 1) : CFSG.IsStronglyQuasithin G :=
  burnsideI13_i14_sqt_20160
    (((CFSG.Timmesfeld.card_statedClassicalModel_two h).1 rfl).trans (by decide))

private theorem burnsideI13_i14_sqt_sz8 {G : Type} [Group G] [Finite G]
    (h : CFSG.Blueprint.SuzukiModel G 2 3) : CFSG.IsStronglyQuasithin G := by
  obtain ⟨-, a, ha, K, _, _, hf, hK, ⟨e⟩⟩ := h
  have ha1 : a = 1 := by omega
  subst ha1
  refine burnsideI13_i14_sqt_29120 ?_
  rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order (a := 1) (K := K) (by simpa using hK)]
  norm_num

private theorem burnsideI13_i14_sqt_M22 {G : Type} [Group G] [Finite G]
    (h : CFSG.Blueprint.NativeSporadic.IsSporadic G .M22) : CFSG.IsStronglyQuasithin G := by
  obtain ⟨e⟩ := h
  exact burnsideI13_i14_sqt_443520
    ((Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Mathieu.card_M22)

private theorem burnsideI13_i14_sqt_alt {G : Type} [Group G] [Finite G] {n : ℕ} (h5 : 5 ≤ n) (h8 : n ≤ 8)
    (e : Nonempty (G ≃* alternatingGroup (Fin n))) : CFSG.IsStronglyQuasithin G := by
  obtain ⟨e⟩ := e
  have hcard : Nat.card G = n.factorial / 2 := by
    haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  interval_cases n
  · exact burnsideI13_i14_sqt_60 (hcard.trans (by decide))
  · exact burnsideI13_i14_sqt_360 (hcard.trans (by decide))
  · exact burnsideI13_i14_sqt_2520 (hcard.trans (by decide))
  · exact burnsideI13_i14_sqt_20160 (hcard.trans (by decide))

private theorem burnsideI13_i14_pRank_le_two {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hcard : ¬ p ^ 4 ∣ Nat.card G) (H : Subgroup G) (hH : IsPGroup p H)
    (hnab : ∃ x ∈ H, ∃ y ∈ H, x * y ≠ y * x) : CFSG.pRank p G ≤ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  unfold CFSG.pRank
  refine csSup_le' ?_
  rintro r ⟨A, hA, hAcard⟩
  by_contra hr
  have hr3 : 3 ≤ r := by omega
  have hdvd : p ^ r ∣ Nat.card G := hAcard ▸ Subgroup.card_subgroup_dvd_card A
  have hr3' : r = 3 := by
    by_contra hne
    have h4 : 4 ≤ r := by omega
    exact hcard ((pow_dvd_pow p h4).trans hdvd)
  subst hr3'
  have hne : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have hfact : (Nat.card G).factorization p = 3 := by
    have h2 : 3 ≤ (Nat.card G).factorization p :=
      (hp.pow_dvd_iff_le_factorization hne).1 hdvd
    have h3 : (Nat.card G).factorization p < 4 := by
      by_contra hh
      exact hcard ((hp.pow_dvd_iff_le_factorization hne).2 (by omega))
    omega
  let P : Sylow p G := Sylow.ofCard A (by rw [hAcard, hfact])
  obtain ⟨Q, hHQ⟩ := hH.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Q
  obtain ⟨x, hx, y, hy, hxy⟩ := hnab
  apply hxy
  have hxQ : x ∈ (Q : Subgroup G) := hHQ hx
  have hyQ : y ∈ (Q : Subgroup G) := hHQ hy
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hxQ hyQ
  obtain ⟨x', hx', hxx⟩ := hxQ
  obtain ⟨y', hy', hyy⟩ := hyQ
  have hP : (P : Subgroup G) = A := Sylow.coe_ofCard A _
  rw [hP] at hx' hy'
  have hcomm : x' * y' = y' * x' := by
    have := hA.toIsMulCommutative.is_comm.comm (⟨x', hx'⟩ : A) ⟨y', hy'⟩
    exact congrArg Subtype.val this
  have hxx' : x = g * x' * g⁻¹ := by
    rw [← hxx]; simp [MulAut.smul_def, MulAut.conj_apply]
  have hyy' : y = g * y' * g⁻¹ := by
    rw [← hyy]; simp [MulAut.smul_def, MulAut.conj_apply]
  rw [hxx', hyy', show g * x' * g⁻¹ * (g * y' * g⁻¹) = g * (x' * y') * g⁻¹ by group,
    show g * y' * g⁻¹ * (g * x' * g⁻¹) = g * (y' * x') * g⁻¹ by group, hcomm]

private theorem burnsideI13_i14_pRank_le_two_of_not_dvd {G : Type} [Group G] [Finite G] {p : ℕ}
    (h : ¬ p ^ 3 ∣ Nat.card G) : CFSG.pRank p G ≤ 2 := by
  unfold CFSG.pRank
  refine csSup_le' ?_
  rintro r ⟨A, -, hAcard⟩
  by_contra hr
  have hr3 : 3 ≤ r := by omega
  exact h ((pow_dvd_pow p hr3).trans (hAcard ▸ Subgroup.card_subgroup_dvd_card A))

private theorem burnsideI13_i14_sqt_of_sylow {G : Type} [Group G] [Finite G]
    (h4 : ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ^ 4 ∣ Nat.card G)
    (hW : ∀ p : ℕ, p.Prime → p ≠ 2 → p ^ 3 ∣ Nat.card G →
      ∃ H : Subgroup G, IsPGroup p H ∧ ∃ x ∈ H, ∃ y ∈ H, x * y ≠ y * x) :
    CFSG.IsStronglyQuasithin G := by
  intro p hp hp2
  by_cases h3 : p ^ 3 ∣ Nat.card G
  · obtain ⟨H, hH, hnab⟩ := hW p hp hp2 h3
    exact burnsideI13_i14_pRank_le_two hp (h4 p hp hp2) H hH hnab
  · exact burnsideI13_i14_pRank_le_two_of_not_dvd h3

open scoped commutatorElement in
private theorem burnsideI13_i14_witness {S : Type} [Group S] {p : ℕ} (hp : p.Prime) {x y : S}
    (hz : ⁅x, y⁆ ≠ 1) (hcard : Nat.card (Subgroup.closure ({x, y} : Set S)) = p ^ 3) :
    ∃ H : Subgroup S, IsPGroup p H ∧ ∃ a ∈ H, ∃ b ∈ H, a * b ≠ b * a := by
  haveI : Finite (Subgroup.closure ({x, y} : Set S)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 3 hp.ne_zero)
  exact ⟨Subgroup.closure {x, y}, IsPGroup.of_card hcard, x, Subgroup.subset_closure (by simp), y,
    Subgroup.subset_closure (by simp), fun h => hz (commutatorElement_eq_one_iff_mul_comm.2 h)⟩

private theorem burnsideI13_i14_mem_of_dvd {N p : ℕ} {S : Finset ℕ} (hN : N ≠ 0)
    (hS : Nat.primeFactors N = S) (hp : p.Prime) (h : p ∣ N) : p ∈ S :=
  hS ▸ Nat.mem_primeFactors.2 ⟨hp, h, hN⟩

private theorem burnsideI13_i14_arith_J2 (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    (p ^ 3 ∣ 604800 → p = 3) ∧ ¬ p ^ 4 ∣ 604800 := by
  have hmem := burnsideI13_i14_mem_of_dvd (by norm_num : (604800 : ℕ) ≠ 0)
    (by simp [Nat.primeFactors] : Nat.primeFactors 604800 = {2, 3, 5, 7}) hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  constructor
  · intro h
    rcases hmem ((dvd_pow_self p (by norm_num)).trans h) with rfl | rfl | rfl | rfl <;>
      first | rfl | exact absurd rfl hp2 | (exfalso; norm_num at h)
  · intro h
    rcases hmem ((dvd_pow_self p (by norm_num)).trans h) with rfl | rfl | rfl | rfl <;>
      first | exact hp2 rfl | (norm_num at h)

private theorem burnsideI13_i14_arith_HS (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    (p ^ 3 ∣ 44352000 → p = 5) ∧ ¬ p ^ 4 ∣ 44352000 := by
  have hmem := burnsideI13_i14_mem_of_dvd (by norm_num : (44352000 : ℕ) ≠ 0)
    (by simp [Nat.primeFactors] : Nat.primeFactors 44352000 = {2, 3, 5, 7, 11}) hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  constructor
  · intro h
    rcases hmem ((dvd_pow_self p (by norm_num)).trans h) with rfl | rfl | rfl | rfl | rfl <;>
      first | rfl | exact absurd rfl hp2 | (exfalso; norm_num at h)
  · intro h
    rcases hmem ((dvd_pow_self p (by norm_num)).trans h) with rfl | rfl | rfl | rfl | rfl <;>
      first | exact hp2 rfl | (norm_num at h)

private theorem burnsideI13_i14_arith_Ru (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    (p ^ 3 ∣ 145926144000 → p = 3 ∨ p = 5) ∧ ¬ p ^ 4 ∣ 145926144000 := by
  have hmem := burnsideI13_i14_mem_of_dvd (by norm_num : (145926144000 : ℕ) ≠ 0)
    (by simp [Nat.primeFactors] : Nat.primeFactors 145926144000 = {2, 3, 5, 7, 13, 29}) hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  constructor
  · intro h
    rcases hmem ((dvd_pow_self p (by norm_num)).trans h) with
        rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | (left; rfl) | (right; rfl) | exact absurd rfl hp2 | (exfalso; norm_num at h)
  · intro h
    rcases hmem ((dvd_pow_self p (by norm_num)).trans h) with
        rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact hp2 rfl | (norm_num at h)

private theorem burnsideI13_i14_arith_M12 (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    (p ^ 3 ∣ 95040 → p = 3) ∧ ¬ p ^ 4 ∣ 95040 := by
  have hmem := burnsideI13_i14_mem_of_dvd (by norm_num : (95040 : ℕ) ≠ 0)
    (by simp [Nat.primeFactors] : Nat.primeFactors 95040 = {2, 3, 5, 11}) hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  constructor
  · intro h
    rcases hmem ((dvd_pow_self p (by norm_num)).trans h) with rfl | rfl | rfl | rfl <;>
      first | rfl | exact absurd rfl hp2 | (exfalso; norm_num at h)
  · intro h
    rcases hmem ((dvd_pow_self p (by norm_num)).trans h) with rfl | rfl | rfl | rfl <;>
      first | exact hp2 rfl | (norm_num at h)

private theorem burnsideI13_i14_arith_G24 (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    (p ^ 3 ∣ 251596800 → p = 3) ∧ ¬ p ^ 4 ∣ 251596800 := by
  have hmem := burnsideI13_i14_mem_of_dvd (by norm_num : (251596800 : ℕ) ≠ 0)
    (by simp [Nat.primeFactors] : Nat.primeFactors 251596800 = {2, 3, 5, 7, 13}) hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  constructor
  · intro h
    rcases hmem ((dvd_pow_self p (by norm_num)).trans h) with rfl | rfl | rfl | rfl | rfl <;>
      first | rfl | exact absurd rfl hp2 | (exfalso; norm_num at h)
  · intro h
    rcases hmem ((dvd_pow_self p (by norm_num)).trans h) with rfl | rfl | rfl | rfl | rfl <;>
      first | exact hp2 rfl | (norm_num at h)

private theorem burnsideI13_i14_sqt_J2_native :
    CFSG.IsStronglyQuasithin CFSG.Blueprint.NativeSporadic.J2 := by
  have hc := CFSG.Sporadic.J2.card_J2
  haveI : Finite CFSG.Blueprint.NativeSporadic.J2 :=
    Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  refine burnsideI13_i14_sqt_of_sylow (fun p hp hp2 => ?_) (fun p hp hp2 h3 => ?_)
  · rw [hc]; exact (burnsideI13_i14_arith_J2 p hp hp2).2
  · rw [hc] at h3
    obtain rfl := (burnsideI13_i14_arith_J2 p hp hp2).1 h3
    obtain ⟨x, y, -, -, -, hz, -, -, hcard, -⟩ := CFSG.SectionRank.J2_sylow3_cubic_witness
    exact burnsideI13_i14_witness hp hz hcard

private theorem burnsideI13_i14_sqt_HS_native :
    CFSG.IsStronglyQuasithin CFSG.Blueprint.NativeSporadic.HS := by
  have hc := CFSG.Sporadic.HS.card_HS
  haveI : Finite CFSG.Blueprint.NativeSporadic.HS :=
    Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  refine burnsideI13_i14_sqt_of_sylow (fun p hp hp2 => ?_) (fun p hp hp2 h3 => ?_)
  · rw [hc]; exact (burnsideI13_i14_arith_HS p hp hp2).2
  · rw [hc] at h3
    obtain rfl := (burnsideI13_i14_arith_HS p hp hp2).1 h3
    obtain ⟨x, y, -, -, -, hz, -, -, hcard, -⟩ := CFSG.SectionRank.HS_sylow5_cubic_witness
    exact burnsideI13_i14_witness hp hz hcard

private theorem burnsideI13_i14_sqt_Ru_native :
    CFSG.IsStronglyQuasithin CFSG.Blueprint.NativeSporadic.Ru := by
  have hc := CFSG.Sporadic.Ru.card_Ru
  haveI : Finite CFSG.Blueprint.NativeSporadic.Ru :=
    Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  refine burnsideI13_i14_sqt_of_sylow (fun p hp hp2 => ?_) (fun p hp hp2 h3 => ?_)
  · rw [hc]; exact (burnsideI13_i14_arith_Ru p hp hp2).2
  · rw [hc] at h3
    rcases (burnsideI13_i14_arith_Ru p hp hp2).1 h3 with rfl | rfl
    · obtain ⟨x, y, -, -, -, hz, -, -, hcard, -⟩ := CFSG.SectionRank.Ru_sylow3_cubic_witness
      exact burnsideI13_i14_witness hp hz hcard
    · obtain ⟨x, y, -, -, -, hz, -, -, hcard, -⟩ := CFSG.SectionRank.Ru_sylow5_cubic_witness
      exact burnsideI13_i14_witness hp hz hcard

private theorem burnsideI13_i14_sqt_M12_native :
    CFSG.IsStronglyQuasithin CFSG.Blueprint.NativeSporadic.M12 := by
  have hc := CFSG.Sporadic.Mathieu.card_M12
  haveI : Finite CFSG.Blueprint.NativeSporadic.M12 :=
    Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  refine burnsideI13_i14_sqt_of_sylow (fun p hp hp2 => ?_) (fun p hp hp2 h3 => ?_)
  · rw [hc]; exact (burnsideI13_i14_arith_M12 p hp hp2).2
  · rw [hc] at h3
    obtain rfl := (burnsideI13_i14_arith_M12 p hp hp2).1 h3
    obtain ⟨x, y, -, -, -, hz, -, -, hcard, -⟩ := CFSG.SectionRank.M12_sylow3_cubic_witness
    exact burnsideI13_i14_witness hp hz hcard

private theorem burnsideI13_i14_sqt_J2
    {G : Type} [Group G] [Finite G] (h : CFSG.Blueprint.NativeSporadic.IsSporadic G .J2) :
    CFSG.IsStronglyQuasithin G := by
  obtain ⟨e⟩ := h
  exact CFSG.SectionRank.isStronglyQuasithin_of_mulEquiv e burnsideI13_i14_sqt_J2_native

private theorem burnsideI13_i14_sqt_HS
    {G : Type} [Group G] [Finite G] (h : CFSG.Blueprint.NativeSporadic.IsSporadic G .HS) :
    CFSG.IsStronglyQuasithin G := by
  obtain ⟨e⟩ := h
  exact CFSG.SectionRank.isStronglyQuasithin_of_mulEquiv e burnsideI13_i14_sqt_HS_native

private theorem burnsideI13_i14_sqt_Ru
    {G : Type} [Group G] [Finite G] (h : CFSG.Blueprint.NativeSporadic.IsSporadic G .Ru) :
    CFSG.IsStronglyQuasithin G := by
  obtain ⟨e⟩ := h
  exact CFSG.SectionRank.isStronglyQuasithin_of_mulEquiv e burnsideI13_i14_sqt_Ru_native

private theorem burnsideI13_i14_sqt_M12
    {G : Type} [Group G] [Finite G] (h : CFSG.Blueprint.NativeSporadic.IsSporadic G .M12) :
    CFSG.IsStronglyQuasithin G := by
  obtain ⟨e⟩ := h
  exact CFSG.SectionRank.isStronglyQuasithin_of_mulEquiv e burnsideI13_i14_sqt_M12_native

section G24


open CFSG.Blueprint.Chevalley CFSG.RankThree.PartTwo.Sec4.Item434RemG24 in
private theorem burnsideI13_i14_sqt_g2four_adjoint {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4)
    [Finite (adjointGroup .G2 K)] : CFSG.IsStronglyQuasithin (adjointGroup .G2 K) := by
  haveI : CharP K 2 := CFSG.RankThree.Chevalley.charP_two_of_natCard (n := 2) (by rw [hK]; norm_num)
  have hcard : Nat.card (adjointGroup .G2 K) = 251596800 := by
    rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hK]
    norm_num [CFSG.Open.ordG2]
  obtain ⟨φ, hφ⟩ := CFSG.ComponentClassification.RankTwoExceptional.exists_sl3_hom (K := K)
  have hrange := CFSG.ComponentClassification.RankTwoExceptional.range_sl3_hom hφ
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := Fintype.ofFinite K
  haveI := Fintype.ofFinite (GaloisField 2 2)
  have hc : Fintype.card (GaloisField 2 2) = Fintype.card K := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
      GaloisField.card 2 2 (by norm_num)]
    norm_num
  let σ : CFSG.Fischer.F4 ≃+* K :=
    CFSG.Fischer.F4.equivGaloisField.trans (FiniteField.ringEquivOfCardEq hc)
  refine burnsideI13_i14_sqt_of_sylow (fun p hp hp2 => ?_) (fun p hp hp2 h3 => ?_)
  · rw [hcard]; exact (burnsideI13_i14_arith_G24 p hp hp2).2
  · rw [hcard] at h3
    obtain rfl := (burnsideI13_i14_arith_G24 p hp hp2).1 h3
    have hΦ := phiX_injective hK σ hrange
    obtain ⟨x, hx, y, hy, hxy⟩ := exists_not_comm
    refine ⟨sZeroGrp.map (phiX σ hrange), IsPGroup.of_card (n := 3) ?_, phiX σ hrange x,
      ⟨x, hx, rfl⟩, phiX σ hrange y, ⟨y, hy, rfl⟩, fun h => hxy (hΦ (by rw [map_mul, map_mul, h]))⟩
    rw [Subgroup.card_map_of_injective hΦ, card_sZeroGrp]
    norm_num

private theorem burnsideI13_i14_sqt_G24 {G : Type} [Group G] [Finite G]
    (h : CFSG.Blueprint.ChevalleyExceptionalModel G .G2 2 2) : CFSG.IsStronglyQuasithin G := by
  obtain ⟨-, hm⟩ := h
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ :=
    CFSG.RankThree.Chevalley.exists_mulEquiv_adjointGroup_of_untwisted hm
  haveI : Finite (CFSG.Blueprint.Chevalley.adjointGroup .G2 K) := Finite.of_equiv G e.symm.toEquiv
  exact CFSG.SectionRank.isStronglyQuasithin_of_mulEquiv e.symm
    (burnsideI13_i14_sqt_g2four_adjoint (by rw [hK]; norm_num))

end G24


private def burnsideI13_i14_SqtHard : Prop :=
  (∀ (G : Type) [Group G] [Finite G], CFSG.Blueprint.ChevalleyExceptionalModel G .G2 2 2 →
    CFSG.IsStronglyQuasithin G) ∧
  (∀ (G : Type) [Group G] [Finite G], CFSG.Blueprint.NativeSporadic.IsSporadic G .M12 →
    CFSG.IsStronglyQuasithin G) ∧
  (∀ (G : Type) [Group G] [Finite G], CFSG.Blueprint.NativeSporadic.IsSporadic G .J2 →
    CFSG.IsStronglyQuasithin G) ∧
  (∀ (G : Type) [Group G] [Finite G], CFSG.Blueprint.NativeSporadic.IsSporadic G .HS →
    CFSG.IsStronglyQuasithin G) ∧
  (∀ (G : Type) [Group G] [Finite G], CFSG.Blueprint.NativeSporadic.IsSporadic G .Ru →
    CFSG.IsStronglyQuasithin G)

private theorem burnsideI13_i14_five_le {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) : 5 ≤ p := by
  by_contra hlt
  have := hp.two_le
  interval_cases p <;> first | omega | exact absurd hp (by norm_num)

section


private theorem burnsideI13_i14_sqtHard : burnsideI13_i14_SqtHard :=
  ⟨fun G _ _ h => burnsideI13_i14_sqt_G24 h, fun G _ _ h => burnsideI13_i14_sqt_M12 h,
    fun G _ _ h => burnsideI13_i14_sqt_J2 h, fun G _ _ h => burnsideI13_i14_sqt_HS h,
    fun G _ _ h => burnsideI13_i14_sqt_Ru h⟩

end

private theorem burnsideI13_i14_goal_char2 (hGr : burnsideI13_Griess)
    (hH : burnsideI13_i14_SqtHard) {G : Type} [Group G] [Finite G]
    (hns : ¬ CFSG.IsStronglyQuasithin G) (hn : Nontrivial (quasithinHopfMultiplier G)) {f : ℕ}
    (h : (2 ≤ f ∧ StatedClassicalModel G .PSL 2 2 f) ∨ (1 ≤ f ∧ StatedClassicalModel G .PSL 3 2 f) ∨
      (2 ≤ f ∧ StatedClassicalModel G .PSU 3 2 f) ∨ (2 ≤ f ∧ StatedClassicalModel G .PSp 2 2 f) ∨
      (1 ≤ f ∧ StatedClassicalModel G .PSU 4 2 f) ∨
      (2 ≤ f ∧ CFSG.Blueprint.ChevalleyExceptionalModel G .G2 2 f) ∨
      (1 ≤ f ∧ CFSG.Blueprint.ChevalleyExceptionalModel G .trialityD4 2 f) ∨
      (Odd f ∧ 3 ≤ f ∧ CFSG.Blueprint.ReeTitsModel G .twistedF4 2 f) ∨
      (Odd f ∧ 3 ≤ f ∧ CFSG.Blueprint.SuzukiModel G 2 f)) :
    burnsideI13_i14_Goal G := by
  rcases h with ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨hf, h⟩ |
    ⟨hodd, hf, h⟩ | ⟨hodd, hf, h⟩
  ·
    by_cases hf2 : f = 2
    · subst hf2
      exact (hns (burnsideI13_i14_sqt_psl24 h)).elim
    · exfalso
      refine burnsideI13_false_of_row (hGr G .PSL 2 2 f (Or.inl ⟨by decide, h⟩)) ?_
        (burnsideI13_exc_psl2_two f (by omega)) hn
      show (Nat.gcd 2 (2 ^ f - 1), 1) = (1, 1)
      rw [burnsideI13_gcd_two (burnsideI13_not_two_dvd f (by omega))]
  · exact (hns (burnsideI13_i14_sqt_psl3_two h)).elim
  · exact (hns (burnsideI13_i14_sqt_psu3_two h)).elim
  ·
    exfalso
    refine burnsideI13_false_of_row (hGr G .PSp 2 2 f (Or.inl ⟨by decide, h⟩)) ?_
      (burnsideI13_exc_psp2 2 f) hn
    show (Nat.gcd 2 (2 ^ f - 1), 1) = (1, 1)
    rw [burnsideI13_gcd_two (burnsideI13_not_two_dvd f (by omega))]
  ·
    by_cases hf1 : f = 1
    · subst hf1
      exact Or.inl (burnsideI13_i14_D2_psu42 h)
    · exfalso
      refine burnsideI13_false_of_row (hGr G .PSU 4 2 f (Or.inl ⟨by decide, h⟩)) ?_
        (burnsideI13_i14_exc_psu4_two f (by omega)) hn
      show (Nat.gcd 4 (2 ^ f + 1), 1) = (1, 1)
      have h2 : Nat.Coprime 2 (2 ^ f + 1) := by
        refine burnsideI13_gcd_two ?_
        obtain ⟨m, hm⟩ : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
        omega
      have h4 : Nat.Coprime (2 ^ 2) (2 ^ f + 1) := Nat.Coprime.pow_left 2 h2
      have : Nat.gcd 4 (2 ^ f + 1) = 1 := h4
      rw [this]
  ·
    by_cases hf2 : f = 2
    · subst hf2
      exact (hns (hH.1 G h)).elim
    · exfalso
      exact burnsideI13_false_of_row (hGr G .G2 0 2 f (Or.inr (Or.inl ⟨rfl, by decide, h⟩))) rfl
        (burnsideI13_exc_g2_two f (by omega)) hn
  ·
    exfalso
    exact burnsideI13_false_of_row (hGr G .trialityD4 0 2 f (Or.inr (Or.inl ⟨rfl, by decide, h⟩)))
      rfl rfl hn
  ·
    exfalso
    exact burnsideI13_false_of_row
      (hGr G .twistedF4 0 2 f (Or.inr (Or.inr (Or.inl ⟨rfl, by decide, h⟩)))) rfl rfl hn
  ·
    by_cases hf3 : f = 3
    · subst hf3
      exact (hns (burnsideI13_i14_sqt_sz8 h)).elim
    · exfalso
      obtain ⟨k, hk⟩ := hodd
      exact burnsideI13_false_of_row
        (hGr G .twistedB2 0 2 f (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, h⟩)))) rfl
        (burnsideI13_exc_suzuki f (by omega)) hn

private theorem burnsideI13_i14_goal_spor
    (hT : ∀ s : TauCeti.SporadicName,
      (s = .M11 ∨ s = .M23 ∨ s = .M24 ∨ s = .J1 ∨ s = .J4 ∨ s = .He) →
        Subsingleton (quasithinHopfMultiplier (CFSG.Blueprint.NativeSporadic.Carrier s)))
    (hH : burnsideI13_i14_SqtHard) {G : Type} [Group G] [Finite G]
    (hns : ¬ CFSG.IsStronglyQuasithin G) (hn : Nontrivial (quasithinHopfMultiplier G))
    {s : TauCeti.SporadicName}
    (hs : s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24 ∨ s = .J1 ∨ s = .J2 ∨ s = .J3 ∨
      s = .J4 ∨ s = .HS ∨ s = .He ∨ s = .Ru ∨ s = .McL)
    (e : Nonempty (G ≃* CFSG.Blueprint.NativeSporadic.Carrier s)) : burnsideI13_i14_Goal G := by
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (burnsideI13_false_of_iso e.some (hT _ (by simp)) hn).elim
  · exact (hns (hH.2.1 G e)).elim
  · exact (hns (burnsideI13_i14_sqt_M22 e)).elim
  · exact (burnsideI13_false_of_iso e.some (hT _ (by simp)) hn).elim
  · exact (burnsideI13_false_of_iso e.some (hT _ (by simp)) hn).elim
  · exact (burnsideI13_false_of_iso e.some (hT _ (by simp)) hn).elim
  · exact (hns (hH.2.2.1 G e)).elim
  · exact Or.inr (Or.inl (burnsideI13_i14_D3_J3 e))
  · exact (burnsideI13_false_of_iso e.some (hT _ (by simp)) hn).elim
  · exact (hns (hH.2.2.2.1 G e)).elim
  · exact (burnsideI13_false_of_iso e.some (hT _ (by simp)) hn).elim
  · exact (hns (hH.2.2.2.2 G e)).elim
  · exact Or.inr (Or.inl (burnsideI13_i14_D3_McL e))

private theorem burnsideI13_i14_goal_odd (hGr : burnsideI13_Griess) {G : Type} [Group G] [Finite G]
    (hns : ¬ CFSG.IsStronglyQuasithin G) (hn : Nontrivial (quasithinHopfMultiplier G)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (h : (∃ f : ℕ, 1 ≤ f ∧ StatedClassicalModel G .PSL 2 p f) ∨
      (∃ f : ℕ, (f = 1 ∨ f = 2) ∧
        (StatedClassicalModel G .PSL 3 p f ∨ StatedClassicalModel G .PSU 3 p f)) ∨
      StatedClassicalModel G .PSp 2 p 1 ∨ CFSG.Blueprint.ChevalleyExceptionalModel G .G2 p 1 ∨
      ((∃ a : ℕ, p = 2 ^ a + 1) ∧ StatedClassicalModel G .PSL 4 p 1) ∨
      ((∃ b : ℕ, p + 1 = 2 ^ b) ∧ StatedClassicalModel G .PSU 4 p 1)) :
    burnsideI13_i14_Goal G := by
  rcases h with ⟨f, hf, h⟩ | ⟨f, hf12, h | h⟩ | h | h | ⟨⟨a, ha⟩, h⟩ | ⟨⟨b, hb⟩, h⟩
  ·
    by_cases h9 : 9 < p ^ f
    · exact Or.inl (burnsideI13_i14_D2_psl2 hp2 hf h9 h)
    · exact (hns (burnsideI13_i14_sqt_psl2_small hp2 (by omega) h)).elim
  ·
    by_cases hq : p ^ f % 3 = 1
    · exact Or.inr (Or.inl (burnsideI13_i14_D3_psl hp2 hq h))
    · exfalso
      have hpos : 0 < p ^ f := pow_pos hp.pos f
      refine burnsideI13_false_of_row (hGr G .PSL 3 p f (Or.inl ⟨by decide, h⟩)) ?_
        (burnsideI13_exc_psl3 p f (fun h' => hp2 h'.1) (fun h' => hp2 h'.1)) hn
      show (Nat.gcd 3 (p ^ f - 1), 1) = (1, 1)
      rw [burnsideI13_gcd_three (by omega)]
  ·
    by_cases hq : p ^ f % 3 = 2
    · exact Or.inr (Or.inl (burnsideI13_i14_D3_psu hp2 hq h))
    · exfalso
      refine burnsideI13_false_of_row (hGr G .PSU 3 p f (Or.inl ⟨by decide, h⟩)) ?_
        (burnsideI13_exc_psu3 p f) hn
      show (Nat.gcd 3 (p ^ f + 1), 1) = (1, 1)
      rw [burnsideI13_gcd_three (by omega)]
  ·
    by_cases hp3 : p = 3
    · subst hp3
      exact Or.inl (burnsideI13_i14_D2_psu42 (burnsideI13_i14_psu42_of_psp23 h))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨p, hp, burnsideI13_i14_five_le hp hp2 hp3, h⟩)))))
  ·
    by_cases hp3 : p = 3
    · subst hp3
      exact Or.inr (Or.inl (burnsideI13_i14_D3_g2 h))
    · exfalso
      exact burnsideI13_false_of_row (hGr G .G2 0 p 1 (Or.inr (Or.inl ⟨rfl, by decide, h⟩))) rfl
        (burnsideI13_i14_exc_g2_odd p hp2 hp3) hn
  ·
    by_cases hp3 : p = 3
    · subst hp3
      exact Or.inl (Or.inr (Or.inr (Or.inl h)))
    · have h3 : 3 < p := by have := burnsideI13_i14_five_le hp hp2 hp3; omega
      have ha0 : a ≠ 0 := by
        rintro rfl
        omega
      obtain ⟨m, hm⟩ := Nat.pow_of_pow_add_prime (by norm_num : 1 < 2) ha0 (ha ▸ hp)
      exact Or.inr (Or.inr (Or.inl (Or.inl ⟨p, m, hp, by rw [ha, hm], h3, h⟩)))
  ·
    by_cases hp3 : p = 3
    · subst hp3
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · have h3 : 3 < p := by have := burnsideI13_i14_five_le hp hp2 hp3; omega
      exact Or.inr (Or.inr (Or.inl (Or.inr ⟨p, b, hp, by omega, h3, h⟩)))

private theorem burnsideI13_i14_complete
    (hGr : burnsideI13_Griess)
    (hB : ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], (∃ a b : S, a * b ≠ b * a) →
      CFSG.Quasithin.IsQuasithin S → CFSG.SectionRank.IsKGroupCat S →
      CFSG.SectionRank.QTK.QTKSimpleList S)
    (hT : ∀ s : TauCeti.SporadicName,
      (s = .M11 ∨ s = .M23 ∨ s = .M24 ∨ s = .J1 ∨ s = .J4 ∨ s = .He) →
        Subsingleton (quasithinHopfMultiplier (CFSG.Blueprint.NativeSporadic.Carrier s)))
    (hH : burnsideI13_i14_SqtHard)
    (G : Type) [Group G] [Finite G] (hs : IsSimpleGroup G) (hK : CFSG.SectionRank.IsKGroupCat G)
    (hQ : CFSG.Quasithin.IsQuasithin G) (hns : ¬ CFSG.IsStronglyQuasithin G)
    (hn : Nontrivial (quasithinHopfMultiplier G)) : burnsideI13_i14_Goal G := by
  haveI := hs
  by_cases hab : ∃ a b : G, a * b ≠ b * a
  · rcases hB G hab hQ hK with ⟨n, h5, h9, e⟩ | ⟨p, hp, hp2, h⟩ | (⟨f, h⟩ | h | h) |
      (⟨n, hn45, h⟩ | h) | ⟨s, hsp, e⟩
    · by_cases h9' : n = 9
      · subst h9'
        exact Or.inl (burnsideI13_i14_D2_alt9 e)
      · exact (hns (burnsideI13_i14_sqt_alt h5 (by omega) e)).elim
    · exact burnsideI13_i14_goal_odd hGr hns hn hp hp2 h
    · exact burnsideI13_i14_goal_char2 hGr hH hns hn h
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exfalso
      exact burnsideI13_false_of_row
        (hGr G .Tits 0 2 1 (Or.inr (Or.inr (Or.inl ⟨rfl, by decide, h⟩)))) rfl rfl hn
    · rcases hn45 with rfl | rfl
      · exact (hns (burnsideI13_i14_sqt_psl42 h)).elim
      · exfalso
        refine burnsideI13_false_of_row (hGr G .PSL 5 2 1 (Or.inl ⟨by decide, h⟩)) ?_
          burnsideI13_exc_psl5 hn
        decide
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact burnsideI13_i14_goal_spor hT hH hns hn hsp e
  · exfalso
    haveI := burnsideI13_sub_of_simple_abelian fun a b => by
      by_contra h
      exact hab ⟨a, b, h⟩
    exact false_of_nontrivial_of_subsingleton (quasithinHopfMultiplier G)

section


theorem as_I_1_4
    : I_1_4 := by
  have hH := burnsideI13_i14_sqtHard
  have hGr : burnsideI13_Griess := fun X _ t n p f h => ASVolIRegistered.griess h
  have hB : ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], (∃ a b : S, a * b ≠ b * a) →
      CFSG.Quasithin.IsQuasithin S → CFSG.SectionRank.IsKGroupCat S →
      CFSG.SectionRank.QTK.QTKSimpleList S :=
    fun S _ _ _ hn hQ hK => CFSG.SectionRank.QTK.qtk_simple_list_simple S hn hQ hK
  have hT := burnsideI13_trivRows
  have hJ3 : quasithinMultiplierCyclic (CFSG.Blueprint.NativeSporadic.Carrier .J3) 3 :=
    ASVolIRegistered.multCyc_of_hopf_prime Nat.prime_three
      CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.J3Cover.card_hopfMultiplier_nativeJ3
  have hMcL : quasithinMultiplierCyclic (CFSG.Blueprint.NativeSporadic.Carrier .McL) 3 :=
    ASVolIRegistered.multCyc_of_hopf_prime Nat.prime_three
      CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.nativeRow_McL
  refine ⟨fun G _ _ hs hK hQ hns hn => burnsideI13_i14_complete hGr hB hT hH G hs hK hQ hns hn,
    fun G _ _ h => burnsideI13_i14_table1 hGr ASVolIRegistered.multCyc_A9 G h,
    fun G _ _ h => burnsideI13_i14_table2 hGr hJ3 hMcL G h,
    fun G _ _ h => burnsideI13_i14_table3 hGr G h,
    fun G _ _ h => burnsideI13_i14_table4 hGr G h,
    fun G _ _ h => burnsideI13_i14_table5 hGr G h,
    fun G _ _ h => burnsideI13_i14_table6 hGr G h,
    fun G _ _ p hp hp5 h => burnsideI13_i14_table7 hGr G p hp hp5 h⟩

end

@[expose] def I_1_6 : Prop :=
  (h1Dim (altNaturalRep 5) = 0 ∧ h1Dim (altNaturalRep 7) = 0 ∧
    h1Dim (altNaturalRep 6) = 1 ∧ h1Dim (altNaturalRep 8) = 1 ∧
    Module.Projective (MonoidAlgebra (ZMod 2) (alternatingGroup (Fin 5)))
      (altNaturalRep 5).asModule) ∧
  (∀ n : ℕ, 2 ≤ n → h1Dim (slNaturalRep 2 (GaloisField 2 n)) = n) ∧
  ((∀ n : ℕ, 1 ≤ n → ∀ b c : GaloisField 2 n, (∀ s : GaloisField 2 n, s ^ 2 + b * s + c ≠ 0) →
      h1Dim (orthMinusRep (GaloisField 2 n) b c) = 0) ∧
    (∀ b c : ZMod 2, (∀ s : ZMod 2, s ^ 2 + b * s + c ≠ 0) →
      (∃ (φ : StatedOmega (StatedQuadMinus 2 (ZMod 2) b c) ≃* alternatingGroup (Fin 5))
        (e : (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → ZMod 2) ≃ₗ[ZMod 2]
          (evenWeight 5 ⧸ constInEven 5)),
        ∀ (g : StatedOmega (StatedQuadMinus 2 (ZMod 2) b c)) (v : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → ZMod 2),
          e (orthMinusRep (ZMod 2) b c g v) = altNaturalRep 5 (φ g) (e v)) ∧
      Module.Projective (MonoidAlgebra (ZMod 2) (StatedOmega (StatedQuadMinus 2 (ZMod 2) b c)))
        (orthMinusRep (ZMod 2) b c).asModule)) ∧
  ((∀ n : ℕ, 2 ≤ n → h1Dim (slNaturalRep 3 (GaloisField 2 n)) = 0) ∧
    h1Dim (slNaturalRep 3 (ZMod 2)) = 1) ∧
  (∀ n : ℕ, 1 ≤ n → h1Dim (sp4NaturalRep (GaloisField 2 n)) = n ∧
    h1Dim (g2DerivedNaturalRep (GaloisField 2 n)) = n) ∧
  (h1Dim (slNaturalRep 4 (ZMod 2)) = 0 ∧ h1Dim (slNaturalRep 5 (ZMod 2)) = 0) ∧
  (∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V]
      (ρ : Representation (ZMod 2) SL(5, ZMod 2) V),
    ρ.IsIrreducible → Module.finrank (ZMod 2) V = 10 → h1Dim ρ = 0) ∧
  (∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V]
      (ρ : Representation (ZMod 2) (alternatingGroup (Fin 7)) V),
    ρ.IsIrreducible → Module.finrank (ZMod 2) V = 4 → h1Dim ρ = 0) ∧
  (∀ (G : Type) [Group G] [Finite G], IsHatCover G (alternatingGroup (Fin 6)) →
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G V),
      Function.Injective ρ → ρ.IsIrreducible → Module.finrank (ZMod 2) V = 6 → h1Dim ρ = 0)


end CFSG.ASVolI
