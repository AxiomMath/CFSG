module

public import CFSG.LocalAnalysis.StandardType.GGKD2Leaves1615
public import CFSG.Goldschmidt.Steps.G37Quot
public import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown
public import CFSG.LocalAnalysis.StandardType.GGUSixTwoLayer
public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitaryOutdiag
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeThree
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagProj
public import CFSG.LocalAnalysis.StandardType.GGLinearFusionSURepairBlock
public import CFSG.LocalAnalysis.StandardType.GGSixLinearModelRestSURank
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeBoundNonCommUniBase
public import CFSG.Goldschmidt.Statements
public import CFSG.Goldschmidt.StatementsG2
public import CFSG.Goldschmidt.StatementsG3
public import CFSG.Goldschmidt.StatementsH
public import CFSG.Goldschmidt.Steps.G37Core
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupExhaustion
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRanks
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoFourGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsReduction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFullObstruction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourProperSubgroups
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.SubnormalPSubgroupLeQCore
public import CFSG.Walter.Bender1970.S2
public import CFSG.Walter.Bender1970.S3.Basic
public import CFSG.Walter.Bender1970.S3.OStar
public import CFSG.Walter.PSL2Facts
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate100
public import Certificates.Certificate101
public import Certificates.Certificate102
public import Certificates.Certificate103
public import Certificates.Certificate104
public import Certificates.Certificate105
public import Certificates.Certificate106
public import Certificates.Certificate107
public import Certificates.Certificate108
public import Certificates.Certificate109
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99

public section

namespace CFSG.StandardType.KD2Pieces1615

open CFSG CFSG.Assembly CFSG.StandardType S2MathAs3_1615
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.SectionRank.OddCover (diagHom)

@[expose] def UnitaryInndiagIsConj : Prop :=
  ∀ (d n : ℕ) (K : Type) [Field K] [Finite K] (h : UnitaryFieldData 2 n K) (hd : 1 ≤ d),
    3 ≤ d → ¬ (d = 3 ∧ 2 ^ n = 2) →
    ∀ β ∈ InndiagSU.inndiagU (d := d) h hd,
      β ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n K d))
        (LargeEvenGUSet (Fin d) K (2 ^ n))

@[expose] def UnitaryBlockOfComponent : Prop :=
  ∀ (d n : ℕ) [NeZero d] (K : Type) [Field K] [Finite K] (h : UnitaryFieldData 2 n K),
    3 ∣ 2 ^ n + 1 →
    ∀ {τ : Fin d → Kˣ}, (∀ i, τ i ^ 3 = 1) →
    ∀ {D : GL (Fin d) K}
      (hDnorm : D ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K))),
    D = diagHom d τ →
    ∀ {J₀ : Subgroup (LargeEvenProj (unitarySU 2 n K d))},
      IsComponentOf J₀ (ggFix (TableB.projConj (unitarySU 2 n K d) ⟨D, hDnorm⟩)) →
    ∀ m : ℕ, GGHasLabel (⟨.A, 1, m⟩ : LargeEvenLabel) (↥J₀ ⧸ Subgroup.center ↥J₀) →
      2 ≤ n ∧ ∃ I : Finset (Fin d), I.card = 2 ∧ (∀ i ∈ I, ∀ j, τ j = τ i → j ∈ I) ∧
        (∀ i ∈ I, ∀ j ∈ I, τ i = τ j) ∧
        J₀ = (TableBUE.blockSU (K := K) (n := n) I).map
          (LargeEvenProjMk (unitarySU 2 n K d))

@[expose] def UnitaryBlockAction : Prop :=
  ∀ (d n : ℕ) [NeZero d] (K : Type) [Field K] [Finite K] (h : UnitaryFieldData 2 n K),
    3 ∣ 2 ^ n + 1 →
    ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* LargeEvenProj (unitarySU 2 n K d)),
      Function.Surjective ψ → ψ.ker ≤ Subgroup.center L' →
    ∀ (J : Subgroup L'), CFSG.IsQuasisimple J →
    ∀ (a : MulAut L'), (∀ j ∈ J, a j ∈ J) →
    ∀ {τ : Fin d → Kˣ}, (∀ i, τ i ^ 3 = 1) →
    ∀ {D N : GL (Fin d) K}
      (hDnorm : D ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)))
      (hNnorm : N ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K))),
    N ∈ LargeEvenGUSet (Fin d) K (2 ^ n) →
    D = diagHom d τ →
    ∀ {ζ : Kˣ}, ζ ^ 3 = 1 → N * D * N⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin d) ζ * D →
    ∀ {I : Finset (Fin d)}, I.card = 2 → (∀ i ∈ I, ∀ j, τ j = τ i → j ∈ I) →
      (∀ i ∈ I, ∀ j ∈ I, τ i = τ j) →
    J.map ψ = (TableBUE.blockSU (K := K) (n := n) I).map (LargeEvenProjMk (unitarySU 2 n K d)) →
    (∀ l : L', TableB.projConj (unitarySU 2 n K d) ⟨N, hNnorm⟩ (ψ l) = ψ (a l)) →
      ∃ y : ↥J ⧸ Subgroup.center ↥J, ∀ j j' : ↥J, a (j : L') = (j' : L') →
        (j' : ↥J ⧸ Subgroup.center ↥J) = y * (j : ↥J ⧸ Subgroup.center ↥J) * y⁻¹

@[expose] def SplitLiftUnitaryThreeDvd : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → lab.tag = .twA → 3 ∣ 2 ^ lab.n + 1 →
    LargeEvenLabelAll lab (fun R _ I _ =>
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
        ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
        ∀ (e : MulAut L') (J : Subgroup L') (a : MulAut L'),
          GGRankOneSetup I ψ 3 e J 3 a → SplitLift lab R I ψ e → False)

private lemma ltrcu3_frame {d n : ℕ} [NeZero d] {K : Type} [Field K] [Finite K]
    (h : UnitaryFieldData 2 n K) (hdvd : 3 ∣ 2 ^ n + 1)
    {M : GL (Fin d) K} (hMGU : M ∈ LargeEvenGUSet (Fin d) K (2 ^ n)) (hM3 : M ^ 3 = 1) :
    ∃ (s : ↥(unitarySU 2 n K d)) (τ : Fin d → Kˣ),
      (s : GL (Fin d) K)⁻¹ * M * (s : GL (Fin d) K) = diagHom d τ ∧ ∀ i, τ i ^ 3 = 1 := by
  have hd1 : 1 ≤ d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hMU : M ∈ CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary h
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K d) :=
    CFSG.LocalAnalysis.GLTheoremA.T171Sh.mem_primeFormUnitary_of_gu_pow_eq_one hd1 hMGU hM3
      Nat.prime_three (by norm_num) hdvd
  obtain ⟨s, τ, hs⟩ :=
    CFSG.StandardType.UnitModel.exists_det_one_conj_diag h Nat.prime_three hdvd hMU hM3
  refine ⟨s, τ, hs, ?_⟩
  have hconj : (s : GL (Fin d) K)⁻¹ * M * (s : GL (Fin d) K) =
      MulAut.conj ((s : GL (Fin d) K))⁻¹ M := by
    rw [MulAut.conj_apply, inv_inv]
  have hcube : (diagHom d τ) ^ 3 = 1 := by
    rw [← hs, hconj, ← map_pow, hM3, map_one]
  have hdτ : diagHom d (τ ^ 3) = diagHom d (1 : Fin d → Kˣ) := by
    rw [map_pow, hcube, map_one]
  have hτ3 : τ ^ 3 = 1 := CFSG.SectionRank.OddCover.diagHom_injective d hdτ
  intro i
  simpa using congrFun hτ3 i

private lemma ltrcu3b_conj_apply {X : Type*} [Group X] (f g : MulAut X) (x : X) :
    (f * g * f⁻¹) (f x) = f (g x) := by
  calc (f * g * f⁻¹) (f x) = (f * g) (f⁻¹ (f x)) := by rw [MulAut.mul_apply]
    _ = (f * g) x := by rw [MulAut.inv_apply_self]
    _ = f (g x) := by rw [MulAut.mul_apply]

private lemma ltrcu3_transport {d n : ℕ} [NeZero d] {K : Type} [Field K] [Finite K]
    (h : UnitaryFieldData 2 n K) (hd1 : 1 ≤ d)
    {L' : Type} [Group L'] (ψ₀ : L' →* LargeEvenProj (unitarySU 2 n K d))
    {e a : MulAut L'} {M : GL (Fin d) K}
    (hMN : M ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)))
    (s : ↥(unitarySU 2 n K d)) {τ : Fin d → Kˣ}
    (hs : (s : GL (Fin d) K)⁻¹ * M * (s : GL (Fin d) K) = diagHom d τ)
    (hDnorm : diagHom d τ ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)))
    (hθe : ∀ l : L', TableB.projConj (unitarySU 2 n K d) ⟨M, hMN⟩ (ψ₀ l) = ψ₀ (e l))
    (β : MulAut (LargeEvenProj (unitarySU 2 n K d))) (hβ : β ∈ InndiagSU.inndiagU (d := d) h hd1)
    (hβa : ∀ l : L', β (ψ₀ l) = ψ₀ (a l)) :
    ∃ ψ₁ : L' →* LargeEvenProj (unitarySU 2 n K d),
      ψ₁.ker = ψ₀.ker ∧ (Function.Surjective ψ₀ → Function.Surjective ψ₁) ∧
      (∀ l : L', TableB.projConj (unitarySU 2 n K d) ⟨diagHom d τ, hDnorm⟩ (ψ₁ l) =
        ψ₁ (e l)) ∧
      ∃ β' ∈ InndiagSU.inndiagU (d := d) h hd1, ∀ l : L', β' (ψ₁ l) = ψ₁ (a l) := by
  have hmem_s_inv : (s : GL (Fin d) K)⁻¹ ∈
      Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)) :=
    Subgroup.le_normalizer (Subgroup.inv_mem _ s.2)
  have hmem_s : (s : GL (Fin d) K) ∈
      Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)) :=
    Subgroup.le_normalizer s.2
  set γ : MulAut (LargeEvenProj (unitarySU 2 n K d)) :=
    TableB.projConj (unitarySU 2 n K d) ⟨(s : GL (Fin d) K)⁻¹, hmem_s_inv⟩ with hγdef
  have hγ : γ ∈ InndiagSU.inndiagU (d := d) h hd1 := by
    refine (InndiagSU.mem_inndiagU (h := h) (hd := hd1)).mpr ?_
    have hγrange : γ ∈ (MulAut.conj : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)) →*
        MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))).range := by
      refine ⟨((⟨(s : GL (Fin d) K)⁻¹, Subgroup.inv_mem _ s.2⟩ : unitarySU 2 n K d) :
        LargeEvenProj (unitarySU 2 n K d)), ?_⟩
      rw [hγdef]
      exact (TableB.projConj_of_mem (unitarySU 2 n K d) ((s : GL (Fin d) K)⁻¹)
        (Subgroup.inv_mem _ s.2)).symm
    have hmemcomap := hγrange
    rw [InndiagSU.range_conj_eq_comap_inner (h := h) (hd := hd1)] at hmemcomap
    obtain ⟨s₀, hs₀⟩ := (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.mem_inner_primeFormP h
      ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
      (MulAut.congr (InndiagSU.projEquiv h hd1) γ)).mp hmemcomap
    exact ⟨⟨s₀, s₀.2.1⟩, hs₀.symm⟩
  have hElem : (⟨diagHom d τ, hDnorm⟩ :
        Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K))) *
      (⟨(s : GL (Fin d) K)⁻¹, hmem_s_inv⟩ :
        Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K))) =
      (⟨(s : GL (Fin d) K)⁻¹, hmem_s_inv⟩ :
        Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K))) *
      (⟨M, hMN⟩ : Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K))) := by
    apply Subtype.ext
    show diagHom d τ * (s : GL (Fin d) K)⁻¹ = (s : GL (Fin d) K)⁻¹ * M
    rw [← hs]
    group
  have hD_eq : TableB.projConj (unitarySU 2 n K d) ⟨diagHom d τ, hDnorm⟩ * γ =
      γ * TableB.projConj (unitarySU 2 n K d) ⟨M, hMN⟩ := by
    calc TableB.projConj (unitarySU 2 n K d) ⟨diagHom d τ, hDnorm⟩ * γ
        = TableB.projConj (unitarySU 2 n K d) ⟨diagHom d τ, hDnorm⟩ *
            TableB.projConj (unitarySU 2 n K d) ⟨(s : GL (Fin d) K)⁻¹, hmem_s_inv⟩ := by
          rw [hγdef]
      _ = TableB.projConj (unitarySU 2 n K d)
            ((⟨diagHom d τ, hDnorm⟩ :
              Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K))) *
             (⟨(s : GL (Fin d) K)⁻¹, hmem_s_inv⟩ :
              Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)))) := by
          rw [map_mul]
      _ = TableB.projConj (unitarySU 2 n K d)
            ((⟨(s : GL (Fin d) K)⁻¹, hmem_s_inv⟩ :
              Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K))) *
             (⟨M, hMN⟩ :
              Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)))) := by
          rw [hElem]
      _ = TableB.projConj (unitarySU 2 n K d) ⟨(s : GL (Fin d) K)⁻¹, hmem_s_inv⟩ *
            TableB.projConj (unitarySU 2 n K d) ⟨M, hMN⟩ := by
          rw [map_mul]
      _ = γ * TableB.projConj (unitarySU 2 n K d) ⟨M, hMN⟩ := by
          rw [hγdef]
  have hβ' : γ * β * γ⁻¹ ∈ InndiagSU.inndiagU (d := d) h hd1 :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hγ hβ) (Subgroup.inv_mem _ hγ)
  refine ⟨γ.toMonoidHom.comp ψ₀, ?_, ?_, ?_, γ * β * γ⁻¹, hβ', ?_⟩
  · exact MonoidHom.ker_comp_of_injective ψ₀ γ.toMonoidHom γ.injective
  · intro hψ₀
    exact γ.surjective.comp hψ₀
  · intro l
    calc TableB.projConj (unitarySU 2 n K d) ⟨diagHom d τ, hDnorm⟩
          ((γ.toMonoidHom.comp ψ₀) l)
        = TableB.projConj (unitarySU 2 n K d) ⟨diagHom d τ, hDnorm⟩ (γ (ψ₀ l)) := by
          simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      _ = (TableB.projConj (unitarySU 2 n K d) ⟨diagHom d τ, hDnorm⟩ * γ) (ψ₀ l) := by
          rw [MulAut.mul_apply]
      _ = (γ * TableB.projConj (unitarySU 2 n K d) ⟨M, hMN⟩) (ψ₀ l) := by rw [hD_eq]
      _ = γ (TableB.projConj (unitarySU 2 n K d) ⟨M, hMN⟩ (ψ₀ l)) := by
          rw [MulAut.mul_apply]
      _ = γ (ψ₀ (e l)) := by rw [hθe l]
      _ = (γ.toMonoidHom.comp ψ₀) (e l) := by simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  · intro l
    calc (γ * β * γ⁻¹) ((γ.toMonoidHom.comp ψ₀) l)
        = (γ * β * γ⁻¹) (γ (ψ₀ l)) := by simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      _ = γ (β (ψ₀ l)) := ltrcu3b_conj_apply γ β (ψ₀ l)
      _ = γ (ψ₀ (a l)) := by rw [hβa l]
      _ = (γ.toMonoidHom.comp ψ₀) (a l) := by simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]

private lemma ltrcu3_component {d n : ℕ} {K : Type} [Field K] [Finite K]
    {L' : Type} [Group L'] [Finite L'] (ψ₁ : L' →* LargeEvenProj (unitarySU 2 n K d))
    (hψ₁ : Function.Surjective ψ₁) (hker : ψ₁.ker ≤ Subgroup.center L')
    {D : GL (Fin d) K}
    (hDnorm : D ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)))
    {e : MulAut L'}
    (he : ∀ l : L', TableB.projConj (unitarySU 2 n K d) ⟨D, hDnorm⟩ (ψ₁ l) = ψ₁ (e l))
    {J : Subgroup L'} (hJ : IsComponentOf J (ggFixSub e))
    (hlab : GGHasLabel (⟨.A, 1, 3⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J)) :
    IsComponentOf (J.map ψ₁) (ggFix (TableB.projConj (unitarySU 2 n K d) ⟨D, hDnorm⟩)) ∧
      GGHasLabel (⟨.A, 1, 3⟩ : LargeEvenLabel)
        (↥(J.map ψ₁) ⧸ Subgroup.center ↥(J.map ψ₁)) := by
  refine ⟨USixTwo.isComponentOf_map_fix hψ₁ hker he hJ, ?_⟩
  have hperf : Group.IsPerfect ↥J := Group.isPerfect_def.mpr hJ.2.2.1
  have hf : Function.Surjective (ψ₁.subgroupMap J) := ψ₁.subgroupMap_surjective J
  have hkerf : (ψ₁.subgroupMap J).ker ≤ Subgroup.center ↥J := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hψx : ψ₁ (x : L') = 1 := congrArg Subtype.val hx
    have hxc : (x : L') ∈ Subgroup.center L' := hker (MonoidHom.mem_ker.mpr hψx)
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp hxc (y : L')
  obtain ⟨φ⟩ := CFSG.Goldschmidt.G37.nonempty_centerQuotientEquiv hperf (ψ₁.subgroupMap J) hf hkerf
  exact ggHasLabel_of_mulEquiv φ hlab

private lemma ltrcu3_actor (h0 : UnitaryInndiagIsConj) {d n : ℕ} [NeZero d] {K : Type}
    [Field K] [Finite K] (h : UnitaryFieldData 2 n K) (hd3 : 3 ≤ d)
    (hdq : ¬ (d = 3 ∧ 2 ^ n = 2))
    {L' : Type} [Group L'] (ψ₁ : L' →* LargeEvenProj (unitarySU 2 n K d)) {a : MulAut L'}
    (β : MulAut (LargeEvenProj (unitarySU 2 n K d)))
    (hβ : β ∈ InndiagSU.inndiagU (d := d) h (by omega))
    (hβa : ∀ l : L', β (ψ₁ l) = ψ₁ (a l)) :
    ∃ (N : GL (Fin d) K)
      (hNnorm : N ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K))),
      N ∈ LargeEvenGUSet (Fin d) K (2 ^ n) ∧
        ∀ l : L', TableB.projConj (unitarySU 2 n K d) ⟨N, hNnorm⟩ (ψ₁ l) = ψ₁ (a l) := by
  have hφ : β ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n K d))
      (LargeEvenGUSet (Fin d) K (2 ^ n)) :=
    h0 d n K h (by omega) hd3 hdq β hβ
  have hS : LargeEvenGUSet (Fin d) K (2 ^ n) ⊆
      Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)) :=
    TableBUE.gu_subset_normalizer (d := d) h
  obtain ⟨N, hNgu, heq⟩ := TableB.exists_eq_projConj hS hφ
  refine ⟨N, hS hNgu, hNgu, ?_⟩
  intro l
  rw [← heq]
  exact hβa l

private lemma ltrcu3_zeta {d n : ℕ} [NeZero d] {K : Type} [Field K] [Finite K]
    (h : UnitaryFieldData 2 n K) (hdvd : 3 ∣ 2 ^ n + 1) (hd3 : 3 ≤ d)
    (hdq : ¬ (d = 3 ∧ 2 ^ n = 2))
    {L' : Type} [Group L'] (ψ₁ : L' →* LargeEvenProj (unitarySU 2 n K d))
    (hψ₁ : Function.Surjective ψ₁) {e a : MulAut L'} (hea : a * e = e * a)
    {τ : Fin d → Kˣ} (hτ : ∀ i, τ i ^ 3 = 1)
    (hDnorm : diagHom d τ ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)))
    {N : GL (Fin d) K}
    (hNnorm : N ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)))
    (he : ∀ l : L', TableB.projConj (unitarySU 2 n K d) ⟨diagHom d τ, hDnorm⟩ (ψ₁ l) =
      ψ₁ (e l))
    (ha : ∀ l : L', TableB.projConj (unitarySU 2 n K d) ⟨N, hNnorm⟩ (ψ₁ l) = ψ₁ (a l)) :
    ∃ ζ : Kˣ, ζ ^ 3 = 1 ∧
      N * diagHom d τ * N⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin d) ζ * diagHom d τ := by
  have hae : ∀ l : L', a (e l) = e (a l) := by
    intro l
    have h1 := congrArg (fun f : MulAut L' => f l) hea
    simpa [MulAut.mul_apply] using h1
  have hcomm : TableB.projConj (unitarySU 2 n K d) ⟨N, hNnorm⟩ *
      TableB.projConj (unitarySU 2 n K d) ⟨diagHom d τ, hDnorm⟩ =
      TableB.projConj (unitarySU 2 n K d) ⟨diagHom d τ, hDnorm⟩ *
      TableB.projConj (unitarySU 2 n K d) ⟨N, hNnorm⟩ := by
    ext x
    obtain ⟨l, rfl⟩ := hψ₁ x
    simp only [MulAut.mul_apply]
    rw [he l, ha (e l), hae l, ← he (a l), ← ha l]
  have hprod : TableB.projConj (unitarySU 2 n K d)
      (⟨N, hNnorm⟩ * ⟨diagHom d τ, hDnorm⟩ * ⟨N, hNnorm⟩⁻¹ *
        ⟨diagHom d τ, hDnorm⟩⁻¹) = 1 := by
    have h1 : TableB.projConj (unitarySU 2 n K d)
        (⟨N, hNnorm⟩ * ⟨diagHom d τ, hDnorm⟩ * ⟨N, hNnorm⟩⁻¹ *
          ⟨diagHom d τ, hDnorm⟩⁻¹) =
        TableB.projConj (unitarySU 2 n K d) ⟨N, hNnorm⟩ *
        TableB.projConj (unitarySU 2 n K d) ⟨diagHom d τ, hDnorm⟩ *
        (TableB.projConj (unitarySU 2 n K d) ⟨N, hNnorm⟩)⁻¹ *
        (TableB.projConj (unitarySU 2 n K d) ⟨diagHom d τ, hDnorm⟩)⁻¹ := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    rw [h1, hcomm]
    group
  have hK : Nat.card K = (2 ^ n) ^ 2 := h.card_eq_sq
  have hdq' : (d, 2 ^ n) ≠ (3, 2) := by
    intro hh
    exact hdq ⟨congrArg Prod.fst hh, congrArg Prod.snd hh⟩
  have hMscal := TableBUE.mem_scalars_of_projConj_eq_one h hK hd3 hdq' Nat.prime_three hdvd hprod
  rw [CFSG.Assembly.largeEvenScalars_def] at hMscal
  obtain ⟨ζ, hζ⟩ := hMscal
  have hζeq : Matrix.GeneralLinearGroup.scalar (Fin d) ζ =
      N * diagHom d τ * N⁻¹ * (diagHom d τ)⁻¹ := hζ
  have hτ3 : τ ^ 3 = 1 := by
    funext i
    simpa using hτ i
  have hD3 : (diagHom d τ) ^ 3 = 1 := by
    rw [← map_pow, hτ3, map_one]
  have hfinal : N * diagHom d τ * N⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin d) ζ * diagHom d τ := by
    calc N * diagHom d τ * N⁻¹
        = N * diagHom d τ * N⁻¹ * (diagHom d τ)⁻¹ * diagHom d τ := by group
      _ = Matrix.GeneralLinearGroup.scalar (Fin d) ζ * diagHom d τ := by rw [← hζeq]
  have hconj3 : (N * diagHom d τ * N⁻¹) ^ 3 = 1 := by
    have h1 : (N * diagHom d τ * N⁻¹) ^ 3 = N * (diagHom d τ) ^ 3 * N⁻¹ := conj_pow
    rw [h1, hD3, mul_one, mul_inv_cancel]
  have hscal3 : (Matrix.GeneralLinearGroup.scalar (Fin d) ζ * diagHom d τ) ^ 3 = 1 := by
    rw [← hfinal]
    exact hconj3
  have hmem : Matrix.GeneralLinearGroup.scalar (Fin d) ζ ∈ LargeEvenScalars (Fin d) K :=
    ⟨ζ, rfl⟩
  have hcomm' : Commute (Matrix.GeneralLinearGroup.scalar (Fin d) ζ) (diagHom d τ) :=
    (Subgroup.mem_center_iff.mp (TableB.scalars_le_center hmem) (diagHom d τ)).symm
  have hscalpow : (Matrix.GeneralLinearGroup.scalar (Fin d) ζ * diagHom d τ) ^ 3 =
      Matrix.GeneralLinearGroup.scalar (Fin d) (ζ ^ 3) := by
    rw [hcomm'.mul_pow 3, ← map_pow, hD3, mul_one]
  have hscalone : Matrix.GeneralLinearGroup.scalar (Fin d) (ζ ^ 3) = 1 := by
    rw [← hscalpow]
    exact hscal3
  have hζ3 : ζ ^ 3 = 1 := by
    have h1 : ((ζ ^ 3 : Kˣ) : K) = 1 := by
      have h2 := congrArg (fun g : GL (Fin d) K =>
        (g : Matrix (Fin d) (Fin d) K) 0 0) hscalone
      rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at h2
      simpa using h2
    exact Units.ext h1
  exact ⟨ζ, hζ3, hfinal⟩

private lemma ltrcu3_coreS (h0 : UnitaryInndiagIsConj) (h1 : UnitaryBlockOfComponent)
    (h2 : UnitaryBlockAction) {d n : ℕ} [NeZero d] {K : Type} [Field K] [Finite K]
    (h : UnitaryFieldData 2 n K) (hdvd : 3 ∣ 2 ^ n + 1) (hd3 : 3 ≤ d)
    (hdq : ¬ (d = 3 ∧ 2 ^ n = 2))
    {L' : Type} [Group L'] [Finite L'] (ψ₀ : L' →* LargeEvenProj (unitarySU 2 n K d))
    (hψ₀ : Function.Surjective ψ₀) (hker : ψ₀.ker ≤ Subgroup.center L')
    {e a : MulAut L'} {J : Subgroup L'} (hJ : IsComponentOf J (ggFixSub e))
    (hlab : GGHasLabel (⟨.A, 1, 3⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J))
    (hea : a * e = e * a) (haJ : ∀ j ∈ J, a j ∈ J)
    (hnot : ¬ ∃ y : ↥J ⧸ Subgroup.center ↥J, ∀ j j' : ↥J, a (j : L') = (j' : L') →
      (j' : ↥J ⧸ Subgroup.center ↥J) = y * (j : ↥J ⧸ Subgroup.center ↥J) * y⁻¹)
    {M : GL (Fin d) K}
    (hMN : M ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)))
    (hM3 : M ^ 3 = 1) (hMGU : M ∈ LargeEvenGUSet (Fin d) K (2 ^ n))
    (hθe : ∀ l : L', TableB.projConj (unitarySU 2 n K d) ⟨M, hMN⟩ (ψ₀ l) = ψ₀ (e l))
    (β : MulAut (LargeEvenProj (unitarySU 2 n K d)))
    (hβ : β ∈ InndiagSU.inndiagU (d := d) h (by omega))
    (hβa : ∀ l : L', β (ψ₀ l) = ψ₀ (a l)) : False := by
  obtain ⟨s, τ, hs, hτ⟩ := ltrcu3_frame h hdvd hMGU hM3
  have hDnorm : diagHom d τ ∈
      Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)) := by
    rw [← hs]
    have hsN : (s : GL (Fin d) K) ∈
        Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)) :=
      Subgroup.le_normalizer s.2
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hsN) hMN) hsN
  obtain ⟨ψ₁, hker₁eq, hsurj₁, he₁, β', hβ', hβ'a⟩ :=
    ltrcu3_transport h (by omega) ψ₀ hMN s hs hDnorm hθe β hβ hβa
  have hψ₁surj : Function.Surjective ψ₁ := hsurj₁ hψ₀
  have hker₁ : ψ₁.ker ≤ Subgroup.center L' := by
    rw [hker₁eq]
    exact hker
  obtain ⟨hJ₀, hlab₀⟩ := ltrcu3_component ψ₁ hψ₁surj hker₁ hDnorm he₁ hJ hlab
  obtain ⟨-, I, hIcard, hIclass, hIconst, hmap⟩ :=
    h1 d n K h hdvd hτ hDnorm rfl hJ₀ 3 hlab₀
  obtain ⟨N, hNnorm, hNgu, hN⟩ := ltrcu3_actor h0 h hd3 hdq ψ₁ β' hβ' hβ'a
  obtain ⟨ζ, hζ, hND⟩ := ltrcu3_zeta h hdvd hd3 hdq ψ₁ hψ₁surj hea hτ hDnorm hNnorm he₁ hN
  have hJqs : CFSG.IsQuasisimple J :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp hJ.2.2
  exact hnot (h2 d n K h hdvd L' ψ₁ hψ₁surj hker₁ J hJqs a haJ hτ hDnorm hNnorm hNgu rfl hζ hND
    hIcard hIclass hIconst hmap hN)

private lemma ltrcu3_core_contradiction (h0 : UnitaryInndiagIsConj)
    (h1 : UnitaryBlockOfComponent) (h2 : UnitaryBlockAction)
    (lab : LargeEvenLabel) (hΛ : LargeEvenInLambda2 lab) (htag : lab.tag = .twA)
    (h3 : 3 ∣ 2 ^ lab.n + 1)
    {R : Type} [Group R] {I : Set (MulAut R)}
    {L' : Type} [Group L'] [Finite L'] (ψ : L' →* R) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    (e : MulAut L') (J : Subgroup L') (a : MulAut L')
    (hsetup : GGRankOneSetup I ψ 3 e J 3 a) (hsplit : SplitLift lab R I ψ e) : False := by
  obtain ⟨-, -, -, -, -, hJ, -, hlab, hea, ⟨φa, hφaI, hφa⟩, haJ, hnot⟩ := hsetup
  simp only [LargeEvenInLambda2, htag] at hΛ
  obtain ⟨hn1, hr2, hr2n⟩ := hΛ
  have hd3 : 3 ≤ lab.rank + 1 := by omega
  have hdq : ¬ (lab.rank + 1 = 3 ∧ 2 ^ lab.n = 2) := by
    rintro ⟨hr, hq⟩
    have hn2 := hr2n (by omega)
    have : 2 ^ 2 ≤ 2 ^ lab.n := Nat.pow_le_pow_right (by norm_num) hn2
    omega
  rcases hsplit with ⟨hA, -⟩ | ⟨-, K, fK, finK, h, M, hMN, hM3, hMGU, θ, hθe, hθI⟩
  · rw [htag] at hA
    cases hA
  · letI : Field K := fK
    letI : Finite K := finK
    obtain ⟨β, hβ, hβa⟩ := hθI φa hφaI
    have hψ₀ : Function.Surjective (θ.toMonoidHom.comp ψ) := θ.surjective.comp hψ
    have hker₀ : (θ.toMonoidHom.comp ψ).ker ≤ Subgroup.center L' := by
      intro x hx
      apply hker
      rw [MonoidHom.mem_ker] at hx ⊢
      exact (map_eq_one_iff θ θ.injective).mp hx
    refine ltrcu3_coreS h0 h1 h2 h h3 hd3 hdq (θ.toMonoidHom.comp ψ) hψ₀ hker₀ hJ hlab hea haJ
      hnot hMN hM3 hMGU hθe β hβ ?_
    intro l
    show β (θ (ψ l)) = θ (ψ (a l))
    rw [hβa (ψ l), hφa l]

theorem splitLiftUnitaryThreeDvd_of_pieces (h0 : UnitaryInndiagIsConj)
    (h1 : UnitaryBlockOfComponent) (h2 : UnitaryBlockAction) : SplitLiftUnitaryThreeDvd := by
  intro lab hΛ htag h3
  intro Q hraw
  simp only [LargeEvenRawDatum, htag] at hraw ⊢
  obtain ⟨K, fieldK, finiteK, hcard, hQ⟩ := hraw
  refine ⟨K, fieldK, finiteK, hcard, hQ, ?_⟩
  intro L' _ _ ψ hψ hker hperf e J a hsetup hsplit
  exact ltrcu3_core_contradiction h0 h1 h2 lab hΛ htag h3 ψ hψ hker hperf e J a hsetup hsplit

end CFSG.StandardType.KD2Pieces1615

end
