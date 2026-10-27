module

public import CFSG.RankThree.PartOne.Q1327T.Item7Basic
public import CFSG.RankThree.PartOne.Q1327T.Item7Weights
public import CFSG.RankThree.PartOne.KF.UnitaryModel
public import CFSG.RankThree.PartOne.KF.F128SU
public import CFSG.RankThree.PartOne.KC.PlaneLifting
public import CFSG.RankThree.PartOne.N143X.WeylMatrix
public import CFSG.RankThree.PartOne.N143.SectionGroup
public import CFSG.Assembly.QuasithinDefs
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.Certificates.WordSubgroupRel
public import CFSG.ClassicalGroups
public import CFSG.LieType.Multipliers.ProductKernel
public import CFSG.LieType.Multipliers.U42Bridge
public import CFSG.LieType.Multipliers.U43Action
public import CFSG.LieType.Multipliers.U43BridgeInputs
public import CFSG.LieType.Multipliers.U62Action
public import CFSG.LieType.Multipliers.U62Bridge
public import CFSG.LieType.Multipliers.U62Kernel
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Milestones.CL_LIT_Griess_Schur_multipliers_Lie_type
public import CFSG.Monster.B.Classical.PlaneAut
public import CFSG.Monster.B.TwoA.Amalgam.Data
public import CFSG.Monster.B.TwoA.Sp8.Par1
public import CFSG.Monster.B.TwoA.Unitary.LinThree
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeSetting
public import CFSG.RankThree.PartOne.KF.SU5Model
public import CFSG.RankThree.PartOne.KF.SymCtxMatrix
public import CFSG.RankThree.PartOne.KF.ToralQuot
public import CFSG.RankThree.PartOne.S11c.Sec66Sp
public import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
public import CFSG.RankThree.PartOne.S11d.OutSymplectic
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.SmallOddCore.CheckSpec
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.Walter.Defs
public import CFSG.YGroups.Y322Central
public import Certificates.Certificate1
public import Certificates.Certificate10005
public import Certificates.Certificate10006
public import Certificates.Certificate10007
public import Certificates.Certificate10008
public import Certificates.Certificate10009
public import Certificates.Certificate10010
public import Certificates.Certificate10012
public import Certificates.Certificate10013
public import Certificates.Certificate10014
public import Certificates.Certificate10016
public import Certificates.Certificate10018
public import Certificates.Certificate12041
public import Certificates.Certificate12042
public import Certificates.Certificate12043
public import Certificates.Certificate12044
public import Certificates.Certificate12045
public import Certificates.Certificate12046
public import Certificates.Certificate16015
public import Certificates.Certificate16040
public import Certificates.Certificate2
public import Certificates.Certificate2154
public import Certificates.Certificate2157
public import Certificates.Certificate2267
public import Certificates.Certificate2326
public import Certificates.Certificate3006
public import Certificates.Certificate3007
public import Certificates.Certificate3008
public import Certificates.Certificate3063
public import Certificates.Certificate3077
public import Certificates.Certificate3082
public import Certificates.Certificate3083
public import Certificates.Certificate9130

public section

namespace CFSG.RankThree.PartOne.Q1327T

open Matrix CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU
  CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

section Torus

variable {K : Type} [Field K]

theorem pow_le_card_torusSU [Finite K] {p : ℕ} (hp : p.Prime) (hrK : p ∣ Nat.card Kˣ) (m : ℕ) :
    p ^ m ≤ Nat.card (torusSU p (m + 1) K) := by
  classical
  let μ := rootsOfUnity p K
  have hμ : Nat.card μ = p := CFSG.RankThree.PartTwo.Census.card_rootsOfUnity_of_dvd hp hrK
  let d : (Fin m → μ) → (Fin (m + 1) → Kˣ) := fun t =>
    Fin.snoc (α := fun _ => Kˣ) (fun j => ((t j : μ) : Kˣ)) (∏ j : Fin m, ((t j : μ) : Kˣ))⁻¹
  have hd1 : ∀ t j, d t (Fin.castSucc j) = ((t j : μ) : Kˣ) := fun t j => by
    simp [d]
  have hd2 : ∀ t, d t (Fin.last m) = (∏ j : Fin m, ((t j : μ) : Kˣ))⁻¹ := fun t => by
    simp [d]
  have hdp : ∀ t i, d t i ^ p = 1 := by
    intro t i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [hd2, inv_pow, ← Finset.prod_pow]
      simp [fun j => (mem_rootsOfUnity p _).1 (t j).2]
    · rw [hd1]
      exact (mem_rootsOfUnity p _).1 (t j).2
  have hdprod : ∀ t, ∏ i, d t i = 1 := by
    intro t
    rw [Fin.prod_univ_castSucc, hd2]
    simp [hd1]
  have hmem : ∀ t, (diagU (d t) : GL (Fin (m + 1)) K) ∈ torusSU p (m + 1) K := fun t =>
    mem_torusSU_iff.2 ⟨d t, hdp t, hdprod t, rfl⟩
  let g : (Fin m → μ) → torusSU p (m + 1) K := fun t => ⟨diagU (d t), hmem t⟩
  have hg : Function.Injective g := by
    intro s t hst
    have h2 := diagU_injective (congrArg Subtype.val hst)
    funext j
    have := congrFun h2 (Fin.castSucc j)
    rw [hd1, hd1] at this
    exact Subtype.ext this
  have := Nat.card_le_card_of_injective g hg
  rwa [CFSG.RankThree.PartTwo.Census.card_fun_rootsOfUnity hμ] at this

theorem isElementaryAbelian_torusSU_subgroupOf {n : ℕ} {p : ℕ} (H : Subgroup (GL (Fin n) K)) :
    IsElementaryAbelian p ((torusSU p n K).subgroupOf H) := by
  have hTcomm : ∀ x ∈ torusSU p n K, ∀ y ∈ torusSU p n K, x * y = y * x := by
    intro x hx y hy
    obtain ⟨d, -, -, rfl⟩ := mem_torusSU_iff.1 hx
    obtain ⟨d', -, -, rfl⟩ := mem_torusSU_iff.1 hy
    rw [diagU_mul, diagU_mul, mul_comm]
  have hTpow : ∀ x ∈ torusSU p n K, x ^ p = 1 := by
    intro x hx
    obtain ⟨d, hd, -, rfl⟩ := mem_torusSU_iff.1 hx
    rw [diagU_pow]
    have : d ^ p = 1 := funext fun i => hd i
    rw [this, diagU_one]
  refine { is_comm := ⟨fun a b => ?_⟩, exponent_dvd_p := ?_ }
  · apply Subtype.ext
    apply Subtype.ext
    exact hTcomm _ a.2 _ b.2
  · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => ?_
    apply Subtype.ext
    apply Subtype.ext
    exact hTpow _ x.2

end Torus

section Cover

variable {Q : Type} [Group Q] {K : Type} [Field K] {n q : ℕ}

theorem exists_cover_unitary (hZ : Subgroup.center Q = ⊥)
    (e : (Q ⧸ Subgroup.center Q) ≃* StatedProj (StatedSU n q K)) :
    ∃ π : StatedSU n q K →* Q, Function.Surjective π ∧
      π.ker = (StatedScalars (Fin n) K).subgroupOf (StatedSU n q K) := by
  let ce : Q ≃* (Q ⧸ Subgroup.center Q) :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  let N : Subgroup (StatedSU n q K) := (StatedScalars (Fin n) K).subgroupOf (StatedSU n q K)
  let π : StatedSU n q K →* Q :=
    (ce.symm.toMonoidHom.comp e.symm.toMonoidHom).comp (QuotientGroup.mk' N)
  refine ⟨π, ?_, ?_⟩
  · exact (ce.symm.surjective.comp e.symm.surjective).comp (QuotientGroup.mk'_surjective N)
  · ext x
    rw [MonoidHom.mem_ker]
    change ce.symm (e.symm (QuotientGroup.mk' N x)) = 1 ↔ x ∈ N
    rw [map_eq_one_iff ce.symm ce.symm.injective, map_eq_one_iff e.symm e.symm.injective]
    exact QuotientGroup.eq_one_iff (N := N) x

end Cover

section Diag

variable {Q : Type} [Group Q] [Finite Q] {K : Type} [Field K] {p f n : ℕ}

theorem false_of_unitary_diag (hp : p.Prime) (hn : 4 ≤ n) (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) (hpq : p ∣ 2 ^ f + 1) (π : unitarySU 2 f K n →* Q)
    (hπ : Function.Surjective π) (hker : ¬ p ∣ Nat.card π.ker) (hZ : Subgroup.center Q = ⊥)
    {Ē : Subgroup Q} (hE : IsElementaryAbelian p Ē) (hcard : Nat.card Ē = p ^ 2)
    (hmax : ∀ F : Subgroup Q, IsElementaryAbelian p F → F ≤ Subgroup.centralizer (Ē : Set Q) →
      Ē ≤ F → F ≤ Ē ⊔ Subgroup.center Q) : False := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hU : UnitaryFieldData 2 f K := unitaryFieldData_two hK hf
  have hfinK : Finite K := hU.finite
  obtain ⟨E₀, hE₀, hE₀card, hE₀map⟩ := exists_lift_elementaryAbelian π hp hker Ē
    (fun y _ => hπ y) hcard
  have hE₀exp : ∀ x ∈ E₀, x ^ p = 1 := fun x hx =>
    elemPow_eq_one_of_isElementaryAbelian (A := E₀) x hx
  have hE₀comm : ∀ x ∈ E₀, ∀ y ∈ E₀, x * y = y * x := fun x hx y hy => by
    have := congrArg Subtype.val ((IsMulCommutative.is_comm (M := E₀)).comm ⟨x, hx⟩ ⟨y, hy⟩)
    simpa using this
  obtain ⟨ψ, hψ⟩ := exists_diag_iso_le_of_iso hU hp hpq (MulEquiv.refl _) E₀ hE₀exp hE₀comm
  have hrK : p ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hK]
    have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    have hfac : (2 ^ f) ^ 2 - 1 = (2 ^ f + 1) * (2 ^ f - 1) := by
      zify [Nat.one_le_pow 2 (2 ^ f) (by omega), h1]
      ring
    rw [hfac]
    exact Dvd.dvd.mul_right hpq _
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hTle : torusSU p (m + 1) K ≤ unitarySU 2 f K (m + 1) := torusSU_le_unitarySU hU hpq
  let T : Subgroup (unitarySU 2 f K (m + 1)) := (torusSU p (m + 1) K).subgroupOf _
  have hTmem : ∀ g : unitarySU 2 f K (m + 1), g ∈ T ↔ (g : GL (Fin (m + 1)) K) ∈ torusSU p _ K :=
    fun g => Iff.rfl
  have hTcard : p ^ m ≤ Nat.card T := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTle).toEquiv]
    exact pow_le_card_torusSU hp hrK m
  have hTel : IsElementaryAbelian p T := isElementaryAbelian_torusSU_subgroupOf _
  let Eplus : Subgroup (unitarySU 2 f K (m + 1)) := T.map ψ.toMonoidHom
  have hEel : IsElementaryAbelian p Eplus := IsElementaryAbelian.map ψ.toMonoidHom
  have hE₀le : E₀ ≤ Eplus := by
    intro x hx
    exact ⟨ψ.symm x, (hTmem _).2 (hψ _ (by simpa using hx)), by simp⟩
  have hEcard : p ^ m ≤ Nat.card Eplus := by
    rw [Subgroup.card_map_of_injective ψ.injective]
    exact hTcard
  let P' : Subgroup Q := Eplus.map π
  have hP'el : IsElementaryAbelian p P' := IsElementaryAbelian.map π
  have hEP : Ē ≤ P' := by
    rw [← hE₀map]
    exact Subgroup.map_mono hE₀le
  have hP'card : Nat.card P' = Nat.card Eplus := by
    have hdis := N143.disjoint_ker_of_isPGroup π hp (IsElementaryAbelian.isPGroup p Eplus) hker
    exact N143.card_map_of_disjoint_ker π hdis
  have hC : P' ≤ Subgroup.centralizer (Ē : Set Q) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have := congrArg Subtype.val ((IsMulCommutative.is_comm (M := P')).comm ⟨a, hEP ha⟩ ⟨y, hy⟩)
    simpa using this
  have hle := hmax P' hP'el hC hEP
  rw [hZ, sup_bot_eq] at hle
  have h1 : Nat.card P' ≤ Nat.card Ē := Subgroup.card_le_of_le hle
  rw [hP'card, hcard] at h1
  have h2 : p ^ 2 < p ^ m := by
    have := hEcard
    have : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    have h3 : p ^ 3 ≤ p ^ m := Nat.pow_le_pow_right hp.pos (by omega)
    omega
  omega

end Diag

section Hermitian

open CFSG.RankThree.PartOne.N143X

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
  (L : Type) [Field L] [Algebra K L] (E : Subgroup (GL ι K))

local notation "φ" => iterateFrobenius L 2

theorem hermitian_pairing [CharP L 2] (f : ℕ) {A : Matrix ι ι L}
    (hA : (A.map (φ f))ᵀ * A = 1) (v w : ι → L) :
    ((φ f) ∘ (A *ᵥ v)) ⬝ᵥ (A *ᵥ w) = ((φ f) ∘ v) ⬝ᵥ w := by
  have h1 : ((φ f) ∘ (A *ᵥ v)) = (A.map (φ f)) *ᵥ ((φ f) ∘ v) :=
    funext fun i => RingHom.map_mulVec (φ f) A v i
  rw [h1]
  calc ((A.map (φ f)) *ᵥ ((φ f) ∘ v)) ⬝ᵥ (A *ᵥ w)
      = ((φ f) ∘ v) ⬝ᵥ ((A.map (φ f))ᵀ *ᵥ (A *ᵥ w)) := by
        rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
          dotProduct_comm]
    _ = ((φ f) ∘ v) ⬝ᵥ (((A.map (φ f))ᵀ * A) *ᵥ w) := by rw [Matrix.mulVec_mulVec]
    _ = ((φ f) ∘ v) ⬝ᵥ w := by rw [hA, Matrix.one_mulVec]

theorem joint_qinv_ne_bot_herm [IsAlgClosed L] [CharP L 2] {p : ℕ} (f : ℕ) (hp : (p : L) ≠ 0)
    (hexp : ∀ e : E, (e : GL ι K) ^ p = 1) (hcomm : ∀ e e' : E, (e : GL ι K) * e' = e' * e)
    (hEL : ∀ e : E, ((mapL L (e : GL ι K)).map (φ f))ᵀ * mapL L (e : GL ι K) = 1)
    {χ : E → L} (h : joint L E χ ≠ ⊥) : joint L E (fun e => (φ f (χ e))⁻¹) ≠ ⊥ := by
  by_contra hbot
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 h
  have hvanish : ∀ (ψ : E → L), ∀ w ∈ joint L E ψ, ((φ f) ∘ v) ⬝ᵥ w = 0 := by
    intro ψ w hw
    by_cases hψ : ψ = fun e => (φ f (χ e))⁻¹
    · subst hψ
      rw [hbot, Submodule.mem_bot] at hw
      subst hw
      simp
    · obtain ⟨g, hg⟩ := Function.ne_iff.1 hψ
      have h1 := hermitian_pairing L f (hEL g) v w
      rw [(mem_joint L E).1 hv g, (mem_joint L E).1 hw g] at h1
      have h2 : (φ f) ∘ (χ g • v) = (φ f (χ g)) • ((φ f) ∘ v) := by
        funext i
        simp [map_mul]
      rw [h2] at h1
      simp only [dotProduct_smul, smul_dotProduct, smul_eq_mul] at h1
      have hne : φ f (χ g) * ψ g ≠ 1 := fun h1' => hg (eq_inv_of_mul_eq_one_right h1')
      have h3 : (φ f (χ g) * ψ g - 1) * (((φ f) ∘ v) ⬝ᵥ w) = 0 := by linear_combination h1
      rcases mul_eq_zero.1 h3 with h0 | h0
      · exact absurd (sub_eq_zero.1 h0) hne
      · exact h0
  have htop := iSup_joint_eq_top L E hp hexp hcomm
  have hall : ∀ w : ι → L, ((φ f) ∘ v) ⬝ᵥ w = 0 := by
    intro w
    have hw : w ∈ ⨆ χ : E → L, joint L E χ := by rw [htop]; exact Submodule.mem_top
    refine Submodule.iSup_induction _ (motive := fun w => ((φ f) ∘ v) ⬝ᵥ w = 0) hw
      (fun ψ w hw => hvanish ψ w hw) (by simp) fun x y hx hy => ?_
    rw [dotProduct_add, hx, hy, add_zero]
  apply hv0
  funext i
  have := hall (Pi.single i 1)
  simp only [dotProduct_single, mul_one] at this
  exact (map_eq_zero (φ f)).1 this

theorem nuStable_of_hermitian [IsAlgClosed L] [CharP L 2] {p : ℕ} (f : ℕ) (hp : (p : L) ≠ 0)
    (hpq : p ∣ 2 ^ f - 1) (hexp : ∀ e : E, (e : GL ι K) ^ p = 1)
    (hcomm : ∀ e e' : E, (e : GL ι K) * e' = e' * e)
    (hEL : ∀ e : E, ((mapL L (e : GL ι K)).map (φ f))ᵀ * mapL L (e : GL ι K) = 1) :
    NuStable L E := by
  intro χ h
  have h1 := joint_qinv_ne_bot_herm L E f hp hexp hcomm hEL h
  have h2 : (fun e : E => (φ f (χ e))⁻¹) = fun e => (χ e)⁻¹ := by
    funext e
    have hχ := weight_pow_eq_one L E hexp h e
    obtain ⟨m, hm⟩ := hpq
    have hq : 2 ^ f = p * m + 1 := by
      have : 1 ≤ 2 ^ f := Nat.one_le_two_pow
      omega
    have hx : φ f (χ e) = χ e := by
      rw [iterateFrobenius_def, hq, pow_succ, pow_mul, hχ, one_pow, one_mul]
    rw [hx]
  rwa [h2] at h1

variable {L E}

theorem faithfulSmallSym_normalizer_range_herm [CharP K 2] {p : ℕ} (f : ℕ) (hp : (p : K) ≠ 0)
    (hp2 : p % 2 = 1) (hpq : p ∣ 2 ^ f - 1) [IsElementaryAbelian p E]
    (hEK : ∀ e ∈ E, (((e : GL ι K) : Matrix ι ι K).map (· ^ 2 ^ f))ᵀ *
      ((e : GL ι K) : Matrix ι ι K) = 1) :
    FaithfulSmallSym E.normalizerMonoidHom.range (Fintype.card ι) := by
  let L := AlgebraicClosure K
  have hpL : (p : L) ≠ 0 := by
    intro h0
    apply hp
    apply (algebraMap K L).injective
    rw [map_natCast, map_zero]
    exact h0
  have hexp : ∀ e : E, (e : GL ι K) ^ p = 1 := fun e =>
    elemPow_eq_one_of_isElementaryAbelian (A := E) e e.2
  have hcomm : ∀ e e' : E, (e : GL ι K) * e' = e' * e := fun e e' =>
    congrArg Subtype.val (IsMulCommutative.is_comm.comm e e')
  obtain ⟨hfin, hcard⟩ := nat_card_wts_le L E hpL hexp hcomm
  have hEL : ∀ e : E, ((mapL L (e : GL ι K)).map (iterateFrobenius L 2 f))ᵀ *
      mapL L (e : GL ι K) = 1 := by
    intro e
    have hmap : (mapL L (e : GL ι K)).map (iterateFrobenius L 2 f) =
        (((e : GL ι K) : Matrix ι ι K).map (· ^ 2 ^ f)).map (algebraMap K L) := by
      ext i j
      simp [mapL, Matrix.map_apply, iterateFrobenius_def, map_pow]
    rw [hmap, ← Matrix.transpose_map, mapL, ← Matrix.map_mul, hEK e e.2,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hν : NuStable L E := nuStable_of_hermitian L E f hpL hpq hexp hcomm hEL
  exact ⟨Wts L E, hfin, weightAction, hcard, weightAction_injective hpL hexp hcomm, nuPerm hν,
    nuPerm_sq hν, fun x y hx hy => nuPerm_fixed hp2 hexp hν x y hx hy,
    fun β => weightAction_comm_nuPerm hν β⟩

end Hermitian

section Unitary

variable {K : Type} [Field K] [Finite K] {p f n : ℕ}

theorem not_dvd_two_pow_add_one_of_dvd_sub_one (hp : p.Prime) (hp2 : p ≠ 2)
    (h : p ∣ 2 ^ f - 1) : ¬ p ∣ 2 ^ f + 1 := by
  intro h'
  have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have h2 : p ∣ (2 ^ f + 1) - (2 ^ f - 1) := Nat.dvd_sub h' h
  have h3 : (2 ^ f + 1) - (2 ^ f - 1) = 2 := by omega
  rw [h3] at h2
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)

theorem card_dvd_eight_of_unitary {Y : Type} [Group Y] (hp : p.Prime) (hp2 : p ≠ 2) (hn1 : 1 ≤ n)
    (hn : n ≤ 5) (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2) (hpq : p ∣ 2 ^ f - 1)
    (e : Y ≃* StatedProj (StatedSU n (2 ^ f) K)) {E : Subgroup Y} (hE : IsElementaryAbelian p E) :
    Nat.card E.normalizerMonoidHom.range ∣ 8 := by
  have hU : UnitaryFieldData 2 f K := unitaryFieldData_two hK hf
  have hchar : CharP K 2 := hU.charP
  have hpd : ¬ p ∣ Nat.gcd n (2 ^ f + 1) := fun hd =>
    not_dvd_two_pow_add_one_of_dvd_sub_one hp hp2 hpq (hd.trans (Nat.gcd_dvd_right _ _))
  have hpK : (p : K) ≠ 0 := by
    intro h0
    have := (CharP.cast_eq_zero_iff K 2 p).1 h0
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 this).symm
  obtain ⟨F, hF, hFM, -, hdvd⟩ := N143X.exists_cover_of_matrix_model (StatedSU n (2 ^ f) K) e hp
    (d := Nat.gcd n (2 ^ f + 1)) (fun c hc => by
      obtain ⟨h1, h2⟩ := ((CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hK hn1).2.1 c).1 hc
      exact pow_gcd_eq_one.2 ⟨h1, h2⟩) hpd hE
  have hEK : ∀ x ∈ F, (((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map (· ^ 2 ^ f))ᵀ *
      ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := fun x hx => by
    have := hFM hx
    have hset := (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hK hn1).1
    have hx' : x ∈ ({A : GL (Fin n) K | (A : Matrix (Fin n) (Fin n) K).det = 1 ∧
      ((A : Matrix (Fin n) (Fin n) K).map (· ^ 2 ^ f))ᵀ * (A : Matrix (Fin n) (Fin n) K) = 1} :
        Set (GL (Fin n) K)) := by
      rw [← hset]
      exact this
    exact hx'.2
  exact hdvd.trans (FaithfulSmallSym.card_dvd_eight
    (faithfulSmallSym_normalizer_range_herm f hpK (hp.eq_two_or_odd.resolve_left hp2) hpq hEK)
    (by rw [Fintype.card_fin]; exact hn))

end Unitary

section Rank

variable {K : Type} [Field K] [Finite K] {p n f : ℕ}

theorem pRank_statedProj_statedSU_le_one (hp : p.Prime) (hp2 : p ≠ 2) (hn1 : 1 ≤ n)
    (hK : Nat.card K = (2 ^ f) ^ 2) (hpq : ¬ p ∣ 2 ^ f + 1)
    (h : n / orderOf (-((2 ^ f : ℕ) : ZMod p)) ≤ 1) :
    CFSG.pRank p (StatedProj (StatedSU n (2 ^ f) K)) ≤ 1 := by
  have hpQ : ¬ p ∣ 2 ^ f := fun hd =>
    hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))
  have hN : ¬ p ∣ Nat.card ((StatedScalars (Fin n) K).subgroupOf (StatedSU n (2 ^ f) K)) := by
    rw [(CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hK hn1).2.2]
    exact fun hd => hpq (hd.trans (Nat.gcd_dvd_right _ _))
  rw [CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd hp _ hN]
  exact pRank_statedSU_le_one hp hp2 hK hpQ hn1 h

end Rank

section Conf

variable {p g : ℕ} {Q : Type} [Group Q] [Finite Q] {Ē : Subgroup Q}

theorem Row8Conf.two_le_pRank (h : Row8Conf p g Q Ē) :
    2 ≤ CFSG.pRank p (Q ⧸ Subgroup.center Q) := by
  obtain ⟨A, hA, hcard⟩ := h.exists_image
  exact CFSG.LieType.SteinbergBR.le_pRank_of_card h.prime.one_lt A hA hcard

end Conf

end CFSG.RankThree.PartOne.Q1327T
