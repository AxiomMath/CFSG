module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniLFrame
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpPlaneFrameDefs
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotGenTwoWindows
import CFSG.LocalAnalysis.StandardType.GGSuNsRootGenComp
import CFSG.LocalAnalysis.StandardType.GGLinearFusionSURepairBlock
import CFSG.GroupTheory.LocalCores.Components
import CFSG.LocalAnalysis.SeitzReduction.F4PilotBLift
import CFSG.LocalAnalysis.StandardType.GGTBRowSignedFrameAux
import CFSG.LocalAnalysis.StandardType.GGSecFiveBNbrCompare

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag Matrix CFSG.LocalAnalysis.ComponentInitial
open CFSG.SectionRank.OddCover CFSG.RankThree.Classical CFSG.RankThree.Classical2
open scoped commutatorElement

variable {G : Type} [Group G] {p n f : ℕ} {K : Type} [Field K] {Bs X : Subgroup G}
  {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Equiv.Perm (Fin n)}
  {σ : ↥(unitarySU 2 f K n) →* G} {χ : Multiplicative (ZMod p) →* Kˣ}

private theorem ublk_isBlockOn_conjN {K : Type} [Field K] {n f : ℕ} {S : Finset (Fin n)}
    {D : GL (Fin n) K} {t : Fin n → Kˣ}
    (hDm : (D : Matrix (Fin n) (Fin n) K) = diagonal (fun k => (t k : K)))
    (hD : D ∈ Subgroup.normalizer (unitarySU 2 f K n : Set (GL (Fin n) K)))
    {s : ↥(unitarySU 2 f K n)} (hs : s ∈ TableBUE.blockSU (K := K) (n := f) S) :
    LineU.conjN D hD s ∈ TableBUE.blockSU (K := K) (n := f) S := by
  rw [TableBUE.mem_blockSU] at hs ⊢
  intro i j hij
  have ht : ∀ k, (t k : K) ≠ 0 := fun k => Units.ne_zero (t k)
  rw [LineU.coe_conjN]
  simp only [Units.val_mul, hDm, LineU.coe_inv_diag hDm]
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, hs i j hij]
  by_cases h : i = j
  · subst h
    rw [Matrix.one_apply_eq, mul_one, mul_inv_cancel₀ (ht i)]
  · rw [Matrix.one_apply_ne h, mul_zero, zero_mul]

private theorem ublk_conjN_eq_self {K : Type} [Field K] {n f : ℕ} {S : Finset (Fin n)}
    {D : GL (Fin n) K} {t : Fin n → Kˣ}
    (hDm : (D : Matrix (Fin n) (Fin n) K) = diagonal (fun k => (t k : K)))
    (hD : D ∈ Subgroup.normalizer (unitarySU 2 f K n : Set (GL (Fin n) K)))
    (ht : ∀ i ∈ S, ∀ j ∈ S, t i = t j)
    {s : ↥(unitarySU 2 f K n)} (hs : s ∈ TableBUE.blockSU (K := K) (n := f) S) :
    LineU.conjN D hD s = s := by
  have hD_eq : D = diagHom n t := by
    apply Units.ext
    rw [hDm, coe_diagHom]
  have hcomm : D * (s : GL (Fin n) K) = (s : GL (Fin n) K) * D := by
    rw [hD_eq]
    exact TableBUE.diagHom_mul_comm_of_isBlockOn ht (TableBUE.mem_blockSU.mp hs)
  apply Subtype.ext
  rw [LineU.coe_conjN, hcomm]
  group

private theorem ublk_diagHom_conj_swap_matrix {K : Type} [Field K] {n : ℕ} (i j : Fin n)
    (d : Fin n → Kˣ) :
    (((diagHom n d * permGL (Equiv.swap i j) * (diagHom n d)⁻¹ *
        (permGL (Equiv.swap i j))⁻¹) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) =
      diagonal (fun k => ((d k : K) * (((d (Equiv.swap i j k))⁻¹ : Kˣ) : K))) := by
  have h2 := permGL_mul_diagHom_mul_inv (K := K) (Equiv.swap i j) (fun k => (d k)⁻¹)
  rw [Equiv.symm_swap] at h2
  have hmain : (diagHom n d * permGL (Equiv.swap i j) * (diagHom n d)⁻¹ *
      (permGL (Equiv.swap i j))⁻¹ : GL (Fin n) K) =
      diagHom n (fun k => d k * (d (Equiv.swap i j k))⁻¹) := by
    rw [← map_inv (diagHom (K := K) n) d]
    calc diagHom n d * permGL (Equiv.swap i j) * diagHom n (fun k => (d k)⁻¹) *
          (permGL (Equiv.swap i j))⁻¹
        = diagHom n d * (permGL (Equiv.swap i j) * diagHom n (fun k => (d k)⁻¹) *
            (permGL (Equiv.swap i j))⁻¹) := by group
      _ = diagHom n d * diagHom n ((fun k => (d k)⁻¹) ∘ Equiv.swap i j) := by rw [h2]
      _ = diagHom n (fun k => d k * (d (Equiv.swap i j k))⁻¹) := by
            rw [← map_mul]
            rfl
  rw [hmain, coe_diagHom]
  simp only [Units.val_mul, Units.val_inv_eq_inv_val]

private theorem ublk_conj_mem_map {G : Type} [Group G] {p n f : ℕ} {K : Type} [Field K]
    {Bs X : Subgroup G} {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    {π : Equiv.Perm (Fin n)} {σ : ↥(unitarySU 2 f K n) →* G}
    {χ : Multiplicative (ZMod p) →* Kˣ}
    (hF : GGSecFiveBPermUniLFrame Bs X eta π σ χ) (S : Finset (Fin n)) {b : G}
    (hb : b ∈ Bs) {x : G} (hx : x ∈ (TableBUE.blockSU (K := K) (n := f) S).map σ) :
    b * x * b⁻¹ ∈ (TableBUE.blockSU (K := K) (n := f) S).map σ := by
  obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hx
  obtain ⟨D, hD, hDm, hconj⟩ := hF.2.2.2 ⟨b, hb⟩
  exact Subgroup.mem_map.mpr
    ⟨LineU.conjN D hD s, ublk_isBlockOn_conjN hDm hD hs, (hconj s).symm⟩

theorem GGSecFiveBPermUniLFrame.le_normalizer_map_blockSU
    (hF : GGSecFiveBPermUniLFrame Bs X eta π σ χ) (S : Finset (Fin n)) :
    Bs ≤ Subgroup.normalizer
      (((TableBUE.blockSU (K := K) (n := f) S).map σ : Subgroup G) : Set G) := by
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact ublk_conj_mem_map hF S hb
  · intro hx
    have h := ublk_conj_mem_map hF S (Bs.inv_mem hb) hx
    rwa [show b⁻¹ * (b * x * b⁻¹) * (b⁻¹)⁻¹ = x by group] at h

theorem GGSecFiveBPermUniLFrame.map_blockSU_le_centralizer
    (hF : GGSecFiveBPermUniLFrame Bs X eta π σ χ) (i j : Fin n) :
    (TableBUE.blockSU (K := K) (n := f) ({i, j} : Finset (Fin n))).map σ ≤
      Subgroup.centralizer (ggBsCoordZeroOn Bs eta {π i, π j} : Set G) := by
  rintro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  obtain ⟨hb, hco⟩ := mem_ggBsCoordZeroOn.1 hh
  obtain ⟨D, hD, hDm, hconj⟩ := hF.2.2.2 ⟨h, hb⟩
  obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hx
  let d : Fin n → Kˣ := fun k => χ (eta ⟨h, hb⟩ (π k))
  have hDmd : (D : Matrix (Fin n) (Fin n) K) = diagonal (fun k => (d k : K)) := hDm
  have hdi : d i = 1 := by
    have h1 : eta ⟨h, hb⟩ (π i) = 1 := hco (π i) (by simp)
    show χ (eta ⟨h, hb⟩ (π i)) = 1
    rw [h1, map_one]
  have hdj : d j = 1 := by
    have h1 : eta ⟨h, hb⟩ (π j) = 1 := hco (π j) (by simp)
    show χ (eta ⟨h, hb⟩ (π j)) = 1
    rw [h1, map_one]
  have hconst : ∀ a ∈ ({i, j} : Finset (Fin n)), ∀ b ∈ ({i, j} : Finset (Fin n)),
      d a = d b := by
    intro a ha b hb'
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb'
    rcases ha with rfl | rfl <;> rcases hb' with rfl | rfl
    · rfl
    · rw [hdi, hdj]
    · rw [hdj, hdi]
    · rfl
  have hfix : LineU.conjN D hD s = s := ublk_conjN_eq_self hDmd hD hconst hs
  have hconj' : (h : G) * σ s * (h : G)⁻¹ = σ s := by
    rw [hconj s, hfix]
  calc (h : G) * σ s = ((h : G) * σ s * (h : G)⁻¹) * (h : G) := by group
    _ = σ s * (h : G) := by rw [hconj']

theorem GGSecFiveBPermUniLFrame.not_mem_centralizer_map_blockSU
    (hF : GGSecFiveBPermUniLFrame Bs X eta π σ χ) (hK : UnitaryFieldData 2 f K)
    (hp : p.Prime) (hn : 3 ≤ n) {i j : Fin n} (hij : i ≠ j) :
    ((eta.symm (Pi.mulSingle (π i) (Multiplicative.ofAdd (1 : ZMod p))) : ↥Bs) : G) ∉
      Subgroup.centralizer
        (((TableBUE.blockSU (K := K) (n := f) ({i, j} : Finset (Fin n))).map σ : Subgroup G) :
          Set G) := by
  have : Fact p.Prime := ⟨hp⟩
  let Q : Subgroup G := (TableBUE.blockSU (K := K) (n := f) ({i, j} : Finset (Fin n))).map σ
  let y : Fin n → Multiplicative (ZMod p) :=
    Pi.mulSingle (π i) (Multiplicative.ofAdd (1 : ZMod p))
  let b₀ : ↥Bs := eta.symm y
  change (b₀ : G) ∉ Subgroup.centralizer (Q : Set G)
  intro hc
  obtain ⟨D, hD, hDm, hconj⟩ := hF.2.2.2 b₀
  let d : Fin n → Kˣ := fun k => χ (eta b₀ (π k))
  have hDmd : (D : Matrix (Fin n) (Fin n) K) = diagonal (fun k => (d k : K)) := hDm
  have hD_eq : D = diagHom n d := by
    apply Units.ext
    rw [hDmd, coe_diagHom]
  let P : ↥(unitarySU 2 f K n) :=
    ⟨permGL (Equiv.swap i j), TableBUE.permGL_swap_mem hK i j⟩
  have hPblock : P ∈ TableBUE.blockSU (K := K) (n := f) ({i, j} : Finset (Fin n)) :=
    TableBUE.mem_blockSU.mpr
      (TableBUE.isBlockOn_permGL_swap (S := ({i, j} : Finset (Fin n))) (by simp) (by simp))
  have hPmem : σ P ∈ Q := Subgroup.mem_map.mpr ⟨P, hPblock, rfl⟩
  have hcomm : σ P * (b₀ : G) = (b₀ : G) * σ P :=
    Subgroup.mem_centralizer_iff.mp hc (σ P) hPmem
  have hfix : (b₀ : G) * σ P * (b₀ : G)⁻¹ = σ P := by
    rw [← hcomm]
    group
  have hσeq : σ (LineU.conjN D hD P) = σ P := by
    rw [← hconj P]
    exact hfix
  have hker1 : σ (LineU.conjN D hD P * P⁻¹) = 1 := by
    rw [map_mul, map_inv, hσeq, mul_inv_cancel]
  obtain ⟨c, hc'⟩ := hF.2.1 (LineU.conjN D hD P * P⁻¹) hker1
  have e1 : ((LineU.conjN D hD P * P⁻¹ : ↥(unitarySU 2 f K n)) : GL (Fin n) K) =
      diagHom n d * permGL (Equiv.swap i j) * (diagHom n d)⁻¹ *
        (permGL (Equiv.swap i j))⁻¹ := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, LineU.coe_conjN, hD_eq]
  have hmat : (((LineU.conjN D hD P * P⁻¹ : ↥(unitarySU 2 f K n)) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) =
      diagonal (fun k => ((d k : K) * (((d (Equiv.swap i j k))⁻¹ : Kˣ) : K))) := by
    rw [e1]
    exact ublk_diagHom_conj_swap_matrix i j d
  have hdiag : diagonal (fun k => ((d k : K) * (((d (Equiv.swap i j k))⁻¹ : Kˣ) : K))) =
      diagonal (fun _ => c) := by
    rw [← hmat, hc']
  have hentry : ∀ k, ((d k : K) * (((d (Equiv.swap i j k))⁻¹ : Kˣ) : K)) = c := by
    intro k
    have h := congrFun (congrFun hdiag k) k
    simpa using h
  obtain ⟨k, hki, hkj⟩ := LineU.exists_not_mem_two hn i j
  have hc1 : c = 1 := by
    have h := hentry k
    rw [Equiv.swap_apply_of_ne_of_ne hki hkj] at h
    have h1 : ((d k : K) * (((d k)⁻¹ : Kˣ) : K)) = 1 := by
      rw [Units.val_inv_eq_inv_val, mul_inv_cancel₀ (Units.ne_zero (d k))]
    rw [h1] at h
    exact h.symm
  have hdi : ((d i : K) * (((d j)⁻¹ : Kˣ) : K)) = 1 := by
    have h := hentry i
    rw [Equiv.swap_apply_left, hc1] at h
    exact h
  have hdij : d i = d j := by
    apply Units.ext
    have h1 : (d i : K) * ((d j : K))⁻¹ = 1 := by
      simpa [Units.val_inv_eq_inv_val] using hdi
    exact (mul_inv_eq_one₀ (Units.ne_zero (d j))).mp h1
  have heta : eta b₀ (π i) = eta b₀ (π j) :=
    hF.2.2.1 (show χ (eta b₀ (π i)) = χ (eta b₀ (π j)) from hdij)
  have hb₀eta : eta b₀ = y := MulEquiv.apply_symm_apply eta y
  have hleft : eta b₀ (π i) = Multiplicative.ofAdd (1 : ZMod p) := by
    rw [hb₀eta]
    exact Pi.mulSingle_eq_same (M := fun _ => Multiplicative (ZMod p))
      (π i) (Multiplicative.ofAdd (1 : ZMod p))
  have hright : eta b₀ (π j) = 1 := by
    rw [hb₀eta]
    exact Pi.mulSingle_eq_of_ne (M := fun _ => Multiplicative (ZMod p))
      (π.injective.ne hij.symm) _
  have hone : (1 : ZMod p) = 0 := by
    have h := heta
    rw [hleft, hright] at h
    simpa using congrArg Multiplicative.toAdd h
  exact one_ne_zero hone

theorem GGSecFiveBPermUniLFrame.isQuasisimple_map_blockSU
    (hF : GGSecFiveBPermUniLFrame Bs X eta π σ χ) (hK : UnitaryFieldData 2 f K) (hf : 2 ≤ f)
    {S : Finset (Fin n)} (hS : 2 ≤ S.card) :
    CFSG.IsQuasisimple ↥((TableBUE.blockSU (K := K) (n := f) S).map σ) := by
  have hker : σ.ker ≤ Subgroup.center ↥(unitarySU 2 f K n) := by
    intro g hg
    rw [Subgroup.mem_center_iff]
    intro x
    obtain ⟨c, hc⟩ := hF.2.1 g (MonoidHom.mem_ker.mp hg)
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hc]
    ext a b
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    exact mul_comm _ _
  exact (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp
    (SURepair.isQuasisimple_map_blockSU_of_two_le hK hf hker hS)

theorem GGSecFiveBPermUniLFrame.map_blockSU_le_ggBlockComm
    (hF : GGSecFiveBPermUniLFrame Bs X eta π σ χ) (hK : UnitaryFieldData 2 f K) (hf : 2 ≤ f)
    (hp : p.Prime) (hn : 3 ≤ n) {i j : Fin n} (hij : i ≠ j) :
    (TableBUE.blockSU (K := K) (n := f) ({i, j} : Finset (Fin n))).map σ ≤
      ggBlockComm Bs eta {π i, π j} := by
  have hS : 2 ≤ ({i, j} : Finset (Fin n)).card := by
    simp [Finset.card_pair hij]
  let Q : Subgroup G := (TableBUE.blockSU (K := K) (n := f) ({i, j} : Finset (Fin n))).map σ
  change Q ≤ ggBlockComm Bs eta {π i, π j}
  have hQq : CFSG.IsQuasisimple ↥Q := hF.isQuasisimple_map_blockSU hK hf hS
  have hBsn : Bs ≤ Subgroup.normalizer (Q : Set G) :=
    hF.le_normalizer_map_blockSU ({i, j} : Finset (Fin n))
  let y : Fin n → Multiplicative (ZMod p) :=
    Pi.mulSingle (π i) (Multiplicative.ofAdd (1 : ZMod p))
  let b₀ : ↥Bs := eta.symm y
  have hcent : (b₀ : G) ∉ Subgroup.centralizer (Q : Set G) :=
    hF.not_mem_centralizer_map_blockSU hK hp hn hij
  have hb₀norm : (b₀ : G) ∈ Subgroup.normalizer (Q : Set G) := hBsn b₀.2
  have hle : Q ≤ ⁅Q, Subgroup.zpowers (b₀ : G)⁆ :=
    CFSG.SeitzReduction.F4Pilot.le_commutator_zpowers_of_isQuasisimple hQq hb₀norm hcent
  refine hle.trans ?_
  rw [ggBlockComm]
  exact Subgroup.commutator_mono (hF.map_blockSU_le_centralizer i j)
    (Subgroup.zpowers_le.mpr b₀.2)

theorem GGSecFiveBPermUniLFrame.le_iSup_ggBlockComm
    (hF : GGSecFiveBPermUniLFrame Bs X eta π σ χ) (hK : UnitaryFieldData 2 f K) (hf : 2 ≤ f)
    (hp : p.Prime) (hn : 3 ≤ n) (c₀ d₀ : Fin n) :
    X ≤ ⨆ (c : Fin n) (d : Fin n) (_ : c ≠ d ∧ ({c, d} : Set (Fin n)) ≠ {c₀, d₀}),
      ggBlockComm Bs eta {c, d} := by
  have hq : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hX : X = (⊤ : Subgroup ↥(unitarySU 2 f K n)).map σ := by
    rw [← hF.1, MonoidHom.range_eq_map]
  rw [hX, ← SuNsRootGen.iSup_blockSU_pairs (n := f) (d := n) hK hq hn (π.symm c₀) (π.symm d₀)]
  rw [Subgroup.map_le_iff_le_comap]
  refine iSup_le fun c => iSup_le fun d => iSup_le fun h => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  refine (hF.map_blockSU_le_ggBlockComm hK hf hp hn h.1).trans ?_
  have hne : ({π c, π d} : Set (Fin n)) ≠ {c₀, d₀} := by
    intro he
    apply h.2
    have himg : π.symm '' ({π c, π d} : Set (Fin n)) =
        π.symm '' ({c₀, d₀} : Set (Fin n)) := by rw [he]
    have hset : (({c, d} : Finset (Fin n)) : Set (Fin n)) =
        (({π.symm c₀, π.symm d₀} : Finset (Fin n)) : Set (Fin n)) := by
      simpa [Set.image_pair] using himg
    exact Finset.coe_injective hset
  exact le_iSup_of_le (π c)
    (le_iSup_of_le (π d) (le_iSup_of_le ⟨π.injective.ne h.1, hne⟩ le_rfl))

theorem GGSecFiveBPermUniLFrame.le_of_ggBlockComm_le
    (hF : GGSecFiveBPermUniLFrame Bs X eta π σ χ) (hK : UnitaryFieldData 2 f K) (hf : 2 ≤ f)
    (hp : p.Prime) (hn : 3 ≤ n) (c₀ d₀ : Fin n) {M : Subgroup G}
    (hM : ∀ c d : Fin n, c ≠ d → ({c, d} : Set (Fin n)) ≠ {c₀, d₀} →
      ggBlockComm Bs eta {c, d} ≤ M) :
    X ≤ M :=
  (hF.le_iSup_ggBlockComm hK hf hp hn c₀ d₀).trans <|
    iSup_le fun c => iSup_le fun d => iSup_le fun h => hM c d h.1 h.2

theorem le_of_ggBlockComm_le_of_model [Finite G] (hp : p.Prime) (hp2 : p ≠ 2)
    (hBs : CFSG.Open.IsElemAbelian p Bs)
    (hBsC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hC : Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) ≤ p) (hn : 4 ≤ n)
    (hA : (ggAutomizer X Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p)
    [Finite K] (hf : 2 ≤ f) (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (φ : ↥(unitarySU 2 f K n) →* ↥X) (hM : UnitTB.Model φ)
    (hdiag : ∀ a ∈ (ggGamma X hN).range, ∃ t : Fin n → K, LineU.ActsDiagU φ a t)
    (c₀ d₀ : Fin n) {M : Subgroup G}
    (hMle : ∀ c d : Fin n, c ≠ d → ({c, d} : Set (Fin n)) ≠ {c₀, d₀} →
      ggBlockComm Bs eta {c, d} ≤ M) :
    X ≤ M := by
  obtain ⟨σ', χ', hF⟩ := exists_uniLFrame_of_model hp hp2 hBs hBsC hC hn eta hA hN φ hM hdiag 1
  exact hF.le_of_ggBlockComm_le hM.field hf hp (by omega) c₀ d₀ hMle

private theorem ublk_isBlockOn_mul_apply {K : Type} [Field K] {n : ℕ} {S T : Finset (Fin n)}
    (hST : Disjoint S T) {M N : Matrix (Fin n) (Fin n) K} (hM : TableBUE.IsBlockOn S M)
    (hN : TableBUE.IsBlockOn T N) (i j : Fin n) :
    (M * N) i j = M i j + N i j - (1 : Matrix (Fin n) (Fin n) K) i j := by
  by_cases hi : i ∈ S
  · by_cases hj : j ∈ T
    · have hiT : i ∉ T := Finset.disjoint_left.mp hST hi
      have hjS : j ∉ S := Finset.disjoint_right.mp hST hj
      have hij : i ≠ j := fun h => hiT (by rw [h]; exact hj)
      have h0 : ∀ k, M i k * N k j = 0 := by
        intro k
        by_cases hk : k ∈ S
        · have hkT : k ∉ T := Finset.disjoint_left.mp hST hk
          rw [hN k j (Or.inl hkT), Matrix.one_apply_ne (fun h => hkT (by rw [h]; exact hj)),
            mul_zero]
        · rw [hM i k (Or.inr hk), Matrix.one_apply_ne (fun h => hk (by rw [← h]; exact hi)),
            zero_mul]
      rw [Matrix.mul_apply, Finset.sum_eq_zero fun k _ => h0 k, hM i j (Or.inr hjS),
        hN i j (Or.inl hiT), Matrix.one_apply_ne hij]
      ring
    · rw [hN.mul_apply_right (M := M) i hj, hN i j (Or.inr hj)]
      ring
  · rw [hM.mul_apply_left (N := N) hi, hM i j (Or.inl hi)]
    ring

theorem commute_map_blockSU_of_disjoint (σ : ↥(unitarySU 2 f K n) →* G)
    {S T : Finset (Fin n)} (hST : Disjoint S T) :
    ∀ x ∈ (TableBUE.blockSU (K := K) (n := f) S).map σ,
      ∀ y ∈ (TableBUE.blockSU (K := K) (n := f) T).map σ, x * y = y * x := by
  rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  have hs' := TableBUE.mem_blockSU.mp hs
  have ht' := TableBUE.mem_blockSU.mp ht
  ext i j
  rw [ublk_isBlockOn_mul_apply hST hs' ht' i j, ublk_isBlockOn_mul_apply hST.symm ht' hs' i j,
    add_comm (((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j)]

theorem ublk_centralizer_map_conj (H : Subgroup G) (g : G) :
    (Subgroup.centralizer (H : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ((H.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  ext y
  constructor
  · rintro ⟨c, hc, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff] at hc
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨x, hx, rfl⟩
    have := hc x hx
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * x * g⁻¹ * (g * c * g⁻¹) = g * (x * c) * g⁻¹ := by group
      _ = g * (c * x) * g⁻¹ := by rw [this]
      _ = g * c * g⁻¹ * (g * x * g⁻¹) := by group
  · intro hy
    refine ⟨g⁻¹ * y * g, ?_, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    rw [Subgroup.mem_centralizer_iff] at hy
    intro x hx
    have := hy (g * x * g⁻¹) ⟨x, hx, rfl⟩
    calc x * (g⁻¹ * y * g) = g⁻¹ * ((g * x * g⁻¹) * y) * g := by group
      _ = g⁻¹ * (y * (g * x * g⁻¹)) * g := by rw [this]
      _ = g⁻¹ * y * g * x := by group

theorem eta_ggConjAut_apply_of_permAut {g : G} (hg : g ∈ Subgroup.normalizer (Bs : Set G))
    {τ : Equiv.Perm (Fin n)} (hτ : MulAut.congr eta (ggConjAut Bs hg) = SpCoord.permAut τ)
    (b : ↥Bs) (j : Fin n) : eta (ggConjAut Bs hg b) (τ j) = eta b j := by
  have h := congrArg (fun φ : MulAut (Fin n → Multiplicative (ZMod p)) => φ (eta b)) hτ
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h
  rw [h, SpCoord.permAut_apply]
  simp

theorem ggBsCoordZeroOn_map_conj {g : G} (hg : g ∈ Subgroup.normalizer (Bs : Set G))
    {τ : Equiv.Perm (Fin n)} (hτ : MulAut.congr eta (ggConjAut Bs hg) = SpCoord.permAut τ)
    (S : Set (Fin n)) :
    (ggBsCoordZeroOn Bs eta S).map (MulAut.conj g).toMonoidHom =
      ggBsCoordZeroOn Bs eta (τ '' S) := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨hbB, hbS⟩ := mem_ggBsCoordZeroOn.1 hb
    have hx : (MulAut.conj g).toMonoidHom b ∈ Bs := (Subgroup.mem_normalizer_iff.mp hg b).mp hbB
    have he : (ggConjAut Bs hg ⟨b, hbB⟩ : ↥Bs) = ⟨(MulAut.conj g).toMonoidHom b, hx⟩ := rfl
    refine mem_ggBsCoordZeroOn.2 ⟨hx, ?_⟩
    rintro _ ⟨i, hi, rfl⟩
    have h := eta_ggConjAut_apply_of_permAut hg hτ ⟨b, hbB⟩ i
    rw [he] at h
    rw [h]
    exact hbS i hi
  · intro hx
    obtain ⟨hxB, hxS⟩ := mem_ggBsCoordZeroOn.1 hx
    have hb : g⁻¹ * x * g ∈ Bs := (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * x * g)).mpr
      (by rw [show g * (g⁻¹ * x * g) * g⁻¹ = x by group]; exact hxB)
    refine ⟨g⁻¹ * x * g, mem_ggBsCoordZeroOn.2 ⟨hb, fun i hi => ?_⟩,
      by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
    have he : (ggConjAut Bs hg ⟨g⁻¹ * x * g, hb⟩ : ↥Bs) = ⟨x, hxB⟩ :=
      Subtype.ext (by rw [ggConjAut_apply]; group)
    have h := eta_ggConjAut_apply_of_permAut hg hτ ⟨g⁻¹ * x * g, hb⟩ i
    rw [he] at h
    rw [← h]
    exact hxS (τ i) ⟨i, hi, rfl⟩

theorem ggBlockComm_map_conj {g : G} (hg : g ∈ Subgroup.normalizer (Bs : Set G))
    {τ : Equiv.Perm (Fin n)} (hτ : MulAut.congr eta (ggConjAut Bs hg) = SpCoord.permAut τ)
    (S : Set (Fin n)) :
    (ggBlockComm Bs eta S).map (MulAut.conj g).toMonoidHom = ggBlockComm Bs eta (τ '' S) := by
  have hB : Bs.map (MulAut.conj g).toMonoidHom = Bs := Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
  rw [ggBlockComm, ggBlockComm, Subgroup.map_commutator, ublk_centralizer_map_conj,
    ggBsCoordZeroOn_map_conj hg hτ, hB]

theorem ggBlockComm_image_map_conj {g : G} (hg : g ∈ Subgroup.normalizer (Bs : Set G))
    {ρ : Equiv.Perm (Fin n)}
    (hτ : MulAut.congr eta (ggConjAut Bs hg) = SpCoord.permAut (π * ρ * π⁻¹)) (A : Set (Fin n)) :
    (ggBlockComm Bs eta (π '' A)).map (MulAut.conj g).toMonoidHom =
      ggBlockComm Bs eta (π '' (ρ '' A)) := by
  rw [ggBlockComm_map_conj hg hτ]
  congr 1
  rw [Set.image_image, Set.image_image]
  congr 1
  ext x
  simp [Equiv.Perm.coe_mul]

theorem exists_mem_conjAut_eq_permAut_swap
    (hA : (ggAutomizer X Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p)
    {a b : Fin n} (hab : a ≠ b) :
    ∃ g ∈ X, ∃ hg : g ∈ Subgroup.normalizer (Bs : Set G),
      MulAut.congr eta (ggConjAut Bs hg) = SpCoord.permAut (Equiv.swap a b) := by
  have hmem : SpCoord.permAut (Equiv.swap a b) ∈
      (ggAutomizer X Bs).map (MulAut.congr eta).toMonoidHom := by
    rw [hA]
    exact Subgroup.subset_closure ⟨a, b, hab, rfl⟩
  obtain ⟨g, hg, hgX, hgτ⟩ := exists_mem_of_mem_map_congr eta hmem
  exact ⟨g, hgX, hg, hgτ⟩

theorem permAut_mem_aPermutationFull (τ : Equiv.Perm (Fin n)) :
    SpCoord.permAut (p := p) τ ∈ aPermutationFull n p := by
  refine Equiv.Perm.swap_induction_on (motive := fun τ : Equiv.Perm (Fin n) =>
    SpCoord.permAut (p := p) τ ∈ aPermutationFull n p) τ ?_ ?_
  · change ggSpSigned_permAutHom p n 1 ∈ aPermutationFull n p
    rw [map_one]
    exact Subgroup.one_mem _
  · intro τ a b hab hτ
    change ggSpSigned_permAutHom p n (Equiv.swap a b * τ) ∈ aPermutationFull n p
    rw [map_mul]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨a, b, hab, rfl⟩) hτ

theorem exists_mem_conjAut_eq_permAut
    (hA : (ggAutomizer X Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p)
    (τ : Equiv.Perm (Fin n)) :
    ∃ g ∈ X, ∃ hg : g ∈ Subgroup.normalizer (Bs : Set G),
      MulAut.congr eta (ggConjAut Bs hg) = SpCoord.permAut τ := by
  have hmem : SpCoord.permAut (p := p) τ ∈
      (ggAutomizer X Bs).map (MulAut.congr eta).toMonoidHom := by
    rw [hA]
    exact permAut_mem_aPermutationFull τ
  obtain ⟨g, hg, hgX, hgτ⟩ := exists_mem_of_mem_map_congr eta hmem
  exact ⟨g, hgX, hg, hgτ⟩

theorem GGSecFiveBPermUniLFrame.le_sup_map_conj_of_perm
    (hF : GGSecFiveBPermUniLFrame Bs X eta π σ χ) (hK : UnitaryFieldData 2 f K) (hf : 2 ≤ f)
    (hp : p.Prime) (hn : 3 ≤ n) {i0 : Fin n} {τ : Equiv.Perm (Fin n)} (hτ0 : τ i0 ≠ i0) {g : G}
    (hg : g ∈ Subgroup.normalizer (Bs : Set G))
    (hτ : MulAut.congr eta (ggConjAut Bs hg) = SpCoord.permAut τ)
    {M : Subgroup G}
    (hM : ∀ c d : Fin n, c ≠ d → c ≠ i0 → d ≠ i0 → ggBlockComm Bs eta {c, d} ≤ M) :
    X ≤ M ⊔ M.map (MulAut.conj g).toMonoidHom := by
  refine hF.le_of_ggBlockComm_le hK hf hp hn i0 (τ i0) fun c d hcd hne => ?_
  by_cases hc : c = i0
  · have hdτ : d ≠ τ i0 := by
      intro h
      exact hne (by
        rw [hc, Set.pair_eq_pair_iff]
        exact Or.inl ⟨rfl, h⟩)
    have hdi : d ≠ i0 := fun h => hcd (hc.trans h.symm)
    have himg : τ '' ({τ⁻¹ i0, τ⁻¹ d} : Set (Fin n)) = {c, d} := by
      rw [Set.image_pair]
      simp [hc]
    rw [← himg, ← ggBlockComm_map_conj hg hτ]
    refine le_sup_of_le_right (Subgroup.map_mono ?_)
    exact hM (τ⁻¹ i0) (τ⁻¹ d) (τ.symm.injective.ne hdi.symm)
      (by simpa using τ.symm.injective.ne hτ0.symm)
      (by simpa using τ.symm.injective.ne hdτ)
  · by_cases hd : d = i0
    · have hcτ : c ≠ τ i0 := by
        intro h
        exact hne (by rw [h, hd, Set.pair_comm])
      have himg : τ '' ({τ⁻¹ c, τ⁻¹ i0} : Set (Fin n)) = {c, d} := by
        rw [Set.image_pair]
        simp [hd]
      rw [← himg, ← ggBlockComm_map_conj hg hτ]
      refine le_sup_of_le_right (Subgroup.map_mono ?_)
      exact hM (τ⁻¹ c) (τ⁻¹ i0) (τ.symm.injective.ne hc)
        (by simpa using τ.symm.injective.ne hcτ)
        (by simpa using τ.symm.injective.ne hτ0.symm)
    · exact le_sup_of_le_left (hM c d hcd hc hd)

theorem GGSecFiveBPermUniLFrame.le_sup_map_conj
    (hF : GGSecFiveBPermUniLFrame Bs X eta π σ χ) (hK : UnitaryFieldData 2 f K) (hf : 2 ≤ f)
    (hp : p.Prime) (hn : 3 ≤ n) {i0 j0 : Fin n} (hij : i0 ≠ j0) {g : G}
    (hg : g ∈ Subgroup.normalizer (Bs : Set G))
    (hτ : MulAut.congr eta (ggConjAut Bs hg) = SpCoord.permAut (Equiv.swap i0 j0))
    {M : Subgroup G}
    (hM : ∀ c d : Fin n, c ≠ d → c ≠ i0 → d ≠ i0 → ggBlockComm Bs eta {c, d} ≤ M) :
    X ≤ M ⊔ M.map (MulAut.conj g).toMonoidHom :=
  hF.le_sup_map_conj_of_perm hK hf hp hn (i0 := i0) (τ := Equiv.swap i0 j0)
    (by rw [Equiv.swap_apply_left]; exact hij.symm) hg hτ hM

theorem GGSecFiveBPermUniLFrame.sup_map_conj_eq_of_perm
    (hF : GGSecFiveBPermUniLFrame Bs X eta π σ χ) (hK : UnitaryFieldData 2 f K) (hf : 2 ≤ f)
    (hp : p.Prime) (hn : 3 ≤ n) {i0 : Fin n} {τ : Equiv.Perm (Fin n)} (hτ0 : τ i0 ≠ i0) {g : G}
    (hgX : g ∈ X) (hg : g ∈ Subgroup.normalizer (Bs : Set G))
    (hτ : MulAut.congr eta (ggConjAut Bs hg) = SpCoord.permAut τ)
    {M : Subgroup G}
    (hM : ∀ c d : Fin n, c ≠ d → c ≠ i0 → d ≠ i0 → ggBlockComm Bs eta {c, d} ≤ M) :
    M ⊔ M.map (MulAut.conj g).toMonoidHom = X ⊔ M := by
  apply le_antisymm
  · refine sup_le le_sup_right ?_
    calc M.map (MulAut.conj g).toMonoidHom ≤ (X ⊔ M).map (MulAut.conj g).toMonoidHom :=
          Subgroup.map_mono le_sup_right
      _ = X ⊔ M := Subgroup.mem_normalizer_iff_map_conj_eq.mp
          (Subgroup.le_normalizer (Subgroup.mem_sup_left hgX))
  · exact sup_le (hF.le_sup_map_conj_of_perm hK hf hp hn hτ0 hg hτ hM) le_sup_left

theorem GGSecFiveBPermUniLFrame.sup_map_conj_eq
    (hF : GGSecFiveBPermUniLFrame Bs X eta π σ χ) (hK : UnitaryFieldData 2 f K) (hf : 2 ≤ f)
    (hp : p.Prime) (hn : 3 ≤ n) {i0 j0 : Fin n} (hij : i0 ≠ j0) {g : G} (hgX : g ∈ X)
    (hg : g ∈ Subgroup.normalizer (Bs : Set G))
    (hτ : MulAut.congr eta (ggConjAut Bs hg) = SpCoord.permAut (Equiv.swap i0 j0))
    {M : Subgroup G}
    (hM : ∀ c d : Fin n, c ≠ d → c ≠ i0 → d ≠ i0 → ggBlockComm Bs eta {c, d} ≤ M) :
    M ⊔ M.map (MulAut.conj g).toMonoidHom = X ⊔ M :=
  hF.sup_map_conj_eq_of_perm hK hf hp hn (i0 := i0) (τ := Equiv.swap i0 j0)
    (by rw [Equiv.swap_apply_left]; exact hij.symm) hgX hg hτ hM

private theorem ublk_exists_perm_of_mem_aPermutationFull {n p : ℕ}
    {a : MulAut (Fin n → Multiplicative (ZMod p))} (ha : a ∈ aPermutationFull n p) :
    ∃ τ : Equiv.Perm (Fin n), a = SpCoord.permAut τ := by
  induction ha using Subgroup.closure_induction with
  | mem a ha =>
    obtain ⟨i, j, -, rfl⟩ := ha
    exact ⟨Equiv.swap i j, rfl⟩
  | one => exact ⟨1, by ext f k; rfl⟩
  | mul a b _ _ iha ihb =>
    obtain ⟨ρ, rfl⟩ := iha
    obtain ⟨τ, rfl⟩ := ihb
    exact ⟨ρ * τ, by ext f k; rfl⟩
  | inv a _ iha =>
    obtain ⟨ρ, rfl⟩ := iha
    exact ⟨ρ⁻¹, by ext f k; rfl⟩

private theorem ublk_diag_centralizes
    (hF : GGSecFiveBPermUniLFrame Bs X eta π σ χ)
    {t : ↥(unitarySU 2 f K n)} {v : Fin n → K}
    (htm : ((t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = diagonal v) :
    σ t ∈ Subgroup.centralizer (Bs : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  obtain ⟨D, hD, hDm, hconj⟩ := hF.2.2.2 ⟨b, hb⟩
  have ha : LineU.ActsDiagU σ (MulAut.conj b) (fun k => (χ (eta ⟨b, hb⟩ (π k)) : K)) :=
    ⟨D, hD, hDm, fun s => by rw [MulAut.conj_apply, hconj s]⟩
  have hfix : MulAut.conj b (σ t) = σ t := LineU.ActsDiagU.fix_of_diagonal ha t htm
  rw [MulAut.conj_apply] at hfix
  calc b * σ t = (b * σ t * b⁻¹) * b := by group
    _ = σ t * b := by rw [hfix]

private theorem ublk_conjN_mul {D : GL (Fin n) K}
    {hD : D ∈ Subgroup.normalizer (unitarySU 2 f K n : Set (GL (Fin n) K))}
    (x y : ↥(unitarySU 2 f K n)) :
    LineU.conjN D hD (x * y) = LineU.conjN D hD x * LineU.conjN D hD y := by
  apply Subtype.ext
  simp only [LineU.coe_conjN, Subgroup.coe_mul]
  group

private theorem ublk_scalar_mul_comm {z : GL (Fin n) K} {c : K}
    (hz : (z : Matrix (Fin n) (Fin n) K) = diagonal (fun _ => c)) (X : GL (Fin n) K) :
    X * z = z * X := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hz]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  exact mul_comm _ _

private theorem ublk_scalar_conj_eq {z : GL (Fin n) K} {c : K}
    (hz : (z : Matrix (Fin n) (Fin n) K) = diagonal (fun _ => c)) (X : GL (Fin n) K) :
    X * z * X⁻¹ = z := by
  rw [ublk_scalar_mul_comm hz X, mul_assoc, mul_inv_cancel, mul_one]

private theorem ublk_permSUHom_swap_gl (hK : UnitaryFieldData 2 f K) (i j : Fin n) :
    ((CFSG.SeitzReduction.UnitaryPilot.permSUHom hK (Equiv.swap i j) :
        ↥(unitarySU 2 f K n)) : GL (Fin n) K) = permGL (Equiv.swap i j) := by
  apply Units.ext
  rw [CFSG.SeitzReduction.UnitaryPilot.permSUHom_apply,
    CFSG.SeitzReduction.UnitaryPilot.coe_permSU, LineU.coe_permGL_matrix]

private theorem ublk_pow_p_eq_one (z : Multiplicative (ZMod p)) : z ^ p = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one, nsmul_eq_mul, ZMod.natCast_self, zero_mul]

private theorem ublk_diagHom_swap_const {r : Fin n → Kˣ} {k l : Fin n}
    (hn : 3 ≤ n) {c : K}
    (h : (((diagHom n r * permGL (Equiv.swap k l) * (diagHom n r)⁻¹ *
        (permGL (Equiv.swap k l))⁻¹) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = diagonal (fun _ => c)) :
    r k = r l := by
  have h' : diagonal (fun m => (r m : K) * (((r (Equiv.swap k l m))⁻¹ : Kˣ) : K)) =
      diagonal (fun _ => c) := by
    rw [← ublk_diagHom_conj_swap_matrix k l r]
    exact h
  obtain ⟨i, hik, hil⟩ := LineU.exists_not_mem_two hn k l
  have hc : c = 1 := by
    have h1 := congrFun (congrFun h' i) i
    simp only [Matrix.diagonal_apply_eq] at h1
    rw [Equiv.swap_apply_of_ne_of_ne hik hil] at h1
    have h2 : (r i : K) * ((r i : K))⁻¹ = 1 := mul_inv_cancel₀ (Units.ne_zero (r i))
    simpa [h2, Units.val_inv_eq_inv_val] using h1.symm
  have hk : (r k : K) * ((r l : K))⁻¹ = 1 := by
    have h1 := congrFun (congrFun h' k) k
    simp only [Matrix.diagonal_apply_eq] at h1
    rw [Equiv.swap_apply_left, hc] at h1
    simpa [Units.val_inv_eq_inv_val] using h1
  apply Units.ext
  exact (mul_inv_eq_one₀ (Units.ne_zero (r l))).mp hk

theorem GGSecFiveBPermUniLFrame.permSUHom_swap_mem_normalizer [Finite G] {π : Equiv.Perm (Fin n)}
    {σ : ↥(unitarySU 2 f K n) →* G} {χ : Multiplicative (ZMod p) →* Kˣ}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    (hF : GGSecFiveBPermUniLFrame Bs X eta π σ χ) (hK : UnitaryFieldData 2 f K) (hp : p.Prime)
    (hBsC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hA : (ggAutomizer X Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p)
    (hn : 3 ≤ n) (a b : Fin n) :
    ∃ hu : σ (CFSG.SeitzReduction.UnitaryPilot.permSUHom hK (Equiv.swap a b)) ∈
        Subgroup.normalizer (Bs : Set G),
      MulAut.congr eta (ggConjAut Bs hu) = SpCoord.permAut (Equiv.swap (π a) (π b)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set ρ₀ : Equiv.Perm (Fin n) := Equiv.swap a b with hρ₀
  set w : ↥(unitarySU 2 f K n) :=
    CFSG.SeitzReduction.UnitaryPilot.permSUHom hK ρ₀ with hwdef
  have hwP : (w : GL (Fin n) K) = permGL ρ₀ := by
    rw [hwdef]
    exact ublk_permSUHom_swap_gl hK a b
  have hww : σ w * σ w = 1 := by
    have h2 : w * w = 1 := by
      rw [hwdef, ← map_mul, Equiv.swap_mul_self, map_one]
    rw [← map_mul, h2, map_one]
  have hmem : ∀ x ∈ Bs, σ w * x * (σ w)⁻¹ ∈ Bs := by
    intro x hx
    have hcent : σ w * (x : G) * (σ w)⁻¹ ∈ Subgroup.centralizer (Bs : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨Dy, hDy, hDym, hconjy⟩ := hF.2.2.2 ⟨y, hy⟩
      set d : Fin n → Kˣ := fun k => χ (eta ⟨y, hy⟩ (π k)) with hd
      have hDy_eq : Dy = diagHom n d := Units.ext (by rw [hDym, coe_diagHom])
      set t : ↥(unitarySU 2 f K n) := w⁻¹ * LineU.conjN Dy hDy w with ht
      have htmat : ((t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
          diagonal (fun k => (d (ρ₀ k) : K) * (((d⁻¹ : Fin n → Kˣ) k) : K)) := by
        have h1 : (t : GL (Fin n) K) =
            ((permGL ρ₀)⁻¹ * diagHom n d * permGL ρ₀) * (diagHom n d)⁻¹ := by
          rw [ht]
          apply Units.ext
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, LineU.coe_conjN, hwP, hDy_eq]
          group
        rw [h1]
        simp only [Units.val_mul]
        rw [LineU.coe_permGL_inv_matrix, coe_diagHom, LineU.coe_permGL_matrix,
          ← map_inv (diagHom (K := K) n) d, coe_diagHom]
        have hconj : (ρ₀.permMatrix K * diagonal (fun k => (d k : K)) *
            (ρ₀⁻¹).permMatrix K) = diagonal (fun k => (d (ρ₀ k) : K)) := by
          have h := LineU.permMatrix_conj_diag (K := K) (σ := ρ₀⁻¹) (fun k => (d k : K))
          simpa using h
        rw [hconj, Matrix.diagonal_mul_diagonal]
      have htcent : σ t ∈ Subgroup.centralizer (Bs : Set G) :=
        ublk_diag_centralizes hF htmat
      have hyu : (y : G) * σ w * (y : G)⁻¹ = σ w * σ t := by
        have h := hconjy w
        have hwt : LineU.conjN Dy hDy w = w * t := by
          apply Subtype.ext
          rw [ht]
          simp only [LineU.coe_conjN, Subgroup.coe_mul, Subgroup.coe_inv]
          group
        rw [hwt, map_mul] at h
        exact h
      have habel : (⟨y, hy⟩ : ↥Bs) * ⟨x, hx⟩ = ⟨x, hx⟩ * ⟨y, hy⟩ := by
        apply eta.injective
        rw [map_mul, map_mul, mul_comm]
      have hyx : (y : G) * (x : G) * (y : G)⁻¹ = (x : G) := by
        have h := congrArg (fun z : ↥Bs => (z : G)) habel
        simp only [Subgroup.coe_mul] at h
        calc (y : G) * (x : G) * (y : G)⁻¹ = (x : G) * (y : G) * (y : G)⁻¹ := by rw [h]
          _ = (x : G) := by group
      have htx : (x : G) * σ t = σ t * (x : G) :=
        Subgroup.mem_centralizer_iff.mp htcent x hx
      have hgoal : (y : G) * (σ w * (x : G) * (σ w)⁻¹) * (y : G)⁻¹ =
          σ w * (x : G) * (σ w)⁻¹ := by
        calc (y : G) * (σ w * (x : G) * (σ w)⁻¹) * (y : G)⁻¹
            = ((y : G) * σ w * (y : G)⁻¹) * ((y : G) * (x : G) * (y : G)⁻¹) *
                ((y : G) * σ w * (y : G)⁻¹)⁻¹ := by group
          _ = (σ w * σ t) * (x : G) * (σ w * σ t)⁻¹ := by rw [hyu, hyx]
          _ = σ w * (x : G) * (σ w)⁻¹ := by
              rw [show (σ w * σ t) * (x : G) * (σ w * σ t)⁻¹ =
                σ w * (σ t * (x : G) * (σ t)⁻¹) * (σ w)⁻¹ from by group]
              rw [show σ t * (x : G) * (σ t)⁻¹ = (x : G) from by rw [← htx]; group]
      calc (y : G) * (σ w * (x : G) * (σ w)⁻¹)
          = ((y : G) * (σ w * (x : G) * (σ w)⁻¹) * (y : G)⁻¹) * (y : G) := by group
        _ = (σ w * (x : G) * (σ w)⁻¹) * (y : G) := by rw [hgoal]
    have hxp : (⟨x, hx⟩ : ↥Bs) ^ p = 1 := by
      apply eta.injective
      rw [map_pow, map_one]
      funext k
      exact ublk_pow_p_eq_one (eta ⟨x, hx⟩ k)
    have hxpow : (x : G) ^ p = 1 := by
      have h := congrArg (fun z : ↥Bs => (z : G)) hxp
      simpa using h
    have hpow : (σ w * (x : G) * (σ w)⁻¹) ^ p = 1 := by
      calc (σ w * (x : G) * (σ w)⁻¹) ^ p = (MulAut.conj (σ w) (x : G)) ^ p := rfl
        _ = MulAut.conj (σ w) ((x : G) ^ p) :=
            (map_pow (MulAut.conj (σ w)) (x : G) p).symm
        _ = 1 := by rw [hxpow, map_one]
    exact hBsC _ hcent hpow
  have hnorm : σ w ∈ Subgroup.normalizer (Bs : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact hmem x
    · intro hx
      have hz := hmem (σ w * x * (σ w)⁻¹) hx
      have h1 : (σ w)⁻¹ * (σ w)⁻¹ = 1 := by
        rw [← _root_.mul_inv_rev, hww, inv_one]
      have heq : σ w * (σ w * x * (σ w)⁻¹) * (σ w)⁻¹ = x := by
        calc σ w * (σ w * x * (σ w)⁻¹) * (σ w)⁻¹
            = (σ w * σ w) * x * ((σ w)⁻¹ * (σ w)⁻¹) := by group
          _ = x := by rw [hww, h1]; group
      rwa [heq] at hz
  refine ⟨hnorm, ?_⟩
  set ρ : Equiv.Perm (Fin n) := Equiv.swap (π a) (π b) with hρ
  have hρdef : ρ = π * ρ₀ * π⁻¹ := by
    rw [hρ, hρ₀]
    exact Equiv.swap_apply_apply π a b
  have hρπ : ∀ m : Fin n, π (ρ₀ m) = ρ (π m) := by
    intro m
    rw [hρdef]
    simp [Equiv.Perm.mul_apply]
  have hρ2 : ρ * ρ = 1 := by
    rw [hρ]
    exact Equiv.swap_mul_self _ _
  have huX : σ w ∈ X := by
    rw [← hF.1]
    exact ⟨w, rfl⟩
  have hgen : ggConjAut Bs hnorm ∈ ggAutomizer X Bs := ggConjAut_mem_ggAutomizer huX hnorm
  have hmemA : MulAut.congr eta (ggConjAut Bs hnorm) ∈ aPermutationFull n p := by
    rw [← hA]
    exact Subgroup.mem_map.mpr ⟨ggConjAut Bs hnorm, hgen, rfl⟩
  obtain ⟨τ, hτ⟩ := ublk_exists_perm_of_mem_aPermutationFull hmemA
  have hrel : ∀ x : ↥Bs, ∃ lam : Kˣ, ∀ p : Fin n,
      χ (eta (ggConjAut Bs hnorm x) p) = χ (eta x (ρ p)) * lam := by
    intro x
    obtain ⟨D, hD, hDm, hconj⟩ := hF.2.2.2 x
    obtain ⟨D', hD', hD'm, hconj'⟩ := hF.2.2.2 (ggConjAut Bs hnorm x)
    set d : Fin n → Kˣ := fun k => χ (eta x (π k)) with hd
    set d' : Fin n → Kˣ := fun k => χ (eta (ggConjAut Bs hnorm x) (π k)) with hd'
    have hD_eq : D = diagHom n d := Units.ext (by rw [hDm, coe_diagHom])
    have hD'_eq : D' = diagHom n d' := Units.ext (by rw [hD'm, coe_diagHom])
    have hwn : (w : GL (Fin n) K) ∈
        Subgroup.normalizer (unitarySU 2 f K n : Set (GL (Fin n) K)) :=
      Subgroup.le_normalizer w.2
    set A : GL (Fin n) K := (w : GL (Fin n) K) * D * (w : GL (Fin n) K)⁻¹ with hAdef
    have hAn : A ∈ Subgroup.normalizer (unitarySU 2 f K n : Set (GL (Fin n) K)) := by
      rw [hAdef]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hwn hD) (Subgroup.inv_mem _ hwn)
    have hA_diag : A = diagHom n (d ∘ ρ₀) := by
      rw [hAdef, hwP, hD_eq]
      have h := permGL_mul_diagHom_mul_inv (K := K) ρ₀ d
      have hs : ρ₀.symm = ρ₀ := by rw [hρ₀, Equiv.symm_swap]
      rwa [hs] at h
    have h1 : ∀ s : ↥(unitarySU 2 f K n),
        σ (LineU.conjN A hAn s) = σ (LineU.conjN D' hD' s) := by
      intro s
      have e1 : LineU.conjN A hAn s =
          w * LineU.conjN D hD (w⁻¹ * s * w) * w⁻¹ := by
        apply Subtype.ext
        simp only [LineU.coe_conjN, Subgroup.coe_mul, Subgroup.coe_inv]
        rw [hAdef, hwP]
        group
      rw [e1, map_mul, map_mul, map_inv]
      have hxconj : (x : G) * σ (w⁻¹ * s * w) * (x : G)⁻¹ =
          σ (LineU.conjN D hD (w⁻¹ * s * w)) := hconj _
      have huconj : σ w * σ (w⁻¹ * s * w) * (σ w)⁻¹ = σ s := by
        have h : σ (w⁻¹ * s * w) = (σ w)⁻¹ * σ s * σ w := by
          rw [map_mul, map_mul, map_inv]
        rw [h]
        group
      have hx' : ((ggConjAut Bs hnorm x : ↥Bs) : G) = σ w * (x : G) * (σ w)⁻¹ :=
        ggConjAut_apply Bs hnorm x
      calc σ w * σ (LineU.conjN D hD (w⁻¹ * s * w)) * (σ w)⁻¹
          = σ w * ((x : G) * σ (w⁻¹ * s * w) * (x : G)⁻¹) * (σ w)⁻¹ := by rw [hxconj]
        _ = (σ w * (x : G) * (σ w)⁻¹) * (σ w * σ (w⁻¹ * s * w) * (σ w)⁻¹) *
              (σ w * (x : G) * (σ w)⁻¹)⁻¹ := by group
        _ = (σ w * (x : G) * (σ w)⁻¹) * σ s * (σ w * (x : G) * (σ w)⁻¹)⁻¹ := by
              rw [huconj]
        _ = ((ggConjAut Bs hnorm x : ↥Bs) : G) * σ s *
              (((ggConjAut Bs hnorm x : ↥Bs)) : G)⁻¹ := by rw [hx']
        _ = σ (LineU.conjN D' hD' s) := hconj' s
    set R : GL (Fin n) K := A⁻¹ * D' with hRdef
    have hRn : R ∈ Subgroup.normalizer (unitarySU 2 f K n : Set (GL (Fin n) K)) := by
      rw [hRdef]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hAn) hD'
    have hAinv : A⁻¹ ∈ Subgroup.normalizer (unitarySU 2 f K n : Set (GL (Fin n) K)) :=
      Subgroup.inv_mem _ hAn
    have hker : ∀ s : ↥(unitarySU 2 f K n),
        σ (LineU.conjN R hRn s * s⁻¹) = 1 := by
      intro s
      set SA : ↥(unitarySU 2 f K n) := LineU.conjN A hAn s with hSA
      set SB : ↥(unitarySU 2 f K n) := LineU.conjN D' hD' s with hSB
      set zU : ↥(unitarySU 2 f K n) := SB * SA⁻¹ with hzU
      have hzσ : σ zU = 1 := by
        rw [hzU, map_mul, map_inv, h1 s, mul_inv_cancel]
      obtain ⟨c, hc⟩ := hF.2.1 zU hzσ
      have hzfix : LineU.conjN A⁻¹ hAinv zU = zU := by
        apply Subtype.ext
        simp only [LineU.coe_conjN, inv_inv]
        simpa using (ublk_scalar_conj_eq hc A⁻¹)
      have hSAfix : LineU.conjN A⁻¹ hAinv SA = s := by
        apply Subtype.ext
        simp only [LineU.coe_conjN, inv_inv, hSA]
        group
      have hSBz : SB = zU * SA := by
        rw [hzU]
        group
      have hR_s : LineU.conjN R hRn s = LineU.conjN A⁻¹ hAinv SB := by
        apply Subtype.ext
        simp only [LineU.coe_conjN, inv_inv, hRdef, hSB]
        group
      have heq : LineU.conjN R hRn s * s⁻¹ = zU := by
        rw [hR_s, hSBz, ublk_conjN_mul, hzfix, hSAfix]
        group
      rw [heq]
      exact hzσ
    set r : Fin n → Kˣ := (d ∘ ρ₀)⁻¹ * d' with hr
    have hRr : R = diagHom n r := by
      rw [hRdef, hA_diag, hD'_eq, ← map_inv (diagHom (K := K) n) (d ∘ ρ₀), ← map_mul, hr]
    have hrconst : ∀ k l : Fin n, k ≠ l → r k = r l := by
      intro k l hkl
      set s : ↥(unitarySU 2 f K n) :=
        CFSG.SeitzReduction.UnitaryPilot.permSUHom hK (Equiv.swap k l) with hs
      have hsgl : (s : GL (Fin n) K) = permGL (Equiv.swap k l) := by
        rw [hs]
        exact ublk_permSUHom_swap_gl hK k l
      obtain ⟨c, hc⟩ := hF.2.1 (LineU.conjN R hRn s * s⁻¹) (hker s)
      have hzGL : ((LineU.conjN R hRn s * s⁻¹ : ↥(unitarySU 2 f K n)) :
          GL (Fin n) K) = diagHom n r * permGL (Equiv.swap k l) * (diagHom n r)⁻¹ *
            (permGL (Equiv.swap k l))⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, LineU.coe_conjN, hRr, hsgl]
      rw [hzGL] at hc
      exact ublk_diagHom_swap_const hn hc
    have hd'eq : d' = (d ∘ ρ₀) * r := by
      have h1 : diagHom n d' = diagHom n ((d ∘ ρ₀) * r) := by
        calc diagHom n d' = D' := hD'_eq.symm
          _ = A * R := by rw [hRdef]; group
          _ = diagHom n (d ∘ ρ₀) * diagHom n r := by rw [hA_diag, hRr]
          _ = diagHom n ((d ∘ ρ₀) * r) := by rw [← map_mul]
      exact diagHom_injective n h1
    let m₀ : Fin n := ⟨0, by omega⟩
    refine ⟨r m₀, fun p => ?_⟩
    obtain ⟨m, rfl⟩ := π.surjective p
    have hm : r m = r m₀ := by
      by_cases h : m = m₀
      · rw [h]
      · exact hrconst m m₀ h
    have h := congrFun hd'eq m
    simp only [Pi.mul_apply, Function.comp_apply] at h
    rw [hm] at h
    simp only [hd, hd'] at h
    rwa [hρπ m] at h
  have hτeq : τ = ρ := by
    apply Equiv.ext
    intro j
    set g₀ : Multiplicative (ZMod p) := Multiplicative.ofAdd (1 : ZMod p) with hg₀def
    have hg₀ne : g₀ ≠ 1 := by
      intro h
      have h1 : (1 : ZMod p) = 0 := by
        have := congrArg Multiplicative.toAdd h
        simp [g₀] at this
      exact one_ne_zero h1
    have hχg₀ : χ g₀ ≠ 1 := by
      intro h
      exact hg₀ne (hF.2.2.1 (by rw [h, map_one]))
    set x : ↥Bs := eta.symm (Pi.mulSingle j g₀) with hxdef
    have hxeta : eta x = Pi.mulSingle j g₀ := MulEquiv.apply_symm_apply eta _
    obtain ⟨lam, hlam⟩ := hrel x
    have hη : ∀ q : Fin n, eta (ggConjAut Bs hnorm x) (τ q) = eta x q :=
      eta_ggConjAut_apply_of_permAut hnorm hτ x
    have hη' : ∀ p : Fin n,
        eta (ggConjAut Bs hnorm x) p = if p = τ j then g₀ else 1 := by
      intro p
      have h1 : eta (ggConjAut Bs hnorm x) p = eta x (τ.symm p) := by
        conv_lhs => rw [← Equiv.apply_symm_apply τ p]
        exact hη (τ.symm p)
      rw [h1, hxeta]
      by_cases hp : p = τ j
      · subst hp
        rw [Equiv.symm_apply_apply, if_pos rfl, Pi.mulSingle_eq_same]
      · rw [if_neg hp]
        have hne : τ.symm p ≠ j := by
          intro h
          exact hp (by rw [← h]; exact (Equiv.apply_symm_apply τ p).symm)
        simp only [Pi.mulSingle_apply, if_neg hne]
    have hρ_apply : ∀ q : Fin n, ρ (ρ q) = q := by
      intro q
      rw [show ρ (ρ q) = (ρ * ρ) q from rfl, hρ2, Equiv.Perm.one_apply]
    have hlam1 : lam = 1 := by
      obtain ⟨p0, hp0τ, hp0ρ⟩ := LineU.exists_not_mem_two hn (τ j) (ρ j)
      have h0 := hlam p0
      rw [hη' p0, if_neg hp0τ, map_one] at h0
      have hρp0 : ρ p0 ≠ j := by
        intro h
        exact hp0ρ (by rw [← hρ_apply p0, h])
      rw [hxeta, Pi.mulSingle_eq_of_ne hρp0, map_one, one_mul] at h0
      exact h0.symm
    by_contra hne
    have h1 := hlam (τ j)
    rw [hη' (τ j), if_pos rfl, hlam1, mul_one] at h1
    have hρτ : ρ (τ j) ≠ j := by
      intro h
      exact hne (by rw [← hρ_apply (τ j), h])
    rw [hxeta, Pi.mulSingle_eq_of_ne hρτ, map_one] at h1
    exact hχg₀ h1
  rw [hτ, hτeq, hρ]

end CFSG.StandardType
