module

public import CFSG.LocalAnalysis.StandardType.GGK0KacOmega
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompAlcoveLangNormal
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.Dihedral.DihedralFusionPrefixes
public import CFSG.HardMathSupport.Solomon.Coordinator.B3FamPC
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerBridge
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompAlcoveClasses
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Assembly
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.PlanesSetup
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerTorus
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.Classical2.TwistedE6Phi3A2Case
public import CFSG.RankThree.PartOne.KE.E7FiveBlock
public import CFSG.RankThree.PartOne.KE.ThreeA1Group
public import CFSG.RankThree.PartOne.KLCE.Sector
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremB
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremC
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.ZJTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GW1965RemarkDGroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29Helpers

public section

namespace CFSG.StandardType.GGK0MarkedKacIface1587

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.CrossChar

private theorem dvd_alcoveValue_sub_dot {r : ℕ} (p : ℕ) (μ γ : Fin r → ℤ) :
    (p : ℤ) ∣ alcoveValue p μ γ - dotProduct γ μ := by
  rw [alcoveValue]
  by_cases h : ∀ j, 0 ≤ γ j
  · rw [if_pos h]
    simp
  · rw [if_neg h]
    exact ⟨1, by ring⟩

private theorem zpow_eq_of_dvd_sub_of_orderOf {L : Type} [Field L] {p : ℕ} {ζ : Lˣ}
    (hζ : orderOf ζ = p) {m n : ℤ} (h : (p : ℤ) ∣ m - n) : ζ ^ m = ζ ^ n := by
  rw [zpow_eq_zpow_iff_modEq, hζ]
  refine Int.modEq_iff_dvd.2 ?_
  have h' : n - m = -(m - n) := by ring
  rw [h']
  exact dvd_neg.2 h

private theorem exists_normal_transport
    {τ : Tag} (K : KacData τ) (hK : K.Facts) {p : ℕ} {μ : Fin τ.rank → ℤ}
    {a : Equiv.Perm (Option (Fin τ.rank))} (hμ : K.IsNormal p μ)
    (hma : ∀ x, Option.elim (a x) (1 : ℤ) K.θ = Option.elim x (1 : ℤ) K.θ) :
    ∃ μ' : Fin τ.rank → ℤ, K.IsNormal p μ' ∧
      ∀ x, alcoveValue p μ' (K.extRoot (a x)) = alcoveValue p μ (K.extRoot x) := by
  classical
  set m : Option (Fin τ.rank) → ℤ := fun x => Option.elim x 1 K.θ with hmdef
  set s : Option (Fin τ.rank) → ℤ := fun x => alcoveValue p μ (K.extRoot x) with hsdef
  set μ' : Fin τ.rank → ℤ := fun j => s (a.symm (some j)) with hμ'def
  have hmark : ∑ x : Option (Fin τ.rank), m x * s x = (p : ℤ) := by
    rw [Fintype.sum_option]
    simp only [hmdef, hsdef, Option.elim_none, Option.elim_some, one_mul,
      K.alcoveValue_extRoot_none hK, K.alcoveValue_extRoot_some]
    rw [dotProduct]
    ring
  have hcomp : (∑ x : Option (Fin τ.rank), m x * s (a.symm x)) = ∑ x, m x * s x := by
    rw [← Equiv.sum_comp a (fun x => m x * s (a.symm x))]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Equiv.symm_apply_apply]
    exact congrArg (fun y => y * s x) (hma x)
  have hsplit : (∑ x : Option (Fin τ.rank), m x * s (a.symm x))
      = s (a.symm none) + ∑ k : Fin τ.rank, K.θ k * s (a.symm (some k)) := by
    rw [Fintype.sum_option]
    simp [hmdef, one_mul]
  have hA : (∑ k : Fin τ.rank, K.θ k * s (a.symm (some k)))
      = (p : ℤ) - s (a.symm none) := by
    have h1 := hcomp
    rw [hmark] at h1
    linarith
  have hdot : dotProduct K.θ μ' = (p : ℤ) - s (a.symm none) := by
    rw [dotProduct, hμ'def]
    simpa using hA
  have ha : ∀ x, alcoveValue p μ' (K.extRoot (a x)) = s x := by
    intro x
    cases hx : a x with
    | none =>
      have hx' : a.symm none = x := by rw [← hx, Equiv.symm_apply_apply]
      rw [K.alcoveValue_extRoot_none hK, hdot, hx']
      ring
    | some k =>
      have hx' : a.symm (some k) = x := by rw [← hx, Equiv.symm_apply_apply]
      rw [K.alcoveValue_extRoot_some, hμ'def]
      change s (a.symm (some k)) = s x
      rw [hx']
  refine ⟨μ', ⟨?_, ?_⟩, fun x => ha x⟩
  · intro j
    rw [hμ'def, hsdef]
    exact K.alcoveValue_nonneg hK hμ (K.isRoot_extRoot (a.symm (some j)))
  · rw [hdot]
    have h0 : 0 ≤ s (a.symm none) := by
      rw [hsdef]
      exact K.alcoveValue_nonneg hK hμ (K.isRoot_extRoot (a.symm none))
    linarith

private theorem rootChar_transport
    {τ : Tag} (K : KacData τ) {L : Type} [Field L] {p : ℕ} {ζ : Lˣ}
    (hζ : orderOf ζ = p) {μ μ' : Fin τ.rank → ℤ} {v : WeylGroup τ}
    {a : Equiv.Perm (Option (Fin τ.rank))}
    (ha : ∀ x, alcoveValue p μ' (K.extRoot (a x)) = alcoveValue p μ (K.extRoot x))
    (hv : ∀ x, v • K.extRoot x = K.extRoot (a x)) :
    ∀ lam : Fin τ.rank → ℤ,
      rootChar (fun i => ζ ^ μ' i) (v • lam) = rootChar (fun i => ζ ^ μ i) lam := by
  intro lam
  rw [KacData.rootChar_eq_zpow, KacData.rootChar_eq_zpow]
  refine zpow_eq_of_dvd_sub_of_orderOf hζ ?_
  have hvlam : v • lam = ∑ k : Fin τ.rank, lam k • K.extRoot (a (some k)) := by
    have h1 : lam = ∑ k : Fin τ.rank, lam k • (Pi.single k 1 : Fin τ.rank → ℤ) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [h1]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_comm]
    rw [show (Pi.single k 1 : Fin τ.rank → ℤ) = K.extRoot (some k) from rfl, hv (some k)]
  have hdot1 : dotProduct (v • lam) μ'
      = ∑ k : Fin τ.rank, lam k * dotProduct (K.extRoot (a (some k))) μ' := by
    rw [hvlam]
    simp only [sum_dotProduct, smul_dotProduct, smul_eq_mul]
  have hdot2 : dotProduct lam μ
      = ∑ k : Fin τ.rank, lam k * dotProduct (K.extRoot (some k)) μ := by
    rw [dotProduct]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show K.extRoot (some k) = (Pi.single k 1 : Fin τ.rank → ℤ) from rfl,
      single_dotProduct, one_mul]
  have hterm : ∀ k : Fin τ.rank,
      (p : ℤ) ∣ dotProduct (K.extRoot (a (some k))) μ' -
        dotProduct (K.extRoot (some k)) μ := by
    intro k
    set A := alcoveValue p μ' (K.extRoot (a (some k))) with hAdef
    set B := dotProduct (K.extRoot (a (some k))) μ' with hBdef
    set C := alcoveValue p μ (K.extRoot (some k)) with hCdef
    set D := dotProduct (K.extRoot (some k)) μ with hDdef
    have h1 : (p : ℤ) ∣ A - B := dvd_alcoveValue_sub_dot (p := p) (μ := μ') _
    have h2 : (p : ℤ) ∣ C - D := dvd_alcoveValue_sub_dot (p := p) (μ := μ) _
    have h3 : A = C := ha (some k)
    have hd : (p : ℤ) ∣ -(A - B) + (C - D) + (A - C) :=
      dvd_add (dvd_add (dvd_neg.2 h1) h2) (by rw [h3, sub_self]; exact dvd_zero _)
    have hBD : B - D = -(A - B) + (C - D) + (A - C) := by ring
    rw [hBD]
    exact hd
  have hsumdvd : (p : ℤ) ∣ ∑ k : Fin τ.rank,
      lam k * (dotProduct (K.extRoot (a (some k))) μ' -
        dotProduct (K.extRoot (some k)) μ) :=
    Finset.dvd_sum fun k _ => Dvd.dvd.mul_left (hterm k) (lam k)
  have hdiff : dotProduct (v • lam) μ' - dotProduct lam μ
      = ∑ k : Fin τ.rank,
          lam k * (dotProduct (K.extRoot (a (some k))) μ' -
            dotProduct (K.extRoot (some k)) μ) := by
    rw [hdot1, hdot2, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rwa [hdiff]
private theorem smul_perm_extRoot {τ : Tag} (K : KacData τ) (θ : WeylGroup τ ≃* WeylGroup τ)
    {f : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)} (hf : ∀ v γ, θ v • f γ = f (v • γ))
    {v w : WeylGroup τ} {a σ : Equiv.Perm (Option (Fin τ.rank))} {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) (hσ : ∀ x, ε • (w • f (K.extRoot x)) = K.extRoot (σ x))
    (hv : ∀ x, v • K.extRoot x = K.extRoot (a x)) :
    ∀ x, ε • ((v * w * (θ v)⁻¹) • f (K.extRoot x)) = K.extRoot ((a * σ * a⁻¹) x) := by
  have hvinv : ∀ x, v⁻¹ • K.extRoot x = K.extRoot (a.symm x) := by
    intro x
    have h := hv (a.symm x)
    rw [Equiv.apply_symm_apply] at h
    rw [← h, inv_smul_smul]
  have hmain : ∀ x, (v * w * (θ v)⁻¹) • f (K.extRoot x) =
      v • (w • f (K.extRoot (a.symm x))) := by
    intro x
    rw [mul_smul, mul_smul, ← map_inv, hf, hvinv]
  intro x
  rcases hε with rfl | rfl
  · rw [hmain, smul_comm, hσ, hv]
    rfl
  · rw [hmain, smul_comm, hσ, hv]
    rfl

private theorem alcoveValue_perm_stable {τ : Tag} (K : KacData τ) {p : ℕ}
    {μ μ' : Fin τ.rank → ℤ} {a σ : Equiv.Perm (Option (Fin τ.rank))}
    (ha : ∀ x, alcoveValue p μ' (K.extRoot (a x)) = alcoveValue p μ (K.extRoot x))
    (hσv : ∀ x, alcoveValue p μ (K.extRoot (σ x)) = alcoveValue p μ (K.extRoot x)) :
    ∀ x, alcoveValue p μ' (K.extRoot ((a * σ * a⁻¹) x)) = alcoveValue p μ' (K.extRoot x) := by
  intro x
  have h1 := ha (σ (a.symm x))
  have h2 := hσv (a.symm x)
  have h3 := ha (a.symm x)
  rw [Equiv.apply_symm_apply] at h3
  calc alcoveValue p μ' (K.extRoot ((a * σ * a⁻¹) x))
      = alcoveValue p μ' (K.extRoot (a (σ (a.symm x)))) := rfl
    _ = alcoveValue p μ (K.extRoot (σ (a.symm x))) := h1
    _ = alcoveValue p μ (K.extRoot (a.symm x)) := h2
    _ = alcoveValue p μ' (K.extRoot x) := h3.symm

theorem k0_lang_normal_transport_of
    {τ : Tag} (K : KacData τ) (hK : K.Facts)
    {L : Type} [Field L] [CharP L 2] {p : ℕ} (hp : p.Prime)
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {ζ : Lˣ} (hζ : orderOf ζ = p)
    (F : ModGL τ L →* ModGL τ L) (θ : WeylGroup τ ≃* WeylGroup τ)
    (f : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))
    (hF : ∀ v, F (canonicalRep (coxeterSystem τ) L v) = canonicalRep (coxeterSystem τ) L (θ v))
    (hf : ∀ v γ, θ v • f γ = f (v • γ))
    {u g : ModGL τ L} {μ : Fin τ.rank → ℤ} {w : WeylGroup τ}
    {σ : Equiv.Perm (Option (Fin τ.rank))}
    (hg : g ∈ adjointGroup τ L) (hμ : K.IsNormal p μ)
    (hgu : g⁻¹ * u * g = rootDiagUnit τ (fun i => ζ ^ μ i))
    (hgw : g⁻¹ * F g = canonicalRep (coxeterSystem τ) L w)
    (hσ : ∀ x, ε • (w • f (K.extRoot x)) = K.extRoot (σ x))
    (hσv : ∀ x, alcoveValue p μ (K.extRoot (σ x)) = alcoveValue p μ (K.extRoot x))
    {v : WeylGroup τ} {a : Equiv.Perm (Option (Fin τ.rank))}
    (hv : ∀ x, v • K.extRoot x = K.extRoot (a x))
    (hma : ∀ x, Option.elim (a x) (1 : ℤ) K.θ = Option.elim x (1 : ℤ) K.θ) :
    ∃ g' ∈ adjointGroup τ L, ∃ μ' : Fin τ.rank → ℤ, K.IsNormal p μ' ∧
      (∀ x, alcoveValue p μ' (K.extRoot (a x)) = alcoveValue p μ (K.extRoot x)) ∧
      g'⁻¹ * u * g' = rootDiagUnit τ (fun i => ζ ^ μ' i) ∧
      g'⁻¹ * F g' = canonicalRep (coxeterSystem τ) L (v * w * (θ v)⁻¹) ∧
      (∀ x, ε • ((v * w * (θ v)⁻¹) • f (K.extRoot x)) = K.extRoot ((a * σ * a⁻¹) x)) ∧
      ∀ x, alcoveValue p μ' (K.extRoot ((a * σ * a⁻¹) x)) = alcoveValue p μ' (K.extRoot x) := by
  classical
  have _hp : 0 < p := hp.pos
  obtain ⟨μ', hμ', ha⟩ := exists_normal_transport K hK hμ hma
  set nv : ModGL τ L := canonicalRep (coxeterSystem τ) L v with hnvdef
  have hmem : g * nv⁻¹ ∈ adjointGroup τ L :=
    mul_mem hg (inv_mem (canonicalRep_mem_adjointGroup (coxeterSystem τ) L v))
  have hchar : ∀ lam : Fin τ.rank → ℤ,
      rootChar (fun i => ζ ^ μ' i) (v • lam) = rootChar (fun i => ζ ^ μ i) lam :=
    rootChar_transport K hζ ha hv
  have hconj : rootDiagUnit τ (fun i => ζ ^ μ' i) =
      canonicalRep (coxeterSystem τ) L v * rootDiagUnit τ (fun i => ζ ^ μ i) *
        (canonicalRep (coxeterSystem τ) L v)⁻¹ :=
    (rootDiagUnit_eq_conj_canonicalRep_iff (fun i => ζ ^ μ' i) (fun i => ζ ^ μ i) v).2 hchar
  refine ⟨g * nv⁻¹, hmem, μ', hμ', ha, ?_, ?_, ?_, ?_⟩
  · calc (g * nv⁻¹)⁻¹ * u * (g * nv⁻¹) = nv * (g⁻¹ * u * g) * nv⁻¹ := by group
      _ = nv * rootDiagUnit τ (fun i => ζ ^ μ i) * nv⁻¹ := by rw [hgu]
      _ = rootDiagUnit τ (fun i => ζ ^ μ' i) := hconj.symm
  · have hFr' : F (g * nv⁻¹) = F g * (canonicalRep (coxeterSystem τ) L (θ v))⁻¹ := by
      rw [map_mul, map_inv, hnvdef, hF]
    rw [hFr']
    calc (g * nv⁻¹)⁻¹ * (F g * (canonicalRep (coxeterSystem τ) L (θ v))⁻¹)
        = nv * (g⁻¹ * F g) * (canonicalRep (coxeterSystem τ) L (θ v))⁻¹ := by group
      _ = nv * canonicalRep (coxeterSystem τ) L w *
          (canonicalRep (coxeterSystem τ) L (θ v))⁻¹ := by rw [hgw]
      _ = canonicalRep (coxeterSystem τ) L (v * w * (θ v)⁻¹) := by
        rw [hnvdef,
          ← CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_mul_of_charTwo v w,
          CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_inv_of_charTwo (θ v),
          ← CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_mul_of_charTwo (v * w) (θ v)⁻¹]
  · exact smul_perm_extRoot K θ hf hε hσ hv
  · exact alcoveValue_perm_stable K ha hσv

private theorem linearCombination_extRoot_apply {τ : Tag} (K : KacData τ)
    (x : Fin (τ.rank + 1) → ℤ) (j : Fin τ.rank) :
    (Fintype.linearCombination ℤ (fun i : Fin (τ.rank + 1) => K.extRoot (idxNode i.val))) x j =
      -(x 0 * K.θ j) + x (Fin.succ j) := by
  classical
  rw [Fintype.linearCombination_apply, Finset.sum_apply, Fin.sum_univ_succ]
  simp only [Pi.smul_apply, smul_eq_mul]
  change x 0 * K.extRoot (idxNode (0 : Fin (τ.rank + 1)).val) j +
      ∑ i : Fin τ.rank, x i.succ * K.extRoot (idxNode (Fin.succ i).val) j =
    -(x 0 * K.θ j) + x (Fin.succ j)
  have h0 : K.extRoot (idxNode (0 : Fin (τ.rank + 1)).val) = -K.θ := by
    simp [idxNode, KacData.extRoot]
  have hs : ∀ i : Fin τ.rank,
      K.extRoot (idxNode (Fin.succ i).val) = (Pi.single i 1 : Fin τ.rank → ℤ) := by
    intro i
    have hidx : idxNode (r := τ.rank) (i.val + 1) = some i := by
      have h := idxNode_nodeIdx (some i)
      rwa [show nodeIdx (some i) = i.val + 1 from rfl] at h
    rw [Fin.val_succ, hidx]
    rfl
  rw [h0]
  have hsum : (∑ i : Fin τ.rank, x i.succ * K.extRoot (idxNode (Fin.succ i).val) j)
      = ∑ i : Fin τ.rank, x i.succ * (Pi.single i 1 : Fin τ.rank → ℤ) j := by
    exact Finset.sum_congr rfl fun i _ => by rw [hs i]
  rw [hsum, Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    rw [Pi.single_eq_of_ne (Ne.symm hb), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h

private theorem linearCombination_extRoot_ker {τ : Tag} (K : KacData τ) (marks : List ℕ)
    (hm0 : marks.getD 0 0 = 1)
    (hmθ : ∀ j : Fin τ.rank, K.θ j = ((marks.getD (j.val + 1) 0 : ℕ) : ℤ)) :
    (Fintype.linearCombination ℤ (fun i : Fin (τ.rank + 1) => K.extRoot (idxNode i.val))).ker =
      Submodule.span ℤ
        ({fun i : Fin (τ.rank + 1) => ((marks.getD i.val 0 : ℕ) : ℤ)} :
          Set (Fin (τ.rank + 1) → ℤ)) := by
  classical
  set L : (Fin (τ.rank + 1) → ℤ) →ₗ[ℤ] (Fin τ.rank → ℤ) :=
    Fintype.linearCombination ℤ (fun i : Fin (τ.rank + 1) => K.extRoot (idxNode i.val))
    with hLdef
  have hnode (x : Fin (τ.rank + 1) → ℤ) (j : Fin τ.rank) :
      L x j = -(x 0 * K.θ j) + x (Fin.succ j) := by
    rw [hLdef]
    exact linearCombination_extRoot_apply K x j
  have hmarks0 : ((marks.getD (0 : Fin (τ.rank + 1)).val 0 : ℕ) : ℤ) = 1 := by
    simp only [Fin.val_zero]
    rw [hm0]
    norm_num
  have hmarkss : ∀ j : Fin τ.rank,
      ((marks.getD (Fin.succ j).val 0 : ℕ) : ℤ) = K.θ j := by
    intro j
    simp only [Fin.val_succ]
    exact (hmθ j).symm
  have hker_le : L.ker ≤ Submodule.span ℤ
      ({fun i : Fin (τ.rank + 1) => ((marks.getD i.val 0 : ℕ) : ℤ)} : Set _) := by
    intro x hx
    rw [LinearMap.mem_ker] at hx
    have hx0 : x = x 0 • (fun i : Fin (τ.rank + 1) => ((marks.getD i.val 0 : ℕ) : ℤ)) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · rw [Pi.smul_apply, smul_eq_mul, hmarks0]
        ring
      · rw [Pi.smul_apply, smul_eq_mul, hmarkss j]
        have hj := congrFun hx j
        rw [hnode, Pi.zero_apply] at hj
        linarith
    rw [hx0]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  have hspan_le : Submodule.span ℤ
      ({fun i : Fin (τ.rank + 1) => ((marks.getD i.val 0 : ℕ) : ℤ)} : Set _) ≤ L.ker := by
    refine Submodule.span_le.2 ?_
    rintro v hv
    rw [Set.mem_singleton_iff] at hv
    subst v
    change L (fun i : Fin (τ.rank + 1) => ((marks.getD i.val 0 : ℕ) : ℤ)) = 0
    funext j
    rw [hnode, Pi.zero_apply]
    change -(((marks.getD (0 : Fin (τ.rank + 1)).val 0 : ℕ) : ℤ) * K.θ j) +
      ((marks.getD (Fin.succ j).val 0 : ℕ) : ℤ) = 0
    rw [hmarks0, hmarkss j]
    ring
  exact le_antisymm hker_le hspan_le

private theorem exists_nodeMap_aux {τ : Tag} (K : KacData τ) (marks : List ℕ)
    (_hlen : marks.length = τ.rank + 1) (hm0 : marks.getD 0 0 = 1)
    (hmθ : ∀ j : Fin τ.rank, K.θ j = ((marks.getD (j.val + 1) 0 : ℕ) : ℤ)) :
    ∃ nodeMap : (Fin (τ.rank + 1) → ℤ) →ₗ[ℤ] (Fin τ.rank → ℤ),
      (∀ i : Fin (τ.rank + 1), nodeMap (Pi.single i 1) = K.extRoot (idxNode i.val)) ∧
      Function.Surjective nodeMap ∧
      nodeMap.ker = Submodule.span ℤ
        ({fun i : Fin (τ.rank + 1) => ((marks.getD i.val 0 : ℕ) : ℤ)} :
          Set (Fin (τ.rank + 1) → ℤ)) := by
  classical
  set ext : Fin (τ.rank + 1) → (Fin τ.rank → ℤ) := fun i => K.extRoot (idxNode i.val)
    with hextdef
  set nodeMap : (Fin (τ.rank + 1) → ℤ) →ₗ[ℤ] (Fin τ.rank → ℤ) :=
    Fintype.linearCombination ℤ ext with hnodeMapdef
  have hsingle : ∀ i, nodeMap (Pi.single i 1) = K.extRoot (idxNode i.val) := by
    intro i
    rw [hnodeMapdef, Fintype.linearCombination_apply_single]
    rw [hextdef]
    simp
  have hsurj : Function.Surjective nodeMap := by
    intro y
    refine ⟨Fin.cons 0 y, ?_⟩
    funext j
    rw [hnodeMapdef, hextdef, linearCombination_extRoot_apply K]
    simp
  refine ⟨nodeMap, hsingle, hsurj, ?_⟩
  rw [hnodeMapdef, hextdef]
  exact linearCombination_extRoot_ker K marks hm0 hmθ

theorem exists_k0NodeMap
    (T : GGKacType) :
    ∃ nodeMap : (Fin (k0DiagOf T).marks.length → ℤ) →ₗ[ℤ] (Fin (absTag T).rank → ℤ),
      (∀ i : Fin (k0DiagOf T).marks.length,
        nodeMap (Pi.single i 1) = (k0Kac T).extRoot (idxNode i.val)) ∧
      Function.Surjective nodeMap ∧
      nodeMap.ker = Submodule.span ℤ
        ({fun i : Fin (k0DiagOf T).marks.length => ((k0DiagOf T).marks.getD i.val 0 : ℤ)} :
          Set (Fin (k0DiagOf T).marks.length → ℤ)) := by
  cases T
  · exact exists_nodeMap_aux (k0Kac .E6) (k0DiagOf .E6).marks
      (k0Kac_marks_length .E6) (by decide) (k0Kac_θ .E6)
  · exact exists_nodeMap_aux (k0Kac .E7) (k0DiagOf .E7).marks
      (k0Kac_marks_length .E7) (by decide) (k0Kac_θ .E7)
  · exact exists_nodeMap_aux (k0Kac .E8) (k0DiagOf .E8).marks
      (k0Kac_marks_length .E8) (by decide) (k0Kac_θ .E8)
  · exact exists_nodeMap_aux (k0Kac .F4) (k0DiagOf .F4).marks
      (k0Kac_marks_length .F4) (by decide) (k0Kac_θ .F4)

private theorem alcoveValue_eq_zero_iff_isZ
    {τ : Tag} (K : KacData τ) (hK : K.Facts)
    {p : ℕ} {μ : Fin τ.rank → ℤ} (_hμ : K.IsNormal p μ) {x : Option (Fin τ.rank)} :
    alcoveValue p μ (K.extRoot x) = 0 ↔ K.IsZ p μ x := by
  cases x with
  | none =>
    rw [K.alcoveValue_extRoot_none hK]
    change (p : ℤ) - dotProduct K.θ μ = 0 ↔ dotProduct K.θ μ = (p : ℤ)
    constructor <;> intro h <;> linarith
  | some j =>
    rw [K.alcoveValue_extRoot_some]
    change μ j = 0 ↔ μ j = 0
    exact Iff.rfl

theorem span_kernelRoots_eq_zero_nodes
    (T : GGKacType) {L : Type} [Field L] {p : ℕ} (hp : p.Prime) {ζ : Lˣ} (hζ : orderOf ζ = p)
    {μ : Fin (absTag T).rank → ℤ} (hμ : (k0Kac T).IsNormal p μ) :
    Submodule.span ℤ (kernelRoots (rootCharHom (fun j => ζ ^ μ j))) =
      Submodule.span ℤ {γ | ∃ i : Fin (k0DiagOf T).marks.length,
        alcoveValue p μ ((k0Kac T).extRoot (idxNode i.val)) = 0 ∧
          γ = (k0Kac T).extRoot (idxNode i.val)} := by
  classical
  have hK : (k0Kac T).Facts := k0Kac_facts T
  have hχ : ∀ γ : Fin (absTag T).rank → ℤ, IsRoot (absTag T) γ →
      (rootCharHom (fun j => ζ ^ μ j) (Multiplicative.ofAdd γ) = 1 ↔
        (p : ℤ) ∣ dotProduct γ μ) := by
    intro γ _
    change rootChar (fun j => ζ ^ μ j) γ = 1 ↔ (p : ℤ) ∣ dotProduct γ μ
    rw [KacData.rootChar_eq_zpow ζ μ γ, ← orderOf_dvd_iff_zpow_eq_one, hζ]
  let S : Set (Fin (absTag T).rank → ℤ) := {γ | ∃ i : Fin (k0DiagOf T).marks.length,
    alcoveValue p μ ((k0Kac T).extRoot (idxNode i.val)) = 0 ∧
      γ = (k0Kac T).extRoot (idxNode i.val)}
  have hzero : ∀ x : Option (Fin (absTag T).rank),
      alcoveValue p μ ((k0Kac T).extRoot x) = 0 ↔ (k0Kac T).IsZ p μ x :=
    fun x => alcoveValue_eq_zero_iff_isZ (k0Kac T) hK hμ
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro γ hγ
    obtain ⟨hγroot, hγ1⟩ := hγ
    have hdvd : (p : ℤ) ∣ dotProduct γ μ := (hχ γ hγroot).1 hγ1
    obtain ⟨n, hnZ, hγn⟩ := (k0Kac T).exists_combo_of_dvd hK hp.pos hμ hγroot hdvd
    have hcombo : (k0Kac T).combo n ∈ Submodule.span ℤ S := by
      rw [KacData.combo]
      refine Submodule.sum_mem _ ?_
      intro x _
      by_cases hx : n x = 0
      · rw [hx, Nat.cast_zero, zero_smul]
        exact Submodule.zero_mem _
      · refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
        refine ⟨⟨nodeIdx x, ?_⟩, ?_, ?_⟩
        · rw [k0Kac_marks_length T]
          exact nodeIdx_lt x
        · rw [idxNode_nodeIdx]
          exact (hzero x).2 (hnZ x hx)
        · rw [idxNode_nodeIdx]
    rcases hγn with h | h
    · rw [h]
      exact hcombo
    · rw [h]
      exact Submodule.neg_mem _ hcombo
  · refine Submodule.span_le.2 ?_
    rintro γ ⟨i, hzeroi, rfl⟩
    refine Submodule.subset_span ?_
    refine ⟨(k0Kac T).isRoot_extRoot _, ?_⟩
    have hdvd : (p : ℤ) ∣ dotProduct ((k0Kac T).extRoot (idxNode i.val)) μ := by
      have h1 := dvd_alcoveValue_sub_dot (p := p) (μ := μ)
        ((k0Kac T).extRoot (idxNode i.val))
      rw [hzeroi] at h1
      rw [zero_sub, dvd_neg] at h1
      exact h1
    exact (hχ _ ((k0Kac T).isRoot_extRoot _)).2 hdvd

end CFSG.StandardType.GGK0MarkedKacIface1587

end
