module
public import CFSG.GroupTheory.PerfectCentralQuotient
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FQMat
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AMModel
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.GGNbrCenterPCyclic
public import CFSG.LocalAnalysis.StandardType.GGNbrCenterPCyclicHolds
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenCore
public import CFSG.LocalAnalysis.StandardType.GGAutomizerAbelianMatrix
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeBoundGenKernel

public import CFSG.LocalAnalysis.StandardType.GGTypeANbrTableBPermAut
public import CFSG.LocalAnalysis.StandardType.GGTypeAFarActsVec
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenOver
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBTransport
public import CFSG.LocalAnalysis.StandardType.GGTableBBstar
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerTypeADvdModel
public import CFSG.LocalAnalysis.StandardType.GGL45TALinRk
public import CFSG.RankThree.PartOne.KC.CommonEigenbasis
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrTableBRefl
public import CFSG.LocalAnalysis.StandardType.GGResILineInputs
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaCard
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeACover
public import CFSG.LocalAnalysis.StandardType.GGResLeaf
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATorus
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrTableBPSL
public import CFSG.LocalAnalysis.StandardType.GGResJLineA3
public import CFSG.LocalAnalysis.StandardType.GGResJLineBCGamma
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
public import CFSG.LocalAnalysis.ComponentInitial.LinearModelOuterTwoPart
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ADefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ALinDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AUniDefs

public section
namespace CFSG.StandardType.ResJCubicBlock

open CFSG.StandardType
open CFSG.StandardType.TypeANbrDvd
open CFSG.Assembly
open CFSG.Open
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.CatalogueBHigherLinearAction
open Matrix
open Module Module.End

private lemma ggActsDiag_of_actsDiag
    {d : ℕ} {K : Type} [Field K] [CharP K 2]
    {L' : Type} [Group L'] {φ' : Matrix.SpecialLinearGroup (Fin d) K →* L'}
    {X : Type*} [Group X] {j : L' →* X} {a : MulAut L'} {b : X} {t : Fin d → K}
    (ht : TypeANbrDvd.ActsDiag φ' a t)
    (hb : ∀ s, j (a (φ' s)) = b * j (φ' s) * b⁻¹) :
    GGActsDiag (j.comp φ') b := by
  obtain ⟨D, hD, haD⟩ := ht
  let h : Fin d → Kˣ := fun k =>
    Units.mk0 (t k) (TypeANbrDvd.ActsDiag.ne_zero ⟨D, hD, haD⟩ k)
  have hDg : D = ggDiagUnit h := by
    apply Units.ext
    rw [hD]
    rfl
  refine ⟨h, fun s => ?_⟩
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, ← hb s, haD s, hDg]
  rfl

theorem permSL_mem_normalizer_Bs
    {n p : ℕ} {K : Type} [Field K] [CharP K 2]
    {G : Type} [Group G] {J Bs : Subgroup G}
    (hBJ : Bs ≤ Subgroup.normalizer (J : Set G))
    (φ : Matrix.SpecialLinearGroup (Fin (n+1)) K →* J)
    (hker : ∀ g, φ g = 1 → g ∈ scalars (n+1) K)
    (hBs : CFSG.Open.IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hdiag : ∀ b : Bs, ∃ t : Fin (n+1) → K,
      TypeANbrDvd.ActsDiag φ (ggGamma J hBJ b) t)
    (π : Equiv.Perm (Fin (n+1))) :
    (φ (TypeA.permSL π⁻¹) : G) ∈ Subgroup.normalizer (Bs : Set G) := by
  classical
  let H : Subgroup G := Bs ⊔ J
  let φH : Matrix.SpecialLinearGroup (Fin (n+1)) K →* H :=
    (Subgroup.inclusion (show J ≤ H from le_sup_right)).comp φ
  let BsH : Subgroup H := Bs.comap H.subtype
  have hBp : ∀ b ∈ BsH, b ^ p = 1 := by
    intro b hb
    have hbG : (b : G) ∈ Bs := hb
    let bB : Bs := ⟨(b : G), hbG⟩
    apply Subtype.ext
    simpa [bB] using hBs.2 (b : G) hb
  have hSCH : ∀ g ∈ Subgroup.centralizer (BsH : Set H), g ^ p = 1 → g ∈ BsH := by
    intro g hg hg3
    have hgC : (g : G) ∈ Subgroup.centralizer (Bs : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      let bH : BsH := ⟨⟨b, (show Bs ≤ H from le_sup_left) hb⟩, hb⟩
      have h := (Subgroup.mem_centralizer_iff.mp hg) bH bH.2
      exact congrArg (fun x : H => (x : G)) h
    have hg3G : (g : G) ^ p = 1 := by
      have h := congrArg (fun x : H => (x : G)) hg3
      simpa using h
    exact hSC (g : G) hgC hg3G
  have hkerH : φH.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (n+1)) K) := by
    intro g hg
    apply scalars_le_center (n := n+1) (K := K)
    apply hker
    have h := congrArg (fun x : H => (x : G)) hg
    simpa [φH] using h
  have hdiagH : ∀ b ∈ BsH, GGActsDiag φH b := by
    intro b hb
    let bB : Bs := ⟨(b : G), hb⟩
    obtain ⟨t, ht⟩ := hdiag bB
    have hb' : ∀ s, (Subgroup.inclusion (show J ≤ H from le_sup_right))
        ((ggGamma J hBJ bB) (φ s)) =
        b * (Subgroup.inclusion (show J ≤ H from le_sup_right)) (φ s) * b⁻¹ := by
      intro s
      apply Subtype.ext
      simpa [bB] using ggGamma_coe J hBJ bB (φ s)
    exact ggActsDiag_of_actsDiag
      (j := Subgroup.inclusion (show J ≤ H from le_sup_right)) ht hb'
  have hmain : (φH (slPerm (show (2 : K) = 0 from CharP.cast_eq_zero K 2) π) : H) ∈
      Subgroup.normalizer (BsH : Set H) :=
    slPerm_mem_normalizer_of_actsDiag
      (show (2 : K) = 0 from CharP.cast_eq_zero K 2) hBp hSCH hkerH hdiagH π
  have hsl : slPerm (show (2 : K) = 0 from CharP.cast_eq_zero K 2) π =
      TypeA.permSL π⁻¹ := by
    apply Subtype.ext
    rw [coe_slPerm, TypeA.coe_permSL, signedPerm_one_eq_permMatrix]
  rw [hsl] at hmain
  have hmap : BsH.map H.subtype = Bs :=
    Subgroup.map_comap_eq_self (f := H.subtype) (H := Bs)
      (by rw [Subgroup.subtype_range]; exact (show Bs ≤ H from le_sup_left))
  have hmem : (φH (TypeA.permSL π⁻¹) : G) ∈
      Subgroup.normalizer ((BsH.map H.subtype : Subgroup G) : Set G) :=
    Subgroup.le_normalizer_map (H := BsH) H.subtype ⟨_, hmain, rfl⟩
  rw [hmap] at hmem
  simpa [φH] using hmem


@[expose] noncomputable def permSLInvHom {n : ℕ} {K : Type} [Field K] [CharP K 2] :
    Equiv.Perm (Fin (n + 1)) →* Matrix.SpecialLinearGroup (Fin (n + 1)) K where
  toFun σ := TypeA.permSL σ⁻¹
  map_one' := by rw [inv_one, NbrInnerWeylA.permSL_one]
  map_mul' σ τ := by
    rw [_root_.mul_inv_rev, NbrInnerWeylA.permSL_mul]

theorem ggLinearModel_fix_mem_centralizer
    {G : Type} [Group G] {K : Type} [Field K] [CharP K 2] {d p : ℕ}
    {Bs X : Subgroup G} (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    {ψ : Matrix.SpecialLinearGroup (Fin d) K →* X}
    (hψ : Function.Surjective ψ)
    (hker : ∀ g, ψ g = 1 → g ∈ scalars d K) (hd : 2 ≤ d)
    (hdiag : ∀ a ∈ (ggGamma X hN).range, ∃ t : Fin d → K, ActsDiag ψ a t)
    (b : Bs) (hb : ∀ φ ∈ ggAutomizer X Bs, φ b = b) :
    (b : G) ∈ Subgroup.centralizer (X : Set G) := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_one_of_ne_zero (by omega : d ≠ 0)
  subst d
  have hdiagB : ∀ z : Bs, ∃ t : Fin (n + 1) → K,
      ActsDiag ψ (ggGamma X hN z) t := fun z => hdiag _ ⟨z, rfl⟩
  obtain ⟨t, ht⟩ := hdiag _ ⟨b, rfl⟩
  apply (ggGamma_eq_one_iff X hN b).mp
  apply ht.eq_one_of_conj_perm_of_two_le hd hψ hker
  intro σ
  let v : X := ψ (TypeA.permSL σ)
  have hvN : (v : G) ∈ Subgroup.normalizer (Bs : Set G) := by
    simpa only [inv_inv] using
      permSL_mem_normalizer_Bs hN ψ hker hBs hSC hdiagB σ⁻¹
  have hvfix : (v : G) * (b : G) * (v : G)⁻¹ = b :=
    congrArg Subtype.val
      (hb (ggConjAut Bs hvN) (ggConjAut_mem_ggAutomizer v.2 hvN))
  have hcomm : (v : G) * (b : G) = (b : G) * (v : G) := by
    have he := congrArg (fun z : G => z * (v : G)) hvfix
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using he
  have hbv : ggGamma X hN b v = v := by
    apply Subtype.ext
    change (b : G) * (v : G) * (b : G)⁻¹ = v
    rw [← hcomm, mul_inv_cancel_right]
  have hcommAut : MulAut.conj v * ggGamma X hN b = ggGamma X hN b * MulAut.conj v := by
    apply MulEquiv.ext
    intro z
    change v * (ggGamma X hN b) z * v⁻¹ = (ggGamma X hN b) (v * z * v⁻¹)
    rw [map_mul, map_mul, map_inv, hbv]
  change MulAut.conj v * ggGamma X hN b * (MulAut.conj v)⁻¹ = ggGamma X hN b
  rw [hcommAut, mul_inv_cancel_right]

@[expose] noncomputable def permAutActual {n : ℕ}
    {G : Type} [Group G] {J Bs : Subgroup G}
    (π : Equiv.Perm (Fin (n + 1)) →* J)
    (hN : ∀ σ, (π σ : G) ∈ Subgroup.normalizer (Bs : Set G)) :
    Equiv.Perm (Fin (n + 1)) →* ggAutomizer J Bs where
  toFun σ := ⟨ggConjAut Bs (hN σ),
    ggConjAut_mem_ggAutomizer (π σ).2 (hN σ)⟩
  map_one' := by
    apply Subtype.ext
    apply MulEquiv.ext
    intro b
    apply Subtype.ext
    rw [ggConjAut_apply, map_one]
    simp
  map_mul' σ τ := by
    apply Subtype.ext
    apply MulEquiv.ext
    intro b
    apply Subtype.ext
    have hπ : (π (σ * τ) : G) = (π σ : G) * (π τ : G) :=
      congrArg (fun x : J => (x : G)) (map_mul π σ τ)
    rw [ggConjAut_apply, Subgroup.coe_mul, MulAut.mul_apply,
      ggConjAut_apply, ggConjAut_apply, hπ]
    group

@[simp] theorem permAutActual_apply {n : ℕ}
    {G : Type} [Group G] {J Bs : Subgroup G}
    (π : Equiv.Perm (Fin (n + 1)) →* J)
    (hN : ∀ σ, (π σ : G) ∈ Subgroup.normalizer (Bs : Set G))
    (σ : Equiv.Perm (Fin (n + 1))) :
    (permAutActual π hN σ : MulAut Bs) = ggConjAut Bs (hN σ) := rfl


theorem factorial_dvd_card_ggAutomizer
    {G : Type} [Group G] [Finite G] {J Bs : Subgroup G}
    {d : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hd : 3 ≤ d) (h3K : 3 ∣ Nat.card K - 1)
    (hBJ : Bs ≤ Subgroup.normalizer (J : Set G))
    (φ : Matrix.SpecialLinearGroup (Fin d) K →* J)
    (hφ : Function.Surjective φ)
    (hker : ∀ g, φ g = 1 → g ∈ scalars d K)
    (hBs : CFSG.Open.IsElemAbelian 3 Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hdiag : ∀ b : Bs, ∃ t : Fin d → K,
      TypeANbrDvd.ActsDiag φ (ggGamma J hBJ b) t)
    (h9 : 9 ≤ Nat.card (ggGamma J hBJ).range) :
    d.factorial ∣ Nat.card (ggAutomizer J Bs) := by
  classical
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  let π : Equiv.Perm (Fin (n + 1)) →* J := φ.comp (permSLInvHom (n := n) (K := K))
  have hN : ∀ σ, (π σ : G) ∈ Subgroup.normalizer (Bs : Set G) := by
    intro σ
    simpa [π, permSLInvHom] using
      permSL_mem_normalizer_Bs hBJ φ hker hBs hSC hdiag σ
  let A : Subgroup (MulAut J) := (ggGamma J hBJ).range
  have hAe : CFSG.Open.IsElemAbelian 3 A := by
    dsimp [A]
    exact isElemAbelian_range
      (fun a b : ↥Bs => (@IsMulCommutative.is_comm ↥Bs _ hBs.1).comm a b)
      (fun b : ↥Bs => Subtype.ext (by simpa using hBs.2 b b.2))
      (ggGamma J hBJ)
  have hsc : GGTorusSelfCent 3 A := by
    dsimp [A]
    exact ggTorusSelfCent_ggGamma hBJ hSC
  have hdiagA : ∀ a ∈ A, ∃ t : Fin (n + 1) → K,
      TypeANbrDvd.ActsDiag φ a t := by
    rintro a ⟨b, rfl⟩
    exact hdiag b
  have hNA : ∀ σ, NbrInnerWeylA.permConj φ σ ∈
      Subgroup.normalizer (A : Set (MulAut J)) :=
    fun σ => TypeANbrDvd.permConj_mem_normalizer_of_selfCent
      hφ hker hAe.2 hsc hdiagA σ
  have hinjPerm : Function.Injective (TypeANbrDvd.permAut φ A hNA) := by
    by_cases hd4 : 4 ≤ n + 1
    · exact TypeANbrDvd.permAut_injective (p := 3) (by norm_num) (by norm_num)
        h3K hd4 hφ hker hAe hsc hdiagA hNA
    · have hn : n = 2 := by omega
      subst n
      exact TypeANbrDvd.permAut_injective_of_nine_le_card hNA hφ hker
        (fun a => hdiagA a a.2) h9
  let ρ : Equiv.Perm (Fin (n + 1)) →* ggAutomizer J Bs := permAutActual π hN
  have hkerρ : ∀ σ, ρ σ = 1 → σ = 1 := by
    intro σ hσ
    have hc : (ρ σ : MulAut Bs) = 1 := congrArg Subtype.val hσ
    have hover : GGOverGamma hBJ (ρ σ) (TypeANbrDvd.permAut φ A hNA σ) := by
      rw [show (ρ σ : MulAut Bs) = ggConjAut Bs (hN σ) from by
        simp [ρ]]
      rw [TypeANbrDvd.permAut_apply]
      have hNA' : ggConjAut A (hNA σ) =
          ggConjAut A (conj_mem_normalizer_range_ggGamma hBJ (π σ).2 (hN σ)) := by
        apply MulEquiv.ext
        intro x
        apply Subtype.ext
        rfl
      rw [hNA']
      exact ggOverGamma_conjAut (K := J) (hN := hBJ) (π σ).2 (hN σ)
    have ha : TypeANbrDvd.permAut φ A hNA σ = 1 := by
      apply GGOverGamma.eq_one_of_one
      simpa [hc] using hover
    have ha' : TypeANbrDvd.permAut φ A hNA σ =
        TypeANbrDvd.permAut φ A hNA 1 := by
      rw [map_one]
      exact ha
    exact hinjPerm ha' 
  have hinjρ : Function.Injective ρ := by
    intro σ τ hστ
    have h : ρ (σ * τ⁻¹) = 1 := by
      rw [map_mul, map_inv, hστ, mul_inv_cancel]
    have h1 : σ * τ⁻¹ = 1 := hkerρ (σ * τ⁻¹) h
    calc σ = σ * τ⁻¹ * τ := by group
      _ = 1 * τ := by rw [h1]
      _ = τ := one_mul τ
  have hdvd := Subgroup.card_dvd_of_injective ρ hinjρ
  rw [Nat.card_perm, Nat.card_fin] at hdvd
  exact hdvd


theorem d_eq_three_of_card_ggAutomizer_eq_six
    {G : Type} [Group G] [Finite G] {J Bs : Subgroup G}
    {d : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hd : 3 ≤ d) (h3K : 3 ∣ Nat.card K - 1)
    (hBJ : Bs ≤ Subgroup.normalizer (J : Set G))
    (φ : Matrix.SpecialLinearGroup (Fin d) K →* J)
    (hφ : Function.Surjective φ)
    (hker : ∀ g, φ g = 1 → g ∈ scalars d K)
    (hBs : CFSG.Open.IsElemAbelian 3 Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hdiag : ∀ b : Bs, ∃ t : Fin d → K,
      TypeANbrDvd.ActsDiag φ (ggGamma J hBJ b) t)
    (h9 : 9 ≤ Nat.card (ggGamma J hBJ).range)
    (hAut : Nat.card (ggAutomizer J Bs) = 6) :
    d = 3 := by
  have hdvd := factorial_dvd_card_ggAutomizer hd h3K hBJ φ hφ hker hBs hSC hdiag h9
  have hle : d ≤ 3 := by
    by_contra h
    have h4 : 4 ≤ d := by omega
    have h24 : ((4 : ℕ).factorial) ∣ Nat.card (ggAutomizer J Bs) :=
      (Nat.factorial_dvd_factorial h4).trans hdvd
    rw [show ((4 : ℕ).factorial) = 24 by norm_num, hAut] at h24
    norm_num at h24
  omega

theorem exists_conj_diagonal_of_commuting_GL_cube
    {d : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (h3K : 3 ∣ Nat.card K - 1)
    {ι : Type} [Finite ι] (Y : ι → GL (Fin d) K)
    (hcomm : ∀ i j, Commute (Y i) (Y j))
    (hcube : ∀ i, ∃ r : K, r ≠ 0 ∧
      ((Y i : Matrix (Fin d) (Fin d) K) ^ 3 = (r ^ 3) • (1 : Matrix (Fin d) (Fin d) K))) :
    ∃ (A : GL (Fin d) K) (μ : ι → Fin d → K),
      (∀ i, (A : Matrix (Fin d) (Fin d) K) * (Y i : Matrix (Fin d) (Fin d) K) *
        ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal (μ i)) ∧
      (∀ i j, μ i j ≠ 0) := by
  classical
  obtain ⟨ζ, hζ⟩ := TypeA.exists_isPrimitiveRoot (p := 3) (by norm_num) (K := K) h3K
  let r : ι → K := fun i => Classical.choose (hcube i)
  have hr : ∀ i, r i ≠ 0 := fun i => (Classical.choose_spec (hcube i)).1
  let f : ι → Module.End K (Fin d → K) := fun i => Matrix.toLinAlgEquiv' (Y i : Matrix (Fin d) (Fin d) K)
  have hf_comm : ∀ i j, Commute (f i) (f j) := by
    intro i j
    have h2 : ((Y i : Matrix (Fin d) (Fin d) K) * (Y j : Matrix (Fin d) (Fin d) K)) =
        ((Y j : Matrix (Fin d) (Fin d) K) * (Y i : Matrix (Fin d) (Fin d) K)) := by
      simpa using congrArg (fun g : GL (Fin d) K => (g : Matrix (Fin d) (Fin d) K)) (hcomm i j)
    show f i * f j = f j * f i
    simp only [f, ← map_mul, h2]
  have hf_pow : ∀ i, f i ^ 3 = (r i ^ 3) • (1 : Module.End K (Fin d → K)) := by
    intro i
    have hmat : ((Y i : Matrix (Fin d) (Fin d) K) ^ 3 =
        (r i ^ 3) • (1 : Matrix (Fin d) (Fin d) K)) := (Classical.choose_spec (hcube i)).2
    have h1 : f i ^ 3 = Matrix.toLinAlgEquiv' ((Y i : Matrix (Fin d) (Fin d) K) ^ 3) := by
      rw [show f i = Matrix.toLinAlgEquiv' (Y i : Matrix (Fin d) (Fin d) K) from rfl,
        ← map_pow]
    rw [h1, hmat]
    simp
  obtain ⟨b, μ, hb, hμpow, hμne⟩ :=
    CFSG.RankThree.PartOne.exists_basis_common_eigenvectors_of_pow_eq_scalar
      (p := 3) (ζ := ζ) hζ f r hf_comm hr hf_pow
  let e : Fin (finrank K (Fin d → K)) ≃ Fin d := finCongr (Module.finrank_fin_fun K)
  let b' : Basis (Fin d) K (Fin d → K) := b.reindex e
  let μ' : ι → Fin d → K := fun i j => μ i (e.symm j)
  have hb' : ∀ i j, f i (b' j) = μ' i j • b' j := by
    intro i j
    simpa [b', μ', Basis.reindex_apply] using hb i (e.symm j)
  let P : Matrix (Fin d) (Fin d) K := (Pi.basisFun K (Fin d)).toMatrix b'
  have hPi : Invertible P := Basis.invertibleToMatrix (Pi.basisFun K (Fin d)) b'
  let Pu : GL (Fin d) K := unitOfInvertible P
  refine ⟨Pu⁻¹, μ', ?_, ?_⟩
  · intro i
    have hcol : ∀ j : Fin d, (Y i : Matrix (Fin d) (Fin d) K) *ᵥ (b' j) = μ' i j • b' j := by
      intro j
      have := hb' i j
      simpa [f] using this
    have hxP : (Y i : Matrix (Fin d) (Fin d) K) * P = P * diagonal (μ' i) := by
      ext a j
      have h := congrFun (hcol j) a
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
      rw [Matrix.mul_diagonal]
      simp only [P, Matrix.mul_apply, Basis.toMatrix_apply, Pi.basisFun_repr]
      rw [h, mul_comm]
    have h1 : ((Pu⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = ⅟P := rfl
    have h2 : (((Pu⁻¹)⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = P := by
      simp [Pu]
    rw [h1, h2, Matrix.mul_assoc, hxP, ← Matrix.mul_assoc, invOf_mul_self, Matrix.one_mul]
  · intro i j
    exact hμne i (e.symm j)


theorem exists_diagonal_cover_of_GL_family
    {G : Type} [Group G] {J Bs : Subgroup G} [Finite Bs]
    {d : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (h3K : 3 ∣ Nat.card K - 1)
    (hBJ : Bs ≤ Subgroup.normalizer (J : Set G))
    (φ : Matrix.SpecialLinearGroup (Fin d) K →* J)
    (hφ : Function.Surjective φ)
    (hker : ∀ g, φ g = 1 → g ∈ scalars d K)
    (Y : Bs → GL (Fin d) K)
    (hYcomm : ∀ i j, Commute (Y i) (Y j))
    (hYcube : ∀ i, ∃ r : K, r ≠ 0 ∧
      ((Y i : Matrix (Fin d) (Fin d) K) ^ 3 = (r ^ 3) • (1 : Matrix (Fin d) (Fin d) K)))
    (hYact : ∀ i g, (ggGamma J hBJ i) (φ g) =
      φ (slConjugation d K (Y i) g)) :
    ∃ (A : GL (Fin d) K) (μ : Bs → Fin d → K)
        (φ' : Matrix.SpecialLinearGroup (Fin d) K →* J),
      (∀ i, (A : Matrix (Fin d) (Fin d) K) * (Y i : Matrix (Fin d) (Fin d) K) *
        ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal (μ i)) ∧
      Function.Surjective φ' ∧
      (∀ g, φ' g = 1 → g ∈ scalars d K) ∧
      (∀ i, ∃ t : Fin d → K, ActsDiag φ' (ggGamma J hBJ i) t) := by
  classical
  obtain ⟨A, μ, hAconj, hμne⟩ :=
    exists_conj_diagonal_of_commuting_GL_cube h3K Y hYcomm hYcube
  let φ' : Matrix.SpecialLinearGroup (Fin d) K →* J :=
    φ.comp (slConjugation d K A⁻¹).toMonoidHom
  refine ⟨A, μ, φ', hAconj, ?_, ?_, ?_⟩
  · exact hφ.comp (slConjugation d K A⁻¹).surjective
  · intro g hg
    have hg' : slConjugation d K A⁻¹ g ∈ scalars d K := hker _ hg
    obtain ⟨c, hc, hmat⟩ := mem_scalars.mp hg'
    refine mem_scalars.mpr ⟨c, hc, ?_⟩
    have hg_eq : g = slConjugation d K A (slConjugation d K A⁻¹ g) := by
      have h1 : slConjugation d K A * slConjugation d K A⁻¹ = 1 := by
        rw [← map_mul, mul_inv_cancel, map_one]
      change g = (slConjugation d K A * slConjugation d K A⁻¹) g
      rw [h1, MulAut.one_apply]
    rw [hg_eq, slConjugation_matrix, hmat]
    have hAAi : (A : Matrix (Fin d) (Fin d) K) *
        ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hcomm : Commute (Matrix.scalar (Fin d) (c : K)) (A : Matrix (Fin d) (Fin d) K) :=
      Matrix.scalar_commute _ (fun r => Commute.all _ _) _
    rw [← hcomm.eq, Matrix.mul_assoc, hAAi, Matrix.mul_one]
  · intro i
    let t : Fin d → K := μ i
    let D : GL (Fin d) K := GGL45TA.diagGL d (fun j => Units.mk0 (t j) (hμne i j))
    have hD : (D : Matrix (Fin d) (Fin d) K) = diagonal t := by
      rw [GGL45TA.coe_diagGL]
      rfl
    refine ⟨t, D, hD, ?_⟩
    intro g
    have hAconjGL : A * Y i * A⁻¹ = D := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, hD]
      exact hAconj i
    have hY_A : Y i * A⁻¹ = A⁻¹ * D := by
      calc Y i * A⁻¹ = A⁻¹ * (A * Y i * A⁻¹) := by group
        _ = A⁻¹ * D := by rw [hAconjGL]
    calc
      ggGamma J hBJ i (φ' g) =
          φ (slConjugation d K (Y i) (slConjugation d K A⁻¹ g)) := by
        change (ggGamma J hBJ i) (φ (slConjugation d K A⁻¹ g)) = _
        exact hYact i (slConjugation d K A⁻¹ g)
      _ = φ (slConjugation d K (Y i * A⁻¹) g) := by
        rw [map_mul]
        rfl
      _ = φ (slConjugation d K (A⁻¹ * D) g) := by rw [hY_A]
      _ = φ (slConjugation d K A⁻¹ (slConjugation d K D g)) := by
        rw [map_mul]
        rfl
      _ = φ' (slConjugation d K D g) := rfl


theorem factorial_dvd_card_ggAutomizer_of_GL_family
    {G : Type} [Group G] [Finite G] {J Bs : Subgroup G} [Finite Bs]
    {d : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hd : 3 ≤ d) (h3K : 3 ∣ Nat.card K - 1)
    (hBJ : Bs ≤ Subgroup.normalizer (J : Set G))
    (φ : Matrix.SpecialLinearGroup (Fin d) K →* J)
    (hφ : Function.Surjective φ)
    (hker : ∀ g, φ g = 1 → g ∈ scalars d K)
    (hBs : CFSG.Open.IsElemAbelian 3 Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (Y : Bs → GL (Fin d) K)
    (hYcomm : ∀ b b', Commute (Y b) (Y b'))
    (hYcube : ∀ b, ∃ r : K, r ≠ 0 ∧
      ((Y b : Matrix (Fin d) (Fin d) K) ^ 3 = (r ^ 3) • (1 : Matrix (Fin d) (Fin d) K)))
    (hYact : ∀ b g, (ggGamma J hBJ b) (φ g) = φ (slConjugation d K (Y b) g))
    (h9 : 9 ≤ Nat.card (ggGamma J hBJ).range) :
    d.factorial ∣ Nat.card (ggAutomizer J Bs) := by
  obtain ⟨-, -, φ', -, hφ', hker', hdiag'⟩ :=
    exists_diagonal_cover_of_GL_family h3K hBJ φ hφ hker Y hYcomm hYcube hYact
  exact factorial_dvd_card_ggAutomizer hd h3K hBJ φ' hφ' hker' hBs hSC hdiag' h9

theorem d_eq_three_of_card_ggAutomizer_eq_six_of_GL_family
    {G : Type} [Group G] [Finite G] {J Bs : Subgroup G} [Finite Bs]
    {d : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hd : 3 ≤ d) (h3K : 3 ∣ Nat.card K - 1)
    (hBJ : Bs ≤ Subgroup.normalizer (J : Set G))
    (φ : Matrix.SpecialLinearGroup (Fin d) K →* J)
    (hφ : Function.Surjective φ)
    (hker : ∀ g, φ g = 1 → g ∈ scalars d K)
    (hBs : CFSG.Open.IsElemAbelian 3 Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (Y : Bs → GL (Fin d) K)
    (hYcomm : ∀ b b', Commute (Y b) (Y b'))
    (hYcube : ∀ b, ∃ r : K, r ≠ 0 ∧
      ((Y b : Matrix (Fin d) (Fin d) K) ^ 3 = (r ^ 3) • (1 : Matrix (Fin d) (Fin d) K)))
    (hYact : ∀ b g, (ggGamma J hBJ b) (φ g) = φ (slConjugation d K (Y b) g))
    (h9 : 9 ≤ Nat.card (ggGamma J hBJ).range)
    (hAut : Nat.card (ggAutomizer J Bs) = 6) :
    d = 3 := by
  obtain ⟨-, -, φ', -, hφ', hker', hdiag'⟩ :=
    exists_diagonal_cover_of_GL_family h3K hBJ φ hφ hker Y hYcomm hYcube hYact
  exact d_eq_three_of_card_ggAutomizer_eq_six hd h3K hBJ φ' hφ' hker' hBs hSC hdiag' h9 hAut

theorem hasLabel_and_lambda2_of_scalarKernel_cover
    {G : Type} [Group G] {J : Subgroup G}
    {d f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hd : 3 ≤ d) (hK : Nat.card K = 2 ^ f)
    (φ : Matrix.SpecialLinearGroup (Fin d) K →* J)
    (hφ : Function.Surjective φ)
    (hker : ∀ g, φ g = 1 → g ∈ scalars d K) :
    LargeEvenInLambda2 (⟨.A, d - 1, f⟩ : LargeEvenLabel) ∧
      GGHasLabel (⟨.A, d - 1, f⟩ : LargeEvenLabel) (J ⧸ Subgroup.center J) := by
  classical
  have hf : 1 ≤ f := by
    by_contra h
    have h0 : f = 0 := by omega
    rw [h0, pow_zero] at hK
    have h1 := Finite.one_lt_card (α := K)
    omega
  have hd1 : 1 ≤ d := by omega
  have hdm1 : d - 1 + 1 = d := Nat.sub_add_cancel hd1
  let e : projectiveSL d K ≃* J ⧸ Subgroup.center J :=
    TypeA.centerQuotEquivOfScalarKernel hd φ hφ (fun g hg => hker g hg)
  have hmodel : StatedClassicalModel (J ⧸ Subgroup.center J) .PSL (d - 1 + 1) 2 f := by
    refine ⟨⟨Nat.prime_two, hf, ?_, ?_, ?_⟩, K, inferInstance, inferInstance, hK, ?_⟩
    · simpa [hdm1] using (show 2 ≤ d by omega)
    · intro h
      have h1 : d = 2 := by
        have hd1' : 1 ≤ d := by omega
        have := congrArg Prod.fst h
        simpa [Nat.sub_add_cancel hd1'] using this
      omega
    · intro h
      have h1 : d = 2 := by
        have hd1' : 1 ≤ d := by omega
        have := congrArg Prod.fst h
        simpa [Nat.sub_add_cancel hd1'] using this
      omega
    · rw [hdm1]
      exact ⟨e.symm.trans
        ((CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL d K).symm.trans
          (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj d K))⟩
  exact ⟨largeEvenInLambda2_typeA (n := d - 1) (f := f) hmodel,
    ggHasLabel_typeA (n := d - 1) (f := f) hmodel⟩




theorem actual_card_eq_factorial_of_model
    {G : Type} [Group G] [Finite G] {J Bs : Subgroup G}
    {d : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hd : 4 ≤ d) (h3K : 3 ∣ Nat.card K - 1)
    (hBJ : Bs ≤ Subgroup.normalizer (J : Set G))
    (hBs : CFSG.Open.IsElemAbelian 3 Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hNoTr : GGNoTransvection 3 Bs)
    (hZ : Nat.card ↥(Bs ⊓ J ⊓ Subgroup.centralizer (J : Set G)) ≤ 3)
    (φ : Matrix.SpecialLinearGroup (Fin d) K →* J)
    (hφ : Function.Surjective φ)
    (hker : ∀ g, φ g = 1 → g ∈ scalars d K)
    (hdiag : ∀ b : Bs, ∃ t : Fin d → K,
      TypeANbrDvd.ActsDiag φ (ggGamma J hBJ b) t) :
    Nat.card (ggAutomizer J Bs) = d.factorial := by
  apply actual_card_ggAutomizer_eq_factorial_of_model (p := 3) Nat.prime_three (by norm_num)
    hBs hSC hNoTr hBJ hZ hφ hker ?_ h3K hd
  rintro a ⟨b, rfl⟩
  exact hdiag b

theorem actual_card_eq_six_of_model
    {G : Type} [Group G] [Finite G] {J Bs : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (h3K : 3 ∣ Nat.card K - 1)
    (hBJ : Bs ≤ Subgroup.normalizer (J : Set G))
    (hBs : CFSG.Open.IsElemAbelian 3 Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hNoTr : GGNoTransvection 3 Bs)
    (hZ : Nat.card ↥(Bs ⊓ J ⊓ Subgroup.centralizer (J : Set G)) ≤ 3)
    (φ : Matrix.SpecialLinearGroup (Fin 3) K →* J)
    (hφ : Function.Surjective φ)
    (hker : ∀ g, φ g = 1 → g ∈ scalars 3 K)
    (hdiag : ∀ b : Bs, ∃ t : Fin 3 → K,
      TypeANbrDvd.ActsDiag φ (ggGamma J hBJ b) t)
    (h9 : 9 ≤ Nat.card (ggGamma J hBJ).range) :
    Nat.card (ggAutomizer J Bs) = 6 := by
  apply actual_card_ggAutomizer_eq_six_of_nine_le_card hBs hSC hNoTr hBJ hZ
    hφ hker ?_ h3K h9
  rintro a ⟨b, rfl⟩
  exact hdiag b


theorem actual_card_eq_factorial_of_GL_family
    {G : Type} [Group G] [Finite G] {J Bs : Subgroup G} [Finite Bs]
    {d : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hd : 4 ≤ d) (h3K : 3 ∣ Nat.card K - 1)
    (hBJ : Bs ≤ Subgroup.normalizer (J : Set G))
    (hBs : CFSG.Open.IsElemAbelian 3 Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hNoTr : GGNoTransvection 3 Bs)
    (hZ : Nat.card ↥(Bs ⊓ J ⊓ Subgroup.centralizer (J : Set G)) ≤ 3)
    (φ : Matrix.SpecialLinearGroup (Fin d) K →* J)
    (hφ : Function.Surjective φ)
    (hker : ∀ g, φ g = 1 → g ∈ scalars d K)
    (Y : Bs → GL (Fin d) K)
    (hYcomm : ∀ b b', Commute (Y b) (Y b'))
    (hYcube : ∀ b, ∃ r : K, r ≠ 0 ∧
      ((Y b : Matrix (Fin d) (Fin d) K) ^ 3 = (r ^ 3) • (1 : Matrix (Fin d) (Fin d) K)))
    (hYact : ∀ b g, (ggGamma J hBJ b) (φ g) = φ (slConjugation d K (Y b) g)) :
    Nat.card (ggAutomizer J Bs) = d.factorial := by
  obtain ⟨-, -, φ', -, hφ', hker', hdiag'⟩ :=
    exists_diagonal_cover_of_GL_family h3K hBJ φ hφ hker Y hYcomm hYcube hYact
  exact actual_card_eq_factorial_of_model hd h3K hBJ hBs hSC hNoTr hZ φ' hφ' hker' hdiag'

theorem actual_card_eq_six_of_GL_family
    {G : Type} [Group G] [Finite G] {J Bs : Subgroup G} [Finite Bs]
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (h3K : 3 ∣ Nat.card K - 1)
    (hBJ : Bs ≤ Subgroup.normalizer (J : Set G))
    (hBs : CFSG.Open.IsElemAbelian 3 Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hNoTr : GGNoTransvection 3 Bs)
    (hZ : Nat.card ↥(Bs ⊓ J ⊓ Subgroup.centralizer (J : Set G)) ≤ 3)
    (φ : Matrix.SpecialLinearGroup (Fin 3) K →* J)
    (hφ : Function.Surjective φ)
    (hker : ∀ g, φ g = 1 → g ∈ scalars 3 K)
    (Y : Bs → GL (Fin 3) K)
    (hYcomm : ∀ b b', Commute (Y b) (Y b'))
    (hYcube : ∀ b, ∃ r : K, r ≠ 0 ∧
      ((Y b : Matrix (Fin 3) (Fin 3) K) ^ 3 = (r ^ 3) • (1 : Matrix (Fin 3) (Fin 3) K)))
    (hYact : ∀ b g, (ggGamma J hBJ b) (φ g) = φ (slConjugation 3 K (Y b) g))
    (h9 : 9 ≤ Nat.card (ggGamma J hBJ).range) :
    Nat.card (ggAutomizer J Bs) = 6 := by
  obtain ⟨-, -, φ', -, hφ', hker', hdiag'⟩ :=
    exists_diagonal_cover_of_GL_family h3K hBJ φ hφ hker Y hYcomm hYcube hYact
  exact actual_card_eq_six_of_model h3K hBJ hBs hSC hNoTr hZ φ' hφ' hker' hdiag' h9

theorem lineJType_eq_A2_or_A3_of_card_eq_factorial
    {G : Type} [Group G] {Bs J : Subgroup G} [Fact (Nat.Prime 3)]
    {T : GGResLineJType} (hD : GGResLineJDatum 3 Bs J T)
    {d : ℕ} (hd : 3 ≤ d)
    (hcard : Nat.card (ggAutomizer J Bs) = d.factorial) :
    T = .A2 ∨ T = .A3 := by
  cases T
  · exact Or.inl rfl
  · exfalso
    have hcard8 : Nat.card (ggAutomizer J Bs) = 8 :=
      ggAutomizer_card_of_lineJDatum_B2 (p := 3) rfl hD
    have hdeq : d.factorial = 8 := by rw [← hcard, hcard8]
    have hle : d ≤ 4 := by
      by_contra h
      have h5 : 5 ≤ d := by omega
      have hdvd : ((5 : ℕ).factorial) ∣ d.factorial := Nat.factorial_dvd_factorial h5
      rw [show ((5 : ℕ).factorial) = 120 by norm_num, hdeq] at hdvd
      norm_num at hdvd
    interval_cases d <;> norm_num at hdeq
  · exact Or.inr rfl
  · exfalso
    have hcard48 : Nat.card (ggAutomizer J Bs) = 48 :=
      ggAutomizer_card_of_lineJDatum_B3 (p := 3) rfl hD
    have hdeq : d.factorial = 48 := by rw [← hcard, hcard48]
    have hle : d ≤ 4 := by
      by_contra h
      have h5 : 5 ≤ d := by omega
      have hdvd : ((5 : ℕ).factorial) ∣ d.factorial := Nat.factorial_dvd_factorial h5
      rw [show ((5 : ℕ).factorial) = 120 by norm_num, hdeq] at hdvd
      norm_num at hdvd
    interval_cases d <;> norm_num at hdeq
  · exfalso
    have hcard48 : Nat.card (ggAutomizer J Bs) = 48 :=
      ggAutomizer_card_of_lineJDatum_C3 (p := 3) rfl hD
    have hdeq : d.factorial = 48 := by rw [← hcard, hcard48]
    have hle : d ≤ 4 := by
      by_contra h
      have h5 : 5 ≤ d := by omega
      have hdvd : ((5 : ℕ).factorial) ∣ d.factorial := Nat.factorial_dvd_factorial h5
      rw [show ((5 : ℕ).factorial) = 120 by norm_num, hdeq] at hdvd
      norm_num at hdvd
    interval_cases d <;> norm_num at hdeq

theorem exists_lineJLabel_of_card_eq_factorial
    {G : Type} [Group G] [Finite G] {Bs J : Subgroup G} [Fact (Nat.Prime 3)]
    {T : GGResLineJType} (hD : GGResLineJDatum 3 Bs J T)
    {d f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hd : 3 ≤ d) (hK : Nat.card K = 2 ^ f) (h3K : 3 ∣ Nat.card K - 1)
    (hcard : Nat.card (ggAutomizer J Bs) = d.factorial)
    (φ : Matrix.SpecialLinearGroup (Fin d) K →* J)
    (hφ : Function.Surjective φ)
    (hker : ∀ g, φ g = 1 → g ∈ scalars d K) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧
      ggResLineJLabel T lab ∧ GGHasLabel lab (J ⧸ Subgroup.center J) := by
  have h3f : 3 ∣ 2 ^ f - 1 := by simpa [hK] using h3K
  rcases lineJType_eq_A2_or_A3_of_card_eq_factorial hD hd hcard with hT | hT
  · subst hT
    have hcard6 : Nat.card (ggAutomizer J Bs) = 6 :=
      ggAutomizer_card_of_lineJDatum_A2 (p := 3) rfl hD
    have hdeq : d.factorial = 6 := by rw [← hcard, hcard6]
    have hd3 : d = 3 := by
      by_contra h
      have h4 : 4 ≤ d := by omega
      have hdvd : ((4 : ℕ).factorial) ∣ d.factorial := Nat.factorial_dvd_factorial h4
      rw [show ((4 : ℕ).factorial) = 24 by norm_num, hdeq] at hdvd
      norm_num at hdvd
    subst d
    have hlab := hasLabel_and_lambda2_of_scalarKernel_cover (d := 3) (f := f)
      (by norm_num) hK φ hφ hker
    refine ⟨⟨.A, 2, f⟩, ?_, Or.inl ⟨rfl, rfl, h3f⟩, ?_⟩
    · simpa using hlab.1
    · simpa using hlab.2
  · subst hT
    have hcard24 : Nat.card (ggAutomizer J Bs) = 24 :=
      ggAutomizer_card_of_lineJDatum_A3 (p := 3) rfl hD
    have hdeq : d.factorial = 24 := by rw [← hcard, hcard24]
    have hd4 : d = 4 := by
      have hle : d ≤ 4 := by
        by_contra h
        have h5 : 5 ≤ d := by omega
        have hdvd : ((5 : ℕ).factorial) ∣ d.factorial := Nat.factorial_dvd_factorial h5
        rw [show ((5 : ℕ).factorial) = 120 by norm_num, hdeq] at hdvd
        norm_num at hdvd
      interval_cases d
      · norm_num at hdeq
      · rfl
    subst d
    have hlab := hasLabel_and_lambda2_of_scalarKernel_cover (d := 4) (f := f)
      (by norm_num) hK φ hφ hker
    refine ⟨⟨.A, 3, f⟩, ?_, Or.inl ⟨Or.inl rfl, rfl, h3f⟩, ?_⟩
    · simpa using hlab.1
    · simpa using hlab.2


theorem exists_lineJLabel_of_GL_family
    {G : Type} [Group G] [Finite G] {J Bs : Subgroup G} [Finite Bs]
    [Fact (Nat.Prime 3)] {T : GGResLineJType} (hD : GGResLineJDatum 3 Bs J T)
    {d f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hd : 3 ≤ d) (hK : Nat.card K = 2 ^ f) (h3K : 3 ∣ Nat.card K - 1)
    (hBJ : Bs ≤ Subgroup.normalizer (J : Set G))
    (hBs : CFSG.Open.IsElemAbelian 3 Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hNoTr : GGNoTransvection 3 Bs)
    (hZ : Nat.card ↥(Bs ⊓ J ⊓ Subgroup.centralizer (J : Set G)) ≤ 3)
    (φ : Matrix.SpecialLinearGroup (Fin d) K →* J)
    (hφ : Function.Surjective φ)
    (hker : ∀ g, φ g = 1 → g ∈ scalars d K)
    (Y : Bs → GL (Fin d) K)
    (hYcomm : ∀ b b', Commute (Y b) (Y b'))
    (hYcube : ∀ b, ∃ r : K, r ≠ 0 ∧
      ((Y b : Matrix (Fin d) (Fin d) K) ^ 3 = (r ^ 3) • (1 : Matrix (Fin d) (Fin d) K)))
    (hYact : ∀ b g, (ggGamma J hBJ b) (φ g) = φ (slConjugation d K (Y b) g))
    (h9 : d = 3 → 9 ≤ Nat.card (ggGamma J hBJ).range) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧
      ggResLineJLabel T lab ∧ GGHasLabel lab (J ⧸ Subgroup.center J) := by
  have hcard : Nat.card (ggAutomizer J Bs) = d.factorial := by
    by_cases hd4 : 4 ≤ d
    · exact actual_card_eq_factorial_of_GL_family hd4 h3K hBJ hBs hSC hNoTr hZ
        φ hφ hker Y hYcomm hYcube hYact
    · have hd3 : d = 3 := by omega
      subst d
      have h6 := actual_card_eq_six_of_GL_family h3K hBJ hBs hSC hNoTr hZ
        φ hφ hker Y hYcomm hYcube hYact (h9 rfl)
      rw [h6]
      norm_num
  exact exists_lineJLabel_of_card_eq_factorial hD hd hK h3K hcard φ hφ hker


theorem exists_lineJLabel_of_GGResHyp_GL_family_of_hZ
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {Kc : Subgroup G} [Finite Bs]
    [Fact (Nat.Prime 3)]
    (hH : GGResHyp 3 B Bs x L D J y Kc)
    {T : GGResLineJType} (hD : GGResLineJDatum 3 Bs J T)
    {d f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hd : 3 ≤ d) (hK : Nat.card K = 2 ^ f) (h3K : 3 ∣ Nat.card K - 1)
    (hZ : Nat.card ↥(Bs ⊓ J ⊓ Subgroup.centralizer (J : Set G)) ≤ 3)
    (φ : Matrix.SpecialLinearGroup (Fin d) K →* J)
    (hφ : Function.Surjective φ)
    (hker : ∀ g, φ g = 1 → g ∈ scalars d K)
    (Y : Bs → GL (Fin d) K)
    (hYcomm : ∀ b b', Commute (Y b) (Y b'))
    (hYcube : ∀ b, ∃ r : K, r ≠ 0 ∧
      ((Y b : Matrix (Fin d) (Fin d) K) ^ 3 = (r ^ 3) • (1 : Matrix (Fin d) (Fin d) K)))
    (hYact : ∀ b g, (ggGamma J (GGResHyp.Bs_le_normalizer_J hH) b) (φ g) =
      φ (slConjugation d K (Y b) g)) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧
      ggResLineJLabel T lab ∧ GGHasLabel lab (J ⧸ Subgroup.center J) := by
  let hN : Bs ≤ Subgroup.normalizer (J : Set G) := GGResHyp.Bs_le_normalizer_J hH
  have hBs : CFSG.Open.IsElemAbelian 3 Bs := hH.1.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  have hNoTr : GGNoTransvection 3 Bs := hH.2.2.2.1
  have h9 : 9 ≤ Nat.card (ggGamma J hN).range := by
    have h := GGResHyp.sq_le_card_gamma_J (p := 3) hH
    have hN' : Bs ≤ Subgroup.normalizer (J : Set G) := GGResHyp.Bs_le_normalizer_J hH
    have hsub : ggGamma J hN = ggGamma J hN' := by
      ext b
      rfl
    rw [hsub]
    simpa using h
  exact exists_lineJLabel_of_GL_family hD hd hK h3K hN hBs hSC hNoTr hZ
    φ hφ hker Y hYcomm hYcube hYact (fun _ => h9)

theorem card_center_le_three_of_scalar_cover
    {G : Type} [Group G] [Finite G] {J : Subgroup G}
    {d f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hd : 3 ≤ d) (hd34 : d = 3 ∨ d = 4)
    (hK : Nat.card K = 2 ^ f) (h3K : 3 ∣ Nat.card K - 1)
    (φ : Matrix.SpecialLinearGroup (Fin d) K →* J)
    (hφ : Function.Surjective φ)
    (hker : ∀ g, φ g = 1 → g ∈ scalars d K) :
    Nat.card (Subgroup.center J) ≤ 3 := by
  classical
  have hf : 1 ≤ f := by
    by_contra h
    have h0 : f = 0 := by omega
    rw [h0, pow_zero] at hK
    have h1 := Finite.one_lt_card (α := K)
    omega
  have hodd : Odd (Nat.card K - 1) := by
    rw [hK]
    have hf0 : f ≠ 0 := by omega
    have heven : Even (2 ^ f) := Even.pow_of_ne_zero (by norm_num : Even 2) hf0
    have h2pos : 0 < 2 ^ f := pow_pos (by norm_num) f
    exact Nat.Even.sub_odd (by omega) heven (by norm_num : Odd 1)
  have hcomap := TypeA.comap_center_eq_of_scalarKernel hd φ hφ (fun g hg => hker g hg)
  have hcenter : Subgroup.center J = (scalars d K).map φ := by
    rw [← Subgroup.map_comap_eq_self_of_surjective hφ (Subgroup.center J)]
    rw [hcomap, scalars_eq_center]
  have hcenter_le : Nat.card (Subgroup.center J) ≤ 3 := by
    rw [hcenter]
    have hdvd : Nat.card ((scalars d K).map φ) ∣ Nat.card (scalars d K) :=
      Subgroup.card_map_dvd (H := scalars d K) φ
    have hscard : Nat.card (scalars d K) = Nat.gcd d (Nat.card K - 1) :=
      CFSG.LocalAnalysis.ComponentInitial.card_scalars_eq_gcd K (by omega)
    have hgcd : Nat.gcd d (Nat.card K - 1) ≤ 3 := by
      rcases hd34 with rfl | rfl
      · have hg : Nat.gcd 3 (Nat.card K - 1) = 3 := by
          apply Nat.dvd_antisymm (Nat.gcd_dvd_left _ _)
          exact Nat.dvd_gcd dvd_rfl h3K
        rw [hg]
      · have h2 : Nat.Coprime 2 (Nat.card K - 1) := Odd.coprime_two_left hodd
        have h4 : Nat.Coprime 4 (Nat.card K - 1) := by
          simpa using h2.pow_left 2
        have hg : Nat.gcd 4 (Nat.card K - 1) = 1 := by
          simpa [Nat.Coprime] using h4
        rw [hg]
        norm_num
    calc Nat.card ((scalars d K).map φ) ≤ Nat.card (scalars d K) :=
          Nat.le_of_dvd (Nat.card_pos) hdvd
      _ = Nat.gcd d (Nat.card K - 1) := hscard
      _ ≤ 3 := hgcd
  exact hcenter_le

theorem card_bstar_inf_center_le_three_of_scalar_cover
    {G : Type} [Group G] [Finite G] {J Bs : Subgroup G}
    {d f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hd : 3 ≤ d) (hd34 : d = 3 ∨ d = 4)
    (hK : Nat.card K = 2 ^ f) (h3K : 3 ∣ Nat.card K - 1)
    (φ : Matrix.SpecialLinearGroup (Fin d) K →* J)
    (hφ : Function.Surjective φ)
    (hker : ∀ g, φ g = 1 → g ∈ scalars d K) :
    Nat.card ↥(Bs ⊓ J ⊓ Subgroup.centralizer (J : Set G)) ≤ 3 := by
  classical
  have hcenter := card_center_le_three_of_scalar_cover hd hd34 hK h3K φ hφ hker
  let f : ↥(Bs ⊓ J ⊓ Subgroup.centralizer (J : Set G)) → Subgroup.center J := fun x =>
    ⟨⟨x.1, x.2.1.2⟩, by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp x.2.2 y y.2⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : Subgroup.center J => ((z : J) : G)) hxy
  calc Nat.card ↥(Bs ⊓ J ⊓ Subgroup.centralizer (J : Set G))
      ≤ Nat.card (Subgroup.center J) := Nat.card_le_card_of_injective f hinj
    _ ≤ 3 := hcenter


theorem exists_lineJLabel_of_GGResHyp_GL_family
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {Kc : Subgroup G} [Finite Bs]
    [Fact (Nat.Prime 3)]
    (hH : GGResHyp 3 B Bs x L D J y Kc)
    {T : GGResLineJType} (hD : GGResLineJDatum 3 Bs J T)
    {d f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hd : 3 ≤ d) (hK : Nat.card K = 2 ^ f) (h3K : 3 ∣ Nat.card K - 1)
    (φ : Matrix.SpecialLinearGroup (Fin d) K →* J)
    (hφ : Function.Surjective φ)
    (hker : ∀ g, φ g = 1 → g ∈ scalars d K)
    (Y : Bs → GL (Fin d) K)
    (hYcomm : ∀ b b', Commute (Y b) (Y b'))
    (hYcube : ∀ b, ∃ r : K, r ≠ 0 ∧
      ((Y b : Matrix (Fin d) (Fin d) K) ^ 3 = (r ^ 3) • (1 : Matrix (Fin d) (Fin d) K)))
    (hYact : ∀ b g, (ggGamma J (GGResHyp.Bs_le_normalizer_J hH) b) (φ g) =
      φ (slConjugation d K (Y b) g)) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧
      ggResLineJLabel T lab ∧ GGHasLabel lab (J ⧸ Subgroup.center J) := by
  let hN : Bs ≤ Subgroup.normalizer (J : Set G) := GGResHyp.Bs_le_normalizer_J hH
  have hBs : CFSG.Open.IsElemAbelian 3 Bs := hH.1.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  have hNoTr : GGNoTransvection 3 Bs := hH.2.2.2.1
  have h9 : 9 ≤ Nat.card (ggGamma J hN).range := by
    have h := GGResHyp.sq_le_card_gamma_J (p := 3) hH
    have hN' : Bs ≤ Subgroup.normalizer (J : Set G) := GGResHyp.Bs_le_normalizer_J hH
    have hsub : ggGamma J hN = ggGamma J hN' := by
      ext b
      rfl
    rw [hsub]
    simpa using h
  by_cases hd34 : d = 3 ∨ d = 4
  · have hZ : Nat.card ↥(Bs ⊓ J ⊓ Subgroup.centralizer (J : Set G)) ≤ 3 :=
      card_bstar_inf_center_le_three_of_scalar_cover hd hd34 hK h3K φ hφ hker
    exact exists_lineJLabel_of_GL_family hD hd hK h3K hN hBs hSC hNoTr hZ
      φ hφ hker Y hYcomm hYcube hYact (fun _ => h9)
  · exfalso
    have hd5 : 5 ≤ d := by omega
    have hdiv : d.factorial ∣ Nat.card (ggAutomizer J Bs) :=
      factorial_dvd_card_ggAutomizer_of_GL_family hd h3K hN φ hφ hker hBs hSC
        Y hYcomm hYcube hYact (by simpa [hN] using h9)
    have hle : Nat.card (ggAutomizer J Bs) ≤ 48 :=
      card_ggAutomizer_le_fortyEight_of_lineJDatum hD
    have h120 : 120 ≤ d.factorial := by
      have h5 : ((5 : ℕ).factorial) ≤ d.factorial := Nat.factorial_le hd5
      norm_num at h5
      exact h5
    have h120le : 120 ≤ Nat.card (ggAutomizer J Bs) :=
      le_trans h120 (Nat.le_of_dvd Nat.card_pos hdiv)
    omega

theorem card_le_three_pow_rank_of_compatible_splitLinear_marking
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {Kc : Subgroup G}
    [Fact (Nat.Prime 3)]
    (hH : GGResHyp 3 B Bs x L D J y Kc)
    {rank : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (h3K : 3 ∣ Nat.card K - 1)
    (θ : J ⧸ Subgroup.center J ≃*
      LargeEvenProj (LargeEvenSLGroup (Fin (rank + 1)) K))
    (hperfJ : commutator J = ⊤)
    (hN : Bs ≤ Subgroup.normalizer (J : Set G))
    (hind : ∀ b ∈ Bs, ∃ φ ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSLGroup (Fin (rank + 1)) K)) Set.univ,
        LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) :
    Nat.card (ggGamma J hN).range ≤ 3 ^ rank := by
  classical
  let A : Subgroup (MulAut ↥J) := (ggGamma J hN).range
  have hAe : CFSG.Open.IsElemAbelian 3 A := by
    dsimp [A]
    exact isElemAbelian_range
      (fun a b : ↥Bs => (@IsMulCommutative.is_comm ↥Bs _ hH.1.2.1.2.1.1).comm a b)
      (fun b : ↥Bs => Subtype.ext (by simpa using hH.1.2.1.2.1.2 b b.2))
      (ggGamma J hN)
  let B : Subgroup (MulAut (LargeEvenProj (LargeEvenSLGroup (Fin (rank + 1)) K))) :=
    A.map (ggInducedAut θ)
  have hBcard : Nat.card B = Nat.card A :=
    Subgroup.card_map_of_injective (ggInducedAut_injective_of_perfect hperfJ θ)
  have hBe : CFSG.Open.IsElemAbelian 3 B := hAe.map _
  have hBI : (B : Set (MulAut (LargeEvenProj (LargeEvenSLGroup (Fin (rank + 1)) K)))) ⊆
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin (rank + 1)) K)) Set.univ := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨b, rfl⟩ := ha
    have hmem := ggBeta_mem J θ hN hind b
    have hbeta : ggBeta J θ hN b = ggInducedAut θ (ggGamma J hN b) := by
      rw [ggBeta_eq, ggLAut_eq_ggInducedAut]
      rfl
    have hmem' : ggInducedAut θ (ggGamma J hN b) ∈
        LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin (rank + 1)) K)) Set.univ := by
      rwa [hbeta] at hmem
    exact hmem'
  let e : LargeEvenProj (LargeEvenSLGroup (Fin (rank + 1)) K) ≃*
      projectiveSL (rank + 1) K := TypeA.recipeEquiv (rank + 1) K
  let X : Subgroup (MulAut (projectiveSL (rank + 1) K)) := B.map (MulAut.congr e).toMonoidHom
  have hXcard : Nat.card X = Nat.card B :=
    Subgroup.card_map_of_injective (MulAut.congr e).injective
  have hXe : CFSG.Open.IsElemAbelian 3 X := hBe.map _
  have hXI : (X : Set (MulAut (projectiveSL (rank + 1) K))) ⊆
      Set.range (conjAut (rank + 1) K) := by
    rintro _ ⟨b, hb, rfl⟩
    exact TypeA.congr_recipeEquiv_mem (hBI hb)
  have hrank : Nat.card X ≤ 3 ^ ((rank + 1) - 1) :=
    TypeA.card_le_of_subset_conjAut_gen (d := rank + 1) (p := 3) (K := K)
      (by norm_num) (by norm_num) h3K (by omega) hXe hXI
  calc Nat.card (ggGamma J hN).range = Nat.card A := rfl
    _ = Nat.card B := hBcard.symm
    _ = Nat.card X := hXcard.symm
    _ ≤ 3 ^ ((rank + 1) - 1) := hrank
    _ = 3 ^ rank := by rw [Nat.add_sub_cancel]

theorem three_cube_le_card_gamma_of_compatible_splitLinear_marking
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {Kc : Subgroup G}
    [Fact (Nat.Prime 3)]
    (hH : GGResHyp 3 B Bs x L D J y Kc)
    {d : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (h3K : 3 ∣ Nat.card K - 1) (hd4 : 4 ≤ d)
    (θ : J ⧸ Subgroup.center J ≃*
      LargeEvenProj (LargeEvenSLGroup (Fin d) K)) :
    3 ^ 3 ≤ Nat.card (ggGamma J (GGResHyp.Bs_le_normalizer_J hH)).range := by
  classical
  have hsec : TypeA.SLHasSections d K := slHasSections_of_four_le (p := 3) (K := K)
    (by norm_num) h3K hd4
  have e : LargeEvenProj (LargeEvenSLGroup (Fin d) K) ≃* projectiveSL d K :=
    TypeA.recipeEquiv d K
  by_cases hd_eq : d = 4
  · subst d
    have hTproj : GGTorusLift 3 (4 - 1) (projectiveSL 4 K) :=
      TypeA.ggTorusLift_coprime (p := 3) (d := 4) (K := K) (by norm_num) h3K
        (by norm_num) (by norm_num) hsec
    have hT : GGTorusLift 3 3 (LargeEvenProj (LargeEvenSLGroup (Fin 4) K)) := by
      simpa using TypeA.ggTorusLift_of_mulEquiv (TypeA.recipeEquiv 4 K) hTproj
    simpa using GGResHyp.pow_le_card_range_gamma_J_of_torusLift hH θ hT
  · have hd5 : 5 ≤ d := by omega
    have hTproj : GGTorusLift 3 (d - 2) (projectiveSL d K) :=
      TypeA.ggTorusLift_sub_two (p := 3) (d := d) (K := K) (by norm_num) h3K
        (by omega) hsec
    have hT : GGTorusLift 3 (d - 2) (LargeEvenProj (LargeEvenSLGroup (Fin d) K)) :=
      TypeA.ggTorusLift_of_mulEquiv e hTproj
    have h27 := GGResHyp.pow_le_card_range_gamma_J_of_torusLift hH θ hT
    exact (Nat.pow_le_pow_right (by norm_num) (by omega : 3 ≤ d - 2)).trans h27

theorem exists_actsDiag_model_of_splitLinear_marking_data
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {Kc : Subgroup G}
    [Fact (Nat.Prime 3)]
    (hH : GGResHyp 3 B Bs x L D J y Kc)
    {rank : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (h3K : 3 ∣ Nat.card K - 1)
    (θ : J ⧸ Subgroup.center J ≃*
      LargeEvenProj (LargeEvenSLGroup (Fin (rank + 1)) K))
    (hperfJ : commutator J = ⊤)
    (hind : ∀ b ∈ Bs, ∃ φ ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSLGroup (Fin (rank + 1)) K)) Set.univ,
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (h27 : 3 ^ 3 ≤
      Nat.card (ggGamma J (GGResHyp.Bs_le_normalizer_J hH)).range)
    (hd4 : 4 ≤ rank + 1) :
    ∃ φ' : Matrix.SpecialLinearGroup (Fin (rank + 1)) K →* J,
      Function.Surjective φ' ∧
      (∀ g, φ' g = 1 → g ∈ scalars (rank + 1) K) ∧
      (∀ b : ↥Bs, ∃ t : Fin (rank + 1) → K,
        TypeANbrDvd.ActsDiag φ' (ggGamma J (GGResHyp.Bs_le_normalizer_J hH) b) t) ∧
      (rank + 1).factorial ∣ Nat.card (ggAutomizer J Bs) := by
  classical
  let hN0 : Bs ≤ Subgroup.normalizer (J : Set G) := GGResHyp.Bs_le_normalizer_J hH
  let A : Subgroup (MulAut ↥J) := (ggGamma J hN0).range
  have hAe : CFSG.Open.IsElemAbelian 3 A := by
    dsimp [A]
    exact isElemAbelian_range
      (fun a b : ↥Bs => (@IsMulCommutative.is_comm ↥Bs _ hH.1.2.1.2.1.1).comm a b)
      (fun b : ↥Bs => Subtype.ext (by simpa using hH.1.2.1.2.1.2 b b.2))
      (ggGamma J hN0)
  let R : Type := LargeEvenProj (LargeEvenSLGroup (Fin (rank + 1)) K)
  let e : R ≃* projectiveSL (rank + 1) K := TypeA.recipeEquiv (rank + 1) K
  have hsec : TypeA.SLHasSections (rank + 1) K :=
    slHasSections_of_four_le (p := 3) (K := K) (by norm_num) h3K hd4
  have hTproj : GGTorusLift 3 ((rank + 1) - 2) (projectiveSL (rank + 1) K) :=
    TypeA.ggTorusLift_sub_two (p := 3) (d := rank + 1) (K := K) (by norm_num) h3K
      (by omega) hsec
  have hT : GGTorusLift 3 ((rank + 1) - 2) R :=
    TypeA.ggTorusLift_of_mulEquiv e hTproj
  have hAI : ∀ a ∈ A, ∃ φ ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSLGroup (Fin (rank + 1)) K)) Set.univ,
      ∀ l : ↥J, φ (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    rintro a ⟨b, rfl⟩
    exact ⟨ggBeta J θ hN0 b, ggBeta_mem J θ hN0 hind b,
      fun l => ggBeta_ggQuotHom J hN0 θ b l⟩
  have hTB : GGTorusTBGroup 3 ((rank + 1) - 2) R
      (LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSLGroup (Fin (rank + 1)) K)) Set.univ)
      J (ggQuotHom θ) A := by
    refine ⟨ggQuotHom_surjective θ, ?_, hperfJ, hAe, hAI, ?_, ?_, ?_⟩
    · rw [ker_ggQuotHom θ]
    · simpa [A] using GGResHyp.pow_le_card_range_gamma_J_of_torusLift hH θ hT
    · simpa [A] using h27
    · simpa [A] using GGResHyp.gamma_J_selfCent hH
  have hTBproj : GGTorusTBGroup 3 ((rank + 1) - 2) (projectiveSL (rank + 1) K)
      (Set.range (conjAut (rank + 1) K)) J
      (e.toMonoidHom.comp (ggQuotHom θ)) A :=
    hTB.mulEquiv e (fun φ hφ => TypeA.congr_recipeEquiv_mem hφ)
  obtain ⟨φ', hφ's, hφ'ker, hdiagA⟩ :=
    exists_actsDiag_model_of_tbGroup (d := rank + 1) (p := 3) (K := K)
      (by norm_num) h3K hd4 (r := (rank + 1) - 2) (le_refl _) hTBproj
  have hBs : CFSG.Open.IsElemAbelian 3 Bs := hH.1.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  have h9 : 9 ≤ Nat.card (ggGamma J hN0).range := by
    have h := GGResHyp.sq_le_card_gamma_J (p := 3) hH
    simpa using h
  have hdiag : ∀ b : ↥Bs, ∃ t : Fin (rank + 1) → K,
      TypeANbrDvd.ActsDiag φ' (ggGamma J hN0 b) t :=
    fun b => hdiagA (ggGamma J hN0 b) ⟨b, rfl⟩
  have hdvd : (rank + 1).factorial ∣ Nat.card (ggAutomizer J Bs) :=
    factorial_dvd_card_ggAutomizer (d := rank + 1) (K := K) (by omega) h3K hN0 φ'
      hφ's hφ'ker hBs hSC hdiag h9
  exact ⟨φ', hφ's, hφ'ker, hdiag, hdvd⟩

theorem exists_compatible_splitLinear_marking_factorial
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {Kc : Subgroup G}
    [Fact (Nat.Prime 3)]
    (hH : GGResHyp 3 B Bs x L D J y Kc)
    (hMark : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .A ∧ 3 ∣ 2 ^ lab.n - 1) 3 Bs J)
    (h27 : 3 ^ 3 ≤ Nat.card (ggGamma J (GGResHyp.Bs_le_normalizer_J hH)).range) :
    ∃ (rank n : ℕ),
      LargeEvenInLambda2 (⟨.A, rank, n⟩ : LargeEvenLabel) ∧
      3 ∣ 2 ^ n - 1 ∧ 4 ≤ rank + 1 ∧
      GGHasLabel (⟨.A, rank, n⟩ : LargeEvenLabel) (J ⧸ Subgroup.center J) ∧
      (rank + 1).factorial ∣ Nat.card (ggAutomizer J Bs) := by
  classical
  obtain ⟨hperfJ, lab, hΛ, hraw⟩ := hMark
  have hraw0 := hraw
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨_, _, _, _, _, _, _, hS, _, _⟩ := largeEvenRawDatum_exists hraw
  have htag : tag = .A := hS.1
  have h3n : 3 ∣ 2 ^ n - 1 := hS.2
  subst htag
  dsimp only [LargeEvenRawDatum] at hraw
  obtain ⟨K, hKfield, hKfinite, hKcard, hP⟩ := hraw
  obtain ⟨_hsimple, _hnonab, θ, _hS', hN, hind⟩ := hP
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  haveI : CharP K 2 := charP_two_of_card hKcard
  have hpK : 3 ∣ Nat.card K - 1 := by rw [hKcard]; exact h3n
  let hN0 : Bs ≤ Subgroup.normalizer (J : Set G) := GGResHyp.Bs_le_normalizer_J hH
  have hgamma : ggGamma J hN = ggGamma J hN0 := by ext b; rfl
  have hrank : Nat.card (ggGamma J hN).range ≤ 3 ^ rank :=
    card_le_three_pow_rank_of_compatible_splitLinear_marking hH hpK θ hperfJ hN hind
  have hrank0 : Nat.card (ggGamma J hN0).range ≤ 3 ^ rank := by
    rw [← hgamma]
    exact hrank
  have hd4 : 4 ≤ rank + 1 := by
    have h27' : 3 ^ 3 ≤ 3 ^ rank := h27.trans hrank0
    have h3r : 3 ≤ rank :=
      (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h27'
    omega
  obtain ⟨_, _, _, _, hdvd⟩ :=
    exists_actsDiag_model_of_splitLinear_marking_data hH hpK θ hperfJ hind h27 hd4
  have hHas : GGHasLabel (⟨.A, rank, n⟩ : LargeEvenLabel) (J ⧸ Subgroup.center J) := by
    unfold GGHasLabel
    refine largeEvenRawDatum_mono ?_ hraw0
    intro R' _ I' F' hQ
    obtain ⟨-, -, θ', -⟩ := hQ
    exact ⟨θ'⟩
  exact ⟨rank, n, hΛ, h3n, hd4, hHas, hdvd⟩

theorem GGResHyp.exists_lineJLabel_A3_of_compatible_splitLinear_marking
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    [Fact (Nat.Prime 3)]
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hD : GGResLineJDatum 3 Bs J .A3)
    (hMark : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .A ∧ 3 ∣ 2 ^ lab.n - 1) 3 Bs J) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧
      ggResLineJLabel .A3 lab ∧ GGHasLabel lab (J ⧸ Subgroup.center J) := by
  classical
  have h27 : 3 ^ 3 ≤ Nat.card (ggGamma J (GGResHyp.Bs_le_normalizer_J hH)).range :=
    GGResHyp.cube_le_card_gamma_of_A3 hH hD
  obtain ⟨rank, n, hΛ, h3n, hd4, hHas, hdvd⟩ :=
    exists_compatible_splitLinear_marking_factorial hH hMark h27
  have h24 : Nat.card (ggAutomizer J Bs) = 24 :=
    ggAutomizer_card_of_lineJDatum_A3 (p := 3) rfl hD
  have hfact : (rank + 1).factorial ∣ 24 := by rw [← h24]; exact hdvd
  have hdle : rank + 1 ≤ 4 := by
    by_contra h
    have h5 : 5 ≤ rank + 1 := by omega
    have h120 : 120 ≤ (rank + 1).factorial := by
      have h := Nat.factorial_le h5
      have h5fact : Nat.factorial 5 = 120 := by norm_num
      rwa [h5fact] at h
    have hle : (rank + 1).factorial ≤ 24 := Nat.le_of_dvd (by norm_num) hfact
    omega
  have hrequal : rank = 3 := by omega
  refine ⟨⟨.A, 3, n⟩, ?_, ?_, ?_⟩
  · simpa [hrequal] using hΛ
  · unfold ggResLineJLabel
    exact Or.inl ⟨Or.inl rfl, rfl, h3n⟩
  · simpa [hrequal] using hHas

theorem GGResHyp.exists_lineJLabel_A2_of_compatible_splitLinear_marking
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    [Fact (Nat.Prime 3)]
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hD : GGResLineJDatum 3 Bs J .A2)
    (hMark : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .A ∧ 3 ∣ 2 ^ lab.n - 1) 3 Bs J) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧
      ggResLineJLabel .A2 lab ∧ GGHasLabel lab (J ⧸ Subgroup.center J) := by
  classical
  have hMark0 := hMark
  obtain ⟨hperfJ, lab, hΛ, hraw⟩ := hMark
  have hraw0 := hraw
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨_, _, _, _, _, _, _, hS, _, _⟩ := largeEvenRawDatum_exists hraw
  have htag : tag = .A := hS.1
  have h3n : 3 ∣ 2 ^ n - 1 := hS.2
  subst htag
  dsimp only [LargeEvenRawDatum] at hraw
  obtain ⟨K, hKfield, hKfinite, hKcard, hP⟩ := hraw
  obtain ⟨_hsimple, _hnonab, θ, _hS', hN, hind⟩ := hP
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  haveI : CharP K 2 := charP_two_of_card hKcard
  have hpK : 3 ∣ Nat.card K - 1 := by rw [hKcard]; exact h3n
  have hN0 : Bs ≤ Subgroup.normalizer (J : Set G) := GGResHyp.Bs_le_normalizer_J hH
  have hgamma : ggGamma J hN = ggGamma J hN0 := by ext b; rfl
  have h9 : 9 ≤ Nat.card (ggGamma J hN0).range := by
    have h := GGResHyp.sq_le_card_gamma_J (p := 3) hH
    simpa using h
  rcases Nat.lt_or_ge rank 2 with hlt | hge
  · have h1rank : 1 ≤ rank := by simpa using hΛ.2.1
    have hrank1 : rank = 1 := by omega
    exfalso
    have hbound : Nat.card (ggGamma J hN).range ≤ 3 ^ rank :=
      card_le_three_pow_rank_of_compatible_splitLinear_marking hH hpK θ hperfJ hN hind
    have hbound3 : Nat.card (ggGamma J hN).range ≤ 3 := by
      simpa [hrank1] using hbound
    have h9N : 9 ≤ Nat.card (ggGamma J hN).range := by
      rw [hgamma]
      exact h9
    omega
  · by_cases hrank2 : rank = 2
    · subst rank
      refine ⟨⟨.A, 2, n⟩, ?_, ?_, ?_⟩
      · exact hΛ
      · unfold ggResLineJLabel
        exact Or.inl ⟨rfl, rfl, h3n⟩
      · unfold GGHasLabel
        refine largeEvenRawDatum_mono ?_ hraw0
        intro R' _ I' F' hQ
        obtain ⟨-, -, θ', -⟩ := hQ
        exact ⟨θ'⟩
    · have hrank3 : 3 ≤ rank := by omega
      have hd4 : 4 ≤ rank + 1 := by omega
      have h27 : 3 ^ 3 ≤ Nat.card (ggGamma J hN0).range :=
        three_cube_le_card_gamma_of_compatible_splitLinear_marking hH hpK hd4 θ
      obtain ⟨rank', n', _hΛ', _h3n', hd4', _hHas', hdvd'⟩ :=
        exists_compatible_splitLinear_marking_factorial hH hMark0 h27
      exfalso
      have hAut : Nat.card (ggAutomizer J Bs) = 6 :=
        ggAutomizer_card_of_lineJDatum_A2 (p := 3) rfl hD
      have h4dvd : (4 : ℕ).factorial ∣ Nat.card (ggAutomizer J Bs) :=
        (Nat.factorial_dvd_factorial hd4').trans hdvd'
      rw [show (4 : ℕ).factorial = 24 by norm_num, hAut] at h4dvd
      norm_num at h4dvd


theorem GGResHyp.not_exists_matched_splitLinear_marking_B3C3
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {Kc : Subgroup G}
    [Fact (Nat.Prime 3)]
    (hH : GGResHyp 3 B Bs x L D J y Kc) {T : GGResLineJType}
    (hD : GGResLineJDatum 3 Bs J T)
    (hT : T = .B3 ∨ T = .C3)
    (hMark : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .A ∧ 3 ∣ 2 ^ lab.n - 1) 3 Bs J) :
    False := by
  classical
  obtain ⟨hperfJ, lab, hΛ, hraw⟩ := hMark
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨_, _, _, _, _, _, _, hS, _, _⟩ := largeEvenRawDatum_exists hraw
  have htag : tag = .A := hS.1
  have h3n : 3 ∣ 2 ^ n - 1 := hS.2
  subst htag
  dsimp only [LargeEvenRawDatum] at hraw
  obtain ⟨K, hKfield, hKfinite, hKcard, hP⟩ := hraw
  obtain ⟨_hsimple, _hnonab, θ, _hS', hN, hind⟩ := hP
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  haveI : CharP K 2 := charP_two_of_card hKcard
  have hpK : 3 ∣ Nat.card K - 1 := by rw [hKcard]; exact h3n
  let hN0 : Bs ≤ Subgroup.normalizer (J : Set G) := GGResHyp.Bs_le_normalizer_J hH
  have hgamma : ggGamma J hN = ggGamma J hN0 := by ext b; rfl
  have hrank : Nat.card (ggGamma J hN).range ≤ 3 ^ rank :=
    card_le_three_pow_rank_of_compatible_splitLinear_marking hH hpK θ hperfJ hN hind
  have hrank0 : Nat.card (ggGamma J hN0).range ≤ 3 ^ rank := by
    rw [← hgamma]
    exact hrank
  have h27 : 3 ^ 3 ≤ Nat.card (ggGamma J hN0).range := by
    simpa using cube_le_card_gamma_of_B3C3 (G := G) hN0 hD hT
  have hAut : Nat.card (ggAutomizer J Bs) = 48 := by
    rcases hT with rfl | rfl
    · exact ggAutomizer_card_of_lineJDatum_B3 (p := 3) rfl hD
    · exact ggAutomizer_card_of_lineJDatum_C3 (p := 3) rfl hD
  rcases Nat.lt_or_ge rank 3 with hlt3 | hge3
  · have h27le : 3 ^ 3 ≤ 3 ^ rank := h27.trans hrank0
    have h3r : 3 ≤ rank :=
      (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h27le
    omega
  · have hd4 : 4 ≤ rank + 1 := by omega
    obtain ⟨φ', hφ's, hφ'ker, hdiag, hdvd⟩ :=
      exists_actsDiag_model_of_splitLinear_marking_data hH hpK θ hperfJ hind h27 hd4
    by_cases hrank3 : rank = 3
    · have hZ : Nat.card ↥(Bs ⊓ J ⊓ Subgroup.centralizer (J : Set G)) ≤ 3 :=
        card_bstar_inf_center_le_three_of_scalar_cover (d := rank + 1) (K := K)
          (by omega) (Or.inr (by omega : rank + 1 = 4)) hKcard hpK φ' hφ's hφ'ker
      have hcard := actual_card_eq_factorial_of_model (d := rank + 1) (K := K)
        (by omega) hpK hN0 hH.1.2.1.2.1 hH.1.2.1.2.2.2 hH.2.2.2.1 hZ φ'
        hφ's hφ'ker hdiag
      rw [hAut] at hcard
      have hfac : (rank + 1).factorial = 48 := hcard.symm
      rw [hrank3] at hfac
      norm_num at hfac
    · have hrank4 : 4 ≤ rank := by omega
      have h120 : 120 ∣ Nat.card (ggAutomizer J Bs) := by
        have h5 : 5 ≤ rank + 1 := by omega
        have h120fac : 120 ∣ (rank + 1).factorial := by
          have h5' : Nat.factorial 5 = 120 := by norm_num
          simpa [h5'] using Nat.factorial_dvd_factorial h5
        exact h120fac.trans hdvd
      rw [hAut] at h120
      norm_num at h120

theorem GGResHyp.matched_splitLinear_marking_B2_rank_two
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {Kc : Subgroup G}
    [Fact (Nat.Prime 3)]
    (hH : GGResHyp 3 B Bs x L D J y Kc)
    (hD : GGResLineJDatum 3 Bs J .B2)
    (hMark : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .A ∧ 3 ∣ 2 ^ lab.n - 1) 3 Bs J) :
    ∃ (rank n : ℕ),
      LargeEvenInLambda2 (⟨.A, rank, n⟩ : LargeEvenLabel) ∧
      3 ∣ 2 ^ n - 1 ∧ rank = 2 ∧
      GGHasLabel (⟨.A, rank, n⟩ : LargeEvenLabel) (J ⧸ Subgroup.center J) := by
  classical
  obtain ⟨hperfJ, lab, hΛ, hraw⟩ := hMark
  have hraw0 := hraw
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨_, _, _, _, _, _, _, hS, _, _⟩ := largeEvenRawDatum_exists hraw
  have htag : tag = .A := hS.1
  have h3n : 3 ∣ 2 ^ n - 1 := hS.2
  subst htag
  dsimp only [LargeEvenRawDatum] at hraw
  obtain ⟨K, hKfield, hKfinite, hKcard, hP⟩ := hraw
  obtain ⟨_hsimple, _hnonab, θ, _hS', hN, hind⟩ := hP
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  haveI : CharP K 2 := charP_two_of_card hKcard
  have hpK : 3 ∣ Nat.card K - 1 := by rw [hKcard]; exact h3n
  let hN0 : Bs ≤ Subgroup.normalizer (J : Set G) := GGResHyp.Bs_le_normalizer_J hH
  have hgamma : ggGamma J hN = ggGamma J hN0 := by ext b; rfl
  have hrank : Nat.card (ggGamma J hN).range ≤ 3 ^ rank :=
    card_le_three_pow_rank_of_compatible_splitLinear_marking hH hpK θ hperfJ hN hind
  have hrank0 : Nat.card (ggGamma J hN0).range ≤ 3 ^ rank := by
    rw [← hgamma]
    exact hrank
  have hHas : GGHasLabel (⟨.A, rank, n⟩ : LargeEvenLabel) (J ⧸ Subgroup.center J) := by
    unfold GGHasLabel
    refine largeEvenRawDatum_mono ?_ hraw0
    intro R' _ I' F' hQ
    obtain ⟨-, -, θ', -⟩ := hQ
    exact ⟨θ'⟩
  rcases Nat.lt_or_ge rank 2 with hlt2 | hge2
  · have h1rank : 1 ≤ rank := by simpa using hΛ.2.1
    have hrank1 : rank = 1 := by omega
    have h9N0 : 9 ≤ Nat.card (ggGamma J hN0).range := by
      have h := GGResHyp.sq_le_card_gamma_J (p := 3) hH
      simpa using h
    have h9 : 9 ≤ Nat.card (ggGamma J hN).range := by
      rw [hgamma]
      exact h9N0
    have hle3 : Nat.card (ggGamma J hN).range ≤ 3 := by
      simpa [hrank1] using hrank
    omega
  · rcases Nat.lt_or_ge rank 3 with hlt3 | hge3
    · have hrank2 : rank = 2 := by omega
      exact ⟨rank, n, hΛ, h3n, hrank2, hHas⟩
    · exfalso
      have hd4 : 4 ≤ rank + 1 := by omega
      have h27 :=
        three_cube_le_card_gamma_of_compatible_splitLinear_marking hH hpK hd4 θ
      obtain ⟨_, _, _, _, hdvd⟩ :=
        exists_actsDiag_model_of_splitLinear_marking_data hH hpK θ hperfJ hind h27 hd4
      have hAut8 : Nat.card (ggAutomizer J Bs) = 8 :=
        ggAutomizer_card_of_lineJDatum_B2 (p := 3) rfl hD
      have h24 : 24 ∣ Nat.card (ggAutomizer J Bs) := by
        have h4 : 4 ≤ rank + 1 := by omega
        have h24fac : 24 ∣ (rank + 1).factorial := by
          have h4' : Nat.factorial 4 = 24 := by norm_num
          simpa [h4'] using Nat.factorial_dvd_factorial h4
        exact h24fac.trans hdvd
      rw [hAut8] at h24
      norm_num at h24

open scoped commutatorElement
open Subgroup
open CFSG.Assembly
open CFSG.Open
open CFSG.StandardType

variable {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
  {L D J : Subgroup G} {y : G} {Kc : Subgroup G}
  [Fact (Nat.Prime 3)]

omit [Fact (Nat.Prime 3)] in
theorem commutatorElement_eq_inv_of_conj_eq_central_inv_mul
    {D : Type*} [Group D] {x y s t M : D}
    (hz : ⁅x,y⁆ ∈ Subgroup.center D)
    (hMx : M * x * M⁻¹ = s * x⁻¹)
    (hMy : M * y * M⁻¹ = t * (x * y))
    (hs : s ∈ Subgroup.center D) (ht : t ∈ Subgroup.center D) :
    ⁅x,y⁆ = ⁅x,y⁆⁻¹ := by
  have hyx_eq : ⁅y,x⁆ = ⁅x,y⁆⁻¹ := (commutatorElement_inv x y).symm
  have hyx_cent : ⁅y,x⁆ ∈ Subgroup.center D := by
    rw [hyx_eq]
    exact Subgroup.inv_mem _ hz
  have hyx_comm : Commute ⁅y,x⁆ x := (Subgroup.mem_center_iff.mp hyx_cent x).symm
  have hzy : ⁅x⁻¹,y⁆ = ⁅x,y⁆⁻¹ := by
    rw [commutatorElement_inv_left]
    have hzi : x⁻¹ * ⁅y,x⁆ = ⁅y,x⁆ * x⁻¹ := hyx_comm.inv_right.symm.eq
    rw [hzi, mul_assoc, inv_mul_cancel, mul_one]
    exact hyx_eq
  have hzy_cent : ⁅x⁻¹,y⁆ ∈ Subgroup.center D := by
    rw [hzy]
    exact Subgroup.inv_mem _ hz
  have hconj := conjugate_commutatorElement x y M
  rw [hMx, hMy] at hconj
  have hMz : M * ⁅x,y⁆ * M⁻¹ = ⁅x,y⁆ := by
    have h := Subgroup.mem_center_iff.mp hz M
    calc M * ⁅x,y⁆ * M⁻¹ = (⁅x,y⁆ * M) * M⁻¹ := by rw [h.symm]
      _ = ⁅x,y⁆ := by group
  rw [hMz] at hconj
  have hRHS : ⁅s * x⁻¹, t * (x * y)⁆ = ⁅x,y⁆⁻¹ := by
    have hsx : s * x⁻¹ = x⁻¹ * s := (Subgroup.mem_center_iff.mp hs x⁻¹).symm
    have htx : t * (x * y) = (x * y) * t := (Subgroup.mem_center_iff.mp ht (x * y)).symm
    rw [hsx, htx]
    rw [CFSG.GroupTheory.commutatorElement_mul_center hs ht]
    rw [commutatorElement_mul_right_eq_mul_conj]
    have hxx : ⁅x⁻¹, x⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (Commute.refl x).inv_left
    rw [hxx, one_mul]
    have hconjz : x * ⁅x⁻¹,y⁆ * x⁻¹ = ⁅x⁻¹,y⁆ := by
      have h := Subgroup.mem_center_iff.mp hzy_cent x
      calc x * ⁅x⁻¹,y⁆ * x⁻¹ = (⁅x⁻¹,y⁆ * x) * x⁻¹ := by rw [h.symm]
        _ = ⁅x⁻¹,y⁆ := by group
    rw [hconjz, hzy]
  exact hconj.trans hRHS


theorem b2_coroot_closure_of_data
    (hH : GGResHyp 3 B Bs x L D J y Kc)
    (hD : GGResLineJDatum 3 Bs J .B2)
    {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (h3n : 3 ∣ 2 ^ n - 1) (hKcard : Nat.card K = 2 ^ n)
    (θ : J ⧸ Subgroup.center J ≃*
      LargeEvenProj (LargeEvenSLGroup (Fin 3) K))
    (hperfJ : commutator J = ⊤)
    (hN : Bs ≤ Subgroup.normalizer (J : Set G))
    (hX9 : Nat.card (TypeA.inducedSub (ggQuotHom θ)
      (ggGamma J (GGResHyp.Bs_le_normalizer_J hH)).range) = 9) :
    ∃ (r : Fin GGResLineJType.B2.rank → MulAut ↥Bs) (eG : Fin 2 → G)
      (φ : Fin 2 → MulAut (LargeEvenProj (LargeEvenSLGroup (Fin 3) K))),
      (∀ i, eG i ∈ Bs ⊓ J) ∧
      (∀ i, ∀ hb : eG i ∈ Bs, φ i = ggLAut J θ ⟨eG i, hN hb⟩) ∧
      (∀ i j, φ i * φ j = φ j * φ i) ∧
      (∀ hb1 : eG 1 ∈ Bs,
        r ⟨1, by decide⟩ ⟨eG 1, hb1⟩ = ⟨eG 1, hb1⟩⁻¹) ∧
      (∀ (hb0 : eG 0 ∈ Bs) (hb1 : eG 1 ∈ Bs),
        r ⟨1, by decide⟩ ⟨eG 0, hb0⟩ = ⟨eG 1, hb1⟩ * ⟨eG 0, hb0⟩) ∧
      ggAutomizer J Bs = Subgroup.closure (Set.range r) ∧
      TypeA.inducedSub (ggQuotHom θ)
        (ggGamma J (GGResHyp.Bs_le_normalizer_J hH)).range =
        Subgroup.closure (Set.range φ) := by
  classical
  let U : Subgroup (GL (Fin 3) K) := LargeEvenSLGroup (Fin 3) K
  let R : Type := LargeEvenProj U
  let ψ : J →* R := ggQuotHom θ
  let A : Subgroup (MulAut ↥J) := (ggGamma J hN).range
  let X : Subgroup (MulAut R) := TypeA.inducedSub ψ A
  obtain ⟨V, instA, instM, ι, r, hvec, α, hform, hrefl, hpair, hindep, hgenLine⟩ := hD
  letI : AddCommGroup V := instA
  letI : Module (ZMod 3) V := instM
  have hpK : 3 ∣ Nat.card K - 1 := by rw [hKcard]; exact h3n
  have hdet : (CartanMatrix.B 2).det = 2 := by
    simpa using CartanMatrix.B_det (by norm_num : 0 < 2)
  have hC : ∀ c : Fin 2 → ZMod 3,
      (∀ j, ∑ l, (CartanMatrix.B 2 j l : ZMod 3) * c l = 0) → c = 0 :=
    CFSG.StandardType.ker_zero_of_det_two hdet
  have hdiag : ∀ j : Fin GGResLineJType.B2.rank,
      (GGResLineJType.cartan .B2 j j : ZMod 3) = 2 := by
    intro j
    fin_cases j <;> rfl
  have hα2 : ∀ j : Fin GGResLineJType.B2.rank, α j (hvec j) = 2 := by
    intro j
    rw [hpair j j, hdiag j]
  let W : Submodule (ZMod 3) V := Submodule.span (ZMod 3) (Set.range hvec)
  let E : Subgroup G := ggSpanSub ι W
  have hEprops := GGResLineJDatum.coroot_span_subgroup_properties_of_cartan
    (G := G) (Bs := Bs) (J := J) (k := 2) (V := V) hN ι r hvec α
    (CartanMatrix.B 2) hform hα2 hpair hindep hC hgenLine W rfl
  have hEcard : Nat.card E = 9 := by
    simpa [E, show 3 ^ 2 = 9 by norm_num] using hEprops.2.2.1
  have hEbot : E ⊓ Subgroup.centralizer (J : Set G) = ⊥ := hEprops.2.2.2
  have hE_Bs : E ≤ Bs := hEprops.1.trans inf_le_left
  have hE_J : E ≤ J := hEprops.1.trans inf_le_right
  have hE_N : E ≤ Subgroup.normalizer (J : Set G) := hE_Bs.trans hN
  let eB : Fin 2 → ↥Bs := fun i => Additive.toMul (ι.symm (hvec i))
  let eG : Fin 2 → G := fun i => (eB i : G)
  let eE : Fin 2 → E := fun i => ⟨eG i, by
    rw [show E = ggSpanSub ι W from rfl]
    exact mem_ggSpanSub.mpr ⟨hvec i, Submodule.subset_span (Set.mem_range_self i), by simp [eG, eB]⟩⟩
  have heE : ∀ i, eG i ∈ E := by
    intro i
    rw [show E = ggSpanSub ι W from rfl]
    exact mem_ggSpanSub.mpr ⟨hvec i, Submodule.subset_span (Set.mem_range_self i), by simp [eG, eB]⟩
  have heJ : ∀ i, eG i ∈ J := fun i => hE_J (heE i)
  have heN : ∀ i, eG i ∈ Subgroup.normalizer (J : Set G) := fun i => hN (eB i).2
  let φ : Fin 2 → MulAut R := fun i => ggLAut J θ ⟨eG i, heN i⟩
  have hφX : ∀ i, φ i ∈ X := by
    intro i
    refine TypeA.mem_inducedSub.mpr ⟨ggGamma J hN (eB i), ⟨eB i, rfl⟩, ?_⟩
    intro l
    simpa [φ, eG, ggBeta, Subgroup.inclusion] using ggBeta_ggQuotHom J hN θ (eB i) l
  have hEgen : E = Subgroup.closure (Set.range eG) := by
    apply le_antisymm
    · refine ggSpanSub_le (p := 3) (hv := hvec) ι ?_
      intro j
      exact Subgroup.subset_closure ⟨j, rfl⟩
    · refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨i, rfl⟩
      exact heE i
  let φE : E →* MulAut R := (ggLAut J θ).comp (Subgroup.inclusion hE_N)
  have hφE_inj : Function.Injective φE := by
    refine (injective_iff_map_eq_one φE).mpr ?_
    intro a ha
    have haut : ggLAut J θ (⟨a, hE_N a.2⟩ : Subgroup.normalizer (J : Set G)) = 1 := by
      simpa [φE, Subgroup.inclusion] using ha
    have hcent : (a : G) ∈ Subgroup.centralizer (J : Set G) :=
      mem_centralizer_of_ggLAut_eq_one (L := J) (θ := θ) hperfJ haut
    have hbot : (a : G) ∈ E ⊓ Subgroup.centralizer (J : Set G) := ⟨a.2, hcent⟩
    rw [hEbot] at hbot
    have h1 : (a : G) = 1 := Subgroup.mem_bot.mp hbot
    exact Subtype.ext h1
  have hφE_card : Nat.card φE.range = 9 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hφE_inj).toEquiv]
    exact hEcard
  have hφE_range : φE.range = Subgroup.closure (Set.range φ) := by
    apply le_antisymm
    · rintro _ ⟨a, rfl⟩
      have hEgen' : (⊤ : Subgroup E) = Subgroup.closure (Set.range eE) := by
        apply Subgroup.map_injective (Subgroup.subtype_injective E)
        rw [Subgroup.map_top, Subgroup.range_subtype, MonoidHom.map_closure]
        convert hEgen using 2
        ext x
        constructor
        · rintro ⟨e, ⟨i, rfl⟩, rfl⟩
          exact ⟨i, rfl⟩
        · rintro ⟨i, rfl⟩
          exact ⟨eE i, ⟨i, rfl⟩, rfl⟩
      have hpre : (⊤ : Subgroup E) ≤ (Subgroup.closure (Set.range φ)).comap φE := by
        rw [hEgen']
        refine (Subgroup.closure_le _).mpr ?_
        rintro _ ⟨i, rfl⟩
        exact Subgroup.subset_closure ⟨i, congrArg (ggLAut J θ) (Subtype.ext rfl)⟩
      exact hpre (Subgroup.mem_top a)
    · refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨i, rfl⟩
      exact ⟨eE i, (congrArg (ggLAut J θ) (Subtype.ext rfl)).symm⟩
  have hιe : ∀ i, ι (Additive.ofMul (eB i)) = hvec i := by
    intro i
    simp [eB]
  let j0 : Fin GGResLineJType.B2.rank := ⟨0, by decide⟩
  let j1 : Fin GGResLineJType.B2.rank := ⟨1, by decide⟩
  have hr1e1 : ∀ hb1 : eG 1 ∈ Bs,
      r j1 ⟨eG 1, hb1⟩ = ⟨eG 1, hb1⟩⁻¹ := by
    intro hb1
    rw [ggLin_inv_iff (p := 3) (ι := ι) (φ := r j1) (b := ⟨eG 1, hb1⟩)]
    rw [show ι (Additive.ofMul ⟨eG 1, hb1⟩) = hvec j1 by
      rw [show (⟨eG 1, hb1⟩ : ↥Bs) = eB 1 by apply Subtype.ext; rfl, hιe 1]
      rfl]
    rw [hform j1, hα2 j1]
    module
  have hr1e0 : ∀ (hb0 : eG 0 ∈ Bs) (hb1 : eG 1 ∈ Bs),
      r j1 ⟨eG 0, hb0⟩ = ⟨eG 1, hb1⟩ * ⟨eG 0, hb0⟩ := by
    intro hb0 hb1
    apply Additive.ofMul.injective
    apply ι.injective
    rw [← ggLin_apply_ofMul (p := 3) (ι := ι) (φ := r j1) (b := ⟨eG 0, hb0⟩)]
    rw [show ι (Additive.ofMul ⟨eG 0, hb0⟩) = hvec j0 by
      rw [show (⟨eG 0, hb0⟩ : ↥Bs) = eB 0 by apply Subtype.ext; rfl, hιe 0]
      rfl]
    rw [hform j1, hpair j1 j0]
    have hC : (GGResLineJType.B2.cartan j1 j0 : ZMod 3) = -1 := by
      show (CartanMatrix.B 2 1 0 : ZMod 3) = -1
      rfl
    rw [hC]
    change hvec j0 - -(1 : ZMod 3) • hvec j1 =
      ι (Additive.ofMul ⟨eG 1, hb1⟩ + Additive.ofMul ⟨eG 0, hb0⟩)
    rw [map_add]
    rw [show ι (Additive.ofMul ⟨eG 1, hb1⟩) = hvec j1 by
      rw [show (⟨eG 1, hb1⟩ : ↥Bs) = eB 1 by apply Subtype.ext; rfl, hιe 1]
      rfl]
    rw [show ι (Additive.ofMul ⟨eG 0, hb0⟩) = hvec j0 by
      rw [show (⟨eG 0, hb0⟩ : ↥Bs) = eB 0 by apply Subtype.ext; rfl, hιe 0]
      rfl]
    module
  have hφcomm : ∀ i j, φ i * φ j = φ j * φ i := by
    intro i j
    have hcommE : eE i * eE j = eE j * eE i :=
      hEprops.2.1.1.is_comm.comm (eE i) (eE j)
    have := congrArg φE hcommE
    rw [map_mul, map_mul] at this
    simpa [φE, φ, eE, Subgroup.inclusion] using this
  refine ⟨r, eG, φ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; exact ⟨(hEprops.1 (heE i)).1, heJ i⟩
  · intro i hb
    exact congrArg (ggLAut J θ) (Subtype.ext rfl)
  · exact hφcomm
  · exact hr1e1
  · exact hr1e0
  · exact hgenLine
  · have hEq : φE.range = X := by
      apply Subgroup.eq_of_le_of_card_ge
      · rw [hφE_range]
        refine (Subgroup.closure_le _).mpr ?_
        rintro _ ⟨i, rfl⟩
        exact hφX i
      · rw [hφE_card, hX9]
    change X = Subgroup.closure (Set.range φ)
    rw [← hEq, hφE_range]


section B2Endpoint

omit [Fact (Nat.Prime 3)] in
theorem isMulCommutative_of_map_eq_range
    {S Q : Type*} [Group S] [Group Q] (ρ : S →* Q)
    (P : Subgroup S) (hmap : P.map ρ = ρ.range)
    (hker : ρ.ker ≤ Subgroup.center S) (hP : IsMulCommutative P) :
    IsMulCommutative S := by
  refine ⟨⟨fun a b => ?_⟩⟩
  apply commutatorElement_eq_one_iff_mul_comm.mp
  have ha : ρ a ∈ ρ.range := ⟨a, rfl⟩
  rw [← hmap] at ha
  obtain ⟨p, hp, hpa⟩ := Subgroup.mem_map.mp ha
  have hb : ρ b ∈ ρ.range := ⟨b, rfl⟩
  rw [← hmap] at hb
  obtain ⟨q, hq, hqb⟩ := Subgroup.mem_map.mp hb
  let z : S := p⁻¹ * a
  let w : S := q⁻¹ * b
  have hzker : z ∈ ρ.ker := by
    rw [MonoidHom.mem_ker]
    dsimp [z]
    rw [map_mul, map_inv, hpa]
    simp
  have hwker : w ∈ ρ.ker := by
    rw [MonoidHom.mem_ker]
    dsimp [w]
    rw [map_mul, map_inv, hqb]
    simp
  have hzcent : z ∈ Subgroup.center S := hker hzker
  have hwcent : w ∈ Subgroup.center S := hker hwker
  have haeq : a = p * z := by dsimp [z]; group
  have hbeq : b = q * w := by dsimp [w]; group
  calc
    ⁅a, b⁆ = ⁅p * z, q * w⁆ := by rw [haeq, hbeq]
    _ = ⁅p, q⁆ := CFSG.GroupTheory.commutatorElement_mul_center hzcent hwcent
    _ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (congrArg Subtype.val (hP.is_comm.comm ⟨p, hp⟩ ⟨q, hq⟩))

theorem actual_B2_core
    (hH : GGResHyp 3 B Bs x L D J y Kc)
    (hD : GGResLineJDatum 3 Bs J .B2)
    (hMark : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .A ∧ 3 ∣ 2 ^ lab.n - 1) 3 Bs J)
    (hZ : Nat.card ↥(Bs ⊓ J ⊓ Subgroup.centralizer (J : Set G)) ≤ 3) :
    False := by
  classical
  obtain ⟨hperfJ, lab, hΛ, hraw⟩ := hMark
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨_, _, _, _, _, _, _, hS, _, _⟩ := largeEvenRawDatum_exists hraw
  have htag : tag = .A := hS.1
  have h3n : 3 ∣ 2 ^ n - 1 := hS.2
  subst htag
  dsimp only [LargeEvenRawDatum] at hraw
  obtain ⟨K, hKfield, hKfinite, hKcard, hP⟩ := hraw
  obtain ⟨_hsimple, _hnonab, θ, _hS', hN, hind⟩ := hP
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  haveI : CharP K 2 := charP_two_of_card hKcard
  have hpK : 3 ∣ Nat.card K - 1 := by rw [hKcard]; exact h3n
  let hN0 : Bs ≤ Subgroup.normalizer (J : Set G) := GGResHyp.Bs_le_normalizer_J hH
  have hgamma : ggGamma J hN = ggGamma J hN0 := by ext b; rfl
  have hrank : Nat.card (ggGamma J hN).range ≤ 3 ^ rank :=
    card_le_three_pow_rank_of_compatible_splitLinear_marking hH hpK θ hperfJ hN hind
  have hrank0 : Nat.card (ggGamma J hN0).range ≤ 3 ^ rank := by
    rw [← hgamma]; exact hrank
  have h9N0 : 9 ≤ Nat.card (ggGamma J hN0).range := by
    simpa using GGResHyp.sq_le_card_gamma_J (p := 3) hH
  have h9 : 9 ≤ Nat.card (ggGamma J hN).range := by
    rw [hgamma]; exact h9N0
  have hrank_ge_two : 2 ≤ rank := by
    by_contra hlt
    have hrank1 : rank = 1 := by
      have h1 : 1 ≤ rank := by simpa using hΛ.2.1
      omega
    have hle3 : Nat.card (ggGamma J hN).range ≤ 3 := by
      simpa [hrank1] using hrank
    omega
  have hrank_le_two : rank ≤ 2 := by
    by_contra hlt
    have hge3 : 3 ≤ rank := by omega
    have hd4 : 4 ≤ rank + 1 := by omega
    have h27 := three_cube_le_card_gamma_of_compatible_splitLinear_marking hH hpK hd4 θ
    obtain ⟨_, _, _, _, hdvd⟩ :=
      exists_actsDiag_model_of_splitLinear_marking_data hH hpK θ hperfJ hind h27 hd4
    have hAut8 : Nat.card (ggAutomizer J Bs) = 8 :=
      ggAutomizer_card_of_lineJDatum_B2 (p := 3) rfl hD
    have h24 : 24 ∣ Nat.card (ggAutomizer J Bs) := by
      have h4 : 4 ≤ rank + 1 := by omega
      have h24fac : 24 ∣ (rank + 1).factorial := by
        have h4' : Nat.factorial 4 = 24 := by norm_num
        simpa [h4'] using Nat.factorial_dvd_factorial h4
      exact h24fac.trans hdvd
    rw [hAut8] at h24
    norm_num at h24
  have hrank2 : rank = 2 := by omega
  subst rank
  have hA9 : Nat.card (ggGamma J hN0).range = 9 := by
    have hle9 : Nat.card (ggGamma J hN0).range ≤ 9 := by
      simpa using hrank0
    omega
  let U : Subgroup (GL (Fin 3) K) := LargeEvenSLGroup (Fin 3) K
  let R : Type := LargeEvenProj U
  let ψ : J →* R := ggQuotHom θ
  let A : Subgroup (MulAut ↥J) := (ggGamma J hN0).range
  let X : Subgroup (MulAut R) := TypeA.inducedSub ψ A
  have hAI : ∀ a ∈ A, ∃ φ : MulAut R, ∀ l : ↥J, φ (ψ l) = ψ (a l) := by
    rintro a ⟨b, rfl⟩
    obtain ⟨φ, _hφI, hφ⟩ := hind b⁻¹ (inv_mem b.2)
    refine ⟨φ, fun l => ?_⟩
    have h := hφ l (ggGamma J hN0 b l) ?_
    · change φ (θ (QuotientGroup.mk l)) = θ (QuotientGroup.mk (ggGamma J hN0 b l))
      simpa [ggGamma_coe] using h
    · simp [ggGamma_coe]
  have hX9 : Nat.card X = 9 := by
    change Nat.card (TypeA.inducedSub ψ A) = 9
    rw [TypeA.card_inducedSub (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hperfJ hAI]
    exact hA9
  obtain ⟨r, eG, φ, hmem, hφdef, hφcomm, hr1e1, hr1e0, hgenLine, hXclosure⟩ :=
    b2_coroot_closure_of_data hH hD h3n hKcard θ hperfJ hN0 hX9
  let Dpre : Subgroup (Subgroup.normalizer (U : Set (GL (Fin 3) K))) :=
    fullMatrixPreimage U ψ A
  let ρD : Dpre →* MulAut R := (TableB.projConj U).comp Dpre.subtype
  have hφX : ∀ i, φ i ∈ X := by
    intro i
    change φ i ∈ TypeA.inducedSub ψ A
    rw [hXclosure]
    exact Subgroup.subset_closure ⟨i, rfl⟩
  choose ui hui using fun i =>
    QuotientGroup.mk'_surjective ((LargeEvenScalars (Fin 3) K).subgroupOf U)
      (ggQuotHom θ ⟨eG i, (hmem i).2⟩)
  let MNi : Fin 2 → Subgroup.normalizer (U : Set (GL (Fin 3) K)) :=
    fun i => ⟨ui i, Subgroup.le_normalizer (ui i).2⟩
  have hMNiEq : ∀ i, φ i = TableB.projConj U (MNi i) := by
    intro i
    rw [hφdef i (hmem i).1]
    ext x
    obtain ⟨q, rfl⟩ := θ.surjective x
    induction q using QuotientGroup.induction_on with
    | H l =>
      change ggLAut J θ ⟨eG i, hN0 (hmem i).1⟩ (θ (QuotientGroup.mk l)) =
        TableB.projConj U (MNi i) (θ (QuotientGroup.mk l))
      have hpc : TableB.projConj U (MNi i) (θ (QuotientGroup.mk l)) =
          ggQuotHom θ (⟨eG i, (hmem i).2⟩ * l * ⟨eG i, (hmem i).2⟩⁻¹) := by
        simpa [U, MNi, ggQuotHom] using
          (TableB.projConj_of_eq (ψ := ggQuotHom θ) (hui i) l)
      have hnorm : ((J.normalizerMonoidHom ⟨eG i, hN0 (hmem i).1⟩) l : ↥J) =
          ⟨eG i, (hmem i).2⟩ * l * ⟨eG i, (hmem i).2⟩⁻¹ := by
        apply Subtype.ext
        simpa using normalizerMonoidHom_coe (L := J) ⟨eG i, hN0 (hmem i).1⟩ l
      rw [hpc, ggLAut_apply, hnorm]
      rfl
  let XiD : Fin 2 → Dpre := fun i => ⟨MNi i, by
    change TableB.projConj U (MNi i) ∈ TypeA.inducedSub ψ A
    rw [← hMNiEq i]
    exact hφX i⟩
  have hXiρ : ∀ i, ρD (XiD i) = φ i := by
    intro i
    exact (hMNiEq i).symm
  let eB : Fin 2 → ↥Bs := fun i => ⟨eG i, (hmem i).1⟩
  let j1 : Fin GGResLineJType.B2.rank := ⟨1, by decide⟩
  have hr1 : r j1 ∈ ggAutomizer J Bs := by
    rw [hgenLine]
    exact Subgroup.subset_closure ⟨j1, rfl⟩
  obtain ⟨n0, hn0J, hn0N, hn0act⟩ := mem_ggAutomizer_iff.mp hr1
  have hn0Nf : ∀ b ∈ Bs, n0 * (b : G) * n0⁻¹ ∈ Bs :=
    fun b hb => ((Subgroup.mem_normalizer_iff.mp hn0N) b).mp hb
  have hn0if : ∀ b ∈ Bs, n0⁻¹ * (b : G) * n0 ∈ Bs := by
    intro b hb
    have h := ((Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn0N)) b).mp hb
    simpa using h
  have hn0Nj : n0 ∈ Subgroup.normalizer (J : Set G) := by
    refine (Subgroup.mem_normalizer_iff).mpr ?_
    intro j
    constructor
    · intro hj
      exact J.mul_mem (J.mul_mem hn0J hj) (J.inv_mem hn0J)
    · intro hj
      have hjeq : j = n0⁻¹ * (n0 * j * n0⁻¹) * n0 := by group
      rw [hjeq]
      exact J.mul_mem (J.mul_mem (J.inv_mem hn0J) hj) hn0J
  obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective
    ((LargeEvenScalars (Fin 3) K).subgroupOf U) (ggQuotHom θ ⟨n0, hn0J⟩)
  let MN0 : Subgroup.normalizer (U : Set (GL (Fin 3) K)) :=
    ⟨u, Subgroup.le_normalizer u.2⟩
  have hMproj : TableB.projConj U MN0 = ggLAut J θ ⟨n0, hn0Nj⟩ := by
    ext x
    obtain ⟨q, rfl⟩ := θ.surjective x
    induction q using QuotientGroup.induction_on with
    | H l =>
      change TableB.projConj U MN0 (θ (QuotientGroup.mk l)) =
        ggLAut J θ ⟨n0, hn0Nj⟩ (θ (QuotientGroup.mk l))
      have hpc : TableB.projConj U MN0 (θ (QuotientGroup.mk l)) =
          ggQuotHom θ (⟨n0, hn0J⟩ * l * ⟨n0, hn0J⟩⁻¹) := by
        simpa [U, MN0, ggQuotHom] using
          (TableB.projConj_of_eq (ψ := ggQuotHom θ) hu l)
      have hnorm : ((J.normalizerMonoidHom ⟨n0, hn0Nj⟩) l : ↥J) =
          ⟨n0, hn0J⟩ * l * ⟨n0, hn0J⟩⁻¹ := by
        apply Subtype.ext
        simpa using normalizerMonoidHom_coe (L := J) ⟨n0, hn0Nj⟩ l
      rw [hpc, ggLAut_apply, hnorm]
      rfl
  have hl : MulAut.conj (⟨n0, hn0J⟩ : ↥J) ∈ Subgroup.normalizer (A : Set (MulAut ↥J)) := by
    refine (Subgroup.mem_normalizer_iff).mpr ?_
    intro a
    constructor
    · rintro ⟨b, rfl⟩
      refine ⟨⟨n0 * (b : G) * n0⁻¹, hn0Nf b b.2⟩, ?_⟩
      exact ggGamma_conj J hN0 ⟨n0, hn0J⟩ b (hn0Nf b b.2)
    · rintro ⟨b, hb⟩
      have hnb : ((⟨n0⁻¹, J.inv_mem hn0J⟩ : ↥J) : G) * (b : G) *
          ((⟨n0⁻¹, J.inv_mem hn0J⟩ : ↥J) : G)⁻¹ ∈ Bs := by
        simpa using hn0if b b.2
      refine ⟨⟨((⟨n0⁻¹, J.inv_mem hn0J⟩ : ↥J) : G) * (b : G) *
          ((⟨n0⁻¹, J.inv_mem hn0J⟩ : ↥J) : G)⁻¹, hnb⟩, ?_⟩
      have hγ := ggGamma_conj J hN0 ⟨n0⁻¹, J.inv_mem hn0J⟩ b hnb
      have hcj : MulAut.conj (⟨n0⁻¹, J.inv_mem hn0J⟩ : ↥J) =
          (MulAut.conj (⟨n0, hn0J⟩ : ↥J))⁻¹ := by
        ext x
        simp [MulAut.conj_apply]
      rw [hγ, hb, hcj]
      simp only [inv_inv]
      calc
        (MulAut.conj (⟨n0, hn0J⟩ : ↥J))⁻¹ *
            (MulAut.conj (⟨n0, hn0J⟩ : ↥J) * a *
              (MulAut.conj (⟨n0, hn0J⟩ : ↥J))⁻¹) *
            MulAut.conj (⟨n0, hn0J⟩ : ↥J)
            = (MulAut.conj (⟨n0, hn0J⟩ : ↥J))⁻¹ *
                MulAut.conj (⟨n0, hn0J⟩ : ↥J) * a *
                (MulAut.conj (⟨n0, hn0J⟩ : ↥J))⁻¹ *
                MulAut.conj (⟨n0, hn0J⟩ : ↥J) := by
              simp only [mul_assoc]
        _ = a := by simp
  have hconjD : ∀ d ∈ Dpre, MN0 * d * MN0⁻¹ ∈ Dpre := by
    intro d hd
    change TableB.projConj U (MN0 * d * MN0⁻¹) ∈ X
    rw [map_mul, map_mul, map_inv]
    let dN : Subgroup.normalizer (U : Set (GL (Fin 3) K)) := d
    have hd' : TableB.projConj U dN ∈ X := hd
    exact TableB.projConj_normalizes_inducedSub (d := 3) (K := K) (U := U)
      (L' := J) (ψ := ψ) (A := A) (u := u) (l := ⟨n0, hn0J⟩) hl hu
      (TableB.projConj U dN) hd'
  let Mconj : Fin 2 → Dpre := fun i =>
    ⟨MN0 * XiD i * MN0⁻¹, hconjD (XiD i) (XiD i).2⟩
  have hconjρ : ∀ i, ρD (Mconj i) = ggLAut J θ ⟨n0, hn0Nj⟩ * φ i *
      (ggLAut J θ ⟨n0, hn0Nj⟩)⁻¹ := by
    intro i
    change TableB.projConj U (MN0 * (XiD i).1 * MN0⁻¹) = _
    rw [map_mul, map_mul, map_inv, hMproj]
    rw [show TableB.projConj U (XiD i).1 = φ i from hXiρ i]
  have hb1 : (⟨n0, hn0Nj⟩ * ⟨eG 1, hN0 (hmem 1).1⟩ * ⟨n0, hn0Nj⟩⁻¹ :
      Subgroup.normalizer (J : Set G)) =
      ⟨((r j1 (eB 1) : ↥Bs) : G), hN0 (r j1 (eB 1)).2⟩ := by
    apply Subtype.ext
    simpa [eB] using (hn0act (eB 1)).symm
  have hb0 : (⟨n0, hn0Nj⟩ * ⟨eG 0, hN0 (hmem 0).1⟩ * ⟨n0, hn0Nj⟩⁻¹ :
      Subgroup.normalizer (J : Set G)) =
      ⟨((r j1 (eB 0) : ↥Bs) : G), hN0 (r j1 (eB 0)).2⟩ := by
    apply Subtype.ext
    simpa [eB] using (hn0act (eB 0)).symm
  have hMconj1 : ρD (Mconj 1) = (φ 1)⁻¹ := by
    rw [hconjρ 1, hφdef 1 (hmem 1).1]
    rw [ggLAut_conj (L := J) (θ := θ) (g := ⟨n0, hn0Nj⟩)
      (b := ⟨eG 1, hN0 (hmem 1).1⟩)]
    rw [hb1]
    rw [hr1e1 (hmem 1).1]
    rw [show (⟨(((eB 1)⁻¹ : ↥Bs) : G), hN0 ((eB 1)⁻¹).2⟩ :
        Subgroup.normalizer (J : Set G)) = ⟨eG 1, hN0 (hmem 1).1⟩⁻¹ by
      apply Subtype.ext
      rfl]
    rw [map_inv]
  have hMconj0 : ρD (Mconj 0) = φ 1 * φ 0 := by
    rw [hconjρ 0]
    rw [hφdef 1 (hmem 1).1, hφdef 0 (hmem 0).1]
    rw [ggLAut_conj (L := J) (θ := θ) (g := ⟨n0, hn0Nj⟩)
      (b := ⟨eG 0, hN0 (hmem 0).1⟩)]
    rw [hb0]
    rw [hr1e0 (hmem 0).1 (hmem 1).1]
    rw [show (⟨(((eB 1 * eB 0 : ↥Bs) : G)), hN0 (eB 1 * eB 0).2⟩ :
        Subgroup.normalizer (J : Set G)) =
        ⟨eG 1, hN0 (hmem 1).1⟩ * ⟨eG 0, hN0 (hmem 0).1⟩ by
      apply Subtype.ext
      rfl]
    rw [map_mul]
  have hscal : (TableB.projConj U).ker ≤ (LargeEvenScalars (Fin 3) K).subgroupOf
      (Subgroup.normalizer (U : Set (GL (Fin 3) K))) := by
    intro X hX
    exact Subgroup.mem_subgroupOf.mpr
      (CFSG.LocalAnalysis.GLTheoremA.T171Sh.linKernelScalar_of_three_le (by norm_num : 3 ≤ 3) X hX)
  let sD : Dpre := Mconj 1 * XiD 1
  let tD : Dpre := Mconj 0 * (XiD 1 * XiD 0)⁻¹
  have hsDρ : ρD sD = 1 := by
    change ρD (Mconj 1 * XiD 1) = 1
    rw [map_mul, hMconj1, hXiρ 1]
    simp
  have htDρ : ρD tD = 1 := by
    change ρD (Mconj 0 * (XiD 1 * XiD 0)⁻¹) = 1
    rw [map_mul, map_inv, map_mul, hMconj0, hXiρ 1, hXiρ 0]
    simp
  have hs_scal : (sD : GL (Fin 3) K) ∈ LargeEvenScalars (Fin 3) K := by
    exact Subgroup.mem_subgroupOf.mp
      (hscal (by simpa [ρD] using hsDρ))
  have ht_scal : (tD : GL (Fin 3) K) ∈ LargeEvenScalars (Fin 3) K := by
    exact Subgroup.mem_subgroupOf.mp
      (hscal (by simpa [ρD] using htDρ))
  have hs_center : (sD : GL (Fin 3) K) ∈ Subgroup.center (GL (Fin 3) K) :=
    TableB.scalars_le_center hs_scal
  have ht_center : (tD : GL (Fin 3) K) ∈ Subgroup.center (GL (Fin 3) K) :=
    TableB.scalars_le_center ht_scal
  have hEq1 : (MN0 : GL (Fin 3) K) * (XiD 1 : GL (Fin 3) K) * (MN0 : GL (Fin 3) K)⁻¹ =
      (sD : GL (Fin 3) K) * (XiD 1 : GL (Fin 3) K)⁻¹ := by
    have h : (sD : GL (Fin 3) K) * (XiD 1 : GL (Fin 3) K)⁻¹ =
        (MN0 : GL (Fin 3) K) * (XiD 1 : GL (Fin 3) K) * (MN0 : GL (Fin 3) K)⁻¹ := by
      simp [sD, Mconj, mul_assoc]
    exact h.symm
  have hEq0 : (MN0 : GL (Fin 3) K) * (XiD 0 : GL (Fin 3) K) * (MN0 : GL (Fin 3) K)⁻¹ =
      (tD : GL (Fin 3) K) * ((XiD 1 : GL (Fin 3) K) * (XiD 0 : GL (Fin 3) K)) := by
    have h : (tD : GL (Fin 3) K) * ((XiD 1 : GL (Fin 3) K) * (XiD 0 : GL (Fin 3) K)) =
        (MN0 : GL (Fin 3) K) * (XiD 0 : GL (Fin 3) K) * (MN0 : GL (Fin 3) K)⁻¹ := by
      simp [tD, Mconj, mul_assoc]
    exact h.symm
  let zN : Subgroup.normalizer (U : Set (GL (Fin 3) K)) :=
    ⁅(XiD 1 : Subgroup.normalizer (U : Set (GL (Fin 3) K))),
      (XiD 0 : Subgroup.normalizer (U : Set (GL (Fin 3) K)))⁆
  have hzNρ : TableB.projConj U zN = 1 := by
    change TableB.projConj U ⁅(XiD 1 : Subgroup.normalizer (U : Set (GL (Fin 3) K))),
      (XiD 0 : Subgroup.normalizer (U : Set (GL (Fin 3) K)))⁆ = 1
    rw [map_commutatorElement]
    rw [show TableB.projConj U (XiD 1 : Subgroup.normalizer (U : Set (GL (Fin 3) K))) = φ 1 from hXiρ 1,
      show TableB.projConj U (XiD 0 : Subgroup.normalizer (U : Set (GL (Fin 3) K))) = φ 0 from hXiρ 0]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hφcomm 1 0)
  have hz_scal : (zN : GL (Fin 3) K) ∈ LargeEvenScalars (Fin 3) K :=
    Subgroup.mem_subgroupOf.mp (hscal hzNρ)
  have hz_center : (zN : GL (Fin 3) K) ∈ Subgroup.center (GL (Fin 3) K) :=
    TableB.scalars_le_center hz_scal
  have hzNco : (zN : GL (Fin 3) K) =
      ⁅((XiD 1 : Subgroup.normalizer (U : Set (GL (Fin 3) K))) : GL (Fin 3) K),
        ((XiD 0 : Subgroup.normalizer (U : Set (GL (Fin 3) K))) : GL (Fin 3) K)⁆ := rfl
  have hz_center' : ⁅((XiD 1 : Subgroup.normalizer (U : Set (GL (Fin 3) K))) : GL (Fin 3) K),
      ((XiD 0 : Subgroup.normalizer (U : Set (GL (Fin 3) K))) : GL (Fin 3) K)⁆ ∈
      Subgroup.center (GL (Fin 3) K) := by
    rwa [hzNco] at hz_center
  have hz_inv : ⁅((XiD 1 : Subgroup.normalizer (U : Set (GL (Fin 3) K))) : GL (Fin 3) K),
      ((XiD 0 : Subgroup.normalizer (U : Set (GL (Fin 3) K))) : GL (Fin 3) K)⁆ =
      ⁅((XiD 1 : Subgroup.normalizer (U : Set (GL (Fin 3) K))) : GL (Fin 3) K),
      ((XiD 0 : Subgroup.normalizer (U : Set (GL (Fin 3) K))) : GL (Fin 3) K)⁆⁻¹ :=
    commutatorElement_eq_inv_of_conj_eq_central_inv_mul hz_center' hEq1 hEq0 hs_center ht_center
  have hzN_eq : (zN : GL (Fin 3) K) = (zN : GL (Fin 3) K)⁻¹ := by
    simpa [hzNco] using hz_inv
  have hz2 : (zN : GL (Fin 3) K) ^ 2 = 1 := by
    calc (zN : GL (Fin 3) K) ^ 2 = (zN : GL (Fin 3) K) * (zN : GL (Fin 3) K) := pow_two _
      _ = (zN : GL (Fin 3) K) * (zN : GL (Fin 3) K)⁻¹ :=
        congrArg (fun w => (zN : GL (Fin 3) K) * w) hzN_eq
      _ = 1 := mul_inv_cancel _
  have hn1 : 1 ≤ n := by
    by_contra h
    have hn0 : n = 0 := by omega
    rw [hn0, pow_zero] at hKcard
    have hK2 : 1 < Nat.card K := by
      letI : Fintype K := Fintype.ofFinite K
      simpa [Nat.card_eq_fintype_card] using (Fintype.one_lt_card (α := K))
    omega
  have hScalOdd : Odd (Nat.card ((LargeEvenScalars (Fin 3) K).subgroupOf
      (Subgroup.normalizer (U : Set (GL (Fin 3) K))))) :=
    CFSG.LocalAnalysis.GLTheoremA.FQ.scalars_subgroupOf_odd
      (ι := Fin 3) (K := K) hn1 hKcard _
  have hz_mem_sub : zN ∈ (LargeEvenScalars (Fin 3) K).subgroupOf
      (Subgroup.normalizer (U : Set (GL (Fin 3) K))) :=
    Subgroup.mem_subgroupOf.mpr hz_scal
  have hz2N : zN ^ 2 = 1 := by
    apply Subtype.ext
    simpa using hz2
  have hz_order2 : orderOf zN ∣ 2 :=
    orderOf_dvd_of_pow_eq_one hz2N
  have hz_order_card : orderOf zN ∣
      Nat.card ((LargeEvenScalars (Fin 3) K).subgroupOf
        (Subgroup.normalizer (U : Set (GL (Fin 3) K)))) :=
    Subgroup.orderOf_dvd_natCard _ hz_mem_sub
  have hcop : Nat.Coprime 2 (Nat.card ((LargeEvenScalars (Fin 3) K).subgroupOf
      (Subgroup.normalizer (U : Set (GL (Fin 3) K))))) :=
    Nat.coprime_two_left.mpr hScalOdd
  have hz_order1 : orderOf zN = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hz_order2 hcop) hz_order_card
  have hz_oneN : zN = 1 := orderOf_eq_one_iff.mp hz_order1
  have hz_one : (zN : GL (Fin 3) K) = 1 := by rw [hz_oneN]; rfl
  have hcommX : (XiD 1 : GL (Fin 3) K) * (XiD 0 : GL (Fin 3) K) =
      (XiD 0 : GL (Fin 3) K) * (XiD 1 : GL (Fin 3) K) := by
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [← hzNco]
    exact hz_one
  have hρrange : ρD.range = X := by
    apply le_antisymm
    · rintro _ ⟨d, rfl⟩
      exact d.2
    · calc X = Subgroup.closure (Set.range φ) := hXclosure
        _ ≤ ρD.range := by
          refine (Subgroup.closure_le _).mpr ?_
          rintro _ ⟨i, rfl⟩
          exact ⟨XiD i, hXiρ i⟩
  have hXiComm : ∀ i j : Fin 2, Commute (XiD i) (XiD j) := by
    intro i j
    fin_cases i <;> fin_cases j
    · exact Commute.refl _
    · apply Subtype.ext
      apply Subtype.ext
      simpa using hcommX.symm
    · apply Subtype.ext
      apply Subtype.ext
      simpa using hcommX
    · exact Commute.refl _
  let P : Subgroup Dpre := Subgroup.closure (Set.range XiD)
  have hPmap : P.map ρD = ρD.range := by
    dsimp [P]
    rw [MonoidHom.map_closure]
    have hset : ρD '' Set.range XiD = Set.range φ := by
      ext x
      constructor
      · rintro ⟨_, ⟨i, rfl⟩, hx⟩
        exact ⟨i, (hXiρ i).symm.trans hx⟩
      · rintro ⟨i, rfl⟩
        exact ⟨XiD i, ⟨i, rfl⟩, hXiρ i⟩
    rw [hset, ← hXclosure, hρrange]
  have hPcomm : IsMulCommutative P := by
    apply Subgroup.isMulCommutative_closure
    intro a ha b hb hab
    rcases ha with ⟨i, rfl⟩
    rcases hb with ⟨j, rfl⟩
    exact hXiComm i j
  have hker_center : ρD.ker ≤ Subgroup.center Dpre := by
    intro z hz
    rw [MonoidHom.mem_ker] at hz
    have hzker : (z : Subgroup.normalizer (U : Set (GL (Fin 3) K))) ∈
        (TableB.projConj U).ker := by
      rw [MonoidHom.mem_ker]
      simpa [ρD] using hz
    have hz_scal : (z : GL (Fin 3) K) ∈ LargeEvenScalars (Fin 3) K :=
      Subgroup.mem_subgroupOf.mp (hscal hzker)
    have hz_center : (z : GL (Fin 3) K) ∈ Subgroup.center (GL (Fin 3) K) :=
      TableB.scalars_le_center hz_scal
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    apply Subtype.ext
    simpa using (Subgroup.mem_center_iff.mp hz_center (x : GL (Fin 3) K))
  have hScomm : IsMulCommutative Dpre :=
    isMulCommutative_of_map_eq_range ρD P hPmap hker_center hPcomm
  have hBcomm : ∀ b ∈ Dpre, ∀ c ∈ Dpre, b * c = c * b := by
    intro b hb c hc
    exact congrArg Subtype.val (hScomm.is_comm.comm ⟨b, hb⟩ ⟨c, hc⟩)
  have hprojConj_eq : ∀ (A : GL (Fin 3) K) (φ : MulAut R),
      LargeEvenGraphAut (LargeEvenProjMk U)
        (fun h h' => ((h' : U) : GL (Fin 3) K) = A * (h : GL (Fin 3) K) * A⁻¹) φ →
      TableB.projConj U
        ⟨A, CFSG.LocalAnalysis.GLTheoremA.T173A.lin_normalizes A⟩ = φ := by
    intro A φ hgraph
    ext x
    induction x using QuotientGroup.induction_on with
    | H h =>
      rw [TableB.projConj_mk]
      let h' : U := U.normalizerMonoidHom
        ⟨A, CFSG.LocalAnalysis.GLTheoremA.T173A.lin_normalizes A⟩ h
      have hrel : ((h' : U) : GL (Fin 3) K) = A * (h : GL (Fin 3) K) * A⁻¹ := by
        dsimp [h']
        simp [Subgroup.normalizerMonoidHom_apply_apply_coe]
      exact (hgraph h h' hrel).symm
  have hAInorm : ∀ a ∈ A, ∃ M : Subgroup.normalizer (U : Set (GL (Fin 3) K)),
      ∀ l : ↥J, TableB.projConj U M (ψ l) = ψ (a l) := by
    rintro a ⟨b, rfl⟩
    obtain ⟨φ, ⟨A, -, hgraph⟩, hφ⟩ := hind b⁻¹ (inv_mem b.2)
    refine ⟨⟨A, CFSG.LocalAnalysis.GLTheoremA.T173A.lin_normalizes A⟩, fun l => ?_⟩
    rw [hprojConj_eq A φ hgraph]
    have h := hφ l (ggGamma J hN0 b l) ?_
    · change φ (θ (QuotientGroup.mk l)) = θ (QuotientGroup.mk (ggGamma J hN0 b l))
      simpa [ggGamma_coe] using h
    · simp [ggGamma_coe]
  have hAe : IsElemAbelian 3 A := by
    have hcfg : GGConfig 3 B Bs x L D J := hH.1
    have hBsElem : IsElemAbelian 3 Bs := hcfg.2.1.2.1
    have htop : IsElemAbelian 3 (⊤ : Subgroup ↥Bs) := by
      refine ⟨IsMulCommutative.of_comm (fun a b => ?_), fun x hx => ?_⟩
      · exact Subtype.ext (hBsElem.1.is_comm.comm a b)
      · exact Subtype.ext (hBsElem.2 x x.2)
    simpa [A, Subgroup.map_top] using htop.map (ggGamma J hN0)
  have hAIrange : ∀ a ∈ A, ∃ φ ∈ Set.range (TableB.projConj U),
      ∀ l : ↥J, φ (ψ l) = ψ (a l) := by
    rintro a ha
    obtain ⟨M, hM⟩ := hAInorm a ha
    exact ⟨TableB.projConj U M, ⟨M, rfl⟩, hM⟩
  have hdvdFactorial : Nat.card
      (ggAutomizer (MulAut.conj : ↥J →* MulAut ↥J).range A) ∣ Nat.factorial 3 :=
    card_ggAutomizer_dvd_factorial_of_induced_elemAbelian
      (d := 3) (by norm_num) (U := U) (ψ := ψ)
      (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hperfJ hAe hscal
      (I := Set.range (TableB.projConj U)) (by intro φ hφ; exact hφ) hAIrange hBcomm
  have hBs : IsElemAbelian 3 Bs := hH.1.2.1.2.1
  have hNoTr : GGNoTransvection 3 Bs := hH.2.2.2.1
  have hdvdActual : Nat.card (ggAutomizer J Bs) ∣ Nat.card
      (ggAutomizer (MulAut.conj : ↥J →* MulAut ↥J).range A) := by
    simpa [A] using card_ggAutomizer_dvd_gamma Nat.prime_three hBs hNoTr hN0 hZ
  have h8dvd6 : 8 ∣ 6 := by
    have h8dvd : Nat.card (ggAutomizer J Bs) ∣ Nat.factorial 3 :=
      hdvdActual.trans hdvdFactorial
    have hfact3 : Nat.factorial 3 = 6 := by norm_num
    rw [hfact3] at h8dvd
    have hAut8 : Nat.card (ggAutomizer J Bs) = 8 :=
      ggAutomizer_card_of_lineJDatum_B2 (p := 3) rfl hD
    rw [← hAut8]
    exact h8dvd
  norm_num at h8dvd6

section CertificateInstances


theorem GGResHyp.actual_J_not_splitLinear_for_B2
    (hH : GGResHyp 3 B Bs x L D J y Kc)
    (hD : GGResLineJDatum 3 Bs J .B2)
    (hMark : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .A ∧ 3 ∣ 2 ^ lab.n - 1) 3 Bs J) :
    False := by
  obtain ⟨labJ, hΛJ, hHasJ, -⟩ := largeEvenMarking_exists_hasLabel hMark
  have hperfJ : commutator ↥J = ⊤ := hMark.1
  have hBs : IsElemAbelian 3 Bs := hH.1.2.1.2.1
  have hZ : Nat.card ↥(Bs ⊓ J ⊓ Subgroup.centralizer (J : Set G)) ≤ 3 :=
    card_inf_center_le_of_hasLabel (p := 3) (Bs := Bs) (K := J) (lab := labJ)
      ggLabelCenterPCyclicInput_holds Nat.prime_three (by norm_num) hBs hperfJ hΛJ hHasJ
  exact actual_B2_core hH hD hMark hZ

end CertificateInstances



end B2Endpoint

end CFSG.StandardType.ResJCubicBlock
end
