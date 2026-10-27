module

public import CFSG.LocalAnalysis.StandardType.GGF4H4JBlockUnitary
public import CFSG.LocalAnalysis.StandardType.GGF4LabelH1
public import CFSG.LocalAnalysis.StandardType.GGSecFiveCompatJoinF4
public import CFSG.LocalAnalysis.StandardType.GGStdPosLocalDefs
public import CFSG.LocalAnalysis.StandardType.GGTypeACompatFar
public import Certificates.Certificate2012
public import Certificates.Certificate26122
import CFSG.LocalAnalysis.StandardType.GGF4QGeFourEndsA3Uni
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosPerm
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosPermAux4
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
import CFSG.LocalAnalysis.StandardType.GGF4H4JBlockAux2
import CFSG.LocalAnalysis.StandardType.GGF4LabelH2
import CFSG.LocalAnalysis.StandardType.GGTypeANbrLabels
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpJFrame
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpJSwap
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpJBlock
import CFSG.LocalAnalysis.StandardType.GGStdPosACore
import CFSG.LocalAnalysis.StandardType.GGSixBstarUniqueToralA
import CFSG.LocalAnalysis.StandardType.GGTableBTransport
import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpStdAssembly

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

section Unitary


theorem ggF4A3_exists_reflPair_unitary (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G]
    {p f : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {ks : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J ks) (hf : 2 ≤ f) (hpf : p ∣ 2 ^ f + 1)
    (hLlab : GGHasLabel ⟨.twA, 3, f⟩ (L ⧸ Subgroup.center L)) :
    ∃ u ∈ ggAutomizer J Bs, ∃ v ∈ ggAutomizer J Bs,
      GGIsReflection p u ∧ GGIsReflection p v ∧ orderOf (u * v) = 3 := by
  classical
  obtain ⟨F, hFfield, hFfin, hFchar, hK, ψ, P, h', hd, -, hP3, hJ⟩ :=
    ggF4JB_unitary_block hRig hcfg hf hpf hLlab
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hP3
  obtain ⟨ε, hεapp, hεrefl⟩ := ggNSDiag_automizer_perm h' hd
  have hind : ∀ σ : Equiv.Perm (Fin 4), (∀ i ∉ ({a, b, c} : Finset (Fin 4)), σ⁻¹ i = i) →
      ((ε σ : ↥(ggAutomizer ψ.range Bs)) : MulAut ↥Bs) ∈ ggAutomizer J Bs := by
    intro σ hσ
    have hN := ggNSPosPA_permSU_mem_normalizer h' hd σ⁻¹
    have hgJ : ψ (ggPermSU (K := F) (f := f) σ⁻¹) ∈ J := by
      rw [hJ]
      refine ⟨CFSG.ClassicalInvolution.ModelFacts.UnitaryAut.suEquivUnitarySU F 2 f hK 4
        (ggPermSU (K := F) (f := f) σ⁻¹), ?_, ?_⟩
      · show TableBUE.IsBlockOn {a, b, c} ((σ⁻¹).permMatrix F)
        exact isBlockOn_permMatrix hσ
      · simp [nsJA2Cover]
    have heq : ggConjAut Bs hN = ((ε σ : ↥(ggAutomizer ψ.range Bs)) : MulAut ↥Bs) := by
      refine MulEquiv.ext fun s => Subtype.ext ?_
      rw [ggConjAut_apply, hεapp]
    rw [← heq]
    exact ggConjAut_mem_ggAutomizer hgJ hN
  have hswap : ∀ y z : Fin 4, y ∈ ({a, b, c} : Finset (Fin 4)) → z ∈ ({a, b, c} : Finset (Fin 4)) →
      ∀ i ∉ ({a, b, c} : Finset (Fin 4)), (Equiv.swap y z)⁻¹ i = i := by
    intro y z hy hz i hi
    rw [Equiv.swap_inv]
    exact Equiv.swap_apply_of_ne_of_ne (fun h => hi (h ▸ hy)) (fun h => hi (h ▸ hz))
  refine ⟨_, hind _ (hswap a b (by simp) (by simp)), _, hind _ (hswap a c (by simp) (by simp)),
    hεrefl a b hab, hεrefl a c hac, ?_⟩
  rw [← Subgroup.coe_mul, ← map_mul, Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
  exact (Equiv.Perm.isThreeCycle_swap_mul_swap_same hab hac hbc).orderOf

end Unitary

section Linear

theorem ggKGPosStdPos_of_actsDiag {m : ℕ} {F : Type} [Field F] (hm : 2 ≤ m) {G : Type} [Group G]
    {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G} {Bs : Subgroup G}
    (h : ∀ b ∈ Bs, GGActsDiag ψ b) : GGKGPosStdPos (SpecialLinear.rootDatum m F) ψ Bs := by
  intro b hb γ hγ
  obtain ⟨t, ht⟩ := h b hb
  have hdiag : ((ggDiagUnit t : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F).IsDiag :=
    Matrix.isDiag_diagonal _
  obtain ⟨h', hh', hz⟩ := StdPosA.conjSL_isDiag_eq_torus hm hdiag hγ
  refine ⟨h', hh', fun z hzγ => ?_⟩
  rw [ht z, ← hz z hzγ]
  exact congrArg ψ (RootPlaneA.slConjugation_eq_conjSL (ggDiagUnit t) z)

theorem ggF4A3_exists_reflPair_linear {G : Type} [Group G] [Finite G] {p f : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {ks : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J ks) (hf : 2 ≤ f) (hpf : p ∣ 2 ^ f - 1)
    (hLlab : GGHasLabel ⟨.A, 3, f⟩ (L ⧸ Subgroup.center L)) (hcard : Nat.card Bs = p ^ 4) :
    ∃ u ∈ ggAutomizer J Bs, ∃ v ∈ ggAutomizer J Bs,
      GGIsReflection p u ∧ GGIsReflection p v ∧ orderOf (u * v) = 3 := by
  classical
  have hc : GGConfig p B Bs x L D J := hcfg.1.1
  have hp : p.Prime := hc.tableB_facts.1
  have hBs : IsElemAbelian p Bs := hc.2.1.2.1
  have hC3 : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hc.2.1.2.2.2
  have hB : B = Bs := ggF4Small_eq_Bs hc hcard
  obtain ⟨y, K, hnbr⟩ := exists_ggNbr hc.1.2.2.2.2.2.2.2 hc.2.2
  have hΛ : LargeEvenInLambda2 (⟨.A, 3, f⟩ : LargeEvenLabel) :=
    ⟨le_trans (by norm_num : 1 ≤ 2) hf, by norm_num, fun h => absurd h (by norm_num)⟩
  have hL : GGTypeALocalCfg p B Bs x L D J 3 f y K :=
    ⟨hc, hcfg.1.2.2.1.1, statedClassicalModel_of_hasLabel_typeA hΛ hLlab, hpf, le_rfl, hnbr⟩
  obtain ⟨ψ, hX, hker, hdiag, -⟩ := ggF4JBx_exists_lift_L_lowerBlock ggInnerDiagMpInput_holds hL
  have hstd : GGKGPosStdPos (SpecialLinear.rootDatum 3 (GaloisField 2 f)) ψ Bs :=
    ggKGPosStdPos_of_actsDiag (by norm_num) hdiag
  obtain ⟨ζ, hζ⟩ : ∃ ζ : (GaloisField 2 f)ˣ, IsPrimitiveRoot ζ p := by
    have : Fact p.Prime := ⟨hp⟩
    have h1 : p ∣ Nat.card (GaloisField 2 f)ˣ := by
      rw [Nat.card_units, GaloisField.card 2 f (by omega)]
      exact hpf
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' p h1
    exact ⟨y, by simpa [hy] using IsPrimitiveRoot.orderOf y⟩
  obtain ⟨-, hxB, hx1, hLx, hcyc⟩ := hc.1.2.2.2.2.2.2.1
  have hE : IsElemAbelian p (Bs ⊓ Subgroup.centralizer (ψ.range : Set G)) :=
    TableB.isElemAbelian_mono hBs inf_le_left
  have hC : Nat.card ↥(Bs ⊓ Subgroup.centralizer (ψ.range : Set G)) ≤ p :=
    TableB.card_le_of_isCyclic hp.pos (hcyc _ (by rw [← hX]; exact inf_le_right)
      (TableB.isPGroup_of_isElemAbelian hE)) hE.2
  obtain ⟨δ, hδ, hδp, hδC, hfull⟩ :=
    ggDk_exists_diagFrame (F := GaloisField 2 f) (by norm_num : 2 ≤ 3) hker hp hBs hstd hcard hC
  obtain ⟨-, -, hDcard, hxD, -, hJ, hDJ⟩ := hc.2.2.1
  rw [hB] at hDJ
  let xb : ↥Bs := ⟨x, hc.2.1.1 hxB⟩
  have hxC : (xb : G) ∈ Subgroup.centralizer (ψ.range : Set G) := by
    rw [hX]
    exact Subgroup.mem_centralizer_iff.mpr fun l hl =>
      (Subgroup.mem_centralizer_iff.mp (hLx.1 hl) x (Set.mem_singleton x)).symm
  rw [← hX] at hJ
  obtain ⟨I, hI, hIc⟩ := ggDk_comp_eq_block (F := GaloisField 2 f) (x := xb) hker hp hδ hfull hζ
    hDJ hDcard hxD (fun h => hx1 (congrArg Subtype.val h)) (hδC xb hxC) hJ
  obtain ⟨a, ha, b, hb, c, hc', hab, hac, hbc⟩ := Finset.two_lt_card.mp (show 2 < I.card by omega)
  obtain ⟨hN₁, hr₁, hfix₁⟩ :=
    ggDk_swap_refl (F := GaloisField 2 f) (by norm_num : 2 ≤ 3) hker hp hC3 hδ hδp hfull hζ hab
  obtain ⟨hN₂, hr₂, hfix₂⟩ :=
    ggDk_swap_refl (F := GaloisField 2 f) (by norm_num : 2 ≤ 3) hker hp hC3 hδ hδp hfull hζ hac
  have hJ₁ : ggConjAut Bs hN₁ ∈ ggAutomizer J Bs := ggConjAut_mem_ggAutomizer (by
    rw [hI]
    exact Subgroup.mem_map_of_mem ψ (ggPermSL_swap_mem_blockSpecialLinear ha hb)) hN₁
  have hJ₂ : ggConjAut Bs hN₂ ∈ ggAutomizer J Bs := ggConjAut_mem_ggAutomizer (by
    rw [hI]
    exact Subgroup.mem_map_of_mem ψ (ggPermSL_swap_mem_blockSpecialLinear ha hc')) hN₂
  refine ⟨_, hJ₁, _, hJ₂, hr₁, hr₂, ?_⟩
  set g₁ := ψ (ggPermSL (F := GaloisField 2 f) (Equiv.swap a b)) with hg₁
  set g₂ := ψ (ggPermSL (F := GaloisField 2 f) (Equiv.swap a c)) with hg₂
  have hN : g₁ * g₂ ∈ Subgroup.normalizer (Bs : Set G) := Subgroup.mul_mem _ hN₁ hN₂
  have hmul : ggConjAut Bs hN₁ * ggConjAut Bs hN₂ = ggConjAut Bs hN := by
    refine MulEquiv.ext fun s => Subtype.ext ?_
    rw [MulAut.mul_apply, ggConjAut_apply, ggConjAut_apply, ggConjAut_apply]
    group
  have hcube : (g₁ * g₂) ^ 3 = 1 := by
    have hσ : Equiv.swap a c * Equiv.swap a b * (Equiv.swap a c * Equiv.swap a b) *
        (Equiv.swap a c * Equiv.swap a b) = 1 := by
      have h3 := (Equiv.Perm.isThreeCycle_swap_mul_swap_same hac hab (Ne.symm hbc)).orderOf
      have h := pow_orderOf_eq_one (Equiv.swap a c * Equiv.swap a b)
      rwa [h3, pow_three'] at h
    have hM : (ggPermSL (F := GaloisField 2 f) (Equiv.swap a b) *
        ggPermSL (F := GaloisField 2 f) (Equiv.swap a c)) ^ 3 = 1 := by
      refine Subtype.ext ?_
      rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.SpecialLinearGroup.coe_one]
      change ((Equiv.swap a b).permMatrix (GaloisField 2 f) *
        (Equiv.swap a c).permMatrix (GaloisField 2 f)) ^ 3 = 1
      rw [← Matrix.permMatrix_mul, pow_three, ← Matrix.permMatrix_mul, ← Matrix.permMatrix_mul, hσ,
        Matrix.permMatrix_one]
    rw [hg₁, hg₂, ← map_mul, ← map_pow, hM, map_one]
  rw [hmul]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime ?_ ?_
  · refine MulEquiv.ext fun s => Subtype.ext ?_
    rw [ggConjAut_pow_apply, hcube, one_mul, inv_one, mul_one, MulAut.one_apply]
  ·
    intro h1
    rw [← hmul] at h1
    have hinv : ggConjAut Bs hN₂ = (ggConjAut Bs hN₁)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
    have hsq : (ggConjAut Bs hN₁)⁻¹ = ggConjAut Bs hN₁ := inv_eq_of_mul_eq_one_right (by
      rw [← pow_two]
      exact hr₁.1)
    have hfix : ∀ s : ↥Bs, δ s a = δ s b ↔ δ s a = δ s c := fun s => by
      rw [← hfix₁, ← hfix₂, hinv, hsq]
    rcases ggDk_pair_eq_of_fix_iff hp hfull hζ hab hfix with ⟨-, h2⟩ | ⟨h2, -⟩
    · exact hbc h2.symm
    · exact hab h2

end Linear

section Leaf

theorem ggF4A3_exists_reflPair_J (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) {G : Type}
    [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hP : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hF4 : GGIsWeylMatrixF4 M)
    (hA3 : GGWeylOfType p (CoxeterMatrix.A 3) (ggAutomizer L Bs)) :
    ∃ u ∈ ggAutomizer J Bs, ∃ v ∈ ggAutomizer J Bs,
      GGIsReflection p u ∧ GGIsReflection p v ∧ orderOf (u * v) = 3 := by
  have hp : p.Prime := hcfg.1.1.tableB_facts.1
  have hW4 := ggF4Small_weylOfType_F4 e hP hF4
  have hcard := ggF4Small_card_Bs hTBF hWI hcfg hW4 (ggF4Small_ks_nonempty hW4 hA3)
  obtain ⟨f, hf1, ⟨hpf, hlab⟩ | ⟨hpf, hlab⟩⟩ := ggF4H1_label_of_route hTBF hWI hcfg hP hF4 hA3
  · have hf : 2 ≤ f := by
      by_contra hlt
      have hf' : f = 1 := by omega
      subst hf'
      exact hp.one_lt.ne' (Nat.dvd_one.mp (by simpa using hpf))
    exact ggF4A3_exists_reflPair_linear hcfg hf hpf hlab hcard
  · have hf : 2 ≤ f := by
      by_contra hlt
      have hf' : f = 1 := by omega
      subst hf'
      have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (by simpa using hpf)
      subst hp3
      exact ggF4LabelH2_holds G B Bs x L D J hcfg.1.1 hlab
    exact ggF4A3_exists_reflPair_unitary ggLabelRigidInput_holds hcfg hf hpf hlab

theorem ggF4JoinJReflA2Input_holds (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) :
    GGF4JoinJReflA2Input := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg _ ι M e hP hF4 hA3
  exact ggF4A3_exists_reflPair_J hTBF hWI hcfg hP hF4 hA3

end Leaf

end CFSG.StandardType

end
