module

public import CFSG.RankThree.PartTwo.Sec11.KS11Lie4ProofG2
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie4ProofRoots
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie4ProofSL2
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie4ProofPoly
import CFSG.RankThree.Chevalley.SteinbergCEG2EvenSplitCentralizers
import CFSG.LieType.Chevalley.RootDiagonalWeylTransporter
import CFSG.LieType.Chevalley.ExactNormalFormE
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67A2Hom
import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67A2Torus
import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67A2Sylow
import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67A2Diag
import CFSG.ClassicalInvolution.Balance.LayerGenerationShortAdjoint
import CFSG.RankThree.Classical2.SLnRootPermutingFixedGroups
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B2Thompson
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.Quasithin.Vol2.KGFactC31RuRefBase
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.RankThree.PartTwo.Sec11.Item1117ProofSwap
public import CFSG.RankThree.PartTwo.Sec11.Item1117StepsProofCube
public import CFSG.RankThree.PartTwo.Sec11.Item1117StepsProofTools
public import CFSG.RankThree.PartTwo.Sec11.Item118
public import CFSG.RankThree.PartTwo.Sec4.Item426A6
public import CFSG.RankThree.PartTwo.Sec4.LThreePiSLOn
public import CFSG.RankThree.PartTwo.Sec4.Statements423
public import CFSG.RankThree.PartTwo.Sec6.Statements
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.Sporadic.HeldB.Common
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Sporadic.Schreier.RuPair
public import CFSG.Sporadic.Schreier.RuSylow
public import CFSG.Walter.Defs
public import Certificates.Certificate43
public import Certificates.Certificate7233Base
import CFSG.ClassicalInvolution.Balance.PassTwoFinal
import CFSG.LieType.Ree.SmallReeModelSchreier
import CFSG.LocalAnalysis.ComponentClassification.BadTwoComponentSubgroup
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieClassical
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieE6E7Triality
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwo

public section

namespace CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof

open scoped Pointwise

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Chevalley
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.LieType.HighestRoot

theorem commutator_mem_of_mem_sup {G : Type*} [Group G] {A R : Subgroup G}
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hAR : A ≤ Subgroup.normalizer (R : Set G))
    {x y : G} (hx : x ∈ A ⊔ R) (hy : y ∈ A ⊔ R) : x * y * x⁻¹ * y⁻¹ ∈ R := by
  have hset : ((A ⊔ R : Subgroup G) : Set G) = (A : Set G) * R :=
    Subgroup.coe_mul_of_left_le_normalizer_right A R hAR
  have hx' : x ∈ ((A ⊔ R : Subgroup G) : Set G) := hx
  have hy' : y ∈ ((A ⊔ R : Subgroup G) : Set G) := hy
  rw [hset] at hx' hy'
  obtain ⟨h, hh, q, hq, rfl⟩ := hx'
  obtain ⟨h', hh', q', hq', rfl⟩ := hy'
  have hconj : ∀ a ∈ A, ∀ r ∈ R, a * r * a⁻¹ ∈ R := fun a ha r hr =>
    (Subgroup.mem_normalizer_iff.mp (hAR ha) r).mp hr
  have e1 : h * q * (h' * q') * (h * q)⁻¹ * (h' * q')⁻¹ = (h * h') *
      (h'⁻¹ * q * h'⁻¹⁻¹ * (q' * q⁻¹)) * (h' * h)⁻¹ * (h' * q'⁻¹ * h'⁻¹) := by group
  rw [e1, ← hA h hh h' hh']
  exact mul_mem (hconj _ (mul_mem hh hh') _ (mul_mem (hconj _ (inv_mem hh') _ hq)
    (mul_mem hq' (inv_mem hq)))) (hconj _ hh' _ (inv_mem hq'))


variable {K : Type} [Field K]

theorem rootDiagUnit_one' : rootDiagUnit .G2 (1 : Fin Tag.G2.rank → Kˣ) = 1 :=
  map_one (rootDiagUnitHom .G2 K)

theorem simpleRootSL2_injective_g2 (i : Fin Tag.G2.rank) :
    Function.Injective (simpleRootSL2 .G2 K i) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro A hA
  obtain ⟨l, hl2, hlA⟩ := KS11Lie2Proof.simpleRootSL2_eq_one i (MonoidHom.mem_ker.mp hA)
  have hl2' : l ^ 2 = 1 := Units.ext (by simpa using hl2)
  have hll : (l⁻¹ : Kˣ) = l := by
    rw [inv_eq_iff_mul_eq_one, ← sq, hl2']
  have hAH : A = HSL l := Subtype.ext (by
    rw [hlA, coe_HSL, hll]
    ext a b
    fin_cases a <;> fin_cases b <;> simp)
  have h1 : torusElt .G2 K i l = 1 := by
    rw [← simpleRootSL2_HSL, ← hAH]
    exact MonoidHom.mem_ker.mp hA
  rw [torusElt_eq_rootDiagUnit, ← rootDiagUnit_one'] at h1
  have h2 := rootDiagUnit_injective h1
  have hl : l = 1 := by
    rcases fin_G2_cases i with rfl | rfl
    · have h3 := congrFun h2 g2ir
      have hc : Tag.G2.cartan g2ia g2ir = -1 := by decide
      rw [hc, Pi.one_apply, zpow_neg_one, inv_eq_one] at h3
      exact h3
    · have h3 := congrFun h2 g2ia
      have hc : Tag.G2.cartan g2ir g2ia = -3 := by decide
      rw [hc, Pi.one_apply, zpow_neg, inv_eq_one] at h3
      have h3' : l ^ 3 = 1 := by exact_mod_cast h3
      calc l = l ^ 3 * (l ^ 2)⁻¹ := by group
        _ = 1 := by rw [h3', hl2', inv_one, one_mul]
  rw [hAH, hl, Subgroup.mem_bot]
  exact Subtype.ext (by rw [coe_HSL]; ext a b; fin_cases a <;> fin_cases b <;> simp)

theorem range_simpleRootSL2_g2 (i : Fin Tag.G2.rank) :
    (simpleRootSL2 .G2 K i).range =
      rootSubgroup .G2 K (Pi.single i 1) ⊔ rootSubgroup .G2 K (-Pi.single i 1) := by
  rw [range_simpleRootSL2, closure_xUnit_yUnit_eq_rootSubgroup_sup]

abbrev wV : WeylGroup .G2 := simple .G2 g2s * simple .G2 g2l

@[expose] noncomputable def rhoV (K : Type) [Field K] : SL2 K →* ModGL .G2 K :=
  (MulAut.conj (canonicalRep (coxeterSystem .G2) K wV)).toMonoidHom.comp
    (simpleRootSL2 .G2 K g2s)

theorem rhoV_apply (A : SL2 K) : rhoV K A = canonicalRep (coxeterSystem .G2) K wV *
    simpleRootSL2 .G2 K g2s A * (canonicalRep (coxeterSystem .G2) K wV)⁻¹ := rfl

theorem rhoV_injective : Function.Injective (rhoV K) :=
  (MulAut.conj _).injective.comp (simpleRootSL2_injective_g2 g2s)

theorem range_rhoV :
    (rhoV K).range = rootSubgroup .G2 K g2δ ⊔ rootSubgroup .G2 K (-g2δ) := by
  rw [rhoV, MonoidHom.range_comp, range_simpleRootSL2,
    map_conj_canonicalRep_closure_xUnit_yUnit g2_w_smul]

theorem rhoV_HSL (t : Kˣ) : rhoV K (HSL t) = rootDiagUnit .G2 (Pi.mulSingle g2ir t) := by
  rw [rhoV_apply, simpleRootSL2_HSL, torusElt_eq_rootDiagUnit]
  refine ((rootDiagUnit_eq_conj_canonicalRep_iff _ _ wV).mpr
    (rootChar_smul_eq_of_single fun i => ?_)).symm
  rw [rootChar_mulSingle_eq_zpow, rootChar_pi_single]
  rcases fin_G2_cases i with rfl | rfl
  · rw [show g2ia = g2l from rfl, g2_w_smul_e0]
    rfl
  · rw [show g2ir = g2s from rfl, g2_w_smul]
    rfl

theorem rhoA_HSL (t : Kˣ) : simpleRootSL2 .G2 K g2ia (HSL t) =
    rootDiagUnit .G2 (fun j => t ^ Tag.G2.cartan g2ia j) := by
  rw [simpleRootSL2_HSL, torusElt_eq_rootDiagUnit]

theorem mem_g2ShortSL2_iff {x : adjointGroup .G2 K} :
    x ∈ g2ShortSL2 K ↔ (x : ModGL .G2 K) ∈ (rhoV K).range := by
  rw [range_rhoV]
  rfl

theorem mem_g2LongSL2_iff {x : adjointGroup .G2 K} :
    x ∈ g2LongSL2 K ↔ (x : ModGL .G2 K) ∈ (simpleRootSL2 .G2 K g2ia).range := by
  rw [range_simpleRootSL2_g2]
  rfl

theorem mulAut_mul_conj {G : Type*} [Group G] (α : MulAut G) (y : G) :
    α * MulAut.conj y = MulAut.conj (α y) * α := by
  ext x
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]

theorem exists_pow_conj_mul {G : Type*} [Group G] (α : MulAut G) (g : G) (m : ℕ) :
    ∃ x : G, (MulAut.conj g * α) ^ m = MulAut.conj x * α ^ m := by
  induction m with
  | zero => exact ⟨1, by simp⟩
  | succ m ih =>
    obtain ⟨x, hx⟩ := ih
    refine ⟨x * (α ^ m) g, ?_⟩
    rw [pow_succ, hx, mul_assoc, ← mul_assoc (α ^ m), mulAut_mul_conj, map_mul]
    group

theorem g2ShortOut_holds : G2ShortOut := by
  intro K _ _ hK3 hK4 β hβ hβS
  set n : adjointGroup .G2 K := ⟨canonicalRep (coxeterSystem .G2) K wV,
    canonicalRep_mem_adjointGroup _ K wV⟩ with hn
  set β' : MulAut (adjointGroup .G2 K) := (MulAut.conj n)⁻¹ * β * MulAut.conj n with hβ'
  have hfix : ∀ c : K, β' ⟨xUnit .G2 K g2s c, xUnit_mem_adjointGroup _ _⟩ =
      ⟨xUnit .G2 K g2s c, xUnit_mem_adjointGroup _ _⟩ := by
    intro c
    have hmem : n * ⟨xUnit .G2 K g2s c, xUnit_mem_adjointGroup _ _⟩ * n⁻¹ ∈ g2ShortSL2 K := by
      rw [mem_g2ShortSL2_iff]
      refine ⟨uSL c, ?_⟩
      rw [rhoV_apply, simpleRootSL2_uSL]
      rfl
    have h1 := hβS _ hmem
    rw [hβ', MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, h1, MulAut.inv_apply,
      MulAut.conj_symm_apply]
    group
  obtain ⟨k, hk⟩ := hβ
  have hβ'k : β' ^ 3 ^ k = 1 := by
    have e1 : β' = (MulAut.conj n)⁻¹ * β * ((MulAut.conj n)⁻¹)⁻¹ := by rw [inv_inv]
    rw [e1, conj_pow, hk, mul_one, mul_inv_cancel]
  obtain ⟨hnf, hinn⟩ := CFSG.RankThree.PartTwo.KFacts.g2_automorphism_normal_form hK3 hK4 (K := K)
  obtain ⟨g, σ, hgσ⟩ := hnf β'
  have hσk : σ ^ 3 ^ k = 1 := by
    obtain ⟨x, hx⟩ := exists_pow_conj_mul (CFSG.RankThree.PartTwo.KFacts.g2FieldHom K σ) g (3 ^ k)
    rw [← hgσ, hβ'k, ← map_pow] at hx
    refine hinn _ ⟨x⁻¹, ?_⟩
    rw [map_inv, eq_inv_mul_of_mul_eq hx.symm, mul_one]
  have hσ1 : σ = 1 := by
    refine eq_one_of_conj_xUnit (RingHom.id K) hK3 σ ⟨k, hσk⟩ g2s (g : ModGL .G2 K) fun c => ?_
    have h1 := congrArg Subtype.val ((hfix c).symm.trans (by rw [hgσ]))
    rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, CFSG.RankThree.PartTwo.KFacts.coe_g2FieldHom,
      units_map_entrywiseHom_xUnit] at h1
    exact h1.symm
  rw [hσ1, map_one, mul_one] at hgσ
  refine ⟨n * g * n⁻¹, ?_⟩
  rw [map_mul, map_mul, map_inv, ← hgσ, hβ']
  group

theorem rootSpan_pair (α : Fin Tag.G2.rank → ℤ) :
    rootSpan .G2 K {α, -α} = rootSubgroup .G2 K α ⊔ rootSubgroup .G2 K (-α) := by
  rw [rootSpan, iSup_insert, iSup_singleton]

theorem toralCentralizer_torusA {ζ : Kˣ} (hζ : orderOf ζ = 3) :
    toralCentralizer .G2 K (fun j => ζ ^ Tag.G2.cartan g2ia j) =
      torusGroup .G2 K ⊔ (rootSubgroup .G2 K g2δ ⊔ rootSubgroup .G2 K (-g2δ)) := by
  rw [toralCentralizer_eq_toralRootGroup_of_le (stabilizer_le_torusA hζ), toralRootGroup,
    rootCharKernel_torusA hζ, rootSpan_pair]
  rfl

theorem toralCentralizer_shortNine {μ : Kˣ} (hμ : 4 ≤ orderOf μ) :
    toralCentralizer .G2 K (Pi.mulSingle g2ir μ) =
      torusGroup .G2 K ⊔ (rootSubgroup .G2 K g2e0 ⊔ rootSubgroup .G2 K (-g2e0)) := by
  rw [toralCentralizer_eq_toralRootGroup_of_le (stabilizer_le_shortNine hμ), toralRootGroup,
    rootCharKernel_shortNine hμ, rootSpan_pair, g2a_eq_single]
  rfl

theorem toralCentralizer_threeA {ζ : Kˣ} (hζ : orderOf ζ = 3) :
    toralCentralizer .G2 K (Pi.mulSingle g2ir ζ) =
      torusGroup .G2 K ⊔ rootSpan .G2 K {g2a, -g2a, g2b, -g2b, g2c, -g2c} := by
  rw [toralCentralizer_eq_toralRootGroup_of_le (stabilizer_le_threeA hζ), toralRootGroup,
    rootCharKernel_threeA hζ]

theorem mem_centralizer_iff_toral {b : Fin Tag.G2.rank → Kˣ} {z x : adjointGroup .G2 K}
    (hz : (z : ModGL .G2 K) = rootDiagUnit .G2 b) :
    x ∈ Subgroup.centralizer ({z} : Set (adjointGroup .G2 K)) ↔
      (x : ModGL .G2 K) ∈ toralCentralizer .G2 K b := by
  rw [Subgroup.mem_centralizer_singleton_iff, mem_toralCentralizer, ← hz]
  constructor
  · intro h
    refine ⟨x.2, ?_⟩
    have h1 := congrArg Subtype.val h
    simp only [Subgroup.coe_mul] at h1
    rw [← h1, mul_inv_cancel_right]
  · rintro ⟨-, h⟩
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    calc (x : ModGL .G2 K) * z = (z : ModGL .G2 K) * x * (z : ModGL .G2 K)⁻¹ * z := by rw [h]
      _ = z * x := by group

theorem torus_comm : ∀ a ∈ torusGroup .G2 K, ∀ b ∈ torusGroup .G2 K, a * b = b * a :=
  (triangular_borel_structure.{0, 0} .G2 K).1

theorem pow_card_sub_one_of_mem_torusGroup [Finite K] {t : ModGL .G2 K}
    (ht : t ∈ torusGroup .G2 K) : t ^ (Nat.card K - 1) = 1 := by
  obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  have hl : l ^ (Nat.card K - 1) = 1 := by
    funext j
    rw [Pi.pow_apply, Pi.one_apply, ← Nat.card_units]
    exact pow_card_eq_one'
  change rootDiagUnitHom .G2 K l ^ _ = 1
  rw [← map_pow, hl, map_one]

theorem mem_torusGroup_of_centralizes {α : Fin Tag.G2.rank → ℤ} (hα : IsRoot .G2 α)
    {x : ModGL .G2 K}
    (hx : x ∈ torusGroup .G2 K ⊔ (rootSubgroup .G2 K α ⊔ rootSubgroup .G2 K (-α)))
    (hxc : ∀ y ∈ rootSubgroup .G2 K α ⊔ rootSubgroup .G2 K (-α), x * y = y * x) :
    x ∈ torusGroup .G2 K := by
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right _ _
    (torusGroup_le_normalizer_rootPair (K := K) hα)
  have hx' : x ∈ ((torusGroup .G2 K ⊔ (rootSubgroup .G2 K α ⊔ rootSubgroup .G2 K (-α)) :
      Subgroup (ModGL .G2 K)) : Set (ModGL .G2 K)) := hx
  rw [hset] at hx'
  obtain ⟨t, ht, u, hu, rfl⟩ := hx'
  have hconj : ∀ y ∈ rootSubgroup .G2 K α ⊔ rootSubgroup .G2 K (-α),
      u * y * u⁻¹ = t⁻¹ * y * t⁻¹⁻¹ := fun y hy => by
    have h1 := hxc y hy
    calc u * y * u⁻¹ = t⁻¹ * ((t * u) * y * (t * u)⁻¹) * t⁻¹⁻¹ := by group
      _ = t⁻¹ * y * t⁻¹⁻¹ := by rw [h1]; group
  have hup : ∀ y ∈ rootSubgroup .G2 K α, u * y * u⁻¹ ∈ rootSubgroup .G2 K α := fun y hy => by
    rw [hconj y (Subgroup.mem_sup_left hy)]
    exact conj_mem_rootSubgroup_of_mem_torusGroup (inv_mem ht) hα hy
  have hdown : ∀ y ∈ rootSubgroup .G2 K (-α), u * y * u⁻¹ ∈ rootSubgroup .G2 K (-α) :=
    fun y hy => by
      rw [hconj y (Subgroup.mem_sup_right hy)]
      exact conj_mem_rootSubgroup_of_mem_torusGroup (inv_mem ht) (IsRoot.neg hα) hy
  refine mul_mem ht ?_
  by_cases h2 : ringChar K = 2
  · have : CharP K 2 := ringChar.of_eq h2
    exact EvenG2.mem_torusGroup_of_conj_rootSubgroups_of_charTwo hα hu hup hdown
  · exact mem_torusGroup_of_conj_rootSubgroups h2 hα hu hup hdown

theorem mem_range_rhoA_of_torus {t : ModGL .G2 K} (ht : t ∈ torusGroup .G2 K)
    (htc : t * pinnedX .G2 K g2δ 1 = pinnedX .G2 K g2δ 1 * t) :
    t ∈ (simpleRootSL2 .G2 K g2ia).range := by
  obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  have h1 := rootDiagUnit_conj_pinnedX l isRoot_g2δ 1
  rw [htc, mul_inv_cancel_right] at h1
  have h2 := pinnedX_injective .G2 K g2δ h1
  rw [mul_one] at h2
  have hχ : rootChar l g2δ = 1 := Units.ext (by rw [Units.val_one]; exact h2.symm)
  rw [rootChar_g2] at hχ
  have e1 : g2δ g2ia = 1 := rfl
  have e2 : g2δ g2ir = 2 := rfl
  rw [e1, e2, zpow_one, zpow_two] at hχ
  refine ⟨HSL (l g2ir)⁻¹, ?_⟩
  rw [rhoA_HSL]
  congr 1
  funext j
  rcases fin_G2_cases j with rfl | rfl
  · have hc : Tag.G2.cartan g2ia g2ia = 2 := by decide
    rw [hc, zpow_two, ← mul_inv]
    exact (eq_inv_of_mul_eq_one_left hχ).symm
  · have hc : Tag.G2.cartan g2ia g2ir = -1 := by decide
    rw [hc, zpow_neg_one, inv_inv]

theorem coe_conj (m x : adjointGroup .G2 K) :
    ((m * x * m⁻¹ : adjointGroup .G2 K) : ModGL .G2 K) =
      (m : ModGL .G2 K) * x * (m : ModGL .G2 K)⁻¹ := by
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]

theorem conj_mem_centralizer {G : Type*} [Group G] {m z x : G}
    (hx : x ∈ Subgroup.centralizer ({z} : Set G)) :
    m * x * m⁻¹ ∈ Subgroup.centralizer ({m * z * m⁻¹} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
  calc m * x * m⁻¹ * (m * z * m⁻¹) = m * (x * z) * m⁻¹ := by group
    _ = m * (z * x) * m⁻¹ := by rw [hx]
    _ = m * z * m⁻¹ * (m * x * m⁻¹) := by group

theorem conj_mem_centralizer_set {G : Type*} [Group G] {S : Subgroup G} {m b : G}
    (hm : ∀ s ∈ S, m * s = s * m) (hb : b ∈ Subgroup.centralizer (S : Set G)) :
    m * b * m⁻¹ ∈ Subgroup.centralizer (S : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hb ⊢
  intro s hs
  have h1 : m⁻¹ * s * m = s := by rw [mul_assoc, ← hm s hs, inv_mul_cancel_left]
  calc s * (m * b * m⁻¹) = m * ((m⁻¹ * s * m) * b) * m⁻¹ := by group
    _ = m * (b * (m⁻¹ * s * m)) * m⁻¹ := by rw [h1, hb s hs]
    _ = m * b * m⁻¹ * (m * (m⁻¹ * s * m) * m⁻¹) := by group
    _ = m * b * m⁻¹ * s := by rw [h1, hm s hs, mul_inv_cancel_right]

theorem mem_of_conj_mem {G : Type*} [Group G] {S : Subgroup G} {m c : G}
    (hm : ∀ s ∈ S, m * s = s * m) (hc : m * c * m⁻¹ ∈ S) : c ∈ S := by
  have h1 := hm _ hc
  have : c = m⁻¹ * (m * c * m⁻¹) * m := by group
  rw [this, mul_assoc, ← h1]
  simpa using hc

theorem g2ThreeBCent_split [Finite K] (h31 : 3 ∣ Nat.card K - 1) {z : adjointGroup .G2 K}
    (hzM : z ∈ g2LongSL2 K) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) :
    (∀ x ∈ Subgroup.centralizer ({z} : Set (adjointGroup .G2 K)),
      ∀ y ∈ Subgroup.centralizer ({z} : Set (adjointGroup .G2 K)),
        x * y * x⁻¹ * y⁻¹ ∈ g2ShortSL2 K) ∧
    ∀ b ∈ Subgroup.centralizer ({z} : Set (adjointGroup .G2 K)),
      b ∈ Subgroup.centralizer (g2ShortSL2 K : Set (adjointGroup .G2 K)) →
        b ^ (Nat.card K ^ 2 - 1) = 1 := by
  obtain ⟨A, hA⟩ := mem_g2LongSL2_iff.mp hzM
  have hinj := simpleRootSL2_injective_g2 (K := K) g2ia
  have hA3 : A ^ 3 = 1 := hinj (by
    rw [map_pow, hA, map_one]
    exact congrArg Subtype.val hz3)
  obtain ⟨P, t, hPt⟩ := exists_conj_HSL_of_three h31 A ⟨1, by simpa using hA3⟩
  have ht3 : orderOf t = 3 := by
    refine orderOf_eq_prime ?_ ?_
    · apply HSLHom_injective (K := K)
      rw [map_pow, HSLHom_apply, ← hPt, conj_pow, hA3, mul_one, mul_inv_cancel, map_one]
    · rintro rfl
      apply hz1
      have h1 : A = 1 := by
        have : P * A * P⁻¹ = 1 := by rw [hPt]; exact (map_one (HSLHom K))
        simpa using this
      apply Subtype.ext
      rw [← hA, h1, map_one]
      rfl
  set m : adjointGroup .G2 K := ⟨simpleRootSL2 .G2 K g2ia P, simpleRootSL2_mem_adjointGroup _ P⟩
  have hmM : m ∈ g2LongSL2 K := mem_g2LongSL2_iff.mpr ⟨P, rfl⟩
  have hmz : ((m * z * m⁻¹ : adjointGroup .G2 K) : ModGL .G2 K) =
      rootDiagUnit .G2 (fun j => t ^ Tag.G2.cartan g2ia j) := by
    rw [coe_conj, ← hA, ← rhoA_HSL, ← hPt]
    simp only [map_mul, map_inv]
    rfl
  have hcen : ∀ x ∈ Subgroup.centralizer ({z} : Set (adjointGroup .G2 K)),
      ((m * x * m⁻¹ : adjointGroup .G2 K) : ModGL .G2 K) ∈
        torusGroup .G2 K ⊔ (rootSubgroup .G2 K g2δ ⊔ rootSubgroup .G2 K (-g2δ)) := by
    intro x hx
    rw [← toralCentralizer_torusA ht3, ← mem_centralizer_iff_toral hmz]
    exact conj_mem_centralizer hx
  have hmS : ∀ s ∈ g2ShortSL2 K, m * s = s * m := fun s hs => (g2Short_commute_g2Long hs hmM).symm
  refine ⟨fun x hx y hy => ?_, fun b hb hbS => ?_⟩
  · have h := commutator_mem_of_mem_sup torus_comm
      (torusGroup_le_normalizer_rootPair (K := K) isRoot_g2δ) (hcen x hx) (hcen y hy)
    refine mem_of_conj_mem hmS ?_
    change ((m * (x * y * x⁻¹ * y⁻¹) * m⁻¹ : adjointGroup .G2 K) : ModGL .G2 K) ∈
      rootSubgroup .G2 K g2δ ⊔ rootSubgroup .G2 K (-g2δ)
    convert h using 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  · have hb' := hcen b hb
    have hbS' := conj_mem_centralizer_set hmS hbS
    have hbc : ∀ y ∈ rootSubgroup .G2 K g2δ ⊔ rootSubgroup .G2 K (-g2δ),
        ((m * b * m⁻¹ : adjointGroup .G2 K) : ModGL .G2 K) * y =
          y * ((m * b * m⁻¹ : adjointGroup .G2 K) : ModGL .G2 K) := by
      intro y hy
      have hyC : y ∈ adjointGroup .G2 K := sup_le (rootSubgroup_le_adjointGroup _)
        (rootSubgroup_le_adjointGroup _) hy
      have := Subgroup.mem_centralizer_iff.mp hbS' ⟨y, hyC⟩ hy
      exact (congrArg Subtype.val this).symm
    have hT := mem_torusGroup_of_centralizes isRoot_g2δ hb' hbc
    have h1 := pow_card_sub_one_of_mem_torusGroup hT
    have h2 : (m * b * m⁻¹) ^ (Nat.card K - 1) = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, h1]
      rfl)
    rw [conj_pow, mul_inv_eq_one, mul_eq_left] at h2
    have hq : Nat.card K - 1 ∣ Nat.card K ^ 2 - 1 := by
      have e : Nat.card K ^ 2 - 1 = (Nat.card K + 1) * (Nat.card K - 1) := by
        rw [← Nat.sq_sub_sq, one_pow]
      rw [e]
      exact Dvd.intro_left _ rfl
    obtain ⟨c, hc⟩ := hq
    rw [hc, pow_mul, h2, one_pow]

theorem five_le_orderOf_of_three {G : Type*} [Group G] {t : G} (ht : ∃ k : ℕ, t ^ 3 ^ k = 1)
    (ht3 : t ^ 3 ≠ 1) : 5 ≤ orderOf t := by
  obtain ⟨k, hk⟩ := ht
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hk)
  rcases Nat.lt_or_ge j 2 with h | h
  · exfalso
    apply ht3
    rw [← orderOf_dvd_iff_pow_eq_one, hj]
    interval_cases j <;> norm_num
  · rw [hj]
    calc 5 ≤ 3 ^ 2 := by norm_num
      _ ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) h

theorem g2ShortNineCent_split [Finite K] (h31 : 3 ∣ Nat.card K - 1) {y : adjointGroup .G2 K}
    (hyS : y ∈ g2ShortSL2 K) (hy : ∃ k : ℕ, y ^ 3 ^ k = 1) (hy3 : y ^ 3 ≠ 1) :
    (∀ x ∈ Subgroup.centralizer ({y} : Set (adjointGroup .G2 K)),
      ∀ w ∈ Subgroup.centralizer ({y} : Set (adjointGroup .G2 K)),
        x * w * x⁻¹ * w⁻¹ ∈ g2LongSL2 K) ∧
    ∀ x ∈ Subgroup.centralizer ({y} : Set (adjointGroup .G2 K)),
      x ∈ Subgroup.centralizer (g2ShortSL2 K : Set (adjointGroup .G2 K)) → x ∈ g2LongSL2 K := by
  obtain ⟨A, hA⟩ := mem_g2ShortSL2_iff.mp hyS
  have hinj := rhoV_injective (K := K)
  obtain ⟨k, hk⟩ := hy
  have hAk : A ^ 3 ^ k = 1 := hinj (by
    rw [map_pow, hA, map_one]
    exact congrArg Subtype.val hk)
  have hA3 : A ^ 3 ≠ 1 := fun h => hy3 (Subtype.ext (by
    rw [Subgroup.coe_pow, ← hA, ← map_pow, h, map_one]
    rfl))
  obtain ⟨P, t, hPt⟩ := exists_conj_HSL_of_three h31 A ⟨k, hAk⟩
  have hconjk : ∀ n : ℕ, HSL t ^ n = P * A ^ n * P⁻¹ := fun n => by rw [← hPt, conj_pow]
  have ht5 : 5 ≤ orderOf t := by
    refine five_le_orderOf_of_three ⟨k, HSLHom_injective (K := K) ?_⟩ fun h => hA3 ?_
    · rw [map_pow, map_one, HSLHom_apply, hconjk, hAk, mul_one, mul_inv_cancel]
    · have h1 : HSL t ^ 3 = 1 := by
        have := congrArg (HSLHom K) h
        rwa [map_pow, map_one, HSLHom_apply] at this
      rw [hconjk] at h1
      have h2 : A ^ 3 = P⁻¹ * (P * A ^ 3 * P⁻¹) * P := by group
      rw [h2, h1]
      group
  set m : adjointGroup .G2 K := ⟨rhoV K P, by
    rw [rhoV_apply]
    exact mul_mem (mul_mem (canonicalRep_mem_adjointGroup _ K _)
      (simpleRootSL2_mem_adjointGroup _ P)) (inv_mem (canonicalRep_mem_adjointGroup _ K _))⟩
  have hmS : m ∈ g2ShortSL2 K := mem_g2ShortSL2_iff.mpr ⟨P, rfl⟩
  have hmy : ((m * y * m⁻¹ : adjointGroup .G2 K) : ModGL .G2 K) =
      rootDiagUnit .G2 (Pi.mulSingle g2ir t) := by
    rw [coe_conj, ← hA, ← rhoV_HSL, ← hPt]
    simp only [map_mul, map_inv]
    rfl
  have hcen : ∀ x ∈ Subgroup.centralizer ({y} : Set (adjointGroup .G2 K)),
      ((m * x * m⁻¹ : adjointGroup .G2 K) : ModGL .G2 K) ∈
        torusGroup .G2 K ⊔ (rootSubgroup .G2 K g2e0 ⊔ rootSubgroup .G2 K (-g2e0)) := by
    intro x hx
    rw [← toralCentralizer_shortNine (le_trans (by norm_num) ht5), ← mem_centralizer_iff_toral hmy]
    exact conj_mem_centralizer hx
  have hmM : ∀ s ∈ g2LongSL2 K, m * s = s * m := fun s hs => g2Short_commute_g2Long hmS hs
  refine ⟨fun x hx w hw => ?_, fun x hx hxS => ?_⟩
  · have h := commutator_mem_of_mem_sup torus_comm
      (torusGroup_le_normalizer_rootPair (K := K) (isRoot_single .G2 g2l)) (hcen x hx) (hcen w hw)
    refine mem_of_conj_mem hmM ?_
    change ((m * (x * w * x⁻¹ * w⁻¹) * m⁻¹ : adjointGroup .G2 K) : ModGL .G2 K) ∈
      rootSubgroup .G2 K g2e0 ⊔ rootSubgroup .G2 K (-g2e0)
    convert h using 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  ·
    have hxS' : m * x * m⁻¹ ∈ Subgroup.centralizer (g2ShortSL2 K : Set (adjointGroup .G2 K)) := by
      rw [Subgroup.mem_centralizer_iff] at hxS ⊢
      intro s hs
      have h1 : m⁻¹ * s * m ∈ g2ShortSL2 K :=
        mul_mem (mul_mem (inv_mem hmS) hs) hmS
      have h2 := hxS _ h1
      calc s * (m * x * m⁻¹) = m * ((m⁻¹ * s * m) * x) * m⁻¹ := by group
        _ = m * (x * (m⁻¹ * s * m)) * m⁻¹ := by rw [h2]
        _ = m * x * m⁻¹ * s := by group
    have hset := Subgroup.coe_mul_of_left_le_normalizer_right _ _
      (torusGroup_le_normalizer_rootPair (K := K) (isRoot_single .G2 g2l))
    have hx' : ((m * x * m⁻¹ : adjointGroup .G2 K) : ModGL .G2 K) ∈
        ((torusGroup .G2 K ⊔ (rootSubgroup .G2 K g2e0 ⊔ rootSubgroup .G2 K (-g2e0)) :
          Subgroup (ModGL .G2 K)) : Set (ModGL .G2 K)) := hcen x hx
    rw [hset] at hx'
    obtain ⟨t', ht', u, hu, htu⟩ := hx'
    have hv1 : pinnedX .G2 K g2δ 1 ∈ rootSubgroup .G2 K g2δ ⊔ rootSubgroup .G2 K (-g2δ) :=
      Subgroup.mem_sup_left (mem_rootSubgroup.mpr ⟨1, rfl⟩)
    have hv1C : pinnedX .G2 K g2δ 1 ∈ adjointGroup .G2 K := pinnedX_mem_adjointGroup _ _
    have hc1 : ((m * x * m⁻¹ : adjointGroup .G2 K) : ModGL .G2 K) * pinnedX .G2 K g2δ 1 =
        pinnedX .G2 K g2δ 1 * ((m * x * m⁻¹ : adjointGroup .G2 K) : ModGL .G2 K) :=
      (congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hxS' ⟨_, hv1C⟩ hv1)).symm
    have hc2 : u * pinnedX .G2 K g2δ 1 = pinnedX .G2 K g2δ 1 * u :=
      (KS11Lie2Proof.g2_commute' hu hv1).eq
    have htc : t' * pinnedX .G2 K g2δ 1 = pinnedX .G2 K g2δ 1 * t' := by
      have e : t' = ((m * x * m⁻¹ : adjointGroup .G2 K) : ModGL .G2 K) * u⁻¹ := by
        rw [← htu]; group
      rw [e]
      calc ((m * x * m⁻¹ : adjointGroup .G2 K) : ModGL .G2 K) * u⁻¹ * pinnedX .G2 K g2δ 1 =
          ((m * x * m⁻¹ : adjointGroup .G2 K) : ModGL .G2 K) * (u⁻¹ * pinnedX .G2 K g2δ 1) := by
            group
        _ = ((m * x * m⁻¹ : adjointGroup .G2 K) : ModGL .G2 K) * (pinnedX .G2 K g2δ 1 * u⁻¹) := by
            rw [(Commute.inv_left hc2).eq]
        _ = pinnedX .G2 K g2δ 1 * (((m * x * m⁻¹ : adjointGroup .G2 K) : ModGL .G2 K) * u⁻¹) := by
            rw [← mul_assoc, hc1, mul_assoc]
    have ht'M := mem_range_rhoA_of_torus ht' htc
    rw [← range_simpleRootSL2_g2] at hu
    have hmxM : m * x * m⁻¹ ∈ g2LongSL2 K := by
      rw [mem_g2LongSL2_iff, ← htu]
      exact mul_mem ht'M hu
    exact mem_of_conj_mem hmM hmxM

section ThreeA

open CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.LieType.Steinberg.RankTwo


@[expose] def ThreeAConcl (z : adjointGroup .G2 K) : Prop :=
  ∃ N : Subgroup (adjointGroup .G2 K),
    N ≤ Subgroup.centralizer ({z} : Set (adjointGroup .G2 K)) ∧
    (∀ x ∈ Subgroup.centralizer ({z} : Set (adjointGroup .G2 K)),
      ∀ y ∈ Subgroup.centralizer ({z} : Set (adjointGroup .G2 K)), x * y * x⁻¹ * y⁻¹ ∈ N) ∧
    CFSG.IsQuasisimple N ∧ ∃ x ∈ N, (∀ n ∈ N, x * n = n * x) ∧ x ≠ 1 ∧ x ^ 3 = 1

theorem threeAConcl_of_conj (m z : adjointGroup .G2 K) (h : ThreeAConcl (m * z * m⁻¹)) :
    ThreeAConcl z := by
  obtain ⟨N, hNC, hcomm, hNq, x, hxN, hxc, hx1, hx3⟩ := h
  set c : MulAut (adjointGroup .G2 K) := MulAut.conj m⁻¹
  have hcm : ∀ y, c (m * y * m⁻¹) = y := fun y => by
    simp only [c, MulAut.conj_apply, inv_inv]
    group
  have hcz : c (m * z * m⁻¹) = z := hcm z
  have hcen : ∀ y, y ∈ Subgroup.centralizer ({z} : Set (adjointGroup .G2 K)) →
      m * y * m⁻¹ ∈ Subgroup.centralizer ({m * z * m⁻¹} : Set (adjointGroup .G2 K)) :=
    fun y hy => conj_mem_centralizer hy
  refine ⟨N.map c.toMonoidHom, ?_, fun a ha b hb => ?_, ?_, c x, ⟨x, hxN, rfl⟩, ?_, ?_, ?_⟩
  · rintro _ ⟨n, hn, rfl⟩
    have h1 := hNC hn
    rw [Subgroup.mem_centralizer_singleton_iff] at h1 ⊢
    change c n * z = z * c n
    rw [← hcz, ← map_mul, h1, map_mul]
  · refine ⟨m * (a * b * a⁻¹ * b⁻¹) * m⁻¹, ?_, hcm _⟩
    have := hcomm _ (hcen a ha) _ (hcen b hb)
    rw [show m * (a * b * a⁻¹ * b⁻¹) * m⁻¹ = m * a * m⁻¹ * (m * b * m⁻¹) * (m * a * m⁻¹)⁻¹ *
      (m * b * m⁻¹)⁻¹ by group]
    exact this
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (N.equivMapOfInjective c.toMonoidHom c.injective) hNq
  · rintro _ ⟨n, hn, rfl⟩
    change c x * c n = c n * c x
    rw [← map_mul, ← map_mul, hxc n hn]
  · intro h
    exact hx1 (c.injective (h.trans (map_one c).symm))
  · rw [← map_pow, hx3, map_one]

theorem a2_long_roots {γ : Fin 2 → ℤ}
    (hγ : γ ∈ CFSG.LieType.RootSystem.roots
      (CFSG.LieType.Universal.SpecialLinear.isFiniteType_A 2) (∅ : Set (Fin 2))) :
    g2CommRoot (a2pos (γ 0, γ 1)) ∈ ({g2a, -g2a, g2b, -g2b, g2c, -g2c} :
      Set (Fin Tag.G2.rank → ℤ)) := by
  rcases mem_rootsA2.mp hγ with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (by decide +kernel)
  · exact Or.inr (Or.inr (Or.inl (by decide +kernel)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide +kernel)))))
  · exact Or.inr (Or.inl (by decide +kernel))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by decide +kernel))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by decide +kernel)))))

theorem exists_a2_root {α : Fin Tag.G2.rank → ℤ}
    (hα : α ∈ ({g2a, -g2a, g2b, -g2b, g2c, -g2c} : Set (Fin Tag.G2.rank → ℤ))) :
    ∃ γ ∈ CFSG.LieType.RootSystem.roots
      (CFSG.LieType.Universal.SpecialLinear.isFiniteType_A 2) (∅ : Set (Fin 2)),
      g2CommRoot (a2pos (γ 0, γ 1)) = α := by
  rcases hα with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨![1, 0], mem_rootsA2.mpr (Or.inl rfl), by decide +kernel⟩
  · exact ⟨![-1, 0], mem_rootsA2.mpr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), by decide +kernel⟩
  · exact ⟨![0, 1], mem_rootsA2.mpr (Or.inr (Or.inl rfl)), by decide +kernel⟩
  · exact ⟨![0, -1], mem_rootsA2.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))),
      by decide +kernel⟩
  · exact ⟨![1, 1], mem_rootsA2.mpr (Or.inr (Or.inr (Or.inl rfl))), by decide +kernel⟩
  · exact ⟨![-1, -1], mem_rootsA2.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))),
      by decide +kernel⟩

theorem isRoot_of_long {α : Fin Tag.G2.rank → ℤ}
    (hα : α ∈ ({g2a, -g2a, g2b, -g2b, g2c, -g2c} : Set (Fin Tag.G2.rank → ℤ))) :
    IsRoot .G2 α := by
  rcases hα with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [isRoot_g2a, IsRoot.neg isRoot_g2a, isRoot_g2b, IsRoot.neg isRoot_g2b, isRoot_g2c,
    IsRoot.neg isRoot_g2c]

theorem coe_a2y {γ : Fin 2 → ℤ}
    (hγ : γ ∈ CFSG.LieType.RootSystem.roots
      (CFSG.LieType.Universal.SpecialLinear.isFiniteType_A 2) (∅ : Set (Fin 2))) (c : K) :
    ((a2y γ c : adjointGroup .G2 K) : ModGL .G2 K) =
      pinnedX .G2 K (g2CommRoot (a2pos (γ 0, γ 1)))
        (((rootOperatorFamily .G2).pinnedFamilySign (g2CommRoot (a2pos (γ 0, γ 1))) : ℤ) * c) :=
  CFSG.ClassicalInvolution.Balance.coe_xPar_eq_pinnedX (isRoot_of_long (a2_long_roots hγ)) c

theorem range_le_of_a2y [Finite K] (φ : Matrix.SpecialLinearGroup (Fin (2 + 1)) K →*
      ↥(adjointGroup .G2 K))
    (hφ : ∀ γ ∈ CFSG.LieType.RootSystem.roots
      (CFSG.LieType.Universal.SpecialLinear.isFiniteType_A 2) (∅ : Set (Fin 2)), ∀ c : K,
      φ (CFSG.LieType.Steinberg.SL.x 2 K γ c) = a2y γ c) (H : Subgroup (adjointGroup .G2 K))
    (hH : ∀ γ ∈ CFSG.LieType.RootSystem.roots
      (CFSG.LieType.Universal.SpecialLinear.isFiniteType_A 2) (∅ : Set (Fin 2)), ∀ c : K,
        a2y γ c ∈ H) :
    φ.range ≤ H := by
  obtain ⟨⟨-, ⟨O⟩, hx, -⟩, -⟩ := sl3_rankTwoPresentation.{0} K
  have hgen := closure_range_eq_top_of_presentationB hx O
  rw [MonoidHom.range_eq_map, ← hgen, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨X, hX, rfl⟩
  simp only [Set.mem_iUnion, Set.mem_range] at hX
  obtain ⟨γ, hγ, c, rfl⟩ := hX
  rw [SetLike.mem_coe, hφ γ hγ c]
  exact hH γ hγ c

theorem threeAConcl_diag [Finite K] {ζ : Kˣ} (hζ : orderOf ζ = 3) {z : adjointGroup .G2 K}
    (hz : (z : ModGL .G2 K) = rootDiagUnit .G2 (Pi.mulSingle g2ir ζ)) : ThreeAConcl z := by
  obtain ⟨φ, hφinj, hφ⟩ := exists_a2Hom_injective (K := K)
  have hKer := rootCharKernel_threeA (K := K) hζ
  refine ⟨φ.range, ?_, fun x hx y hy => ?_, ?_, ?_⟩
  ·
    refine range_le_of_a2y φ hφ _ fun γ hγ c => ?_
    rw [mem_centralizer_iff_toral hz, mem_toralCentralizer]
    refine ⟨(a2y γ c).2, ?_⟩
    rw [coe_a2y hγ]
    have hmem : g2CommRoot (a2pos (γ 0, γ 1)) ∈ rootCharKernel (Pi.mulSingle g2ir ζ) := by
      rw [hKer]
      exact a2_long_roots hγ
    rw [rootDiagUnit_conj_pinnedX _ hmem.1, hmem.2, Units.val_one, one_mul]
  ·
    have hx' := (mem_centralizer_iff_toral hz).mp hx
    have hy' := (mem_centralizer_iff_toral hz).mp hy
    rw [toralCentralizer_threeA hζ] at hx' hy'
    have h := commutator_mem_of_mem_sup torus_comm
      (torusGroup_le_normalizer_rootSpan (K := K) fun α hα => isRoot_of_long hα) hx' hy'
    have hle : rootSpan .G2 K {g2a, -g2a, g2b, -g2b, g2c, -g2c} ≤
        φ.range.map (adjointGroup .G2 K).subtype := by
      refine iSup₂_le fun α hα => fun g hg => ?_
      obtain ⟨c, rfl⟩ := mem_rootSubgroup.mp hg
      obtain ⟨γ, hγ, rfl⟩ := exists_a2_root hα
      set s := (rootOperatorFamily .G2).pinnedFamilySign (g2CommRoot (a2pos (γ 0, γ 1)))
      refine ⟨φ (CFSG.LieType.Steinberg.SL.x 2 K γ ((s : K) * c)), ⟨_, rfl⟩, ?_⟩
      rw [Subgroup.coe_subtype, hφ γ hγ, coe_a2y hγ, ← mul_assoc,
        (rootOperatorFamily .G2).pinnedFamilySign_mul_self K, one_mul]
    obtain ⟨w, hw, hwe⟩ := hle h
    have : w = x * y * x⁻¹ * y⁻¹ := Subtype.ext (by
      rw [Subgroup.coe_subtype] at hwe
      rw [hwe]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv])
    rw [← this]
    exact hw
  ·
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (MonoidHom.ofInjective hφinj)
      (CFSG.RankThree.Classical2.isQuasisimple_specialLinearGroup (by norm_num))
  ·
    have hζ3 : ζ ^ 3 = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
    set X : Matrix.SpecialLinearGroup (Fin (2 + 1)) K :=
      ⟨Matrix.scalar (Fin (2 + 1)) (ζ : K), by
        rw [Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin, ← Units.val_pow_eq_pow_val, hζ3, Units.val_one]⟩ with hX
    have hXc : ∀ Y : Matrix.SpecialLinearGroup (Fin (2 + 1)) K, X * Y = Y * X := fun Y =>
      Subtype.ext (by
        rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hX]
        exact (Matrix.scalar_commute (ζ : K) (fun r => Commute.all _ r) _))
    refine ⟨φ X, ⟨X, rfl⟩, ?_, ?_, ?_⟩
    · rintro _ ⟨Y, rfl⟩
      rw [← map_mul, ← map_mul, hXc]
    · intro h
      have h1 : X = 1 := hφinj (h.trans (map_one φ).symm)
      have h2 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin (2 + 1)) K =>
        (A : Matrix (Fin (2 + 1)) (Fin (2 + 1)) K) 0 0) h1
      simp only [hX, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
        Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_eq] at h2
      have : ζ = 1 := Units.ext (by simpa using h2)
      rw [this, orderOf_one] at hζ
      exact absurd hζ (by norm_num)
    · rw [← map_pow]
      have : X ^ 3 = 1 := Subtype.ext (by
        rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
        change (Matrix.scalar (Fin (2 + 1)) (ζ : K)) ^ 3 = 1
        rw [← map_pow, ← Units.val_pow_eq_pow_val, hζ3, Units.val_one, map_one])
      rw [this, map_one]

theorem g2ThreeACent_split [Finite K] (h31 : 3 ∣ Nat.card K - 1) {z : adjointGroup .G2 K}
    (hzS : z ∈ g2ShortSL2 K) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) : ThreeAConcl z := by
  obtain ⟨A, hA⟩ := mem_g2ShortSL2_iff.mp hzS
  have hinj := rhoV_injective (K := K)
  have hA3 : A ^ 3 = 1 := hinj (by
    rw [map_pow, hA, map_one]
    exact congrArg Subtype.val hz3)
  obtain ⟨P, t, hPt⟩ := exists_conj_HSL_of_three h31 A ⟨1, by simpa using hA3⟩
  have ht3 : orderOf t = 3 := by
    refine orderOf_eq_prime ?_ ?_
    · apply HSLHom_injective (K := K)
      rw [map_pow, HSLHom_apply, ← hPt, conj_pow, hA3, mul_one, mul_inv_cancel, map_one]
    · rintro rfl
      apply hz1
      have h1 : A = 1 := by
        have : P * A * P⁻¹ = 1 := by rw [hPt]; exact (map_one (HSLHom K))
        simpa using this
      apply Subtype.ext
      rw [← hA, h1, map_one]
      rfl
  set m : adjointGroup .G2 K := ⟨rhoV K P, by
    rw [rhoV_apply]
    exact mul_mem (mul_mem (canonicalRep_mem_adjointGroup _ K _)
      (simpleRootSL2_mem_adjointGroup _ P)) (inv_mem (canonicalRep_mem_adjointGroup _ K _))⟩
  have hmz : ((m * z * m⁻¹ : adjointGroup .G2 K) : ModGL .G2 K) =
      rootDiagUnit .G2 (Pi.mulSingle g2ir t) := by
    rw [coe_conj, ← hA, ← rhoV_HSL, ← hPt]
    simp only [map_mul, map_inv]
    rfl
  exact threeAConcl_of_conj m z (threeAConcl_diag ht3 hmz)

theorem primitive_cube_root_of_orderOf {ζ : Kˣ} (hζ : orderOf ζ = 3) :
    (ζ : K) ^ 2 + ζ + 1 = 0 ∧ (ζ : K) ≠ 1 := by
  have hζ3 : (ζ : K) ^ 3 = 1 := by
    have h := pow_orderOf_eq_one ζ
    rw [hζ] at h
    simpa using congrArg Units.val h
  have hζ1 : (ζ : K) ≠ 1 := fun h => by
    have h1 : ζ = 1 := Units.ext (by simpa using h)
    rw [h1, orderOf_one] at hζ
    exact absurd hζ (by norm_num)
  refine ⟨?_, hζ1⟩
  have h : ((ζ : K) - 1) * ((ζ : K) ^ 2 + ζ + 1) = 0 := by linear_combination hζ3
  rcases mul_eq_zero.1 h with h | h
  · exact absurd (sub_eq_zero.1 h) hζ1
  · exact h

theorem exists_conj_torus_of_cube [Finite K] (h31 : 3 ∣ Nat.card K - 1) (z : adjointGroup .G2 K)
    (hz3 : z ^ 3 = 1) :
    ∃ (g : adjointGroup .G2 K) (b : Fin Tag.G2.rank → Kˣ),
      ((g * z * g⁻¹ : adjointGroup .G2 K) : ModGL .G2 K) = rootDiagUnit .G2 b := by
  obtain ⟨φ, hφinj, hφ⟩ := exists_a2Hom_injective (K := K)
  have hE : IsPGroup 3 (Subgroup.zpowers z) := by
    rintro ⟨g, hg⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨1, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one, pow_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz3, one_zpow]
  obtain ⟨y, hy⟩ := exists_conj_le_range_of_three_dvd_sub_one h31 φ hφinj _ hE
  obtain ⟨X, hX⟩ : y * z * y⁻¹ ∈ φ.range := hy ⟨z, Subgroup.mem_zpowers z, rfl⟩
  have hX3 : X ^ 3 = 1 := hφinj (by
    rw [map_pow, hX, conj_pow, hz3, mul_one, mul_inv_cancel, map_one])
  obtain ⟨ζ, hζ⟩ := exists_units_orderOf_eq_of_dvd_card_sub_one Nat.prime_three h31
  obtain ⟨hω, hω1⟩ := primitive_cube_root_of_orderOf hζ
  obtain ⟨Y, hY⟩ := exists_diagonalizing_of_commuting_cube_one (ζ : K) hω hω1
    (Subgroup.zpowers X) (fun x hx => by
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hX3, one_zpow])
    (fun x hx w hw => by
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      rw [← zpow_add, ← zpow_add, add_comm])
  have hd := phi_diag_mem_torusGroup φ hφ (Y * X * Y⁻¹) (hY X (Subgroup.mem_zpowers X))
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hd
  refine ⟨φ Y * y, b, ?_⟩
  rw [← hb, map_mul, map_mul, map_inv, hX]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  group

theorem rootDiagUnit_threeB_conj (ζ : Kˣ) :
    rootDiagUnit .G2 (fun j => ζ ^ Tag.G2.cartan g2ia j) =
      canonicalRep (coxeterSystem .G2) K wV * rootDiagUnit .G2 (Pi.mulSingle g2ia ζ) *
        (canonicalRep (coxeterSystem .G2) K wV)⁻¹ := by
  refine (rootDiagUnit_eq_conj_canonicalRep_iff _ _ wV).mpr
    (rootChar_smul_eq_of_single fun i => ?_)
  have c0 : Tag.G2.cartan g2ia g2ia = 2 := by decide
  have c1 : Tag.G2.cartan g2ia g2ir = -1 := by decide
  have hne : g2ir ≠ g2ia := by decide
  rw [rootChar_g2, rootChar_g2]
  simp only [c0, c1]
  rcases fin_G2_cases i with rfl | rfl
  · rw [show (wV • (Pi.single g2ia 1 : Fin Tag.G2.rank → ℤ)) = g2w0 from g2_w_smul_e0]
    have e0 : g2w0 g2ia = -1 := by decide
    have e1 : g2w0 g2ir = -3 := by decide
    rw [e0, e1, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hne, Pi.single_eq_same,
      Pi.single_eq_of_ne hne, ← zpow_mul, ← zpow_mul, ← zpow_add, one_zpow, mul_one]
    norm_num
  · rw [show (wV • (Pi.single g2ir 1 : Fin Tag.G2.rank → ℤ)) = g2δ from g2_w_smul]
    have e0 : g2δ g2ia = 1 := rfl
    have e1 : g2δ g2ir = 2 := rfl
    rw [e0, e1, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hne, Pi.single_eq_same,
      Pi.single_eq_of_ne hne.symm, ← zpow_mul, ← zpow_mul, ← zpow_add, one_zpow, zpow_zero]
    norm_num

theorem g2ThreeConjSL2_split [Finite K] (h31 : 3 ∣ Nat.card K - 1) {z : adjointGroup .G2 K}
    (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) :
    ∃ g : adjointGroup .G2 K, g * z * g⁻¹ ∈ g2ShortSL2 K ∨ g * z * g⁻¹ ∈ g2LongSL2 K := by
  obtain ⟨g₁, b, hb⟩ := exists_conj_torus_of_cube h31 z hz3
  have hb3 : b ^ 3 = 1 := by
    apply rootDiagUnit_injective (τ := .G2) (K := K)
    change rootDiagUnitHom .G2 K (b ^ 3) = rootDiagUnitHom .G2 K 1
    rw [map_pow, map_one]
    change rootDiagUnit .G2 b ^ 3 = 1
    rw [← hb, ← Subgroup.coe_pow, conj_pow, hz3, mul_one, mul_inv_cancel, Subgroup.coe_one]
  have hb1 : b ≠ 1 := by
    rintro rfl
    apply hz1
    have h1 : g₁ * z * g₁⁻¹ = 1 := Subtype.ext (by
      rw [hb, Subgroup.coe_one]
      exact rootDiagUnit_one')
    rw [mul_inv_eq_one, mul_eq_left] at h1
    exact h1
  by_cases hb0 : b g2ia = 1
  ·
    refine ⟨g₁, Or.inl (mem_g2ShortSL2_iff.mpr ⟨HSL (b g2ir), ?_⟩)⟩
    rw [rhoV_HSL, hb]
    congr 1
    funext j
    rcases fin_G2_cases j with rfl | rfl
    · rw [hb0, Pi.mulSingle_eq_of_ne (by decide)]
    · rw [Pi.mulSingle_eq_same]
  · obtain ⟨w, ζ, -, hw⟩ := exists_weyl_threeB hb3 hb0
    have h1 := (rootDiagUnit_eq_conj_canonicalRep_iff b (Pi.mulSingle g2ia ζ) w).mpr hw
    set n : adjointGroup .G2 K :=
      ⟨canonicalRep (coxeterSystem .G2) K w, canonicalRep_mem_adjointGroup _ K w⟩ with hn
    set n' : adjointGroup .G2 K :=
      ⟨canonicalRep (coxeterSystem .G2) K wV, canonicalRep_mem_adjointGroup _ K wV⟩ with hn'
    refine ⟨n' * n⁻¹ * g₁, Or.inr (mem_g2LongSL2_iff.mpr ⟨HSL ζ, ?_⟩)⟩
    have hnv : (n : ModGL .G2 K) = canonicalRep (coxeterSystem .G2) K w := rfl
    have hnv' : (n' : ModGL .G2 K) = canonicalRep (coxeterSystem .G2) K wV := rfl
    have h2 : rootDiagUnit .G2 (Pi.mulSingle g2ia ζ) =
        (n : ModGL .G2 K)⁻¹ * rootDiagUnit .G2 b * (n : ModGL .G2 K) := by
      rw [h1, hnv]
      group
    rw [rhoA_HSL, rootDiagUnit_threeB_conj, h2, ← hb]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hnv']
    group

end ThreeA

end CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof
