module

public import CFSG.Quasithin.EmptyFaithful.LRed5Plumb
public import CFSG.Quasithin.EmptyFaithful.LRed5Pair
public import CFSG.Quasithin.EmptyFaithful.S146yU3
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.Dihedral.FourgroupCycleControl
public import CFSG.Dihedral.OriginalCentralizerOddCore
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherWalterSchurEight
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwo
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupExhaustion
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRanks
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoFourGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsReduction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFullObstruction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourProperSubgroups
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Background.A3Structure36BCase3
public import CFSG.Quasithin.Background.A3Structure36BCases
public import CFSG.Quasithin.Background.A3Structure36BCommon
public import CFSG.Quasithin.Background.A3Structure36BStar
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B5CompA
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.B5FinOut
public import CFSG.Quasithin.Background.C1PackS1531Top
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.D2Cyclic
public import CFSG.Quasithin.Background.E2Statements
public import CFSG.Quasithin.Background.E2Three
public import CFSG.Quasithin.Background.E3
public import CFSG.Quasithin.Background.E3Nprime
public import CFSG.Quasithin.Background.E3Uniq
public import CFSG.Quasithin.Background.F6CatRecogL2
public import CFSG.Quasithin.Background.F6CatRecogTools2
public import CFSG.Quasithin.Background.FFC5Case1
public import CFSG.Quasithin.Background.FFC5Dich
public import CFSG.Quasithin.Background.FFC5Main
public import CFSG.Quasithin.Background.G2Omega4PlusQuot
public import CFSG.Quasithin.Background.G2Relaxed
public import CFSG.Quasithin.Background.G64SymCase
public import CFSG.Quasithin.Background.InternalSecData
public import CFSG.Quasithin.Background.InternalSecIso
public import CFSG.Quasithin.Background.S1567Z4
public import CFSG.Quasithin.EmptyFaithful.Insp11Irr
public import CFSG.Quasithin.EmptyFaithful.Insp9Cases4
public import CFSG.Quasithin.EmptyFaithful.S14110
public import CFSG.Quasithin.EmptyFaithful.S152UGen
public import CFSG.Quasithin.EmptyFaithful.S152Y15
public import CFSG.Quasithin.EmptyFaithful.S153E58A
public import CFSG.Quasithin.EmptyFaithful.S153E58B
public import CFSG.Quasithin.EmptyFaithful.S153E59A
public import CFSG.Quasithin.EmptyFaithful.T1515Der
public import CFSG.Quasithin.EmptyFaithful.T1531Final
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch11SecA02NatFix
public import CFSG.Quasithin.Vol2.Ch11SecA02Setup
public import CFSG.Quasithin.Vol2.Ch11SecA03Basic
public import CFSG.Quasithin.Vol2.Ch11SecA04Glue
public import CFSG.Quasithin.Vol2.Ch11SecA11Exists
public import CFSG.Quasithin.Vol2.Ch11SecAFacts03
public import CFSG.Quasithin.Vol2.Ch11SecAFacts04
public import CFSG.Quasithin.Vol2.Ch11SecAVi2
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma8
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.Walter.J1Props
public import CFSG.Walter.J1Recog
public import CFSG.Walter.PSL2Facts
public import CFSG.Walter.W67.Statements
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
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99

public section

namespace CFSG.Quasithin

namespace LRed5

section Fin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem image_facts {H K : Subgroup G} (hK : K ∈ cComp H) (hS : IsSimpleGroup (KBar K))
    {W : Type} [CommGroup W] (ρ : ↥H →* MulAut W)
    (hker : ∀ x : ↥H, ρ x = 1 ↔ (x : G) ∈ pCoreOf 2 H) :
    CFSG.IsQuasisimple ↥((K.subgroupOf H).map ρ) ∧ Centerless ((K.subgroupOf H).map ρ) ∧
      Nonempty (KBar K ≃* ↥((K.subgroupOf H).map ρ)) := by
  obtain ⟨e⟩ := kbar_equiv_image hK ρ hker
  have hLsimple : IsSimpleGroup ↥((K.subgroupOf H).map ρ) := e.symm.isSimpleGroup
  have hnc : ¬ IsMulCommutative ↥((K.subgroupOf H).map ρ) := by
    intro hc
    apply not_isMulCommutative_kbar hK
    exact ⟨⟨fun a b => e.injective (by rw [map_mul, map_mul]; exact mul_comm' _ _)⟩⟩
  have hcenter : Subgroup.center ↥((K.subgroupOf H).map ρ) = ⊥ := center_eq_bot_of_isSimpleGroup hnc
  have hZ : Centerless ((K.subgroupOf H).map ρ) := by
    intro x hx hxc
    have : (⟨x, hx⟩ : ↥((K.subgroupOf H).map ρ)) ∈ Subgroup.center ↥((K.subgroupOf H).map ρ) :=
      Subgroup.mem_center_iff.2 fun z => Subtype.ext (hxc z z.2).symm
    rw [hcenter, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  have : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.2 (perfect_of_mem_cComp hK)
  have hpKbar : Group.IsPerfect (KBar K) := inferInstance
  have hperfL : Group.IsPerfect ↥((K.subgroupOf H).map ρ) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hnc' : ∃ a b : ↥((K.subgroupOf H).map ρ), a * b ≠ b * a := by
    by_contra h
    push Not at h
    exact hnc ⟨⟨fun a b => h a b⟩⟩
  exact ⟨isQuasisimple_of_simple_nonabelian hperfL hnc', hZ, ⟨e⟩⟩

omit [Finite G] in
theorem centerless_sup {X : Type*} [Group X] {L₁ L₂ : Subgroup X}
    (hc : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) (h₁ : Centerless L₁) (h₂ : Centerless L₂) :
    Centerless (L₁ ⊔ L₂) := by
  intro x hx hxc
  obtain ⟨a, ha, b, hb, rfl⟩ := LRed4.exists_mul_of_mem_sup_comm hc hx
  have ha1 : a = 1 := h₁ a ha fun y hy => by
    have h := hxc y (Subgroup.mem_sup_left hy)
    have e1 : a * b * y = a * y * b := by rw [mul_assoc, ← hc y hy b hb, mul_assoc]
    have e2 : y * (a * b) = y * a * b := by rw [mul_assoc]
    rw [e1, e2] at h
    exact mul_right_cancel h
  have hb1 : b = 1 := h₂ b hb fun y hy => by
    have h := hxc y (Subgroup.mem_sup_right hy)
    have e1 : y * (a * b) = a * y * b := by rw [← mul_assoc, ← hc a ha y hy]
    rw [e1] at h
    have h' : a * (b * y) = a * (y * b) := by rw [← mul_assoc, ← mul_assoc]; exact h
    exact mul_left_cancel h'
  rw [ha1, hb1, one_mul]
theorem card_eq_mul_two_pow {Γ L T₀ : Subgroup G} (hLΓ : L ≤ Γ) (hn : (L.subgroupOf Γ).Normal)
    (hT₀Γ : T₀ ≤ Γ) (hT₀ : IsPGroup 2 T₀) (hΓ : Γ = L ⊔ T₀) :
    ∃ k : ℕ, Nat.card ↥Γ = Nat.card ↥L * 2 ^ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsup : L.subgroupOf Γ ⊔ T₀.subgroupOf Γ = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hLΓ hT₀Γ, ← hΓ]
    exact Subgroup.subgroupOf_self _
  have hT₀' : IsPGroup 2 (T₀.subgroupOf Γ) := hT₀.of_equiv (Subgroup.subgroupOfEquivOfLe hT₀Γ).symm
  have hQ := isPGroup_quotient_of_sup hsup hT₀'
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hQ
  refine ⟨k, ?_⟩
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (L.subgroupOf Γ), hk,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLΓ).toEquiv, mul_comm]

omit [Finite G] in
theorem normal_map_range {H : Subgroup G} {W : Type} [CommGroup W] (ρ : ↥H →* MulAut W)
    {N : Subgroup ↥H} (hN : N.Normal) : ((N.map ρ).subgroupOf ρ.range).Normal := by
  have hrs : (N.map ρ).subgroupOf ρ.range = N.map ρ.rangeRestrict := by
    ext y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map, Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, hxy⟩
      exact ⟨x, hx, Subtype.ext hxy⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
  rw [hrs]
  exact hN.map ρ.rangeRestrict ρ.rangeRestrict_surjective

theorem noFaithfulFFPair_of_b56 (h56 : AsB56) : NoFaithfulFFPair := by
  classical
  intro G _ _ T M S hB c19 c20 K hK hcase2 hL32 hHeq
  obtain ⟨t, htT, htK, hper⟩ := hcase2
  have hHTM : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hTH : T ≤ mcOf T := hHTM.1.1
  have hKH : K ≤ mcOf T := le_of_mem_cComp hK
  have hsqtk : SQTKGroup ↥(mcOf T) := S.sqtkGroup_of_isHTM hHTM
  have hT2 : IsPGroup 2 T := S.hyp.sylow.1
  have hcperf : perfectCore (mcOf T) ≤ mcOf T := perfectCore_le _
  have hHnorm : mcOf T ≤ Subgroup.normalizer ((perfectCore (mcOf T) : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hcperf).mp (perfectCore_normal _)
  have hK₀ : conjClosure K T = perfectCore (mcOf T) := by
    apply le_antisymm
    · refine conjClosure_le fun t' ht' z hz => ?_
      exact (Subgroup.mem_normalizer_iff.mp (hHnorm (hTH ht')) z).mp
        (le_perfectCore_of_perfect (le_of_mem_cComp hK) (perfect_of_mem_cComp hK) hz)
    · rw [hper]
      refine sup_le (le_conjClosure K T) ?_
      rintro _ ⟨z, hz, rfl⟩
      exact mem_conjClosure htT hz
  rw [hK₀] at hHeq ⊢
  rw [← hHeq]
  intro W _ _ hW ρ hker hff
  set K₂ := conjSub t K with hK₂def
  have hK₂ : K₂ ∈ cComp (mcOf T) := map_conj_mem_cComp hK (hTH htT)
  have hne : K₂ ≠ K := fun h => htK (A38.map_conj_eq_iff.mp h)
  have hcomps : ∀ L ∈ cComp (mcOf T), L = K ∨ L = K₂ := fun L hL =>
    cComp_eq_of_le_sup hL hK hK₂
      (hper ▸ le_perfectCore_of_perfect (le_of_mem_cComp hL) (perfect_of_mem_cComp hL))
  have hK₂H : K₂ ≤ mcOf T := le_of_mem_cComp hK₂
  set Γ := ρ.range with hΓ
  set L₁ := (K.subgroupOf (mcOf T)).map ρ with hL₁
  set L₂ := (K₂.subgroupOf (mcOf T)).map ρ with hL₂
  set t' : ↥(mcOf T) := ⟨t, hTH htT⟩ with ht'
  obtain ⟨hq₁, hz₁, ⟨e₁⟩⟩ := image_facts hK ((c19 _ hHTM).2 K hK) ρ hker
  obtain ⟨hq₂, hz₂, -⟩ := image_facts hK₂ ((c19 _ hHTM).2 K₂ hK₂) ρ hker
  have hL₁Γ : L₁ ≤ Γ := Subgroup.map_le_range ρ _
  have hL₂Γ : L₂ ≤ Γ := Subgroup.map_le_range ρ _
  have hcard₁ : Nat.card ↥L₁ = 168 := by
    rw [← Nat.card_congr e₁.toEquiv]
    obtain ⟨e3⟩ := hL32
    rw [Nat.card_congr e3.toEquiv]
    exact card_sl3_zmod
  have hswap₁ : ∀ x ∈ L₁, ρ t' * x * (ρ t')⁻¹ ∈ L₂ := by
    intro x hx
    obtain ⟨k, hkK, rfl⟩ := exists_of_mem_map ρ hx
    have : ρ t' * ρ k * (ρ t')⁻¹ = ρ (t' * k * t'⁻¹) := by simp [map_mul, map_inv]
    rw [this]
    exact Subgroup.mem_map_of_mem ρ
      (show (t' * k * t'⁻¹ : ↥(mcOf T)) ∈ K₂.subgroupOf (mcOf T) from mul_mem_conjSub hkK)
  have hswap₂ : ∀ y ∈ L₂, (ρ t')⁻¹ * y * ρ t' ∈ L₁ := by
    intro y hy
    obtain ⟨k, hkK, rfl⟩ := exists_of_mem_map ρ hy
    have : (ρ t')⁻¹ * ρ k * ρ t' = ρ (t'⁻¹ * k * t') := by simp [map_mul, map_inv]
    rw [this]
    have h1 : t⁻¹ * (k : G) * t ∈ K := mem_conjSub.mp (hkK : (k : G) ∈ conjSub t K)
    exact Subgroup.mem_map_of_mem ρ
      (show (t'⁻¹ * k * t' : ↥(mcOf T)) ∈ K.subgroupOf (mcOf T) from h1)
  have hcard₂ : Nat.card ↥L₂ = 168 := by
    have h1 : Nat.card ↥L₁ ≤ Nat.card ↥L₂ :=
      Nat.card_le_card_of_injective
        (fun x : ↥L₁ => (⟨ρ t' * x * (ρ t')⁻¹, hswap₁ x x.2⟩ : ↥L₂)) (by
          intro a b h
          exact Subtype.ext (by simpa using congrArg Subtype.val h))
    have h2 : Nat.card ↥L₂ ≤ Nat.card ↥L₁ :=
      Nat.card_le_card_of_injective
        (fun y : ↥L₂ => (⟨(ρ t')⁻¹ * y * ρ t', hswap₂ y y.2⟩ : ↥L₁)) (by
          intro a b h
          exact Subtype.ext (by simpa using congrArg Subtype.val h))
    omega
  have hcomm₀ : ⁅K, K₂⁆ ≤ pCoreOf 2 (mcOf T) :=
    (cComp_ne_commutator_le_solvRad hK hK₂ hne.symm).trans
      (solvRad_le_pCoreOf_of_oddCore (hB _ hHTM))
  have hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, hkK, rfl⟩ := exists_of_mem_map ρ ha
    obtain ⟨k₂, hk₂, rfl⟩ := exists_of_mem_map ρ hb
    have h1 : ρ (k * k₂ * k⁻¹ * k₂⁻¹) = 1 := (hker _).2 (by
      have := hcomm₀ (Subgroup.commutator_mem_commutator hkK hk₂)
      simpa [commutatorElement_def] using this)
    simp only [map_mul, map_inv] at h1
    exact commutatorElement_eq_one_iff_mul_comm.mp (by simpa [commutatorElement_def] using h1)
  have hLsup : L₁ ⊔ L₂ = ((perfectCore (mcOf T)).subgroupOf (mcOf T)).map ρ := by
    rw [hper, Subgroup.subgroupOf_sup hKH hK₂H, Subgroup.map_sup]
  have hLΓ : L₁ ⊔ L₂ ≤ Γ := sup_le hL₁Γ hL₂Γ
  have hLn : ((L₁ ⊔ L₂).subgroupOf Γ).Normal := by
    rw [hLsup]
    exact normal_map_range ρ (perfectCore_normal _)
  have hnormal : ∀ g ∈ Γ, ∀ x ∈ L₁ ⊔ L₂, g * x * g⁻¹ ∈ L₁ ⊔ L₂ := fun g hg x hx =>
    (Subgroup.mem_normalizer_iff.mp (EmptyFaithfulMultiple.FFL.le_normalizer_of_normal hLΓ hLn hg) x).mp hx
  set T₀ := (T.subgroupOf (mcOf T)).map ρ with hT₀
  have hT₀2 : IsPGroup 2 T₀ := (hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTH).symm).map ρ
  have hT₀Γ : T₀ ≤ Γ := Subgroup.map_le_range ρ _
  have hΓeq : Γ = (L₁ ⊔ L₂) ⊔ T₀ := by
    have h1 : (perfectCore (mcOf T)).subgroupOf (mcOf T) ⊔ T.subgroupOf (mcOf T) = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hcperf hTH, ← hHeq]
      exact Subgroup.subgroupOf_self _
    rw [hΓ, MonoidHom.range_eq_map, ← h1, Subgroup.map_sup, hLsup]
  have hO2 : pCoreOf 2 Γ = ⊥ := pCoreOf_range_eq_bot ρ hker
  have hZ := centerless_sup hcomm hz₁ hz₂
  have hC := centralizer_eq_bot_of_two_quotient hLΓ hLn hZ hT₀Γ hT₀2 hΓeq hO2
  have hQ : G64.IsQuotientOfSQTKCat ↥Γ :=
    ⟨↥(mcOf T), inferInstance, inferInstance, ρ.ker, inferInstance, SQTKGroup.isSQTKCat hsqtk,
      ⟨(QuotientGroup.quotientKerEquivRange ρ).symm⟩⟩
  obtain ⟨-, s, hs, hdyn⟩ := c20 _ hHTM K hK
  have hsT : s ∈ T := hs.1
  have hsK : s ∈ Subgroup.normalizer (K : Set G) := hs.2
  set s' : ↥(mcOf T) := ⟨s, hTH hsT⟩ with hs'
  have hout : KbarInducesOuter K (s' : G) := by
    rcases hdyn with ⟨-, hout⟩ | ⟨he6, -⟩
    · exact hout
    · exfalso
      obtain ⟨e6⟩ := he6
      have h1 : Nat.card (KBar K) = 168 := by rw [Nat.card_congr e₁.toEquiv]; exact hcard₁
      rw [Nat.card_congr e6.toEquiv, card_alternatingGroup1527d 6 (by norm_num)] at h1
      norm_num [Nat.factorial] at h1
  have hout' := outer_transfer hK ρ hker (s := s') hsK hout
  have hs₁ : ∀ x ∈ L₁, ρ s' * x * (ρ s')⁻¹ ∈ L₁ := by
    intro x hx
    obtain ⟨k, hkK, rfl⟩ := exists_of_mem_map ρ hx
    have : ρ s' * ρ k * (ρ s')⁻¹ = ρ (s' * k * s'⁻¹) := by simp [map_mul, map_inv]
    rw [this]
    exact Subgroup.mem_map_of_mem ρ
      (show (s' * k * s'⁻¹ : ↥(mcOf T)) ∈ K.subgroupOf (mcOf T) from
        (Subgroup.mem_normalizer_iff.mp hsK (k : G)).mp hkK)
  have hs₁' : ∀ x ∈ L₁, (ρ s')⁻¹ * x * ρ s' ∈ L₁ := by
    intro x hx
    obtain ⟨k, hkK, rfl⟩ := exists_of_mem_map ρ hx
    have : (ρ s')⁻¹ * ρ k * ρ s' = ρ (s'⁻¹ * k * s') := by simp [map_mul, map_inv]
    rw [this]
    exact Subgroup.mem_map_of_mem ρ
      (show (s'⁻¹ * k * s' : ↥(mcOf T)) ∈ K.subgroupOf (mcOf T) from by
        have h2 : s⁻¹ * (k : G) * s ∈ K := by
          have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hsK) (k : G)).mp hkK
          simpa using this
        exact h2)
  have hV : ∀ v : W, v * v = 1 := fun v => by rw [← sq]; exact hW v
  have P : PairData Γ L₁ L₂ (ρ t') :=
    { le₁ := hL₁Γ
      le₂ := hL₂Γ
      q₁ := hq₁
      q₂ := hq₂
      z₁ := hz₁
      z₂ := hz₂
      c₁ := hcard₁
      c₂ := hcard₂
      comm := hcomm
      tΓ := ⟨t', rfl⟩
      swap₁ := hswap₁
      swap₂ := hswap₂
      normal := hnormal
      cent := fun g hg hx => by
        have : g ∈ Γ ⊓ Subgroup.centralizer ((L₁ ⊔ L₂ : Subgroup (MulAut W)) : Set (MulAut W)) :=
          ⟨hg, Subgroup.mem_centralizer_iff.2 fun h hh => (hx h hh).symm⟩
        rw [hC] at this
        exact Subgroup.mem_bot.1 this
      two := card_eq_mul_two_pow hLΓ hLn hT₀Γ hT₀2 hΓeq
      o2 := hO2
      sqtk := hQ
      off := B6.exists_isFFStarOffender hff }
  exact false_of_pair_outer h56 hV P ⟨s', rfl⟩ hs₁ hs₁' hout'

theorem noFaithfulFF_of_b56
    (h56 : AsB56) (h21 : Stage14621) : NoFaithfulFFInput :=
  noFaithfulFF_of_inputs h56 h21 (noFaithfulFFPair_of_b56 h56)

end Fin

end LRed5

end CFSG.Quasithin
