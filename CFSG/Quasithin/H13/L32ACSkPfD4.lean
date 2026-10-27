module

public import CFSG.Quasithin.H13.L32ACSkPfB
public import CFSG.Quasithin.H13.L32ACSk10
public import CFSG.RankThree.PartTwo.KFacts.KS116ProofTorus
public import CFSG.RankThree.PartTwo.KFacts.AutTriality
public import CFSG.LieType.Chevalley.GraphFixedBorelSelfNormalizer
public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
public import CFSG.LieType.Chevalley.GraphFixedSylowOpposition
public import CFSG.LieType.Chevalley.TwistedE6NormalFormActors
public import CFSG.LieType.Chevalley.DiagonalFieldActorData
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7Iso
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.EmptyFaithful.S143Pre
public import CFSG.Quasithin.H13.L32A5Props
public import CFSG.Quasithin.H13.L32ACSk6
public import CFSG.Quasithin.H13.L32AHStr
public import CFSG.Quasithin.H13.L32ASk1
public import CFSG.Quasithin.H13.L32NSet14Gen
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem6
public import CFSG.RankThree.Asc83Table.PermTables
public import CFSG.Sporadic.J4.QT2LocProof
public import CFSG.Sporadic.Schreier.MathieuOddCore
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CPrime
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralAut
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.Walter.J1
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.Quasithin.H13.L32A.C.SkPf

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartTwo.KFacts (exists_conj_mul_fieldActor)

section D4

variable {K : Type} [Field K] [Finite K] (σ : K ≃+* K)

local notation "C₀" => graphFixedRootGroup TwistTag.D4 K (RingEquiv.toRingHom σ)

local notation "U₀" => Subgroup.subgroupOf (graphFixedPosUnipotent TwistTag.D4 K
  (RingEquiv.toRingHom σ)) (graphFixedRootGroup TwistTag.D4 K (RingEquiv.toRingHom σ))

local notation "N₀" => Subgroup.normalizer ((Subgroup.subgroupOf (graphFixedPosUnipotent
  TwistTag.D4 K (RingEquiv.toRingHom σ)) (graphFixedRootGroup TwistTag.D4 K
  (RingEquiv.toRingHom σ)) : Subgroup (graphFixedRootGroup TwistTag.D4 K
  (RingEquiv.toRingHom σ))) : Set (graphFixedRootGroup TwistTag.D4 K (RingEquiv.toRingHom σ)))

@[expose] def d4Tuple (t : Kˣ) : Fin TwistTag.D4.tag.rank → Kˣ := fun i =>
  if i.val = 0 then t else if i.val = 1 then Units.map σ.toRingHom.toMonoidHom t
  else if i.val = 2 then 1
  else Units.map σ.toRingHom.toMonoidHom (Units.map σ.toRingHom.toMonoidHom t)

omit [Finite K] in
theorem d4Tuple_mul (s t : Kˣ) : d4Tuple σ (s * t) = d4Tuple σ s * d4Tuple σ t := by
  funext i
  fin_cases i <;> simp [d4Tuple]

omit [Finite K] in
theorem d4Tuple_one : d4Tuple σ 1 = 1 := by
  funext i
  fin_cases i <;> simp [d4Tuple]

omit [Finite K] in
theorem d4Tuple_compat (hσ3 : ∀ c, σ (σ (σ c)) = c) (t : Kˣ) (i : Fin TwistTag.D4.tag.rank) :
    d4Tuple σ t (TwistTag.D4.perm i) = Units.map σ.toRingHom.toMonoidHom (d4Tuple σ t i) := by
  have h0 : TwistTag.D4.perm ⟨0, by decide⟩ = ⟨1, by decide⟩ := by decide
  have h1 : TwistTag.D4.perm ⟨1, by decide⟩ = ⟨3, by decide⟩ := by decide
  have h2 : TwistTag.D4.perm ⟨2, by decide⟩ = ⟨2, by decide⟩ := by decide
  have h3 : TwistTag.D4.perm ⟨3, by decide⟩ = ⟨0, by decide⟩ := by decide
  fin_cases i
  · rw [h0]; rfl
  · rw [h1]; rfl
  · rw [h2]; simp [d4Tuple]
  · rw [h3]
    refine Units.ext ?_
    simp [d4Tuple, hσ3]

omit [Finite K] in
theorem cartanChar_mul (b c : Fin TwistTag.D4.tag.rank → Kˣ) :
    cartanChar (b * c) = cartanChar b * cartanChar c := by
  funext l
  simp only [cartanChar, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

omit [Finite K] in
theorem cartanChar_one : cartanChar (1 : Fin TwistTag.D4.tag.rank → Kˣ) = 1 := by
  funext l
  simp [cartanChar]

theorem rootDiagUnit_cartanChar_mem
    [CharP K 2]
    (hσ3 : ∀ c, σ (σ (σ c)) = c) (t : Kˣ) :
    rootDiagUnit TwistTag.D4.tag (cartanChar (d4Tuple σ t)) ∈ C₀ ∧
      rootDiagUnit TwistTag.D4.tag (cartanChar (d4Tuple σ t)) ∈ torusGroup TwistTag.D4.tag K ∧
      rootDiagUnit TwistTag.D4.tag (cartanChar (d4Tuple σ t)) ∈
        twistedFixedGroup TwistTag.D4 K σ.toRingHom := by
  have hprod := list_prod_torusElt_eq_rootDiagUnit (τ := TwistTag.D4.tag) (K := K) (d4Tuple σ t)
  have hH : rootDiagUnit TwistTag.D4.tag (cartanChar (d4Tuple σ t)) ∈
      torusGroup TwistTag.D4.tag K := by
    rw [← hprod]
    refine Subgroup.list_prod_mem _ fun g hg => ?_
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
    exact torusElt_mem_torusGroup i _
  have hC : rootDiagUnit TwistTag.D4.tag (cartanChar (d4Tuple σ t)) ∈
      adjointGroup TwistTag.D4.tag K := by
    rw [← hprod]
    refine Subgroup.list_prod_mem _ fun g hg => ?_
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
    exact torusElt_mem_adjointGroup i _
  have hT : rootDiagUnit TwistTag.D4.tag (cartanChar (d4Tuple σ t)) ∈
      twistedFixedGroup TwistTag.D4 K σ.toRingHom := by
    refine (mem_twistedFixedGroup_iff_twistHom _ _ _).2 ⟨hC, ?_⟩
    rw [twistHom_rootDiagUnit_eq]
    congr 1
    funext i
    have h1 := cartanChar_perm (t := TwistTag.D4) (σ := σ.toRingHom) (d4Tuple_compat σ hσ3 t)
      (TwistTag.D4.perm.symm i)
    rw [Equiv.apply_symm_apply] at h1
    exact h1.symm
  have hchar : ringChar K = 2 := ringChar.eq K 2
  refine ⟨?_, hH, hT⟩
  rw [← (even_triality_fixed_group_eq_root_group K hchar σ hσ3).1]
  exact hT

@[expose] noncomputable def d4Torus
    [CharP K 2]
    (hσ3 : ∀ c, σ (σ (σ c)) = c) : Kˣ →* C₀ where
  toFun t := ⟨rootDiagUnit TwistTag.D4.tag (cartanChar (d4Tuple σ t)),
    (rootDiagUnit_cartanChar_mem σ hσ3 t).1⟩
  map_one' := Subtype.ext (by
    show rootDiagUnit TwistTag.D4.tag (cartanChar (d4Tuple σ 1)) = 1
    rw [d4Tuple_one, cartanChar_one, rootDiagUnit_one])
  map_mul' s t := Subtype.ext (by
    show rootDiagUnit TwistTag.D4.tag (cartanChar (d4Tuple σ (s * t))) =
      rootDiagUnit TwistTag.D4.tag (cartanChar (d4Tuple σ s)) *
        rootDiagUnit TwistTag.D4.tag (cartanChar (d4Tuple σ t))
    rw [d4Tuple_mul, cartanChar_mul, rootDiagUnit_mul])

omit [Finite K] in
theorem mem_normalizer_d4U_iff
    (g : C₀) :
    g ∈ N₀ ↔
      (g : ModGL TwistTag.D4.tag K) ∈ graphFixedRootBorel TwistTag.D4 K σ.toRingHom := by
  rw [mem_normalizer_subgroupOf_iff (graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _),
    ← graphFixedRootGroup_inf_normalizer_graphFixedPosUnipotent σ.surjective, Subgroup.mem_inf]
  exact ⟨fun h => ⟨g.2, h⟩, fun h => h.2⟩

omit [Finite K] in
theorem d4_comm_mem :
    ∀ a ∈ N₀,
      ∀ b ∈ N₀, a * b * a⁻¹ * b⁻¹ ∈ U₀ := by
  intro a ha b hb
  rw [mem_normalizer_d4U_iff] at ha hb
  obtain ⟨hab, -, hHN, -, hHU, -⟩ := triangular_borel_structure.{0, 0} TwistTag.D4.tag K
  have hBa : (a : ModGL TwistTag.D4.tag K) ∈ borelGroup TwistTag.D4.tag K :=
    (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp ha).1).1
  have hBb : (b : ModGL TwistTag.D4.tag K) ∈ borelGroup TwistTag.D4.tag K :=
    (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hb).1).1
  rw [← SetLike.mem_coe, hHU] at hBa hBb
  have hTa : (a : ModGL TwistTag.D4.tag K) ∈ twistedFixedGroup TwistTag.D4 K σ.toRingHom :=
    (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp ha).1).2
  have hTb : (b : ModGL TwistTag.D4.tag K) ∈ twistedFixedGroup TwistTag.D4 K σ.toRingHom :=
    (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hb).1).2
  refine Subgroup.mem_inf.mpr ⟨mul_mul_inv_mul_inv_mem_of_mem_mul hHN hab hBa hBb, ?_⟩
  exact mul_mem (mul_mem (mul_mem hTa hTb) (inv_mem hTa)) (inv_mem hTb)

theorem d4Torus_mem_normalizer
    [CharP K 2]
    (hσ3 : ∀ c, σ (σ (σ c)) = c) :
    (d4Torus σ hσ3).range ≤ N₀ := by
  rintro _ ⟨t, rfl⟩
  rw [mem_normalizer_d4U_iff]
  obtain ⟨hC, hH, hT⟩ := rootDiagUnit_cartanChar_mem σ hσ3 t
  exact ⟨⟨(le_sup_left : torusGroup TwistTag.D4.tag K ≤ borelGroup TwistTag.D4.tag K) hH, hT⟩, hC⟩

theorem d4Torus_mem_iff
    [CharP K 2]
    (hσ3 : ∀ c, σ (σ (σ c)) = c) (t : Kˣ) :
    d4Torus σ hσ3 t ∈ U₀ ↔ t = 1 := by
  constructor
  · intro h
    obtain ⟨-, hH, -⟩ := rootDiagUnit_cartanChar_mem σ hσ3 t
    have h1 : rootDiagUnit TwistTag.D4.tag (cartanChar (d4Tuple σ t)) ∈
        torusGroup TwistTag.D4.tag K ⊓ posUnipotent TwistTag.D4.tag K := ⟨hH, h.1⟩
    rw [(triangular_borel_structure.{0, 0} TwistTag.D4.tag K).2.2.2.1, Subgroup.mem_bot] at h1
    have h2 := congrFun (rootDiagUnit_injective (h1.trans rootDiagUnit_one.symm)) ⟨0, by decide⟩
    rw [cartanChar_D4_zero] at h2
    simp [d4Tuple] at h2
    have ht2 : (t : K) ^ 2 = 1 := by
      have := congrArg Units.val h2
      simpa using this
    have h3 : ((t : K) + 1) ^ 2 = 0 := by
      rw [CharTwo.add_sq, ht2, one_pow, CharTwo.add_self_eq_zero]
    have h4 : (t : K) + 1 = 0 := (pow_eq_zero_iff two_ne_zero).mp h3
    have h5 : (t : K) = -1 := eq_neg_of_add_eq_zero_left h4
    rw [CharTwo.neg_eq] at h5
    exact Units.ext h5
  · rintro rfl
    rw [map_one]
    exact one_mem _

theorem fieldActor_d4Torus
    [CharP K 2]
    (hσ3 : ∀ c, σ (σ (σ c)) = c) (δ : K ≃+* K)
    (t : Kˣ) : fieldActor σ δ (d4Torus σ hσ3 t) =
      d4Torus σ hσ3 (Units.map δ.toRingHom.toMonoidHom t) := by
  apply Subtype.ext
  rw [coe_fieldActor]
  show Units.map (entrywiseHom δ.toRingHom)
      (rootDiagUnit TwistTag.D4.tag (cartanChar (d4Tuple σ t))) =
    rootDiagUnit TwistTag.D4.tag (cartanChar (d4Tuple σ (Units.map δ.toRingHom.toMonoidHom t)))
  rw [units_map_entrywiseHom_rootDiagUnit_ringEquiv]
  congr 1
  funext l
  have hc : ∀ j, Units.map δ.toRingHom.toMonoidHom (d4Tuple σ t j) =
      d4Tuple σ (Units.map δ.toRingHom.toMonoidHom t) j := by
    intro j
    refine Units.ext ?_
    fin_cases j <;> simp [d4Tuple, ringEquiv_comm_of_finite σ δ]
  simp only [cartanChar, map_prod, map_zpow, hc]

theorem comap_centMod_d4
    [CharP K 2]
    (hσ3 : ∀ c, σ (σ (σ c)) = c) (δ : K ≃+* K) :
    (centMod U₀ (fieldActor σ δ)).comap (d4Torus σ hσ3) = unitsFix δ := by
  ext t
  rw [Subgroup.mem_comap, mem_centMod, fieldActor_d4Torus, ← map_inv, ← map_mul,
    d4Torus_mem_iff, mem_unitsFix]
  refine ⟨fun h => ?_, fun h => ⟨d4Torus_mem_normalizer σ hσ3 ⟨t, rfl⟩, ?_⟩⟩
  · exact congrArg Units.val (mul_inv_eq_one.mp h.2)
  · exact mul_inv_eq_one.mpr (Units.ext h)

theorem map_fieldActor_d4U
    (δ : K ≃+* K) :
    (U₀).map (fieldActor σ δ).toMonoidHom = U₀ := by
  have h := (normalActor_mem (t := TwistTag.D4) σ 1 δ).1
  rw [normalActor_one_left] at h
  exact h

theorem centMod_d4
    (g : C₀) (δ : K ≃+* K)
    (h : (U₀).map (MulAut.conj g * fieldActor σ δ).toMonoidHom = U₀) :
    centMod U₀ (MulAut.conj g * fieldActor σ δ) =
      centMod U₀ (fieldActor σ δ) :=
  centMod_conj_mul_eq (d4_comm_mem σ) (map_fieldActor_d4U σ δ) h

variable {σ}

theorem n4At_d4
    [CharP K 2] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ 2 ^ f) : N4At (C₀) U₀ := by
  intro α _ hαU hcent
  have hσ3 : ∀ c, σ (σ (σ c)) = c := fun c => ringEquiv_cube_apply_eq hK hσ c
  obtain ⟨g, δ, rfl⟩ := exists_conj_mul_fieldActor hf hK hσ α
  rw [centMod_d4 σ g δ hαU] at hcent
  have hδ : δ = 1 := by
    rw [← unitsFix_eq_top_iff, ← comap_centMod_d4 σ hσ3, eq_top_iff]
    intro t _
    exact hcent (d4Torus_mem_normalizer σ hσ3 ⟨t, rfl⟩)
  left
  rw [hδ, fieldActor_one, mul_one]
  exact ⟨g, rfl⟩

theorem n2At_d4
    [CharP K 2] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ 2 ^ f) : N2At (C₀) U₀ := by
  intro α _ hαU hidx
  exfalso
  have hσ3 : ∀ c, σ (σ (σ c)) = c := fun c => ringEquiv_cube_apply_eq hK hσ c
  obtain ⟨g, δ, rfl⟩ := exists_conj_mul_fieldActor hf hK hσ α
  rw [centMod_d4 σ g δ hαU] at hidx
  have := finite_modGL (τ := TwistTag.D4.tag) (K := K)
  have h1 := index_comap_le _ (fieldActor σ δ) (d4Torus σ hσ3) (d4Torus_mem_normalizer σ hσ3)
  rw [comap_centMod_d4, hidx] at h1
  rcases eq_one_or_card_eq_four_of_index_unitsFix_le_three h1 with hδ | h4
  · rw [hδ, fieldActor_one, centMod_one, Subgroup.relIndex_self] at hidx
    omega
  · rw [hK] at h4
    have h8 : 2 ^ 3 ≤ (2 ^ f) ^ 3 :=
      Nat.pow_le_pow_left (Nat.le_self_pow (by omega) 2 |>.trans' (by norm_num)) 3
    omega

theorem isSylowTwoOf_d4U
    [CharP K 2] :
    IsSylowTwoOf U₀ ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := finite_modGL (τ := TwistTag.D4.tag) (K := K)
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem TwistTag.D4.tag).length
  obtain ⟨⟨P, hP⟩, -⟩ := exceptional_fixed_Sylow_opposition TwistTag.D4 K 2 σ w₀ hw₀
  rw [← hP]
  exact isSylowTwoOf_sylow P

end D4

theorem n2Model_n4Model_of_is3D4
    {M : Type} [Group M]
    {n : ℕ} (hn : 1 ≤ n) (h : Is3D4 2 n M) : N2Model M ∧ N4Model M := by
  obtain ⟨-, K, _, _, hK, σ₀, hσ₀, ⟨e⟩⟩ := h
  have hK3 : Nat.card K = (2 ^ n) ^ 3 := hK
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega) (show Nat.card K = 2 ^ (n * 3) by rw [hK3, ← pow_mul])
  obtain ⟨σ, rfl⟩ : ∃ σ : K ≃+* K, σ.toRingHom = σ₀ :=
    ⟨RingEquiv.ofBijective σ₀ ⟨σ₀.injective, Finite.surjective_of_injective σ₀.injective⟩, rfl⟩
  have hσ : ∀ c, σ c = c ^ (2 ^ n) := hσ₀
  obtain ⟨-, -, -, -, -, -, -, ⟨E⟩⟩ := even_triality_exact_automorphism_normal_form hn K hK3 σ hσ
  have := finite_modGL (τ := TwistTag.D4.tag) (K := K)
  exact ⟨(N2Model.of_at isSylowTwoOf_d4U (n2At_d4 hn hK3 hσ)).of_mulEquiv (e.trans E).symm,
    (N4Model.of_at isSylowTwoOf_d4U (n4At_d4 hn hK3 hσ)).of_mulEquiv (e.trans E).symm⟩

end CFSG.Quasithin.H13.L32A.C.SkPf
