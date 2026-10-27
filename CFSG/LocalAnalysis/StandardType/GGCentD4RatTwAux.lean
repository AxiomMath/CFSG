module

public import CFSG.LocalAnalysis.StandardType.GGNTPlaneInput
public import CFSG.HardMathSupport.Lang.D4Three.NormalForm
public import CFSG.LieType.Chevalley.CoordinateFieldBaseChange
public import CFSG.HardMathSupport.Lang.D4Three.Outer
public import CFSG.LieType.Chevalley.TrialityFullAmbientFixedGroup
public import CFSG.RankThree.Chevalley.SteinbergCFTrialityNoninnerDescent
public import CFSG.LieType.Chevalley.LangFiniteRootCentralizer
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.ExcTrialityOrient
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedTriality2Final
public import CFSG.RankThree.PartTwo.Sec11.Data
public import CFSG.RankThree.PartTwo.Sec13.Item135
public import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
public import CFSG.RankThree.PartTwo.Sec14.Item143N
public import CFSG.RankThree.PartTwo.Sec15.Item157
public import CFSG.RankThree.PartTwo.Sec16.Item1617StepsProofFus
public import CFSG.RankThree.PartTwo.Sec16.Item1617StepsProofTools
public import CFSG.RankThree.PartTwo.Sec16.Item167Proof
public import CFSG.RankThree.PartTwo.Sec16.Item16Tail17
public import CFSG.RankThree.PartTwo.Sec16.Item16Tail19
public import CFSG.RankThree.PartTwo.Sec16.Item16TailMore
public import CFSG.RankThree.PartTwo.Sec17.Item1724Two
public import CFSG.RankThree.PartTwo.Sec17.Item17TailSteps
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers142
public import CFSG.RankThree.S4Free.SuzukiEight
public import Certificates.Certificate8166

public section

namespace CFSG.StandardType.NTPlane

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.D4Three CFSG.HardMathSupport.Dickson.DefCharOuter.Export
  CFSG.RankThree.Chevalley


theorem ntpRT_d4P_conj_mem {K : Type} [Field K] (ε : ℕ) {a : ModGL Tag.D4 K}
    (ha : a ∈ adjointGroup Tag.D4 K) :
    d4P K ^ ε * a * (d4P K ^ ε)⁻¹ ∈ adjointGroup Tag.D4 K := by
  have h := (d4Graph K ε ⟨a, ha⟩).2
  rwa [coe_d4Graph] at h

theorem ntpRT_d4P_conj_cancel {K : Type} [Field K] {r : ℕ} (hr : r = 1 ∨ r = 2)
    (a : ModGL Tag.D4 K) :
    d4P K ^ r * (d4P K ^ (3 - r) * a * (d4P K ^ (3 - r))⁻¹) * (d4P K ^ r)⁻¹ = a := by
  have hP3 : d4P K ^ 3 = 1 := diagramMap_pow_order TwistTag.D4 K
  have e : d4P K ^ r * (d4P K ^ (3 - r) * a * (d4P K ^ (3 - r))⁻¹) *
      (d4P K ^ r)⁻¹ =
      (d4P K ^ r * d4P K ^ (3 - r)) * a * (d4P K ^ r * d4P K ^ (3 - r))⁻¹ := by
    group
  rw [e, ← pow_add, show r + (3 - r) = 3 by omega, hP3, one_mul, inv_one, mul_one]

theorem ntpRT_S_conjP {L : Type} [Field L] (Fr : L →+* L) (r : ℕ) (a : ModGL Tag.D4 L)
    (d : ℕ) :
    d4P L ^ r * Units.map (entrywiseHom Fr) (d4P L ^ d * a * (d4P L ^ d)⁻¹) *
        (d4P L ^ r)⁻¹ =
      d4P L ^ d * (d4P L ^ r * Units.map (entrywiseHom Fr) a * (d4P L ^ r)⁻¹) *
        (d4P L ^ d)⁻¹ := by
  rw [map_mul, map_mul, map_inv, map_pow]
  have hP : Units.map (entrywiseHom Fr) (d4P L) = d4P L :=
    units_map_entrywiseHom_diagramMap (t := TwistTag.D4) (K := L) Fr
  rw [hP]
  group

theorem ntpRT_entrywise_eq_conj {K : Type} [Field K] [Finite K] {L : Type} [Field L]
    [Algebra K L] (σ : K ≃+* K) {ε : ℕ} (hε : ε = 1 ∨ ε = 2)
    (x : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
    d4P L ^ ε * (baseChangeGL (algebraMap K L) (x.1 : ModGL Tag.D4 K) : ModGL Tag.D4 L) *
        (d4P L ^ ε)⁻¹ =
      (baseChangeGL (algebraMap K L)
        ((fieldActor (t := TwistTag.D4) σ (σ ^ (3 - ε)) x).1 : ModGL Tag.D4 K) :
          ModGL Tag.D4 L) := by
  have hmain : @Eq (ModGL TwistTag.D4.tag L)
      (diagramMap TwistTag.D4 L ^ ε * baseChangeGL (algebraMap K L) x.1 *
        (diagramMap TwistTag.D4 L ^ ε)⁻¹)
      (baseChangeGL (algebraMap K L)
        (fieldActor (t := TwistTag.D4) σ (σ ^ (3 - ε)) x).1) := by
    have h := CFSG.RankThree.Chevalley.diagramMap_pow_conj_eq_entrywise (K := K) σ hε x
    have h' := congrArg (baseChangeGL (algebraMap K L)) h
    rw [← coe_fieldActor (t := TwistTag.D4) σ (σ ^ (3 - ε)) x] at h'
    rw [map_mul, map_mul, map_inv, map_pow, baseChangeGL_diagramMap] at h'
    exact h'
  convert hmain using 2 <;> rfl

theorem ntpRT_map_entrywise_adjointGroup {L : Type} [Field L] [IsAlgClosed L] (f : ℕ)
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ ((2 : ℕ) ^ f)) :
    (adjointGroup Tag.D4 L).map (Units.map (entrywiseHom Fr)) = adjointGroup Tag.D4 L := by
  have hsurj : Function.Surjective Fr := fun y => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (n := (2 : ℕ) ^ f) y (pow_pos (by norm_num) f)
    exact ⟨z, by rw [hFr, hz]⟩
  obtain ⟨FrE, rfl⟩ : ∃ FrE : L ≃+* L, FrE.toRingHom = Fr :=
    ⟨RingEquiv.ofBijective Fr ⟨Fr.injective, hsurj⟩, RingHom.ext fun _ => rfl⟩
  exact ((chevalley_root_character_and_field_conjugation (TwistTag.D4.tag) L).2.2.2.2.1 FrE).1

theorem ntpRT_S_surj {L : Type} [Field L] [IsAlgClosed L] (f : ℕ) (Fr : L →+* L)
    (hFr : ∀ c, Fr c = c ^ ((2 : ℕ) ^ f)) (r : ℕ) (hr : r = 1 ∨ r = 2) :
    ∀ b ∈ adjointGroup Tag.D4 L, ∃ a ∈ adjointGroup Tag.D4 L,
      d4P L ^ r * Units.map (entrywiseHom Fr) a * (d4P L ^ r)⁻¹ = b := by
  intro b hb
  have hFA := ntpRT_map_entrywise_adjointGroup (f := f) Fr hFr
  have hc : d4P L ^ (3 - r) * b * (d4P L ^ (3 - r))⁻¹ ∈ adjointGroup Tag.D4 L :=
    ntpRT_d4P_conj_mem (3 - r) hb
  have hcm : d4P L ^ (3 - r) * b * (d4P L ^ (3 - r))⁻¹ ∈
      (adjointGroup Tag.D4 L).map (Units.map (entrywiseHom Fr)) := by
    rw [hFA]
    exact hc
  obtain ⟨a, ha, hFa⟩ := Subgroup.mem_map.1 hcm
  refine ⟨a, ha, ?_⟩
  rw [hFa]
  exact ntpRT_d4P_conj_cancel hr b

theorem ntpRT_S_fixed {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = ((2 : ℕ) ^ f) ^ 3) {L : Type} [Field L] [IsAlgClosed L]
    [Algebra K L] (r : ℕ) (hr : r = 1 ∨ r = 2) (Fr : L →+* L)
    (hFr : ∀ c, Fr c = c ^ ((2 : ℕ) ^ f)) (g : ↥(adjointGroup Tag.D4 L)) (ε : ℕ)
    (hε : ε = 1 ∨ ε = 2)
    (hcomm : ∀ x ∈ adjointGroup Tag.D4 L,
      d4P L ^ r * Units.map (entrywiseHom Fr) ((g : ModGL Tag.D4 L) *
          (d4P L ^ ε * x * (d4P L ^ ε)⁻¹) * (g : ModGL Tag.D4 L)⁻¹) * (d4P L ^ r)⁻¹ =
        (g : ModGL Tag.D4 L) * (d4P L ^ ε * (d4P L ^ r * Units.map (entrywiseHom Fr) x *
          (d4P L ^ r)⁻¹) * (d4P L ^ ε)⁻¹) * (g : ModGL Tag.D4 L)⁻¹) :
    d4P L ^ r * Units.map (entrywiseHom Fr) (g : ModGL Tag.D4 L) * (d4P L ^ r)⁻¹ =
      (g : ModGL Tag.D4 L) := by
  set S : ModGL Tag.D4 L → ModGL Tag.D4 L :=
    fun x => d4P L ^ r * Units.map (entrywiseHom Fr) x * (d4P L ^ r)⁻¹ with hSdef
  have hcommS : ∀ x ∈ adjointGroup Tag.D4 L,
      S ((g : ModGL Tag.D4 L) * (d4P L ^ ε * x * (d4P L ^ ε)⁻¹) * (g : ModGL Tag.D4 L)⁻¹) =
        (g : ModGL Tag.D4 L) * (d4P L ^ ε * S x * (d4P L ^ ε)⁻¹) *
          (g : ModGL Tag.D4 L)⁻¹ := by
    intro x hx
    simpa only [hSdef] using hcomm x hx
  have hSconjP : ∀ (d : ℕ) (a : ModGL Tag.D4 L),
      S (d4P L ^ d * a * (d4P L ^ d)⁻¹) =
        d4P L ^ d * S a * (d4P L ^ d)⁻¹ := by
    intro d a
    simpa only [hSdef] using ntpRT_S_conjP Fr r a d
  have hcommA : ∀ a ∈ adjointGroup Tag.D4 L,
      S ((g : ModGL Tag.D4 L) * a * (g : ModGL Tag.D4 L)⁻¹) =
        (g : ModGL Tag.D4 L) * S a * (g : ModGL Tag.D4 L)⁻¹ := by
    intro a ha
    have hx : d4P L ^ (3 - ε) * a * (d4P L ^ (3 - ε))⁻¹ ∈ adjointGroup Tag.D4 L :=
      ntpRT_d4P_conj_mem (3 - ε) ha
    have h1 := hcommS _ hx
    have e1 : d4P L ^ ε * (d4P L ^ (3 - ε) * a * (d4P L ^ (3 - ε))⁻¹) *
        (d4P L ^ ε)⁻¹ = a := ntpRT_d4P_conj_cancel hε a
    have e2 : d4P L ^ ε * S (d4P L ^ (3 - ε) * a * (d4P L ^ (3 - ε))⁻¹) *
        (d4P L ^ ε)⁻¹ = S a := by
      rw [hSconjP]
      exact ntpRT_d4P_conj_cancel hε (S a)
    rw [e1, e2] at h1
    exact h1
  have hFgA : Units.map (entrywiseHom Fr) (g : ModGL Tag.D4 L) ∈
      adjointGroup Tag.D4 L := by
    have h := Subgroup.mem_map_of_mem (Units.map (entrywiseHom Fr)) g.2
    rwa [ntpRT_map_entrywise_adjointGroup (f := f) Fr hFr] at h
  have hSgA : S (g : ModGL Tag.D4 L) ∈ adjointGroup Tag.D4 L := by
    simpa only [hSdef] using ntpRT_d4P_conj_mem r hFgA
  have hcenter : (⟨(g : ModGL Tag.D4 L)⁻¹ * S (g : ModGL Tag.D4 L),
      mul_mem (inv_mem g.2) hSgA⟩ : ↥(adjointGroup Tag.D4 L)) ∈
      Subgroup.center ↥(adjointGroup Tag.D4 L) := by
    rw [Subgroup.mem_center_iff]
    intro b
    obtain ⟨a, ha, hSa⟩ := ntpRT_S_surj f Fr hFr r hr (b : ModGL Tag.D4 L) b.2
    have hSaS : S a = (b : ModGL Tag.D4 L) := by simpa only [hSdef] using hSa
    have h2 := hcommA a ha
    have h3 : S ((g : ModGL Tag.D4 L) * a * (g : ModGL Tag.D4 L)⁻¹) =
        S (g : ModGL Tag.D4 L) * S a * (S (g : ModGL Tag.D4 L))⁻¹ := by
      simp only [hSdef]
      rw [map_mul, map_mul, map_inv]
      group
    rw [h3] at h2
    rw [hSaS] at h2
    refine Subtype.ext ?_
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk]
    calc (b : ModGL Tag.D4 L) * ((g : ModGL Tag.D4 L)⁻¹ * S (g : ModGL Tag.D4 L)) =
        (g : ModGL Tag.D4 L)⁻¹ *
          ((g : ModGL Tag.D4 L) * (b : ModGL Tag.D4 L) * (g : ModGL Tag.D4 L)⁻¹) *
            S (g : ModGL Tag.D4 L) := by group
      _ = (g : ModGL Tag.D4 L)⁻¹ *
          (S (g : ModGL Tag.D4 L) * (b : ModGL Tag.D4 L) * (S (g : ModGL Tag.D4 L))⁻¹) *
            S (g : ModGL Tag.D4 L) := by rw [← h2]
      _ = ((g : ModGL Tag.D4 L)⁻¹ * S (g : ModGL Tag.D4 L)) * (b : ModGL Tag.D4 L) := by
        group
  have hZ : Subgroup.center ↥(adjointGroup Tag.D4 L) = ⊥ :=
    center_adjointGroup_eq_bot_field Tag.D4 L
  rw [hZ, Subgroup.mem_bot] at hcenter
  have hval : (g : ModGL Tag.D4 L)⁻¹ * S (g : ModGL Tag.D4 L) = 1 := by
    have := congrArg Subtype.val hcenter
    simpa using this
  have hSg : S (g : ModGL Tag.D4 L) = (g : ModGL Tag.D4 L) := by
    calc S (g : ModGL Tag.D4 L) =
        (g : ModGL Tag.D4 L) * ((g : ModGL Tag.D4 L)⁻¹ * S (g : ModGL Tag.D4 L)) := by
          group
      _ = (g : ModGL Tag.D4 L) * 1 := by rw [hval]
      _ = (g : ModGL Tag.D4 L) := mul_one _
  simpa only [hSdef] using hSg

theorem ntpRT_mem_image {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = ((2 : ℕ) ^ f) ^ 3) {L : Type} [Field L] [IsAlgClosed L]
    [Algebra K L] (r : ℕ) (hr : r = 1 ∨ r = 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (((2 : ℕ) ^ f) ^ r)) (Fr : L →+* L)
    (hFr : ∀ c, Fr c = c ^ ((2 : ℕ) ^ f)) (g : ↥(adjointGroup Tag.D4 L))
    (hg : d4P L ^ r * Units.map (entrywiseHom Fr) (g : ModGL Tag.D4 L) * (d4P L ^ r)⁻¹ =
      (g : ModGL Tag.D4 L)) :
    ∃ g' : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      @Eq (ModGL Tag.D4 L) (baseChangeGL (algebraMap K L) g'.1) (g : ModGL Tag.D4 L) := by
  have hset := fixedSet_D4_eq_map_baseChangeGL (ℓ := 2) (d := f) Nat.prime_two hf (K := K) hK
    (Ω := L) r hr σ.toRingHom hσ Fr hFr
  have hmem : (g.1 : ModGL TwistTag.D4.tag L) ∈ {x : ModGL TwistTag.D4.tag L |
      x ∈ adjointGroup TwistTag.D4.tag L ∧ diagramMap TwistTag.D4 L ^ r *
        Units.map (entrywiseHom Fr) x * (diagramMap TwistTag.D4 L ^ r)⁻¹ = x} := by
    refine ⟨g.2, ?_⟩
    convert hg using 2 <;> rfl
  rw [hset] at hmem
  obtain ⟨g', hg', hgg⟩ := hmem
  refine ⟨⟨g', hg'⟩, ?_⟩
  convert hgg using 2 <;> rfl

theorem ntpRT_sigma_eq_frob_pow {f r : ℕ} (hf : 1 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = ((2 : ℕ) ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (((2 : ℕ) ^ f) ^ r)) :
    ∃ φ : K ≃+* K, orderOf φ = 3 * f ∧ σ = φ ^ (r * f) := by
  have hK3 : Nat.card K = 2 ^ (3 * f) := by
    calc Nat.card K = ((2 : ℕ) ^ f) ^ 3 := hK
      _ = 2 ^ (f * 3) := by rw [← pow_mul]
      _ = 2 ^ (3 * f) := by rw [Nat.mul_comm]
  obtain ⟨φ, hφ, hord, -, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two (by omega : 1 ≤ 3 * f) hK3
  exact ⟨φ, hord, RingEquiv.ext fun c => by
    rw [hσ, ringAut_pow_apply_of_frobenius hφ (r * f) c, ← pow_mul, Nat.mul_comm f r]⟩

theorem ntpRT_sigma_cube {f r : ℕ} (hf : 1 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = ((2 : ℕ) ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (((2 : ℕ) ^ f) ^ r)) : σ ^ 3 = 1 := by
  obtain ⟨φ, hord, hσφ⟩ := ntpRT_sigma_eq_frob_pow hf hK σ hσ
  have e : (φ ^ (r * f)) ^ 3 = (φ ^ (3 * f)) ^ r := by
    rw [← pow_mul, ← pow_mul, show r * f * 3 = 3 * f * r by ring]
  rw [hσφ, e, ← hord, pow_orderOf_eq_one, one_pow]

theorem ntpRT_orient_fieldActor {K : Type} [Field K] [Finite K] (σ τ : K ≃+* K)
    (h1 : τ.toRingHom.comp σ.toRingHom = RingHom.id K)
    (h2 : σ.toRingHom.comp τ.toRingHom = RingHom.id K) (δ : K ≃+* K) :
    MulAut.congr
      ((Subgroup.equivMapOfInjective (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
          (MulAut.conj (permModuleMap d4OuterSwap_cartan K)).toMonoidHom
          (MulAut.conj (permModuleMap d4OuterSwap_cartan K)).injective).trans
        (MulEquiv.subgroupCongr (map_conj_outerSwap_graphFixedRootGroup K h1 h2)))
      (fieldActor (t := TwistTag.D4) σ δ) = fieldActor (t := TwistTag.D4) τ δ := by
  let Q : ModGL TwistTag.D4.tag K := permModuleMap d4OuterSwap_cartan K
  have hQinj : Function.Injective (⇑(MulEquiv.toMonoidHom (MulAut.conj Q))) :=
    (MulAut.conj Q).injective
  let P : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ≃*
      ↥(graphFixedRootGroup TwistTag.D4 K τ.toRingHom) :=
    (Subgroup.equivMapOfInjective _ (MulAut.conj Q).toMonoidHom hQinj).trans
      (MulEquiv.subgroupCongr (map_conj_outerSwap_graphFixedRootGroup K h1 h2))
  have hcoe : ∀ y : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      (((Subgroup.equivMapOfInjective (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
        (MulAut.conj Q).toMonoidHom hQinj) y).1 : ModGL TwistTag.D4.tag K) =
        (MulAut.conj Q) y.1 := fun _ => rfl
  have he : ∀ y : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      (P y).1 = Q * y.1 * Q⁻¹ := by
    intro y
    rw [show P = (Subgroup.equivMapOfInjective (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
        (MulAut.conj Q).toMonoidHom hQinj).trans
        (MulEquiv.subgroupCongr (map_conj_outerSwap_graphFixedRootGroup K h1 h2)) from rfl]
    rw [MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply, hcoe, MulAut.conj_apply]
  have hesym : ∀ x : ↥(graphFixedRootGroup TwistTag.D4 K τ.toRingHom),
      (P.symm x).1 = Q⁻¹ * x.1 * Q := by
    intro x
    have hx := he (P.symm x)
    rw [MulEquiv.apply_symm_apply] at hx
    calc (P.symm x).1 = Q⁻¹ * (Q * (P.symm x).1 * Q⁻¹) * Q := by group
      _ = Q⁻¹ * x.1 * Q := by rw [hx]
  refine MulEquiv.ext fun x => Subtype.ext ?_
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply]
  change (((P (fieldActor (t := TwistTag.D4) σ δ (P.symm x))).1 :
      ModGL TwistTag.D4.tag K)) = (((fieldActor (t := TwistTag.D4) τ δ x).1 :
        ModGL TwistTag.D4.tag K))
  rw [he, coe_fieldActor, hesym, coe_fieldActor]
  have hconj := units_map_entrywiseHom_conj_permModuleMap (τ := TwistTag.D4.tag)
    (hπ := d4OuterSwap_cartan) (K := K) δ.toRingHom (Q⁻¹ * x.1 * Q)
  rw [MulAut.conj_apply, MulAut.conj_apply] at hconj
  rw [show Q * (Q⁻¹ * x.1 * Q) * Q⁻¹ = x.1 by group] at hconj
  exact hconj.symm

theorem ntpRT_sigma_pow_ne_one {f r : ℕ} (hf : 1 ≤ f) (hr : r = 1 ∨ r = 2)
    {K : Type} [Field K] (hK : Nat.card K = ((2 : ℕ) ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (((2 : ℕ) ^ f) ^ r)) :
    ∀ ε : ℕ, (ε = 1 ∨ ε = 2) → σ ^ (3 - ε) ≠ 1 := by
  obtain ⟨φ, hord, hσφ⟩ := ntpRT_sigma_eq_frob_pow hf hK σ hσ
  have hσ3 : σ ^ 3 = 1 := ntpRT_sigma_cube hf hK σ hσ
  have hσ1 : σ ≠ 1 := by
    intro h1
    rw [hσφ] at h1
    have hdvd : orderOf φ ∣ r * f := orderOf_dvd_of_pow_eq_one h1
    rw [hord] at hdvd
    have hf0 : 0 < f := by omega
    have hr0 : 0 < r := by rcases hr with rfl | rfl <;> norm_num
    have hle : 3 * f ≤ r * f := Nat.le_of_dvd (Nat.mul_pos hr0 hf0) hdvd
    rcases hr with rfl | rfl <;> omega
  intro ε hε hp
  rcases hε with rfl | rfl
  · have hp2 : σ ^ 2 = 1 := by simpa using hp
    have h1 : σ = 1 := by
      have e : σ = σ ^ 3 * (σ ^ 2)⁻¹ := by group
      rw [e, hσ3, hp2, inv_one, mul_one]
    exact hσ1 h1
  · exact hσ1 (by simpa using hp)

end CFSG.StandardType.NTPlane

end
