module

public import CFSG.Quasithin.EmptyFaithful.T1515gG
public import CFSG.Quasithin.EmptyFaithful.T1515gF
public import CFSG.Quasithin.EmptyFaithful.T1515gH
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246A7Rep
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.Dihedral.FourgroupCycleControl
public import CFSG.Dihedral.OriginalCentralizerOddCore
public import CFSG.LieType.Chevalley.RootCommutator
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPrimeCompatibility
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.A1cA132Action
public import CFSG.Quasithin.Background.A1cA133Three
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B216Quotient
public import CFSG.Quasithin.Background.B5Basic
public import CFSG.Quasithin.Background.B5CompA
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.C1GNSolvConnect
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.E3Gen
public import CFSG.Quasithin.Background.InternalSecData
public import CFSG.Quasithin.Background.InternalSecIso
public import CFSG.Quasithin.EmptyFaithful.S14117
public import CFSG.Quasithin.EmptyFaithful.S14117Coprime
public import CFSG.Quasithin.EmptyFaithful.S14117Rank
public import CFSG.Quasithin.EmptyFaithful.S1417Glue
public import CFSG.Quasithin.EmptyFaithful.S1421Defs
public import CFSG.Quasithin.EmptyFaithful.S151cA2
public import CFSG.Quasithin.EmptyFaithful.S151cCases
public import CFSG.Quasithin.EmptyFaithful.S152UGen
public import CFSG.Quasithin.EmptyFaithful.T1515Top9
public import CFSG.Quasithin.EmptyFaithful.T1515gE
public import CFSG.Quasithin.H13.J4Core
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch11SecA02Setup
public import CFSG.Quasithin.Vol2.Ch11SecA03Basic
public import CFSG.Quasithin.Vol2.Ch11SecAFacts03
public import CFSG.Quasithin.Vol2.Ch11SecAFacts04
public import CFSG.Quasithin.Vol2.Ch11StatementsC
public import CFSG.Quasithin.Vol2.Ch3Sec1Thm311
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import Certificates.Certificate8026Base

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

@[expose] def a7T1 : Equiv.Perm (Fin 7) :=
  Equiv.swap 0 2 * Equiv.swap 2 4 * Equiv.swap 1 3 * Equiv.swap 3 5

@[expose] def a7T2 : Equiv.Perm (Fin 7) :=
  Equiv.swap 1 3 * Equiv.swap 3 4 * Equiv.swap 0 2 * Equiv.swap 2 5

@[expose] def a7StdP : Finset (Finset (Fin 7)) := {{0, 1}, {2, 3}, {4, 5}, {6}}

theorem a7T1_cube : a7T1 ^ 3 = 1 := by decide +kernel
theorem a7T2_cube : a7T2 ^ 3 = 1 := by decide +kernel
theorem a7T1_even : a7T1 ∈ alternatingGroup (Fin 7) := by
  rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel
theorem a7T2_even : a7T2 ∈ alternatingGroup (Fin 7) := by
  rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel
theorem a7T1_stab : StabilizesPartition a7T1 a7StdP := by
  unfold StabilizesPartition a7StdP; decide +kernel
theorem a7T2_stab : StabilizesPartition a7T2 a7StdP := by
  unfold StabilizesPartition a7StdP; decide +kernel

theorem a7_fixed_std (z : Fin 7 → ZMod 2) (hz : ∑ i, z i = 0)
    (h1 : ∀ i, z ((a7T1⁻¹ : Equiv.Perm (Fin 7)) i) = z i)
    (h2 : ∀ i, z ((a7T2⁻¹ : Equiv.Perm (Fin 7)) i) = z i) :
    z = 0 ∨ z = fun k => if k = 6 then 0 else 1 := by
  revert z
  unfold a7T1 a7T2
  decide +kernel

set_option maxRecDepth 100000 in
theorem a7_centralizer_three (σ : Equiv.Perm (Fin 7))
    (h1 : σ * a7T1 = a7T1 * σ) (h2 : σ * a7T2 = a7T2 * σ) :
    σ = 1 ∨ σ = Equiv.swap 0 1 * Equiv.swap 2 3 * Equiv.swap 4 5 := by
  revert σ
  unfold a7T1 a7T2
  decide +kernel

theorem a7_fixed_zero (z : Fin 7 → ZMod 2) (hz : ∑ i, z i = 0)
    (h1 : ∀ i, z (((Equiv.swap (0 : Fin 7) 1 * Equiv.swap 1 2)⁻¹ : Equiv.Perm (Fin 7)) i) = z i)
    (h2 : ∀ i, z (((Equiv.swap (0 : Fin 7) 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 3 4 *
      Equiv.swap 4 5 * Equiv.swap 5 6)⁻¹ : Equiv.Perm (Fin 7)) i) = z i) : z = 0 := by
  revert z
  decide +kernel

theorem a7_partition_normal_form {P : Finset (Finset (Fin 7))} {d : Fin 7}
    (hP : IsPartitionOfType P {2, 2, 2, 1}) (hd : {d} ∈ P) :
    ∃ π : Equiv.Perm (Fin 7), π 6 = d ∧ P = a7StdP.image (Finset.image π) := by
  obtain ⟨-, hdisj, -, hcard⟩ := hP
  classical
  set P' := P.erase {d} with hP'
  have hPval : P.val = {d} ::ₘ P'.val := by
    rw [hP', Finset.erase_val]
    exact (Multiset.cons_erase (Finset.mem_val.mpr hd)).symm
  have hcard' : P'.val.map Finset.card = {2, 2, 2} := by
    rw [hPval, Multiset.map_cons, Finset.card_singleton] at hcard
    have h : ({2, 2, 2, 1} : Multiset ℕ) = 1 ::ₘ {2, 2, 2} := by decide
    rw [h] at hcard
    exact (Multiset.cons_inj_right 1).mp hcard
  have hcardP' : P'.card = 3 := by
    have := congrArg Multiset.card hcard'
    simpa using this
  have hB2 : ∀ B ∈ P', B.card = 2 := by
    intro B hB
    have hm : B.card ∈ P'.val.map Finset.card := Multiset.mem_map_of_mem _ hB
    rw [hcard'] at hm
    simpa using hm
  obtain ⟨B₁, B₂, B₃, h12, h13, h23, hP'eq⟩ := Finset.card_eq_three.mp hcardP'
  have hB₁ : B₁ ∈ P' := by rw [hP'eq]; simp
  have hB₂ : B₂ ∈ P' := by rw [hP'eq]; simp
  have hB₃ : B₃ ∈ P' := by rw [hP'eq]; simp
  obtain ⟨x₁, y₁, hxy₁, rfl⟩ := Finset.card_eq_two.mp (hB2 B₁ hB₁)
  obtain ⟨x₂, y₂, hxy₂, rfl⟩ := Finset.card_eq_two.mp (hB2 B₂ hB₂)
  obtain ⟨x₃, y₃, hxy₃, rfl⟩ := Finset.card_eq_two.mp (hB2 B₃ hB₃)
  have hmemP : ∀ B ∈ P', B ∈ P := fun B hB => Finset.mem_of_mem_erase hB
  have hne_d : ∀ B ∈ P', B ≠ {d} := fun B hB => Finset.ne_of_mem_erase hB
  have hdis : ∀ B ∈ P', ∀ B' ∈ P', B ≠ B' → Disjoint B B' :=
    fun B hB B' hB' hne => hdisj B (hmemP B hB) B' (hmemP B' hB') hne
  have hdis_d : ∀ B ∈ P', Disjoint B {d} :=
    fun B hB => hdisj B (hmemP B hB) {d} hd (hne_d B hB)
  have hd1 : d ∉ ({x₁, y₁} : Finset (Fin 7)) := fun h => by
    have := hdis_d _ hB₁
    exact (Finset.disjoint_left.mp this h) (Finset.mem_singleton_self d)
  have hd2 : d ∉ ({x₂, y₂} : Finset (Fin 7)) := fun h => by
    have := hdis_d _ hB₂
    exact (Finset.disjoint_left.mp this h) (Finset.mem_singleton_self d)
  have hd3 : d ∉ ({x₃, y₃} : Finset (Fin 7)) := fun h => by
    have := hdis_d _ hB₃
    exact (Finset.disjoint_left.mp this h) (Finset.mem_singleton_self d)
  have hd12 := hdis _ hB₁ _ hB₂ h12
  have hd13 := hdis _ hB₁ _ hB₃ h13
  have hd23 := hdis _ hB₂ _ hB₃ h23
  simp only [Finset.disjoint_left, Finset.mem_insert, Finset.mem_singleton] at hd12 hd13 hd23
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hd1 hd2 hd3
  have e1 : x₁ ≠ x₂ := fun h => hd12 (Or.inl rfl) (Or.inl h)
  have e2 : x₁ ≠ y₂ := fun h => hd12 (Or.inl rfl) (Or.inr h)
  have e3 : y₁ ≠ x₂ := fun h => hd12 (Or.inr rfl) (Or.inl h)
  have e4 : y₁ ≠ y₂ := fun h => hd12 (Or.inr rfl) (Or.inr h)
  have e5 : x₁ ≠ x₃ := fun h => hd13 (Or.inl rfl) (Or.inl h)
  have e6 : x₁ ≠ y₃ := fun h => hd13 (Or.inl rfl) (Or.inr h)
  have e7 : y₁ ≠ x₃ := fun h => hd13 (Or.inr rfl) (Or.inl h)
  have e8 : y₁ ≠ y₃ := fun h => hd13 (Or.inr rfl) (Or.inr h)
  have e9 : x₂ ≠ x₃ := fun h => hd23 (Or.inl rfl) (Or.inl h)
  have e10 : x₂ ≠ y₃ := fun h => hd23 (Or.inl rfl) (Or.inr h)
  have e11 : y₂ ≠ x₃ := fun h => hd23 (Or.inr rfl) (Or.inl h)
  have e12 : y₂ ≠ y₃ := fun h => hd23 (Or.inr rfl) (Or.inr h)
  let f : Fin 7 → Fin 7 := ![x₁, y₁, x₂, y₂, x₃, y₃, d]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [f] at hij ⊢ <;> grind
  let π : Equiv.Perm (Fin 7) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf)
  refine ⟨π, rfl, ?_⟩
  have hPins : P = insert {d} P' := (Finset.insert_erase hd).symm
  rw [hPins, hP'eq]
  ext B
  simp [a7StdP, Finset.image_insert, π, f]
  tauto

theorem a7_stab_conj {σ : Equiv.Perm (Fin 7)} (π : Equiv.Perm (Fin 7)) {P : Finset (Finset (Fin 7))}
    (h : StabilizesPartition σ P) :
    StabilizesPartition (π * σ * π⁻¹) (P.image (Finset.image π)) := by
  unfold StabilizesPartition at h ⊢
  rw [Finset.image_image]
  have hcomp : (Finset.image (π * σ * π⁻¹)) ∘ (Finset.image π) = (Finset.image π) ∘ (Finset.image σ) := by
    funext B
    simp only [Function.comp_apply, Finset.image_image]
    congr 1
    funext b
    simp
  rw [hcomp, ← Finset.image_image, h]

theorem a7_conj_alt (π : Equiv.Perm (Fin 7)) {t : Equiv.Perm (Fin 7)}
    (ht : t ∈ alternatingGroup (Fin 7)) : π * t * π⁻¹ ∈ alternatingGroup (Fin 7) := by
  rw [Equiv.Perm.mem_alternatingGroup] at ht ⊢
  rw [map_mul, map_mul, ht, map_inv]
  simp

theorem a7_conj_cube (π : Equiv.Perm (Fin 7)) {t : Equiv.Perm (Fin 7)} (ht : t ^ 3 = 1) :
    (π * t * π⁻¹) ^ 3 = 1 := by
  rw [conj_pow, ht]
  group

theorem a7_fixed_of_partition {P : Finset (Finset (Fin 7))} {d : Fin 7}
    (hP : IsPartitionOfType P {2, 2, 2, 1}) (hd : {d} ∈ P) (y : ↥(evenWeight 7))
    (hy : ∀ a : Equiv.Perm (Fin 7), a ∈ alternatingGroup (Fin 7) → StabilizesPartition a P →
      a ^ 3 = 1 → permWeight 7 a y = y) : y = 0 ∨ y = a7ETheta d := by
  obtain ⟨π, hπ6, hPπ⟩ := a7_partition_normal_form hP hd
  have hfix : ∀ t : Equiv.Perm (Fin 7), t ∈ alternatingGroup (Fin 7) → StabilizesPartition t a7StdP →
      t ^ 3 = 1 → ∀ j, (fun i => (y : Fin 7 → ZMod 2) (π i)) (t⁻¹ j) =
        (fun i => (y : Fin 7 → ZMod 2) (π i)) j := by
    intro t ht hst ht3 j
    have h1 := hy (π * t * π⁻¹) (a7_conj_alt π ht) (hPπ ▸ a7_stab_conj π hst) (a7_conj_cube π ht3)
    have h2 := congrArg (fun z : ↥(evenWeight 7) => (z : Fin 7 → ZMod 2) (π j)) h1
    simp only [permWeight] at h2
    simpa [Equiv.Perm.mul_apply] using h2
  have hsum : ∑ i, (fun i => (y : Fin 7 → ZMod 2) (π i)) i = 0 := by
    have h0 : ∑ i, (y : Fin 7 → ZMod 2) i = 0 := by
      have := y.2
      simpa [evenWeight] using this
    simpa using (Equiv.sum_comp π (y : Fin 7 → ZMod 2)).trans h0
  rcases a7_fixed_std _ hsum (hfix _ a7T1_even a7T1_stab a7T1_cube)
    (hfix _ a7T2_even a7T2_stab a7T2_cube) with h0 | h1
  · left
    apply Subtype.ext
    funext i
    have := congrFun h0 (π⁻¹ i)
    simpa using this
  · right
    apply Subtype.ext
    funext i
    have := congrFun h1 (π⁻¹ i)
    have hpi : π (π⁻¹ i) = i := by simp
    simp only [hpi] at this
    have hiff : π⁻¹ i = 6 ↔ i = d := by rw [Equiv.Perm.inv_eq_iff_eq, hπ6]
    rw [this]
    show (if π⁻¹ i = 6 then (0 : ZMod 2) else 1) = if i = d then 0 else 1
    split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; tauto)

theorem a7_exists_sigma0 {P : Finset (Finset (Fin 7))} {d : Fin 7}
    (hP : IsPartitionOfType P {2, 2, 2, 1}) (hd : {d} ∈ P) :
    ∃ σ₀ : Equiv.Perm (Fin 7), A7IsThreeSwaps σ₀ ∧
      ∀ σ : Equiv.Perm (Fin 7), (∀ a : Equiv.Perm (Fin 7), a ∈ alternatingGroup (Fin 7) →
        StabilizesPartition a P → a ^ 3 = 1 → σ * a = a * σ) → σ = 1 ∨ σ = σ₀ := by
  obtain ⟨π, hπ6, hPπ⟩ := a7_partition_normal_form hP hd
  refine ⟨π * (Equiv.swap 0 1 * Equiv.swap 2 3 * Equiv.swap 4 5) * π⁻¹, ?_, ?_⟩
  · refine ⟨π 0, π 1, π 2, π 3, π 4, π 5, ?_, ?_⟩
    · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
        and_true, π.injective.eq_iff]
      decide
    · have e : ∀ x y : Fin 7, π * Equiv.swap x y * π⁻¹ = Equiv.swap (π x) (π y) := fun x y =>
        (Equiv.swap_apply_apply π x y).symm
      calc π * (Equiv.swap 0 1 * Equiv.swap 2 3 * Equiv.swap 4 5) * π⁻¹
          = (π * Equiv.swap 0 1 * π⁻¹) * (π * Equiv.swap 2 3 * π⁻¹) * (π * Equiv.swap 4 5 * π⁻¹) := by
            group
        _ = _ := by rw [e, e, e]
  · intro σ hσ
    have hc : ∀ t : Equiv.Perm (Fin 7), t ∈ alternatingGroup (Fin 7) → StabilizesPartition t a7StdP →
        t ^ 3 = 1 → (π⁻¹ * σ * π) * t = t * (π⁻¹ * σ * π) := by
      intro t ht hst ht3
      have h := hσ (π * t * π⁻¹) (a7_conj_alt π ht) (hPπ ▸ a7_stab_conj π hst) (a7_conj_cube π ht3)
      calc (π⁻¹ * σ * π) * t = π⁻¹ * (σ * (π * t * π⁻¹)) * π := by group
        _ = π⁻¹ * ((π * t * π⁻¹) * σ) * π := by rw [h]
        _ = t * (π⁻¹ * σ * π) := by group
    rcases a7_centralizer_three _ (hc _ a7T1_even a7T1_stab a7T1_cube)
      (hc _ a7T2_even a7T2_stab a7T2_cube) with h | h
    · left
      have : σ = π * (π⁻¹ * σ * π) * π⁻¹ := by group
      rw [this, h]
      group
    · right
      have : σ = π * (π⁻¹ * σ * π) * π⁻¹ := by group
      rw [this, h]

theorem a7_schur_hom {U : Type*} [Group U] (γ Φ : U →* Multiplicative ↥(evenWeight 7))
    (hγ : Function.Surjective γ) (hker : γ.ker ≤ Φ.ker)
    (hact : ∀ (a : alternatingGroup (Fin 7)) (x : U), ∃ x' : U,
      Multiplicative.toAdd (γ x') =
          permWeight 7 (a : Equiv.Perm (Fin 7)) (Multiplicative.toAdd (γ x)) ∧
        Multiplicative.toAdd (Φ x') =
          permWeight 7 (a : Equiv.Perm (Fin 7)) (Multiplicative.toAdd (Φ x))) :
    (∀ x, Φ x = 1) ∨ (∀ x, Φ x = γ x) := by
  obtain ⟨τ, hτ⟩ : ∃ τ : Multiplicative ↥(evenWeight 7) →* Multiplicative ↥(evenWeight 7),
      ∀ x, τ (γ x) = Φ x :=
    ⟨γ.liftOfRightInverse (Function.surjInv hγ) (Function.rightInverse_surjInv hγ) ⟨Φ, hker⟩,
      fun x => MonoidHom.liftOfRightInverse_comp_apply γ _ _ ⟨Φ, hker⟩ x⟩
  let τ' : ↥(evenWeight 7) →+ ↥(evenWeight 7) := AddMonoidHom.toMultiplicative.symm τ
  have hτ'apply : ∀ x, τ' (Multiplicative.toAdd (γ x)) = Multiplicative.toAdd (Φ x) := fun x => by
    rw [← hτ x]
    rfl
  have hτ'eq : ∀ (a : alternatingGroup (Fin 7)) (w : ↥(evenWeight 7)),
      τ' (permWeight 7 (a : Equiv.Perm (Fin 7)) w) = permWeight 7 (a : Equiv.Perm (Fin 7)) (τ' w) := by
    intro a w
    obtain ⟨x, hx⟩ := hγ (Multiplicative.ofAdd w)
    have hw : Multiplicative.toAdd (γ x) = w := by rw [hx]; rfl
    obtain ⟨x', h1, h2⟩ := hact a x
    rw [← hw, ← h1, hτ'apply x', h2, hτ'apply x]
  rcases a7_schur τ' hτ'eq with h0 | h1
  · left
    intro x
    apply Multiplicative.toAdd.injective
    rw [← hτ'apply x, h0]
    rfl
  · right
    intro x
    apply Multiplicative.toAdd.injective
    rw [← hτ'apply x, h1]
    rfl

noncomputable def a7E : AltHeart 7 →+ ↥(evenWeight 7) :=
  QuotientAddGroup.lift (constWeight 7) (AddMonoidHom.id _) (by
    rw [a7_constWeight_eq_bot]
    exact bot_le)

theorem a7E_mk (x : ↥(evenWeight 7)) : a7E (QuotientAddGroup.mk x : AltHeart 7) = x := by
  simp [a7E]

theorem a7_mk_E (a : AltHeart 7) : (QuotientAddGroup.mk (a7E a) : AltHeart 7) = a := by
  induction a using QuotientAddGroup.induction_on with
  | H x => rw [a7E_mk]

variable {G : Type} [Group G] [Finite G]

structure A7Gamma (L : Subgroup G) (α : ↥L →* alternatingGroup (Fin 7))
    (β : ↥(blockU L) →* Multiplicative (AltHeart 7))
    (γ : ↥(blockU L) →* Multiplicative ↥(evenWeight 7)) : Prop where
  surj : Function.Surjective γ
  ker : ∀ u : ↥(blockU L), γ u = 1 ↔ (u : G) ∈ blockZ L
  equi : ∀ (ℓ : ↥L) (u v : ↥(blockU L)), (v : G) = ℓ * u * ℓ⁻¹ →
    Multiplicative.toAdd (γ v) = permWeight 7 (α ℓ : Equiv.Perm (Fin 7)) (Multiplicative.toAdd (γ u))
  mk_eq : ∀ u : ↥(blockU L), (QuotientAddGroup.mk (Multiplicative.toAdd (γ u)) : AltHeart 7) =
    Multiplicative.toAdd (β u)

omit [Finite G] in
theorem a7_exists_gamma {L : Subgroup G} {α : ↥L →* alternatingGroup (Fin 7)}
    {β : ↥(blockU L) →* Multiplicative (AltHeart 7)} (hstr : A7Str L α β) :
    ∃ γ : ↥(blockU L) →* Multiplicative ↥(evenWeight 7), A7Gamma L α β γ := by
  refine ⟨(AddMonoidHom.toMultiplicative a7E).comp β, ?_, ?_, ?_, ?_⟩
  · intro w
    obtain ⟨u, hu⟩ := hstr.2.2.1 (Multiplicative.ofAdd (QuotientAddGroup.mk (Multiplicative.toAdd w) : AltHeart 7))
    refine ⟨u, ?_⟩
    show Multiplicative.ofAdd (a7E (Multiplicative.toAdd (β u))) = w
    rw [hu]
    exact congrArg Multiplicative.ofAdd (a7E_mk _)
  · intro u
    have hmk : ∀ a : AltHeart 7, a7E a = 0 ↔ a = 0 := fun a => by
      constructor
      · intro h
        rw [← a7_mk_E a, h]
        rfl
      · rintro rfl
        exact map_zero a7E
    have h1 : ((AddMonoidHom.toMultiplicative a7E).comp β) u = 1 ↔ β u = 1 := by
      show Multiplicative.ofAdd (a7E (Multiplicative.toAdd (β u))) = 1 ↔ β u = 1
      rw [ofAdd_eq_one, hmk]
      exact ⟨fun h => Multiplicative.toAdd.injective h, fun h => by rw [h]; rfl⟩
    rw [h1]
    have h2 : u ∈ β.ker ↔ β u = 1 := MonoidHom.mem_ker
    rw [← h2, hstr.2.2.2.1]
    exact Subgroup.mem_subgroupOf
  · intro ℓ u v h
    have h1 := hstr.2.2.2.2 ℓ u v h (Multiplicative.toAdd (((AddMonoidHom.toMultiplicative a7E).comp β) u))
      (a7_mk_E _)
    show a7E (Multiplicative.toAdd (β v)) = _
    rw [← h1, a7E_mk]
  · intro u
    exact a7_mk_E _

theorem a7_permWeight_add (σ : Equiv.Perm (Fin 7)) (x y : ↥(evenWeight 7)) :
    permWeight 7 σ (x + y) = permWeight 7 σ x + permWeight 7 σ y :=
  Subtype.ext (funext fun _ => rfl)

theorem a7_permWeight_zero (σ : Equiv.Perm (Fin 7)) : permWeight 7 σ 0 = 0 :=
  Subtype.ext (funext fun _ => rfl)

theorem a7_permWeight_neg (σ : Equiv.Perm (Fin 7)) (x : ↥(evenWeight 7)) :
    permWeight 7 σ (-x) = -permWeight 7 σ x :=
  Subtype.ext (funext fun _ => rfl)

theorem a7_permWeight_one (x : ↥(evenWeight 7)) : permWeight 7 1 x = x :=
  Subtype.ext (funext fun _ => rfl)

theorem a7_permWeight_mul (σ τ : Equiv.Perm (Fin 7)) (x : ↥(evenWeight 7)) :
    permWeight 7 (σ * τ) x = permWeight 7 σ (permWeight 7 τ x) :=
  Subtype.ext (funext fun i => by simp [permWeight, mul_inv_rev])

theorem a7_fixed_zero' (v : ↥(evenWeight 7))
    (hv : ∀ a : alternatingGroup (Fin 7), permWeight 7 (a : Equiv.Perm (Fin 7)) v = v) : v = 0 := by
  have hsum : ∑ i, (v : Fin 7 → ZMod 2) i = 0 := by
    have := v.2
    simpa [evenWeight] using this
  have hfix : ∀ σ : Equiv.Perm (Fin 7), σ ∈ alternatingGroup (Fin 7) →
      ∀ i, (v : Fin 7 → ZMod 2) (σ⁻¹ i) = (v : Fin 7 → ZMod 2) i := by
    intro σ hσ i
    have := congrArg (fun w : ↥(evenWeight 7) => (w : Fin 7 → ZMod 2) i) (hv ⟨σ, hσ⟩)
    exact this
  have h1 : (Equiv.swap (0 : Fin 7) 1 * Equiv.swap 1 2) ∈ alternatingGroup (Fin 7) := by
    rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel
  have h2 : (Equiv.swap (0 : Fin 7) 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 3 4 *
      Equiv.swap 4 5 * Equiv.swap 5 6) ∈ alternatingGroup (Fin 7) := by
    rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel
  exact Subtype.ext (a7_fixed_zero _ hsum (hfix _ h1) (hfix _ h2))

theorem a7_two_nsmul (x : ↥(evenWeight 7)) : x + x = 0 := by
  apply Subtype.ext
  funext i
  have : ∀ a : ZMod 2, a + a = 0 := by decide
  exact this _

theorem a7PairVec_ne_zero : a7PairVec 0 1 ≠ 0 := by
  intro h
  have := congrArg (fun z : ↥(evenWeight 7) => (z : Fin 7 → ZMod 2) 0) h
  revert this
  decide +kernel

theorem a7_hC3 {L : Subgroup G} {α : ↥L →* alternatingGroup (Fin 7)}
    {β : ↥(blockU L) →* Multiplicative (AltHeart 7)} (hstr : A7Str L α β) :
    ¬ 3 ∣ Nat.card α.ker := by
  rw [hstr.2.1]
  obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).exists_card_eq
  rw [hm]
  intro h3
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  omega

omit [Finite G] in
theorem a7_exists_Y1_gen {L : Subgroup G} {α : ↥L →* alternatingGroup (Fin 7)}
    (hα : Function.Surjective α) (hC3 : ¬ 3 ∣ Nat.card α.ker) {P : Finset (Finset (Fin 7))}
    {a : Equiv.Perm (Fin 7)} (ha : a ∈ alternatingGroup (Fin 7)) (hst : StabilizesPartition a P)
    (ha3 : a ^ 3 = 1) :
    ∃ t : ↥L, (α t : Equiv.Perm (Fin 7)) = a ∧ (t : G) ∈ a7Y1Of L α P := by
  have hord : ∃ n : ℕ, orderOf (⟨a, ha⟩ : alternatingGroup (Fin 7)) = 3 ^ n := by
    have h3 : (⟨a, ha⟩ : alternatingGroup (Fin 7)) ^ 3 = 1 := Subtype.ext ha3
    rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one h3) with h1 | h1
    · exact ⟨0, by simpa using h1⟩
    · exact ⟨1, by simpa using h1⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨t, hta, n, hn⟩ := CFSG.LieType.CentralExt.exists_pLift_aux (p := 3) hα hC3 hord
  refine ⟨t, by rw [hta], Subgroup.subset_closure ⟨t.2, ?_, n, by rw [Subgroup.orderOf_coe]; exact hn⟩⟩
  have h1 : α ⟨(t : G), t.2⟩ = ⟨a, ha⟩ := hta
  rw [h1]
  exact hst

end CFSG.Quasithin
