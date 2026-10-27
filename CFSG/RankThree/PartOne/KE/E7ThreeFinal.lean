module

public import CFSG.RankThree.PartOne.KE.E7ThreeHI
public import CFSG.RankThree.PartOne.KE.E7ThreeStab
public import CFSG.RankThree.PartOne.KE.PlaneToral
public import CFSG.RankThree.PartOne.KE.E7ThreeLayerProof

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.LocalRank
open CFSG.RankThree.PartOne CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Chevalley (exhaustionPhi)
open scoped Matrix Pointwise MatrixGroups

section Solvable

theorem e7T3_abelian_two_torsion {L : Type} [Field L] (Fr : L →+* L) {q : ℕ}
    (hFr : ∀ x, Fr x = x ^ q) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {V : Type*} [Group V]
    (ψ : V →* ModGL .E7 L) (hψ : Function.Injective ψ)
    (hV : ∀ v : V, ψ v ∈ (fixedCharTuples (ε • e7T3W) Fr).map (rootDiagUnitHom .E7 L)) :
    (∀ v w : V, v * w = w * v) ∧ Nat.card {v : V // v ^ 2 = 1} ≤ 2 := by
  classical
  choose a ha hav using fun v : V => hV v
  have hinj0 : Function.Injective (rootDiagUnitHom .E7 L) := rootDiagUnit_injective
  refine ⟨fun v w => ?_, ?_⟩
  · apply hψ
    rw [map_mul, map_mul, ← hav v, ← hav w, ← map_mul, ← map_mul, mul_comm]
  · set Γ : Subgroup (Fin Tag.E7.rank → Lˣ) :=
      (fixedCharTuples (ε • e7T3W) Fr) ⊓ ψ.range.comap (rootDiagUnitHom .E7 L) with hΓ
    have hΓle : Γ ≤ fixedCharTuples (ε • e7T3W) Fr := inf_le_left
    let φ : {v : V // v ^ 2 = 1} → {g : Γ // g ^ 2 = 1} := fun v =>
      ⟨⟨a v.1, Subgroup.mem_inf.2 ⟨ha v.1, ⟨v.1, (hav v.1).symm⟩⟩⟩, by
        apply Subtype.ext
        apply hinj0
        change rootDiagUnitHom .E7 L (a v.1 ^ 2) = rootDiagUnitHom .E7 L 1
        rw [map_pow, hav, ← map_pow, v.2, map_one, map_one]⟩
    have hφ : Function.Injective φ := fun v w h => by
      apply Subtype.ext
      apply hψ
      rw [← hav v.1, ← hav w.1]
      have := congrArg (fun g : {g : Γ // g ^ 2 = 1} => ((g : Γ) : Fin Tag.E7.rank → Lˣ)) h
      simp only [φ] at this
      rw [this]
    obtain ⟨hfin, hcard⟩ := e7T3_card_two_torsion_le_two hε hFr hΓle
    exact (Nat.card_le_card_of_injective φ hφ).trans hcard

variable {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] {p : ℕ}
  {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ] {ε : ℤ}

theorem e7_three_solvable (hLay : E7ThreeLayers) (F : E7ThreeFrame K L ℓ f p ε) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hp3 : 3 < p) (hε : ε = 1 ∨ ε = -1)
    (hpf : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + ε * (Nat.card K : ℤ) + 1)
    (hstab : E7StabHyp F.n (iterateFrobenius L ℓ f) p) :
    ∀ x : adjointGroup .E7 K, orderOf x = p →
      ∀ V : Subgroup (Subgroup.centralizer ({x} : Set (adjointGroup .E7 K))), V.Normal →
        Group.IsSolvable V →
        (∀ v ∈ V, ∀ w ∈ V, v * w = w * v) ∧ Nat.card {v : V // v ^ 2 = 1} ≤ 4 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hFr : ∀ c, iterateFrobenius L ℓ f c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact iterateFrobenius_def ℓ f c
  intro x hx V hVn hVs
  have hpg : IsPGroup p (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨c, hc⟩ := F.hconj _ hpg
  have hh := hc x (Subgroup.mem_zpowers x)
  obtain ⟨b, hb, hap, hb1, hbh, -⟩ := e7_three_prelim F hp hx c hh
  obtain ⟨ι', P, ψ, -, hψinj, -, -, -, -, -, -, hψV, -⟩ := e7_three_perx hLay F hf hK hp hp3 hε
    hpf hstab hx c hh hb hap hb1 hbh
  have hVT : ∀ v : V, ψ (v : Subgroup.centralizer ({x} : Set (adjointGroup .E7 K))) ∈
      (fixedCharTuples (ε • e7T3W) (iterateFrobenius L ℓ f)).map (rootDiagUnitHom .E7 L) :=
    fun v => by
    rw [← F.hT]
    exact subtorusSigma_le_twistedTorusOf _ _ _ (hψV V hVn hVs v v.2)
  obtain ⟨hab, h2⟩ := e7T3_abelian_two_torsion (iterateFrobenius L ℓ f) hFr hε
    (ψ.comp V.subtype) (hψinj.comp V.subtype_injective) hVT
  refine ⟨fun v hv w hw => ?_, h2.trans (by norm_num)⟩
  have := hab ⟨v, hv⟩ ⟨w, hw⟩
  exact congrArg Subtype.val this

end Solvable

section Plane

theorem planeLocalCoreOdd_E7_three_six (hLay : E7ThreeLayers) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (K : Type) [Field K] [Finite K] {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpf : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + ε * (Nat.card K : ℤ) + 1) :
    PlaneLocalCoreOdd p (adjointGroup .E7 K) := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ℓ := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    hℓ hf hK
  let L := AlgebraicClosure K
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  obtain ⟨F⟩ := exists_e7ThreeFrame K hf hK hp hp3 hε hpf L
  have hstab := e7T3_stabHyp F hK hp hp3 hε hpf
  exact planeLocalCoreOdd_of_toral_kernels_abstract hp hp3 center_adjointGroup_eq_bot
    (e7_three_solvable hLay F hf hK hp hp3 hε hpf hstab)
    (ordinary_E_outer_derived_subgroup_odd .E7 (Or.inr (Or.inl rfl)) K).1
    (localCoreTrivialOn_noninner_E .E7 (Or.inr (Or.inl rfl)) K hp hp3)
    (e7_three_hI hLay F hf hK hp hp3 hε hpf hstab)

theorem oddEndpoint_E7_phi3Phi6_of_layers (hLay : E7ThreeLayers) :
    OddEndpoint .E7 fun p ℓ f => (p : ℤ) ∣ cycloVal 3 ℓ f ∨ (p : ℤ) ∣ cycloVal 6 ℓ f := by
  refine oddEndpoint_E7_of_native ?_
  intro K _ _ p ℓ f hp hp3 hℓ hℓp hf hK hc
  rcases hc with hc | hc
  · refine planeLocalCoreOdd_E7_three_six hLay (ε := 1) (Or.inl rfl) K hℓ hf hK hp hp3 ?_
    simpa [cycloVal, exhaustionPhi, hK] using hc
  · refine planeLocalCoreOdd_E7_three_six hLay (ε := -1) (Or.inr rfl) K hℓ hf hK hp hp3 ?_
    simpa [cycloVal, exhaustionPhi, hK, sub_eq_add_neg] using hc

theorem oddEndpoint_E7_phi3Phi6 (hD4 : D4TrialityLayer Tag.E7)
    (hA5 : A5Layer Tag.E7) :
    OddEndpoint .E7 fun p ℓ f => (p : ℤ) ∣ cycloVal 3 ℓ f ∨ (p : ℤ) ∣ cycloVal 6 ℓ f :=
  oddEndpoint_E7_phi3Phi6_of_layers (e7ThreeLayers hD4 hA5)

end Plane

end CFSG.RankThree.PartOne.KE
