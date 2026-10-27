module

public import CFSG.RankThree.PartOne.KE.E7FourPerX
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.Chevalley.SteinbergBNExceptionalCyclotomicExhaustion
public import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.LocalRank
open CFSG.RankThree.PartOne CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Chevalley (exhaustionPhi)

open scoped Matrix Pointwise MatrixGroups

section Generic

variable {τ : Tag} {L : Type} [Field L]

theorem rootChar_eq_one_of_centralizes {S : Set (Fin τ.rank → ℤ)} {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) (hαS : α ∈ S) {a : Fin τ.rank → Lˣ}
    (hC : rootDiagUnit τ a ∈ Subgroup.centralizer (rootSpan τ L S : Set (ModGL τ L))) :
    rootChar a α = 1 := by
  have hXmem : pinnedX τ L α 1 ∈ rootSpan τ L S := pinnedX_mem_rootSpan hαS 1
  have hcomm := Subgroup.mem_centralizer_iff.1 hC _ hXmem
  have hconj := rootDiagUnit_conj_pinnedX a hα (1 : L)
  have hX : rootDiagUnit τ a * pinnedX τ L α 1 * (rootDiagUnit τ a)⁻¹ = pinnedX τ L α 1 := by
    rw [← hcomm]
    group
  have h3 : pinnedX τ L α (((rootChar a α : Lˣ) : L) * 1) = pinnedX τ L α 1 :=
    hconj.symm.trans hX
  have h4 := pinnedX_injective (τ := τ) (R := L) α h3
  exact Units.ext (by simpa using h4)

end Generic

section Solvable

theorem e7_four_abelian_two_torsion {L : Type} [Field L] (Fr : L →+* L) {q : ℕ}
    (hFr : ∀ x, Fr x = x ^ q) {V : Type*} [Group V] (ψ : V →* ModGL .E7 L)
    (hψ : Function.Injective ψ)
    (hV : ∀ v : V, ψ v ∈ (fixedCharTuples e7F4W Fr).map (rootDiagUnitHom .E7 L))
    (hVF : ∀ v : V, ∀ a : Fin Tag.E7.rank → Lˣ, rootDiagUnit .E7 a = ψ v →
      ∀ f ∈ e7F4FList, rootChar a (toVec Tag.E7.rank f) = 1) :
    (∀ v w : V, v * w = w * v) ∧ Nat.card {v : V // v ^ 2 = 1} ≤ 4 := by
  classical
  choose a ha hav using fun v : V => hV v
  have hinj0 : Function.Injective (rootDiagUnitHom .E7 L) := rootDiagUnit_injective
  have hmul : ∀ v w : V, a (v * w) = a v * a w := fun v w => by
    apply hinj0
    rw [hav, map_mul, map_mul, hav, hav]
  refine ⟨fun v w => ?_, ?_⟩
  · apply hψ
    rw [map_mul, map_mul, ← hav v, ← hav w, ← map_mul, ← map_mul, mul_comm]
  · set Γ : Subgroup (Fin Tag.E7.rank → Lˣ) :=
      (fixedCharTuples e7F4W Fr) ⊓ ψ.range.comap (rootDiagUnitHom .E7 L) with hΓ
    have hΓle : Γ ≤ fixedCharTuples e7F4W Fr := inf_le_left
    have hΓF : ∀ g ∈ Γ, ∀ f ∈ e7F4FList, rootChar g (toVec Tag.E7.rank f) = 1 := by
      intro g hg f hf
      obtain ⟨v, hv⟩ := (Subgroup.mem_inf.1 hg).2
      exact hVF v g hv.symm f hf
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
    obtain ⟨hfin, hcard⟩ := e7F4_card_two_torsion_le_four Fr hFr hΓle hΓF
    exact (Nat.card_le_card_of_injective φ hφ).trans hcard

variable {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] {p : ℕ}
  {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]

theorem e7_four_solvable (hD4 : D4TranspositionLayer Tag.E7) (F : E7FourFrame K L ℓ f p)
    (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hp3 : 3 < p)
    (hq4 : 4 ≤ Nat.card K) (hpf : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + 1)
    (hstab : E7StabHyp F.n (iterateFrobenius L ℓ f) p) :
    ∀ x : adjointGroup .E7 K, orderOf x = p →
      ∀ V : Subgroup (Subgroup.centralizer ({x} : Set (adjointGroup .E7 K))), V.Normal →
        Group.IsSolvable V →
        (∀ v ∈ V, ∀ w ∈ V, v * w = w * v) ∧ Nat.card {v : V // v ^ 2 = 1} ≤ 4 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hΦ : ((Nat.card K : ℕ) : ZMod p) ^ 2 + 1 = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((Nat.card K : ℤ) ^ 2 + 1) p).2 hpf
    simpa using this
  have hFr : ∀ c, iterateFrobenius L ℓ f c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact iterateFrobenius_def ℓ f c
  intro x hx V hVn hVs
  have hpg : IsPGroup p (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨c, hc⟩ := F.hconj _ hpg
  have hh := hc x (Subgroup.mem_zpowers x)
  obtain ⟨b, hb, hap, hb1, hbh, -⟩ := e7_perx_prelim F hp hx c hh
  have hkind : rootCharKernel b = e7F4S0Set ∨ ∃ cert ∈ e7F4Certs,
      rootCharKernel b = e7F4S0Set ∪ classSetL7 e7F4Rows cert.cls := by
    rcases e7F4_kernel_structure (iterateFrobenius L ℓ f) hFr hp hp3 hΦ hb hap hb1 with
      h | ⟨cert, hcert, h, -⟩
    · exact Or.inl h
    · exact Or.inr ⟨cert, hcert, h⟩
  obtain ⟨ψ, hψinj, hψ, hψV⟩ := e7_four_perx_sigma hD4 F hf hK hp hq4 hstab hx c hh hbh hkind
  have hS0 : e7F4S0Set ⊆ rootCharKernel b := by
    rcases hkind with h | ⟨cert, hcert, h⟩
    · exact h.symm.subset
    · rw [h]
      exact Set.subset_union_left
  have hVT : ∀ v : V, ψ (v : Subgroup.centralizer ({x} : Set (adjointGroup .E7 K))) ∈
      (fixedCharTuples e7F4W (iterateFrobenius L ℓ f)).map (rootDiagUnitHom .E7 L) := fun v => by
    rw [← F.hT]
    exact subtorusSigma_le_twistedTorusOf _ _ _ (hψV V hVn hVs v v.2)
  have hVF : ∀ v : V, ∀ a : Fin Tag.E7.rank → Lˣ,
      rootDiagUnit .E7 a = ψ (v : Subgroup.centralizer ({x} : Set (adjointGroup .E7 K))) →
        ∀ f' ∈ e7F4FList, rootChar a (toVec Tag.E7.rank f') = 1 := by
    intro v a hav f' hf'
    have hC : rootDiagUnit .E7 a ∈ Subgroup.centralizer (rootSpan .E7 L (rootCharKernel b) :
        Set (ModGL .E7 L)) := by
      rw [hav]
      exact (Subgroup.mem_inf.1 (hψV V hVn hVs v v.2)).2
    have hroot : toVec Tag.E7.rank f' ∈ rootCharKernel b := hS0 ⟨f', by
      simp only [e7F4S0, e7T12SigmaList, e7F4FList, List.mem_cons, List.not_mem_nil, or_false] at hf' ⊢
      rcases hf' with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), rfl⟩
    exact rootChar_eq_one_of_centralizes hroot.1 hroot hC
  obtain ⟨hab, h2⟩ := e7_four_abelian_two_torsion (iterateFrobenius L ℓ f) hFr
    (ψ.comp V.subtype) (hψinj.comp V.subtype_injective) hVT hVF
  refine ⟨fun v hv w hw => ?_, h2⟩
  have := hab ⟨v, hv⟩ ⟨w, hw⟩
  exact congrArg Subtype.val this

end Solvable

end CFSG.RankThree.PartOne.KE
