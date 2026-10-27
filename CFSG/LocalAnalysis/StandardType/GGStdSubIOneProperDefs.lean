module

public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneExist
public import CFSG.LocalAnalysis.StandardType.GGInnLocal

public section

namespace CFSG.StandardType

open CFSG.Assembly

section EndNode

variable {L' : Type} [Group L']

@[expose] def GGCentEnd (S : Subgroup (MulAut L')) (a : MulAut L') : Prop :=
  ∀ a' ∈ S, ((∀ j ∈ LargeEvenLayer (ggFix a), a' j = j) ↔ a' ∈ Subgroup.zpowers a)

@[expose] def GGIsEndNode (A : Subgroup (MulAut L')) (a : MulAut L') : Prop :=
  a ∈ A ∧ a ≠ 1 ∧ IsComponentOf (LargeEvenLayer (ggFix a)) (ggFix a) ∧ GGCentEnd A a

@[expose] def GGNonSmallRule (p : ℕ) (A : Subgroup (MulAut L')) (a : MulAut L') : Prop :=
  p = 3 → (∃ a₁, GGIsEndNode A a₁ ∧ ¬ LargeEvenSmall (LargeEvenLayer (ggFix a₁))) →
    ¬ LargeEvenSmall (LargeEvenLayer (ggFix a))

@[expose] def GGNormTwoR {R : Type} [Group R] (ψ : L' →* R) (A : Subgroup (MulAut L')) : Prop :=
  ∃ U : Subgroup R, U ≠ ⊥ ∧ IsPGroup 2 U ∧ ∀ a ∈ A, ∀ l : L', ψ l ∈ U → ψ (a l) ∈ U

@[expose] def GGNoTwoBetween (A As : Subgroup (MulAut L')) : Prop :=
  ∀ E : Subgroup (MulAut L'), A < E → E ≤ As → ∀ U : Subgroup L', IsPGroup 2 U →
    (∀ a ∈ E, ∀ u ∈ U, a u ∈ U) → U = ⊥

end EndNode

@[expose] def GGEndNodeIOne (p r : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ A As : Subgroup (MulAut L'), IsElemAbelian p A → A < As → IsElemAbelian p As →
      Nat.card As ≤ p * Nat.card A →
      (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
      p ^ r ≤ Nat.card A → p ^ 3 ≤ Nat.card A →
      (GGNormTwoR ψ A ∨ GGDeltaAdm p L' A) → GGNoTwoBetween A As →
      ∃ a, GGIsEndNode A a ∧ GGCentEnd As a ∧ GGNonSmallRule p A a

@[expose] def GGEndNodeRoot (p r : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ A : Subgroup (MulAut L'), IsElemAbelian p A →
      (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
      p ^ r ≤ Nat.card A → p ^ 3 ≤ Nat.card A → GGNormTwoR ψ A →
      ∃ a, GGIsEndNode A a ∧ GGNonSmallRule p A a ∧
        ∃ U : Subgroup L', U ≤ LargeEvenLayer (ggFix a) ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧
          ∀ a' ∈ A, ∀ u ∈ U, a' u ∈ U

@[expose] def GGEndNodeIOneDelta (p r : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ A As : Subgroup (MulAut L'), IsElemAbelian p A → A < As → IsElemAbelian p As →
      Nat.card As ≤ p * Nat.card A →
      (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
      p ^ r ≤ Nat.card A → p ^ 3 ≤ Nat.card A →
      GGDeltaAdm p L' A → GGNoTwoBetween A As →
      ∃ a, GGIsEndNode A a ∧ GGCentEnd As a ∧ GGNonSmallRule p A a

@[expose] def GGEndNodeIOneNonSmall (p r : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ A As : Subgroup (MulAut L'), IsElemAbelian p A → A < As → IsElemAbelian p As →
      Nat.card As ≤ p * Nat.card A →
      (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
      p ^ r ≤ Nat.card A → p ^ 3 ≤ Nat.card A →
      (GGNormTwoR ψ A ∨ GGDeltaAdm p L' A) → GGNoTwoBetween A As →
      ∃ a, GGIsEndNode A a ∧ GGCentEnd As a ∧ (p = 3 → ¬ LargeEvenSmall (LargeEvenLayer (ggFix a)))

theorem GGEndNodeIOneNonSmall.endNodeIOne {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (h : GGEndNodeIOneNonSmall p r R I) : GGEndNodeIOne p r R I := by
  intro L' _ _ ψ hψ hker hcomm A As hA hAlt hAs hcard hI hr h3 hcase hnone
  obtain ⟨a, hend, hcent, hns⟩ := h L' ψ hψ hker hcomm A As hA hAlt hAs hcard hI hr h3 hcase hnone
  exact ⟨a, hend, hcent, fun hp _ => hns hp⟩

section Cases

variable {L' : Type} [Group L'] [Finite L']

theorem forall_mem_closure_mapsTo {U : Subgroup L'} {S : Set (MulAut L')}
    (hS : ∀ a ∈ S, ∀ u ∈ U, a u ∈ U) : ∀ a ∈ Subgroup.closure S, ∀ u ∈ U, a u ∈ U := by
  let H : Subgroup (MulAut L') :=
    { carrier := {a | ∀ u ∈ U, a u ∈ U}
      mul_mem' := fun {a b} ha hb u hu => ha _ (hb u hu)
      one_mem' := fun u hu => hu
      inv_mem' := fun {a} ha u hu => by
        have hinj : Function.Injective (fun v : U => (⟨a v, ha v v.2⟩ : U)) := by
          intro v w hvw
          exact Subtype.ext (a.injective (congrArg Subtype.val hvw))
        obtain ⟨v, hv⟩ := (Finite.injective_iff_surjective.mp hinj) ⟨u, hu⟩
        have hv' : a v = u := congrArg Subtype.val hv
        show a⁻¹ u ∈ U
        rw [← hv', ← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
        exact v.2 }
  intro a ha
  exact (Subgroup.closure_le H).mpr (fun b hb => hS b hb) ha

theorem ggCentEnd_of_root {A As : Subgroup (MulAut L')} {a : MulAut L'} (haA : a ∈ A)
    (hcent : GGCentEnd A a) (hAAs : A ≤ As) (hnone : GGNoTwoBetween A As) {U : Subgroup L'}
    (hUJ : U ≤ LargeEvenLayer (ggFix a)) (hU1 : U ≠ ⊥) (hU2 : IsPGroup 2 U)
    (hUA : ∀ a' ∈ A, ∀ u ∈ U, a' u ∈ U) : GGCentEnd As a := by
  intro a' ha'
  by_cases hA' : a' ∈ A
  · exact hcent a' hA'
  · constructor
    · intro hfix
      exfalso
      apply hU1
      have hS : ∀ b ∈ (A : Set (MulAut L')) ∪ {a'}, ∀ u ∈ U, b u ∈ U := by
        rintro b (hb | hb) u hu
        · exact hUA b hb u hu
        · rw [Set.mem_singleton_iff.mp hb, hfix u (hUJ hu)]
          exact hu
      have hle : A ⊔ Subgroup.zpowers a' ≤ Subgroup.closure ((A : Set (MulAut L')) ∪ {a'}) :=
        sup_le (fun c hc => Subgroup.subset_closure (Or.inl hc))
          (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Or.inr (Set.mem_singleton a'))))
      refine hnone (A ⊔ Subgroup.zpowers a') ?_ (sup_le hAAs (Subgroup.zpowers_le.mpr ha')) U
        hU2 fun b hb => forall_mem_closure_mapsTo hS b (hle hb)
      refine lt_of_le_of_ne le_sup_left fun h => hA' ?_
      rw [h]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers a')
    · intro hmem
      exact absurd ((Subgroup.zpowers_le.mpr haA) hmem) hA'

end Cases

theorem ggEndNodeIOne_of_root_delta {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (hroot : GGEndNodeRoot p r R I) (hdel : GGEndNodeIOneDelta p r R I) :
    GGEndNodeIOne p r R I := by
  intro L' _ _ ψ hψ hker hperf A As hA hAAs hAs hcard hAI hr h3 hcase hnone
  rcases hcase with hα | hδ
  · obtain ⟨a, ⟨haA, ha1, hcomp, hcent⟩, hrule, U, hUJ, hU1, hU2, hUA⟩ :=
      hroot L' ψ hψ hker hperf A hA hAI hr h3 hα
    exact ⟨a, ⟨haA, ha1, hcomp, hcent⟩,
      ggCentEnd_of_root haA hcent hAAs.le hnone hUJ hU1 hU2 hUA, hrule⟩
  · exact hdel L' ψ hψ hker hperf A As hA hAAs hAs hcard hAI hr h3 hδ hnone

theorem ggEndNodeIOneDelta_of_prime {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (hO : GGOutdiagPrime p R I) (hZ : GGCenterPrime p R) : GGEndNodeIOneDelta p r R I := by
  intro L' _ _ ψ hψ hker hperf A _ hA _ _ _ hAI _ _ hδ _
  exact absurd hδ (not_ggDeltaAdm_of_prime hO hZ hψ hker hperf hA hAI)

theorem ggEndNodeIOne_of_root_prime {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (hroot : GGEndNodeRoot p r R I) (hO : GGOutdiagPrime p R I) (hZ : GGCenterPrime p R) :
    GGEndNodeIOne p r R I :=
  ggEndNodeIOne_of_root_delta hroot (ggEndNodeIOneDelta_of_prime hO hZ)

theorem largeEvenSmall_congr {H₁ H₂ : Type*} [Group H₁] [Group H₂] {K₁ : Subgroup H₁}
    {K₂ : Subgroup H₂} (e : K₁ ≃* K₂) : LargeEvenSmall K₁ ↔ LargeEvenSmall K₂ := by
  constructor
  · rintro (⟨F, hF, hfin, hc, ⟨f⟩⟩ | hA)
    · exact Or.inl ⟨F, hF, hfin, hc, ⟨e.symm.trans f⟩⟩
    · obtain ⟨f⟩ := hA
      exact Or.inr ⟨e.symm.trans f⟩
  · rintro (⟨F, hF, hfin, hc, ⟨f⟩⟩ | hA)
    · exact Or.inl ⟨F, hF, hfin, hc, ⟨e.trans f⟩⟩
    · obtain ⟨f⟩ := hA
      exact Or.inr ⟨e.trans f⟩

@[expose] def GGStdSubIOneProperInputOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L : Subgroup G),
    GGThmIHyp p B x L → GGBstar p B Bs → B ≠ Bs →
    LargeEvenMarking L (fun lab _ _ I _ θ => S p lab ∧ LargeEvenSplit p lab ∧
      B ≤ Subgroup.normalizer (L : Set G) ∧
      ∀ b ∈ B, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) →
    ∃ D J : Subgroup G, LargeEvenStdSub p B x L D J ∧
      Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D

theorem GGStdSubIOneProperInputOn.or {S T : ℕ → LargeEvenLabel → Prop}
    (hS : GGStdSubIOneProperInputOn S) (hT : GGStdSubIOneProperInputOn T) :
    GGStdSubIOneProperInputOn fun p lab => S p lab ∨ T p lab := by
  intro G _ _ p B Bs x L hI hBs hne hM
  obtain ⟨hperf, lab, hlab, hraw⟩ := hM
  obtain ⟨R, _, I, F, -, -, θ, hST, -⟩ := largeEvenRawDatum_exists hraw
  rcases hST with h | h
  · exact hS G p B Bs x L hI hBs hne ⟨hperf, lab, hlab, largeEvenRawDatum_mono
      (fun _ _ _ _ ⟨hs, hna, θ', _, hP⟩ => ⟨hs, hna, θ', h, hP⟩) hraw⟩
  · exact hT G p B Bs x L hI hBs hne ⟨hperf, lab, hlab, largeEvenRawDatum_mono
      (fun _ _ _ _ ⟨hs, hna, θ', _, hP⟩ => ⟨hs, hna, θ', h, hP⟩) hraw⟩

theorem ggStdSubIOneProperInput_of_cover {S : ℕ → LargeEvenLabel → Prop}
    (hS : GGStdSubIOneProperInputOn S)
    (hcov : ∀ p lab, LargeEvenInLambda2 lab → LargeEvenSplit p lab → S p lab) :
    GGStdSubIOneProperInput := by
  intro G _ _ p B Bs x L hI hBs hne
  obtain ⟨hperf, lab, hlab, hraw⟩ := hI.2.2.2.2.2.2.2.1
  exact hS G p B Bs x L hI hBs hne ⟨hperf, lab, hlab, largeEvenRawDatum_mono
    (fun _ _ _ _ ⟨hs, hna, θ, hP⟩ => ⟨hs, hna, θ, hcov p lab hlab hP.1, hP⟩) hraw⟩

end CFSG.StandardType
