module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection9.PFsection9_8.XmuTransport

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped IsMulCommutative commutatorElement

namespace CFSG.Section9

universe u v w

@[expose] public noncomputable def theorem_9_8_initial_degree_subfamily_sec9
    {G : Type u} [Group G] [Finite G]
    (M : Subgroup G)
    (q a : ℕ)
    (SH0U : Finset (Section1.ClassFunction M)) :
    Finset (Section1.ClassFunction M) := by
  classical
  exact SH0U.filter fun χ =>
    Section1.IsIrreducibleCharacterOnGroup χ ∧
      Section1.degree χ = (q * a : ℂ)

@[expose] public def theorem_9_8_initial_constituent_family_data_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U H0 Uprime : Subgroup G)
    (p a : ℕ) : Prop :=
  ∃ ι : Type u, ∃ instFintype : Fintype ι, ∃ instDecidableEq : DecidableEq ι,
    letI : Fintype ι := instFintype
    letI : DecidableEq ι := instDecidableEq
    ∃ θ : ι → Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M),
      Function.Injective
          (fun i : ι =>
            Section1.inducedCF ((ambientDerivedSubgroup M).subgroupOf M) (θ i)) ∧
        ((p - 1) / a) * (Nat.card U / (a * Nat.card Uprime)) ≤ Fintype.card ι ∧
        ∀ i : ι,
          Section1.IsIrreducibleCharacterOnGroup (θ i) ∧
            ¬ Section1.subgroupInKernel' (θ i)
              ((MF.subgroupOf M).subgroupOf
                ((ambientDerivedSubgroup M).subgroupOf M)) ∧
            Section1.subgroupInKernel' (θ i)
              (((H0 ⊔ Uprime).subgroupOf M).subgroupOf
                ((ambientDerivedSubgroup M).subgroupOf M)) ∧
            Section1.degree (θ i) = (a : ℂ) ∧
            Section1.IsIrreducibleCharacterOnGroup
              (Section1.inducedCF ((ambientDerivedSubgroup M).subgroupOf M) (θ i))

public theorem theorem_9_8_initial_degree_count_of_constituent_family_data_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 Uprime : Subgroup G)
    (p q a : ℕ)
    (SH0U : Finset (Section1.ClassFunction M)) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ Uprime) SH0U →
        theorem_9_8_initial_constituent_family_data_sec9 M MF U H0 Uprime p a →
          (theorem_9_8_initial_degree_subfamily_sec9 M q a SH0U).card ≥
            ((p - 1) / a) * (Nat.card U / (a * Nat.card Uprime)) := by
  intro h92 hSH0U hfamily
  classical
  rcases hfamily with ⟨ι, instFintype, instDecidableEq, θ, hθinj, hcard, hθdata⟩
  letI : Fintype ι := instFintype
  letI : DecidableEq ι := instDecidableEq
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let μ : ι → Section1.ClassFunction M := fun i => Section1.inducedCF Dm (θ i)
  let image : Finset (Section1.ClassFunction M) := Finset.univ.image μ
  have hDindex : Subgroup.index Dm = q :=
    ambientDerived_subgroupOf_index_eq_q_of_hypothesis_9_2_sec9
      M MF U W1 W2 q h92
  have himage_card : image.card = Fintype.card ι := by
    simpa [image, μ, Dm] using
      Finset.card_image_of_injective (s := (Finset.univ : Finset ι)) hθinj
  have himage_sub :
      image ⊆ theorem_9_8_initial_degree_subfamily_sec9 M q a SH0U := by
    intro χ hχ
    rcases Finset.mem_image.mp hχ with ⟨i, _hi, rfl⟩
    rcases hθdata i with ⟨hθirr, hθnot, hθker, hθdegree, hμirr⟩
    have hμSH0U : μ i ∈ SH0U := by
      rcases hSH0U with ⟨_hYle, _hMFle, hmem⟩
      rw [hmem (μ i)]
      exact ⟨θ i, hθirr, by simpa [Dm] using hθnot, by simpa [Dm] using hθker, rfl⟩
    have hμdegree : Section1.degree (μ i) = (q * a : ℂ) := by
      change Section1.degree (Section1.inducedCF Dm (θ i)) = (q * a : ℂ)
      rw [Section1.degree_inducedClassFunction, hθdegree, hDindex]
    simpa [theorem_9_8_initial_degree_subfamily_sec9, μ] using
      (show μ i ∈ SH0U ∧
          Section1.IsIrreducibleCharacterOnGroup (μ i) ∧
          Section1.degree (μ i) = (q * a : ℂ) from
        ⟨hμSH0U, hμirr, hμdegree⟩)
  have himage_le :
      image.card ≤ (theorem_9_8_initial_degree_subfamily_sec9 M q a SH0U).card :=
    Finset.card_le_card himage_sub
  exact hcard.trans (by simpa [himage_card] using himage_le)

@[expose] public def theorem_9_8_initial_constituent_orbit_data_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U H0 Uprime : Subgroup G)
    (p a : ℕ) : Prop :=
  ∃ κ : Type u, ∃ instFintypeκ : Fintype κ, ∃ instDecidableEqκ : DecidableEq κ,
    ∃ ι : Type u, ∃ instFintypeι : Fintype ι, ∃ instDecidableEqι : DecidableEq ι,
      letI : Fintype κ := instFintypeκ
      letI : DecidableEq κ := instDecidableEqκ
      letI : Fintype ι := instFintypeι
      letI : DecidableEq ι := instDecidableEqι
      ∃ orbit : κ → ι,
        (((p - 1) / a) * (Nat.card U / (a * Nat.card Uprime))) * a ≤
          Fintype.card κ ∧
        (∀ i : ι, Fintype.card {k : κ // orbit k = i} = a) ∧
        ∃ θ : ι → Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M),
          Function.Injective
              (fun i : ι =>
                Section1.inducedCF ((ambientDerivedSubgroup M).subgroupOf M) (θ i)) ∧
            ∀ i : ι,
              Section1.IsIrreducibleCharacterOnGroup (θ i) ∧
                ¬ Section1.subgroupInKernel' (θ i)
                  ((MF.subgroupOf M).subgroupOf
                    ((ambientDerivedSubgroup M).subgroupOf M)) ∧
                Section1.subgroupInKernel' (θ i)
                  (((H0 ⊔ Uprime).subgroupOf M).subgroupOf
                    ((ambientDerivedSubgroup M).subgroupOf M)) ∧
                Section1.degree (θ i) = (a : ℂ) ∧
                Section1.IsIrreducibleCharacterOnGroup
                  (Section1.inducedCF ((ambientDerivedSubgroup M).subgroupOf M) (θ i))

@[expose] public def theorem_9_8_initial_constituent_Mtheta_data_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U H0 Uprime : Subgroup G)
    (p a : ℕ) : Prop :=
  ∃ κ : Type u, ∃ instFintypeκ : Fintype κ, ∃ instDecidableEqκ : DecidableEq κ,
    ∃ ι : Type u, ∃ instFintypeι : Fintype ι, ∃ instDecidableEqι : DecidableEq ι,
      letI : Fintype κ := instFintypeκ
      letI : DecidableEq κ := instDecidableEqκ
      letI : Fintype ι := instFintypeι
      letI : DecidableEq ι := instDecidableEqι
      ∃ orbit : κ → ι,
        Fintype.card κ = (p - 1) * (Nat.card U / (a * Nat.card Uprime)) ∧
        (∀ i : ι, Fintype.card {k : κ // orbit k = i} = a) ∧
        ∃ θ : ι → Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M),
          Function.Injective
              (fun i : ι =>
                Section1.inducedCF ((ambientDerivedSubgroup M).subgroupOf M) (θ i)) ∧
            ∀ i : ι,
              Section1.IsIrreducibleCharacterOnGroup (θ i) ∧
                ¬ Section1.subgroupInKernel' (θ i)
                  ((MF.subgroupOf M).subgroupOf
                    ((ambientDerivedSubgroup M).subgroupOf M)) ∧
                Section1.subgroupInKernel' (θ i)
                  (((H0 ⊔ Uprime).subgroupOf M).subgroupOf
                    ((ambientDerivedSubgroup M).subgroupOf M)) ∧
                Section1.degree (θ i) = (a : ℂ) ∧
                Section1.IsIrreducibleCharacterOnGroup
                  (Section1.inducedCF ((ambientDerivedSubgroup M).subgroupOf M) (θ i))

@[expose] public def theorem_9_8_initial_constituent_Mtheta_raw_product_data_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U H0 Uprime : Subgroup G)
    (p a : ℕ) : Prop :=
  ∃ Lam : Type u, ∃ instFintypeLam : Fintype Lam,
    ∃ instDecidableEqLam : DecidableEq Lam,
    letI : Fintype Lam := instFintypeLam
    letI : DecidableEq Lam := instDecidableEqLam
    Fintype.card Lam = Nat.card U / (a * Nat.card Uprime) ∧
      ∃ ι : Type u, ∃ instFintypeι : Fintype ι, ∃ instDecidableEqι : DecidableEq ι,
        letI : Fintype ι := instFintypeι
        letI : DecidableEq ι := instDecidableEqι
        ∃ orbit : (Fin (p - 1) × Lam) → ι,
          (∀ i : ι, Fintype.card {k : Fin (p - 1) × Lam // orbit k = i} = a) ∧
          ∃ θ : ι → Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M),
            Function.Injective
                (fun i : ι =>
                  Section1.inducedCF ((ambientDerivedSubgroup M).subgroupOf M) (θ i)) ∧
              ∀ i : ι,
                Section1.IsIrreducibleCharacterOnGroup (θ i) ∧
                  ¬ Section1.subgroupInKernel' (θ i)
                    ((MF.subgroupOf M).subgroupOf
                      ((ambientDerivedSubgroup M).subgroupOf M)) ∧
                  Section1.subgroupInKernel' (θ i)
                    (((H0 ⊔ Uprime).subgroupOf M).subgroupOf
                      ((ambientDerivedSubgroup M).subgroupOf M)) ∧
                  Section1.degree (θ i) = (a : ℂ) ∧
                  Section1.IsIrreducibleCharacterOnGroup
                    (Section1.inducedCF ((ambientDerivedSubgroup M).subgroupOf M) (θ i))

@[expose] public def theorem_9_8_initial_constituent_Mtheta_free_action_data_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U H0 Uprime : Subgroup G)
    (p a : ℕ) : Prop :=
  ∃ Lam : Type u, ∃ instFintypeLam : Fintype Lam,
    ∃ instDecidableEqLam : DecidableEq Lam,
    letI : Fintype Lam := instFintypeLam
    letI : DecidableEq Lam := instDecidableEqLam
    Fintype.card Lam = Nat.card U / (a * Nat.card Uprime) ∧
      ∃ A : Type u, ∃ instGroupA : Group A, ∃ instFintypeA : Fintype A,
        letI : Group A := instGroupA
        letI : Fintype A := instFintypeA
        Nat.card A = a ∧
          ∃ instAction : MulAction A (Fin (p - 1) × Lam),
            letI : MulAction A (Fin (p - 1) × Lam) := instAction
            (∀ k : Fin (p - 1) × Lam, MulAction.stabilizer A k = ⊥) ∧
              ∃ θ :
                Quotient (MulAction.orbitRel A (Fin (p - 1) × Lam)) →
                  Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M),
                Function.Injective
                    (fun i : Quotient (MulAction.orbitRel A (Fin (p - 1) × Lam)) =>
                      Section1.inducedCF ((ambientDerivedSubgroup M).subgroupOf M)
                        (θ i)) ∧
                  ∀ i : Quotient (MulAction.orbitRel A (Fin (p - 1) × Lam)),
                    Section1.IsIrreducibleCharacterOnGroup (θ i) ∧
                      ¬ Section1.subgroupInKernel' (θ i)
                        ((MF.subgroupOf M).subgroupOf
                          ((ambientDerivedSubgroup M).subgroupOf M)) ∧
                      Section1.subgroupInKernel' (θ i)
                        (((H0 ⊔ Uprime).subgroupOf M).subgroupOf
                          ((ambientDerivedSubgroup M).subgroupOf M)) ∧
                      Section1.degree (θ i) = (a : ℂ) ∧
                      Section1.IsIrreducibleCharacterOnGroup
                        (Section1.inducedCF ((ambientDerivedSubgroup M).subgroupOf M)
                          (θ i))

@[expose] public def theorem_9_8_initial_constituent_Mtheta_cyclic_action_data_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U H0 Uprime : Subgroup G)
    (p a : ℕ) [NeZero a] : Prop :=
  ∃ Lam : Type u, ∃ instFintypeLam : Fintype Lam,
    ∃ instDecidableEqLam : DecidableEq Lam,
    letI : Fintype Lam := instFintypeLam
    letI : DecidableEq Lam := instDecidableEqLam
    Fintype.card Lam = Nat.card U / (a * Nat.card Uprime) ∧
      ∃ instAction :
        MulAction (ULift.{u,0} (Multiplicative (ZMod a))) (Fin (p - 1) × Lam),
        letI : MulAction (ULift.{u,0} (Multiplicative (ZMod a)))
            (Fin (p - 1) × Lam) := instAction
        (∀ k : Fin (p - 1) × Lam,
          MulAction.stabilizer (ULift.{u,0} (Multiplicative (ZMod a))) k = ⊥) ∧
          ∃ θ :
            Quotient
                (MulAction.orbitRel
                  (ULift.{u,0} (Multiplicative (ZMod a))) (Fin (p - 1) × Lam)) →
              Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M),
            Function.Injective
                (fun i : Quotient
                    (MulAction.orbitRel
                      (ULift.{u,0} (Multiplicative (ZMod a))) (Fin (p - 1) × Lam)) =>
                  Section1.inducedCF ((ambientDerivedSubgroup M).subgroupOf M)
                    (θ i)) ∧
              ∀ i : Quotient
                  (MulAction.orbitRel
                    (ULift.{u,0} (Multiplicative (ZMod a))) (Fin (p - 1) × Lam)),
                Section1.IsIrreducibleCharacterOnGroup (θ i) ∧
                  ¬ Section1.subgroupInKernel' (θ i)
                    ((MF.subgroupOf M).subgroupOf
                      ((ambientDerivedSubgroup M).subgroupOf M)) ∧
                  Section1.subgroupInKernel' (θ i)
                    (((H0 ⊔ Uprime).subgroupOf M).subgroupOf
                      ((ambientDerivedSubgroup M).subgroupOf M)) ∧
                  Section1.degree (θ i) = (a : ℂ) ∧
                  Section1.IsIrreducibleCharacterOnGroup
                    (Section1.inducedCF ((ambientDerivedSubgroup M).subgroupOf M)
                      (θ i))

public theorem orbitRel_compHom_mulEquiv_iff_sec9
    {A : Type u} {B : Type v} {κ : Type w}
    [Group A] [Group B] [MulAction B κ]
    (e : A ≃* B) :
    let instAction : MulAction A κ := MulAction.compHom κ e.toMonoidHom
    letI : MulAction A κ := instAction
    ∀ x y : κ,
      (MulAction.orbitRel A κ) x y ↔ (MulAction.orbitRel B κ) x y := by
  intro instAction
  letI : MulAction A κ := instAction
  intro x y
  constructor
  · intro h
    rw [MulAction.orbitRel_apply] at h ⊢
    rcases MulAction.mem_orbit_iff.mp h with ⟨g, hg⟩
    exact MulAction.mem_orbit_iff.mpr
      ⟨e g, by simpa [instAction, MulAction.compHom_smul_def] using hg⟩
  · intro h
    rw [MulAction.orbitRel_apply] at h ⊢
    rcases MulAction.mem_orbit_iff.mp h with ⟨b, hb⟩
    exact MulAction.mem_orbit_iff.mpr
      ⟨e.symm b, by simpa [instAction, MulAction.compHom_smul_def] using hb⟩

public theorem stabilizer_compHom_mulEquiv_eq_bot_sec9
    {A : Type u} {B : Type v} {κ : Type w}
    [Group A] [Group B] [MulAction B κ]
    (e : A ≃* B)
    (hfree : ∀ k : κ, MulAction.stabilizer B k = ⊥) :
    let instAction : MulAction A κ := MulAction.compHom κ e.toMonoidHom
    letI : MulAction A κ := instAction
    ∀ k : κ, MulAction.stabilizer A k = ⊥ := by
  intro instAction
  letI : MulAction A κ := instAction
  intro k
  ext g
  constructor
  · intro hg
    rw [Subgroup.mem_bot]
    have hbg : e g ∈ MulAction.stabilizer B k := by
      rw [MulAction.mem_stabilizer_iff]
      rw [MulAction.mem_stabilizer_iff] at hg
      simpa [instAction, MulAction.compHom_smul_def] using hg
    have hbg1 : e g = 1 := by
      simpa [hfree k] using hbg
    exact e.injective (by simpa using hbg1)
  · intro hg
    rw [Subgroup.mem_bot] at hg
    rw [hg]
    simp

@[expose] public def theorem_9_8_initial_constituent_Mtheta_abstract_cyclic_action_data_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U H0 Uprime : Subgroup G)
    (p a : ℕ) : Prop :=
  ∃ Lam : Type u, ∃ instFintypeLam : Fintype Lam,
    ∃ instDecidableEqLam : DecidableEq Lam,
    letI : Fintype Lam := instFintypeLam
    letI : DecidableEq Lam := instDecidableEqLam
    Fintype.card Lam = Nat.card U / (a * Nat.card Uprime) ∧
      ∃ A : Type u, ∃ instGroupA : Group A, ∃ instFintypeA : Fintype A,
        letI : Group A := instGroupA
        letI : Fintype A := instFintypeA
        IsCyclic A ∧ Nat.card A = a ∧
          ∃ instAction : MulAction A (Fin (p - 1) × Lam),
            letI : MulAction A (Fin (p - 1) × Lam) := instAction
            (∀ k : Fin (p - 1) × Lam, MulAction.stabilizer A k = ⊥) ∧
              ∃ θ :
                Quotient (MulAction.orbitRel A (Fin (p - 1) × Lam)) →
                  Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M),
                Function.Injective
                    (fun i : Quotient (MulAction.orbitRel A (Fin (p - 1) × Lam)) =>
                      Section1.inducedCF ((ambientDerivedSubgroup M).subgroupOf M)
                        (θ i)) ∧
                  ∀ i : Quotient (MulAction.orbitRel A (Fin (p - 1) × Lam)),
                    Section1.IsIrreducibleCharacterOnGroup (θ i) ∧
                      ¬ Section1.subgroupInKernel' (θ i)
                        ((MF.subgroupOf M).subgroupOf
                          ((ambientDerivedSubgroup M).subgroupOf M)) ∧
                      Section1.subgroupInKernel' (θ i)
                        (((H0 ⊔ Uprime).subgroupOf M).subgroupOf
                          ((ambientDerivedSubgroup M).subgroupOf M)) ∧
                      Section1.degree (θ i) = (a : ℂ) ∧
                      Section1.IsIrreducibleCharacterOnGroup
                        (Section1.inducedCF ((ambientDerivedSubgroup M).subgroupOf M)
                          (θ i))

public theorem theorem_9_8_initial_constituent_Mtheta_cyclic_action_data_of_abstract_cyclic_action_data_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U H0 Uprime : Subgroup G)
    (p a : ℕ) [NeZero a] :
    theorem_9_8_initial_constituent_Mtheta_abstract_cyclic_action_data_sec9
      M MF U H0 Uprime p a →
        theorem_9_8_initial_constituent_Mtheta_cyclic_action_data_sec9
          M MF U H0 Uprime p a := by
  intro habstract
  classical
  rcases habstract with
    ⟨Lam, instFintypeLam, instDecidableEqLam, hLamcard,
      A, instGroupA, instFintypeA, hcyclicA, hAcard, instActionA, hfreeA,
      θA, hθinjA, hθdataA⟩
  letI : Fintype Lam := instFintypeLam
  letI : DecidableEq Lam := instDecidableEqLam
  letI : Group A := instGroupA
  letI : Fintype A := instFintypeA
  let κ : Type u := Fin (p - 1) × Lam
  let eZ : Multiplicative (ZMod a) ≃* A :=
    (AddEquiv.toMultiplicative
        (ZMod.ringEquivCongr hAcard.symm).toAddEquiv).trans
      (zmodCyclicMulEquiv hcyclicA)
  let eCanon : ULift.{u,0} (Multiplicative (ZMod a)) ≃* A :=
    MulEquiv.ulift.trans eZ
  let instActionCanon :
      MulAction (ULift.{u,0} (Multiplicative (ZMod a))) κ :=
    MulAction.compHom κ eCanon.toMonoidHom
  letI : MulAction (ULift.{u,0} (Multiplicative (ZMod a))) κ := instActionCanon
  have hrel : ∀ x y : κ,
      (MulAction.orbitRel (ULift.{u,0} (Multiplicative (ZMod a))) κ) x y ↔
        (MulAction.orbitRel A κ) x y := by
    intro x y
    simpa [instActionCanon] using
      orbitRel_compHom_mulEquiv_iff_sec9
        (A := ULift.{u,0} (Multiplicative (ZMod a))) (B := A) (κ := κ)
        eCanon x y
  let orbitToA :
      Quotient (MulAction.orbitRel (ULift.{u,0} (Multiplicative (ZMod a))) κ) →
        Quotient (MulAction.orbitRel A κ) :=
    Quotient.map (fun x : κ => x) (by
      intro x y hxy
      exact (hrel x y).mp hxy)
  have hOrbitMap_inj : Function.Injective orbitToA := by
    intro i j hij
    refine Quotient.inductionOn₂ i j ?_ hij
    intro x y hxy
    apply Quotient.sound
    exact (hrel x y).mpr (Quotient.exact hxy)
  let θCanon :
      Quotient (MulAction.orbitRel
        (ULift.{u,0} (Multiplicative (ZMod a))) κ) →
          Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M) :=
    fun i => θA (orbitToA i)
  refine ⟨Lam, instFintypeLam, instDecidableEqLam, hLamcard,
    instActionCanon, ?_, θCanon, ?_, ?_⟩
  · have hfreeA' : ∀ k : κ, MulAction.stabilizer A k = ⊥ := by
      intro k
      simpa [κ] using hfreeA k
    simpa [κ, instActionCanon] using
      stabilizer_compHom_mulEquiv_eq_bot_sec9
        (A := ULift.{u,0} (Multiplicative (ZMod a))) (B := A) (κ := κ)
        eCanon hfreeA'
  · intro i j hij
    exact hOrbitMap_inj (hθinjA (by simpa [θCanon] using hij))
  · intro i
    simpa [θCanon] using hθdataA (orbitToA i)

public theorem theorem_9_8_initial_constituent_Mtheta_free_action_data_of_cyclic_action_data_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U H0 Uprime : Subgroup G)
    (p a : ℕ) [NeZero a] :
    theorem_9_8_initial_constituent_Mtheta_cyclic_action_data_sec9
      M MF U H0 Uprime p a →
        theorem_9_8_initial_constituent_Mtheta_free_action_data_sec9
          M MF U H0 Uprime p a := by
  intro hcyc
  classical
  rcases hcyc with
    ⟨Lam, instFintypeLam, instDecidableEqLam, hLamcard, instAction, hfree,
      θ, hθinj, hθdata⟩
  letI : Fintype Lam := instFintypeLam
  letI : DecidableEq Lam := instDecidableEqLam
  let A : Type u := ULift.{u,0} (Multiplicative (ZMod a))
  let instGroupA : Group A := inferInstance
  letI : Fintype (ZMod a) := ZMod.fintype a
  let instFintypeA : Fintype A :=
    Fintype.ofEquiv (Multiplicative (ZMod a)) Equiv.ulift.symm
  have hAcard : Nat.card A = a := by
    calc
      Nat.card A = Nat.card (Multiplicative (ZMod a)) :=
        Nat.card_congr Equiv.ulift
      _ = a :=
        (Nat.card_congr
          (Multiplicative.toAdd : Multiplicative (ZMod a) ≃ ZMod a)).trans
          (Nat.card_zmod a)
  exact ⟨Lam, instFintypeLam, instDecidableEqLam, hLamcard,
    A, instGroupA, instFintypeA, hAcard, instAction, hfree, θ, hθinj, hθdata⟩

public theorem theorem_9_8_initial_constituent_Mtheta_raw_product_data_of_free_action_data_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U H0 Uprime : Subgroup G)
    (p a : ℕ) :
    theorem_9_8_initial_constituent_Mtheta_free_action_data_sec9
      M MF U H0 Uprime p a →
        theorem_9_8_initial_constituent_Mtheta_raw_product_data_sec9
          M MF U H0 Uprime p a := by
  intro hfreeData
  classical
  rcases hfreeData with
    ⟨Lam, instFintypeLam, instDecidableEqLam, hLamcard,
      A, instGroupA, instFintypeA, hAcard, instAction, hfree, θ, hθinj,
      hθdata⟩
  letI : Fintype Lam := instFintypeLam
  letI : DecidableEq Lam := instDecidableEqLam
  letI : Group A := instGroupA
  letI : Fintype A := instFintypeA
  let κ : Type u := Fin (p - 1) × Lam
  letI : MulAction A κ := instAction
  let ι : Type u := Quotient (MulAction.orbitRel A κ)
  let instFintypeι : Fintype ι := Fintype.ofFinite ι
  let instDecidableEqι : DecidableEq ι := Classical.decEq ι
  let orbit : κ → ι := fun k => Quotient.mk'' k
  refine ⟨Lam, instFintypeLam, instDecidableEqLam, hLamcard,
    ι, instFintypeι, instDecidableEqι, orbit, ?_, θ, ?_, ?_⟩
  · intro i
    rw [← hAcard]
    rw [← Nat.card_eq_fintype_card]
    exact freeAction_orbitQuotient_fiber_natCard_sec9 (A := A) (κ := κ)
      hfree i
  · simpa [κ, ι] using hθinj
  · intro i
    simpa [κ, ι] using hθdata i

public theorem theorem_9_8_initial_constituent_Mtheta_data_of_raw_product_data_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U H0 Uprime : Subgroup G)
    (p a : ℕ) :
    theorem_9_8_initial_constituent_Mtheta_raw_product_data_sec9
      M MF U H0 Uprime p a →
        theorem_9_8_initial_constituent_Mtheta_data_sec9 M MF U H0 Uprime p a := by
  intro hraw
  classical
  rcases hraw with
    ⟨Lam, instFintypeLam, instDecidableEqLam, hLamcard,
      ι, instFintypeι, instDecidableEqι, orbit, hfiber, θ, hθinj, hθdata⟩
  letI : Fintype Lam := instFintypeLam
  letI : DecidableEq Lam := instDecidableEqLam
  letI : Fintype ι := instFintypeι
  letI : DecidableEq ι := instDecidableEqι
  let κ : Type u := Fin (p - 1) × Lam
  let instFintypeκ : Fintype κ := inferInstance
  let instDecidableEqκ : DecidableEq κ := inferInstance
  refine ⟨κ, instFintypeκ, instDecidableEqκ,
    ι, instFintypeι, instDecidableEqι, orbit, ?_, hfiber, θ, hθinj, hθdata⟩
  calc
    Fintype.card κ = (p - 1) * Fintype.card Lam := by
      simp [κ]
    _ = (p - 1) * (Nat.card U / (a * Nat.card Uprime)) := by
      rw [hLamcard]

public theorem theorem_9_8_initial_constituent_orbit_data_of_Mtheta_data_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U H0 Uprime : Subgroup G)
    (p a : ℕ) :
    a ∣ p - 1 →
      theorem_9_8_initial_constituent_Mtheta_data_sec9 M MF U H0 Uprime p a →
        theorem_9_8_initial_constituent_orbit_data_sec9 M MF U H0 Uprime p a := by
  intro hdiv hMtheta
  classical
  rcases hMtheta with
    ⟨κ, instFintypeκ, instDecidableEqκ,
      ι, instFintypeι, instDecidableEqι, orbit, hκcard, hfiber,
      θ, hθinj, hθdata⟩
  letI : Fintype κ := instFintypeκ
  letI : DecidableEq κ := instDecidableEqκ
  letI : Fintype ι := instFintypeι
  letI : DecidableEq ι := instDecidableEqι
  refine ⟨κ, instFintypeκ, instDecidableEqκ,
    ι, instFintypeι, instDecidableEqι, orbit, ?_, hfiber, θ, hθinj, hθdata⟩
  let b : ℕ := Nat.card U / (a * Nat.card Uprime)
  have hrawEq :
      (((p - 1) / a) * b) * a = Fintype.card κ := by
    calc
      (((p - 1) / a) * b) * a = (p - 1) * b := by
        rw [Nat.mul_assoc, Nat.mul_comm b a, ← Nat.mul_assoc,
          Nat.div_mul_cancel hdiv]
      _ = Fintype.card κ := hκcard.symm
  simpa [b] using le_of_eq hrawEq

public theorem theorem_9_8_initial_constituent_family_data_of_orbit_data_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U H0 Uprime : Subgroup G)
    (p a : ℕ) :
    0 < a →
      theorem_9_8_initial_constituent_orbit_data_sec9 M MF U H0 Uprime p a →
        theorem_9_8_initial_constituent_family_data_sec9 M MF U H0 Uprime p a := by
  intro ha horbit
  classical
  rcases horbit with
    ⟨κ, instFintypeκ, _instDecidableEqκ,
      ι, instFintypeι, instDecidableEqι, orbit, hrawCard, hfiber,
      θ, hθinj, hθdata⟩
  letI : Fintype κ := instFintypeκ
  letI : Fintype ι := instFintypeι
  letI : DecidableEq ι := instDecidableEqι
  refine ⟨ι, instFintypeι, instDecidableEqι, θ, hθinj, ?_, hθdata⟩
  have hκcard :
      Fintype.card κ = a * Fintype.card ι :=
    card_eq_mul_card_of_fiber_card_sec9 orbit a hfiber
  have hmul :
      (((p - 1) / a) * (Nat.card U / (a * Nat.card Uprime))) * a ≤
        Fintype.card ι * a := by
    calc
      (((p - 1) / a) * (Nat.card U / (a * Nat.card Uprime))) * a
          ≤ Fintype.card κ := hrawCard
      _ = a * Fintype.card ι := hκcard
      _ = Fintype.card ι * a := Nat.mul_comm a (Fintype.card ι)
  exact le_of_mul_le_mul_right hmul ha

@[expose] public def theorem_9_8_initial_constituent_Mtheta_base_range_action_data_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U H0 C Uprime : Subgroup G)
    (p q a : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hnormalC : (C.subgroupOf U).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hqpos : 0 < q)
    (ρBase : (U ⧸ C.subgroupOf U) →* MulAut (H ⟨0, hqpos⟩)) : Prop :=
  ∃ Lam : Type u, ∃ instFintypeLam : Fintype Lam,
    ∃ instDecidableEqLam : DecidableEq Lam,
    letI : Fintype Lam := instFintypeLam
    letI : DecidableEq Lam := instDecidableEqLam
    Fintype.card Lam = Nat.card U / (a * Nat.card Uprime) ∧
      ∃ instAction : MulAction ρBase.range (Fin (p - 1) × Lam),
        letI : MulAction ρBase.range (Fin (p - 1) × Lam) := instAction
        (∀ k : Fin (p - 1) × Lam, MulAction.stabilizer ρBase.range k = ⊥) ∧
          ∃ θ :
            Quotient (MulAction.orbitRel ρBase.range (Fin (p - 1) × Lam)) →
              Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M),
            Function.Injective
                (fun i : Quotient
                    (MulAction.orbitRel ρBase.range (Fin (p - 1) × Lam)) =>
                  Section1.inducedCF ((ambientDerivedSubgroup M).subgroupOf M)
                    (θ i)) ∧
              ∀ i : Quotient
                  (MulAction.orbitRel ρBase.range (Fin (p - 1) × Lam)),
                Section1.IsIrreducibleCharacterOnGroup (θ i) ∧
                  ¬ Section1.subgroupInKernel' (θ i)
                    ((MF.subgroupOf M).subgroupOf
                      ((ambientDerivedSubgroup M).subgroupOf M)) ∧
                  Section1.subgroupInKernel' (θ i)
                    (((H0 ⊔ Uprime).subgroupOf M).subgroupOf
                      ((ambientDerivedSubgroup M).subgroupOf M)) ∧
                  Section1.degree (θ i) = (a : ℂ) ∧
                  Section1.IsIrreducibleCharacterOnGroup
                    (Section1.inducedCF ((ambientDerivedSubgroup M).subgroupOf M)
                      (θ i))

public theorem theorem_9_8_initial_constituent_Mtheta_uprime_subgroupOf_normal_sec9
    {G : Type u} [Group G] [Finite G]
    (U Uprime : Subgroup G)
    (hUprimeEq : Uprime = (_root_.commutator U).map U.subtype) :
    (Uprime.subgroupOf U).Normal := by
  classical
  rw [hUprimeEq]
  have hsub :
      ((Subgroup.map U.subtype (_root_.commutator U)).subgroupOf U) =
        _root_.commutator U := by
    ext x
    constructor
    · intro hx
      change (x : G) ∈ Subgroup.map U.subtype (_root_.commutator U) at hx
      rcases hx with ⟨y, hy, hyx⟩
      have hxy : x = y := Subtype.ext (by simpa using hyx.symm)
      simpa [hxy]
    · intro hx
      change (x : G) ∈ Subgroup.map U.subtype (_root_.commutator U)
      exact ⟨x, hx, rfl⟩
  rw [hsub]
  infer_instance

public theorem theorem_9_8_initial_constituent_Mtheta_baseActionKernel_uprime_le_sec9
    {G Q : Type u} [Group G] [Finite G] [Group Q]
    (U C Uprime : Subgroup G)
    [hnormalC : (C.subgroupOf U).Normal]
    (ρBase : (U ⧸ C.subgroupOf U) →* MulAut Q)
    (hρcycBase : IsCyclic ρBase.range)
    (hUprimeEq : Uprime = (_root_.commutator U).map U.subtype) :
    let f : U →* ρBase.range :=
      ρBase.rangeRestrict.comp (QuotientGroup.mk' (C.subgroupOf U))
    Uprime.subgroupOf U ≤ f.ker := by
  classical
  intro f x hx
  have hxG : (x : G) ∈ Uprime := by
    simpa [Subgroup.mem_subgroupOf] using hx
  rw [hUprimeEq] at hxG
  rcases hxG with ⟨y, hy, hy_eq⟩
  have hxy : x = y := Subtype.ext (by simpa using hy_eq.symm)
  letI : IsCyclic ρBase.range := hρcycBase
  letI : CommGroup ρBase.range := IsCyclic.commGroup
  have hyker : y ∈ f.ker := Abelianization.commutator_subset_ker f hy
  simpa [hxy]

public theorem theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_comm_sec9
    {G Q : Type u} [Group G] [Finite G] [Group Q]
    (U C Uprime : Subgroup G)
    [hnormalC : (C.subgroupOf U).Normal]
    (ρBase : (U ⧸ C.subgroupOf U) →* MulAut Q)
    (hUprimeEq : Uprime = (_root_.commutator U).map U.subtype) :
    let f : U →* ρBase.range :=
      ρBase.rangeRestrict.comp (QuotientGroup.mk' (C.subgroupOf U))
    let K : Subgroup U := f.ker
    let Hsub : Subgroup K := (Uprime.subgroupOf U).subgroupOf K
    letI : Hsub.Normal :=
      (theorem_9_8_initial_constituent_Mtheta_uprime_subgroupOf_normal_sec9
        U Uprime hUprimeEq).subgroupOf K
    IsMulCommutative (K ⧸ Hsub) := by
  classical
  intro f K Hsub
  letI : (Uprime.subgroupOf U).Normal :=
    theorem_9_8_initial_constituent_Mtheta_uprime_subgroupOf_normal_sec9
      U Uprime hUprimeEq
  letI : Hsub.Normal :=
    (theorem_9_8_initial_constituent_Mtheta_uprime_subgroupOf_normal_sec9
      U Uprime hUprimeEq).subgroupOf K
  apply Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
  intro x hx
  change (x : U) ∈ Uprime.subgroupOf U
  rw [hUprimeEq]
  have hsub :
      ((Subgroup.map U.subtype (_root_.commutator U)).subgroupOf U) =
        _root_.commutator U := by
    ext y
    constructor
    · intro hy
      change (y : G) ∈ Subgroup.map U.subtype (_root_.commutator U) at hy
      rcases hy with ⟨z, hz, hzy⟩
      have hyz : y = z := Subtype.ext (by simpa using hzy.symm)
      simpa [hyz]
    · intro hy
      change (y : G) ∈ Subgroup.map U.subtype (_root_.commutator U)
      exact ⟨y, hy, rfl⟩
  rw [hsub]
  have hxmap : (x : U) ∈ (_root_.commutator K).map K.subtype := by
    exact ⟨x, hx, rfl⟩
  rw [Subgroup.map_subtype_commutator] at hxmap
  exact Subgroup.commutator_mono (show K ≤ (⊤ : Subgroup U) by exact le_top)
    (show K ≤ (⊤ : Subgroup U) by exact le_top) hxmap

public theorem theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_card_sec9
    {G Q : Type u} [Group G] [Finite G] [Group Q]
    (U C Uprime : Subgroup G)
    (a : ℕ) [NeZero a]
    [hnormalC : (C.subgroupOf U).Normal]
    (ρBase : (U ⧸ C.subgroupOf U) →* MulAut Q)
    (hρcycBase : IsCyclic ρBase.range)
    (hρcardBase : Nat.card ρBase.range = a)
    (hUprimeEq : Uprime = (_root_.commutator U).map U.subtype) :
    let f : U →* ρBase.range :=
      ρBase.rangeRestrict.comp (QuotientGroup.mk' (C.subgroupOf U))
    let K : Subgroup U := f.ker
    let Hsub : Subgroup K := (Uprime.subgroupOf U).subgroupOf K
    letI : Hsub.Normal :=
      (theorem_9_8_initial_constituent_Mtheta_uprime_subgroupOf_normal_sec9
        U Uprime hUprimeEq).subgroupOf K
    Nat.card (K ⧸ Hsub) = Nat.card U / (a * Nat.card Uprime) := by
  classical
  intro f K Hsub
  letI : (Uprime.subgroupOf U).Normal :=
    theorem_9_8_initial_constituent_Mtheta_uprime_subgroupOf_normal_sec9
      U Uprime hUprimeEq
  letI : Hsub.Normal :=
    (theorem_9_8_initial_constituent_Mtheta_uprime_subgroupOf_normal_sec9
      U Uprime hUprimeEq).subgroupOf K
  have hf_range_top : f.range = ⊤ := by
    rw [MonoidHom.range_eq_top]
    intro y
    rcases y with ⟨y, hy⟩
    rcases hy with ⟨x, rfl⟩
    rcases QuotientGroup.mk'_surjective (C.subgroupOf U) x with ⟨u, rfl⟩
    exact ⟨u, rfl⟩
  have hKindex : K.index = a := by
    calc
      K.index = Nat.card f.range := by simpa [K] using Subgroup.index_ker f
      _ = Nat.card (⊤ : Subgroup ρBase.range) := by rw [hf_range_top]
      _ = Nat.card ρBase.range := by simp
      _ = a := hρcardBase
  have hKmul : a * Nat.card K = Nat.card U := by
    simpa [hKindex] using (Subgroup.index_mul_card (H := K))
  have hUprimeU : Uprime ≤ U := by
    rw [hUprimeEq, Subgroup.map_subtype_commutator]
    exact Subgroup.commutator_le_self U
  have hUprime_le_K : Uprime.subgroupOf U ≤ K := by
    simpa [K] using
      theorem_9_8_initial_constituent_Mtheta_baseActionKernel_uprime_le_sec9
        U C Uprime ρBase hρcycBase hUprimeEq
  have hHsub_card : Nat.card Hsub = Nat.card Uprime := by
    calc
      Nat.card Hsub = Nat.card (Uprime.subgroupOf U) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUprime_le_K).toEquiv
      _ = Nat.card Uprime :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUprimeU).toEquiv
  have hquot_mul : Nat.card K = Nat.card (K ⧸ Hsub) * Nat.card Hsub := by
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup Hsub
  have hmain : (a * Nat.card Uprime) * Nat.card (K ⧸ Hsub) = Nat.card U := by
    calc
      (a * Nat.card Uprime) * Nat.card (K ⧸ Hsub)
          = a * (Nat.card (K ⧸ Hsub) * Nat.card Uprime) := by ac_rfl
      _ = a * (Nat.card (K ⧸ Hsub) * Nat.card Hsub) := by rw [hHsub_card]
      _ = a * Nat.card K := by rw [← hquot_mul]
      _ = Nat.card U := hKmul
  have hden_ne : a * Nat.card Uprime ≠ 0 := by
    exact Nat.ne_of_gt
      (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne a)) (Nat.card_pos))
  exact Nat.eq_div_of_mul_eq_right hden_ne hmain

@[expose] public def theorem_9_8_initial_constituent_Mtheta_clam_parameter_data_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U H0 C Uprime : Subgroup G)
    (p q a : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hnormalC : (C.subgroupOf U).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hqpos : 0 < q)
    (ρBase : (U ⧸ C.subgroupOf U) →* MulAut (H ⟨0, hqpos⟩)) : Prop :=
  ∃ Clam : Type u, ∃ instGroupClam : Group Clam,
    ∃ instFintypeClam : Fintype Clam, ∃ instDecidableEqClam : DecidableEq Clam,
    letI : Group Clam := instGroupClam
    letI : Fintype Clam := instFintypeClam
    letI : DecidableEq Clam := instDecidableEqClam
    letI : Finite Clam := Finite.of_fintype Clam
    IsMulCommutative Clam ∧
      Fintype.card Clam = Nat.card U / (a * Nat.card Uprime) ∧
      ∃ Lam : Type u, ∃ instFintypeLam : Fintype Lam,
        ∃ instDecidableEqLam : DecidableEq Lam,
        letI : Fintype Lam := instFintypeLam
        letI : DecidableEq Lam := instDecidableEqLam
        ∃ lam : Lam → Clam →* ℂˣ,
          Function.Injective lam ∧
            Fintype.card Lam = Fintype.card Clam ∧
            (∀ j : Lam,
              Section1.IsIrreducibleCharacterOnGroup
                (fun x : Clam => (lam j x : ℂ)) ∧
                Section1.degree (fun x : Clam => (lam j x : ℂ)) = 1) ∧
            ∃ instAction : MulAction ρBase.range (Fin (p - 1) × Lam),
              letI : MulAction ρBase.range (Fin (p - 1) × Lam) := instAction
              (∀ k : Fin (p - 1) × Lam, MulAction.stabilizer ρBase.range k = ⊥) ∧
                ∃ θ :
                  Quotient (MulAction.orbitRel ρBase.range (Fin (p - 1) × Lam)) →
                    Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M),
                  Function.Injective
                      (fun i : Quotient
                          (MulAction.orbitRel ρBase.range (Fin (p - 1) × Lam)) =>
                        Section1.inducedCF ((ambientDerivedSubgroup M).subgroupOf M)
                          (θ i)) ∧
                    ∀ i : Quotient
                        (MulAction.orbitRel ρBase.range (Fin (p - 1) × Lam)),
                      Section1.IsIrreducibleCharacterOnGroup (θ i) ∧
                        ¬ Section1.subgroupInKernel' (θ i)
                          ((MF.subgroupOf M).subgroupOf
                            ((ambientDerivedSubgroup M).subgroupOf M)) ∧
                        Section1.subgroupInKernel' (θ i)
                          (((H0 ⊔ Uprime).subgroupOf M).subgroupOf
                            ((ambientDerivedSubgroup M).subgroupOf M)) ∧
                        Section1.degree (θ i) = (a : ℂ) ∧
                        Section1.IsIrreducibleCharacterOnGroup
                          (Section1.inducedCF ((ambientDerivedSubgroup M).subgroupOf M)
                            (θ i))

@[expose] public def theorem_9_8_initial_constituent_Mtheta_clam_raw_theta_data_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U H0 C Uprime : Subgroup G)
    (p q a : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hnormalC : (C.subgroupOf U).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hqpos : 0 < q)
    (ρBase : (U ⧸ C.subgroupOf U) →* MulAut (H ⟨0, hqpos⟩)) : Prop :=
  ∃ Clam : Type u, ∃ instGroupClam : Group Clam,
    ∃ instFintypeClam : Fintype Clam, ∃ instDecidableEqClam : DecidableEq Clam,
    letI : Group Clam := instGroupClam
    letI : Fintype Clam := instFintypeClam
    letI : DecidableEq Clam := instDecidableEqClam
    letI : Finite Clam := Finite.of_fintype Clam
    IsMulCommutative Clam ∧
      Fintype.card Clam = Nat.card U / (a * Nat.card Uprime) ∧
      ∃ Lam : Type u, ∃ instFintypeLam : Fintype Lam,
        ∃ instDecidableEqLam : DecidableEq Lam,
        letI : Fintype Lam := instFintypeLam
        letI : DecidableEq Lam := instDecidableEqLam
        ∃ lam : Lam → Clam →* ℂˣ,
          Function.Injective lam ∧
            Fintype.card Lam = Fintype.card Clam ∧
            (∀ j : Lam,
              Section1.IsIrreducibleCharacterOnGroup
                (fun x : Clam => (lam j x : ℂ)) ∧
                Section1.degree (fun x : Clam => (lam j x : ℂ)) = 1) ∧
            ∃ instAction : MulAction ρBase.range (Fin (p - 1) × Lam),
              letI : MulAction ρBase.range (Fin (p - 1) × Lam) := instAction
              (∀ k : Fin (p - 1) × Lam, MulAction.stabilizer ρBase.range k = ⊥) ∧
                ∃ θraw : Fin (p - 1) × Lam →
                    Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M),
                  (∀ k : Fin (p - 1) × Lam,
                    Section1.IsIrreducibleCharacterOnGroup (θraw k) ∧
                      ¬ Section1.subgroupInKernel' (θraw k)
                        ((MF.subgroupOf M).subgroupOf
                          ((ambientDerivedSubgroup M).subgroupOf M)) ∧
                      Section1.subgroupInKernel' (θraw k)
                        (((H0 ⊔ Uprime).subgroupOf M).subgroupOf
                          ((ambientDerivedSubgroup M).subgroupOf M)) ∧
                      Section1.degree (θraw k) = (a : ℂ) ∧
                      Section1.IsIrreducibleCharacterOnGroup
                        (Section1.inducedCF ((ambientDerivedSubgroup M).subgroupOf M)
                          (θraw k))) ∧
                    ∀ k l : Fin (p - 1) × Lam,
                      Section1.inducedCF ((ambientDerivedSubgroup M).subgroupOf M)
                          (θraw k) =
                        Section1.inducedCF ((ambientDerivedSubgroup M).subgroupOf M)
                          (θraw l) →
                        MulAction.orbitRel ρBase.range (Fin (p - 1) × Lam) k l

@[expose] public def theorem_9_8_initial_constituent_Mtheta_clam_index_action_data_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U H0 C Uprime : Subgroup G)
    (p q a : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    [hnormalC : (C.subgroupOf U).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hqpos : 0 < q)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (ρBase : (U ⧸ C.subgroupOf U) →* MulAut (H ⟨0, hqpos⟩)) : Prop :=
  ∃ Clam : Type u, ∃ instGroupClam : Group Clam,
    ∃ instFintypeClam : Fintype Clam, ∃ instDecidableEqClam : DecidableEq Clam,
    letI : Group Clam := instGroupClam
    letI : Fintype Clam := instFintypeClam
    letI : DecidableEq Clam := instDecidableEqClam
    letI : Finite Clam := Finite.of_fintype Clam
    IsMulCommutative Clam ∧
      Fintype.card Clam = Nat.card U / (a * Nat.card Uprime) ∧
      ∃ Lam : Type u, ∃ instFintypeLam : Fintype Lam,
        ∃ instDecidableEqLam : DecidableEq Lam,
        letI : Fintype Lam := instFintypeLam
        letI : DecidableEq Lam := instDecidableEqLam
        ∃ lam : Lam → Clam →* ℂˣ,
          Function.Injective lam ∧
            Fintype.card Lam = Fintype.card Clam ∧
            (∀ j : Lam,
              Section1.IsIrreducibleCharacterOnGroup
                (fun x : Clam => (lam j x : ℂ)) ∧
                Section1.degree (fun x : Clam => (lam j x : ℂ)) = 1) ∧
            ∃ instLamAction : MulAction ρBase.range Lam,
              let ρRange : ρBase.range →* MulAut (H ⟨0, hqpos⟩) :=
                Subgroup.subtype ρBase.range
              let instFirstAction : MulAction ρBase.range (Fin (p - 1)) :=
                nonprincipalLinearCharacterIndexMulAction_sec9 p
                  (hHcard ⟨0, hqpos⟩) ρRange
              letI : MulAction ρBase.range Lam := instLamAction
              letI : MulAction ρBase.range (Fin (p - 1)) := instFirstAction
              ∃ θraw : Fin (p - 1) × Lam →
                  Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M),
                (∀ k : Fin (p - 1) × Lam,
                  Section1.IsIrreducibleCharacterOnGroup (θraw k) ∧
                    ¬ Section1.subgroupInKernel' (θraw k)
                      ((MF.subgroupOf M).subgroupOf
                        ((ambientDerivedSubgroup M).subgroupOf M)) ∧
                    Section1.subgroupInKernel' (θraw k)
                      (((H0 ⊔ Uprime).subgroupOf M).subgroupOf
                        ((ambientDerivedSubgroup M).subgroupOf M)) ∧
                    Section1.degree (θraw k) = (a : ℂ) ∧
                    Section1.IsIrreducibleCharacterOnGroup
                      (Section1.inducedCF ((ambientDerivedSubgroup M).subgroupOf M)
                        (θraw k))) ∧
                  ∀ k l : Fin (p - 1) × Lam,
                    Section1.inducedCF ((ambientDerivedSubgroup M).subgroupOf M)
                        (θraw k) =
                    Section1.inducedCF ((ambientDerivedSubgroup M).subgroupOf M)
                      (θraw l) →
                      MulAction.orbitRel ρBase.range (Fin (p - 1) × Lam) k l

@[expose] public def theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_data_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U H0 C Uprime : Subgroup G)
    (p q a : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    [hnormalC : (C.subgroupOf U).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hqpos : 0 < q)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (ρBase : (U ⧸ C.subgroupOf U) →* MulAut (H ⟨0, hqpos⟩))
    (hUprimeEq : Uprime = (_root_.commutator U).map U.subtype) : Prop :=
  let f : U →* ρBase.range :=
    ρBase.rangeRestrict.comp (QuotientGroup.mk' (C.subgroupOf U))
  let K : Subgroup U := f.ker
  let hUprimeNormal : (Uprime.subgroupOf U).Normal :=
    theorem_9_8_initial_constituent_Mtheta_uprime_subgroupOf_normal_sec9
      U Uprime hUprimeEq
  let Hsub : Subgroup K := (Uprime.subgroupOf U).subgroupOf K
  letI : Hsub.Normal := hUprimeNormal.subgroupOf K
  let Clam : Type u := K ⧸ Hsub
  letI : Group Clam := inferInstance
  letI : Fintype Clam := Fintype.ofFinite Clam
  letI : DecidableEq Clam := Classical.decEq Clam
  ∃ Lam : Type u, ∃ instFintypeLam : Fintype Lam,
    ∃ instDecidableEqLam : DecidableEq Lam,
      letI : Fintype Lam := instFintypeLam
      letI : DecidableEq Lam := instDecidableEqLam
      ∃ lam : Lam → Clam →* ℂˣ,
        Function.Injective lam ∧
          Fintype.card Lam = Fintype.card Clam ∧
          (∀ j : Lam,
            Section1.IsIrreducibleCharacterOnGroup
              (fun x : Clam => (lam j x : ℂ)) ∧
              Section1.degree (fun x : Clam => (lam j x : ℂ)) = 1) ∧
          ∃ instLamAction : MulAction ρBase.range Lam,
            let ρRange : ρBase.range →* MulAut (H ⟨0, hqpos⟩) :=
              Subgroup.subtype ρBase.range
            let instFirstAction : MulAction ρBase.range (Fin (p - 1)) :=
              nonprincipalLinearCharacterIndexMulAction_sec9 p
                (hHcard ⟨0, hqpos⟩) ρRange
            letI : MulAction ρBase.range Lam := instLamAction
            letI : MulAction ρBase.range (Fin (p - 1)) := instFirstAction
            ∃ θraw : Fin (p - 1) × Lam →
                Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M),
              (∀ k : Fin (p - 1) × Lam,
                Section1.IsIrreducibleCharacterOnGroup (θraw k) ∧
                  ¬ Section1.subgroupInKernel' (θraw k)
                    ((MF.subgroupOf M).subgroupOf
                      ((ambientDerivedSubgroup M).subgroupOf M)) ∧
                  Section1.subgroupInKernel' (θraw k)
                    (((H0 ⊔ Uprime).subgroupOf M).subgroupOf
                      ((ambientDerivedSubgroup M).subgroupOf M)) ∧
                  Section1.degree (θraw k) = (a : ℂ) ∧
                  Section1.IsIrreducibleCharacterOnGroup
                    (Section1.inducedCF ((ambientDerivedSubgroup M).subgroupOf M)
                      (θraw k))) ∧
                ∀ k l : Fin (p - 1) × Lam,
                  Section1.inducedCF ((ambientDerivedSubgroup M).subgroupOf M)
                      (θraw k) =
                    Section1.inducedCF ((ambientDerivedSubgroup M).subgroupOf M)
                      (θraw l) →
                    MulAction.orbitRel ρBase.range (Fin (p - 1) × Lam) k l

public theorem
    theorem_9_8_initial_constituent_Mtheta_clam_index_action_data_of_clam_kernel_quotient_theta_data_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U H0 C Uprime : Subgroup G)
    (p q a : ℕ) [NeZero a]
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    [hnormalC : (C.subgroupOf U).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hqpos : 0 < q)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (ρBase : (U ⧸ C.subgroupOf U) →* MulAut (H ⟨0, hqpos⟩))
    (hρcycBase : IsCyclic ρBase.range)
    (hρcardBase : Nat.card ρBase.range = a)
    (hUprimeEq : Uprime = (_root_.commutator U).map U.subtype) :
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_data_sec9
      M MF U H0 C Uprime p q a H hqpos hHcard ρBase hUprimeEq →
        theorem_9_8_initial_constituent_Mtheta_clam_index_action_data_sec9
          M MF U H0 C Uprime p q a H hqpos hHcard ρBase := by
  intro hkernel
  classical
  dsimp [theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_data_sec9]
    at hkernel
  let f : U →* ρBase.range :=
    ρBase.rangeRestrict.comp (QuotientGroup.mk' (C.subgroupOf U))
  let K : Subgroup U := f.ker
  let hUprimeNormal : (Uprime.subgroupOf U).Normal :=
    theorem_9_8_initial_constituent_Mtheta_uprime_subgroupOf_normal_sec9
      U Uprime hUprimeEq
  let Hsub : Subgroup K := (Uprime.subgroupOf U).subgroupOf K
  letI : Hsub.Normal := hUprimeNormal.subgroupOf K
  let Clam : Type u := K ⧸ Hsub
  letI : Group Clam := inferInstance
  letI : Fintype Clam := Fintype.ofFinite Clam
  letI : DecidableEq Clam := Classical.decEq Clam
  rcases hkernel with
    ⟨Lam, instFintypeLam, instDecidableEqLam, lam, hlaminj, hLamClamcard,
      hlamdata, instLamAction, θraw, hθrawdata, hθraworbit⟩
  let instGroupClam : Group Clam := inferInstance
  let instFintypeClam : Fintype Clam := inferInstance
  let instDecidableEqClam : DecidableEq Clam := inferInstance
  have hClamComm : IsMulCommutative Clam := by
    simpa [Clam, Hsub, K, f] using
      theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_comm_sec9
        U C Uprime ρBase hUprimeEq
  have hClamcard : Fintype.card Clam = Nat.card U / (a * Nat.card Uprime) := by
    rw [← Nat.card_eq_fintype_card]
    simpa [Clam, Hsub, K, f] using
      theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_card_sec9
        U C Uprime a ρBase hρcycBase hρcardBase hUprimeEq
  exact ⟨Clam, instGroupClam, instFintypeClam, instDecidableEqClam,
    hClamComm, hClamcard, Lam, instFintypeLam, instDecidableEqLam, lam,
    hlaminj, hLamClamcard, hlamdata, instLamAction, θraw, hθrawdata,
    hθraworbit⟩

public theorem
    theorem_9_8_initial_constituent_Mtheta_clam_raw_theta_data_of_clam_index_action_data_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U H0 C Uprime : Subgroup G)
    (p q a : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    [hnormalC : (C.subgroupOf U).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hqpos : 0 < q)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (ρBase : (U ⧸ C.subgroupOf U) →* MulAut (H ⟨0, hqpos⟩))
    (hp : Nat.Prime p) :
    theorem_9_8_initial_constituent_Mtheta_clam_index_action_data_sec9
      M MF U H0 C Uprime p q a H hqpos hHcard ρBase →
        theorem_9_8_initial_constituent_Mtheta_clam_raw_theta_data_sec9
          M MF U H0 C Uprime p q a H hqpos ρBase := by
  intro hindex
  classical
  rcases hindex with
    ⟨Clam, instGroupClam, instFintypeClam, instDecidableEqClam,
      hClamComm, hClamcard, Lam, instFintypeLam, instDecidableEqLam,
      lam, hlaminj, hLamClamcard, hlamdata, instLamAction, θraw,
      hθrawdata, hθraworbit⟩
  letI : Group Clam := instGroupClam
  letI : Fintype Clam := instFintypeClam
  letI : DecidableEq Clam := instDecidableEqClam
  letI : Fintype Lam := instFintypeLam
  letI : DecidableEq Lam := instDecidableEqLam
  let ρRange : ρBase.range →* MulAut (H ⟨0, hqpos⟩) :=
    Subgroup.subtype ρBase.range
  let instFirstAction : MulAction ρBase.range (Fin (p - 1)) :=
    nonprincipalLinearCharacterIndexMulAction_sec9 p
      (hHcard ⟨0, hqpos⟩) ρRange
  letI : MulAction ρBase.range Lam := instLamAction
  letI : MulAction ρBase.range (Fin (p - 1)) := instFirstAction
  let instPairAction : MulAction ρBase.range (Fin (p - 1) × Lam) := inferInstance
  refine ⟨Clam, instGroupClam, instFintypeClam, instDecidableEqClam,
    hClamComm, hClamcard, Lam, instFintypeLam, instDecidableEqLam, lam,
    hlaminj, hLamClamcard, hlamdata, instPairAction, ?_, θraw, ?_, ?_⟩
  · letI : MulAction ρBase.range (Fin (p - 1) × Lam) := instPairAction
    intro k
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_bot]
      rw [MulAction.mem_stabilizer_iff] at hx
      have hfirst : x • k.1 = k.1 := by
        exact congrArg Prod.fst hx
      let e := nonprincipalLinearCharacterEquivFin_sec9
        (H ⟨0, hqpos⟩) p (hHcard ⟨0, hqpos⟩)
      have hcharfixed :
          nonprincipalLinearCharacterDualEquiv_sec9 (ρRange x) (e k.1) =
            e k.1 := by
        apply Subtype.ext
        have hspec :=
          nonprincipalLinearCharacterIndexMulAction_spec_sec9
            p (hHcard ⟨0, hqpos⟩) ρRange x k.1
        have hleft : (e (x • k.1)).1 = (e k.1).1 := by
          exact congrArg Subtype.val (congrArg e hfirst)
        exact hspec.symm.trans hleft
      have hxval : (x : MulAut (H ⟨0, hqpos⟩)) = 1 :=
        mulAut_eq_one_of_nonprincipalLinearCharacterDualEquiv_eq_self_sec9
          (hHcard ⟨0, hqpos⟩) hp (ρRange x) (e k.1) hcharfixed
      exact Subtype.ext hxval
    · intro hx
      rw [Subgroup.mem_bot] at hx
      rw [MulAction.mem_stabilizer_iff]
      simp [hx]
  · intro k
    simpa [instPairAction] using hθrawdata k
  · intro k l
    simpa [instPairAction] using hθraworbit k l

public theorem
    theorem_9_8_initial_constituent_Mtheta_clam_parameter_data_of_clam_raw_theta_data_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U H0 C Uprime : Subgroup G)
    (p q a : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hnormalC : (C.subgroupOf U).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hqpos : 0 < q)
    (ρBase : (U ⧸ C.subgroupOf U) →* MulAut (H ⟨0, hqpos⟩)) :
    theorem_9_8_initial_constituent_Mtheta_clam_raw_theta_data_sec9
      M MF U H0 C Uprime p q a H hqpos ρBase →
        theorem_9_8_initial_constituent_Mtheta_clam_parameter_data_sec9
          M MF U H0 C Uprime p q a H hqpos ρBase := by
  intro hraw
  classical
  rcases hraw with
    ⟨Clam, instGroupClam, instFintypeClam, instDecidableEqClam,
      hClamComm, hClamcard, Lam, instFintypeLam, instDecidableEqLam,
      lam, hlaminj, hLamClamcard, hlamdata, instAction, hfree, θraw,
      hθrawdata, hθraworbit⟩
  letI : Group Clam := instGroupClam
  letI : Fintype Clam := instFintypeClam
  letI : DecidableEq Clam := instDecidableEqClam
  letI : Fintype Lam := instFintypeLam
  letI : DecidableEq Lam := instDecidableEqLam
  letI : MulAction ρBase.range (Fin (p - 1) × Lam) := instAction
  let κ : Type u := Fin (p - 1) × Lam
  let θ : Quotient (MulAction.orbitRel ρBase.range κ) →
      Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M) :=
    fun i => θraw i.out
  refine ⟨Clam, instGroupClam, instFintypeClam, instDecidableEqClam,
    hClamComm, hClamcard, Lam, instFintypeLam, instDecidableEqLam, lam,
    hlaminj, hLamClamcard, hlamdata, instAction, hfree, θ, ?_, ?_⟩
  · intro i j hij
    have hrel :
        MulAction.orbitRel ρBase.range κ i.out j.out := by
      exact hθraworbit i.out j.out hij
    calc
      i = Quotient.mk (MulAction.orbitRel ρBase.range κ) i.out :=
        (Quotient.out_eq i).symm
      _ = Quotient.mk (MulAction.orbitRel ρBase.range κ) j.out :=
        Quotient.sound hrel
      _ = j := Quotient.out_eq j
  · intro i
    simpa [θ, κ] using hθrawdata i.out

public theorem
    theorem_9_8_initial_constituent_Mtheta_base_range_action_data_of_clam_parameter_data_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U H0 C Uprime : Subgroup G)
    (p q a : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hnormalC : (C.subgroupOf U).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hqpos : 0 < q)
    (ρBase : (U ⧸ C.subgroupOf U) →* MulAut (H ⟨0, hqpos⟩)) :
    theorem_9_8_initial_constituent_Mtheta_clam_parameter_data_sec9
      M MF U H0 C Uprime p q a H hqpos ρBase →
        theorem_9_8_initial_constituent_Mtheta_base_range_action_data_sec9
          M MF U H0 C Uprime p q a H hqpos ρBase := by
  intro hclam
  classical
  rcases hclam with
    ⟨Clam, instGroupClam, instFintypeClam, instDecidableEqClam,
      _hClamComm, hClamcard, Lam, instFintypeLam, instDecidableEqLam,
      _lam, _hlaminj, hLamClamcard, _hlamdata, instAction, hfree, θ, hθinj,
      hθdata⟩
  letI : Group Clam := instGroupClam
  letI : Fintype Clam := instFintypeClam
  letI : DecidableEq Clam := instDecidableEqClam
  letI : Fintype Lam := instFintypeLam
  letI : DecidableEq Lam := instDecidableEqLam
  refine ⟨Lam, instFintypeLam, instDecidableEqLam, ?_, instAction, hfree, θ,
    hθinj, hθdata⟩
  exact hLamClamcard.trans hClamcard

public theorem theorem_9_8_initial_constituent_Mtheta_abstract_cyclic_action_data_of_base_range_action_data_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U H0 C Uprime : Subgroup G)
    (p q a : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hnormalC : (C.subgroupOf U).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hqpos : 0 < q)
    (ρBase : (U ⧸ C.subgroupOf U) →* MulAut (H ⟨0, hqpos⟩))
    (hρcycBase : IsCyclic ρBase.range)
    (hρcardBase : Nat.card ρBase.range = a) :
    theorem_9_8_initial_constituent_Mtheta_base_range_action_data_sec9
      M MF U H0 C Uprime p q a H hqpos ρBase →
        theorem_9_8_initial_constituent_Mtheta_abstract_cyclic_action_data_sec9
          M MF U H0 Uprime p a := by
  intro hrange
  classical
  rcases hrange with
    ⟨Lam, instFintypeLam, instDecidableEqLam, hLamcard, instAction, hfree,
      θ, hθinj, hθdata⟩
  let A : Type u := ρBase.range
  let instGroupA : Group A := inferInstance
  let instFintypeA : Fintype A := Fintype.ofFinite A
  exact ⟨Lam, instFintypeLam, instDecidableEqLam, hLamcard,
    A, instGroupA, instFintypeA, by simpa [A] using hρcycBase,
    by simpa [A] using hρcardBase, instAction, hfree, θ, hθinj, hθdata⟩

@[expose]
public def
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_tail_data_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U H0 C Uprime : Subgroup G)
    (p q a : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    [hnormalC : (C.subgroupOf U).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hqpos : 0 < q)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (ρBase : (U ⧸ C.subgroupOf U) →* MulAut (H ⟨0, hqpos⟩))
    (hρcycBase : IsCyclic ρBase.range)
    (hUprimeEq : Uprime = (_root_.commutator U).map U.subtype) : Prop := by
  classical
  let f : U →* ρBase.range :=
    ρBase.rangeRestrict.comp (QuotientGroup.mk' (C.subgroupOf U))
  let K : Subgroup U := f.ker
  let hUprimeNormal : (Uprime.subgroupOf U).Normal :=
    theorem_9_8_initial_constituent_Mtheta_uprime_subgroupOf_normal_sec9
      U Uprime hUprimeEq
  let Hsub : Subgroup K := (Uprime.subgroupOf U).subgroupOf K
  letI : Hsub.Normal := hUprimeNormal.subgroupOf K
  let Clam : Type u := K ⧸ Hsub
  letI : Group Clam := inferInstance
  let hClamComm : IsMulCommutative Clam :=
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_comm_sec9
      U C Uprime ρBase hUprimeEq
  let Lam : Type u := Clam →* ℂˣ
  have hf_surj : Function.Surjective f := by
    intro y
    rcases y with ⟨y, hy⟩
    rcases hy with ⟨x, rfl⟩
    rcases QuotientGroup.mk'_surjective (C.subgroupOf U) x with ⟨u, rfl⟩
    exact ⟨u, rfl⟩
  haveI : IsCyclic ρBase.range := hρcycBase
  haveI : IsMulCommutative ρBase.range := IsCyclic.isMulCommutative
  let σ : ρBase.range →* MulAut Clam :=
    mulAutHomInvOfCommDomain_sec9
      (kernelQuotientConjHomOfSurjective_sec9 f (Uprime.subgroupOf U) (by
        simpa [Clam, Hsub, K, f] using hClamComm) hf_surj)
  let instLamAction : MulAction ρBase.range Lam :=
    linearCharacterMulAction_sec9 σ
  let ρRange : ρBase.range →* MulAut (H ⟨0, hqpos⟩) :=
    Subgroup.subtype ρBase.range
  let instFirstAction : MulAction ρBase.range (Fin (p - 1)) :=
    nonprincipalLinearCharacterIndexMulAction_sec9 p
      (hHcard ⟨0, hqpos⟩) ρRange
  letI : MulAction ρBase.range Lam := instLamAction
  letI : MulAction ρBase.range (Fin (p - 1)) := instFirstAction
  exact
    ∃ θraw : Fin (p - 1) × Lam →
        Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M),
      (∀ k : Fin (p - 1) × Lam,
        Section1.IsIrreducibleCharacterOnGroup (θraw k) ∧
          ¬ Section1.subgroupInKernel' (θraw k)
            ((MF.subgroupOf M).subgroupOf
              ((ambientDerivedSubgroup M).subgroupOf M)) ∧
          Section1.subgroupInKernel' (θraw k)
            (((H0 ⊔ Uprime).subgroupOf M).subgroupOf
              ((ambientDerivedSubgroup M).subgroupOf M)) ∧
          Section1.degree (θraw k) = (a : ℂ) ∧
          Section1.IsIrreducibleCharacterOnGroup
            (Section1.inducedCF ((ambientDerivedSubgroup M).subgroupOf M)
              (θraw k))) ∧
                ∀ k l : Fin (p - 1) × Lam,
                  Section1.inducedCF ((ambientDerivedSubgroup M).subgroupOf M)
                      (θraw k) =
                    Section1.inducedCF ((ambientDerivedSubgroup M).subgroupOf M)
                      (θraw l) →
                    MulAction.orbitRel ρBase.range (Fin (p - 1) × Lam) k l

@[expose]
public def
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_semidirect_data_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U H0 C Uprime : Subgroup G)
    (p q a : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    [hnormalC : (C.subgroupOf U).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hqpos : 0 < q)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (ρBase : (U ⧸ C.subgroupOf U) →* MulAut (H ⟨0, hqpos⟩))
    (hρcycBase : IsCyclic ρBase.range)
    (hUprimeEq : Uprime = (_root_.commutator U).map U.subtype) : Prop := by
  classical
  let f : U →* ρBase.range :=
    ρBase.rangeRestrict.comp (QuotientGroup.mk' (C.subgroupOf U))
  let K : Subgroup U := f.ker
  let hUprimeNormal : (Uprime.subgroupOf U).Normal :=
    theorem_9_8_initial_constituent_Mtheta_uprime_subgroupOf_normal_sec9
      U Uprime hUprimeEq
  let Hsub : Subgroup K := (Uprime.subgroupOf U).subgroupOf K
  letI : Hsub.Normal := hUprimeNormal.subgroupOf K
  let Clam : Type u := K ⧸ Hsub
  letI : Group Clam := inferInstance
  let hClamComm : IsMulCommutative Clam :=
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_comm_sec9
      U C Uprime ρBase hUprimeEq
  let Lam : Type u := Clam →* ℂˣ
  have hf_surj : Function.Surjective f := by
    intro y
    rcases y with ⟨y, hy⟩
    rcases hy with ⟨x, rfl⟩
    rcases QuotientGroup.mk'_surjective (C.subgroupOf U) x with ⟨u, rfl⟩
    exact ⟨u, rfl⟩
  haveI : IsCyclic ρBase.range := hρcycBase
  haveI : IsMulCommutative ρBase.range := IsCyclic.isMulCommutative
  let σ : ρBase.range →* MulAut Clam :=
    mulAutHomInvOfCommDomain_sec9
      (kernelQuotientConjHomOfSurjective_sec9 f (Uprime.subgroupOf U) (by
        simpa [Clam, Hsub, K, f] using hClamComm) hf_surj)
  let instLamAction : MulAction ρBase.range Lam :=
    linearCharacterMulAction_sec9 σ
  let ρRange : ρBase.range →* MulAut (H ⟨0, hqpos⟩) :=
    Subgroup.subtype ρBase.range
  let instFirstAction : MulAction ρBase.range (Fin (p - 1)) :=
    nonprincipalLinearCharacterIndexMulAction_sec9 p
      (hHcard ⟨0, hqpos⟩) ρRange
  letI : MulAction ρBase.range Lam := instLamAction
  letI : MulAction ρBase.range (Fin (p - 1)) := instFirstAction
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let A : Subgroup Dm := (((H0 ⊔ Uprime).subgroupOf M).subgroupOf Dm)
  let MFD : Subgroup Dm := ((MF.subgroupOf M).subgroupOf Dm)
  exact
    ∃ B : Subgroup Dm,
      ∃ hBnormal : B.Normal,
      ∃ hAnormal : A.Normal,
      A ≤ B ∧
        Subgroup.index B = a ∧
        letI : B.Normal := hBnormal
        letI : A.Normal := hAnormal
        ∃ ψraw : Fin (p - 1) × Lam → Section1.ClassFunction B,
          (∀ k : Fin (p - 1) × Lam,
            Section1.IsIrreducibleCharacterOnGroup (ψraw k) ∧
              Section1.inertiaSubgroup B (ψraw k) = B ∧
              Section1.subgroupInKernel' (ψraw k) (A.subgroupOf B) ∧
              Section1.degree (ψraw k) = 1) ∧
            (∀ k : Fin (p - 1) × Lam,
              ¬ Section1.subgroupInKernel'
                (Section1.inducedCF B (ψraw k)) MFD) ∧
            (∀ k : Fin (p - 1) × Lam,
              Section1.IsIrreducibleCharacterOnGroup
                (Section1.inducedCF Dm (Section1.inducedCF B (ψraw k)))) ∧
            ∀ k l : Fin (p - 1) × Lam,
              Section1.inducedCF Dm (Section1.inducedCF B (ψraw k)) =
                Section1.inducedCF Dm (Section1.inducedCF B (ψraw l)) →
              MulAction.orbitRel ρBase.range (Fin (p - 1) × Lam) k l

@[expose]
public def
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_quotient_linear_data_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U H0 C Uprime : Subgroup G)
    (p q a : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    [hnormalC : (C.subgroupOf U).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hqpos : 0 < q)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (ρBase : (U ⧸ C.subgroupOf U) →* MulAut (H ⟨0, hqpos⟩))
    (hρcycBase : IsCyclic ρBase.range)
    (hUprimeEq : Uprime = (_root_.commutator U).map U.subtype) : Prop := by
  classical
  let f : U →* ρBase.range :=
    ρBase.rangeRestrict.comp (QuotientGroup.mk' (C.subgroupOf U))
  let K : Subgroup U := f.ker
  let hUprimeNormal : (Uprime.subgroupOf U).Normal :=
    theorem_9_8_initial_constituent_Mtheta_uprime_subgroupOf_normal_sec9
      U Uprime hUprimeEq
  let Hsub : Subgroup K := (Uprime.subgroupOf U).subgroupOf K
  letI : Hsub.Normal := hUprimeNormal.subgroupOf K
  let Clam : Type u := K ⧸ Hsub
  letI : Group Clam := inferInstance
  let hClamComm : IsMulCommutative Clam :=
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_comm_sec9
      U C Uprime ρBase hUprimeEq
  let Lam : Type u := Clam →* ℂˣ
  have hf_surj : Function.Surjective f := by
    intro y
    rcases y with ⟨y, hy⟩
    rcases hy with ⟨x, rfl⟩
    rcases QuotientGroup.mk'_surjective (C.subgroupOf U) x with ⟨u, rfl⟩
    exact ⟨u, rfl⟩
  haveI : IsCyclic ρBase.range := hρcycBase
  haveI : IsMulCommutative ρBase.range := IsCyclic.isMulCommutative
  let σ : ρBase.range →* MulAut Clam :=
    mulAutHomInvOfCommDomain_sec9
      (kernelQuotientConjHomOfSurjective_sec9 f (Uprime.subgroupOf U) (by
        simpa [Clam, Hsub, K, f] using hClamComm) hf_surj)
  let instLamAction : MulAction ρBase.range Lam :=
    linearCharacterMulAction_sec9 σ
  let ρRange : ρBase.range →* MulAut (H ⟨0, hqpos⟩) :=
    Subgroup.subtype ρBase.range
  let instFirstAction : MulAction ρBase.range (Fin (p - 1)) :=
    nonprincipalLinearCharacterIndexMulAction_sec9 p
      (hHcard ⟨0, hqpos⟩) ρRange
  letI : MulAction ρBase.range Lam := instLamAction
  letI : MulAction ρBase.range (Fin (p - 1)) := instFirstAction
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let A : Subgroup Dm := (((H0 ⊔ Uprime).subgroupOf M).subgroupOf Dm)
  let MFD : Subgroup Dm := ((MF.subgroupOf M).subgroupOf Dm)
  exact
    ∃ B : Subgroup Dm,
      ∃ hBnormal : B.Normal,
      ∃ hAnormal : A.Normal,
      A ≤ B ∧
        Subgroup.index B = a ∧
        letI : B.Normal := hBnormal
        letI : A.Normal := hAnormal
        letI : (A.subgroupOf B).Normal := hAnormal.subgroupOf B
        ∃ ψlin : Fin (p - 1) × Lam → (B ⧸ A.subgroupOf B) →* ℂˣ,
          (∀ k : Fin (p - 1) × Lam,
            Section1.inertiaSubgroup B
              (Section1.quotientCharacterInflation A B (ψlin k)) = B) ∧
            (∀ k : Fin (p - 1) × Lam,
              ¬ Section1.subgroupInKernel'
                (Section1.inducedCF B
                  (Section1.quotientCharacterInflation A B (ψlin k))) MFD) ∧
            (∀ k : Fin (p - 1) × Lam,
              Section1.IsIrreducibleCharacterOnGroup
                (Section1.inducedCF Dm
                  (Section1.inducedCF B
                    (Section1.quotientCharacterInflation A B (ψlin k))))) ∧
            ∀ k l : Fin (p - 1) × Lam,
              Section1.inducedCF Dm
                  (Section1.inducedCF B
                    (Section1.quotientCharacterInflation A B (ψlin k))) =
                Section1.inducedCF Dm
                  (Section1.inducedCF B
                    (Section1.quotientCharacterInflation A B (ψlin l))) →
              MulAction.orbitRel ρBase.range (Fin (p - 1) × Lam) k l

@[expose] public def theorem_9_8_MFDSubgroupOf_to_MF_sec9
    {G : Type u} [Group G] (M MF : Subgroup G) :
    ((MF.subgroupOf M).subgroupOf ((ambientDerivedSubgroup M).subgroupOf M)) →* MF where
  toFun x :=
    ⟨(((x : (ambientDerivedSubgroup M).subgroupOf M) : M) : G), by
      change ((x : (ambientDerivedSubgroup M).subgroupOf M) : M) ∈ MF.subgroupOf M
      exact x.property⟩
  map_one' := by
    ext
    rfl
  map_mul' := by
    intro x y
    ext
    rfl

@[expose]
public def
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_semidirect_product_structure_data_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U H0 C Uprime : Subgroup G)
    (p q a : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [_hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    [hnormalC : (C.subgroupOf U).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hqpos : 0 < q)
    (_hHcard : ∀ i, Nat.card (H i) = p)
    (ρBase : (U ⧸ C.subgroupOf U) →* MulAut (H ⟨0, hqpos⟩))
    (_hρcycBase : IsCyclic ρBase.range)
    (hUprimeEq : Uprime = (_root_.commutator U).map U.subtype) : Prop := by
  classical
  let f : U →* ρBase.range :=
    ρBase.rangeRestrict.comp (QuotientGroup.mk' (C.subgroupOf U))
  let K : Subgroup U := f.ker
  let hUprimeNormal : (Uprime.subgroupOf U).Normal :=
    theorem_9_8_initial_constituent_Mtheta_uprime_subgroupOf_normal_sec9
      U Uprime hUprimeEq
  let Hsub : Subgroup K := (Uprime.subgroupOf U).subgroupOf K
  letI : Hsub.Normal := hUprimeNormal.subgroupOf K
  let Clam : Type u := K ⧸ Hsub
  letI : Group Clam := inferInstance
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let A : Subgroup Dm := (((H0 ⊔ Uprime).subgroupOf M).subgroupOf Dm)
  let MFD : Subgroup Dm := ((MF.subgroupOf M).subgroupOf Dm)
  let W : Subgroup Dm := ((U.subgroupOf M).subgroupOf Dm)
  exact
    ∃ B : Subgroup Dm,
      ∃ hBnormal : B.Normal,
      ∃ hAnormal : A.Normal,
      A ≤ B ∧
        Subgroup.index B = a ∧
        MFD ≤ B ∧
        ∃ hBsemi : Section2.IsInternalSemidirectProduct B MFD (W ⊓ B),
        ∃ eWBK : ↥(W ⊓ B) ≃* K,
          (∀ x : ↥(W ⊓ B),
            (((eWBK x : K) : U) : G) = ((((x : Dm) : M) : G))) ∧
        letI : B.Normal := hBnormal
        letI : A.Normal := hAnormal
        letI : (A.subgroupOf B).Normal := hAnormal.subgroupOf B
        let Q : Type u := B ⧸ A.subgroupOf B
        letI : Group Q := inferInstance
        let MFDsubB : Subgroup B := MFD.subgroupOf B
        ∃ QMF : Subgroup Q,
        ∃ QH1c : Subgroup Q,
        ∃ QH1 : Subgroup Q,
        ∃ QClam : Subgroup Q,
        ∃ QH1CH1 : Subgroup Q,
        ∃ hsemi : Section2.IsInternalSemidirectProduct
            (⊤ : Subgroup Q) QH1c QH1CH1,
        ∃ hprod : Section2.IsInternalDirectProduct QH1CH1 QH1 QClam,
        ∃ eH1 : QH1 ≃* H ⟨0, hqpos⟩,
        ∃ eClam : QClam ≃* Clam,
          (∀ m : MFDsubB,
            ∀ hmH1 :
              QuotientGroup.mk' (H0.subgroupOf MF)
                  (theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF
                    ((Subgroup.subgroupOfEquivOfLe hBsemi.left_le) m)) ∈
                H ⟨0, hqpos⟩,
              ∃ hmQH1 : QuotientGroup.mk' (A.subgroupOf B) m ∈ QH1,
                eH1
                    ⟨QuotientGroup.mk' (A.subgroupOf B) m, hmQH1⟩ =
                  ⟨QuotientGroup.mk' (H0.subgroupOf MF)
                      (theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF
                        ((Subgroup.subgroupOfEquivOfLe hBsemi.left_le) m)),
                    hmH1⟩) ∧
          (∀ m : MFDsubB,
            QuotientGroup.mk' (H0.subgroupOf MF)
                (theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF
                  ((Subgroup.subgroupOfEquivOfLe hBsemi.left_le) m)) ∈
              (⨆ i, ⨆ _ : i ≠ ⟨0, hqpos⟩, H i) →
            QuotientGroup.mk' (A.subgroupOf B) m ∈ QH1c) ∧
          (∀ w : (W ⊓ B).subgroupOf B,
            ∃ hwQClam : QuotientGroup.mk' (A.subgroupOf B) w ∈ QClam,
              eClam
                  ⟨QuotientGroup.mk' (A.subgroupOf B) w, hwQClam⟩ =
                QuotientGroup.mk' Hsub
                    (eWBK
                      (⟨((w : B) : Dm), by
                        simpa [W, Subgroup.mem_subgroupOf] using w.property⟩ :
                        ↥(W ⊓ B)))) ∧
          QMF =
              ((MFD.subgroupOf B).map (QuotientGroup.mk' (A.subgroupOf B))) ∧
          Section2.IsInternalDirectProduct QMF QH1c QH1 ∧
            QH1 ≤ QMF

@[expose]
public def
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_semidirect_product_formula_data_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U H0 C Uprime : Subgroup G)
    (p q a : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    [hnormalC : (C.subgroupOf U).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hqpos : 0 < q)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (ρBase : (U ⧸ C.subgroupOf U) →* MulAut (H ⟨0, hqpos⟩))
    (hρcycBase : IsCyclic ρBase.range)
    (hUprimeEq : Uprime = (_root_.commutator U).map U.subtype) : Prop := by
  classical
  let f : U →* ρBase.range :=
    ρBase.rangeRestrict.comp (QuotientGroup.mk' (C.subgroupOf U))
  let K : Subgroup U := f.ker
  let hUprimeNormal : (Uprime.subgroupOf U).Normal :=
    theorem_9_8_initial_constituent_Mtheta_uprime_subgroupOf_normal_sec9
      U Uprime hUprimeEq
  let Hsub : Subgroup K := (Uprime.subgroupOf U).subgroupOf K
  letI : Hsub.Normal := hUprimeNormal.subgroupOf K
  let Clam : Type u := K ⧸ Hsub
  letI : Group Clam := inferInstance
  let hClamComm : IsMulCommutative Clam :=
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_comm_sec9
      U C Uprime ρBase hUprimeEq
  let Lam : Type u := Clam →* ℂˣ
  have hf_surj : Function.Surjective f := by
    intro y
    rcases y with ⟨y, hy⟩
    rcases hy with ⟨x, rfl⟩
    rcases QuotientGroup.mk'_surjective (C.subgroupOf U) x with ⟨u, rfl⟩
    exact ⟨u, rfl⟩
  haveI : IsCyclic ρBase.range := hρcycBase
  haveI : IsMulCommutative ρBase.range := IsCyclic.isMulCommutative
  let σ : ρBase.range →* MulAut Clam :=
    mulAutHomInvOfCommDomain_sec9
      (kernelQuotientConjHomOfSurjective_sec9 f (Uprime.subgroupOf U) (by
        simpa [Clam, Hsub, K, f] using hClamComm) hf_surj)
  let instLamAction : MulAction ρBase.range Lam :=
    linearCharacterMulAction_sec9 σ
  let ρRange : ρBase.range →* MulAut (H ⟨0, hqpos⟩) :=
    Subgroup.subtype ρBase.range
  let instFirstAction : MulAction ρBase.range (Fin (p - 1)) :=
    nonprincipalLinearCharacterIndexMulAction_sec9 p
      (hHcard ⟨0, hqpos⟩) ρRange
  letI : MulAction ρBase.range Lam := instLamAction
  letI : MulAction ρBase.range (Fin (p - 1)) := instFirstAction
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let A : Subgroup Dm := (((H0 ⊔ Uprime).subgroupOf M).subgroupOf Dm)
  let MFD : Subgroup Dm := ((MF.subgroupOf M).subgroupOf Dm)
  exact
    ∃ B : Subgroup Dm,
      ∃ hBnormal : B.Normal,
      ∃ hAnormal : A.Normal,
      A ≤ B ∧
        Subgroup.index B = a ∧
        letI : B.Normal := hBnormal
        letI : A.Normal := hAnormal
        letI : (A.subgroupOf B).Normal := hAnormal.subgroupOf B
        let Q : Type u := B ⧸ A.subgroupOf B
        letI : Group Q := inferInstance
        ∃ QH1c : Subgroup Q,
        ∃ QH1 : Subgroup Q,
        ∃ QClam : Subgroup Q,
        ∃ QH1CH1 : Subgroup Q,
        ∃ hsemi : Section2.IsInternalSemidirectProduct
            (⊤ : Subgroup Q) QH1c QH1CH1,
        ∃ hprod : Section2.IsInternalDirectProduct QH1CH1 QH1 QClam,
        ∃ eH1 : QH1 ≃* H ⟨0, hqpos⟩,
        ∃ eClam : QClam ≃* Clam,
          let ψlin : Fin (p - 1) × Lam → Q →* ℂˣ := fun k =>
            semidirectProductOfInternalDirectProductLinearCharacter_sec9
              hsemi hprod
              (((nonprincipalLinearCharacterEquivFin_sec9
                    (H ⟨0, hqpos⟩) p (hHcard ⟨0, hqpos⟩)) k.1).1.comp
                eH1.toMonoidHom)
              (k.2.comp eClam.toMonoidHom)
          (∀ k : Fin (p - 1) × Lam,
            Section1.inertiaSubgroup B
              (Section1.quotientCharacterInflation A B (ψlin k)) = B) ∧
            (∀ k : Fin (p - 1) × Lam,
              ¬ Section1.subgroupInKernel'
                (Section1.inducedCF B
                  (Section1.quotientCharacterInflation A B (ψlin k))) MFD) ∧
            (∀ k : Fin (p - 1) × Lam,
              Section1.IsIrreducibleCharacterOnGroup
                (Section1.inducedCF Dm
                  (Section1.inducedCF B
                    (Section1.quotientCharacterInflation A B (ψlin k))))) ∧
            ∀ k l : Fin (p - 1) × Lam,
              Section1.inducedCF Dm
                  (Section1.inducedCF B
                    (Section1.quotientCharacterInflation A B (ψlin k))) =
                Section1.inducedCF Dm
                  (Section1.inducedCF B
                    (Section1.quotientCharacterInflation A B (ψlin l))) →
              MulAction.orbitRel ρBase.range (Fin (p - 1) × Lam) k l

public theorem
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_quotient_linear_data_of_semidirect_product_formula_data_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U H0 C Uprime : Subgroup G)
    (p q a : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    [hnormalC : (C.subgroupOf U).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hqpos : 0 < q)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (ρBase : (U ⧸ C.subgroupOf U) →* MulAut (H ⟨0, hqpos⟩))
    (hρcycBase : IsCyclic ρBase.range)
    (hUprimeEq : Uprime = (_root_.commutator U).map U.subtype) :
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_semidirect_product_formula_data_sec9
      M MF U H0 C Uprime p q a H hqpos hHcard ρBase hρcycBase hUprimeEq →
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_quotient_linear_data_sec9
      M MF U H0 C Uprime p q a H hqpos hHcard ρBase hρcycBase hUprimeEq := by
  intro hformula
  classical
  dsimp [theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_semidirect_product_formula_data_sec9]
    at hformula
  dsimp [theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_quotient_linear_data_sec9]
  let f : U →* ρBase.range :=
    ρBase.rangeRestrict.comp (QuotientGroup.mk' (C.subgroupOf U))
  let K : Subgroup U := f.ker
  let hUprimeNormal : (Uprime.subgroupOf U).Normal :=
    theorem_9_8_initial_constituent_Mtheta_uprime_subgroupOf_normal_sec9
      U Uprime hUprimeEq
  let Hsub : Subgroup K := (Uprime.subgroupOf U).subgroupOf K
  letI : Hsub.Normal := hUprimeNormal.subgroupOf K
  let Clam : Type u := K ⧸ Hsub
  letI : Group Clam := inferInstance
  let hClamComm : IsMulCommutative Clam :=
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_comm_sec9
      U C Uprime ρBase hUprimeEq
  let Lam : Type u := Clam →* ℂˣ
  have hf_surj : Function.Surjective f := by
    intro y
    rcases y with ⟨y, hy⟩
    rcases hy with ⟨x, rfl⟩
    rcases QuotientGroup.mk'_surjective (C.subgroupOf U) x with ⟨u, rfl⟩
    exact ⟨u, rfl⟩
  haveI : IsCyclic ρBase.range := hρcycBase
  haveI : IsMulCommutative ρBase.range := IsCyclic.isMulCommutative
  let σ : ρBase.range →* MulAut Clam :=
    mulAutHomInvOfCommDomain_sec9
      (kernelQuotientConjHomOfSurjective_sec9 f (Uprime.subgroupOf U) (by
        simpa [Clam, Hsub, K, f] using hClamComm) hf_surj)
  let instLamAction : MulAction ρBase.range Lam :=
    linearCharacterMulAction_sec9 σ
  let ρRange : ρBase.range →* MulAut (H ⟨0, hqpos⟩) :=
    Subgroup.subtype ρBase.range
  let instFirstAction : MulAction ρBase.range (Fin (p - 1)) :=
    nonprincipalLinearCharacterIndexMulAction_sec9 p
      (hHcard ⟨0, hqpos⟩) ρRange
  letI : MulAction ρBase.range Lam := instLamAction
  letI : MulAction ρBase.range (Fin (p - 1)) := instFirstAction
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let A : Subgroup Dm := (((H0 ⊔ Uprime).subgroupOf M).subgroupOf Dm)
  let MFD : Subgroup Dm := ((MF.subgroupOf M).subgroupOf Dm)
  rcases hformula with
    ⟨B, hBnormal, hAnormal, hA_le_B, hBindex, QH1c, QH1, QClam,
      QH1CH1, hsemi, hprod, eH1, eClam, hIeq, hθnotMF, hθfinalIrr,
      hθorbit⟩
  letI : B.Normal := hBnormal
  letI : A.Normal := hAnormal
  letI : (A.subgroupOf B).Normal := hAnormal.subgroupOf B
  let Q : Type u := B ⧸ A.subgroupOf B
  letI : Group Q := inferInstance
  let ψlin : Fin (p - 1) × Lam → Q →* ℂˣ := fun k =>
    semidirectProductOfInternalDirectProductLinearCharacter_sec9
      hsemi hprod
      (((nonprincipalLinearCharacterEquivFin_sec9
            (H ⟨0, hqpos⟩) p (hHcard ⟨0, hqpos⟩)) k.1).1.comp
        eH1.toMonoidHom)
      (k.2.comp eClam.toMonoidHom)
  refine ⟨B, hBnormal, hAnormal, hA_le_B, hBindex, ψlin, ?_, ?_, ?_, ?_⟩
  · exact hIeq
  · exact hθnotMF
  · exact hθfinalIrr
  · exact hθorbit

public theorem
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_semidirect_data_of_quotient_linear_data_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U H0 C Uprime : Subgroup G)
    (p q a : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    [hnormalC : (C.subgroupOf U).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hqpos : 0 < q)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (ρBase : (U ⧸ C.subgroupOf U) →* MulAut (H ⟨0, hqpos⟩))
    (hρcycBase : IsCyclic ρBase.range)
    (hUprimeEq : Uprime = (_root_.commutator U).map U.subtype) :
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_quotient_linear_data_sec9
      M MF U H0 C Uprime p q a H hqpos hHcard ρBase hρcycBase hUprimeEq →
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_semidirect_data_sec9
      M MF U H0 C Uprime p q a H hqpos hHcard ρBase hρcycBase hUprimeEq := by
  intro hquotData
  classical
  dsimp [theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_quotient_linear_data_sec9]
    at hquotData
  dsimp [theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_semidirect_data_sec9]
  let f : U →* ρBase.range :=
    ρBase.rangeRestrict.comp (QuotientGroup.mk' (C.subgroupOf U))
  let K : Subgroup U := f.ker
  let hUprimeNormal : (Uprime.subgroupOf U).Normal :=
    theorem_9_8_initial_constituent_Mtheta_uprime_subgroupOf_normal_sec9
      U Uprime hUprimeEq
  let Hsub : Subgroup K := (Uprime.subgroupOf U).subgroupOf K
  letI : Hsub.Normal := hUprimeNormal.subgroupOf K
  let Clam : Type u := K ⧸ Hsub
  letI : Group Clam := inferInstance
  let hClamComm : IsMulCommutative Clam :=
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_comm_sec9
      U C Uprime ρBase hUprimeEq
  let Lam : Type u := Clam →* ℂˣ
  have hf_surj : Function.Surjective f := by
    intro y
    rcases y with ⟨y, hy⟩
    rcases hy with ⟨x, rfl⟩
    rcases QuotientGroup.mk'_surjective (C.subgroupOf U) x with ⟨u, rfl⟩
    exact ⟨u, rfl⟩
  haveI : IsCyclic ρBase.range := hρcycBase
  haveI : IsMulCommutative ρBase.range := IsCyclic.isMulCommutative
  let σ : ρBase.range →* MulAut Clam :=
    mulAutHomInvOfCommDomain_sec9
      (kernelQuotientConjHomOfSurjective_sec9 f (Uprime.subgroupOf U) (by
        simpa [Clam, Hsub, K, f] using hClamComm) hf_surj)
  let instLamAction : MulAction ρBase.range Lam :=
    linearCharacterMulAction_sec9 σ
  let ρRange : ρBase.range →* MulAut (H ⟨0, hqpos⟩) :=
    Subgroup.subtype ρBase.range
  let instFirstAction : MulAction ρBase.range (Fin (p - 1)) :=
    nonprincipalLinearCharacterIndexMulAction_sec9 p
      (hHcard ⟨0, hqpos⟩) ρRange
  letI : MulAction ρBase.range Lam := instLamAction
  letI : MulAction ρBase.range (Fin (p - 1)) := instFirstAction
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let A : Subgroup Dm := (((H0 ⊔ Uprime).subgroupOf M).subgroupOf Dm)
  let MFD : Subgroup Dm := ((MF.subgroupOf M).subgroupOf Dm)
  rcases hquotData with
    ⟨B, hBnormal, hAnormal, hA_le_B, hBindex, ψlin, hIeq,
      hθnotMF, hθfinalIrr, hθorbit⟩
  letI : B.Normal := hBnormal
  letI : A.Normal := hAnormal
  letI : (A.subgroupOf B).Normal := hAnormal.subgroupOf B
  refine
    ⟨B, hBnormal, hAnormal, hA_le_B, hBindex,
      (fun k => Section1.quotientCharacterInflation A B (ψlin k)), ?_, ?_, ?_, ?_⟩
  · intro k
    exact
      ⟨Section1.quotientCharacterInflation_isIrreducibleCharacterOnGroup
          A B (ψlin k),
        hIeq k,
        Section1.subgroupInKernel'_quotientCharacterInflation A B (ψlin k),
        Section1.quotientCharacterInflation_degree A B (ψlin k)⟩
  · intro k
    exact hθnotMF k
  · intro k
    exact hθfinalIrr k
  · intro k l
    exact hθorbit k l

public theorem
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_tail_data_of_semidirect_data_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U H0 C Uprime : Subgroup G)
    (p q a : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    [hnormalC : (C.subgroupOf U).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hqpos : 0 < q)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (ρBase : (U ⧸ C.subgroupOf U) →* MulAut (H ⟨0, hqpos⟩))
    (hρcycBase : IsCyclic ρBase.range)
    (hUprimeEq : Uprime = (_root_.commutator U).map U.subtype) :
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_semidirect_data_sec9
      M MF U H0 C Uprime p q a H hqpos hHcard ρBase hρcycBase hUprimeEq →
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_tail_data_sec9
      M MF U H0 C Uprime p q a H hqpos hHcard ρBase hρcycBase hUprimeEq := by
  intro hsemiData
  classical
  dsimp [theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_semidirect_data_sec9]
    at hsemiData
  dsimp [theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_tail_data_sec9]
  let f : U →* ρBase.range :=
    ρBase.rangeRestrict.comp (QuotientGroup.mk' (C.subgroupOf U))
  let K : Subgroup U := f.ker
  let hUprimeNormal : (Uprime.subgroupOf U).Normal :=
    theorem_9_8_initial_constituent_Mtheta_uprime_subgroupOf_normal_sec9
      U Uprime hUprimeEq
  let Hsub : Subgroup K := (Uprime.subgroupOf U).subgroupOf K
  letI : Hsub.Normal := hUprimeNormal.subgroupOf K
  let Clam : Type u := K ⧸ Hsub
  letI : Group Clam := inferInstance
  let hClamComm : IsMulCommutative Clam :=
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_comm_sec9
      U C Uprime ρBase hUprimeEq
  let Lam : Type u := Clam →* ℂˣ
  have hf_surj : Function.Surjective f := by
    intro y
    rcases y with ⟨y, hy⟩
    rcases hy with ⟨x, rfl⟩
    rcases QuotientGroup.mk'_surjective (C.subgroupOf U) x with ⟨u, rfl⟩
    exact ⟨u, rfl⟩
  haveI : IsCyclic ρBase.range := hρcycBase
  haveI : IsMulCommutative ρBase.range := IsCyclic.isMulCommutative
  let σ : ρBase.range →* MulAut Clam :=
    mulAutHomInvOfCommDomain_sec9
      (kernelQuotientConjHomOfSurjective_sec9 f (Uprime.subgroupOf U) (by
        simpa [Clam, Hsub, K, f] using hClamComm) hf_surj)
  let instLamAction : MulAction ρBase.range Lam :=
    linearCharacterMulAction_sec9 σ
  let ρRange : ρBase.range →* MulAut (H ⟨0, hqpos⟩) :=
    Subgroup.subtype ρBase.range
  let instFirstAction : MulAction ρBase.range (Fin (p - 1)) :=
    nonprincipalLinearCharacterIndexMulAction_sec9 p
      (hHcard ⟨0, hqpos⟩) ρRange
  letI : MulAction ρBase.range Lam := instLamAction
  letI : MulAction ρBase.range (Fin (p - 1)) := instFirstAction
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let A : Subgroup Dm := (((H0 ⊔ Uprime).subgroupOf M).subgroupOf Dm)
  let MFD : Subgroup Dm := ((MF.subgroupOf M).subgroupOf Dm)
  rcases hsemiData with
    ⟨B, hBnormal, hAnormal, hA_le_B, hBindex, ψraw, hψdata,
      hθnotMF, hθfinalIrr, hθorbit⟩
  letI : B.Normal := hBnormal
  letI : A.Normal := hAnormal
  refine ⟨fun k => Section1.inducedCF B (ψraw k), ?_, ?_⟩
  · intro k
    rcases hψdata k with ⟨hψirr, hIeq, hψker, hψdegree⟩
    have hθirr :
        Section1.IsIrreducibleCharacterOnGroup
          (Section1.inducedCF B (ψraw k)) :=
      inducedCF_isIrreducible_of_inertia_eq_self_sec9 B hψirr hIeq
    have hθker :
        Section1.subgroupInKernel' (Section1.inducedCF B (ψraw k)) A :=
      subgroupInKernel'_inducedCF_of_subgroupInKernel'_sec9
        B A hA_le_B hψirr hψker
    have hθdegree :
        Section1.degree (Section1.inducedCF B (ψraw k)) = (a : ℂ) := by
      rw [Section1.degree_inducedClassFunction, hψdegree, hBindex]
      simp
    exact ⟨hθirr, hθnotMF k, hθker, hθdegree, hθfinalIrr k⟩
  · intro k l
    exact hθorbit k l

@[expose]
public def
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_right_factor_quotient_bridge_data_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U H0 C Uprime : Subgroup G)
    (q : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hnormalC : (C.subgroupOf U).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hqpos : 0 < q)
    (ρBase : (U ⧸ C.subgroupOf U) →* MulAut (H ⟨0, hqpos⟩))
    (hUprimeEq : Uprime = (_root_.commutator U).map U.subtype)
    (B : Subgroup ((ambientDerivedSubgroup M).subgroupOf M))
    (eWBK :
      let W : Subgroup ((ambientDerivedSubgroup M).subgroupOf M) :=
        (U.subgroupOf M).subgroupOf ((ambientDerivedSubgroup M).subgroupOf M)
      let f : U →* ρBase.range :=
        ρBase.rangeRestrict.comp (QuotientGroup.mk' (C.subgroupOf U))
      let K : Subgroup U := f.ker
      ↥(W ⊓ B) ≃* K) : Prop := by
  classical
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let W : Subgroup Dm := (U.subgroupOf M).subgroupOf Dm
  let f : U →* ρBase.range :=
    ρBase.rangeRestrict.comp (QuotientGroup.mk' (C.subgroupOf U))
  let K : Subgroup U := f.ker
  let hUprimeNormal : (Uprime.subgroupOf U).Normal :=
    theorem_9_8_initial_constituent_Mtheta_uprime_subgroupOf_normal_sec9
      U Uprime hUprimeEq
  let Hsub : Subgroup K := (Uprime.subgroupOf U).subgroupOf K
  letI : Hsub.Normal := hUprimeNormal.subgroupOf K
  let UprimeD : Subgroup Dm := (Uprime.subgroupOf M).subgroupOf Dm
  let WBUprime : Subgroup ↥(W ⊓ B) := UprimeD.subgroupOf (W ⊓ B)
  let e : ↥(W ⊓ B) ≃* K := eWBK
  let WBHsub : Subgroup ↥(W ⊓ B) := Hsub.comap e.toMonoidHom
  letI : WBHsub.Normal := (hUprimeNormal.subgroupOf K).comap e.toMonoidHom
  exact ∃ eWBHsub : (↥(W ⊓ B) ⧸ WBHsub) ≃* (K ⧸ Hsub),
    WBUprime = WBHsub ∧
      ∀ x : ↥(W ⊓ B),
        eWBHsub (QuotientGroup.mk' WBHsub x) =
          QuotientGroup.mk' Hsub (e x)

public theorem theorem_9_8_mem_right_of_mem_sup_inf_and_left_inf_eq_bot_sec9
    {L : Type u} [Group L]
    (H U W B MFD : Subgroup L)
    [H.Normal]
    (hH_le_MFD : H ≤ MFD)
    (hU_le_W : U ≤ W)
    (hU_le_B : U ≤ B)
    (hdisj : MFD ⊓ (W ⊓ B) = ⊥) :
    ∀ x : ↥(W ⊓ B), (x : L) ∈ H ⊔ U → (x : L) ∈ U := by
  intro x hx
  rcases (Subgroup.mem_sup_of_normal_left (s := H) (t := U) (x := (x : L))).1 hx with
    ⟨h, hh, u, hu, hhu⟩
  have huW : u ∈ W := hU_le_W hu
  have huB : u ∈ B := hU_le_B hu
  have hhB : h ∈ B := by
    have hxB : (x : L) ∈ B := x.property.2
    have hh_eq : h = (x : L) * u⁻¹ := by
      rw [← hhu]
      simp
    rw [hh_eq]
    exact B.mul_mem hxB (B.inv_mem huB)
  have hhWB : h ∈ W ⊓ B := by
    constructor
    · have hxW : (x : L) ∈ W := x.property.1
      have hh_eq : h = (x : L) * u⁻¹ := by
        rw [← hhu]
        simp
      rw [hh_eq]
      exact W.mul_mem hxW (W.inv_mem huW)
    · exact hhB
  have hhbot : h ∈ (⊥ : Subgroup L) := by
    have hhinf : h ∈ MFD ⊓ (W ⊓ B) := ⟨hH_le_MFD hh, hhWB⟩
    simpa [hdisj] using hhinf
  have hh_one : h = 1 := by
    simpa using hhbot
  have hx_eq_u : (x : L) = u := by
    simpa [hh_one] using hhu.symm
  simpa [hx_eq_u] using hu

public theorem theorem_9_8_mem_left_of_mem_sup_and_left_inf_right_eq_bot_sec9
    {L : Type u} [Group L]
    (H U MFD R : Subgroup L)
    [H.Normal]
    (hH_le_MFD : H ≤ MFD)
    (hU_le_R : U ≤ R)
    (hdisj : MFD ⊓ R = ⊥) :
    ∀ x : MFD, (x : L) ∈ H ⊔ U → (x : L) ∈ H := by
  intro x hx
  rcases (Subgroup.mem_sup_of_normal_left (s := H) (t := U) (x := (x : L))).1 hx with
    ⟨h, hh, u, hu, hhu⟩
  have huMFD : u ∈ MFD := by
    have hxMFD : (x : L) ∈ MFD := x.property
    have hu_eq : u = h⁻¹ * (x : L) := by
      rw [← hhu]
      simp
    rw [hu_eq]
    exact MFD.mul_mem (MFD.inv_mem (hH_le_MFD hh)) hxMFD
  have huR : u ∈ R := hU_le_R hu
  have hubot : u ∈ (⊥ : Subgroup L) := by
    have huinf : u ∈ MFD ⊓ R := ⟨huMFD, huR⟩
    simpa [hdisj] using huinf
  have hu_one : u = 1 := by
    simpa using hubot
  have hx_eq_h : (x : L) = h := by
    simpa [hu_one] using hhu.symm
  simpa [hx_eq_h] using hh


end CFSG.Section9
