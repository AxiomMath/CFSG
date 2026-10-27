module

public import CFSG.Quasithin.Vol2.KGFactInsp4316Props
public import CFSG.LocalAnalysis.ComponentInitial.QTNQRLinearUnitaryOuterDerived
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveSp4Out
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenAutomorphisms
public import CFSG.LieType.Chevalley.EvenTrialityAutomorphismNormalForm
public import CFSG.LieType.Suzuki.SuzukiOuterCyclic
public import CFSG.Quasithin.Background.A318PF4Frame
public import CFSG.RankThree.PartOne.S11d.OutAbstract

public section

namespace CFSG.Quasithin.H13.KGInsp4316

open CFSG.Open hiding StatedSL StatedSp StatedClassicalModel StatedLieTag
open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence)
open CFSG.LocalAnalysis.ComponentInitial.OuterDerived
  (linear_perfect_cover_outer_derived_diagonal_bound
    unitary_perfect_cover_outer_derived_diagonal_bound)
open CFSG.ComponentClassification.UnbalancedCatalog
  (large_Ree_full_inner_field_automorphism_normal_form even_G2_exact_automorphism_normal_form)
open scoped commutatorElement

section Gen

variable {S : Type} [Group S]

theorem isPerfect_of_simple (hs : IsSimpleGroup S) (hnc : ∃ a b : S, a * b ≠ b * a) :
    Group.IsPerfect S := by
  rw [Group.isPerfect_def]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator S) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    apply hab
    have : ⁅a, b⁆ ∈ commutator S := Subgroup.commutator_mem_commutator (Subgroup.mem_top a)
      (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this
  · exact h

theorem center_eq_bot_of_simple (hs : IsSimpleGroup S) (hnc : ∃ a b : S, a * b ≠ b * a) :
    Subgroup.center S = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)

@[expose] noncomputable def quotCenterEquiv (h : Subgroup.center S = ⊥) :
    S ⧸ Subgroup.center S ≃* S :=
  (QuotientGroup.quotientMulEquivOfEq h).trans QuotientGroup.quotientBot

theorem odd_card_commutator_of_comm {A : Type*} [Group A] (h : ∀ a b : A, a * b = b * a) :
    Odd (Nat.card (commutator A)) := by
  have : commutator A = ⊥ := by
    rw [eq_bot_iff, commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact h a b
  rw [this, Subgroup.card_bot]
  exact odd_one

theorem comm_of_isCyclic {A : Type*} [Group A] (h : IsCyclic A) : ∀ a b : A, a * b = b * a := by
  intro a b
  exact h.commGroup.mul_comm a b

theorem outer_comm_of_hom {C : Type*} [Group C] (hC : ∀ a b : C, a * b = b * a)
    (Θ : MulAut S →* C) (hker : Θ.ker = inner S) : ∀ a b : Outer S, a * b = b * a := by
  intro a b
  induction a using QuotientGroup.induction_on with
  | H α =>
    induction b using QuotientGroup.induction_on with
    | H β =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, hC (Θ α) (Θ β),
        inv_mul_cancel]

theorem outer_comm_of_mulEquiv {T : Type} [Group T] (e : S ≃* T)
    (h : ∀ a b : Outer T, a * b = b * a) : ∀ a b : Outer S, a * b = b * a := by
  intro a b
  apply (equivalence e).injective
  rw [map_mul, map_mul]
  exact h _ _

end Gen

section Families

variable {S : Type} [Group S]

theorem odd_outer_psl3 (hs : IsSimpleGroup S) (hnc : ∃ a b : S, a * b ≠ b * a) {p f : ℕ}
    (hm : StatedClassicalModel S .PSL 3 p f) : Odd (Nat.card (commutator (Outer S))) := by
  have := isPerfect_of_simple hs hnc
  have hm' := CFSG.LieType.CurtisTits.statedClassicalModel_of_mulEquiv
    (quotCenterEquiv (center_eq_bot_of_simple hs hnc)).symm hm
  obtain ⟨-, hdvd, -⟩ :=
    linear_perfect_cover_outer_derived_diagonal_bound
      S 3 p f hm'
  exact (Nat.odd_iff.mpr (by
    have h3 : Nat.gcd 3 (p ^ f - 1) ∣ 3 := Nat.gcd_dvd_left _ _
    have : Nat.card (commutator (Outer S)) ∣ 3 := hdvd.trans h3
    rcases (Nat.dvd_prime Nat.prime_three).mp this with h | h <;> rw [h]))

theorem odd_outer_psu3 (hs : IsSimpleGroup S) (hnc : ∃ a b : S, a * b ≠ b * a) {p f : ℕ}
    (hm : StatedClassicalModel S .PSU 3 p f) : Odd (Nat.card (commutator (Outer S))) := by
  have := isPerfect_of_simple hs hnc
  have hm' := CFSG.LieType.CurtisTits.statedClassicalModel_of_mulEquiv
    (quotCenterEquiv (center_eq_bot_of_simple hs hnc)).symm hm
  obtain ⟨-, hdvd, -⟩ :=
    unitary_perfect_cover_outer_derived_diagonal_bound
      S 3 p f hm'
  exact (Nat.odd_iff.mpr (by
    have h3 : Nat.gcd 3 (p ^ f + 1) ∣ 3 := Nat.gcd_dvd_left _ _
    have : Nat.card (commutator (Outer S)) ∣ 3 := hdvd.trans h3
    rcases (Nat.dvd_prime Nat.prime_three).mp this with h | h <;> rw [h]))

theorem outer_comm_psl2 (hs : IsSimpleGroup S) (hnc : ∃ a b : S, a * b ≠ b * a) {p f : ℕ}
    (hm : StatedClassicalModel S .PSL 2 p f) : ∀ a b : Outer S, a * b = b * a := by
  have := isPerfect_of_simple hs hnc
  have hm' := CFSG.LieType.CurtisTits.statedClassicalModel_of_mulEquiv
    (quotCenterEquiv (center_eq_bot_of_simple hs hnc)).symm hm
  obtain ⟨-, -, -, h2⟩ :=
    linear_perfect_cover_outer_derived_diagonal_bound
      S 2 p f hm'
  exact h2 rfl

theorem outer_cyclic_psp4 {f : ℕ} (hm : StatedClassicalModel S .PSp 2 2 f) :
    IsCyclic (Outer S) := by
  obtain ⟨⟨-, hf, -⟩, K, _, _, hK, ⟨e⟩⟩ := hm
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 2 ^ f := by rw [← Nat.card_eq_fintype_card]; exact hK
  have h := (CFSG.QuasithinUnique.Lin2.sp4OutCyclic K f hcard (by omega)).1
  exact isCyclic_of_surjective (equivalence e).symm.toMonoidHom (equivalence e).symm.surjective

theorem outer_cyclic_sz {f : ℕ} (hm : SuzukiModel S 2 f) :
    IsCyclic (Outer S) :=
  (CFSG.LieType.Suzuki.Suzuki_model_and_perfect_cover_outer_cyclicity.{0} S 2 f hm).1.1

theorem outer_cyclic_2f4
    {f : ℕ} (hm : ReeTitsModel S .twistedF4 2 f) : IsCyclic (Outer S) := by
  obtain ⟨K, _, _, _, a, ha, hK, ⟨e⟩⟩ := CFSG.SectionRank.exists_mulEquiv_reeFixed_of_model hm
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := hK
  obtain ⟨-, -, -, hcyc, -⟩ :=
    large_Ree_full_inner_field_automorphism_normal_form
      a ha K hK'
  let e' := e.trans (CFSG.Quasithin.A318P.reeFixedEquivGamma (K := K) a)
  exact isCyclic_of_surjective (equivalence e').symm.toMonoidHom (equivalence e').symm.surjective

theorem outer_comm_g2
    {f : ℕ} (hf : 2 ≤ f) (hm : ChevalleyExceptionalModel S .G2 2 f) :
    ∀ a b : Outer S, a * b = b * a := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hm
  let ψ : S ≃* ↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 K) :=
    e.trans ((QuotientGroup.quotientMulEquivOfEq
      (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .G2) (K := K))).trans
        QuotientGroup.quotientBot)
  obtain ⟨-, Θ, -, -, hker, -⟩ :=
    even_G2_exact_automorphism_normal_form hf K hK
  exact outer_comm_of_mulEquiv ψ (outer_comm_of_hom
    (CFSG.RankThree.PartOne.OutStructure.ringAut_comm K) Θ hker)

theorem outer_comm_d4
    {f : ℕ} (hf : 1 ≤ f) (hm : ChevalleyExceptionalModel S .trialityD4 2 f) :
    ∀ a b : Outer S, a * b = b * a := by
  obtain ⟨-, K, _, _, hKcard, σ₀, hσ₀, ⟨e⟩⟩ := hm
  have hK : Nat.card K = (2 ^ f) ^ 3 := by rw [hKcard]; rfl
  have hbij : Function.Bijective σ₀ :=
    ⟨σ₀.injective, Finite.surjective_of_injective σ₀.injective⟩
  let σ : K ≃+* K := RingEquiv.ofBijective σ₀ hbij
  have hσ : ∀ c, σ c = c ^ (2 ^ f) := hσ₀
  obtain ⟨-, -, ⟨Θ, -, -, hker, -⟩, -, -, -, -, ⟨iso⟩⟩ :=
    CFSG.LieType.Chevalley.even_triality_exact_automorphism_normal_form hf K hK σ hσ
  exact outer_comm_of_mulEquiv (e.trans iso) (outer_comm_of_hom
    (CFSG.RankThree.PartOne.OutStructure.ringAut_comm K) Θ hker)

end Families

theorem insp4316OutDer_holds :
    Insp4316OutDer := by
  intro S _ _ hs hnc hS
  rcases hS with ⟨⟨p, hp, hp2, hm | hm⟩ | ⟨f, ⟨-, hm⟩ | ⟨-, hm⟩ | ⟨-, hm⟩ | ⟨-, hm⟩ | ⟨hf, hm⟩ |
      ⟨hf, hm⟩ | ⟨-, -, hm⟩ | ⟨-, -, hm⟩⟩⟩ | ⟨s, q, p, e, -, -, -, hm⟩
  · exact odd_outer_psl3 hs hnc hm
  · exact odd_outer_psu3 hs hnc hm
  · exact odd_card_commutator_of_comm (outer_comm_psl2 hs hnc hm)
  · exact odd_outer_psl3 hs hnc hm
  · exact odd_outer_psu3 hs hnc hm
  · exact odd_card_commutator_of_comm (comm_of_isCyclic (outer_cyclic_psp4 hm))
  · exact odd_card_commutator_of_comm (outer_comm_g2 hf hm)
  · exact odd_card_commutator_of_comm (outer_comm_d4 hf hm)
  · exact odd_card_commutator_of_comm (comm_of_isCyclic (outer_cyclic_2f4 hm))
  · exact odd_card_commutator_of_comm (comm_of_isCyclic (outer_cyclic_sz hm))
  · cases s
    · exact odd_outer_psu3 hs hnc hm
    · exact odd_outer_psl3 hs hnc hm

end CFSG.Quasithin.H13.KGInsp4316
