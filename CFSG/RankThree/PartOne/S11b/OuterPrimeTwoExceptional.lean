module

public import CFSG.RankThree.PartOne.S11b.OuterPrimeTwoGeneral
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenAutomorphisms
import CFSG.LieType.Chevalley.EvenF4AutomorphismNormalForm
import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank
import CFSG.LieType.Chevalley.EvenTrialityAutomorphismNormalForm
import CFSG.LieType.Suzuki.SuzukiOuterCyclic
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogLargeReeModel
import CFSG.LieType.Ree.SmallReeModelSchreier
import CFSG.Sporadic.Schreier.TitsOuterTwo
public import CFSG.LieType.Ree.Duality

public section

namespace CFSG.RankThree.PartOne

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence)
open CFSG.ComponentClassification.UnbalancedCatalog
  (even_G2_exact_automorphism_normal_form large_Ree_model_field_outer_group_and_inner_involutions)
open CFSG.LieType.Ree
  (ReeTag small_Ree_model_Schreier small_Ree_outer_three_kernel_field_complement)

namespace OuterPrimeTwoExceptional

theorem mul_comm_of_isCyclic {A : Type*} [Group A] [IsCyclic A] (a b : A) : a * b = b * a :=
  (IsCyclic.isMulCommutative (α := A)).is_comm.comm a b

theorem ringAut_comm {p n : ℕ} (hp : p.Prime) (K : Type*) [Field K] [Finite K]
    (hK : Nat.card K = p ^ n) (a b : RingAut K) : a * b = b * a := by
  have := (card_ringAut_and_isCyclic hp K hK).2
  exact mul_comm_of_isCyclic a b

theorem outer_comm_of_ker_eq_inner {C A : Type*} [Group C] [Group A] (Θ : MulAut C →* A)
    (hA : ∀ a b : A, a * b = b * a) (hker : Θ.ker = inner C) :
    ∀ x y : Outer C, x * y = y * x := by
  have hle : inner C ≤ Θ.ker := hker.ge
  have hΦker : (QuotientGroup.lift (inner C) Θ hle).ker = ⊥ := by
    rw [QuotientGroup.ker_lift, hker, QuotientGroup.map_mk'_self]
  have hinj : Function.Injective (QuotientGroup.lift (inner C) Θ hle) :=
    (MonoidHom.ker_eq_bot_iff _).mp hΦker
  intro x y
  apply hinj
  rw [map_mul, map_mul]
  exact hA _ _

theorem quotient_ker_comm {G A : Type*} [Group G] [Group A] (Φ : G →* A)
    (hA : ∀ a b : A, a * b = b * a) (x y : G ⧸ Φ.ker) : x * y = y * x := by
  apply QuotientGroup.kerLift_injective Φ
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  simp only [QuotientGroup.kerLift_mk, map_mul]
  exact hA _ _

theorem odd_card_of_pow_three_eq_one {G : Type*} [Group G] [Finite G] (N : Subgroup G)
    (h : ∀ x ∈ N, x ^ 3 = 1) : Odd (Nat.card N) := by
  rw [Nat.odd_iff]
  by_contra h2
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := N) 2 (by omega)
  have h3 : x ^ 3 = 1 := Subtype.ext (by simpa using h x x.2)
  have h4 := orderOf_dvd_of_pow_eq_one h3
  rw [hx] at h4
  omega

theorem outerPrimeTwoTrivial_of_equiv_ker_eq_inner {S C A : Type} [Group S] [Finite S] [Group C]
    [Group A] (e : S ≃* C) (Θ : MulAut C →* A) (hA : ∀ a b : A, a * b = b * a)
    (hker : Θ.ker = inner C) : OuterPrimeTwoTrivial S := by
  have : Finite C := Finite.of_equiv S e.toEquiv
  exact outerPrimeTwoTrivial_of_mulEquiv e
    (outerPrimeTwoTrivial_of_abelian (outer_comm_of_ker_eq_inner Θ hA hker))

theorem outerPrimeTwoTrivial_of_adjoint_E {S : Type} [Group S] [Finite S] {p f : ℕ}
    (hp : p.Prime) {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {r : ℕ} [Fact r.Prime]
    (hr : τ.cartan.det.natAbs ∣ r) (h : UntwistedChevalleyModel S τ (p ^ f)) :
    OuterPrimeTwoTrivial S := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup τ h
  have : Finite (adjointGroup τ K) := Finite.of_equiv S e.toEquiv
  obtain ⟨Φ, -, -, hdvd⟩ := exists_outer_hom_E (K := K) hτ
  have hcomm : ∀ a b : RingAut K × Multiplicative (ZMod (exactE τ)), a * b = b * a :=
    fun a b => Prod.ext (ringAut_comm hp K hK a.1 b.1) (mul_comm a.2 b.2)
  have : IsCyclic Φ.ker := isCyclic_of_card_dvd_prime (hdvd.trans hr)
  exact outerPrimeTwoTrivial_of_mulEquiv e
    (outerPrimeTwoTrivial_of_cyclic_abelian_quotient Φ.ker (quotient_ker_comm Φ hcomm))

end OuterPrimeTwoExceptional

open OuterPrimeTwoExceptional

theorem outerPrimeTwoTrivial_G2 {S : Type} [Group S] [Finite S] {p f : ℕ}
    (h : ChevalleyExceptionalModel S .G2 p f) : OuterPrimeTwoTrivial S := by
  obtain ⟨⟨hp, hf, hadm⟩, hm⟩ := h
  have hm' : UntwistedChevalleyModel S .G2 (p ^ f) := hm
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .G2 hm'
  rcases eq_or_ne p 3 with rfl | hp3
  · have : CharP K ReeTag.G2.prime := finite_field_prime_power_characteristic hp hf hK
    obtain ⟨-, -, ⟨Θ, -, -, hker⟩, -⟩ := G2_three_exact_automorphism_normal_form hf K hK
    exact outerPrimeTwoTrivial_of_equiv_ker_eq_inner e Θ (fun a b => mul_comm a b) hker
  · rcases eq_or_ne p 2 with rfl | hp2
    · have hf2 : 2 ≤ f := by
        by_contra hcon
        have : f = 1 := by omega
        subst this
        exact absurd hadm.2 (by norm_num)
      obtain ⟨-, Θ, -, -, hker, -⟩ := even_G2_exact_automorphism_normal_form hf2 K hK
      exact outerPrimeTwoTrivial_of_equiv_ker_eq_inner e Θ (ringAut_comm hp K hK) hker
    · obtain ⟨-, Θ, -, -, hker, -⟩ := odd_F4_and_nonexceptional_G2_automorphism_normal_form
        hp hp2 hf K hK .G2 (Or.inr ⟨rfl, hp3⟩)
      exact outerPrimeTwoTrivial_of_equiv_ker_eq_inner e Θ (ringAut_comm hp K hK) hker

theorem outerPrimeTwoTrivial_F4 {S : Type} [Group S] [Finite S] {p f : ℕ}
    (h : ChevalleyExceptionalModel S .F4 p f) : OuterPrimeTwoTrivial S := by
  obtain ⟨⟨hp, hf, -⟩, hm⟩ := h
  have hm' : UntwistedChevalleyModel S .F4 (p ^ f) := hm
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .F4 hm'
  rcases eq_or_ne p 2 with rfl | hp2
  · have : CharP K ReeTag.F4.prime := finite_field_prime_power_characteristic hp hf hK
    obtain ⟨-, -, ⟨Θ, -, -, hker⟩, -⟩ := even_F4_exact_automorphism_normal_form hf K hK
    exact outerPrimeTwoTrivial_of_equiv_ker_eq_inner e Θ (fun a b => mul_comm a b) hker
  · obtain ⟨-, Θ, -, -, hker, -⟩ := odd_F4_and_nonexceptional_G2_automorphism_normal_form
      hp hp2 hf K hK .F4 (Or.inl rfl)
    exact outerPrimeTwoTrivial_of_equiv_ker_eq_inner e Θ (ringAut_comm hp K hK) hker

theorem outerPrimeTwoTrivial_E6 {S : Type} [Group S] [Finite S] {p f : ℕ}
    (h : ChevalleyExceptionalModel S .E6 p f) : OuterPrimeTwoTrivial S := by
  obtain ⟨⟨hp, -, -⟩, hm⟩ := h
  exact outerPrimeTwoTrivial_of_adjoint_E hp (τ := .E6) (Or.inl rfl) (r := 3)
    (by rw [det_cartan_E6]; decide) hm

theorem outerPrimeTwoTrivial_E7 {S : Type} [Group S] [Finite S] {p f : ℕ}
    (h : ChevalleyExceptionalModel S .E7 p f) : OuterPrimeTwoTrivial S := by
  obtain ⟨⟨hp, -, -⟩, hm⟩ := h
  exact outerPrimeTwoTrivial_of_adjoint_E hp (τ := .E7) (Or.inr (Or.inl rfl)) (r := 2)
    (by rw [det_cartan_E7]; decide) hm

theorem outerPrimeTwoTrivial_E8 {S : Type} [Group S] [Finite S] {p f : ℕ}
    (h : ChevalleyExceptionalModel S .E8 p f) : OuterPrimeTwoTrivial S := by
  obtain ⟨⟨hp, -, -⟩, hm⟩ := h
  exact outerPrimeTwoTrivial_of_adjoint_E hp (τ := .E8) (Or.inr (Or.inr rfl)) (r := 2)
    (by rw [det_cartan_E8]; decide) hm

theorem outerPrimeTwoTrivial_twistedE6 {S : Type} [Group S] [Finite S] {p f : ℕ}
    (h : ChevalleyExceptionalModel S .twistedE6 p f) : OuterPrimeTwoTrivial S := by
  obtain ⟨⟨hp, hf, -⟩, hm⟩ := h
  have hm' : TwistedChevalleyModel S .E6 (p ^ f) := hm
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card .E6 hp hf hm'
  have hK2 : Nat.card K = (p ^ f) ^ 2 := hK
  have hK' : Nat.card K = p ^ (2 * f) := by rw [hK2, ← pow_mul, mul_comm]
  have : Finite (twistedE6RootGroup K σ) := Finite.of_equiv S e.toEquiv
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, -, -, hker, -, hcube, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hp hf K hK2 σ hσ
  have hle : inner (twistedE6RootGroup K σ) ≤ Θ.ker := by
    rw [hker]
    exact le_sup_left
  set Φ := QuotientGroup.lift (inner (twistedE6RootGroup K σ)) Θ hle
  have hcube' : ∀ x ∈ Φ.ker, x ^ 3 = 1 := by
    intro x hx
    rw [QuotientGroup.ker_lift, hker] at hx
    obtain ⟨α, hα, rfl⟩ := hx
    have h3 := hcube (QuotientGroup.mk ⟨α, hα⟩)
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      Subgroup.coe_pow] at h3
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact h3
  have : Finite (MulAut (twistedE6RootGroup K σ)) := MulEquiv.finite_left
  have hodd : Odd (Nat.card Φ.ker) := odd_card_of_pow_three_eq_one Φ.ker hcube'
  exact outerPrimeTwoTrivial_of_mulEquiv e
    (outerPrimeTwoTrivial_of_odd_abelian_quotient Φ.ker hodd
      (quotient_ker_comm Φ (ringAut_comm hp K hK')))

theorem outerPrimeTwoTrivial_trialityD4 {S : Type} [Group S] [Finite S] {p f : ℕ}
    (h : ChevalleyExceptionalModel S .trialityD4 p f) : OuterPrimeTwoTrivial S := by
  obtain ⟨⟨hp, hf, -⟩, hm⟩ := h
  have hm' : TwistedChevalleyModel S .D4 (p ^ f) := hm
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card .D4 hp hf hm'
  rcases eq_or_ne p 2 with rfl | hp2
  · obtain ⟨-, -, ⟨Θ, -, -, hker, -⟩, hcyc, -⟩ :=
      even_triality_exact_automorphism_normal_form hf K hK σ hσ
    exact outerPrimeTwoTrivial_of_equiv_ker_eq_inner e Θ mul_comm_of_isCyclic hker
  · obtain ⟨-, -, ⟨Θ, -, -, hker, -⟩, hcyc, -⟩ :=
      odd_triality_exact_automorphism_normal_form hp hp2 hf K hK σ hσ
    exact outerPrimeTwoTrivial_of_equiv_ker_eq_inner e Θ mul_comm_of_isCyclic hker

theorem outerPrimeTwoTrivial_suzuki {S : Type} [Group S] [Finite S] {p f : ℕ}
    (h : SuzukiModel S p f) : OuterPrimeTwoTrivial S :=
  outerPrimeTwoTrivial_of_odd
    (CFSG.LieType.Suzuki.Suzuki_model_and_perfect_cover_outer_cyclicity.{0} S p f h).1.2.2

theorem outerPrimeTwoTrivial_twistedF4 {S : Type} [Group S] [Finite S] {p f : ℕ}
    (h : ReeTitsModel S .twistedF4 p f) : OuterPrimeTwoTrivial S := by
  obtain ⟨-, -, hodd, -, hcard, -⟩ :=
    large_Ree_model_field_outer_group_and_inner_involutions S p f h
  exact outerPrimeTwoTrivial_of_odd (by rw [hcard]; exact hodd)

theorem outerPrimeTwoTrivial_twistedG2 {S : Type} [Group S] [Finite S] {p f : ℕ}
    (h : ReeTitsModel S .twistedG2 p f) : OuterPrimeTwoTrivial S := by
  obtain ⟨-, -, rfl, ⟨a, ha, hfa⟩, hiso⟩ := small_Ree_model_Schreier S p f h
  obtain ⟨-, a', hfa', K, _, _, hK, hw⟩ := h
  have ha' : a' = a := by omega
  subst ha'
  have : CharP K ReeTag.G2.prime :=
    finite_field_prime_power_characteristic Nat.prime_three (by omega) hK
  obtain ⟨E⟩ := hiso a' K hfa hK hw
  have hK' : Nat.card K = 3 ^ (2 * a' + 1) := by rw [hK, hfa]
  obtain ⟨-, -, -, -, hoddO, -⟩ := small_Ree_outer_three_kernel_field_complement a' ha K hK'
  have hO := Nat.card_congr (equivalence E).toEquiv
  exact outerPrimeTwoTrivial_of_odd (by rw [hO]; exact hoddO)

theorem outerPrimeTwoTrivial_Tits {S : Type} [Group S] [Finite S] {p f : ℕ}
    (h : ReeTitsModel S .Tits p f) : OuterPrimeTwoTrivial S :=
  outerPrimeTwoTrivial_of_card_lt (by
    rw [(CFSG.Sporadic.Schreier.Tits.CTI_Tits_model_outer_two_part_bound S p f h).2.2.1]
    norm_num)

theorem exceptionalOuterPrimeTwoTrivial : ExceptionalOuterPrimeTwoTrivial := by
  intro S _ _ _ _ hexc
  rcases hexc with ⟨t, p, f, ht, hmodel⟩ | ⟨t, p, f, ht, hmodel⟩ | ⟨p, f, hmodel⟩
  · cases t with
    | G2 => exact outerPrimeTwoTrivial_G2 hmodel
    | F4 => exact outerPrimeTwoTrivial_F4 hmodel
    | E6 => exact outerPrimeTwoTrivial_E6 hmodel
    | E7 => exact outerPrimeTwoTrivial_E7 hmodel
    | E8 => exact outerPrimeTwoTrivial_E8 hmodel
    | twistedE6 => exact outerPrimeTwoTrivial_twistedE6 hmodel
    | trialityD4 => exact outerPrimeTwoTrivial_trialityD4 hmodel
    | PSL | PSU | PSp | POmegaOdd | POmegaPlus | POmegaMinus
    | twistedB2 | twistedG2 | twistedF4 | Tits => exact absurd ht (by decide)
  · cases t with
    | twistedG2 => exact outerPrimeTwoTrivial_twistedG2 hmodel
    | twistedF4 => exact outerPrimeTwoTrivial_twistedF4 hmodel
    | Tits => exact outerPrimeTwoTrivial_Tits hmodel
    | PSL | PSU | PSp | POmegaOdd | POmegaPlus | POmegaMinus
    | G2 | F4 | E6 | E7 | E8 | twistedE6 | trialityD4 | twistedB2 => exact absurd ht (by decide)
  · exact outerPrimeTwoTrivial_suzuki hmodel

end CFSG.RankThree.PartOne
