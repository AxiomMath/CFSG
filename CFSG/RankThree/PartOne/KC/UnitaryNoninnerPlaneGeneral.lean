module

public import CFSG.RankThree.PartOne.KC.UnitaryFieldActorCore
public import CFSG.RankThree.PartOne.KC.ElementaryPlaneCyclicImage
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeCentralizer

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.RankThree.LocalRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.Classical CFSG.LieType.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open scoped Pointwise

theorem pElement_mem_inner_of_not_dvd_gcd {ℓ f n p : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData ℓ f K) (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2)) (hp : p.Prime)
    (hg : ¬ p ∣ Nat.gcd n (ℓ ^ f + 1)) {d : MulAut (primeFormP h (idGram K n))}
    (hd : d ∈ primeFormD h (idGram K n)) (hdp : d ^ p = 1) : d ∈ innU h n := by
  have := h.finite
  obtain ⟨-, -, hquot, -⟩ := unitary_full_diagonal_outer_order h hn hne
  set Q := primeFormD h (idGram K n) ⧸ (inner (primeFormP h (idGram K n))).subgroupOf
    (primeFormD h (idGram K n)) with hQ
  have h1 : orderOf (QuotientGroup.mk (⟨d, hd⟩ : primeFormD h (idGram K n)) : Q) ∣ p := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← QuotientGroup.mk_pow]
    have : (⟨d, hd⟩ : primeFormD h (idGram K n)) ^ p = 1 := Subtype.ext hdp
    rw [this]
    rfl
  have h2 : orderOf (QuotientGroup.mk (⟨d, hd⟩ : primeFormD h (idGram K n)) : Q) ∣
      Nat.gcd n (ℓ ^ f + 1) := hquot ▸ (_root_.orderOf_dvd_natCard _)
  rcases (Nat.dvd_prime hp).mp h1 with h3 | h3
  · have h4 := orderOf_eq_one_iff.mp h3
    have h5 := (QuotientGroup.eq_one_iff (N := (inner (primeFormP h (idGram K n))).subgroupOf
      (primeFormD h (idGram K n))) _).mp h4
    exact h5
  · exact absurd (h3 ▸ h2) hg

theorem innU_le_primeFormD {ℓ f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K) :
    innU h n ≤ primeFormD h (idGram K n) := by
  rintro _ ⟨y, rfl⟩
  obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective y
  refine ⟨liftUnitary s, ?_⟩
  exact primeFormConjHom_liftUnitary s

@[expose] def UnitaryFixedGroupData {ℓ f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)
    (n p : ℕ) (σ : K ≃+* K) : Prop :=
  (¬(n = 3 ∧ ℓ ^ (f / p) = 2) →
    IsSimpleGroup (fieldFixedPSU h n σ) ∧ (¬∀ x y : fieldFixedPSU h n σ, x * y = y * x) ∧
      fixingSubgroup (MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))
          (fieldFixedPSU h n σ : Set (primeFormP h
            ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) =
        (fixingSubgroup (K ≃+* K) (fixSubfield σ : Set K)).map
          (primeFormFieldHom h (isPrimeFormGram_one (n := n))) ∧
      (fixingSubgroup (K ≃+* K) (fixSubfield σ : Set K)).map
          (primeFormFieldHom h (isPrimeFormGram_one (n := n))) =
        Subgroup.zpowers (primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ) ∧
      Nat.card (Subgroup.zpowers (primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ)) = p) ∧
  (n = 3 ∧ ℓ ^ (f / p) = 2 → ∀ x ∈ fieldFixedPSU h n σ, orderOf x ≠ p)

theorem unitary_noninner_plane_general {ℓ f n p : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData ℓ f K) (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2)) (hp : p.Prime)
    (hp3 : 3 < p) (hpℓ : p ≠ ℓ) (hg : ¬ p ∣ Nat.gcd n (ℓ ^ f + 1))
    (hBT : ∀ σ : K ≃+* K, orderOf σ = p → UnitaryFixedGroupData h n p σ)
    (hcomm : 3 < ℓ ^ f → ∀ B : Subgroup (MulAut (primeFormP h (idGram K n))), innU h n ≤ B →
      ∀ t ∈ innU h n, orderOf t = p →
        ∀ A : Subgroup (MulAut (primeFormP h (idGram K n))),
          A ≤ B ⊓ Subgroup.centralizer ({t} : Set (MulAut (primeFormP h (idGram K n)))) →
          IsPGroup p A →
          Odd (Nat.card ↥⁅inSubgroup (aschbacherSolvableCore p)
            (B ⊓ Subgroup.centralizer ({t} : Set (MulAut (primeFormP h (idGram K n))))), A⁆))
    (B : Subgroup (MulAut (primeFormP h (idGram K n)))) (hB : innU h n ≤ B)
    (A : Subgroup (MulAut (primeFormP h (idGram K n)))) (hAB : A ≤ B)
    (hAel : IsElementaryAbelian p A) (hAcard : Nat.card A = p ^ 2) (hAnot : ¬ A ≤ innU h n) :
    Nat.card (A ⊓ innU h n : Subgroup (MulAut (primeFormP h (idGram K n)))) = p ∧ p ∣ f ∧
      2 ^ p ≤ ℓ ^ f ∧ 3 < ℓ ^ f ∧
      (∀ a ∈ A, a ∉ innU h n →
        inSubgroup (aschbacherSolvableCore p) (B ⊓ Subgroup.centralizer {a}) = ⊥) ∧
      autThetaT p B A = ⊥ ∧
      ∀ t ∈ A, t ≠ 1 →
        PlaneProductIsSubgroup p B A t ∧ ¬ 2 ∣ Nat.card (autPlaneProduct p B A t) ∧
          (t ∉ innU h n → autPlaneProduct p B A t = ⊥) := by
  classical
  have hfin := h.finite
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have : Finite (primeFormP h (idGram K n)) := finite_primeFormP
  have : Finite (MulAut (primeFormP h (idGram K n))) := inferInstance
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  obtain ⟨-, -, -, -, -, -, -, hkerD, -, -, -⟩ :=
    unitary_prime_form_full_semilinear_realization h hC hn hne
  set π := primeFormFieldFactor h hC hn hne with hπdef
  have hApow : ∀ x : A, x ^ p = 1 := fun x => by
    have := hAel
    have h1 : (x : MulAut (primeFormP h (idGram K n))) ^ p = 1 :=
      elemPow_eq_one_of_isElementaryAbelian (x : MulAut (primeFormP h (idGram K n))) x.2
    exact Subtype.ext (by simpa using h1)
  have hApG : IsPGroup p A := fun g => ⟨1, by rw [pow_one]; exact hApow g⟩
  set π' : A →* (K ≃+* K) := π.comp A.subtype with hπ'
  have hD : ∀ a ∈ A, π a = 1 ↔ a ∈ primeFormD h (idGram K n) := fun a _ => by
    rw [← hkerD, MonoidHom.mem_ker]
  have hADH : ∀ a ∈ A, a ∈ primeFormD h (idGram K n) → a ∈ innU h n := fun a haA haD =>
    pElement_mem_inner_of_not_dvd_gcd h hn hne hp hg haD (by
      have := hApow ⟨a, haA⟩
      exact congrArg Subtype.val this)
  have hπne : π' ≠ 1 := by
    intro h1
    apply hAnot
    intro a haA
    have : π a = 1 := by
      have := congrArg (fun φ : A →* (K ≃+* K) => φ ⟨a, haA⟩) h1
      simpa [hπ'] using this
    exact hADH a haA ((hD a haA).mp this)
  have hcyc : IsCyclic (K ≃+* K) := (card_ringAut_and_isCyclic h.prime K h.card).2
  obtain ⟨hker, hrange⟩ := card_ker_eq_prime_of_ne_one hp hApow hAcard π' hπne
  have hAD : A ⊓ innU h n = A ⊓ primeFormD h (idGram K n) :=
    le_antisymm (inf_le_inf_left _ (innU_le_primeFormD h)) (fun a ha => ⟨ha.1, hADH a ha.1 ha.2⟩)
  have hkerA : (π'.ker).map A.subtype = A ⊓ primeFormD h (idGram K n) := by
    ext a
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, (hD x x.2).mp hx⟩
    · rintro ⟨haA, haD⟩
      exact ⟨⟨a, haA⟩, (hD a haA).mpr haD, rfl⟩
  have hcard1 : Nat.card (A ⊓ innU h n : Subgroup (MulAut (primeFormP h (idGram K n)))) = p := by
    rw [hAD, ← hkerA, Subgroup.card_map_of_injective A.subtype_injective]
    exact hker
  have hAutCard : Nat.card (K ≃+* K) = 2 * f := (card_ringAut_and_isCyclic h.prime K h.card).1
  have hpf : p ∣ f := by
    have h1 : p ∣ 2 * f := by
      have := Subgroup.card_subgroup_dvd_card π'.range
      rwa [hrange, hAutCard] at this
    rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h2
    · exact absurd (Nat.le_of_dvd (by norm_num) h2) (by omega)
    · exact h2
  have hfp : p ≤ f := Nat.le_of_dvd (by have := h.one_le; omega) hpf
  have h2p : 2 ^ p ≤ ℓ ^ f :=
    calc 2 ^ p ≤ ℓ ^ p := Nat.pow_le_pow_left h.prime.two_le p
      _ ≤ ℓ ^ f := Nat.pow_le_pow_right h.prime.pos hfp
  have h3q : 3 < ℓ ^ f := by
    have : 2 ^ 4 ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨a₀, ha₀A, ha₀H⟩ := IsConcreteLE.not_le_iff_exists.mp hAnot
  have hnotD : ∀ a ∈ A, a ∉ innU h n → π a ≠ 1 := fun a haA haH h1 =>
    haH (hADH a haA ((hD a haA).mp h1))
  have hordσ : ∀ a ∈ A, π a ≠ 1 → orderOf (π a) = p := fun a haA hne => by
    have h1 : (π a) ^ p = 1 := by
      rw [← map_pow]
      have := hApow ⟨a, haA⟩
      rw [show a ^ p = 1 from congrArg Subtype.val this, map_one]
    exact orderOf_eq_prime h1 hne
  have horda : ∀ a ∈ A, a ≠ 1 → orderOf a = p := fun a haA hne =>
    orderOf_eq_prime (congrArg Subtype.val (hApow ⟨a, haA⟩)) hne
  have hne1 : ∀ a ∈ A, a ∉ innU h n → a ≠ 1 := fun a _ haH h1 => haH (h1 ▸ Subgroup.one_mem _)
  have hcoreA : ∀ a ∈ A, a ∉ innU h n →
      (n = 3 ∧ ℓ ^ (f / p) = 2 → ∀ g ∈ innU h n, a * g = g * a → orderOf g ≠ p) ∧
      (¬(n = 3 ∧ ℓ ^ (f / p) = 2) →
        inSubgroup (aschbacherSolvableCore p) (B ⊓ Subgroup.centralizer {a}) = ⊥) :=
    fun a haA haH =>
      unitary_field_actor_core h hn hne hp hp2 hpℓ (π a)
        (hordσ a haA (hnotD a haA haH))
        (hBT _ (hordσ a haA (hnotD a haA haH))).1 (hBT _ (hordσ a haA (hnotD a haA haH))).2
        B hB (horda a haA (hne1 a haA haH)) rfl
  have hnotexc : ¬(n = 3 ∧ ℓ ^ (f / p) = 2) := by
    intro hex
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥(A ⊓ innU h n)) p
      (by rw [hcard1])
    have hcomm : a₀ * (g : MulAut (primeFormP h (idGram K n))) =
        (g : MulAut (primeFormP h (idGram K n))) * a₀ := by
      have := hAel
      have hh := (IsMulCommutative.is_comm (M := A)).comm ⟨a₀, ha₀A⟩ ⟨g, g.2.1⟩
      exact congrArg Subtype.val hh
    exact (hcoreA a₀ ha₀A ha₀H).1 hex g g.2.2 hcomm (by rw [Subgroup.orderOf_coe]; exact hg)
  have hSa : ∀ a ∈ A, a ∉ innU h n →
      inSubgroup (aschbacherSolvableCore p) (B ⊓ Subgroup.centralizer {a}) = ⊥ :=
    fun a haA haH => (hcoreA a haA haH).2 hnotexc
  have hI : autThetaT p B A = ⊥ := by
    apply le_bot_iff.mp
    calc autThetaT p B A ≤ inSubgroup (aschbacherSolvableCore p)
          (B ⊓ Subgroup.centralizer ({a₀} : Set (MulAut (primeFormP h (idGram K n))))) :=
        (iInf_le _ a₀).trans ((iInf_le _ ha₀A).trans (iInf_le _ (hne1 a₀ ha₀A ha₀H)))
      _ = ⊥ := hSa a₀ ha₀A ha₀H
  refine ⟨hcard1, hpf, h2p, h3q, hSa, hI, fun t htA ht1 => ?_⟩
  have hprod : autPlaneProduct p B A t =
      ⁅inSubgroup (aschbacherSolvableCore p) (B ⊓ Subgroup.centralizer {t}), A⁆ := by
    rw [autPlaneProduct, hI, sup_bot_eq]
  have hset : PlaneProductIsSubgroup p B A t := by
    unfold PlaneProductIsSubgroup
    rw [hI]
    simp
  by_cases htH : t ∈ innU h n
  · have htp : orderOf t = p := horda t htA ht1
    have hAB' : A ≤ B ⊓ Subgroup.centralizer ({t} : Set (MulAut (primeFormP h (idGram K n)))) :=
      fun x hx => ⟨hAB hx, Subgroup.mem_centralizer_singleton_iff.mpr (by
        have := hAel
        have hh := (IsMulCommutative.is_comm (M := A)).comm ⟨t, htA⟩ ⟨x, hx⟩
        exact (congrArg Subtype.val hh).symm)⟩
    have hodd := hcomm h3q B hB t htH htp A hAB' hApG
    refine ⟨hset, ?_, fun hn' => absurd htH hn'⟩
    rw [hprod]
    intro h2
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  · have hS := hSa t htA htH
    have h0 : autPlaneProduct p B A t = ⊥ := by
      rw [hprod, hS, Subgroup.commutator_bot_left]
    refine ⟨hset, ?_, fun _ => h0⟩
    rw [h0, Subgroup.card_bot]
    omega

end CFSG.RankThree.PartOne
