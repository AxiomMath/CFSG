module

public import CFSG.RankThree.PartOne.KC.PlaneLifting
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeModel

public section

namespace CFSG.RankThree.PartOne.KCUnitaryPlane

open CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel

variable {ℓ f n p : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)

@[expose] noncomputable def innerLift (n : ℕ) :
    gramSU h (idGram K n) →* MulAut (primeFormP h (idGram K n)) :=
  (MulAut.conj : primeFormP h (idGram K n) →* MulAut (primeFormP h (idGram K n))).comp
    (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n))

variable {h}

theorem innerLift_apply (x : gramSU h (idGram K n)) :
    innerLift h n x = MulAut.conj (x : primeFormP h (idGram K n)) := rfl

theorem innerLift_eq_iff (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2))
    {x y : gramSU h (idGram K n)} :
    innerLift h n x = innerLift h n y ↔
      (x : primeFormP h (idGram K n)) = (y : primeFormP h (idGram K n)) := by
  rw [innerLift_apply, innerLift_apply]
  exact (KCUnitaryRegular.conj_injective_primeFormP h (isPrimeFormGram_idGram (K := K) (n := n))
    hn hne).eq_iff

theorem eq_of_innerLift_eq (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2))
    (hZp : ∀ c : Kˣ, h.norm (c : K) = 1 → c ^ n = 1 → c ^ p = 1 → c = 1)
    {x y : gramSU h (idGram K n)} (hx : x ^ p = 1) (hy : y ^ p = 1)
    (hxy : innerLift h n x = innerLift h n y) : x = y :=
  eq_of_mk_eq_of_pow_eq_one_of_noTorsion hZp (by omega) hx hy ((innerLift_eq_iff hn hne).mp hxy)

theorem not_dvd_card_ker_innerLift (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2)) (hp : p.Prime)
    (hZp : ∀ c : Kˣ, h.norm (c : K) = 1 → c ^ n = 1 → c ^ p = 1 → c = 1) :
    ¬ p ∣ Nat.card (innerLift h n).ker := by
  intro hdvd
  have : Fact p.Prime := ⟨hp⟩
  have := h.finite
  have : Finite (gramSU h (idGram K n)) := inferInstance
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := (innerLift h n).ker) p hdvd
  have hz1 : (z : gramSU h (idGram K n)) ^ p = 1 := by
    have := pow_orderOf_eq_one z
    rw [hz] at this
    exact congrArg Subtype.val this
  have hz2 : innerLift h n (z : gramSU h (idGram K n)) = innerLift h n 1 := by
    rw [map_one]
    exact z.2
  have hz3 := eq_of_innerLift_eq hn hne hZp hz1 (one_pow p) hz2
  have : z = 1 := Subtype.ext hz3
  rw [this, orderOf_one] at hz
  exact hp.one_lt.ne hz

@[expose] def IsPlaneLift (h : UnitaryFieldData ℓ f K) (n p : ℕ)
    (A : Subgroup (MulAut (primeFormP h (idGram K n))))
    (Ahat : Subgroup (gramSU h (idGram K n))) : Prop :=
  IsElementaryAbelian p Ahat ∧ Nat.card Ahat = p ^ 2 ∧ Ahat.map (innerLift h n) = A ∧
    Set.InjOn (innerLift h n) Ahat


theorem range_innerLift_eq :
    (innerLift h n).range =
      (MulAut.conj : primeFormP h (idGram K n) →* MulAut (primeFormP h (idGram K n))).range := by
  ext a
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(x : primeFormP h (idGram K n)), rfl⟩
  · rintro ⟨t, rfl⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective t
    exact ⟨x, rfl⟩

theorem exists_unique_planeLift (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2)) (hp : p.Prime)
    (hZp : ∀ c : Kˣ, h.norm (c : K) = 1 → c ^ n = 1 → c ^ p = 1 → c = 1)
    (A : Subgroup (MulAut (primeFormP h (idGram K n))))
    (hAinn : A ≤ (MulAut.conj : primeFormP h (idGram K n) →*
      MulAut (primeFormP h (idGram K n))).range)
    (hA : IsElementaryAbelian p A) (hAcard : Nat.card A = p ^ 2) :
    ∃! Ahat : Subgroup (gramSU h (idGram K n)), IsPlaneLift h n p A Ahat := by
  have : Fact p.Prime := ⟨hp⟩
  have := h.finite
  have := hA
  have hrange : A ≤ (innerLift h n).range := by rw [range_innerLift_eq]; exact hAinn
  obtain ⟨E₀, hE₀, hE₀card, hmap⟩ := exists_lift_elementaryAbelian (innerLift h n) hp
    (not_dvd_card_ker_innerLift hn hne hp hZp) A hrange hAcard
  have hpow : ∀ (E : Subgroup (gramSU h (idGram K n))), IsElementaryAbelian p E →
      ∀ x ∈ E, x ^ p = 1 := fun E hE x hx => by
    have := hE
    exact elemPow_eq_one_of_isElementaryAbelian x hx
  have hinj : ∀ (E : Subgroup (gramSU h (idGram K n))), IsElementaryAbelian p E →
      Set.InjOn (innerLift h n) E := fun E hE x hx y hy hxy =>
    eq_of_innerLift_eq hn hne hZp (hpow E hE x hx) (hpow E hE y hy) hxy
  refine ⟨E₀, ⟨hE₀, hE₀card, hmap, hinj E₀ hE₀⟩, ?_⟩
  rintro E₁ ⟨hE₁, -, hmap₁, -⟩
  have hle : ∀ (E E' : Subgroup (gramSU h (idGram K n))), IsElementaryAbelian p E →
      IsElementaryAbelian p E' → E.map (innerLift h n) = E'.map (innerLift h n) → E ≤ E' :=
    fun E E' hE hE' hmm x hx => by
      have : innerLift h n x ∈ E'.map (innerLift h n) := hmm ▸ Subgroup.mem_map_of_mem _ hx
      obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp this
      have := eq_of_innerLift_eq hn hne hZp (hpow E' hE' y hy) (hpow E hE x hx) hxy
      rw [← this]
      exact hy
  have hmm : E₁.map (innerLift h n) = E₀.map (innerLift h n) := by rw [hmap₁, hmap]
  exact le_antisymm (hle E₁ E₀ hE₁ hE₀ hmm) (hle E₀ E₁ hE₀ hE₁ hmm.symm)

theorem planeLift_unique_lift (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2)) (hp : p.Prime)
    (hZp : ∀ c : Kˣ, h.norm (c : K) = 1 → c ^ n = 1 → c ^ p = 1 → c = 1)
    {A : Subgroup (MulAut (primeFormP h (idGram K n)))}
    {Ahat : Subgroup (gramSU h (idGram K n))} (hlift : IsPlaneLift h n p A Ahat) {a : MulAut
      (primeFormP h (idGram K n))} (haA : a ∈ A) (ha1 : a ≠ 1) :
    ∃ x ∈ Ahat, innerLift h n x = a ∧ orderOf x = p ∧
      ∀ y : gramSU h (idGram K n), innerLift h n y = a → y ^ p = 1 → y = x := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hE, -, hmap, -⟩ := hlift
  have : a ∈ Ahat.map (innerLift h n) := hmap ▸ haA
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp this
  have hxp : x ^ p = 1 := by
    have := hE
    exact elemPow_eq_one_of_isElementaryAbelian x hx
  have hx1 : x ≠ 1 := fun h1 => ha1 (by rw [h1, map_one])
  refine ⟨x, hx, rfl, orderOf_eq_prime hxp hx1, fun y hy hyp => ?_⟩
  exact eq_of_innerLift_eq hn hne hZp hyp hxp hy

end CFSG.RankThree.PartOne.KCUnitaryPlane
