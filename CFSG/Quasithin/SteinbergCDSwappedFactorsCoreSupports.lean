module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.GroupTheory.SolvableHallNodes
public import CFSG.Quasithin.SteinbergCCResidualGeneration
public import CFSG.Quasithin.SteinbergCDCommutingSupportsLinePair

public section

namespace CFSG.Quasithin.SteinbergCD

open Subgroup CFSG.ABGLocalTools
open scoped commutatorElement Pointwise
open CFSG.LocalAnalysis.GorensteinLyons (mem_conjugate_iff_conj_mem
  mem_normalizer_iff_conjugate_eq conjugate_conjugate)

variable {H : Type*} [Group H]

theorem conjugate_inf (A B : Subgroup H) (g : H) :
    conjugate (A ⊓ B) g = conjugate A g ⊓ conjugate B g :=
  Subgroup.map_inf_eq A B _ (MulAut.conj g⁻¹).injective

theorem conjugate_commutator (A B : Subgroup H) (g : H) :
    conjugate ⁅A, B⁆ g = ⁅conjugate A g, conjugate B g⁆ :=
  Subgroup.map_commutator A B _

theorem mem_normalizer_inSubgroup_pCore {X : Subgroup H} (r : ℕ) {g : H}
    (hg : g ∈ normalizer (X : Set H)) : g ∈ normalizer (inSubgroup (pCore r) X : Set H) := by
  have hX : ∀ c ∈ normalizer (X : Set H), ∀ y ∈ inSubgroup (pCore r) X,
      c * y * c⁻¹ ∈ inSubgroup (pCore r) X := by
    intro c hc y hy
    let φ : X ≃* X :=
      { toFun := fun x => ⟨c * x * c⁻¹, (mem_normalizer_iff.mp hc x).mp x.2⟩
        invFun := fun x => ⟨c⁻¹ * x * c, by
          have h := (mem_normalizer_iff.mp (inv_mem hc) x).mp x.2
          simpa using h⟩
        left_inv := fun x => Subtype.ext (by simp [mul_assoc])
        right_inv := fun x => Subtype.ext (by simp [mul_assoc])
        map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }
    obtain ⟨y', hy', rfl⟩ := hy
    have h1 : φ y' ∈ (pCore r X).map φ.toMonoidHom := ⟨y', hy', rfl⟩
    rw [pCore_map_iso r φ] at h1
    exact ⟨φ y', h1, rfl⟩
  rw [mem_normalizer_iff]
  intro y
  refine ⟨hX g hg y, fun h => ?_⟩
  have h1 := hX g⁻¹ (inv_mem hg) _ h
  simpa [mul_assoc] using h1

theorem commuting_swapped_factors_produce_full_core_supports [Finite H] {r p : ℕ}
    (hr : r.Prime) (hp : p.Prime) (hrp : r ≠ p) {K₁ K₂ : Subgroup H} (hK : ⁅K₁, K₂⁆ = ⊥)
    {X : Subgroup H} (hXK : X ≤ K₁ ⊔ K₂) (hQ1 : inSubgroup (pCore r) X ≠ ⊥)
    (hres : ∀ (N : Subgroup X) [N.Normal], IsPGroup r (X ⧸ N) → N = ⊤)
    {P : Subgroup H} (hP : IsSylowOf p P X) (hXQP : inSubgroup (pCore r) X ⊔ P = X)
    (hP₁ : Nat.card (P ⊓ K₁ : Subgroup H) = p) (hP₂ : Nat.card (P ⊓ K₂ : Subgroup H) = p)
    (hPsup : (P ⊓ K₁) ⊔ (P ⊓ K₂) = P)
    {h : H} (hhX : h ∈ normalizer (X : Set H)) (hh₁ : conjugate K₁ h = K₂)
    (hh₂ : conjugate K₂ h = K₁) :
    ⁅inSubgroup (pCore r) X, P ⊓ K₁⁆ ≤ inSubgroup (pCore r) X ⊓ K₁ ∧
      ⁅inSubgroup (pCore r) X, P ⊓ K₂⁆ ≤ inSubgroup (pCore r) X ⊓ K₂ ∧
      P ≤ normalizer ((⁅inSubgroup (pCore r) X, P ⊓ K₁⁆ : Subgroup H) : Set H) ∧
      P ≤ normalizer ((⁅inSubgroup (pCore r) X, P ⊓ K₂⁆ : Subgroup H) : Set H) ∧
      (inSubgroup (pCore r) X : Set H) =
        ((⁅inSubgroup (pCore r) X, P ⊓ K₁⁆ : Subgroup H) : Set H) *
          ((⁅inSubgroup (pCore r) X, P ⊓ K₂⁆ : Subgroup H) : Set H) ∧
      ⁅⁅inSubgroup (pCore r) X, P ⊓ K₁⁆, ⁅inSubgroup (pCore r) X, P ⊓ K₂⁆⁆ = ⊥ ∧
      ⁅⁅inSubgroup (pCore r) X, P ⊓ K₁⁆, P ⊓ K₂⁆ = ⊥ ∧
      ⁅⁅inSubgroup (pCore r) X, P ⊓ K₂⁆, P ⊓ K₁⁆ = ⊥ ∧
      ⁅⁅inSubgroup (pCore r) X, P ⊓ K₁⁆, P ⊓ K₁⁆ ≠ ⊥ ∧
      ⁅⁅inSubgroup (pCore r) X, P ⊓ K₂⁆, P ⊓ K₂⁆ ≠ ⊥ ∧
      ∃ x ∈ X, h * x ∈ normalizer (P : Set H) ∧ conjugate (P ⊓ K₁) (h * x) = P ⊓ K₂ ∧
        conjugate (P ⊓ K₂) (h * x) = P ⊓ K₁ ∧
        conjugate ⁅inSubgroup (pCore r) X, P ⊓ K₁⁆ (h * x) = ⁅inSubgroup (pCore r) X, P ⊓ K₂⁆ ∧
        conjugate ⁅inSubgroup (pCore r) X, P ⊓ K₂⁆ (h * x) =
          ⁅inSubgroup (pCore r) X, P ⊓ K₁⁆ := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact r.Prime := ⟨hr⟩
  set Q := inSubgroup (pCore r) X with hQdef
  set P₁ := P ⊓ K₁ with hP₁def
  set P₂ := P ⊓ K₂ with hP₂def
  set A₁ := ⁅Q, P₁⁆ with hA₁def
  set A₂ := ⁅Q, P₂⁆ with hA₂def
  have hPX : P ≤ X := hP.le
  have hQX : Q ≤ X := map_subtype_le _
  have hQr : IsPGroup r Q := pCore_isPGroup.map X.subtype
  have hpQ : ¬ p ∣ Nat.card Q := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQr
    rw [hk]
    intro h
    exact hrp ((Nat.prime_dvd_prime_iff_eq hp hr).mp (hp.dvd_of_dvd_pow h)).symm
  have hXQ : ∀ g ∈ X, g ∈ normalizer (Q : Set H) := fun g hg =>
    mem_normalizer_inSubgroup_pCore r (le_normalizer hg)
  have hK₁n : K₁ ⊔ K₂ ≤ normalizer (K₁ : Set H) :=
    sup_le le_normalizer ((commutator_eq_bot_iff_le_centralizer.mp
      ((commutator_comm K₂ K₁).trans hK)).trans (centralizer_le_normalizer _))
  have hK₂n : K₁ ⊔ K₂ ≤ normalizer (K₂ : Set H) :=
    sup_le ((commutator_eq_bot_iff_le_centralizer.mp hK).trans (centralizer_le_normalizer _))
      le_normalizer
  have hXK₁ : ∀ g ∈ X, conjugate K₁ g = K₁ := fun g hg =>
    mem_normalizer_iff_conjugate_eq.mp (hK₁n (hXK hg))
  have hXK₂ : ∀ g ∈ X, conjugate K₂ g = K₂ := fun g hg =>
    mem_normalizer_iff_conjugate_eq.mp (hK₂n (hXK hg))
  have hXQc : ∀ g ∈ X, conjugate Q g = Q := fun g hg =>
    mem_normalizer_iff_conjugate_eq.mp (hXQ g hg)
  have hhQ : conjugate Q h = Q :=
    mem_normalizer_iff_conjugate_eq.mp (mem_normalizer_inSubgroup_pCore r hhX)
  have hPPc : ∀ g ∈ P, conjugate P g = P := fun g hg =>
    mem_normalizer_iff_conjugate_eq.mp (le_normalizer hg)
  have hPA₁ : P ≤ normalizer (A₁ : Set H) := fun g hg => by
    rw [mem_normalizer_iff_conjugate_eq, hA₁def, conjugate_commutator, hP₁def, conjugate_inf,
      hXQc g (hPX hg), hPPc g hg, hXK₁ g (hPX hg)]
  have hPA₂ : P ≤ normalizer (A₂ : Set H) := fun g hg => by
    rw [mem_normalizer_iff_conjugate_eq, hA₂def, conjugate_commutator, hP₂def, conjugate_inf,
      hXQc g (hPX hg), hPPc g hg, hXK₂ g (hPX hg)]
  have hcommQ : ∀ (K : Subgroup H), X ≤ normalizer (K : Set H) → ⁅Q, P ⊓ K⁆ ≤ Q ⊓ K := by
    intro K hXKn
    rw [commutator_le]
    intro q hq a ha
    have haP : a ∈ P := (Subgroup.mem_inf.mp ha).1
    have haK : a ∈ K := (Subgroup.mem_inf.mp ha).2
    rw [commutatorElement_def]
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have h1 : a * q⁻¹ * a⁻¹ ∈ Q := (mem_normalizer_iff.mp (hXQ a (hPX haP)) _).mp (inv_mem hq)
      have e : q * a * q⁻¹ * a⁻¹ = q * (a * q⁻¹ * a⁻¹) := by group
      rw [e]
      exact mul_mem hq h1
    · have h1 : q * a * q⁻¹ ∈ K := (mem_normalizer_iff.mp (hXKn (hQX hq)) a).mp haK
      exact mul_mem h1 (inv_mem haK)
  have hA₁le : A₁ ≤ Q ⊓ K₁ := hcommQ K₁ fun g hg => hK₁n (hXK hg)
  have hA₂le : A₂ ≤ Q ⊓ K₂ := hcommQ K₂ fun g hg => hK₂n (hXK hg)
  have hA₁K₁ : A₁ ≤ K₁ := hA₁le.trans inf_le_right
  have hA₂K₂ : A₂ ≤ K₂ := hA₂le.trans inf_le_right
  have hK₂₁ : ⁅K₂, K₁⁆ = ⊥ := (commutator_comm K₂ K₁).trans hK
  have hcA : ⁅A₁, A₂⁆ = ⊥ := le_bot_iff.mp ((commutator_mono hA₁K₁ hA₂K₂).trans hK.le)
  have hcA₁P₂ : ⁅A₁, P₂⁆ = ⊥ :=
    le_bot_iff.mp ((commutator_mono hA₁K₁ inf_le_right).trans hK.le)
  have hcA₂P₁ : ⁅A₂, P₁⁆ = ⊥ :=
    le_bot_iff.mp ((commutator_mono hA₂K₂ inf_le_right).trans hK₂₁.le)
  have hQP : ⁅Q, P⁆ = Q := by
    have hP'map : (P.subgroupOf X).map X.subtype = P := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPX]
    have hsup : pCore r X ⊔ P.subgroupOf X = ⊤ := by
      apply Subgroup.map_injective X.subtype_injective
      rw [Subgroup.map_sup, hP'map, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
      exact hXQP
    have hP'cop : Nat.Coprime (Nat.card (P.subgroupOf X)) r := by
      have hp' : IsPGroup p (P.subgroupOf X) :=
        hP.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hPX).symm
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp'
      rw [hk]
      exact Nat.Coprime.pow_left k ((Nat.coprime_primes hp hr).mpr (Ne.symm hrp))
    have hcomm := (CFSG.Quasithin.SteinbergCC.residual_coprime_complement_normal_generation.{_, 0}
      hr pCore_isPGroup hP'cop hsup hres).2.1
    have h1 := congrArg (Subgroup.map X.subtype) hcomm
    rw [Subgroup.map_commutator, hP'map] at h1
    exact h1
  have hA₁₂ : A₁ ≤ normalizer (A₂ : Set H) :=
    (commutator_eq_bot_iff_le_centralizer.mp hcA).trans (centralizer_le_normalizer _)
  have hsupA : ((A₁ ⊔ A₂ : Subgroup H) : Set H) = (A₁ : Set H) * (A₂ : Set H) :=
    coe_mul_of_left_le_normalizer_right A₁ A₂ hA₁₂
  have hP₁₂ : P₁ ≤ normalizer (P₂ : Set H) :=
    (commutator_eq_bot_iff_le_centralizer.mp
      (le_bot_iff.mp ((commutator_mono inf_le_right inf_le_right).trans hK.le))).trans
        (centralizer_le_normalizer _)
  have hPmul : (P : Set H) = (P₁ : Set H) * (P₂ : Set H) := by
    rw [← hPsup]
    exact coe_mul_of_left_le_normalizer_right P₁ P₂ hP₁₂
  have hQle : Q ≤ A₁ ⊔ A₂ := by
    rw [← hQP, commutator_le]
    intro q hq g hg
    have hg' : g ∈ (P₁ : Set H) * (P₂ : Set H) := hPmul ▸ hg
    obtain ⟨a, ha, b, hb, rfl⟩ := hg'
    have haP : a ∈ P := (Subgroup.mem_inf.mp ha).1
    have e : ⁅q, a * b⁆ = ⁅q, a⁆ * (a * ⁅q, b⁆ * a⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact mul_mem_sup (commutator_mem_commutator hq ha)
      ((mem_normalizer_iff.mp (hPA₂ haP) _).mp (commutator_mem_commutator hq hb))
  have hQeq : (Q : Set H) = (A₁ : Set H) * (A₂ : Set H) := by
    apply Set.Subset.antisymm
    · rw [← hsupA]
      exact hQle
    · rintro _ ⟨u, hu, v, hv, rfl⟩
      exact mul_mem (Subgroup.mem_inf.mp (hA₁le hu)).1 (Subgroup.mem_inf.mp (hA₂le hv)).1
  have hPhX : conjugate P h ≤ X := by
    intro y hy
    rw [mem_conjugate_iff_conj_mem] at hy
    have h1 := (mem_normalizer_iff.mp (inv_mem hhX) _).mp (hPX hy)
    simpa [mul_assoc] using h1
  have hcardc : ∀ (K : Subgroup H) (g : H), Nat.card (conjugate K g) = Nat.card K :=
    fun K g => Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have hPh : IsSylowOf p (conjugate P h) X :=
    isSylowOf_of_card hPhX (by rw [hcardc, hP.card_eq])
  obtain ⟨S, hS⟩ := id hP
  obtain ⟨S', hS'⟩ := hPh
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X S' S
  set x : H := ((g⁻¹ : X) : H) with hxdef
  have hxX : x ∈ X := (g⁻¹).2
  have hconjP : conjugate P (h * x) = P := by
    rw [← conjugate_conjugate]
    symm
    refine Subgroup.eq_of_le_of_card_ge ?_ (by rw [hcardc, hcardc])
    intro y hy
    rw [← hS] at hy
    obtain ⟨s, hsS, rfl⟩ := hy
    rw [← hg, ← CFSG.SolvableHall.map_conj_eq_coe_smul] at hsS
    obtain ⟨s', hs', rfl⟩ := hsS
    rw [mem_conjugate_iff_conj_mem]
    have hs'' : ((s' : X) : H) ∈ conjugate P h := hS' ▸ ⟨s', hs', rfl⟩
    convert hs'' using 1
    simp only [hxdef, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_subtype,
      Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hhx : h * x ∈ normalizer (P : Set H) := mem_normalizer_iff_conjugate_eq.mpr hconjP
  have hK₁hx : conjugate K₁ (h * x) = K₂ := by rw [← conjugate_conjugate, hh₁, hXK₂ x hxX]
  have hK₂hx : conjugate K₂ (h * x) = K₁ := by rw [← conjugate_conjugate, hh₂, hXK₁ x hxX]
  have hQhx : conjugate Q (h * x) = Q := by rw [← conjugate_conjugate, hhQ, hXQc x hxX]
  have hP₁hx : conjugate P₁ (h * x) = P₂ := by rw [hP₁def, conjugate_inf, hconjP, hK₁hx]
  have hP₂hx : conjugate P₂ (h * x) = P₁ := by rw [hP₂def, conjugate_inf, hconjP, hK₂hx]
  have hA₁hx : conjugate A₁ (h * x) = A₂ := by
    rw [hA₁def, conjugate_commutator, hQhx, hP₁hx]
  have hA₂hx : conjugate A₂ (h * x) = A₁ := by
    rw [hA₂def, conjugate_commutator, hQhx, hP₂hx]
  have hA₁ne : A₁ ≠ ⊥ := by
    intro hA
    apply hQ1
    have hA₂ : A₂ = ⊥ := by
      rw [← hA₁hx, hA]
      exact Subgroup.map_bot _
    rw [eq_bot_iff]
    intro y hy
    have hy' : y ∈ (A₁ : Set H) * (A₂ : Set H) := hQeq ▸ hy
    obtain ⟨u, hu, v, hv, huv⟩ := hy'
    have huv : u * v = y := huv
    rw [SetLike.mem_coe, hA, mem_bot] at hu
    rw [SetLike.mem_coe, hA₂, mem_bot] at hv
    rw [← huv, hu, hv, mul_one]
    exact one_mem _
  have hA₂ne : A₂ ≠ ⊥ := by
    intro hA
    apply hA₁ne
    rw [← hA₂hx, hA]
    exact Subgroup.map_bot _
  have hsupp : ∀ (K : Subgroup H), X ≤ normalizer (K : Set H) →
      Nat.card (P ⊓ K : Subgroup H) = p → ⁅Q, P ⊓ K⁆ ≠ ⊥ → ⁅⁅Q, P ⊓ K⁆, P ⊓ K⁆ ≠ ⊥ := by
    intro K hXKn hPK hne hc
    apply hne
    rw [eq_bot_iff, commutator_le]
    intro q hq a ha
    have hcA : ⁅q, a⁆ ∈ ⁅Q, P ⊓ K⁆ := commutator_mem_commutator hq ha
    have hcQ : ⁅q, a⁆ ∈ Q := (Subgroup.mem_inf.mp (hcommQ K hXKn hcA)).1
    have hca : a * ⁅q, a⁆ * a⁻¹ = ⁅q, a⁆ := by
      have h1 := commute_of_commutator_eq_bot hc hcA ha
      rw [← h1, mul_inv_cancel_right]
    have hap : a ^ p = 1 := pow_eq_one_of_mem_of_card_eq hPK ha
    have hxq : a * q⁻¹ * a⁻¹ = q⁻¹ * ⁅q, a⁆ := by
      simp only [commutatorElement_def]
      group
    rw [mem_bot]
    exact eq_one_of_conj_eq_mul_fixed hpQ hp hcQ hap hca hxq
  exact ⟨hA₁le, hA₂le, hPA₁, hPA₂, hQeq, hcA, hcA₁P₂, hcA₂P₁,
    hsupp K₁ (fun g hg => hK₁n (hXK hg)) hP₁ hA₁ne,
    hsupp K₂ (fun g hg => hK₂n (hXK hg)) hP₂ hA₂ne,
    x, hxX, hhx, hP₁hx, hP₂hx, hA₁hx, hA₂hx⟩

end CFSG.Quasithin.SteinbergCD
