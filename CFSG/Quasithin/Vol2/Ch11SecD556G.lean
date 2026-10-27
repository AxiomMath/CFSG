module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.A1bBasic
public import CFSG.Quasithin.Background.B2FactorizationResidual
public import CFSG.Quasithin.H13.Statements

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G]

theorem commutator_sSup_le {𝒮 : Set (Subgroup G)} {X N : Subgroup G}
    (hN : sSup 𝒮 ≤ Subgroup.normalizer (N : Set G)) (h : ∀ S ∈ 𝒮, ⁅S, X⁆ ≤ N) :
    ⁅sSup 𝒮, X⁆ ≤ N := by
  let C : Subgroup G :=
    { carrier := {g | g ∈ Subgroup.normalizer (N : Set G) ∧ ∀ x ∈ X, ⁅g, x⁆ ∈ N}
      one_mem' := ⟨Subgroup.one_mem _, fun x _ => by simp⟩
      mul_mem' := by
        rintro a b ⟨haN, ha⟩ ⟨hbN, hb⟩
        refine ⟨Subgroup.mul_mem _ haN hbN, fun x hx => ?_⟩
        have e : ⁅a * b, x⁆ = a * ⁅b, x⁆ * a⁻¹ * ⁅a, x⁆ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact N.mul_mem ((Subgroup.mem_normalizer_iff.mp haN _).mp (hb x hx)) (ha x hx)
      inv_mem' := by
        rintro a ⟨haN, ha⟩
        refine ⟨Subgroup.inv_mem _ haN, fun x hx => ?_⟩
        have e : ⁅a⁻¹, x⁆ = a⁻¹ * ⁅a, x⁆⁻¹ * a⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ haN) _).mp
          (N.inv_mem (ha x hx)) }
  have hle : sSup 𝒮 ≤ C := sSup_le fun S hS g hg =>
    ⟨hN (le_sSup hS hg), fun x hx => Subgroup.commutator_le.mp (h S hS) g hg x hx⟩
  exact Subgroup.commutator_le.mpr fun g hg x hx => (hle hg).2 x hx

theorem opResidual_eq_self_of_odd [Finite G] {X : Subgroup G} (hX : Odd (Nat.card X)) :
    opResidual 2 X = X := by
  refine le_antisymm (opResidual_le 2 X) fun x hx => Subgroup.subset_closure ⟨hx, ?_⟩
  have hdvd : orderOf x ∣ Nat.card X := by
    rw [← Subgroup.orderOf_mk x hx]
    exact orderOf_dvd_natCard _
  exact Nat.Coprime.coprime_dvd_left hdvd (Nat.coprime_two_right.mpr hX)

theorem le_two_of_elemAbelian_quotient [Finite G] {G₁ : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2)
    (hrank : ∀ E : Subgroup G, E ≤ G₁ → IsElemAbelian p E → ∀ r, Nat.card E = p ^ r → r ≤ 2)
    {E : Subgroup (↥G₁ ⧸ CFSG.pCore 2 ↥G₁)} (hE : IsElemAbelian p E) {r : ℕ}
    (hcard : Nat.card E = p ^ r) : r ≤ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥G₁) with hπdef
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hEp : IsPGroup p E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  obtain ⟨Q, hEQ⟩ := hEp.exists_le_sylow
  obtain ⟨S, hS⟩ := Sylow.mapSurjective_surjective hπ p Q
  have hSQ : (S : Subgroup ↥G₁).map π = Q := by rw [← hS]; rfl
  have hinj : ∀ a ∈ (S : Subgroup ↥G₁), ∀ b ∈ (S : Subgroup ↥G₁), π a = π b → a = b := by
    intro a ha b hb hab
    have hk : a⁻¹ * b ∈ CFSG.pCore 2 ↥G₁ := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      change (π a)⁻¹ * π b = 1
      rw [hab, inv_mul_cancel]
    have hs : a⁻¹ * b ∈ (S : Subgroup ↥G₁) := Subgroup.mul_mem _ (Subgroup.inv_mem _ ha) hb
    obtain ⟨i, hi⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥G₁)) ⟨_, hk⟩
    obtain ⟨j, hj⟩ := S.isPGroup' ⟨_, hs⟩
    have hi' : (a⁻¹ * b) ^ 2 ^ i = 1 := by simpa using congrArg Subtype.val hi
    have hj' : (a⁻¹ * b) ^ p ^ j = 1 := by simpa using congrArg Subtype.val hj
    have h1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left
      (orderOf_dvd_of_pow_eq_one hi') (Nat.Coprime.pow_left i
        (Nat.Coprime.pow_right j ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)))))
      (orderOf_dvd_of_pow_eq_one hj')
    rw [orderOf_eq_one_iff, inv_mul_eq_one] at h1
    exact h1
  set E' := E.comap π ⊓ (S : Subgroup ↥G₁) with hE'def
  have hmap : E'.map π = E := by
    refine le_antisymm (fun _ ⟨s, hs, hse⟩ => hse ▸ hs.1) fun e he => ?_
    have heQ : e ∈ (S : Subgroup ↥G₁).map π := hSQ ▸ hEQ he
    obtain ⟨s, hs, rfl⟩ := heQ
    exact ⟨s, ⟨he, hs⟩, rfl⟩
  have hcard' : Nat.card E' = p ^ r := by
    rw [← hcard, ← hmap]
    refine (Nat.card_congr (Equiv.ofBijective (fun s : ↥E' => (⟨π s, s, s.2, rfl⟩ : ↥(E'.map π)))
      ⟨fun a b hab => Subtype.ext (hinj a a.2.2 b b.2.2 (congrArg Subtype.val hab)), ?_⟩))
    rintro ⟨_, s, hs, rfl⟩
    exact ⟨⟨s, hs⟩, rfl⟩
  set E'' := E'.map G₁.subtype with hE''def
  have hE''ab : IsElemAbelian p E'' := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨a', ha', haa⟩ := Subgroup.mem_map.mp a.2
      obtain ⟨b', hb', hbb⟩ := Subgroup.mem_map.mp b.2
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← haa, ← hbb, ← map_mul, ← map_mul]
      congr 1
      refine hinj _ (Subgroup.mul_mem _ ha'.2 hb'.2) _ (Subgroup.mul_mem _ hb'.2 ha'.2) ?_
      rw [map_mul, map_mul]
      have := hE.1
      exact congrArg Subtype.val (mul_comm (⟨π a', ha'.1⟩ : ↥E) ⟨π b', hb'.1⟩)
    · obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
      have h1 : x' ^ p = 1 := by
        refine hinj _ (Subgroup.pow_mem _ hx'.2 p) _ (Subgroup.one_mem _) ?_
        rw [map_pow, map_one]
        exact hE.2 _ hx'.1
      rw [← map_pow, h1, map_one]
  have hE''card : Nat.card E'' = p ^ r := by
    rw [hE''def, Subgroup.card_map_of_injective G₁.subtype_injective, hcard']
  exact hrank E'' (Subgroup.map_subtype_le _) hE''ab r hE''card

end CFSG.Quasithin.Vol2.Ch11.SecD
