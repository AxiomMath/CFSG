module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderUOMono

public section

namespace CFSG.StandardType

namespace NoOffOm

open Multiplicative

section Supp

variable {p r : ℕ}

@[expose] def SuppLE (s s' : Fin r → ZMod p) : Prop := ∀ i, s i ≠ 0 → s' i ≠ 0

theorem suppLE_zero_left (s : Fin r → ZMod p) : SuppLE 0 s := fun _ h => absurd rfl h

theorem eq_zero_of_suppLE_zero {s : Fin r → ZMod p} (h : SuppLE s 0) : s = 0 :=
  funext fun i => by
    by_contra hi
    exact h i hi rfl

theorem suppLE_single_iff [DecidableEq (Fin r)] {j : Fin r} {a : ZMod p} (ha : a ≠ 0)
    (s : Fin r → ZMod p) : SuppLE s (Pi.single j a) ↔ ∀ i, i ≠ j → s i = 0 := by
  constructor
  · intro h i hij
    by_contra hi
    exact h i hi (by rw [Pi.single_eq_of_ne hij])
  · intro h i hi
    by_cases hij : i = j
    · subst hij
      rwa [Pi.single_eq_same]
    · exact absurd (h i hij) hi

theorem single_suppLE [DecidableEq (Fin r)] {j : Fin r} {a : ZMod p} {s : Fin r → ZMod p}
    (hs : s j ≠ 0) : SuppLE (Pi.single j a) s := by
  intro i hi
  by_cases hij : i = j
  · rwa [hij]
  · rw [Pi.single_eq_of_ne hij] at hi
    exact absurd rfl hi

theorem eq_single_of_forall [DecidableEq (Fin r)] {j : Fin r} {s : Fin r → ZMod p}
    (h : ∀ i, i ≠ j → s i = 0) : s = Pi.single j (s j) := by
  funext i
  by_cases hij : i = j
  · subst hij
    rw [Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne hij, h i hij]

theorem exists_monomial_of_suppLE [Fact p.Prime] (φ : (Fin r → ZMod p) →+ (Fin r → ZMod p))
    (hφ : ∀ s s', SuppLE (φ s) (φ s') ↔ SuppLE s s') :
    ∃ (π : Equiv.Perm (Fin r)) (η : Fin r → (ZMod p)ˣ),
      ∀ s, φ s = fun i => (η i : ZMod p) * s (π i) := by
  classical
  have hpp : p.Prime := Fact.out
  have : NeZero p := ⟨hpp.ne_zero⟩
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro s hs
    refine eq_zero_of_suppLE_zero ((hφ s 0).mp ?_)
    rw [hs]
    exact suppLE_zero_left _
  have hsurj : Function.Surjective φ := Finite.surjective_of_injective hinj
  have hone : ∀ j : Fin r, ∃ i, φ (Pi.single j 1) i ≠ 0 ∧ ∀ k, k ≠ i → φ (Pi.single j 1) k = 0 := by
    intro j
    set v := φ (Pi.single j 1) with hv
    have hv0 : v ≠ 0 := fun h0 => by
      have h1 : Pi.single (M := fun _ => ZMod p) j (1 : ZMod p) = 0 :=
        hinj (by rw [← hv, h0, map_zero])
      have := congrFun h1 j
      rw [Pi.single_eq_same, Pi.zero_apply] at this
      exact one_ne_zero this
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hv0 (funext hcon)
    refine ⟨i, hi, ?_⟩
    obtain ⟨s', hs'⟩ := hsurj (Pi.single i (v i))
    have h1 : SuppLE s' (Pi.single j 1) := (hφ s' _).mp (by
      rw [hs']
      exact single_suppLE hi)
    have h2 : ∀ k, k ≠ j → s' k = 0 := (suppLE_single_iff one_ne_zero s').mp h1
    have h3 : s' j ≠ 0 := by
      intro h0
      have hs0 : s' = 0 := funext fun k => by
        by_cases hk : k = j
        · rw [hk, h0, Pi.zero_apply]
        · rw [h2 k hk, Pi.zero_apply]
      have := congrFun hs' i
      rw [hs0, map_zero, Pi.zero_apply, Pi.single_eq_same] at this
      exact hi this.symm
    have h4 : SuppLE (Pi.single j 1) s' := single_suppLE h3
    have h5 : SuppLE v (Pi.single i (v i)) := by
      rw [← hs']
      exact (hφ _ _).mpr h4
    exact (suppLE_single_iff hi v).mp h5
  choose π' hπ'0 hπ' using hone
  have hπinj : Function.Injective π' := by
    intro j k hjk
    have h1 : SuppLE (φ (Pi.single j 1)) (φ (Pi.single k 1)) := by
      intro i hi
      by_cases hij : i = π' j
      · rw [hij, hjk]
        exact hπ'0 k
      · exact absurd (hπ' j i hij) hi
    have h2 := (hφ _ _).mp h1 j (by rw [Pi.single_eq_same]; exact one_ne_zero)
    by_contra hne
    exact h2 (Pi.single_eq_of_ne hne _)
  set σ := Equiv.ofBijective π' (Finite.injective_iff_bijective.mp hπinj) with hσ
  have hσj : ∀ j, σ j = π' j := fun j => rfl
  set c : Fin r → ZMod p := fun j => φ (Pi.single j 1) (π' j) with hc
  have hc0 : ∀ j, c j ≠ 0 := hπ'0
  have hφe : ∀ j, φ (Pi.single j 1) = Pi.single (π' j) (c j) := fun j =>
    eq_single_of_forall (hπ' j)
  have hφs : ∀ j (a : ZMod p), φ (Pi.single j a) = Pi.single (π' j) (a * c j) := by
    intro j a
    have e1 : Pi.single (M := fun _ => ZMod p) j a = a.val • Pi.single j (1 : ZMod p) := by
      rw [← Pi.single_smul, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
    rw [e1, map_nsmul, hφe, ← Pi.single_smul, nsmul_eq_mul, ZMod.natCast_zmod_val]
  refine ⟨σ.symm, fun i => Units.mk0 (c (σ.symm i)) (hc0 _), fun s => ?_⟩
  funext i
  have hs : s = ∑ j, Pi.single j (s j) := (Finset.univ_sum_single s).symm
  conv_lhs => rw [hs]
  rw [map_sum, Finset.sum_apply]
  simp only [hφs]
  rw [Finset.sum_eq_single (σ.symm i)]
  · have : π' (σ.symm i) = i := by rw [← hσj, Equiv.apply_symm_apply]
    rw [this, Pi.single_eq_same, Units.val_mk0, mul_comm]
  · intro j _ hj
    have : π' j ≠ i := by
      intro hji
      apply hj
      rw [← hji, ← hσj, Equiv.symm_apply_apply]
    exact Pi.single_eq_of_ne' this _
  · intro h
    exact absurd (Finset.mem_univ _) h

end Supp

section Group

variable {G : Type} [Group G] {p r : ℕ}

theorem inv_mul_mul_mem {H : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (H : Set G))
    {b : G} (hb : b ∈ H) : g⁻¹ * b * g ∈ H := by
  have := (Subgroup.mem_normalizer_iff.1 (inv_mem hg) b).1 hb
  rwa [inv_inv] at this

theorem monoAct_of_suppRel [Fact p.Prime] {ι : Multiplicative (Fin r → ZMod p) →* G}
    (hinj : Function.Injective ι) {g : G} (hg : g ∈ Subgroup.normalizer (ι.range : Set G))
    (R : G → G → Prop) (hR : ∀ s s', R (ι (ofAdd s)) (ι (ofAdd s')) ↔ SuppLE s s')
    (hRg : ∀ s s', R (g⁻¹ * ι (ofAdd s) * g) (g⁻¹ * ι (ofAdd s') * g) ↔
      R (ι (ofAdd s)) (ι (ofAdd s'))) :
    NoOffUO.GGMonoAct ι g := by
  have hmem : ∀ s : Fin r → ZMod p, ∃ t : Fin r → ZMod p,
      ι (ofAdd t) = g⁻¹ * ι (ofAdd s) * g := by
    intro s
    obtain ⟨t, ht⟩ := inv_mul_mul_mem hg (MonoidHom.mem_range.mpr ⟨ofAdd s, rfl⟩)
    exact ⟨toAdd t, ht⟩
  choose φ hφ using hmem
  have hadd : ∀ s s', φ (s + s') = φ s + φ s' := by
    intro s s'
    have e : ι (ofAdd (φ (s + s'))) = ι (ofAdd (φ s + φ s')) := by
      simp only [ofAdd_add, map_mul, hφ]
      group
    exact ofAdd.injective (hinj e)
  set Φ : (Fin r → ZMod p) →+ (Fin r → ZMod p) := AddMonoidHom.mk' φ hadd with hΦ
  have hΦφ : ∀ s, Φ s = φ s := fun s => rfl
  have hsupp : ∀ s s', SuppLE (Φ s) (Φ s') ↔ SuppLE s s' := by
    intro s s'
    rw [hΦφ, hΦφ, ← hR, hφ, hφ, hRg, hR]
  obtain ⟨π, η, hπη⟩ := exists_monomial_of_suppLE Φ hsupp
  refine ⟨π, η, fun s => ?_⟩
  rw [← hφ, ← hΦφ, hπη]

end Group

end NoOffOm

end CFSG.StandardType
