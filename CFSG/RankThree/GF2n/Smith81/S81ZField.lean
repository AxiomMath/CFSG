module

public import CFSG.RankThree.GF2n.Smith81.S81ZGal
public import CFSG.RankThree.GF2n.Smith81.S81ZUnip

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.S81Z

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
  CFSG.RankThree.GF2n.Smith81.XOps CFSG.RankThree.GF2n.Smith81.E7Model
  CFSG.RankThree.GF2n.Smith81.E7X
open scoped commutatorElement


variable {K : Type} [Field K]

theorem exists_toWeight_unit {α : Rt} (hα : IsRoot .E7 α) :
    ∃ i, MinData.toWeight α i = 1 ∨ MinData.toWeight α i = -1 := by
  refine (forall_isRoot_iff fun γ => ∃ i, MinData.toWeight γ i = 1 ∨ MinData.toWeight γ i = -1).2
    ?_ α hα
  decide +kernel

theorem chi_eq_prod (α : Rt) (t : Tt K) :
    (chi α t : Kˣ) = ∏ i, t i ^ MinData.toWeight α i := by
  unfold chi
  simp only [MonoidHom.coe_mk, OneHom.coe_mk]
  rw [← List.prod_ofFn]
  congr 1

theorem chi_mulSingle (α : Rt) (i : Fin (Tag.rank .E7)) (c : Kˣ) :
    (chi α (Pi.mulSingle i c) : Kˣ) = c ^ MinData.toWeight α i := by
  rw [chi_eq_prod, Finset.prod_eq_single i]
  · simp
  · intro j _ hji
    simp [Pi.mulSingle_apply, hji]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem chi_surjective {α : Rt} (hα : IsRoot .E7 α) : Function.Surjective (chi (K := K) α) := by
  intro u
  obtain ⟨i, hi⟩ := exists_toWeight_unit hα
  rcases hi with hi | hi
  · exact ⟨Pi.mulSingle i u, by rw [chi_mulSingle, hi, zpow_one]⟩
  · exact ⟨Pi.mulSingle i u⁻¹, by rw [chi_mulSingle, hi, zpow_neg_one, inv_inv]⟩

theorem frob_form [Finite K] [CharP K 2] (σ : K ≃+* K) :
    letI : Algebra (ZMod 2) K := ZMod.algebra K 2
    ∃ j : ℕ, j < Module.finrank (ZMod 2) K ∧ ∀ x : K, σ x = x ^ 2 ^ j := by
  letI : Algebra (ZMod 2) K := ZMod.algebra K 2
  let σa : K →ₐ[ZMod 2] K :=
    { σ.toRingHom with
      commutes' := fun r => by
        have := RingHom.congr_fun (RingHom.ext_zmod (σ.toRingHom.comp (algebraMap (ZMod 2) K))
          (algebraMap (ZMod 2) K)) r
        simpa using this }
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgHom_pow (ZMod 2) K).2 σa
  refine ⟨n.1, n.2, fun x => ?_⟩
  have := congrArg (fun φ : K →ₐ[ZMod 2] K => φ x) hn
  simp only [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate] at this
  rw [ZMod.card] at this
  exact this.symm

theorem chi_ne [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K) {α β : Rt} (hα : IsRoot .E7 α)
    (hαp : 0 < ht α) (hβ : IsRoot .E7 β) (hβp : 0 < ht β) (hne : α ≠ β) (σ : K ≃+* K) :
    ∃ t : Tt K, σ ((chi α t : Kˣ) : K) ≠ ((chi β t : Kˣ) : K) := by
  by_contra hcon
  push Not at hcon
  letI : Algebra (ZMod 2) K := ZMod.algebra K 2
  obtain ⟨j, hj, hσ⟩ := frob_form σ
  set f := Module.finrank (ZMod 2) K with hfdef
  have hcard : Nat.card K = 2 ^ f := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := K), Nat.card_zmod]
  have hf2 : 2 ≤ f := by
    by_contra hlt
    push Not at hlt
    interval_cases f <;> simp at hcard <;> omega
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf g = 2 ^ f - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hcard]
  have hdvd : ∀ i : Fin (Tag.rank .E7), ((2 : ℤ) ^ f - 1) ∣
      MinData.toWeight β i - 2 ^ j * MinData.toWeight α i := by
    intro i
    have h1 := hcon (Pi.mulSingle i g)
    rw [chi_mulSingle, chi_mulSingle] at h1
    have h2 : (g : K) ^ ((2 : ℤ) ^ j * MinData.toWeight α i) = (g : K) ^ MinData.toWeight β i := by
      rw [Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, map_zpow₀, hσ] at h1
      rw [zpow_mul]
      have e : (g : K) ^ ((2 : ℤ) ^ j) = (g : K) ^ (2 ^ j) := by norm_cast
      rw [e]
      exact h1
    have h3 : g ^ ((2 : ℤ) ^ j * MinData.toWeight α i) = g ^ MinData.toWeight β i := by
      apply Units.ext
      rw [Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val]
      exact h2
    have h4 := Int.modEq_iff_dvd.1 (zpow_eq_zpow_iff_modEq.1 h3)
    rw [hord] at h4
    have h5 : ((2 ^ f - 1 : ℕ) : ℤ) = (2 : ℤ) ^ f - 1 := by
      rw [Nat.cast_sub Nat.one_le_two_pow]
      push_cast
      ring
    rwa [h5] at h4
  exact hne (exps_equal hf2 hj hα hαp hβ hβp hdvd)

end CFSG.RankThree.GF2n.Smith81.S81Z
