module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TwE6Rad
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TwE6CoordAct
public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs

public section

namespace CFSG.StandardType.LieKnownR2.Short

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Exceptional CFSG.Blueprint.Chevalley
open scoped commutatorElement

theorem twE6_rad_irreducible
    (f : ℕ) (hf : 2 ≤ f) :
    ∀ V : Subgroup (twistedE6Group 2 f),
      twE6Cen (frobQ 2 f) ≤ V → V ≤ twE6Rad (frobQ 2 f) →
      Subgroup.normalizer
          (((twistedE6Datum 2 f).rootGroup twE6Alpha : Subgroup (twistedE6Group 2 f)) :
            Set (twistedE6Group 2 f)) ≤ Subgroup.normalizer (V : Set (twistedE6Group 2 f)) →
      V = twE6Cen (frobQ 2 f) ∨ V = twE6Rad (frobQ 2 f) := by
  intro V hCen hVrad hNorm
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hθ : ∀ c : GaloisField 2 (2 * f), frobQ 2 f (frobQ 2 f c) = c :=
    frobQ_frobQ 2 f (by omega)
  obtain ⟨Φ, hΦ⟩ := twE6_exists_coord (frobQ 2 f) hθ
  obtain ⟨t, ht⟩ := IsCyclic.exists_generator (α := (GaloisField 2 (2 * f))ˣ)
  have h1 : (1 : fixedGroup (GaloisField 2 (2 * f)) (frobQ 2 f)) ∈ twE6Rad (frobQ 2 f) :=
    (twE6Rad (frobQ 2 f)).one_mem
  have hΦ_one : Φ 1 = 0 := by
    have h := hΦ.1 1 h1 1 h1
    rw [mul_one] at h
    exact (add_left_cancel ((add_zero (Φ 1)).trans h)).symm
  have hΦ_neg : ∀ v ∈ twE6Rad (frobQ 2 f), Φ v⁻¹ = -Φ v := by
    intro v hv
    have h := hΦ.1 v hv v⁻¹ ((twE6Rad (frobQ 2 f)).inv_mem hv)
    rw [mul_inv_cancel, hΦ_one] at h
    refine (eq_neg_iff_add_eq_zero).mpr ?_
    simpa [add_comm] using h.symm
  let W : AddSubgroup (Fin 8 → GaloisField 2 (2 * f)) :=
    { carrier := {m | ∃ v ∈ V, Φ v = m}
      zero_mem' := ⟨1, V.one_mem, hΦ_one⟩
      add_mem' := by
        rintro m m' ⟨v, hv, rfl⟩ ⟨v', hv', rfl⟩
        exact ⟨v * v', V.mul_mem hv hv', hΦ.1 v (hVrad hv) v' (hVrad hv')⟩
      neg_mem' := by
        rintro m ⟨v, hv, rfl⟩
        exact ⟨v⁻¹, V.inv_mem hv, hΦ_neg v (hVrad hv)⟩ }
  have hWmem : ∀ m : Fin 8 → GaloisField 2 (2 * f), m ∈ W ↔ ∃ v ∈ V, Φ v = m :=
    fun _ => Iff.rfl
  have hshift : ∀ (j : Fin 12), ∀ m ∈ W, m + twE6ShiftMap j m ∈ W := by
    intro j m hm
    rw [hWmem] at hm ⊢
    obtain ⟨v, hv, rfl⟩ := hm
    refine ⟨twE6Y (frobQ 2 f) j * v * (twE6Y (frobQ 2 f) j)⁻¹, ?_,
      (twE6_coord_shift (frobQ 2 f) hθ hΦ j (hVrad hv)).2⟩
    exact (Subgroup.mem_normalizer_iff.mp
      (hNorm (twE6Y_mem_normalizer_alpha (frobQ 2 f) j)) v).mp hv
  have htorus : ∀ m ∈ W, twE6TorusMap (frobQ 2 f) (t : GaloisField 2 (2 * f)) m ∈ W := by
    intro m hm
    rw [hWmem] at hm ⊢
    obtain ⟨v, hv, rfl⟩ := hm
    obtain ⟨h, hh, hconj⟩ := twE6_coord_torus (frobQ 2 f) hθ hΦ t
    refine ⟨h * v * h⁻¹, ?_, (hconj v (hVrad hv)).2⟩
    exact (Subgroup.mem_normalizer_iff.mp
      (hNorm (hHat_le_normalizer_alpha (frobQ 2 f) twE6ShortNode hh)) v).mp hv
  have hperm : ∀ m ∈ W, twE6PermMap m ∈ W := by
    intro m hm
    rw [hWmem] at hm ⊢
    obtain ⟨v, hv, rfl⟩ := hm
    refine ⟨nHat (frobQ 2 f) twE6ShortNode * v * (nHat (frobQ 2 f) twE6ShortNode)⁻¹, ?_,
      (twE6_coord_perm (frobQ 2 f) hθ hΦ (hVrad hv)).2⟩
    exact (Subgroup.mem_normalizer_iff.mp
      (hNorm (nHat_mem_normalizer_alpha (frobQ 2 f))) v).mp hv
  have hsurj : Function.Surjective (frobQ 2 f) := fun y => ⟨frobQ 2 f y, hθ y⟩
  have htgen : ∀ S : AddSubgroup (GaloisField 2 (2 * f)), (1 : GaloisField 2 (2 * f)) ∈ S →
      (∀ x ∈ S, (t : GaloisField 2 (2 * f)) * x ∈ S) → S = ⊤ := by
    intro S hS1 hSt
    have hpow : ∀ n : ℕ, (t : GaloisField 2 (2 * f)) ^ n ∈ S := by
      intro n
      induction n with
      | zero => simpa using hS1
      | succ n ih => simpa [pow_succ, mul_comm] using hSt _ ih
    rw [eq_top_iff]
    intro x _
    by_cases hx : x = 0
    · rw [hx]; exact S.zero_mem
    · have hpw : (Units.mk0 x hx : (GaloisField 2 (2 * f))ˣ) ∈ Submonoid.powers t :=
        (isOfFinOrder_of_finite t).mem_powers_iff_mem_zpowers.mpr (ht (Units.mk0 x hx))
      obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp hpw
      have hnval : (t : GaloisField 2 (2 * f)) ^ n = x := by
        have := congrArg (fun u : (GaloisField 2 (2 * f))ˣ => (u : GaloisField 2 (2 * f))) hn
        simpa using this
      rw [← hnval]
      exact hpow n
  have hres := twE6_model_irreducible (frobQ 2 f) hsurj htgen W hshift htorus hperm
  rcases hres with hW | hW
  · left
    apply le_antisymm _ hCen
    intro v hv
    have hm : Φ v ∈ W := (hWmem (Φ v)).mpr ⟨v, hv, rfl⟩
    rw [hW] at hm
    exact (hΦ.2.1 v (hVrad hv)).mp (by simpa using hm)
  · right
    apply le_antisymm hVrad
    intro g hg
    have hm : Φ g ∈ W := by rw [hW]; exact AddSubgroup.mem_top _
    obtain ⟨v, hv, hvg⟩ := (hWmem (Φ g)).mp hm
    have hmem : v⁻¹ * g ∈ twE6Cen (frobQ 2 f) := by
      refine (hΦ.2.1 (v⁻¹ * g) ?_).mp ?_
      · exact (twE6Rad (frobQ 2 f)).mul_mem ((twE6Rad (frobQ 2 f)).inv_mem (hVrad hv)) hg
      · rw [hΦ.1 v⁻¹ ((twE6Rad (frobQ 2 f)).inv_mem (hVrad hv)) g hg,
          hΦ_neg v (hVrad hv), hvg]
        exact neg_add_cancel _
    have hmemV : v⁻¹ * g ∈ V := hCen hmem
    have hg_eq : g = v * (v⁻¹ * g) := by group
    rw [hg_eq]
    exact V.mul_mem hv hmemV

end CFSG.StandardType.LieKnownR2.Short
