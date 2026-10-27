module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesNatural

public section

namespace CFSG.Quasithin.B45L2

open CFSG.QuasithinUnique.Setup.SL2Modules
open scoped MatrixGroups

theorem card_fixed_sq_le {W : Type*} [AddCommGroup W] [Finite W] (U : AddSubgroup W)
    (a κ κ' : W →+ W) (hκ : ∀ w, a (κ w) = κ' (a w)) (hinj : ∀ z, κ z = κ' z → z = 0)
    (hU : ∀ u ∈ U, κ u ∈ U) :
    Nat.card {u : W // u ∈ U ∧ a u = u} ^ 2 ≤ Nat.card U := by
  set C := {u : W // u ∈ U ∧ a u = u}
  let f : C × C → U := fun p => ⟨p.1.1 + κ p.2.1, U.add_mem p.1.2.1 (hU _ p.2.2.1)⟩
  have hf : Function.Injective f := by
    rintro ⟨⟨x, hxU, hx⟩, ⟨y, hyU, hy⟩⟩ ⟨⟨x', hx'U, hx'⟩, ⟨y', hy'U, hy'⟩⟩ h
    have h1 : x + κ y = x' + κ y' := congrArg Subtype.val h
    have h2 : x - x' = κ (y' - y) := by
      rw [map_sub, sub_eq_sub_iff_add_eq_add, add_comm (κ y') x']
      exact h1
    have h3 : a (x - x') = x - x' := by rw [map_sub, hx, hx']
    have h4 : κ (y' - y) = κ' (y' - y) := by
      rw [← h2, ← h3, h2, hκ, map_sub, hy, hy']
    have h5 : y' - y = 0 := hinj _ h4
    have h6 : y = y' := (sub_eq_zero.mp h5).symm
    subst h6
    have h7 : x = x' := by simpa using h1
    subst h7
    rfl
  have h := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod, ← sq] at h

section Field

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

theorem zmod_two_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c
  decide

theorem card_endRing_le_of_finrank_eq_two {n : ℕ} (hn : 1 ≤ n) (hF : Fintype.card F = 2 ^ n)
    (ρ : Representation (ZMod 2) SL(2, F) W) [Fact ρ.IsIrreducible] (hnt : ∃ g, ρ g ≠ 1)
    {d : ℕ} (hD : Nat.card (EndRing ρ) = 2 ^ d) (hdim : Module.finrank (EndRing ρ) W = 2)
    (ιF : F →+* EndRing ρ) : Nat.card (EndRing ρ) ≤ Nat.card F := by
  classical
  have hfin : Finite (EndRing ρ) := finite_endRing ρ
  have hchar : CharP (EndRing ρ) 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) (EndRing ρ)).injective 2
  obtain ⟨j, θ, hθ⟩ := exists_coordinate_iso hn hF ρ hnt hD hdim ιF
  let φ : F →+* EndRing ρ := (iterateFrobenius (EndRing ρ) 2 j).comp ιF
  have hφ : ∀ x, φ x = (ιF x) ^ (2 ^ j) := fun x => by simp [φ, iterateFrobenius_def]
  let R : Subring (EndRing ρ) := φ.range
  let U : Submodule (ZMod 2) W :=
    { carrier := {w | ∀ a, θ w a ∈ R}
      add_mem' := fun {x y} hx hy a => by
        simp only [Set.mem_ofPred_eq, map_add, Pi.add_apply] at hx hy ⊢
        exact R.add_mem (hx a) (hy a)
      zero_mem' := fun a => by
        simp only [map_zero, Pi.zero_apply]
        exact R.zero_mem
      smul_mem' := fun c {x} hx a => by
        rcases zmod_two_cases c with rfl | rfl
        · simp only [zero_smul, map_zero, Pi.zero_apply]
          exact R.zero_mem
        · simpa using hx a }
  have hUinv : ∀ g, ∀ u ∈ U, ρ g u ∈ U := by
    intro g u hu a
    show θ (ρ g u) a ∈ R
    rw [hθ]
    refine R.sum_mem fun c _ => R.mul_mem ?_ (hu c)
    rw [← hφ]
    exact ⟨_, rfl⟩
  obtain ⟨-, hirr⟩ := (isIrreducible_iff ρ).mp Fact.out
  have hUtop : U = ⊤ := by
    rcases hirr U hUinv with h | h
    · exfalso
      set w₀ := θ.symm (Pi.single 0 1) with hw₀
      have hw₀U : w₀ ∈ U := by
        intro a
        show θ w₀ a ∈ R
        rw [hw₀, AddEquiv.apply_symm_apply]
        by_cases ha : a = 0
        · subst ha
          simp only [Pi.single_eq_same]
          exact R.one_mem
        · rw [Pi.single_eq_of_ne ha]
          exact R.zero_mem
      rw [h, Submodule.mem_bot] at hw₀U
      have h1 := congrArg θ hw₀U
      rw [hw₀, AddEquiv.apply_symm_apply, map_zero] at h1
      have := congrFun h1 0
      simp at this
    · exact h
  have hsurj : Function.Surjective φ := by
    intro δ
    have hmem : θ.symm (fun _ => δ) ∈ U := by rw [hUtop]; trivial
    obtain ⟨x, hx⟩ := hmem 0
    refine ⟨x, ?_⟩
    rw [hx, AddEquiv.apply_symm_apply]
  exact Nat.card_le_card_of_surjective φ hsurj

theorem eq_of_finrank_eq_two {n : ℕ} (hn : 1 ≤ n) (hF : Fintype.card F = 2 ^ n)
    (ρ : Representation (ZMod 2) SL(2, F) W) [Fact ρ.IsIrreducible] (hnt : ∃ g, ρ g ≠ 1)
    {d : ℕ} (hD : Nat.card (EndRing ρ) = 2 ^ d) (hdim : Module.finrank (EndRing ρ) W = 2)
    (hnd : n ∣ d) : d = n := by
  classical
  have hfin : Finite (EndRing ρ) := finite_endRing ρ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Algebra (ZMod 2) F := ZMod.algebra F 2
  have : Module.Finite (ZMod 2) (EndRing ρ) := Module.Finite.of_finite
  have : Module.Finite (ZMod 2) F := Module.Finite.of_finite
  have hfrD : Module.finrank (ZMod 2) (EndRing ρ) = d := by
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := EndRing ρ)
    rw [hD, Nat.card_zmod] at h1
    exact (Nat.pow_right_injective le_rfl h1).symm
  have hfrF : Module.finrank (ZMod 2) F = n := by
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F)
    rw [Nat.card_eq_fintype_card, hF, Nat.card_zmod] at h1
    exact (Nat.pow_right_injective le_rfl h1).symm
  obtain ⟨ψ⟩ := FiniteField.nonempty_algHom_of_finrank_dvd (F := ZMod 2) (K := F)
    (L := EndRing ρ) (by rw [hfrD, hfrF]; exact hnd)
  have hle := card_endRing_le_of_finrank_eq_two hn hF ρ hnt hD hdim (ψ : F →+* EndRing ρ)
  rw [hD, Nat.card_eq_fintype_card, hF] at hle
  have h1 : d ≤ n := (Nat.pow_le_pow_iff_right (by norm_num)).mp hle
  have h2 : n ≤ d := Nat.le_of_dvd (by
    rcases Nat.eq_zero_or_pos d with h | h
    · subst h
      have : Nat.card (EndRing ρ) = 1 := by rw [hD]; rfl
      have h3 := Finite.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial (EndRing ρ))
      omega
    · exact h) hnd
  omega

end Field

end CFSG.Quasithin.B45L2
