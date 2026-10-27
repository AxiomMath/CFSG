module

public import CFSG.GH74.GLS.IVK.Defs
import CFSG.Adapters.SpecialLinearPerfect
import CFSG.GH74.GLS.IVK.L2.FieldProj
import CFSG.RankThree.PartTwo.Sec20.SimsAscBridgeL2OddGroup

public section

namespace CFSG.RankThree.PartTwo.Sec20.SL2Aut

open Matrix CFSG.GH74.GLS CFSG.GH74.GLS.IVK
open scoped commutatorElement

theorem subsingleton_ringEquiv_of_card_prime {F : Type*} [Field F] [Finite F]
    (hF : (Nat.card F).Prime) : Subsingleton (F ≃+* F) := by
  have := Fintype.ofFinite F
  let ι : ZMod (Nat.card F) ≃+* F := ZMod.ringEquivOfPrime F hF Nat.card_eq_fintype_card.symm
  refine ⟨fun σ τ => RingEquiv.ext fun x => ?_⟩
  obtain ⟨n, rfl⟩ := ι.surjective x
  exact congrArg (fun f : ZMod (Nat.card F) →+* F => f n)
    (RingHom.ext_zmod (σ.toRingHom.comp ι.toRingHom) (τ.toRingHom.comp ι.toRingHom))

theorem eq_one_of_isPerfect_of_mem_center {S : Type*} [Group S] (hS : Group.IsPerfect S)
    {σ : MulAut S} (h : ∀ s : S, s⁻¹ * σ s ∈ Subgroup.center S) : σ = 1 := by
  have hleft : ∀ x y z : S, y ∈ Subgroup.center S → ⁅x * y, z⁆ = ⁅x, z⁆ := by
    intro x y z hy
    rw [commutatorElement_mul_left_eq_conj_mul, commutatorElement_eq_one_iff_mul_comm.2
      (Subgroup.mem_center_iff.1 hy z).symm, mul_one, mul_inv_cancel, one_mul]
  have hright : ∀ x y z : S, z ∈ Subgroup.center S → ⁅x, y * z⁆ = ⁅x, y⁆ := by
    intro x y z hz
    rw [commutatorElement_mul_right_eq_mul_conj, commutatorElement_eq_one_iff_mul_comm.2
      (Subgroup.mem_center_iff.1 hz x), mul_one, mul_inv_cancel_right]
  have hle : commutator S ≤ fixedSubgroup S σ := by
    rw [commutator_eq_closure, Subgroup.closure_le]
    rintro _ ⟨x, y, rfl⟩
    show σ ⁅x, y⁆ = ⁅x, y⁆
    have hx : σ x = x * (x⁻¹ * σ x) := (mul_inv_cancel_left x (σ x)).symm
    have hy : σ y = y * (y⁻¹ * σ y) := (mul_inv_cancel_left y (σ y)).symm
    rw [map_commutatorElement, hx, hy, hleft _ _ _ (h x), hright _ _ _ (h y)]
  ext s
  exact hle (by rw [hS.commutator_eq_top]; exact Subgroup.mem_top s)

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

theorem eq_one_of_mem_innDiagSub_of_fixes_isPerfect (hF : L2Field F) (e : K ≃* L2 F)
    {τ : MulAut K} (hτD : τ ∈ innDiagSub e) {a : ℕ} (hτ : τ ^ 2 ^ a = 1)
    {M : Subgroup K} (hM : Group.IsPerfect M) (hM1 : M ≠ ⊥) (hfix : ∀ m ∈ M, τ m = m) :
    τ = 1 := by
  by_contra hτ1
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hτ)
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hτ1 (orderOf_eq_one_iff.1 (by rw [hk, pow_zero]))
  have h0 : orderOf τ ≠ 0 := by
    rw [hk]
    exact pow_ne_zero k two_ne_zero
  have h2 : 2 ∣ orderOf τ := by
    rw [hk]
    exact dvd_pow_self 2 hk0
  have hpow : ∀ j : ℕ, ∀ m ∈ M, (τ ^ j) m = m := by
    intro j
    induction j with
    | zero =>
      intro m _
      rw [pow_zero, MulAut.one_apply]
    | succ j ih =>
      intro m hm
      rw [pow_succ, MulAut.mul_apply, hfix m hm, ih m hm]
  exact hM1 (L2OddGroup.eq_bot_of_isPerfect_of_le_fixedSubgroup hF e
    ((innDiagSub e).pow_mem hτD _) (orderOf_pow_orderOf_div h0 h2) hM
    (fun m hm => hpow _ m hm))

theorem eq_one_of_fixes_isPerfect_of_card_prime (hF : L2Field F) (hFp : (Nat.card F).Prime)
    (e : K ≃* L2 F) {τ : MulAut K} {a : ℕ} (hτ : τ ^ 2 ^ a = 1)
    {M : Subgroup K} (hM : Group.IsPerfect M) (hM1 : M ≠ ⊥) (hfix : ∀ m ∈ M, τ m = m) :
    τ = 1 :=
  have := subsingleton_ringEquiv_of_card_prime hFp
  eq_one_of_mem_innDiagSub_of_fixes_isPerfect hF e
    ((mem_innDiagSub_iff e τ).2 (Subsingleton.elim _ _)) hτ hM hM1 hfix

theorem eq_one_of_fixes_isPerfect {S : Type} [Group S] [Finite S] {p : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (e : S ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField p 1))
    {σ : MulAut S} {a : ℕ} (hσ : σ ^ 2 ^ a = 1)
    {L : Subgroup S} (hL : Group.IsPerfect L) (hLZ : ¬ L ≤ Subgroup.center S)
    (hfix : ∀ l ∈ L, σ l = l) : σ = 1 := by
  have hcard : Nat.card (GaloisField p 1) = p := by
    rw [GaloisField.card p 1 one_ne_zero, pow_one]
  have hF : L2Field (GaloisField p 1) := by
    refine ⟨?_, ?_⟩
    · rw [hcard]
      exact (Fact.out : p.Prime).odd_of_ne_two (by omega)
    · rw [hcard]
      omega
  have hFp : (Nat.card (GaloisField p 1)).Prime := by
    rw [hcard]
    exact Fact.out
  set Z := Subgroup.center S
  let bar : MulAut S →* MulAut (S ⧸ Z) := MonoidHom.mk'
    (fun α => QuotientGroup.congr Z Z α (Subgroup.map_center_eq α))
    (fun α β => by
      ext x
      induction x using QuotientGroup.induction_on
      rfl)
  have hbar : ∀ (α : MulAut S) (s : S), bar α (s : S ⧸ Z) = ((α s : S) : S ⧸ Z) :=
    fun _ _ => rfl
  let e' : S ⧸ Z ≃* L2 (GaloisField p 1) :=
    (QuotientGroup.congr Z (Subgroup.center (SpecialLinearGroup (Fin 2) (GaloisField p 1))) e
      (Subgroup.map_center_eq e)).trans (L2.equivPSL (GaloisField p 1)).symm
  have hM : Group.IsPerfect (L.map (QuotientGroup.mk' Z)) := Group.IsPerfect.map _
  have hM1 : L.map (QuotientGroup.mk' Z) ≠ ⊥ := by
    rw [Ne, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hLZ
  have hσ1 : bar σ = 1 := by
    refine eq_one_of_fixes_isPerfect_of_card_prime hF hFp e' (a := a)
      (by rw [← map_pow, hσ, map_one]) hM hM1 ?_
    rintro _ ⟨l, hl, rfl⟩
    exact congrArg (QuotientGroup.mk' Z) (hfix l hl)
  have h1 : ∀ s : S, ((σ s : S) : S ⧸ Z) = (s : S ⧸ Z) := fun s => by
    rw [← hbar, hσ1, MulAut.one_apply]
  have : Group.IsPerfect (SpecialLinearGroup (Fin 2) (GaloisField p 1)) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card _ (by omega)
  exact eq_one_of_isPerfect_of_mem_center
    (Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective)
    fun s => QuotientGroup.eq.1 (h1 s).symm

end CFSG.RankThree.PartTwo.Sec20.SL2Aut
