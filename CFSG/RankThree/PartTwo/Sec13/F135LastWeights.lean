module

public import CFSG.RankThree.LocalRank.ElementaryTwoWeights
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG Subgroup
open CFSG.RankThree.LocalRank

abbrev l10a_commGroup {T : Type*} [Group T] (hT : ∀ t : T, t * t = 1) : CommGroup T :=
  { ‹Group T› with
    mul_comm := fun a b => by
      have ha : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hT a)
      have hb : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hT b)
      have hab : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right (hT (a * b))
      calc a * b = (a * b)⁻¹ := hab.symm
        _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
        _ = b * a := by rw [ha, hb] }

theorem l10a_two_nsmul {T : Type*} [Group T] (hT : ∀ t : T, t * t = 1) (x : Additive T) :
    (2 : ℕ) • x = 0 := by
  rw [two_nsmul]
  exact hT (Additive.toMul x)

theorem l10a_finrank {T : Type*} [CommGroup T] [Finite T] [Module (ZMod 2) (Additive T)] {n : ℕ}
    (hcard : Nat.card T = 2 ^ n) : Module.finrank (ZMod 2) (Additive T) = n := by
  haveI : Module.Finite (ZMod 2) (Additive T) := Module.Finite.of_finite
  have h : Nat.card (Additive T) = Nat.card (ZMod 2) ^ Module.finrank (ZMod 2) (Additive T) :=
    Module.natCard_eq_pow_finrank
  rw [Nat.card_congr Additive.toMul, Nat.card_zmod, hcard] at h
  exact (Nat.pow_right_injective (le_refl 2) h).symm

theorem l10a_dual_finite {T : Type*} [CommGroup T] [Finite T] [Module (ZMod 2) (Additive T)] :
    Finite (Module.Dual (ZMod 2) (Additive T)) :=
  Finite.of_injective (fun f : Module.Dual (ZMod 2) (Additive T) => (f : Additive T → ZMod 2))
    DFunLike.coe_injective

theorem l10a_subset {T : Type*} [CommGroup T] [Finite T] [Module (ZMod 2) (Additive T)]
    {W : Type*} [AddCommGroup W] [Module (ZMod 3) W] {n : ℕ}
    (hfin : Module.finrank (ZMod 2) (Additive T) = n) (ρ : Representation (ZMod 3) T W)
    (hspan : Submodule.span (ZMod 2) {χ | signWeightSpace ρ χ ≠ ⊥} = ⊤) :
    ∃ S : Finset (Module.Dual (ZMod 2) (Additive T)), S.card = n - 1 ∧
      ∀ χ ∈ S, signWeightSpace ρ χ ≠ ⊥ := by
  classical
  haveI := l10a_dual_finite (T := T)
  haveI : FiniteDimensional (ZMod 2) (Additive T) := Module.Finite.of_finite
  haveI := Fintype.ofFinite (Module.Dual (ZMod 2) (Additive T))
  set Λ : Finset (Module.Dual (ZMod 2) (Additive T)) :=
    Finset.univ.filter (fun χ => signWeightSpace ρ χ ≠ ⊥) with hΛdef
  have hΛ : (Λ : Set (Module.Dual (ZMod 2) (Additive T))) = {χ | signWeightSpace ρ χ ≠ ⊥} := by
    ext χ
    simp [hΛdef]
  have hle : n ≤ Λ.card := by
    have h1 : Module.finrank (ZMod 2)
        (Submodule.span (ZMod 2) (Λ : Set (Module.Dual (ZMod 2) (Additive T)))) ≤ Λ.card :=
      finrank_span_finset_le_card (R := ZMod 2) Λ
    rw [hΛ, hspan, finrank_top, Subspace.dual_finrank_eq, hfin] at h1
    exact h1
  obtain ⟨S, hSΛ, hScard⟩ := Finset.exists_subset_card_eq (show n - 1 ≤ Λ.card by omega)
  refine ⟨S, hScard, fun χ hχ => ?_⟩
  have h2 := hSΛ hχ
  rw [hΛdef, Finset.mem_filter] at h2
  exact h2.2

theorem l10a_ker_ne_bot {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {ι : Type*} [Fintype ι] (f : V →ₗ[K] (ι → K))
    (h : Fintype.card ι < Module.finrank K V) : LinearMap.ker f ≠ ⊥ := by
  apply LinearMap.ker_ne_bot_of_finrank_lt
  rw [Module.finrank_fintype_fun_eq_card]
  exact h

theorem l10a_common_kernel {T : Type*} [CommGroup T] [Finite T] [Module (ZMod 2) (Additive T)]
    {n : ℕ} (hfin : Module.finrank (ZMod 2) (Additive T) = n) (hn : 1 ≤ n)
    (S : Finset (Module.Dual (ZMod 2) (Additive T))) (hS : S.card = n - 1) :
    ∃ x : Additive T, x ≠ 0 ∧ ∀ χ ∈ S, χ x = 0 := by
  classical
  haveI : FiniteDimensional (ZMod 2) (Additive T) := Module.Finite.of_finite
  let f : Additive T →ₗ[ZMod 2] (S → ZMod 2) :=
    LinearMap.pi (fun χ : S => (χ.1 : Additive T →ₗ[ZMod 2] ZMod 2))
  have hker : LinearMap.ker f ≠ ⊥ := by
    apply l10a_ker_ne_bot f
    rw [hfin, Fintype.card_coe, hS]
    omega
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp hker
  refine ⟨x, hx0, fun χ hχ => ?_⟩
  have h := congrFun (LinearMap.mem_ker.mp hx) ⟨χ, hχ⟩
  simpa [f, LinearMap.pi_apply] using h

theorem l10a_fix {T : Type*} [CommGroup T] [Module (ZMod 2) (Additive T)]
    {W : Type*} [AddCommGroup W] [Module (ZMod 3) W] (ρ : Representation (ZMod 3) T W)
    (χ : Module.Dual (ZMod 2) (Additive T)) (x : Additive T) (hx : χ x = 0) :
    signWeightSpace ρ χ ≤ LinearMap.ker (ρ (Additive.toMul x) - 1) := by
  intro v hv
  have h := (mem_signWeightSpace ρ χ v).mp hv (Additive.toMul x)
  have hx' : χ (Additive.ofMul (Additive.toMul x)) = 0 := hx
  rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero, h, hx',
    ZMod.val_zero, pow_zero, one_smul]

theorem l10a_card_le {T : Type*} [CommGroup T] [Finite T] [Module (ZMod 2) (Additive T)]
    {W : Type*} [AddCommGroup W] [Module (ZMod 3) W] [FiniteDimensional (ZMod 3) W]
    (ρ : Representation (ZMod 3) T W) (hK : (2 : ZMod 3) ≠ 0)
    (S : Finset (Module.Dual (ZMod 2) (Additive T))) (hS : ∀ χ ∈ S, signWeightSpace ρ χ ≠ ⊥)
    (L : Submodule (ZMod 3) W) (hL : ∀ χ ∈ S, signWeightSpace ρ χ ≤ L) :
    S.card ≤ Module.finrank (ZMod 3) L := by
  haveI := Fintype.ofFinite T
  have hind : iSupIndep (fun χ : S => signWeightSpace ρ χ.1) :=
    (iSupIndep_signWeightSpace ρ hK).comp Subtype.val_injective
  have hne : ∀ χ : S, ∃ v : W, v ∈ signWeightSpace ρ χ.1 ∧ v ≠ 0 := fun χ =>
    Submodule.exists_mem_ne_zero_of_ne_bot (hS χ.1 χ.2)
  choose v hvmem hv0 using hne
  have hli : LinearIndependent (ZMod 3) v :=
    iSupIndep.linearIndependent (fun χ : S => signWeightSpace ρ χ.1) hind hvmem hv0
  have hvL : ∀ χ : S, v χ ∈ L := fun χ => hL χ.1 χ.2 (hvmem χ)
  have hw : LinearIndependent (ZMod 3) (fun χ : S => (⟨v χ, hvL χ⟩ : L)) :=
    LinearIndependent.of_comp L.subtype hli
  have h := hw.fintype_card_le_finrank
  rw [Fintype.card_coe] at h
  exact h

theorem l10a_core {T : Type*} [CommGroup T] [Finite T] [Module (ZMod 2) (Additive T)]
    {W : Type*} [AddCommGroup W] [Module (ZMod 3) W] [FiniteDimensional (ZMod 3) W]
    {n : ℕ} (hn : 1 ≤ n) (hfin : Module.finrank (ZMod 2) (Additive T) = n)
    (ρ : Representation (ZMod 3) T W) (hρ : Function.Injective ρ) :
    ∃ t : T, t ≠ 1 ∧ n - 1 ≤ Module.finrank (ZMod 3) (LinearMap.ker (ρ t - 1)) := by
  have hK : (2 : ZMod 3) ≠ 0 := by decide
  have hspan := (elementary_two_weight_decomposition hK ρ).2.2.1.mp hρ
  obtain ⟨S, hSc, hSne⟩ := l10a_subset hfin ρ hspan
  obtain ⟨x, hx0, hxS⟩ := l10a_common_kernel hfin hn S hSc
  have hcard := l10a_card_le ρ hK S hSne (LinearMap.ker (ρ (Additive.toMul x) - 1))
    (fun χ hχ => l10a_fix ρ χ x (hxS χ hχ))
  refine ⟨Additive.toMul x, ?_, ?_⟩
  · intro h
    apply hx0
    have h' : Additive.ofMul (Additive.toMul x) = Additive.ofMul 1 := congrArg Additive.ofMul h
    exact h'
  · rw [hSc] at hcard
    exact hcard

theorem L10a_lin {W : Type*} [AddCommGroup W] [Module (ZMod 3) W] [FiniteDimensional (ZMod 3) W]
    {T : Type*} [Group T] [Finite T] (hT : ∀ t : T, t * t = 1) {n : ℕ} (hn : 1 ≤ n)
    (hcard : Nat.card T = 2 ^ n) (ρ : Representation (ZMod 3) T W) (hρ : Function.Injective ρ) :
    ∃ t : T, t ≠ 1 ∧ n - 1 ≤ Module.finrank (ZMod 3) (LinearMap.ker (ρ t - 1)) := by
  letI : CommGroup T := l10a_commGroup hT
  letI : Module (ZMod 2) (Additive T) := AddCommGroup.zmodModule (n := 2) (l10a_two_nsmul hT)
  exact l10a_core hn (l10a_finrank hcard) ρ hρ

end CFSG.RankThree.PartTwo.Sec13.F135Last
