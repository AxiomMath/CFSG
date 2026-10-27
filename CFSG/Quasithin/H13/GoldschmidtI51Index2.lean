module

public import Mathlib.GroupTheory.Index
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.Quasithin.H13.I51

theorem card_index_two {Q ι : Type*} [Group Q] [Finite Q] [Fintype ι] (K : ι → Subgroup Q)
    (hK : Function.Injective K) (h2 : ∀ i, (K i).index = 2) :
    (Fintype.card ι + 1) * Nat.card ↥(⨅ i, K i) ≤ Nat.card Q := by
  classical
  have : Fintype Q := Fintype.ofFinite Q
  let f : Q → (ι → ZMod 2) := fun q i => if q ∈ K i then 0 else 1
  have hf1 : f 1 = 0 := by
    ext i; simp [f]
  have hfm : ∀ a b, f (a * b) = f a + f b := by
    intro a b; ext i
    simp only [f, Pi.add_apply]
    have := Subgroup.mul_mem_iff_of_index_two (h2 i) (a := a) (b := b)
    by_cases ha : a ∈ K i <;> by_cases hb : b ∈ K i <;> simp [ha, hb, this]
    decide
  let Φ : Q →* Multiplicative (ι → ZMod 2) :=
    { toFun := fun q => Multiplicative.ofAdd (f q)
      map_one' := by simp [hf1]
      map_mul' := fun a b => by simp [hfm] }
  have hker : Φ.ker = ⨅ i, K i := by
    ext q
    simp only [MonoidHom.mem_ker, Subgroup.mem_iInf]
    constructor
    · intro h i
      have := congr_fun (Multiplicative.ofAdd.injective (show Multiplicative.ofAdd (f q) =
        Multiplicative.ofAdd (0 : ι → ZMod 2) from h)) i
      simpa [f] using this
    · intro h
      show Multiplicative.ofAdd (f q) = 1
      have : f q = 0 := by ext i; simp [f, h i]
      rw [this]; rfl
  let I : Submodule (ZMod 2) (ι → ZMod 2) :=
    { carrier := Set.range f
      add_mem' := by
        rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
        exact ⟨a * b, hfm a b⟩
      zero_mem' := ⟨1, hf1⟩
      smul_mem' := by
        rintro c _ ⟨a, rfl⟩
        rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
        · exact ⟨1, by simp [hf1]⟩
        · exact ⟨a, by simp⟩ }
  have hrange : Nat.card Φ.range = Nat.card I := by
    refine Nat.card_congr ?_
    exact Equiv.subtypeEquiv Multiplicative.toAdd (fun x => by
      constructor
      · rintro ⟨q, rfl⟩; exact ⟨q, rfl⟩
      · rintro ⟨q, hq⟩; exact ⟨q, by show Multiplicative.ofAdd (f q) = x; rw [hq]; rfl⟩)
  let e : ι → Module.Dual (ZMod 2) I := fun i => (LinearMap.proj i).comp I.subtype
  have hnz : ∀ i, e i ≠ 0 := by
    intro i h
    have hne : ∃ q : Q, q ∉ K i := by
      by_contra hcon
      push Not at hcon
      have : K i = ⊤ := (Subgroup.eq_top_iff' _).2 hcon
      have h1 := h2 i
      rw [this, Subgroup.index_top] at h1
      omega
    obtain ⟨q, hq⟩ := hne
    have := LinearMap.congr_fun h ⟨f q, ⟨q, rfl⟩⟩
    have h3 : (1 : ZMod 2) = 0 := by simp [e, f, hq] at this
    exact absurd h3 (by decide)
  have hinj : Function.Injective e := by
    intro i j hij
    by_contra hne
    have hKne : K i ≠ K j := fun h => hne (hK h)
    have hnle : ∀ a b : ι, K a ≠ K b → ¬ K a ≤ K b := by
      intro a b hab hle
      have h1 := Subgroup.relIndex_mul_index hle
      rw [h2 a, h2 b] at h1
      have h3 : (K a).relIndex (K b) = 1 := by omega
      exact hab (le_antisymm hle (Subgroup.relIndex_eq_one.1 h3))
    obtain ⟨q, hqi, hqj⟩ := IsConcreteLE.not_le_iff_exists.1 (hnle i j hKne)
    have := LinearMap.congr_fun hij ⟨f q, ⟨q, rfl⟩⟩
    have h3 : (0 : ZMod 2) = 1 := by simp [e, f, hqi, hqj] at this
    exact absurd h3 (by decide)
  have : Fintype I := Fintype.ofFinite I
  have hfin : Finite (Module.Dual (ZMod 2) I) :=
    Finite.of_injective (fun φ : Module.Dual (ZMod 2) I => (φ : I → ZMod 2)) DFunLike.coe_injective
  have : Fintype (Module.Dual (ZMod 2) I) := Fintype.ofFinite _
  have hdual : Fintype.card (Module.Dual (ZMod 2) I) = Fintype.card I := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2) (V := Module.Dual (ZMod 2) I),
      Module.card_eq_pow_finrank (K := ZMod 2) (V := I), Subspace.dual_finrank_eq]
  have hcard : Fintype.card ι + 1 ≤ Fintype.card I := by
    have h1 : (insert 0 (Finset.univ.image e)).card = Fintype.card ι + 1 := by
      rw [Finset.card_insert_of_notMem, Finset.card_image_of_injective _ hinj,
        Finset.card_univ]
      simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
      exact fun i h => hnz i h
    have h2' := Finset.card_le_univ (insert 0 (Finset.univ.image e))
    rw [h1, hdual] at h2'
    exact h2'
  have hmain := Subgroup.card_ker_mul_card_range Φ
  rw [hker, hrange, Nat.card_eq_fintype_card (α := I)] at hmain
  calc (Fintype.card ι + 1) * Nat.card ↥(⨅ i, K i) ≤ Fintype.card I * Nat.card ↥(⨅ i, K i) :=
        Nat.mul_le_mul_right _ hcard
    _ = Nat.card ↥(⨅ i, K i) * Fintype.card I := mul_comm _ _
    _ = Nat.card Q := hmain

end CFSG.Quasithin.H13.I51
