module

public import CFSG.Certificates.NativeSchreierCard
public import CFSG.Sporadic.Schreier.ONPermArr
public import Certificates.Data.CFSGNative.YGroups.ExactCheck

public section

namespace CFSG.Sporadic.HNOddCore

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
open CFSG.ONSchreier CFSG.ONSchreier.Native

@[expose] def arrGen (n : ℕ) (O : Array (Array ℕ)) : Subgroup (Equiv.Perm (Fin n)) :=
  Subgroup.closure {g | ∃ k < O.size, Monster.B.Co2.permOfArr n O[k]! = g}

@[expose] def strongArrs (n : Nat) (O : Array (Array Nat)) (W : Array (List Int)) :
    Array (Array Nat) :=
  (CFSG.YGroups.ModelNative.strongOf n O (W.extract O.size W.size)).1

@[expose] def chainCheck (n : Nat) (O : Array (Array Nat)) (W : Array (List Int))
    (base : List (Fin n)) (sizes : List Nat) : Bool :=
  decide (O.size ≤ (strongArrs n O W).size) &&
    (allBelowN O.size fun i => (strongArrs n O W)[i]! == O[i]!) &&
    rawChainOK n ((strongArrs n O W).extract 0 O.size) (strongArrs n O W)
      (base.map Fin.val).toArray W 4 &&
    rawOrbitSizes n (strongArrs n O W) (base.map Fin.val).toArray == sizes

theorem card_arrGen_of_chainCheck {n : ℕ} (hn : 1 ≤ n) {O : Array (Array ℕ)}
    {W : Array (List ℤ)} {base : List (Fin n)} {sizes : List ℕ} (hb : base.Nodup)
    (h : chainCheck n O W base sizes = true) : Nat.card (arrGen n O) = sizes.prod := by
  unfold chainCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨hOS, h2⟩, h3⟩, h4⟩ := h
  have hSO : ∀ i < O.size, (strongArrs n O W)[i]! = O[i]! := fun i hi => by
    simpa using allBelowN_spec h2 hi
  rw [← h4]
  have hF := chainCheckFacts h3
  have hA := chainArrays_ofArrays (hn := hn) (k := O.size) (hk := hOS) (hb := hb) (W := W)
    hF.strong_inv
  have hcard := card_originalSubgroup_of_chainOK hA (by norm_num) h3
  have hQ : (RawSchreierDatum.ofArrays n hn (strongArrs n O W) O.size hOS base hb
      W).originalSubgroup = arrGen n O := by
    unfold RawSchreierDatum.originalSubgroup arrGen
    congr 1
    ext g
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, RawSchreierDatum.mem_ofArrays_original]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, hi, by rw [hSO i hi]⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, hi, by rw [hSO i hi]⟩
  rw [← hQ]
  exact hcard

theorem permOfArr_eq_of_prep {n : ℕ} {t : Array ℕ} {g : Equiv.Perm (Fin n)} (ht : PRep n t g) :
    Monster.B.Co2.permOfArr n t = g := by
  have hc : (∀ i < n, t[i]! < n) ∧ ∀ i < n, ∀ j < n, t[i]! = t[j]! → i = j := by
    refine ⟨fun i hi => by rw [ht ⟨i, hi⟩]; exact (g _).2, fun i hi j hj hij => ?_⟩
    rw [ht ⟨i, hi⟩, ht ⟨j, hj⟩] at hij
    exact congrArg Fin.val (g.injective (Fin.ext hij))
  apply Equiv.ext
  intro x
  rw [Monster.B.Co2.permOfArr, dite_eq_left hc]
  exact Fin.ext (ht x)

theorem arrGen_eq {n : ℕ} {O : Array (Array ℕ)} {σ : ℕ → Equiv.Perm (Fin n)}
    (hO : ∀ k < O.size, PRep n O[k]! (σ k)) :
    arrGen n O = Subgroup.closure (Set.range fun k : Fin O.size => σ k) := by
  unfold arrGen
  congr 1
  ext g
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k, hk⟩, (permOfArr_eq_of_prep (hO k hk)).symm⟩
  · rintro ⟨⟨k, hk⟩, rfl⟩
    exact ⟨k, hk, permOfArr_eq_of_prep (hO k hk)⟩

end CFSG.Sporadic.HNOddCore
