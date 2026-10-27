module

public import CFSG.YGroups.Exact.Model
public import CFSG.Certificates.NativeSchreierCard

public section

namespace CFSG.YGroups

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native

theorem card_arrClosure_of_rawChainOK {n : ℕ} (hn : 1 ≤ n) {O S : Array (Array ℕ)}
    {W : Array (List ℤ)} {base : List (Fin n)} (hb : base.Nodup) {chunks : ℕ} (hc : 0 < chunks)
    (hOS : O.size ≤ S.size) (hSO : ∀ i < O.size, S[i]! = O[i]!)
    (h : rawChainOK n (S.extract 0 O.size) S (base.map Fin.val).toArray W chunks = true) :
    Nat.card (arrClosure n O) = (rawOrbitSizes n S (base.map Fin.val).toArray).prod := by
  have hF := chainCheckFacts h
  have hA := chainArrays_ofArrays (hn := hn) (k := O.size) (hk := hOS) (hb := hb) (W := W)
    hF.strong_inv
  have hcard := card_originalSubgroup_of_chainOK hA hc h
  have hQ : (RawSchreierDatum.ofArrays n hn S O.size hOS base hb W).originalSubgroup =
      arrClosure n O := by
    unfold RawSchreierDatum.originalSubgroup arrClosure
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

end CFSG.YGroups
