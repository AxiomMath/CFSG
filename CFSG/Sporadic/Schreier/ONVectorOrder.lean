module

public import CFSG.Sporadic.Schreier.ONSchreierData
public import CFSG.Sporadic.Schreier.ONCompactSpec
public import CFSG.Sporadic.Schreier.ONCheckChain
public import CFSG.Certificates.SchreierPointSiftSoundness
public import Certificates.Certificate2212
public import Certificates.Certificate2217
public import Certificates.Certificate3171
public import CFSG.Sporadic.ON.Lines
public import CFSG.Sporadic.Th.F2Spec

public noncomputable section

namespace CFSG.ONSchreier

open CFSG.Sporadic.ON CFSG.Sporadic.ON.Native CFSG.ONSchreier.Native CFSG.Certificates
open CFSG.Sporadic.Th.Native

theorem qonStrongArrs_eq :
    qonStrongArrs = strongArrs nPts (natTab vectorOrbit.alpha) (natTab vectorOrbit.beta)
      Data.strongWords := by
  rw [qonStrongArrs, vectorOrbit_def]

theorem strong_parts : qonStrongArrs.size = 7 ∧
    peq nPts qonStrongArrs[0]! (natTab vectorOrbit.alpha) = true ∧
    peq nPts qonStrongArrs[1]! (natTab vectorOrbit.beta) = true := by
  have h := vectorFacts.strong
  rw [← qonStrongArrs_eq] at h
  unfold strongOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨-, h1⟩, h2⟩, h3⟩, -⟩, -⟩ := h
  exact ⟨by rw [h1, words_facts.1], h2, h3⟩

theorem natTab_getElem! {t : Table} {i : ℕ} (hi : i < t.size) : (natTab t)[i]! = ap t i := by
  rw [natTab, getElem!_pos _ i (by simpa using hi), Array.getElem_map, ap,
    getElem!_pos t i hi]

theorem prep_a0 :
    PRep N (natTab vectorOrbit.alpha) a0 := fun x => by
  rw [natTab_getElem! (by rw [vparts.2.1]; exact x.isLt), a0_apply, f0_eq x.isLt]

theorem prep_a1 :
    PRep N (natTab vectorOrbit.beta) a1 := fun x => by
  rw [natTab_getElem! (by rw [vparts.2.2.1]; exact x.isLt), a1_apply, f1_eq x.isLt]

theorem baseArr_size : Data.baseList.toArray.size = 29 := by simp [base_facts.1]

theorem qon_arrays :
    CArrays QON 2 qonStrongArrs Data.baseList.toArray Data.strongWords := by
  refine ⟨rfl, by rw [strong_parts.1]; exact words_facts.1.symm, by
    rw [baseArr_size]; exact baseFin_length.symm, fun j hj => ?_, fun i => ?_, fun _ _ => rfl,
    ofWords_initial, ofWords_words⟩
  · rw [show QON.strong.get j = sgen j from ofWords_strong_get j]
    interval_cases hv : j.val
    · rw [sgen, wordStrong_of_lt _ _ (by simp)]
      exact prep_of_peq strong_parts.2.1 prep_a0
    · rw [sgen, wordStrong_of_lt _ _ (by simp)]
      exact prep_of_peq strong_parts.2.2 prep_a1
  · have hi : i.val < 29 := by
      have := i.isLt
      have h29 : QON.baseCount = 29 := baseFin_length
      omega
    rw [cert_on_schreier_action_data.2.2.2.2.2.2.2.2.1 i, getElem!_pos _ _ (by
      simp [base_facts.1]; exact hi), List.getElem_toArray, baseIndex_eq hi]

theorem qon_point :
    ValidPointSchreier QON ∧ ∀ i : Fin QON.baseCount,
    QON.orbitSize i = (CArrays.lev nPts qonStrongArrs Data.baseList.toArray i).pts.size :=
  validPointSchreier_of_pointChainOK qon_arrays (by norm_num) qon_chain_cert.1

theorem qon_originalSubgroup :
    QON.originalSubgroup = Pv := by
  rw [RawSchreierDatum.originalSubgroup, cert_on_schreier_action_data.2.2.2.1, Pv]
  congr 1
  ext x
  simp

theorem qon_base_set :
    {b | b ∈ QON.base.toList} = baseSet := by
  have h29 : QON.baseCount = 29 := baseFin_length
  ext x
  show x ∈ QON.base.toList ↔ ∃ k < 29, (x : ℕ) = baseIndex k
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := (schreier_vector_mem_toList_iff_get QON.base x).1 hx
    refine ⟨i.val, by have := i.isLt; omega, ?_⟩
    rw [← hi, cert_on_schreier_action_data.2.2.2.2.2.2.2.2.1 i]
  · rintro ⟨k, hk, hx⟩
    apply (schreier_vector_mem_toList_iff_get QON.base x).2
    refine ⟨⟨k, by omega⟩, Fin.ext ?_⟩
    rw [cert_on_schreier_action_data.2.2.2.2.2.2.2.2.1, hx]

theorem qon_stab :
    QON.originalSubgroup ⊓
    fixingSubgroup (Equiv.Perm (Fin N)) {b | b ∈ QON.base.toList} = ⊥ := by
  rw [qon_originalSubgroup, qon_base_set]
  exact pv_inf_fixing_base

theorem qon_valid :
    ValidSchreier QON :=
  (QON.certified_base_point_sift_soundness qon_point.1 qon_stab).1

theorem qon_baseCount :
    QON.baseCount = 29 := baseFin_length

theorem levelsOf_qon_size :
    (levelsOf nPts qonStrongArrs Data.baseList.toArray).size = 29 := by
  rw [CArrays.levelsOf_size, baseArr_size]

theorem qon_orbit_sizes :

    (List.finRange QON.baseCount).map (fun i => Nat.card (QON.orbitPoints i))
    = [245520, 52136, 36] ++ List.replicate 26 1 := by
  rw [← qon_chain_cert.2, cOrbitSizes]
  apply List.ext_getElem (by simp [qon_baseCount, levelsOf_qon_size])
  intro k h1 h2
  simp only [List.getElem_map, List.getElem_finRange, Array.getElem_toList]
  rw [← QON.orbitSize_eq_card, qon_point.2]
  simp only [CArrays.lev, Fin.val_cast]
  rw [getElem!_pos _ k (by simpa [levelsOf_qon_size, qon_baseCount] using h1)]

theorem qon_card_orbit
    (i : Fin QON.baseCount) :
    Nat.card (QON.orbitPoints i) = ([245520, 52136, 36] ++ List.replicate 26 1)[i.val]'(by
      simpa [qon_baseCount] using i.isLt) := by
  have hlen : i.val < ((List.finRange QON.baseCount).map
      fun i => Nat.card (QON.orbitPoints i)).length := by simp
  have := List.getElem_of_eq qon_orbit_sizes hlen
  simpa using this

theorem card_Pv :
    Nat.card Pv = 460815505920 := by
  rw [← qon_originalSubgroup, QON.original_card_eq_orbit_product qon_valid, Fin.prod_univ_def]
  rw [qon_orbit_sizes]
  decide

theorem qon_base_take_one :
    {b | b ∈ QON.base.toList.take 1} = ({(⟨0, by norm_num⟩ : Fin N)} : Set (Fin N)) := by
  ext x
  have h0 : QON.base.toList.take 1 = [⟨0, by norm_num⟩] := by
    have hb : QON.base.toList = baseFin := by simp [QON, RawSchreierDatum.ofWords]
    rw [hb, baseFin]
    decide
  simp [h0]

theorem card_Pv_stab_zero :
    Nat.card (Pv ⊓ fixingSubgroup (Equiv.Perm (Fin N)) {(⟨0, by norm_num⟩ : Fin N)} : Subgroup _) =
      1876896 := by
  have hl := QON.levelSubgroup_eq_pointwise_stabilizer qon_valid 1 (by rw [qon_baseCount]; omega)
  rw [qon_originalSubgroup, qon_base_take_one] at hl
  rw [← hl, QON.level_card_eq_orbit_product qon_valid 1 (by rw [qon_baseCount]; omega)]
  have h := qon_orbit_sizes
  have e : ((List.finRange QON.baseCount).drop 1).map (fun j => Nat.card (QON.orbitPoints j)) =
      ((List.finRange QON.baseCount).map fun j => Nat.card (QON.orbitPoints j)).drop 1 := by
    rw [List.map_drop]
  rw [e, h]
  decide

theorem fam_on_vector_schreier_order :
    ValidPointSchreier QON ∧ ValidSchreier QON ∧
      (List.finRange QON.baseCount).map (fun i => Nat.card (QON.orbitPoints i)) =
        [245520, 52136, 36] ++ List.replicate 26 1 ∧
      Nat.card Pv = 460815505920 ∧
      Nat.card (Pv ⊓ fixingSubgroup (Equiv.Perm (Fin N)) {(⟨0, by norm_num⟩ : Fin N)} :
        Subgroup _) = 1876896 ∧
      Nat.card Blueprint.NativeSporadic.ON = 460815505920 ∧ Nat.card J = 460815505920 :=
  ⟨qon_point.1, qon_valid, qon_orbit_sizes, card_Pv, card_Pv_stab_zero,
    by rw [Nat.card_congr onEquivPv.toEquiv, card_Pv],
    by rw [Nat.card_congr jEquivPv.toEquiv, card_Pv]⟩

end CFSG.ONSchreier
