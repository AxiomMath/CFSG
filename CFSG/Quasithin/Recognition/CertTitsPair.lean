module

public import CFSG.Quasithin.Recognition.CertTitsSimple
public import CFSG.Sporadic.Schreier.PairChain

public noncomputable section

namespace CFSG.Quasithin

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative

@[expose] def titsPermA : Equiv.Perm (Fin 1755) := permOfArr 1755 titsA

@[expose] def titsPermB : Equiv.Perm (Fin 1755) := permOfArr 1755 titsB

attribute [local irreducible] titsPairO titsPairStrong titsGens titsStrong titsA titsB

private theorem titsPairO_size' : titsPairO.size = 2 := by simp [titsPairO]

private theorem titsPairO_zero' : titsPairO[0]! = titsA := by simp [titsPairO]

private theorem titsPairO_one' : titsPairO[1]! = titsB := by simp [titsPairO]

abbrev titsPairQ : RawSchreierDatum 1755 :=
  RawSchreierDatum.ofArrays 1755 (by norm_num) titsPairStrong titsPairO.size
    titsPair_check.2.2.2.2.1 titsPairBase (by decide) titsPairRawWords

theorem titsPairChainArrays :
    ChainArrays titsPairQ (titsPairStrong.extract 0 titsPairO.size) titsPairStrong
      (titsPairBase.map Fin.val).toArray titsPairRawWords :=
  chainArrays_ofArrays (chainCheckFacts titsPair_check.2.2.2.2.2.2.1).strong_inv

theorem titsPairQ_valid : ValidSchreier titsPairQ :=
  (validSchreier_of_chainOK titsPairChainArrays (by norm_num)
    titsPair_check.2.2.2.2.2.2.1).1

theorem titsPairQ_orbitSize (i : Fin titsPairQ.baseCount) :
    titsPairQ.orbitSize i = [1755, 10, 8, 2, 8, 4, 2].getD i.val 0 := by
  rw [(validSchreier_of_chainOK titsPairChainArrays (by norm_num)
    titsPair_check.2.2.2.2.2.2.1).2 i, ← titsPair_check.2.2.2.2.2.2.2.1, rawOrbitSizes,
    List.getD_eq_getElem?_getD, List.getElem?_map, Array.getElem?_toList]
  have h := congrArg List.length titsPair_check.2.2.2.2.2.2.2.1
  simp only [rawOrbitSizes, List.length_map, Array.length_toList] at h
  have hi : i.val < (rawLevels 1755 titsPairStrong (titsPairBase.map Fin.val).toArray).size := by
    have hb : i.val < 7 := i.2
    simp only [List.length_cons, List.length_nil] at h
    omega
  rw [Array.getElem?_eq_getElem hi,
    getElem!_pos (rawLevels 1755 titsPairStrong (titsPairBase.map Fin.val).toArray) i.val hi]
  rfl

theorem titsPairQ_base :
    titsPairQ.base.toList.map Fin.val = [0, 3, 1, 5, 6, 12, 24] := by
  rw [titsPairQ, RawSchreierDatum.ofArrays_base_toList]
  rfl

theorem titsPair_baseFaithful :
    BaseFaithful titsPairQ.originalSubgroup [0, 3, 1, 5, 6, 12, 24] := by
  have h := baseFaithful_of_valid titsPairQ_valid
  rwa [titsPairQ_base] at h

theorem titsPairQ_original :
    titsPairQ.originalSubgroup =
      Subgroup.closure {g | ∃ k < titsPairO.size, permOfArr 1755 titsPairO[k]! = g} := by
  obtain ⟨-, -, -, -, -, hSO, -⟩ := titsPair_check
  unfold RawSchreierDatum.originalSubgroup
  congr 1
  ext g
  rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, RawSchreierDatum.mem_ofArrays_original]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, by rw [hSO i hi]⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, by rw [hSO i hi]⟩

theorem titsPairQ_original' :
    titsPairQ.originalSubgroup =
      Subgroup.closure ({titsPermA, titsPermB} : Set (Equiv.Perm (Fin 1755))) := by
  rw [titsPairQ_original]
  congr 1
  ext g
  rw [Set.mem_ofPred_eq, titsPairO_size', Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨k, hk, rfl⟩
    interval_cases k
    · exact Or.inl (by rw [titsPairO_zero']; rfl)
    · exact Or.inr (by rw [titsPairO_one']; rfl)
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num, by rw [titsPairO_zero']; rfl⟩
    · exact ⟨1, by norm_num, by rw [titsPairO_one']; rfl⟩

theorem titsPairStrong_zero : titsPairStrong[0]! = titsA := by
  rw [(titsPair_check.2.2.2.2.2.1) 0 (by rw [titsPairO_size']; norm_num), titsPairO_zero']

theorem titsPairStrong_one : titsPairStrong[1]! = titsB := by
  rw [(titsPair_check.2.2.2.2.2.1) 1 (by rw [titsPairO_size']; norm_num), titsPairO_one']

theorem rep_titsPermA : Rep 1755 titsA titsPermA :=
  (rep_permOfArr titsPair_check.1).1

theorem rep_titsPermB : Rep 1755 titsB titsPermB :=
  (rep_permOfArr titsPair_check.2.1).1

theorem titsPermA_mem : titsPermA ∈ titsPairQ.originalSubgroup := by
  rw [titsPairQ_original']
  exact Subgroup.subset_closure (Set.mem_insert _ _)

theorem titsPermB_mem : titsPermB ∈ titsPairQ.originalSubgroup := by
  rw [titsPairQ_original']
  exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem card_titsPair_chain :
    Nat.card titsPairQ.originalSubgroup = 17971200 := by
  obtain ⟨-, -, -, -, hOS, hSO, hchain, horb, -⟩ := titsPair_check
  have := card_closure_permOfArr_of_rawChainOK (n := 1755) (by norm_num) (O := titsPairO)
    (S := titsPairStrong) (W := titsPairRawWords) (by decide) (chunks := 4) (by norm_num)
    hOS hSO hchain
  rw [horb] at this
  rw [titsPairQ_original, this]
  norm_num

theorem rep_powA_tits {t : Array ℕ} {g : Equiv.Perm (Fin 1755)} (ht : Rep 1755 t g) :
    ∀ d : Nat, Rep 1755 (powA 1755 t d) (g ^ d)
  | 0 => by
    rw [pow_zero]
    exact rep_idA
  | d + 1 => by
    rw [pow_succ']
    exact rep_compA ht (rep_powA_tits ht d)

theorem titsPermAB_pow : (titsPermA * titsPermB) ^ 13 = 1 :=
  eq_of_eqA (rep_powA_tits (rep_compA rep_titsPermA rep_titsPermB) 13) rep_idA
    titsPair_check.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem titsPermA_sq : titsPermA ^ 2 = 1 :=
  eq_of_eqA (rep_powA_tits rep_titsPermA 2) rep_idA titsPair_check.2.2.2.2.2.2.2.2.2.1

theorem titsPermB_cube : titsPermB ^ 3 = 1 :=
  eq_of_eqA (rep_powA_tits rep_titsPermB 3) rep_idA titsPair_check.2.2.2.2.2.2.2.2.2.2.2.1

theorem titsPerm_noncomm :
    titsPermA * titsPermB ≠ titsPermB * titsPermA := by
  intro h
  have h6 : (titsPermA * titsPermB) ^ 6 = 1 := by
    rw [(Commute.mul_pow h 6), show 6 = 2 * 3 by norm_num, pow_mul, titsPermA_sq, one_pow,
      show 2 * 3 = 3 * 2 by norm_num, pow_mul, titsPermB_cube, one_pow, one_mul]
  have h1 : titsPermA * titsPermB = 1 := by
    calc titsPermA * titsPermB
        = (titsPermA * titsPermB) ^ 13 * ((titsPermA * titsPermB) ^ 6)⁻¹ *
          ((titsPermA * titsPermB) ^ 6)⁻¹ := by group
      _ = 1 := by rw [titsPermAB_pow, h6]; group
  have e := (eqA_iff (rep_compA rep_titsPermA rep_titsPermB) rep_idA).2 h1
  rw [titsPair_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2] at e
  exact Bool.false_ne_true e

end CFSG.Quasithin
