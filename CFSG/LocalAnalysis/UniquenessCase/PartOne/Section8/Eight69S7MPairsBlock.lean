module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight69S7MPairsCheck
import CFSG.Quasithin.Recognition.CertChain

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.McLPairs

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four CFSG.AGLEmbedding.FusD2
open CFSG.RankThree.Native Certificates.McLFivePairs CFSG.Monster.B.Co2

private theorem sgsWords_length : sgsWords.length = 8 := by
  decide

private theorem mclB5_zero_closure : mclB5 0 = Subgroup.closure {g | g ∈ mclB0Gens} := by
  have hgen : mclBGens5 0 = mclB0Gens := by
    rw [mclBGens5, mclH5_zero]
    exact List.map_id'' (fun x => by simp) mclB0Gens
  show Subgroup.closure {g | g ∈ mclBGens5 (0 : ℕ)} = _
  rw [hgen]

private theorem closure_map_conj_mclB0Gens (c : Equiv.Perm (Fin 275)) :
    Subgroup.closure {g | g ∈ mclB0Gens.map (fun x => c⁻¹ * x * c)} =
      (Subgroup.closure {g | g ∈ mclB0Gens}).map (MulAut.conj c⁻¹).toMonoidHom := by
  rw [MonoidHom.map_closure]
  congr 1
  ext g
  simp only [Set.mem_ofPred_eq, Set.mem_image, List.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, by
      change MulAut.conj c⁻¹ x = c⁻¹ * x * c
      rw [MulAut.conj_apply, inv_inv]⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, by
      change c⁻¹ * x * c = MulAut.conj c⁻¹ x
      rw [MulAut.conj_apply, inv_inv]⟩

private theorem extract_getElem! {S : Array Tab} (h4 : 4 ≤ S.size) {k : ℕ} (hk : k < 4) :
    (S.extract 0 4)[k]! = S[k]! := by
  have hmin : k < min 4 S.size - 0 := by
    rw [Nat.min_eq_left h4, Nat.sub_zero]
    exact hk
  rw [Array.getElem!_eq_getD, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
    Array.getD_eq_getD_getElem?, Array.getElem?_extract, if_pos hmin, Nat.zero_add]

private theorem strongTabs_getElem! (b : Array Tab) {k : ℕ} (hk : k < sgsWords.length) :
    (strongTabs b)[k]! = wordIn b (sgsWords.getD k []) := by
  have h1 : (strongTabs b)[k]! = (sgsWords.map (wordIn b))[k]! := by
    rw [strongTabs, List.getElem!_toArray]
  have h2 : (sgsWords.map (wordIn b))[k]! = wordIn b (sgsWords.getD k []) := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hk,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
    rfl
  rw [h1, h2]

private theorem sgsWords_getD_lt_four {k : ℕ} (hk : k < 4) :
    sgsWords.getD k [] = (((k : ℤ) + 1) :: []) := by
  interval_cases k <;> decide

private theorem strongTabs_getElem!_lt_four (b : Array Tab) {k : ℕ} (hk : k < 4) :
    (strongTabs b)[k]! = wordIn b (((k : ℤ) + 1) :: []) := by
  rw [strongTabs_getElem! b (by rw [sgsWords_length]; omega), sgsWords_getD_lt_four hk]

private theorem wordVal_single {G : Type*} [Group G] (L : List G) (k : ℕ) :
    wordVal L (((k : ℤ) + 1) :: []) = L.getD k 1 := by
  rw [wordVal, if_pos (by positivity), Int.toNat_natCast_add_one, Nat.add_sub_cancel]
  show L.getD k 1 * 1 = L.getD k 1
  rw [mul_one]

theorem mclB5_zero :
    mclB5 0 = mclR5 ⊔ mclR5.map (MulAut.conj (mclRep5 95)⁻¹).toMonoidHom := by
  rw [mclB5_zero_closure, closure_four_eq_sup mclU5 mclV5 (mclRep5 95), mclR5_eq]

theorem mclB5_eq_map (k : Fin 3) :
    mclB5 k = (mclB5 0).map (MulAut.conj (mclH5 k)⁻¹).toMonoidHom := by
  have hk : mclB5 k = Subgroup.closure {g | g ∈ mclB0Gens.map
      (fun x => (mclH5 (k : ℕ))⁻¹ * x * mclH5 (k : ℕ))} := by
    show Subgroup.closure {g | g ∈ mclBGens5 ((k : Fin 3) : ℕ)} = _
    rw [mclBGens5]
  rw [mclB5_zero_closure, hk, closure_map_conj_mclB0Gens]

theorem mclB5_le (k : Fin 3) : mclB5 k ≤ mcl275P := by
  have hU : mclU5 ∈ mcl275P :=
    mclR5_le (by rw [mclR5_eq]; exact Subgroup.subset_closure (by simp))
  have hV : mclV5 ∈ mcl275P :=
    mclR5_le (by rw [mclR5_eq]; exact Subgroup.subset_closure (by simp))
  have hR : mclRep5 95 ∈ mcl275P := mclRep5_mem 95
  have hH : mclH5 (k : ℕ) ∈ mcl275P := mclN5_le (mclH5_mem (k : ℕ))
  have hB0 : ∀ x ∈ mclB0Gens, x ∈ mcl275P := by
    intro x hx
    rw [mclB0Gens, List.mem_cons, List.mem_cons, List.mem_cons, List.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact hU
    · exact hV
    · exact mcl275P.mul_mem (mcl275P.mul_mem (mcl275P.inv_mem hR) hU) hR
    · exact mcl275P.mul_mem (mcl275P.mul_mem (mcl275P.inv_mem hR) hV) hR
  rw [show mclB5 k = Subgroup.closure {g | g ∈ mclBGens5 (k : ℕ)} from rfl]
  refine (Subgroup.closure_le (K := mcl275P)).mpr ?_
  rintro x hx
  simp only [Set.mem_ofPred_eq, mclBGens5, List.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact mcl275P.mul_mem (mcl275P.mul_mem (mcl275P.inv_mem hH) (hB0 y hy)) hH

theorem card_closure_of_chainOK {b : Array Tab} {L : List (Equiv.Perm (Fin 275))}
    (hb : ∀ j, TabRep (b.getD j (idTab 275)) (L.getD j 1)) (hlen : L.length = 4)
    (h : chainOK b = true) : Nat.card (Subgroup.closure {g | g ∈ L}) = 126000 := by
  simp only [chainOK, Bool.and_eq_true] at h
  obtain ⟨⟨hgens, hraw⟩, horb⟩ := h
  set S : Array Tab := strongTabs b with hSdef
  have hSsize : S.size = 8 := by
    rw [hSdef, strongTabs]
    simp only [List.size_toArray, List.length_map]
    exact sgsWords_length
  have h8le : 4 ≤ S.size := by rw [hSsize]; omega
  have hOsize : (S.extract 0 4).size = 4 := by
    rw [Array.size_extract, hSsize]
    simp
  have hOS : (S.extract 0 4).size ≤ S.size := by rw [hOsize]; exact h8le
  have hSO : ∀ i < (S.extract 0 4).size, S[i]! = (S.extract 0 4)[i]! := by
    intro i hi
    rw [hOsize] at hi
    exact (extract_getElem! h8le hi).symm
  have hbase : (([0, 1, 2] : List (Fin 275)).map Fin.val).toArray = chainBase := by decide
  have hraw' : CFSG.Certificates.Native.rawChainOK 275 (S.extract 0 (S.extract 0 4).size) S
      (([0, 1, 2] : List (Fin 275)).map Fin.val).toArray sgsWords.toArray 4 = true := by
    rw [hOsize, hbase]
    exact hraw
  have hperm : ∀ k, k < 4 → permOfArr 275 (S.extract 0 4)[k]! = L.getD k 1 := by
    intro k hk
    have hO : (S.extract 0 4)[k]! = wordIn b (((k : ℤ) + 1) :: []) := by
      rw [extract_getElem! h8le hk, hSdef, strongTabs_getElem!_lt_four b hk]
    rw [hO, ← wordVal_single L k]
    exact permOfArr_eq_of_rep (rep_wordIn hb hgens (((k : ℤ) + 1) :: [])).2
  have hLget : ∀ (k : ℕ) (hk : k < L.length), L.getD k 1 = L[k]'hk := by
    intro k hk
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
    rfl
  have hset : {g : Equiv.Perm (Fin 275) | ∃ k < (S.extract 0 4).size,
      permOfArr 275 (S.extract 0 4)[k]! = g} = {g | g ∈ L} := by
    ext g
    constructor
    · rintro ⟨k, hk, rfl⟩
      have hk4 : k < 4 := hOsize ▸ hk
      have hkL : k < L.length := by omega
      rw [hperm k hk4, hLget k hkL]
      exact List.mem_iff_getElem.mpr ⟨k, hkL, rfl⟩
    · intro hg
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hg
      refine ⟨k, by rw [hOsize]; omega, ?_⟩
      rw [hperm k (by omega), hLget k hk]
  have hprod : (CFSG.Certificates.Native.rawOrbitSizes 275 S chainBase).prod = 126000 := by
    have horb' : CFSG.Certificates.Native.rawOrbitSizes 275 S chainBase = orbitLengths := by
      simpa using horb
    rw [horb', orbitLengths]
    decide
  have hcard := CFSG.Quasithin.card_closure_permOfArr_of_rawChainOK (n := 275) (by norm_num)
    (O := S.extract 0 4) (S := S) (W := sgsWords.toArray) (base := ([0, 1, 2] : List (Fin 275)))
    (hb := by decide) (chunks := 4) (by norm_num) hOS hSO hraw'
  rw [← hset]
  rw [hcard, hbase]
  exact hprod

theorem card_mclB5
    (k : Fin 3) :
    Nat.card (mclB5 k) = 126000 := by
  rw [mclB5_eq_map,
    Subgroup.card_map_of_injective (MulAut.conj (mclH5 k)⁻¹).injective, mclB5_zero_closure]
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hchain⟩ := mcl_pairs_check_spec
  exact card_closure_of_chainOK rep_mclB0T rfl hchain

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.McLPairs
