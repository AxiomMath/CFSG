module

public import Certificates.Certificate799751
public import CFSG.RankThree.PartTwo.Sec21.FF81Am6LSideCert
public import CFSG.Quasithin.H13.GoldschmidtSp62Base
public import CFSG.RankThree.PartTwo.Sec21.FF81Am6Grp

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.Am6.A2

open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.Quasithin.G2U
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII
open CFSG.RankThree.PartTwo.Sec21.FF81.Am6.A2Data
open CFSG.RankThree.PartTwo.Sec21.FF81.Am6.LSideData CFSG.RankThree.PartTwo.Sec21.FF81.Am6.LSide
open CFSG.Quasithin.H13.U3 (exists_eq_of_isConj centralizer_tH_eq)

section Parts

theorem a2_parts : xCheck = true ∧ scanCheck = true ∧ badCheck = true ∧ goodCheck = true ∧
    dCheck = true ∧ chainCheck = true := by
  have h : a2Check = true := Certificates.certificate799751
  simp only [a2Check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

end Parts

noncomputable def zS : H6 := ofCode (a2Z7, a2Z7I) (by decide +kernel)

theorem mat6_zS : mat6 zS = dec6 a2Z7 := mat6_ofCode _ _

def tauC : Fin 3 → List ℕ := ![a2Tau0, a2Tau1, a2Tau2]

theorem pair_tau (i : Fin 3) : pairCheck (tauC i, tauC i) = true := by
  fin_cases i <;> decide +kernel

noncomputable def tauH (i : Fin 3) : H6 := ofCode (tauC i, tauC i) (pair_tau i)

def xPairs (i : Fin 3) : List (List ℕ × List ℕ) := [(a2Z7, a2Z7I), (tauC i, tauC i)]

theorem xPairs_all (i : Fin 3) : (xPairs i).all pairCheck = true := by
  have h := pair_tau i
  simp only [xPairs, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  exact ⟨by decide +kernel, h⟩

theorem xPairs_map (i : Fin 3) : (xPairs i).map Prod.fst = a2XGens i := by
  fin_cases i <;> rfl

theorem genSet_xPairs (i : Fin 3) : genSet (xPairs i) (xPairs_all i) = {zS, tauH i} := by
  ext g
  simp only [genSet, xPairs, List.mem_cons, List.not_mem_nil, or_false, Set.mem_setOf_eq,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨cc, hm, rfl⟩
    rcases hm with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨_, Or.inl rfl, rfl⟩
    · exact ⟨_, Or.inr rfl, rfl⟩

noncomputable def Xs (i : Fin 3) : Subgroup H6 := Subgroup.closure {zS, tauH i}

theorem Xs_eq (i : Fin 3) : Xs i = Subgroup.closure (genSet (xPairs i) (xPairs_all i)) := by
  rw [Xs, genSet_xPairs]

section Tables

theorem closureOK_X (i : Fin 3) :
    closureOK ((xPairs i).map Prod.fst) (closureT ((xPairs i).map Prod.fst)) 168 = true := by
  have h := a2_parts.1
  simp only [xCheck, Bool.and_eq_true, List.all_eq_true] at h
  have := h.1.1.1.1 i (List.mem_finRange i)
  rw [xPairs_map]
  exact this

theorem card_Xs (i : Fin 3) : Nat.card (Xs i) = 168 := by
  rw [Xs_eq]
  exact card_closure_genSet _ _ _ (closureOK_X i)

theorem zS_mem_Xs (i : Fin 3) : zS ∈ Xs i := Subgroup.subset_closure (by simp)

theorem mem_Xs_of_found (i : Fin 3) {c : List ℕ} {u : H6} (hu : mat6 u = dec6 c)
    (hf : found (a2XTab i) (indexMap (a2XTab i)) c = true) : u ∈ Xs i := by
  obtain ⟨k, hk, hck⟩ := found_spec hf
  have hmem : c ∈ closureT ((xPairs i).map Prod.fst) := by
    rw [xPairs_map]
    rw [← hck]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk, Option.getD_some]
    exact Array.getElem_mem hk
  rw [Xs_eq]
  exact CFSG.Quasithin.H13.U3.mem_closure_of_mem_table (xPairs i) (xPairs_all i) 168
    (closureOK_X i) hmem hu

end Tables

theorem mem_image_closure_build (S : Set H6) (gens : List (List ℕ))
    (hS : mat6 '' S = {y | ∃ c ∈ gens, dec6 c = y}) (par : List (ℕ × ℕ)) {x : List ℕ}
    (hx : x ∈ build one6 mul6 gens par) :
    dec6 x ∈ mat6 '' (Subgroup.closure S : Set H6) := by
  have hcl : mat6 '' (Subgroup.closure S : Set H6) =
      (Submonoid.closure {y | ∃ c ∈ gens, dec6 c = y} :
        Set (Matrix (Fin 6) (Fin 6) (ZMod 2))) := by
    rw [← hS, ← MonoidHom.map_mclosure, Submonoid.coe_map,
      ← Subgroup.closure_toSubmonoid_of_finite]
    rfl
  rw [hcl]
  exact decode_mem_closure_build dec6 one6 mul6 gens dec6_one6 dec6_mul6 par x hx

theorem le_card_of_tabGe (S : Set H6) (gens : List (List ℕ))
    (hS : mat6 '' S = {y | ∃ c ∈ gens, dec6 c = y}) (n : ℕ) (par : List (ℕ × ℕ))
    (h : tabGe n (build one6 mul6 gens par) = true) :
    n ≤ Nat.card (Subgroup.closure S) := by
  set tab := build one6 mul6 gens par with htab
  simp only [tabGe, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hn, hdist⟩, hcanon⟩ := h
  have hex : ∀ t : Fin tab.size, ∃ g : H6, g ∈ Subgroup.closure S ∧
      mat6 g = dec6 (tab.getD t []) := fun t => by
    have hmem : tab.getD t [] ∈ tab := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem t.2, Option.getD_some]
      exact Array.getElem_mem t.2
    obtain ⟨g, hg, e⟩ := mem_image_closure_build S gens hS par hmem
    exact ⟨g, hg, e⟩
  choose g hg hge using hex
  have hinj : Function.Injective
      fun t : Fin tab.size => (⟨g t, hg t⟩ : Subgroup.closure S) := by
    intro t t' e
    have e' : g t = g t' := congrArg Subtype.val e
    have e'' : dec6 (tab.getD t []) = dec6 (tab.getD t' []) := by
      rw [← hge t, ← hge t', e']
    exact Fin.ext (distinctCheck_spec hdist t.2 t'.2
      (dec6_injective (allCheck_spec hcanon t.2) (allCheck_spec hcanon t'.2) e''))
  calc n ≤ tab.size := hn
    _ = Nat.card (Fin tab.size) := (Nat.card_fin _).symm
    _ ≤ Nat.card (Subgroup.closure S) := Nat.card_le_card_of_injective _ hinj

section Orbit

theorem exists_orbit_code {s : H6} (hs : orderOf s = 2) :
    ∃ (i : Fin 4) (k : ℕ), ∃ hk : k < (orbTab i).size,
      mat6 s = dec6 ((orbTab i).getD k []) ∧ canon6 ((orbTab i).getD k []) = true := by
  obtain ⟨i, g, hg⟩ := exists_conj_of_sylow_classes SH_isPGroup SH_index exists_conj_of_mem_SH hs
  have hconj : IsConj (tH i) s := isConj_iff.mpr ⟨g, hg.symm⟩
  have hcard : Nat.card (Subgroup.centralizer ({tH i} : Set H6)) * orbSize i =
      Nat.card H6 := by
    rw [centralizer_tH_eq, card_XH, card_H6]
    fin_cases i <;> rfl
  obtain ⟨k, hk⟩ := exists_eq_of_isConj (orbElt i) (orbElt_injective i) (orbElt_conj i) hcard hconj
  have hok := orbitsOK_parts i
  simp only [orbitOK, Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨hsize, -⟩, hcanon⟩ := hok
  have hk' : (k : ℕ) < (orbTab i).size := by rw [hsize]; exact k.2
  refine ⟨i, k, hk', ?_, allCheck_spec hcanon hk'⟩
  rw [← hk, mat6_orbElt i hk']

end Orbit

section Scan

theorem scan_sound {τ : H6} (h2 : τ * τ = 1) (h1 : τ ≠ 1) (h3 : (zS * τ) ^ 3 = 1)
    (h4 : zS * τ ≠ 1) :
    168 ≤ Nat.card (Subgroup.closure ({zS, τ} : Set H6)) ∧
      (Nat.card (Subgroup.closure ({zS, τ} : Set H6)) ≤ 168 →
        τ ∈ Xs 0 ∨ τ ∈ Xs 1 ∨ τ ∈ Xs 2) := by
  have hτ2 : orderOf τ = 2 := orderOf_eq_prime (by rw [pow_two]; exact h2) h1
  obtain ⟨i, k, hk, hcode, hcanon⟩ := exists_orbit_code hτ2
  set t := (orbTab i).getD k [] with ht
  have hone : scanOne (indexMap (a2XTab 0)) (indexMap (a2XTab 1)) (indexMap (a2XTab 2)) t =
      true := by
    have hscan := a2_parts.2.1
    simp only [scanCheck, Bool.and_eq_true] at hscan
    obtain ⟨⟨⟨h0, h1'⟩, h2'⟩, h3'⟩ := hscan
    fin_cases i
    · exact allCheck_spec h0 hk
    · exact allCheck_spec h1' hk
    · exact allCheck_spec h2' hk
    · exact allCheck_spec h3' hk
  have hwdec : dec6 (mul6 a2Z7 t) = mat6 (zS * τ) := by
    rw [dec6_mul6, map_mul, mat6_zS, hcode]
  have hthree : isThree (mul6 a2Z7 t) = true := by
    have hne : (mul6 a2Z7 t == one6) = false := by
      by_contra hcon
      have heq : mul6 a2Z7 t = one6 := by
        simpa using hcon
      apply h4
      apply mat6_injective
      rw [← hwdec, heq, dec6_one6, map_one]
    have hcube : mul6 (mul6 (mul6 a2Z7 t) (mul6 a2Z7 t)) (mul6 a2Z7 t) = one6 := by
      refine dec6_injective (canon6_mul6 _ _) canon6_one6 ?_
      rw [dec6_mul6, dec6_mul6, hwdec, ← map_mul, ← map_mul, ← pow_two, ← pow_succ, h3, map_one,
        dec6_one6]
    simp [isThree, hne, hcube]
  simp only [scanOne, hthree, Bool.not_true, Bool.false_or, Bool.and_eq_true,
    Bool.or_eq_true] at hone
  obtain ⟨hge168, hrest⟩ := hone
  have hS : mat6 '' ({zS, τ} : Set H6) = {y | ∃ c ∈ [a2Z7, t], dec6 c = y} := by
    ext y
    simp only [Set.image_insert_eq, Set.image_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff, mat6_zS, hcode, Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil,
      or_false, exists_eq_or_imp, exists_eq_left]
    exact or_congr eq_comm eq_comm
  have hle : ∀ n, tabGe n (capTab [a2Z7, t]) = true →
      n ≤ Nat.card (Subgroup.closure ({zS, τ} : Set H6)) := fun n hn =>
    le_card_of_tabGe {zS, τ} [a2Z7, t] hS n _ hn
  refine ⟨hle 168 hge168, fun hcard => ?_⟩
  have hmem : ∀ j : Fin 3, found (a2XTab j) (indexMap (a2XTab j)) t = true → τ ∈ Xs j :=
    fun j hf => mem_Xs_of_found j hcode hf
  rcases hrest with ((h169 | hf0) | hf1) | hf2
  · exact absurd (hle 169 h169) (by omega)
  · exact Or.inl (hmem 0 hf0)
  · exact Or.inr (Or.inl (hmem 1 hf1))
  · exact Or.inr (Or.inr (hmem 2 hf2))

end Scan

set_option maxRecDepth 100000 in
theorem g3_exists_involution (x : G3) (hx : x ^ 7 = 1) (hx1 : x ≠ 1) :
    ∃ t : G3, t * t = 1 ∧ t ≠ 1 ∧ (x * t) ^ 3 = 1 := by
  have h : ∀ x : G3, x ^ 7 = 1 → x ≠ 1 → ∃ t : G3, t * t = 1 ∧ t ≠ 1 ∧ (x * t) ^ 3 = 1 := by
    decide +kernel
  exact h x hx hx1

end CFSG.RankThree.PartTwo.Sec21.FF81.Am6.A2
