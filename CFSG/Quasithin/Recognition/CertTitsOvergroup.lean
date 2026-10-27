module

public import CFSG.Sporadic.Schreier.TitsPair
public import CFSG.Quasithin.Recognition.CertTitsOvergroupCheck

public noncomputable section

namespace CFSG.Quasithin

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.Tits

abbrev titsSD : Subgroup titsD := titsS.subgroupOf titsD

abbrev titsHD : Subgroup titsD := titsH.subgroupOf titsD

abbrev titsND : Subgroup titsD := titsN.subgroupOf titsD

theorem titsSD_eq_flagStab
    : titsSD = titsFlagStab := by
  show titsS.subgroupOf titsD = titsFlagStab
  rw [titsS_eq_stab]
  exact map_subgroupOf_titsD _

theorem mem_titsSD_iff
    (g : titsD) : g ∈ titsSD ↔ titsDFlagAct g 0 = 0 := by
  rw [titsSD_eq_flagStab]
  exact Iff.rfl

@[expose] def titsSFlagGen (i : ℕ) : Equiv.Perm (Fin 8775) :=
  wordIn 13 titsTFlag (titsSWords.getD i [])

@[expose] def titsOverRep (c : ℕ) : Fin 8775 := finPt 8775 titsOverReps[c]!

theorem titsSFlagArrs_size
    : titsSFlagArrs.size = 3 := titsOver_check.1

theorem titsSWords_length : titsSWords.length = 3 := rfl

theorem titsSFlag_rep
    : ∀ i < titsSFlagArrs.size,
    Rep 8775 titsSFlagArrs[i]! (titsSFlagGen i) := by
  intro i hi
  rw [titsSFlagArrs_size] at hi
  have hi' : i < titsSWords.length := by rw [titsSWords_length]; exact hi
  have e : titsSFlagArrs[i]! = wordArr 8775 titsTFlagArrs titsSWords[i] := by
    rw [titsSFlagArrs, getElem!_pos _ i (by simpa [titsSWords_length] using hi)]
    simp
  rw [e, titsSFlagGen, getD_eq_get hi']
  exact rep_wordArr_tflag (titsLocalWords_letters titsLocalWords_mem.2.1 (List.getElem_mem _))

theorem titsSFlagGen_mem
    {i : ℕ} (hi : i < titsSWords.length) :
    ∃ s ∈ titsSD, titsDFlagAct s = titsSFlagGen i := by
  have hw : wordIn 13 titsT titsSWords[i] ∈ titsS :=
    Subgroup.subset_closure ⟨titsSWords[i], List.getElem_mem hi, rfl⟩
  refine ⟨⟨wordIn 13 titsT titsSWords[i], wordIn_titsT_mem_titsD _⟩, hw, ?_⟩
  rw [titsDFlagAct_word, titsSFlagGen, getD_eq_get hi]

theorem genGroup_titsSFlag_le
    :
    genGroup titsSFlagArrs titsSFlagGen ≤ titsSD.map titsDFlagAct := by
  rw [genGroup, Subgroup.closure_le]
  rintro _ ⟨i, hi, rfl⟩
  have hi' : i < titsSWords.length := by
    rw [titsSWords_length]
    simpa [titsSFlagArrs_size] using hi
  obtain ⟨s, hs, e⟩ := titsSFlagGen_mem hi'
  exact ⟨s, hs, e⟩

theorem titsOver_orbitOK :
    orbitLabelOK 8775 titsSFlagArrs 18 titsOverForest.1 titsOverReps.toArray titsOverForest.2.1
      titsOverForest.2.2.1 titsOverForest.2.2.2 = true := titsOver_check.2.2.1

theorem titsOver_lab_lt
    (x : Fin 8775) : titsOverForest.1[(x : ℕ)]! < 18 :=
  (orbitLabelOK_parts titsOver_orbitOK).1 x x.2

theorem titsOver_rep_lt
    {c : ℕ} (hc : c < 18) : titsOverReps[c]! < 8775 := by
  have := ((orbitLabelOK_parts titsOver_orbitOK).2.2.1 c hc).1
  simpa using this

theorem titsOver_orbit
    {c : ℕ} (hc : c < 18) {x : Fin 8775} (hx : titsOverForest.1[(x : ℕ)]! = c) :
    ∃ s ∈ titsSD, titsDFlagAct s (titsOverRep c) = x := by
  have h := orbit_eq_label titsOver_orbitOK titsSFlag_rep hc
  have hx' : x ∈ {y : Fin 8775 | titsOverForest.1[(y : ℕ)]! = c} := hx
  rw [← h] at hx'
  obtain ⟨⟨g, hg⟩, hgx⟩ := hx'
  obtain ⟨s, hs, rfl⟩ := genGroup_titsSFlag_le hg
  refine ⟨s, hs, ?_⟩
  rw [← hgx]
  have e : titsOverRep c = (⟨(titsOverReps.toArray)[c]! % 8775,
      Nat.mod_lt _ (by have := titsOver_rep_lt hc; omega)⟩ : Fin 8775) := by
    apply Fin.ext
    simp [titsOverRep, finPt]
  rw [e]
  rfl

theorem titsOver_cover
    (x : Fin 8775) :
    ∃ c < 18, ∃ s ∈ titsSD, titsDFlagAct s (titsOverRep c) = x :=
  ⟨_, titsOver_lab_lt x, titsOver_orbit (titsOver_lab_lt x) rfl⟩

theorem titsOverRep_zero : titsOverRep 0 = 0 := rfl

theorem titsOverRep_one : titsOverRep 1 = 1 := rfl

theorem titsOverRep_two : titsOverRep 2 = 2 := rfl

theorem titsOver_fixed
    {y : Fin 8775} (hy : ∀ s ∈ titsSD, titsDFlagAct s y = y) : y = 0 := by
  obtain ⟨c, hc, s₀, hs₀, hsy⟩ := titsOver_cover y
  have hrep : titsOverRep c = y := by
    have h1 : titsDFlagAct s₀⁻¹ y = y := hy _ (inv_mem hs₀)
    rw [← hsy, ← Equiv.Perm.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Equiv.Perm.one_apply] at h1
    exact h1.trans hsy
  by_cases hc0 : c = 0
  · rw [← hrep, hc0]
    exact titsOverRep_zero
  · exfalso
    obtain ⟨i, hi, hne⟩ := titsOver_check.2.2.2.2.2.2.1 c hc hc0
    have hi' : i < titsSWords.length := by rw [titsSWords_length]; exact hi
    obtain ⟨s, hs, e⟩ := titsSFlagGen_mem hi'
    have hfix : titsSFlagGen i (titsOverRep c) = titsOverRep c := by
      rw [← e, hrep]
      exact hy s hs
    apply hne
    have hrepi := titsSFlag_rep i (by rw [titsSFlagArrs_size]; exact hi)
    exact (wordArr_fix_iff hrepi (titsOver_rep_lt hc)).2 hfix

theorem titsSD_normalizer_le
    : Subgroup.normalizer (titsSD : Set titsD) ≤ titsSD := by
  intro g hg
  rw [mem_titsSD_iff]
  apply titsOver_fixed
  intro s hs
  have h1 : g⁻¹ * s * g ∈ titsSD := by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hg) s).1 hs
    simpa using this
  have h2 := (mem_titsSD_iff _).1 h1
  rw [map_mul, map_mul, map_inv, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
    Equiv.Perm.inv_eq_iff_eq] at h2
  exact h2

@[expose] def titsOverRel
    (X : Subgroup titsD) (u v : Fin 8775) : Prop :=
  ∃ g h : titsD, titsDFlagAct g 0 = u ∧ titsDFlagAct h 0 = v ∧ g⁻¹ * h ∈ X

theorem titsOverRel_equiv
    {X : Subgroup titsD} (hX : titsSD ≤ X) : Equivalence (titsOverRel X) := by
  refine ⟨fun u => ?_, fun ⟨g, h, hg, hh, hgh⟩ => ⟨h, g, hh, hg, ?_⟩, ?_⟩
  · obtain ⟨g, hg⟩ := titsDFlag_transitive u
    exact ⟨g, g, hg, hg, by simp⟩
  · simpa using X.inv_mem hgh
  · rintro u v w ⟨g, h, hg, hh, hgh⟩ ⟨h', k, hh', hk, hh'k⟩
    have hs : h⁻¹ * h' ∈ titsSD := by
      rw [mem_titsSD_iff, map_mul, map_inv, Equiv.Perm.mul_apply, hh', ← hh]
      exact perm_inv_apply _ _
    refine ⟨g, k, hg, hk, ?_⟩
    have := X.mul_mem (X.mul_mem hgh (hX hs)) hh'k
    simpa [mul_assoc] using this

theorem titsOverRel_inv
    {X : Subgroup titsD} (a : titsD) {u v : Fin 8775}
    (h : titsOverRel X u v) : titsOverRel X (titsDFlagAct a u) (titsDFlagAct a v) := by
  obtain ⟨g, h, hg, hh, hgh⟩ := h
  refine ⟨a * g, a * h, ?_, ?_, ?_⟩
  · rw [map_mul, Equiv.Perm.mul_apply, hg]
  · rw [map_mul, Equiv.Perm.mul_apply, hh]
  · simpa [mul_assoc] using hgh

theorem titsOverRel_base
    {X : Subgroup titsD} (hX : titsSD ≤ X) {n : titsD}
    (h : titsOverRel X 0 (titsDFlagAct n 0)) : n ∈ X := by
  obtain ⟨g, k, hg, hk, hgk⟩ := h
  have hgS : g ∈ titsSD := (mem_titsSD_iff g).2 hg
  have hkX : k ∈ X := by
    have := X.mul_mem (hX hgS) hgk
    simpa using this
  have hnk : k⁻¹ * n ∈ titsSD := by
    rw [mem_titsSD_iff, map_mul, map_inv, Equiv.Perm.mul_apply, ← hk]
    exact perm_inv_apply _ _
  have := X.mul_mem hkX (hX hnk)
  simpa using this

theorem titsOverRel_of_mem
    {X : Subgroup titsD} {x : titsD} (hx : x ∈ X) :
    titsOverRel X 0 (titsDFlagAct x 0) :=
  ⟨1, x, by simp, rfl, by simpa using hx⟩

theorem titsOverRel_smul_S
    {X : Subgroup titsD} {s : titsD} (hs : s ∈ titsSD) {u : Fin 8775}
    (h : titsOverRel X 0 u) : titsOverRel X 0 (titsDFlagAct s u) := by
  have := titsOverRel_inv s h
  rwa [(mem_titsSD_iff s).1 hs] at this

theorem titsOverRel_orbit
    {X : Subgroup titsD} {c : ℕ} (hc : c < 18) {x : Fin 8775}
    (hx : titsOverForest.1[(x : ℕ)]! = c) (h : titsOverRel X 0 (titsOverRep c)) :
    titsOverRel X 0 x := by
  obtain ⟨s, hs, rfl⟩ := titsOver_orbit hc hx
  exact titsOverRel_smul_S hs h

theorem titsHD_le_of_rel
    {X : Subgroup titsD} (hX : titsSD ≤ X) (h2 : titsOverRel X 0 2) :
    titsHD ≤ X := by
  intro n hn
  apply titsOverRel_base hX
  have hF : titsDFlagAct n 0 ∈ titsF5 := by
    have h0 : (0 : Fin 8775) ∈ titsF5 := by rw [titsF5_eq]; simp
    exact (titsHFlag_mem ⟨(n : Equiv.Perm (Fin 1755)), hn⟩ 0).2 h0
  rw [titsF5_eq] at hF
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hF
  have hrel : ∀ x : Fin 8775, titsOverForest.1[(x : ℕ)]! = 2 → titsOverRel X 0 x := fun x hx =>
    titsOverRel_orbit (by norm_num) hx (by rw [titsOverRep_two]; exact h2)
  rcases hF with h | h | h | h | h <;> rw [h]
  · exact (titsOverRel_equiv hX).refl 0
  · exact h2
  · exact hrel _ titsOver_check.2.2.2.2.2.1.2.1
  · exact hrel _ titsOver_check.2.2.2.2.2.1.2.2.1
  · exact hrel _ titsOver_check.2.2.2.2.2.1.2.2.2

theorem titsND_le_of_rel
    {X : Subgroup titsD} (hX : titsSD ≤ X) (h1 : titsOverRel X 0 1) :
    titsND ≤ X := by
  intro n hn
  apply titsOverRel_base hX
  have hF : titsDFlagAct n 0 ∈ titsF3 := by
    have h0 : (0 : Fin 8775) ∈ titsF3 := by rw [titsF3_eq]; simp
    exact (titsNFlag_mem ⟨(n : Equiv.Perm (Fin 1755)), hn⟩ 0).2 h0
  rw [titsF3_eq] at hF
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hF
  rcases hF with h | h | h <;> rw [h]
  · exact (titsOverRel_equiv hX).refl 0
  · exact h1
  · exact titsOverRel_orbit (c := 1) (by norm_num) titsOver_check.2.2.2.2.1.2
      (by rw [titsOverRep_one]; exact h1)

theorem titsOverRel_merge
    {X : Subgroup titsD} (hX : titsSD ≤ X) {c : ℕ} (hc3 : 3 ≤ c)
    (hc : c < 18) (hp : titsOverRel X 0 (titsOverRep c)) :
    titsOverRel X 0 1 ∧ titsOverRel X 0 2 := by
  obtain ⟨j, rfl⟩ : ∃ j, c = j + 3 := ⟨c - 3, by omega⟩
  have hj : j < 15 := by omega
  have hmerge := (titsOver_check.2.2.2.2.2.2.2 j hj).2
  have hrep : ∀ i : Fin 13, Rep 8775 titsTFlagArrs[(i : ℕ)]! (titsTFlag i) :=
    fun i => titsTFlag_rep i.2
  have hx : ((titsOverRep (j + 3) : Fin 8775) : ℕ) = titsOverReps[j + 3]! :=
    finPt_val (titsOver_rep_lt hc)
  have hvalid := validTargetMerge_of_mergeTargetsOK (S := fun i : Fin 13 => titsTFlag i)
    (G := titsTFlagArrs) hrep (b := (0 : Fin 8775)) (x := titsOverRep (j + 3))
    (L := titsOverMerge j) (ts := [1, 2]) (by rw [hx]; exact hmerge)
  have hinv : ∀ (i : Fin 13) (u v : Fin 8775), titsOverRel X u v →
      titsOverRel X (titsTFlag i u) (titsTFlag i v) := by
    intro i u v h
    have := titsOverRel_inv (X := X) ⟨titsT i, titsT_mem_titsD i.2⟩ h
    rwa [titsDFlagAct_t i.2] at this
  have := invariant_merge_targets_soundness (fun i : Fin 13 => titsTFlag i) 0
    (titsOverRep (j + 3)) (titsOverMerge j) [1, 2] hvalid (titsOverRel X) (titsOverRel_equiv hX)
    hinv hp
  exact ⟨this 1 (by simp), this 2 (by simp)⟩

theorem titsD_overgroups
    (X : Subgroup titsD) (hX : titsSD ≤ X) :
    X = titsSD ∨ X = titsHD ∨ X = titsND ∨ X = ⊤ := by
  by_cases hXS : X ≤ titsSD
  · exact Or.inl (le_antisymm hXS hX)
  right
  obtain ⟨g, hgX, hgS⟩ := IsConcreteLE.not_le_iff_exists.1 hXS
  have hy0 : titsDFlagAct g 0 ≠ 0 := fun h => hgS ((mem_titsSD_iff g).2 h)
  have hRy : titsOverRel X 0 (titsDFlagAct g 0) := titsOverRel_of_mem hgX
  obtain ⟨c, hc, s, hs, hsy⟩ := titsOver_cover (titsDFlagAct g 0)
  have hp : titsOverRel X 0 (titsOverRep c) := by
    have h := titsOverRel_inv (X := X) s⁻¹ hRy
    have h0 : titsDFlagAct s⁻¹ 0 = 0 := (mem_titsSD_iff _).1 (inv_mem hs)
    rw [h0, ← hsy, ← Equiv.Perm.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Equiv.Perm.one_apply] at h
    exact h
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hy0
    rw [← hsy, titsOverRep_zero]
    exact (mem_titsSD_iff s).1 hs
  have hcoatom : ∀ M : Subgroup titsD, IsCoatom M → M ≤ X → X = M ∨ X = ⊤ := by
    intro M hM hMX
    by_cases h : X = M
    · exact Or.inl h
    · exact Or.inr (hM.2 X (lt_of_le_of_ne hMX (Ne.symm h)))
  have hboth : titsHD ≤ X → titsND ≤ X → X = ⊤ := by
    intro hH hN
    rcases hcoatom _ titsH_isCoatom hH with h | h
    · exfalso
      apply titsN_not_le_H
      intro x hx
      have h1 : (⟨x, titsN_le_titsD hx⟩ : titsD) ∈ titsND := hx
      have h2 := hN h1
      rw [h] at h2
      exact h2
    · exact h
  by_cases hc1 : c = 1
  · subst hc1
    rw [titsOverRep_one] at hp
    rcases hcoatom _ titsN_isCoatom (titsND_le_of_rel hX hp) with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  by_cases hc2 : c = 2
  · subst hc2
    rw [titsOverRep_two] at hp
    rcases hcoatom _ titsH_isCoatom (titsHD_le_of_rel hX hp) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  obtain ⟨h1, h2⟩ := titsOverRel_merge hX (by omega) hc hp
  exact Or.inr (Or.inr (hboth (titsHD_le_of_rel hX h2) (titsND_le_of_rel hX h1)))

end CFSG.Quasithin
