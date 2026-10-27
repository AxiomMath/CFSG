module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3V1SixFinBJ
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3V1SixFinBI
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3V1SixFinBU
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.G6 Equiv

private theorem s1611e3_sixVNat_one :
    s1611e3_sixVNat (1 : SixE6 × SixE6) = 0 := by
  simp [s1611e3_sixVNat, s1611e3_sixE6Nat_one]

theorem s1611e3_sixVNat_sq_eq_one (u : SixE6 × SixE6) : u * u = 1 := by
  apply s1611e3_sixVNat_injective
  rw [s1611e3_sixVNat_mul, s1611e3_sixVNat_one]
  simp

theorem s1611e3_sixVNat_inv_eq_self (u : SixE6 × SixE6) : u⁻¹ = u :=
  inv_eq_of_mul_eq_one_right (s1611e3_sixVNat_sq_eq_one u)

private theorem s1611e3_testBit_foldl_or_aux (l : List Nat) (a m : Nat) :
    (l.foldl (fun acc x => acc ||| (1 <<< x)) a).testBit m =
      (a.testBit m || decide (m ∈ l)) := by
  induction l generalizing a with
  | nil => simp
  | cons b t ih =>
    rw [List.foldl_cons, ih (a ||| (1 <<< b))]
    rw [show (1 : Nat) <<< b = 2 ^ b by rw [Nat.shiftLeft_eq, Nat.one_mul]]
    rw [Nat.testBit_or, Nat.testBit_two_pow]
    simp [List.mem_cons, eq_comm, Bool.or_assoc]

private theorem s1611e3_testBit_foldl_or (l : List Nat) (m : Nat) :
    (l.foldl (fun acc x => acc ||| (1 <<< x)) 0).testBit m = decide (m ∈ l) := by
  rw [s1611e3_testBit_foldl_or_aux]
  simp

theorem s1611e3_testBit_sixFull (m : Nat) : sixFull.testBit m = decide (m ∈ sixVecs) := by
  unfold sixFull
  exact s1611e3_testBit_foldl_or sixVecs m

private theorem s1611e3_testBit_sixProf_true {Kb : Bool} {t m : Nat}
    (h : (sixProf Kb t).testBit m = true) :
    m ∈ sixVecs ∧ sixFixes Kb t m = true := by
  rw [testBit_sixProf] at h
  exact ⟨of_decide_eq_true (Bool.and_eq_true_iff.mp h).1, (Bool.and_eq_true_iff.mp h).2⟩

private theorem s1611e3_sixFixes_false_of_testBit_false {Kb : Bool} {t m : Nat}
    (hm : m ∈ sixVecs) (h : (sixProf Kb t).testBit m = false) : sixFixes Kb t m = false := by
  rw [testBit_sixProf] at h
  rw [decide_eq_true_eq.mpr hm] at h
  simpa using h

private theorem s1611e3_exists_testBit_ne {P Q : Nat} (h : P ≠ Q) :
    ∃ m, P.testBit m ≠ Q.testBit m :=
  Nat.exists_testBit_ne_of_ne h

private theorem s1611e3_exists_profile_diff {P Q : Nat} (h : P ≠ Q) :
    (∃ m, P.testBit m = true ∧ Q.testBit m = false) ∨
      ∃ m, P.testBit m = false ∧ Q.testBit m = true := by
  obtain ⟨m, hm⟩ := s1611e3_exists_testBit_ne h
  cases hP : P.testBit m <;> cases hQ : Q.testBit m
  · exact absurd (by rw [hP, hQ]) hm
  · exact Or.inr ⟨m, hP, hQ⟩
  · exact Or.inl ⟨m, hP, hQ⟩
  · exact absurd (by rw [hP, hQ]) hm

private theorem s1611e3_exists_full_false {P : Nat} (hsub : ∀ m, P.testBit m = true →
    sixFull.testBit m = true) (hne : P ≠ sixFull) :
    ∃ m, sixFull.testBit m = true ∧ P.testBit m = false := by
  by_contra h
  apply hne
  apply Nat.eq_of_testBit_eq
  intro m
  by_cases hp : P.testBit m = true
  · have hf := hsub m hp
    simp [hp, hf]
  · have hp' : P.testBit m = false := by cases hb : P.testBit m <;> simp_all
    by_cases hf : sixFull.testBit m = true
    · exact absurd ⟨m, hf, hp'⟩ h
    · have hf' : sixFull.testBit m = false := by cases hb : sixFull.testBit m <;> simp_all
      simp [hp', hf']

private theorem s1611e3_sixInvTabs_length : sixInvTabs.length = 111 := by
  decide +kernel

private theorem s1611e3_sixInvTabs_nodup : sixInvTabs.Nodup := by
  decide +kernel

private theorem s1611e3_sixIdx_getElem (i : Nat) (hi : i < sixInvTabs.length) :
    sixIdx (sixInvTabs[i]) = i := by
  unfold sixIdx
  rw [List.findIdx_eq hi]
  constructor
  · simp
  · intro j hj
    have hne : sixInvTabs[j]'(Nat.lt_trans hj hi) ≠ sixInvTabs[i] := by
      intro h
      have := (s1611e3_sixInvTabs_nodup.getElem_inj).mp h
      omega
    simp [hne]

theorem s1611e3_sixProfOf_eq (Kb : Bool) {t : Nat} (ht : t ∈ sixInvTabs) :
    sixProfOf Kb t = sixProf Kb t := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ht
  have hlen : i < 111 := by rw [← s1611e3_sixInvTabs_length]; exact hi
  unfold sixProfOf
  rw [s1611e3_sixIdx_getElem i hi]
  rw [sixInvProf, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map]

private theorem s1611e3_sixGhatOf_one : s1611e3_sixGhatOf s1611e3_sixCodeOne = 1 := by
  simp [s1611e3_sixGhatOf, s1611e3_sixCodeOne]

private theorem s1611e3_sixCodeValid_one : s1611e3_sixCodeValid s1611e3_sixCodeOne := by
  simp [s1611e3_sixCodeValid, s1611e3_sixCodeOne]

theorem s1611e3_sixTab_of_mul {c d e : s1611e3_SixCode}
    (hc : s1611e3_sixCodeValid c) (hd : s1611e3_sixCodeValid d)
    (he : s1611e3_sixCodeValid e)
    (h : s1611e3_sixGhatOf e = s1611e3_sixGhatOf c * s1611e3_sixGhatOf d) :
    sixCodeTab e = sixTabComp (sixCodeTab c) (sixCodeTab d) := by
  have hmul : e = s1611e3_sixCodeMul c d := by
    apply sixGhatOf_injective he (s1611e3_sixCodeValid_mul hc hd)
    rw [h, s1611e3_sixGhatOf_mul hc hd]
  rw [hmul, sixCodeTab_mul]

theorem s1611e3_sixTab_mem_invTabs {c : s1611e3_SixCode}
    (hc : s1611e3_sixCodeValid c)
    (h2 : s1611e3_sixCodeMul c c = s1611e3_sixCodeOne)
    (h1 : c ≠ s1611e3_sixCodeOne) : sixCodeTab c ∈ sixInvTabs := by
  obtain ⟨σ, τ, ε⟩ := c
  have hτ : τ = sixAlpha σ := hc
  rw [hτ] at h2 h1 ⊢
  exact sixInvTabs_complete σ ε h2 h1

theorem s1611e3_sixFixes_iff {K : Subgroup (SixE6 × SixE6)} {Kb : Bool}
    (hK : (Kb = false ∧ K = ⊥) ∨ (Kb = true ∧ K = sixDiag))
    {c : s1611e3_SixCode} (hc : s1611e3_sixCodeValid c) (u : SixE6 × SixE6) :
    s1611e3_sixGhatOf c u * u⁻¹ ∈ K ↔
      sixFixes Kb (sixCodeTab c) (s1611e3_sixVNat u) = true := by
  have hcode : s1611e3_sixVNat (s1611e3_sixGhatOf c u * u⁻¹) =
      sixTabAct (sixCodeTab c) (s1611e3_sixVNat u) ^^^ s1611e3_sixVNat u := by
    rw [s1611e3_sixVNat_mul, s1611e3_sixVNat_inv_eq_self, sixVNat_act_tab hc]
  rw [← sixKMem_iff hK, hcode]
  rfl

private theorem s1611e3_K_invariant {K : Subgroup (SixE6 × SixE6)}
    (hK : K = ⊥ ∨ K = sixDiag) :
    ∀ g ∈ sixGhat, ∀ u ∈ K, (g : MulAut (SixE6 × SixE6)) u ∈ K := by
  intro g hg u hu
  rcases hK with rfl | rfl
  · simp only [Subgroup.mem_bot] at hu ⊢
    rw [hu]
    simp
  · exact sixDiag_invariant g hg u hu

private theorem s1611e3_fixMod_mul {K : Subgroup (SixE6 × SixE6)} (hK : K = ⊥ ∨ K = sixDiag)
    {a b : MulAut (SixE6 × SixE6)} (ha : a ∈ sixGhat) (hb : b ∈ sixGhat)
    {u : SixE6 × SixE6} (hua : a u * u⁻¹ ∈ K) (hub : b u * u⁻¹ ∈ K) :
    (a * b) u * u⁻¹ ∈ K := by
  have hkey : (a * b) u * u⁻¹ = a (b u * u⁻¹) * (a u * u⁻¹) := by
    rw [MulAut.mul_apply, map_mul, map_inv]
    group
  rw [hkey]
  exact K.mul_mem (s1611e3_K_invariant hK a ha _ hub) hua

private theorem s1611e3_not_mem_of_fixes_false {K : Subgroup (SixE6 × SixE6)} {Kb : Bool}
    (hK : (Kb = false ∧ K = ⊥) ∨ (Kb = true ∧ K = sixDiag))
    {c : s1611e3_SixCode} (hc : s1611e3_sixCodeValid c) {m : Nat} {u : SixE6 × SixE6}
    (hu : s1611e3_sixVNat u = m) (hfix : sixFixes Kb (sixCodeTab c) m = false) :
    s1611e3_sixGhatOf c u * u⁻¹ ∉ K := by
  intro hmem
  have h := (s1611e3_sixFixes_iff hK hc u).mp hmem
  rw [hu, hfix] at h
  exact Bool.false_ne_true h

theorem s1611e3_sixChk1_spec {Kb : Bool} (h : sixChk1 Kb = true) {i : Nat} (hi : i < 111) :
    (sixInvProf Kb).getD i 0 ≠ sixFull := by
  have h1 := List.all_eq_true.mp h i (List.mem_range.mpr hi)
  simpa using h1

theorem s1611e3_sixChk2_spec (Kb : Bool) (h : sixChk2 Kb = true)
    {i j : Nat} (hi : i < 111) (hj : j < 111) (hij : i ≠ j)
    (hadj : (sixInvAdj.getD i 0).testBit j = true) :
    ((sixInvProf Kb).getD i 0 ≠ (sixInvProf Kb).getD j 0) ∨
      ((sixInvProf Kb).getD j 0 ≠
        sixProfOf Kb (sixTabComp (sixInvTabs.getD i 0) (sixInvTabs.getD j 0))) := by
  have h1 := List.all_eq_true.mp h i (List.mem_range.mpr hi)
  have h2 := List.all_eq_true.mp h1 j (List.mem_range.mpr hj)
  rw [hadj] at h2
  simp only [Bool.beq_eq_decide_eq, hij, decide_false, Bool.not_true, Bool.false_or,
    Bool.or_false] at h2
  simpa [← List.getD_eq_getElem?_getD] using h2

theorem s1611e3_sixChk3_spec (Kb : Bool) (h : sixChk3 Kb = true)
    {i j k : Nat} (hi : i < 111) (hj : j < 111) (hk : k < 111)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (haji : (sixInvAdj.getD i 0).testBit j = true)
    (haki : (sixInvAdj.getD i 0).testBit k = true)
    (hakj : (sixInvAdj.getD j 0).testBit k = true)
    (hcomp : sixTabComp (sixInvTabs.getD i 0) (sixInvTabs.getD j 0) ≠
      sixInvTabs.getD k 0) :
    (((sixInvProf Kb).getD i 0 &&& (sixInvProf Kb).getD j 0) ≠
        ((sixInvProf Kb).getD i 0 &&& (sixInvProf Kb).getD j 0 &&&
          (sixInvProf Kb).getD k 0)) ∨
      (((sixInvProf Kb).getD i 0 &&& (sixInvProf Kb).getD k 0) ≠
        ((sixInvProf Kb).getD i 0 &&& (sixInvProf Kb).getD j 0 &&&
          (sixInvProf Kb).getD k 0)) ∨
      (((sixInvProf Kb).getD j 0 &&& (sixInvProf Kb).getD k 0) ≠
        ((sixInvProf Kb).getD i 0 &&& (sixInvProf Kb).getD j 0 &&&
          (sixInvProf Kb).getD k 0)) ∨
      (((sixInvProf Kb).getD i 0 &&&
          sixProfOf Kb (sixTabComp (sixInvTabs.getD j 0) (sixInvTabs.getD k 0))) ≠
        ((sixInvProf Kb).getD i 0 &&& (sixInvProf Kb).getD j 0 &&&
          (sixInvProf Kb).getD k 0)) ∨
      (((sixInvProf Kb).getD j 0 &&&
          sixProfOf Kb (sixTabComp (sixInvTabs.getD i 0) (sixInvTabs.getD k 0))) ≠
        ((sixInvProf Kb).getD i 0 &&& (sixInvProf Kb).getD j 0 &&&
          (sixInvProf Kb).getD k 0)) ∨
      (((sixInvProf Kb).getD k 0 &&&
          sixProfOf Kb (sixTabComp (sixInvTabs.getD i 0) (sixInvTabs.getD j 0))) ≠
        ((sixInvProf Kb).getD i 0 &&& (sixInvProf Kb).getD j 0 &&&
          (sixInvProf Kb).getD k 0)) ∨
      ((sixProfOf Kb (sixTabComp (sixInvTabs.getD i 0) (sixInvTabs.getD j 0)) &&&
          sixProfOf Kb (sixTabComp (sixInvTabs.getD i 0) (sixInvTabs.getD k 0))) ≠
        ((sixInvProf Kb).getD i 0 &&& (sixInvProf Kb).getD j 0 &&&
          (sixInvProf Kb).getD k 0)) := by
  have h1 := List.all_eq_true.mp h i (List.mem_range.mpr hi)
  have h2 := List.all_eq_true.mp h1 j (List.mem_range.mpr hj)
  rw [haji] at h2
  simp only [Bool.beq_eq_decide_eq, hij, decide_false, Bool.not_true, Bool.false_or,
    Bool.or_false] at h2
  have hki : k ≠ i := fun h => hik h.symm
  have hkj : k ≠ j := fun h => hjk h.symm
  have h3 := List.all_eq_true.mp h2 k (List.mem_range.mpr hk)
  rw [haki, hakj] at h3
  simp only [Bool.beq_eq_decide_eq, hki, hkj, hcomp, decide_false, Bool.not_true,
    Bool.false_or, Bool.or_false] at h3
  simpa [or_assoc, ← List.getD_eq_getElem?_getD] using h3

theorem s1611e3_sixChk4_spec (h : sixChk4 = true)
    {i j k l : Nat} (hi : i < 111) (hj : j < 111) (hk : k < 111) (hl : l < 111)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (haji : (sixInvAdj.getD i 0).testBit j = true)
    (haki : (sixInvAdj.getD i 0).testBit k = true)
    (hakj : (sixInvAdj.getD j 0).testBit k = true)
    (hcomp : sixTabComp (sixInvTabs.getD i 0) (sixInvTabs.getD j 0) ≠
      sixInvTabs.getD k 0)
    (hn : ((sixInvAdj.getD i 0) &&& (sixInvAdj.getD j 0) &&&
      (sixInvAdj.getD k 0)).testBit l = true) :
    sixInvTabs.getD l 0 = sixInvTabs.getD i 0 ∨
      sixInvTabs.getD l 0 = sixInvTabs.getD j 0 ∨
      sixInvTabs.getD l 0 = sixInvTabs.getD k 0 ∨
      sixInvTabs.getD l 0 = sixTabComp (sixInvTabs.getD i 0) (sixInvTabs.getD j 0) ∨
      sixInvTabs.getD l 0 = sixTabComp (sixInvTabs.getD i 0) (sixInvTabs.getD k 0) ∨
      sixInvTabs.getD l 0 = sixTabComp (sixInvTabs.getD j 0) (sixInvTabs.getD k 0) ∨
      sixInvTabs.getD l 0 = sixTabComp (sixTabComp (sixInvTabs.getD i 0)
        (sixInvTabs.getD j 0)) (sixInvTabs.getD k 0) := by
  have h1 := List.all_eq_true.mp h i (List.mem_range.mpr hi)
  have h2 := List.all_eq_true.mp h1 j (List.mem_range.mpr hj)
  rw [haji] at h2
  simp only [Bool.beq_eq_decide_eq, hij, decide_false, Bool.not_true, Bool.false_or,
    Bool.or_false] at h2
  have hki : k ≠ i := fun h => hik h.symm
  have hkj : k ≠ j := fun h => hjk h.symm
  have h3 := List.all_eq_true.mp h2 k (List.mem_range.mpr hk)
  simp only [Bool.beq_eq_decide_eq, hki, hkj, decide_false, Bool.not_true,
    Bool.false_or, Bool.or_false, haki, hakj, hcomp] at h3
  have h4 := List.all_eq_true.mp h3 l (List.mem_range.mpr hl)
  rw [hn] at h4
  simp only [Bool.not_true, Bool.false_or, Bool.or_false] at h4
  simpa [or_assoc, Bool.beq_eq_decide_eq, ← List.getD_eq_getElem?_getD] using h4

private theorem s1611e3_K_of_Kb {K : Subgroup (SixE6 × SixE6)} {Kb : Bool}
    (hKb : (Kb = false ∧ K = ⊥) ∨ (Kb = true ∧ K = sixDiag)) :
    K = ⊥ ∨ K = sixDiag := by
  rcases hKb with ⟨-, h⟩ | ⟨-, h⟩
  · exact Or.inl h
  · exact Or.inr h

private theorem s1611e3_exists_bit_and_of_ne {e P Q : Nat}
    (hPe : ∀ m, e.testBit m = true → P.testBit m = true)
    (hQe : ∀ m, e.testBit m = true → Q.testBit m = true)
    (hne : (P &&& Q) ≠ e) :
    ∃ m, P.testBit m = true ∧ Q.testBit m = true ∧ e.testBit m = false := by
  obtain ⟨m, hm⟩ := s1611e3_exists_testBit_ne hne
  rw [Nat.testBit_and] at hm
  by_cases he : e.testBit m = true
  · have hP := hPe m he
    have hQ := hQe m he
    rw [hP, hQ, he] at hm
    simp at hm
  · have he' : e.testBit m = false := by cases h : e.testBit m <;> simp_all
    by_cases hP : P.testBit m = true
    · by_cases hQ : Q.testBit m = true
      · exact ⟨m, hP, hQ, he'⟩
      · have hQ' : Q.testBit m = false := by cases h : Q.testBit m <;> simp_all
        rw [hP, hQ', he'] at hm
        simp at hm
    · have hP' : P.testBit m = false := by cases h : P.testBit m <;> simp_all
      rw [hP', he'] at hm
      simp at hm

private theorem s1611e3_eq_of_tab_eq {x y : MulAut (SixE6 × SixE6)}
    {cx cy : s1611e3_SixCode} (hcx : s1611e3_sixCodeValid cx)
    (hcy : s1611e3_sixCodeValid cy) (hgx : s1611e3_sixGhatOf cx = x)
    (hgy : s1611e3_sixGhatOf cy = y) (h : sixCodeTab cx = sixCodeTab cy) : x = y := by
  have hcc : cx = cy := sixCodeTab_injective h
  calc x = s1611e3_sixGhatOf cx := hgx.symm
    _ = s1611e3_sixGhatOf cy := by rw [hcc]
    _ = y := hgy

theorem s1611e3_sixFin_one_aux {K : Subgroup (SixE6 × SixE6)} {Kb : Bool}
    (hKb : (Kb = false ∧ K = ⊥) ∨ (Kb = true ∧ K = sixDiag))
    (hchk : sixChk1 Kb = true)
    {a : MulAut (SixE6 × SixE6)} (ha : a ∈ sixGhat) (ha1 : a ≠ 1) (ha2 : a * a = 1) :
    ∃ u : SixE6 × SixE6, a u * u⁻¹ ∉ K := by
  obtain ⟨ca, hca, hga⟩ := s1611e3_sixGhatOf_surjective a ha
  have hca_ne : ca ≠ s1611e3_sixCodeOne := by
    intro h
    apply ha1
    calc a = s1611e3_sixGhatOf ca := hga.symm
      _ = s1611e3_sixGhatOf s1611e3_sixCodeOne := by rw [h]
      _ = 1 := s1611e3_sixGhatOf_one
  have hca2 : s1611e3_sixCodeMul ca ca = s1611e3_sixCodeOne := by
    apply sixGhatOf_injective (c := s1611e3_sixCodeMul ca ca) (d := s1611e3_sixCodeOne)
    · exact s1611e3_sixCodeValid_mul hca hca
    · exact s1611e3_sixCodeValid_one
    · rw [s1611e3_sixGhatOf_mul hca hca, hga, ha2, s1611e3_sixGhatOf_one]
  have hmem : sixCodeTab ca ∈ sixInvTabs := s1611e3_sixTab_mem_invTabs hca hca2 hca_ne
  obtain ⟨i, hi_len, hgeti⟩ := List.mem_iff_getElem.mp hmem
  have hi : i < 111 := by rw [← s1611e3_sixInvTabs_length]; exact hi_len
  have hget : sixInvTabs.getD i 0 = sixCodeTab ca := by
    rw [List.getD_eq_getElem _ _ hi_len]; exact hgeti
  have hprof : (sixInvProf Kb).getD i 0 = sixProf Kb (sixCodeTab ca) := by
    rw [sixInvProf, List.getD_eq_getElem _ _ (by simpa using hi_len), List.getElem_map, hgeti]
  have hneFull : sixProf Kb (sixCodeTab ca) ≠ sixFull := by
    intro h
    exact s1611e3_sixChk1_spec hchk hi (by rw [hprof, h])
  have hsub : ∀ m, (sixProf Kb (sixCodeTab ca)).testBit m = true →
      sixFull.testBit m = true := by
    intro m hm
    rw [s1611e3_testBit_sixFull]
    exact decide_eq_true_eq.mpr (s1611e3_testBit_sixProf_true hm).1
  obtain ⟨m, hF, hP⟩ := s1611e3_exists_full_false hsub hneFull
  have hmvec : m ∈ sixVecs := by
    rw [s1611e3_testBit_sixFull] at hF
    exact of_decide_eq_true hF
  have hfix : sixFixes Kb (sixCodeTab ca) m = false :=
    s1611e3_sixFixes_false_of_testBit_false hmvec hP
  obtain ⟨u, hu⟩ := exists_of_mem_sixVecs hmvec
  refine ⟨u, ?_⟩
  have h := s1611e3_not_mem_of_fixes_false hKb hca hu hfix
  simpa [hga] using h

theorem s1611e3_sixFin_two_aux {K : Subgroup (SixE6 × SixE6)} {Kb : Bool}
    (hKb : (Kb = false ∧ K = ⊥) ∨ (Kb = true ∧ K = sixDiag))
    (hchk : sixChk2 Kb = true)
    {a b : MulAut (SixE6 × SixE6)} (ha : a ∈ sixGhat) (hb : b ∈ sixGhat) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) (hab : a ≠ b) (ha2 : a * a = 1) (hb2 : b * b = 1)
    (habc : a * b = b * a) :
    ∃ x ∈ ({a, b, a * b} : Set (MulAut (SixE6 × SixE6))), ∃ u : SixE6 × SixE6,
      x u * u⁻¹ ∈ K ∧ ¬ (a u * u⁻¹ ∈ K ∧ b u * u⁻¹ ∈ K) := by
  obtain ⟨ca, hca, hga⟩ := s1611e3_sixGhatOf_surjective a ha
  obtain ⟨cb, hcb, hgb⟩ := s1611e3_sixGhatOf_surjective b hb
  have hab_mem : a * b ∈ sixGhat := sixGhat.mul_mem ha hb
  obtain ⟨cab, hcab, hgcab⟩ := s1611e3_sixGhatOf_surjective (a * b) hab_mem
  have hab1 : a * b ≠ 1 := by
    intro h
    apply hab
    symm
    calc b = 1 * b := (one_mul b).symm
      _ = (a * a) * b := by rw [ha2]
      _ = a * (a * b) := by rw [mul_assoc]
      _ = a * 1 := by rw [h]
      _ = a := mul_one a
  have hab2 : (a * b) * (a * b) = 1 := by
    calc (a * b) * (a * b) = a * (b * (a * b)) := by rw [mul_assoc]
      _ = a * ((b * a) * b) := by rw [mul_assoc]
      _ = a * ((a * b) * b) := by rw [← habc]
      _ = a * (a * (b * b)) := by rw [mul_assoc]
      _ = (a * a) * (b * b) := by rw [mul_assoc]
      _ = 1 := by rw [ha2, hb2, one_mul]
  have hca_ne : ca ≠ s1611e3_sixCodeOne := by
    intro h
    apply ha1
    calc a = s1611e3_sixGhatOf ca := hga.symm
      _ = 1 := by rw [h, s1611e3_sixGhatOf_one]
  have hcb_ne : cb ≠ s1611e3_sixCodeOne := by
    intro h
    apply hb1
    calc b = s1611e3_sixGhatOf cb := hgb.symm
      _ = 1 := by rw [h, s1611e3_sixGhatOf_one]
  have hcab_ne : cab ≠ s1611e3_sixCodeOne := by
    intro h
    apply hab1
    calc a * b = s1611e3_sixGhatOf cab := hgcab.symm
      _ = 1 := by rw [h, s1611e3_sixGhatOf_one]
  have hca2 : s1611e3_sixCodeMul ca ca = s1611e3_sixCodeOne := by
    apply sixGhatOf_injective (c := s1611e3_sixCodeMul ca ca) (d := s1611e3_sixCodeOne)
    · exact s1611e3_sixCodeValid_mul hca hca
    · exact s1611e3_sixCodeValid_one
    · rw [s1611e3_sixGhatOf_mul hca hca, hga, ha2, s1611e3_sixGhatOf_one]
  have hcb2 : s1611e3_sixCodeMul cb cb = s1611e3_sixCodeOne := by
    apply sixGhatOf_injective (c := s1611e3_sixCodeMul cb cb) (d := s1611e3_sixCodeOne)
    · exact s1611e3_sixCodeValid_mul hcb hcb
    · exact s1611e3_sixCodeValid_one
    · rw [s1611e3_sixGhatOf_mul hcb hcb, hgb, hb2, s1611e3_sixGhatOf_one]
  have hcab2 : s1611e3_sixCodeMul cab cab = s1611e3_sixCodeOne := by
    apply sixGhatOf_injective (c := s1611e3_sixCodeMul cab cab) (d := s1611e3_sixCodeOne)
    · exact s1611e3_sixCodeValid_mul hcab hcab
    · exact s1611e3_sixCodeValid_one
    · rw [s1611e3_sixGhatOf_mul hcab hcab, hgcab, hab2, s1611e3_sixGhatOf_one]
  have hta : sixCodeTab ca ∈ sixInvTabs := s1611e3_sixTab_mem_invTabs hca hca2 hca_ne
  have htb : sixCodeTab cb ∈ sixInvTabs := s1611e3_sixTab_mem_invTabs hcb hcb2 hcb_ne
  have htab : sixCodeTab cab ∈ sixInvTabs := s1611e3_sixTab_mem_invTabs hcab hcab2 hcab_ne
  have hcomp_ab : sixCodeTab cab = sixTabComp (sixCodeTab ca) (sixCodeTab cb) :=
    s1611e3_sixTab_of_mul hca hcb hcab (by rw [hgcab, hga, hgb])
  have hcomp_ba : sixCodeTab cab = sixTabComp (sixCodeTab cb) (sixCodeTab ca) :=
    s1611e3_sixTab_of_mul hcb hca hcab (by rw [hgcab, hga, hgb, habc])
  have hcomm_tab : sixTabComp (sixCodeTab ca) (sixCodeTab cb) =
      sixTabComp (sixCodeTab cb) (sixCodeTab ca) := hcomp_ab.symm.trans hcomp_ba
  obtain ⟨i, hi_len, hgeti⟩ := List.mem_iff_getElem.mp hta
  obtain ⟨j, hj_len, hgetj⟩ := List.mem_iff_getElem.mp htb
  have hi : i < 111 := by rw [← s1611e3_sixInvTabs_length]; exact hi_len
  have hj : j < 111 := by rw [← s1611e3_sixInvTabs_length]; exact hj_len
  have hgeta : sixInvTabs.getD i 0 = sixCodeTab ca := by
    rw [List.getD_eq_getElem _ _ hi_len]; exact hgeti
  have hgetb : sixInvTabs.getD j 0 = sixCodeTab cb := by
    rw [List.getD_eq_getElem _ _ hj_len]; exact hgetj
  have hta_ne_tb : sixCodeTab ca ≠ sixCodeTab cb := by
    intro h
    apply hab
    exact s1611e3_eq_of_tab_eq hca hcb hga hgb h
  have hij : i ≠ j := by
    intro h
    apply hta_ne_tb
    rw [← hgeta, ← hgetb, h]
  have hadj : (sixInvAdj.getD i 0).testBit j = true := by
    rw [testBit_sixInvAdj hi hj, hgeta, hgetb]
    simp [sixComm, hcomm_tab]
  have hspec := s1611e3_sixChk2_spec Kb hchk hi hj hij hadj
  have hpa : (sixInvProf Kb).getD i 0 = sixProf Kb (sixCodeTab ca) := by
    rw [sixInvProf, List.getD_eq_getElem _ _ (by simpa using hi_len), List.getElem_map, hgeti]
  have hpb : (sixInvProf Kb).getD j 0 = sixProf Kb (sixCodeTab cb) := by
    rw [sixInvProf, List.getD_eq_getElem _ _ (by simpa using hj_len), List.getElem_map, hgetj]
  have hpab : sixProfOf Kb (sixTabComp (sixInvTabs.getD i 0) (sixInvTabs.getD j 0)) =
      sixProf Kb (sixCodeTab cab) := by
    rw [hgeta, hgetb, ← hcomp_ab, s1611e3_sixProfOf_eq Kb htab]
  have hspec' : sixProf Kb (sixCodeTab ca) ≠ sixProf Kb (sixCodeTab cb) ∨
      sixProf Kb (sixCodeTab cb) ≠ sixProf Kb (sixCodeTab cab) := by
    rcases hspec with h | h
    · exact Or.inl (by rwa [hpa, hpb] at h)
    · exact Or.inr (by rwa [hpb, hpab] at h)
  rcases hspec' with hne_ab | hne_bab
  · rcases s1611e3_exists_profile_diff hne_ab with ⟨m, hpaM, hpbM⟩ | ⟨m, hpaM, hpbM⟩
    · have hmvec := (s1611e3_testBit_sixProf_true hpaM).1
      have hfixa := (s1611e3_testBit_sixProf_true hpaM).2
      have hfixb := s1611e3_sixFixes_false_of_testBit_false hmvec hpbM
      obtain ⟨u, hu⟩ := exists_of_mem_sixVecs hmvec
      have hua : s1611e3_sixGhatOf ca u * u⁻¹ ∈ K :=
        (s1611e3_sixFixes_iff hKb hca u).mpr (by rw [hu]; exact hfixa)
      have hnb : s1611e3_sixGhatOf cb u * u⁻¹ ∉ K :=
        s1611e3_not_mem_of_fixes_false hKb hcb hu hfixb
      refine ⟨a, by simp, u, ?_, ?_⟩
      · simpa [hga] using hua
      · intro h
        exact hnb (by simpa [hgb] using h.2)
    · have hmvec := (s1611e3_testBit_sixProf_true hpbM).1
      have hfixb := (s1611e3_testBit_sixProf_true hpbM).2
      have hfixa := s1611e3_sixFixes_false_of_testBit_false hmvec hpaM
      obtain ⟨u, hu⟩ := exists_of_mem_sixVecs hmvec
      have hub : s1611e3_sixGhatOf cb u * u⁻¹ ∈ K :=
        (s1611e3_sixFixes_iff hKb hcb u).mpr (by rw [hu]; exact hfixb)
      have hna : s1611e3_sixGhatOf ca u * u⁻¹ ∉ K :=
        s1611e3_not_mem_of_fixes_false hKb hca hu hfixa
      refine ⟨b, by simp, u, ?_, ?_⟩
      · simpa [hgb] using hub
      · intro h
        exact hna (by simpa [hga] using h.1)
  · rcases s1611e3_exists_profile_diff hne_bab with ⟨m, hpbM, hpabM⟩ | ⟨m, hpbM, hpabM⟩
    · have hmvec := (s1611e3_testBit_sixProf_true hpbM).1
      have hfixb := (s1611e3_testBit_sixProf_true hpbM).2
      have hfixab := s1611e3_sixFixes_false_of_testBit_false hmvec hpabM
      obtain ⟨u, hu⟩ := exists_of_mem_sixVecs hmvec
      have hub : s1611e3_sixGhatOf cb u * u⁻¹ ∈ K :=
        (s1611e3_sixFixes_iff hKb hcb u).mpr (by rw [hu]; exact hfixb)
      have hnab : s1611e3_sixGhatOf cab u * u⁻¹ ∉ K :=
        s1611e3_not_mem_of_fixes_false hKb hcab hu hfixab
      refine ⟨b, by simp, u, ?_, ?_⟩
      · simpa [hgb] using hub
      · intro h
        have huab : s1611e3_sixGhatOf cab u * u⁻¹ ∈ K := by
          have := s1611e3_fixMod_mul (s1611e3_K_of_Kb hKb) ha hb h.1 h.2
          simpa [hgcab] using this
        exact hnab huab
    · have hmvec := (s1611e3_testBit_sixProf_true hpabM).1
      have hfixab := (s1611e3_testBit_sixProf_true hpabM).2
      have hfixb := s1611e3_sixFixes_false_of_testBit_false hmvec hpbM
      obtain ⟨u, hu⟩ := exists_of_mem_sixVecs hmvec
      have huab : s1611e3_sixGhatOf cab u * u⁻¹ ∈ K :=
        (s1611e3_sixFixes_iff hKb hcab u).mpr (by rw [hu]; exact hfixab)
      have hnb : s1611e3_sixGhatOf cb u * u⁻¹ ∉ K :=
        s1611e3_not_mem_of_fixes_false hKb hcb hu hfixb
      refine ⟨a * b, by simp, u, ?_, ?_⟩
      · simpa [hgcab] using huab
      · intro h
        exact hnb (by simpa [hgb] using h.2)

theorem s1611e3_sixFin_three_aux {K : Subgroup (SixE6 × SixE6)} {Kb : Bool}
    (hKb : (Kb = false ∧ K = ⊥) ∨ (Kb = true ∧ K = sixDiag))
    (hchk : sixChk3 Kb = true)
    {a b c : MulAut (SixE6 × SixE6)} (ha : a ∈ sixGhat) (hb : b ∈ sixGhat)
    (hc : c ∈ sixGhat) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hc1 : c ≠ 1) (hab : a ≠ b)
    (hca_ne : c ≠ a) (hcb_ne : c ≠ b) (hcab_ne : c ≠ a * b) (ha2 : a * a = 1) (hb2 : b * b = 1)
    (hc2 : c * c = 1) (habc : a * b = b * a) (hac : a * c = c * a)
    (hbc : b * c = c * b) :
    ∃ x y : MulAut (SixE6 × SixE6),
      (x, y) ∈ ({(a, b), (a, c), (b, c), (a, b * c), (b, a * c), (c, a * b),
        (a * b, a * c)} : Set (MulAut (SixE6 × SixE6) × MulAut (SixE6 × SixE6))) ∧
      ∃ u : SixE6 × SixE6, x u * u⁻¹ ∈ K ∧ y u * u⁻¹ ∈ K ∧
        ¬ (a u * u⁻¹ ∈ K ∧ b u * u⁻¹ ∈ K ∧ c u * u⁻¹ ∈ K) := by
  obtain ⟨ca, vca, gca⟩ := s1611e3_sixGhatOf_surjective a ha
  obtain ⟨cb, vcb, gcb⟩ := s1611e3_sixGhatOf_surjective b hb
  obtain ⟨cc, vcc, gcc⟩ := s1611e3_sixGhatOf_surjective c hc
  have hab_mem : a * b ∈ sixGhat := sixGhat.mul_mem ha hb
  have hac_mem : a * c ∈ sixGhat := sixGhat.mul_mem ha hc
  have hbc_mem : b * c ∈ sixGhat := sixGhat.mul_mem hb hc
  obtain ⟨cab, vcab, gccab⟩ := s1611e3_sixGhatOf_surjective (a * b) hab_mem
  obtain ⟨cac, vcac, gccac⟩ := s1611e3_sixGhatOf_surjective (a * c) hac_mem
  obtain ⟨cbc, vcbc, gccbc⟩ := s1611e3_sixGhatOf_surjective (b * c) hbc_mem
  have hab1 : a * b ≠ 1 := by
    intro h
    apply hab
    symm
    calc b = 1 * b := (one_mul b).symm
      _ = (a * a) * b := by rw [ha2]
      _ = a * (a * b) := by rw [mul_assoc]
      _ = a * 1 := by rw [h]
      _ = a := mul_one a
  have hac1 : a * c ≠ 1 := by
    intro h
    apply hca_ne
    calc c = c * 1 := (mul_one c).symm
      _ = c * (a * a) := by rw [ha2]
      _ = (c * a) * a := by rw [mul_assoc]
      _ = (a * c) * a := by rw [hac]
      _ = 1 * a := by rw [h]
      _ = a := one_mul a
  have hbc1 : b * c ≠ 1 := by
    intro h
    apply hcb_ne
    calc c = c * 1 := (mul_one c).symm
      _ = c * (b * b) := by rw [hb2]
      _ = (c * b) * b := by rw [mul_assoc]
      _ = (b * c) * b := by rw [hbc]
      _ = 1 * b := by rw [h]
      _ = b := one_mul b
  have hab2 : (a * b) * (a * b) = 1 := by
    calc (a * b) * (a * b) = a * (b * (a * b)) := by rw [mul_assoc]
      _ = a * ((b * a) * b) := by rw [mul_assoc]
      _ = a * ((a * b) * b) := by rw [← habc]
      _ = a * (a * (b * b)) := by rw [mul_assoc]
      _ = (a * a) * (b * b) := by rw [mul_assoc]
      _ = 1 := by rw [ha2, hb2, one_mul]
  have hac2 : (a * c) * (a * c) = 1 := by
    calc (a * c) * (a * c) = a * (c * (a * c)) := by rw [mul_assoc]
      _ = a * ((c * a) * c) := by rw [mul_assoc]
      _ = a * ((a * c) * c) := by rw [← hac]
      _ = a * (a * (c * c)) := by rw [mul_assoc]
      _ = (a * a) * (c * c) := by rw [mul_assoc]
      _ = 1 := by rw [ha2, hc2, one_mul]
  have hbc2 : (b * c) * (b * c) = 1 := by
    calc (b * c) * (b * c) = b * (c * (b * c)) := by rw [mul_assoc]
      _ = b * ((c * b) * c) := by rw [mul_assoc]
      _ = b * ((b * c) * c) := by rw [← hbc]
      _ = b * (b * (c * c)) := by rw [mul_assoc]
      _ = (b * b) * (c * c) := by rw [mul_assoc]
      _ = 1 := by rw [hb2, hc2, one_mul]
  have vca_ne : ca ≠ s1611e3_sixCodeOne := by
    intro h
    apply ha1
    calc a = s1611e3_sixGhatOf ca := gca.symm
      _ = 1 := by rw [h, s1611e3_sixGhatOf_one]
  have vcb_ne : cb ≠ s1611e3_sixCodeOne := by
    intro h
    apply hb1
    calc b = s1611e3_sixGhatOf cb := gcb.symm
      _ = 1 := by rw [h, s1611e3_sixGhatOf_one]
  have vcc_ne : cc ≠ s1611e3_sixCodeOne := by
    intro h
    apply hc1
    calc c = s1611e3_sixGhatOf cc := gcc.symm
      _ = 1 := by rw [h, s1611e3_sixGhatOf_one]
  have vcab_ne : cab ≠ s1611e3_sixCodeOne := by
    intro h
    apply hab1
    calc a * b = s1611e3_sixGhatOf cab := gccab.symm
      _ = 1 := by rw [h, s1611e3_sixGhatOf_one]
  have vcac_ne : cac ≠ s1611e3_sixCodeOne := by
    intro h
    apply hac1
    calc a * c = s1611e3_sixGhatOf cac := gccac.symm
      _ = 1 := by rw [h, s1611e3_sixGhatOf_one]
  have vcbc_ne : cbc ≠ s1611e3_sixCodeOne := by
    intro h
    apply hbc1
    calc b * c = s1611e3_sixGhatOf cbc := gccbc.symm
      _ = 1 := by rw [h, s1611e3_sixGhatOf_one]
  have vca2' : s1611e3_sixCodeMul ca ca = s1611e3_sixCodeOne := by
    apply sixGhatOf_injective (c := s1611e3_sixCodeMul ca ca) (d := s1611e3_sixCodeOne)
    · exact s1611e3_sixCodeValid_mul vca vca
    · exact s1611e3_sixCodeValid_one
    · rw [s1611e3_sixGhatOf_mul vca vca, gca, ha2, s1611e3_sixGhatOf_one]
  have vcb2' : s1611e3_sixCodeMul cb cb = s1611e3_sixCodeOne := by
    apply sixGhatOf_injective (c := s1611e3_sixCodeMul cb cb) (d := s1611e3_sixCodeOne)
    · exact s1611e3_sixCodeValid_mul vcb vcb
    · exact s1611e3_sixCodeValid_one
    · rw [s1611e3_sixGhatOf_mul vcb vcb, gcb, hb2, s1611e3_sixGhatOf_one]
  have vcc2' : s1611e3_sixCodeMul cc cc = s1611e3_sixCodeOne := by
    apply sixGhatOf_injective (c := s1611e3_sixCodeMul cc cc) (d := s1611e3_sixCodeOne)
    · exact s1611e3_sixCodeValid_mul vcc vcc
    · exact s1611e3_sixCodeValid_one
    · rw [s1611e3_sixGhatOf_mul vcc vcc, gcc, hc2, s1611e3_sixGhatOf_one]
  have vcab2' : s1611e3_sixCodeMul cab cab = s1611e3_sixCodeOne := by
    apply sixGhatOf_injective (c := s1611e3_sixCodeMul cab cab) (d := s1611e3_sixCodeOne)
    · exact s1611e3_sixCodeValid_mul vcab vcab
    · exact s1611e3_sixCodeValid_one
    · rw [s1611e3_sixGhatOf_mul vcab vcab, gccab, hab2, s1611e3_sixGhatOf_one]
  have vcac2' : s1611e3_sixCodeMul cac cac = s1611e3_sixCodeOne := by
    apply sixGhatOf_injective (c := s1611e3_sixCodeMul cac cac) (d := s1611e3_sixCodeOne)
    · exact s1611e3_sixCodeValid_mul vcac vcac
    · exact s1611e3_sixCodeValid_one
    · rw [s1611e3_sixGhatOf_mul vcac vcac, gccac, hac2, s1611e3_sixGhatOf_one]
  have vcbc2' : s1611e3_sixCodeMul cbc cbc = s1611e3_sixCodeOne := by
    apply sixGhatOf_injective (c := s1611e3_sixCodeMul cbc cbc) (d := s1611e3_sixCodeOne)
    · exact s1611e3_sixCodeValid_mul vcbc vcbc
    · exact s1611e3_sixCodeValid_one
    · rw [s1611e3_sixGhatOf_mul vcbc vcbc, gccbc, hbc2, s1611e3_sixGhatOf_one]
  have hta : sixCodeTab ca ∈ sixInvTabs := s1611e3_sixTab_mem_invTabs vca vca2' vca_ne
  have htb : sixCodeTab cb ∈ sixInvTabs := s1611e3_sixTab_mem_invTabs vcb vcb2' vcb_ne
  have htc : sixCodeTab cc ∈ sixInvTabs := s1611e3_sixTab_mem_invTabs vcc vcc2' vcc_ne
  have htab : sixCodeTab cab ∈ sixInvTabs := s1611e3_sixTab_mem_invTabs vcab vcab2' vcab_ne
  have htac : sixCodeTab cac ∈ sixInvTabs := s1611e3_sixTab_mem_invTabs vcac vcac2' vcac_ne
  have htbc : sixCodeTab cbc ∈ sixInvTabs := s1611e3_sixTab_mem_invTabs vcbc vcbc2' vcbc_ne
  have hcomp_ab : sixCodeTab cab = sixTabComp (sixCodeTab ca) (sixCodeTab cb) :=
    s1611e3_sixTab_of_mul vca vcb vcab (by rw [gccab, gca, gcb])
  have hcomp_ac : sixCodeTab cac = sixTabComp (sixCodeTab ca) (sixCodeTab cc) :=
    s1611e3_sixTab_of_mul vca vcc vcac (by rw [gccac, gca, gcc])
  have hcomp_bc : sixCodeTab cbc = sixTabComp (sixCodeTab cb) (sixCodeTab cc) :=
    s1611e3_sixTab_of_mul vcb vcc vcbc (by rw [gccbc, gcb, gcc])
  have hcomp_ab_ba : sixCodeTab cab = sixTabComp (sixCodeTab cb) (sixCodeTab ca) :=
    s1611e3_sixTab_of_mul vcb vca vcab (by rw [gccab, gca, gcb, habc])
  have hcomp_ac_ca : sixCodeTab cac = sixTabComp (sixCodeTab cc) (sixCodeTab ca) :=
    s1611e3_sixTab_of_mul vcc vca vcac (by rw [gccac, gca, gcc, hac])
  have hcomp_bc_cb : sixCodeTab cbc = sixTabComp (sixCodeTab cc) (sixCodeTab cb) :=
    s1611e3_sixTab_of_mul vcc vcb vcbc (by rw [gccbc, gcb, gcc, hbc])
  have hcomm_ab : sixTabComp (sixCodeTab ca) (sixCodeTab cb) =
      sixTabComp (sixCodeTab cb) (sixCodeTab ca) := hcomp_ab.symm.trans hcomp_ab_ba
  have hcomm_ac : sixTabComp (sixCodeTab ca) (sixCodeTab cc) =
      sixTabComp (sixCodeTab cc) (sixCodeTab ca) := hcomp_ac.symm.trans hcomp_ac_ca
  have hcomm_bc : sixTabComp (sixCodeTab cb) (sixCodeTab cc) =
      sixTabComp (sixCodeTab cc) (sixCodeTab cb) := hcomp_bc.symm.trans hcomp_bc_cb
  obtain ⟨i, hi_len, hgeti⟩ := List.mem_iff_getElem.mp hta
  obtain ⟨j, hj_len, hgetj⟩ := List.mem_iff_getElem.mp htb
  obtain ⟨k, hk_len, hgetk⟩ := List.mem_iff_getElem.mp htc
  have hi : i < 111 := by rw [← s1611e3_sixInvTabs_length]; exact hi_len
  have hj : j < 111 := by rw [← s1611e3_sixInvTabs_length]; exact hj_len
  have hk : k < 111 := by rw [← s1611e3_sixInvTabs_length]; exact hk_len
  have hgeta : sixInvTabs.getD i 0 = sixCodeTab ca := by
    rw [List.getD_eq_getElem _ _ hi_len]; exact hgeti
  have hgetb : sixInvTabs.getD j 0 = sixCodeTab cb := by
    rw [List.getD_eq_getElem _ _ hj_len]; exact hgetj
  have hgetc : sixInvTabs.getD k 0 = sixCodeTab cc := by
    rw [List.getD_eq_getElem _ _ hk_len]; exact hgetk
  have hta_ne_tb : sixCodeTab ca ≠ sixCodeTab cb := fun h =>
    hab (s1611e3_eq_of_tab_eq vca vcb gca gcb h)
  have hta_ne_tc : sixCodeTab ca ≠ sixCodeTab cc := fun h =>
    hca_ne (s1611e3_eq_of_tab_eq vca vcc gca gcc h).symm
  have htb_ne_tc : sixCodeTab cb ≠ sixCodeTab cc := fun h =>
    hcb_ne (s1611e3_eq_of_tab_eq vcb vcc gcb gcc h).symm
  have hij : i ≠ j := by intro h; apply hta_ne_tb; rw [← hgeta, ← hgetb, h]
  have hik : i ≠ k := by intro h; apply hta_ne_tc; rw [← hgeta, ← hgetc, h]
  have hjk : j ≠ k := by intro h; apply htb_ne_tc; rw [← hgetb, ← hgetc, h]
  have hcomp_ne_c : sixTabComp (sixInvTabs.getD i 0) (sixInvTabs.getD j 0) ≠
      sixInvTabs.getD k 0 := by
    intro h
    apply hcab_ne
    symm
    have h' : sixTabComp (sixCodeTab ca) (sixCodeTab cb) = sixCodeTab cc := by
      rw [← hgeta, ← hgetb, ← hgetc]; exact h
    have vcc_eq : cab = cc := sixCodeTab_injective (by rw [hcomp_ab, h'])
    calc a * b = s1611e3_sixGhatOf cab := gccab.symm
      _ = s1611e3_sixGhatOf cc := by rw [vcc_eq]
      _ = c := gcc
  have haji : (sixInvAdj.getD i 0).testBit j = true := by
    rw [testBit_sixInvAdj hi hj, hgeta, hgetb]
    simp [sixComm, hcomm_ab]
  have haki : (sixInvAdj.getD i 0).testBit k = true := by
    rw [testBit_sixInvAdj hi hk, hgeta, hgetc]
    simp [sixComm, hcomm_ac]
  have hakj : (sixInvAdj.getD j 0).testBit k = true := by
    rw [testBit_sixInvAdj hj hk, hgetb, hgetc]
    simp [sixComm, hcomm_bc]
  have hspec := s1611e3_sixChk3_spec Kb hchk hi hj hk hij hik hjk haji haki hakj hcomp_ne_c
  have hpa : (sixInvProf Kb).getD i 0 = sixProf Kb (sixCodeTab ca) := by
    rw [sixInvProf, List.getD_eq_getElem _ _ (by simpa using hi_len), List.getElem_map, hgeti]
  have hpb : (sixInvProf Kb).getD j 0 = sixProf Kb (sixCodeTab cb) := by
    rw [sixInvProf, List.getD_eq_getElem _ _ (by simpa using hj_len), List.getElem_map, hgetj]
  have hpc : (sixInvProf Kb).getD k 0 = sixProf Kb (sixCodeTab cc) := by
    rw [sixInvProf, List.getD_eq_getElem _ _ (by simpa using hk_len), List.getElem_map, hgetk]
  have hpab : sixProfOf Kb (sixTabComp (sixInvTabs.getD i 0) (sixInvTabs.getD j 0)) =
      sixProf Kb (sixCodeTab cab) := by
    rw [hgeta, hgetb, ← hcomp_ab, s1611e3_sixProfOf_eq Kb htab]
  have hpac : sixProfOf Kb (sixTabComp (sixInvTabs.getD i 0) (sixInvTabs.getD k 0)) =
      sixProf Kb (sixCodeTab cac) := by
    rw [hgeta, hgetc, ← hcomp_ac, s1611e3_sixProfOf_eq Kb htac]
  have hpbc : sixProfOf Kb (sixTabComp (sixInvTabs.getD j 0) (sixInvTabs.getD k 0)) =
      sixProf Kb (sixCodeTab cbc) := by
    rw [hgetb, hgetc, ← hcomp_bc, s1611e3_sixProfOf_eq Kb htbc]
  set Pa := sixProf Kb (sixCodeTab ca) with hPaDef
  set Pb := sixProf Kb (sixCodeTab cb) with hPbDef
  set Pc := sixProf Kb (sixCodeTab cc) with hPcDef
  set Pab := sixProf Kb (sixCodeTab cab) with hPabDef
  set Pac := sixProf Kb (sixCodeTab cac) with hPacDef
  set Pbc := sixProf Kb (sixCodeTab cbc) with hPbcDef
  set E := Pa &&& Pb &&& Pc with hEDef
  have hspec' : (Pa &&& Pb) ≠ E ∨ (Pa &&& Pc) ≠ E ∨ (Pb &&& Pc) ≠ E ∨
      (Pa &&& Pbc) ≠ E ∨ (Pb &&& Pac) ≠ E ∨ (Pc &&& Pab) ≠ E ∨
      (Pab &&& Pac) ≠ E := by
    rw [hpa, hpb, hpc, hpab, hpac, hpbc] at hspec
    simpa [hPaDef, hPbDef, hPcDef, hPabDef, hPacDef, hPbcDef, hEDef] using hspec
  have hE : ∀ m, E.testBit m = true → Pa.testBit m = true ∧ Pb.testBit m = true ∧
      Pc.testBit m = true := by
    intro m hm
    simp only [hEDef, Nat.testBit_and, Bool.and_eq_true_iff] at hm
    exact ⟨hm.1.1, hm.1.2, hm.2⟩
  have hpa_sub : ∀ m, E.testBit m = true → Pa.testBit m = true := fun m hm => (hE m hm).1
  have hpb_sub : ∀ m, E.testBit m = true → Pb.testBit m = true := fun m hm => (hE m hm).2.1
  have hpc_sub : ∀ m, E.testBit m = true → Pc.testBit m = true := fun m hm => (hE m hm).2.2
  have vcab_eq : cab = s1611e3_sixCodeMul ca cb :=
    sixCodeTab_injective (by rw [hcomp_ab, sixCodeTab_mul])
  have vcac_eq : cac = s1611e3_sixCodeMul ca cc :=
    sixCodeTab_injective (by rw [hcomp_ac, sixCodeTab_mul])
  have vcbc_eq : cbc = s1611e3_sixCodeMul cb cc :=
    sixCodeTab_injective (by rw [hcomp_bc, sixCodeTab_mul])
  have hsub_prod : ∀ (c1 c2 : s1611e3_SixCode) (P12 : Nat)
      (x1 x2 : MulAut (SixE6 × SixE6)),
      s1611e3_sixCodeValid c1 → s1611e3_sixCodeValid c2 →
      s1611e3_sixGhatOf c1 = x1 → x1 ∈ sixGhat → s1611e3_sixGhatOf c2 = x2 →
      x2 ∈ sixGhat → P12 = sixProf Kb (sixCodeTab (s1611e3_sixCodeMul c1 c2)) →
      (∀ m, E.testBit m = true → (sixProf Kb (sixCodeTab c1)).testBit m = true) →
      (∀ m, E.testBit m = true → (sixProf Kb (sixCodeTab c2)).testBit m = true) →
      ∀ m, E.testBit m = true → P12.testBit m = true := by
    intro c1 c2 P12 x1 x2 hc1 hc2 hg1 hx1 hg2 hx2 hP12 hs1 hs2 m hm
    have hm1 := hs1 m hm
    have hm2 := hs2 m hm
    have hmvec := (s1611e3_testBit_sixProf_true hm1).1
    have hfix1 := (s1611e3_testBit_sixProf_true hm1).2
    have hfix2 := (s1611e3_testBit_sixProf_true hm2).2
    obtain ⟨u, hu⟩ := exists_of_mem_sixVecs hmvec
    have hx1fix : x1 u * u⁻¹ ∈ K := by
      have := (s1611e3_sixFixes_iff hKb hc1 u).mpr (by rw [hu]; exact hfix1)
      simpa [hg1] using this
    have hx2fix : x2 u * u⁻¹ ∈ K := by
      have := (s1611e3_sixFixes_iff hKb hc2 u).mpr (by rw [hu]; exact hfix2)
      simpa [hg2] using this
    have hprod : (x1 * x2) u * u⁻¹ ∈ K :=
      s1611e3_fixMod_mul (s1611e3_K_of_Kb hKb) hx1 hx2 hx1fix hx2fix
    have hprodfix : sixFixes Kb (sixCodeTab (s1611e3_sixCodeMul c1 c2))
        (s1611e3_sixVNat u) = true := by
      have := (s1611e3_sixFixes_iff hKb (s1611e3_sixCodeValid_mul hc1 hc2) u).mp (by
        simpa [s1611e3_sixGhatOf_mul hc1 hc2, hg1, hg2] using hprod)
      exact this
    rw [hP12, testBit_sixProf, decide_eq_true_eq.mpr hmvec, ← hu]
    simpa using hprodfix
  have hPab' : Pab = sixProf Kb (sixCodeTab (s1611e3_sixCodeMul ca cb)) := by
    rw [hPabDef, vcab_eq]
  have hPac' : Pac = sixProf Kb (sixCodeTab (s1611e3_sixCodeMul ca cc)) := by
    rw [hPacDef, vcac_eq]
  have hPbc' : Pbc = sixProf Kb (sixCodeTab (s1611e3_sixCodeMul cb cc)) := by
    rw [hPbcDef, vcbc_eq]
  have hPab_sub : ∀ m, E.testBit m = true → Pab.testBit m = true :=
    hsub_prod ca cb Pab a b vca vcb gca ha gcb hb hPab' hpa_sub hpb_sub
  have hPac_sub : ∀ m, E.testBit m = true → Pac.testBit m = true :=
    hsub_prod ca cc Pac a c vca vcc gca ha gcc hc hPac' hpa_sub hpc_sub
  have hPbc_sub : ∀ m, E.testBit m = true → Pbc.testBit m = true :=
    hsub_prod cb cc Pbc b c vcb vcc gcb hb gcc hc hPbc' hpb_sub hpc_sub
  have mk : ∀ (Px Py : Nat) (x y : MulAut (SixE6 × SixE6)) (cx cy : s1611e3_SixCode),
      s1611e3_sixCodeValid cx → s1611e3_sixCodeValid cy →
      s1611e3_sixGhatOf cx = x → s1611e3_sixGhatOf cy = y →
      Px = sixProf Kb (sixCodeTab cx) → Py = sixProf Kb (sixCodeTab cy) →
      (∀ m, E.testBit m = true → Px.testBit m = true) →
      (∀ m, E.testBit m = true → Py.testBit m = true) →
      (Px &&& Py) ≠ E →
      ∃ u : SixE6 × SixE6, x u * u⁻¹ ∈ K ∧ y u * u⁻¹ ∈ K ∧
        ¬ (a u * u⁻¹ ∈ K ∧ b u * u⁻¹ ∈ K ∧ c u * u⁻¹ ∈ K) := by
    intro Px Py x y cx cy hcx hcy hgx hgy hPx hPy hsx hsy hne
    obtain ⟨m, hPxM, hPyM, hEM⟩ := s1611e3_exists_bit_and_of_ne hsx hsy hne
    rw [hPx] at hPxM
    rw [hPy] at hPyM
    have hmvec := (s1611e3_testBit_sixProf_true hPxM).1
    have hfixx := (s1611e3_testBit_sixProf_true hPxM).2
    have hfixy := (s1611e3_testBit_sixProf_true hPyM).2
    obtain ⟨u, hu⟩ := exists_of_mem_sixVecs hmvec
    have hxfix : x u * u⁻¹ ∈ K := by
      have := (s1611e3_sixFixes_iff hKb hcx u).mpr (by rw [hu]; exact hfixx)
      simpa [hgx] using this
    have hyfix : y u * u⁻¹ ∈ K := by
      have := (s1611e3_sixFixes_iff hKb hcy u).mpr (by rw [hu]; exact hfixy)
      simpa [hgy] using this
    refine ⟨u, hxfix, hyfix, ?_⟩
    intro ⟨haK, hbK, hcK⟩
    have hPaM : Pa.testBit m = true := by
      have hfixa := (s1611e3_sixFixes_iff hKb vca u).mp (by simpa [gca] using haK)
      rw [testBit_sixProf, decide_eq_true_eq.mpr hmvec, ← hu]
      simpa using hfixa
    have hPbM : Pb.testBit m = true := by
      have hfixb := (s1611e3_sixFixes_iff hKb vcb u).mp (by simpa [gcb] using hbK)
      rw [testBit_sixProf, decide_eq_true_eq.mpr hmvec, ← hu]
      simpa using hfixb
    have hPcM : Pc.testBit m = true := by
      have hfixc := (s1611e3_sixFixes_iff hKb vcc u).mp (by simpa [gcc] using hcK)
      rw [testBit_sixProf, decide_eq_true_eq.mpr hmvec, ← hu]
      simpa using hfixc
    have hEtrue : E.testBit m = true := by simp [hEDef, hPaM, hPbM, hPcM]
    rw [hEM] at hEtrue
    exact Bool.false_ne_true hEtrue
  rcases hspec' with h1 | h2 | h3 | h4 | h5 | h6 | h7
  · exact ⟨a, b, by simp, mk Pa Pb a b ca cb vca vcb gca gcb rfl rfl hpa_sub hpb_sub h1⟩
  · exact ⟨a, c, by simp, mk Pa Pc a c ca cc vca vcc gca gcc rfl rfl hpa_sub hpc_sub h2⟩
  · exact ⟨b, c, by simp, mk Pb Pc b c cb cc vcb vcc gcb gcc rfl rfl hpb_sub hpc_sub h3⟩
  · exact ⟨a, b * c, by simp, mk Pa Pbc a (b * c) ca cbc vca vcbc gca gccbc rfl rfl
      hpa_sub hPbc_sub h4⟩
  · exact ⟨b, a * c, by simp, mk Pb Pac b (a * c) cb cac vcb vcac gcb gccac rfl rfl
      hpb_sub hPac_sub h5⟩
  · exact ⟨c, a * b, by simp, mk Pc Pab c (a * b) cc cab vcc vcab gcc gccab rfl rfl
      hpc_sub hPab_sub h6⟩
  · exact ⟨a * b, a * c, by simp, mk Pab Pac (a * b) (a * c) cab cac vcab vcac gccab gccac
      rfl rfl hPab_sub hPac_sub h7⟩

private theorem s1611e3_comm_tab {a b : MulAut (SixE6 × SixE6)} (ha : a ∈ sixGhat)
    (hb : b ∈ sixGhat) (hcomm : a * b = b * a) {ca cb : s1611e3_SixCode}
    (vca : s1611e3_sixCodeValid ca) (vcb : s1611e3_sixCodeValid cb)
    (gca : s1611e3_sixGhatOf ca = a) (gcb : s1611e3_sixGhatOf cb = b) :
    sixTabComp (sixCodeTab ca) (sixCodeTab cb) =
      sixTabComp (sixCodeTab cb) (sixCodeTab ca) := by
  obtain ⟨cab, vcab, gccab⟩ := s1611e3_sixGhatOf_surjective (a * b)
    (sixGhat.mul_mem ha hb)
  have h1 : sixCodeTab cab = sixTabComp (sixCodeTab ca) (sixCodeTab cb) :=
    s1611e3_sixTab_of_mul vca vcb vcab (by rw [gccab, gca, gcb])
  have h2 : sixCodeTab cab = sixTabComp (sixCodeTab cb) (sixCodeTab ca) :=
    s1611e3_sixTab_of_mul vcb vca vcab (by rw [gccab, gca, gcb, hcomm])
  exact h1.symm.trans h2

theorem s1611e3_sixFin_four_aux
    {a b c d : MulAut (SixE6 × SixE6)} (ha : a ∈ sixGhat) (hb : b ∈ sixGhat)
    (hc : c ∈ sixGhat) (hd : d ∈ sixGhat) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hc1 : c ≠ 1)
    (hd1 : d ≠ 1) (hab : a ≠ b) (hca_ne : c ≠ a) (hcb_ne : c ≠ b) (hcab_ne : c ≠ a * b)
    (hda : d ≠ a) (hdb : d ≠ b) (hdc : d ≠ c) (hdab : d ≠ a * b)
    (hdac : d ≠ a * c) (hdbc : d ≠ b * c) (hdabc : d ≠ a * b * c)
    (ha2 : a * a = 1) (hb2 : b * b = 1) (hc2 : c * c = 1) (hd2 : d * d = 1)
    (habc : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b)
    (had : a * d = d * a) (hbd : b * d = d * b) (hcd_comm : c * d = d * c) : False := by
  obtain ⟨ca, vca, gca⟩ := s1611e3_sixGhatOf_surjective a ha
  obtain ⟨cb, vcb, gcb⟩ := s1611e3_sixGhatOf_surjective b hb
  obtain ⟨cc, vcc, gcc⟩ := s1611e3_sixGhatOf_surjective c hc
  obtain ⟨cd, vcd, gcd⟩ := s1611e3_sixGhatOf_surjective d hd
  have hab_mem : a * b ∈ sixGhat := sixGhat.mul_mem ha hb
  have hac_mem : a * c ∈ sixGhat := sixGhat.mul_mem ha hc
  have hbc_mem : b * c ∈ sixGhat := sixGhat.mul_mem hb hc
  have habc_mem : (a * b) * c ∈ sixGhat := sixGhat.mul_mem hab_mem hc
  obtain ⟨cab, vcab, gccab⟩ := s1611e3_sixGhatOf_surjective (a * b) hab_mem
  obtain ⟨cac, vcac, gccac⟩ := s1611e3_sixGhatOf_surjective (a * c) hac_mem
  obtain ⟨cbc, vcbc, gccbc⟩ := s1611e3_sixGhatOf_surjective (b * c) hbc_mem
  obtain ⟨cabc, vcabc, gccabc⟩ := s1611e3_sixGhatOf_surjective ((a * b) * c) habc_mem
  have hcomp_ab : sixCodeTab cab = sixTabComp (sixCodeTab ca) (sixCodeTab cb) :=
    s1611e3_sixTab_of_mul vca vcb vcab (by rw [gccab, gca, gcb])
  have hcomp_ac : sixCodeTab cac = sixTabComp (sixCodeTab ca) (sixCodeTab cc) :=
    s1611e3_sixTab_of_mul vca vcc vcac (by rw [gccac, gca, gcc])
  have hcomp_bc : sixCodeTab cbc = sixTabComp (sixCodeTab cb) (sixCodeTab cc) :=
    s1611e3_sixTab_of_mul vcb vcc vcbc (by rw [gccbc, gcb, gcc])
  have hcomp_abc : sixCodeTab cabc =
      sixTabComp (sixCodeTab cab) (sixCodeTab cc) :=
    s1611e3_sixTab_of_mul vcab vcc vcabc (by rw [gccabc, gccab, gcc])
  have vcab_ne : cab ≠ s1611e3_sixCodeOne := by
    intro h
    apply hab
    symm
    calc b = 1 * b := (one_mul b).symm
      _ = (a * a) * b := by rw [ha2]
      _ = a * (a * b) := by rw [mul_assoc]
      _ = a * s1611e3_sixGhatOf cab := by rw [gccab]
      _ = a * 1 := by rw [h, s1611e3_sixGhatOf_one]
      _ = a := mul_one a
  have vcab2 : s1611e3_sixCodeMul cab cab = s1611e3_sixCodeOne := by
    apply sixGhatOf_injective (c := s1611e3_sixCodeMul cab cab) (d := s1611e3_sixCodeOne)
    · exact s1611e3_sixCodeValid_mul vcab vcab
    · exact s1611e3_sixCodeValid_one
    · rw [s1611e3_sixGhatOf_mul vcab vcab, gccab, s1611e3_sixGhatOf_one]
      calc (a * b) * (a * b) = a * (b * (a * b)) := by rw [mul_assoc]
        _ = a * ((b * a) * b) := by rw [mul_assoc]
        _ = a * ((a * b) * b) := by rw [← habc]
        _ = a * (a * (b * b)) := by rw [mul_assoc]
        _ = (a * a) * (b * b) := by rw [mul_assoc]
        _ = 1 := by rw [ha2, hb2, one_mul]
  have vcab_tabs : sixCodeTab cab ∈ sixInvTabs :=
    s1611e3_sixTab_mem_invTabs vcab vcab2 vcab_ne
  have hta : sixCodeTab ca ∈ sixInvTabs := by
    apply s1611e3_sixTab_mem_invTabs vca
    · apply sixGhatOf_injective (c := s1611e3_sixCodeMul ca ca) (d := s1611e3_sixCodeOne)
      · exact s1611e3_sixCodeValid_mul vca vca
      · exact s1611e3_sixCodeValid_one
      · rw [s1611e3_sixGhatOf_mul vca vca, gca, ha2, s1611e3_sixGhatOf_one]
    · intro h
      apply ha1
      calc a = s1611e3_sixGhatOf ca := gca.symm
        _ = 1 := by rw [h, s1611e3_sixGhatOf_one]
  have htb : sixCodeTab cb ∈ sixInvTabs := by
    apply s1611e3_sixTab_mem_invTabs vcb
    · apply sixGhatOf_injective (c := s1611e3_sixCodeMul cb cb) (d := s1611e3_sixCodeOne)
      · exact s1611e3_sixCodeValid_mul vcb vcb
      · exact s1611e3_sixCodeValid_one
      · rw [s1611e3_sixGhatOf_mul vcb vcb, gcb, hb2, s1611e3_sixGhatOf_one]
    · intro h
      apply hb1
      calc b = s1611e3_sixGhatOf cb := gcb.symm
        _ = 1 := by rw [h, s1611e3_sixGhatOf_one]
  have htc : sixCodeTab cc ∈ sixInvTabs := by
    apply s1611e3_sixTab_mem_invTabs vcc
    · apply sixGhatOf_injective (c := s1611e3_sixCodeMul cc cc) (d := s1611e3_sixCodeOne)
      · exact s1611e3_sixCodeValid_mul vcc vcc
      · exact s1611e3_sixCodeValid_one
      · rw [s1611e3_sixGhatOf_mul vcc vcc, gcc, hc2, s1611e3_sixGhatOf_one]
    · intro h
      apply hc1
      calc c = s1611e3_sixGhatOf cc := gcc.symm
        _ = 1 := by rw [h, s1611e3_sixGhatOf_one]
  have htd : sixCodeTab cd ∈ sixInvTabs := by
    apply s1611e3_sixTab_mem_invTabs vcd
    · apply sixGhatOf_injective (c := s1611e3_sixCodeMul cd cd) (d := s1611e3_sixCodeOne)
      · exact s1611e3_sixCodeValid_mul vcd vcd
      · exact s1611e3_sixCodeValid_one
      · rw [s1611e3_sixGhatOf_mul vcd vcd, gcd, hd2, s1611e3_sixGhatOf_one]
    · intro h
      apply hd1
      calc d = s1611e3_sixGhatOf cd := gcd.symm
        _ = 1 := by rw [h, s1611e3_sixGhatOf_one]
  obtain ⟨i, hi_len, hgeti⟩ := List.mem_iff_getElem.mp hta
  obtain ⟨j, hj_len, hgetj⟩ := List.mem_iff_getElem.mp htb
  obtain ⟨k, hk_len, hgetk⟩ := List.mem_iff_getElem.mp htc
  obtain ⟨l, hl_len, hgetl⟩ := List.mem_iff_getElem.mp htd
  have hi : i < 111 := by rw [← s1611e3_sixInvTabs_length]; exact hi_len
  have hj : j < 111 := by rw [← s1611e3_sixInvTabs_length]; exact hj_len
  have hk : k < 111 := by rw [← s1611e3_sixInvTabs_length]; exact hk_len
  have hl : l < 111 := by rw [← s1611e3_sixInvTabs_length]; exact hl_len
  have hgeta : sixInvTabs.getD i 0 = sixCodeTab ca := by
    rw [List.getD_eq_getElem _ _ hi_len]; exact hgeti
  have hgetb : sixInvTabs.getD j 0 = sixCodeTab cb := by
    rw [List.getD_eq_getElem _ _ hj_len]; exact hgetj
  have hgetc : sixInvTabs.getD k 0 = sixCodeTab cc := by
    rw [List.getD_eq_getElem _ _ hk_len]; exact hgetk
  have hgetd : sixInvTabs.getD l 0 = sixCodeTab cd := by
    rw [List.getD_eq_getElem _ _ hl_len]; exact hgetl
  have hta_ne_tb : sixCodeTab ca ≠ sixCodeTab cb := fun h =>
    hab (s1611e3_eq_of_tab_eq vca vcb gca gcb h)
  have hta_ne_tc : sixCodeTab ca ≠ sixCodeTab cc := fun h =>
    hca_ne (s1611e3_eq_of_tab_eq vca vcc gca gcc h).symm
  have htb_ne_tc : sixCodeTab cb ≠ sixCodeTab cc := fun h =>
    hcb_ne (s1611e3_eq_of_tab_eq vcb vcc gcb gcc h).symm
  have hij : i ≠ j := by intro h; apply hta_ne_tb; rw [← hgeta, ← hgetb, h]
  have hik : i ≠ k := by intro h; apply hta_ne_tc; rw [← hgeta, ← hgetc, h]
  have hjk : j ≠ k := by intro h; apply htb_ne_tc; rw [← hgetb, ← hgetc, h]
  have hcomp_ne_c : sixTabComp (sixInvTabs.getD i 0) (sixInvTabs.getD j 0) ≠
      sixInvTabs.getD k 0 := by
    intro h
    apply hcab_ne
    symm
    have h' : sixTabComp (sixCodeTab ca) (sixCodeTab cb) = sixCodeTab cc := by
      rw [← hgeta, ← hgetb, ← hgetc]; exact h
    have vcc_eq : cab = cc := sixCodeTab_injective (by rw [hcomp_ab, h'])
    calc a * b = s1611e3_sixGhatOf cab := gccab.symm
      _ = s1611e3_sixGhatOf cc := by rw [vcc_eq]
      _ = c := gcc
  have haji : (sixInvAdj.getD i 0).testBit j = true := by
    rw [testBit_sixInvAdj hi hj, hgeta, hgetb]
    simp [sixComm, s1611e3_comm_tab ha hb habc vca vcb gca gcb]
  have haki : (sixInvAdj.getD i 0).testBit k = true := by
    rw [testBit_sixInvAdj hi hk, hgeta, hgetc]
    simp [sixComm, s1611e3_comm_tab ha hc hac vca vcc gca gcc]
  have hakj : (sixInvAdj.getD j 0).testBit k = true := by
    rw [testBit_sixInvAdj hj hk, hgetb, hgetc]
    simp [sixComm, s1611e3_comm_tab hb hc hbc vcb vcc gcb gcc]
  have hcomm_ad : sixTabComp (sixCodeTab ca) (sixCodeTab cd) =
      sixTabComp (sixCodeTab cd) (sixCodeTab ca) :=
    s1611e3_comm_tab ha hd had vca vcd gca gcd
  have hcomm_bd : sixTabComp (sixCodeTab cb) (sixCodeTab cd) =
      sixTabComp (sixCodeTab cd) (sixCodeTab cb) :=
    s1611e3_comm_tab hb hd hbd vcb vcd gcb gcd
  have hcomm_cd : sixTabComp (sixCodeTab cc) (sixCodeTab cd) =
      sixTabComp (sixCodeTab cd) (sixCodeTab cc) :=
    s1611e3_comm_tab hc hd hcd_comm vcc vcd gcc gcd
  have hn : ((sixInvAdj.getD i 0) &&& (sixInvAdj.getD j 0) &&&
      (sixInvAdj.getD k 0)).testBit l = true := by
    rw [Nat.testBit_and, Nat.testBit_and]
    rw [testBit_sixInvAdj hi hl, testBit_sixInvAdj hj hl, testBit_sixInvAdj hk hl]
    rw [hgeta, hgetb, hgetc, hgetd]
    simp [sixComm, hcomm_ad, hcomm_bd, hcomm_cd]
  have htabc : sixCodeTab cabc =
      sixTabComp (sixTabComp (sixCodeTab ca) (sixCodeTab cb)) (sixCodeTab cc) := by
    rw [hcomp_abc, hcomp_ab]
  have hspec := s1611e3_sixChk4_spec sixChk4_true hi hj hk hl hij hik hjk haji haki hakj
    hcomp_ne_c hn
  have hspec' : sixCodeTab cd = sixCodeTab ca ∨ sixCodeTab cd = sixCodeTab cb ∨
      sixCodeTab cd = sixCodeTab cc ∨
      sixCodeTab cd = sixTabComp (sixCodeTab ca) (sixCodeTab cb) ∨
      sixCodeTab cd = sixTabComp (sixCodeTab ca) (sixCodeTab cc) ∨
      sixCodeTab cd = sixTabComp (sixCodeTab cb) (sixCodeTab cc) ∨
      sixCodeTab cd = sixTabComp (sixTabComp (sixCodeTab ca) (sixCodeTab cb))
        (sixCodeTab cc) := by
    simpa [← List.getD_eq_getElem?_getD, hgeta, hgetb, hgetc, hgetd] using hspec
  rcases hspec' with h | h | h | h | h | h | h
  · exact hda (s1611e3_eq_of_tab_eq vcd vca gcd gca h)
  · exact hdb (s1611e3_eq_of_tab_eq vcd vcb gcd gcb h)
  · exact hdc (s1611e3_eq_of_tab_eq vcd vcc gcd gcc h)
  · exact hdab (s1611e3_eq_of_tab_eq vcd vcab gcd gccab (h.trans hcomp_ab.symm))
  · exact hdac (s1611e3_eq_of_tab_eq vcd vcac gcd gccac (h.trans hcomp_ac.symm))
  · exact hdbc (s1611e3_eq_of_tab_eq vcd vcbc gcd gccbc (h.trans hcomp_bc.symm))
  · exact hdabc (s1611e3_eq_of_tab_eq vcd vcabc gcd gccabc (h.trans htabc.symm))

noncomputable def s1611e3_sixKb (K : Subgroup (SixE6 × SixE6)) : Bool := by
  classical
  exact if K = sixDiag then true else false

theorem s1611e3_Kb_spec {K : Subgroup (SixE6 × SixE6)} (hK : K = ⊥ ∨ K = sixDiag) :
    (s1611e3_sixKb K = false ∧ K = ⊥) ∨
      (s1611e3_sixKb K = true ∧ K = sixDiag) := by
  unfold s1611e3_sixKb
  by_cases h : K = sixDiag
  · rw [if_pos h]
    exact Or.inr ⟨rfl, h⟩
  · rw [if_neg h]
    refine Or.inl ⟨rfl, ?_⟩
    rcases hK with rfl | hd
    · rfl
    · exact absurd hd h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
