module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporE81Check
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporE81Gen

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434SporE81

open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.Assembly (IsElemAbelian)

@[expose] noncomputable def wordPerm (n : ℕ) (gs : Array (Array ℕ)) (w : List ℕ) :
    Equiv.Perm (Fin n) :=
  (w.map fun l => permOfArr n gs[l]!).prod

theorem rep_posWord {n : ℕ} {gs : Array (Array ℕ)} (hv : ∀ l < gs.size, validA n gs[l]! = true)
    (w : List ℕ) (hw : ∀ l ∈ w, l < gs.size) : Rep n (posWord n gs w) (wordPerm n gs w) := by
  have key : ∀ (w : List ℕ), (∀ l ∈ w, l < gs.size) → ∀ (acc : Array ℕ) (g : Equiv.Perm (Fin n)),
      Rep n acc g → Rep n (w.foldl (fun acc l => compA n acc gs[l]!) acc)
        (g * (w.map fun l => permOfArr n gs[l]!).prod) := by
    intro w
    induction w with
    | nil => intro _ acc g h; simpa using h
    | cons l w ih =>
      intro hw acc g h
      rw [List.foldl_cons, List.map_cons, List.prod_cons, ← mul_assoc]
      exact ih (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')) _ _
        (rep_compA h (rep_of_validA (hv l (hw l (List.mem_cons_self ..)))))
  have := key w hw (idA n) 1 rep_idA
  rwa [one_mul] at this

theorem wordPerm_mem {n : ℕ} {gs : Array (Array ℕ)} {S : Subgroup (Equiv.Perm (Fin n))}
    (hS : ∀ l < gs.size, permOfArr n gs[l]! ∈ S) {w : List ℕ} (hw : ∀ l ∈ w, l < gs.size) :
    wordPerm n gs w ∈ S :=
  Subgroup.list_prod_mem _ fun x hx => by
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
    exact hS l (hw l hl)

theorem getElem!_map' {α β : Type*} [Inhabited α] [Inhabited β] (A : Array α) (f : α → β)
    {k : ℕ} (hk : k < A.size) : (A.map f)[k]! = f A[k]! := by
  rw [getElem!_pos _ k (by simpa using hk), Array.getElem_map, getElem!_pos A k hk]

theorem letters_of_all {ws : Array (List ℕ)} {m : ℕ}
    (h : ws.all (fun w => w.all fun l => decide (l < m)) = true) :
    ∀ k < ws.size, ∀ l ∈ ws[k]!, l < m := by
  intro k hk l hl
  rw [Array.all_eq_true] at h
  have := h k hk
  rw [getElem!_pos ws k hk] at hl
  simpa using List.all_eq_true.1 this l hl

theorem mapWord_rep {n : ℕ} {gs : Array (Array ℕ)} (hv : ∀ l < gs.size, validA n gs[l]! = true)
    {ws : Array (List ℕ)} (hw : ∀ k < ws.size, ∀ l ∈ ws[k]!, l < gs.size) {k : ℕ}
    (hk : k < ws.size) : Rep n (ws.map (posWord n gs))[k]! (wordPerm n gs ws[k]!) := by
  rw [getElem!_map' ws _ hk]
  exact rep_posWord hv _ (hw k hk)

theorem dPair_facts {n : ℕ} {qg : Array (Array ℕ)}
    (hqgv : ∀ l < qg.size, validA n qg[l]! = true) {Q : Subgroup (Equiv.Perm (Fin n))}
    (hQ : ∀ l < qg.size, permOfArr n qg[l]! ∈ Q) {keys : List ℕ} (hkeys : ∀ p ∈ keys, p < n)
    {ws : Array (List ℕ)} (hws : ∀ k < ws.size, ∀ l ∈ ws[k]!, l < qg.size) {c : ArrCert}
    (henum : enumOK n (ws.map (posWord n qg)) keys c = true) (hsize : 81 ≤ c.pts.size)
    (hab : elemAbOK n (ws.map (posWord n qg)) = true) :
    ∃ D : Subgroup (Equiv.Perm (Fin n)), D ≤ Q ∧ IsElemAbelian 3 D ∧ 81 ≤ Nat.card D ∧
      ∀ (t : Array ℕ) (x : Equiv.Perm (Fin n)), Rep n t x → t ∈ c.pts.toList → x ∈ D := by
  have hdgv : ∀ l < (ws.map (posWord n qg)).size, validA n (ws.map (posWord n qg))[l]! = true :=
    fun l hl => enumOK_gens_valid henum hl
  refine ⟨Subgroup.closure (permsA n (ws.map (posWord n qg))), ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    have hk' : k < ws.size := by simpa using hk
    change permOfArr n (ws.map (posWord n qg))[k]! ∈ Q
    rw [permOfArr_eq_of_rep (mapWord_rep hqgv hws hk')]
    exact wordPerm_mem hQ (hws k hk')
  · apply isElemAbelian_closure_of_comm
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      have h1 := allLt_spec hab ha
      rw [Bool.and_eq_true] at h1
      have h2 := allLt_spec h1.2 hb
      exact (eqA_iff (rep_compA (rep_of_validA (hdgv a ha)) (rep_of_validA (hdgv b hb)))
        (rep_compA (rep_of_validA (hdgv b hb)) (rep_of_validA (hdgv a ha)))).1 h2
    · rintro _ ⟨a, ha, rfl⟩
      have h1 := allLt_spec hab ha
      rw [Bool.and_eq_true] at h1
      have hx := rep_of_validA (hdgv a ha)
      rw [pow_three]
      exact (eqA_iff (rep_compA hx (rep_compA hx hx)) rep_idA).1 h1.1
  · rw [(enumOK_spec hkeys henum).2.1]
    exact hsize
  · intro t x ht hmem
    exact enumOK_mem_of_mem hkeys henum ht hmem

theorem e81_sound (X : E81Data) (h : e81Check X = true)
    (P : Subgroup (Equiv.Perm (Fin X.n))) (hP : ∀ l < X.pg.size, permOfArr X.n X.pg[l]! ∈ P) :
    ∃ (Q R : Subgroup (Equiv.Perm (Fin X.n))) (z : Equiv.Perm (Fin X.n)),
      Q ≤ P ∧ Nat.card Q = X.qOrd ∧ z ^ 3 = 1 ∧ z ≠ 1 ∧ z ∈ Q ∧ (∀ q ∈ Q, q * z = z * q) ∧
      R ≤ Q ∧ X.qOrd ≤ Nat.card R * 3 ∧
      ∀ s ∈ R, s ^ 3 = 1 → s ∉ Subgroup.zpowers z →
        ∃ E : Subgroup (Equiv.Perm (Fin X.n)), E ≤ P ∧ IsElemAbelian 3 E ∧ 81 ≤ Nat.card E ∧
          s ∈ E ∧ z ∈ E := by
  unfold e81Check e81Check' at h
  simp only [Bool.and_eq_true, and_assoc, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨hpg, hkeys, hqW, hhW, hzW, hrW, hdW, hQenum, hQcard, hzv, hz3, hz1, hzc, hRenum,
    hRcard, hRord, hD, hhv, hcover⟩ := h
  have hpgv : ∀ l < X.pg.size, validA X.n X.pg[l]! = true := fun l hl => allLt_spec hpg hl
  have hk3 : ∀ p ∈ X.qKeys ++ X.rKeys ++ X.dKeys, p < X.n := fun p hp => by
    simpa using List.all_eq_true.1 hkeys p hp
  have hqk : ∀ p ∈ X.qKeys, p < X.n := fun p hp => hk3 p (by simp [hp])
  have hrk : ∀ p ∈ X.rKeys, p < X.n := fun p hp => hk3 p (by simp [hp])
  have hdk : ∀ p ∈ X.dKeys, p < X.n := fun p hp => hk3 p (by simp [hp])
  have hqWl := letters_of_all hqW
  have hhWl := letters_of_all hhW
  have hzWl : ∀ l ∈ X.zW, l < (qGens X).size := fun l hl => by
    simpa using List.all_eq_true.1 hzW l hl
  have hrWl := letters_of_all hrW
  have hdWl : ∀ ws ∈ X.dW, ∀ k < ws.size, ∀ l ∈ ws[k]!, l < (qGens X).size := by
    intro ws hws
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hws
    rw [Array.all_eq_true] at hdW
    exact letters_of_all (hdW i hi)
  set qg := qGens X with hqg
  have hqgv : ∀ l < qg.size, validA X.n qg[l]! = true := fun l hl => enumOK_gens_valid hQenum hl
  have hqsize : qg.size = X.qW.size := by simp [hqg, qGens]
  have hqgP : ∀ k < qg.size, permOfArr X.n qg[k]! ∈ P := by
    intro k hk
    have hk' : k < X.qW.size := hqsize ▸ hk
    show permOfArr X.n (X.qW.map (posWord X.n X.pg))[k]! ∈ P
    rw [permOfArr_eq_of_rep (mapWord_rep hpgv hqWl hk')]
    exact wordPerm_mem hP (hqWl k hk')
  set Q := Subgroup.closure (permsA X.n qg) with hQdef
  have hQgen : ∀ k < qg.size, permOfArr X.n qg[k]! ∈ Q := fun k hk =>
    Subgroup.subset_closure ⟨k, hk, rfl⟩
  have hQP : Q ≤ P := by
    rw [hQdef, Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    exact hqgP k hk
  have hQcard' : Nat.card Q = X.qOrd := (enumOK_spec hqk hQenum).2.1.trans hQcard
  set zA := zArr X with hzA
  have hzrep : Rep X.n zA (wordPerm X.n qg X.zW) := rep_posWord hqgv X.zW hzWl
  set z := wordPerm X.n qg X.zW with hz
  have hzQ : z ∈ Q := wordPerm_mem hQgen hzWl
  have hz3' : z ^ 3 = 1 := by
    rw [pow_three]
    exact (eqA_iff (rep_compA hzrep (rep_compA hzrep hzrep)) rep_idA).1 hz3
  have hz1' : z ≠ 1 := by
    intro h1
    have h2 : eqA X.n zA (idA X.n) = true := (eqA_iff hzrep rep_idA).2 h1
    rw [Bool.not_eq_true', h2] at hz1
    exact absurd hz1 (by simp)
  have hzcomm : ∀ q ∈ Q, q * z = z * q := by
    have hle : Q ≤ Subgroup.centralizer {z} := by
      rw [hQdef, Subgroup.closure_le]
      rintro _ ⟨k, hk, rfl⟩
      have hg := rep_of_validA (hqgv k hk)
      have h2 : z * permOfArr X.n qg[k]! = permOfArr X.n qg[k]! * z :=
        (eqA_iff (rep_compA hzrep hg) (rep_compA hg hzrep)).1 (allLt_spec hzc hk)
      exact Subgroup.mem_centralizer_singleton_iff.2 h2.symm
    exact fun q hq => Subgroup.mem_centralizer_singleton_iff.1 (hle hq)
  set rg := rGens X with hrg
  have hrgv : ∀ l < rg.size, validA X.n rg[l]! = true := fun l hl => enumOK_gens_valid hRenum hl
  have hrsize : rg.size = X.rW.size := by simp [hrg, rGens]
  have hrgQ : ∀ k < rg.size, permOfArr X.n rg[k]! ∈ Q := by
    intro k hk
    have hk' : k < X.rW.size := hrsize ▸ hk
    show permOfArr X.n (X.rW.map (posWord X.n qg))[k]! ∈ Q
    rw [permOfArr_eq_of_rep (mapWord_rep hqgv hrWl hk')]
    exact wordPerm_mem hQgen (hrWl k hk')
  set R := Subgroup.closure (permsA X.n rg) with hRdef
  have hRQ : R ≤ Q := by
    rw [hRdef, Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    exact hrgQ k hk
  have hRcard' : Nat.card R = X.rOrd := (enumOK_spec hrk hRenum).2.1.trans hRcard
  have hindex : X.qOrd ≤ Nat.card R * 3 := by rw [hRcard']; omega
  have hDfacts : ∀ p ∈ (dPairs X).toList, ∃ D : Subgroup (Equiv.Perm (Fin X.n)), D ≤ Q ∧
      IsElemAbelian 3 D ∧ 81 ≤ Nat.card D ∧
      ∀ (t : Array ℕ) (x : Equiv.Perm (Fin X.n)), Rep X.n t x → t ∈ p.2.pts.toList → x ∈ D := by
    intro p hp
    have hp' := List.all_eq_true.1 hD p hp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp'
    obtain ⟨⟨henum, hsize⟩, hab⟩ := hp'
    obtain ⟨ws, hws, rfl⟩ := Array.mem_map.1 (Array.mem_toList_iff.1 hp)
    exact dPair_facts hqgv hQgen hdk (hdWl ws hws) henum hsize hab
  refine ⟨Q, R, z, hQP, hQcard', hz3', hz1', hzQ, hzcomm, hRQ, hindex, ?_⟩
  intro s hsR hs3 hsz
  obtain ⟨k, hk, hrep⟩ := enumOK_exists_rep hrk hRenum hsR
  have hc := allLt_spec hcover hk
  simp only [coverOK, Bool.or_eq_true, Bool.not_eq_true', List.any_eq_true,
    Bool.and_eq_true] at hc
  rcases hc with
    ((((h1 | h2) | h3) | h4) | ⟨hArr, hmemH, pp, hmemP, ⟨t1, ht1, he1⟩, ⟨t2, ht2, he2⟩⟩)
  · exfalso
    have h5 := (eqA_iff (rep_compA hrep (rep_compA hrep hrep)) rep_idA).2
      (by rw [← pow_three]; exact hs3)
    rw [h5] at h1
    exact absurd h1 (by simp)
  · exfalso
    exact hsz (by rw [(eqA_iff hrep rep_idA).1 h2]; exact Subgroup.one_mem _)
  · exfalso
    exact hsz (by rw [(eqA_iff hrep hzrep).1 h3]; exact Subgroup.mem_zpowers _)
  · exfalso
    exact hsz (by
      rw [(eqA_iff hrep (rep_compA hzrep hzrep)).1 h4]
      exact Subgroup.mul_mem _ (Subgroup.mem_zpowers z) (Subgroup.mem_zpowers z))
  · obtain ⟨i, hi, hiEq⟩ := List.mem_iff_getElem.1 hmemH
    have hi' : i < (hArrs X).size := by simpa using hi
    have hi'' : i < X.hW.size := by simpa [hArrs] using hi
    have hArrEq : hArr = (hArrs X)[i]! := by
      rw [getElem!_pos _ i hi', ← hiEq]
      simp
    subst hArrEq
    have hv : validA X.n (hArrs X)[i]! = true := allLt_spec hhv hi'
    have hHrep : Rep X.n (hArrs X)[i]! (wordPerm X.n X.pg X.hW[i]!) :=
      mapWord_rep hpgv hhWl hi''
    have hHP : wordPerm X.n X.pg X.hW[i]! ∈ P := wordPerm_mem hP (hhWl i hi'')
    set H := wordPerm X.n X.pg X.hW[i]! with hH
    have hcs := rep_conjA hv hrep
    have hcz := rep_conjA hv hzrep
    rw [permOfArr_eq_of_rep hHrep] at hcs hcz
    obtain ⟨D, hDQ, hDe, hD81, hDmem⟩ := hDfacts pp hmemP
    have hsD : H * s * H⁻¹ ∈ D := hDmem t1 _ (rep_of_eqA hcs he1) ht1
    have hzD : H * z * H⁻¹ ∈ D := hDmem t2 _ (rep_of_eqA hcz he2) ht2
    have hmemE : ∀ x, H * x * H⁻¹ ∈ D → x ∈ D.map (MulAut.conj H⁻¹).toMonoidHom := fun x hx =>
      ⟨H * x * H⁻¹, hx, by simp [mul_assoc]⟩
    refine ⟨D.map (MulAut.conj H⁻¹).toMonoidHom, ?_, ?_, ?_, hmemE s hsD, hmemE z hzD⟩
    · rintro _ ⟨d, hd, rfl⟩
      show H⁻¹ * d * H⁻¹⁻¹ ∈ P
      rw [inv_inv]
      exact P.mul_mem (P.mul_mem (P.inv_mem hHP) (hQP (hDQ hd))) hHP
    · exact CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ D hDe
    · rw [Subgroup.card_map_of_injective (MulAut.conj H⁻¹).injective]
      exact hD81

theorem exists_e81_of_e81Check (X : E81Data) (h : e81Check X = true)
    {J : Subgroup (Equiv.Perm (Fin X.n))} [Finite J]
    (hJ : ∀ l < X.pg.size, permOfArr X.n X.pg[l]! ∈ J)
    (hord : X.qOrd = 3 ^ (Nat.card J).factorization 3) {P : Subgroup J}
    (hP : IsElemAbelian 3 P) (hP27 : Nat.card P = 27) :
    ∃ B E : Subgroup J, B ≤ P ∧ 9 ≤ Nat.card B ∧ IsElemAbelian 3 E ∧ 81 ≤ Nat.card E ∧
      ∀ b ∈ B, ∀ d ∈ E, b * d = d * b := by
  obtain ⟨Q, R, z, hQJ, hQ, hz3, hz1, hzQ, hzc, hRQ, hR, hgood⟩ := e81_sound X h J hJ
  exact exists_e81_of_e27_ambient hQJ (hQ.trans hord) hz3 hz1 hzQ hzc hRQ (by rw [hQ]; exact hR)
    hgood hP hP27

end CFSG.RankThree.PartTwo.Sec4.Item434SporE81
