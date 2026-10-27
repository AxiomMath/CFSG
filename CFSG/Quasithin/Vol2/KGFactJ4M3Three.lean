module

public import CFSG.Quasithin.Vol2.KGFactJ4M3KL
public import Certificates.Certificate725101

public section

namespace CFSG.Quasithin.J4M3

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2 CFSG.Sporadic.J4.Native Matrix
open CFSG.Quasithin.J4Loc CFSG.Quasithin.J4Fam CFSG.Quasithin.KGC31 CFSG.Quasithin.Special2
open scoped commutatorElement

@[expose] noncomputable def y3J : J := wordProd xJ y3Word

@[expose] noncomputable def a3J (c : ℕ) : J :=
  (List.range 12).foldl (fun acc j => if c.testBit j then acc * qJ j else acc) 1

noncomputable abbrev q3Rows : Array (Array V2) :=
  ((List.range 12).map fun j =>
    commRows (pRows (locMats ()) (locInvs ()) T₀ j) (pInvRows (locMats ()) (locInvs ()) T₀ j)
      (wordRows (locMats ()) (locInvs ()) xWord)
      (wordRows (locMats ()) (locInvs ()) (invWord xWord))).toArray

theorem v3Masks_mem : ∀ i < 12, v3Masks.getD i 0 ∈ v0Masks := by decide

theorem q3Rows_get {j : ℕ} (hj : j < 12) :
    q3Rows[j]?.getD idRows = commRows (pRows (locMats ()) (locInvs ()) T₀ j)
      (pInvRows (locMats ()) (locInvs ()) T₀ j) (wordRows (locMats ()) (locInvs ()) xWord)
      (wordRows (locMats ()) (locInvs ()) (invWord xWord)) := by
  simp [q3Rows, hj]

theorem Mx_foldl_ite {P : ℕ → Bool} {f : ℕ → J} {F : ℕ → Array V2} :
    ∀ (l : List ℕ), (∀ j ∈ l, Mx (f j) = rowsMatrix (F j)) → ∀ (acc : J) (accR : Array V2),
      Mx acc = rowsMatrix accR →
      Mx (l.foldl (fun a j => if P j then a * f j else a) acc) =
        rowsMatrix (l.foldl (fun a j => if P j then mulRows a (F j) else a) accR)
  | [], _, _, _, h => h
  | j :: l, hf, acc, accR, h => by
    simp only [List.foldl_cons]
    refine Mx_foldl_ite l (fun k hk => hf k (List.mem_cons_of_mem _ hk)) _ _ ?_
    split_ifs
    · rw [map_mul, h, hf j List.mem_cons_self, rowsMatrix_mulRows]
    · exact h

theorem foldl_ite_mem {P : ℕ → Bool} {f : ℕ → J} {S : Subgroup J} :
    ∀ (l : List ℕ), (∀ j ∈ l, f j ∈ S) → ∀ acc ∈ S,
      l.foldl (fun a j => if P j then a * f j else a) acc ∈ S
  | [], _, _, h => h
  | j :: l, hf, acc, h => by
    simp only [List.foldl_cons]
    refine foldl_ite_mem l (fun k hk => hf k (List.mem_cons_of_mem _ hk)) _ ?_
    split_ifs
    · exact S.mul_mem h (hf j List.mem_cons_self)
    · exact h

section Mat

theorem qJ_mem_Q {j : ℕ} (hj : j < 12) : qJ j ∈ Qg := mem_tabGroup (q := qF) ⟨j, hj⟩

theorem a3J_mem_Q (c : ℕ) : a3J c ∈ Qg :=
  foldl_ite_mem _ (fun _ hj => qJ_mem_Q (List.mem_range.mp hj)) 1 Qg.one_mem

theorem Mx_y3J : Mx y3J = rowsMatrix (wordRows (locMats ()) (locInvs ()) y3Word) :=
  Mx_wordProd j4Facts.mat _

theorem Mx_a3J (c : ℕ) : Mx (a3J c) = rowsMatrix (a3Rows q3Rows c) := by
  refine Mx_foldl_ite _ (fun j hj => ?_) 1 idRows (by rw [map_one, rowsMatrix_idRows])
  rw [q3Rows_get (List.mem_range.mp hj)]
  exact Mx_qJ j4Facts.mat j (List.mem_range.mp hj)

theorem chkY3_facts :
    eqRows (mulRows (mulRows (wordRows (locMats ()) (locInvs ()) y3Word)
      (wordRows (locMats ()) (locInvs ()) y3Word)) (wordRows (locMats ()) (locInvs ()) y3Word))
      idRows = true ∧
    centV0 T₀ (wordRows (locMats ()) (locInvs ()) y3Word) = true ∧
    ∀ i < 12, eqRows (mulRows (a3Rows q3Rows (a3Masks.getD i 0)) (wordRows (locMats ()) (locInvs ()) y3Word))
      (mulRows (mulRows (mulRows (q3Rows[i]?.getD idRows) (eR T₀ (v3Masks.getD i 0)))
        (wordRows (locMats ()) (locInvs ()) y3Word)) (a3Rows q3Rows (a3Masks.getD i 0))) = true := by
  have h := Certificates.certificate725101
  dsimp only [chkY3] at h
  unfold chkY3With at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem y3J_pow_three : y3J ^ 3 = 1 := by
  refine eq_of_eqRows' ?_ (by rw [map_one, rowsMatrix_idRows]) chkY3_facts.1
  rw [pow_three, ← mul_assoc, map_mul, map_mul, Mx_y3J, rowsMatrix_mulRows, rowsMatrix_mulRows]

theorem y3J_mem_centralizer :
    y3J ∈ Subgroup.centralizer (V0 : Set J) := by
  have hM := j4Facts.mat
  have h := chkY3_facts.2.1
  unfold centV0 at h
  rw [List.all_eq_true] at h
  have hc : ∀ c ∈ v0Gens, y3J * eta uJ 11 c = eta uJ 11 c * y3J := fun c hc =>
    eq_of_eqRows' (by rw [map_mul, Mx_y3J, Mx_eta' hM, rowsMatrix_mulRows])
      (by rw [map_mul, Mx_y3J, Mx_eta' hM, rowsMatrix_mulRows]) (h c hc)
  have hle : V0 ≤ Subgroup.centralizer ({y3J} : Set J) := by
    rw [V0, Subgroup.closure_le]
    intro g hg
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact (hc 422 (by simp [v0Gens])).symm
    · exact (hc 553 (by simp [v0Gens])).symm
    · exact (hc 1131 (by simp [v0Gens])).symm
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hv))

theorem a3J_mul_y3J {i : ℕ} (hi : i < 12) :
    a3J (a3Masks.getD i 0) * y3J =
      qJ i * eta uJ 11 (v3Masks.getD i 0) * y3J * a3J (a3Masks.getD i 0) := by
  have hM := j4Facts.mat
  refine eq_of_eqRows' (by rw [map_mul, Mx_a3J, Mx_y3J, rowsMatrix_mulRows]) ?_ (chkY3_facts.2.2 i hi)
  rw [map_mul, map_mul, map_mul, Mx_a3J, Mx_y3J, Mx_qJ hM i hi, Mx_eta' hM, q3Rows_get hi,
    rowsMatrix_mulRows, rowsMatrix_mulRows, rowsMatrix_mulRows]

end Mat

section Core

theorem Q_le_of_decomp {Y : Subgroup J}
    (hdec : ∀ i : Fin 12, ∃ a ∈ Y, ∃ b ∈ V0, qF i = a * b) : Qg ≤ Y := by
  choose a ha b hb hab using hdec
  have haQ : ∀ i, a i ∈ Qg := fun i => by
    have e : a i = qF i * (b i)⁻¹ := by rw [hab i]; group
    rw [e]
    exact Qg.mul_mem (mem_tabGroup i) (Qg.inv_mem (V0_le_Q (hb i)))
  have hcomm : ∀ i j, ⁅qF i, qF j⁆ ∈ Y := by
    intro i j
    rw [hab i, hab j, commutatorElement_mul_V0 (haQ i) (hb i) (haQ j) (hb j),
      commutatorElement_def]
    exact Y.mul_mem (Y.mul_mem (Y.mul_mem (ha i) (ha j)) (Y.inv_mem (ha i))) (Y.inv_mem (ha j))
  have hV0 : eSub hv0 ≤ Y := by
    rw [eSub_eq_closure, Subgroup.closure_le]
    rintro _ ⟨k, rfl⟩
    obtain ⟨i, j, e⟩ := v0_comm k
    rw [e]
    exact hcomm i j
  have hV0' : V0 ≤ Y := eSub_v0 ▸ hV0
  refine sup_le ((Subgroup.closure_le _).mpr ?_) hV0
  rintro _ ⟨i, rfl⟩
  rw [hab i]
  exact Y.mul_mem (ha i) (hV0' (hb i))

theorem Q_le_of_normal_y3 {Y : Subgroup J} (hYM : Y ≤ M3)
    (hY : M3 ≤ Subgroup.normalizer (Y : Set J)) {y' : J} (hy : y' ∈ Y) (hyx : y'⁻¹ * y3J ∈ Qg) :
    Qg ≤ Y := by
  obtain ⟨q₀, hq₀, hx⟩ : ∃ q₀ ∈ Qg, y3J = y' * q₀ := ⟨y'⁻¹ * y3J, hyx, by group⟩
  refine Q_le_of_decomp fun i => ?_
  set A := a3J (a3Masks.getD (i : ℕ) 0) with hA
  set v := eta uJ 11 (v3Masks.getD (i : ℕ) 0) with hv
  have hAQ : A ∈ Qg := a3J_mem_Q _
  have hvV : v ∈ V0 := mem_V0_of_mem_v0Masks (v3Masks_mem i i.2)
  have hrel := a3J_mul_y3J (i := (i : ℕ)) i.2
  rw [← hA, ← hv] at hrel
  have hq : qF i = ⁅A, y3J⁆ * v⁻¹ := by
    show qJ i = _
    rw [commutatorElement_def, hrel]
    group
  have hsplit : ⁅A, y3J⁆ = ⁅A, y'⁆ * (y' * ⁅A, q₀⁆ * y'⁻¹) := by
    rw [hx, commutatorElement_def, commutatorElement_def, commutatorElement_def]
    group
  have hAY : ⁅A, y'⁆ ∈ Y := by
    rw [commutatorElement_def]
    exact Y.mul_mem ((Subgroup.mem_normalizer_iff.mp (hY (Q_le_M3 hAQ)) y').mp hy) (Y.inv_mem hy)
  have hw : y' * ⁅A, q₀⁆ * y'⁻¹ ∈ V0 := by
    have hc : ⁅A, q₀⁆ ∈ V0 := by
      rw [← eSub_v0]
      exact qTable.comm_mem hAQ q₀ hq₀
    exact (Subgroup.mem_normalizer_iff.mp (hYM hy) _).mp hc
  refine ⟨⁅A, y'⁆, hAY, y' * ⁅A, q₀⁆ * y'⁻¹ * v⁻¹, V0.mul_mem hw (V0.inv_mem hvV), ?_⟩
  rw [hq, hsplit]
  group

end Core

end CFSG.Quasithin.J4M3
