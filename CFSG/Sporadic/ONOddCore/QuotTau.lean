module

public import CFSG.Sporadic.ONOddCore.QuotOuterCheck
public import CFSG.Sporadic.Schreier.ONIntersection
public import CFSG.Sporadic.ONOddCore.QuotBasics
public import CFSG.Sporadic.ONOddCore.SigmaElem

public noncomputable section

namespace CFSG.Sporadic.ONOddCore

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.PSL3Four.Native
open CFSG.ComponentClassification.PSL3Four (TabRep Enumerates)

theorem prep_posArr {n : ℕ} {gs : Array (Array ℕ)} {G : List (Equiv.Perm (Fin n))}
    (hG : ∀ l, 1 ≤ l → l ≤ G.length → PRep n (gs.getD (l - 1) (pid n)) (G.getD (l - 1) 1)) :
    ∀ w : List ℕ, (∀ l ∈ w, 1 ≤ l ∧ l ≤ G.length) → PRep n (posArr n gs w) (evalPos G w)
  | [], _ => by simpa [posArr, evalPos] using prep_pid (n := n)
  | l :: w, hw => by
    have ih := prep_posArr hG w fun i hi => hw i (List.mem_cons_of_mem _ hi)
    obtain ⟨h1, h2⟩ := hw l List.mem_cons_self
    rw [evalPos_cons]
    exact prep_pcomp (hG l h1 h2) ih

theorem quot_facts :
    (∀ j < 2, peq 120 (qgArr j) (pcomp 120 Data.quotientConjugator
      (pcomp 120 Data.M120Chain.generators[j]! (pinvCand 120 Data.quotientConjugator))) = true) ∧
      (∀ m < 12, peq 120 (posArr 120 #[qgArr 0, qgArr 1] xWords[m]!)
        Data.PSL120Chain.generators[m]! = true) ∧
      (∀ w ∈ xWords, ∀ l ∈ w, 1 ≤ l ∧ l ≤ 2) ∧
      ∀ r ∈ localCert.records, recordCheck (indexOf m120Enum.tabs) r = true := by
  have h := quot_cert
  simp only [quotCheck, Bool.and_eq_true, Array.all_eq_true', List.all_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨fun j hj => allBelowN_spec h1 hj, fun m hm => allBelowN_spec h2 hm, h3, h4⟩

theorem record_facts {r : QuotRecord} (hr : r ∈ localCert.records) :
    (∀ j < 2, found (indexOf m120Enum.tabs) m120Enum.tabs
      (pcomp 120 (pinvCand 120 Data.quotientConjugator)
        (pcomp 120 (qiArr r j) Data.quotientConjugator)) = true) ∧
      treeOK (leftStep 240 (pairGens r)) 2 pairRoot
        (bfs (leftStep 240 (pairGens r)) 2 pairRoot 50000) = true ∧
      (bfs (leftStep 240 (pairGens r)) 2 pairRoot 50000).tabs.size = 40320 ∧
      ∀ m < 12, peq 120 (posArr 120 #[qiArr r 0, qiArr r 1] xWords[m]!)
        (posArr 120 Data.PSL120Chain.generators (sigWord r.diag r.field r.graph m)) = true := by
  have h := quot_facts.2.2.2 r hr
  simp only [recordCheck, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨fun j hj => allBelowN_spec h1 hj, h2, h3, fun m hm => allBelowN_spec h4 hm⟩

theorem form_facts :
    (∀ a ∈ localCert.quotGens, permArr120 a = true) ∧ localCert.quotGens.length = 2 ∧
      ∀ r ∈ localCert.records, r.images.length = 2 ∧ ∀ a ∈ r.images, permArr120 a = true := by
  obtain ⟨h1, h2, -, h4, -⟩ := r3e_on_local_automorphism_certificate_data
  exact ⟨h2, h1, fun r hr => ⟨(h4 r hr).1, (h4 r hr).2.1⟩⟩

theorem prep_of_permArr120 {a : Array ℕ} (h : permArr120 a = true) :
    PRep 120 a (permOfArr 120 a) ∧ a.size = 120 := by
  simp only [permArr120, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨(prep_permOfArr h.2).1, h.1⟩

theorem getD_mem {α : Type*} {l : List α} {j : ℕ} (hj : j < l.length) (d : α) :
    l.getD j d ∈ l := by
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem hj

theorem prep_qgArr
    {j : ℕ} (hj : j < 2) : PRep 120 (qgArr j) (qGenPerm j) ∧ (qgArr j).size = 120 :=
  prep_of_permArr120 (form_facts.1 _ (getD_mem (by rw [form_facts.2.1]; exact hj) _))

theorem prep_qiArr
    {r : QuotRecord} (hr : r ∈ localCert.records) {j : ℕ} (hj : j < 2) :
    PRep 120 (qiArr r j) (qImgPerm r j) ∧ (qiArr r j).size = 120 :=
  prep_of_permArr120 ((form_facts.2.2 r hr).2 _
    (getD_mem (by rw [(form_facts.2.2 r hr).1]; exact hj) _))

theorem qGenPerm_eq
    {j : ℕ} (hj : j < 2) :
    qGenPerm j = onu * permOfArr 120 Data.M120Chain.generators[j]! * onu⁻¹ := by
  have hg := prep_smallGen small_chain_certs.2.1 j (by rw [m120_gens_size]; exact hj)
  have h := prep_pcomp prep_u (prep_pcomp hg prep_u_inv)
  rw [← mul_assoc] at h
  exact eq_of_peq (prep_qgArr hj).1 h (quot_facts.1 j hj)

theorem qGroup_eq_RM :
    qGroup = RM := by
  rw [RM_eq_map, rhoM_range, onM120Chain, smallChain_sub, MonoidHom.map_closure, qGroup,
    m120_gens_size]
  congr 1
  ext g
  simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false, Set.mem_image]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨_, ⟨0, by norm_num, rfl⟩, by rw [qGenPerm_eq (by norm_num)]; rfl⟩
    · exact ⟨_, ⟨1, by norm_num, rfl⟩, by rw [qGenPerm_eq (by norm_num)]; rfl⟩
  · rintro ⟨_, ⟨j, hj, rfl⟩, rfl⟩
    have hj2 : j < 2 := hj
    interval_cases j
    · left; rw [qGenPerm_eq (by norm_num)]; rfl
    · right; rw [qGenPerm_eq (by norm_num)]; rfl

theorem qGenPerm_mem_RM
    {j : ℕ} (hj : j < 2) : qGenPerm j ∈ RM :=
  qGroup_eq_RM ▸ qGenPerm_mem j hj

theorem qImgPerm_mem_RM
    {r : QuotRecord} (hr : r ∈ localCert.records) {j : ℕ} (hj : j < 2) :
    qImgPerm r j ∈ RM := by
  have hf := (record_facts hr).1 j hj
  obtain ⟨hp, hs⟩ := prep_qiArr hr hj
  have hrep := prep_pcomp prep_u_inv (prep_pcomp hp prep_u)
  have htab : TabRep (pcomp 120 (pinvCand 120 Data.quotientConjugator)
      (pcomp 120 (qiArr r j) Data.quotientConjugator)) (onu⁻¹ * (qImgPerm r j * onu)) :=
    tabRep_of_prep Array.size_ofFn hrep
  obtain ⟨g, hg, hgrep⟩ := m120_enumerates.sound _
    (CFSG.ComponentClassification.PSL3Four.mem_of_found hf)
  have e : g = onu⁻¹ * (qImgPerm r j * onu) := hgrep.perm_eq htab
  rw [RM_eq_map, rhoM_range]
  refine ⟨g, hg, ?_⟩
  rw [e]
  show onu * (onu⁻¹ * (qImgPerm r j * onu)) * onu⁻¹ = qImgPerm r j
  group

theorem xGen_eq
    {m : ℕ} (hm : m < 12) : xGen m = evalPos [qGenPerm 0, qGenPerm 1] xWords[m]! := by
  have hw : ∀ l ∈ xWords[m]!, 1 ≤ l ∧ l ≤ [qGenPerm 0, qGenPerm 1].length := fun l hl => by
    have h := quot_facts.2.2.1 _ (by
      rw [getElem!_pos xWords m (by simpa [xWords] using hm)]; exact Array.getElem_mem _) l hl
    simpa using h
  have hrep := prep_posArr (n := 120) (gs := #[qgArr 0, qgArr 1])
    (G := [qGenPerm 0, qGenPerm 1]) (fun l h1 h2 => by
      simp only [List.length_cons, List.length_nil] at h2
      interval_cases l
      · exact (prep_qgArr (by norm_num)).1
      · exact (prep_qgArr (by norm_num)).1) _ hw
  exact (eq_of_peq hrep (prep_smallGen small_chain_certs.2.2.2.2.1 m
    (by rw [psl120_size]; exact hm)) (quot_facts.2.1 m hm)).symm

end CFSG.Sporadic.ONOddCore
