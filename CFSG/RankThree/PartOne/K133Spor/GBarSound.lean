module

public import CFSG.RankThree.PartOne.K133Spor.GBarInputs
public import CFSG.RankThree.PartOne.K133Spor.HSPairSound

public section

namespace CFSG.RankThree.PartOne.K133Spor

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native

theorem commA_iff {n : ℕ} {a b : Array ℕ} {A B : Equiv.Perm (Fin n)} (ha : Rep n a A)
    (hb : Rep n b B) : commA n a b = true ↔ A * B = B * A := by
  unfold commA
  rw [allLt_iff]
  constructor
  · intro H
    refine Equiv.ext fun x => Fin.ext ?_
    have h := H x x.2
    rw [beq_iff_eq, hb.apply x.2, ha.apply (B x).2, ha.apply x.2, hb.apply (A x).2] at h
    simpa using h
  · intro H i hi
    rw [beq_iff_eq, hb.apply hi, ha.apply hi, ha.apply (B ⟨i, hi⟩).2, hb.apply (A ⟨i, hi⟩).2]
    have := congrArg (fun p : Equiv.Perm (Fin n) => (p ⟨i, hi⟩ : ℕ)) H
    simpa using this

theorem isFiveA_iff {n : ℕ} {f : Array ℕ} {F : Equiv.Perm (Fin n)} (hf : Rep n f F) :
    isFiveA n f = true ↔ F ^ 5 = 1 ∧ F ≠ 1 := by
  unfold isFiveA
  rw [Bool.and_eq_true, eqA_iff (rep_powA5 hf) rep_idA, Bool.not_eq_true', Bool.eq_false_iff,
    ne_eq, eqA_iff hf rep_idA]

theorem isTwoA_iff {n : ℕ} {u : Array ℕ} {U : Equiv.Perm (Fin n)} (hu : Rep n u U) :
    isTwoA n u = true ↔ U * U = 1 ∧ U ≠ 1 := by
  unfold isTwoA
  rw [Bool.and_eq_true, eqA_iff (rep_compA hu hu) rep_idA, Bool.not_eq_true', Bool.eq_false_iff,
    ne_eq, eqA_iff hu rep_idA]

theorem pts_mem {c : ArrCert} {i : ℕ} (hi : i < c.pts.size) : c.pts[i]! ∈ c.pts := by
  rw [getElem!_pos c.pts i hi]
  exact Array.getElem_mem hi

theorem mem_fives {n : ℕ} {c : ArrCert} {i : ℕ} (hi : i < c.pts.size) {F : Equiv.Perm (Fin n)}
    (hF : Rep n c.pts[i]! F) (h5 : F ^ 5 = 1) (h1 : F ≠ 1) :
    c.pts[i]! ∈ c.pts.filter (isFiveA n) := by
  rw [Array.mem_filter]
  exact ⟨pts_mem hi, (isFiveA_iff hF).2 ⟨h5, h1⟩⟩

theorem mem_twos {n : ℕ} {c : ArrCert} {i : ℕ} (hi : i < c.pts.size) {U : Equiv.Perm (Fin n)}
    (hU : Rep n c.pts[i]! U) (h2 : U * U = 1) (h1 : U ≠ 1) :
    c.pts[i]! ∈ c.pts.filter (isTwoA n) := by
  rw [Array.mem_filter]
  exact ⟨pts_mem hi, (isTwoA_iff hU).2 ⟨h2, h1⟩⟩

theorem gbar_invFree {n : ℕ} {gs : Array (Array ℕ)} {ps : List ℕ} {c : ArrCert}
    (hps : ∀ p ∈ ps, p < n) (henum : enumOK n gs ps c = true)
    (hcheck : gbarCheck n c.pts = true) {u a b : Equiv.Perm (Fin n)}
    (hu : u ∈ Subgroup.closure (permsA n gs)) (ha : a ∈ Subgroup.closure (permsA n gs))
    (hb : b ∈ Subgroup.closure (permsA n gs)) (hu2 : u * u = 1) (hu1 : u ≠ 1) (ha5 : a ^ 5 = 1)
    (ha1 : a ≠ 1) (hb5 : b ^ 5 = 1) (hb1 : b ≠ 1) (hba : b ∉ Subgroup.zpowers a)
    (hab : a * b = b * a) (hua : u * a = a * u) (hub : u * b = b * u) : False := by
  obtain ⟨iu, hiu, hRu⟩ := enumOK_exists_rep hps henum hu
  obtain ⟨ia, hia, hRa⟩ := enumOK_exists_rep hps henum ha
  obtain ⟨ib, hib, hRb⟩ := enumOK_exists_rep hps henum hb
  unfold gbarCheck at hcheck
  simp only [Bool.and_eq_true] at hcheck
  obtain ⟨hA, -⟩ := hcheck
  rw [Array.all_eq_true_iff_forall_mem] at hA
  have h1 := hA _ (mem_twos hiu hRu hu2 hu1)
  rw [Array.all_eq_true_iff_forall_mem] at h1
  have h2 := h1 _ (Array.mem_filter.2 ⟨mem_fives hia hRa ha5 ha1, (commA_iff hRu hRa).2 hua⟩)
  rw [Array.all_eq_true_iff_forall_mem] at h2
  have h3 := h2 _ (Array.mem_filter.2 ⟨mem_fives hib hRb hb5 hb1, (commA_iff hRu hRb).2 hub⟩)
  have hC : commA n c.pts[ia]! c.pts[ib]! = true := (commA_iff hRa hRb).2 hab
  rw [hC] at h3
  simp only [Bool.not_true, Bool.false_or] at h3
  exact hba (memLineA_spec hRa hRb h3)

theorem gbar_fixFree {n : ℕ} {gs : Array (Array ℕ)} {ps : List ℕ} {c : ArrCert}
    (hps : ∀ p ∈ ps, p < n) (henum : enumOK n gs ps c = true)
    (hcheck : gbarCheck n c.pts = true) {a b : Equiv.Perm (Fin n)}
    (ha : a ∈ Subgroup.closure (permsA n gs)) (hb : b ∈ Subgroup.closure (permsA n gs))
    (ha5 : a ^ 5 = 1) (ha1 : a ≠ 1) (hb5 : b ^ 5 = 1) (hb1 : b ≠ 1)
    (hba : b ∉ Subgroup.zpowers a) (hab : a * b = b * a) (m : Fin n) (hm : (m : ℕ) ≠ 0)
    (ham : a m = m) (hbm : b m = m) : False := by
  obtain ⟨ia, hia, hRa⟩ := enumOK_exists_rep hps henum ha
  obtain ⟨ib, hib, hRb⟩ := enumOK_exists_rep hps henum hb
  unfold gbarCheck at hcheck
  simp only [Bool.and_eq_true] at hcheck
  obtain ⟨-, hB⟩ := hcheck
  rw [Array.all_eq_true_iff_forall_mem] at hB
  have h1 := hB _ (mem_fives hia hRa ha5 ha1)
  rw [Array.all_eq_true_iff_forall_mem] at h1
  have h2 := h1 _ (mem_fives hib hRb hb5 hb1)
  have hC : commA n c.pts[ia]! c.pts[ib]! = true := (commA_iff hRa hRb).2 hab
  have hM : memLineA n c.pts[ia]! c.pts[ib]! = false := by
    by_contra hne
    exact hba (memLineA_spec hRa hRb (by simpa using hne))
  rw [hC, hM] at h2
  simp only [Bool.not_true, Bool.or_false] at h2
  unfold fixFreeA at h2
  have h3 := allLt_spec h2 m.2
  rw [hRa.apply m.2, hRb.apply m.2] at h3
  have e1 : (a ⟨m, m.2⟩ : ℕ) = m := by rw [Fin.eta, ham]
  have e2 : (b ⟨m, m.2⟩ : ℕ) = m := by rw [Fin.eta, hbm]
  rw [e1, e2] at h3
  simp [hm] at h3

end CFSG.RankThree.PartOne.K133Spor
