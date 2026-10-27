module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42J2Perm
public import Certificates.Certificate725006
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowConjInvSound
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowEp2Orbit

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.Bridge.J2Excl CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.Schreier CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native

private theorem rep_ep2LineA {n : ℕ} {x y : Array ℕ} {gx gy : Equiv.Perm (Fin n)}
    (hx : Rep n x gx) (hy : Rep n y gy) :
    ∀ i, Rep n (ep2LineA n x y i) (ep2Line gx gy i)
  | 0 => by simpa [ep2LineA, ep2Line] using hy
  | i + 1 => by
      simpa [ep2LineA, ep2Line] using rep_compA hx (rep_powA hy i)

private theorem ep2Base_of_check {n p : ℕ} {x y : Array ℕ} {gx gy : Equiv.Perm (Fin n)}
    (hx : Rep n x gx) (hy : Rep n y gy) (hc : ep2BaseCheck n p x y = true) :
    gx ^ p = 1 ∧ gy ^ p = 1 ∧ gx ≠ 1 ∧ gx * gy = gy * gx ∧
      (∀ j < p, gy ≠ gx ^ j) := by
  simp only [ep2BaseCheck, Bool.and_eq_true, Bool.not_eq_true'] at hc
  obtain ⟨⟨⟨⟨hxp, hyp⟩, hxne⟩, hcomm⟩, hnotmem⟩ := hc
  refine ⟨(eqA_iff (rep_powA hx p) (rep_idA (n := n))).1 hxp,
    (eqA_iff (rep_powA hy p) (rep_idA (n := n))).1 hyp,
    ne_of_eqA_eq_false hx (rep_idA (n := n)) hxne,
    (eqA_iff (rep_compA hx hy) (rep_compA hy hx)).1 hcomm, ?_⟩
  intro j hj
  exact ne_of_eqA_eq_false hy (rep_powA hx j)
    (by simpa only [Bool.not_eq_true'] using allLt_iff.1 hnotmem j hj)

private theorem ep2PartCheck_sound {n : ℕ} {K : Subgroup (Equiv.Perm (Fin n))}
    {x y : Array ℕ} {gx gy : Equiv.Perm (Fin n)} {idx : List (ℕ × ℕ × ℕ)} {ms : List PArr}
    (hx : Rep n x gx) (hy : Rep n y gy)
    (hms : ∀ m ∈ ms, ∃ g ∈ K, PRep n m g)
    (hc : ep2PartCheck n x y idx ms = true) :
    ∀ q ∈ idx, ∃ m ∈ K, m * ep2Line gx gy q.1 * m⁻¹ = ep2Line gx gy q.2.1 ^ q.2.2 := by
  simp only [ep2PartCheck, Bool.and_eq_true, List.all_eq_true] at hc
  obtain ⟨hlen, hall⟩ := hc
  have hlen' : idx.length = ms.length := by simpa using hlen
  intro q hq
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hq
  have hmi : i < ms.length := by rwa [← hlen']
  have hz : (idx[i], ms[i]) ∈ idx.zip ms := by
    rw [List.mem_iff_getElem]
    refine ⟨i, ?_, ?_⟩
    · rw [List.length_zip, hlen', Nat.min_self]
      exact hmi
    · exact List.getElem_zip
  have hci := hall (idx[i], ms[i]) hz
  obtain ⟨m, hm, hmrep⟩ := hms ms[i] (List.getElem_mem hmi)
  refine ⟨m, hm, ?_⟩
  have hleft : Rep n (compA n (compA n ms[i].1 (ep2LineA n x y (idx[i]).1)) ms[i].2)
      (m * ep2Line gx gy (idx[i]).1 * m⁻¹) := by
    have := rep_compA (rep_compA hmrep.1 (rep_ep2LineA hx hy (idx[i]).1)) hmrep.2
    simpa [mul_assoc] using this
  have hright : Rep n (powA n (ep2LineA n x y (idx[i]).2.1) (idx[i]).2.2)
      (ep2Line gx gy (idx[i]).2.1 ^ (idx[i]).2.2) :=
    rep_powA (rep_ep2LineA hx hy (idx[i]).2.1) (idx[i]).2.2
  exact (eqA_iff hleft hright).1 hci

private theorem j2_ep2_partners {x y : Equiv.Perm (Fin 315)}
    (hpart : ∀ q ∈ j2E25PartIdx, ∃ m ∈ j2P,
      m * ep2Line x y q.1 * m⁻¹ = ep2Line x y q.2.1 ^ q.2.2) :
    ∀ i ≤ 5, ∃ j ≤ 5, ∃ k ≤ 5, j ≠ i ∧ k ≠ i ∧ j ≠ k ∧
      (∃ m ∈ j2P, ∃ e : ℕ, (e = 1 ∨ e = 2) ∧
        m * ep2Line x y i * m⁻¹ = ep2Line x y j ^ e) ∧
      (∃ m ∈ j2P, ∃ e : ℕ, (e = 1 ∨ e = 2) ∧
        m * ep2Line x y i * m⁻¹ = ep2Line x y k ^ e) := by
  intro i hi
  interval_cases i
  · refine ⟨1, by norm_num, 3, by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_⟩
    · obtain ⟨m, hm, he⟩ := hpart (0, 1, 2) (by simp [j2E25PartIdx])
      exact ⟨m, hm, 2, Or.inr rfl, he⟩
    · obtain ⟨m, hm, he⟩ := hpart (0, 3, 2) (by simp [j2E25PartIdx])
      exact ⟨m, hm, 2, Or.inr rfl, he⟩
  · refine ⟨0, by norm_num, 3, by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_⟩
    · obtain ⟨m, hm, he⟩ := hpart (1, 0, 2) (by simp [j2E25PartIdx])
      exact ⟨m, hm, 2, Or.inr rfl, he⟩
    · obtain ⟨m, hm, he⟩ := hpart (1, 3, 1) (by simp [j2E25PartIdx])
      exact ⟨m, hm, 1, Or.inl rfl, he⟩
  · refine ⟨5, by norm_num, 4, by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_⟩
    · obtain ⟨m, hm, he⟩ := hpart (2, 5, 2) (by simp [j2E25PartIdx])
      exact ⟨m, hm, 2, Or.inr rfl, he⟩
    · obtain ⟨m, hm, he⟩ := hpart (2, 4, 2) (by simp [j2E25PartIdx])
      exact ⟨m, hm, 2, Or.inr rfl, he⟩
  · refine ⟨0, by norm_num, 1, by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_⟩
    · obtain ⟨m, hm, he⟩ := hpart (3, 0, 2) (by simp [j2E25PartIdx])
      exact ⟨m, hm, 2, Or.inr rfl, he⟩
    · obtain ⟨m, hm, he⟩ := hpart (3, 1, 1) (by simp [j2E25PartIdx])
      exact ⟨m, hm, 1, Or.inl rfl, he⟩
  · refine ⟨2, by norm_num, 5, by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_⟩
    · obtain ⟨m, hm, he⟩ := hpart (4, 2, 2) (by simp [j2E25PartIdx])
      exact ⟨m, hm, 2, Or.inr rfl, he⟩
    · obtain ⟨m, hm, he⟩ := hpart (4, 5, 1) (by simp [j2E25PartIdx])
      exact ⟨m, hm, 1, Or.inl rfl, he⟩
  · refine ⟨2, by norm_num, 4, by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_⟩
    · obtain ⟨m, hm, he⟩ := hpart (5, 2, 2) (by simp [j2E25PartIdx])
      exact ⟨m, hm, 2, Or.inr rfl, he⟩
    · obtain ⟨m, hm, he⟩ := hpart (5, 4, 1) (by simp [j2E25PartIdx])
      exact ⟨m, hm, 1, Or.inl rfl, he⟩

theorem j2_e25_package :
    ∃ x₁ ∈ j2P, ∃ x₂ ∈ j2P, x₁ ^ 5 = 1 ∧ x₂ ^ 5 = 1 ∧ x₁ ≠ 1 ∧ x₁ * x₂ = x₂ * x₁ ∧
      (∀ j < 5, x₂ ≠ x₁ ^ j) ∧
      (∀ i ≤ 5, ∃ j ≤ 5, ∃ k ≤ 5, j ≠ i ∧ k ≠ i ∧ j ≠ k ∧
        (∃ m ∈ j2P, ∃ e : ℕ, (e = 1 ∨ e = 2) ∧
          m * ep2Line x₁ x₂ i * m⁻¹ = ep2Line x₁ x₂ j ^ e) ∧
        (∃ m ∈ j2P, ∃ e : ℕ, (e = 1 ∨ e = 2) ∧
          m * ep2Line x₁ x₂ i * m⁻¹ = ep2Line x₁ x₂ k ^ e)) ∧
      (∀ t ∈ [tp 315 (j2CentTbl 17), tp 315 (j2CentTbl 31)], ∃ h ∈ j2P,
        t * (h * x₁ * h⁻¹) * t⁻¹ = (h * x₁ * h⁻¹)⁻¹) ∧
      GenSet j2P 3 {tp 315 (j2CentTbl 9)} := by
  obtain ⟨x, hxP, hx⟩ := regIn_j2P.word j2E25WX
  obtain ⟨y, hyP, hy⟩ := regIn_j2P.word j2E25WY
  obtain ⟨hB, hBP, hBrep⟩ := regIn_j2P.word j2E25WHB
  obtain ⟨hA, hAP, hArep⟩ := regIn_j2P.word j2E25WHA
  have hxw : PRep 315 (j2WordP j2E25WX) x := by simpa [j2WordP] using hx
  have hyw : PRep 315 (j2WordP j2E25WY) y := by simpa [j2WordP] using hy
  have hBw : PRep 315 (j2WordP j2E25WHB) hB := by simpa [j2WordP] using hBrep
  have hAw : PRep 315 (j2WordP j2E25WHA) hA := by simpa [j2WordP] using hArep
  have hms : ∀ m ∈ j2E25WMs.map j2WordP, ∃ g ∈ j2P, PRep 315 m g := by
    intro m hm
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hm
    obtain ⟨g, hg, hrep⟩ := regIn_j2P.word w
    exact ⟨g, hg, by simpa [j2WordP] using hrep⟩
  have hc := Certificates.certificate725006
  simp only [j2E25Check, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨hbase, hpartc⟩, hcB⟩, hcA⟩, hc3⟩ := hc
  obtain ⟨hx5, hy5, hxne, hcomm, hnotmem⟩ := ep2Base_of_check hxw.1 hyw.1 hbase
  have hpart : ∀ q ∈ j2E25PartIdx, ∃ m ∈ j2P,
      m * ep2Line x y q.1 * m⁻¹ = ep2Line x y q.2.1 ^ q.2.2 :=
    ep2PartCheck_sound hxw.1 hyw.1 hms hpartc
  have hsq9 : tp 315 (j2CentTbl 9) * tp 315 (j2CentTbl 9) = 1 := by
    have h := rows_sq (j2Rows[0]'(by simp [j2Rows])) (List.getElem_mem _)
    simpa [j2Rows] using h
  have hsq17 : tp 315 (j2CentTbl 17) * tp 315 (j2CentTbl 17) = 1 := by
    have h := rows_sq (j2Rows[1]'(by simp [j2Rows])) (List.getElem_mem _)
    simpa [j2Rows] using h
  have hsq31 : tp 315 (j2CentTbl 31) * tp 315 (j2CentTbl 31) = 1 := by
    have h := rows_sq (j2Rows[2]'(by simp [j2Rows])) (List.getElem_mem _)
    simpa [j2Rows] using h
  have hT17 : PRep 315 (j2TP 17) (tp 315 (j2CentTbl 17)) :=
    pRep_j2TP (j2_perm_check.2.2 17 (by simp)) hsq17
  have hT31 : PRep 315 (j2TP 31) (tp 315 (j2CentTbl 31)) :=
    pRep_j2TP (j2_perm_check.2.2 31 (by simp)) hsq31
  have hT9 : PRep 315 (j2TP 9) (tp 315 (j2CentTbl 9)) :=
    pRep_j2TP (j2_perm_check.2.2 9 (by simp)) hsq9
  refine ⟨x, hxP, y, hyP, hx5, hy5, hxne, hcomm, hnotmem, j2_ep2_partners hpart, ?_, ?_⟩
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact ⟨hB, hBP, inv_of_conjInvCheck hT17 hBw hxw hcB⟩
    · exact ⟨hA, hAP, inv_of_conjInvCheck hT31 hAw hxw hcA⟩
  · exact gen_of_check hT9 (by decide) hc3

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
