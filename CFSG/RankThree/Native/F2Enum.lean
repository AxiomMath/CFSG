module

public import CFSG.RankThree.Native.F2Tail
public import CFSG.RankThree.PartOne.KS.ConjWords

public section

namespace CFSG.RankThree.Native.F2

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def pointM (mm : ℕ → ℕ → ℕ) (ngen N : ℕ) (GM PM : ℕ → ℕ)
    (E : ℕ → ℕ → ℕ) (PAR LAB : ℕ → ℕ) (i : ℕ) : Bool :=
  allN ngen (fun k => Nat.blt (E i k) N && Nat.beq (PM (E i k)) (mm (PM i) (GM k))) &&
    (Nat.beq i 0 || (Nat.blt (PAR i) i && Nat.blt (LAB i) ngen &&
      Nat.beq (PM i) (mm (PM (PAR i)) (GM (LAB i)))))

@[expose] noncomputable def keyM (vm : ℕ → ℕ → ℕ) (n : ℕ) (VG LK : ℕ → ℕ) (ps : List ℕ)
    (PM : ℕ → ℕ) (i : ℕ) : ℕ :=
  ps.foldr (fun p acc => Nat.add (LK (vm (VG p) (PM i))) (Nat.mul n acc)) 0

theorem pointM_tree {mm : ℕ → ℕ → ℕ} {ngen N : ℕ} {GM PM : ℕ → ℕ} {E : ℕ → ℕ → ℕ}
    {PAR LAB : ℕ → ℕ} {i : ℕ} (h : pointM mm ngen N GM PM E PAR LAB i = true) (hi : i ≠ 0) :
    PAR i < i ∧ LAB i < ngen ∧ PM i = mm (PM (PAR i)) (GM (LAB i)) := by
  unfold pointM at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq, Nat.blt_eq] at h
  rcases h.2 with h0 | ⟨⟨h1, h2⟩, h3⟩
  · exact absurd h0 hi
  · exact ⟨h1, h2, h3⟩

theorem tree_inv {d : ℕ} (hd : 0 < d) {V : Array ℕ} (hVd : ∀ v ∈ V, v < 2 ^ d)
    {mm : ℕ → ℕ → ℕ} (hmm : ∀ A B, mm A B = mmul d A B) {I : ℕ} (hI : I = idM d)
    {ngen N : ℕ} {GM GMI PM PMI : ℕ → ℕ} {E : ℕ → ℕ → ℕ} {PAR LAB : ℕ → ℕ}
    (hG : ∀ k < ngen, Inv d V (GM k) (GMI k)) (h0 : PM 0 = I) (h0' : PMI 0 = I)
    (hp : ∀ i < N, pointM mm ngen N GM PM E PAR LAB i = true)
    (hpi : ∀ i < N, i ≠ 0 → PMI i = mm (GMI (LAB i)) (PMI (PAR i))) :
    ∀ i < N, Inv d V (PM i) (PMI i) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [h0, h0', hI]
      exact inv_idM hd hVd
    · obtain ⟨h1, h2, h3⟩ := pointM_tree (hp i hi) (by omega)
      rw [h3, hpi i hi (by omega), hmm, hmm]
      exact (ih _ h1 (by omega)).mul hd (hG _ h2)

theorem tree_good {d : ℕ} (hd : 0 < d) {V : Array ℕ} (hVd : ∀ v ∈ V, v < 2 ^ d)
    {mm : ℕ → ℕ → ℕ} (hmm : ∀ A B, mm A B = mmul d A B) {I : ℕ} (hI : I = idM d)
    {ngen N : ℕ} {GM PM : ℕ → ℕ} {E : ℕ → ℕ → ℕ} {PAR LAB : ℕ → ℕ}
    (hG : ∀ k < ngen, ∀ v ∈ V, vmul d v (GM k) ∈ V) (h0 : PM 0 = I)
    (hp : ∀ i < N, pointM mm ngen N GM PM E PAR LAB i = true) :
    ∀ i < N, (∀ v ∈ V, vmul d v (PM i) ∈ V) ∧ PM i < 2 ^ (d * d) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [h0, hI]
      exact ⟨(inv_idM hd hVd).1, idM_lt⟩
    · obtain ⟨h1, h2, h3⟩ := pointM_tree (hp i hi) (by omega)
      rw [h3, hmm]
      exact ⟨maps_mmul (ih _ h1 (by omega)).1 (hG _ h2), mmul_lt _ _⟩

@[expose] noncomputable def wordM (mm : ℕ → ℕ → ℕ) (I : ℕ) (LM : ℤ → ℕ) : List ℤ → ℕ
  | [] => I
  | l :: w => mm (wordM mm I LM w) (LM l)

@[expose] noncomputable def letterM (CS CSI : ℕ → ℕ) (l : ℤ) : ℕ :=
  bif decide (0 < l) then CS (l.toNat - 1) else CSI ((-l).toNat - 1)

theorem letterA_permOfMat {d : ℕ} {V : Array ℕ} {S Sinv : Array (Array ℕ)} {CS CSI : ℕ → ℕ}
    {j : ℕ} (hS : ∀ h < j, S[h]! = permOfMat d V (CS h))
    (hSI : ∀ h < j, Sinv[h]! = permOfMat d V (CSI h)) {l : ℤ} (hl : l ≠ 0 ∧ l.natAbs ≤ j) :
    letterA S Sinv l = permOfMat d V (letterM CS CSI l) := by
  unfold letterA letterM
  by_cases hpos : 0 < l
  · rw [ite_eq_left hpos, decide_eq_true hpos, Bool.cond_true]
    exact hS _ (by omega)
  · rw [ite_eq_right hpos, decide_eq_false hpos, Bool.cond_false]
    exact hSI _ (by omega)

theorem wordA_permOfMat {d : ℕ} {V : Array ℕ} (hd : 0 < d) (hV : V.toList.Nodup)
    (hVd : ∀ v ∈ V, v < 2 ^ d) {mm : ℕ → ℕ → ℕ} (hmm : ∀ A B, mm A B = mmul d A B) {I : ℕ}
    (hI : I = idM d) {S Sinv : Array (Array ℕ)} {CS CSI : ℕ → ℕ} {j : ℕ}
    (hS : ∀ h < j, S[h]! = permOfMat d V (CS h)) (hSI : ∀ h < j, Sinv[h]! = permOfMat d V (CSI h))
    (hCS : ∀ h < j, ∀ v ∈ V, vmul d v (CS h) ∈ V) (hCSI : ∀ h < j, ∀ v ∈ V, vmul d v (CSI h) ∈ V) :
    ∀ w : List ℤ, lettersOK j w = true →
      (∀ v ∈ V, vmul d v (wordM mm I (letterM CS CSI) w) ∈ V) ∧
        wordA V.size S Sinv w = permOfMat d V (wordM mm I (letterM CS CSI) w)
  | [], _ => by
    rw [wordM, hI, wordA, permOfMat_idM hd hV hVd]
    exact ⟨fun v hv => by rwa [vmul_idM hd (hVd v hv)], rfl⟩
  | l :: w, hw => by
    simp only [lettersOK, List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at hw
    obtain ⟨⟨hl0, hlj⟩, hw⟩ := hw
    have hw' : lettersOK j w = true := by
      simpa [lettersOK, List.all_eq_true] using hw
    obtain ⟨ih1, ih2⟩ := wordA_permOfMat hd hV hVd hmm hI hS hSI hCS hCSI w hw'
    have hL : ∀ v ∈ V, vmul d v (letterM CS CSI l) ∈ V := by
      unfold letterM
      by_cases hpos : 0 < l
      · rw [decide_eq_true hpos, Bool.cond_true]
        exact hCS _ (by omega)
      · rw [decide_eq_false hpos, Bool.cond_false]
        exact hCSI _ (by omega)
    rw [wordM, hmm, wordA, ih2, letterA_permOfMat hS hSI ⟨hl0, hlj⟩, compA_permOfMat ih1]
    exact ⟨maps_mmul ih1 hL, rfl⟩

theorem getD_eq {s : List ℕ} {h : ℕ} (hh : h < s.length) : s.getD h 0 = s[h] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hh, Option.getD_some]

@[expose] noncomputable def conjWordsM (mm : ℕ → ℕ → ℕ) (I ngen N : ℕ) (GM PM PMI : ℕ → ℕ)
    (sel : ℕ → List ℕ) (W : ℕ → List (List ℤ)) : Bool :=
  allN N fun k => Nat.beq (PM k) I ||
    ((sel k).all (fun j => Nat.blt j N) && Nat.beq (W k).length ngen &&
      allN ngen fun l => lettersOK (sel k).length (W k)[l]! &&
        Nat.beq (GM l) (wordM mm I (letterM
          (fun h => mm (mm (PMI ((sel k).getD h 0)) (PM k)) (PM ((sel k).getD h 0)))
          (fun h => mm (mm (PMI ((sel k).getD h 0)) (PMI k)) (PM ((sel k).getD h 0))))
          (W k)[l]!))

theorem conjWordsOK_of_conjWordsM {d : ℕ} {V : Array ℕ} {VG LK : ℕ → ℕ} (hs : Sys d V VG LK)
    {l : ℕ → List ℕ} (hsp : Spans d V l) {mm : ℕ → ℕ → ℕ} (hmm : ∀ A B, mm A B = mmul d A B)
    {I : ℕ} (hI : I = idM d) {ngen N : ℕ} {GM PM PMI : ℕ → ℕ} {gs : Array (Array ℕ)}
    (hgs : gs.size = ngen) (hG : ∀ k < ngen, gs[k]! = permOfMat d V (GM k))
    (hGl : ∀ k < ngen, GM k < 2 ^ (d * d)) (hGm : ∀ k < ngen, ∀ v ∈ V, vmul d v (GM k) ∈ V)
    {c : ArrCert} (hN : c.pts.size = N) (hP : ∀ i < N, c.pts[i]! = permOfMat d V (PM i))
    (hPI : ∀ i < N, Inv d V (PM i) (PMI i))
    {sel : ℕ → List ℕ} {W : ℕ → List (List ℤ)}
    (h : conjWordsM mm I ngen N GM PM PMI sel W = true) :
    CFSG.RankThree.PartOne.conjWordsOK V.size c gs sel W = true := by
  have hd := hs.hd
  rw [CFSG.RankThree.PartOne.conjWordsOK, allLt_iff, hN]
  intro k hk
  have hk' := allN_spec h k hk
  rw [Bool.or_eq_true] at hk' ⊢
  rcases hk' with h1 | h1
  · left
    rw [Nat.beq_eq] at h1
    rw [hP k hk, h1, hI, permOfMat_idM hd hs.nodup hs.lt, eqA, allLt_iff]
    exact fun i _ => beq_self_eq_true _
  right
  rw [Bool.and_eq_true, Bool.and_eq_true] at h1
  obtain ⟨⟨hsel, hlen⟩, hw⟩ := h1
  rw [List.all_eq_true] at hsel
  have hsel' : ∀ j ∈ sel k, j < N := fun j hj => by
    have := hsel j hj
    rwa [Nat.blt_eq] at this
  rw [Nat.beq_eq] at hlen
  rw [Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro j hj
    exact decide_eq_true (hsel' j hj)
  · rw [beq_iff_eq, hlen, hgs]
  rw [allLt_iff, hgs]
  intro i hi
  have hwi := allN_spec hw i hi
  rw [Bool.and_eq_true] at hwi ⊢
  obtain ⟨hlet, heq⟩ := hwi
  refine ⟨hlet, ?_⟩
  set s := sel k
  have hsj : ∀ h < s.length, s.getD h 0 < N := fun h hh => by
    rw [getD_eq hh]
    exact hsel' _ (List.getElem_mem hh)
  have hS : ∀ h < s.length, (CFSG.RankThree.PartOne.conjSel V.size c k s)[h]! =
      permOfMat d V (mm (mm (PMI (s.getD h 0)) (PM k)) (PM (s.getD h 0))) := by
    intro h hh
    rw [CFSG.RankThree.PartOne.conjSel, getElem!_pos _ h (by simpa using hh)]
    simp only [List.getElem_toArray, List.getElem_map]
    rw [← getD_eq hh, hP _ (hsj h hh), hP k hk, hmm, hmm,
      conjA_permOfMat hd hs.nodup hs.lt (hPI _ (hsj h hh)) (hPI k hk).1]
  have hSI : ∀ h < s.length, (CFSG.RankThree.PartOne.conjSelInv V.size c k s)[h]! =
      permOfMat d V (mm (mm (PMI (s.getD h 0)) (PMI k)) (PM (s.getD h 0))) := by
    intro h hh
    rw [CFSG.RankThree.PartOne.conjSelInv, getElem!_pos _ h (by simpa using hh)]
    simp only [List.getElem_toArray, List.getElem_map]
    rw [← getD_eq hh, hP _ (hsj h hh), hP k hk, hmm, hmm,
      invCand_permOfMat hd hs.nodup hs.lt (hPI k hk),
      conjA_permOfMat hd hs.nodup hs.lt (hPI _ (hsj h hh)) (hPI k hk).2.1]
  have hCS : ∀ h < s.length, ∀ v ∈ V,
      vmul d v (mm (mm (PMI (s.getD h 0)) (PM k)) (PM (s.getD h 0))) ∈ V := by
    intro h hh
    rw [hmm, hmm]
    exact maps_mmul (maps_mmul (hPI _ (hsj h hh)).2.1 (hPI k hk).1) (hPI _ (hsj h hh)).1
  have hCSI : ∀ h < s.length, ∀ v ∈ V,
      vmul d v (mm (mm (PMI (s.getD h 0)) (PMI k)) (PM (s.getD h 0))) ∈ V := by
    intro h hh
    rw [hmm, hmm]
    exact maps_mmul (maps_mmul (hPI _ (hsj h hh)).2.1 (hPI k hk).2.1) (hPI _ (hsj h hh)).1
  obtain ⟨hwm, hwe⟩ := wordA_permOfMat hd hs.nodup hs.lt hmm hI hS hSI hCS hCSI _ hlet
  rw [hwe, hG i hi, eqA_permOfMat hsp (hGm i hi) hwm (hGl i hi), heq]
  cases hW : (W k)[i]! with
  | nil => rw [wordM, hI]; exact idM_lt
  | cons a w => rw [wordM, hmm]; exact mmul_lt _ _

end CFSG.RankThree.Native.F2

end
