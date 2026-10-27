module

public import CFSG.Monster.B.Fischer.HexadDiagInputs
public import CFSG.Certificates.Kernel.SortTreeArr
public import CFSG.Certificates.Kernel.SortTreeKey
public import CFSG.Certificates.Kernel.MonsterB.ArrBfsSound
public import Certificates.Kernel.MonsterB.Diag3031Data
import CFSG.Certificates.Kernel.Common.Harness

public section

open CFSG.Monster.B.Fischer CFSG.KC.SortTree CFSG.KLie.CT CFSG.KC.U6Orb CFSG.KC.Bfs

namespace CertificateChecks.Batch3031

open CFSG.Monster.B.Fischer CFSG.KC.SortTree CFSG.KLie.CT CFSG.KC.U6Orb CFSG.KC.Bfs

set_option maxRecDepth 100000

@[expose] def perm (j : ℕ) : ℕ := if j < 32 then 22 + j else j - 32

@[expose] def permI (i : ℕ) : ℕ := if i < 22 then 32 + i else i - 22

@[expose] noncomputable def code (x : Array ℕ) : ℕ :=
  packL 5 ((List.range 54).map fun j => x[perm j]!)

@[expose] noncomputable def dec (c : ℕ) : Array ℕ :=
  ((List.range 54).map fun i => fget c (permI i) 5).toArray

@[expose] noncomputable def genC (k : ℕ) : ℕ :=
  nIf(Nat.beq k 0,
    1876289168436146502542621705223669448494252737487731115637252983976843625931836017,
    nIf(Nat.beq k 1,
      1711464907551828695555602030035882258656249483105645620117327672732917731326315552,
      1882180873000949733767101039107762116320706191244505136471893346907252207287542835))

@[expose] noncomputable def offC (j : ℕ) : ℕ := nIf(Nat.blt j 32, 22, 0)

@[expose] noncomputable def actC (k c : ℕ) : ℕ :=
  orN 54 fun j => Nat.shiftLeft (fget (genC k) (Nat.add (fget c j 5) (offC j)) 5) (Nat.mul 5 j)

@[expose] noncomputable def rootC : ℕ :=
  1283183593695861139212134819925623510180861874038398136160209720294929411132721184

noncomputable abbrev recD : ℕ → ℕ := recT Diag3031.R 6 292

noncomputable abbrev edgeD : ℕ → ℕ → ℕ := fun i k => fget (recT Diag3031.E 6 40 i) k 13

theorem kTree : treeOK actC 3 (fun _ => true) rootC recD 5760 270 4 13 64 90 = true := by
  quickRfl

theorem kClose : closeOK actC 3 recD edgeD 5760 270 64 90 = true := by quickRfl

theorem kKey : hiIncK recD 5760 270 160 = true := by quickRfl

theorem kGen : ∀ k < 3, genC k = packL 5 (dGenArr k).toList ∧ (dGenArr k).size = 54 ∧
    (∀ x ∈ (dGenArr k).toList, x < 32) ∧ PermArrN 22 ((dGenArr k).extract 0 22) = true ∧
    PermArrN 32 ((dGenArr k).extract 22 54) = true := by
  decide +kernel

theorem kRoot : code dRoot = rootC ∧ dValid dRoot = true := by decide +kernel

theorem perm_lt {j : ℕ} (hj : j < 54) : perm j < 54 := by unfold perm; split <;> omega

theorem permI_lt {i : ℕ} (hi : i < 54) : permI i < 54 := by unfold permI; split <;> omega

theorem perm_permI {i : ℕ} (hi : i < 54) : perm (permI i) = i := by
  unfold perm permI; split <;> split <;> omega

theorem valid_get {x : Array ℕ} (h : dValid x = true) :
    x.size = 54 ∧ (∀ i < 22, x[i]! < 22) ∧ (∀ i, 22 ≤ i → i < 54 → x[i]! < 32) := by
  simp only [dValid, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hs, h1⟩, h2⟩ := h
  refine ⟨hs, fun i hi => ?_, fun i hi1 hi2 => ?_⟩
  · have := PermArrN_lt h1 ⟨i, hi⟩
    rwa [getElem!_pos _ i (by simp [hs]; omega), Array.getElem_extract,
      ← getElem!_pos x _ (by omega), Nat.zero_add] at this
  · have := PermArrN_lt h2 ⟨i - 22, by omega⟩
    rwa [getElem!_pos _ _ (by simp [hs]; omega), Array.getElem_extract,
      ← getElem!_pos x _ (by omega), Nat.add_sub_cancel' hi1] at this

theorem valid_lt {x : Array ℕ} (h : dValid x = true) {i : ℕ} (hi : i < 54) : x[i]! < 32 := by
  obtain ⟨-, h1, h2⟩ := valid_get h
  by_cases h' : i < 22
  · exact lt_trans (h1 i h') (by norm_num)
  · exact h2 i (by omega) hi

theorem code_list_lt {x : Array ℕ} (h : dValid x = true) :
    ∀ y ∈ (List.range 54).map (fun j => x[perm j]!), y < 2 ^ 5 := by
  intro y hy
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
  exact valid_lt h (perm_lt (List.mem_range.1 hj))

theorem fget_code {x : Array ℕ} (h : dValid x = true) {j : ℕ} (hj : j < 54) :
    fget (code x) j 5 = x[perm j]! := by
  rw [code, fget_packL (code_list_lt h) j (by simpa using hj)]
  simp

theorem dec_code {x : Array ℕ} (h : dValid x = true) : dec (code x) = x := by
  have hs := (valid_get h).1
  apply Array.ext
  · simp [dec, hs]
  · intro i h1 h2
    have hi : i < 54 := by simpa [dec] using h1
    simp only [dec, List.getElem_toArray, List.getElem_map, List.getElem_range]
    rw [fget_code h (permI_lt hi), perm_permI hi, getElem!_pos x i h2]

theorem get_extract {a : Array ℕ} {s e m : ℕ} (hm : m < e - s) (he : e ≤ a.size) :
    (a.extract s e)[m]! = a[s + m]! := by
  rw [getElem!_pos _ m (by simp; omega), Array.getElem_extract, getElem!_pos a _ (by omega)]

theorem get_append_left {A B : Array ℕ} {i : ℕ} (h : i < A.size) : (A ++ B)[i]! = A[i]! := by
  rw [getElem!_pos _ i (by simp; omega), Array.getElem_append_left h, getElem!_pos A i h]

theorem get_append_right {A B : Array ℕ} {i : ℕ} (h : A.size ≤ i) (h' : i < A.size + B.size) :
    (A ++ B)[i]! = B[i - A.size]! := by
  rw [getElem!_pos _ i (by simp; omega), Array.getElem_append_right h,
    getElem!_pos B _ (by omega)]

theorem get_amulN {s x : Array ℕ} {i : ℕ} (h : i < x.size) : (amulN s x)[i]! = s[x[i]!]! := by
  rw [amulN, getElem!_pos _ i (by simp; omega), Array.getElem_map, getElem!_pos x i h]

theorem extract_left {A B : Array ℕ} {m : ℕ} (h : A.size = m) : (A ++ B).extract 0 m = A := by
  subst h
  rw [Array.extract_append_left, Array.extract_size]

theorem extract_right {A B : Array ℕ} {m l e : ℕ} (h : A.size = m) (hB : B.size = l)
    (he : m + l = e) : (A ++ B).extract m e = B := by
  subst h hB he
  rw [Array.extract_append_right, Array.extract_size]

theorem dAct_get {k : ℕ} (hk : k < 3) {x : Array ℕ} (h : dValid x = true) {i : ℕ}
    (hi : i < 54) : (dAct k x)[i]! = (dGenArr k)[x[i]! + (if i < 22 then 0 else 22)]! := by
  obtain ⟨hs, h1, h2⟩ := valid_get h
  obtain ⟨-, hg, -, -, -⟩ := kGen k hk
  have hA : (amulN ((dGenArr k).extract 0 22) (x.extract 0 22)).size = 22 := by
    simp [amulN, hs]
  have hB : (amulN ((dGenArr k).extract 22 54) (x.extract 22 54)).size = 32 := by
    simp [amulN, hs]
  change (amulN ((dGenArr k).extract 0 22) (x.extract 0 22) ++
    amulN ((dGenArr k).extract 22 54) (x.extract 22 54))[i]! = _
  by_cases hi' : i < 22
  · have hx := h1 i hi'
    rw [get_append_left (by omega), get_amulN (by simp [hs]; omega),
      get_extract (a := x) (by omega) (by omega), Nat.zero_add,
      get_extract (a := dGenArr k) (by omega) (by omega), Nat.zero_add,
      ite_eq_left_of_eq_true _ _ (eq_true hi'), Nat.add_zero]
  · have hx := h2 i (by omega) hi
    rw [get_append_right (by omega) (by omega), hA, get_amulN (by simp [hs]; omega),
      get_extract (a := x) (by omega) (by omega), Nat.add_sub_cancel' (by omega : 22 ≤ i),
      get_extract (a := dGenArr k) (by omega) (by omega),
      ite_eq_right_of_eq_false _ _ (eq_false hi'), Nat.add_comm 22 (x[i]!)]

theorem packL_append (w : ℕ) : ∀ (A B : List ℕ),
    packL w (A ++ B) = packL w A ||| (packL w B <<< (w * A.length))
  | [], B => by simp [packL]
  | a :: A, B => by
    rw [List.cons_append, packL_cons, packL_cons, packL_append w A B, Nat.shiftLeft_or_distrib,
      ← Nat.shiftLeft_add, List.length_cons, Nat.mul_succ, Nat.add_comm (w * A.length) w,
      Nat.or_assoc]

theorem orN_pack (w : ℕ) (f : ℕ → ℕ) (hf : ∀ j, f j < 2 ^ w) : ∀ n,
    orN n (fun j => Nat.shiftLeft (f j) (Nat.mul w j)) = packL w ((List.range n).map f)
  | 0 => rfl
  | n + 1 => by
    change Nat.lor _ (orN n _) = _
    rw [orN_pack w f hf n, List.range_succ, List.map_append, packL_append, List.length_map,
      List.length_range, List.map_singleton, packL_cons]
    change _ = _ ||| ((f n ||| 0 <<< w) <<< (w * n))
    rw [Nat.zero_shiftLeft, Nat.or_zero, Nat.or_comm]
    rfl

theorem fget_lt (X i w : ℕ) : fget X i w < 2 ^ w := by
  rw [fget_eq]
  exact Nat.mod_lt _ (Nat.two_pow_pos w)

theorem actC_code {k : ℕ} (hk : k < 3) {x : Array ℕ} (h : dValid x = true) :
    actC k (code x) = code (dAct k x) := by
  obtain ⟨hG, hg, hglt, -, -⟩ := kGen k hk
  have hf : ∀ j ∈ List.range 54,
      fget (genC k) (Nat.add (fget (code x) j 5) (offC j)) 5 = (dAct k x)[perm j]! := by
    intro j hj
    have hj' : j < 54 := List.mem_range.1 hj
    have hoff : offC j = (if perm j < 22 then 0 else 22) := by
      by_cases hj32 : j < 32
      · have e : Nat.blt j 32 = true := blt_iff.2 hj32
        have : ¬ perm j < 22 := by unfold perm; split <;> omega
        change Bool.rec (motive := fun _ => ℕ) 0 22 (Nat.blt j 32) = _
        rw [e, ite_eq_right_of_eq_false _ _ (eq_false this)]
      · have e : Nat.blt j 32 = false := by
          cases e' : Nat.blt j 32
          · rfl
          · exact absurd (blt_iff.1 e') hj32
        have : perm j < 22 := by unfold perm; split <;> omega
        change Bool.rec (motive := fun _ => ℕ) 0 22 (Nat.blt j 32) = _
        rw [e, ite_eq_left_of_eq_true _ _ (eq_true this)]
    have hb : x[perm j]! + offC j < (dGenArr k).size := by
      have := valid_lt h (perm_lt hj')
      have h22 : perm j < 22 → x[perm j]! < 22 := fun hp => (valid_get h).2.1 _ hp
      rw [hg, hoff]
      split <;> omega
    change fget (genC k) (fget (code x) j 5 + offC j) 5 = _
    rw [fget_code h hj', hG, dAct_get hk h (perm_lt hj'), ← hoff]
    exact fget_packA hglt hb
  exact (orN_pack 5 _ (fun j => fget_lt _ _ _) 54).trans
    (congrArg (packL 5) (List.map_congr_left hf))

theorem dValid_of {y : Array ℕ} (hs : y.size = 54) (h1 : PermArrN 22 (y.extract 0 22) = true)
    (h2 : PermArrN 32 (y.extract 22 54) = true) : dValid y = true := by
  simp only [dValid, Bool.and_eq_true, beq_iff_eq]
  exact ⟨⟨hs, h1⟩, h2⟩

theorem dAct_valid {k : ℕ} (hk : k < 3) {x : Array ℕ} (h : dValid x = true) :
    dValid (dAct k x) = true := by
  obtain ⟨-, -, -, hp1, hp2⟩ := kGen k hk
  have hx := h
  simp only [dValid, Bool.and_eq_true, beq_iff_eq] at hx
  obtain ⟨⟨hs, h1⟩, h2⟩ := hx
  have hA : (amulN ((dGenArr k).extract 0 22) (x.extract 0 22)).size = 22 := by
    simp [amulN, hs]
  have hB : (amulN ((dGenArr k).extract 22 54) (x.extract 22 54)).size = 32 := by
    simp [amulN, hs]
  have hd : dAct k x = amulN ((dGenArr k).extract 0 22) (x.extract 0 22) ++
      amulN ((dGenArr k).extract 22 54) (x.extract 22 54) := rfl
  have e2 := extract_right (B := amulN ((dGenArr k).extract 22 54) (x.extract 22 54)) hA hB
    (rfl : 22 + 32 = 54)
  rw [hd]
  refine dValid_of (by rw [Array.size_append, hA, hB]) ?_ ?_
  · rw [extract_left hA]
    exact PermArrN_amulN hp1 h1
  · rw [e2]
    exact PermArrN_amulN hp2 h2

theorem packL_append_shift {w : ℕ} : ∀ (A B : List ℕ), (∀ x ∈ A, x < 2 ^ w) →
    packL w (A ++ B) >>> (w * A.length) = packL w B
  | [], B, _ => by simp
  | a :: A, B, h => by
    have ha := h a (by simp)
    have e1 : (packL w (A ++ B) * 2 ^ w + a) >>> w = packL w (A ++ B) := by
      rw [Nat.shiftRight_eq_div_pow, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos w),
        Nat.div_eq_of_lt ha, Nat.zero_add]
    rw [List.cons_append, packL_cons, or_shl_eq ha, List.length_cons, Nat.mul_succ,
      Nat.add_comm (w * A.length) w, Nat.shiftRight_add, e1]
    exact packL_append_shift A B fun x hx => h x (by simp [hx])

theorem code_shift {x : Array ℕ} (h : dValid x = true) :
    code x >>> 160 = packL 5 ((List.range 22).map fun i => x[i]!) := by
  have e : (List.range 54).map (fun j => x[perm j]!) =
      (List.range 32).map (fun j => x[perm j]!) ++ (List.range 22).map fun i => x[i]! := by
    rw [show (54 : ℕ) = 32 + 22 from rfl, List.range_add, List.map_append, List.map_map]
    refine congrArg _ (List.map_congr_left fun i hi => ?_)
    have : ¬ 32 + i < 32 := by omega
    simp [perm, this]
  have hA : ∀ y ∈ (List.range 32).map (fun j => x[perm j]!), y < 2 ^ 5 := by
    intro y hy
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
    exact valid_lt h (perm_lt (by have := List.mem_range.1 hj; omega))
  have := packL_append_shift _ ((List.range 22).map fun i => x[i]!) hA
  rw [List.length_map, List.length_range] at this
  rw [code, e]
  exact this

theorem key_inj {x y : Array ℕ} (hx : dValid x = true) (hy : dValid y = true)
    (e : dKey x = dKey y) : code x >>> 160 = code y >>> 160 := by
  have hx' := hx
  have hy' := hy
  simp only [dValid, Bool.and_eq_true, beq_iff_eq] at hx' hy'
  have he := akeyN_inj hx'.1.2 hy'.1.2 e
  rw [code_shift hx, code_shift hy]
  refine congrArg (packL 5) (List.map_congr_left fun i hi => ?_)
  have hi' : i < 22 := List.mem_range.1 hi
  have h1 := get_extract (a := x) (s := 0) (e := 22) (m := i) (by omega)
    (by rw [hx'.1.1]; norm_num)
  have h2 := get_extract (a := y) (s := 0) (e := 22) (m := i) (by omega)
    (by rw [hy'.1.1]; norm_num)
  rw [Nat.zero_add] at h1 h2
  rw [← h1, ← h2, he]

theorem cert : arrCertOK dAct 3 dValid dKey dRoot dCert = true ∧ dCert.pts.size = 5760 := by
  obtain ⟨hrc, hrv⟩ := kRoot
  have hT := kTree
  rw [← hrc] at hT
  obtain ⟨S', hS', hcard, -, -, hmem⟩ := orbit_sound (by norm_num) hT kClose
  have hdec : ∀ a, dValid a = true → dec (code a) = a := fun a ha => dec_code ha
  have hact : ∀ k < 3, ∀ a, dValid a = true → dValid (dAct k a) = true :=
    fun k hk a ha => dAct_valid hk ha
  have hcode : ∀ k < 3, ∀ a, dValid a = true → actC k (code a) = code (dAct k a) :=
    fun k hk a ha => actC_code hk ha
  obtain ⟨hS, hc, hv⟩ := orbit_code (valid := fun a => dValid a = true) hdec hact hcode hrv hS'
  have hrc' := fun c (hc : c ∈ S') => reach_code (valid := fun a => dValid a = true) hdec hact
    hcode hrv ((hS' c).2 hc)
  have hkey : ∀ a ∈ S'.image dec, ∀ b ∈ S'.image dec, dKey a = dKey b → a = b := by
    intro a ha b hb e
    obtain ⟨c1, h1, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨c2, h2, rfl⟩ := Finset.mem_image.1 hb
    have e' := key_inj (hrc' c1 h1).1 (hrc' c2 h2).1 e
    rw [(hrc' c1 h1).2.2, (hrc' c2 h2).2.2] at e'
    obtain ⟨i, hi, rfl⟩ := (hmem c1).1 h1
    obtain ⟨j, hj, rfl⟩ := (hmem c2).1 h2
    rw [hiIncK_sound kKey hi hj e']
  obtain ⟨h1, -, h3, -⟩ := arrBfs_spec (fuel := 6000) (valid := dValid) (S'.image dec) hS hv hkey
    (by rw [hc, hcard]; norm_num)
  exact ⟨h1, h3.trans (hc.trans hcard)⟩

end CertificateChecks.Batch3031

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.Fischer in
theorem certificate3031 : (arrCertOK dAct 3 dValid dKey dRoot dCert = true)
    ∧ (dCert.pts.size = 5760) := CertificateChecks.Batch3031.cert

end Certificates
