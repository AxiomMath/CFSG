
module

public import CFSG.Sporadic.Co1.Module.OddLitInputs
public import CFSG.Sporadic.Co1.Module.InvSpec
public import CFSG.Certificates.Kernel.SortTreeChunks
public import CFSG.Certificates.Kernel.VecKRegs
public import CFSG.Certificates.Kernel.Co1BTrSound

public section

namespace CFSG.Sporadic.Co1.Module.Odd

open CFSG.Blueprint CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix
  CFSG.KC.InvFam CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KLie.CT CFSG.KC.SortTree CFSG.KC.Odd73

theorem strictN73 (y : Nat) (k : Nat → Nat) : CFSG.KC.Loop.strictN y k = k y := by
  cases y <;> rfl

theorem orN_congr73 {f g : Nat → Nat} : ∀ n, (∀ i < n, f i = g i) →
    CFSG.KLie.CT.orN n f = CFSG.KLie.CT.orN n g
  | 0, _ => rfl
  | n + 1, h => by
    change Nat.lor (f n) (CFSG.KLie.CT.orN n f) = Nat.lor (g n) (CFSG.KLie.CT.orN n g)
    rw [h n (by omega), orN_congr73 n (fun i hi => h i (by omega))]

@[expose] def Canon73 (M : Nat) : Prop := M = CFSG.KLie.CT.orN 24 fun i => rowF 24 M i <<< (24 * i)

theorem canon73_mulF (A B : Nat) : Canon73 (mulF 24 A B) := by
  unfold Canon73
  rw [CFSG.KC.F2W.mulF_eq_orN]
  exact orN_congr73 24 fun i hi => by
    rw [CFSG.KC.F2W.rowF_orN 24 (fun j _ => CFSG.KC.F2W.vmF_lt 24 B (rowF 24 A j)) hi]

theorem unpackR_get73 (M : Nat) {i : Nat} (hi : i < 24) :
    (unpackR 24 M)[i]?.getD 0 = rowF 24 M i := by
  rw [CFSG.KC.F2W.rowF_eq]
  simp [unpackR, hi]

theorem eq_of_unpackR73 {A B : Nat} (hA : Canon73 A) (hB : Canon73 B)
    (h : unpackR 24 A = unpackR 24 B) : A = B := by
  rw [hA, hB]
  exact orN_congr73 24 fun i hi => by rw [← unpackR_get73 A hi, ← unpackR_get73 B hi, h]

@[expose] def PM73 (x : NativeSporadic.Co1) (M : Nat) : Prop :=
  mat x = rowsMatrix 24 (unpackR 24 M)

theorem rM73_mul (A B : Nat) : rowsMatrix 24 (unpackR 24 A) * rowsMatrix 24 (unpackR 24 B) =
    rowsMatrix 24 (unpackR 24 (mulF 24 A B)) := by
  rw [← rowsMatrix_mulRows, CFSG.KC.F2W.mulRows_unpackR]

theorem pm73_mul {x y : NativeSporadic.Co1} {A B : Nat} (hx : PM73 x A) (hy : PM73 y B) :
    PM73 (x * y) (mulF 24 A B) := by
  unfold PM73 at *
  rw [map_mul, hx, hy, rM73_mul]

theorem pm73_one : PM73 1 (idF 24) := by
  unfold PM73
  rw [map_one, CFSG.KC.VecK.unpackR_idF, rowsMatrix_idRows]

theorem pm73_conj {x g gi : NativeSporadic.Co1} {X G Gi : Nat} (hx : PM73 x X) (hg : PM73 g G)
    (hgi : PM73 gi Gi) : PM73 (g * x * gi) (mulF 24 (mulF 24 G X) Gi) :=
  pm73_mul (pm73_mul hg hx) hgi

theorem pm73_inj {x y : NativeSporadic.Co1} {M : Nat} (hx : PM73 x M) (hy : PM73 y M) : x = y :=
  mat_injective (hx.trans hy.symm)

theorem pm73_eq {x y : NativeSporadic.Co1} {A B : Nat} (hx : PM73 x A) (hy : PM73 y B)
    (hA : Canon73 A) (hB : Canon73 B) (e : x = y) : A = B := by
  subst e
  exact eq_of_unpackR73 hA hB (CFSG.Sporadic.Co1.Module.rowsMatrix_injective_of_valid
    (CFSG.KC.Co1F2.validRows_unpackR A) (CFSG.KC.Co1F2.validRows_unpackR B) (hx.symm.trans hy))

theorem orderOf_eq73 {x : NativeSporadic.Co1} {M n : Nat} (hx : PM73 x M) (hn : 0 < n)
    (h : orderIsK 24 M n = true) : orderOf x = n :=
  CFSG.Sporadic.Co1.Module.orderOf_eq_of_orderIs hx hn (orderIs_sound h)

theorem pm73_act {x : NativeSporadic.Co1} {M : Nat} (hx : PM73 x M) (v : Nat) :
    co1Act x (toVecD 24 v) = toVecD 24 (vmF 24 (trK 24 M) v) := by
  rw [co1Act_eq_mulVec, hx, rowsMatrix_mulVec, CFSG.KC.F2W.transposeRows_unpackR,
    CFSG.KC.F2W.vecMulN_unpackR]

theorem getL73 (x : Nat) : ∀ (L : List Nat) (i : Nat), getL x L i = L.getD i x
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: L, i + 1 => getL73 x L i

theorem lenL73 : ∀ L : List Nat, lenL L = L.length
  | [] => rfl
  | _ :: L => by
    change Nat.succ (lenL L) = _
    rw [lenL73 L]
    rfl

theorem andB73 {a b : Bool} : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> simp [andB]

theorem orB73 {a b : Bool} : orB a b = true ↔ a = true ∨ b = true := by
  cases a <;> simp [orB]

theorem notB73 {a : Bool} : notB a = true ↔ a = false := by
  cases a <;> simp [notB]

theorem allN73 {n : Nat} {f : Nat → Bool} : allN n f = true ↔ ∀ i < n, f i = true :=
  CFSG.KC.SortTree.allN_iff n f

theorem canonL73 {L : List Nat} (h : CFSG.KD.Co1Odd.canonL L = true) {i : Nat} (hi : i < L.length) :
    Canon73 (L.getD i 0) := by
  unfold CFSG.KD.Co1Odd.canonL CFSG.KD.Co1Odd.canonsL at h
  rw [List.all_eq_true] at h
  exact beq_iff_eq.1 (h i (List.mem_range'_1.2 ⟨Nat.zero_le _, by omega⟩))

theorem distinctL73 : ∀ L : List ℕ, CFSG.KD.Co1Odd.distinctL L = true → L.Nodup
  | [], _ => List.nodup_nil
  | a :: t, h => by
    have h' : a ∉ t ∧ CFSG.KD.Co1Odd.distinctL t = true := by
      simpa [CFSG.KD.Co1Odd.distinctL] using h
    exact List.nodup_cons.2 ⟨h'.1, distinctL73 t h'.2⟩

section Regs

variable {W : OddW} (hW : OddOK W)
include hW

theorem len73 : W.R.length = 94 := by
  have h := hW.len
  rwa [lenL73] at h

theorem regs73 : regsRows = (W.R.map (unpackR 24)).toArray := by
  obtain ⟨a, b, L, hR⟩ : ∃ a b L, W.R = a :: b :: L := by
    have h := len73 hW
    rcases e : W.R with _ | ⟨a, _ | ⟨b, L⟩⟩
    · rw [e] at h
      simp at h
    · rw [e] at h
      simp at h
    · exact ⟨a, b, L, rfl⟩
  have hA : dat.rowsA = unpackR 24 a := by
    have h := hW.rA
    rwa [OddW.reg, hR] at h
  have hB : dat.rowsB = unpackR 24 b := by
    have h := hW.rB
    rwa [OddW.reg, hR] at h
  have hp := prog_sound hW.prog
  rw [hR] at hp
  rw [regsRows, initRows, hA, hB, ← hW.progEq, hR]
  exact hp

theorem rr73 {i : ℕ} (hi : i < 94) : rr i = unpackR 24 (W.reg i) := by
  have hl := len73 hW
  rw [rr, regs73 hW, OddW.reg, getL73, List.getD_eq_getElem _ _ (by omega)]
  simp [hl, hi]

theorem pm73_reg {i : ℕ} (hi : i < 94) : PM73 (reg i) (W.reg i) := by
  unfold PM73
  rw [mat_reg, rr73 hW hi]

theorem canon73_reg {i : ℕ} (hi : i < 94) : Canon73 (W.reg i) := by
  have h := canonL73 hW.canon (i := i) (by rw [len73 hW]; exact hi)
  rwa [OddW.reg, getL73]

end Regs

section Recs

variable {W : OddW} (hW : OddOK W)
include hW

noncomputable abbrev val73 (W : OddW) (i : ℕ) : ℕ := valF 576 (W.T.tab i)

theorem tree73_spec : (∀ i < nS, recOK (act73 W.R) 14 (fun _ => true) (W.reg 27) W.T.tab nS 576
      W.T.wl W.T.wp (W.T.tab i) = true) ∧
    (∀ i, i + 1 < nS → val73 W i < val73 W (i + 1)) :=
  tree_spec (treeOK_of_chunks hW.tree.1 hW.tree.2)

theorem rec73_spec {i : ℕ} (hi : i < nS) :
    (levF 576 W.T.wl (W.T.tab i) = 0 → val73 W i = W.reg 27) ∧
    (levF 576 W.T.wl (W.T.tab i) ≠ 0 → parF 576 W.T.wl W.T.wp (W.T.tab i) < nS ∧
      letF 576 W.T.wl W.T.wp (W.T.tab i) < 14 ∧
      levF 576 W.T.wl (W.T.tab (parF 576 W.T.wl W.T.wp (W.T.tab i))) <
        levF 576 W.T.wl (W.T.tab i) ∧
      act73 W.R (letF 576 W.T.wl W.T.wp (W.T.tab i))
        (val73 W (parF 576 W.T.wl W.T.wp (W.T.tab i))) = val73 W i) :=
  (recOK_spec ((tree73_spec hW).1 i hi)).2

theorem val73_strict : ∀ {i j : ℕ}, i < j → j < nS → val73 W i < val73 W j :=
  fun hij hj => val_lt_of_lt (tree73_spec hW).2 hij hj

theorem val73_inj {i j : ℕ} (hi : i < nS) (hj : j < nS) (e : val73 W i = val73 W j) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · exact absurd e (ne_of_lt (val73_strict hW h hj))
  · exact h
  · exact absurd e.symm (ne_of_lt (val73_strict hW h hi))

theorem aux73_spec {i : ℕ} (hi : i < nS) :
    auxOK73 W.R W.T.tab W.aux 576 W.T.wl W.T.wp i = true := by
  obtain ⟨hcC, e, hm⟩ := split_idx hW.tree.1 hi
  have hj : i % W.T.B < cntF nS W.T.B (i / W.T.B * W.T.B) := by
    rw [cntF_eq]
    omega
  have h : auxOK73 W.R W.T.tab W.aux 576 W.T.wl W.T.wp (i / W.T.B * W.T.B + i % W.T.B) = true :=
    allN73.1 (hW.aux _ hcC) _ hj
  rwa [e] at h

end Recs

theorem nIf73 (c : Bool) (t e : Nat) :
    Bool.rec (motive := fun _ => Nat) e t c = if c = true then t else e := by
  cases c <;> rfl

theorem bIf73 (c : Bool) (t e : Bool) :
    Bool.rec (motive := fun _ => Bool) e t c = if c = true then t else e := by
  cases c <;> rfl

theorem act73_lt {R : List Nat} {l : Nat} (hl : l < 10) (X : Nat) :
    act73 R l X = mulF 24 (mulF 24 (getL 0 R (getL 0 I73 l)) X) (getL 0 R (getL 0 Ii73 l)) := by
  unfold act73
  simp only [nIf73, blt_iff, hl, ↓reduceIte]
  unfold actC
  rw [CFSG.KC.F2W.mulW_eq, CFSG.KC.F2W.mulW_eq]

theorem act73_ge {R : List Nat} {l : Nat} (hl : ¬ l < 10) (X : Nat) :
    act73 R l X = getL 0 R (getL 0 J73 (l - 10)) := by
  unfold act73
  simp only [nIf73, blt_iff, hl, ↓reduceIte]
  rfl

theorem ruleOK73_spec {R : List Nat} {v L g c o cp : Nat} (h : ruleOK R v L g c o cp = true) :
    c < 6 ∧ (c = 5 → mulF 24 v (getL 0 R 86) = mulF 24 (getL 0 R 86) v) ∧ (L = 0 → c = 1) ∧
    (L ≠ 0 → g < 8 → c = cp) ∧
    (L ≠ 0 → 8 ≤ g → g < 10 → (cp = 5 → c = 5) ∧
      (cp ≠ 5 → c = 0 ∧ 0 < o ∧ o % 2 = 0 ∧ orderIsK 24 (mulF 24 (getL 0 R 27) v) o = true)) ∧
    (L ≠ 0 → 10 ≤ g → g < 13 → c = g - 8) ∧ (L ≠ 0 → 13 ≤ g → c = 5) := by
  unfold ruleOK at h
  simp only [bIf73, andB73, beq_iff, blt_iff, CFSG.KC.F2W.mulW_eq] at h
  obtain ⟨hc6, h2, h3⟩ := h
  refine ⟨hc6, fun hc => by simpa [hc] using h3, fun hL => by simpa [hL] using h2,
    fun hL hg => by simpa [hL, hg] using h2, fun hL hg8 hg10 => ?_,
    fun hL hg10 hg13 => ?_, fun hL hg13 => ?_⟩
  · have hg8' : ¬ g < 8 := by omega
    simp only [hL, hg8', hg10, ↓reduceIte] at h2
    refine ⟨fun hcp => by simpa [hcp] using h2, fun hcp => ?_⟩
    simp only [hcp, ↓reduceIte, andB73, beq_iff, blt_iff] at h2
    obtain ⟨e1, e2, e3, e4⟩ := h2
    refine ⟨e1, e2, ?_, e4⟩
    have e3' : o &&& 1 = 0 := e3
    rwa [Nat.and_one_is_mod] at e3'
  · have hg8' : ¬ g < 8 := by omega
    have hg10' : ¬ g < 10 := by omega
    simpa [hL, hg8', hg10', hg13] using h2
  · have hg8' : ¬ g < 8 := by omega
    have hg10' : ¬ g < 10 := by omega
    have hg13' : ¬ g < 13 := by omega
    simpa [hL, hg8', hg10', hg13'] using h2

theorem preOK73_spec {a a' : Nat} (h : preOK a a' = true) {c : Nat} (hc : c < 4) :
    preA a' c = preA a c + if clsA a = c + 2 then 1 else 0 := by
  unfold preOK at h
  have h' := allN73.1 h c hc
  simp only [nIf73, beq_iff] at h'
  exact h'

end CFSG.Sporadic.Co1.Module.Odd

end
