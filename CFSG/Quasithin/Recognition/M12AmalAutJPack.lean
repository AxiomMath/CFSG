module

public import CFSG.Quasithin.Recognition.M12AmalAutCheck2
public import CFSG.Quasithin.Background.HParabCode22Pack
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

public section

namespace CFSG.Quasithin.M12AmalAut.JPack

open CFSG.Quasithin.H.Coc24Pack CFSG.Quasithin.H.Code22Pack

@[expose] def decL (x : ℕ) : List ℕ := (List.range 24).map (lane x)

theorem getD_decL (a j : ℕ) : (decL a).getD j 0 = getK a j := by
  unfold decL getK
  by_cases hj : j < 24
  · rw [List.getD_eq_getElem _ _ (by simpa using hj), Nat.blt_eq.mpr hj]
    simp
  · rw [List.getD_eq_default _ _ (by simpa using hj)]
    have hb : Nat.blt j 24 = false := by
      cases h : Nat.blt j 24
      · rfl
      · exact absurd (Nat.blt_eq.mp h) hj
    rw [hb]

theorem compL_decL (a b : ℕ) : compL (decL a) (decL b) = decL (cK a b) := by
  rw [compL]
  change ((List.range 24).map (lane b)).map (fun j => (decL a).getD j 0) =
    (List.range 24).map (lane (cK a b))
  rw [List.map_map]
  apply List.map_congr_left
  intro p hp
  change (decL a).getD (lane b p) 0 = lane (cK a b) p
  rw [getD_decL, cK, packN_lane _ (fun t => getK_lt _ _) 24 p (List.mem_range.1 hp)]

#kc_repo #kc_decls CFSG.Quasithin.M12AmalAut.JPack "CFSG/Quasithin/Recognition/data/m12amalautj_pack.txt" 3846 9727665545137146019

@[expose] noncomputable def TK (i : ℕ) : ℕ := lane120 tT i

theorem tT_ok : telTab = (List.range 128).map fun i => decL (TK i) :=
  eq_of_beq (by decide +kernel)

theorem tl_dec {i : ℕ} (hi : i < 128) : tl i = decL (TK i) := by
  unfold tl
  rw [tT_ok, List.getD_eq_getElem _ _ (by simpa using hi)]
  simp

@[expose] def allLt (f : ℕ → Bool) (n : ℕ) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k acc => Bool.rec false acc (f k)) n

theorem of_allLt {f : ℕ → Bool} : ∀ {n : ℕ}, allLt f n = true → ∀ k < n, f k = true
  | 0, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | n + 1, h, k, hk => by
    have h' : Bool.rec false (allLt f n) (f n) = true := h
    cases hf : f n
    · rw [hf] at h'
      exact absurd h' Bool.false_ne_true
    · rw [hf] at h'
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · exact of_allLt h' k hk
      · exact hf

@[expose] noncomputable def rowB (mul : ℕ → ℕ → ℕ) (i : ℕ) : Bool :=
  allLt (fun j => Bool.rec false (Nat.beq (cK (TK i) (TK j)) (TK (mul i j)))
    (Nat.blt (mul i j) 128)) 128

theorem row_spec (mul : ℕ → ℕ → ℕ) {i : ℕ} (hi : i < 128) (h : rowB mul i = true) :
    ∀ j < 128, mul i j < 128 ∧ compL (tl i) (tl j) = tl (mul i j) := by
  intro j hj
  unfold rowB at h
  have hb : Bool.rec false (Nat.beq (cK (TK i) (TK j)) (TK (mul i j)))
      (Nat.blt (mul i j) 128) = true := of_allLt h j hj
  cases hm : Nat.blt (mul i j) 128
  · rw [hm] at hb
    exact absurd hb Bool.false_ne_true
  · rw [hm] at hb
    have hm' : mul i j < 128 := Nat.blt_eq.mp hm
    refine ⟨hm', ?_⟩
    rw [tl_dec hi, tl_dec hj, tl_dec hm', compL_decL]
    exact congrArg decL (Nat.eq_of_beq_eq_true hb)

@[expose] noncomputable def allL {α : Type} (f : α → Bool) (L : List α) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a _ acc => Bool.rec false acc (f a)) L

theorem allL_iff {α : Type} {f : α → Bool} : ∀ {L : List α}, allL f L = true ↔ ∀ a ∈ L, f a = true
  | [] => by simp [allL]
  | a :: L => by
    change Bool.rec false (allL f L) (f a) = true ↔ _
    rw [List.forall_mem_cons, ← allL_iff]
    cases f a
    · exact ⟨fun h => absurd h Bool.false_ne_true, fun h => absurd h.1 Bool.false_ne_true⟩
    · exact ⟨fun h => ⟨rfl, h⟩, fun h => h.2⟩

@[expose] noncomputable def memN (k : ℕ) (L : List ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a _ acc => Bool.rec acc true (Nat.beq a k)) L

theorem memN_iff {k : ℕ} : ∀ {L : List ℕ}, memN k L = true ↔ k ∈ L
  | [] => by simp [memN]
  | a :: L => by
    change Bool.rec (memN k L) true (Nat.beq a k) = true ↔ _
    rw [List.mem_cons, ← memN_iff]
    by_cases hak : a = k
    · rw [hak, Nat.beq_refl]
      exact ⟨fun _ => Or.inl rfl, fun _ => rfl⟩
    · have hb : Nat.beq a k = false := by
        cases h : Nat.beq a k
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true h) hak
      rw [hb]
      exact ⟨Or.inr, fun h => h.resolve_left fun e => hak e.symm⟩

@[expose] noncomputable def incB (L : List ℕ) : ℕ → Bool :=
  List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
    (fun a _ ih b => Bool.rec false (ih (Nat.succ a)) (Nat.ble b a)) L

theorem nodup_of_incB : ∀ {L : List ℕ} {b : ℕ}, incB L b = true → (∀ x ∈ L, b ≤ x) ∧ L.Nodup
  | [], _, _ => ⟨fun _ h => absurd h List.not_mem_nil, List.nodup_nil⟩
  | a :: L, b, h => by
    have h' : Bool.rec false (incB L (Nat.succ a)) (Nat.ble b a) = true := h
    cases hb : Nat.ble b a
    · rw [hb] at h'
      exact absurd h' Bool.false_ne_true
    · rw [hb] at h'
      have h'' : incB L (Nat.succ a) = true := h'
      obtain ⟨h1, h2⟩ := nodup_of_incB h''
      have hba : b ≤ a := Nat.le_of_ble_eq_true hb
      refine ⟨fun x hx => ?_, List.nodup_cons.2 ⟨fun ha => ?_, h2⟩⟩
      · rcases List.mem_cons.1 hx with rfl | hx
        · exact hba
        · have := h1 x hx
          omega
      · have := h1 a ha
        omega

@[expose] noncomputable def insK (a : ℕ) (L : List ℕ) : List ℕ :=
  List.rec (motive := fun _ => List ℕ) [a]
    (fun b l acc => Bool.rec (b :: acc) (a :: b :: l) (Nat.ble a b)) L

theorem insK_nil (a : ℕ) : insK a [] = [a] := rfl

theorem insK_cons (a b : ℕ) (l : List ℕ) :
    insK a (b :: l) = if a ≤ b then a :: b :: l else b :: insK a l := by
  change Bool.rec (motive := fun _ => List ℕ) (b :: insK a l) (a :: b :: l) (Nat.ble a b) = _
  by_cases hab : a ≤ b
  · rw [if_pos hab, Nat.ble_eq_true_of_le hab]
  · have hb : Nat.ble a b = false := by
      cases h : Nat.ble a b
      · rfl
      · exact absurd (Nat.le_of_ble_eq_true h) hab
    rw [if_neg hab, hb]

@[expose] noncomputable def sortK (L : List ℕ) : List ℕ :=
  List.rec (motive := fun _ => List ℕ) [] (fun a _ acc => insK a acc) L

@[expose] noncomputable def mapSortK (g : ℕ → ℕ) (X : List ℕ) : List ℕ :=
  List.rec (motive := fun _ => List ℕ) [] (fun j _ acc => insK (g j) acc) X

@[expose] noncomputable def extK (g : ℕ → ℕ) (X : List ℕ) : List ℕ :=
  List.rec (motive := fun _ => List ℕ) (mapSortK g X) (fun a _ acc => insK a acc) X

theorem sortK_append (B : List ℕ) : ∀ A : List ℕ,
    sortK (A ++ B) = List.rec (motive := fun _ => List ℕ) (sortK B) (fun a _ acc => insK a acc) A
  | [] => rfl
  | a :: A => by
    change insK a (sortK (A ++ B)) = insK a _
    rw [sortK_append B A]

theorem sortK_map (g : ℕ → ℕ) : ∀ X : List ℕ, sortK (X.map g) = mapSortK g X
  | [] => rfl
  | j :: X => by
    change insK (g j) (sortK (X.map g)) = insK (g j) (mapSortK g X)
    rw [sortK_map g X]

theorem sortK_ext (g : ℕ → ℕ) (X : List ℕ) : sortK (X ++ X.map g) = extK g X := by
  rw [sortK_append, sortK_map]
  rfl

@[expose] noncomputable def eqK (L : List ℕ) : List ℕ → Bool :=
  List.rec (motive := fun _ => List ℕ → Bool)
    (fun M => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) M)
    (fun a _ ih M => List.rec (motive := fun _ => Bool) false
      (fun b M' _ => Bool.rec false (ih M') (Nat.beq a b)) M) L

theorem eq_of_eqK : ∀ {L M : List ℕ}, eqK L M = true → L = M
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h Bool.false_ne_true
  | _ :: _, [], h => absurd h Bool.false_ne_true
  | a :: L, b :: M, h => by
    have h' : Bool.rec false (eqK L M) (Nat.beq a b) = true := h
    cases hb : Nat.beq a b
    · rw [hb] at h'
      exact absurd h' Bool.false_ne_true
    · rw [hb] at h'
      have h'' : eqK L M = true := h'
      rw [Nat.eq_of_beq_eq_true hb, eq_of_eqK h'']

@[expose] noncomputable def keyK (Y : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0
    (fun y _ acc => Nat.add acc (Nat.add (Nat.shiftLeft 1 (Nat.add 64 y)) y)) Y

@[expose] noncomputable def memF (kY : ℕ) (Y : List ℕ) (F : List (List ℕ)) : List ℕ → Bool :=
  List.rec (motive := fun _ => List ℕ → Bool) (fun _ => false)
    (fun Z _ ih ks => List.rec (motive := fun _ => Bool) false
      (fun k ks' _ => Bool.rec (ih ks') (Bool.rec (ih ks') true (eqK Y Z)) (Nat.beq kY k)) ks) F

theorem mem_of_memF {kY : ℕ} {Y : List ℕ} :
    ∀ {F : List (List ℕ)} {ks : List ℕ}, memF kY Y F ks = true → Y ∈ F
  | [], _, h => absurd h Bool.false_ne_true
  | _ :: _, [], h => absurd h Bool.false_ne_true
  | Z :: F, k :: ks, h => by
    have h' : Bool.rec (memF kY Y F ks) (Bool.rec (memF kY Y F ks) true (eqK Y Z))
        (Nat.beq kY k) = true := h
    cases hk : Nat.beq kY k
    · rw [hk] at h'
      have h'' : memF kY Y F ks = true := h'
      exact List.mem_cons_of_mem _ (mem_of_memF h'')
    · rw [hk] at h'
      cases he : eqK Y Z
      · rw [he] at h'
        have h'' : memF kY Y F ks = true := h'
        exact List.mem_cons_of_mem _ (mem_of_memF h'')
      · rw [eq_of_eqK he]
        exact List.mem_cons_self

@[expose] noncomputable def extOK (Y : List ℕ) (F : List (List ℕ)) (ks : List ℕ) : Bool :=
  memF (keyK Y) Y F ks

@[expose] noncomputable def famB (mul : ℕ → ℕ → ℕ) (F : List (List ℕ)) (I ks : List ℕ) : Bool :=
  allL (fun X => allL (fun u => Bool.rec
    (Bool.rec true (extOK (extK (fun j => mul j u) X) F ks)
      (allL (fun j => Nat.beq (mul u j) (mul j u)) X)) true (memN u X)) I) F

theorem famB_spec {mul : ℕ → ℕ → ℕ} {F : List (List ℕ)} {I ks : List ℕ} (h : famB mul F I ks = true) :
    ∀ X ∈ F, ∀ u ∈ I, u ∉ X → (∀ j ∈ X, mul u j = mul j u) → extK (fun j => mul j u) X ∈ F := by
  intro X hX u hu hn hc
  have h1 : Bool.rec (Bool.rec true (extOK (extK (fun j => mul j u) X) F ks)
      (allL (fun j => Nat.beq (mul u j) (mul j u)) X)) true (memN u X) = true :=
    allL_iff.1 (allL_iff.1 h X hX) u hu
  have hm : memN u X = false := by
    cases e : memN u X
    · rfl
    · exact absurd (memN_iff.1 e) hn
  have hcB : allL (fun j => Nat.beq (mul u j) (mul j u)) X = true := by
    refine allL_iff.2 fun j hj => ?_
    change Nat.beq (mul u j) (mul j u) = true
    rw [hc j hj]
    exact Nat.beq_refl _
  rw [hm, hcB] at h1
  exact mem_of_memF h1

end CFSG.Quasithin.M12AmalAut.JPack
