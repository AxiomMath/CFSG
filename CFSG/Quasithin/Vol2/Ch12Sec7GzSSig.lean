module

public import Certificates.Data.S1277Sig
public import CFSG.Quasithin.Vol2.Ch12Sec7GzSAct

public section

namespace CFSG.Quasithin.H13.I1277

open Certificates.Data.S1277Sig

theorem applyCols_nil (x : Nat) : applyCols [] x = 0 := rfl

theorem applyCols_cons (c : Nat) (cs : List Nat) (x : Nat) :
    applyCols (c :: cs) x = (if x % 2 = 1 then c else 0) ^^^ applyCols cs (x / 2) := rfl

theorem applyCols_zero (cols : List Nat) : applyCols cols 0 = 0 := by
  induction cols with
  | nil => rfl
  | cons c cs ih => rw [applyCols_cons]; simp [ih]

theorem applyCols_xor (cols : List Nat) : ∀ x y : Nat,
    applyCols cols (x ^^^ y) = applyCols cols x ^^^ applyCols cols y := by
  induction cols with
  | nil => intro x y; simp [applyCols_nil]
  | cons c cs ih =>
    intro x y
    rw [applyCols_cons, applyCols_cons, applyCols_cons, Nat.xor_div_two, ih]
    have hxy : (x ^^^ y) % 2 = (x + y) % 2 := Nat.xor_mod_two_eq
    rcases Nat.mod_two_eq_zero_or_one x with hx | hx <;>
      rcases Nat.mod_two_eq_zero_or_one y with hy | hy
    · have : (x ^^^ y) % 2 = 0 := by omega
      simp [hx, hy, this, Nat.xor_assoc, Nat.xor_comm, Nat.xor_left_comm]
    · have : (x ^^^ y) % 2 = 1 := by omega
      simp [hx, hy, this, Nat.xor_assoc, Nat.xor_comm, Nat.xor_left_comm]
    · have : (x ^^^ y) % 2 = 1 := by omega
      simp [hx, hy, this, Nat.xor_assoc, Nat.xor_comm, Nat.xor_left_comm]
    · have : (x ^^^ y) % 2 = 0 := by omega
      simp [hx, hy, this, Nat.xor_assoc, Nat.xor_comm, Nat.xor_left_comm]

theorem applyCols_lt {d : Nat} {cols : List Nat} (h : ∀ c ∈ cols, c < 2 ^ d) (x : Nat) :
    applyCols cols x < 2 ^ d := by
  induction cols generalizing x with
  | nil => rw [applyCols_nil]; exact Nat.two_pow_pos _
  | cons c cs ih =>
    rw [applyCols_cons]
    refine Nat.xor_lt_two_pow ?_ (ih (fun c' hc' => h c' (List.mem_cons_of_mem _ hc')) _)
    split_ifs
    · exact h c List.mem_cons_self
    · exact Nat.two_pow_pos _

theorem applyCols_append_lt (p q : List Nat) : ∀ x : Nat, x < 2 ^ p.length →
    applyCols (p ++ q) x = applyCols p x := by
  induction p with
  | nil =>
    intro x hx
    rw [List.length_nil, pow_zero] at hx
    have hx0 : x = 0 := by omega
    subst hx0
    simp [applyCols_zero]
  | cons c cs ih =>
    intro x hx
    simp only [List.cons_append, applyCols_cons]
    rw [ih (x / 2)]
    rw [List.length_cons, pow_succ] at hx
    omega

theorem applyCols_append_ge (c : Nat) (p : List Nat) : ∀ y : Nat, y < 2 ^ p.length →
    applyCols (p ++ [c]) (2 ^ p.length + y) = c ^^^ applyCols p y := by
  induction p with
  | nil =>
    intro y hy
    rw [List.length_nil, pow_zero] at hy
    have hy0 : y = 0 := by omega
    subst hy0
    simp [applyCols_cons, applyCols_nil]
  | cons c' cs ih =>
    intro y hy
    simp only [List.cons_append, applyCols_cons, List.length_cons]
    have hy' : y / 2 < 2 ^ cs.length := by
      rw [List.length_cons, pow_succ] at hy; omega
    have e1 : (2 ^ (cs.length + 1) + y) % 2 = y % 2 := by
      rw [pow_succ]; omega
    have e2 : (2 ^ (cs.length + 1) + y) / 2 = 2 ^ cs.length + y / 2 := by
      rw [pow_succ]; omega
    rw [e1, e2, ih (y / 2) hy']
    exact Nat.xor_left_comm _ _ _

theorem applyCols_pow (cols : List Nat) (i : Nat) (hi : i < cols.length) :
    applyCols cols (2 ^ i) = cols[i] := by
  induction cols generalizing i with
  | nil => simp at hi
  | cons c cs ih =>
    cases i with
    | zero => simp [applyCols_cons, applyCols_zero]
    | succ i =>
      rw [applyCols_cons]
      have e1 : 2 ^ (i + 1) % 2 = 0 := by rw [pow_succ]; omega
      have e2 : 2 ^ (i + 1) / 2 = 2 ^ i := by rw [pow_succ]; omega
      rw [e1, e2, ih i (by simpa using hi)]
      simp


theorem okPre_iff (φ : Nat → Nat) (cols : List Nat) :
    okPre φ cols = true ↔ ∀ x < 2 ^ cols.length, φ (applyCols cols x) = φ x := by
  unfold okPre
  simp [List.all_eq_true]

theorem okInc_iff (φ : Nat → Nat) (p : List Nat) (c : Nat) :
    okInc φ p c = true ↔ ∀ y < 2 ^ p.length, φ (c ^^^ applyCols p y) = φ (2 ^ p.length + y) := by
  unfold okInc
  simp [List.all_eq_true]

theorem okPre_append (φ : Nat → Nat) (p : List Nat) (c : Nat) :
    okPre φ (p ++ [c]) = true ↔ okPre φ p = true ∧ okInc φ p c = true := by
  rw [okPre_iff, okPre_iff, okInc_iff]
  have hlen : (p ++ [c]).length = p.length + 1 := by simp
  rw [hlen]
  constructor
  · intro h
    refine ⟨fun x hx => ?_, fun y hy => ?_⟩
    · have := h x (by rw [pow_succ]; omega)
      rwa [applyCols_append_lt p [c] x hx] at this
    · have := h (2 ^ p.length + y) (by rw [pow_succ]; omega)
      rw [applyCols_append_ge c p y hy] at this
      exact this
  · rintro ⟨h1, h2⟩ x hx
    by_cases hlt : x < 2 ^ p.length
    · rw [applyCols_append_lt p [c] x hlt]; exact h1 x hlt
    · obtain ⟨y, rfl⟩ : ∃ y, x = 2 ^ p.length + y := ⟨x - 2 ^ p.length, by omega⟩
      have hy : y < 2 ^ p.length := by rw [pow_succ] at hx; omega
      rw [applyCols_append_ge c p y hy]; exact h2 y hy

theorem mem_sigEnum (d : Nat) (φ : Nat → Nat) : ∀ (k : Nat) (cols : List Nat),
    cols ∈ sigEnum d φ k ↔ cols.length = k ∧ (∀ c ∈ cols, c < 2 ^ d) ∧ okPre φ cols = true := by
  intro k
  induction k with
  | zero =>
    intro cols
    simp only [sigEnum, List.mem_singleton]
    constructor
    · rintro rfl
      refine ⟨rfl, by simp, ?_⟩
      rw [okPre_iff]
      intro x hx
      simp at hx; subst hx
      simp [applyCols_zero]
    · rintro ⟨h, -, -⟩
      exact List.length_eq_zero_iff.1 h
  | succ k ih =>
    intro cols
    unfold sigEnum
    simp only [List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range]
    constructor
    · rintro ⟨p, hp, c, ⟨hc, hinc⟩, rfl⟩
      obtain ⟨h1, h2, h3⟩ := (ih p).1 hp
      refine ⟨by simp [h1], ?_, (okPre_append φ p c).2 ⟨h3, hinc⟩⟩
      intro c' hc'
      rcases List.mem_append.1 hc' with h | h
      · exact h2 c' h
      · rw [List.mem_singleton.1 h]; exact hc
    · rintro ⟨hlen, hlt, hok⟩
      rcases List.eq_nil_or_concat cols with rfl | ⟨p, c, hcols⟩
      · simp at hlen
      · rw [List.concat_eq_append] at hcols
        subst hcols
        have hplen : p.length = k := by simpa using hlen
        obtain ⟨h3, hinc⟩ := (okPre_append φ p c).1 hok
        refine ⟨p, (ih p).2 ⟨hplen, fun c' hc' => hlt c' (List.mem_append_left _ hc'), h3⟩, c,
          ⟨hlt c (List.mem_append_right _ (List.mem_singleton_self c)), hinc⟩, rfl⟩

theorem sigEnum_nodup (d : Nat) (φ : Nat → Nat) : ∀ k, (sigEnum d φ k).Nodup := by
  intro k
  induction k with
  | zero => simp [sigEnum]
  | succ k ih =>
    unfold sigEnum
    rw [List.nodup_flatMap]
    refine ⟨fun p _ => ?_, ?_⟩
    · refine (List.Nodup.filter _ (List.nodup_range)).map ?_
      intro c c' h
      have := List.append_cancel_left h
      simpa using this
    · refine List.Pairwise.imp_of_mem ?_ ih
      intro p p' hp hp' hne
      simp only [Function.onFun, List.disjoint_left]
      intro x hx hx'
      simp only [List.mem_map] at hx hx'
      obtain ⟨c, -, rfl⟩ := hx
      obtain ⟨c', -, hcc⟩ := hx'
      have := List.append_inj' hcc rfl
      exact hne this.1.symm

theorem sigList_nodup (d : Nat) (φ : Nat → Nat) : (sigList d φ).Nodup :=
  (sigEnum_nodup d φ d).filter _

theorem mem_sigList (d : Nat) (φ : Nat → Nat) (cols : List Nat) :
    cols ∈ sigList d φ ↔ cols.length = d ∧ (∀ c ∈ cols, c < 2 ^ d) ∧ okPre φ cols = true ∧
      ((List.range (2 ^ d)).map (applyCols cols)).Nodup := by
  unfold sigList
  rw [List.mem_filter, mem_sigEnum]
  unfold injCols
  simp only [decide_eq_true_eq]
  tauto


theorem xor_pow_of_lt (k : Nat) : ∀ y, y < 2 ^ k → 2 ^ k ^^^ y = 2 ^ k + y := by
  induction k with
  | zero =>
    intro y hy
    rw [pow_zero] at hy
    have : y = 0 := by omega
    subst this; simp
  | succ k ih =>
    intro y hy
    have hy2 : y / 2 < 2 ^ k := by rw [pow_succ] at hy; omega
    have h1 : (2 ^ (k + 1) ^^^ y) % 2 = (2 ^ (k + 1) + y) % 2 := Nat.xor_mod_two_eq
    have h2 : (2 ^ (k + 1) ^^^ y) / 2 = (2 ^ (k + 1) + y) / 2 := by
      rw [Nat.xor_div_two, show 2 ^ (k + 1) / 2 = 2 ^ k by rw [pow_succ]; omega, ih _ hy2]
      rw [pow_succ]; omega
    omega

def colsOf {d : Nat} (σ : Equiv.Perm (Fin (2 ^ d))) : List Nat :=
  (List.range d).map fun i =>
    if h : i < d then (σ ⟨2 ^ i, Nat.pow_lt_pow_right (by norm_num) h⟩).1 else 0

theorem length_colsOf {d : Nat} (σ : Equiv.Perm (Fin (2 ^ d))) : (colsOf σ).length = d := by
  simp [colsOf]

theorem getElem_colsOf {d : Nat} (σ : Equiv.Perm (Fin (2 ^ d))) (i : Nat) (hi : i < d) :
    (colsOf σ)[i]'(by rw [length_colsOf]; exact hi) =
      (σ ⟨2 ^ i, Nat.pow_lt_pow_right (by norm_num) hi⟩).1 := by
  simp [colsOf, hi]

theorem applyCols_colsOf {d : Nat} {σ : Equiv.Perm (Fin (2 ^ d))}
    (hσ : ∀ a b c : Fin (2 ^ d), a.1 ^^^ b.1 = c.1 → (σ a).1 ^^^ (σ b).1 = (σ c).1) :
    ∀ x : Fin (2 ^ d), (σ x).1 = applyCols (colsOf σ) x.1 := by
  have h0 : (σ ⟨0, Nat.two_pow_pos d⟩).1 = 0 := by
    have := hσ ⟨0, Nat.two_pow_pos d⟩ ⟨0, Nat.two_pow_pos d⟩ ⟨0, Nat.two_pow_pos d⟩ (by simp)
    rw [Nat.xor_self] at this
    exact this.symm
  have key : ∀ k, k ≤ d → ∀ x (hx : x < 2 ^ d), x < 2 ^ k →
      (σ ⟨x, hx⟩).1 = applyCols ((colsOf σ).take k) x := by
    intro k
    induction k with
    | zero =>
      intro _ x hx hxk
      rw [pow_zero] at hxk
      have : x = 0 := by omega
      subst this
      simpa [applyCols_zero] using h0
    | succ k ih =>
      intro hk x hx hxk
      have hkd : k < d := hk
      have hlen : ((colsOf σ).take k).length = k := by
        rw [List.length_take, length_colsOf]; omega
      have htake : (colsOf σ).take (k + 1) = (colsOf σ).take k ++ [(colsOf σ)[k]'(by
          rw [length_colsOf]; exact hkd)] := List.take_succ_eq_append_getElem _
      rw [htake]
      by_cases hlt : x < 2 ^ k
      · rw [applyCols_append_lt _ _ x (by rw [hlen]; exact hlt)]
        exact ih (by omega) x hx hlt
      · obtain ⟨y, rfl⟩ : ∃ y, x = 2 ^ k + y := ⟨x - 2 ^ k, by omega⟩
        have hy : y < 2 ^ k := by rw [pow_succ] at hxk; omega
        have hyd : y < 2 ^ d := by
          have : 2 ^ k ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hkd.le
          omega
        have e1 := applyCols_append_ge ((colsOf σ)[k]'(by rw [length_colsOf]; exact hkd))
          ((colsOf σ).take k) y (by rw [hlen]; exact hy)
        rw [hlen] at e1
        have hσk := hσ ⟨2 ^ k, Nat.pow_lt_pow_right (by norm_num) hkd⟩ ⟨y, hyd⟩ ⟨2 ^ k + y, hx⟩
          (by simpa using xor_pow_of_lt k y hy)
        rw [← hσk, e1, ih (by omega) y hyd hy, getElem_colsOf σ k hkd]
  intro x
  have := key d le_rfl x.1 x.2 x.2
  rw [this, List.take_of_length_le (by rw [length_colsOf])]

@[expose] noncomputable def ofCols (d : Nat) (cols : List Nat) (hlt : ∀ c ∈ cols, c < 2 ^ d)
    (hinj : ((List.range (2 ^ d)).map (applyCols cols)).Nodup) : Equiv.Perm (Fin (2 ^ d)) :=
  Equiv.ofBijective (fun x => ⟨applyCols cols x.1, applyCols_lt hlt x.1⟩) (by
    apply Finite.injective_iff_bijective.1
    intro x y hxy
    have hxy' : applyCols cols x.1 = applyCols cols y.1 := congrArg Fin.val hxy
    have hnd := List.nodup_map_iff_inj_on (List.nodup_range) |>.1 hinj
    exact Fin.ext (hnd x.1 (List.mem_range.2 x.2) y.1 (List.mem_range.2 y.2) hxy'))

theorem ofCols_apply (d : Nat) (cols : List Nat) (hlt : ∀ c ∈ cols, c < 2 ^ d)
    (hinj : ((List.range (2 ^ d)).map (applyCols cols)).Nodup) (x : Fin (2 ^ d)) :
    (ofCols d cols hlt hinj x).1 = applyCols cols x.1 := rfl


theorem colsOf_mem_sigList {d : Nat} {φ : Nat → Nat} {σ : Equiv.Perm (Fin (2 ^ d))}
    (hσ : σ ∈ Sig d φ) : colsOf σ ∈ sigList d φ := by
  rw [mem_sigList]
  obtain ⟨hadd, hφ⟩ := hσ
  refine ⟨length_colsOf σ, ?_, ?_, ?_⟩
  · intro c hc
    unfold colsOf at hc
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hc
    rw [List.mem_range] at hi
    simp only [hi, dite_true]
    exact (σ _).2
  · rw [okPre_iff, length_colsOf]
    intro x hx
    have := applyCols_colsOf hadd ⟨x, hx⟩
    rw [← this]
    exact hφ ⟨x, hx⟩
  · refine List.Nodup.map_on ?_ List.nodup_range
    intro x hx y hy hxy
    have hx' : x < 2 ^ d := List.mem_range.1 hx
    have hy' : y < 2 ^ d := List.mem_range.1 hy
    have h1 := applyCols_colsOf hadd ⟨x, hx'⟩
    have h2 := applyCols_colsOf hadd ⟨y, hy'⟩
    have : (σ ⟨x, hx'⟩).1 = (σ ⟨y, hy'⟩).1 := by
      rw [h1, h2]; exact hxy
    have := σ.injective (Fin.ext this)
    exact congrArg Fin.val this

theorem exists_of_mem_sigList {d : Nat} {φ : Nat → Nat} {cols : List Nat}
    (h : cols ∈ sigList d φ) : ∃ σ ∈ Sig d φ, colsOf σ = cols := by
  obtain ⟨hlen, hlt, hok, hinj⟩ := (mem_sigList d φ cols).1 h
  refine ⟨ofCols d cols hlt hinj, ⟨?_, ?_⟩, ?_⟩
  · intro a b c habc
    rw [ofCols_apply, ofCols_apply, ofCols_apply, ← applyCols_xor, habc]
  · intro a
    rw [ofCols_apply]
    exact (okPre_iff φ cols).1 hok a.1 (by rw [hlen]; exact a.2)
  · apply List.ext_getElem
    · rw [length_colsOf, hlen]
    · intro i h1 h2
      have hi : i < d := by simpa [length_colsOf] using h1
      rw [getElem_colsOf _ i hi, ofCols_apply]
      exact applyCols_pow cols i h2

theorem colsOf_injective {d : Nat} {φ : Nat → Nat} {σ τ : Equiv.Perm (Fin (2 ^ d))}
    (hσ : σ ∈ Sig d φ) (hτ : τ ∈ Sig d φ) (h : colsOf σ = colsOf τ) : σ = τ := by
  apply Equiv.ext
  intro x
  apply Fin.ext
  rw [applyCols_colsOf hσ.1 x, applyCols_colsOf hτ.1 x, h]

theorem card_Sig (d : Nat) (φ : Nat → Nat) : Nat.card ↥(Sig d φ) = (sigList d φ).length := by
  let f : ↥(Sig d φ) → {c : List Nat // c ∈ sigList d φ} := fun σ => ⟨colsOf σ.1, colsOf_mem_sigList σ.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro σ τ h
      exact Subtype.ext (colsOf_injective σ.2 τ.2 (congrArg Subtype.val h))
    · rintro ⟨c, hc⟩
      obtain ⟨σ, hσ, rfl⟩ := exists_of_mem_sigList hc
      exact ⟨⟨σ, hσ⟩, rfl⟩
  rw [Nat.card_congr (Equiv.ofBijective f hf)]
  have e2 : {c : List Nat // c ∈ sigList d φ} ≃ ↥(sigList d φ).toFinset :=
    Equiv.subtypeEquivRight fun c => by simp
  rw [Nat.card_congr e2, Nat.card_eq_finsetCard, List.toFinset_card_of_nodup (sigList_nodup d φ)]


theorem colsOf_one (d : Nat) : colsOf (1 : Equiv.Perm (Fin (2 ^ d))) = idCols d := by
  apply List.ext_getElem
  · rw [length_colsOf]; simp [idCols]
  · intro i h1 h2
    have hi : i < d := by simpa [length_colsOf] using h1
    rw [getElem_colsOf _ i hi]
    simp [idCols]

theorem colsOf_mul {d : Nat} {σ : Equiv.Perm (Fin (2 ^ d))}
    (hσ : ∀ a b c : Fin (2 ^ d), a.1 ^^^ b.1 = c.1 → (σ a).1 ^^^ (σ b).1 = (σ c).1)
    (τ : Equiv.Perm (Fin (2 ^ d))) : colsOf (σ * τ) = compCols (colsOf σ) (colsOf τ) := by
  apply List.ext_getElem
  · rw [length_colsOf]; simp [compCols, length_colsOf]
  · intro i h1 h2
    have hi : i < d := by simpa [length_colsOf] using h1
    rw [getElem_colsOf _ i hi]
    simp only [compCols, List.getElem_map]
    rw [getElem_colsOf τ i hi]
    exact applyCols_colsOf hσ _

end CFSG.Quasithin.H13.I1277

end
