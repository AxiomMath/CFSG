module

public import CFSG.Quasithin.H13.AS91Sec3Masks
public import CFSG.Quasithin.AppendixH.Common.OctadBasic
public import Certificates.Certificate89011

public section

open scoped Pointwise

namespace CFSG.Quasithin.H13.AS91.M24G

open CFSG.ASVolI.ChH

@[expose] def octFin (i : ℕ) : Finset (Fin 24) := maskFin (Native.octList ())[i]!

@[expose] def trioOf (t : ℕ × ℕ × ℕ) : Finset (Finset (Fin 24)) :=
  {maskFin t.1, maskFin t.2.1, maskFin t.2.2}

@[expose] def trioFin (p : ℕ) : Finset (Finset (Fin 24)) := trioOf (Native.trioList ())[p]!

@[expose] def sextOfL (s : List ℕ) : Finset (Finset (Fin 24)) := (s.map maskFin).toFinset

@[expose] def sextFin (q : ℕ) : Finset (Finset (Fin 24)) := sextOfL (Native.sextList ())[q]!

theorem maskFin_zero : maskFin 0 = ∅ := (maskFin_eq_empty (by norm_num)).2 rfl

theorem octList_octIdx {m : ℕ} (h : Native.octIdx m < 759) :
    (Native.octList ())[Native.octIdx m]! = m := by
  unfold Native.octIdx at h ⊢
  split at h
  · rename_i q _
    split_ifs at h ⊢ with hq
    · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hq
      exact hq.2
    · exact absurd h (by simp [Native.nOct])
  · exact absurd h (by simp [Native.nOct])

theorem trioList_trioIdx {u : ℕ × ℕ × ℕ} (h : Native.trioIdx u < 3795) :
    (Native.trioList ())[Native.trioIdx u]! = u := by
  unfold Native.trioIdx at h ⊢
  split at h
  · rename_i q _
    split_ifs at h ⊢ with hq
    · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hq
      exact hq.2
    · exact absurd h (by simp [Native.nTrio])
  · exact absurd h (by simp [Native.nTrio])

theorem sextList_sextIdx {s : List ℕ} (h : Native.sextIdx s < 1771) :
    (Native.sextList ())[Native.sextIdx s]! = s := by
  unfold Native.sextIdx at h ⊢
  split at h
  · rename_i q _
    split_ifs at h ⊢ with hq
    · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hq
      exact hq.2
    · exact absurd h (by simp [Native.nSext])
  · exact absurd h (by simp [Native.nSext])

theorem octFin_octIdx {m : ℕ} (h : Native.octIdx m < 759) :
    octFin (Native.octIdx m) = maskFin m := by
  rw [octFin, octList_octIdx h]

theorem trioOf_trioIdx {u : ℕ × ℕ × ℕ} (h : Native.trioIdx u < 3795) :
    trioFin (Native.trioIdx u) = trioOf u := by
  rw [trioFin, trioList_trioIdx h]

theorem sextOfL_sextIdx {s : List ℕ} (h : Native.sextIdx s < 1771) :
    sextFin (Native.sextIdx s) = sextOfL s := by
  rw [sextFin, sextList_sextIdx h]

theorem smul_octFin {t : Array ℕ} {g : Equiv.Perm (Fin 24)} (h : RepT t g) {i : ℕ}
    (hi : i < 759) : g • octFin i = maskFin (Native.img t (Native.octList ())[i]!) := by
  rw [octFin, maskFin_img h]

theorem trioOf_sort3 (a b c : ℕ) :
    trioOf (Native.sort3 a b c) = {maskFin a, maskFin b, maskFin c} := by
  unfold Native.sort3 trioOf
  split_ifs <;> ext x <;> simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto

theorem smul_trioFin {t : Array ℕ} {g : Equiv.Perm (Fin 24)} (h : RepT t g) {p : ℕ}
    (hp : p < 3795) :
    g • trioFin p = trioOf (Native.imgTrio t (Native.trioList ())[p]!) := by
  rw [trioFin, Native.imgTrio, trioOf_sort3, trioOf, Finset.smul_finset_insert,
    Finset.smul_finset_insert, Finset.smul_finset_singleton, maskFin_img h, maskFin_img h,
    maskFin_img h]

theorem mem_sortL {x : ℕ} {l : List ℕ} : x ∈ Native.sortL l ↔ x ∈ l :=
  (List.mergeSort_perm l _).mem_iff

theorem mem_sextOfL {s : List ℕ} {X : Finset (Fin 24)} :
    X ∈ sextOfL s ↔ ∃ x ∈ s, maskFin x = X := by
  simp [sextOfL]

theorem smul_sextOfL {t : Array ℕ} {g : Equiv.Perm (Fin 24)} (h : RepT t g) (s : List ℕ) :
    g • sextOfL s = sextOfL (Native.imgSext t s) := by
  ext X
  rw [Finset.mem_smul_finset]
  simp only [mem_sextOfL, Native.imgSext, mem_sortL, List.mem_map]
  constructor
  · rintro ⟨Y, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨Native.img t x, ⟨x, hx, rfl⟩, maskFin_img h x⟩
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨maskFin x, ⟨x, hx, rfl⟩, (maskFin_img h x).symm⟩

theorem smul_sextFin {t : Array ℕ} {g : Equiv.Perm (Fin 24)} (h : RepT t g) {q : ℕ}
    (hq : q < 1771) :
    g • sextFin q = sextOfL (Native.imgSext t (Native.sextList ())[q]!) := by
  rw [sextFin, smul_sextOfL h]

theorem ne_of_disjoint_octad {X Y : Finset (Fin 24)} (hX : IsOctad X) (h : Disjoint X Y) :
    X ≠ Y := by
  rintro rfl
  have h0 := Finset.disjoint_self_iff_empty _ |>.1 h
  have h8 := hX.1
  rw [h0] at h8
  simp at h8

theorem isTrio_of_three {A B C : Finset (Fin 24)} (hA : IsOctad A) (hB : IsOctad B)
    (hC : IsOctad C) (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hU : A ∪ B ∪ C = Finset.univ) : IsTrio {A, B, C} := by
  refine ⟨Finset.card_eq_three.2 ⟨A, B, C, ne_of_disjoint_octad hA hAB,
    ne_of_disjoint_octad hA hAC, ne_of_disjoint_octad hB hBC, rfl⟩, ?_, ?_, ?_⟩
  · intro O hO
    simp only [Finset.mem_insert, Finset.mem_singleton] at hO
    rcases hO with rfl | rfl | rfl <;> assumption
  · intro O hO O' hO' hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hO hO'
    rcases hO with rfl | rfl | rfl <;> rcases hO' with rfl | rfl | rfl <;>
      first
        | exact absurd rfl hne
        | exact hAB | exact hAB.symm | exact hAC | exact hAC.symm | exact hBC | exact hBC.symm
  · rw [Finset.biUnion_insert, Finset.biUnion_insert, Finset.singleton_biUnion]
    simpa [Finset.union_assoc] using hU

theorem trio_eq_of_mem {T : Finset (Finset (Fin 24))} (hT : IsTrio T) {A B : Finset (Fin 24)}
    (hA : A ∈ T) (hB : B ∈ T) (hAB : A ≠ B) : T = {A, B, (A ∪ B)ᶜ} := by
  have hAo := hT.2.1 A hA
  have hBo := hT.2.1 B hB
  have hdisj : Disjoint A B := hT.2.2.1 A hA B hB hAB
  have hcardC : ((A ∪ B)ᶜ).card = 8 := by
    rw [Finset.card_compl, Finset.card_union_of_disjoint hdisj, hAo.1, hBo.1]
    simp
  have hAC : Disjoint A (A ∪ B)ᶜ := by
    rw [Finset.disjoint_left]
    intro x hxA hx
    simp [hxA] at hx
  have hBC : Disjoint B (A ∪ B)ᶜ := by
    rw [Finset.disjoint_left]
    intro x hxB hx
    simp [hxB] at hx
  have hCT : (A ∪ B)ᶜ ∈ T := by
    obtain ⟨X, hXT, hXn⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({A, B} : Finset (Finset (Fin 24)))) (t := T)
      (by rw [hT.1, Finset.card_pair hAB]; norm_num)
    have hXA : X ≠ A := fun h => hXn (by simp [h])
    have hXB : X ≠ B := fun h => hXn (by simp [h])
    have hXo := hT.2.1 X hXT
    have hXsub : X ⊆ (A ∪ B)ᶜ := by
      intro x hx
      simp only [Finset.mem_compl, Finset.mem_union, not_or]
      exact ⟨fun h => Finset.disjoint_left.1 (hT.2.2.1 X hXT A hA hXA) hx h,
        fun h => Finset.disjoint_left.1 (hT.2.2.1 X hXT B hB hXB) hx h⟩
    have hXeq : X = (A ∪ B)ᶜ := Finset.eq_of_subset_of_card_le hXsub (by rw [hcardC, hXo.1])
    rw [← hXeq]
    exact hXT
  have hsub : ({A, B, (A ∪ B)ᶜ} : Finset (Finset (Fin 24))) ⊆ T := by
    intro X hX
    simp only [Finset.mem_insert, Finset.mem_singleton] at hX
    rcases hX with rfl | rfl | rfl
    · exact hA
    · exact hB
    · exact hCT
  have hcard3 : ({A, B, (A ∪ B)ᶜ} : Finset (Finset (Fin 24))).card = 3 :=
    Finset.card_eq_three.2 ⟨A, B, (A ∪ B)ᶜ, hAB, ne_of_disjoint_octad hAo hAC,
      ne_of_disjoint_octad hBo hBC, rfl⟩
  exact (Finset.eq_of_subset_of_card_le hsub (by rw [hT.1, hcard3])).symm

theorem isTrio_trioOf {t : ℕ × ℕ × ℕ} (h1 : IsOctad (maskFin t.1))
    (h2 : IsOctad (maskFin t.2.1)) (h3 : IsOctad (maskFin t.2.2)) (h12 : t.1 &&& t.2.1 = 0)
    (h13 : t.1 &&& t.2.2 = 0) (h23 : t.2.1 &&& t.2.2 = 0)
    (hU : t.1 ||| t.2.1 ||| t.2.2 = Native.full) : IsTrio (trioOf t) := by
  have hd : ∀ {a b : ℕ}, a &&& b = 0 → Disjoint (maskFin a) (maskFin b) := fun h => by
    rw [disjoint_maskFin, h, maskFin_zero]
  refine isTrio_of_three h1 h2 h3 (hd h12) (hd h13) (hd h23) ?_
  rw [← maskFin_or, ← maskFin_or, hU, maskFin_full]

theorem trioOf_inj {a b c a' b' c' : ℕ} (h1 : a < b) (h2 : b < c) (h3 : c < 2 ^ 24)
    (h1' : a' < b') (h2' : b' < c') (h3' : c' < 2 ^ 24)
    (h : trioOf (a, b, c) = trioOf (a', b', c')) : (a, b, c) = (a', b', c') := by
  have mem : ∀ {x : ℕ}, x < 2 ^ 24 → ∀ {u v w : ℕ}, u < 2 ^ 24 → v < 2 ^ 24 → w < 2 ^ 24 →
      maskFin x ∈ trioOf (u, v, w) → x = u ∨ x = v ∨ x = w := by
    intro x hx u v w hu hv hw hm
    simp only [trioOf, Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with hm | hm | hm
    · exact Or.inl (maskFin_inj hx hu hm)
    · exact Or.inr (Or.inl (maskFin_inj hx hv hm))
    · exact Or.inr (Or.inr (maskFin_inj hx hw hm))
  have ha : maskFin a ∈ trioOf (a, b, c) := by simp [trioOf]
  have hb : maskFin b ∈ trioOf (a, b, c) := by simp [trioOf]
  have hc : maskFin c ∈ trioOf (a, b, c) := by simp [trioOf]
  have ha' : maskFin a' ∈ trioOf (a', b', c') := by simp [trioOf]
  have hb' : maskFin b' ∈ trioOf (a', b', c') := by simp [trioOf]
  have hc' : maskFin c' ∈ trioOf (a', b', c') := by simp [trioOf]
  rw [h] at ha hb hc
  rw [← h] at ha' hb' hc'
  have e1 := mem (by omega) (by omega) (by omega) (by omega) ha
  have e2 := mem (by omega) (by omega) (by omega) (by omega) hb
  have e3 := mem (by omega) (by omega) (by omega) (by omega) hc
  have e4 := mem (by omega) (by omega) (by omega) (by omega) ha'
  have e5 := mem (by omega) (by omega) (by omega) (by omega) hb'
  have e6 := mem (by omega) (by omega) (by omega) (by omega) hc'
  simp only [Prod.mk.injEq]
  omega

theorem maskFin_full_xor {a b : ℕ} (h : Disjoint (maskFin a) (maskFin b)) :
    maskFin (Native.full ^^^ a ^^^ b) = (maskFin a ∪ maskFin b)ᶜ := by
  ext x
  rw [maskFin_xor, maskFin_xor, maskFin_full]
  simp only [Finset.mem_symmDiff, Finset.mem_univ, true_and, Finset.mem_compl, Finset.mem_union,
    not_or]
  by_cases hA : x ∈ maskFin a <;> by_cases hB : x ∈ maskFin b
  · exact absurd hB (Finset.disjoint_left.1 h hA)
  all_goals simp [hA, hB]

theorem mem_maskFin_foldl_or (l : List ℕ) : ∀ (a : ℕ) (i : Fin 24),
    i ∈ maskFin (l.foldl (fun x y => x ||| y) a) ↔ i ∈ maskFin a ∨ ∃ x ∈ l, i ∈ maskFin x := by
  induction l with
  | nil => intro a i; simp
  | cons x l ih =>
    intro a i
    rw [List.foldl_cons, ih, maskFin_or, Finset.mem_union]
    simp only [List.mem_cons, exists_eq_or_imp]
    tauto

theorem isSextet_sextOfL {s : List ℕ} (hlen : s.length = 6) (hpw : s.Pairwise (· < ·))
    (hpop : ∀ x ∈ s, Native.pop x = 4 ∧ x < 2 ^ 24)
    (hU : s.foldl (fun x y => x ||| y) 0 = Native.full)
    (hpair : ∀ x ∈ s, ∀ y ∈ s, x = y ∨ x &&& y = 0 ∧ IsOctad (maskFin (x ||| y))) :
    IsSextet (sextOfL s) := by
  have hnd : s.Nodup := hpw.imp (fun h => ne_of_lt h)
  have hinj : ∀ x ∈ s, ∀ y ∈ s, maskFin x = maskFin y → x = y :=
    fun x hx y hy h => maskFin_inj (hpop x hx).2 (hpop y hy).2 h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [sextOfL, List.toFinset_card_of_nodup (hnd.map_on hinj), List.length_map, hlen]
  · intro B hB
    obtain ⟨x, hx, rfl⟩ := mem_sextOfL.1 hB
    rw [card_maskFin, (hpop x hx).1]
  · intro B hB B' hB' hne
    obtain ⟨x, hx, rfl⟩ := mem_sextOfL.1 hB
    obtain ⟨y, hy, rfl⟩ := mem_sextOfL.1 hB'
    rcases hpair x hx y hy with h | ⟨h, -⟩
    · exact absurd (by rw [h]) hne
    · rw [disjoint_maskFin, h, maskFin_zero]
  · ext i
    simp only [Finset.mem_biUnion, id, Finset.mem_univ, iff_true]
    have hfull : i ∈ maskFin (s.foldl (fun x y => x ||| y) 0) := by
      rw [hU, maskFin_full]
      exact Finset.mem_univ _
    rcases (mem_maskFin_foldl_or s 0 i).1 hfull with h0 | ⟨x, hx, hix⟩
    · rw [maskFin_zero] at h0
      simp at h0
    · exact ⟨maskFin x, mem_sextOfL.2 ⟨x, hx, rfl⟩, hix⟩
  · intro B hB B' hB' hne
    obtain ⟨x, hx, rfl⟩ := mem_sextOfL.1 hB
    obtain ⟨y, hy, rfl⟩ := mem_sextOfL.1 hB'
    rcases hpair x hx y hy with h | ⟨-, h⟩
    · exact absurd (by rw [h]) hne
    · rw [← maskFin_or]
      exact h

theorem maskFin_tetrad (a b c : Fin 24) :
    maskFin (1 ||| (1 <<< (a : ℕ)) ||| (1 <<< (b : ℕ)) ||| (1 <<< (c : ℕ))) = {0, a, b, c} := by
  ext i
  simp only [mem_maskFin, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow,
    Nat.testBit_one_eq_true_iff_self_eq_zero, Bool.or_eq_true, decide_eq_true_eq,
    Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, Fin.val_zero]
  omega

theorem mem_tetrads0 {a b c : ℕ} (ha : 0 < a) (hab : a < b) (hbc : b < c) (hc : c < 24) :
    (1 ||| (1 <<< a) ||| (1 <<< b) ||| (1 <<< c)) ∈ Native.tetrads0 () := by
  unfold Native.tetrads0
  simp only [List.mem_flatMap, List.mem_filterMap, List.mem_range]
  refine ⟨a, by omega, b, by omega, c, hc, ?_⟩
  simp [ha, hab, hbc]

theorem exists_tetrad0 {B : Finset (Fin 24)} (hB : B.card = 4) (h0 : (0 : Fin 24) ∈ B) :
    ∃ t ∈ Native.tetrads0 (), t < 2 ^ 24 ∧ maskFin t = B := by
  set f := B.orderEmbOfFin hB with hf
  have hf0 : f 0 = 0 := by
    have hmem : (0 : Fin 24) ∈ Set.range f := by
      rw [hf, Finset.range_orderEmbOfFin]
      exact h0
    obtain ⟨i, hi⟩ := hmem
    have h1 : f 0 ≤ f i := f.monotone (Fin.zero_le i)
    rw [hi] at h1
    exact le_antisymm h1 (Fin.zero_le _)
  have h01 : f 0 < f 1 := f.strictMono (by decide)
  have h12 : f 1 < f 2 := f.strictMono (by decide)
  have h23 : f 2 < f 3 := f.strictMono (by decide)
  have hBeq : B = {0, f 1, f 2, f 3} := by
    rw [← hf0]
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hx
      have hx' : x ∈ Set.range f := by
        rw [hf, Finset.range_orderEmbOfFin]
        exact hx
      obtain ⟨i, rfl⟩ := hx'
      fin_cases i <;> simp
    · rintro (rfl | rfl | rfl | rfl) <;> exact Finset.orderEmbOfFin_mem B hB _
  rw [hf0] at h01
  have h01' : 0 < (f 1 : ℕ) := by
    have h := Fin.lt_def.1 h01
    rwa [Fin.val_zero] at h
  have h12' : (f 1 : ℕ) < f 2 := h12
  have h23' : (f 2 : ℕ) < f 3 := h23
  have hc : (f 3 : ℕ) < 24 := (f 3).2
  refine ⟨_, mem_tetrads0 h01' h12' h23' hc, ?_, ?_⟩
  · refine Nat.or_lt_two_pow (Nat.or_lt_two_pow (Nat.or_lt_two_pow (by norm_num) ?_) ?_) ?_ <;>
      rw [Nat.one_shiftLeft] <;> exact Nat.pow_lt_pow_right (by norm_num) (Fin.is_lt _)
  · rw [maskFin_tetrad, ← hBeq]

theorem card_octads_containing {B : Finset (Fin 24)} (hB : B.card = 4) :
    (CFSG.Monster.Code.octads.filter (fun O => B ⊆ O)).card = 5 := by
  have h := CFSG.Monster.Code.card_octads_superset B (by omega)
  rw [hB] at h
  norm_num [Nat.choose] at h
  omega

theorem exists_union_of_octad {S : Finset (Finset (Fin 24))} (hS : IsSextet S)
    {B : Finset (Fin 24)} (hBS : B ∈ S) {O : Finset (Fin 24)} (hO : IsOctad O) (hBO : B ⊆ O) :
    ∃ B' ∈ S, B' ≠ B ∧ O = B ∪ B' := by
  have hcard := card_octads_containing (hS.2.1 B hBS)
  have key : ∀ {X Y : Finset (Fin 24)}, Disjoint X B → B ∪ X = B ∪ Y → X ⊆ Y := by
    intro X Y hXB h x hx
    have hx' : x ∈ B ∪ Y := by
      rw [← h]
      exact Finset.mem_union_right _ hx
    rcases Finset.mem_union.1 hx' with hxB | hxY
    · exact absurd hxB (Finset.disjoint_left.1 hXB hx)
    · exact hxY
  have hdisj : ∀ {X : Finset (Fin 24)}, X ∈ S.erase B → Disjoint X B := fun {X} hX =>
    hS.2.2.1 X (Finset.mem_of_mem_erase hX) B hBS (Finset.ne_of_mem_erase hX)
  have hFsub : (S.erase B).image (fun B' => B ∪ B') ⊆
      CFSG.Monster.Code.octads.filter (fun O => B ⊆ O) := by
    intro O' hO'
    obtain ⟨B', hB', rfl⟩ := Finset.mem_image.1 hO'
    rw [Finset.mem_filter]
    exact ⟨CFSG.ASVolI.AppH.isOctad_iff_mem_octads.1
      (hS.2.2.2.2 B hBS B' (Finset.mem_of_mem_erase hB') (Finset.ne_of_mem_erase hB').symm),
      Finset.subset_union_left⟩
  have hFcard : ((S.erase B).image (fun B' => B ∪ B')).card = 5 := by
    rw [Finset.card_image_of_injOn, Finset.card_erase_of_mem hBS, hS.1]
    intro B₁ h₁ B₂ h₂ h
    exact Finset.Subset.antisymm (key (hdisj (Finset.mem_coe.1 h₁)) h)
      (key (hdisj (Finset.mem_coe.1 h₂)) h.symm)
  have hFeq := Finset.eq_of_subset_of_card_le hFsub (by rw [hcard, hFcard])
  have hOmem : O ∈ CFSG.Monster.Code.octads.filter (fun O => B ⊆ O) :=
    Finset.mem_filter.2 ⟨CFSG.ASVolI.AppH.isOctad_iff_mem_octads.1 hO, hBO⟩
  rw [← hFeq] at hOmem
  obtain ⟨B', hB', rfl⟩ := Finset.mem_image.1 hOmem
  exact ⟨B', Finset.mem_of_mem_erase hB', Finset.ne_of_mem_erase hB', rfl⟩

theorem and_eq_iff_subset {o t : ℕ} (ht : t < 2 ^ 24) :
    o &&& t = t ↔ maskFin t ⊆ maskFin o := by
  constructor
  · intro h
    have h1 : maskFin t = maskFin o ∩ maskFin t := by rw [← maskFin_and, h]
    rw [h1]
    exact Finset.inter_subset_left
  · intro h
    apply maskFin_inj (Nat.and_lt_two_pow _ ht) ht
    rw [maskFin_and]
    exact Finset.inter_eq_right.2 h

theorem Native.allLt_iff {n : ℕ} {p : ℕ → Bool} :
    Native.allLt n p = true ↔ ∀ i < n, p i = true := by
  unfold Native.allLt
  rw [List.all_eq_true]
  simp [List.mem_range]

section Cert


theorem octCheck_true : Native.octCheck () = true := by
  have h : Native.listChecks () = true := Certificates.certificate89011
  simp only [Native.listChecks, Bool.and_eq_true] at h
  exact h.1.1

theorem trioCheck_true : Native.trioCheck () = true := by
  have h : Native.listChecks () = true := Certificates.certificate89011
  simp only [Native.listChecks, Bool.and_eq_true] at h
  exact h.1.2

theorem sextCheck_true : Native.sextCheck () = true := by
  have h : Native.listChecks () = true := Certificates.certificate89011
  simp only [Native.listChecks, Bool.and_eq_true] at h
  exact h.2

theorem octList_get {i : ℕ} (hi : i < 759) {o : ℕ} (ho : (Native.octList ())[i]! = o) :
    o < 2 ^ 24 ∧ Native.pop o = 8 ∧ Native.synd o = 0 ∧ Native.octIdx o = i := by
  subst ho
  have h := octCheck_true
  simp only [Native.octCheck, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Native.allLt_iff,
    List.all_eq_true, and_assoc] at h
  obtain ⟨-, -, hall, -⟩ := h
  obtain ⟨h1, h2, h3, h4, -⟩ := hall i hi
  exact ⟨h1, h2, h3, h4⟩

theorem trioList_get {p : ℕ} (hp : p < 3795) {t : ℕ × ℕ × ℕ}
    (ht : (Native.trioList ())[p]! = t) :
    t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧ Native.octIdx t.1 < 759 ∧ Native.octIdx t.2.1 < 759 ∧
      Native.octIdx t.2.2 < 759 ∧ t.1 &&& t.2.1 = 0 ∧ t.1 &&& t.2.2 = 0 ∧ t.2.1 &&& t.2.2 = 0 ∧
      t.1 ||| t.2.1 ||| t.2.2 = Native.full ∧ Native.trioIdx t = p := by
  subst ht
  have h := trioCheck_true
  simp only [Native.trioCheck, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Native.allLt_iff,
    List.all_eq_true, and_assoc, bne_iff_ne, ne_eq, Bool.or_eq_true] at h
  obtain ⟨-, -, hall, -, -⟩ := h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, -⟩ := hall p hp
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

theorem trioIdx_lt_of_octads {i j : ℕ} (hi : i < 759) (hj : j < 759) {a b : ℕ}
    (ha : (Native.octList ())[i]! = a) (hb : (Native.octList ())[j]! = b) (hab : a &&& b = 0)
    (hne : a ≠ b) : Native.trioIdx (Native.sort3 a b (Native.full ^^^ a ^^^ b)) < 3795 := by
  subst ha hb
  have h := trioCheck_true
  simp only [Native.trioCheck, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Native.allLt_iff,
    List.all_eq_true, and_assoc, bne_iff_ne, ne_eq, Bool.or_eq_true] at h
  obtain ⟨-, -, -, -, hcomp⟩ := h
  rcases hcomp i hi j hj with (h1 | h1) | h1
  · exact absurd hab h1
  · exact absurd h1 hne
  · exact h1

theorem sextList_get {q : ℕ} (hq : q < 1771) {s : List ℕ} (hs : (Native.sextList ())[q]! = s) :
    s.length = 6 ∧ s.Pairwise (· < ·) ∧ (∀ x ∈ s, Native.pop x = 4 ∧ x < 2 ^ 24) ∧
      s.foldl (fun x y => x ||| y) 0 = Native.full ∧
      (∀ x ∈ s, ∀ y ∈ s, x = y ∨ x &&& y = 0 ∧ Native.octIdx (x ||| y) < 759) ∧
      Native.sextIdx s = q := by
  subst hs
  have h := sextCheck_true
  simp only [Native.sextCheck, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Native.allLt_iff,
    List.all_eq_true, and_assoc, bne_iff_ne, ne_eq, Bool.or_eq_true] at h
  obtain ⟨-, -, hall, -, -⟩ := h
  obtain ⟨h1, -, h3, h4, h5, h6, h7, -⟩ := hall q hq
  exact ⟨h1, h3, h4, h5, h6, h7⟩

theorem sextIdx_sextOf_lt {t : ℕ} (ht : t ∈ Native.tetrads0 ()) :
    Native.sextIdx (Native.sextOf t) < 1771 := by
  have h := sextCheck_true
  simp only [Native.sextCheck, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Native.allLt_iff,
    List.all_eq_true, and_assoc, bne_iff_ne, ne_eq, Bool.or_eq_true] at h
  obtain ⟨-, -, -, -, htet⟩ := h
  exact (htet t ht).2

theorem octIdx_img_lt {i : ℕ} (hi : i < 759) {g : Array ℕ} (hg : g ∈ Native.genTabs) :
    Native.octIdx (Native.img g (Native.octList ())[i]!) < 759 := by
  have h := octCheck_true
  simp only [Native.octCheck, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Native.allLt_iff,
    List.all_eq_true, and_assoc] at h
  obtain ⟨-, -, hall, -⟩ := h
  obtain ⟨-, -, -, -, hgen⟩ := hall i hi
  exact hgen g hg

theorem trioIdx_imgTrio_lt {p : ℕ} (hp : p < 3795) {g : Array ℕ} (hg : g ∈ Native.genTabs) :
    Native.trioIdx (Native.imgTrio g (Native.trioList ())[p]!) < 3795 := by
  have h := trioCheck_true
  simp only [Native.trioCheck, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Native.allLt_iff,
    List.all_eq_true, and_assoc, bne_iff_ne, ne_eq, Bool.or_eq_true] at h
  obtain ⟨-, -, hall, -, -⟩ := h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hgen⟩ := hall p hp
  exact hgen g hg

theorem sextIdx_imgSext_lt {q : ℕ} (hq : q < 1771) {g : Array ℕ} (hg : g ∈ Native.genTabs) :
    Native.sextIdx (Native.imgSext g (Native.sextList ())[q]!) < 1771 := by
  have h := sextCheck_true
  simp only [Native.sextCheck, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Native.allLt_iff,
    List.all_eq_true, and_assoc, bne_iff_ne, ne_eq, Bool.or_eq_true] at h
  obtain ⟨-, -, hall, -, -⟩ := h
  obtain ⟨-, -, -, -, -, -, -, hgen⟩ := hall q hq
  exact hgen g hg

theorem isOctad_octFin {i : ℕ} (hi : i < 759) : IsOctad (octFin i) := by
  obtain ⟨h1, h2, h3, -⟩ := octList_get hi rfl
  exact ⟨by rw [octFin, card_maskFin, h2], by rw [octFin, eY_maskFin_mem_golayC h1, h3]⟩

theorem octFin_injective {i j : ℕ} (hi : i < 759) (hj : j < 759) (h : octFin i = octFin j) :
    i = j := by
  obtain ⟨hi1, -, -, hi4⟩ := octList_get hi rfl
  obtain ⟨hj1, -, -, hj4⟩ := octList_get hj rfl
  have e := maskFin_inj hi1 hj1 h
  rw [← hi4, ← hj4, e]

theorem isOctad_iff (O : Finset (Fin 24)) : IsOctad O ↔ ∃ i < 759, octFin i = O := by
  constructor
  · intro hO
    have hS : (Finset.range 759).image octFin = CFSG.Monster.Code.octads := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
        exact CFSG.ASVolI.AppH.isOctad_iff_mem_octads.1 (isOctad_octFin (Finset.mem_range.1 hi))
      · rw [CFSG.Monster.Code.card_octads, Finset.card_image_of_injOn, Finset.card_range]
        intro i hi j hj h
        exact octFin_injective (by simpa using hi) (by simpa using hj) h
    have hmem : O ∈ (Finset.range 759).image octFin := by
      rw [hS]
      exact CFSG.ASVolI.AppH.isOctad_iff_mem_octads.1 hO
    obtain ⟨i, hi, hiO⟩ := Finset.mem_image.1 hmem
    exact ⟨i, Finset.mem_range.1 hi, hiO⟩
  · rintro ⟨i, hi, rfl⟩
    exact isOctad_octFin hi

theorem isOctad_maskFin_of_octIdx {m : ℕ} (h : Native.octIdx m < 759) :
    IsOctad (maskFin m) ∧ m < 2 ^ 24 := by
  have e := octList_octIdx h
  refine ⟨?_, ?_⟩
  · have := isOctad_octFin h
    rwa [octFin, e] at this
  · have := (octList_get h rfl).1
    rwa [e] at this

theorem isTrio_trioFin {p : ℕ} (hp : p < 3795) : IsTrio (trioFin p) := by
  obtain ⟨-, -, h3, h4, h5, h6, h7, h8, h9, -⟩ := trioList_get hp rfl
  exact isTrio_trioOf (isOctad_maskFin_of_octIdx h3).1 (isOctad_maskFin_of_octIdx h4).1
    (isOctad_maskFin_of_octIdx h5).1 h6 h7 h8 h9

theorem trioFin_injective {p p' : ℕ} (hp : p < 3795) (hp' : p' < 3795)
    (h : trioFin p = trioFin p') : p = p' := by
  obtain ⟨a1, a2, -, -, a5, -, -, -, -, a10⟩ := trioList_get hp rfl
  obtain ⟨b1, b2, -, -, b5, -, -, -, -, b10⟩ := trioList_get hp' rfl
  have c3 := (isOctad_maskFin_of_octIdx a5).2
  have d3 := (isOctad_maskFin_of_octIdx b5).2
  have e : (Native.trioList ())[p]! = (Native.trioList ())[p']! := by
    have := trioOf_inj a1 a2 c3 b1 b2 d3 (by simpa only [trioFin] using h)
    simpa only [Prod.mk.injEq, Prod.ext_iff] using this
  rw [← a10, ← b10, e]

theorem isTrio_iff (T : Finset (Finset (Fin 24))) : IsTrio T ↔ ∃ p < 3795, trioFin p = T := by
  constructor
  · intro hT
    obtain ⟨A, hA, B, hB, hAB⟩ := Finset.one_lt_card.1 (by rw [hT.1]; norm_num : 1 < T.card)
    obtain ⟨i, hi, rfl⟩ := (isOctad_iff A).1 (hT.2.1 A hA)
    obtain ⟨j, hj, rfl⟩ := (isOctad_iff B).1 (hT.2.1 B hB)
    obtain ⟨hj1, -, -, -⟩ := octList_get hj rfl
    have hdisj := hT.2.2.1 _ hA _ hB hAB
    have hab : (Native.octList ())[i]! &&& (Native.octList ())[j]! = 0 :=
      (maskFin_eq_empty (Nat.and_lt_two_pow _ hj1)).1 ((disjoint_maskFin _ _).1 hdisj)
    have hne : (Native.octList ())[i]! ≠ (Native.octList ())[j]! := fun h => hAB (by
      rw [octFin, octFin, h])
    have hlt := trioIdx_lt_of_octads hi hj rfl rfl hab hne
    refine ⟨_, hlt, ?_⟩
    rw [trioOf_trioIdx hlt, trioOf_sort3, trio_eq_of_mem hT hA hB hAB,
      maskFin_full_xor hdisj]
    rfl
  · rintro ⟨p, hp, rfl⟩
    exact isTrio_trioFin hp

theorem isSextet_sextFin {q : ℕ} (hq : q < 1771) : IsSextet (sextFin q) := by
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := sextList_get hq rfl
  refine isSextet_sextOfL h1 h2 h3 h4 fun x hx y hy => ?_
  rcases h5 x hx y hy with h | ⟨h, h'⟩
  · exact Or.inl h
  · exact Or.inr ⟨h, (isOctad_maskFin_of_octIdx h').1⟩

theorem sextFin_injective {q q' : ℕ} (hq : q < 1771) (hq' : q' < 1771)
    (h : sextFin q = sextFin q') : q = q' := by
  obtain ⟨-, h2, h3, -, -, h6⟩ := sextList_get hq rfl
  obtain ⟨-, h2', h3', -, -, h6'⟩ := sextList_get hq' rfl
  have e : (Native.sextList ())[q]! = (Native.sextList ())[q']! := by
    apply List.Pairwise.eq_of_mem_iff h2 h2'
    intro x
    constructor
    · intro hx
      have hm : maskFin x ∈ sextFin q' := by
        rw [← h]
        exact mem_sextOfL.2 ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hxy⟩ := mem_sextOfL.1 hm
      rw [← maskFin_inj (h3' y hy).2 (h3 x hx).2 hxy]
      exact hy
    · intro hx
      have hm : maskFin x ∈ sextFin q := by
        rw [h]
        exact mem_sextOfL.2 ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hxy⟩ := mem_sextOfL.1 hm
      rw [← maskFin_inj (h3 y hy).2 (h3' x hx).2 hxy]
      exact hy
  rw [← h6, ← h6', e]

theorem octList_size : (Native.octList ()).size = 759 := by
  have h := octCheck_true
  simp only [Native.octCheck, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Native.allLt_iff,
    List.all_eq_true, and_assoc] at h
  exact h.1

theorem mem_octList_toList {o : ℕ} :
    o ∈ (Native.octList ()).toList ↔ ∃ i < 759, (Native.octList ())[i]! = o := by
  rw [Array.mem_toList_iff, Array.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, rfl⟩
    refine ⟨i, by rwa [octList_size] at hi, ?_⟩
    simp [getElem!_pos, hi]
  · rintro ⟨i, hi, rfl⟩
    have hi' : i < (Native.octList ()).size := by
      rw [octList_size]
      exact hi
    exact ⟨i, hi', by simp [getElem!_pos, hi']⟩

theorem mem_sextOfL_sextOf {t : ℕ} (ht : t < 2 ^ 24) {X : Finset (Fin 24)} :
    X ∈ sextOfL (Native.sextOf t) ↔
      X = maskFin t ∨ ∃ O, IsOctad O ∧ maskFin t ⊆ O ∧ X = O \ maskFin t := by
  rw [mem_sextOfL]
  simp only [Native.sextOf, mem_sortL, List.mem_cons, List.mem_map, List.mem_filter,
    mem_octList_toList, beq_iff_eq]
  constructor
  · rintro ⟨y, rfl | ⟨o, ⟨⟨i, hi, rfl⟩, ho⟩, rfl⟩, rfl⟩
    · exact Or.inl rfl
    · have hsub := (and_eq_iff_subset ht).1 ho
      exact Or.inr ⟨octFin i, isOctad_octFin hi, hsub, by
        rw [maskFin_xor, symmDiff_of_ge hsub]; rfl⟩
  · rintro (rfl | ⟨O, hO, hsub, rfl⟩)
    · exact ⟨t, Or.inl rfl, rfl⟩
    · obtain ⟨i, hi, rfl⟩ := (isOctad_iff O).1 hO
      have hsub' : maskFin t ⊆ maskFin (Native.octList ())[i]! := hsub
      refine ⟨_, Or.inr ⟨(Native.octList ())[i]!, ⟨⟨i, hi, rfl⟩,
        (and_eq_iff_subset ht).2 hsub'⟩, rfl⟩, ?_⟩
      rw [maskFin_xor, symmDiff_of_ge hsub']
      rfl

theorem isSextet_iff (S : Finset (Finset (Fin 24))) : IsSextet S ↔ ∃ q < 1771, sextFin q = S := by
  constructor
  · intro hS
    have h0 : (0 : Fin 24) ∈ S.biUnion id := by
      rw [hS.2.2.2.1]
      exact Finset.mem_univ _
    obtain ⟨B, hBS, h0B⟩ := Finset.mem_biUnion.1 h0
    obtain ⟨t, htet, ht24, htB⟩ := exists_tetrad0 (hS.2.1 B hBS) h0B
    have hidx := sextIdx_sextOf_lt htet
    refine ⟨_, hidx, ?_⟩
    rw [sextOfL_sextIdx hidx]
    ext X
    rw [mem_sextOfL_sextOf ht24, htB]
    constructor
    · rintro (rfl | ⟨O, hO, hsub, rfl⟩)
      · exact hBS
      · obtain ⟨B', hB'S, hne, rfl⟩ := exists_union_of_octad hS hBS hO hsub
        rw [Finset.union_sdiff_cancel_left (hS.2.2.1 B hBS B' hB'S hne.symm)]
        exact hB'S
    · intro hX
      by_cases hXB : X = B
      · exact Or.inl hXB
      · refine Or.inr ⟨B ∪ X, hS.2.2.2.2 B hBS X hX (Ne.symm hXB), Finset.subset_union_left, ?_⟩
        rw [Finset.union_sdiff_cancel_left (hS.2.2.1 B hBS X hX (Ne.symm hXB))]
  · rintro ⟨q, hq, rfl⟩
    exact isSextet_sextFin hq

end Cert

end CFSG.Quasithin.H13.AS91.M24G
