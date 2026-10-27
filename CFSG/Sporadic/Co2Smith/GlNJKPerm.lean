module

public import CFSG.Sporadic.Co2Smith.GlNJPts
public import CFSG.Sporadic.Co2Smith.GlNJAut
public import CFSG.Sporadic.Co2Smith.GlWChart
public import CFSG.Sporadic.Co2Smith.GlC0MarkFix
public import CFSG.Sporadic.Co2Smith.GlNJPerm

public section

namespace CFSG.Sporadic.Co2Smith

open Subgroup CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

section Tab

theorem conj_jcFold_of_tab {g : K} {R : Array ℕ} (hg : g.val.val = rowsMatrix 22 R)
    {tab : List ℕ} (h : Native.glWTabOK R tab = true) (m : ℕ) :
    ∀ l : List ℕ, (∀ i ∈ l, i < 10) → g * jcFold m l * g⁻¹ =
      jcElt (l.foldr (fun i acc => if m.testBit i then tab[i]! ^^^ acc else acc) 0)
  | [], _ => by simp [jcFold, jcElt_zero]
  | i :: l, hl => by
    have hi : i < 10 := hl i List.mem_cons_self
    have ih := conj_jcFold_of_tab hg h m l fun j hj => hl j (List.mem_cons_of_mem _ hj)
    have hB : g * jcB i * g⁻¹ = jcElt tab[i]! := by
      obtain ⟨-, he⟩ := glWTab_spec h i hi
      have e : g * jcB i = jcElt tab[i]! * g :=
        eq_of_rows (val_mul_rows hg (jcB_val hi)) (val_mul_rows (jcElt_val _) hg) he
      rw [e, mul_inv_cancel_right]
    have e1 : jcFold m (i :: l) = if m.testBit i then jcB i * jcFold m l else jcFold m l := rfl
    rw [e1, List.foldr_cons]
    split_ifs
    · rw [jcElt_xor, ← ih, ← hB]
      group
    · exact ih

theorem conj_jcElt_of_tab {g : K} {R : Array ℕ} (hg : g.val.val = rowsMatrix 22 R)
    {tab : List ℕ} (h : Native.glWTabOK R tab = true) (m : ℕ) :
    g * jcElt m * g⁻¹ =
      jcElt ((List.range 10).foldr (fun i acc => if m.testBit i then tab[i]! ^^^ acc else acc) 0) :=
  conj_jcFold_of_tab hg h m (List.range 10) fun _ hi => List.mem_range.1 hi

end Tab

section Gen

@[expose] noncomputable def qK (k : ℕ) : K := glE Native.glNJGw[k]!

@[expose] noncomputable def qtK (k : ℕ) : K := jcElt Native.glNJTw[k]! * qK k

theorem qK_val {k : ℕ} (hk : k < 3) : (qK k).val.val = rowsMatrix 22 (Native.glNJG k) :=
  glE_val (glNJGen_spec.1 k hk)

theorem qtK_val {k : ℕ} (hk : k < 3) : (qtK k).val.val = rowsMatrix 22 (Native.glNJGt k) :=
  val_mul_rows (jcElt_val _) (qK_val hk)

theorem qK_conj {k : ℕ} (hk : k < 3) (m : ℕ) :
    qK k * jcElt m * (qK k)⁻¹ = jcElt (Native.glNJT k m) :=
  conj_jcElt_of_tab (qK_val hk) (glNJGen_spec.2.2.2.2 k hk).1 m

theorem qK_mem_N {k : ℕ} (hk : k < 3) : qK k ∈ normalizer (Jc : Set K) :=
  mem_normalizer_of_tab (qK_val hk) (glNJGen_spec.2.2.2.2 k hk).1

theorem qtK_mem_N {k : ℕ} (hk : k < 3) : qtK k ∈ normalizer (Jc : Set K) :=
  mem_normalizer_of_tab (qtK_val hk) (glNJGen_spec.2.2.2.2 k hk).2

theorem qK_comm_z0 {k : ℕ} (hk : k < 2) : qK k * z0 = z0 * qK k := by
  refine comm_of_commRows (qK_val (by omega)) z0_val' ?_
  rcases Nat.lt_succ_iff_lt_or_eq.1 hk with h | rfl
  · rw [Nat.lt_one_iff.1 h]
    exact glNJGen_spec.2.2.1
  · exact glNJGen_spec.2.2.2.1

theorem qK_mem_Cz {k : ℕ} (hk : k < 2) : qK k ∈ Cz := mem_Cz_of_comm (qK_comm_z0 hk)

end Gen

section Om

@[expose] noncomputable def omK (k : Fin 77) : K := jcElt Native.glNJOm[(k : ℕ)]!

theorem jcElt_inj {a b : ℕ} (ha : a < 1024) (hb : b < 1024) (h : jcElt a = jcElt b) : a = b := by
  have h1 : jcElt (a ^^^ b) = 1 := by rw [jcElt_xor, h, jcElt_mul_self]
  have h0 := jcElt_fix_ptP (Nat.xor_lt_two_pow (n := 10) ha hb) (by rw [h1, map_one]; rfl)
  have e := congrArg (· ^^^ b) h0
  simpa [Nat.xor_assoc] using e

theorem glNJOm_lt (k : Fin 77) : Native.glNJOm[(k : ℕ)]! < 1024 :=
  (glNJOm_spec.2.1 k k.2).2

theorem omK_injective : Function.Injective omK := by
  intro a b h
  exact Fin.ext (glNJOm_spec.2.2.2.1 a a.2 b b.2 (jcElt_inj (glNJOm_lt a) (glNJOm_lt b) h))

theorem omK_zero : omK 0 = z0 := by
  rw [omK, show ((0 : Fin 77) : ℕ) = 0 from rfl, glNJOm_spec.2.2.1,
    show (1 : ℕ) = 2 ^ 0 from rfl, jcElt_two_pow (by norm_num), jcB_zero]

theorem jcElt_mem_range_omK {z : ℕ} (hz : z < 1024) :
    jcElt z ∈ Set.range omK ↔ z ∈ Native.glNJOm := by
  constructor
  · rintro ⟨k, hk⟩
    rw [← jcElt_inj (glNJOm_lt k) hz hk]
    exact list_getElem!_mem (by rw [glNJOm_spec.1]; exact k.2)
  · intro h
    obtain ⟨k, hk, e⟩ := List.getElem_of_mem h
    refine ⟨⟨k, by rw [← glNJOm_spec.1]; exact hk⟩, ?_⟩
    rw [omK, getElem!_pos _ k hk, e]

theorem omK_mem_Jc (k : Fin 77) : omK k ∈ Jc := jcElt_mem _

theorem qK_conj_omK {i : ℕ} (hi : i < 3) (k : Fin 77) :
    qK i * omK k * (qK i)⁻¹ =
      omK ⟨(Native.glNJPerm[i]!)[(k : ℕ)]!, ((glNJOm_spec.2.2.2.2.2.1 i hi).2 k k.2).1⟩ := by
  have e := ((glNJOm_spec.2.2.2.2.2.1 i hi).2 k k.2).2
  show qK i * jcElt _ * (qK i)⁻¹ = jcElt Native.glNJOm[(Native.glNJPerm[i]!)[(k : ℕ)]!]!
  rw [qK_conj hi, e]

@[expose] noncomputable def wordK (w : List ℕ) : K := (w.map qK).prod

theorem glNJWordP_lt {w : List ℕ} (hw : ∀ i ∈ w, i < 3) {j : ℕ} (hj : j < 77) :
    (Native.glNJWordP w)[j]! < 77 := by
  induction w with
  | nil =>
    rw [Native.glNJWordP, List.foldr_nil, idA_get hj]
    exact hj
  | cons i w ih =>
    have hi := hw i List.mem_cons_self
    have ih' := ih fun l hl => hw l (List.mem_cons_of_mem _ hl)
    have e : Native.glNJWordP (i :: w) = compA 77 Native.glNJPerm[i]! (Native.glNJWordP w) := rfl
    rw [e, compA_get hj]
    exact ((glNJOm_spec.2.2.2.2.2.1 i hi).2 _ ih').1

theorem qK_conj_omN {i : ℕ} (hi : i < 3) {j : ℕ} (hj : j < 77) :
    qK i * jcElt Native.glNJOm[j]! * (qK i)⁻¹ =
      jcElt Native.glNJOm[(Native.glNJPerm[i]!)[j]!]! := by
  rw [qK_conj hi, ((glNJOm_spec.2.2.2.2.2.1 i hi).2 j hj).2]

theorem wordK_conj_omN {w : List ℕ} (hw : ∀ i ∈ w, i < 3) {j : ℕ} (hj : j < 77) :
    wordK w * jcElt Native.glNJOm[j]! * (wordK w)⁻¹ =
      jcElt Native.glNJOm[(Native.glNJWordP w)[j]!]! := by
  induction w with
  | nil =>
    rw [show Native.glNJWordP [] = idA 77 from rfl, idA_get hj]
    simp [wordK]
  | cons i w ih =>
    have hi := hw i List.mem_cons_self
    have hw' : ∀ l ∈ w, l < 3 := fun l hl => hw l (List.mem_cons_of_mem _ hl)
    have e : wordK (i :: w) = qK i * wordK w := by
      rw [wordK, List.map_cons, List.prod_cons]
      rfl
    have e2 : Native.glNJWordP (i :: w) = compA 77 Native.glNJPerm[i]! (Native.glNJWordP w) := rfl
    calc wordK (i :: w) * jcElt Native.glNJOm[j]! * (wordK (i :: w))⁻¹ =
        qK i * (wordK w * jcElt Native.glNJOm[j]! * (wordK w)⁻¹) * (qK i)⁻¹ := by
          rw [e]; group
      _ = qK i * jcElt Native.glNJOm[(Native.glNJWordP w)[j]!]! * (qK i)⁻¹ := by rw [ih hw']
      _ = jcElt Native.glNJOm[(Native.glNJWordP (i :: w))[j]!]! := by
          rw [qK_conj_omN hi (glNJWordP_lt hw' hj), e2, compA_get hj]

theorem omK_conj_z0 (k : Fin 77) :
    wordK Native.glNJConj[(k : ℕ)]! * z0 * (wordK Native.glNJConj[(k : ℕ)]!)⁻¹ = omK k := by
  have h := wordK_conj_omN (glNJOm_spec.2.2.2.2.2.2.1 k k.2).1 (j := 0) (by norm_num)
  rw [glNJOm_spec.2.2.2.2.2.2.1 k k.2 |>.2] at h
  rw [← omK_zero]
  exact h

theorem wordK_mem {w : List ℕ} {S : Subgroup K} (hS : ∀ i ∈ w, qK i ∈ S) : wordK w ∈ S := by
  induction w with
  | nil => exact S.one_mem
  | cons i w ih =>
    rw [wordK, List.map_cons, List.prod_cons]
    exact S.mul_mem (hS i List.mem_cons_self) (ih fun j hj => hS j (List.mem_cons_of_mem _ hj))

end Om

section Perm

theorem exists_omK_of_isConj {y : K} (hy : y ∈ Jc) (hc : IsConj z0 y) : ∃ k, omK k = y := by
  obtain ⟨m, hm, rfl⟩ := exists_coord hy
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [jcElt_zero] at hc
    have h1 : omK 0 = jcElt 0 := by rw [omK_zero, jcElt_zero]; exact isConj_one_right.1 hc.symm
    exact (glNJOm_spec.2.1 0 (by norm_num)).1.ne'
      (jcElt_inj (glNJOm_lt 0) (by norm_num) h1)
  have hmOm : m ∈ Native.glNJOm := by
    by_contra hn
    apply glNJFix_spec hm hm0 hn
    rw [← fixK_eq_glNJFixR (jcElt_val m), ← fixK_eq_of_isConj hc, fixK_z0]
  exact (jcElt_mem_range_omK hm).2 hmOm

theorem stable_normalizer : ∀ g ∈ normalizer (Jc : Set K), ConjStable omK g := by
  intro g hg k
  have hmem : g * omK k * g⁻¹ ∈ Jc := (mem_normalizer_iff.1 hg _).1 (omK_mem_Jc k)
  have hc : IsConj z0 (g * omK k * g⁻¹) := by
    rw [← omK_conj_z0 k]
    exact (isConj_iff.2 ⟨_, rfl⟩).trans (isConj_iff.2 ⟨g, rfl⟩)
  obtain ⟨k', hk'⟩ := exists_omK_of_isConj hmem hc
  exact ⟨k', hk'.symm⟩

@[expose] noncomputable def piK : normalizer (Jc : Set K) →* Equiv.Perm (Fin 77) :=
  chom omK_injective (normalizer (Jc : Set K)) stable_normalizer

theorem piK_spec (g : normalizer (Jc : Set K)) (k : Fin 77) :
    omK (piK g k) = g * omK k * (g : K)⁻¹ :=
  chom_spec omK_injective _ stable_normalizer g k

theorem Jc_le_closure_omK : Jc ≤ Subgroup.closure (Set.range omK) := by
  rw [Jc, closure_le]
  rintro _ ⟨i, rfl⟩
  have hspan := glNJOm_spec.2.2.2.2.2.2.2 i i.2
  have key : ∀ (l : List ℕ) (a : ℕ), (∀ k ∈ l, k < 77) →
      jcElt a ∈ Subgroup.closure (Set.range omK) →
        jcElt (l.foldl (fun acc k => acc ^^^ Native.glNJOm[k]!) a) ∈
          Subgroup.closure (Set.range omK) := by
    intro l
    induction l with
    | nil => intro a _ ha; exact ha
    | cons k l ih =>
      intro a hl ha
      rw [List.foldl_cons]
      refine ih _ (fun j hj => hl j (List.mem_cons_of_mem _ hj)) ?_
      rw [jcElt_xor]
      refine mul_mem ha (subset_closure ⟨⟨k, hl k List.mem_cons_self⟩, rfl⟩)
  have h := key _ 0 hspan.1 (by rw [jcElt_zero]; exact one_mem _)
  rw [hspan.2, jcElt_two_pow i.2] at h
  exact h

theorem mem_Jc_of_piK_eq_one {g : normalizer (Jc : Set K)} (h : piK g = 1) : (g : K) ∈ Jc := by
  have hc := (chom_eq_one_iff omK_injective _ stable_normalizer g).1 h
  apply centralizer_Jc_le
  have h1 : (g : K) ∈ centralizer (Set.range omK) := by
    refine mem_centralizer_iff.2 ?_
    rintro _ ⟨k, rfl⟩
    exact (hc k).symm
  rw [← centralizer_closure] at h1
  exact centralizer_le Jc_le_closure_omK h1

theorem cnt_omK_jcElt {c : ℕ} (hc : c < 1024) :
    cnt omK (jcElt c) = Native.glNJN Native.glNJOmT c := by
  have key : ∀ k : Fin 77, omK k * jcElt c ∈ Set.range omK ↔
      Native.glNJOmT[Native.glNJOm[(k : ℕ)]! ^^^ c]! = true := by
    intro k
    have hlt : Native.glNJOm[(k : ℕ)]! ^^^ c < 1024 :=
      Nat.xor_lt_two_pow (n := 10) (glNJOm_lt k) hc
    rw [omK, ← jcElt_xor, jcElt_mem_range_omK hlt, Native.glNJOmT,
      getElem!_pos (Array.ofFn (n := 1024) fun y => Native.glNJOm.contains y.val) _
        (by rw [Array.size_ofFn]; exact hlt), Array.getElem_ofFn]
    simp
  rw [cnt, Native.glNJN, ← Fintype.card_subtype, Fintype.card_eq_nat_card]
  exact Nat.card_congr (Equiv.subtypeEquivRight key)

theorem mem_glNJNbr_iff (x y : Fin 77) :
    (y : ℕ) ∈ Native.glNJNbr[(x : ℕ)]! ↔ adj omK x y := by
  rw [Native.glNJNbr, getElem!_pos _ _ (by rw [Array.size_ofFn]; exact x.2), Array.getElem_ofFn]
  simp only [List.mem_filter, List.mem_range, y.2, true_and, Bool.and_eq_true, bne_iff_ne,
    ne_eq, beq_iff_eq]
  unfold adj
  rw [omK, omK, ← jcElt_xor,
    cnt_omK_jcElt (Nat.xor_lt_two_pow (n := 10) (glNJOm_lt x) (glNJOm_lt y))]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun e => h1 (congrArg Fin.val e).symm, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun e => h1 (Fin.ext e.symm), h2⟩

theorem nbrInv_chom {S : Subgroup K} (hS : ∀ g ∈ S, ConjStable omK g) (g : S) :
    NbrInv Native.glNJNbr (chom omK_injective S hS g) := by
  intro x y
  rw [mem_glNJNbr_iff, mem_glNJNbr_iff, adj_chom omK_injective S hS g]

theorem piK_mem_njAut (g : normalizer (Jc : Set K)) : piK g ∈ njAut :=
  nbrInv_chom stable_normalizer g

end Perm

end CFSG.Sporadic.Co2Smith
