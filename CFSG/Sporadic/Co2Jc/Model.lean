module

public import CFSG.Sporadic.Co2Jc.Normalizer
public import CFSG.Sporadic.Co2Jc.Words
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co2Std.Exclusion.Facts

public section

namespace CFSG.Sporadic.Co2Jc

open CFSG.Sporadic.Co2Smith Subgroup
open CFSG.EvenSporadicStandard.Co2Std.Exclusion (conjN autImage)

section Coord


@[expose] noncomputable def jcA (m : ℕ) : ↥Jc := ⟨jcElt m, jcElt_mem m⟩

@[simp]
theorem coe_jcA (m : ℕ) : (jcA m : K) = jcElt m := rfl

theorem jcA_xor (a b : ℕ) : jcA (a ^^^ b) = jcA a * jcA b := by
  apply Subtype.ext
  rw [coe_jcA, Subgroup.coe_mul, coe_jcA, coe_jcA, jcElt_xor]

theorem jcA_zero : jcA 0 = 1 := Subtype.ext jcElt_zero

theorem exists_jcA (x : ↥Jc) : ∃ m < 1024, jcA m = x := by
  obtain ⟨m, hm, hx⟩ := exists_coord x.2
  exact ⟨m, hm, Subtype.ext hx⟩

private theorem finite_Jc : Finite ↥Jc :=
  Finite.of_surjective (fun m : Fin 1024 => jcA m) fun x => by
    obtain ⟨m, hm, hx⟩ := exists_jcA x
    exact ⟨⟨m, hm⟩, hx⟩

theorem jcA_inj {a b : ℕ}
    (ha : a < 1024) (hb : b < 1024) :
    jcA a = jcA b ↔ a = b := by
  constructor
  · intro h
    exact jcElt_inj ha hb (congrArg Subtype.val h)
  · rintro rfl
    rfl

theorem coe_jcA_one : (jcA 1 : K) = z0 := by
  rw [coe_jcA, show (1 : ℕ) = 2 ^ 0 from rfl, jcElt_two_pow (by norm_num), jcB_zero]

@[expose] noncomputable def coord (x : ↥Jc) : ℕ := Classical.choose (exists_jcA x)

theorem coord_lt (x : ↥Jc) : coord x < 1024 := (Classical.choose_spec (exists_jcA x)).1

@[simp]
theorem jcA_coord (x : ↥Jc) : jcA (coord x) = x := (Classical.choose_spec (exists_jcA x)).2

theorem coord_jcA {m : ℕ}
    (hm : m < 1024) : coord (jcA m) = m := by
  have h := jcA_coord (jcA m)
  exact (jcA_inj (coord_lt (jcA m)) hm).1 h

theorem coord_mul (x y : ↥Jc) :
    coord (x * y) = coord x ^^^ coord y := by
  refine (jcA_inj (coord_lt (x * y)) ?_).1 ?_
  · simpa using Nat.xor_lt_two_pow (n := 10) (coord_lt x) (coord_lt y)
  · rw [jcA_coord, jcA_xor, jcA_coord, jcA_coord]

theorem coord_one :
    coord 1 = 0 := by
  rw [← jcA_zero]
  exact coord_jcA (by norm_num)

private theorem mulAut_ext_jcB {f g : MulAut ↥Jc}
    (h : ∀ i < 10, f (jcA (2 ^ i)) = g (jcA (2 ^ i))) :
    ∀ (l : List ℕ) (m : ℕ) (hl : ∀ i ∈ l, i < 10),
      f ⟨jcFold m l, jcFold_mem m l hl⟩ = g ⟨jcFold m l, jcFold_mem m l hl⟩
  | [], m, hl => by
    have h1 : (⟨jcFold m [], jcFold_mem m [] hl⟩ : ↥Jc) = 1 := Subtype.ext rfl
    rw [h1, map_one, map_one]
  | i :: l, m, hl => by
    have hi : i < 10 := hl i List.mem_cons_self
    have hl' : ∀ j ∈ l, j < 10 := fun j hj => hl j (List.mem_cons_of_mem _ hj)
    have ih := mulAut_ext_jcB h l m hl'
    have hB : (⟨jcB i, jcB_mem hi⟩ : ↥Jc) = jcA (2 ^ i) := by
      apply Subtype.ext
      rw [coe_jcA, jcElt_two_pow hi]
    have hP : (⟨jcFold m (i :: l), jcFold_mem m (i :: l) hl⟩ : ↥Jc) =
        (if m.testBit i then
          (⟨jcB i, jcB_mem hi⟩ : ↥Jc) * ⟨jcFold m l, jcFold_mem m l hl'⟩
         else ⟨jcFold m l, jcFold_mem m l hl'⟩) := by
      by_cases hbit : m.testBit i
      · rw [if_pos hbit]
        apply Subtype.ext
        change jcFold m (i :: l) = jcB i * jcFold m l
        rw [show jcFold m (i :: l) =
          (if m.testBit i then jcB i * jcFold m l else jcFold m l) from rfl, if_pos hbit]
      · rw [if_neg hbit]
        apply Subtype.ext
        change jcFold m (i :: l) = jcFold m l
        rw [show jcFold m (i :: l) =
          (if m.testBit i then jcB i * jcFold m l else jcFold m l) from rfl, if_neg hbit]
    rw [hP]
    by_cases hbit : m.testBit i
    · rw [if_pos hbit, map_mul, map_mul, hB, h i hi, ih]
    · rw [if_neg hbit]
      exact ih

theorem mulAut_ext_basis {f g : MulAut ↥Jc} (h : ∀ i < 10, f (jcA (2 ^ i)) = g (jcA (2 ^ i))) :
    f = g := by
  refine MulEquiv.ext fun x => ?_
  obtain ⟨m, hm, hx⟩ := exists_jcA x
  rw [← hx]
  have key := mulAut_ext_jcB (f := f) (g := g) h (List.range 10) m
    (fun _ hi => List.mem_range.1 hi)
  have hx' : jcA m = (⟨jcFold m (List.range 10),
      jcFold_mem m (List.range 10) (fun _ hi => List.mem_range.1 hi)⟩ : ↥Jc) := by
    apply Subtype.ext
    exact jcElt_eq_jcFold m
  rw [hx']
  exact key

@[expose] noncomputable def tA : ↥Jc := jcA 1

theorem coe_tA : (tA : K) = z0 := coe_jcA_one

end Coord

section Gen


@[expose] noncomputable def qA (k : ℕ) : MulAut ↥Jc :=
  if hk : k < 3 then Jc.normalizerMonoidHom ⟨qK k, qK_mem_N hk⟩ else 1

theorem coe_qA_apply {k : ℕ} (hk : k < 3) (x : ↥Jc) :
    ((qA k x : ↥Jc) : K) = qK k * x * (qK k)⁻¹ := by
  rw [qA, dif_pos hk]
  rfl

theorem qA_jcA {k : ℕ} (hk : k < 3) (m : ℕ) :
    qA k (jcA m) = jcA (Native.glNJT k m) := by
  apply Subtype.ext
  rw [coe_qA_apply hk, coe_jcA, coe_jcA]
  exact qK_conj hk m

@[expose] noncomputable def qWord (w : List ℕ) : MulAut ↥Jc := (w.map qA).prod

theorem qWord_nil : qWord [] = 1 := rfl

theorem qWord_cons (k : ℕ) (w : List ℕ) : qWord (k :: w) = qA k * qWord w := by
  rw [qWord, List.map_cons, List.prod_cons]
  rfl

theorem qWord_append (w w' : List ℕ) : qWord (w ++ w') = qWord w * qWord w' := by
  rw [qWord, List.map_append, List.prod_append, qWord, qWord]

theorem qWord_jcA {w : List ℕ} (hw : ∀ k ∈ w, k < 3) (m : ℕ) :
    qWord w (jcA m) = jcA (wordAct w m) := by
  induction w with
  | nil => simp [qWord, wordAct]
  | cons k w ih =>
    have hk := hw k List.mem_cons_self
    have hw' : ∀ j ∈ w, j < 3 := fun j hj => hw j (List.mem_cons_of_mem _ hj)
    rw [qWord_cons]
    change qA k (qWord w (jcA m)) = jcA (wordAct (k :: w) m)
    rw [ih hw', qA_jcA hk]
    rfl

theorem qWord_eq_qWord {w w' : List ℕ} (hw : ∀ k ∈ w, k < 3)
    (hw' : ∀ k ∈ w', k < 3) (h : ∀ i < 10, wordAct w (2 ^ i) = wordAct w' (2 ^ i)) :
    qWord w = qWord w' := by
  apply mulAut_ext_basis
  intro i hi
  rw [qWord_jcA hw, qWord_jcA hw', h i hi]

noncomputable abbrev Qj : Subgroup (MulAut ↥Jc) := autImage (⊤ : Subgroup K) Jc

theorem qA_mem {k : ℕ} (hk : k < 3) : qA k ∈ Qj := by
  rw [Qj, autImage]
  refine ⟨⟨qK k, ⟨by trivial, qK_mem_N hk⟩⟩, ?_⟩
  rw [qA, dif_pos hk]
  rfl

theorem qWord_mem {w : List ℕ} (hw : ∀ k ∈ w, k < 3) : qWord w ∈ Qj := by
  induction w with
  | nil => rw [qWord_nil]; exact Qj.one_mem
  | cons k w ih =>
    have hk := hw k List.mem_cons_self
    have hw' : ∀ j ∈ w, j < 3 := fun j hj => hw j (List.mem_cons_of_mem _ hj)
    rw [qWord_cons]
    exact Qj.mul_mem (qA_mem hk) (ih hw')

end Gen

section Q


theorem Qj_eq_closure : Qj = closure (Set.range fun k : Fin 3 => qA k) := by
  let C : Subgroup (MulAut ↥Jc) := closure (Set.range fun k : Fin 3 => qA k)
  let H : Subgroup K :=
    (C.comap Jc.normalizerMonoidHom).map (Subgroup.subtype (normalizer (Jc : Set K)))
  have hJc : Jc ≤ H := by
    intro x hx
    let y : normalizer (Jc : Set K) := ⟨x, le_normalizer hx⟩
    have hcent : (y : K) ∈ Subgroup.centralizer (Jc : Set K) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact (Jc_comm hx hz).symm
    have hker : y ∈ Jc.normalizerMonoidHom.ker := by
      rw [Subgroup.normalizerMonoidHom_ker]
      exact hcent
    rw [MonoidHom.mem_ker] at hker
    refine Subgroup.mem_map.2 ⟨y, ?_, rfl⟩
    rw [Subgroup.mem_comap, hker]
    exact C.one_mem
  have hLK : LK ≤ H := by
    rw [LK, Subgroup.closure_le]
    rintro _ ⟨k, rfl⟩
    have hk : (k : ℕ) < 3 := k.2
    let y : normalizer (Jc : Set K) := ⟨qK k, qK_mem_N hk⟩
    refine Subgroup.mem_map.2 ⟨y, ?_, rfl⟩
    rw [Subgroup.mem_comap]
    rw [show Jc.normalizerMonoidHom y = qA k from by rw [qA, dif_pos hk]]
    exact Subgroup.subset_closure ⟨k, rfl⟩
  have hN : normalizer (Jc : Set K) ≤ H := by
    rw [normalizer_Jc_eq]
    exact sup_le hJc hLK
  refine le_antisymm ?_ ?_
  · intro g hg
    rw [Qj, autImage] at hg
    obtain ⟨x, hx⟩ := hg
    have hxN : (x : K) ∈ normalizer (Jc : Set K) := x.2.2
    have hxH := hN hxN
    rw [Subgroup.mem_map] at hxH
    obtain ⟨y, hy, hyx⟩ := hxH
    rw [Subgroup.mem_comap] at hy
    rw [← hx]
    have hyx' : y = Subgroup.inclusion inf_le_right x := Subtype.ext hyx
    rw [show conjN (⊤ : Subgroup K) Jc x = Jc.normalizerMonoidHom y by
      rw [hyx']; rfl]
    exact hy
  · rw [Subgroup.closure_le]
    rintro _ ⟨k, rfl⟩
    exact qA_mem k.2

theorem exists_qWord {g : MulAut ↥Jc} (hg : g ∈ Qj) :
    ∃ w : List ℕ, (∀ k ∈ w, k < 3) ∧ qWord w = g := by
  haveI : Finite ↥Jc := finite_Jc
  haveI : Finite (MulAut ↥Jc) := inferInstance
  rw [Qj_eq_closure] at hg
  refine Subgroup.closure_induction_left (s := Set.range fun k : Fin 3 => qA k)
    ?one ?mul ?inv hg
  · exact ⟨[], by simp, qWord_nil⟩
  · intro x hx y hy ih
    obtain ⟨k, rfl⟩ := hx
    obtain ⟨w, hw, hqw⟩ := ih
    refine ⟨(k : ℕ) :: w, ?_, ?_⟩
    · intro j hj
      rcases List.mem_cons.1 hj with rfl | hj
      · exact k.2
      · exact hw j hj
    · rw [qWord_cons, hqw]
  · intro x hx y hy ih
    obtain ⟨k, rfl⟩ := hx
    obtain ⟨w, hw, hqw⟩ := ih
    let n := orderOf (qA (k : ℕ)) - 1
    have hinv : (qA (k : ℕ)) ^ n = (qA (k : ℕ))⁻¹ := by
      have hpos : 0 < orderOf (qA (k : ℕ)) := orderOf_pos _
      have h1 : n + 1 = orderOf (qA (k : ℕ)) := by
        show orderOf (qA (k : ℕ)) - 1 + 1 = orderOf (qA (k : ℕ))
        exact Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)
      have hmul : (qA (k : ℕ)) ^ n * qA (k : ℕ) = 1 := by
        rw [← pow_succ, h1, pow_orderOf_eq_one]
      exact eq_inv_of_mul_eq_one_left hmul
    have hrep : qWord (List.replicate n (k : ℕ)) = (qA (k : ℕ)) ^ n := by
      rw [qWord, List.map_replicate, List.prod_replicate]
    refine ⟨List.replicate n (k : ℕ) ++ w, ?_, ?_⟩
    · intro j hj
      rcases List.mem_append.1 hj with hj | hj
      · rw [List.mem_replicate] at hj
        rw [hj.2]
        exact k.2
      · exact hw j hj
    · rw [qWord_append, hqw, hrep, hinv]

theorem Qj_induction {P : MulAut ↥Jc → Prop} (one : P 1)
    (mul : ∀ k < 3, ∀ g ∈ Qj, P g → P (qA k * g)) {g : MulAut ↥Jc} (hg : g ∈ Qj) : P g := by
  obtain ⟨w, hw, rfl⟩ := exists_qWord hg
  have key : ∀ w : List ℕ, (∀ k ∈ w, k < 3) → P (qWord w) := by
    intro w
    induction w with
    | nil => intro _; simpa [qWord_nil] using one
    | cons k w ih =>
      intro hw
      have hk : k < 3 := hw k List.mem_cons_self
      have hw' : ∀ j ∈ w, j < 3 := fun j hj => hw j (List.mem_cons_of_mem _ hj)
      rw [qWord_cons]
      exact mul k hk (qWord w) (qWord_mem hw') (ih hw')
  exact key w hw

end Q

end CFSG.Sporadic.Co2Jc
