module

public import CFSG.Quasithin.Recognition.SzVBA5Loc

public section

namespace CFSG.Quasithin.Kleidman.VBEven

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.SzVB
open scoped Pointwise symmDiff

variable {G : Type} [Group G] {P T V : Subgroup G} {z : G}

structure Frame (P V : Subgroup G) (z : G) where
  t : ConjSet P V → G
  abel : IsElemAbelian 2 (conjClosure V P)
  tdata : TDataG P (conjClosure V P) t z
  mem : ∀ U : ConjSet P V, t U ∈ U.1
  ne_one : ∀ U : ConjSet P V, t U ≠ 1
  ne_z : ∀ U : ConjSet P V, t U ≠ z

theorem exists_frame (F : A5Facts P T V z) : Nonempty (Frame P V z) := by
  obtain ⟨t, ht, hmem⟩ := exists_tDataG_mem F.klein
  exact ⟨⟨t, F.abel, ht, fun U => (hmem U).1, fun U => (hmem U).2.1, fun U => (hmem U).2.2⟩⟩

theorem mem_iff_of_fixed [DecidableEq (ConjSet P V)] {R : Set ↥P} {I : Finset (ConjSet P V)}
    (hR : ∀ U U' : ConjSet P V, U ≠ ConjSet.base P V → U' ≠ ConjSet.base P V →
      ∃ x ∈ R, x • U = U')
    (hI : ∀ x ∈ R, x • I = I) {U U' : ConjSet P V} (hU : U ≠ ConjSet.base P V)
    (hU' : U' ≠ ConjSet.base P V) : U ∈ I ↔ U' ∈ I := by
  constructor
  · intro h
    obtain ⟨x, hx, hxU⟩ := hR U U' hU hU'
    rw [← hI x hx, ← hxU]
    exact Finset.smul_mem_smul_finset h
  · intro h
    obtain ⟨x, hx, hxU⟩ := hR U' U hU' hU
    rw [← hI x hx, ← hxU]
    exact Finset.smul_mem_smul_finset h

theorem T_invariant_cases [DecidableEq (ConjSet P V)] (F : A5Facts P T V z)
    {I : Finset (ConjSet P V)} (hI : ∀ s : ↥P, (s : G) ∈ T → s • I = I) :
    I = ∅ ∨ I = {ConjSet.base P V} ∨ (∀ a, a ∈ I ↔ a ≠ ConjSet.base P V) ∨ (∀ a, a ∈ I) := by
  have key : ∀ {U U' : ConjSet P V}, U ≠ ConjSet.base P V → U' ≠ ConjSet.base P V →
      (U ∈ I ↔ U' ∈ I) := fun {U U'} hU hU' =>
    mem_iff_of_fixed (R := {s : ↥P | (s : G) ∈ T})
      (fun U U' hU hU' => F.l24.S_transitive U U' hU hU') hI hU hU'
  by_cases h : ∃ a ∈ I, a ≠ ConjSet.base P V
  · obtain ⟨a, haI, hao⟩ := h
    have hall : ∀ b, b ≠ ConjSet.base P V → b ∈ I := fun b hb => (key hao hb).mp haI
    by_cases ho : ConjSet.base P V ∈ I
    · right; right; right
      intro b
      by_cases hb : b = ConjSet.base P V
      · rw [hb]; exact ho
      · exact hall b hb
    · right; right; left
      intro b
      constructor
      · rintro hb rfl
        exact ho hb
      · exact hall b
  · push Not at h
    by_cases ho : ConjSet.base P V ∈ I
    · right; left
      ext b
      simp only [Finset.mem_singleton]
      constructor
      · intro hb
        by_contra hbo
        exact hbo (h b hb)
      · rintro rfl
        exact ho
    · left
      apply Finset.eq_empty_of_forall_notMem
      intro b hb
      exact ho (h b hb ▸ hb)

namespace Frame

variable (E : Frame P V z)

include E

theorem comm {a b : G} (ha : a ∈ conjClosure V P) (hb : b ∈ conjClosure V P) : a * b = b * a :=
  F7.isElemAbelian_comm E.abel ha hb

theorem mul_self {a : G} (ha : a ∈ conjClosure V P) : a * a = 1 := by
  rw [← pow_two]
  exact F7.isElemAbelian_pow_eq_one E.abel ha

theorem inv_eq {a : G} (ha : a ∈ conjClosure V P) : a⁻¹ = a :=
  inv_eq_of_mul_eq_one_right (E.mul_self ha)

theorem mul_eq_of_mul_eq {a b c d : G} (hb : b ∈ conjClosure V P)
    (hc : c ∈ conjClosure V P) (hd : d ∈ conjClosure V P) (h : a * c = b * d) :
    a * b = c * d := by
  calc a * b = (a * c) * (c * b) := by rw [mul_assoc a c, ← mul_assoc c c b, E.mul_self hc,
          one_mul]
    _ = (b * d) * (b * c) := by rw [h, E.comm hc hb]
    _ = (d * b) * (b * c) := by rw [E.comm hb hd]
    _ = d * (b * b) * c := by group
    _ = c * d := by rw [E.mul_self hb, mul_one, E.comm hd hc]

noncomputable def prod (I : Finset (ConjSet P V)) : G :=
  I.noncommProd E.t fun a _ b _ _ => E.comm (E.tdata.t_mem a) (E.tdata.t_mem b)

theorem prod_empty : E.prod ∅ = 1 :=
  Finset.noncommProd_empty _ _

theorem prod_singleton (a : ConjSet P V) : E.prod {a} = E.t a :=
  Finset.noncommProd_singleton _ _

theorem prod_insert [DecidableEq (ConjSet P V)] {a : ConjSet P V} {I : Finset (ConjSet P V)}
    (ha : a ∉ I) : E.prod (insert a I) = E.t a * E.prod I :=
  Finset.noncommProd_insert_of_notMem _ _ _ _ ha

theorem prod_mem (I : Finset (ConjSet P V)) : E.prod I ∈ conjClosure V P :=
  Subgroup.noncommProd_mem _ _ fun a _ => E.tdata.t_mem a

theorem z_comm (I : Finset (ConjSet P V)) : z * E.prod I = E.prod I * z :=
  E.comm E.tdata.z_mem (E.prod_mem I)

theorem t_mul_prod [DecidableEq (ConjSet P V)] (a : ConjSet P V) (K : Finset (ConjSet P V)) :
    E.t a * E.prod K = E.prod ({a} ∆ K) := by
  by_cases ha : a ∈ K
  · have h1 : ({a} ∆ K : Finset (ConjSet P V)) = K.erase a := by
      ext x
      by_cases hx : x = a <;> simp [Finset.mem_symmDiff, hx, ha]
    have h2 : E.prod K = E.t a * E.prod (K.erase a) := by
      conv_lhs => rw [← Finset.insert_erase ha]
      exact E.prod_insert (Finset.notMem_erase a K)
    rw [h1, h2, ← mul_assoc, E.tdata.t_sq, one_mul]
  · have h1 : ({a} ∆ K : Finset (ConjSet P V)) = insert a K := by
      ext x
      by_cases hx : x = a <;> simp [Finset.mem_symmDiff, hx, ha]
    rw [h1, E.prod_insert ha]

theorem prod_mul [DecidableEq (ConjSet P V)] (I J : Finset (ConjSet P V)) :
    E.prod I * E.prod J = E.prod (I ∆ J) := by
  induction I using Finset.induction_on with
  | empty => rw [E.prod_empty, one_mul, ← Finset.bot_eq_empty, bot_symmDiff]
  | insert a I ha ih =>
    rw [E.prod_insert ha, mul_assoc, ih, E.t_mul_prod, ← symmDiff_assoc]
    congr 2
    ext x
    by_cases hx : x = a <;> simp [Finset.mem_symmDiff, hx, ha]

theorem conj_prod [DecidableEq (ConjSet P V)] (x : ↥P) (I : Finset (ConjSet P V)) :
    ∃ ε : G, (ε = 1 ∨ ε = z) ∧ (x : G) * E.prod I * (x : G)⁻¹ = E.prod (x • I) * ε := by
  induction I using Finset.induction_on with
  | empty => exact ⟨1, Or.inl rfl, by rw [Finset.smul_finset_empty, E.prod_empty]; group⟩
  | insert a I ha ih =>
    obtain ⟨ε, hε, h⟩ := ih
    have hxa : x • a ∉ x • I := fun h' => ha ((Finset.smul_mem_smul_finset_iff x).mp h')
    rw [Finset.smul_finset_insert, E.prod_insert hxa, E.prod_insert ha]
    have e : (x : G) * (E.t a * E.prod I) * (x : G)⁻¹ =
        ((x : G) * E.t a * (x : G)⁻¹) * ((x : G) * E.prod I * (x : G)⁻¹) := by group
    rw [e, h]
    rcases E.tdata.act x a with h1 | h1
    · exact ⟨ε, hε, by rw [h1, mul_assoc]⟩
    · refine ⟨z * ε, ?_, ?_⟩
      · rcases hε with rfl | rfl
        · exact Or.inr (mul_one z)
        · exact Or.inl E.tdata.z_sq
      · rw [h1]
        calc E.t (x • a) * z * (E.prod (x • I) * ε) = E.t (x • a) * (z * E.prod (x • I)) * ε := by
              group
          _ = E.t (x • a) * (E.prod (x • I) * z) * ε := by rw [E.z_comm]
          _ = E.t (x • a) * E.prod (x • I) * (z * ε) := by group

theorem exists_of_mem [DecidableEq (ConjSet P V)] {w : G} (hw : w ∈ conjClosure V P) :
    ∃ I : Finset (ConjSet P V), w = E.prod I ∨ w = E.prod I * z := by
  rw [E.tdata.gen] at hw
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | ⟨U, rfl⟩
    · exact ⟨∅, Or.inr (by rw [E.prod_empty, one_mul])⟩
    · exact ⟨{U}, Or.inl (E.prod_singleton U).symm⟩
  | one => exact ⟨∅, Or.inl E.prod_empty.symm⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨I, hI⟩ := ihx
    obtain ⟨J, hJ⟩ := ihy
    refine ⟨I ∆ J, ?_⟩
    rcases hI with rfl | rfl <;> rcases hJ with rfl | rfl
    · exact Or.inl (E.prod_mul I J)
    · exact Or.inr (by rw [← mul_assoc, E.prod_mul])
    · exact Or.inr (by rw [mul_assoc, E.z_comm, ← mul_assoc, E.prod_mul])
    · refine Or.inl ?_
      calc E.prod I * z * (E.prod J * z) = E.prod I * (z * E.prod J) * z := by group
        _ = E.prod I * (E.prod J * z) * z := by rw [E.z_comm]
        _ = E.prod I * E.prod J * (z * z) := by group
        _ = E.prod (I ∆ J) := by rw [E.tdata.z_sq, mul_one, E.prod_mul]
  | inv x hx ih =>
    obtain ⟨I, hI⟩ := ih
    rw [← E.tdata.gen] at hx
    exact ⟨I, by rw [E.inv_eq hx]; exact hI⟩

theorem V_cases (hK : KleinData P V z) {w : G} (hw : w ∈ V) :
    w = 1 ∨ w = z ∨ w = E.t (ConjSet.base P V) ∨ w = E.t (ConjSet.base P V) * z :=
  klein_cases hK.elemAbelian hK.card_eq hK.z_mem hK.z_ne_one (E.mem (ConjSet.base P V))
    (E.ne_one _) (E.ne_z _) hw

theorem ker [Finite G] [DecidableEq (ConjSet P V)] (F : A5Facts P T V z)
    {I : Finset (ConjSet P V)} (h : E.prod I = 1 ∨ E.prod I = z) : I = ∅ ∨ ∀ U, U ∈ I := by
  have : Fintype (ConjSet P V) := Fintype.ofFinite _
  have hN : IsInvFamily ↥P {I : Finset (ConjSet P V) | E.prod I = 1 ∨ E.prod I = z} :=
    { empty_mem := Or.inl E.prod_empty
      symmDiff_mem := fun I hI J hJ => by
        show E.prod (I ∆ J) = 1 ∨ E.prod (I ∆ J) = z
        rw [← E.prod_mul]
        rcases hI with h1 | h1 <;> rcases hJ with h2 | h2 <;> rw [h1, h2]
        · exact Or.inl (mul_one 1)
        · exact Or.inr (one_mul z)
        · exact Or.inr (mul_one z)
        · exact Or.inl E.tdata.z_sq
      smul_mem := fun g I hI => by
        obtain ⟨ε, hε, he⟩ := E.conj_prod g I
        show E.prod (g • I) = 1 ∨ E.prod (g • I) = z
        have hεε : ε * ε = 1 := by
          rcases hε with rfl | rfl
          · exact mul_one 1
          · exact E.tdata.z_sq
        have key : E.prod (g • I) = (g : G) * E.prod I * (g : G)⁻¹ * ε := by
          rw [he, mul_assoc, hεε, mul_one]
        have hz : (g : G) * z * (g : G)⁻¹ = z := by
          rw [E.tdata.z_cent g g.2, mul_assoc, mul_inv_cancel, mul_one]
        rw [key]
        rcases hI with h1 | h1 <;> rw [h1]
        · rcases hε with rfl | rfl
          · exact Or.inl (by group)
          · exact Or.inr (by group)
        · rw [hz]
          rcases hε with rfl | rfl
          · exact Or.inr (mul_one z)
          · exact Or.inl E.tdata.z_sq }
  by_contra hcon
  push Not at hcon
  obtain ⟨hne, U₀, hU₀⟩ := hcon
  have hu : I ≠ Finset.univ := fun h' => hU₀ (h' ▸ Finset.mem_univ U₀)
  have hodd : Odd (Fintype.card (ConjSet P V)) := by
    rw [← Nat.card_eq_fintype_card, F.l24.card_five]
    decide
  have hpair := pair_mem_of_not_const hN (OddAux.conjSet_isPretransitive P V) (T.subgroupOf P)
    (F.l24.S_pGroup.of_equiv (Subgroup.subgroupOfEquivOfLe F.l24.S_le).symm)
    (ConjSet.base P V)
    (fun r hr => Subtype.ext
      (OddAux.conjSub_eq_of_mem_normalizer' (F.l24.S_le_normalizer (Subgroup.mem_subgroupOf.mp hr))))
    (fun a b ha hb => by
      obtain ⟨s, hs, hsab⟩ := F.l24.S_transitive a b ha hb
      exact ⟨s, Subgroup.mem_subgroupOf.mpr hs, hsab⟩)
    hodd h (Finset.nonempty_iff_ne_empty.mp hne) hu
  have h1 : 1 < Fintype.card (ConjSet P V) := by
    rw [← Nat.card_eq_fintype_card, F.l24.card_five]
    decide
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card h1
  have hab' := hpair a b hab
  have hb : a ∉ ({b} : Finset (ConjSet P V)) := by simpa using hab
  change E.prod (insert a {b}) = 1 ∨ E.prod (insert a {b}) = z at hab'
  rw [E.prod_insert hb, E.prod_singleton] at hab'
  obtain ⟨h2, h3⟩ := E.tdata.distinct a b hab
  rcases hab' with h4 | h4
  · exact h2 h4
  · exact h3 h4

theorem smul_eq_of_conj [Finite G] [DecidableEq (ConjSet P V)] (F : A5Facts P T V z) (x : ↥P)
    {I : Finset (ConjSet P V)} (h : (x : G) * E.prod I * (x : G)⁻¹ = E.prod I ∨
      (x : G) * E.prod I * (x : G)⁻¹ = E.prod I * z) : x • I = I := by
  have : Fintype (ConjSet P V) := Fintype.ofFinite _
  obtain ⟨ε, hε, he⟩ := E.conj_prod x I
  have hεW : ε ∈ conjClosure V P := by
    rcases hε with rfl | rfl
    · exact one_mem _
    · exact E.tdata.z_mem
  have hk : E.prod ((x • I) ∆ I) = 1 ∨ E.prod ((x • I) ∆ I) = z := by
    rw [← E.prod_mul]
    rcases h with h | h
    ·
      have h' : E.prod (x • I) * ε = E.prod I * 1 := by rw [← he, h, mul_one]
      rw [E.mul_eq_of_mul_eq (E.prod_mem _) hεW (one_mem _) h', mul_one]
      exact hε
    · have h' : E.prod (x • I) * ε = E.prod I * z := by rw [← he, h]
      rw [E.mul_eq_of_mul_eq (E.prod_mem _) hεW E.tdata.z_mem h']
      rcases hε with rfl | rfl
      · exact Or.inr (one_mul z)
      · exact Or.inl E.tdata.z_sq
  rcases E.ker F hk with h0 | hall
  · exact Finset.symmDiff_eq_empty.mp h0
  · exfalso
    have heven := PermAux.even_card_symmDiff_of_card_eq (Finset.card_smul_finset x I)
    have huniv : (x • I) ∆ I = Finset.univ := Finset.eq_univ_iff_forall.mpr hall
    rw [huniv, Finset.card_univ, ← Nat.card_eq_fintype_card, F.l24.card_five] at heven
    exact (by decide : ¬ Even 5) heven

end Frame

end CFSG.Quasithin.Kleidman.VBEven
