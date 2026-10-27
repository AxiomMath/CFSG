module

public import CFSG.Quasithin.Background.F6CatA7InspectChk
public import CFSG.Quasithin.Background.F6CatInputs
public import CFSG.Quasithin.Recognition.CertOvergroup

public section

namespace CFSG.Quasithin

open scoped Pointwise
open CFSG.Open Equiv CFSG.Sporadic.Bridge

namespace F6

namespace A7Insp

theorem gL_rep (i : ℕ) : RepL (gL i) (gen i) := by
  by_cases h : i = 0
  · subst h
    exact gen_chk.1
  · have e1 : gL i = gL 1 := by simp [gL, h]
    have e2 : gen i = gen 1 := by simp [gen, h]
    rw [e1, e2]
    exact gen_chk.2.1

theorem giL_rep (i : ℕ) : RepL (giL i) (gen i)⁻¹ := by
  by_cases h : i = 0
  · subst h
    exact gen_chk.2.2.1
  · have e1 : giL i = giL 1 := by simp [giL, h]
    have e2 : gen i = gen 1 := by simp [gen, h]
    rw [e1, e2]
    exact gen_chk.2.2.2

theorem repL_word (w : List (ℕ × Bool)) : RepL (F6.wordLst gL giL 7 w) (wordProd gen w) :=
  F6.repL_wordProd gL_rep giL_rep w

theorem rL_rep : RepL rL r := by
  rw [tgen_chk.1]
  exact repL_word wR

theorem fL_rep : RepL fL f := by
  rw [tgen_chk.2]
  exact repL_word wF

theorem telL_rep {a : ℕ} (ha : a < 8) : RepL (telL a) (tel a) := by
  rw [telL_chk a ha]
  exact repL_mul (F6.repL_pow rL_rep _) (F6.repL_pow fL_rep _)

theorem dL_rep {j : ℕ} (hj : j < 49) : RepL (dL j) (d j) := by
  rw [dL_chk j hj]
  exact repL_word _

theorem gen_mem (i : ℕ) : gen i ∈ alternatingGroup (Fin 7) := by
  rw [Perm.mem_alternatingGroup]
  unfold gen
  split_ifs <;> decide

theorem wordProd_mem_alt (w : List (ℕ × Bool)) : wordProd gen w ∈ alternatingGroup (Fin 7) :=
  wordProd_mem gen_mem w

theorem closure_gen : Subgroup.closure (Set.range gen) = alternatingGroup (Fin 7) := by
  set K := Subgroup.closure (Set.range gen) with hK
  have hgK : ∀ i, gen i ∈ K := fun i => Subgroup.subset_closure ⟨i, rfl⟩
  have hle : K ≤ alternatingGroup (Fin 7) :=
    (Subgroup.closure_le _).mpr (by rintro _ ⟨i, rfl⟩; exact gen_mem i)
  have st : ∀ {g : Perm (Fin 7)} {b : Fin 7}, g b = b →
      g ∈ MulAction.stabilizer (Perm (Fin 7)) b := fun h => mem_stabilizer_iff_apply.mpr h
  have h0 := le_card_of_witnesses (K := K) gen 0 wit0 (fun x _ => wordProd_mem hgK x.2)
    (fun x hx => wit0_chk x hx) wit_nodup.1
  have h1 := le_card_of_witnesses (K := K ⊓ MulAction.stabilizer (Perm (Fin 7)) (0 : Fin 7))
    gen 1 wit1 (fun x hx => ⟨wordProd_mem hgK x.2, st (wit1_chk x hx).1⟩)
    (fun x hx => (wit1_chk x hx).2) wit_nodup.2.1
  have h2 := le_card_of_witnesses (K := K ⊓ MulAction.stabilizer (Perm (Fin 7)) (0 : Fin 7) ⊓
      MulAction.stabilizer (Perm (Fin 7)) (1 : Fin 7)) gen 2 wit2
    (fun x hx => ⟨⟨wordProd_mem hgK x.2, st (wit2_chk x hx).1⟩, st (wit2_chk x hx).2.1⟩)
    (fun x hx => (wit2_chk x hx).2.2) wit_nodup.2.2.1
  have h3 := le_card_of_witnesses (K := K ⊓ MulAction.stabilizer (Perm (Fin 7)) (0 : Fin 7) ⊓
      MulAction.stabilizer (Perm (Fin 7)) (1 : Fin 7) ⊓
      MulAction.stabilizer (Perm (Fin 7)) (2 : Fin 7)) gen 3 wit3
    (fun x hx => ⟨⟨⟨wordProd_mem hgK x.2, st (wit3_chk x hx).1⟩, st (wit3_chk x hx).2.1⟩,
      st (wit3_chk x hx).2.2.1⟩)
    (fun x hx => (wit3_chk x hx).2.2.2) wit_nodup.2.2.2.1
  have h4 := le_card_of_witnesses (K := K ⊓ MulAction.stabilizer (Perm (Fin 7)) (0 : Fin 7) ⊓
      MulAction.stabilizer (Perm (Fin 7)) (1 : Fin 7) ⊓
      MulAction.stabilizer (Perm (Fin 7)) (2 : Fin 7) ⊓
      MulAction.stabilizer (Perm (Fin 7)) (3 : Fin 7)) gen 4 wit4
    (fun x hx => ⟨⟨⟨⟨wordProd_mem hgK x.2, st (wit4_chk x hx).1⟩, st (wit4_chk x hx).2.1⟩,
      st (wit4_chk x hx).2.2.1⟩, st (wit4_chk x hx).2.2.2.1⟩)
    (fun x hx => (wit4_chk x hx).2.2.2.2) wit_nodup.2.2.2.2
  obtain ⟨l0, l1, l2, l3, l4⟩ := wit_length
  rw [l0] at h0
  rw [l1] at h1
  rw [l2] at h2
  rw [l3] at h3
  rw [l4] at h4
  have h5 : 1 ≤ Nat.card ↥(K ⊓ MulAction.stabilizer (Perm (Fin 7)) (0 : Fin 7) ⊓
      MulAction.stabilizer (Perm (Fin 7)) (1 : Fin 7) ⊓
      MulAction.stabilizer (Perm (Fin 7)) (2 : Fin 7) ⊓
      MulAction.stabilizer (Perm (Fin 7)) (3 : Fin 7) ⊓
      MulAction.stabilizer (Perm (Fin 7)) (4 : Fin 7)) := Nat.card_pos
  have hA : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  exact Subgroup.eq_of_le_of_card_ge hle (by omega)

@[expose] def T₀ : Subgroup (Perm (Fin 7)) := Subgroup.closure {r, f}

theorem hord_perm (s : Perm (Fin 7)) : ∃ n : ℕ, 0 < n ∧ s ^ n = 1 :=
  ⟨Nat.card (Perm (Fin 7)), Nat.card_pos, pow_card_eq_one'⟩

theorem r_mem : r ∈ T₀ := Subgroup.subset_closure (by simp)

theorem f_mem : f ∈ T₀ := Subgroup.subset_closure (by simp)

theorem tel_mem (a : ℕ) : tel a ∈ T₀ :=
  Subgroup.mul_mem _ (Subgroup.pow_mem _ r_mem _) (Subgroup.pow_mem _ f_mem _)

theorem tel_zero : tel 0 = 1 := by simp [tel]

theorem mem_T₀_iff {g : Perm (Fin 7)} : g ∈ T₀ ↔ ∃ a < 8, g = tel a := by
  constructor
  · intro hg
    have h := closure_subset_of_right_closed (S := {r, f}) (P := {g | ∃ a < 8, g = tel a})
      (fun s _ => hord_perm s) ⟨0, by norm_num, tel_zero.symm⟩ (by
        rintro _ ⟨a, ha, rfl⟩ s hs
        have hc := tr_chk a ha
        rcases hs with rfl | rfl
        · exact ⟨_, hc.1, eq_of_repL (repL_mul (telL_rep ha) rL_rep)
            (hc.2.1 ▸ telL_rep hc.1)⟩
        · exact ⟨_, hc.2.2.1, eq_of_repL (repL_mul (telL_rep ha) fL_rep)
            (hc.2.2.2 ▸ telL_rep hc.2.2.1)⟩)
    exact h hg
  · rintro ⟨a, -, rfl⟩
    exact tel_mem a

theorem card_T₀ : Nat.card T₀ = 8 := by
  let e : Fin 8 → T₀ := fun a => ⟨tel a, tel_mem a⟩
  have hinj : Function.Injective e := fun a b h => by
    have h' : tel a = tel b := congrArg Subtype.val h
    have r := telL_rep b.2
    rw [← h'] at r
    exact Fin.ext (telL_inj_chk a a.2 b b.2 (repL_unique (telL_rep a.2) r))
  have hsurj : Function.Surjective e := fun ⟨g, hg⟩ => by
    obtain ⟨a, ha, rfl⟩ := mem_T₀_iff.mp hg
    exact ⟨⟨a, ha⟩, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective e ⟨hinj, hsurj⟩), Nat.card_fin]

theorem T₀_le : T₀ ≤ alternatingGroup (Fin 7) :=
  (Subgroup.closure_le _).mpr (by
    rintro _ (rfl | rfl)
    · exact wordProd_mem_alt wR
    · exact wordProd_mem_alt wF)

theorem d_zero : d 0 = 1 := by
  rw [d, d_zero_chk]
  rfl

theorem mem_cover {g : Perm (Fin 7)} (hg : g ∈ alternatingGroup (Fin 7)) :
    ∃ j < 49, ∃ a < 8, ∃ b < 8, g = tel a * d j * tel b := by
  rw [← closure_gen] at hg
  refine closure_subset_of_right_closed (S := Set.range gen)
    (P := {g | ∃ j < 49, ∃ a < 8, ∃ b < 8, g = tel a * d j * tel b})
    (fun s _ => hord_perm s) ⟨0, by norm_num, 0, by norm_num, 0, by norm_num, by
      rw [tel_zero, d_zero, mul_one, mul_one]⟩ ?_ hg
  rintro _ ⟨j, hj, a, ha, b, hb, rfl⟩ _ ⟨k, rfl⟩
  have key : ∀ k < 2, ∃ j' < 49, ∃ a' < 8, ∃ b' < 8,
      tel a * d j * tel b * gen k = tel a' * d j' * tel b' := by
    intro k hk
    obtain ⟨h0, h1, h2, h3⟩ := dec_chk j hj b hb k hk
    have e1 : d j * tel b * gen k = tel (decE j b k 0) * d (decE j b k 1) * tel (decE j b k 2) :=
      eq_of_repL (repL_mul (repL_mul (dL_rep hj) (telL_rep hb)) (gL_rep k))
        (h3 ▸ repL_mul (repL_mul (telL_rep h0) (dL_rep h1)) (telL_rep h2))
    obtain ⟨a'', ha'', he⟩ := mem_T₀_iff.mp
      (Subgroup.mul_mem _ (tel_mem a) (tel_mem (decE j b k 0)))
    refine ⟨_, h1, a'', ha'', _, h2, ?_⟩
    rw [← he, mul_assoc (tel a) (d j), mul_assoc (tel a), e1]
    group
  by_cases hk : k = 0
  · subst hk
    exact key 0 (by norm_num)
  · have e2 : gen k = gen 1 := by simp [gen, hk]
    rw [e2]
    exact key 1 (by norm_num)

abbrev D : Type := ↥(alternatingGroup (Fin 7))

@[expose] noncomputable def T₀D : Subgroup D := T₀.subgroupOf (alternatingGroup (Fin 7))

@[expose] noncomputable def rep (j : ℕ) : D := ⟨d j, wordProd_mem_alt _⟩

theorem card_T₀D : Nat.card T₀D = 8 := by
  rw [T₀D, Nat.card_congr (Subgroup.subgroupOfEquivOfLe T₀_le).toEquiv, card_T₀]

theorem telD_mem (a : ℕ) : (⟨tel a, T₀_le (tel_mem a)⟩ : D) ∈ T₀D := by
  rw [T₀D, Subgroup.mem_subgroupOf]
  exact tel_mem a

theorem hcover (g : D) : ∃ j ∈ List.range 49, ∃ t ∈ T₀D, ∃ t' ∈ T₀D, g = t * rep j * t' := by
  obtain ⟨j, hj, a, -, b, -, hg⟩ := mem_cover g.2
  exact ⟨j, List.mem_range.mpr hj, _, telD_mem a, _, telD_mem b, Subtype.ext hg⟩

theorem hR (j : ℕ) (hj : j ∈ List.range 49) : rep j ∈ T₀D ∨ j ∈ good ∨
    ∃ x ∈ Subgroup.closure ((T₀D : Set D) ∪ {rep j}), ¬ (x ^ 4 = 1 ∨ x ^ 3 = 1) := by
  have hj' := List.mem_range.mp hj
  rcases cls_chk j hj' with ⟨rfl, -⟩ | ⟨-, hg⟩ | ⟨-, ha, h4, h3⟩
  · left
    rw [T₀D, Subgroup.mem_subgroupOf]
    change d 0 ∈ T₀
    rw [d_zero]
    exact T₀.one_mem
  · exact Or.inr (Or.inl hg)
  · right
    right
    set a := clsTab.getD j 0 - 2
    refine ⟨rep j * ⟨tel a, T₀_le (tel_mem a)⟩, Subgroup.mul_mem _
      (Subgroup.subset_closure (Set.mem_union_right _ rfl))
      (Subgroup.subset_closure (Set.mem_union_left _ (telD_mem a))), ?_⟩
    have hrep := repL_mul (dL_rep hj') (telL_rep ha)
    have hpow : ∀ m, (rep j * ⟨tel a, T₀_le (tel_mem a)⟩) ^ m = 1 → (d j * tel a) ^ m = 1 :=
      fun m h => by simpa [rep] using congrArg Subtype.val h
    have hid : ∀ m, (d j * tel a) ^ m = 1 → RepL idL ((d j * tel a) ^ m) := fun m h => by
      rw [h]
      exact repL_one 7
    rintro (h | h)
    · exact h4 (repL_unique (F6.repL_pow hrep 4) (hid 4 (hpow 4 h)))
    · exact h3 (repL_unique (F6.repL_pow hrep 3) (hid 3 (hpow 3 h)))

theorem hpair (j : ℕ) (hj : j ∈ good) (j' : ℕ) (hj' : j' ∈ good) (hne : j ≠ j') :
    Subgroup.closure ((T₀D : Set D) ∪ {rep j, rep j'}) ≠ ⊤ := by
  obtain ⟨hr, hf, hd, hd', hg0⟩ := pair_chk j hj j' hj' hne
  set M := MulAction.stabilizer (Perm (Fin 7)) (pairX j j')
  have hT₀M : T₀ ≤ M := (Subgroup.closure_le _).mpr (by
    rintro _ (rfl | rfl)
    · exact F6.mem_stabilizer_of_repL rL_rep hr
    · exact F6.mem_stabilizer_of_repL fL_rep hf)
  have hle : Subgroup.closure ((T₀D : Set D) ∪ {rep j, rep j'}) ≤
      M.subgroupOf (alternatingGroup (Fin 7)) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro x (hx | hx | hx)
    · rw [SetLike.mem_coe, T₀D, Subgroup.mem_subgroupOf] at hx
      exact Subgroup.mem_subgroupOf.mpr (hT₀M hx)
    · rw [hx]
      exact Subgroup.mem_subgroupOf.mpr
        (F6.mem_stabilizer_of_repL (dL_rep (good_lt_chk j hj)) hd)
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact Subgroup.mem_subgroupOf.mpr
        (F6.mem_stabilizer_of_repL (dL_rep (good_lt_chk j' hj')) hd')
  intro htop
  have h0 : (⟨gen 0, gen_mem 0⟩ : D) ∈ M.subgroupOf (alternatingGroup (Fin 7)) :=
    hle (htop ▸ Subgroup.mem_top _)
  exact F6.not_mem_stabilizer_of_repL (gL_rep 0) hg0 (Subgroup.mem_subgroupOf.mp h0)

end A7Insp

theorem a7InspectionFact_holds : A7InspectionFact := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 A7Insp.T₀D := IsPGroup.of_card (n := 3) (by rw [A7Insp.card_T₀D]; rfl)
  have hidx : ¬ 2 ∣ A7Insp.T₀D.index := by
    have h1 := A7Insp.T₀D.card_mul_index
    have hA : Nat.card A7Insp.D = 2520 := by
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      decide
    rw [A7Insp.card_T₀D, hA] at h1
    have h2 : A7Insp.T₀D.index = 315 := by omega
    rw [h2]
    decide
  have hK : Nat.card (Perm (Fin 4)) = 3 * Nat.card A7Insp.T₀D := by
    rw [A7Insp.card_T₀D, Nat.card_perm, Nat.card_fin]
    rfl
  have hKpq : ∀ y : Perm (Fin 4), y ^ 4 = 1 ∨ y ^ 3 = 1 := by decide
  exact not_goldschmidt_of_cover A7Insp.T₀D hp hidx hK hKpq A7Insp.rep (List.range 49)
    A7Insp.hcover A7Insp.good A7Insp.hR A7Insp.hpair

end F6

end CFSG.Quasithin
