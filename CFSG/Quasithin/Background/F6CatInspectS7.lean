module

public import CFSG.Quasithin.Background.F6CatS7InspectChk
public import CFSG.Quasithin.Background.F6CatInputs
public import CFSG.Quasithin.Recognition.CertOvergroup

public section

namespace CFSG.Quasithin

open scoped Pointwise
open CFSG.Open Equiv CFSG.Sporadic.Bridge

namespace F6

namespace S7Insp

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
  rw [tgen_chk.2.1]
  exact repL_word wF

theorem zL_rep : RepL zL z := by
  rw [tgen_chk.2.2]
  exact repL_word wZ

theorem telL_rep {a : ℕ} (ha : a < 16) : RepL (telL a) (tel a) := by
  rw [telL_chk a ha]
  exact repL_mul (repL_mul (F6.repL_pow rL_rep _) (F6.repL_pow fL_rep _)) (F6.repL_pow zL_rep _)

theorem dL_rep {j : ℕ} (hj : j < 35) : RepL (dL j) (d j) := by
  rw [dL_chk j hj]
  exact repL_word _

theorem closure_gen : Subgroup.closure (Set.range gen) = ⊤ := by
  set K := Subgroup.closure (Set.range gen) with hK
  have hgK : ∀ i, gen i ∈ K := fun i => Subgroup.subset_closure ⟨i, rfl⟩
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
    (fun x hx => (wit4_chk x hx).2.2.2.2) wit_nodup.2.2.2.2.1
  have h5 := le_card_of_witnesses (K := K ⊓ MulAction.stabilizer (Perm (Fin 7)) (0 : Fin 7) ⊓
      MulAction.stabilizer (Perm (Fin 7)) (1 : Fin 7) ⊓
      MulAction.stabilizer (Perm (Fin 7)) (2 : Fin 7) ⊓
      MulAction.stabilizer (Perm (Fin 7)) (3 : Fin 7) ⊓
      MulAction.stabilizer (Perm (Fin 7)) (4 : Fin 7)) gen 5 wit5
    (fun x hx => ⟨⟨⟨⟨⟨wordProd_mem hgK x.2, st (wit5_chk x hx).1⟩, st (wit5_chk x hx).2.1⟩,
      st (wit5_chk x hx).2.2.1⟩, st (wit5_chk x hx).2.2.2.1⟩, st (wit5_chk x hx).2.2.2.2.1⟩)
    (fun x hx => (wit5_chk x hx).2.2.2.2.2) wit_nodup.2.2.2.2.2
  obtain ⟨l0, l1, l2, l3, l4, l5⟩ := wit_length
  rw [l0] at h0
  rw [l1] at h1
  rw [l2] at h2
  rw [l3] at h3
  rw [l4] at h4
  rw [l5] at h5
  have h6 : 1 ≤ Nat.card ↥(K ⊓ MulAction.stabilizer (Perm (Fin 7)) (0 : Fin 7) ⊓
      MulAction.stabilizer (Perm (Fin 7)) (1 : Fin 7) ⊓
      MulAction.stabilizer (Perm (Fin 7)) (2 : Fin 7) ⊓
      MulAction.stabilizer (Perm (Fin 7)) (3 : Fin 7) ⊓
      MulAction.stabilizer (Perm (Fin 7)) (4 : Fin 7) ⊓
      MulAction.stabilizer (Perm (Fin 7)) (5 : Fin 7)) := Nat.card_pos
  have hS : Nat.card (⊤ : Subgroup (Perm (Fin 7))) = 5040 := by
    rw [Subgroup.card_top, Nat.card_perm, Nat.card_fin]
    rfl
  exact Subgroup.eq_of_le_of_card_ge le_top (by omega)

@[expose] def T₀ : Subgroup (Perm (Fin 7)) := Subgroup.closure {r, f, z}

theorem hord_perm (s : Perm (Fin 7)) : ∃ n : ℕ, 0 < n ∧ s ^ n = 1 :=
  ⟨Nat.card (Perm (Fin 7)), Nat.card_pos, pow_card_eq_one'⟩

theorem r_mem : r ∈ T₀ := Subgroup.subset_closure (by simp)

theorem f_mem : f ∈ T₀ := Subgroup.subset_closure (by simp)

theorem z_mem : z ∈ T₀ := Subgroup.subset_closure (by simp)

theorem tel_mem (a : ℕ) : tel a ∈ T₀ :=
  Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ r_mem _) (Subgroup.pow_mem _ f_mem _))
    (Subgroup.pow_mem _ z_mem _)

theorem tel_zero : tel 0 = 1 := by simp [tel]

theorem mem_T₀_iff {g : Perm (Fin 7)} : g ∈ T₀ ↔ ∃ a < 16, g = tel a := by
  constructor
  · intro hg
    have h := closure_subset_of_right_closed (S := {r, f, z}) (P := {g | ∃ a < 16, g = tel a})
      (fun s _ => hord_perm s) ⟨0, by norm_num, tel_zero.symm⟩ (by
        rintro _ ⟨a, ha, rfl⟩ s hs
        obtain ⟨h1, h2, h3, h4, h5, h6⟩ := tr_chk a ha
        rcases hs with rfl | rfl | rfl
        · exact ⟨_, h1, eq_of_repL (repL_mul (telL_rep ha) rL_rep) (h2 ▸ telL_rep h1)⟩
        · exact ⟨_, h3, eq_of_repL (repL_mul (telL_rep ha) fL_rep) (h4 ▸ telL_rep h3)⟩
        · exact ⟨_, h5, eq_of_repL (repL_mul (telL_rep ha) zL_rep) (h6 ▸ telL_rep h5)⟩)
    exact h hg
  · rintro ⟨a, -, rfl⟩
    exact tel_mem a

theorem card_T₀ : Nat.card T₀ = 16 := by
  let e : Fin 16 → T₀ := fun a => ⟨tel a, tel_mem a⟩
  have hinj : Function.Injective e := fun a b h => by
    have h' : tel a = tel b := congrArg Subtype.val h
    have r := telL_rep b.2
    rw [← h'] at r
    exact Fin.ext (telL_inj_chk a a.2 b b.2 (repL_unique (telL_rep a.2) r))
  have hsurj : Function.Surjective e := fun ⟨g, hg⟩ => by
    obtain ⟨a, ha, rfl⟩ := mem_T₀_iff.mp hg
    exact ⟨⟨a, ha⟩, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective e ⟨hinj, hsurj⟩), Nat.card_fin]

theorem d_zero : d 0 = 1 := by
  rw [d, d_zero_chk]
  rfl

theorem mem_cover (g : Perm (Fin 7)) :
    ∃ j < 35, ∃ a < 16, ∃ b < 16, g = tel a * d j * tel b := by
  have hg : g ∈ Subgroup.closure (Set.range gen) := closure_gen ▸ Subgroup.mem_top g
  refine closure_subset_of_right_closed (S := Set.range gen)
    (P := {g | ∃ j < 35, ∃ a < 16, ∃ b < 16, g = tel a * d j * tel b})
    (fun s _ => hord_perm s) ⟨0, by norm_num, 0, by norm_num, 0, by norm_num, by
      rw [tel_zero, d_zero, mul_one, mul_one]⟩ ?_ hg
  rintro _ ⟨j, hj, a, ha, b, hb, rfl⟩ _ ⟨k, rfl⟩
  have key : ∀ k < 2, ∃ j' < 35, ∃ a' < 16, ∃ b' < 16,
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

theorem pow_z2s4 : ∀ y : Multiplicative (ZMod 2) × Perm (Fin 4), y ^ 4 = 1 ∨ y ^ 6 = 1 := by
  decide +kernel

theorem hcover (g : Perm (Fin 7)) :
    ∃ j ∈ List.range 35, ∃ t ∈ T₀, ∃ t' ∈ T₀, g = t * d j * t' := by
  obtain ⟨j, hj, a, -, b, -, hg⟩ := mem_cover g
  exact ⟨j, List.mem_range.mpr hj, _, tel_mem a, _, tel_mem b, hg⟩

theorem hR (j : ℕ) (hj : j ∈ List.range 35) : d j ∈ T₀ ∨ j ∈ good ∨
    ∃ x ∈ Subgroup.closure ((T₀ : Set (Perm (Fin 7))) ∪ {d j}), ¬ (x ^ 4 = 1 ∨ x ^ 6 = 1) := by
  have hj' := List.mem_range.mp hj
  rcases cls_chk j hj' with ⟨rfl, -⟩ | ⟨-, hg⟩ | ⟨-, ha, h4, h6⟩
  · left
    rw [d_zero]
    exact T₀.one_mem
  · exact Or.inr (Or.inl hg)
  · right
    right
    set a := clsTab.getD j 0 - 2
    refine ⟨d j * tel a, Subgroup.mul_mem _
      (Subgroup.subset_closure (Set.mem_union_right _ rfl))
      (Subgroup.subset_closure (Set.mem_union_left _ (tel_mem a))), ?_⟩
    have hrep := repL_mul (dL_rep hj') (telL_rep ha)
    have hid : ∀ m, (d j * tel a) ^ m = 1 → RepL idL ((d j * tel a) ^ m) := fun m h => by
      rw [h]
      exact repL_one 7
    rintro (h | h)
    · exact h4 (repL_unique (F6.repL_pow hrep 4) (hid 4 h))
    · exact h6 (repL_unique (F6.repL_pow hrep 6) (hid 6 h))

theorem hpair (j : ℕ) (hj : j ∈ good) (j' : ℕ) (hj' : j' ∈ good) (hne : j ≠ j') :
    Subgroup.closure ((T₀ : Set (Perm (Fin 7))) ∪ {d j, d j'}) ≠ ⊤ := by
  obtain ⟨hr, hf, hz, hd, hd', hg0⟩ := pair_chk j hj j' hj' hne
  set M := MulAction.stabilizer (Perm (Fin 7)) (pairX j j')
  have hT₀M : T₀ ≤ M := (Subgroup.closure_le _).mpr (by
    rintro _ (rfl | rfl | rfl)
    · exact F6.mem_stabilizer_of_repL rL_rep hr
    · exact F6.mem_stabilizer_of_repL fL_rep hf
    · exact F6.mem_stabilizer_of_repL zL_rep hz)
  have hle : Subgroup.closure ((T₀ : Set (Perm (Fin 7))) ∪ {d j, d j'}) ≤ M := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro x (hx | hx | hx)
    · exact hT₀M hx
    · rw [hx]
      exact F6.mem_stabilizer_of_repL (dL_rep (good_lt_chk j hj)) hd
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact F6.mem_stabilizer_of_repL (dL_rep (good_lt_chk j' hj')) hd'
  intro htop
  exact F6.not_mem_stabilizer_of_repL (gL_rep 0) hg0 (hle (htop ▸ Subgroup.mem_top _))

end S7Insp

theorem s7InspectionFact_holds : S7InspectionFact := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 S7Insp.T₀ := IsPGroup.of_card (n := 4) (by rw [S7Insp.card_T₀]; rfl)
  have hidx : ¬ 2 ∣ S7Insp.T₀.index := by
    have h1 := S7Insp.T₀.card_mul_index
    have hS : Nat.card (Perm (Fin 7)) = 5040 := by
      rw [Nat.card_perm, Nat.card_fin]
      rfl
    rw [S7Insp.card_T₀, hS] at h1
    have h2 : S7Insp.T₀.index = 315 := by omega
    rw [h2]
    decide
  have hK : Nat.card (Multiplicative (ZMod 2) × Perm (Fin 4)) = 3 * Nat.card S7Insp.T₀ := by
    rw [S7Insp.card_T₀, Nat.card_prod, Nat.card_perm, Nat.card_fin, Nat.card_eq_fintype_card]
    rfl
  exact not_goldschmidt_of_cover S7Insp.T₀ hp hidx hK S7Insp.pow_z2s4 S7Insp.d (List.range 35)
    S7Insp.hcover S7Insp.good S7Insp.hR S7Insp.hpair

end F6

end CFSG.Quasithin
