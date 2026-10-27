module

public import CFSG.Quasithin.Recognition.CertU33Dc
public import CFSG.Quasithin.Recognition.CertTwoLocal

public section

namespace CFSG.Quasithin

open CFSG.CosetTable CFSG.Sporadic.Bridge

abbrev U33G : Type := PG 5 u33PresRels

@[expose] def u33GenPG (i : ℕ) : U33G := if h : i < 5 then PresentedGroup.of ⟨i, h⟩ else 1

theorem u33GenPG_of (i : Fin 5) : u33GenPG i.val = PresentedGroup.of i := by
  unfold u33GenPG
  rw [dite_eq_left i.2]

theorem u33PresHom_genPG (i : ℕ) : u33PresHom (u33GenPG i) = u33GenP i := by
  unfold u33GenPG u33GenP
  split_ifs with h
  · exact u33PresHom_of _
  · exact map_one _

theorem u33PresHom_wordProd' (w : List (ℕ × Bool)) :
    u33PresHom (wordProd u33GenPG w) = wordProd u33GenP w := by
  rw [map_wordProd]
  exact congrArg (fun f => wordProd f w) (funext u33PresHom_genPG)

theorem u33Tel_hom (i : ℕ) : u33PresHom (u33Tel u33GenPG i) = u33Tel u33GenP i :=
  u33PresHom_wordProd' _

theorem u33D_hom (j : ℕ) : u33PresHom (u33D u33GenPG j) = u33D u33GenP j :=
  u33PresHom_wordProd' _

theorem u33Gen4_hom (d : U33G) (i : ℕ) :
    u33PresHom (u33Gen4 u33GenPG d i) = u33Gen4 u33GenP (u33PresHom d) i := by
  unfold u33Gen4
  split_ifs <;> simp [u33PresHom_genPG]

theorem u33Gen4_wordProd_hom (d : U33G) (w : List (ℕ × Bool)) :
    u33PresHom (wordProd (u33Gen4 u33GenPG d) w) =
      wordProd (u33Gen4 u33GenP (u33PresHom d)) w := by
  rw [map_wordProd]
  exact congrArg (fun f => wordProd f w) (funext (u33Gen4_hom d))

theorem wordProd_mem_pred {G : Type*} [Group G] {K : Subgroup G} {x : ℕ → G} {P : ℕ → Prop}
    (hx : ∀ i, P i → x i ∈ K) {w : List (ℕ × Bool)} (hw : ∀ l ∈ w, P l.1) :
    wordProd x w ∈ K := by
  induction w with
  | nil => exact K.one_mem
  | cons l w ih =>
    simp only [wordProd, List.map_cons, List.prod_cons] at ih ⊢
    refine K.mul_mem ?_ (ih fun l' hl' => hw l' (List.mem_cons_of_mem _ hl'))
    split
    · exact hx _ (hw l List.mem_cons_self)
    · exact K.inv_mem (hx _ (hw l List.mem_cons_self))

theorem u33_Tel_mem (i : Fin 32) :
    u33Tel u33GenPG i ∈ Subgroup.closure ({u33GenPG 0, u33GenPG 1, u33GenPG 2} : Set U33G) := by
  refine wordProd_mem_pred (P := fun k => k < 3) ?_ (u33P_letters.1 i i.2)
  intro k hk
  apply Subgroup.subset_closure
  interval_cases k <;> simp

theorem u33_mem4 (d : U33G) {w : List (ℕ × Bool)} (hw : ∀ l ∈ w, l.1 < 4) :
    wordProd (u33Gen4 u33GenPG d) w ∈
      Subgroup.closure ({u33GenPG 0, u33GenPG 1, u33GenPG 2, d} : Set U33G) := by
  refine wordProd_mem_pred (P := fun k => k < 4) ?_ hw
  intro k hk
  apply Subgroup.subset_closure
  unfold u33Gen4
  split_ifs
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
      (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

theorem u33_gen : Subgroup.closure
    ({u33GenPG 0, u33GenPG 1, u33GenPG 2, u33GenPG 3, u33GenPG 4} : Set U33G) = ⊤ := by
  have h := PresentedGroup.closure_range_of
    {r : FreeGroup (Fin 5) | r ∈ u33PresRels.map FreeGroup.mk}
  have hset : ({u33GenPG 0, u33GenPG 1, u33GenPG 2, u33GenPG 3, u33GenPG 4} : Set U33G) =
      Set.range (PresentedGroup.of : Fin 5 → U33G) := by
    ext g
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range]
    constructor
    · rintro (rfl | rfl | rfl | rfl | rfl)
      · exact ⟨0, (u33GenPG_of 0).symm⟩
      · exact ⟨1, (u33GenPG_of 1).symm⟩
      · exact ⟨2, (u33GenPG_of 2).symm⟩
      · exact ⟨3, (u33GenPG_of 3).symm⟩
      · exact ⟨4, (u33GenPG_of 4).symm⟩
    · rintro ⟨i, rfl⟩
      rw [← u33GenPG_of]
      fin_cases i
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  rw [hset]
  exact h

theorem u33_orders
    : u33GenPG 0 ^ 4 = 1 ∧ u33GenPG 1 ^ 4 = 1 ∧ u33GenPG 2 ^ 2 = 1 ∧
    u33GenPG 3 ^ 3 = 1 ∧ u33GenPG 4 ^ 3 = 1 := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := u33P_orders
  refine ⟨u33PresHom_injective ?_, u33PresHom_injective ?_, u33PresHom_injective ?_,
    u33PresHom_injective ?_, u33PresHom_injective ?_⟩
  · rw [map_pow, map_one, u33PresHom_genPG]
    exact h0
  · rw [map_pow, map_one, u33PresHom_genPG]
    exact h1
  · rw [map_pow, map_one, u33PresHom_genPG]
    exact h2
  · rw [map_pow, map_one, u33PresHom_genPG]
    exact h3
  · rw [map_pow, map_one, u33PresHom_genPG]
    exact h4

theorem u33Tel_zero : u33Tel u33GenPG 0 = 1 := by
  have : u33TelW 0 = [] := by decide +kernel
  simp [u33Tel, this, wordProd]

theorem u33D_zero : u33D u33GenPG 0 = 1 := by
  have : u33DW 0 = [] := by decide +kernel
  simp [u33D, this, wordProd]

theorem u33_next
    (i : Fin 32) (g : Fin 3) :
    u33Tel u33GenPG i * u33GenPG g = u33Tel u33GenPG (u33Nxt i g % 32) := by
  apply u33PresHom_injective
  rw [map_mul, u33Tel_hom, u33PresHom_genPG, u33Tel_hom]
  exact u33P_next i g

theorem u33_decX_eq
    (j : Fin 14) (i : Fin 32) :
    u33D u33GenPG j * u33Tel u33GenPG i * u33GenPG 3 =
      u33Tel u33GenPG (u33DecXa j i % 32) * u33D u33GenPG (u33DecXk j i % 14) *
        u33Tel u33GenPG (u33DecXb j i % 32) := by
  apply u33PresHom_injective
  simp only [map_mul, u33Tel_hom, u33D_hom, u33PresHom_genPG]
  exact u33P_decX j i

theorem u33_decY_eq
    (j : Fin 14) (i : Fin 32) :
    u33D u33GenPG j * u33Tel u33GenPG i * u33GenPG 4 =
      u33Tel u33GenPG (u33DecYa j i % 32) * u33D u33GenPG (u33DecYk j i % 14) *
        u33Tel u33GenPG (u33DecYb j i % 32) := by
  apply u33PresHom_injective
  simp only [map_mul, u33Tel_hom, u33D_hom, u33PresHom_genPG]
  exact u33P_decY j i

theorem u33_memX
    (j : Fin 14) (hj : u33MemX.getD j "" ≠ "") :
    u33GenPG 3 ∈ Subgroup.closure
      ({u33GenPG 0, u33GenPG 1, u33GenPG 2, u33D u33GenPG j} : Set U33G) := by
  obtain ⟨hl, -, hx, -⟩ := u33P_mem j
  have heq : u33GenPG 3 = wordProd (u33Gen4 u33GenPG (u33D u33GenPG j))
      (u33W4 (u33MemX.getD j "")) := by
    apply u33PresHom_injective
    rw [u33PresHom_genPG, u33Gen4_wordProd_hom, u33D_hom]
    exact (hx hj).symm
  rw [heq]
  exact u33_mem4 _ hl

theorem u33_memY
    (j : Fin 14) (hj : u33MemY.getD j "" ≠ "") :
    u33GenPG 4 ∈ Subgroup.closure
      ({u33GenPG 0, u33GenPG 1, u33GenPG 2, u33D u33GenPG j} : Set U33G) := by
  obtain ⟨-, hl, -, hy⟩ := u33P_mem j
  have heq : u33GenPG 4 = wordProd (u33Gen4 u33GenPG (u33D u33GenPG j))
      (u33W4 (u33MemY.getD j "")) := by
    apply u33PresHom_injective
    rw [u33PresHom_genPG, u33Gen4_wordProd_hom, u33D_hom]
    exact (hy hj).symm
  rw [heq]
  exact u33_mem4 _ hl

theorem u33_inj
    : Function.Injective fun i : Fin 32 => u33Tel u33GenPG i := by
  intro i j h
  exact u33P_inj i j (by simpa only [u33Tel_hom] using congrArg u33PresHom h)

@[expose] noncomputable def u33Data
    : OvergroupData U33G (Fin 32) (Fin 14) where
  a := u33GenPG 0
  b := u33GenPG 1
  s := u33GenPG 2
  x := u33GenPG 3
  y := u33GenPG 4
  gen := u33_gen
  ha := u33_orders.1
  hb := u33_orders.2.1
  hs := u33_orders.2.2.1
  hx := u33_orders.2.2.2.1
  hy := u33_orders.2.2.2.2
  Tel := fun i => u33Tel u33GenPG i
  i0 := 0
  Tel_zero := u33Tel_zero
  Tel_mem := u33_Tel_mem
  Tel_next := fun i =>
    ⟨⟨⟨u33Nxt i 0 % 32, Nat.mod_lt _ (by norm_num)⟩, u33_next i 0⟩,
      ⟨⟨u33Nxt i 1 % 32, Nat.mod_lt _ (by norm_num)⟩, u33_next i 1⟩,
      ⟨⟨u33Nxt i 2 % 32, Nat.mod_lt _ (by norm_num)⟩, u33_next i 2⟩⟩
  D := fun j => u33D u33GenPG j
  j0 := 0
  ja := 1
  jb := 2
  D_zero := u33D_zero
  decX := fun j i =>
    ⟨⟨u33DecXk j i % 14, Nat.mod_lt _ (by norm_num)⟩, ⟨u33DecXa j i % 32, Nat.mod_lt _ (by norm_num)⟩,
      ⟨u33DecXb j i % 32, Nat.mod_lt _ (by norm_num)⟩, u33_decX_eq j i⟩
  decY := fun j i =>
    ⟨⟨u33DecYk j i % 14, Nat.mod_lt _ (by norm_num)⟩, ⟨u33DecYa j i % 32, Nat.mod_lt _ (by norm_num)⟩,
      ⟨u33DecYb j i % 32, Nat.mod_lt _ (by norm_num)⟩, u33_decY_eq j i⟩
  decXA := fun j hj i => by
    have hj2 : j.val < 2 := by
      rcases hj with rfl | rfl <;> decide
    exact ⟨⟨u33DecXk j i % 14, Nat.mod_lt _ (by norm_num)⟩, by
      rcases u33P_decXA j hj2 i i.2 with h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Fin.ext h),
      ⟨u33DecXa j i % 32, Nat.mod_lt _ (by norm_num)⟩, ⟨u33DecXb j i % 32, Nat.mod_lt _ (by norm_num)⟩,
      u33_decX_eq j i⟩
  decYB := fun j hj i => by
    have hj2 : j.val < 3 ∧ j.val ≠ 1 := by
      rcases hj with rfl | rfl <;> decide
    exact ⟨⟨u33DecYk j i % 14, Nat.mod_lt _ (by norm_num)⟩, by
      rcases u33P_decYB j hj2.1 hj2.2 i i.2 with h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Fin.ext h),
      ⟨u33DecYa j i % 32, Nat.mod_lt _ (by norm_num)⟩, ⟨u33DecYb j i % 32, Nat.mod_lt _ (by norm_num)⟩,
      u33_decY_eq j i⟩
  D_ja := by
    refine wordProd_mem_pred (P := fun k => k < 4) ?_ u33P_letters.2.2.1
    intro k hk
    apply Subgroup.subset_closure
    interval_cases k <;> simp
  D_jb := by
    refine wordProd_mem_pred (P := fun k => k = 4) ?_ u33P_letters.2.2.2
    intro k hk
    apply Subgroup.subset_closure
    subst hk
    simp
  genA := u33_memX 1 u33P_mem_ne.1
  genB := u33_memY 2 u33P_mem_ne.2.1
  genO := fun j h0 ha hb => by
    have hj3 : 3 ≤ j.val := by
      have h0' : j.val ≠ 0 := fun h => h0 (Fin.ext h)
      have h1' : j.val ≠ 1 := fun h => ha (Fin.ext h)
      have h2' : j.val ≠ 2 := fun h => hb (Fin.ext h)
      omega
    exact ⟨u33_memX j (u33P_mem_ne.2.2 j hj3).1, u33_memY j (u33P_mem_ne.2.2 j hj3).2⟩
  sepA := fun i h => by
    have h' := congrArg u33PresHom h
    simp only [u33Tel_hom, u33D_hom] at h'
    exact u33P_sep.1 i h'
  sepB := fun i h => by
    have h' := congrArg u33PresHom h
    simp only [u33Tel_hom, u33D_hom] at h'
    exact u33P_sep.2.1 i h'
  sepAB := fun i₁ i₂ h => by
    have h' := congrArg u33PresHom h
    simp only [map_mul, u33Tel_hom, u33D_hom] at h'
    exact u33P_sep.2.2 i₁ i₂ h'

theorem u33_card_T
    : Nat.card u33Data.T = 32 := by
  have h1 : Nat.card u33Data.T = Nat.card (Set.range u33Data.Tel) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun g => u33Data.mem_T_iff g)
  rw [h1]
  exact (Nat.card_range_of_injective u33_inj).trans (by simp)

theorem u33_syl
    : IsPGroup 2 u33Data.T ∧ ¬ 2 ∣ u33Data.T.index := by
  have hcard := u33_card_T
  refine ⟨IsPGroup.of_card (n := 5) (by rw [hcard]; norm_num), ?_⟩
  have h := Subgroup.card_mul_index u33Data.T
  rw [hcard, card_u33Pres] at h
  have h189 : u33Data.T.index = 189 := by omega
  rw [h189]
  norm_num

@[expose] def u33VSet : Set U33G := {u | ∃ i : Fin 3, u33PresHom u = u33V3 i}

@[expose] def u33z : U33G := (u33GenPG 0 * u33GenPG 0) * (u33GenPG 1 * u33GenPG 1)

theorem u33PresHom_A2 : u33PresHom (u33GenPG 0 * u33GenPG 0) = u33A2 := by
  simp [u33A2, u33PresHom_genPG]

theorem u33PresHom_B2 : u33PresHom (u33GenPG 1 * u33GenPG 1) = u33B2 := by
  simp [u33B2, u33PresHom_genPG]

theorem u33PresHom_z : u33PresHom u33z = u33Z := by
  simp [u33z, u33Z, u33A2, u33B2, u33PresHom_genPG]

theorem mem_normalizer_closure_of {G : Type*} [Group G] (s : Set G) (g : G)
    (h1 : ∀ u ∈ s, g * u * g⁻¹ ∈ s) (h2 : ∀ u ∈ s, g⁻¹ * u * g ∈ s) :
    g ∈ Subgroup.normalizer (Subgroup.closure s : Set G) := by
  apply Subgroup.normalizer_le_normalizer_closure s
  rw [Subgroup.mem_set_normalizer_iff]
  intro h
  refine ⟨h1 h, fun hh => ?_⟩
  have h3 := h2 _ hh
  have e : g⁻¹ * (g * h * g⁻¹) * g = h := by group
  rwa [e] at h3

theorem u33z_mem_T
    : u33z ∈ u33Data.T := by
  have ha : u33GenPG 0 ∈ u33Data.T := u33Data.a_mem_T
  have hb : u33GenPG 1 ∈ u33Data.T := u33Data.b_mem_T
  exact u33Data.T.mul_mem (u33Data.T.mul_mem ha ha) (u33Data.T.mul_mem hb hb)

theorem u33V3_mem_T
    (i : Fin 3) : ∃ w ∈ u33Data.T, u33PresHom w = u33V3 i := by
  have ha : u33GenPG 0 ∈ u33Data.T := u33Data.a_mem_T
  have hb : u33GenPG 1 ∈ u33Data.T := u33Data.b_mem_T
  fin_cases i
  · exact ⟨u33GenPG 0 * u33GenPG 0, u33Data.T.mul_mem ha ha, u33PresHom_A2⟩
  · exact ⟨u33GenPG 1 * u33GenPG 1, u33Data.T.mul_mem hb hb, u33PresHom_B2⟩
  · exact ⟨u33z, u33z_mem_T, u33PresHom_z⟩

theorem u33VSet_le_T
    : Subgroup.closure u33VSet ≤ u33Data.T := by
  refine (Subgroup.closure_le _).2 ?_
  rintro u ⟨i, hi⟩
  obtain ⟨w, hw, hwi⟩ := u33V3_mem_T i
  have : u = w := u33PresHom_injective (hi.trans hwi.symm)
  rw [SetLike.mem_coe, this]
  exact hw

theorem u33_conj_V (k : ℕ) (hk : k ∈ [0, 1, 2, 3]) :
    u33GenPG k ∈ Subgroup.normalizer (Subgroup.closure u33VSet : Set U33G) := by
  have hV : ∀ i : Fin 3, (∃ j : Fin 3, u33GenP k * u33V3 i * (u33GenP k)⁻¹ = u33V3 j) ∧
      (∃ j : Fin 3, (u33GenP k)⁻¹ * u33V3 i * u33GenP k = u33V3 j) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl
    · exact u33P_V0
    · exact u33P_V1
    · exact u33P_V2
    · exact u33P_V3
  apply mem_normalizer_closure_of
  · rintro u ⟨i, hi⟩
    obtain ⟨⟨j, hj⟩, -⟩ := hV i
    refine ⟨j, ?_⟩
    rw [map_mul, map_mul, map_inv, u33PresHom_genPG, hi]
    exact hj
  · rintro u ⟨i, hi⟩
    obtain ⟨-, ⟨j, hj⟩⟩ := hV i
    refine ⟨j, ?_⟩
    rw [map_mul, map_mul, map_inv, u33PresHom_genPG, hi]
    exact hj

theorem u33_conj_Z
    (k : ℕ) (hk : k ∈ [0, 1, 2, 4]) :
    u33GenPG k ∈ Subgroup.normalizer (Subgroup.closure ({u33z} : Set U33G) : Set U33G) := by
  apply mem_normalizer_closure_of
  · intro u hu
    rw [Set.mem_singleton_iff] at hu ⊢
    subst hu
    apply u33PresHom_injective
    rw [map_mul, map_mul, map_inv, u33PresHom_genPG, u33PresHom_z]
    exact (u33P_Z.1 k hk).1
  · intro u hu
    rw [Set.mem_singleton_iff] at hu ⊢
    subst hu
    apply u33PresHom_injective
    rw [map_mul, map_mul, map_inv, u33PresHom_genPG, u33PresHom_z]
    exact (u33P_Z.1 k hk).2

@[expose] noncomputable def u33Extra
    : u33Data.Extra where
  syl := u33_syl
  g := wordProd u33GenPG (u33W u33GWord)
  hg := fun i i' h => by
    change u33Tel u33GenPG i = 1
    change wordProd u33GenPG (u33W u33GWord) * u33Tel u33GenPG i' *
      (wordProd u33GenPG (u33W u33GWord))⁻¹ = u33Tel u33GenPG i at h
    apply u33PresHom_injective
    rw [map_one, u33Tel_hom]
    apply u33P_g i i'
    have h' := congrArg u33PresHom h
    simpa only [map_mul, map_inv, u33PresHom_wordProd', u33Tel_hom] using h'
  a_ne_one := fun h => u33P_xy.1 (by
    have h' : u33GenPG 0 = 1 := h
    simpa [u33PresHom_genPG] using congrArg u33PresHom h')
  xN := ⟨5, fun i' h => u33P_xy.2.1 i' (by
    have h' : u33GenPG 3 * u33Tel u33GenPG 5 * (u33GenPG 3)⁻¹ = u33Tel u33GenPG i' := h
    simpa only [map_mul, map_inv, u33Tel_hom, u33PresHom_genPG] using congrArg u33PresHom h')⟩
  yN := ⟨1, fun i' h => u33P_xy.2.2 i' (by
    have h' : u33GenPG 4 * u33Tel u33GenPG 1 * (u33GenPG 4)⁻¹ = u33Tel u33GenPG i' := h
    simpa only [map_mul, map_inv, u33Tel_hom, u33PresHom_genPG] using congrArg u33PresHom h')⟩
  PA := Subgroup.closure u33VSet
  PA_ne := by
    intro h
    have hmem : u33GenPG 0 * u33GenPG 0 ∈ Subgroup.closure u33VSet :=
      Subgroup.subset_closure ⟨0, u33PresHom_A2⟩
    rw [h, Subgroup.mem_bot] at hmem
    apply u33P_A2
    rw [← u33PresHom_A2, hmem, map_one]
  PA_p := u33_syl.1.to_le u33VSet_le_T
  PA_norm := by
    refine (Subgroup.closure_le _).2 ?_
    rintro g (rfl | rfl | rfl | rfl)
    · exact u33_conj_V 0 (by simp)
    · exact u33_conj_V 1 (by simp)
    · exact u33_conj_V 2 (by simp)
    · exact u33_conj_V 3 (by simp)
  PB := Subgroup.closure ({u33z} : Set U33G)
  PB_ne := by
    intro h
    have hmem : u33z ∈ Subgroup.closure ({u33z} : Set U33G) := Subgroup.subset_closure rfl
    rw [h, Subgroup.mem_bot] at hmem
    apply u33P_Z.2
    rw [← u33PresHom_z, hmem, map_one]
  PB_p := u33_syl.1.to_le ((Subgroup.closure_le _).2 (by
    rintro g rfl
    exact u33z_mem_T))
  PB_norm := by
    refine (Subgroup.closure_le _).2 ?_
    rintro g (rfl | rfl | rfl | rfl)
    · exact u33_conj_Z 0 (by simp)
    · exact u33_conj_Z 1 (by simp)
    · exact u33_conj_Z 2 (by simp)
    · exact u33_conj_Z 4 (by simp)

end CFSG.Quasithin
