module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP3Core

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin U42F431
open CFSG.Quasithin.H13.F431.U42 (Y P45)

@[expose] def c3A : Ah := incl U42.c3Y

@[expose] def D1A : Ah := incl (U42.Dj 1)

@[expose] def gensP1 : Set Ah := Set.range (fun k : Fin 5 => gTA k) ∪ {fhatA, c3A, D1A}

theorem c3A_mem_Bh' : c3A ∈ Bh := c3A_mem_Bh

theorem orderOf_c3A : orderOf c3A = 3 := by
  rw [c3A, orderOf_injective incl incl_injective]
  exact U42.orderOf_c3

theorem D1A_mem_P1h : D1A ∈ P1h := by
  rw [D1A, ← Subgroup.mem_comap, comap_P1h]
  exact U42.D1_mem_P1

theorem D1A_not_mem_P2h : D1A ∉ P2h := by
  rw [D1A, ← Subgroup.mem_comap, comap_P2h]
  exact U42.D1_not_mem_P2

theorem Bh_le_closure :
    Bh ≤ Subgroup.closure (Set.range (fun k : Fin 5 => gTA k) ∪ {fhatA, c3A}) := by
  set K' := Subgroup.closure (Set.range (fun k : Fin 5 => gTA k) ∪ {fhatA, c3A}) with hK'
  have hK'B : K' ≤ Bh := by
    rw [hK', Subgroup.closure_le]
    rintro _ (⟨k, rfl⟩ | rfl | rfl)
    · have := U42.gTY_mem_B0 k k.2
      rw [← comap_Bh] at this
      exact this
    · exact fhatA_mem_Bh
    · exact c3A_mem_Bh
  have hThatK : That ≤ K' := by
    rw [That, Subgroup.closure_le]
    rintro _ (⟨k, rfl⟩ | rfl)
    · exact Subgroup.subset_closure (Or.inl ⟨k, rfl⟩)
    · exact Subgroup.subset_closure (Or.inr (Or.inl rfl))
  have hc3K : c3A ∈ K' := Subgroup.subset_closure (Or.inr (Or.inr rfl))
  have h128 : 128 ∣ Nat.card K' := card_That ▸ Subgroup.card_dvd_of_le hThatK
  have h3 : 3 ∣ Nat.card K' := by
    have := Subgroup.orderOf_dvd_natCard K' hc3K
    rwa [orderOf_c3A] at this
  have h384 : 384 ∣ Nat.card K' := by
    have : Nat.Coprime 128 3 := by norm_num
    simpa using Nat.Coprime.mul_dvd_of_dvd_of_dvd this h128 h3
  have hcard : Nat.card Bh ≤ Nat.card K' := by
    rw [card_Bh]
    exact Nat.le_of_dvd Nat.card_pos h384
  exact (Subgroup.eq_of_le_of_card_ge hK'B hcard).symm ▸ le_rfl

theorem P1h_le_closure :
    P1h ≤ Subgroup.closure gensP1 := by
  set K := Subgroup.closure gensP1 with hK
  have hBK : Bh ≤ K := (Bh_le_closure).trans (Subgroup.closure_mono (by
    intro g hg
    rcases hg with hg | rfl | rfl
    · exact Or.inl hg
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))))
  have hD1 : D1A ∈ K := Subgroup.subset_closure (Or.inr (Or.inr (Or.inr rfl)))
  rcases lattice_Bh (H := K ⊓ P1h) (le_inf hBK Bh_le_P1h) with h | h | h | h
  · exfalso
    have : D1A ∈ K ⊓ P1h := ⟨hD1, D1A_mem_P1h⟩
    rw [h] at this
    exact D1A_not_mem_P2h this.2
  · exact h ▸ inf_le_left
  · exfalso
    exact P2h_not_le_P1h (h ▸ inf_le_right)
  · exfalso
    have h1 : (⊤ : Subgroup Ah) ≤ P1h := h ▸ inf_le_right
    have := Subgroup.card_le_of_le h1
    rw [Subgroup.card_top, card_A, card_P1h] at this
    omega

@[expose] def Q1idx : List ℕ :=
  [0, 1, 2, 4, 5, 6, 7, 9, 10, 11, 13, 14, 19, 20, 21, 22, 23, 25, 26, 28, 29, 33, 34, 36, 40, 42,
    46, 53, 54, 58, 60, 62]

@[expose] def Q1l : List PL := Q1idx.map fun i => Tl.getD i []

theorem Q1l_check :
    idL ∈ Q1l ∧ Q1l.Nodup ∧ (∀ l ∈ Q1l, l ∈ Thl) ∧
    (∀ l ∈ Q1l, ∀ m ∈ Q1l, comp l m ∈ Q1l) ∧ (∀ l ∈ Q1l, ∃ m ∈ Q1l, comp l m = idL) ∧
    (∀ l ∈ Q1l, ∀ k < 5, ∃ m ∈ Q1l, comp (gTL k) l = comp m (gTL k)) ∧
    (∀ l ∈ Q1l, ∃ m ∈ Q1l, comp fhatL l = comp m fhatL) ∧
    (∀ l ∈ Q1l, ∃ m ∈ Q1l, comp c3L l = comp m c3L) ∧
    (∀ l ∈ Q1l, ∃ m ∈ Q1l, comp (DL 1) l = comp m (DL 1)) := by
  decide +kernel

theorem inv_mem_of_mul_closed {G : Type*} [Group G] [Finite G] {S : Set G} (h1 : (1 : G) ∈ S)
    (hmul : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) {a : G} (ha : a ∈ S) : a⁻¹ ∈ S := by
  have hpow : ∀ n : ℕ, a ^ n ∈ S := by
    intro n
    induction n with
    | zero => simpa using h1
    | succ n ih => rw [pow_succ]; exact hmul _ ih _ ha
  have hpos := orderOf_pos a
  have : a ^ (orderOf a - 1) = a⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← pow_succ, Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
  rw [← this]
  exact hpow _

@[expose] def Q1 : Subgroup Ah where
  carrier := {g | ∃ l ∈ Q1l, RepL l (g : P45)}
  mul_mem' := by
    rintro a b ⟨l, hl, hla⟩ ⟨m, hm, hmb⟩
    exact ⟨comp l m, Q1l_check.2.2.2.1 l hl m hm, repL_mul hla hmb⟩
  one_mem' := ⟨idL, Q1l_check.1, repL_one 45⟩
  inv_mem' := by
    intro a ha
    refine inv_mem_of_mul_closed (S := {g : Ah | ∃ l ∈ Q1l, RepL l (g : P45)})
      ⟨idL, Q1l_check.1, repL_one 45⟩ ?_ ha
    rintro a ⟨l, hl, hla⟩ b ⟨m, hm, hmb⟩
    exact ⟨comp l m, Q1l_check.2.2.2.1 l hl m hm, repL_mul hla hmb⟩

theorem Q1_le_That : Q1 ≤ That := by
  rintro g ⟨l, hl, hrep⟩
  obtain ⟨g', hg', hrep'⟩ := exists_That_of_mem_Thl (Q1l_check.2.2.1 l hl)
  have : g = g' := Subtype.ext (eq_of_repL hrep hrep')
  rwa [this]

theorem Q1_conj_gen {s : Ah} {sL : PL} (hs : RepL sL (s : P45))
    (hcl : ∀ l ∈ Q1l, ∃ m ∈ Q1l, comp sL l = comp m sL) {q : Ah} (hq : q ∈ Q1) :
    s * q * s⁻¹ ∈ Q1 := by
  obtain ⟨l, hl, hlq⟩ := hq
  obtain ⟨m, hm, hml⟩ := hcl l hl
  obtain ⟨m', -, hm'⟩ := exists_That_of_mem_Thl (Q1l_check.2.2.1 m hm)
  have h2 : RepL (comp m sL) (((m' * s : Ah)) : P45) := repL_mul hm' hs
  rw [← hml] at h2
  have h3 : RepL (comp sL l) (((s * q : Ah)) : P45) := repL_mul hs hlq
  have h1 : s * q = m' * s := Subtype.ext (eq_of_repL h3 h2)
  have : s * q * s⁻¹ = m' := by rw [h1]; group
  rw [this]
  exact ⟨m, hm, hm'⟩

theorem Q1_conj_gT (k : Fin 5) {q : Ah} (hq : q ∈ Q1) :
    gTA k * q * (gTA k)⁻¹ ∈ Q1 :=
  Q1_conj_gen (s := gTA k) (repL_gTA k) (fun l hl => Q1l_check.2.2.2.2.2.1 l hl k k.2) hq

theorem Q1_conj_fhat {q : Ah} (hq : q ∈ Q1) :
    fhatA * q * fhatA⁻¹ ∈ Q1 :=
  Q1_conj_gen (s := fhatA) repL_fhat Q1l_check.2.2.2.2.2.2.1 hq

theorem Q1_conj_c3 {q : Ah} (hq : q ∈ Q1) :
    c3A * q * c3A⁻¹ ∈ Q1 :=
  Q1_conj_gen (s := c3A) U42.repL_c3 Q1l_check.2.2.2.2.2.2.2.1 hq

theorem Q1_conj_D1 {q : Ah} (hq : q ∈ Q1) :
    D1A * q * D1A⁻¹ ∈ Q1 :=
  Q1_conj_gen (s := D1A) (U42.repL_Dj 1) Q1l_check.2.2.2.2.2.2.2.2 hq

theorem Q1_conj_gensP1 {s : Ah} (hs : s ∈ gensP1) {q : Ah}
    (hq : q ∈ Q1) : s * q * s⁻¹ ∈ Q1 := by
  rw [gensP1] at hs
  rcases hs with ⟨k, rfl⟩ | rfl | rfl | rfl
  · exact Q1_conj_gT k hq
  · exact Q1_conj_fhat hq
  · exact Q1_conj_c3 hq
  · exact Q1_conj_D1 hq

theorem Q1_conj_mem {g : Ah}
    (hg : g ∈ P1h) {q : Ah} (hq : q ∈ Q1) : g * q * g⁻¹ ∈ Q1 := by
  have key := closure_subset_of_right_closed (S := gensP1)
    (P := {g : Ah | ∀ q ∈ Q1, g * q * g⁻¹ ∈ Q1})
    (fun s _ => by
      obtain ⟨n, hn, h⟩ := (isOfFinOrder_of_finite s).exists_pow_eq_one
      exact ⟨n, hn, h⟩)
    (fun q hq => by simpa using hq)
    (fun p hp s hs q hq => by
      have hsq : s * q * s⁻¹ ∈ Q1 := Q1_conj_gensP1 hs hq
      have := hp _ hsq
      simpa [mul_assoc] using this)
  exact key (P1h_le_closure hg) q hq

theorem length_le_card_of_nodup (S : Subgroup Ah) {L : List PL} (hnd : L.Nodup)
    (hL : ∀ l ∈ L, ∃ g ∈ S, RepL l (g : P45)) : L.length ≤ Nat.card S := by
  choose! gf hgf using hL
  have hinj : Function.Injective fun i : Fin L.length =>
      (⟨gf (L.get i), (hgf _ (List.get_mem L i)).1⟩ : ↥S) := by
    intro i j hij
    have h1 : gf (L.get i) = gf (L.get j) := congrArg Subtype.val hij
    have h2 := hgf _ (List.get_mem L i)
    have h3 := hgf _ (List.get_mem L j)
    have : L.get i = L.get j := by
      apply repL_unique h2.2
      rw [h1]
      exact h3.2
    exact (hnd.get_inj_iff).1 this
  have := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_eq_fintype_card, Fintype.card_fin] at this

theorem card_Q1_ge : 32 ≤ Nat.card Q1 := by
  have h := length_le_card_of_nodup Q1 Q1l_check.2.1 (fun l hl => by
    obtain ⟨g, hg, hrep⟩ := exists_That_of_mem_Thl (Q1l_check.2.2.1 l hl)
    exact ⟨g, ⟨l, hl, hrep⟩, hrep⟩)
  have h32 : Q1l.length = 32 := by decide +kernel
  omega

end CFSG.Quasithin.H13.F431.U42Aut
