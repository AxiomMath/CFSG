module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.RankThree.PartTwo.KFacts.KF163A10

variable {B : Subgroup (Equiv.Perm (Fin 10))}

private theorem card_orbit_ne_one_of_smul_ne {p : Fin 10} {g : B} (hg : g • p ≠ p) :
    Nat.card (MulAction.orbit B p) ≠ 1 := by
  intro h1
  haveI : Subsingleton (MulAction.orbit B p) :=
    Finite.card_le_one_iff_subsingleton.mp (le_of_eq h1)
  have h : (⟨g • p, MulAction.mem_orbit p g⟩ : MulAction.orbit B p) =
      ⟨p, (MulAction.mem_orbit_self p : p ∈ MulAction.orbit B p)⟩ := Subsingleton.elim _ _
  exact hg (congrArg Subtype.val h)

theorem card_orbit_eq_one_or_three_or_nine (hB27 : Nat.card B = 27) (a : Fin 10) :
    Nat.card (MulAction.orbit B a) = 1 ∨ Nat.card (MulAction.orbit B a) = 3 ∨
      Nat.card (MulAction.orbit B a) = 9 := by
  have hdvd : Nat.card (MulAction.orbit B a) ∣ 3 ^ 3 := by
    have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup B a)
    rw [Nat.card_prod, hB27] at h
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← h]
    exact dvd_mul_right _ _
  have hle : Nat.card (MulAction.orbit B a) ≤ 10 := by
    simpa using Nat.card_le_card_of_injective (fun x : MulAction.orbit B a => (x : Fin 10))
      Subtype.val_injective
  obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 3)).mp hdvd
  have hle' : 3 ^ k ≤ 10 := by rw [← hk]; exact hle
  have hk2 : k ≤ 2 := by
    rcases Nat.lt_or_ge k 3 with h | h
    · omega
    · have h3 : 3 ^ 3 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) h
      norm_num at h3
      omega
  rw [hk]
  interval_cases k <;> norm_num

theorem smul_eq_of_mem_stabilizer_of_mem_orbit (hB : CFSG.Open.IsElemAbelian 3 B)
    {a p : Fin 10} (hp : p ∈ MulAction.orbit B a) {b : B}
    (hb : b ∈ MulAction.stabilizer B a) : b • p = p := by
  haveI : IsMulCommutative B := hB.1
  obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hp
  calc b • (g • a) = (b * g) • a := (mul_smul b g a).symm
    _ = (g * b) • a := by rw [mul_comm']
    _ = g • (b • a) := mul_smul g b a
    _ = g • a := by rw [MulAction.mem_stabilizer_iff.mp hb]

theorem card_orbit_ne_nine (hB : CFSG.Open.IsElemAbelian 3 B) (hB27 : Nat.card B = 27)
    (a : Fin 10) : Nat.card (MulAction.orbit B a) ≠ 9 := by
  intro h9
  have h9n : (MulAction.orbit B a).ncard = 9 := h9
  have hK1 : Nat.card (MulAction.stabilizer B a) = 3 := by
    have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup B a)
    rw [Nat.card_prod, hB27, h9] at h
    omega
  have hfix : ∀ p, p ∉ MulAction.orbit B a → ∀ g : B, g • p = p := by
    intro p hp g
    have hdisj : Disjoint (MulAction.orbit B p) (MulAction.orbit B a) := by
      rcases MulAction.orbit.eq_or_disjoint (G := B) p a with h | h
      · rw [← h] at hp
        exact absurd ((MulAction.mem_orbit_self p : p ∈ MulAction.orbit B p)) hp
      · exact h
    have hsub : MulAction.orbit B p ⊆ (MulAction.orbit B a)ᶜ := by
      intro q hq
      exact Set.disjoint_left.mp hdisj hq
    have hcompl : ((MulAction.orbit B a)ᶜ).ncard = 1 := by
      rw [Set.ncard_compl, h9n, Nat.card_fin]
    have hle : Nat.card (MulAction.orbit B p) ≤ 1 := by
      rw [Nat.card_coe_set_eq]
      calc (MulAction.orbit B p).ncard ≤ ((MulAction.orbit B a)ᶜ).ncard :=
            Set.ncard_le_ncard hsub
        _ = 1 := hcompl
    haveI : Nonempty (MulAction.orbit B p) :=
      ⟨⟨p, (MulAction.mem_orbit_self p : p ∈ MulAction.orbit B p)⟩⟩
    have hpos : 1 ≤ Nat.card (MulAction.orbit B p) := Nat.card_pos
    have h1 : Nat.card (MulAction.orbit B p) = 1 := le_antisymm hle hpos
    haveI : Subsingleton (MulAction.orbit B p) :=
      Finite.card_le_one_iff_subsingleton.mp (le_of_eq h1)
    exact congrArg Subtype.val (Subsingleton.elim
      (⟨g • p, MulAction.mem_orbit p g⟩ : MulAction.orbit B p)
      ⟨p, (MulAction.mem_orbit_self p : p ∈ MulAction.orbit B p)⟩)
  have hsub : Subsingleton (MulAction.stabilizer B a) := by
    constructor
    intro b c
    apply Subtype.ext
    apply Subtype.ext
    ext p
    by_cases hp : p ∈ MulAction.orbit B a
    · have hb : (b : Equiv.Perm (Fin 10)) p = p :=
        smul_eq_of_mem_stabilizer_of_mem_orbit hB hp b.2
      have hc : (c : Equiv.Perm (Fin 10)) p = p :=
        smul_eq_of_mem_stabilizer_of_mem_orbit hB hp c.2
      rw [hb, hc]
    · have hb : (b : Equiv.Perm (Fin 10)) p = p := hfix p hp b
      have hc : (c : Equiv.Perm (Fin 10)) p = p := hfix p hp c
      rw [hb, hc]
  have hcard1 : Nat.card (MulAction.stabilizer B a) = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨1⟩⟩
  rw [hcard1] at hK1
  omega

private theorem exists_orbit_card_three (hB : CFSG.Open.IsElemAbelian 3 B)
    (hB27 : Nat.card B = 27) : ∃ a : Fin 10, Nat.card (MulAction.orbit B a) = 3 := by
  have hBne : B ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hB27
    omega
  haveI : Nontrivial B :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hB27]; norm_num)
  obtain ⟨g, hg1⟩ := exists_ne (1 : B)
  have hgm : ∃ a : Fin 10, g • a ≠ a := by
    by_contra h
    push Not at h
    exact hg1 (Subtype.ext (Equiv.ext h))
  obtain ⟨a, ha⟩ := hgm
  refine ⟨a, ?_⟩
  rcases card_orbit_eq_one_or_three_or_nine hB27 a with h | h | h
  · exact absurd h (card_orbit_ne_one_of_smul_ne ha)
  · exact h
  · exact absurd h (card_orbit_ne_nine hB hB27 a)

private theorem exists_second_orbit (hB : CFSG.Open.IsElemAbelian 3 B)
    (hB27 : Nat.card B = 27) {a : Fin 10}
    (ha3 : Nat.card (MulAction.orbit B a) = 3) :
    ∃ b : Fin 10, Nat.card (MulAction.orbit B b) = 3 ∧
      b ∉ MulAction.orbit B a ∧
      3 ≤ Nat.card ↥(MulAction.stabilizer B a ⊓ MulAction.stabilizer B b) := by
  have ha3n : (MulAction.orbit B a).ncard = 3 := ha3
  have hK1 : Nat.card (MulAction.stabilizer B a) = 9 := by
    have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup B a)
    rw [Nat.card_prod, hB27, ha3] at h
    omega
  haveI : Nontrivial (MulAction.stabilizer B a) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hK1]; norm_num)
  obtain ⟨k, hk1⟩ := exists_ne (1 : MulAction.stabilizer B a)
  have hkm : ∃ b : Fin 10, (k : B) • b ≠ b := by
    by_contra h
    push Not at h
    have hk_eq : (k : B) = 1 := Subtype.ext (Equiv.ext h)
    exact hk1 (Subtype.ext hk_eq)
  obtain ⟨b, hb⟩ := hkm
  have hb_not : b ∉ MulAction.orbit B a := by
    intro hb'
    exact hb (smul_eq_of_mem_stabilizer_of_mem_orbit hB hb' k.2)
  have hb3 : Nat.card (MulAction.orbit B b) = 3 := by
    rcases card_orbit_eq_one_or_three_or_nine hB27 b with h | h | h
    · exact absurd h (card_orbit_ne_one_of_smul_ne (g := (k : B)) hb)
    · exact h
    · exact absurd h (card_orbit_ne_nine hB hB27 b)
  have hb3n : (MulAction.orbit B b).ncard = 3 := hb3
  refine ⟨b, hb3, hb_not, ?_⟩
  have hidx_a : (MulAction.stabilizer B a).index = 3 := by
    rw [MulAction.index_stabilizer]
    exact ha3n
  have hidx_b : (MulAction.stabilizer B b).index = 3 := by
    rw [MulAction.index_stabilizer]
    exact hb3n
  have hidx : (MulAction.stabilizer B a ⊓ MulAction.stabilizer B b).index ≤ 9 := by
    calc (MulAction.stabilizer B a ⊓ MulAction.stabilizer B b).index
        ≤ (MulAction.stabilizer B a).index * (MulAction.stabilizer B b).index :=
          Subgroup.index_inf_le
      _ = 3 * 3 := by rw [hidx_a, hidx_b]
      _ = 9 := by norm_num
  have hmul : Nat.card ↥(MulAction.stabilizer B a ⊓ MulAction.stabilizer B b) *
      (MulAction.stabilizer B a ⊓ MulAction.stabilizer B b).index = 27 := by
    rw [Subgroup.card_mul_index, hB27]
  have h9 : 3 * 9 ≤ Nat.card ↥(MulAction.stabilizer B a ⊓ MulAction.stabilizer B b) * 9 := by
    calc 3 * 9 = 27 := by norm_num
      _ = Nat.card ↥(MulAction.stabilizer B a ⊓ MulAction.stabilizer B b) *
            (MulAction.stabilizer B a ⊓ MulAction.stabilizer B b).index := hmul.symm
      _ ≤ Nat.card ↥(MulAction.stabilizer B a ⊓ MulAction.stabilizer B b) * 9 :=
            Nat.mul_le_mul_left _ hidx
  exact Nat.le_of_mul_le_mul_right h9 (by norm_num)

private theorem exists_third_orbit (hB : CFSG.Open.IsElemAbelian 3 B)
    (hB27 : Nat.card B = 27) {a b : Fin 10}
    (hK : 3 ≤ Nat.card ↥(MulAction.stabilizer B a ⊓ MulAction.stabilizer B b)) :
    ∃ c : Fin 10, Nat.card (MulAction.orbit B c) = 3 ∧
      c ∉ MulAction.orbit B a ∧ c ∉ MulAction.orbit B b := by
  have hKne : MulAction.stabilizer B a ⊓ MulAction.stabilizer B b ≠ ⊥ := by
    intro hbot
    rw [Subgroup.eq_bot_iff_card] at hbot
    omega
  haveI : Nontrivial ↥(MulAction.stabilizer B a ⊓ MulAction.stabilizer B b) :=
    Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨k, hk1⟩ := exists_ne (1 : ↥(MulAction.stabilizer B a ⊓ MulAction.stabilizer B b))
  have hkm : ∃ c : Fin 10, (k : B) • c ≠ c := by
    by_contra h
    push Not at h
    have hk_eq : (k : B) = 1 := Subtype.ext (Equiv.ext h)
    exact hk1 (Subtype.ext hk_eq)
  obtain ⟨c, hc⟩ := hkm
  have hc_not_a : c ∉ MulAction.orbit B a := by
    intro hc'
    exact hc (smul_eq_of_mem_stabilizer_of_mem_orbit hB hc' (k.2).1)
  have hc_not_b : c ∉ MulAction.orbit B b := by
    intro hc'
    exact hc (smul_eq_of_mem_stabilizer_of_mem_orbit hB hc' (k.2).2)
  have hc3 : Nat.card (MulAction.orbit B c) = 3 := by
    rcases card_orbit_eq_one_or_three_or_nine hB27 c with h | h | h
    · exact absurd h (card_orbit_ne_one_of_smul_ne (g := (k : B)) hc)
    · exact h
    · exact absurd h (card_orbit_ne_nine hB hB27 c)
  exact ⟨c, hc3, hc_not_a, hc_not_b⟩

private theorem smul_eq_of_notMem_three_orbits {a b c p : Fin 10}
    (ha3 : Nat.card (MulAction.orbit B a) = 3)
    (hb3 : Nat.card (MulAction.orbit B b) = 3)
    (hc3 : Nat.card (MulAction.orbit B c) = 3)
    (hab : Disjoint (MulAction.orbit B a) (MulAction.orbit B b))
    (hac : Disjoint (MulAction.orbit B a) (MulAction.orbit B c))
    (hbc : Disjoint (MulAction.orbit B b) (MulAction.orbit B c))
    (hp1 : p ∉ MulAction.orbit B a) (hp2 : p ∉ MulAction.orbit B b)
    (hp3 : p ∉ MulAction.orbit B c) (g : B) : g • p = p := by
  have ha3n : (MulAction.orbit B a).ncard = 3 := ha3
  have hb3n : (MulAction.orbit B b).ncard = 3 := hb3
  have hc3n : (MulAction.orbit B c).ncard = 3 := hc3
  have hdisj_a : Disjoint (MulAction.orbit B p) (MulAction.orbit B a) := by
    rcases MulAction.orbit.eq_or_disjoint (G := B) p a with h | h
    · rw [← h] at hp1
      exact absurd ((MulAction.mem_orbit_self p : p ∈ MulAction.orbit B p)) hp1
    · exact h
  have hdisj_b : Disjoint (MulAction.orbit B p) (MulAction.orbit B b) := by
    rcases MulAction.orbit.eq_or_disjoint (G := B) p b with h | h
    · rw [← h] at hp2
      exact absurd ((MulAction.mem_orbit_self p : p ∈ MulAction.orbit B p)) hp2
    · exact h
  have hdisj_c : Disjoint (MulAction.orbit B p) (MulAction.orbit B c) := by
    rcases MulAction.orbit.eq_or_disjoint (G := B) p c with h | h
    · rw [← h] at hp3
      exact absurd ((MulAction.mem_orbit_self p : p ∈ MulAction.orbit B p)) hp3
    · exact h
  have hsub : MulAction.orbit B p ⊆
      (MulAction.orbit B a ∪ MulAction.orbit B b ∪ MulAction.orbit B c)ᶜ := by
    intro q hq
    simp only [Set.mem_compl_iff, Set.mem_union, not_or]
    exact ⟨⟨Set.disjoint_left.mp hdisj_a hq, Set.disjoint_left.mp hdisj_b hq⟩,
      Set.disjoint_left.mp hdisj_c hq⟩
  have h1 : (MulAction.orbit B a ∪ MulAction.orbit B b).ncard = 6 := by
    rw [Set.ncard_union_eq hab, ha3n, hb3n]
  have hU : (MulAction.orbit B a ∪ MulAction.orbit B b ∪ MulAction.orbit B c).ncard = 9 := by
    rw [Set.ncard_union_eq (Set.disjoint_union_left.mpr ⟨hac, hbc⟩), h1, hc3n]
  have hcompl : (MulAction.orbit B a ∪ MulAction.orbit B b ∪ MulAction.orbit B c)ᶜ.ncard = 1 := by
    rw [Set.ncard_compl, hU, Nat.card_fin]
  have hle : Nat.card (MulAction.orbit B p) ≤ 1 := by
    rw [Nat.card_coe_set_eq]
    calc (MulAction.orbit B p).ncard ≤
          (MulAction.orbit B a ∪ MulAction.orbit B b ∪ MulAction.orbit B c)ᶜ.ncard :=
          Set.ncard_le_ncard hsub
      _ = 1 := hcompl
  haveI : Nonempty (MulAction.orbit B p) :=
    ⟨⟨p, (MulAction.mem_orbit_self p : p ∈ MulAction.orbit B p)⟩⟩
  have hpos : 1 ≤ Nat.card (MulAction.orbit B p) := Nat.card_pos
  have h1p : Nat.card (MulAction.orbit B p) = 1 := le_antisymm hle hpos
  haveI : Subsingleton (MulAction.orbit B p) :=
    Finite.card_le_one_iff_subsingleton.mp (le_of_eq h1p)
  exact congrArg Subtype.val (Subsingleton.elim
    (⟨g • p, MulAction.mem_orbit p g⟩ : MulAction.orbit B p)
    ⟨p, (MulAction.mem_orbit_self p : p ∈ MulAction.orbit B p)⟩)

private theorem exists_three_orbits (hB : CFSG.Open.IsElemAbelian 3 B)
    (hB27 : Nat.card B = 27) :
    ∃ a b c : Fin 10,
      Nat.card (MulAction.orbit B a) = 3 ∧ Nat.card (MulAction.orbit B b) = 3 ∧
      Nat.card (MulAction.orbit B c) = 3 ∧
      Disjoint (MulAction.orbit B a) (MulAction.orbit B b) ∧
      Disjoint (MulAction.orbit B a) (MulAction.orbit B c) ∧
      Disjoint (MulAction.orbit B b) (MulAction.orbit B c) ∧
      (∀ p, p ∉ MulAction.orbit B a → p ∉ MulAction.orbit B b →
        p ∉ MulAction.orbit B c → ∀ g : B, g • p = p) := by
  obtain ⟨a, ha3⟩ := exists_orbit_card_three hB hB27
  obtain ⟨b, hb3, hb_not, hK⟩ := exists_second_orbit hB hB27 ha3
  obtain ⟨c, hc3, hc_not_a, hc_not_b⟩ := exists_third_orbit hB hB27 hK
  have hab : Disjoint (MulAction.orbit B a) (MulAction.orbit B b) := by
    rcases MulAction.orbit.eq_or_disjoint (G := B) a b with h | h
    · rw [h] at hb_not
      exact absurd ((MulAction.mem_orbit_self b : b ∈ MulAction.orbit B b)) hb_not
    · exact h
  have hac : Disjoint (MulAction.orbit B a) (MulAction.orbit B c) := by
    rcases MulAction.orbit.eq_or_disjoint (G := B) a c with h | h
    · rw [h] at hc_not_a
      exact absurd ((MulAction.mem_orbit_self c : c ∈ MulAction.orbit B c)) hc_not_a
    · exact h
  have hbc : Disjoint (MulAction.orbit B b) (MulAction.orbit B c) := by
    rcases MulAction.orbit.eq_or_disjoint (G := B) b c with h | h
    · rw [h] at hc_not_b
      exact absurd ((MulAction.mem_orbit_self c : c ∈ MulAction.orbit B c)) hc_not_b
    · exact h
  exact ⟨a, b, c, ha3, hb3, hc3, hab, hac, hbc,
    fun p hp1 hp2 hp3 g => smul_eq_of_notMem_three_orbits ha3 hb3 hc3 hab hac hbc hp1 hp2 hp3 g⟩

private theorem disjoint_support_of_subset {u v : Equiv.Perm (Fin 10)} {S T : Set (Fin 10)}
    (hu : (u.support : Set (Fin 10)) ⊆ S) (hv : (v.support : Set (Fin 10)) ⊆ T)
    (hST : Disjoint S T) : Disjoint u.support v.support := by
  rw [← Finset.disjoint_coe]
  exact Disjoint.mono hu hv hST

private theorem exists_threeCycle_support_subset (hB : CFSG.Open.IsElemAbelian 3 B)
    (hB27 : Nat.card B = 27) {a b c : Fin 10}
    (ha3 : Nat.card (MulAction.orbit B a) = 3)
    (hb3 : Nat.card (MulAction.orbit B b) = 3)
    (hc3 : Nat.card (MulAction.orbit B c) = 3)
    (hfix : ∀ p, p ∉ MulAction.orbit B a → p ∉ MulAction.orbit B b →
      p ∉ MulAction.orbit B c → ∀ g : B, g • p = p) :
    ∃ x ∈ B, x.IsThreeCycle ∧ (x.support : Set (Fin 10)) ⊆ MulAction.orbit B a := by
  have ha3n : (MulAction.orbit B a).ncard = 3 := ha3
  have hb3n : (MulAction.orbit B b).ncard = 3 := hb3
  have hc3n : (MulAction.orbit B c).ncard = 3 := hc3
  have hidx_b : (MulAction.stabilizer B b).index = 3 := by
    rw [MulAction.index_stabilizer]
    exact hb3n
  have hidx_c : (MulAction.stabilizer B c).index = 3 := by
    rw [MulAction.index_stabilizer]
    exact hc3n
  have hidx : (MulAction.stabilizer B b ⊓ MulAction.stabilizer B c).index ≤ 9 := by
    calc (MulAction.stabilizer B b ⊓ MulAction.stabilizer B c).index
        ≤ (MulAction.stabilizer B b).index * (MulAction.stabilizer B c).index :=
          Subgroup.index_inf_le
      _ = 3 * 3 := by rw [hidx_b, hidx_c]
      _ = 9 := by norm_num
  have hmul : Nat.card ↥(MulAction.stabilizer B b ⊓ MulAction.stabilizer B c) *
      (MulAction.stabilizer B b ⊓ MulAction.stabilizer B c).index = 27 := by
    rw [Subgroup.card_mul_index, hB27]
  have hcardK : 3 ≤ Nat.card ↥(MulAction.stabilizer B b ⊓ MulAction.stabilizer B c) := by
    have h9 : 3 * 9 ≤ Nat.card ↥(MulAction.stabilizer B b ⊓ MulAction.stabilizer B c) * 9 := by
      calc 3 * 9 = 27 := by norm_num
        _ = Nat.card ↥(MulAction.stabilizer B b ⊓ MulAction.stabilizer B c) *
              (MulAction.stabilizer B b ⊓ MulAction.stabilizer B c).index := hmul.symm
        _ ≤ Nat.card ↥(MulAction.stabilizer B b ⊓ MulAction.stabilizer B c) * 9 :=
              Nat.mul_le_mul_left _ hidx
    exact Nat.le_of_mul_le_mul_right h9 (by norm_num)
  have hKne : MulAction.stabilizer B b ⊓ MulAction.stabilizer B c ≠ ⊥ := by
    intro hbot
    rw [Subgroup.eq_bot_iff_card] at hbot
    omega
  haveI : Nontrivial ↥(MulAction.stabilizer B b ⊓ MulAction.stabilizer B c) :=
    Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨k, hk1⟩ := exists_ne (1 : ↥(MulAction.stabilizer B b ⊓ MulAction.stabilizer B c))
  let x : Equiv.Perm (Fin 10) := (k : B)
  have hxne : x ≠ 1 := by
    intro h
    exact hk1 (Subtype.ext (Subtype.ext h))
  have hx3 : x ^ 3 = 1 := by
    simpa [x] using hB.2 (k : B) (k : B).2
  have hsup : (x.support : Set (Fin 10)) ⊆ MulAction.orbit B a := by
    intro p hp
    by_contra hpout
    rcases em (p ∈ MulAction.orbit B b) with hpb | hpb
    · have h : x p = p := smul_eq_of_mem_stabilizer_of_mem_orbit hB hpb (k.2).1
      exact (Equiv.Perm.mem_support.mp hp) h
    · rcases em (p ∈ MulAction.orbit B c) with hpc | hpc
      · have h : x p = p := smul_eq_of_mem_stabilizer_of_mem_orbit hB hpc (k.2).2
        exact (Equiv.Perm.mem_support.mp hp) h
      · have h : x p = p := hfix p hpout hpb hpc (k : B)
        exact (Equiv.Perm.mem_support.mp hp) h
  have hcard_le : x.support.card ≤ 3 := by
    calc x.support.card = ((x.support : Set (Fin 10))).ncard := (Set.ncard_coe_finset _).symm
      _ ≤ (MulAction.orbit B a).ncard := Set.ncard_le_ncard hsup
      _ = 3 := ha3n
  have hcard_ge : 2 ≤ x.support.card := Equiv.Perm.two_le_card_support_of_ne_one hxne
  have hcard3 : x.support.card = 3 := by
    rcases Nat.lt_or_ge x.support.card 3 with h | h
    · have h2 : x.support.card = 2 := by omega
      have hswap : x.IsSwap := Equiv.Perm.card_support_eq_two.mp h2
      have hdvd : orderOf x ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hx3
      rw [hswap.orderOf] at hdvd
      norm_num at hdvd
    · exact le_antisymm hcard_le h
  exact ⟨x, (k : B).2, card_support_eq_three_iff.mp hcard3, hsup⟩

theorem exists_threeCycles {B : Subgroup (Equiv.Perm (Fin 10))}
    (hB : CFSG.Open.IsElemAbelian 3 B) (hB27 : Nat.card B = 27) :
    ∃ x : Fin 3 → Equiv.Perm (Fin 10), (∀ i, x i ∈ B) ∧ (∀ i, (x i).IsThreeCycle) ∧
      ∀ i j, i ≠ j → Disjoint (x i).support (x j).support := by
  obtain ⟨a, b, c, ha3, hb3, hc3, hab, hac, hbc, hfix⟩ := exists_three_orbits hB hB27
  obtain ⟨x0, hx0B, hx0, hsup0⟩ :=
    exists_threeCycle_support_subset hB hB27 ha3 hb3 hc3 hfix
  obtain ⟨x1, hx1B, hx1, hsup1⟩ :=
    exists_threeCycle_support_subset hB hB27 hb3 ha3 hc3
      (fun p hp1 hp2 hp3 => hfix p hp2 hp1 hp3)
  obtain ⟨x2, hx2B, hx2, hsup2⟩ :=
    exists_threeCycle_support_subset hB hB27 hc3 ha3 hb3
      (fun p hp1 hp2 hp3 => hfix p hp2 hp3 hp1)
  let x : Fin 3 → Equiv.Perm (Fin 10) := ![x0, x1, x2]
  refine ⟨x, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · simpa [x] using hx0B
    · simpa [x] using hx1B
    · simpa [x] using hx2B
  · intro i
    fin_cases i
    · simpa [x] using hx0
    · simpa [x] using hx1
    · simpa [x] using hx2
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · simpa [x] using disjoint_support_of_subset hsup0 hsup1 hab
    · simpa [x] using disjoint_support_of_subset hsup0 hsup2 hac
    · simpa [x] using disjoint_support_of_subset hsup1 hsup0 hab.symm
    · exact (hij rfl).elim
    · simpa [x] using disjoint_support_of_subset hsup1 hsup2 hbc
    · simpa [x] using disjoint_support_of_subset hsup2 hsup0 hac.symm
    · simpa [x] using disjoint_support_of_subset hsup2 hsup1 hbc.symm
    · exact (hij rfl).elim

end CFSG.RankThree.PartTwo.KFacts.KF163A10
