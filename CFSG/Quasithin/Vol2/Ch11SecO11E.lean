module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246A7Perm

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.O11

open Equiv CFSG.QuasithinUnique.L246A7

@[expose] def presSub {α : Type*} (p : α → Prop) : Subgroup (Perm α) where
  carrier := {σ | ∀ x, p (σ x) ↔ p x}
  one_mem' := fun _ => Iff.rfl
  mul_mem' := fun {a b} ha hb => by
    show ∀ x, p (a (b x)) ↔ p x
    intro x
    have ha' : ∀ x, p (a x) ↔ p x := ha
    have hb' : ∀ x, p (b x) ↔ p x := hb
    exact (ha' (b x)).trans (hb' x)
  inv_mem' := fun {a} ha => by
    show ∀ x, p (a⁻¹ x) ↔ p x
    intro x
    have ha' : ∀ x, p (a x) ↔ p x := ha
    have h := ha' (a⁻¹ x)
    have e : a (a⁻¹ x) = x := Equiv.apply_symm_apply a x
    rw [e] at h
    exact h.symm

theorem card_dvd_of_le_presSub {α : Type*} [Fintype α] [DecidableEq α] (p : α → Prop)
    [DecidablePred p] {Y : Subgroup (Perm α)} (hY : Y ≤ presSub p) :
    Nat.card Y ∣ (Fintype.card {a // p a}).factorial * (Fintype.card {a // ¬ p a}).factorial := by
  have hle : presSub p ≤ (Perm.subtypeCongrHom p).range := by
    intro σ hσ
    have hσ' : ∀ x, p (σ x) ↔ p x := hσ
    refine ⟨(σ.subtypePerm hσ', σ.subtypePerm fun x => not_congr (hσ' x)), ?_⟩
    ext x
    rw [Perm.subtypeCongrHom_apply, Perm.subtypeCongr.apply]
    split_ifs <;> rfl
  have h1 := Subgroup.card_dvd_of_le (hY.trans hle)
  rw [← Nat.card_eq_fintype_card (α := {a // p a}), ← Nat.card_eq_fintype_card (α := {a // ¬ p a})]
  rwa [← Nat.card_congr (MonoidHom.ofInjective (Perm.subtypeCongrHom_injective p)).toEquiv,
    Nat.card_prod, Nat.card_perm, Nat.card_perm] at h1

theorem eq_top_of_not_dvd_factorial {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (H : Subgroup G) (h : ¬ Nat.card G ∣ H.index.factorial) : H = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H.normalCore with h0 | h0
  · exfalso
    apply h
    have := H.index_normalCore_dvd_factorial_index
    rwa [h0, Subgroup.index_bot] at this
  · exact top_le_iff.mp (h0 ▸ H.normalCore_le)

theorem fin7_forall {P : Fin 7 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4)
    (h5 : P 5) (h6 : P 6) : ∀ x, P x := by
  intro x
  fin_cases x
  exacts [h0, h1, h2, h3, h4, h5, h6]

abbrev G7 : Type := alternatingGroup (Fin 7)

abbrev PstdA : Subgroup G7 := Pstd.subgroupOf (alternatingGroup (Fin 7))

@[expose] def g1A : G7 := ⟨g1, Pstd_le_alt g1_mem⟩

theorem g1A_mem : g1A ∈ PstdA := Subgroup.mem_subgroupOf.mpr g1_mem

theorem card_range_jA : Nat.card jA.range = 360 := by
  have : Nontrivial ↥pts6 := by
    rw [← Fintype.one_lt_card_iff_nontrivial, card_pts6]
    norm_num
  rw [← Nat.card_congr (MonoidHom.ofInjective jA_injective).toEquiv, nat_card_alternatingGroup,
    Nat.card_eq_fintype_card, card_pts6]
  rfl

theorem smul_eq_apply {Y : Subgroup G7} (y : Y) (x : Fin 7) :
    y • x = ((y : G7) : Perm (Fin 7)) x := rfl

theorem apply_mem_orbit_iff {Y : Subgroup G7} {y : G7} (hy : y ∈ Y) (x : Fin 7) :
    (y : Perm (Fin 7)) x ∈ MulAction.orbit Y (6 : Fin 7) ↔ x ∈ MulAction.orbit Y (6 : Fin 7) := by
  simp only [MulAction.mem_orbit_iff, smul_eq_apply]
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨⟨y, hy⟩⁻¹ * g, ?_⟩
    simp [hg]
  · rintro ⟨g, hg⟩
    refine ⟨⟨y, hy⟩ * g, ?_⟩
    simp [hg]

theorem mem_orbit_iff {Y : Subgroup G7} (hP : PstdA ≤ Y) (x : Fin 7) :
    x ∈ MulAction.orbit Y (6 : Fin 7) ↔
      (x.val < 4 ∧ (0 : Fin 7) ∈ MulAction.orbit Y (6 : Fin 7)) ∨
        ((x = 4 ∨ x = 5) ∧ (4 : Fin 7) ∈ MulAction.orbit Y (6 : Fin 7)) ∨ x = 6 := by
  have hs : ∀ z, g1 z ∈ MulAction.orbit Y (6 : Fin 7) ↔ z ∈ MulAction.orbit Y (6 : Fin 7) :=
    apply_mem_orbit_iff (hP g1A_mem)
  have e01 := hs 0
  have e12 := hs 1
  have e23 := hs 2
  have e45 := hs 4
  rw [show g1 0 = 1 by decide +kernel] at e01
  rw [show g1 1 = 2 by decide +kernel] at e12
  rw [show g1 2 = 3 by decide +kernel] at e23
  rw [show g1 4 = 5 by decide +kernel] at e45
  have h6 : (6 : Fin 7) ∈ MulAction.orbit Y (6 : Fin 7) := MulAction.mem_orbit_self 6
  revert x
  refine fin7_forall ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simp
  · simp [e01]
  · simp [e12, e01]
  · simp [e23, e12, e01]
  · simp
  · simp [e45]
  · simp [h6]

theorem preserves_45 {Y : Subgroup G7} (hP : PstdA ≤ Y) (hY : Nat.card Y = 120) :
    ∀ y ∈ Y, ∀ x : Fin 7,
      ((y : Perm (Fin 7)) x = 4 ∨ (y : Perm (Fin 7)) x = 5) ↔ (x = 4 ∨ x = 5) := by
  have hO := mem_orbit_iff hP
  have h6 : (6 : Fin 7) ∈ MulAction.orbit Y (6 : Fin 7) := MulAction.mem_orbit_self 6
  by_cases h0 : (0 : Fin 7) ∈ MulAction.orbit Y (6 : Fin 7) <;>
    by_cases h4 : (4 : Fin 7) ∈ MulAction.orbit Y (6 : Fin 7)
  ·
    exfalso
    have hall : MulAction.orbit Y (6 : Fin 7) = Set.univ := by
      refine Set.eq_univ_of_forall fun x => (hO x).mpr ?_
      simp only [h0, h4, and_true]
      revert x
      decide
    have h7 := (MulAction.stabilizer Y (6 : Fin 7)).index_dvd_card
    rw [MulAction.index_stabilizer, hall, Set.ncard_univ, Nat.card_fin, hY] at h7
    norm_num at h7
  ·
    have hq : ∀ z : Fin 7, (z = 4 ∨ z = 5) ↔ z ∉ MulAction.orbit Y (6 : Fin 7) := by
      intro z
      rw [hO z]
      simp only [h0, h4, and_true, and_false, false_or]
      revert z
      decide
    intro y hy x
    rw [hq, hq]
    exact not_congr (apply_mem_orbit_iff hy x)
  ·
    exfalso
    have hq : ∀ z : Fin 7, z.val < 4 ↔ z ∉ MulAction.orbit Y (6 : Fin 7) := by
      intro z
      rw [hO z]
      simp only [h0, h4, and_true, and_false, false_or]
      revert z
      decide
    have hle : Y.map (alternatingGroup (Fin 7)).subtype ≤ presSub fun z : Fin 7 => z.val < 4 := by
      rintro _ ⟨y, hy, rfl⟩
      show ∀ z : Fin 7, ((y : Perm (Fin 7)) z).val < 4 ↔ z.val < 4
      intro z
      rw [hq, hq]
      exact not_congr (apply_mem_orbit_iff hy z)
    have hd := card_dvd_of_le_presSub _ hle
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hY] at hd
    revert hd
    decide
  ·
    exfalso
    have hfix : ∀ y ∈ Y, (y : Perm (Fin 7)) 6 = 6 := by
      intro y hy
      have h := (hO _).mp ((apply_mem_orbit_iff hy 6).mpr h6)
      simp only [h0, h4, and_false, false_or] at h
      exact h
    have hle : Y ≤ jA.range := fun y hy => mem_range_jA.mpr (hfix y hy)
    have := isSimpleGroup_range_jA
    have hH : Nat.card (Y.subgroupOf jA.range) = 120 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hY]
    have hi : (Y.subgroupOf jA.range).index = 3 := by
      have h := (Y.subgroupOf jA.range).index_mul_card
      rw [hH, card_range_jA] at h
      omega
    have htop := eq_top_of_not_dvd_factorial (Y.subgroupOf jA.range)
      (by rw [card_range_jA, hi]; decide)
    rw [htop, Subgroup.card_top, card_range_jA] at hH
    norm_num at hH

theorem eq_of_card_eq_120 {Y₁ Y₂ : Subgroup G7} (h₁ : PstdA ≤ Y₁) (h₂ : PstdA ≤ Y₂)
    (c₁ : Nat.card Y₁ = 120) (c₂ : Nat.card Y₂ = 120) : Y₁ = Y₂ := by
  have hle : (Y₁ ⊔ Y₂).map (alternatingGroup (Fin 7)).subtype ≤
      presSub fun z : Fin 7 => z = 4 ∨ z = 5 := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact preserves_45 h₁ c₁ y hy
    · rintro _ ⟨y, hy, rfl⟩
      exact preserves_45 h₂ c₂ y hy
  have hd := card_dvd_of_le_presSub _ hle
  rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)] at hd
  have e1 : Fintype.card {a : Fin 7 // a = 4 ∨ a = 5} = 2 := by decide
  have e2 : Fintype.card {a : Fin 7 // ¬ (a = 4 ∨ a = 5)} = 5 := by decide
  rw [e1, e2] at hd
  have h240 : Nat.card ↥(Y₁ ⊔ Y₂) ∣ 240 := hd
  have h2520 : Nat.card ↥(Y₁ ⊔ Y₂) ∣ 2520 := card_alt7 ▸ Subgroup.card_subgroup_dvd_card _
  have h120 : 120 ∣ Nat.card ↥(Y₁ ⊔ Y₂) := c₁ ▸ Subgroup.card_dvd_of_le le_sup_left
  have hg : Nat.gcd 240 2520 = 120 := by norm_num
  have hM : Nat.card ↥(Y₁ ⊔ Y₂) = 120 := Nat.dvd_antisymm (hg ▸ Nat.dvd_gcd h240 h2520) h120
  have e₁ : Y₁ = Y₁ ⊔ Y₂ := Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hM, c₁])
  have e₂ : Y₂ = Y₁ ⊔ Y₂ := Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [hM, c₂])
  exact e₁.trans e₂.symm

end CFSG.Quasithin.Vol2.Ch11.SecS.O11
