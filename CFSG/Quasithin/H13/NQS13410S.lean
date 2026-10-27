module

public import CFSG.Quasithin.H13.NQS13410L

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def l3Blist : List L3.Γ :=
  [⟨!![1, 0, 0; 0, 1, 0; 0, 0, 1], by decide⟩, ⟨!![1, 0, 0; 0, 1, 1; 0, 0, 1], by decide⟩,
    ⟨!![1, 0, 1; 0, 1, 0; 0, 0, 1], by decide⟩, ⟨!![1, 0, 1; 0, 1, 1; 0, 0, 1], by decide⟩,
    ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by decide⟩, ⟨!![1, 1, 0; 0, 1, 1; 0, 0, 1], by decide⟩,
    ⟨!![1, 1, 1; 0, 1, 0; 0, 0, 1], by decide⟩, ⟨!![1, 1, 1; 0, 1, 1; 0, 0, 1], by decide⟩]

theorem l3B_mul : ∀ a ∈ l3Blist, ∀ b ∈ l3Blist, a * b ∈ l3Blist := by decide +kernel

theorem l3B_inv : ∀ a ∈ l3Blist, a⁻¹ ∈ l3Blist := by decide +kernel

theorem l3B_one : (1 : L3.Γ) ∈ l3Blist := by decide +kernel

theorem l3B_nodup : l3Blist.Nodup := by decide +kernel

@[expose] def l3B : Subgroup L3.Γ where
  carrier := {g | g ∈ l3Blist}
  mul_mem' := fun {a b} ha hb => l3B_mul a ha b hb
  one_mem' := l3B_one
  inv_mem' := fun {a} ha => l3B_inv a ha

@[expose] def l3e1 : L3.Vec := ![1, 0, 0]

@[expose] def l3e2 : L3.Vec := ![0, 1, 0]

@[expose] def l3Stab (p : L3.Vec) : Subgroup L3.Γ where
  carrier := {g | L3.act g p = p}
  mul_mem' := fun {a b} ha hb => by
    show L3.act (a * b) p = p
    rw [L3.act_mul, show L3.act b p = p from hb, show L3.act a p = p from ha]
  one_mem' := L3.act_one p
  inv_mem' := fun {a} ha => by
    show L3.act a⁻¹ p = p
    conv_lhs => rw [← show L3.act a p = p from ha]
    exact L3.act_inv_act a p

@[expose] def InL3P2 (g : L3.Γ) : Prop := L3.act g l3e1 2 = 0 ∧ L3.act g l3e2 2 = 0

instance : DecidablePred InL3P2 := fun g => by unfold InL3P2; infer_instance

theorem l3P2_mul : ∀ a b : L3.Γ, InL3P2 a → InL3P2 b → InL3P2 (a * b) := by decide +kernel

theorem l3P2_inv : ∀ a : L3.Γ, InL3P2 a → InL3P2 a⁻¹ := by decide +kernel

@[expose] def l3P2 : Subgroup L3.Γ where
  carrier := {g | InL3P2 g}
  mul_mem' := fun {a b} ha hb => l3P2_mul a b ha hb
  one_mem' := by decide
  inv_mem' := fun {a} ha => l3P2_inv a ha

theorem mem_l3Stab {p : L3.Vec} {g : L3.Γ} : g ∈ l3Stab p ↔ L3.act g p = p := Iff.rfl

theorem mem_l3P2 {g : L3.Γ} : g ∈ l3P2 ↔ InL3P2 g := Iff.rfl

theorem l3B_le_P1 : ∀ g ∈ l3Blist, L3.act g l3e1 = l3e1 := by decide +kernel

theorem l3B_le_P2 : ∀ g ∈ l3Blist, InL3P2 g := by decide +kernel

theorem l3_fixB : ∀ p : L3.Vec, p ≠ 0 → (∀ g ∈ l3Blist, L3.act g p = p) → p = l3e1 := by
  decide +kernel

theorem l3Stab_card' : ∀ p : L3.Vec, p ≠ 0 →
    (Finset.univ.filter fun g : L3.Γ => L3.act g p = p).card = 24 := by decide +kernel

theorem l3P2_card' : (Finset.univ.filter fun g : L3.Γ => InL3P2 g).card = 24 := by decide +kernel

theorem l3_word : ∀ g : L3.Γ, L3.act g l3e1 ≠ l3e1 → ¬ InL3P2 g → ∃ b ∈ l3Blist, ∃ b' ∈ l3Blist,
    InL3P2 (g * b * g⁻¹ * b' * (g * b * g⁻¹)) ∧ g * b * g⁻¹ * b' * (g * b * g⁻¹) ∉ l3Blist := by
  decide +kernel

theorem card_l3B : Nat.card ↥l3B = 8 := by
  classical
  rw [← (show l3Blist.length = 8 from rfl), ← List.toFinset_card_of_nodup l3B_nodup,
    ← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun g => by rw [List.mem_toFinset]; rfl)

theorem card_l3Stab {p : L3.Vec} (hp : p ≠ 0) : Nat.card ↥(l3Stab p) = 24 := by
  classical
  rw [← l3Stab_card' p hp, ← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun g => by simp [mem_l3Stab])

theorem card_l3P2 : Nat.card ↥l3P2 = 24 := by
  classical
  rw [← l3P2_card', ← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun g => by simp [mem_l3P2])

theorem card_l3Γ : Nat.card L3.Γ = 168 := HSType.card_SL_three_two

theorem l3Stab_max {p : L3.Vec} (hp : p ≠ 0) {Y : Subgroup L3.Γ} (hY : l3Stab p ≤ Y) :
    Y = l3Stab p ∨ Y = ⊤ := by
  have h1 := relIndex_mul_relIndex (l3Stab p) Y ⊤ hY le_top
  have h2 : (l3Stab p).relIndex ⊤ = 7 := by
    rw [relIndex_top_right]
    have := Subgroup.card_mul_index (l3Stab p)
    rw [card_l3Stab hp, card_l3Γ] at this
    omega
  rw [h2] at h1
  rcases (Nat.prime_mul_iff.mp (h1 ▸ (by norm_num : Nat.Prime 7))) with ⟨-, hb⟩ | ⟨-, ha⟩
  · right
    rw [relIndex_top_right, index_eq_one] at hb
    exact hb
  · left
    exact le_antisymm (relIndex_eq_one.mp ha) hY

theorem l3P2_le_of {Y : Subgroup L3.Γ} (hB : l3B ≤ Y) (hY : ¬ Y ≤ l3Stab l3e1) : l3P2 ≤ Y := by
  have hw : ∃ w ∈ Y, w ∈ l3P2 ∧ w ∉ l3B := by
    obtain ⟨g, hgY, hgP⟩ := IsConcreteLE.not_le_iff_exists.1 hY
    by_cases hg2 : InL3P2 g
    · exact ⟨g, hgY, hg2, fun h => hgP (l3B_le_P1 g h)⟩
    · obtain ⟨b, hb, b', hb', h2, hB'⟩ := l3_word g hgP hg2
      have hx : g * b * g⁻¹ ∈ Y := mul_mem (mul_mem hgY (hB hb)) (inv_mem hgY)
      exact ⟨_, mul_mem (mul_mem hx (hB hb')) hx, h2, hB'⟩
  obtain ⟨w, hwY, hwP, hwB⟩ := hw
  have hBP : l3B ≤ l3P2 := fun g hg => l3B_le_P2 g hg
  have hBY2 : l3B ≤ Y ⊓ l3P2 := le_inf hB hBP
  have h1 := relIndex_mul_relIndex l3B (Y ⊓ l3P2) l3P2 hBY2 inf_le_right
  have h3 : l3B.relIndex l3P2 = 3 := by
    have h4 := relIndex_mul_card l3B l3P2
    rw [inf_eq_left.2 hBP, card_l3B, card_l3P2] at h4
    omega
  rw [h3] at h1
  rcases (Nat.prime_mul_iff.mp (h1 ▸ (by norm_num : Nat.Prime 3))) with ⟨-, hb⟩ | ⟨-, ha⟩
  · exact (relIndex_eq_one.mp hb).trans inf_le_left
  · exact absurd (relIndex_eq_one.mp ha (mem_inf.2 ⟨hwY, hwP⟩)) hwB

variable {G : Type} [Group G]

namespace L3Coords

variable {K X : Subgroup G}

@[expose] noncomputable def conj (C : L3Coords K X) (h : L3.Γ) : L3Coords K X where
  ρ := (MulAut.conj h⁻¹).toMonoidHom.comp C.ρ
  c := fun x => L3.act h⁻¹ (C.c x)
  c_inj := fun x y hxy => C.c_inj (by
    have := congrArg (L3.act h) hxy
    simpa only [L3.act_act_inv] using this)
  c_one := by rw [C.c_one, L3.act_zero]
  equiv := fun g x => by
    show L3.act h⁻¹ (C.c (conjAct X g x)) = L3.act (h⁻¹ * C.ρ g * h⁻¹⁻¹) (L3.act h⁻¹ (C.c x))
    rw [C.equiv, inv_inv, L3.act_mul, L3.act_mul, L3.act_act_inv]
  ker := fun g => by
    show h⁻¹ * C.ρ g * h⁻¹⁻¹ = 1 ↔ _
    rw [← C.ker g]
    constructor
    · intro h1
      have := congrArg (fun γ => h * γ * h⁻¹) h1
      simpa [mul_assoc] using this
    · intro h1
      rw [h1]
      group
  image_K := fun γ => by
    obtain ⟨g, hgK, hg⟩ := C.image_K (h * γ * h⁻¹)
    refine ⟨g, hgK, ?_⟩
    show h⁻¹ * C.ρ g * h⁻¹⁻¹ = γ
    rw [hg]
    group

theorem conj_ρ (C : L3Coords K X) (h : L3.Γ) (g : ↥(normalizer (X : Set G))) :
    (C.conj h).ρ g = h⁻¹ * C.ρ g * h := by
  show h⁻¹ * C.ρ g * h⁻¹⁻¹ = _
  rw [inv_inv]

theorem exists_conj_eq [Finite G] (C : L3Coords K X) {T : Subgroup G}
    (hKX : K ≤ normalizer (X : Set G)) (hT2 : IsPGroup 2 ↥(T ⊓ K)) :
    ∃ C' : L3Coords K X, ∀ s : ↥(normalizer (X : Set G)), (s : G) ∈ T ⊓ K → C'.ρ s ∈ l3B := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P : Subgroup L3.Γ := ((T ⊓ K).subgroupOf (normalizer (X : Set G))).map C.ρ with hP
  have hP2 : IsPGroup 2 ↥P :=
    (hT2.of_equiv (subgroupOfEquivOfLe (inf_le_right.trans hKX)).symm).map C.ρ
  obtain ⟨Q, hPQ⟩ := hP2.exists_le_sylow
  have hB2 : IsPGroup 2 ↥l3B := IsPGroup.of_card (n := 3) (by rw [card_l3B]; norm_num)
  obtain ⟨QB, hBQ⟩ := hB2.exists_le_sylow
  have hQB : (QB : Subgroup L3.Γ) = l3B := by
    obtain ⟨k, hk⟩ := QB.isPGroup'.exists_card_eq
    have hdvd : Nat.card ↥(QB : Subgroup L3.Γ) ∣ 168 :=
      card_l3Γ ▸ Subgroup.card_subgroup_dvd_card _
    rw [hk] at hdvd
    have hk3 : k ≤ 3 := by
      by_contra h
      have : 2 ^ 4 ∣ 168 := (pow_dvd_pow 2 (by omega)).trans hdvd
      norm_num at this
    refine (eq_of_le_of_card_ge hBQ ?_).symm
    rw [hk, card_l3B]
    calc 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hk3
      _ = 8 := by norm_num
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq L3.Γ QB Q
  refine ⟨C.conj h, fun s hs => ?_⟩
  rw [conj_ρ]
  have hsP : C.ρ s ∈ P := ⟨s, mem_subgroupOf.2 hs, rfl⟩
  have hsQ : C.ρ s ∈ (Q : Subgroup L3.Γ) := hPQ hsP
  rw [← hh, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, hQB] at hsQ
  have e : (MulAut.conj h)⁻¹ • C.ρ s = h⁻¹ * C.ρ s * h := by
    rw [MulAut.smul_def, ← map_inv, MulAut.conj_apply, inv_inv]
  rwa [e] at hsQ

end L3Coords

end CFSG.Quasithin.H13.NQS134
