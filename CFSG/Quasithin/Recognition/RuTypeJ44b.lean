module

public import CFSG.Quasithin.Recognition.RuTypeJ44a

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped MatrixGroups

theorem mem_closure_pair_of_sq {X : Type*} [Group X] (hX : ∀ y : X, y * y = 1) {p q y : X}
    (hy : y ∈ Subgroup.closure ({p, q} : Set X)) : y = 1 ∨ y = p ∨ y = q ∨ y = p * q := by
  have hinv : ∀ x : X, x⁻¹ = x := fun x => inv_eq_of_mul_eq_one_right (hX x)
  have hc : ∀ a b : X, a * b = b * a := fun a b => by
    calc a * b = (a * b)⁻¹ := (hinv _).symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by rw [hinv, hinv]
  have hp := hX p
  have hq := hX q
  induction hy using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact Or.inr (Or.inl hx)
    · exact Or.inr (Or.inr (Or.inl hx))
  | one => exact Or.inl rfl
  | mul x y _ _ hx hy =>
    rcases hx with hx | hx | hx | hx <;> rcases hy with hy | hy | hy | hy <;> rw [hx, hy]
    · exact Or.inl (mul_one 1)
    · exact Or.inr (Or.inl (one_mul p))
    · exact Or.inr (Or.inr (Or.inl (one_mul q)))
    · exact Or.inr (Or.inr (Or.inr (one_mul _)))
    · exact Or.inr (Or.inl (mul_one p))
    · exact Or.inl hp
    · exact Or.inr (Or.inr (Or.inr rfl))
    · exact Or.inr (Or.inr (Or.inl (by rw [← mul_assoc, hp, one_mul])))
    · exact Or.inr (Or.inr (Or.inl (mul_one q)))
    · exact Or.inr (Or.inr (Or.inr (hc q p)))
    · exact Or.inl hq
    · exact Or.inr (Or.inl (by rw [hc p q, ← mul_assoc, hq, one_mul]))
    · exact Or.inr (Or.inr (Or.inr (mul_one _)))
    · exact Or.inr (Or.inr (Or.inl (by rw [mul_assoc, hc q p, ← mul_assoc, hp, one_mul])))
    · exact Or.inr (Or.inl (by rw [mul_assoc, hq, mul_one]))
    · exact Or.inl (hX _)
  | inv x _ hx => rw [hinv]; exact hx

namespace SL3

theorem zP0_mul_ne_one : zP0 * (x0 * zP0 * x0⁻¹) ≠ 1 := by decide

theorem x0_zP0_ne_one : x0 * zP0 * x0⁻¹ ≠ 1 := by decide

theorem Pl_eq : ∀ g ∈ Pl, ∃ t ∈ P0, g = t ∨ g = t * x0 ∨ g = t * x0 ^ 2 := by
  decide +kernel

end SL3

namespace RuDataM

variable {G : Type} [Group G] (M : RuDataM G) [Finite G]

noncomputable abbrev WR : Subgroup M.R2 := M.W.subgroupOf M.R2

instance WR_normal : M.WR.Normal :=
  ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact M.conj_mem_W (M.R2_le_G2 g.2) hx⟩

noncomputable abbrev R2bar : Type _ := ↥M.R2 ⧸ M.WR

theorem R2bar_sq (y : M.R2bar) : y * y = 1 := by
  induction y using QuotientGroup.induction_on with
  | H r =>
  rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have := M.sq_mem_W_of_R2 r.2
  rw [pow_two] at this
  exact this

omit [Finite G] in
theorem mk_R2bar_eq_iff {r r' : M.R2} :
    (r : M.R2bar) = (r' : M.R2bar) ↔ (r : G)⁻¹ * r' ∈ M.W := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  rfl

noncomputable abbrev abar (k : ℕ) : M.R2bar :=
  ((⟨M.cak k, M.cak_mem_R2 k⟩ : M.R2) : M.R2bar)

noncomputable abbrev Abar : Subgroup M.R2bar :=
  Subgroup.closure {M.abar 0, M.abar 1}

noncomputable abbrev Agrp : Subgroup G :=
  (M.Abar.comap (QuotientGroup.mk' M.WR)).map M.R2.subtype

theorem mem_Agrp {x : G} :
    x ∈ M.Agrp ↔ ∃ hx : x ∈ M.R2, ((⟨x, hx⟩ : M.R2) : M.R2bar) ∈ M.Abar := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem cak_zero : M.cak 0 = M.ael := by
  simp [cak]

theorem mem_Agrp_iff {x : G} :
    x ∈ M.Agrp ↔ x ∈ M.R2 ∧ (x ∈ M.W ∨ (M.cak 0)⁻¹ * x ∈ M.W ∨ (M.cak 1)⁻¹ * x ∈ M.W ∨
      (M.cak 0 * M.cak 1)⁻¹ * x ∈ M.W) := by
  have h01 : M.cak 0 * M.cak 1 ∈ M.R2 := mul_mem (M.cak_mem_R2 0) (M.cak_mem_R2 1)
  have e01 : M.abar 0 * M.abar 1 = ((⟨M.cak 0 * M.cak 1, h01⟩ : M.R2) : M.R2bar) := rfl
  rw [M.mem_Agrp]
  constructor
  · rintro ⟨hx, h⟩
    refine ⟨hx, ?_⟩
    rcases mem_closure_pair_of_sq M.R2bar_sq h with h1 | h1 | h1 | h1
    · left
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
      exact h1
    · right; left
      exact (M.mk_R2bar_eq_iff.mp h1.symm)
    · right; right; left
      exact (M.mk_R2bar_eq_iff.mp h1.symm)
    · right; right; right
      rw [e01] at h1
      exact (M.mk_R2bar_eq_iff.mp h1.symm)
  · rintro ⟨hx, h | h | h | h⟩
    · refine ⟨hx, ?_⟩
      have : ((⟨x, hx⟩ : M.R2) : M.R2bar) = 1 := by
        rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        exact h
      rw [this]
      exact one_mem _
    · refine ⟨hx, ?_⟩
      have : ((⟨x, hx⟩ : M.R2) : M.R2bar) = M.abar 0 :=
        (M.mk_R2bar_eq_iff (r := ⟨M.cak 0, M.cak_mem_R2 0⟩) (r' := ⟨x, hx⟩)).mpr h |>.symm
      rw [this]
      exact Subgroup.subset_closure (Set.mem_insert _ _)
    · refine ⟨hx, ?_⟩
      have : ((⟨x, hx⟩ : M.R2) : M.R2bar) = M.abar 1 :=
        (M.mk_R2bar_eq_iff (r := ⟨M.cak 1, M.cak_mem_R2 1⟩) (r' := ⟨x, hx⟩)).mpr h |>.symm
      rw [this]
      exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    · refine ⟨hx, ?_⟩
      have : ((⟨x, hx⟩ : M.R2) : M.R2bar) = M.abar 0 * M.abar 1 := by
        rw [e01]
        exact ((M.mk_R2bar_eq_iff (r := ⟨M.cak 0 * M.cak 1, h01⟩) (r' := ⟨x, hx⟩)).mpr h).symm
      rw [this]
      exact mul_mem (Subgroup.subset_closure (Set.mem_insert _ _))
        (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))

theorem Agrp_le_R2 : M.Agrp ≤ M.R2 := Subgroup.map_subtype_le _

theorem W_le_Agrp : M.W ≤ M.Agrp := fun _ hx =>
  M.mem_Agrp_iff.mpr ⟨M.S_le_R2 (M.W_le_S hx), Or.inl hx⟩

theorem cak_mem_Agrp_zero : M.cak 0 ∈ M.Agrp :=
  M.mem_Agrp_iff.mpr ⟨M.cak_mem_R2 0, Or.inr (Or.inl (by rw [inv_mul_cancel]; exact one_mem _))⟩

theorem ael_mem_Agrp : M.ael ∈ M.Agrp := by
  rw [← M.cak_zero]
  exact M.cak_mem_Agrp_zero

theorem cak_mem_Agrp_one : M.cak 1 ∈ M.Agrp :=
  M.mem_Agrp_iff.mpr ⟨M.cak_mem_R2 1,
    Or.inr (Or.inr (Or.inl (by rw [inv_mul_cancel]; exact one_mem _)))⟩

theorem cak_mem_Agrp_two : M.cak 2 ∈ M.Agrp := by
  refine M.mem_Agrp_iff.mpr ⟨M.cak_mem_R2 2, Or.inr (Or.inr (Or.inr ?_))⟩
  have h1 := M.sq_mem_W_of_R2 (mul_mem (M.cak_mem_R2 0) (M.cak_mem_R2 1))
  have h2 := M.prod_cak_mem_W
  have e : (M.cak 0 * M.cak 1)⁻¹ * M.cak 2 =
      ((M.cak 0 * M.cak 1) ^ 2)⁻¹ * (M.cak 0 * M.cak 1 * M.cak 2) := by
    rw [pow_two]; group
  rw [e]
  exact mul_mem (inv_mem h1) h2

theorem Agrp_inf_S : M.Agrp ⊓ ruS M.L = M.W := by
  refine le_antisymm ?_ (le_inf M.W_le_Agrp M.W_le_S)
  rintro x ⟨hxA, hxS⟩
  obtain ⟨hxR, h | h | h | h⟩ := M.mem_Agrp_iff.mp hxA
  · exact h
  all_goals exfalso
  ·
    have hc : M.cak 0 ∈ ruS M.L := by
      have e : M.cak 0 = x * ((M.cak 0)⁻¹ * x)⁻¹ := by group
      rw [e]
      exact mul_mem hxS (inv_mem (M.W_le_S h))
    rw [M.mem_S_iff_θ (M.cak_mem_L 0), M.θ_cak] at hc
    simp only [pow_zero, one_mul, inv_one, mul_one] at hc
    exact SL3.zP0_ne_one hc
  · have hc : M.cak 1 ∈ ruS M.L := by
      have e : M.cak 1 = x * ((M.cak 1)⁻¹ * x)⁻¹ := by group
      rw [e]
      exact mul_mem hxS (inv_mem (M.W_le_S h))
    rw [M.mem_S_iff_θ (M.cak_mem_L 1), M.θ_cak] at hc
    simp only [pow_one] at hc
    exact SL3.x0_zP0_ne_one hc
  · have hcL : M.cak 0 * M.cak 1 ∈ M.L := mul_mem (M.cak_mem_L 0) (M.cak_mem_L 1)
    have hc : M.cak 0 * M.cak 1 ∈ ruS M.L := by
      have e : M.cak 0 * M.cak 1 = x * ((M.cak 0 * M.cak 1)⁻¹ * x)⁻¹ := by group
      rw [e]
      exact mul_mem hxS (inv_mem (M.W_le_S h))
    rw [M.mem_S_iff_θ hcL] at hc
    have e : (⟨M.cak 0 * M.cak 1, hcL⟩ : M.L) =
        ⟨M.cak 0, M.cak_mem_L 0⟩ * ⟨M.cak 1, M.cak_mem_L 1⟩ := rfl
    rw [e, map_mul, M.θ_cak, M.θ_cak] at hc
    simp only [pow_zero, one_mul, inv_one, mul_one, pow_one] at hc
    exact SL3.zP0_mul_ne_one hc

theorem exists_Agrp_θ {g : SL(3, ZMod 2)} (hg : g ∈ SL3.R2m) :
    ∃ y ∈ M.Agrp, ∃ hy : y ∈ M.L, M.θ ⟨y, hy⟩ = g := by
  rcases SL3.R2m_elems g hg with rfl | rfl | rfl | rfl
  · exact ⟨1, one_mem _, one_mem _, map_one _⟩
  · exact ⟨M.cak 0, M.cak_mem_Agrp_zero, M.cak_mem_L 0, by rw [M.θ_cak]; simp⟩
  · exact ⟨M.cak 1, M.cak_mem_Agrp_one, M.cak_mem_L 1, by rw [M.θ_cak]; simp⟩
  · exact ⟨M.cak 2, M.cak_mem_Agrp_two, M.cak_mem_L 2, by rw [M.θ_cak]⟩

theorem Agrp_le_L : M.Agrp ≤ M.L :=
  fun _ hx => (mem_pullL.mp (M.Agrp_le_R2 hx)).1

theorem card_Agrp : Nat.card M.Agrp = 2 ^ 11 := by
  set f : M.Agrp →* SL(3, ZMod 2) := M.θ.comp (Subgroup.inclusion M.Agrp_le_L)
  have h := Subgroup.card_ker_mul_card_range f
  have hS : ∀ (x : G) (hx : x ∈ M.L), M.θ ⟨x, hx⟩ = 1 ↔ x ∈ ruS M.L := fun x hx =>
    (M.mem_S_iff_θ hx).symm
  have hker : Nat.card f.ker = Nat.card M.W := by
    rw [← M.Agrp_inf_S]
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1.1, x.1.2, (hS _ _).mp x.2⟩
        invFun := fun y => ⟨⟨y.1, y.2.1⟩, (hS _ _).mpr y.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hrange : f.range = SL3.R2m := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact (mem_pullL.mp (M.Agrp_le_R2 x.2)).2
    · intro g hg
      obtain ⟨y, hy, hyL, hyθ⟩ := M.exists_Agrp_θ hg
      exact ⟨⟨y, hy⟩, hyθ⟩
  rw [hker, hrange, M.card_W, SL3.card_R2m] at h
  exact h.symm.trans (by norm_num)

theorem conj_mem_of_reps {g : G} (hg : g ∈ M.G2)
    (h0 : g * M.cak 0 * g⁻¹ ∈ M.Agrp) (h1 : g * M.cak 1 * g⁻¹ ∈ M.Agrp) {y : G}
    (hy : y ∈ M.Agrp) : g * y * g⁻¹ ∈ M.Agrp := by
  obtain ⟨_, h | h | h | h⟩ := M.mem_Agrp_iff.mp hy
  · exact M.W_le_Agrp (M.conj_mem_W hg h)
  · have e : g * y * g⁻¹ = (g * M.cak 0 * g⁻¹) * (g * ((M.cak 0)⁻¹ * y) * g⁻¹) := by group
    rw [e]
    exact mul_mem h0 (M.W_le_Agrp (M.conj_mem_W hg h))
  · have e : g * y * g⁻¹ = (g * M.cak 1 * g⁻¹) * (g * ((M.cak 1)⁻¹ * y) * g⁻¹) := by group
    rw [e]
    exact mul_mem h1 (M.W_le_Agrp (M.conj_mem_W hg h))
  · have e : g * y * g⁻¹ = (g * M.cak 0 * g⁻¹) * (g * M.cak 1 * g⁻¹) *
        (g * ((M.cak 0 * M.cak 1)⁻¹ * y) * g⁻¹) := by group
    rw [e]
    exact mul_mem (mul_mem h0 h1) (M.W_le_Agrp (M.conj_mem_W hg h))

theorem xel_conj_mem_Agrp {y : G} (hy : y ∈ M.Agrp) :
    (M.xel : G) * y * (M.xel : G)⁻¹ ∈ M.Agrp := by
  refine M.conj_mem_of_reps M.xel_mem_G2 ?_ ?_ hy
  · have e : (M.xel : G) * M.cak 0 * (M.xel : G)⁻¹ = M.cak 1 := by simp [cak]
    rw [e]
    exact M.cak_mem_Agrp_one
  · have e : (M.xel : G) * M.cak 1 * (M.xel : G)⁻¹ = M.cak 2 := by
      simp only [cak]
      group
    rw [e]
    exact M.cak_mem_Agrp_two

theorem R2_conj_mem_Agrp {r y : G} (hr : r ∈ M.R2)
    (hy : y ∈ M.Agrp) : r * y * r⁻¹ ∈ M.Agrp := by
  have key : ∀ c ∈ M.Agrp, r * c * r⁻¹ ∈ M.Agrp := by
    intro c hc
    have hcR := M.Agrp_le_R2 hc
    have h := M.comm_mem_W_of_R2 hr hcR
    have e : r * c * r⁻¹ = (r * c * r⁻¹ * c⁻¹) * c := by group
    rw [e]
    exact mul_mem (M.W_le_Agrp h) hc
  exact key y hy

theorem T_conj_mem_Agrp {t y : G}
    (ht : t ∈ (M.T : Subgroup G)) (hy : y ∈ M.Agrp) : t * y * t⁻¹ ∈ M.Agrp := by
  have htG := M.T_le_G2 ht
  have htL := M.toRuData.T_le_L ht
  have hw := M.comm_ael_T_mem_W ht
  have h0 : t * M.cak 0 * t⁻¹ ∈ M.Agrp := by
    rw [M.cak_zero]
    have e : t * M.ael * t⁻¹ = (t * M.ael * t⁻¹ * M.ael⁻¹) * M.ael := by group
    rw [e]
    exact mul_mem (M.W_le_Agrp hw) M.ael_mem_Agrp
  refine M.conj_mem_of_reps htG h0 ?_ hy
  have hθ : M.θ ⟨t, htL⟩ ∈ SL3.P0 := M.θ_mem_P0 ht
  have hxL := M.xel.2
  have key : ∀ j : ℕ, (t * M.xel * t⁻¹) * ((M.xel : G) ^ j)⁻¹ ∈ M.R2 →
      t * M.cak 1 * t⁻¹ ∈ M.Agrp := by
    intro j hj
    set r := (t * M.xel * t⁻¹) * ((M.xel : G) ^ j)⁻¹ with hr
    have hc : t * M.cak 1 * t⁻¹ = r * ((M.xel : G) ^ j * (t * M.ael * t⁻¹ * M.ael⁻¹) *
        ((M.xel : G) ^ j)⁻¹) * M.cak j * r⁻¹ := by
      simp only [cak, hr, pow_one]
      group
    rw [hc]
    have hw' : (M.xel : G) ^ j * (t * M.ael * t⁻¹ * M.ael⁻¹) * ((M.xel : G) ^ j)⁻¹ ∈ M.W :=
      M.conj_mem_W (M.xel_pow_mem_G2 j) hw
    have hcj : M.cak j ∈ M.Agrp := by
      rcases Nat.lt_or_ge j 3 with hj3 | hj3
      · interval_cases j
        · exact M.cak_mem_Agrp_zero
        · exact M.cak_mem_Agrp_one
        · exact M.cak_mem_Agrp_two
      ·
        have e : M.cak j = M.cak (j % 3) := by
          simp only [cak]
          conv_lhs => rw [← Nat.div_add_mod j 3, pow_add, pow_mul, M.xel_pow_three, one_pow,
            one_mul]
        rw [e]
        have hj' : j % 3 < 3 := Nat.mod_lt _ (by norm_num)
        interval_cases (j % 3)
        · exact M.cak_mem_Agrp_zero
        · exact M.cak_mem_Agrp_one
        · exact M.cak_mem_Agrp_two
    have e : r * ((M.xel : G) ^ j * (t * M.ael * t⁻¹ * M.ael⁻¹) * ((M.xel : G) ^ j)⁻¹) *
        M.cak j * r⁻¹ = r * (((M.xel : G) ^ j * (t * M.ael * t⁻¹ * M.ael⁻¹) *
          ((M.xel : G) ^ j)⁻¹) * M.cak j) * r⁻¹ := by group
    rw [e]
    exact M.R2_conj_mem_Agrp hj (mul_mem (M.W_le_Agrp hw') hcj)
  have hm : ∀ j : ℕ, (M.θ ⟨t, htL⟩ * SL3.x0 * (M.θ ⟨t, htL⟩)⁻¹) * (SL3.x0 ^ j)⁻¹ ∈ SL3.R2m →
      (t * M.xel * t⁻¹) * ((M.xel : G) ^ j)⁻¹ ∈ M.R2 := by
    intro j hj
    refine mem_pullL.mpr ⟨mul_mem (mul_mem (mul_mem htL hxL) (inv_mem htL))
      (inv_mem (pow_mem hxL j)), ?_⟩
    have e : (⟨(t * M.xel * t⁻¹) * ((M.xel : G) ^ j)⁻¹, mul_mem (mul_mem (mul_mem htL hxL)
        (inv_mem htL)) (inv_mem (pow_mem hxL j))⟩ : M.L) =
        (⟨t, htL⟩ * M.xel * ⟨t, htL⟩⁻¹) * (M.xel ^ j)⁻¹ := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, map_pow, M.θ_xel]
    exact hj
  rcases SL3.P0_conj_x0 _ hθ with h | h
  · exact key 1 (hm 1 (by rw [pow_one]; exact h))
  · exact key 2 (hm 2 h)

theorem exists_T_mul_xel_pow {g : G} (hg : g ∈ M.G2) :
    ∃ t ∈ (M.T : Subgroup G), ∃ k : ℕ, g = t * (M.xel : G) ^ k := by
  obtain ⟨hgL, hgP⟩ := mem_pullL.mp hg
  obtain ⟨t0, ht0, hk⟩ := SL3.Pl_eq _ hgP
  rw [← M.hP0] at ht0
  obtain ⟨t1, ht1, ht1θ⟩ := ht0
  have ht1T : (t1 : G) ∈ (M.T : Subgroup G) := Subgroup.mem_subgroupOf.mp ht1
  have key : ∀ k : ℕ, M.θ ⟨g, hgL⟩ = t0 * SL3.x0 ^ k →
      ∃ t ∈ (M.T : Subgroup G), ∃ k : ℕ, g = t * (M.xel : G) ^ k := by
    intro k hk
    have hsL : ((t1 : G) * (M.xel : G) ^ k)⁻¹ * g ∈ M.L :=
      mul_mem (inv_mem (mul_mem t1.2 (pow_mem M.xel.2 k))) hgL
    have hsS : ((t1 : G) * (M.xel : G) ^ k)⁻¹ * g ∈ ruS M.L := by
      rw [M.mem_S_iff_θ hsL]
      have e : (⟨((t1 : G) * (M.xel : G) ^ k)⁻¹ * g, hsL⟩ : M.L) =
          (t1 * M.xel ^ k)⁻¹ * ⟨g, hgL⟩ := rfl
      rw [e, map_mul, map_inv, map_mul, map_pow, M.θ_xel, ht1θ, hk, inv_mul_cancel]
    set s := ((t1 : G) * (M.xel : G) ^ k)⁻¹ * g
    have hxs : (M.xel : G) ^ k * s * ((M.xel : G) ^ k)⁻¹ ∈ ruS M.L :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 M.L (pow_mem M.xel.2 k)) _).mp
        hsS
    refine ⟨(t1 : G) * ((M.xel : G) ^ k * s * ((M.xel : G) ^ k)⁻¹),
      mul_mem ht1T (M.toRuData.S_le_T hxs), k, ?_⟩
    simp only [s]
    group
  rcases hk with hk | hk | hk
  · exact key 0 (by rw [hk, pow_zero, mul_one])
  · exact key 1 (by rw [hk, pow_one])
  · exact key 2 hk

theorem conj_mem_Agrp {g y : G} (hg : g ∈ M.G2)
    (hy : y ∈ M.Agrp) : g * y * g⁻¹ ∈ M.Agrp := by
  obtain ⟨t, ht, k, rfl⟩ := M.exists_T_mul_xel_pow hg
  have hxk : ∀ k : ℕ, ∀ y ∈ M.Agrp, (M.xel : G) ^ k * y * ((M.xel : G) ^ k)⁻¹ ∈ M.Agrp := by
    intro k
    induction k with
    | zero => intro y hy; simpa using hy
    | succ k ih =>
      intro y hy
      have e : (M.xel : G) ^ (k + 1) * y * ((M.xel : G) ^ (k + 1))⁻¹ =
          (M.xel : G) * ((M.xel : G) ^ k * y * ((M.xel : G) ^ k)⁻¹) * (M.xel : G)⁻¹ := by
        rw [pow_succ']; group
      rw [e]
      exact M.xel_conj_mem_Agrp (ih y hy)
  have e : t * (M.xel : G) ^ k * y * (t * (M.xel : G) ^ k)⁻¹ =
      t * ((M.xel : G) ^ k * y * ((M.xel : G) ^ k)⁻¹) * t⁻¹ := by group
  rw [e]
  exact M.T_conj_mem_Agrp ht (hxk k y hy)

end RuDataM

end CFSG.Quasithin.RuType
