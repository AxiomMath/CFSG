module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1CoverAltTenB
public import CFSG.Quasithin.H13.VolIAltCoverSeven
public import CFSG.Quasithin.H13.VolIAltCoverUniversal

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.VolI CFSG.Quasithin.G6
  CFSG.OddStandard.AltStdSec Subgroup Equiv

@[expose] def s16c11_v1_h : ↥(alternatingGroup (Fin 10)) :=
  ⟨swap 0 9 * swap 1 2, by rw [Perm.mem_alternatingGroup]; decide⟩

@[expose] def s16c11_v1_m012 : ↥(alternatingGroup (Fin 10)) :=
  ⟨swap 0 1 * swap 1 2, by rw [Perm.mem_alternatingGroup]; decide⟩

@[expose] def s16c11_v1_rep10 : Fin 10 → ↥(alternatingGroup (Fin 10)) :=
  ![1, 1, s16c11_v1_c123,
    ⟨swap 1 3 * swap 3 2, by rw [Perm.mem_alternatingGroup]; decide⟩,
    ⟨swap 1 4 * swap 4 2, by rw [Perm.mem_alternatingGroup]; decide⟩,
    ⟨swap 1 5 * swap 5 2, by rw [Perm.mem_alternatingGroup]; decide⟩,
    ⟨swap 1 6 * swap 6 2, by rw [Perm.mem_alternatingGroup]; decide⟩,
    ⟨swap 1 7 * swap 7 2, by rw [Perm.mem_alternatingGroup]; decide⟩,
    ⟨swap 1 8 * swap 8 2, by rw [Perm.mem_alternatingGroup]; decide⟩,
    ⟨swap 1 9 * swap 9 2, by rw [Perm.mem_alternatingGroup]; decide⟩]

theorem s16c11_v1_rep10_spec (j : Fin 10) (hj : j ≠ 0) :
    (s16c11_v1_rep10 j : Perm (Fin 10)) 0 = 0 ∧
      (s16c11_v1_rep10 j : Perm (Fin 10)) 1 = j := by
  fin_cases j <;> simp_all <;> decide

theorem s16c11_v1_h_mul_self : s16c11_v1_h * s16c11_v1_h = 1 := by decide

theorem s16c11_v1_h_zero : (s16c11_v1_h : Perm (Fin 10)) 0 = 9 := by decide

theorem s16c11_v1_h_nine : (s16c11_v1_h : Perm (Fin 10)) 9 = 0 := by decide

@[expose] def s16c11_v1_A8 : Finset (Fin 10) := s16c11_v1_T.erase 9

theorem s16c11_v1_mem_A8 {i : Fin 10} : i ∈ s16c11_v1_A8 ↔ i ≠ 0 ∧ i ≠ 9 := by
  simp only [s16c11_v1_A8, s16c11_v1_T, Finset.mem_erase, Finset.mem_univ, and_true, true_and]
  exact and_comm

theorem s16c11_v1_conj_h_mem_A8 {κ : ↥(alternatingGroup (Fin 10))}
    (hκ : (κ : Perm (Fin 10)) ∈ altSub s16c11_v1_A8) :
    ((s16c11_v1_h * κ * s16c11_v1_h : ↥(alternatingGroup (Fin 10))) : Perm (Fin 10)) ∈
      altSub s16c11_v1_A8 := by
  rw [mem_altSub] at hκ ⊢
  refine ⟨?_, fun i hi => ?_⟩
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, Perm.sign_mul, Perm.sign_mul, hκ.1]
    norm_num
  · have hi' : i = 0 ∨ i = 9 := by
      by_contra h
      exact hi (by
        rw [s16c11_v1_mem_A8]
        exact ⟨fun h0 => h (Or.inl h0), fun h9 => h (Or.inr h9)⟩)
    rcases hi' with rfl | rfl
    · have hκ9 : (κ : Perm (Fin 10)) 9 = 9 := hκ.2 9 (by rw [s16c11_v1_mem_A8]; decide)
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Perm.mul_apply, Perm.mul_apply,
        s16c11_v1_h_zero, hκ9, s16c11_v1_h_nine]
    · have hκ0 : (κ : Perm (Fin 10)) 0 = 0 := hκ.2 0 (by rw [s16c11_v1_mem_A8]; decide)
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Perm.mul_apply, Perm.mul_apply,
        s16c11_v1_h_nine, hκ0, s16c11_v1_h_zero]

structure s16c11_v1_AltCover10 (W : Type*) [CommGroup W] where
  ρ : ↥(alternatingGroup (Fin 10)) →* MulAut W
  β : W →* DnQuot 10
  surj : Function.Surjective β
  fix : ∀ σ v, β v = 1 → ρ σ v = v
  equiv : ∀ σ v (m : ↥(coreMod 10)), β v = QuotientGroup.mk m →
    β (ρ σ v) = QuotientGroup.mk (coreAct 10 (σ : Perm (Fin 10)) m)
  gen : ∀ v : W, v ∈ closure {x | ∃ σ w, x = ρ σ w * w⁻¹}

@[expose] def s16c11_v1_ModelCover.toAltCover10 {W : Type*} [CommGroup W]
    (C : ModelCover (FFModel.altDn 10) W) : s16c11_v1_AltCover10 W where
  ρ := C.ρ
  β := C.β
  surj := C.surj
  fix := C.fix
  equiv σ v m h := C.equiv σ v m (permAct_mem_coreMod _ m.2) h
  gen := C.gen

namespace s16c11_v1_AltCover10

variable {W : Type*} [CommGroup W] (C : s16c11_v1_AltCover10 W)

@[expose] def Y : Subgroup W :=
  ((commMap (C.ρ s16c11_v1_c123)).range ⊔ (commMap (C.ρ s16c11_v1_c345)).range) ⊔
    ((commMap (C.ρ s16c11_v1_c567)).range ⊔ (commMap (C.ρ s16c11_v1_c789)).range)

theorem β_comm (σ : ↥(alternatingGroup (Fin 10))) {v : W} {m : ↥(coreMod 10)}
    (h : C.β v = QuotientGroup.mk m) :
    C.β (C.ρ σ v * v⁻¹) =
      QuotientGroup.mk (coreAct 10 (σ : Perm (Fin 10)) m * m⁻¹) := by
  rw [map_mul, map_inv, C.equiv σ v m h, h, QuotientGroup.mk_mul, QuotientGroup.mk_inv]

theorem β_comm4 (σ τ υ ω : ↥(alternatingGroup (Fin 10))) {a b c d : PermMod 10}
    (ha : a ∈ coreMod 10) (hb : b ∈ coreMod 10) (hc : c ∈ coreMod 10) (hd : d ∈ coreMod 10)
    {u v w x : W} (hu : C.β u = QuotientGroup.mk ⟨a, ha⟩)
    (hv : C.β v = QuotientGroup.mk ⟨b, hb⟩) (hw : C.β w = QuotientGroup.mk ⟨c, hc⟩)
    (hx : C.β x = QuotientGroup.mk ⟨d, hd⟩) :
    C.β (C.ρ σ u * u⁻¹ * (C.ρ τ v * v⁻¹) * (C.ρ υ w * w⁻¹) * (C.ρ ω x * x⁻¹)) =
      QuotientGroup.mk ⟨s16c11_v1_comm4 σ τ υ ω a b c d,
        s16c11_v1_comm4_mem σ τ υ ω ha hb hc hd⟩ := by
  rw [map_mul, map_mul, map_mul, C.β_comm σ hu, C.β_comm τ hv, C.β_comm υ hw,
    C.β_comm ω hx, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  rfl

theorem comm_mul {a b : ↥(alternatingGroup (Fin 10))} {M : Subgroup W}
    (ha : ∀ v, C.ρ a v * v⁻¹ ∈ M) (hb : ∀ v, C.ρ b v * v⁻¹ ∈ M) (v : W) :
    C.ρ (a * b) v * v⁻¹ ∈ M := by
  have e : C.ρ (a * b) v * v⁻¹ = (C.ρ a (C.ρ b v) * (C.ρ b v)⁻¹) * (C.ρ b v * v⁻¹) := by
    rw [map_mul, MulAut.mul_apply]
    group
  rw [e]
  exact mul_mem (ha _) (hb v)

theorem comm_inv {a : ↥(alternatingGroup (Fin 10))} {M : Subgroup W}
    (ha : ∀ v, C.ρ a v * v⁻¹ ∈ M) (v : W) : C.ρ a⁻¹ v * v⁻¹ ∈ M := by
  have h := ha (C.ρ a⁻¹ v)
  have h1 : C.ρ a (C.ρ a⁻¹ v) = v := by
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  rw [h1] at h
  have h2 : C.ρ a⁻¹ v * v⁻¹ = (v * (C.ρ a⁻¹ v)⁻¹)⁻¹ := by group
  rw [h2]
  exact M.inv_mem h

theorem comm_mem_Y {σ : ↥(alternatingGroup (Fin 10))}
    (hσ : (σ : Perm (Fin 10)) ∈ altSub s16c11_v1_T) (v : W) :
    C.ρ σ v * v⁻¹ ∈ C.Y := by
  have hP : ∀ h ∈ s16c11_v1_H, ∀ v, C.ρ h v * v⁻¹ ∈ C.Y := by
    intro h hh
    induction hh using Subgroup.closure_induction with
    | mem x hx =>
      intro v
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact mem_sup_left (mem_sup_left ⟨v, rfl⟩)
      · exact mem_sup_left (mem_sup_right ⟨v, rfl⟩)
      · exact mem_sup_right (mem_sup_left ⟨v, rfl⟩)
      · exact mem_sup_right (mem_sup_right ⟨v, rfl⟩)
    | one =>
      intro v
      rw [map_one, MulAut.one_apply, mul_inv_cancel]
      exact one_mem _
    | mul a b _ _ ha hb =>
      intro v
      exact C.comm_mul ha hb v
    | inv a _ ha =>
      intro v
      exact C.comm_inv ha v
  have hσQ : (σ : Perm (Fin 10)) ∈ s16c11_v1_Q := s16c11_v1_altSub_le_Q hσ
  obtain ⟨h, hh, hhe⟩ := Subgroup.mem_map.1 hσQ
  have hσh : σ = h := Subtype.ext hhe.symm
  rw [hσh]
  exact hP h hh v

theorem card_Y_le [Finite W] (hW2 : ∀ v : W, v ^ 2 = 1) : Nat.card C.Y ≤ 2 ^ 8 := by
  have hβk : ∀ v, C.β v = 1 ↔ v ∈ C.β.ker := fun v => MonoidHom.mem_ker
  have h1 : Nat.card (commMap (C.ρ s16c11_v1_c123)).range ≤ 4 := by
    have h := card_commMap_range_le (n := 10) (β := C.β) (t := C.ρ s16c11_v1_c123)
      (γ := (s16c11_v1_c123 : Perm (Fin 10))) hW2 hβk
      (by rw [← map_pow, show s16c11_v1_c123 ^ 3 = 1 by decide, map_one])
      (fun z hz => C.fix s16c11_v1_c123 z (hβk z |>.1 hz))
      (fun _ _ h => C.equiv _ _ _ h)
      (evenOn 1 2 3) s16c11_v1_comm_mem_evenOn_ten_123
    rwa [s16c11_v1_evenOn_ten_123_card] at h
  have h2 : Nat.card (commMap (C.ρ s16c11_v1_c345)).range ≤ 4 := by
    have h := card_commMap_range_le (n := 10) (β := C.β) (t := C.ρ s16c11_v1_c345)
      (γ := (s16c11_v1_c345 : Perm (Fin 10))) hW2 hβk
      (by rw [← map_pow, show s16c11_v1_c345 ^ 3 = 1 by decide, map_one])
      (fun z hz => C.fix s16c11_v1_c345 z (hβk z |>.1 hz))
      (fun _ _ h => C.equiv _ _ _ h)
      (evenOn 3 4 5) s16c11_v1_comm_mem_evenOn_ten_345
    rwa [s16c11_v1_evenOn_ten_345_card] at h
  have h3 : Nat.card (commMap (C.ρ s16c11_v1_c567)).range ≤ 4 := by
    have h := card_commMap_range_le (n := 10) (β := C.β) (t := C.ρ s16c11_v1_c567)
      (γ := (s16c11_v1_c567 : Perm (Fin 10))) hW2 hβk
      (by rw [← map_pow, show s16c11_v1_c567 ^ 3 = 1 by decide, map_one])
      (fun z hz => C.fix s16c11_v1_c567 z (hβk z |>.1 hz))
      (fun _ _ h => C.equiv _ _ _ h)
      (evenOn 5 6 7) s16c11_v1_comm_mem_evenOn_ten_567
    rwa [s16c11_v1_evenOn_ten_567_card] at h
  have h4 : Nat.card (commMap (C.ρ s16c11_v1_c789)).range ≤ 4 := by
    have h := card_commMap_range_le (n := 10) (β := C.β) (t := C.ρ s16c11_v1_c789)
      (γ := (s16c11_v1_c789 : Perm (Fin 10))) hW2 hβk
      (by rw [← map_pow, show s16c11_v1_c789 ^ 3 = 1 by decide, map_one])
      (fun z hz => C.fix s16c11_v1_c789 z (hβk z |>.1 hz))
      (fun _ _ h => C.equiv _ _ _ h)
      (evenOn 7 8 9) s16c11_v1_comm_mem_evenOn_ten_789
    rwa [s16c11_v1_evenOn_ten_789_card] at h
  calc Nat.card C.Y ≤
        Nat.card ↥((commMap (C.ρ s16c11_v1_c123)).range ⊔
          (commMap (C.ρ s16c11_v1_c345)).range) *
          Nat.card ↥((commMap (C.ρ s16c11_v1_c567)).range ⊔
            (commMap (C.ρ s16c11_v1_c789)).range) := card_sup_le_mul _ _
    _ ≤ (Nat.card (commMap (C.ρ s16c11_v1_c123)).range *
          Nat.card (commMap (C.ρ s16c11_v1_c345)).range) *
          (Nat.card (commMap (C.ρ s16c11_v1_c567)).range *
            Nat.card (commMap (C.ρ s16c11_v1_c789)).range) :=
        Nat.mul_le_mul (card_sup_le_mul _ _) (card_sup_le_mul _ _)
    _ ≤ (4 * 4) * (4 * 4) := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) (Nat.mul_le_mul h3 h4)
    _ = 2 ^ 8 := by norm_num

theorem exists_mem_Y (q : DnQuot 10) : ∃ y ∈ C.Y, C.β y = q := by
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨a, ha, b, hb, c, hc, d, hd, hm⟩ := s16c11_v1_coreMod_ten_eq m m.2
  obtain ⟨u, hu⟩ := C.surj (QuotientGroup.mk ⟨a, s16c11_v1_lifts123Ten_mem a ha⟩)
  obtain ⟨v, hv⟩ := C.surj (QuotientGroup.mk ⟨b, s16c11_v1_lifts345Ten_mem b hb⟩)
  obtain ⟨w, hw⟩ := C.surj (QuotientGroup.mk ⟨c, s16c11_v1_lifts567Ten_mem c hc⟩)
  obtain ⟨x, hx⟩ := C.surj (QuotientGroup.mk ⟨d, s16c11_v1_lifts789Ten_mem d hd⟩)
  refine ⟨C.ρ s16c11_v1_c123 u * u⁻¹ * (C.ρ s16c11_v1_c345 v * v⁻¹) *
      (C.ρ s16c11_v1_c567 w * w⁻¹) * (C.ρ s16c11_v1_c789 x * x⁻¹),
    mul_mem (mul_mem (mul_mem (mem_sup_left (mem_sup_left ⟨u, rfl⟩))
      (mem_sup_left (mem_sup_right ⟨v, rfl⟩))) (mem_sup_right (mem_sup_left ⟨w, rfl⟩)))
      (mem_sup_right (mem_sup_right ⟨x, rfl⟩)), ?_⟩
  rw [C.β_comm4 s16c11_v1_c123 s16c11_v1_c345 s16c11_v1_c567 s16c11_v1_c789 _ _ _ _
    hu hv hw hx]
  rcases hm with hm | hm
  · exact s16c11_v1_mk_eq_mk_iff_ten.2 (Or.inl hm)
  · exact s16c11_v1_mk_eq_mk_iff_ten.2 (Or.inr hm)

theorem bijective_Y [Finite W] (hW2 : ∀ v : W, v ^ 2 = 1) :
    Function.Bijective (C.β.comp C.Y.subtype) := by
  refine Function.Surjective.bijective_of_nat_card_le (fun q => ?_)
    (C.card_Y_le hW2 |>.trans (le_of_eq s16c11_v1_card_dnQuot_ten.symm))
  obtain ⟨y, hy, rfl⟩ := C.exists_mem_Y q
  exact ⟨⟨y, hy⟩, rfl⟩

theorem card_Y [Finite W] (hW2 : ∀ v : W, v ^ 2 = 1) : Nat.card C.Y = 2 ^ 8 := by
  rw [Nat.card_congr (Equiv.ofBijective _ (C.bijective_Y hW2)), s16c11_v1_card_dnQuot_ten]
  norm_num

theorem inf_ker [Finite W] (hW2 : ∀ v : W, v ^ 2 = 1) : C.Y ⊓ C.β.ker = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨hy1, hy2⟩ := mem_inf.1 hy
  rw [MonoidHom.mem_ker] at hy2
  refine mem_bot.2 (congrArg Subtype.val
    (C.bijective_Y hW2 |>.1 (a₁ := ⟨y, hy1⟩) (a₂ := ⟨1, one_mem _⟩) ?_))
  simp [hy2]

theorem sup_ker [Finite W] (hW2 : ∀ v : W, v ^ 2 = 1) : C.Y ⊔ C.β.ker = ⊤ := by
  rw [eq_top_iff]
  intro v _
  obtain ⟨y, hy, hβ⟩ := C.exists_mem_Y (C.β v)
  refine mem_sup.2 ⟨y, hy, y⁻¹ * v, ?_, mul_inv_cancel_left y v⟩
  rw [MonoidHom.mem_ker, map_mul, map_inv, hβ, inv_mul_cancel]

theorem card_eq [Finite W] (hW2 : ∀ v : W, v ^ 2 = 1) :
    Nat.card W = 2 ^ 8 * Nat.card C.β.ker := by
  have hN : C.Y ≤ normalizer (C.β.ker : Set W) := by
    rw [normalizer_eq_top]
    exact le_top
  have h := card_sup_mul_card_inf hN
  rw [C.sup_ker hW2, C.inf_ker hW2, card_top, card_bot, mul_one, C.card_Y hW2] at h
  exact h

@[expose] def sY : Subgroup W := C.Y.map (C.ρ s16c11_v1_h).toMonoidHom

theorem h_apply_h (v : W) : C.ρ s16c11_v1_h (C.ρ s16c11_v1_h v) = v := by
  rw [← MulAut.mul_apply, ← map_mul, s16c11_v1_h_mul_self, map_one, MulAut.one_apply]

theorem comm_mem_sY {κ : ↥(alternatingGroup (Fin 10))}
    (hκ : ((s16c11_v1_h * κ * s16c11_v1_h : ↥(alternatingGroup (Fin 10))) : Perm (Fin 10)) ∈
      altSub s16c11_v1_T) (v : W) : C.ρ κ v * v⁻¹ ∈ C.sY := by
  refine mem_map.2 ⟨C.ρ (s16c11_v1_h * κ * s16c11_v1_h) (C.ρ s16c11_v1_h v) *
    (C.ρ s16c11_v1_h v)⁻¹, C.comm_mem_Y hκ _, ?_⟩
  show C.ρ s16c11_v1_h (C.ρ (s16c11_v1_h * κ * s16c11_v1_h) (C.ρ s16c11_v1_h v) *
    (C.ρ s16c11_v1_h v)⁻¹) = C.ρ κ v * v⁻¹
  have e : C.ρ (s16c11_v1_h * κ * s16c11_v1_h) (C.ρ s16c11_v1_h v) =
      C.ρ s16c11_v1_h (C.ρ κ v) := by
    rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply, C.h_apply_h]
  rw [e, map_mul, map_inv, C.h_apply_h, C.h_apply_h]

theorem sup_eq_top_ten : C.Y ⊔ C.sY = ⊤ := by
  have hP : ∀ σ : ↥(alternatingGroup (Fin 10)), ∀ v, C.ρ σ v * v⁻¹ ∈ C.Y ⊔ C.sY := by
    intro σ
    by_cases h0 : (σ : Perm (Fin 10)) 0 = 0
    · exact fun v => mem_sup_left (C.comm_mem_Y (by
        rw [mem_altSub]
        exact ⟨Perm.mem_alternatingGroup.1 σ.2, fun i hi => by
          rw [s16c11_v1_mem_T] at hi
          rw [show i = 0 from not_not.mp hi]
          exact h0⟩) v)
    · intro v
      obtain ⟨hr0, hr1⟩ := s16c11_v1_rep10_spec ((σ : Perm (Fin 10)) 0) h0
      let r := s16c11_v1_rep10 ((σ : Perm (Fin 10)) 0)
      let κ := (r * s16c11_v1_m012)⁻¹ * σ
      have hm0 : (s16c11_v1_m012 : Perm (Fin 10)) 0 = 1 := by decide
      have hrm0 : ((r * s16c11_v1_m012 : ↥(alternatingGroup (Fin 10))) : Perm (Fin 10)) 0 =
          (σ : Perm (Fin 10)) 0 := by
        rw [Subgroup.coe_mul, Perm.mul_apply, hm0, hr1]
      have hκ0 : (κ : Perm (Fin 10)) 0 = 0 := by
        show (((r * s16c11_v1_m012)⁻¹ * σ : ↥(alternatingGroup (Fin 10))) :
          Perm (Fin 10)) 0 = 0
        rw [Subgroup.coe_mul, Perm.mul_apply, Subgroup.coe_inv]
        rw [show (σ : Perm (Fin 10)) 0 = ((r * s16c11_v1_m012 : ↥(alternatingGroup (Fin 10))) :
          Perm (Fin 10)) 0 from hrm0.symm]
        exact Equiv.symm_apply_apply _ _
      have hκmem : (κ : Perm (Fin 10)) ∈ altSub s16c11_v1_T := by
        rw [mem_altSub]
        exact ⟨Perm.mem_alternatingGroup.1 κ.2, fun i hi => by
          rw [s16c11_v1_mem_T] at hi
          rw [show i = 0 from not_not.mp hi]
          exact hκ0⟩
      have hmfix : ((s16c11_v1_h * s16c11_v1_m012 * s16c11_v1_h :
          ↥(alternatingGroup (Fin 10))) : Perm (Fin 10)) ∈ altSub s16c11_v1_T := by
        rw [mem_altSub]
        exact ⟨Perm.mem_alternatingGroup.1
          (s16c11_v1_h * s16c11_v1_m012 * s16c11_v1_h).2, fun i hi => by
          rw [s16c11_v1_mem_T] at hi
          rw [show i = 0 from not_not.mp hi]
          decide⟩
      have e : σ = r * s16c11_v1_m012 * κ := by
        show σ = r * s16c11_v1_m012 * ((r * s16c11_v1_m012)⁻¹ * σ)
        group
      have hrY : ∀ v, C.ρ r v * v⁻¹ ∈ C.Y ⊔ C.sY := fun v =>
        mem_sup_left (C.comm_mem_Y (by
          rw [mem_altSub]
          exact ⟨Perm.mem_alternatingGroup.1 r.2, fun i hi => by
            rw [s16c11_v1_mem_T] at hi
            rw [show i = 0 from not_not.mp hi]
            exact hr0⟩) v)
      have hmY : ∀ v, C.ρ s16c11_v1_m012 v * v⁻¹ ∈ C.Y ⊔ C.sY := fun v =>
        mem_sup_right (C.comm_mem_sY hmfix v)
      have hκY : ∀ v, C.ρ κ v * v⁻¹ ∈ C.Y ⊔ C.sY := fun v =>
        mem_sup_left (C.comm_mem_Y hκmem v)
      rw [e]
      exact C.comm_mul (C.comm_mul hrY hmY) hκY v
  rw [eq_top_iff]
  intro v _
  refine (closure_le _).2 ?_ (C.gen v)
  rintro _ ⟨σ, w, rfl⟩
  exact hP σ w

@[expose] def s16c11_v1_gens : Fin 7 → PermMod 10 :=
  ![s16c11_v1_ev10 1 8, s16c11_v1_ev10 2 8, s16c11_v1_ev10 3 8, s16c11_v1_ev10 4 8,
    s16c11_v1_ev10 5 8, s16c11_v1_ev10 6 8, s16c11_v1_ev10 7 8]

@[expose] def s16c11_v1_mvec : Fin 7 → PermMod 10 :=
  ![s16c11_v1_ev10 1 2, s16c11_v1_ev10 2 1, s16c11_v1_ev10 3 1, s16c11_v1_ev10 4 1,
    s16c11_v1_ev10 5 1, s16c11_v1_ev10 6 1, s16c11_v1_ev10 7 1]

@[expose] def s16c11_v1_sig : Fin 7 → ↥(alternatingGroup (Fin 10)) :=
  ![⟨swap 1 8 * swap 8 3, by rw [Perm.mem_alternatingGroup]; decide⟩,
    ⟨swap 2 8 * swap 8 3, by rw [Perm.mem_alternatingGroup]; decide⟩,
    ⟨swap 3 8 * swap 8 2, by rw [Perm.mem_alternatingGroup]; decide⟩,
    ⟨swap 4 8 * swap 8 2, by rw [Perm.mem_alternatingGroup]; decide⟩,
    ⟨swap 5 8 * swap 8 2, by rw [Perm.mem_alternatingGroup]; decide⟩,
    ⟨swap 6 8 * swap 8 2, by rw [Perm.mem_alternatingGroup]; decide⟩,
    ⟨swap 7 8 * swap 8 2, by rw [Perm.mem_alternatingGroup]; decide⟩]

theorem s16c11_v1_gens_mem (i : Fin 7) : s16c11_v1_gens i ∈ coreMod 10 := by
  fin_cases i <;> simp only [mem_coreMod] <;> decide +kernel

theorem s16c11_v1_mvec_mem (i : Fin 7) : s16c11_v1_mvec i ∈ coreMod 10 := by
  fin_cases i <;> simp only [mem_coreMod] <;> decide +kernel

theorem s16c11_v1_sig_mem (i : Fin 7) :
    (s16c11_v1_sig i : Perm (Fin 10)) ∈ altSub s16c11_v1_A8 := by
  rw [mem_altSub]
  refine ⟨?_, fun j hj => ?_⟩
  · fin_cases i <;> decide
  · fin_cases i <;> fin_cases j <;> simp_all [s16c11_v1_mem_A8] <;> decide

theorem s16c11_v1_sig_comm (i : Fin 7) :
    permAct 10 (s16c11_v1_sig i : Perm (Fin 10)) (s16c11_v1_mvec i) *
      (s16c11_v1_mvec i)⁻¹ = s16c11_v1_gens i := by
  fin_cases i <;> decide +kernel

theorem s16c11_v1_coreAct_sig (i : Fin 7) :
    coreAct 10 (s16c11_v1_sig i : Perm (Fin 10))
        (⟨s16c11_v1_mvec i, s16c11_v1_mvec_mem i⟩ : ↥(coreMod 10)) *
      (⟨s16c11_v1_mvec i, s16c11_v1_mvec_mem i⟩ : ↥(coreMod 10))⁻¹ =
      (⟨s16c11_v1_gens i, s16c11_v1_gens_mem i⟩ : ↥(coreMod 10)) := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_inv]
  exact s16c11_v1_sig_comm i

@[expose] def s16c11_v1_gensProd (c : Fin 7 → ZMod 2) : ↥(coreMod 10) :=
  ∏ i, if c i = 0 then 1 else (⟨s16c11_v1_gens i, s16c11_v1_gens_mem i⟩ : ↥(coreMod 10))

theorem s16c11_v1_gens_indep : ∀ c c' : Fin 7 → ZMod 2,
    ((s16c11_v1_gensProd c' : PermMod 10) = s16c11_v1_gensProd c ∨
      (s16c11_v1_gensProd c' : PermMod 10) = s16c11_v1_gensProd c * allOnes 10) → c = c' := by
  decide +kernel

@[expose] def s16c11_v1_actA8 : ↥(altSub s16c11_v1_A8) →* MulAut W :=
  C.ρ.comp (Subgroup.inclusion (altSub_le_alternatingGroup s16c11_v1_A8))

@[expose] def s16c11_v1_commV_A8 : Subgroup W :=
  Subgroup.closure {x | ∃ h : ↥(altSub s16c11_v1_A8), ∃ v : W,
    x = C.s16c11_v1_actA8 h v * v⁻¹}

theorem s16c11_v1_commV_A8_le_Y : C.s16c11_v1_commV_A8 ≤ C.Y := by
  rw [s16c11_v1_commV_A8, Subgroup.closure_le]
  rintro _ ⟨h, v, rfl⟩
  show C.ρ (Subgroup.inclusion (altSub_le_alternatingGroup s16c11_v1_A8) h) v * v⁻¹ ∈ C.Y
  refine C.comm_mem_Y ?_ v
  rw [Subgroup.coe_inclusion]
  exact altSub_mono (Finset.erase_subset 9 s16c11_v1_T) h.2

theorem s16c11_v1_commV_A8_le_sY : C.s16c11_v1_commV_A8 ≤ C.sY := by
  rw [s16c11_v1_commV_A8, Subgroup.closure_le]
  rintro _ ⟨h, v, rfl⟩
  have hconj : ((s16c11_v1_h * Subgroup.inclusion (altSub_le_alternatingGroup s16c11_v1_A8) h *
      s16c11_v1_h : ↥(alternatingGroup (Fin 10))) : Perm (Fin 10)) ∈ altSub s16c11_v1_T :=
    altSub_mono (Finset.erase_subset 9 s16c11_v1_T)
      (s16c11_v1_conj_h_mem_A8 (κ := Subgroup.inclusion
        (altSub_le_alternatingGroup s16c11_v1_A8) h) (by
          rw [Subgroup.coe_inclusion]; exact h.2))
  show C.ρ (Subgroup.inclusion (altSub_le_alternatingGroup s16c11_v1_A8) h) v * v⁻¹ ∈ C.sY
  exact C.comm_mem_sY hconj v

local instance s16c11_v1_instCommGroupDnQuotTen : CommGroup (DnQuot 10) :=
  { (inferInstance : Group (DnQuot 10)) with
    mul_comm := fun a b => by
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
      show QuotientGroup.mk x * QuotientGroup.mk y =
        QuotientGroup.mk y * QuotientGroup.mk x
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mul_comm] }

theorem s16c11_v1_card_commV_A8_ge [Finite W] (hW2 : ∀ v : W, v ^ 2 = 1) :
    2 ^ 7 ≤ Nat.card ↥(C.s16c11_v1_commV_A8) := by
  classical
  have hex : ∀ i : Fin 7, ∃ g : W, g ∈ C.s16c11_v1_commV_A8 ∧
      C.β g = QuotientGroup.mk (⟨s16c11_v1_gens i, s16c11_v1_gens_mem i⟩ : ↥(coreMod 10)) := by
    intro i
    obtain ⟨w, hw⟩ := C.surj (QuotientGroup.mk
      (⟨s16c11_v1_mvec i, s16c11_v1_mvec_mem i⟩ : ↥(coreMod 10)))
    refine ⟨C.ρ (s16c11_v1_sig i) w * w⁻¹, ?_, ?_⟩
    · refine Subgroup.subset_closure ⟨⟨s16c11_v1_sig i, s16c11_v1_sig_mem i⟩, w, ?_⟩
      have hinc : C.s16c11_v1_actA8 ⟨s16c11_v1_sig i, s16c11_v1_sig_mem i⟩ =
          C.ρ (s16c11_v1_sig i) := by
        show C.ρ (Subgroup.inclusion (altSub_le_alternatingGroup s16c11_v1_A8)
          ⟨s16c11_v1_sig i, s16c11_v1_sig_mem i⟩) = C.ρ (s16c11_v1_sig i)
        rw [show (Subgroup.inclusion (altSub_le_alternatingGroup s16c11_v1_A8)
          ⟨s16c11_v1_sig i, s16c11_v1_sig_mem i⟩ : ↥(alternatingGroup (Fin 10))) =
          s16c11_v1_sig i from Subtype.ext rfl]
      rw [hinc]
    · rw [C.β_comm (s16c11_v1_sig i) hw]
      congr 1
      exact s16c11_v1_coreAct_sig i
  choose g hgmem hgβ using hex
  let f : (Fin 7 → ZMod 2) → ↥(C.s16c11_v1_commV_A8) := fun c =>
    ⟨∏ i, if c i = 0 then 1 else g i, by
      rw [s16c11_v1_commV_A8]
      refine Finset.prod_induction _ _ (fun a b ha hb => mul_mem ha hb) (one_mem _) (fun i _ => ?_)
      by_cases h : c i = 0
      · rw [if_pos h]; exact one_mem _
      · rw [if_neg h]; exact hgmem i⟩
  have hβprod : ∀ c : Fin 7 → ZMod 2, C.β (f c).1 = QuotientGroup.mk
      (s16c11_v1_gensProd c) := by
    intro c
    have h1 : C.β (f c).1 = ∏ i, QuotientGroup.mk (if c i = 0 then 1 else
        (⟨s16c11_v1_gens i, s16c11_v1_gens_mem i⟩ : ↥(coreMod 10))) := by
      show C.β (∏ i, if c i = 0 then 1 else g i) = _
      rw [map_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      by_cases h : c i = 0
      · rw [if_pos h, if_pos h]; exact map_one C.β
      · rw [if_neg h, if_neg h, hgβ i]
    have h2 : (QuotientGroup.mk (s16c11_v1_gensProd c) : DnQuot 10) =
        ∏ i, QuotientGroup.mk (if c i = 0 then 1 else
          (⟨s16c11_v1_gens i, s16c11_v1_gens_mem i⟩ : ↥(coreMod 10))) := by
      rw [s16c11_v1_gensProd]
      exact map_prod (QuotientGroup.mk' _) _ _
    rw [h1, h2]
  have hf : Function.Injective f := by
    intro c c' hcc
    have hβ : C.β (f c).1 = C.β (f c').1 := congrArg (fun x : ↥(C.s16c11_v1_commV_A8) =>
      C.β x.1) hcc
    rw [hβprod c, hβprod c'] at hβ
    exact s16c11_v1_gens_indep c c' (s16c11_v1_mk_eq_mk_iff_ten.1 hβ)
  calc 2 ^ 7 = Nat.card (Fin 7 → ZMod 2) := by rw [Nat.card_pi]; simp
    _ ≤ Nat.card ↥(C.s16c11_v1_commV_A8) := Nat.card_le_card_of_injective f hf

theorem card_le (C : s16c11_v1_AltCover10 W) [Finite W] (hW2 : ∀ v : W, v ^ 2 = 1) :
    Nat.card W ≤ 2 ^ 9 := by
  have hN : C.Y ≤ normalizer (C.sY : Set W) := by
    rw [normalizer_eq_top]
    exact le_top
  have h := card_sup_mul_card_inf hN
  have hsY : Nat.card C.sY = 2 ^ 8 := by
    show Nat.card ↥(C.Y.map (C.ρ s16c11_v1_h).toMonoidHom) = 2 ^ 8
    rw [card_map_of_injective (f := (C.ρ s16c11_v1_h).toMonoidHom)
      (C.ρ s16c11_v1_h).injective, C.card_Y hW2]
  rw [C.sup_eq_top_ten, card_top, C.card_Y hW2, hsY] at h
  have hinf : 2 ^ 7 ≤ Nat.card ↥(C.Y ⊓ C.sY) :=
    (C.s16c11_v1_card_commV_A8_ge hW2).trans (card_le_of_le
      (le_inf C.s16c11_v1_commV_A8_le_Y C.s16c11_v1_commV_A8_le_sY))
  have h2 : Nat.card W * 2 ^ 7 ≤ 2 ^ 8 * 2 ^ 8 :=
    calc Nat.card W * 2 ^ 7 ≤ Nat.card W * Nat.card ↥(C.Y ⊓ C.sY) := Nat.mul_le_mul_left _ hinf
      _ = 2 ^ 8 * 2 ^ 8 := h
  omega

theorem card_ker_le (C : s16c11_v1_AltCover10 W) [Finite W] (hW2 : ∀ v : W, v ^ 2 = 1) :
    Nat.card C.β.ker ≤ 2 := by
  have h1 := C.card_eq hW2
  have h2 := s16c11_v1_AltCover10.card_le C hW2
  have hpos : 0 < Nat.card C.β.ker := Nat.card_pos
  omega

end s16c11_v1_AltCover10

@[expose] def s16c11_v1_d1 : ↥(alternatingGroup (Fin 10)) :=
  ⟨swap 0 1 * swap 2 3, by rw [Perm.mem_alternatingGroup]; decide⟩

@[expose] def s16c11_v1_d2 : ↥(alternatingGroup (Fin 10)) :=
  ⟨swap 4 5 * swap 6 7, by rw [Perm.mem_alternatingGroup]; decide⟩

@[expose] def s16c11_v1_d3 : ↥(alternatingGroup (Fin 10)) :=
  ⟨swap 8 9 * swap 9 1, by rw [Perm.mem_alternatingGroup]; decide⟩

theorem s16c11_v1_allOnes_ten_eq :
    allOnes 10 = permAct 10 (s16c11_v1_d1 : Perm (Fin 10)) (s16c11_v1_ev10 0 2) *
        (s16c11_v1_ev10 0 2)⁻¹ *
      (permAct 10 (s16c11_v1_d2 : Perm (Fin 10)) (s16c11_v1_ev10 4 6) *
        (s16c11_v1_ev10 4 6)⁻¹) *
      (permAct 10 (s16c11_v1_d3 : Perm (Fin 10)) (s16c11_v1_ev10 8 0) *
        (s16c11_v1_ev10 8 0)⁻¹) := by
  decide +kernel

theorem s16c11_v1_cover_ten_bound : ∀ (W : Type) [CommGroup W] [Finite W],
    (∀ w : W, w ^ 2 = 1) → ∀ C : ModelCover (FFModel.altDn 10) W, Nat.card C.β.ker ≤ 2 :=
  fun _ _ _ hW2 C => (s16c11_v1_ModelCover.toAltCover10 C).card_ker_le hW2

@[expose] def s16c11_v1_act10 : ↥(alternatingGroup (Fin 10)) →* MulAut ↥(coreMod 10) :=
  (coreAct 10).comp (alternatingGroup (Fin 10)).subtype

theorem s16c11_v1_act10_ker (σ : ↥(alternatingGroup (Fin 10))) (m : ↥(coreMod 10))
    (hm : (m : PermMod 10) ∈ Subgroup.zpowers (allOnes 10) ⊓ coreMod 10) :
    s16c11_v1_act10 σ m = m := by
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (mem_inf.1 hm).1
  apply Subtype.ext
  show permAct 10 (σ : Perm (Fin 10)) m = m
  rw [← hk, map_zpow]
  rfl

theorem s16c11_v1_card_ker_ten :
    Nat.card ↥((FFModel.altDn 10).ker.subgroupOf (FFModel.altDn 10).sec) = 2 := by
  have hle : Subgroup.zpowers (allOnes 10) ≤ coreMod 10 :=
    zpowers_le.2 s16c11_v1_allOnes_ten_mem
  show Nat.card ↥((Subgroup.zpowers (allOnes 10) ⊓ coreMod 10).subgroupOf (coreMod 10)) = 2
  rw [Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv, inf_eq_left.2 hle,
    Nat.card_zpowers, s16c11_v1_orderOf_allOnes_ten]

theorem s16c11_v1_coreMod_ten_gen (m : ↥(coreMod 10)) :
    m ∈ Subgroup.closure {x | ∃ σ y, x = s16c11_v1_act10 σ y * y⁻¹} := by
  have hg : ∀ σ (y : ↥(coreMod 10)),
      s16c11_v1_act10 σ y * y⁻¹ ∈
        Subgroup.closure {x | ∃ σ y, x = s16c11_v1_act10 σ y * y⁻¹} :=
    fun σ y => Subgroup.subset_closure ⟨σ, y, rfl⟩
  have h02 : s16c11_v1_ev10 0 2 ∈ coreMod 10 := by
    rw [mem_coreMod]; decide
  have h46 : s16c11_v1_ev10 4 6 ∈ coreMod 10 := by
    rw [mem_coreMod]; decide
  have h80 : s16c11_v1_ev10 8 0 ∈ coreMod 10 := by
    rw [mem_coreMod]; decide
  have h1 : (⟨allOnes 10, s16c11_v1_allOnes_ten_mem⟩ : ↥(coreMod 10)) ∈
      Subgroup.closure {x | ∃ σ y, x = s16c11_v1_act10 σ y * y⁻¹} := by
    have e : (⟨allOnes 10, s16c11_v1_allOnes_ten_mem⟩ : ↥(coreMod 10)) =
        (s16c11_v1_act10 s16c11_v1_d1 ⟨s16c11_v1_ev10 0 2, h02⟩ *
          (⟨s16c11_v1_ev10 0 2, h02⟩ : ↥(coreMod 10))⁻¹) *
        (s16c11_v1_act10 s16c11_v1_d2 ⟨s16c11_v1_ev10 4 6, h46⟩ *
          (⟨s16c11_v1_ev10 4 6, h46⟩ : ↥(coreMod 10))⁻¹) *
        (s16c11_v1_act10 s16c11_v1_d3 ⟨s16c11_v1_ev10 8 0, h80⟩ *
          (⟨s16c11_v1_ev10 8 0, h80⟩ : ↥(coreMod 10))⁻¹) := by
      apply Subtype.ext
      simp only [s16c11_v1_act10, MonoidHom.comp_apply, coreAct, Subgroup.coe_mul,
        Subgroup.coe_inv, Subtype.coe_mk]
      exact s16c11_v1_allOnes_ten_eq
    rw [e]
    exact mul_mem (mul_mem (hg _ _) (hg _ _)) (hg _ _)
  obtain ⟨a, ha, b, hb, c, hc, d, hd, hm⟩ := s16c11_v1_coreMod_ten_eq m m.2
  let m4 : ↥(coreMod 10) :=
    ⟨s16c11_v1_comm4 s16c11_v1_c123 s16c11_v1_c345 s16c11_v1_c567 s16c11_v1_c789 a b c d,
      s16c11_v1_comm4_mem _ _ _ _ (s16c11_v1_lifts123Ten_mem a ha)
        (s16c11_v1_lifts345Ten_mem b hb) (s16c11_v1_lifts567Ten_mem c hc)
        (s16c11_v1_lifts789Ten_mem d hd)⟩
  have h4 : m4 ∈ Subgroup.closure {x | ∃ σ y, x = s16c11_v1_act10 σ y * y⁻¹} := by
    have e : m4 =
        (s16c11_v1_act10 s16c11_v1_c123 ⟨a, s16c11_v1_lifts123Ten_mem a ha⟩ *
          (⟨a, s16c11_v1_lifts123Ten_mem a ha⟩ : ↥(coreMod 10))⁻¹) *
        (s16c11_v1_act10 s16c11_v1_c345 ⟨b, s16c11_v1_lifts345Ten_mem b hb⟩ *
          (⟨b, s16c11_v1_lifts345Ten_mem b hb⟩ : ↥(coreMod 10))⁻¹) *
        (s16c11_v1_act10 s16c11_v1_c567 ⟨c, s16c11_v1_lifts567Ten_mem c hc⟩ *
          (⟨c, s16c11_v1_lifts567Ten_mem c hc⟩ : ↥(coreMod 10))⁻¹) *
        (s16c11_v1_act10 s16c11_v1_c789 ⟨d, s16c11_v1_lifts789Ten_mem d hd⟩ *
          (⟨d, s16c11_v1_lifts789Ten_mem d hd⟩ : ↥(coreMod 10))⁻¹) := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul,
        Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul,
        Subgroup.coe_inv, Subgroup.coe_inv, Subgroup.coe_inv, Subgroup.coe_inv]
      rfl
    rw [e]
    exact mul_mem (mul_mem (mul_mem (hg _ _) (hg _ _)) (hg _ _)) (hg _ _)
  rcases hm with hm | hm
  · rwa [show m = m4 from Subtype.ext hm]
  · rw [show m = m4 * ⟨allOnes 10, s16c11_v1_allOnes_ten_mem⟩ from Subtype.ext hm]
    exact mul_mem h4 h1

theorem s16c11_v1_permMod_sq {n : ℕ} (x : PermMod n) : x ^ 2 = 1 := by
  apply Multiplicative.toAdd.injective
  funext i
  rw [toAdd_pow, toAdd_one, Pi.smul_apply, two_nsmul, Pi.zero_apply]
  exact zmod2_add_self _

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
