module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModS5Off

public section

namespace CFSG.Quasithin.F53Mod

open Equiv

@[expose] def Model.modA5 (M : Model 5) : Model 5 :=
  M.quot (fixW M (alternatingGroup (Fin 5)))
    (isInvSub_fixW_of_normal M alternatingGroup.normal)

@[expose] def Model.projA5 (M : Model 5) : M.W →* M.modA5.W :=
  M.projQuot (fixW M (alternatingGroup (Fin 5)))
    (isInvSub_fixW_of_normal M alternatingGroup.normal)

theorem Model.projA5_act (M : Model 5) (σ : Perm (Fin 5)) (w : M.W) :
    M.modA5.act σ (M.projA5 w) = M.projA5 (M.act σ w) :=
  M.projQuot_act _ _ σ w

theorem Model.projA5_surjective (M : Model 5) : Function.Surjective M.projA5 :=
  M.projQuot_surjective _ _

theorem Model.projA5_eq_one_iff (M : Model 5) (w : M.W) :
    M.projA5 w = 1 ↔ w ∈ fixW M (alternatingGroup (Fin 5)) := by
  have h := M.ker_projQuot (fixW M (alternatingGroup (Fin 5)))
    (isInvSub_fixW_of_normal M alternatingGroup.normal)
  rw [← h]
  exact (MonoidHom.mem_ker).symm

theorem Model.projA5_mem_fixW_iff (M : Model 5) (B : Subgroup (Perm (Fin 5))) (w : M.W) :
    M.projA5 w ∈ fixW M.modA5 B ↔ w ∈ fixQ M B (fixW M (alternatingGroup (Fin 5))) :=
  M.projQuot_mem_fixW_iff _ _ B w

theorem Model.fixW_modA5_top (M : Model 5) : fixW M.modA5 ⊤ = ⊥ := by
  have h := fixW_quot_alt5_eq_bot M (isInvSub_fixW_of_normal M alternatingGroup.normal)
  exact eq_bot_iff.mpr ((fixW_antitone M.modA5 (le_top : alternatingGroup (Fin 5) ≤ ⊤)).trans h.le)

theorem Model.index_fixW_modA5 (M : Model 5) (B : Subgroup (Perm (Fin 5))) :
    (fixW M.modA5 B).index = (fixQ M B (fixW M (alternatingGroup (Fin 5)))).index :=
  index_fixW_quot M _ _ B

theorem Model.mem_fixW_of_index_le (M : Model 5) {B : Subgroup (Perm (Fin 5))}
    (h : (fixW M B).index ≤ (fixW M.modA5 B).index) {x : M.W}
    (hx : M.projA5 x ∈ fixW M.modA5 B) : x ∈ fixW M B := by
  set Z := fixW M (alternatingGroup (Fin 5)) with hZ
  have hle : fixW M B ≤ fixQ M B Z := fixW_le_fixQ B Z
  have hidx : (fixQ M B Z).index = (fixW M.modA5 B).index := (M.index_fixW_modA5 B).symm
  have hmul := Subgroup.relIndex_mul_index hle
  have hpos : 0 < (fixQ M B Z).index := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  have h1 : (fixW M B).relIndex (fixQ M B Z) = 1 := by
    have h2 : (fixW M B).relIndex (fixQ M B Z) * (fixQ M B Z).index ≤ 1 * (fixQ M B Z).index := by
      rw [hmul, one_mul, hidx]; exact h
    have h3 := Nat.le_of_mul_le_mul_right h2 hpos
    have h4 : 0 < (fixW M B).relIndex (fixQ M B Z) := Nat.pos_of_ne_zero (by
      rw [Subgroup.relIndex]; exact Subgroup.FiniteIndex.index_ne_zero)
    omega
  have h5 := Subgroup.relIndex_eq_one.mp h1
  exact h5 ((M.projA5_mem_fixW_iff B x).mp hx)

theorem exp_two_of_offender (M : Model 5) (hf : M.Faithful) {B R : Subgroup (Perm (Fin 5))}
    (hBR : B ≤ R) (hR : Nat.card R = 4) (hexp : ∀ x ∈ B, x * x = 1) (hne : B ≠ ⊥)
    (hoff : (fixW M B).index ≤ Nat.card B) : ∀ x ∈ R, x * x = 1 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨g, hgR, hg⟩ := hcon
  have hg2 : g ^ 2 ≠ 1 := by rw [pow_two]; exact hg
  have hg1 : g ≠ 1 := fun h => hg (by rw [h, one_mul])
  have hdvd : orderOf g ∣ 4 := hR ▸ Subgroup.orderOf_dvd_natCard R hgR
  have hord : orderOf g = 4 := by
    have h4 : orderOf g ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    have hpos : 0 < orderOf g := orderOf_pos g
    have h1 : orderOf g ≠ 1 := fun h => hg1 (orderOf_eq_one_iff.mp h)
    have h2 : orderOf g ≠ 2 := fun h => hg2 (orderOf_dvd_iff_pow_eq_one.mp h.dvd)
    have h3 : orderOf g ≠ 3 := fun h => by
      have := h ▸ hdvd
      omega
    omega
  have hg4 : g ^ 4 = 1 := by rw [← hord]; exact pow_orderOf_eq_one g
  obtain ⟨d, hd⟩ : ∃ d, d = g ^ 2 := ⟨_, rfl⟩
  have hd1 : d ≠ 1 := hd ▸ hg2
  have hdd : d * d = 1 := by rw [hd, ← pow_add]; exact hg4
  have hdA : d ∈ alternatingGroup (Fin 5) := by
    rw [Perm.mem_alternatingGroup, hd, map_pow]
    exact Int.units_sq _
  have hd5 : d ^ 5 ≠ 1 := by
    have : d ^ 5 = d := by
      have h2 : d ^ 2 = 1 := by rw [pow_two]; exact hdd
      calc d ^ 5 = (d ^ 2) ^ 2 * d := by rw [← pow_mul, ← pow_succ]
        _ = d := by rw [h2, one_pow, one_mul]
    rw [this]; exact hd1
  have hRz : R = Subgroup.zpowers g := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hgR) ?_).symm
    rw [hR, Nat.card_zpowers, hord]
  have hBle : B ≤ Subgroup.zpowers d := by
    intro b hb
    have hbz : b ∈ Subgroup.zpowers g := hRz ▸ hBR hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hbz
    have h1 : g ^ (k + k) = 1 := by rw [zpow_add]; exact hexp _ hb
    have h2 : (orderOf g : ℤ) ∣ k + k := orderOf_dvd_iff_zpow_eq_one.mpr h1
    rw [hord] at h2
    obtain ⟨j, hj⟩ : ∃ j : ℤ, k = 2 * j := by
      refine ⟨k / 2, ?_⟩
      omega
    exact ⟨j, by rw [hj, zpow_mul, hd]; norm_cast⟩
  have hdcard : Nat.card (Subgroup.zpowers d) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact hdd) hd1
  have hdB : d ∈ B := by
    obtain ⟨⟨b, hbB⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
    have hbz : b ∈ Subgroup.zpowers d := hBle hbB
    rw [mem_zpowers_iff_of_pow_eq_one (m := 2) (by rw [pow_two]; exact hdd) (by norm_num)] at hbz
    obtain ⟨k, hk, rfl⟩ := hbz
    interval_cases k
    · exact absurd (pow_zero d) hb1'
    · simpa using hbB
  have hBcard : Nat.card B ≤ 2 := hdcard ▸ Subgroup.card_le_of_le hBle
  have hfix : fixW M B ≤ fixW M (Subgroup.zpowers d) :=
    fixW_antitone M (Subgroup.zpowers_le.mpr hdB)
  have hidx : idx M d ≤ (fixW M B).index := by
    have h1 := Subgroup.index_dvd_of_le hfix
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero) h1
  have hcf := cf_small M (fixW_alt5_ne_top_of_faithful hf) hdA hd1 hd5
  omega

theorem mem_fixW_zpowers_iff {n : ℕ} (M : Model n) (ρ : Perm (Fin n)) (w : M.W) :
    w ∈ fixW M (Subgroup.zpowers ρ) ↔ M.act ρ w = w := by
  rw [Subgroup.zpowers_eq_closure, mem_fixW_closure]
  simp

theorem exists_fixed_of_lift (M : Model 5) {B' : Subgroup (Perm (Fin 5))} {ρ : Perm (Fin 5)}
    (hρ : ρ * ρ = 1) (hBρ : ∀ b ∈ B', ρ * b * ρ ∈ B')
    (hS : S5Syl ≤ B' ⊔ Subgroup.zpowers ρ)
    (hE : ∀ x : M.W, M.projA5 x ∈ fixW M.modA5 B' → x ∈ fixW M B')
    (hy : ¬ fixW M.modA5 B' ≤ fixW M.modA5 S5Syl) :
    ∃ v ∈ fixW M S5Syl, v ∉ fixW M ⊤ := by
  obtain ⟨y, hyB, hyS⟩ := IsConcreteLE.not_le_iff_exists.mp hy
  obtain ⟨x, rfl⟩ := M.projA5_surjective y
  have hxB : x ∈ fixW M B' := hE x hyB
  have hρρ : ∀ w : M.W, M.act ρ (M.act ρ w) = w := fun w => by
    rw [← act_mul_apply, hρ]; simp
  refine ⟨x * M.act ρ x, ?_, ?_⟩
  · have h1 : x * M.act ρ x ∈ fixW M B' := by
      refine Subgroup.mul_mem _ hxB (fun b hb => ?_)
      have e : b * ρ = ρ * (ρ * b * ρ) := by
        calc b * ρ = (ρ * ρ) * b * ρ := by rw [hρ, one_mul]
          _ = ρ * (ρ * b * ρ) := by group
      rw [← act_mul_apply, e, act_mul_apply, hxB _ (hBρ b hb)]
    have h2 : x * M.act ρ x ∈ fixW M (Subgroup.zpowers ρ) := by
      rw [mem_fixW_zpowers_iff, map_mul, hρρ, mul_comm]
    have h3 : x * M.act ρ x ∈ fixW M (B' ⊔ Subgroup.zpowers ρ) := by
      rw [fixW_sup]; exact ⟨h1, h2⟩
    exact fixW_antitone M hS h3
  · intro hv
    have hv' : x * M.act ρ x ∈ fixW M (alternatingGroup (Fin 5)) := fixW_antitone M le_top hv
    rw [← M.projA5_eq_one_iff, map_mul, ← M.projA5_act] at hv'
    have hyρ : M.modA5.act ρ (M.projA5 x) = M.projA5 x := by
      have h1 : M.projA5 x * M.modA5.act ρ (M.projA5 x) = 1 := hv'
      have h2 := M.modA5.sq (M.projA5 x)
      calc M.modA5.act ρ (M.projA5 x) = (M.projA5 x)⁻¹ * (M.projA5 x * M.modA5.act ρ (M.projA5 x)) := by
            group
        _ = (M.projA5 x)⁻¹ := by rw [h1, mul_one]
        _ = M.projA5 x := (inv_eq_of_mul_eq_one_right h2)
    apply hyS
    have h3 : M.projA5 x ∈ fixW M.modA5 (B' ⊔ Subgroup.zpowers ρ) := by
      rw [fixW_sup]; exact ⟨hyB, (mem_fixW_zpowers_iff _ _ _).mpr hyρ⟩
    exact fixW_antitone M.modA5 hS h3

theorem card_fixW_of_iso {n : ℕ} {M N : Model n} (e : M.Iso N) (B : Subgroup (Perm (Fin n))) :
    Nat.card (fixW N B) = Nat.card (fixW M B) := by
  rw [e.fixW_eq B]
  exact Subgroup.card_map_of_injective e.toMulEquiv.injective

theorem S5That_le_S5Syl : S5That ≤ S5Syl := by
  unfold S5That
  rw [Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact Subgroup.subset_closure (by simp)
  · show swap (1 : Fin 5) 3 ∈ S5Syl
    rw [mem_S5Syl_iff]; unfold S5SylF; decide +kernel

theorem S5Syl_le_sup_that : S5Syl ≤ S5That ⊔ Subgroup.zpowers (swap (0 : Fin 5) 1 * swap 2 3) := by
  unfold S5Syl
  rw [Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · have h1 : swap (0 : Fin 5) 1 * swap 1 2 * swap 2 3 =
        (swap (0 : Fin 5) 1 * swap 1 2 * swap 2 3 * (swap 0 1 * swap 2 3)) *
          (swap (0 : Fin 5) 1 * swap 2 3) := by
      decide +kernel
    have h2 : swap (0 : Fin 5) 1 * swap 1 2 * swap 2 3 * (swap 0 1 * swap 2 3) ∈ S5That :=
      (mem_S5That_iff _).mpr (by unfold S5ThatF; decide +kernel)
    show _ ∈ _
    rw [h1]
    exact Subgroup.mul_mem_sup h2 (Subgroup.mem_zpowers _)
  · exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))

theorem S5Syl_le_sup_T : S5Syl ≤ S5T ⊔ Subgroup.zpowers (swap (0 : Fin 5) 2) := by
  unfold S5Syl
  rw [Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · have h1 : swap (0 : Fin 5) 1 * swap 1 2 * swap 2 3 =
        (swap (0 : Fin 5) 1 * swap 1 2 * swap 2 3 * swap 0 2) * swap (0 : Fin 5) 2 := by
      decide +kernel
    have h2 : swap (0 : Fin 5) 1 * swap 1 2 * swap 2 3 * swap 0 2 ∈ S5T :=
      (mem_S5T_iff _).mpr (by unfold S5TF; decide +kernel)
    show _ ∈ _
    rw [h1]
    exact Subgroup.mul_mem_sup h2 (Subgroup.mem_zpowers _)
  · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

theorem that_hBρ : ∀ b ∈ S5That, (swap (0 : Fin 5) 1 * swap 2 3) * b * (swap (0 : Fin 5) 1 * swap 2 3) ∈ S5That := by
  intro b hb
  rw [mem_S5That_iff] at hb ⊢
  revert b
  unfold S5ThatF
  decide +kernel

theorem T_hBρ : ∀ b ∈ S5T, (swap (0 : Fin 5) 2) * b * (swap (0 : Fin 5) 2) ∈ S5T := by
  intro b hb
  rw [mem_S5T_iff] at hb ⊢
  revert b
  unfold S5TF
  decide +kernel

theorem lift_orth (M : Model 5) (e : M.modA5.Iso orth)
    (hE : ∀ x : M.W, M.projA5 x ∈ fixW M.modA5 S5That → x ∈ fixW M S5That) :
    ∃ v ∈ fixW M S5Syl, v ∉ fixW M ⊤ := by
  refine exists_fixed_of_lift M (ρ := swap (0 : Fin 5) 1 * swap 2 3) (by decide +kernel)
    that_hBρ S5Syl_le_sup_that hE ?_
  intro hle
  have h1 : Nat.card (fixW orth S5That) = 4 := by
    have := congrArg (fun p => p.2.1) profile_orth.2.2.1
    simpa [profile] using this
  have h2 : Nat.card (fixW orth S5Syl) = 2 := by
    have := congrArg (fun p => p.2.1) profile_orth.2.2.2.2.2
    simpa [profile] using this
  have heq : fixW M.modA5 S5That = fixW M.modA5 S5Syl :=
    le_antisymm hle (fixW_antitone _ S5That_le_S5Syl)
  have h3 := card_fixW_of_iso e S5That
  have h4 := card_fixW_of_iso e S5Syl
  rw [heq] at h3
  omega

theorem lift_nat (M : Model 5) (e : M.modA5.Iso nat)
    (hE : ∀ x : M.W, M.projA5 x ∈ fixW M.modA5 S5T → x ∈ fixW M S5T) :
    ∃ v ∈ fixW M S5Syl, v ∉ fixW M ⊤ := by
  refine exists_fixed_of_lift M (ρ := swap (0 : Fin 5) 2) (by decide +kernel)
    T_hBρ S5Syl_le_sup_T hE ?_
  intro hle
  have h1 : Nat.card (fixW nat S5T) = 4 := by
    have := congrArg (fun p => p.2.1) profile_nat.2.2.2.1
    simpa [profile] using this
  have h2 : Nat.card (fixW nat S5Syl) = 2 := by
    have := congrArg (fun p => p.2.1) profile_nat.2.2.2.2.2
    simpa [profile] using this
  have heq : fixW M.modA5 S5T = fixW M.modA5 S5Syl :=
    le_antisymm hle (fixW_antitone _ inf_le_left)
  have h3 := card_fixW_of_iso e S5T
  have h4 := card_fixW_of_iso e S5Syl
  rw [heq] at h3
  omega

theorem swap_mem_S5Syl : ∀ x y : Fin 5, x ≠ y → swap x y ∈ S5SylF →
    swap x y = swap 0 2 ∨ swap x y = swap 1 3 := by
  unfold S5SylF
  decide +kernel

theorem swap13_conj : swap (1 : Fin 5) 3 =
    (swap (0 : Fin 5) 1 * swap 2 3) * swap 0 2 * (swap (0 : Fin 5) 1 * swap 2 3)⁻¹ := by
  decide +kernel

theorem swap02_conj : swap (0 : Fin 5) 2 =
    (swap (0 : Fin 5) 1 * swap 2 3) * swap 1 3 * (swap (0 : Fin 5) 1 * swap 2 3)⁻¹ := by
  decide +kernel

theorem idx_orth_swap02 : idx orth (swap (0 : Fin 5) 2) = 2 := by
  have h1 : Nat.card (fixW orth (Subgroup.zpowers (swap (0 : Fin 5) 2))) = 8 := by
    have := congrArg (fun p => p.2.1) profile_orth.1
    simpa [profile] using this
  have h2 := Subgroup.card_mul_index (fixW orth (Subgroup.zpowers (swap (0 : Fin 5) 2)))
  rw [h1, card_orth] at h2
  unfold idx
  omega

theorem idx_orth_swap13 : idx orth (swap (1 : Fin 5) 3) = 2 := by
  rw [swap13_conj, idx_conj, idx_orth_swap02]

theorem S5That_eq_fix {M : Model 5}
    (h1 : ∀ x : M.W, M.projA5 x ∈ fixW M.modA5 (Subgroup.zpowers (swap (0 : Fin 5) 2)) →
      x ∈ fixW M (Subgroup.zpowers (swap (0 : Fin 5) 2)))
    (h2 : ∀ x : M.W, M.projA5 x ∈ fixW M.modA5 (Subgroup.zpowers (swap (1 : Fin 5) 3)) →
      x ∈ fixW M (Subgroup.zpowers (swap (1 : Fin 5) 3))) :
    ∀ x : M.W, M.projA5 x ∈ fixW M.modA5 S5That → x ∈ fixW M S5That := by
  intro x hx
  show x ∈ fixW M (Subgroup.closure {swap (0 : Fin 5) 2, swap 1 3})
  rw [mem_fixW_closure]
  have hle1 : Subgroup.zpowers (swap (0 : Fin 5) 2) ≤ S5That :=
    Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
  have hle2 : Subgroup.zpowers (swap (1 : Fin 5) 3) ≤ S5That :=
    Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
  rintro s (rfl | rfl)
  · exact (mem_fixW_zpowers_iff M _ _).mp (h1 x (fixW_antitone _ hle1 hx))
  · exact (mem_fixW_zpowers_iff M _ _).mp (h2 x (fixW_antitone _ hle2 hx))

theorem m10 (M : Model 5) (hf : M.Faithful) {B : Subgroup (Perm (Fin 5))} (hB : B ≤ S5Syl)
    (hexp : ∀ x ∈ B, x * x = 1) (hne : B ≠ ⊥) (hoff : (fixW M B).index ≤ Nat.card B) :
    ∃ v ∈ fixW M S5Syl, v ∉ fixW M ⊤ := by
  have hA := fixW_alt5_ne_top_of_faithful hf
  have hnt : ∃ w : M.modA5.W, w ≠ 1 := by
    by_contra h
    push Not at h
    apply hA
    rw [eq_top_iff]
    intro w _
    exact (M.projA5_eq_one_iff w).mp (h _)
  have hoff' : (fixW M.modA5 B).index ≤ Nat.card B := by
    rw [M.index_fixW_modA5]
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero)
      (Subgroup.index_dvd_of_le (fixW_le_fixQ B _))).trans hoff
  obtain ⟨hidx, hcases⟩ := offender_dichotomy M.modA5 hnt M.fixW_modA5_top hne hexp hoff'
  have hle : (fixW M B).index ≤ (fixW M.modA5 B).index := hidx ▸ hoff
  rcases le_syl_cases hB hexp hne with ⟨t, htB, ht1, hBt, hc2⟩ | hT | hThat
  · rcases hcases with ⟨⟨e⟩, hsub⟩ | ⟨_, h4, _⟩
    · rcases hsub with ⟨t', ⟨x, y, hxy, rfl⟩, hBt'⟩ | ⟨h4, _⟩
      · have hmem : swap x y ∈ S5Syl := hB (by rw [hBt']; exact Subgroup.mem_zpowers _)
        have hu := swap_mem_S5Syl x y hxy ((mem_S5Syl_iff _).mp hmem)
        have hi : idx M (swap x y) ≤ 2 := by
          have h2 : (fixW M B).index ≤ 2 := hc2 ▸ hoff
          rw [hBt'] at h2
          exact h2
        have hu1 : idx M (swap 0 2) ≤ 2 ∧ idx M (swap 1 3) ≤ 2 := by
          rcases hu with hu | hu
          · rw [hu] at hi
            refine ⟨hi, ?_⟩
            rw [swap13_conj, idx_conj]; exact hi
          · rw [hu] at hi
            refine ⟨?_, hi⟩
            rw [swap02_conj, idx_conj]; exact hi
        refine lift_orth M e (S5That_eq_fix ?_ ?_)
        · intro z hz
          refine M.mem_fixW_of_index_le ?_ hz
          show idx M (swap 0 2) ≤ idx M.modA5 (swap 0 2)
          rw [← e.idx_eq, idx_orth_swap02]; exact hu1.1
        · intro z hz
          refine M.mem_fixW_of_index_le ?_ hz
          show idx M (swap 1 3) ≤ idx M.modA5 (swap 1 3)
          rw [← e.idx_eq, idx_orth_swap13]; exact hu1.2
      · omega
    · omega
  · subst hT
    rcases hcases with ⟨_, hsub⟩ | ⟨⟨e⟩, _, _⟩
    · exfalso
      rcases hsub with ⟨t, ht, hBt⟩ | ⟨_, hnA⟩
      · have htT : t ∈ S5T := by rw [hBt]; exact Subgroup.mem_zpowers _
        have h1 := (isSwap_iff t).mp ht
        have h2 := Perm.mem_alternatingGroup.mp (Subgroup.mem_inf.mp htT).2
        exact h1.2.2 h2
      · exact hnA inf_le_right
    · exact lift_nat M e (fun z hz => M.mem_fixW_of_index_le hle hz)
  · subst hThat
    rcases hcases with ⟨⟨e⟩, _⟩ | ⟨_, _, hA5⟩
    · exact lift_orth M e (fun z hz => M.mem_fixW_of_index_le hle hz)
    · exfalso
      have hmem : swap (0 : Fin 5) 2 ∈ S5That := Subgroup.subset_closure (by simp)
      have := Perm.mem_alternatingGroup.mp (hA5 hmem)
      rw [Perm.sign_swap (by decide)] at this
      revert this; decide

end CFSG.Quasithin.F53Mod
