module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3TenFam
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10MBarFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10DirectSupport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {T : Type} [CommGroup T] [Finite T]

private theorem s16t_odd_eq_one_of_fix_summands {ι : Type} {Y : ι → Subgroup T}
    (hsup : ⨆ i, Y i = ⊤) {x : MulAut T} (h : ∀ i, ∀ v ∈ Y i, x v = v) : x = 1 := by
  have hle : (⨆ i, Y i) ≤ fixV (Subgroup.zpowers x) :=
    iSup_le fun i v hv => mem_fixV_zpowers_iff_apply.2 (h i v hv)
  rw [hsup] at hle
  ext v
  exact mem_fixV_zpowers_iff_apply.1 (hle (Subgroup.mem_top v))

theorem s16t_false_of_blocks_odd (hT : ∀ t : T, t ^ 2 = 1) {X B : Subgroup (MulAut T)}
    {ι : Type} [Fintype ι] {Y : ι → Subgroup T} {d : ℕ} (hY : S16tBlocks X Y d)
    (hstab : ∀ φ ∈ X, φ ^ 2 = 1 → ∀ i, (Y i).map φ.toMonoidHom = Y i → ∀ y ∈ Y i, φ y = y)
    (hBX : B ≤ X) (hB1 : B ≠ ⊥) (hB2 : IsElemAbelian2 B) {Ut : Subgroup T} (hUt : Ut ≠ ⊤)
    (hk : rkIdx Ut < d) (hA3 : ∀ b ∈ B, b ≠ 1 → fixV (Subgroup.zpowers b) ≤ Ut)
    (hA4 : ∀ b ∈ B, b ≠ 1 → ∀ w, w ∈ Ut ↔ w * (b w)⁻¹ ∈ fixV B) : False := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, ¬ Y i ≤ Ut := by
    by_contra hcon
    exact hUt (eq_top_iff.mpr (by
      rw [← hY.sup]
      exact iSup_le fun i => by
        by_contra hi
        exact hcon ⟨i, hi⟩))
  have hlt : rkIdx Ut < rk ↥(Y i) := by
    rw [hY.rank i]
    exact hk
  have hinf_ne : Y i ⊓ Ut ≠ ⊥ := s16c1610_inf_ne_bot_of_rkIdx_lt hT hlt
  obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hinf_ne
  have hui : (u : T) ∈ Y i := u.2.1
  have hUu : (u : T) ∈ Ut := u.2.2
  have hu_ne : (u : T) ≠ 1 := fun h => hu1 (Subtype.ext h)
  have hclaim : ∃ Y' : Subgroup T,
      ∀ b ∈ B, (Y i).map b.toMonoidHom = Y i ∨ (Y i).map b.toMonoidHom = Y' := by
    by_cases hall : ∀ b ∈ B, (Y i).map b.toMonoidHom = Y i
    · exact ⟨Y i, fun b hb => Or.inl (hall b hb)⟩
    · obtain ⟨b, hb⟩ := not_forall.mp hall
      have hb' : b ∈ B ∧ (Y i).map b.toMonoidHom ≠ Y i := by
        simpa only [not_imp] using hb
      obtain ⟨hbB, hbmap⟩ := hb'
      have hbX : b ∈ X := hBX hbB
      obtain ⟨j, hbj⟩ := hY.perm b hbX i
      have hji : j ≠ i := by
        rintro rfl
        exact hbmap hbj
      have hb1 : b ≠ 1 := by
        rintro rfl
        exact hbmap (by
          show (Y i).map (MonoidHom.id T) = Y i
          exact Subgroup.map_id (K := Y i))
      have hbu2 : b (u : T) * b (u : T) = 1 := by
        rw [← pow_two]
        exact hT (b (u : T))
      have hbu_inv : (b (u : T))⁻¹ = b (u : T) := mul_eq_one_iff_inv_eq.mp hbu2
      have hfixu : (u : T) * b (u : T) ∈ fixV B := by
        have h := (hA4 b hbB hb1 (u : T)).mp hUu
        rwa [hbu_inv] at h
      refine ⟨Y j, ?_⟩
      exact s16c1610_orbit_pair hY.indep hB2.1 (fun b hb => hY.perm b (hBX hb))
        (Ne.symm hji) hbB hbj hui hu_ne hfixu
  obtain ⟨Y', hY'⟩ := hclaim
  have hcard_le : Nat.card B ≤ 2 * Nat.card ↥(B ⊓ stabSub (Y i)) :=
    s16c1610_card_le_two_mul_stab (Y := Y i) (Y' := Y') hY'
  have hstab_bot : B ⊓ stabSub (Y i) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro b hb
    obtain ⟨hbB, hbstab⟩ := hb
    have hbmap : (Y i).map b.toMonoidHom = Y i :=
      (s15_Lin_map_eq_iff_mem_stabSub (Y i) b).mpr hbstab
    have hfix : ∀ y ∈ Y i, b y = y := hstab b (hBX hbB) (hB2.2 b hbB) i hbmap
    have hbcent : b ∈ centSub (Y i) := fun y hy => hfix y hy
    have hmem : b ∈ B ⊓ centSub (Y i) := ⟨hbB, hbcent⟩
    have hbot : B ⊓ centSub (Y i) = ⊥ := s16c1610_inf_centSub_eq_bot hA3 hi
    rw [hbot] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hcardB : Nat.card B ≤ 2 := by
    have h := hcard_le
    rw [hstab_bot, Subgroup.card_bot] at h
    simpa using h
  exact hUt (s16c1610_ut_eq_top_of_card_le_two hT hB1 hB2 hcardB hA4)

theorem s16t_le_mParam_of_blocks (hT : ∀ t : T, t ^ 2 = 1) {X : Subgroup (MulAut T)} {ι : Type}
    [Fintype ι] {Y : ι → Subgroup T} {d : ℕ} (hY : S16tBlocks X Y d)
    (hstab : ∀ φ ∈ X, φ ^ 2 = 1 → ∀ i, (Y i).map φ.toMonoidHom = Y i → ∀ y ∈ Y i, φ y = y) :
    d ≤ E3.mParam X := by
  classical
  have hinv : ∀ φ ∈ X, orderOf φ = 2 → d ≤ rkIdx (fixV (Subgroup.zpowers φ)) := by
    intro φ hφX hφ
    by_contra hlt
    push Not at hlt
    have hφ2 : φ ^ 2 = 1 := by
      rw [← hφ]
      exact pow_orderOf_eq_one φ
    have hC_lt : rkIdx (fixV (Subgroup.zpowers φ)) < 2 * d := by omega
    rcases s16n9b_case4_rank_moved hT hY.indep hY.inj hY.rank (hY.perm φ hφX) hC_lt with
      hid | ⟨a, b, hab, hφa, hφb, -⟩
    · have hone : φ = 1 :=
        s16t_odd_eq_one_of_fix_summands hY.sup fun i v hv => hstab φ hφX hφ2 i (hid i) v hv
      rw [hone, orderOf_one] at hφ
      omega
    · have h := s16c1610_le_rkIdx_fixV_swap hT (hY.indep.pairwiseDisjoint hab) (hY.rank a)
        (hY.rank b) hφa hφb
      omega
  unfold E3.mParam
  split_ifs with hev
  · set S : Set ℕ := {n | ∃ t ∈ X, orderOf t = 2 ∧ n = rkIdx (fixV (Subgroup.zpowers t))} with hS'
    have hne : S.Nonempty := by
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) 2 (even_iff_two_dvd.1 hev)
      exact ⟨_, (x : MulAut T), x.2, by rw [Subgroup.orderOf_coe]; exact hx, rfl⟩
    obtain ⟨t, htX, ht2, hn⟩ := Nat.sInf_mem hne
    rw [hn]
    exact hinv t htX ht2
  · have hpos : 0 < Fintype.card ι := by
      have := hY.card
      omega
    obtain ⟨i⟩ := Fintype.card_pos_iff.1 hpos
    have h1 : rk ↥(Y i) ≤ rk ↥(⊤ : Subgroup T) := rk_mono le_top
    rw [rk_top, hY.rank i] at h1
    exact h1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
