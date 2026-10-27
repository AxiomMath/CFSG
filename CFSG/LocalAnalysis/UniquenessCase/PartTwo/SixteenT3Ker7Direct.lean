module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3Ker7
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10MBarFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10DirectSupport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {T : Type} [CommGroup T] [Finite T]

private theorem s16t_eq_one_of_fix_summands {ι : Type} {Y : ι → Subgroup T}
    (hsup : ⨆ i, Y i = ⊤) {x : MulAut T} (h : ∀ i, ∀ v ∈ Y i, x v = v) : x = 1 := by
  have hle : (⨆ i, Y i) ≤ fixV (Subgroup.zpowers x) :=
    iSup_le fun i v hv => mem_fixV_zpowers_iff_apply.2 (h i v hv)
  rw [hsup] at hle
  ext v
  exact mem_fixV_zpowers_iff_apply.1 (hle (Subgroup.mem_top v))

theorem s16t_stab_trivial_seven (hT : ∀ t : T, t ^ 2 = 1) {X A : Subgroup (MulAut T)}
    {r : ℕ} (hr : 1 < r) (hA : IsElemAbelianOfRank 7 r ↥A) (hAP : A ≤ pCoreOf 7 X)
    (hS : SymSumOfConj X (⊤ : Subgroup T) r (dParam 7)) :
    ∃ (ι : Type) (_ : Fintype ι) (Y : ι → Subgroup T), SymSumFamily X Y r (dParam 7) ∧
      ∀ φ ∈ X, φ ^ 2 = 1 → ∀ i, (Y i).map φ.toMonoidHom = Y i → ∀ y ∈ Y i, φ y = y := by
  classical
  obtain ⟨ι, hι, Y, hY⟩ := s16c1610_symSumFamily_of_symSumOfConj hS
  letI : Fintype ι := hι
  obtain ⟨Q, hQX, hQp, hQne, hnorm, hQY⟩ :=
    s16t_ker7_exists_Q hT hr hA hAP hY.indep hY.inj hY.sup hY.card hY.rank hY.perm hY.surj
  refine ⟨ι, hι, Y, hY, ?_⟩
  intro φ hφX hφ2 i hφY y hy
  by_contra hne
  have hφne : φ ≠ 1 := fun h => hne (by simp [h])
  have horder2 : orderOf φ = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime hφ2 hφne
  have hrki : rk ↥(Y i) = 3 := by rw [hY.rank i, s16c1610_dParam_seven]
  have hQi := s16n9b_case4_aut_norm7 hT hrki hQp (fun q hq => hQY q hq i)
    ⟨1, by simpa using horder2⟩ hφY (hnorm φ hφX) ⟨y, hy, hne⟩
  have hQall : ∀ q ∈ Q, ∀ j, ∀ v ∈ Y j, q v = v := by
    intro q hq j v hv
    obtain ⟨g, hgX, hg⟩ := hY.surj (Equiv.swap i j)
    have hgi : (Y i).map g.toMonoidHom = Y j := by
      rw [hg i, Equiv.swap_apply_left]
    have hv' : v ∈ (Y i).map g.toMonoidHom := by rw [hgi]; exact hv
    obtain ⟨v₀, hv₀, rfl⟩ := Subgroup.mem_map.1 hv'
    have hq' : g⁻¹ * q * g ∈ Q := by
      have h1 := Subgroup.mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom hq
      rw [hnorm g⁻¹ (X.inv_mem hgX)] at h1
      simpa [MulAut.conj_apply] using h1
    have h2 : (g⁻¹ * q * g) v₀ = v₀ := hQi _ hq' v₀ hv₀
    have h3 : g⁻¹ (q (g v₀)) = v₀ := by simpa [MulAut.mul_apply] using h2
    have h4 : q (g v₀) = g v₀ := by
      have := congrArg g h3
      simpa using this
    exact h4
  obtain ⟨q, hq1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hQne
  exact hq1 (Subtype.ext (s16t_eq_one_of_fix_summands hY.sup (hQall q.1 q.2)))

theorem s16t_false_of_direct_seven (hT : ∀ t : T, t ^ 2 = 1) {X A B : Subgroup (MulAut T)}
    {r : ℕ} (hr : 1 < r) (hA : IsElemAbelianOfRank 7 r ↥A) (hAP : A ≤ pCoreOf 7 X)
    (hS : SymSumOfConj X (⊤ : Subgroup T) r (dParam 7))
    (hBX : B ≤ X) (hB1 : B ≠ ⊥) (hB2 : IsElemAbelian2 B) {Ut : Subgroup T} (hUt : Ut ≠ ⊤)
    (hk : rkIdx Ut ≤ 2) (hA3 : ∀ b ∈ B, b ≠ 1 → fixV (Subgroup.zpowers b) ≤ Ut)
    (hA4 : ∀ b ∈ B, b ≠ 1 → ∀ w, w ∈ Ut ↔ w * (b w)⁻¹ ∈ fixV B) : False := by
  classical
  obtain ⟨ι, hι, Y, hY, hstab⟩ := s16t_stab_trivial_seven hT hr hA hAP hS
  letI : Fintype ι := hι
  obtain ⟨i, hi⟩ : ∃ i, ¬ Y i ≤ Ut := by
    by_contra hcon
    exact hUt (eq_top_iff.mpr (by
      rw [← hY.sup]
      exact iSup_le fun i => by
        by_contra hi
        exact hcon ⟨i, hi⟩))
  have hlt : rkIdx Ut < rk ↥(Y i) := by
    rw [hY.rank i, s16c1610_dParam_seven]
    omega
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

theorem s16t_two_lt_mParam_of_case4_seven (hT : ∀ t : T, t ^ 2 = 1)
    {X A : Subgroup (MulAut T)} {r : ℕ} (hr : 1 < r) (hA : IsElemAbelianOfRank 7 r ↥A)
    (hAP : A ≤ pCoreOf 7 X) (hS : SymSumOfConj X (⊤ : Subgroup T) r (dParam 7)) :
    2 < E3.mParam X := by
  classical
  obtain ⟨ι, hι, Y, hind, hinj, hsup, hcard, hrk, hperm, hsurj⟩ := s16n9b_case4_data hS
  obtain ⟨Q, hQX, hQp, hQne, hnorm, hQY⟩ :=
    s16t_ker7_exists_Q hT hr hA hAP hind hinj hsup hcard hrk hperm hsurj
  have hd7 : dParam 7 = 3 := s16c1610_dParam_seven
  have hinv : ∀ φ ∈ X, orderOf φ = 2 → 3 ≤ rkIdx (fixV (Subgroup.zpowers φ)) := by
    intro φ hφX hφ
    by_contra hlt
    push Not at hlt
    have hC_lt : rkIdx (fixV (Subgroup.zpowers φ)) < 2 * dParam 7 := by
      rw [hd7]
      omega
    rcases s16n9b_case4_rank_moved hT hind hinj hrk (hperm φ hφX) hC_lt with
      hid | ⟨a, b, hab, hφa, hφb, -⟩
    · have hφne : φ ≠ 1 := by
        rintro rfl
        simp at hφ
      obtain ⟨i, y, hy, hφy⟩ : ∃ i, ∃ y ∈ Y i, φ y ≠ y := by
        by_contra hcon
        push Not at hcon
        exact hφne (s16t_eq_one_of_fix_summands hsup hcon)
      have hrki : rk ↥(Y i) = 3 := by rw [hrk i, hd7]
      have hQi := s16n9b_case4_aut_norm7 hT hrki hQp (fun q hq => hQY q hq i)
        ⟨1, by simpa using hφ⟩ (hid i) (hnorm φ hφX) ⟨y, hy, hφy⟩
      have hQall : ∀ q ∈ Q, ∀ j, ∀ v ∈ Y j, q v = v := by
        intro q hq j v hv
        obtain ⟨g, hgX, hg⟩ := hsurj (Equiv.swap i j)
        have hgi : (Y i).map g.toMonoidHom = Y j := by
          rw [hg i, Equiv.swap_apply_left]
        have hv' : v ∈ (Y i).map g.toMonoidHom := by
          rw [hgi]
          exact hv
        obtain ⟨v₀, hv₀, rfl⟩ := Subgroup.mem_map.1 hv'
        have hq' : g⁻¹ * q * g ∈ Q := by
          have h1 := Subgroup.mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom hq
          rw [hnorm g⁻¹ (X.inv_mem hgX)] at h1
          simpa [MulAut.conj_apply] using h1
        have h2 : (g⁻¹ * q * g) v₀ = v₀ := hQi _ hq' v₀ hv₀
        have h3 : g⁻¹ (q (g v₀)) = v₀ := by simpa [MulAut.mul_apply] using h2
        have h4 : q (g v₀) = g v₀ := by
          have := congrArg g h3
          simpa using this
        exact h4
      obtain ⟨q, hq1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hQne
      exact hq1 (Subtype.ext (s16t_eq_one_of_fix_summands hsup (hQall q.1 q.2)))
    · have h := s16c1610_le_rkIdx_fixV_swap hT (hind.pairwiseDisjoint hab) (hrk a) (hrk b) hφa hφb
      rw [hd7] at h
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
    have := hinv t htX ht2
    omega
  · have hpos : 0 < Fintype.card ι := by omega
    obtain ⟨i⟩ := Fintype.card_pos_iff.1 hpos
    have h1 : rk ↥(Y i) ≤ rk ↥(⊤ : Subgroup T) := rk_mono le_top
    rw [rk_top, hrk i, hd7] at h1
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
