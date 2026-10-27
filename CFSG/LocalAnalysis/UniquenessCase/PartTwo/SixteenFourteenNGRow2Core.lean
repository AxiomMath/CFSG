module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFourteenNGRow2Fam
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFourteenNGRow2Odd
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFourteenNGRow2Pick

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s1614_row2_zpowers_stable {W : Type} [CommGroup W] {t : MulAut W}
    (ht2 : t * t = 1) {J : Subgroup W} (hJ : J.map t.toMonoidHom = J) :
    ∀ x ∈ Subgroup.zpowers t, ∀ w ∈ J, x w ∈ J := by
  intro x hx w hw
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  have htw : ∀ w ∈ J, t w ∈ J := fun w hw => by
    have h : t w ∈ J.map t.toMonoidHom := ⟨w, hw, rfl⟩
    rwa [hJ] at h
  obtain ⟨n, hn | hn⟩ := Int.even_or_odd' k
  · have h : t ^ k = 1 := by rw [hn, zpow_mul, zpow_two, ht2, one_zpow]
    rw [h]
    simpa using hw
  · have h : t ^ k = t := by
      rw [hn, zpow_add, zpow_mul, zpow_two, ht2, one_zpow, one_mul, zpow_one]
    rw [h]
    exact htw w hw

theorem s1614_row2_hrow (D : Data G) {V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hc : Counterex16 D ⊥ V L hV) (hS2 : Case168_2Small D ⊥ V hV L) (hk1 : D.k = 1) :
    ∀ t ∈ Mbar D.M ⊥ V hV, orderOf t = 2 → D.k < rkIdx (fixV (Subgroup.zpowers t)) →
      ∀ W : Subgroup (Vtil ⊥ V hV), W ≤ fixV (Subgroup.zpowers t) → rkIdx W ≤ D.k + 2 →
        ∃ z ∈ W, z ≠ 1 ∧ ∃ p ∈ D.sig, ∃ B : Subgroup (MulAut (Vtil ⊥ V hV)),
          B ≤ Mbar D.M ⊥ V hV ∧ IsPGroup p ↥B ∧ ¬ IsCyclic ↥B ∧ z ∈ fixV B := by
  classical
  intro t htM ht2 hkt W hWC hW
  have hW2 : ∀ w : Vtil ⊥ V hV, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one ⊥ V hV
  have hWsq : ∀ x : Vtil ⊥ V hV, x * x = 1 := fun x => by rw [← pow_two]; exact hW2 x
  have hD3 : (3 : ℕ) ∈ D.sig := by
    rw [hS2.2.2]
    exact Set.mem_singleton 3
  have hLM : lBar ⊥ V hV L ≤ Mbar D.M ⊥ V hV := barSub_mono ⊥ V hV hc.setting.hyp151.le
  obtain ⟨J₀, J₁, hJ₀, hJ₁, hinf, hsup, h4, hhyp⟩ := s1614_row2_summand D hS2
  have ht2' : t * t = 1 := by
    rw [← pow_two, ← ht2]
    exact pow_orderOf_eq_one t
  have hEsq : ∀ e ∈ Subgroup.zpowers t, e * e = 1 := by
    intro e he
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 he
    rw [← zpow_add, ← two_mul, zpow_mul, zpow_two, ht2', one_zpow]
  have hfix3 : rkIdx (fixV (Subgroup.zpowers t)) ≤ 3 :=
    (rkIdx_anti hWC).trans (hW.trans (by omega))
  obtain ⟨hcomm, hfaith, hcsub, -⟩ := s16c15t_frame D hc hS2 hJ₀ hJ₁ hinf hsup h4
    (E := Subgroup.zpowers t) ((Subgroup.zpowers_le).2 htM) hEsq hfix3
  have htc : ∀ y ∈ oddBar D.M ⊥ V hV, t * y = y * t := hcomm t (Subgroup.mem_zpowers t)
  have htJ : J₀.map t.toMonoidHom = J₀ := s1614_row2_stab D hc hS2 hJ₀ htM ht2' htc
  have hstab := s1614_row2_zpowers_stable ht2' htJ
  have hcomm_ne : commSub J₀ (Subgroup.zpowers t) ≠ ⊥ := by
    intro h
    rw [commSub_eq_bot_iff] at h
    have h1 : t = 1 := hfaith t (Subgroup.mem_zpowers t) fun x hx =>
      mem_fixV_zpowers_iff_apply.1 (h hx)
    rw [h1, orderOf_one] at ht2
    omega
  have hcomm_rk : rk ↥(commSub J₀ (Subgroup.zpowers t)) = 1 := by
    have h1 := hcsub t (Subgroup.mem_zpowers t)
    have h0 : rk ↥(commSub J₀ (Subgroup.zpowers t)) ≠ 0 := fun h0 =>
      hcomm_ne ((rk_eq_zero_iff hW2).1 h0)
    omega
  have hidx := rk_commSub_add_rk_inf_fixV (g := t) (W := J₀) hstab
  have hr : rk ↥J₀ = rk ↥(J₀ ⊓ fixV (Subgroup.zpowers t)) + 1 := by omega
  have hcard : 2 * Nat.card ↥(J₀ ⊓ fixV (Subgroup.zpowers t)) = Nat.card ↥J₀ := by
    rw [card_eq_two_pow hW2 J₀, card_eq_two_pow hW2 (J₀ ⊓ fixV (Subgroup.zpowers t)), hr,
      pow_succ']
  obtain ⟨X, hXH, hX4, E, hEL, hE3, hE9, hEX⟩ := hhyp _ inf_le_left hcard
  obtain ⟨y, hyM, hyO, hy1, hy3, hyL, hyfpf, hJy⟩ := s1614_row2_oddBar D hc hS2 hJ₀
  have hXfix : X ≤ fixV (Subgroup.zpowers t) := hXH.trans inf_le_right
  have hXJ : X ≤ J₀ := hXH.trans inf_le_left
  have hyXfix : X.map y.toMonoidHom ≤ fixV (Subgroup.zpowers t) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_fixV_zpowers_iff_apply]
    have h1 : t x = x := mem_fixV_zpowers_iff_apply.1 (hXfix hx)
    have h2 : t (y x) = y (t x) := by
      have := congrArg (fun f : MulAut (Vtil ⊥ V hV) => f x) (htc y hyO)
      simpa [MulAut.mul_apply] using this
    show t (y x) = y x
    rw [h2, h1]
  have hXy : X ⊓ X.map y.toMonoidHom = ⊥ := by
    rw [eq_bot_iff, ← hJy]
    exact inf_le_inf hXJ (Subgroup.map_mono hXJ)
  have hrkX : rk ↥X = 2 := by
    have h : 2 ^ rk ↥X = 2 ^ 2 := by
      rw [← card_eq_two_pow hW2 X, hX4]
      norm_num
    exact Nat.pow_right_injective le_rfl h
  have hrkXy : rk ↥(X.map y.toMonoidHom) = rk ↥X := by
    unfold rk
    rw [Subgroup.card_map_of_injective (f := y.toMonoidHom) y.injective]
  have hrkQ : rk ↥(X ⊔ X.map y.toMonoidHom) = 4 := by
    have h := rk_sup_add_rk_inf X (X.map y.toMonoidHom)
    rw [hXy, rk_bot] at h
    omega
  have hQfix : X ⊔ X.map y.toMonoidHom ≤ fixV (Subgroup.zpowers t) := sup_le hXfix hyXfix
  have hS3 : 3 ≤ rk ↥(W ⊓ (X ⊔ X.map y.toMonoidHom)) := by
    have h1 := rk_sup_add_rk_inf W (X ⊔ X.map y.toMonoidHom)
    have h2 : rk ↥(W ⊔ (X ⊔ X.map y.toMonoidHom)) ≤ rk ↥(fixV (Subgroup.zpowers t)) :=
      rk_mono (sup_le hWC hQfix)
    have h3 := rk_add_rkIdx W
    have h4' := rk_add_rkIdx (fixV (Subgroup.zpowers t))
    omega
  have hyE' : y ∉ E := by
    intro hyE
    have hst := hJ₀.2.2.1 y (hEL hyE)
    have hJ0ne : J₀ ≠ ⊥ := by
      intro h
      rw [h, rk_bot] at h4
      omega
    obtain ⟨u, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hJ0ne
    have hmem : y (u : Vtil ⊥ V hV) ∈ J₀ ⊓ J₀.map y.toMonoidHom :=
      ⟨hst (u : Vtil ⊥ V hV) u.2, ⟨(u : Vtil ⊥ V hV), u.2, rfl⟩⟩
    rw [hJy, Subgroup.mem_bot] at hmem
    apply hu1
    apply Subtype.ext
    exact y.injective (hmem.trans (map_one y).symm)
  obtain ⟨z, hzS, hz1, B, hBM, hB3, hBnc, hzB⟩ := s1614_row2_pick hWsq (hEL.trans hLM) hE3 hE9
    hX4 hEX hyM hy3 (fun e he => hyL e (hEL he)) hyE' hyfpf hXy
    (S := W ⊓ (X ⊔ X.map y.toMonoidHom)) inf_le_right hS3
  exact ⟨z, hzS.1, hz1, 3, hD3, B, hBM, hB3, hBnc, hzB⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
