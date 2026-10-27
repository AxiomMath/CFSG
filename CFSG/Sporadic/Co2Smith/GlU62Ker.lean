module

public import CFSG.LieType.Universal.Unitary.Clause0
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.Sporadic.Co2Smith.GlDataG0
public import CFSG.Sporadic.Co2Smith.GlRootD1Main
public import CFSG.Sporadic.Co2Smith.GlU62Spec

public section

namespace CFSG.Sporadic.Co2Smith

open Subgroup CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix
  CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.CurtisTits CFSG.Fischer
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Unitary.SUExtras

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

theorem su6_iSup : ⨆ γ ∈ su6D.roots, su6D.rootGroup γ = ⊤ :=
  su6D_steinbergPresentation.1

theorem range_le_of_roots {X : Type*} [Group X] (θ : SU6 →* X) {S : Subgroup X}
    (h : ∀ γ ∈ su6D.roots, ∀ x ∈ su6D.rootGroup γ, θ x ∈ S) : θ.range ≤ S := by
  rintro _ ⟨y, rfl⟩
  have hle : ⨆ γ ∈ su6D.roots, su6D.rootGroup γ ≤ S.comap θ :=
    iSup₂_le fun γ hγ x hx => h γ hγ x hx
  rw [su6_iSup] at hle
  exact hle (Subgroup.mem_top y)

theorem isQuasisimple_SU6 : CFSG.IsQuasisimple SU6 :=
  isQuasisimple_SU (p := 2) (f := 1) natCard_F4 (by norm_num) (by decide)

theorem ker_le_center_of_ne {X : Type*} [Group X] (θ : SU6 →* X) (hθ : ∃ x, θ x ≠ 1) :
    θ.ker ≤ center SU6 := by
  obtain ⟨hperf, hsimp, -⟩ := isQuasisimple_SU6
  have hN : (θ.ker.map (QuotientGroup.mk' (center SU6))).Normal :=
    (MonoidHom.normal_ker θ).map _ (QuotientGroup.mk'_surjective _)
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hsimp _ hN with h | h
  · rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
  · exfalso
    obtain ⟨x, hx⟩ := hθ
    have hdec : ∀ g : SU6, ∃ n ∈ θ.ker, ∃ c ∈ center SU6, g = n * c := by
      intro g
      have hg : QuotientGroup.mk' (center SU6) g ∈ θ.ker.map (QuotientGroup.mk' _) := by
        rw [h]
        exact Subgroup.mem_top _
      obtain ⟨n, hn, hng⟩ := hg
      refine ⟨n, hn, n⁻¹ * g, ?_, by group⟩
      rw [← QuotientGroup.ker_mk' (center SU6), MonoidHom.mem_ker, map_mul, map_inv, hng,
        inv_mul_cancel]
    have hcomm : commutator SU6 ≤ θ.ker := by
      rw [commutator_def, Subgroup.commutator_le]
      intro g₁ _ g₂ _
      obtain ⟨n₁, hn₁, c₁, hc₁, rfl⟩ := hdec g₁
      obtain ⟨n₂, hn₂, c₂, hc₂, rfl⟩ := hdec g₂
      rw [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv,
        map_mul, map_mul, MonoidHom.mem_ker.1 hn₁, MonoidHom.mem_ker.1 hn₂, one_mul, one_mul,
        ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul,
        show c₁ * c₂ * c₁⁻¹ * c₂⁻¹ = 1 by
          rw [Subgroup.mem_center_iff.1 hc₂ c₁]
          group, map_one]
    rw [hperf.commutator_eq_top] at hcomm
    exact hx (MonoidHom.mem_ker.1 (hcomm (Subgroup.mem_top x)))

attribute [local instance high] f4DecEq

theorem su6Entry_su6Elt_short {r : Fin 18} (hr : r.val < 12) (c : F4) :
    su6Entry r (su6Elt r c) = c := by
  rw [su6Elt, ite_eq_left_of_eq_true _ _ (eq_true hr), su6Entry, mat_apply, coe_rootHom,
    rootMatrix_apply_pos r hr]
  rfl

theorem su6Entry_su6Elt_long {r : Fin 18} (hr : 12 ≤ r.val) : su6Entry r (su6Elt r 1) = 1 := by
  rw [su6Elt, ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
    ite_eq_right_of_eq_false _ _ (eq_false one_ne_zero), su6Entry, mat_apply, coe_longRootHom,
    su6Pos_long r hr, longRootMatrix_apply_pos r]
  rfl

theorem f4c_val_code {t : ℕ} (ht : t < 4) : (Native.f4c t).code.val = t := by
  show t % 4 = t
  exact Nat.mod_eq_of_lt ht

@[expose] noncomputable def su6Pre (r t : ℕ) : SU6 :=
  if h : r < 18 then (if r < 12 then su6Elt ⟨r, h⟩ (Native.f4c t) else
    if t = 0 then 1 else su6Elt ⟨r, h⟩ 1) else 1

theorem su6Pre_mem {r : ℕ} (hr : r < 18) (t : ℕ) :
    su6Pre r t ∈ su6D.rootGroup (su6Root ⟨r, hr⟩) := by
  rw [su6Pre, dite_eq_left hr]
  split_ifs
  · exact su6Elt_mem _ _
  · exact Subgroup.one_mem _
  · exact su6Elt_mem _ _

theorem xRootK_long' {r t : ℕ} (hr : 12 ≤ r) (ht : t ≠ 0) :
    xRootK r t = xRootK r 1 := by
  rw [xRootK_long hr ht, xRootK_long hr one_ne_zero]

theorem psiRootK_su6Pre {r : ℕ} (hr : r < 18) {t : ℕ}
    (ht : t < 4) : psiRootK (su6Root ⟨r, hr⟩) ⟨su6Pre r t, su6Pre_mem hr t⟩ = xRootK r t := by
  rw [psiRootK_su6Root]
  dsimp only
  by_cases hr12 : r < 12
  · have e : su6Pre r t = su6Elt ⟨r, hr⟩ (Native.f4c t) := by
      rw [su6Pre, dite_eq_left hr, ite_eq_left_of_eq_true _ _ (eq_true hr12)]
    rw [e, su6Entry_su6Elt_short hr12, f4c_val_code ht]
  · by_cases ht0 : t = 0
    · subst ht0
      have e : su6Pre r 0 = 1 := by
        rw [su6Pre, dite_eq_left hr, ite_eq_right_of_eq_false _ _ (eq_false hr12),
          ite_eq_left_of_eq_true _ _ (eq_true rfl)]
      rw [e, show su6Entry ⟨r, hr⟩ 1 = 0 by
        rw [su6Entry, map_one, Matrix.one_apply_ne (su6Pos_ne _)]]
      rfl
    · have e : su6Pre r t = su6Elt ⟨r, hr⟩ 1 := by
        rw [su6Pre, dite_eq_left hr, ite_eq_right_of_eq_false _ _ (eq_false hr12),
          ite_eq_right_of_eq_false _ _ (eq_false ht0)]
      rw [e, su6Entry_su6Elt_long (by simp; omega), xRootK_long' (by omega) ht0]
      rfl

theorem thetaK_su6Pre {r : ℕ}
    (hr : r < 18) {t : ℕ} (ht : t < 4) : thetaK (su6Pre r t) = xRootK r t :=
  (thetaK_spec ((mem_su6D_roots_iff' _).2 ⟨⟨r, hr⟩, rfl⟩) ⟨su6Pre r t, su6Pre_mem hr t⟩).trans
    (psiRootK_su6Pre hr ht)

theorem xRootK_12 : xRootK 12 1 = z0 := by
  rw [xRootK_long (by norm_num) one_ne_zero]
  exact xLongK_zero

theorem xRootK_15 : xRootK 15 1 = x61K := by
  rw [xRootK_long (by norm_num) one_ne_zero]
  simp [xLongK]

theorem eq_one_of_comm_roots
    {c : K} (hz : c * z0 = z0 * c)
    (hr : ∀ r < 4, ∀ t < 4, c * xRootK r t = xRootK r t * c) (h61 : c * x61K = x61K * c) :
    c = 1 := by
  rcases centralizer_Q c (mem_Cz_of_comm hz) (comm_Qsub_of_comm_roots hz hr) with h | h
  · exact h
  · exfalso
    rw [h, ← x16K_eq] at h61
    exact x16K_x61K_ne h61

theorem ker_thetaK :
    thetaK.ker = center SU6 := by
  refine le_antisymm (ker_le_center_of_ne thetaK ⟨su6Pre 12 1, ?_⟩) fun ζ hζ => ?_
  · rw [thetaK_su6Pre (by norm_num) (by norm_num), xRootK_12]
    exact z0_ne_one
  · have hc : ∀ {r : ℕ} (hr : r < 18) {t : ℕ} (ht : t < 4),
        thetaK ζ * xRootK r t = xRootK r t * thetaK ζ := fun hr t ht => by
      rw [← thetaK_su6Pre hr ht, ← map_mul, ← map_mul,
        (Subgroup.mem_center_iff.1 hζ (su6Pre _ t)).symm]
    refine MonoidHom.mem_ker.2 (eq_one_of_comm_roots ?_ (fun r hr t ht => hc (by omega) ht) ?_)
    · rw [← xRootK_12]
      exact hc (by norm_num) (by norm_num)
    · rw [← xRootK_15]
      exact hc (by norm_num) (by norm_num)

theorem natCard_SU6_quot_center :
    Nat.card (SU6 ⧸ center SU6) = 9196830720 := by
  rw [Nat.card_congr (centerQuotientEquivStatedProj natCard_F4
    (isQuasisimple_statedSU_of_card natCard_F4 (by norm_num) (by decide)).2).toEquiv]
  exact CFSG.Fischer.Classification.Recognition.card_statedProj_statedSU_six F4 natCard_F4

theorem xRootK_mem_G0c_lt
    {r t : ℕ} (hr : r < 18) (ht : t < 4) : xRootK r t ∈ G0c := by
  by_cases ht0 : t = 0
  · subst ht0
    rw [xRootK_zero_eq]
    exact G0c.one_mem
  by_cases hr12 : r < 12
  · exact xRootK_mem_G0c hr (by simp [Native.glParams, hr12]; omega)
  · rw [xRootK_long' (by omega) ht0]
    exact xRootK_mem_G0c hr (by simp [Native.glParams, hr12])

theorem range_thetaK :
    thetaK.range = G0c := by
  refine Subgroup.eq_of_le_of_card_ge (range_le_of_roots thetaK fun γ hγ x hx => ?_) ?_
  · obtain ⟨r, rfl⟩ := (mem_su6D_roots_iff' γ).1 hγ
    rw [thetaK_root r hx]
    exact xRootK_mem_G0c_lt r.isLt (su6Entry r x).code.isLt
  · rw [card_G0c, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange thetaK).toEquiv,
      Nat.card_congr (QuotientGroup.quotientMulEquivOfEq ker_thetaK).toEquiv,
      natCard_SU6_quot_center]

theorem eq_one_of_comm_G0c
    {k : K} (hk : ∀ g ∈ G0c, k * g = g * k) : k = 1 :=
  eq_one_of_comm_roots (by rw [← xRootK_12]; exact hk _ (xRootK_mem_G0c_lt (by norm_num)
      (by norm_num)))
    (fun r hr t ht => hk _ (xRootK_mem_G0c_lt (by omega) ht))
    (by rw [← xRootK_15]; exact hk _ (xRootK_mem_G0c_lt (by norm_num) (by norm_num)))

end CFSG.Sporadic.Co2Smith
