module

public import CFSG.LocalAnalysis.StandardType.GGPhiTwoGenTwEightTorusFrame

public noncomputable section

namespace CFSG.StandardType.PhiTwoRootGen

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Malle.SeitzCube
open scoped MatrixGroups
open CFSG.StandardType.TableBExcTwoFusion

private def frameEU : Fin 6 → ℤ := fun k =>
  match k.val with
  | 0 => 2
  | 1 => 0
  | 2 => -1
  | 3 => 0
  | 4 => 1
  | _ => -2

private def frameEV : Fin 6 → ℤ := fun k =>
  match k.val with
  | 0 => -1
  | 1 => 0
  | 2 => 2
  | 3 => 0
  | 4 => -2
  | _ => 1

private lemma cartan_frameEU (k : Fin 6) :
    Tag.E6.cartan (0 : Fin Tag.E6.rank) k - Tag.E6.cartan (5 : Fin Tag.E6.rank) k =
      frameEU k := by
  fin_cases k <;> decide

private lemma cartan_frameEV (k : Fin 6) :
    Tag.E6.cartan (2 : Fin Tag.E6.rank) k - Tag.E6.cartan (4 : Fin Tag.E6.rank) k =
      frameEV k := by
  fin_cases k <;> decide

private lemma zmod_val_neg_modEq (t : Fin 6 → ZMod 3)
    (h : t 2 + t 4 = 0) :
    ((t 4).val : ℤ) ≡ -((t 2).val : ℤ) [ZMOD 3] := by
  have hzmod : ((t 4).val : ZMod 3) = ((-((t 2).val : ℤ)) : ZMod 3) := by
    rw [ZMod.natCast_zmod_val]
    push_cast
    rw [ZMod.natCast_zmod_val]
    linear_combination h
  rw [Int.modEq_iff_dvd]
  have hdvd : (3 : ℤ) ∣ ((t 4).val : ℤ) - (-((t 2).val : ℤ)) := by
    have h0 : ((((t 4).val : ℤ) - (-((t 2).val : ℤ)) : ℤ) : ZMod 3) = 0 := by
      push_cast
      rw [hzmod]
      exact sub_self _
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp h0
  convert dvd_neg.mpr hdvd using 1
  ring

private lemma zmod_val_neg_modEq' (t : Fin 6 → ZMod 3)
    (h : t 0 + t 5 = 0) :
    ((t 5).val : ℤ) ≡ -((t 0).val : ℤ) [ZMOD 3] := by
  have hzmod : ((t 5).val : ZMod 3) = ((-((t 0).val : ℤ)) : ZMod 3) := by
    rw [ZMod.natCast_zmod_val]
    push_cast
    rw [ZMod.natCast_zmod_val]
    linear_combination h
  rw [Int.modEq_iff_dvd]
  have hdvd : (3 : ℤ) ∣ ((t 5).val : ℤ) - (-((t 0).val : ℤ)) := by
    have h0 : ((((t 5).val : ℤ) - (-((t 0).val : ℤ)) : ℤ) : ZMod 3) = 0 := by
      push_cast
      rw [hzmod]
      exact sub_self _
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp h0
  convert dvd_neg.mpr hdvd using 1
  ring


variable {K : Type} [Field K] [CharP K 2]

private lemma frameW_exp (t : Fin 6 → ZMod 3) (h1 : t 1 = 0) (h3 : t 3 = 0)
    (h05 : t 0 + t 5 = 0) (h24 : t 2 + t 4 = 0) (k : Fin 6) :
    (2 * ((t 0).val : ℤ) + ((t 2).val : ℤ)) * frameEU k +
        (((t 0).val : ℤ) + 2 * ((t 2).val : ℤ)) * frameEV k ≡
      3 * ((t k).val : ℤ) [ZMOD 9] := by
  fin_cases k
  · change (2 * ((t 0).val : ℤ) + ((t 2).val : ℤ)) * frameEU (0 : Fin 6) +
        (((t 0).val : ℤ) + 2 * ((t 2).val : ℤ)) * frameEV (0 : Fin 6) ≡
      3 * ((t (0 : Fin 6)).val : ℤ) [ZMOD 9]
    rw [show frameEU (0 : Fin 6) = 2 from rfl, show frameEV (0 : Fin 6) = -1 from rfl]
    have h : (2 * ((t 0).val : ℤ) + ((t 2).val : ℤ)) * 2 +
        (((t 0).val : ℤ) + 2 * ((t 2).val : ℤ)) * (-1) =
        3 * ((t 0).val : ℤ) := by ring
    rw [h]
  · change (2 * ((t 0).val : ℤ) + ((t 2).val : ℤ)) * frameEU (1 : Fin 6) +
        (((t 0).val : ℤ) + 2 * ((t 2).val : ℤ)) * frameEV (1 : Fin 6) ≡
      3 * ((t (1 : Fin 6)).val : ℤ) [ZMOD 9]
    rw [show frameEU (1 : Fin 6) = 0 from rfl, show frameEV (1 : Fin 6) = 0 from rfl,
      h1]
    norm_num
  · change (2 * ((t 0).val : ℤ) + ((t 2).val : ℤ)) * frameEU (2 : Fin 6) +
        (((t 0).val : ℤ) + 2 * ((t 2).val : ℤ)) * frameEV (2 : Fin 6) ≡
      3 * ((t (2 : Fin 6)).val : ℤ) [ZMOD 9]
    rw [show frameEU (2 : Fin 6) = -1 from rfl, show frameEV (2 : Fin 6) = 2 from rfl]
    have h : (2 * ((t 0).val : ℤ) + ((t 2).val : ℤ)) * (-1) +
        (((t 0).val : ℤ) + 2 * ((t 2).val : ℤ)) * 2 =
        3 * ((t 2).val : ℤ) := by ring
    rw [h]
  · change (2 * ((t 0).val : ℤ) + ((t 2).val : ℤ)) * frameEU (3 : Fin 6) +
        (((t 0).val : ℤ) + 2 * ((t 2).val : ℤ)) * frameEV (3 : Fin 6) ≡
      3 * ((t (3 : Fin 6)).val : ℤ) [ZMOD 9]
    rw [show frameEU (3 : Fin 6) = 0 from rfl, show frameEV (3 : Fin 6) = 0 from rfl,
      h3]
    norm_num
  · change (2 * ((t 0).val : ℤ) + ((t 2).val : ℤ)) * frameEU (4 : Fin 6) +
        (((t 0).val : ℤ) + 2 * ((t 2).val : ℤ)) * frameEV (4 : Fin 6) ≡
      3 * ((t (4 : Fin 6)).val : ℤ) [ZMOD 9]
    rw [show frameEU (4 : Fin 6) = 1 from rfl, show frameEV (4 : Fin 6) = -2 from rfl]
    have h : (2 * ((t 0).val : ℤ) + ((t 2).val : ℤ)) * 1 +
        (((t 0).val : ℤ) + 2 * ((t 2).val : ℤ)) * (-2) =
        3 * (-((t 2).val : ℤ)) := by ring
    have hmul : 3 * ((t 4).val : ℤ) ≡ 3 * (-((t 2).val : ℤ)) [ZMOD 9] := by
      obtain ⟨c, hc⟩ := Int.modEq_iff_dvd.mp (zmod_val_neg_modEq t h24)
      refine Int.modEq_iff_dvd.mpr ⟨c, ?_⟩
      linear_combination 3 * hc
    rw [h]
    exact hmul.symm
  · change (2 * ((t 0).val : ℤ) + ((t 2).val : ℤ)) * frameEU (5 : Fin 6) +
        (((t 0).val : ℤ) + 2 * ((t 2).val : ℤ)) * frameEV (5 : Fin 6) ≡
      3 * ((t (5 : Fin 6)).val : ℤ) [ZMOD 9]
    rw [show frameEU (5 : Fin 6) = -2 from rfl, show frameEV (5 : Fin 6) = 1 from rfl]
    have h : (2 * ((t 0).val : ℤ) + ((t 2).val : ℤ)) * (-2) +
        (((t 0).val : ℤ) + 2 * ((t 2).val : ℤ)) * 1 =
        3 * (-((t 0).val : ℤ)) := by ring
    have hmul : 3 * ((t 5).val : ℤ) ≡ 3 * (-((t 0).val : ℤ)) [ZMOD 9] := by
      obtain ⟨c, hc⟩ := Int.modEq_iff_dvd.mp (zmod_val_neg_modEq' t h05)
      refine Int.modEq_iff_dvd.mpr ⟨c, ?_⟩
      linear_combination 3 * hc
    rw [h]
    exact hmul.symm

private lemma cube_root_eq {ζu : Kˣ} (hζ : (ζu : K) ^ 2 + ζu + 1 = 0)
    {x : Kˣ} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    x = ζu ∨ x = ζu ^ 2 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hxval : (x : K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hx3, Units.val_one]
  have hxval1 : (x : K) ≠ 1 := fun h => hx1 (Units.ext h)
  have hxpoly : (x : K) ^ 2 + (x : K) + 1 = 0 := by
    have hfac : ((x : K) - 1) * ((x : K) ^ 2 + (x : K) + 1) = 0 := by
      rw [show ((x : K) - 1) * ((x : K) ^ 2 + (x : K) + 1) = (x : K) ^ 3 - 1 by ring,
        hxval]
      ring
    exact (mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr hxval1)
  have hζcube : (ζu : K) ^ 3 = 1 := pow_three_of_sq_add hζ
  have hsum : (ζu : K) + (ζu : K) ^ 2 = 1 := by
    linear_combination hζ - h2
  have hprod : ((x : K) + (ζu : K)) * ((x : K) + (ζu : K) ^ 2) = 0 := by
    calc ((x : K) + (ζu : K)) * ((x : K) + (ζu : K) ^ 2) =
        (x : K) ^ 2 + (x : K) * ((ζu : K) + (ζu : K) ^ 2) + (ζu : K) ^ 3 := by ring
      _ = (x : K) ^ 2 + (x : K) + 1 := by rw [hsum, hζcube]; ring
      _ = 0 := hxpoly
  rcases mul_eq_zero.mp hprod with h | h
  · left
    apply Units.ext
    have hxeq : (x : K) = (ζu : K) := by
      calc (x : K) = -(ζu : K) := eq_neg_of_add_eq_zero_left h
        _ = (ζu : K) := CharTwo.neg_eq _
    exact hxeq
  · right
    apply Units.ext
    have hxeq : (x : K) = (ζu : K) ^ 2 := by
      calc (x : K) = -((ζu : K) ^ 2) := eq_neg_of_add_eq_zero_left h
        _ = (ζu : K) ^ 2 := CharTwo.neg_eq _
    exact hxeq

omit
  [CharP K 2] in
private lemma mem_normOne_of_order_nine (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 8)
    {η : Kˣ} (hη9 : η ^ 9 = 1) : η ∈ normOne σ.toRingHom := by
  rw [normOne, Subgroup.mem_mk]
  change sU σ.toRingHom η = η⁻¹
  have h8 : sU σ.toRingHom η = η ^ 8 := by
    ext
    change σ (η : K) = ((η ^ 8 : Kˣ) : K)
    rw [hσ, Units.val_pow_eq_pow_val]
  have h8inv : η ^ 8 = η⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    rw [mul_comm, ← pow_succ, show 8 + 1 = 9 by norm_num, hη9]
  rw [h8, h8inv]

private lemma exists_eta_normOne [Finite K] (hK : Nat.card K = 64) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 8) {ζu : Kˣ} (hζu : ζu ^ 3 = 1)
    (hζ : (ζu : K) ^ 2 + ζu + 1 = 0) :
    ∃ η : Kˣ, η ^ 3 = ζu ∧ orderOf η = 9 ∧ η ∈ normOne σ.toRingHom := by
  have hK' : Nat.card K = (2 ^ 3) ^ 2 := by simpa using hK
  obtain ⟨ν, hνo⟩ :=
    CFSG.LocalAnalysis.WeakClosure81.exists_orderOf_eq_of_dvd_two_pow_add_one
      (n := 3) (F₀ := K) hK' (m := 9) (by norm_num)
  let νu : Kˣ := ν
  have hνuo : orderOf νu = 9 := by
    rw [Subgroup.orderOf_coe]
    exact hνo
  have hνu9 : νu ^ 9 = 1 := by
    rw [← hνuo]
    exact pow_orderOf_eq_one νu
  let x : Kˣ := νu ^ 3
  have hx3 : x ^ 3 = 1 := by
    change (νu ^ 3) ^ 3 = 1
    rw [← pow_mul, show 3 * 3 = 9 by norm_num, hνu9]
  have hx1 : x ≠ 1 := by
    intro hx
    have hdiv : orderOf νu ∣ 3 := by
      apply orderOf_dvd_of_pow_eq_one
      change νu ^ 3 = 1
      exact hx
    rw [hνuo] at hdiv
    norm_num at hdiv
  rcases cube_root_eq hζ hx3 hx1 with hx | hx
  · refine ⟨νu, ?_, hνuo, ?_⟩
    · exact hx
    · exact mem_normOne_of_order_nine σ hσ hνu9
  · refine ⟨νu ^ 2, ?_, ?_, ?_⟩
    · have hx' : νu ^ 3 = ζu ^ 2 := hx
      rw [show (νu ^ 2) ^ 3 = (νu ^ 3) ^ 2 by group, hx']
      rw [show (ζu ^ 2) ^ 2 = ζu ^ 4 by group,
        show ζu ^ 4 = ζu ^ 3 * ζu by group, hζu]
      group
    · rw [orderOf_pow, hνuo]
      norm_num
    · apply mem_normOne_of_order_nine σ hσ
      rw [← pow_mul, show 2 * 9 = 9 * 2 by norm_num, pow_mul, hνu9, one_pow]

omit
  [CharP K 2] in
private lemma frameW_tuple {ζu η : Kˣ} (hζu : ζu ^ 3 = 1) (hη3 : η ^ 3 = ζu)
    (hηo : orderOf η = 9) (σ : K ≃+* K) (hηnorm : η ∈ normOne σ.toRingHom)
    {t : Fin TwistTag.E6.tag.rank → ZMod 3} (h1 : t 1 = 0) (h3 : t 3 = 0)
    (h05 : t 0 + t 5 = 0) (h24 : t 2 + t 4 = 0) :
    TableBExc.E6Three.zetaVec (τ := TwistTag.E6.tag) ζu hζu t =
      torusTuple σ.toRingHom
        (η ^ (2 * ((t 0).val : ℤ) + ((t 2).val : ℤ)))
        (η ^ (((t 0).val : ℤ) + 2 * ((t 2).val : ℤ))) := by
  let A : ℤ := 2 * ((t 0).val : ℤ) + ((t 2).val : ℤ)
  let B : ℤ := ((t 0).val : ℤ) + 2 * ((t 2).val : ℤ)
  funext k
  let k' : Fin Tag.E6.rank := k
  change ζu ^ ((t k).val) = torusTuple σ.toRingHom (η ^ A) (η ^ B) k'
  rw [torusTuple_eq]
  simp only [Pi.mul_apply, e6TorParam]
  have hAinv : sU σ.toRingHom (η ^ A) = (η ^ A)⁻¹ := by
    rw [map_zpow, hηnorm, inv_zpow]
  have hBinv : sU σ.toRingHom (η ^ B) = (η ^ B)⁻¹ := by
    rw [map_zpow, hηnorm, inv_zpow]
  rw [hAinv, hBinv]
  have hL : ζu ^ ((t k).val) = η ^ (3 * ((t k).val : ℤ)) := by
    have hexp : ((3 * (t k).val : ℕ) : ℤ) = 3 * ((t k).val : ℤ) := by
      push_cast
      ring
    rw [← hη3, ← pow_mul, ← zpow_natCast]
    simp [hexp]
  have h0 : (η ^ A) ^ Tag.E6.cartan (0 : Fin Tag.E6.rank) k' =
      η ^ (A * Tag.E6.cartan (0 : Fin Tag.E6.rank) k') := by
    rw [← zpow_mul]
  have h5 : ((η ^ A)⁻¹) ^ Tag.E6.cartan (5 : Fin Tag.E6.rank) k' =
      η ^ (-(A * Tag.E6.cartan (5 : Fin Tag.E6.rank) k')) := by
    rw [← zpow_neg_one (η ^ A), ← zpow_mul, ← zpow_mul]
    congr 1
    ring
  have h2 : (η ^ B) ^ Tag.E6.cartan (2 : Fin Tag.E6.rank) k' =
      η ^ (B * Tag.E6.cartan (2 : Fin Tag.E6.rank) k') := by
    rw [← zpow_mul]
  have h4 : ((η ^ B)⁻¹) ^ Tag.E6.cartan (4 : Fin Tag.E6.rank) k' =
      η ^ (-(B * Tag.E6.cartan (4 : Fin Tag.E6.rank) k')) := by
    rw [← zpow_neg_one (η ^ B), ← zpow_mul, ← zpow_mul]
    congr 1
    ring
  have hR : (η ^ A) ^ Tag.E6.cartan (0 : Fin Tag.E6.rank) k' *
      ((η ^ A)⁻¹) ^ Tag.E6.cartan (5 : Fin Tag.E6.rank) k' *
      ((η ^ B) ^ Tag.E6.cartan (2 : Fin Tag.E6.rank) k' *
        ((η ^ B)⁻¹) ^ Tag.E6.cartan (4 : Fin Tag.E6.rank) k') =
      η ^ (A * frameEU k' + B * frameEV k') := by
    rw [h0, h5, h2, h4]
    rw [← zpow_add, ← zpow_add, ← zpow_add]
    congr 1
    rw [← cartan_frameEU k', ← cartan_frameEV k']
    ring
  have hgoal : η ^ (3 * ((t k).val : ℤ)) = η ^ (A * frameEU k' + B * frameEV k') := by
    rw [zpow_eq_zpow_iff_modEq, hηo]
    exact (frameW_exp t h1 h3 h05 h24 k').symm
  exact hL.trans (hgoal.trans hR.symm)

theorem frameTorusHom_W [Finite K] (hK : Nat.card K = 64) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 8) {ζu : Kˣ} (hζ : (ζu : K) ^ 2 + ζu + 1 = 0)
    (hζu : ζu ^ 3 = 1) {t : Fin TwistTag.E6.tag.rank → ZMod 3}
    (ht : t ∈ frameW) :
    frameTorusHom ζu hζu (frameLang (ζu : K) hζ) (Multiplicative.ofAdd t) ∈
      (torusG σ.toRingHom).range.map (twistedE6RootGroup K σ).subtype := by
  obtain ⟨η, hη3, hηo, hηnorm⟩ := exists_eta_normOne hK σ hσ hζu hζ
  obtain ⟨h1, h3, h05, h24⟩ := ht
  let A : ℤ := 2 * ((t 0).val : ℤ) + ((t 2).val : ℤ)
  let B : ℤ := ((t 0).val : ℤ) + 2 * ((t 2).val : ℤ)
  let u : Kˣ := η ^ A
  let v : Kˣ := η ^ B
  have hu : u ∈ normOne σ.toRingHom := by
    change sU σ.toRingHom (η ^ A) = (η ^ A)⁻¹
    rw [map_zpow, hηnorm, inv_zpow]
  have hv : v ∈ normOne σ.toRingHom := by
    change sU σ.toRingHom (η ^ B) = (η ^ B)⁻¹
    rw [map_zpow, hηnorm, inv_zpow]
  have htuple : TableBExc.E6Three.zetaVec (τ := TwistTag.E6.tag) ζu hζu t =
      torusTuple σ.toRingHom u v := by
    simpa [u, v, A, B] using frameW_tuple hζu hη3 hηo σ hηnorm h1 h3 h05 h24
  have hT : frameTorusHom ζu hζu (frameLang (ζu : K) hζ) (Multiplicative.ofAdd t) =
      torusAB σ.toRingHom u v := by
    rw [frameTorusHom_apply]
    change frameLang (ζu : K) hζ *
        rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζu hζu t) *
        (frameLang (ζu : K) hζ)⁻¹ = _
    rw [htuple]
    change frameLang (ζu : K) hζ *
        rootDiagUnit TwistTag.E6.tag (torusTuple σ.toRingHom u v) *
        (frameLang (ζu : K) hζ)⁻¹ =
      rootDiagUnit TwistTag.E6.tag (torusTuple σ.toRingHom u v)
    have hcomm : Commute (rootDiagUnit TwistTag.E6.tag (torusTuple σ.toRingHom u v))
        (frameLang (ζu : K) hζ) := by
      rw [frameLang]
      have h0 := commute_torusAB_frame σ.toRingHom hu hv 0 (by
        rw [← range_rootSL2_of_isRoot (isRoot_frameRoot 0)]
        exact ⟨frameLangSL2 (ζu : K) hζ, rfl⟩)
      have h1' := commute_torusAB_frame σ.toRingHom hu hv 1 (by
        rw [← range_rootSL2_of_isRoot (isRoot_frameRoot 1)]
        exact ⟨frameLangSL2 (ζu : K) hζ, rfl⟩)
      have h2' := commute_torusAB_frame σ.toRingHom hu hv 2 (by
        rw [← range_rootSL2_of_isRoot (isRoot_frameRoot 2)]
        exact ⟨frameLangSL2 (ζu : K) hζ, rfl⟩)
      have h3' := commute_torusAB_frame σ.toRingHom hu hv 3 (by
        rw [← range_rootSL2_of_isRoot (isRoot_frameRoot 3)]
        exact ⟨frameLangSL2 (ζu : K) hζ, rfl⟩)
      exact ((h0.mul_right h1').mul_right h2').mul_right h3'
    rw [← hcomm.eq]
    group
  rw [hT]
  exact Subgroup.mem_map_of_mem _
    (show torusG σ.toRingHom (⟨u, hu⟩, ⟨v, hv⟩) ∈ (torusG σ.toRingHom).range from
      ⟨_, rfl⟩)

end CFSG.StandardType.PhiTwoRootGen

end
