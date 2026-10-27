module

public import CFSG.RankThree.SubgroupLists.MitchellDicksonTwo
public import CFSG.RankThree.SubgroupLists.MitchellFrame
public import CFSG.RankThree.SubgroupLists.MitchellIcosaCore
public import CFSG.RankThree.SubgroupLists.MitchellPlusImage

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.Assembly.LowTwoRank Module

local notation "V₄" => Fin 2 ⊕ Fin 2

local notation "⟪" x "⟫" => Units.val x

variable {K K' : Type} [Field K] [Field K']

theorem frameHom_neg (φ : K →+* K') (k : GL V₄ K') (g : GL V₄ K) :
    frameHom φ k (-g) = -frameHom φ k g := by
  rw [← neg_one_mul, map_mul, frameHom_neg_one, neg_one_mul]

theorem frameHom_pow_ne (φ : K →+* K') (k : GL V₄ K') {g : GL V₄ K} {j : ℕ}
    (h : g ^ j ≠ 1 ∧ g ^ j ≠ -1) : frameHom φ k g ^ j ≠ 1 ∧ frameHom φ k g ^ j ≠ -1 := by
  rw [← map_pow]
  exact ⟨fun h1 => h.1 (frameHom_injective φ k (by rw [h1, map_one])),
    fun h1 => h.2 (frameHom_injective φ k (by rw [h1, frameHom_neg_one]))⟩

section Frame

variable [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p] [Finite K'] [CharP K' p]

theorem plusImage_of_icosa_triple (hp5 : 5 ≤ p)
    {G : Subgroup (GL V₄ K)} (hGS : G ≤ StatedSp 2 K) (hU0 : ∀ x ∈ G, IsSqZero x → x = 1)
    (hneg : (-1 : GL V₄ K) ∈ G) {d e f : GL V₄ K} (hdG : d ∈ G) (heG : e ∈ G) (hfG : f ∈ G)
    (hd : IsNCInv d) (he : IsNCInv e) (hf : IsNCInv f)
    (hθ : 16 * cliffB ⟪d⟫ ⟪e⟫ ^ 4 - 12 * cliffB ⟪d⟫ ⟪e⟫ ^ 2 + 1 = 0)
    (hβ1 : cliffB ⟪d⟫ ⟪e⟫ ^ 2 ≠ 1) (hfP : ∀ a b : K, ⟪f⟫ ≠ a • ⟪d⟫ + b • ⟪e⟫)
    (hγ : cliffB ⟪d⟫ ⟪f⟫ ≠ 0) {u w : Matrix V₄ V₄ K} (huM : u ∈ (cliffSpace : Submodule K _))
    (hwM : w ∈ (cliffSpace : Submodule K _)) (hud : cliffB u ⟪d⟫ = 0) (hue : cliffB u ⟪e⟫ = 0)
    (huf : cliffB u ⟪f⟫ = 0) (hwd : cliffB w ⟪d⟫ = 0) (hwe : cliffB w ⟪e⟫ = 0)
    (hwf : cliffB w ⟪f⟫ = 0) (huw : cliffB u w = 0) (hQw : cliffB w w ≠ 0) (φ : K →+* K')
    {k : GL V₄ K'} (hk : k ∈ StatedSp 2 K') {s : K'} (hs : s ≠ 0)
    (hku : frameMat φ k u = s • tStdMat) :
    Nonempty (plusImage (two_ne_zero_of_charP (p := p) (by omega)) (frameGroup φ k G) ≃*
        alternatingGroup (Fin 5)) ∧
      ∀ c ∈ frameGroup φ k G, c ∈ stdCent K' → ∃ h ∈ Subgroup.closure
          {frameHom φ k (d * e), frameHom φ k (d * f)},
        plusBlock ⟪c⟫ = plusBlock ⟪h⟫ ∨ plusBlock ⟪c⟫ = -plusBlock ⟪h⟫ := by
  have hp2 : p ≠ 2 := by omega
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP hp2
  have h2' : (2 : K') ≠ 0 := two_ne_zero_of_charP hp2
  obtain ⟨h5, hx5, hy3, hnc1, hnc2⟩ :=
    icosa_triple_core hp5 hU0 hneg hdG heG hfG hd he hf hθ hβ1 hfP hγ
  have hdM := (mem_cliffSpace_of_involution h2 hd.1 hd.2.1 hd.2.2.1 hd.2.2.2).1
  have heM := (mem_cliffSpace_of_involution h2 he.1 he.2.1 he.2.2.1 he.2.2.2).1
  have hfM := (mem_cliffSpace_of_involution h2 hf.1 hf.2.1 hf.2.2.1 hf.2.2.2).1
  have hGS' : frameGroup φ k G ≤ StatedSp 2 K' := frameGroup_le φ hk hGS
  have hU0' := frameGroup_U0 φ k hU0
  have hneg' := frameGroup_neg φ k hneg
  have hd' := isNCInv_frameHom φ hk hd
  have he' := isNCInv_frameHom φ hk he
  have hf' := isNCInv_frameHom φ hk hf
  have hTM : (tStdMat : Matrix V₄ V₄ K') ∈ (cliffSpace : Submodule K' _) := by
    have := Submodule.smul_mem _ s⁻¹ (hku ▸ frameMat_mem_cliffSpace φ hk huM)
    rwa [smul_smul, inv_mul_cancel₀ hs, one_smul] at this
  have hWM := frameMat_mem_cliffSpace φ hk hwM
  have hT : ∀ Z : Matrix V₄ V₄ K, Z ∈ (cliffSpace : Submodule K _) → cliffB u Z = 0 →
      tStdMat * frameMat φ k Z = -(frameMat φ k Z * tStdMat) := by
    intro Z hZ hu0
    refine (mul_eq_neg_mul_iff h2' hTM (frameMat_mem_cliffSpace φ hk hZ)).mpr ?_
    have := cliffB_frameMat h2' φ k huM hZ
    rw [hku, cliffB_smul_left, hu0, map_zero] at this
    exact (mul_eq_zero.mp this).resolve_left hs
  have hW : ∀ Z : Matrix V₄ V₄ K, Z ∈ (cliffSpace : Submodule K _) → cliffB w Z = 0 →
      frameMat φ k w * frameMat φ k Z = -(frameMat φ k Z * frameMat φ k w) := by
    intro Z hZ hw0
    refine (mul_eq_neg_mul_iff h2' hWM (frameMat_mem_cliffSpace φ hk hZ)).mpr ?_
    rw [cliffB_frameMat h2' φ k hwM hZ, hw0, map_zero]
  have hWT : frameMat φ k w * tStdMat = -(tStdMat * frameMat φ k w) := by
    refine (mul_eq_neg_mul_iff h2' hWM hTM).mpr ?_
    have := cliffB_frameMat h2' φ k hwM huM
    rw [hku, cliffB_smul_right, cliffB_comm w u, huw, map_zero] at this
    exact (mul_eq_zero.mp this).resolve_left hs
  have hQ : frameMat φ k w * frameMat φ k w = φ (cliffB w w) • (1 : Matrix V₄ V₄ K') := by
    rw [mul_self_of_mem h2' hWM, ← cliffB_self h2', cliffB_frameMat h2' φ k hwM hwM]
  have hq : φ (cliffB w w) ≠ 0 := fun h => hQw (φ.injective (by rw [h, map_zero]))
  have hxG := mem_frameGroup φ k (G.mul_mem hdG heG)
  have hyG := mem_frameGroup φ k (G.mul_mem hdG hfG)
  have hxT : ⟪frameHom φ k (d * e)⟫ * tStdMat = tStdMat * ⟪frameHom φ k (d * e)⟫ := by
    rw [coe_frameHom, Units.val_mul, frameMat_mul]
    exact (mul_comm_of_anticomm (hT _ hdM hud) (hT _ heM hue)).symm
  have hyT : ⟪frameHom φ k (d * f)⟫ * tStdMat = tStdMat * ⟪frameHom φ k (d * f)⟫ := by
    rw [coe_frameHom, Units.val_mul, frameMat_mul]
    exact (mul_comm_of_anticomm (hT _ hdM hud) (hT _ hfM huf)).symm
  have hxC : frameHom φ k (d * e) ∈ stdCent K' := mem_stdCent.mpr ⟨hGS' hxG, hxT⟩
  have hyC : frameHom φ k (d * f) ∈ stdCent K' := mem_stdCent.mpr ⟨hGS' hyG, hyT⟩
  have hxW : frameMat φ k w * ⟪frameHom φ k (d * e)⟫ =
      ⟪frameHom φ k (d * e)⟫ * frameMat φ k w := by
    rw [coe_frameHom, Units.val_mul, frameMat_mul]
    exact mul_comm_of_anticomm (hW _ hdM hwd) (hW _ heM hwe)
  have hyW : frameMat φ k w * ⟪frameHom φ k (d * f)⟫ =
      ⟪frameHom φ k (d * f)⟫ * frameMat φ k w := by
    rw [coe_frameHom, Units.val_mul, frameMat_mul]
    exact mul_comm_of_anticomm (hW _ hdM hwd) (hW _ hfM hwf)
  have hx : ⟪frameHom φ k (d * e)⟫ * ⟪frameHom φ k (d * e)⟫ =
      (2 * cliffB ⟪frameHom φ k d⟫ ⟪frameHom φ k e⟫) • ⟪frameHom φ k (d * e)⟫ - 1 := by
    rw [map_mul, Units.val_mul]
    exact mul_sq_of_isNCInv h2' hd' he'
  have hy : ⟪frameHom φ k (d * f)⟫ * ⟪frameHom φ k (d * f)⟫ =
      (2 * cliffB ⟪frameHom φ k d⟫ ⟪frameHom φ k f⟫) • ⟪frameHom φ k (d * f)⟫ - 1 := by
    rw [map_mul, Units.val_mul]
    exact mul_sq_of_isNCInv h2' hd' hf'
  have hxo : 5 ≤ orderOf (plusBar h2' hxG hxC) :=
    two_lt_orderOf_plusBar_of hp2 hU0' hneg' hxG hxC hx (m := 5)
      (fun j h1 h2 => frameHom_pow_ne φ k (hx5 j h1 h2)) (by norm_num)
  have hyo : 3 ≤ orderOf (plusBar h2' hyG hyC) :=
    two_lt_orderOf_plusBar_of hp2 hU0' hneg' hyG hyC hy (m := 3)
      (fun j h1 h2 => frameHom_pow_ne φ k (hy3 j h1 h2)) (by norm_num)
  have hxord : orderOf (plusBar h2' hxG hxC) = 5 := by
    refine Nat.le_antisymm (Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one ?_)) hxo
    rw [plusBar_pow, plusBar_eq_one_iff]
    have h5' : frameHom φ k (d * e) ^ 5 = 1 ∨ frameHom φ k (d * e) ^ 5 = -1 := by
      rw [← map_pow]
      rcases h5 with h | h
      · exact Or.inl (by rw [h, map_one])
      · exact Or.inr (by rw [h, frameHom_neg_one])
    rcases h5' with h | h
    · exact Or.inl (by rw [h, Units.val_one, plusBlock_one])
    · refine Or.inr ?_
      rw [h, Units.val_neg, Units.val_one, ← neg_one_smul K' (1 : Matrix V₄ V₄ K'),
        plusBlock_smul, plusBlock_one, neg_one_smul]
  have hyord : 2 < orderOf (plusBar h2' hyG hyC) := by omega
  generalize hx' : frameHom φ k (d * e) = x' at *
  generalize hy' : frameHom φ k (d * f) = y' at *
  have hnc : plusBar h2' hxG hxC * plusBar h2' hyG hyC ≠
      plusBar h2' hyG hyC * plusBar h2' hxG hxC := by
    intro hcomm
    rcases mul_eq_or_eq_neg_of_plusBar_commute hp2 hU0' hneg' hxG hxC hyG hyC hq hWT hQ hxW hyW
      hcomm with h | h
    · refine hnc1 (frameHom_injective φ k ?_)
      rw [map_mul (frameHom φ k) (d * e) (d * f), map_mul (frameHom φ k) (d * f) (d * e), hx', hy',
        h]
    · refine hnc2 (frameHom_injective φ k ?_)
      rw [frameHom_neg, map_mul (frameHom φ k) (d * e) (d * f),
        map_mul (frameHom φ k) (d * f) (d * e), hx', hy', h]
  obtain ⟨n, hF⟩ := card_eq_pow_of_finite (K := K') (p := p) hp2
  have hxH : x' ∈ Subgroup.closure {x', y'} := Subgroup.subset_closure (Set.mem_insert _ _)
  have hyH : y' ∈ Subgroup.closure {x', y'} :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hHG : Subgroup.closure {x', y'} ≤ frameGroup φ k G :=
    (Subgroup.closure_le _).mpr (by rintro _ (rfl | rfl) <;> assumption)
  have hLY := plusImage_mono h2' hHG
  have hY : ¬ p ∣ Nat.card (plusImage h2' (frameGroup φ k G)) :=
    not_dvd_card_plusImage hp2 hU0' hneg'
  obtain ⟨eL⟩ : Nonempty (plusImage h2' (Subgroup.closure {x', y'}) ≃*
      alternatingGroup (Fin 5)) := by
    refine nonempty_mulEquiv_alternating_five hF _
      (fun hdvd => hY (dvd_trans hdvd (Subgroup.card_dvd_of_le hLY)))
      (x := plusBar h2' hxH hxC) (y := plusBar h2' hyH hyC) ?_ ?_ ?_
    · rw [← orderOf_injective _ (Subgroup.inclusion_injective hLY) (plusBar h2' hxH hxC)]
      exact hxord
    · rw [← orderOf_injective _ (Subgroup.inclusion_injective hLY) (plusBar h2' hyH hyC)]
      exact hyord
    · intro h
      have := congrArg (Subgroup.inclusion hLY) h
      rw [map_mul, map_mul] at this
      exact hnc this
  have hL : plusImage h2' (Subgroup.closure {x', y'}) = plusImage h2' (frameGroup φ k G) :=
    eq_of_le_of_mulEquiv_alternating_five hF hLY hY eL
  refine ⟨⟨(MulEquiv.subgroupCongr hL).symm.trans eL⟩, ?_⟩
  intro c hcG hcC
  have hz : (plusBar h2' hcG hcC).1 ∈ plusImage h2' (Subgroup.closure {x', y'}) := by
    rw [hL]
    exact (plusBar h2' hcG hcC).2
  obtain ⟨h, hhH, hhC, hh⟩ := exists_mem_of_mem_plusImage h2' hz
  exact ⟨h, hhH, plusBlock_eq_or_neg_of_plusBar_eq hp2 hU0' hneg' hcG hcC (hHG hhH) hhC
    (Subtype.ext hh)⟩

end Frame

end CFSG.RankThree.SubgroupLists
