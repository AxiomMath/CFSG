module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveEighteenSetting
public import CFSG.LocalAnalysis.WeakClosure81.W172Bridge
public import CFSG.LocalAnalysis.WeakClosure81.W172EndGame
public import CFSG.LocalAnalysis.WeakClosure81.W172OrbitBound

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

namespace MinCex172

variable {D : Data G} {V₀ V H : Subgroup G}

theorem w172_exists_involution (h162 : W3Thm162Gt2 G) (c : MinCex172 D V₀ V H)
    (M : ModDataE H (eOmegaZ H D.T)) :
    ∃ e : LGL 2 M.W, M.img V = Subgroup.zpowers e ∧ e * e = 1 ∧ e ≠ 1 := by
  have hg := c.w172_gam183_one h162
  have hm := w172_two5 h162 c hg
  have hiS : 1 ≤ (c.ctx188 h162).iStar := (c.ctx188 h162).iStar_pos
  obtain ⟨e, he, hge⟩ := (c.ctx188 h162).w172_exists_mem_D M ⟨hg, hm.trans hiS⟩ hm
  have hI := (c.ctx188 h162).w172_invSys M
  refine ⟨e, ?_, hI.sq e he, hI.ne_one e he⟩
  rw [← c.w172_vInH_one]
  exact hge

theorem w172_img_isSolvable (c : MinCex172 D V₀ V H) (M : ModDataE H (eOmegaZ H D.T)) :
    Group.IsSolvable ↥(M.img H) := by
  haveI : Group.IsSolvable ↥H := c.solv
  have h : M.img H = M.ρ.range := by
    unfold ModDataE.img
    rw [Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map]
  rw [h]
  exact solvable_of_surjective (MonoidHom.rangeRestrict_surjective M.ρ)

theorem w172_pCoreOf_img_eq_bot (c : MinCex172 D V₀ V H) (M : ModDataE H (eOmegaZ H D.T)) :
    pCoreOf 2 (M.img H) = ⊥ := by
  have hZcent : D.T ≤ Subgroup.centralizer (omegaOneCenterOf D.T : Set G) := by
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hΩ : omegaOneCenterOf D.T ≤ centerOf D.T := by
      rw [omegaOneCenterOf, omegaOneOf]
      exact (Subgroup.closure_le _).mpr fun u hu => hu.1
    have hz' : z ∈ centerOf D.T := hΩ hz
    exact (Subgroup.mem_centralizer_iff.1 hz'.2 t ht).symm
  exact M.pCoreOf_img_eq_bot (J := H) (T := D.T) (Z := omegaOneCenterOf D.T)
    c.hyp.isSylowIn_T (Hyp183.omegaOneCenterOf_le_eOmegaZ H D.T) hZcent (le_refl _)

theorem w172_img_R_comm (h162 : W3Thm162Gt2 G) (c : MinCex172 D V₀ V H)
    (M : ModDataE H (eOmegaZ H D.T)) {e : LGL 2 M.W} (hge : M.img V = Subgroup.zpowers e)
    (he : e * e = 1) (he1 : e ≠ 1) {s : LGL 2 M.W} (hs : s ∈ M.img (w172R D V₀ V)) :
    s * e = e * s := by
  obtain ⟨r, hr, rfl⟩ := M.mem_img.1 hs
  have hg := c.w172_gam183_one h162
  have hm := w172_two5 h162 c hg
  have hge' : M.img (vInH V H 1) = Subgroup.zpowers e := by
    rw [c.w172_vInH_one]
    exact hge
  refine (w172_mem_conj_iff_comm h162 c hg hm M hge' he he1 r.2).1 ?_
  rw [conjSubgroup_one]
  exact w172R_le_M D V₀ V hr

theorem w172_false (h162 : W3Thm162Gt2 G) (hL : W172Lem26 D V₀ V) (c : MinCex172 D V₀ V H) :
    False := by
  classical
  obtain ⟨M⟩ := exists_modDataE c.hyp.isElemAbelian_eOmegaZ (Hyp183.normalizer_eOmegaZ H D.T)
  obtain ⟨e, hge, he, he1⟩ := c.w172_exists_involution h162 M
  have hV : IsElemAbelian 2 V := c.hyp.setting.isElemAbelian
  have hV₀V : V₀ ≤ V := c.hyp.setting.hyp6H.le
  have hV₀ab : IsElemAbelian 2 V₀ := hV.mono hV₀V
  have heL : e ∈ M.img H :=
    M.img_mono c.w172_V_le_H (hge ▸ Subgroup.mem_zpowers e)
  obtain ⟨p, hp, hp2, x₀, hx₀, hx₀c⟩ :=
    w172_exists_acting_prime (c.w172_img_isSolvable M) (c.w172_pCoreOf_img_eq_bot M) heL he he1
  haveI : Fact p.Prime := ⟨hp⟩
  have hXL : pCoreOf p (M.img H) ≤ M.img H := CFSG.LieType.BorelTits.pCoreOf_le p _
  have hXp : IsPGroup p (pCoreOf p (M.img H)) := CFSG.LieType.BorelTits.pCoreOf_isPGroup p _
  have hnorm : ∀ s ∈ M.img H, ∀ x ∈ pCoreOf p (M.img H),
      s * x * s⁻¹ ∈ pCoreOf p (M.img H) := fun s hs x hx =>
    (Subgroup.mem_normalizer_iff.1 (CFSG.LieType.BorelTits.le_normalizer_pCoreOf p _ hs) x).1 hx
  have hRH : w172R D V₀ V ≤ H := (w172R_le_T D V₀ V).trans c.hyp.hyp171.2.1
  have hset : W172InvSetup p (pCoreOf p (M.img H)) e (M.img (w172R D V₀ V)) :=
    { prime := hp
      odd := hp2
      pgroup := hXp
      sq := by rw [pow_two]; exact he
      d_norm := fun x hx => hnorm e heL x hx
      s_norm := fun s hs x hx => hnorm s (M.img_mono hRH hs) x hx
      s_comm := fun s hs => c.w172_img_R_comm h162 M hge he he1 hs }
  have hnt : ∃ x ∈ pCoreOf p (M.img H), e * x * e⁻¹ ≠ x := by
    refine ⟨x₀, hx₀, fun h => hx₀c ?_⟩
    rw [h, mul_inv_cancel]
    exact Subgroup.one_mem _
  have hS : IsPGroup 2 (M.img (w172R D V₀ V)) := M.isPGroup_img (w172R_isPGroup D V₀ V)
  have hk : 1 ≤ rk ↥V₀ := by
    refine Nat.one_le_iff_ne_zero.2 fun h0 => c.hyp.ne_bot ?_
    exact (rk_eq_zero_iff_of_isPGroup hV₀ab.isPGroup).1 h0
  have hm2 : 2 < mBar D.M V₀ V hV := (c.hyp.setting.pair.mBarGT_iff_lt_mBar 2).1 c.mbar
  refine w172_false_of_orbit_bound (k := rk ↥V₀) (c := rk ↥V₀ * (mBar D.M V₀ V hV - 1))
    hset hnt hS hk ?_ ?_ ?_
  · calc 2 * rk ↥V₀ = rk ↥V₀ * 2 := mul_comm _ _
      _ ≤ rk ↥V₀ * (mBar D.M V₀ V hV - 1) := Nat.mul_le_mul_left _ (by omega)
  · intro y hy
    exact c.w172_finrank_commSub_conj_le h162 M hge he (hXL hy)
  · intro y hy hinv hy1
    have hodd : Odd (orderOf y) := by
      obtain ⟨k, hk⟩ := hXp ⟨y, hy⟩
      have h1 : y ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one h1)
      rw [hj]
      exact (hp.odd_of_ne_two hp2).pow
    exact c.w172_two_pow_le_relIndex_normalizer h162 hL M hge he he1 (hXL hy) hodd hinv hy1

end MinCex172

end CFSG.LocalAnalysis.WeakClosure81

end
