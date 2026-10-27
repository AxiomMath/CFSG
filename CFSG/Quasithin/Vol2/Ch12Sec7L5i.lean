module

public import CFSG.Quasithin.Vol2.Ch12Sec7L5h
public import CFSG.Quasithin.Background.KGSchurMult2Pf
public import CFSG.Quasithin.MS93.ASGroup
public import CFSG.Quasithin.EmptyFaithful.A38c14HatM22

public section

namespace CFSG.Quasithin.H13.S127.L5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem not_isCyclic_of_sq_eq_one {X : Type} [Group X] [Finite X] (h4 : Nat.card X = 4)
    (h2 : ∀ x : X, x ^ 2 = 1) : ¬ IsCyclic X := by
  intro hc
  obtain ⟨g, hg⟩ := hc.exists_generator
  have ho : orderOf g = 4 := (orderOf_eq_card_of_forall_mem_zpowers hg).trans h4
  have := orderOf_dvd_of_pow_eq_one (h2 g)
  rw [ho] at this
  norm_num at this

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {t : G}

namespace D127

variable (d : D127 G T L V t)
include d

theorem center_ne_bot {K : Subgroup G} (htZ : t ∈ centerOf K) : Subgroup.center ↥K ≠ ⊥ :=
  fun h => d.ne_one (eq_one_of_mem_centerOf h htZ)

theorem not_isSimpleGroup {K : Subgroup G} (hKq : CFSG.Open.IsQuasisimple ↥K)
    (htZ : t ∈ centerOf K) (hs : IsSimpleGroup ↥K) : False :=
  d.center_ne_bot htZ (center_eq_bot_of_isSimpleGroup hKq)

theorem vt_le_centerOf {K : Subgroup G} (hLK : Lt L t ≤ K)
    (h4 : 4 ≤ Nat.card ↥(V ⊓ centerOf K)) : Vt L t ≤ centerOf K := by
  have hle : V ⊓ centerOf K ≤ Vt L t :=
    (le_inf inf_le_left (inf_le_right.trans (inf_le_right.trans
      (Subgroup.centralizer_le hLK)))).trans d.inf_centralizer_le
  have heq : V ⊓ centerOf K = Vt L t :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [d.card_Vt]; exact h4)
  rw [← heq]
  exact inf_le_right

theorem c31Case1
    (hSp4 : SchurMult2Sp4) (hG24 : SchurMult2G24) (hD4 : SchurMult2D4)
    {H R M K : Subgroup G} (hKq : CFSG.Open.IsQuasisimple ↥K) (hZ : IsPGroup 2 ↥(centerOf K))
    (htZ : t ∈ centerOf K) (hM0 : Lt L t = conjClosure (Lt L t) M) (hLK : Lt L t ≤ K)
    (h1 : C31Case1 H R M (Lt L t) V K) :
    IsPSL 3 2 2 (↥K ⧸ Subgroup.center ↥K) ∧ Vt L t ≤ centerOf K := by
  obtain ⟨n, hlie, -, -, hpsl, hnat⟩ := h1
  have hn : n = 2 := eq_two_of_isPSL hpsl ((card_modO2_congr hM0.symm).trans d.card_modO2)
  subst hn
  have hVt : Vt L t ≤ centerOf K := by
    rcases hnat with ⟨F, _, _, hF, hNS⟩ | ⟨hsp, -⟩
    · obtain ⟨-, -, -, -, β, hβs, hβk, -⟩ := hNS
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup β.ker
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective β hβs).toEquiv, hβk,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv, d.card_V] at h1
      have h16 : Nat.card (Multiplicative (Fin 2 → F)) = 16 := by
        rw [show Nat.card (Multiplicative (Fin 2 → F)) = Nat.card (Fin 2 → F) from rfl,
          Nat.card_fun, Nat.card_eq_fintype_card, hF, Nat.card_fin]
        norm_num
      rw [h16] at h1
      exact d.vt_le_centerOf hLK (by omega)
    · exact (d.not_isSimpleGroup hKq htZ
        (CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp _ 2 2 2
          hsp)).elim
  have hZ' := isPGroup_center hZ
  have h4 : 4 ≤ Nat.card ↥(Subgroup.center ↥K) := by
    rw [card_center_eq, ← d.card_Vt]
    exact Subgroup.card_le_of_le hVt
  refine ⟨?_, hVt⟩
  rcases hlie with h | h | h | h | h | h | h | ⟨h, -⟩
  · exact h
  · exact (d.center_ne_bot htZ (hSp4 2 ↥K hKq hZ' h)).elim
  · have := Nat.le_of_dvd (by norm_num) (hG24 ↥K hKq hZ' h)
    omega
  · exact (d.center_ne_bot htZ (hD4 2 ↥K hKq hZ' h)).elim
  · obtain ⟨-, a, ha, -⟩ := h
    omega
  · exact (d.center_ne_bot htZ (schurMult2U4_holds 2 le_rfl ↥K hKq hZ' h)).elim
  · exact (d.center_ne_bot htZ (schurMult2U5_holds 2 ↥K hKq hZ' h)).elim
  · omega

theorem not_c31Case2 {H R M K : Subgroup G} (hKq : CFSG.Open.IsQuasisimple ↥K)
    (htZ : t ∈ centerOf K) (h2 : C31Case2 H R M (Lt L t) V K) : False := by
  obtain ⟨n, -, hpsl, -⟩ := h2
  exact d.not_isSimpleGroup hKq htZ (CFSG.LieType.Simplicity.fam_PSL_simplicity _ n 2 1 hpsl).2

theorem not_c31Case3 (hM22 : SchurMult2M22) (hV2 : ∀ v ∈ V, v ^ 2 = 1) {H R M K : Subgroup G}
    (hKq : CFSG.Open.IsQuasisimple ↥K) (hZ : IsPGroup 2 ↥(centerOf K))
    (hM0 : Lt L t = conjClosure (Lt L t) M) (hLK : Lt L t ≤ K)
    (h3 : C31Case3 H R M (Lt L t) V K) : False := by
  obtain ⟨hspor, hshape⟩ := h3
  rw [← hM0] at hshape
  rcases hshape with ⟨N, _, hN4, hNq⟩ | h6 | h32
  ·
    have hNc : Nat.card ↥N = 16 := by rw [A38c14.card_of_isE2 hN4]; norm_num
    have hN2 : IsPGroup 2 ↥N := fun x => ⟨1, by rw [pow_one]; exact MS93.sq_eq_one_of_isE2 hN4 x⟩
    have hY : Nat.card (↥(imageModCenter K (Lt L t)) ⧸ N) = Nat.card (ModO2 (Lt L t)) := by
      rw [GoldS146R.card_isPSL_two_two hNq, d.card_modO2]
      norm_num
    have hle := card_le_of_isExt_image hLK hZ d.v_le_lt d.subgroupOf_le_pCore N hN2 hY
    rw [d.card_V, hNc] at hle
    have hVt := d.vt_le_centerOf hLK (by omega)
    obtain ⟨hcyc, hdvd⟩ := hM22 ↥K hKq (isPGroup_center hZ) hspor
    have h4 : Nat.card ↥(centerOf K) = 4 := by
      refine le_antisymm ?_ ?_
      · rw [← card_center_eq]
        exact Nat.le_of_dvd (by norm_num) hdvd
      · rw [← d.card_Vt]
        exact Subgroup.card_le_of_le hVt
    have heq : Vt L t = centerOf K := Subgroup.eq_of_le_of_card_ge hVt (by rw [h4, d.card_Vt])
    refine not_isCyclic_of_sq_eq_one (X := ↥(Subgroup.center ↥K))
      ((card_center_eq K).trans h4) (fun z => ?_) hcyc
    have hz : ((z : ↥K) : G) ∈ Vt L t := by
      rw [heq, ← map_center_eq_centerOf]
      exact ⟨z, z.2, rfl⟩
    have h1 : ((z : ↥K) : G) ^ 2 = 1 := hV2 _ (d.vt_le hz)
    exact Subtype.ext (Subtype.ext (by simpa using h1))
  · exact d.not_nine_dvd ((dvd_card_of_isExt h6 nine_dvd_of_isAlt_six).trans
      (card_imageModCenter_dvd hLK))
  · exact d.not_seven_dvd ((dvd_card_of_isExt h32 seven_dvd_of_isPSL_three).trans
      (card_imageModCenter_dvd hLK))

theorem not_c31Case4 {H R M K : Subgroup G} (hM0 : Lt L t = conjClosure (Lt L t) M)
    (h4 : C31Case4 H R M (Lt L t) V K) : False := by
  obtain ⟨-, hshape⟩ := h4
  rw [← hM0] at hshape
  rcases hshape with ⟨N, _, hN4, hNq⟩ | h7 | h32
  · have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [GoldS146R.card_isPSL_two_two hNq, A38c14.card_of_isE2 hN4, d.card_Lt] at h1
    have h2 := d.card_V_le
    rw [d.card_V] at h2
    norm_num at h1
    omega
  · exact d.not_seven_dvd (dvd_card_of_isExt h7 seven_dvd_of_isAlt_seven)
  · exact d.not_seven_dvd (dvd_card_of_isExt h32 seven_dvd_of_isPSL_three)

theorem not_c31Case5 {H R M K : Subgroup G} (hM0 : Lt L t = conjClosure (Lt L t) M)
    (h5 : C31Case5 H R M (Lt L t) V K) : False := by
  obtain ⟨-, hshape⟩ := h5
  rw [← hM0] at hshape
  rcases hshape with h | h | h
  · exact d.not_nine_dvd (dvd_card_of_isExt h nine_dvd_of_isHat)
  · exact d.not_seven_dvd (dvd_card_of_isExt h seven_dvd_of_isPSL_four)
  · exact d.not_seven_dvd (dvd_card_of_isExt h seven_dvd_of_isPSL_three)

theorem not_c31Case6 {H R M K : Subgroup G}
    (hM0 : Lt L t = conjClosure (Lt L t) M) (h6 : C31Case6 H R M (Lt L t) V K) : False := by
  obtain ⟨-, h | h | h⟩ := h6
  · unfold C31Case6M24 at h
    rw [← hM0] at h
    exact d.not_seven_dvd (dvd_card_of_isExt h seven_dvd_of_isSporadic_M24)
  · unfold C31Case6L3 at h
    rw [← hM0] at h
    exact d.not_seven_dvd (dvd_card_of_isExt h seven_dvd_of_isPSL_three)
  · unfold C31Case6L5 at h
    rw [← hM0] at h
    exact d.not_seven_dvd (dvd_card_of_isExt h seven_dvd_of_isPSL_five)

theorem not_c31Case7 {H R M K : Subgroup G} (hM0 : Lt L t = conjClosure (Lt L t) M)
    (hLK : Lt L t ≤ K) (h7 : C31Case7 H R M (Lt L t) V K) : False := by
  obtain ⟨-, hshape⟩ := h7
  rw [← hM0] at hshape
  rcases hshape with h | h
  · exact d.not_seven_dvd ((dvd_card_of_isExt h seven_dvd_of_isPSL_three).trans
      (card_imageModCenter_dvd hLK))
  · exact d.not_nine_dvd ((dvd_card_of_isExt h nine_dvd_of_isAlt_six).trans
      (card_imageModCenter_dvd hLK))

theorem not_c31Case8 {H R M K : Subgroup G} (hM0 : Lt L t = conjClosure (Lt L t) M)
    (h8 : C31Case8 H R M (Lt L t) V K) : False := by
  obtain ⟨-, h⟩ := h8
  rw [← hM0] at h
  exact d.not_nine_dvd (dvd_card_of_isExt h nine_dvd_of_isHat)

theorem not_c31Case9 {H R M K : Subgroup G} (hM0 : Lt L t = conjClosure (Lt L t) M)
    (hLK : Lt L t ≤ K) (h9 : C31Case9 H R M (Lt L t) V K) : False := by
  obtain ⟨-, hshape⟩ := h9
  rw [← hM0] at hshape
  rcases hshape with h | h
  · exact d.not_seven_dvd ((dvd_card_of_isExt h seven_dvd_of_isPSL_three).trans
      (card_imageModCenter_dvd hLK))
  · exact d.not_seven_dvd ((dvd_card_of_isExt h seven_dvd_of_isPSU).trans
      (card_imageModCenter_dvd hLK))

theorem not_c31Case10 {H R M K : Subgroup G} (h10 : C31Case10 H R M (Lt L t) V K) : False := by
  obtain ⟨-, -, -, -, h16, -⟩ := h10
  have := d.card_V
  rw [h16] at this
  norm_num at this

theorem c31_analysis
    (hSp4 : SchurMult2Sp4)
    (hG24 : SchurMult2G24) (hD4 : SchurMult2D4) (hM22 : SchurMult2M22)
    (hV2 : ∀ v ∈ V, v ^ 2 = 1) {H R M K : Subgroup G} (hKq : CFSG.Open.IsQuasisimple ↥K)
    (htZ : t ∈ centerOf K) (h31 : C31Conclusion H R M (Lt L t) V K) :
    IsPSL 3 2 2 (↥K ⧸ Subgroup.center ↥K) ∧ Vt L t ≤ centerOf K := by
  obtain ⟨hM0, -, hLK, -, hZ, hcase⟩ := h31
  rw [← hM0] at hLK
  rcases hcase with h | h | h | h | h | h | h | h | h | h
  · exact d.c31Case1 hSp4 hG24 hD4 hKq hZ htZ hM0 hLK h
  · exact (d.not_c31Case2 hKq htZ h).elim
  · exact (d.not_c31Case3 hM22 hV2 hKq hZ hM0 hLK h).elim
  · exact (d.not_c31Case4 hM0 h).elim
  · exact (d.not_c31Case5 hM0 h).elim
  · exact (d.not_c31Case6 hM0 h).elim
  · exact (d.not_c31Case7 hM0 hLK h).elim
  · exact (d.not_c31Case8 hM0 h).elim
  · exact (d.not_c31Case9 hM0 hLK h).elim
  · exact (d.not_c31Case10 h).elim

end D127

end CFSG.Quasithin.H13.S127.L5
