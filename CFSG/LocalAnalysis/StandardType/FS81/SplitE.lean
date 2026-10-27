module

public import CFSG.LocalAnalysis.StandardType.GGFrameRouteFSInputs
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.LocalAnalysis.StandardType.FS81.SplitEAux

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Open CFSG.Assembly CFSG.ComponentClassification.OuterAutomorphisms

theorem fs81Sp_order3_unique {H : Type} [Group H] [Finite H] [IsCyclic H]
    {d b₀ : H} (hb₀ : orderOf b₀ = 3) (hd : d ^ 3 = 1) :
    d ∈ Subgroup.zpowers b₀ := by
  by_cases hd1 : d = 1
  · rw [hd1]
    exact Subgroup.one_mem _
  · have hd_order : orderOf d = 3 := by
      have hdvd : orderOf d ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hd
      exact (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd |>.resolve_left
        (fun h => hd1 (orderOf_eq_one_iff.mp h))
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := H)
    have hd_g : d ∈ Subgroup.zpowers g := hg d
    have hb₀_g : b₀ ∈ Subgroup.zpowers g := hg b₀
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hd_g
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hb₀_g
    have hgcd : (orderOf g).gcd i.natAbs = (orderOf g).gcd j.natAbs := by
      have h1 : orderOf (g ^ i) = 3 := by rw [hi]; exact hd_order
      have h2 : orderOf (g ^ j) = 3 := by rw [hj]; exact hb₀
      rw [orderOf_zpow] at h1
      rw [orderOf_zpow] at h2
      have ha_dvd : (orderOf g).gcd i.natAbs ∣ orderOf g := Nat.gcd_dvd_left _ _
      have hb_dvd : (orderOf g).gcd j.natAbs ∣ orderOf g := Nat.gcd_dvd_left _ _
      have h1' : 3 * (orderOf g).gcd i.natAbs = orderOf g := by
        have := Nat.div_mul_cancel ha_dvd
        rw [h1] at this
        exact this
      have h2' : 3 * (orderOf g).gcd j.natAbs = orderOf g := by
        have := Nat.div_mul_cancel hb_dvd
        rw [h2] at this
        exact this
      exact Nat.mul_left_cancel (by norm_num : 0 < 3) (h1'.trans h2'.symm)
    have hzp : Subgroup.zpowers d = Subgroup.zpowers b₀ := by
      rw [← hi, ← hj]
      rw [Subgroup.zpowers_eq_zpowers_iff']
      rw [Int.gcd_eq_natAbs, Int.gcd_eq_natAbs]
      simp only [Int.natAbs_natCast]
      simpa [Nat.gcd_comm] using hgcd
    rw [← hzp]
    exact Subgroup.mem_zpowers d

theorem fs81_split_E {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}
    (hb₀ : orderOf b₀ = 3) (hKC : K ≤ Subgroup.centralizer ({b₀} : Set G))
    (hKn : (K.subgroupOf (Subgroup.centralizer ({b₀} : Set G))).Normal)
    (hKz : Subgroup.center K = ⊥)
    (hOut : ¬ 3 ∣ Nat.card (Outer K))
    (hA2 : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (K : Set G) → IsPGroup 3 S → IsCyclic S)
    (hE : IsMaxElemAb3 (Subgroup.centralizer ({b₀} : Set G)) E) (hbE : b₀ ∈ E) :
    Disjoint (Subgroup.zpowers b₀) (E ⊓ K) ∧ Subgroup.zpowers b₀ ⊔ (E ⊓ K) = E ∧
      IsMaxElemAb3 K (E ⊓ K) := by
  let C := Subgroup.centralizer ({b₀} : Set G)
  let D := C ⊓ Subgroup.centralizer (K : Set G)
  have hK_le_C : K ≤ C := hKC
  have hb₀_mem_C : b₀ ∈ C := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
  have hb₀_mem_CK : b₀ ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact (Subgroup.mem_centralizer_iff.mp (hK_le_C hk) b₀ (by simp)).symm
  have hb₀_mem_D : b₀ ∈ D := ⟨hb₀_mem_C, hb₀_mem_CK⟩
  have hD_le_C : D ≤ C := inf_le_left
  have hD_le_CK : D ≤ Subgroup.centralizer (K : Set G) := inf_le_right
  have hK_le_D_sup : K ≤ K ⊔ D := le_sup_left
  have hD_le_sup : D ≤ K ⊔ D := le_sup_right
  have hKD_comm : ∀ k ∈ K, ∀ d ∈ D, k * d = d * k := fs81Sp_comm
  have hKD_disjoint : K ⊓ D = ⊥ := fs81Sp_inf_eq_bot hKC hKz
  have hC_le_norm : C ≤ Subgroup.normalizer (K : Set G) := by
    rw [← Subgroup.normal_subgroupOf_iff_le_normalizer hK_le_C]
    exact hKn
  have hD_normal_C : (D.subgroupOf C).Normal := by
    have hDc_eq : D.subgroupOf C = Subgroup.centralizer (K.subgroupOf C : Set C) := by
      ext x
      constructor
      · intro hx
        rw [Subgroup.mem_subgroupOf] at hx
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        apply Subtype.ext
        exact Subgroup.mem_centralizer_iff.mp hx.2 (y : G) hy
      · intro hx
        rw [Subgroup.mem_centralizer_iff] at hx
        refine ⟨x.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
        intro y hy
        have hyC : y ∈ C := hK_le_C hy
        exact congrArg Subtype.val (hx ⟨y, hyC⟩ hy)
    rw [hDc_eq]
    exact Subgroup.normal_centralizer (H := K.subgroupOf C)
  have hK_normal_C : (K.subgroupOf C).Normal := hKn
  have hKD_normal_C : ((K ⊔ D).subgroupOf C).Normal := by
    rw [Subgroup.subgroupOf_sup hK_le_C hD_le_C]
    letI : (K.subgroupOf C).Normal := hK_normal_C
    letI : (D.subgroupOf C).Normal := hD_normal_C
    exact Subgroup.sup_normal (K.subgroupOf C) (D.subgroupOf C)
  have hKD_index_coprime : ¬ 3 ∣ ((K ⊔ D).subgroupOf C).index := fs81Sp_no_three_index hKC hKn hOut
  have hE_pgroup : IsPGroup 3 E := IsElemAbelian.isPGroup hE.2.1
  have hE_le_C : E ≤ C := hE.1
  have hE_sub_pgroup : IsPGroup 3 (E.subgroupOf C) :=
    hE_pgroup.of_equiv (Subgroup.subgroupOfEquivOfLe hE_le_C).symm
  obtain ⟨P, hE_le_P⟩ := IsPGroup.exists_le_sylow (p := 3) (G := C) hE_sub_pgroup
  have hP_le_KD : P ≤ (K ⊔ D).subgroupOf C := by
    have hS : ((K ⊔ D).subgroupOf C).Normal := hKD_normal_C
    exact fs81Sp_sylow_le_normal hKD_index_coprime P
  have hE_le_KD : E ≤ K ⊔ D := by
    intro e he
    have heC : e ∈ C := hE_le_C he
    have he_sub : (⟨e, heC⟩ : C) ∈ E.subgroupOf C := he
    have he_P : (⟨e, heC⟩ : C) ∈ P := hE_le_P he_sub
    have he_KD : (⟨e, heC⟩ : C) ∈ (K ⊔ D).subgroupOf C := hP_le_KD he_P
    exact he_KD
  have hE_inf_K_le_E : E ⊓ K ≤ E := inf_le_left
  have hb₀_mem_E : b₀ ∈ E := hbE
  have hb₀_mem_sup_E : b₀ ∈ Subgroup.zpowers b₀ ⊔ (E ⊓ K) := by
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers b₀)
  have hsup_le_E : Subgroup.zpowers b₀ ⊔ (E ⊓ K) ≤ E := by
    apply sup_le
    · exact Subgroup.zpowers_le.mpr hb₀_mem_E
    · exact inf_le_left
  have hE_le_sup : E ≤ Subgroup.zpowers b₀ ⊔ (E ⊓ K) := by
    intro e he
    obtain ⟨k, hk, d, hd, he_eq⟩ := fs81Sp_mem_sup_of_commute hKD_comm (hE_le_KD he)
    have hd_C : d ∈ C := hD_le_C hd
    have hd_comm_b₀ : d * b₀ = b₀ * d := by
      exact (Subgroup.mem_centralizer_iff.mp hd_C b₀ (by simp)).symm
    have hd_cube : d ^ 3 = 1 := by
      have he_cube : e ^ 3 = 1 := hE.2.1.2 e he
      have hkd_cube : (k * d) ^ 3 = k ^ 3 * d ^ 3 := by
        exact Commute.mul_pow (hKD_comm k hk d hd) 3
      rw [← he_eq, he_cube] at hkd_cube
      have hk3D : k ^ 3 ∈ D := by
        have hk3_eq : k ^ 3 = (d ^ 3)⁻¹ := by
          exact eq_inv_of_mul_eq_one_left hkd_cube.symm
        rw [hk3_eq]
        exact D.inv_mem (D.pow_mem hd 3)
      have hk3K : k ^ 3 ∈ K := K.pow_mem hk 3
      have hk3_bot : k ^ 3 ∈ (⊥ : Subgroup G) := by
        rw [← hKD_disjoint]
        exact ⟨hk3K, hk3D⟩
      have hk3_one : k ^ 3 = 1 := by simpa using hk3_bot
      rw [hk3_one, one_mul] at hkd_cube
      exact hkd_cube.symm
    have hd_in_zp : d ∈ Subgroup.zpowers b₀ := by
      have hH_le_D : Subgroup.zpowers d ⊔ Subgroup.zpowers b₀ ≤ D := by
        apply sup_le
        · exact Subgroup.zpowers_le.mpr hd
        · exact Subgroup.zpowers_le.mpr hb₀_mem_D
      have hH_le_CK : Subgroup.zpowers d ⊔ Subgroup.zpowers b₀ ≤ Subgroup.centralizer (K : Set G) :=
        hH_le_D.trans hD_le_CK
      have hH_pgroup : IsPGroup 3 ↥(Subgroup.zpowers d ⊔ Subgroup.zpowers b₀) := by
        have hd_elem : IsElemAbelian 3 (Subgroup.zpowers d) := isElemAbelian_zpowers hd_cube
        have hb0_elem : IsElemAbelian 3 (Subgroup.zpowers b₀) :=
          isElemAbelian_zpowers (by rw [← hb₀]; exact pow_orderOf_eq_one b₀)
        exact (hd_elem.sup_of_commute hb0_elem (by
          intro a ha b hb
          obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp ha
          obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hb
          rw [← hi, ← hj]
          exact ((show Commute d b₀ from hd_comm_b₀).zpow_left i).zpow_right j)).isPGroup
      have hH_cyc : IsCyclic ↥(Subgroup.zpowers d ⊔ Subgroup.zpowers b₀) :=
        hA2 (Subgroup.zpowers d ⊔ Subgroup.zpowers b₀) hH_le_CK hH_pgroup
      haveI : IsCyclic ↥(Subgroup.zpowers d ⊔ Subgroup.zpowers b₀) := hH_cyc
      let dH : ↥(Subgroup.zpowers d ⊔ Subgroup.zpowers b₀) :=
        ⟨d, Subgroup.mem_sup_left (Subgroup.mem_zpowers d)⟩
      let b₀H : ↥(Subgroup.zpowers d ⊔ Subgroup.zpowers b₀) :=
        ⟨b₀, Subgroup.mem_sup_right (Subgroup.mem_zpowers b₀)⟩
      have hd3H : dH ^ 3 = 1 := by
        apply Subtype.ext
        simp [dH, hd_cube]
      have hb₀_order_H : orderOf b₀H = 3 := by
        rw [← Subgroup.orderOf_coe b₀H]
        exact hb₀
      have hmem := fs81Sp_order3_unique (d := dH) (b₀ := b₀H) hb₀_order_H hd3H
      rw [Subgroup.mem_zpowers_iff] at hmem
      obtain ⟨j, hj⟩ := hmem
      rw [Subgroup.mem_zpowers_iff]
      use j
      have := congrArg Subtype.val hj
      simpa [dH, b₀H] using this
    have hk_mem_EK : k ∈ E ⊓ K := by
      constructor
      · have hd_E : d ∈ E := Subgroup.zpowers_le.mpr hb₀_mem_E hd_in_zp
        have hk_eq : k = e * d⁻¹ := by
          rw [he_eq]
          group
        rw [hk_eq]
        exact E.mul_mem he (E.inv_mem hd_E)
      · exact hk
    rw [he_eq]
    have hd_mem_sup : d ∈ Subgroup.zpowers b₀ ⊔ (E ⊓ K) := Subgroup.mem_sup_left hd_in_zp
    have hk_mem_sup : k ∈ Subgroup.zpowers b₀ ⊔ (E ⊓ K) := Subgroup.mem_sup_right hk_mem_EK
    exact mul_mem hk_mem_sup hd_mem_sup
  have hsup_eq_E : Subgroup.zpowers b₀ ⊔ (E ⊓ K) = E := le_antisymm hsup_le_E hE_le_sup
  have h_disjoint : Disjoint (Subgroup.zpowers b₀) (E ⊓ K) := by
    rw [disjoint_iff]
    apply le_antisymm _ bot_le
    intro x hx
    have hx_zp : x ∈ Subgroup.zpowers b₀ := hx.1
    have hx_EK : x ∈ E ⊓ K := hx.2
    have hx_K : x ∈ K := hx_EK.2
    have hb₀_not_K : b₀ ∉ K := by
      intro hb₀K
      have hb₀_D : b₀ ∈ D := hb₀_mem_D
      have hb₀_inf : b₀ ∈ K ⊓ D := ⟨hb₀K, hb₀_D⟩
      rw [hKD_disjoint] at hb₀_inf
      have hb₀_one : b₀ = 1 := by simpa using hb₀_inf
      rw [hb₀_one, orderOf_one] at hb₀
      exact Nat.succ_ne_zero 0 (by simpa using hb₀.symm)
    haveI : Fact (Nat.card (Subgroup.zpowers b₀)).Prime := by
      rw [Nat.card_zpowers, hb₀]
      exact ⟨by norm_num⟩
    let H := (Subgroup.zpowers b₀ ⊓ K).subgroupOf (Subgroup.zpowers b₀)
    have hH : H = ⊥ ∨ H = ⊤ := Subgroup.eq_bot_or_eq_top_of_prime_card (G := Subgroup.zpowers b₀) H
    rcases hH with hbot | htop
    · have hxH : (⟨x, hx_zp⟩ : Subgroup.zpowers b₀) ∈ H := by
        change x ∈ Subgroup.zpowers b₀ ⊓ K
        exact ⟨hx_zp, hx_K⟩
      rw [hbot] at hxH
      have hx_one : (⟨x, hx_zp⟩ : Subgroup.zpowers b₀) = 1 := by simpa using hxH
      exact Subtype.ext_iff.mp hx_one
    · have hle : Subgroup.zpowers b₀ ≤ K := by
        intro y hy
        have hyH : (⟨y, hy⟩ : Subgroup.zpowers b₀) ∈ H := by
          rw [htop]
          trivial
        have hy_inf : y ∈ Subgroup.zpowers b₀ ⊓ K := Subgroup.mem_subgroupOf.mp hyH
        exact hy_inf.2
      exact (hb₀_not_K (hle (Subgroup.mem_zpowers b₀))).elim
  refine ⟨h_disjoint, hsup_eq_E, ?_⟩
  have hE_inf_K_le_K : E ⊓ K ≤ K := inf_le_right
  have hE_inf_K_elem : IsElemAbelian 3 (E ⊓ K) := hE.2.1.mono inf_le_left
  refine ⟨hE_inf_K_le_K, hE_inf_K_elem, ?_⟩
  intro E' hE'_K hE'_elem hE_inf_K_le_E'
  have hb₀_comm_E' : ∀ b ∈ Subgroup.zpowers b₀, ∀ e ∈ E', b * e = e * b := by
    intro b hb e he
    have he_K : e ∈ K := hE'_K he
    have he_comm_b₀ : e * b₀ = b₀ * e :=
      (Subgroup.mem_centralizer_iff.mp (hK_le_C he_K) b₀ (by simp)).symm
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hb
    rw [← hn]
    exact ((show Commute e b₀ from he_comm_b₀).zpow_right n).eq.symm
  have hsup_elem : IsElemAbelian 3 (Subgroup.zpowers b₀ ⊔ E') := by
    apply IsElemAbelian.sup_of_commute
      (isElemAbelian_zpowers (by rw [← hb₀]; exact pow_orderOf_eq_one b₀)) hE'_elem hb₀_comm_E'
  have hsup_le_C : Subgroup.zpowers b₀ ⊔ E' ≤ C := by
    apply sup_le
    · exact Subgroup.zpowers_le.mpr (hE.1 hb₀_mem_E)
    · exact hE'_K.trans hK_le_C
  have hE_le_sup_E' : E ≤ Subgroup.zpowers b₀ ⊔ E' := by
    rw [← hsup_eq_E]
    exact sup_le_sup (le_refl _) hE_inf_K_le_E'
  have hsup_eq_E : Subgroup.zpowers b₀ ⊔ E' = E :=
    hE.2.2 _ hsup_le_C hsup_elem hE_le_sup_E'
  apply le_antisymm _ hE_inf_K_le_E'
  intro x hx
  have hx_E : x ∈ E := by
    have hx_sup : x ∈ Subgroup.zpowers b₀ ⊔ E' := Subgroup.mem_sup_right hx
    rw [hsup_eq_E] at hx_sup
    exact hx_sup
  exact ⟨hx_E, hE'_K hx⟩

end CFSG.StandardType.FrameRoute
