module

public import CFSG.Quasithin.Recognition.J2RecTwoB
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallCardTwoA5

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique Equiv CFSG.LieType.BorelTits J2Cz J2Cz.QM
open scoped Pointwise commutatorElement

theorem nonempty_mulEquiv_alt5_of_centralizer {Y : Type} [Group Y] [Finite Y] {z s : Y}
    (hz2 : z * z = 1) (hz1 : z ≠ 1) (hs2 : s * s = 1) (hs1 : s ≠ 1) (hsz : s ≠ z)
    (hzs : z * s = s * z)
    (hC : ∀ g : Y, g * z = z * g → g = 1 ∨ g = z ∨ g = s ∨ g = z * s)
    (hinv : ∀ u : Y, u * u = 1 → u ≠ 1 → ∃ g : Y, g * u * g⁻¹ = z)
    (h5 : 5 ∣ Nat.card Y) : Nonempty (Y ≃* alternatingGroup (Fin 5)) := by
  have hto : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
  have hzt : ∀ x ∈ Subgroup.zpowers z, x = 1 ∨ x = z := by
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← zpow_mod_orderOf, hto]
    have h0 : 0 ≤ k % ((2 : ℕ) : ℤ) := Int.emod_nonneg _ (by norm_num)
    have h2 : k % ((2 : ℕ) : ℤ) < 2 := Int.emod_lt_of_pos _ (by norm_num)
    rcases (by omega : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1) with h | h
    · left
      rw [h, zpow_zero]
    · right
      rw [h, zpow_one]
  have hzcard : Nat.card (Subgroup.zpowers z) = 2 := by rw [Nat.card_zpowers, hto]
  have hsK : s ∉ Subgroup.zpowers z := fun h1 => by
    rcases hzt s h1 with h2 | h2
    · exact hs1 h2
    · exact hsz h2
  have hzC : z ∈ Subgroup.centralizer ({z} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hsC : s ∈ Subgroup.centralizer ({z} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hzs.symm
  have hjoin : Subgroup.centralizer ({z} : Set Y) = Subgroup.zpowers z ⊔ Subgroup.zpowers s := by
    apply le_antisymm
    · intro g hg
      rcases hC g (Subgroup.mem_centralizer_singleton_iff.mp hg) with rfl | rfl | rfl | rfl
      · exact one_mem _
      · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
      · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
      · exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
    · exact sup_le (Subgroup.zpowers_le.mpr hzC) (Subgroup.zpowers_le.mpr hsC)
  have hdisj : ∀ g : Y, g ∉ Subgroup.centralizer ({z} : Set Y) →
      Disjoint (Subgroup.zpowers z) ((Subgroup.zpowers z).conjBy g) := by
    intro g hg
    rw [Subgroup.disjoint_def]
    intro x hx hxg
    rcases hzt x hx with hx1 | hxt
    · exact hx1
    · exfalso
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxg
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
      rw [hxt] at hyx
      rcases hzt y hy with hy1 | hyt
      · apply hz1
        rw [← hyx, hy1]
        group
      · apply hg
        rw [Subgroup.mem_centralizer_singleton_iff]
        rw [hyt] at hyx
        calc g * z = g * z * g⁻¹ * g := by group
          _ = z * g := by rw [hyx]
  let h : CFSG.GorensteinWalter.BrauerSuzukiWallHypotheses Y :=
    { t := z
      K := Subgroup.zpowers z
      H := Subgroup.centralizer ({z} : Set Y)
      s := s
      t_involution := ⟨hz1, by rw [pow_two]; exact hz2⟩
      t_mem_K := Subgroup.mem_zpowers z
      H_eq_centralizer := rfl
      K_commutative := inferInstance
      s_involution := ⟨hs1, by rw [pow_two]; exact hs2⟩
      s_not_mem_K := hsK
      H_eq_join := hjoin
      fixed_subgroup_eq :=
        inf_eq_left.mpr (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hzs))
      s_inverts_K := fun x hx => by
        rcases hzt x hx with rfl | rfl
        · group
        · rw [← hzs, mul_inv_cancel_right]
          exact (inv_eq_of_mul_eq_one_right hz2).symm
      conjugate_disjoint := hdisj
      involutions_conjugate := fun u hu => hinv u (by rw [← pow_two]; exact hu.2) hu.1 }
  have hk : Nat.card h.K = 2 := hzcard
  have hNne : Subgroup.normalizer (h.H : Set Y) ≠ ⊤ := by
    intro htop
    obtain ⟨e4⟩ := h.normalizer_mulEquiv_alternatingGroup_four_of_card_K_eq_two hk
    have h12 : Nat.card ↥(Subgroup.normalizer (h.H : Set Y)) = 12 :=
      (Nat.card_congr e4.toEquiv).trans (alternatingGroup.card_of_card_eq_four (by simp))
    rw [htop, Subgroup.card_top] at h12
    rw [h12] at h5
    norm_num at h5
  exact h.mulEquiv_alternatingGroup_five_of_card_K_eq_two_of_normalizer_ne_top hk hNne

namespace J2Frame

variable {G : Type} [Group G] [Finite G] {z : G} (F : J2Frame G z)

theorem mul_conj_mem_W (hcount : involutionClassCount G = 2) {m : G} (hmX : m ∈ F.X)
    (hmN : m ∈ Subgroup.normalizer (F.T : Set G)) {x : G} (hx : x ∈ F.T) :
    x * (m * x * m⁻¹) ∈ F.W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hWinv : ∀ {g : G}, g ∈ Subgroup.normalizer (F.T : Set G) → ∀ w ∈ F.W,
      g * w * g⁻¹ ∈ F.W := fun hg w hw =>
    F.mem_W_of_conj hcount hw ((Subgroup.mem_normalizer_iff.mp hg w).mp (F.W_le_T hw))
  have hmT : ∀ y ∈ F.T, m * y * m⁻¹ ∈ F.T := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp hmN y).mp hy
  have hmiN : m⁻¹ ∈ Subgroup.normalizer (F.T : Set G) := Subgroup.inv_mem _ hmN
  have hmt : m * F.t * m⁻¹ = F.t := by rw [F.mem_X.mp hmX, mul_inv_cancel_right]
  obtain ⟨k, hk, hmk⟩ : ∃ k : ℕ, Odd k ∧ m ^ k ∈ F.T := by
    obtain ⟨e, k, hk, he⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos m).ne'
    refine ⟨k, hk, ?_⟩
    have hk0 : k ≠ 0 := by rintro rfl; exact (Nat.not_odd_zero hk).elim
    have h2 : IsPGroup 2 (Subgroup.zpowers (m ^ k)) := by
      refine IsPGroup.of_card (n := e) ?_
      rw [Nat.card_zpowers, orderOf_pow_of_dvd hk0 (he ▸ Dvd.intro_left _ rfl), he,
        Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hk0)]
    have hle : Subgroup.zpowers (m ^ k) ≤ Subgroup.normalizer (F.T : Set G) :=
      Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ hmN k)
    have heq := F.eq_T_of_isPGroup hcount (IsPGroup.to_sup_of_normal_right' h2 F.isPGroup_T hle)
      (sup_le (Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ hmX k)) F.T_le_X) le_sup_right
    rw [← heq]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have ha : F.a * (m * F.a * m⁻¹) ∈ F.W := by
    obtain ⟨l', hl', w', hw', hb⟩ := F.exists_eq_mul_of_mem_T (hmT F.a F.a_mem_T)
    rcases hl' with rfl | rfl | rfl | rfl
    · exfalso
      apply F.a_not_mem_W
      have e1 : F.a = m⁻¹ * w' * m⁻¹⁻¹ := by
        rw [one_mul] at hb
        rw [← hb]
        group
      rw [e1]
      exact hWinv hmiN w' hw'
    · exfalso
      apply F.ta_not_mem_W
      have e1 : F.a = F.t * (m⁻¹ * w' * m⁻¹⁻¹) := by
        calc F.a = m⁻¹ * (m * F.a * m⁻¹) * m := by group
          _ = m⁻¹ * (F.t * w') * m := by rw [hb]
          _ = (m⁻¹ * F.t * m) * (m⁻¹ * w' * m⁻¹⁻¹) := by group
          _ = F.t * (m⁻¹ * w' * m⁻¹⁻¹) := by
            rw [show m⁻¹ * F.t * m = F.t by
              rw [mul_assoc, ← F.mem_X.mp hmX, inv_mul_cancel_left]]
      rw [e1, ← mul_assoc, F.t_mul_t, one_mul]
      exact hWinv hmiN w' hw'
    · rw [hb, ← mul_assoc, F.a_mul_a, one_mul]
      exact hw'
    · exfalso
      have hpow : ∀ j : ℕ, ∃ w ∈ F.W, m ^ j * F.a * (m ^ j)⁻¹ = F.t ^ j * F.a * w := by
        intro j
        induction j with
        | zero => exact ⟨1, one_mem _, by simp⟩
        | succ j ih =>
          obtain ⟨w, hw, hj⟩ := ih
          refine ⟨w' * (m * w * m⁻¹), F.W.mul_mem hw' (hWinv hmN w hw), ?_⟩
          have hmtj : m * F.t ^ j * m⁻¹ = F.t ^ j := by rw [← conj_pow, hmt]
          calc m ^ (j + 1) * F.a * (m ^ (j + 1))⁻¹ = m * (m ^ j * F.a * (m ^ j)⁻¹) * m⁻¹ := by
                rw [pow_succ']
                group
            _ = m * (F.t ^ j * F.a * w) * m⁻¹ := by rw [hj]
            _ = (m * F.t ^ j * m⁻¹) * (m * F.a * m⁻¹) * (m * w * m⁻¹) := by group
            _ = F.t ^ j * (F.t * F.a * w') * (m * w * m⁻¹) := by rw [hmtj, hb]
            _ = F.t ^ (j + 1) * F.a * (w' * (m * w * m⁻¹)) := by
                rw [pow_succ]
                group
      obtain ⟨w, hw, hk'⟩ := hpow k
      have h1 : m ^ k * F.a * (m ^ k)⁻¹ = F.a := by
        rw [F.comm_of_mem_T hmk F.a_mem_T, mul_inv_cancel_right]
      have h2 : F.t ^ k = F.t := by
        obtain ⟨r, rfl⟩ := hk
        rw [pow_succ, pow_mul, pow_two, F.t_mul_t, one_pow, one_mul]
      rw [h1, h2] at hk'
      apply F.t_not_mem_W
      have e1 : F.t = F.a * w⁻¹ * F.a⁻¹ := by
        calc F.t = F.t * F.a * w * w⁻¹ * F.a⁻¹ := by group
          _ = F.a * w⁻¹ * F.a⁻¹ := by rw [← hk']
      rw [e1, F.comm_of_mem_T F.a_mem_T (F.W_le_T (F.W.inv_mem hw)), mul_inv_cancel_right]
      exact F.W.inv_mem hw
  obtain ⟨l, hl, w, hw, rfl⟩ := F.exists_eq_mul_of_mem_T hx
  have hlT : l ∈ F.T := by
    rcases hl with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact F.t_mem_T
    · exact F.a_mem_T
    · exact F.T.mul_mem F.t_mem_T F.a_mem_T
  have hwT := F.W_le_T hw
  have hmlT := hmT l hlT
  have key : l * (m * l * m⁻¹) ∈ F.W := by
    rcases hl with rfl | rfl | rfl | rfl
    · rw [one_mul, mul_one, mul_inv_cancel]
      exact one_mem _
    · rw [hmt, F.t_mul_t]
      exact one_mem _
    · exact ha
    · have e1 : F.t * F.a * (m * (F.t * F.a) * m⁻¹) = F.a * (m * F.a * m⁻¹) := by
        calc F.t * F.a * (m * (F.t * F.a) * m⁻¹) =
              F.t * F.a * ((m * F.t * m⁻¹) * (m * F.a * m⁻¹)) := by group
          _ = F.t * (F.a * F.t) * (m * F.a * m⁻¹) := by rw [hmt]; group
          _ = F.t * (F.t * F.a) * (m * F.a * m⁻¹) := by rw [F.t_mul_a_comm]
          _ = F.a * (m * F.a * m⁻¹) := by
            rw [show F.t * (F.t * F.a) = F.a by rw [← mul_assoc, F.t_mul_t, one_mul]]
      rw [e1]
      exact ha
  have e2 : l * w * (m * (l * w) * m⁻¹) = l * (m * l * m⁻¹) * (w * (m * w * m⁻¹)) := by
    calc l * w * (m * (l * w) * m⁻¹) = l * (w * (m * l * m⁻¹)) * (m * w * m⁻¹) := by group
      _ = l * ((m * l * m⁻¹) * w) * (m * w * m⁻¹) := by rw [F.comm_of_mem_T hwT hmlT]
      _ = l * (m * l * m⁻¹) * (w * (m * w * m⁻¹)) := by group
  rw [e2]
  exact F.W.mul_mem key (F.W.mul_mem hw (hWinv hmN w hw))

theorem isMulCommutative_sylowT (hcount : involutionClassCount G = 2) :
    IsMulCommutative ↥(F.sylowT hcount : Subgroup ↥F.X) :=
  ⟨⟨fun a b => Subtype.ext (Subtype.ext (F.comm_of_mem_T (Subgroup.mem_subgroupOf.mp a.2)
    (Subgroup.mem_subgroupOf.mp b.2)))⟩⟩

theorem mem_normalizer_T_of_mem_normalizer (hcount : involutionClassCount G = 2) {n : ↥F.X}
    (hn : n ∈ Subgroup.normalizer ((F.sylowT hcount : Subgroup ↥F.X) : Set ↥F.X)) :
    (n : G) ∈ Subgroup.normalizer (F.T : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  by_cases hgX : g ∈ F.X
  · have h1 := Subgroup.mem_normalizer_iff.mp hn ⟨g, hgX⟩
    rw [coe_sylowT, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at h1
    exact h1
  · constructor
    · intro hT
      exact absurd (F.T_le_X hT) hgX
    · intro hT
      exfalso
      apply hgX
      have e1 : g = (n : G)⁻¹ * ((n : G) * g * (n : G)⁻¹) * n := by group
      rw [e1]
      exact F.X.mul_mem (F.X.mul_mem (F.X.inv_mem n.2) (F.T_le_X hT)) n.2

theorem focalSubgroup_sylowT (hcount : involutionClassCount G = 2) :
    (F.sylowT hcount : Subgroup ↥F.X).focalSubgroup = F.W.subgroupOf F.X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := F.isMulCommutative_sylowT hcount
  apply le_antisymm
  · rw [Subgroup.focalSubgroup_def, Subgroup.closure_le]
    rintro g ⟨hgP, x, hxP, u, rfl⟩
    have hxT : (x : G) ∈ F.T := by
      rw [coe_sylowT, Subgroup.mem_subgroupOf] at hxP
      exact hxP
    have hxx : x * x = 1 := Subtype.ext (F.mul_self_of_mem_T hxT)
    have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
    obtain ⟨n, hnN, hn⟩ := (F.sylowT hcount).conj_eq_normalizer_conj_of_mem x⁻¹ u⁻¹
      (Subgroup.inv_mem _ hxP) (by
        have e1 : (u⁻¹)⁻¹ * x⁻¹ * u⁻¹ = x⁻¹ * ⁅x, u⁆ := by rw [commutatorElement_def]; group
        rw [e1]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hxP) hgP)
    have e2 : ⁅x, u⁆ = x * (n⁻¹ * x * n⁻¹⁻¹) := by
      calc ⁅x, u⁆ = x * ((u⁻¹)⁻¹ * x⁻¹ * u⁻¹) := by rw [commutatorElement_def]; group
        _ = x * (n⁻¹ * x⁻¹ * n) := by rw [hn]
        _ = x * (n⁻¹ * x * n⁻¹⁻¹) := by rw [hxi, inv_inv]
    show ⁅x, u⁆ ∈ F.W.subgroupOf F.X
    rw [e2, Subgroup.mem_subgroupOf]
    exact F.mul_conj_mem_W hcount (n⁻¹).2
      (Subgroup.inv_mem _ (F.mem_normalizer_T_of_mem_normalizer hcount hnN)) hxT
  ·
    have hx4W := F.pt_four_mem_W
    have hzx4W := F.W.mul_mem F.z_mem_W hx4W
    have hx4x4 := F.mul_self_of_mem_W hx4W
    have hzz := F.mul_self_of_mem_W F.z_mem_W
    have hx4i : (F.pt 4)⁻¹ = F.pt 4 := inv_eq_of_mul_eq_one_right hx4x4
    have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
    have hzP : (⟨z, F.z_mem_X⟩ : ↥F.X) ∈ (F.sylowT hcount : Subgroup ↥F.X) := by
      rw [coe_sylowT, Subgroup.mem_subgroupOf]
      exact F.W_le_T F.z_mem_W
    have hx4ne : F.pt 4 ≠ 1 := fun h1 =>
      x_ne_one 4 (F.emb_injective (h1.trans (map_one F.emb).symm))
    have hzx4ne : z * F.pt 4 ≠ 1 := fun h1 => by
      have h2 : F.emb (J2Cz.QM.z * x 4) = F.emb 1 := by
        rw [map_mul, F.emb_z, map_one]
        exact h1
      exact x_ne_z 4 (by
        have h3 := F.emb_injective h2
        calc x 4 = J2Cz.QM.z * (J2Cz.QM.z * x 4) := by rw [← mul_assoc, z_sq, one_mul]
          _ = J2Cz.QM.z := by rw [h3, mul_one])
    obtain ⟨u, huX, hu⟩ := F.exists_mem_X_conj_eq hcount hx4W hx4ne
    obtain ⟨v, hvX, hv⟩ := F.exists_mem_X_conj_eq hcount hzx4W hzx4ne
    have hgen : ∀ {y w : G} (hyX : y ∈ F.X) (hwW : w ∈ F.W), y * z * y⁻¹ = w →
        (⟨z * w⁻¹, F.X.mul_mem F.z_mem_X (F.X.inv_mem (F.W_le_T hwW).1)⟩ : ↥F.X) ∈
          (F.sylowT hcount : Subgroup ↥F.X).focalSubgroup := by
      intro y w hyX hwW hy
      rw [Subgroup.focalSubgroup_def]
      refine Subgroup.subset_closure ⟨?_, ⟨z, F.z_mem_X⟩, hzP, ⟨y, hyX⟩, ?_⟩
      · rw [coe_sylowT, Subgroup.mem_subgroupOf]
        exact F.T.mul_mem (F.W_le_T F.z_mem_W) (F.T.inv_mem (F.W_le_T hwW))
      · apply Subtype.ext
        rw [commutatorElement_def]
        show z * w⁻¹ = z * y * z⁻¹ * y⁻¹
        rw [← hy]
        group
    have h1 := hgen huX hx4W hu
    have h2 := hgen hvX hzx4W hv
    have e1 : z * (F.pt 4)⁻¹ = z * F.pt 4 := by rw [hx4i]
    have e2 : z * (z * F.pt 4)⁻¹ = F.pt 4 := by
      rw [mul_inv_rev, hx4i, hzi, F.comm_of_mem_W hx4W F.z_mem_W, ← mul_assoc, hzz, one_mul]
    intro g hg
    rw [Subgroup.mem_subgroupOf] at hg
    have hzx4 : (⟨z * F.pt 4, F.X.mul_mem F.z_mem_X (F.W_le_T hx4W).1⟩ : ↥F.X) ∈
        (F.sylowT hcount : Subgroup ↥F.X).focalSubgroup := by
      convert h1 using 2
      exact e1.symm
    have hx4 : (⟨F.pt 4, (F.W_le_T hx4W).1⟩ : ↥F.X) ∈
        (F.sylowT hcount : Subgroup ↥F.X).focalSubgroup := by
      convert h2 using 2
      exact e2.symm
    rcases F.mem_W.mp hg with h3 | h3 | h3 | h3
    · have : g = 1 := Subtype.ext h3
      rw [this]
      exact one_mem _
    · have : g = ⟨z * F.pt 4, F.X.mul_mem F.z_mem_X (F.W_le_T hx4W).1⟩ *
          ⟨F.pt 4, (F.W_le_T hx4W).1⟩ := by
        apply Subtype.ext
        show (g : G) = z * F.pt 4 * F.pt 4
        rw [h3, mul_assoc, hx4x4, mul_one]
      rw [this]
      exact Subgroup.mul_mem _ hzx4 hx4
    · have : g = ⟨F.pt 4, (F.W_le_T hx4W).1⟩ := Subtype.ext h3
      rw [this]
      exact hx4
    · have : g = ⟨z * F.pt 4, F.X.mul_mem F.z_mem_X (F.W_le_T hx4W).1⟩ := Subtype.ext h3
      rw [this]
      exact hzx4

noncomputable def M (hcount : involutionClassCount G = 2) : Subgroup G :=
  ((F.sylowT hcount : Subgroup ↥F.X).transferFocal.ker).map F.X.subtype

theorem M_le_X (hcount : involutionClassCount G = 2) : F.M hcount ≤ F.X :=
  Subgroup.map_subtype_le _

theorem mem_M (hcount : involutionClassCount G = 2) {g : G} :
    g ∈ F.M hcount ↔
      ∃ hg : g ∈ F.X, (F.sylowT hcount : Subgroup ↥F.X).transferFocal ⟨g, hg⟩ = 1 := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hg, h1⟩
    exact ⟨⟨g, hg⟩, h1, rfl⟩

theorem mem_M_and_mem_T_iff (hcount : involutionClassCount G = 2) {g : G} :
    g ∈ F.M hcount ∧ g ∈ F.T ↔ g ∈ F.W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker := Subgroup.ker_transferFocal_inf_eq_focalSubgroup (F.sylowT hcount)
  rw [F.focalSubgroup_sylowT hcount] at hker
  constructor
  · rintro ⟨hgM, hgT⟩
    obtain ⟨hgX, h1⟩ := (F.mem_M hcount).mp hgM
    have h2 : (⟨g, hgX⟩ : ↥F.X) ∈ (F.sylowT hcount : Subgroup ↥F.X).transferFocal.ker ⊓
        (F.sylowT hcount : Subgroup ↥F.X) := by
      refine Subgroup.mem_inf.mpr ⟨h1, ?_⟩
      rw [coe_sylowT, Subgroup.mem_subgroupOf]
      exact hgT
    rw [hker, Subgroup.mem_subgroupOf] at h2
    exact h2
  · intro hgW
    have hgX := (F.W_le_T hgW).1
    have h2 : (⟨g, hgX⟩ : ↥F.X) ∈ (F.sylowT hcount : Subgroup ↥F.X).transferFocal.ker ⊓
        (F.sylowT hcount : Subgroup ↥F.X) := by
      rw [hker, Subgroup.mem_subgroupOf]
      exact hgW
    exact ⟨(F.mem_M hcount).mpr ⟨hgX, (Subgroup.mem_inf.mp h2).1⟩, F.W_le_T hgW⟩

theorem W_le_M (hcount : involutionClassCount G = 2) : F.W ≤ F.M hcount := fun _ hg =>
  ((F.mem_M_and_mem_T_iff hcount).mpr hg).1

theorem exists_mem_T_mul_inv_mem_M (hcount : involutionClassCount G = 2) {g : G}
    (hg : g ∈ F.X) : ∃ s ∈ F.T, g * s⁻¹ ∈ F.M hcount := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, hy⟩ := Subgroup.focalSubgroupOf.pow_index_surjective (F.sylowT hcount)
    ((F.sylowT hcount : Subgroup ↥F.X).transferFocal ⟨g, hg⟩)
  obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective _ y
  have h1 : (F.sylowT hcount : Subgroup ↥F.X).transferFocal (s : ↥F.X) =
      (F.sylowT hcount : Subgroup ↥F.X).transferFocal ⟨g, hg⟩ := by
    rw [Subgroup.transferFocal_eq_pow]
    exact hy
  have hs : (s : ↥F.X) ∈ F.T.subgroupOf F.X := s.2
  have hsT : ((s : ↥F.X) : G) ∈ F.T := Subgroup.mem_subgroupOf.mp hs
  refine ⟨((s : ↥F.X) : G), hsT, (F.mem_M hcount).mpr ⟨F.X.mul_mem hg (F.X.inv_mem (s : ↥F.X).2),
    ?_⟩⟩
  have e1 : (⟨g * ((s : ↥F.X) : G)⁻¹, F.X.mul_mem hg (F.X.inv_mem (s : ↥F.X).2)⟩ : ↥F.X) =
      ⟨g, hg⟩ * (s : ↥F.X)⁻¹ := rfl
  rw [e1, map_mul, map_inv, ← h1, mul_inv_cancel]

theorem mem_M_of_pow_eq_one (hcount : involutionClassCount G = 2) {f : G} (hfX : f ∈ F.X)
    {n : ℕ} (hn : Odd n) (hf : f ^ n = 1) : f ∈ F.M hcount := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine (F.mem_M hcount).mpr ⟨hfX, ?_⟩
  set P := F.sylowT hcount with hP
  have hQ : IsPGroup 2 (↥(P : Subgroup ↥F.X) ⧸ (P : Subgroup ↥F.X).focalSubgroupOf) :=
    P.isPGroup'.to_quotient _
  set y := (P : Subgroup ↥F.X).transferFocal ⟨f, hfX⟩ with hy
  have hyn : y ^ n = 1 := by
    rw [hy, ← map_pow]
    have : (⟨f, hfX⟩ : ↥F.X) ^ n = 1 := Subtype.ext (by simpa using hf)
    rw [this, map_one]
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hQ y
  have hd : orderOf y ∣ n := orderOf_dvd_of_pow_eq_one hyn
  rw [hk] at hd
  have hk0 : k = 0 := by
    by_contra hk0
    have h2 : 2 ∣ n := (dvd_pow_self 2 hk0).trans hd
    exact (Nat.not_even_iff_odd.mpr hn) (even_iff_two_dvd.mpr h2)
  rw [hk0, pow_zero, orderOf_eq_one_iff] at hk
  exact hk

theorem conj_mem_M (hcount : involutionClassCount G = 2) {m g : G} (hm : m ∈ F.M hcount)
    (hg : g ∈ F.X) : g * m * g⁻¹ ∈ F.M hcount := by
  obtain ⟨hmX, hm1⟩ := (F.mem_M hcount).mp hm
  refine (F.mem_M hcount).mpr ⟨F.X.mul_mem (F.X.mul_mem hg hmX) (F.X.inv_mem hg), ?_⟩
  have e1 : (⟨g * m * g⁻¹, F.X.mul_mem (F.X.mul_mem hg hmX) (F.X.inv_mem hg)⟩ : ↥F.X) =
      ⟨g, hg⟩ * ⟨m, hmX⟩ * (⟨g, hg⟩ : ↥F.X)⁻¹ := rfl
  rw [e1, map_mul, map_mul, hm1, mul_one, map_inv, mul_inv_cancel]

theorem mem_W_of_mem_M (hcount : involutionClassCount G = 2) {g : G} (hgM : g ∈ F.M hcount)
    (hgz : g * z = z * g) : g ∈ F.W :=
  (F.mem_M_and_mem_T_iff hcount).mp
    ⟨hgM, F.M_le_X hcount hgM, Subgroup.mem_centralizer_singleton_iff.mpr hgz⟩

theorem exists_mem_M_conj_eq_z (hcount : involutionClassCount G = 2) {y : G}
    (hyM : y ∈ F.M hcount) (hy2 : y * y = 1) (hy1 : y ≠ 1) :
    ∃ m ∈ F.M hcount, m * y * m⁻¹ = z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyX := F.M_le_X hcount hyM
  set P := F.sylowT hcount with hP
  have hyX1 : (⟨y, hyX⟩ : ↥F.X) ≠ 1 := fun h1 => hy1 (congrArg Subtype.val h1)
  have hsp : IsPGroup 2 (Subgroup.zpowers (⟨y, hyX⟩ : ↥F.X)) :=
    IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, orderOf_eq_prime (Subtype.ext (by rw [pow_two]; exact hy2)) hyX1,
        pow_one])
  obtain ⟨P', hP'⟩ := hsp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥F.X P' P
  have h1 : MulAut.conj g ⟨y, hyX⟩ ∈ MulAut.conj g • (P' : Subgroup ↥F.X) :=
    Subgroup.smul_mem_pointwise_smul _ _ _ (hP' (Subgroup.mem_zpowers _))
  rw [← Sylow.coe_subgroup_smul, hg] at h1
  have hgyT : (g : G) * y * (g : G)⁻¹ ∈ F.T := by
    have h2 : g * ⟨y, hyX⟩ * g⁻¹ ∈ (P : Subgroup ↥F.X) := by
      simpa [MulAut.conj_apply] using h1
    rw [hP, coe_sylowT, Subgroup.mem_subgroupOf] at h2
    simpa using h2
  have hgyW : (g : G) * y * (g : G)⁻¹ ∈ F.W :=
    (F.mem_M_and_mem_T_iff hcount).mp ⟨F.conj_mem_M hcount hyM g.2, hgyT⟩
  have hgy1 : (g : G) * y * (g : G)⁻¹ ≠ 1 := fun h2 => hy1 (by
    calc y = (g : G)⁻¹ * ((g : G) * y * (g : G)⁻¹) * g := by group
      _ = 1 := by rw [h2]; group)
  obtain ⟨u, huX, hu⟩ := F.exists_mem_X_conj_eq hcount hgyW hgy1
  obtain ⟨s, hsT, hms⟩ := F.exists_mem_T_mul_inv_mem_M hcount
    (F.X.mul_mem (F.X.inv_mem g.2) huX)
  refine ⟨((g : G)⁻¹ * u * s⁻¹)⁻¹, Subgroup.inv_mem _ hms, ?_⟩
  have hsz : s * z = z * s := Subgroup.mem_centralizer_singleton_iff.mp (F.T_le_centralizer hsT)
  calc ((g : G)⁻¹ * u * s⁻¹)⁻¹ * y * ((g : G)⁻¹ * u * s⁻¹)⁻¹⁻¹ =
        s * u⁻¹ * ((g : G) * y * (g : G)⁻¹) * u * s⁻¹ := by group
    _ = s * z * s⁻¹ := by rw [← hu]; group
    _ = z := by rw [hsz, mul_inv_cancel_right]

theorem nonempty_mulEquiv_M (hcount : involutionClassCount G = 2)
    (h5 : 5 ∣ Nat.card (F.M hcount)) :
    Nonempty (↥(F.M hcount) ≃* alternatingGroup (Fin 5)) := by
  have hzM := F.W_le_M hcount F.z_mem_W
  have hx4M := F.W_le_M hcount F.pt_four_mem_W
  have hzz := F.mul_self_of_mem_W F.z_mem_W
  have hx4x4 := F.mul_self_of_mem_W F.pt_four_mem_W
  have hx4ne : F.pt 4 ≠ 1 := fun h1 =>
    x_ne_one 4 (F.emb_injective (h1.trans (map_one F.emb).symm))
  have hx4z : F.pt 4 ≠ z := fun h1 =>
    x_ne_z 4 (F.emb_injective (h1.trans F.emb_z.symm))
  refine nonempty_mulEquiv_alt5_of_centralizer (z := ⟨z, hzM⟩) (s := ⟨F.pt 4, hx4M⟩)
    (Subtype.ext hzz) (fun h1 => F.isTypeH2.ne_one (congrArg Subtype.val h1))
    (Subtype.ext hx4x4) (fun h1 => hx4ne (congrArg Subtype.val h1))
    (fun h1 => hx4z (congrArg Subtype.val h1))
    (Subtype.ext (F.comm_of_mem_W F.z_mem_W F.pt_four_mem_W)) ?_ ?_ h5
  · intro g hg
    have hgW := F.mem_W_of_mem_M hcount g.2 (congrArg Subtype.val hg)
    rcases F.mem_W.mp hgW with h1 | h1 | h1 | h1
    · exact Or.inl (Subtype.ext h1)
    · exact Or.inr (Or.inl (Subtype.ext h1))
    · exact Or.inr (Or.inr (Or.inl (Subtype.ext h1)))
    · exact Or.inr (Or.inr (Or.inr (Subtype.ext h1)))
  · intro u hu hu1
    obtain ⟨m, hmM, hm⟩ := F.exists_mem_M_conj_eq_z hcount u.2 (congrArg Subtype.val hu)
      (fun h1 => hu1 (Subtype.ext h1))
    exact ⟨⟨m, hmM⟩, Subtype.ext hm⟩

end J2Frame

end CFSG.Quasithin
