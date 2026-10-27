module

public import CFSG.Quasithin.Recognition.J2RecHexagon
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Recognition.J2RecWords

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique Equiv CFSG.LieType.BorelTits J2Cz J2Cz.QM
open scoped Pointwise

theorem isStronglyEmbedded_of_centralizer_le {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (hK : K ≠ ⊤) {r : G} (hrK : r ∈ K) (hr : BenderSuzuki.PFAppendixIII.IsInvolution r)
    (hcent : ∀ y ∈ K, BenderSuzuki.PFAppendixIII.IsInvolution y →
      Subgroup.centralizer ({y} : Set G) ≤ K)
    (hfus : ∀ x ∈ K, ∀ y ∈ K, BenderSuzuki.PFAppendixIII.IsInvolution x → IsConj x y →
      ∃ k ∈ K, k * x * k⁻¹ = y) :
    BenderSuzuki.IsStronglyEmbedded K := by
  refine ⟨hK, ⟨r, hrK, hr⟩, fun {g} hg {x} hxK hxg hx => ?_⟩
  obtain ⟨k, hkK, hkx⟩ := Subgroup.mem_map.mp hxg
  have hk : k = g * x * g⁻¹ := by
    have e1 : g⁻¹ * k * g⁻¹⁻¹ = x := hkx
    rw [← e1]
    group
  obtain ⟨k', hk'K, hk'⟩ := hfus x hxK k hkK hx (isConj_iff.mpr ⟨g, hk.symm⟩)
  have hc : g⁻¹ * k' ∈ Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have e2 : k' * x = g * x * g⁻¹ * k' := by rw [← hk, ← hk']; group
    calc g⁻¹ * k' * x = g⁻¹ * (g * x * g⁻¹ * k') := by rw [mul_assoc, e2]
      _ = x * (g⁻¹ * k') := by group
  apply hg
  have e3 : g = k' * (g⁻¹ * k')⁻¹ := by group
  rw [e3]
  exact K.mul_mem hk'K (K.inv_mem (hcent x hxK hx hc))

namespace J2Frame

variable {G : Type} [Group G] [Finite G] {z : G} (F : J2Frame G z)

theorem exists_conj_z_or_t_of_mem {K : Subgroup G}
    (hHK : Subgroup.centralizer ({z} : Set G) ≤ K)
    (hQz : ∀ y ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)), y * y = 1 → y ≠ 1 →
      ∃ k ∈ K, k * y * k⁻¹ = z)
    {y : G} (hyK : y ∈ K) (hy2 : y * y = 1) (hy1 : y ≠ 1) :
    ∃ k ∈ K, k * y * k⁻¹ = z ∨ k * y * k⁻¹ = F.t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hPH⟩ := F.isTypeH2.exists_sylow_le_centralizer
  have hPK : (P : Subgroup G) ≤ K := hPH.trans hHK
  have hyK1 : (⟨y, hyK⟩ : ↥K) ≠ 1 := fun h1 => hy1 (congrArg Subtype.val h1)
  have hsp : IsPGroup 2 (Subgroup.zpowers (⟨y, hyK⟩ : ↥K)) :=
    IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, orderOf_eq_prime (Subtype.ext (by rw [pow_two]; exact hy2)) hyK1,
        pow_one])
  obtain ⟨P', hP'⟩ := hsp.exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq ↥K P' (P.subtype hPK)
  have h1 : MulAut.conj k ⟨y, hyK⟩ ∈ MulAut.conj k • (P' : Subgroup ↥K) :=
    Subgroup.smul_mem_pointwise_smul _ _ _ (hP' (Subgroup.mem_zpowers _))
  rw [← Sylow.coe_subgroup_smul, hk, Sylow.coe_subtype] at h1
  have hky : (k : G) * y * (k : G)⁻¹ ∈ (P : Subgroup G) := by
    have h2 : k * ⟨y, hyK⟩ * k⁻¹ ∈ (P : Subgroup G).subgroupOf K := by
      simpa [MulAut.conj_apply] using h1
    rw [Subgroup.mem_subgroupOf] at h2
    simpa using h2
  have hy'2 : (k : G) * y * (k : G)⁻¹ * ((k : G) * y * (k : G)⁻¹) = 1 := by
    calc (k : G) * y * (k : G)⁻¹ * ((k : G) * y * (k : G)⁻¹) = (k : G) * (y * y) * (k : G)⁻¹ := by
          group
      _ = 1 := by rw [hy2]; group
  have hy'1 : (k : G) * y * (k : G)⁻¹ ≠ 1 := fun h2 => hy1 (by
    calc y = (k : G)⁻¹ * ((k : G) * y * (k : G)⁻¹) * k := by group
      _ = 1 := by rw [h2]; group)
  by_cases hQ : (k : G) * y * (k : G)⁻¹ ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G))
  · obtain ⟨k', hk'K, hk'⟩ := hQz _ hQ hy'2 hy'1
    exact ⟨k' * k, K.mul_mem hk'K k.2, Or.inl (by rw [← hk']; group)⟩
  · obtain ⟨k', hk'H, hk'⟩ := F.exists_conj_eq_t (hPH hky) hy'2 hQ
    exact ⟨k' * k, K.mul_mem (hHK hk'H) k.2, Or.inr (by rw [← hk']; group)⟩

theorem nonempty_mulEquiv_J2 (hE : J2LineEndgame) (hcount : involutionClassCount G = 2)
    (h5 : 5 ∣ Nat.card (Subgroup.centralizer (F.L : Set G))) :
    Nonempty (G ≃* CFSG.Blueprint.NativeSporadic.J2) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hzz : z * z = 1 := by rw [← pow_two]; exact F.isTypeH2.sq
  obtain ⟨f, hfL, hf5, hf1, hzf⟩ := F.exists_mem_centralizer_L h5
  have hfcomm : ∀ l ∈ F.L, f * l = l * f := fun l hl =>
    ((Subgroup.mem_centralizer_iff.mp hfL) l hl).symm
  have hzL : ∀ l ∈ F.L, z * l = l * z := fun l hl =>
    (Subgroup.mem_centralizer_singleton_iff.mp (F.le hl)).symm
  set c := z * f with hc
  have hcL : ∀ l ∈ F.L, c * l = l * c := fun l hl => by
    rw [hc, mul_assoc, hfcomm l hl, ← mul_assoc, hzL l hl, mul_assoc]
  have hc2 : c * c = 1 := by
    calc c * c = (z * f * z) * f := by rw [hc]; group
      _ = 1 := by rw [hzf, inv_mul_cancel]
  have hzc : z * c = f := by rw [hc, ← mul_assoc, hzz, one_mul]
  have hzc5 : (z * c) ^ 5 = 1 := by rw [hzc]; exact hf5
  have hzc1 : z * c ≠ 1 := by rw [hzc]; exact hf1
  have hfX : f ∈ F.X := F.mem_X.mpr (hfcomm _ F.t_mem_L)
  have hfM : f ∈ F.M hcount := F.mem_M_of_pow_eq_one hcount hfX ⟨2, rfl⟩ hf5
  have hzM := F.W_le_M hcount F.z_mem_W
  have hcM : c ∈ F.M hcount := (F.M hcount).mul_mem hzM hfM
  have hfo : orderOf f = 5 := orderOf_eq_prime hf5 hf1
  have h5M : 5 ∣ Nat.card (F.M hcount) := by
    have h1 := Subgroup.orderOf_dvd_natCard (F.M hcount) hfM
    rwa [hfo] at h1
  obtain ⟨e⟩ := F.nonempty_mulEquiv_M hcount h5M
  have hord := F.orders_pt_four hcount hcM hc2 hzc5 hzc1 e
  obtain ⟨x, hxQ, h1, h2⟩ := F.exists_hexagon hcL hc2 hzc5 hzc1 hord
  set K := Subgroup.closure (insert z (insert c (Set.range x))) with hK
  have hzK : z ∈ K := Subgroup.subset_closure (Set.mem_insert _ _)
  have hcK : c ∈ K := Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hxK : ∀ i, x i ∈ K := fun i =>
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ ⟨i, rfl⟩))
  have hQK : pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) ≤ K := by
    rw [← F.isTypeH2.closure_eq_pCoreOf hxQ h1]
    exact (Subgroup.closure_le K).mpr (by rintro _ ⟨i, rfl⟩; exact hxK i)
  obtain ⟨w₃, w₅, g, h3K, h5K, hgK, h3c, h3o, h3, h5c, h5o, h5', hg⟩ := hE.exists_words h1 h2
  have hHK : Subgroup.centralizer ({z} : Set G) ≤ K :=
    F.isTypeH2.centralizer_le_of_orders hQK h3K h5K h3c h5c h3o h3 h5o h5'
  have hQz : ∀ y ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)), y * y = 1 → y ≠ 1 →
      ∃ k ∈ K, k * y * k⁻¹ = z := by
    intro y hyQ hy2 hy1
    by_cases hyz : y = z
    · exact ⟨1, one_mem _, by rw [hyz]; group⟩
    · obtain ⟨c', hc'H, hc'⟩ := F.isTypeH2.exists_conj_of_noncentral hyQ hy2 hy1 hyz (hxQ 0)
        (h1.x_sq 0) (h1.x_ne_one F.isTypeH2.ne_one 0) (h1.x_ne_d F.isTypeH2.ne_one 0)
      have hg0 : g 0 * z * (g 0)⁻¹ = x 0 := by rw [(hg 0).1, mul_inv_cancel_right]
      refine ⟨(g 0)⁻¹ * c', K.mul_mem (K.inv_mem (hgK 0)) (hHK hc'H), ?_⟩
      calc (g 0)⁻¹ * c' * y * ((g 0)⁻¹ * c')⁻¹ = (g 0)⁻¹ * (c' * y * c'⁻¹) * g 0 := by group
        _ = (g 0)⁻¹ * (g 0 * z * (g 0)⁻¹) * g 0 := by rw [hc', hg0]
        _ = z := by group
  have hMK : F.M hcount ≤ K := by
    have hsimp : IsSimpleGroup ↥(F.M hcount) := e.isSimpleGroup_congr.mpr inferInstance
    have h60 : Nat.card ↥(F.M hcount) = 60 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      rfl
    have hcW : ∀ w ∈ F.W, c * w ≠ 1 := by
      intro w hw h3
      have hcw : c = w⁻¹ := eq_inv_of_mul_eq_one_left h3
      have hfW : f ∈ F.W := by
        rw [← hzc, hcw]
        exact F.W.mul_mem F.z_mem_W (F.W.inv_mem hw)
      apply hf1
      have hff := F.mul_self_of_mem_W hfW
      calc f = f ^ 5 * (f * f)⁻¹ * (f * f)⁻¹ := by group
        _ = 1 := by rw [hf5, hff]; group
    obtain ⟨y₃, hy₃M, hy₃K, hy₃⟩ : ∃ y ∈ F.M hcount, y ∈ K ∧ orderOf y = 3 := by
      rcases hord with ⟨h3', -⟩ | ⟨-, h3'⟩
      · exact ⟨c * F.pt 4, (F.M hcount).mul_mem hcM (F.W_le_M hcount F.pt_four_mem_W),
          K.mul_mem hcK (hQK (F.pt_mem 4)), orderOf_eq_prime h3' (hcW _ F.pt_four_mem_W)⟩
      · have hzx := F.W.mul_mem F.z_mem_W F.pt_four_mem_W
        exact ⟨c * (z * F.pt 4), (F.M hcount).mul_mem hcM (F.W_le_M hcount hzx),
          K.mul_mem hcK (K.mul_mem hzK (hQK (F.pt_mem 4))), orderOf_eq_prime h3' (hcW _ hzx)⟩
    have hfK : f ∈ K := by
      rw [← hzc]
      exact K.mul_mem hzK hcK
    have h3N : 3 ∣ Nat.card (K.subgroupOf (F.M hcount)) := by
      have h4 := Subgroup.orderOf_dvd_natCard (K.subgroupOf (F.M hcount))
        (x := ⟨y₃, hy₃M⟩) (Subgroup.mem_subgroupOf.mpr hy₃K)
      rwa [Subgroup.orderOf_mk, hy₃] at h4
    have h5N : 5 ∣ Nat.card (K.subgroupOf (F.M hcount)) := by
      have h4 := Subgroup.orderOf_dvd_natCard (K.subgroupOf (F.M hcount))
        (x := ⟨f, hfM⟩) (Subgroup.mem_subgroupOf.mpr hfK)
      rwa [Subgroup.orderOf_mk, hfo] at h4
    have h15 : 15 ∣ Nat.card (K.subgroupOf (F.M hcount)) :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 3 5) h3N h5N
    have hNtop := subgroup_eq_top_of_fifteen_dvd h60 h15
    intro m hm
    have h4 : (⟨m, hm⟩ : ↥(F.M hcount)) ∈ K.subgroupOf (F.M hcount) := by
      rw [hNtop]
      trivial
    exact Subgroup.mem_subgroupOf.mp h4
  have hXK : F.X ≤ K := by
    intro g' hg'
    obtain ⟨s, hsT, hs⟩ := F.exists_mem_T_mul_inv_mem_M hcount hg'
    have e1 : g' = g' * s⁻¹ * s := by group
    rw [e1]
    exact K.mul_mem (hMK hs) (hHK (F.T_le_centralizer hsT))
  have hcls : ∀ y ∈ K, y * y = 1 → y ≠ 1 → ∃ k ∈ K, k * y * k⁻¹ = z ∨ k * y * k⁻¹ = F.t :=
    fun y hyK hy2 hy1 => F.exists_conj_z_or_t_of_mem hHK hQz hyK hy2 hy1
  have hKtop : K = ⊤ := by
    by_contra hKne
    have hcent : ∀ y ∈ K, BenderSuzuki.PFAppendixIII.IsInvolution y →
        Subgroup.centralizer ({y} : Set G) ≤ K := by
      intro y hyK hy g' hg'
      obtain ⟨k, hkK, hk⟩ := hcls y hyK (by rw [← pow_two]; exact hy.2) hy.1
      have hkg : k * g' * k⁻¹ ∈ Subgroup.centralizer ({k * y * k⁻¹} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff] at hg' ⊢
        calc k * g' * k⁻¹ * (k * y * k⁻¹) = k * (g' * y) * k⁻¹ := by group
          _ = k * (y * g') * k⁻¹ := by rw [hg']
          _ = k * y * k⁻¹ * (k * g' * k⁻¹) := by group
      have hkgK : k * g' * k⁻¹ ∈ K := by
        rcases hk with hk | hk
        · rw [hk] at hkg
          exact hHK hkg
        · rw [hk] at hkg
          exact hXK hkg
      have e1 : g' = k⁻¹ * (k * g' * k⁻¹) * k := by group
      rw [e1]
      exact K.mul_mem (K.mul_mem (K.inv_mem hkK) hkgK) hkK
    have hfus : ∀ x' ∈ K, ∀ y ∈ K, BenderSuzuki.PFAppendixIII.IsInvolution x' → IsConj x' y →
        ∃ k ∈ K, k * x' * k⁻¹ = y := by
      intro x' hx'K y hyK hx' hxy
      obtain ⟨c₀, hc₀⟩ := isConj_iff.mp hxy
      have hx'2 : x' * x' = 1 := by rw [← pow_two]; exact hx'.2
      have hy2 : y * y = 1 := by
        rw [← hc₀]
        calc c₀ * x' * c₀⁻¹ * (c₀ * x' * c₀⁻¹) = c₀ * (x' * x') * c₀⁻¹ := by group
          _ = 1 := by rw [hx'2]; group
      have hy1 : y ≠ 1 := fun h3 => hx'.1 (by
        calc x' = c₀⁻¹ * (c₀ * x' * c₀⁻¹) * c₀ := by group
          _ = 1 := by rw [hc₀, h3]; group)
      obtain ⟨k₁, hk₁K, hk₁⟩ := hcls x' hx'K hx'2 hx'.1
      obtain ⟨k₂, hk₂K, hk₂⟩ := hcls y hyK hy2 hy1
      have hsame : ∀ r : G, k₁ * x' * k₁⁻¹ = r → k₂ * y * k₂⁻¹ = r →
          ∃ k ∈ K, k * x' * k⁻¹ = y := fun r h3 h4 =>
        ⟨k₂⁻¹ * k₁, K.mul_mem (K.inv_mem hk₂K) hk₁K, by
          calc k₂⁻¹ * k₁ * x' * (k₂⁻¹ * k₁)⁻¹ = k₂⁻¹ * (k₁ * x' * k₁⁻¹) * k₂ := by group
            _ = k₂⁻¹ * (k₂ * y * k₂⁻¹) * k₂ := by rw [h3, h4]
            _ = y := by group⟩
      have hx'c : ∀ r : G, k₁ * x' * k₁⁻¹ = r → IsConj r x' := fun r h3 =>
        isConj_iff.mpr ⟨k₁⁻¹, by rw [← h3]; group⟩
      have hyc : ∀ r : G, k₂ * y * k₂⁻¹ = r → IsConj y r := fun r h4 => isConj_iff.mpr ⟨k₂, h4⟩
      rcases hk₁ with hk₁ | hk₁ <;> rcases hk₂ with hk₂ | hk₂
      · exact hsame z hk₁ hk₂
      · exact absurd (((hx'c _ hk₁).trans hxy).trans (hyc _ hk₂)) (F.not_isConj_t hcount)
      · exact absurd ((((hx'c _ hk₁).trans hxy).trans (hyc _ hk₂)).symm) (F.not_isConj_t hcount)
      · exact hsame F.t hk₁ hk₂
    have hSE : BenderSuzuki.IsStronglyEmbedded K :=
      isStronglyEmbedded_of_centralizer_le hKne hzK ⟨F.isTypeH2.ne_one, F.isTypeH2.sq⟩ hcent hfus
    obtain ⟨g', hg'⟩ := hSE.involutions_conjugate (x := z) (y := F.t)
      ⟨F.isTypeH2.ne_one, F.isTypeH2.sq⟩ ⟨F.t_ne_one, by rw [pow_two]; exact F.t_mul_t⟩
    exact F.not_isConj_t hcount (isConj_iff.mpr ⟨g'⁻¹, by rw [inv_inv]; exact hg'⟩)
  obtain ⟨e'⟩ := hE G z c x h1 h2
  exact ⟨((Subgroup.topEquiv (G := G)).symm.trans (MulEquiv.subgroupCongr hKtop.symm)).trans e'⟩

end J2Frame

end CFSG.Quasithin
