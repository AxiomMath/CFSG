module

public import CFSG.Quasithin.H13.A6S13821L32HatB
public import CFSG.Quasithin.H13.A6S13821L32HatC2

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom

namespace L32HatC3

open CFSG.Quasithin.H13.A6.L32HatC2 (SX1 SX2 theta theta_mem_X1 theta_mem_X2 E0_le_X1
  E0_normal_X1 E0_sq A0_le_oTwoUpper_X1)

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem map_theta_X2 : SX2.map (theta : SL3.S ≃* SL3.S).toMonoidHom = SX1 := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (theta_mem_X1 y).2 hy
  · intro hx
    refine ⟨theta.symm x, ?_, by simp⟩
    refine (theta_mem_X1 (theta.symm x)).1 ?_
    rw [MulEquiv.apply_symm_apply]
    exact hx

theorem map_theta_X1 : SX1.map (theta : SL3.S ≃* SL3.S).toMonoidHom = SX2 := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (theta_mem_X2 y).2 hy
  · intro hx
    refine ⟨theta.symm x, ?_, by simp⟩
    refine (theta_mem_X2 (theta.symm x)).1 ?_
    rw [MulEquiv.apply_symm_apply]
    exact hx

theorem map_theta_P0 : (SX1 ⊓ SX2).map (theta : SL3.S ≃* SL3.S).toMonoidHom = SX1 ⊓ SX2 := by
  rw [Subgroup.map_inf _ _ (theta : SL3.S ≃* SL3.S).toMonoidHom theta.injective, map_theta_X1,
    map_theta_X2, inf_comm]

theorem le_pCoreOf_of_two {Y H : Subgroup G} (hYH : Y ≤ H)
    (hN : H ≤ Subgroup.normalizer (Y : Set G)) (hY : ∀ y ∈ Y, ∃ k : ℕ, y ^ 2 ^ k = 1) :
    Y ≤ pCoreOf 2 H := by
  have hnorm : (Y.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYH).mpr hN
  have h2 : IsPGroup 2 ↥(Y.subgroupOf H) := by
    intro x
    obtain ⟨k, hk⟩ := hY x.1 (Subgroup.mem_subgroupOf.mp x.2)
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    simpa using hk
  have hle : Y.subgroupOf H ≤ CFSG.pCore 2 ↥H := le_sSup ⟨hnorm, h2⟩
  intro y hy
  exact Subgroup.mem_map.mpr ⟨⟨y, hYH hy⟩, hle (Subgroup.mem_subgroupOf.mpr hy), rfl⟩

theorem two_pow_of_mem_pCoreOf {K : Subgroup G} {x : G} (hx : x ∈ pCoreOf 2 K) :
    ∃ j : ℕ, x ^ 2 ^ j = 1 := by
  obtain ⟨j, hj⟩ := pCoreOf_isPGroup 2 K ⟨x, hx⟩
  exact ⟨j, by simpa using congrArg Subtype.val hj⟩

theorem exists_pi_good {S : Setting4 G T L V}
    (h139 : Stmt13_3_9) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h1334 : Stmt13_3_4)
    (hS : S.Hyp138) (hhat : IsHatA6 L) {H K : Subgroup G} (hH : H ∈ S.Hz) (hK : K ∈ cComp H)
    (hKn : H ≤ Subgroup.normalizer (K : Set G)) (hP : IsPSL 3 2 1 (↥K ⧸ CFSG.pCore 2 ↥K))
    (hHK : H = K ⊔ (S.L1 ⊔ T)) :
    ∃ π : ↥K →* SL3.S, Function.Surjective π ∧ (∀ k : ↥K, π k = 1 ↔ (k : G) ∈ pCoreOf 2 K) ∧
      (∀ e ∈ L32HatM.E₀, ∃ k : ↥K, (k : G) ∈ pCoreOf 2 (S.L1 ⊔ T) ∧ π k = e) ∧
      (∀ a ∈ L32HatM.A₀, ∃ k : ↥K, (k : G) ∈ l0 L ∧ π k = a) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hL1H : S.L1 ⊔ T ≤ H := hH.1.1
  have hTH : T ≤ H := le_sup_right.trans hL1H
  have hTsylH : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.h13.sylow hTH
  have hP' : IsPSL 3 2 1 (L32A.cStar K) := IsPSL.of_mulEquiv (L32A.C.cStarEquiv K).symm hP
  obtain ⟨π₀, hπ₀, hker₀, hD₀⟩ := L32HatStep.exists_pi_sl3 hK hKn hTsylH hP'
  have hL0K : l0 L ≤ K := S.l0_le_of_hat h139 h37 h38 hhat hH hK hKn hP
  have hL0M : l0 L ≤ S.L1 ⊔ T := (S.l0_le_L1).trans le_sup_left
  have hTl0 : T ≤ Subgroup.normalizer (l0 L : Set G) := S.frame.T_le.trans S.normalizer_le_l0
  have hMK : S.L1 ⊔ T ≤ Subgroup.normalizer (K : Set G) := hL1H.trans hKn
  have hsolvM : Group.IsSolvable ↥(S.L1 ⊔ T) := S.isSolvable_L1T h1334 hS
  have hS₀M : K ⊓ (S.L1 ⊔ T) ≤ S.L1 ⊔ T := inf_le_right
  have hsolv₀ : Group.IsSolvable ↥(K ⊓ (S.L1 ⊔ T)) :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hS₀M)
      (Subgroup.inclusion_injective hS₀M)
  obtain ⟨c, hcL0, hc3, hcO, -⟩ := l0_decomp hhat
  have hcK : c ∈ K := hL0K hcL0
  have hcM : c ∈ K ⊓ (S.L1 ⊔ T) := ⟨hcK, hL0M hcL0⟩
  have hcO' : c ∉ pCoreOf 2 K := by
    intro hcQ
    apply hcO
    obtain ⟨j, hj⟩ := two_pow_of_mem_pCoreOf hcQ
    have h1 : c = 1 := by
      have hg : c ^ (Nat.gcd 3 (2 ^ j)) = 1 := (pow_gcd_eq_one).2 ⟨hc3, hj⟩
      have hcop : Nat.gcd 3 (2 ^ j) = 1 := Nat.Coprime.pow_right j (by norm_num)
      rwa [hcop, pow_one] at hg
    rw [h1]
    exact (pCoreOf 2 (l0 L)).one_mem
  have hTS₀ : ∀ t ∈ T, t ∈ K → t ∈ K ⊓ (S.L1 ⊔ T) := fun t ht htK =>
    ⟨htK, Subgroup.mem_sup_right ht⟩
  have hpar := L32HatStep.image_is_parabolic hK hπ₀ hker₀ hD₀ inf_le_left hsolv₀ hTS₀ hcK hcM
    hc3 hcO'
  obtain ⟨π, hπ, hker, hD, hX⟩ : ∃ π : ↥K →* SL3.S, Function.Surjective π ∧
      (∀ k : ↥K, π k = 1 ↔ (k : G) ∈ pCoreOf 2 K) ∧
      (T.subgroupOf K).map π = SL3.P0 ∧ ((K ⊓ (S.L1 ⊔ T)).subgroupOf K).map π = SX1 := by
    rcases hpar with h | h
    · exact ⟨π₀, hπ₀, hker₀, hD₀, h⟩
    · refine ⟨(theta : SL3.S ≃* SL3.S).toMonoidHom.comp π₀, theta.surjective.comp hπ₀, ?_, ?_, ?_⟩
      · intro k
        show theta (π₀ k) = 1 ↔ _
        exact (map_eq_one_iff theta theta.injective).trans (hker₀ k)
      · rw [← Subgroup.map_map]
        have hP0 : SL3.P0 = SX1 ⊓ SX2 := rfl
        rw [hD₀, hP0, map_theta_P0]
      · rw [← Subgroup.map_map, h, map_theta_X2]
  set Ŝ : Subgroup ↥K := (K ⊓ (S.L1 ⊔ T)).subgroupOf K with hŜdef
  let ψ : ↥Ŝ →* SL3.S := π.comp Ŝ.subtype
  have hψ : ∀ x : SL3.S, x ∈ SX1 → ∃ s : ↥Ŝ, ψ s = x := by
    intro x hx
    rw [← hX] at hx
    obtain ⟨s, hs, hsx⟩ := Subgroup.mem_map.mp hx
    exact ⟨⟨s, hs⟩, hsx⟩
  have hψX1 : ∀ s : ↥Ŝ, ψ s ∈ SX1 := by
    intro s
    rw [← hX]
    exact Subgroup.mem_map_of_mem π s.2
  let W : Subgroup ↥Ŝ := L32HatM.E₀.comap ψ
  have hW_mem : ∀ w : ↥Ŝ, w ∈ W ↔ ψ w ∈ L32HatM.E₀ := fun w => Iff.rfl
  have hW_norm : ∀ s : ↥Ŝ, ∀ w ∈ W, s * w * s⁻¹ ∈ W := by
    intro s w hw
    rw [hW_mem] at hw ⊢
    rw [map_mul, map_mul, map_inv]
    exact E0_normal_X1 (hψX1 s) hw
  have hW_pgroup : ∀ w ∈ W, ∃ k : ℕ, w ^ 2 ^ k = 1 := by
    intro w hw
    have h2 : ψ (w ^ 2) = 1 := by
      rw [map_pow]
      exact E0_sq ((hW_mem w).mp hw)
    have hG : (((w ^ 2 : ↥Ŝ) : ↥K) : G) ∈ pCoreOf 2 K := (hker _).mp h2
    obtain ⟨j, hj⟩ := two_pow_of_mem_pCoreOf hG
    refine ⟨j + 1, Subtype.ext (Subtype.ext ?_)⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at hj ⊢
    rw [pow_succ', pow_mul]
    exact hj
  let Wg : Subgroup G := W.map (K.subtype.comp Ŝ.subtype)
  have hWg_le : Wg ≤ K ⊓ (S.L1 ⊔ T) := by
    rintro _ ⟨w, -, rfl⟩
    exact Subgroup.mem_subgroupOf.mp w.2
  have hconj : ∀ g ∈ K ⊓ (S.L1 ⊔ T), ∀ x ∈ Wg, g * x * g⁻¹ ∈ Wg := by
    rintro g hg _ ⟨w, hw, rfl⟩
    refine ⟨(⟨⟨g, hg.1⟩, Subgroup.mem_subgroupOf.mpr hg⟩ : ↥Ŝ) * w *
      (⟨⟨g, hg.1⟩, Subgroup.mem_subgroupOf.mpr hg⟩ : ↥Ŝ)⁻¹, hW_norm _ w hw, ?_⟩
    simp [map_mul, map_inv]
  have hWg_norm : K ⊓ (S.L1 ⊔ T) ≤ Subgroup.normalizer (Wg : Set G) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hconj s hs x hx
    · intro hx
      have h := hconj s⁻¹ (inv_mem hs) _ hx
      have e : s⁻¹ * (s * x * s⁻¹) * s⁻¹⁻¹ = x := by group
      rwa [e] at h
  have hWg_pgroup : ∀ y ∈ Wg, ∃ k : ℕ, y ^ 2 ^ k = 1 := by
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨k, hk⟩ := hW_pgroup w hw
    exact ⟨k, by rw [← map_pow, hk, map_one]⟩
  have hWg_core : Wg ≤ pCoreOf 2 (K ⊓ (S.L1 ⊔ T)) :=
    le_pCoreOf_of_two hWg_le hWg_norm hWg_pgroup
  have hMN : S.L1 ⊔ T ≤ Subgroup.normalizer ((pCoreOf 2 (K ⊓ (S.L1 ⊔ T)) : Subgroup G) : Set G) := by
    refine le_trans ?_ (normalizer_le_normalizer_pCoreOf 2 (K ⊓ (S.L1 ⊔ T)))
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have key : ∀ g ∈ S.L1 ⊔ T, ∀ y ∈ K ⊓ (S.L1 ⊔ T), g * y * g⁻¹ ∈ K ⊓ (S.L1 ⊔ T) := by
      intro g hg y hy
      exact ⟨(Subgroup.mem_normalizer_iff.mp (hMK hg) y).mp hy.1,
        (S.L1 ⊔ T).mul_mem ((S.L1 ⊔ T).mul_mem hg hy.2) ((S.L1 ⊔ T).inv_mem hg)⟩
    constructor
    · intro hx
      exact key m hm x hx
    · intro hx
      have h := key m⁻¹ ((S.L1 ⊔ T).inv_mem hm) _ hx
      have e : m⁻¹ * (m * x * m⁻¹) * m⁻¹⁻¹ = x := by group
      rwa [e] at h
  have hS₀core : pCoreOf 2 (K ⊓ (S.L1 ⊔ T)) ≤ pCoreOf 2 (S.L1 ⊔ T) :=
    le_pCoreOf_of_two ((pCoreOf_le 2 _).trans hS₀M)
      hMN (fun y hy => two_pow_of_mem_pCoreOf hy)
  have hE0 : ∀ e ∈ L32HatM.E₀, ∃ k : ↥K, (k : G) ∈ pCoreOf 2 (S.L1 ⊔ T) ∧ π k = e := by
    intro e he
    obtain ⟨s, hs⟩ := hψ e (E0_le_X1 he)
    have hsW : s ∈ W := by
      rw [hW_mem, hs]
      exact he
    refine ⟨Ŝ.subtype s, ?_, hs⟩
    have h1 : ((Ŝ.subtype s : ↥K) : G) ∈ Wg := ⟨s, hsW, rfl⟩
    exact hS₀core (hWg_core h1)
  have hY : ((l0 L).subgroupOf K).map π = oTwoUpper SX1 := by
    have hYX : ((l0 L).subgroupOf K).map π ≤ SX1 := by
      rw [← hX]
      refine Subgroup.map_mono ?_
      intro x hx
      have hxl : (x : G) ∈ l0 L := Subgroup.mem_subgroupOf.mp hx
      exact Subgroup.mem_subgroupOf.mpr ⟨hL0K hxl, hL0M hxl⟩
    have hP : SL3.P0 ≤ Subgroup.normalizer (((l0 L).subgroupOf K).map π : Set SL3.S) :=
      L32HatStep.P0_le_normalizer_image hD hL0K
        (fun t ht z hz => (Subgroup.mem_normalizer_iff.mp (hTl0 ht) z).mp hz)
    have hO : ((l0 L).subgroupOf K).map π ≤ oTwoUpper (((l0 L).subgroupOf K).map π) :=
      L32HatStep.image_le_oTwoUpper hL0K (le_of_eq (S.oTwoUpper_l0).symm)
    have hY0 : ((l0 L).subgroupOf K).map π ≠ ⊥ := by
      intro hbot
      have hmem : π ⟨c, hcK⟩ ∈ ((l0 L).subgroupOf K).map π :=
        Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hcL0)
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hcO' ((hker ⟨c, hcK⟩).mp hmem)
    exact L32HatSL3.fA4_X1 hYX hP hO hY0
  refine ⟨π, hπ, hker, hE0, ?_⟩
  intro a ha
  have ha' : a ∈ oTwoUpper SX1 := A0_le_oTwoUpper_X1 ha
  rw [← hY] at ha'
  obtain ⟨k, hk, hka⟩ := Subgroup.mem_map.mp ha'
  exact ⟨k, Subgroup.mem_subgroupOf.mp hk, hka⟩

end L32HatC3

end CFSG.Quasithin.H13.A6
