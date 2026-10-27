module

public import CFSG.Quasithin.Vol2.Ch12Sec7GzSMLine

public section

namespace CFSG.Quasithin.H13.I1277

open CFSG.Open CFSG.Quasithin S127 S127.I77
open scoped IsMulCommutative

section Abstract

variable {G : Type} [Group G]

theorem zpow_cases {y : G} (hy3 : y ^ 3 = 1) (k : ℤ) : y ^ k = 1 ∨ y ^ k = y ∨ y ^ k = y ^ 2 := by
  have hk : y ^ k = y ^ (k % 3) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 3]
    rw [zpow_add, zpow_mul]
    have : y ^ (3 : ℤ) = 1 := by exact_mod_cast hy3
    rw [this, one_zpow, mul_one]
  rw [hk]
  have h3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases h3 with h | h | h <;> rw [h]
  · left; simp
  · right; left; simp
  · right; right; simp

theorem mem_zpowers_cases {y : G} (hy3 : y ^ 3 = 1) {g : G} :
    g ∈ Subgroup.zpowers y ↔ g = 1 ∨ g = y ∨ g = y ^ 2 := by
  constructor
  · intro h
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp h
    exact zpow_cases hy3 k
  · rintro (rfl | rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _
    · exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 2


theorem split_of_fpf [Finite G] {V X M : Subgroup G} [IsMulCommutative ↥V] {y : G}
    (hV2 : ∀ v ∈ V, v ^ 2 = 1)
    (hVM : V ≤ M) (hMV : M ≤ Subgroup.normalizer (V : Set G))
    (hXM : X ≤ M) (hMX : M ≤ Subgroup.normalizer (X : Set G))
    (hyX : y ∈ X) (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1)
    (hXV : ∀ x ∈ X, ∃ v ∈ V, ∃ j : ℤ, x = v * y ^ j)
    (hfpf : ∀ w ∈ V, y * w * y⁻¹ = w → w = 1) :
    ∃ M₀ : Subgroup G, M₀ ≤ M ∧ V ⊓ M₀ = ⊥ ∧ ∀ m ∈ M, ∃ v ∈ V, ∃ h ∈ M₀, m = v * h := by
  classical
  set P : Subgroup G := Subgroup.zpowers y with hP
  have hyM : y ∈ M := hXM hyX
  have hyNV : y ∈ Subgroup.normalizer (V : Set G) := hMV hyM
  have hVcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (IsMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hV3 : ∀ g ∈ V, g ^ 3 = 1 → g = 1 := by
    intro g hg hg3
    have h2 := hV2 g hg
    calc g = g ^ 3 * (g ^ 2)⁻¹ := by group
      _ = 1 := by rw [hg3, h2]; simp
  have hVP : ∀ g ∈ V, g ∈ P → g = 1 := by
    intro g hgV hgP
    rcases (mem_zpowers_cases hy3).mp hgP with h | h | h
    · exact h
    · exact hV3 g hgV (h ▸ hy3)
    · exact hV3 g hgV (by rw [h]; calc (y ^ 2) ^ 3 = (y ^ 3) ^ 2 := by group
                                  _ = 1 := by rw [hy3]; simp)
  have hφ : ∀ u ∈ V, ∃ v ∈ V, v * (y * v * y⁻¹)⁻¹ = u := by
    intro u hu
    let a : MulAut ↥V := conjAct V ⟨y, hyNV⟩
    let φ : ↥V →* ↥V := MonoidHom.id ↥V / (a : ↥V →* ↥V)
    have hφv : ∀ v : ↥V, ((φ v : ↥V) : G) = (v : G) * (y * v * y⁻¹)⁻¹ := by
      intro v
      show (((v / a v : ↥V)) : G) = _
      rw [div_eq_mul_inv]
      rfl
    have hinj : Function.Injective φ := by
      rw [injective_iff_map_eq_one]
      intro v hv
      have h1 : (v : G) * (y * v * y⁻¹)⁻¹ = 1 := by rw [← hφv, hv]; rfl
      have h2 : y * (v : G) * y⁻¹ = v := by
        have := mul_inv_eq_one.mp h1
        exact this.symm
      exact Subtype.ext (hfpf v v.2 h2)
    obtain ⟨v, hv⟩ := (Finite.injective_iff_surjective.mp hinj) ⟨u, hu⟩
    exact ⟨v, v.2, by rw [← hφv, hv]⟩
  refine ⟨Subgroup.normalizer (P : Set G) ⊓ M, inf_le_right, ?_, ?_⟩
  ·
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨hvV, hvN, -⟩ : v ∈ V ∧ v ∈ Subgroup.normalizer (P : Set G) ∧ v ∈ M :=
      ⟨(Subgroup.mem_inf.mp hv).1, (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hv).2).1,
        (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hv).2).2⟩
    have hvy : v * y * v⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.mp hvN y).mp (Subgroup.mem_zpowers y)
    have hc : v * (y * v⁻¹ * y⁻¹) ∈ V :=
      V.mul_mem hvV ((Subgroup.mem_normalizer_iff.mp hyNV v⁻¹).mp (V.inv_mem hvV))
    have hcP : v * (y * v⁻¹ * y⁻¹) ∈ P := by
      have e : v * (y * v⁻¹ * y⁻¹) = (v * y * v⁻¹) * y⁻¹ := by group
      rw [e]
      exact P.mul_mem hvy (P.inv_mem (Subgroup.mem_zpowers y))
    have h1 : v * (y * v⁻¹ * y⁻¹) = 1 := hVP _ hc hcP
    have h2 : y * v * y⁻¹ = v := by
      have e1 : v * y * v⁻¹ * y⁻¹ = 1 := by rw [← h1]; group
      have e3 : v * y * v⁻¹ = y := mul_inv_eq_one.mp e1
      have e2 : v * y = y * v := by
        calc v * y = (v * y * v⁻¹) * v := by group
          _ = y * v := by rw [e3]
      calc y * v * y⁻¹ = (v * y) * y⁻¹ := by rw [e2]
        _ = v := by group
    have hv1 : v = 1 := hfpf v hvV h2
    exact Subgroup.mem_bot.mpr hv1
  ·
    intro m hm
    have hy' : m * y * m⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (hMX hm) y).mp hyX
    obtain ⟨v₀, hv₀, j, hj⟩ := hXV _ hy'
    have hy'3 : (m * y * m⁻¹) ^ 3 = 1 := by
      calc (m * y * m⁻¹) ^ 3 = m * y ^ 3 * m⁻¹ := conj_pow
        _ = 1 := by rw [hy3]; simp
    have hy'V : m * y * m⁻¹ ∉ V := by
      intro h
      have := hV3 _ h hy'3
      apply hy1
      calc y = m⁻¹ * (m * y * m⁻¹) * m := by group
        _ = 1 := by rw [this]; simp
    have hyj : y ^ j = 1 ∨ y ^ j = y ∨ y ^ j = y ^ 2 := zpow_cases hy3 j
    obtain ⟨v, hv, y₁, hy₁, hconj⟩ : ∃ v ∈ V, ∃ y₁ : G,
        (m * y * m⁻¹ = y₁ ∨ m * y * m⁻¹ = y₁ ^ 2) ∧ v * y * v⁻¹ = y₁ := by
      rcases hyj with h | h | h
      · exfalso
        apply hy'V
        rw [hj, h, mul_one]
        exact hv₀
      · obtain ⟨v, hv, hφv⟩ := hφ v₀ hv₀
        refine ⟨v, hv, m * y * m⁻¹, Or.inl rfl, ?_⟩
        rw [hj, h]
        calc v * y * v⁻¹ = (v * (y * v * y⁻¹)⁻¹) * y := by group
          _ = v₀ * y := by rw [hφv]
      · set v₁ : G := v₀ * (y ^ 2 * v₀ * (y ^ 2)⁻¹) with hv₁
        have hv₁V : v₁ ∈ V :=
          V.mul_mem hv₀ ((Subgroup.mem_normalizer_iff.mp (hMV (M.pow_mem hyM 2)) v₀).mp hv₀)
        obtain ⟨v, hv, hφv⟩ := hφ v₁ hv₁V
        have e : (m * y * m⁻¹) ^ 2 = v₁ * y := by
          rw [hj, h]
          calc (v₀ * y ^ 2) ^ 2 = (v₀ * (y ^ 2 * v₀ * (y ^ 2)⁻¹)) * (y ^ 2 * y ^ 2) := by
                rw [pow_two (v₀ * y ^ 2)]; group
            _ = v₁ * y := by
                rw [hv₁]
                congr 1
                calc y ^ 2 * y ^ 2 = y ^ 3 * y := by group
                  _ = y := by rw [hy3, one_mul]
        refine ⟨v, hv, (m * y * m⁻¹) ^ 2, Or.inr ?_, ?_⟩
        · calc m * y * m⁻¹ = (m * y * m⁻¹) ^ 3 * (m * y * m⁻¹) := by rw [hy'3, one_mul]
            _ = ((m * y * m⁻¹) ^ 2) ^ 2 := by rw [← pow_succ, ← pow_mul]
        · rw [e]
          calc v * y * v⁻¹ = (v * (y * v * y⁻¹)⁻¹) * y := by group
            _ = v₁ * y := by rw [hφv]
    have hconj' : v⁻¹ * y₁ * v = y := by
      rw [← hconj]; group
    have hhy : (v⁻¹ * m) * y * (v⁻¹ * m)⁻¹ ∈ P := by
      have e : (v⁻¹ * m) * y * (v⁻¹ * m)⁻¹ = v⁻¹ * (m * y * m⁻¹) * v := by group
      rw [e]
      rcases hy₁ with h | h
      · rw [h, hconj']
        exact Subgroup.mem_zpowers y
      · rw [h]
        have : v⁻¹ * y₁ ^ 2 * v = (v⁻¹ * y₁ * v) ^ 2 := by simp only [pow_two]; group
        rw [this, hconj']
        exact Subgroup.pow_mem _ (Subgroup.mem_zpowers y) 2
    have hhN : v⁻¹ * m ∈ Subgroup.normalizer (P : Set G) := by
      refine Subgroup.mem_normalizer_fintype fun g hg => ?_
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      have e : (v⁻¹ * m) * y ^ k * (v⁻¹ * m)⁻¹ = ((v⁻¹ * m) * y * (v⁻¹ * m)⁻¹) ^ k := by
        rw [conj_zpow]
      rw [e]
      exact Subgroup.zpow_mem _ hhy k
    refine ⟨v, hv, v⁻¹ * m, Subgroup.mem_inf.mpr ⟨hhN, M.mul_mem (M.inv_mem (hVM hv)) hm⟩, ?_⟩
    group

end Abstract

section Setting

variable {G : Type} [Group G] [Finite G]

theorem exists_complement_1277
    (h71 : Setup1271) (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h1226 : Stmt12_2_6)
    {T L V : Subgroup G} {t : G} (s : Set77 G T L V t) :
    ∃ M₀ : Subgroup G, M₀ ≤ Subgroup.normalizer (L : Set G) ∧ V ⊓ M₀ = ⊥ ∧
      ∀ m ∈ Subgroup.normalizer (L : Set G), ∃ v ∈ V, ∃ h ∈ M₀, m = v * h := by
  classical
  have hyp := s.d.hyp
  haveI : IsMulCommutative ↥V := ⟨⟨fun a b => Subtype.ext (s.d.comm a a.2 b b.2)⟩⟩
  have hNLV : Subgroup.normalizer (L : Set G) = Subgroup.normalizer (V : Set G) :=
    mEqNormV1277_of h331 h1222 h1226 G T L V t s
  have hCV : Subgroup.centralizer (V : Set G) = V := s.centralizer_V_eq h1222 h1226 h331
  obtain ⟨-, -, -, hX3, -, hfpf⟩ := h71 G T L V hyp
  have hVL : V ≤ L := s.d.v_le_lt.trans (Set77.lt_le_L (L := L) (t := t))
  have hVM : V ≤ Subgroup.normalizer (L : Set G) := hVL.trans Subgroup.le_normalizer
  have hMV : Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (V : Set G) := hNLV.le
  have hXL : XOf L ≤ L := XOf_le L
  have hXM : XOf L ≤ Subgroup.normalizer (L : Set G) := hXL.trans Subgroup.le_normalizer
  have hXN : XOf L ≤ Subgroup.normalizer (V : Set G) := hXM.trans hMV
  have hV2 : ∀ v ∈ V, v ^ 2 = 1 := fun v hv => S127.sq_eq_one_of_mem hyp.hyp hv
  have h3X : 3 ∣ Nat.card ↥(XOf L) := by
    have h1 : Nat.card ↥(autOn (XOf L) V) ∣
        Nat.card ↥((XOf L).subgroupOf (Subgroup.normalizer (V : Set G))) :=
      Subgroup.card_map_dvd ((XOf L).subgroupOf (Subgroup.normalizer (V : Set G))) (conjAct V)
    rw [hX3, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXN).toEquiv] at h1
    exact h1
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 3 h3X
  have hyo : orderOf (y : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hy
  have hy3 : (y : G) ^ 3 = 1 := by rw [← hyo]; exact pow_orderOf_eq_one _
  have hy1 : (y : G) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hyo
    omega
  have hyX : (y : G) ∈ XOf L := y.2
  have hyNV : (y : G) ∈ Subgroup.normalizer (V : Set G) := hXN hyX
  have hyV : (y : G) ∉ V := by
    intro h
    apply hy1
    have h2 := hV2 _ h
    calc (y : G) = (y : G) ^ 3 * ((y : G) ^ 2)⁻¹ := by group
      _ = 1 := by rw [hy3, h2]; simp
  have hyC : (y : G) ∉ Subgroup.centralizer (V : Set G) := by rw [hCV]; exact hyV
  have hXV : ∀ x ∈ XOf L, ∃ v ∈ V, ∃ j : ℤ, x = v * (y : G) ^ j := by
    intro x hx
    have hxN : x ∈ Subgroup.normalizer (V : Set G) := hXN hx
    set A := autOn (XOf L) V with hA
    have hAmem : ∀ {g : G} (hg : g ∈ Subgroup.normalizer (V : Set G)), g ∈ XOf L →
        conjAct V ⟨g, hg⟩ ∈ A := fun hg hgX =>
      (AutOn.mem_autOn_iff_exists).2 ⟨_, hg, hgX, rfl⟩
    let ay : ↥A := ⟨conjAct V ⟨y, hyNV⟩, hAmem hyNV hyX⟩
    let ax : ↥A := ⟨conjAct V ⟨x, hxN⟩, hAmem hxN hx⟩
    have hay1 : ay ≠ 1 := by
      intro h
      have h' : conjAct V ⟨y, hyNV⟩ = 1 := congrArg Subtype.val h
      exact conjAct_ne_one hyNV hyV hCV h'
    have hA3 : Nat.card ↥A = 3 := hX3
    have hax : ax ∈ Subgroup.zpowers ay := by
      rw [zpowers_eq_top_of_prime_card hA3 hay1]
      exact Subgroup.mem_top _
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hax
    have hk' : (conjAct V ⟨y, hyNV⟩) ^ k = conjAct V ⟨x, hxN⟩ := congrArg Subtype.val hk
    set w : G := x * (y : G) ^ (-k) with hw
    have hwN : w ∈ Subgroup.normalizer (V : Set G) :=
      Subgroup.mul_mem _ hxN (Subgroup.zpow_mem _ hyNV _)
    have hw1 : conjAct V ⟨w, hwN⟩ = 1 := by
      have e : (⟨w, hwN⟩ : Subgroup.normalizer (V : Set G)) =
          ⟨x, hxN⟩ * (⟨y, hyNV⟩ : Subgroup.normalizer (V : Set G)) ^ (-k) := rfl
      rw [e, map_mul, map_zpow, zpow_neg, hk', mul_inv_cancel]
    have hwV : w ∈ V := by
      rw [← hCV]
      exact A4.conjAct_eq_one_iff.1 hw1
    refine ⟨w, hwV, k, ?_⟩
    rw [hw]
    group
  have hfpf' : ∀ w ∈ V, (y : G) * w * (y : G)⁻¹ = w → w = 1 := by
    intro w hw hyw
    have hmem : w ∈ V ⊓ Subgroup.centralizer ({(y : G)} : Set G) :=
      Subgroup.mem_inf.mpr ⟨hw, Subgroup.mem_centralizer_singleton_iff.mpr (by
        calc w * (y : G) = ((y : G) * w * (y : G)⁻¹) * (y : G) := by rw [hyw]
          _ = (y : G) * w := by group)⟩
    rw [hfpf (y : G) hyX hyC, Subgroup.mem_bot] at hmem
    exact hmem
  exact split_of_fpf hV2 hVM hMV hXM (S127.L5.normalizer_le_normalizer_XOf L) hyX hy3 hy1 hXV hfpf'

end Setting

end CFSG.Quasithin.H13.I1277

end
