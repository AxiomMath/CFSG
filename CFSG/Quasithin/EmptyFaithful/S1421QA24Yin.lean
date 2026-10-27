module

public import CFSG.Quasithin.EmptyFaithful.S1421QA24Bender
public import CFSG.Quasithin.EmptyFaithful.S1421QA24Borel

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace QA24

variable {G : Type} [Group G] [Finite G] {T M L : Subgroup G}

theorem centralizes_VZ_of_fixes (h : Hyp1281Two G T M L) {x u : G}
    (hxN : x ∈ Subgroup.normalizer (VZ T M : Set G)) (hodd : Odd (orderOf x))
    (hu : u ∈ VZ T M) (hu1 : u ≠ 1) (hfix : x * u * x⁻¹ = u) :
    x ∈ Subgroup.centralizer (VZ T M : Set G) := by
  obtain ⟨hVred, -⟩ := h.isTwoReducedIn
  have hsq : ∀ w : VZ T M, w * w = 1 := fun w =>
    Subtype.ext (by simpa [sq] using hVred.2.2.1.2 w w.2)
  set σ : MulAut (VZ T M) := conjAct (VZ T M) ⟨x, hxN⟩ with hσ
  have hσapp : ∀ y : VZ T M, ((σ y : VZ T M) : G) = x * y * x⁻¹ := fun y =>
    Subgroup.normalizerMonoidHom_apply_apply_coe (VZ T M)
      (Subgroup.inclusion le_rfl ⟨x, hxN⟩) y
  have hσu : σ ⟨u, hu⟩ = ⟨u, hu⟩ := Subtype.ext (by rw [hσapp]; exact hfix)
  have hσm : σ ^ orderOf x = 1 := by
    rw [hσ, ← map_pow]
    have : (⟨x, hxN⟩ : Subgroup.normalizer (VZ T M : Set G)) ^ orderOf x = 1 :=
      Subtype.ext (by simp only [Subgroup.coe_pow, Subgroup.coe_one]; exact pow_orderOf_eq_one x)
    rw [this, map_one]
  have hσ1 := mulAut_eq_one_of_fix_of_odd h.rank_two hsq (z := ⟨u, hu⟩)
    (fun h1 => hu1 (show u = 1 from congrArg (fun y : VZ T M => (y : G)) h1)) hσu hodd hσm
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have := congrArg (fun φ : MulAut (VZ T M) => ((φ ⟨y, hy⟩ : VZ T M) : G)) hσ1
  simp only [hσapp, MulAut.one_apply] at this
  calc y * x = (x * y * x⁻¹) * x := by rw [this]
    _ = x * y := by group

section Context

variable {H K1 M₁ : Subgroup G}

theorem false_of_four_cube_roots {P : Type*} [Group P] [Finite P] [IsCyclic P] {a b : P}
    (hb1 : b ≠ 1) (hb3 : b ^ 3 = 1) (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1) (hab : a ≠ b)
    (hab2 : a ≠ b ^ 2) : False := by
  classical
  have : Fintype P := Fintype.ofFinite P
  have hle := IsCyclic.card_pow_eq_one_le (α := P) (n := 3) (by norm_num)
  have hb2 : b ^ 2 ≠ 1 := by
    intro h
    apply hb1
    calc b = b ^ 3 * (b ^ 2)⁻¹ := by group
      _ = 1 := by rw [hb3, h]; simp
  have hbb2 : b ≠ b ^ 2 := by
    intro h
    apply hb1
    calc b = b ^ 2 * b⁻¹ := by group
      _ = 1 := by rw [← h]; simp
  have hsub : ({1, b, b ^ 2, a} : Finset P) ⊆ Finset.univ.filter (fun x : P => x ^ 3 = 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl | rfl | rfl
    · simp
    · exact hb3
    · rw [← pow_mul, show 2 * 3 = 3 * 2 by rfl, pow_mul, hb3, one_pow]
    · exact ha3
  have hcard : ({1, b, b ^ 2, a} : Finset P).card = 4 := by
    have h1 : (1 : P) ∉ ({b, b ^ 2, a} : Finset P) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hb1 h.symm, fun h => hb2 h.symm, fun h => ha1 h.symm⟩
    have h2 : b ∉ ({b ^ 2, a} : Finset P) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hbb2, fun h => hab h.symm⟩
    have h3 : b ^ 2 ∉ ({a} : Finset P) := by
      simp only [Finset.mem_singleton]
      exact fun h => hab2 h.symm
    rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
      Finset.card_insert_of_notMem h3, Finset.card_singleton]
  have := Finset.card_le_card hsub
  omega

omit [Finite G] in
theorem inv_mul_mul_mem_of_smul_eq {K : Type*} [Group K] {p : ℕ} [Fact p.Prime] {P₁ P₂ : Sylow p K}
    {g : K} (hg : g • P₁ = P₂) {x : K} (hx : x ∈ (P₂ : Subgroup K)) :
    g⁻¹ * x * g ∈ (P₁ : Subgroup K) := by
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx
  simpa [MulAut.smul_def] using hx

theorem false_of_y_le (hSL2 : A312SL2Fact) (h36 : A36ForSQTK)
    (h37 : A37ForSQTK) (c : S1421.Core3Ctx T M H K1 L M₁)
    (hnq : ¬ CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) (hY : yOfL22 T M ≤ L) : False := by
  have h1281 := lemma_14_2_4 c.st.hyp c.st.facts
  have hL2 := isL2Quot_two hSL2 h36 h37 c hnq
  have hr1 := pRank_three_le_one_L hSL2 h36 h37 c hnq
  obtain ⟨y₁, ⟨hy₁K, hy₁N⟩, hy₁3⟩ :=
    exists_threeElement_normalizer_of_isL2Quot_two c.st.notation_.sylow hL2
  have hy₁M : y₁ ∈ M := c.st.notation_.borel_le ⟨hy₁K, hy₁N⟩
  have hy₁L : y₁ ∈ L := c.lt_L.le hy₁K
  have hy₁NY : y₁ ∈ Subgroup.normalizer (yOfL22 T M : Set G) := le_normalizer_yOfL22 T M hy₁M
  have hMV : M ≤ Subgroup.normalizer (VZ T M : Set G) := le_normalizer_conjClosure _ _
  obtain ⟨z, hzZ⟩ : ∃ z : quasithinOmegaOneCenter T, z ≠ 1 := by
    by_contra hall
    push Not at hall
    exact h1281.omegaOneCenter_ne_bot (by
      rw [eq_bot_iff]
      intro w hw
      have := hall ⟨w, hw⟩
      rw [Subgroup.mem_bot]
      exact congrArg Subtype.val this)
  have hz1 : (z : G) ≠ 1 := fun he => hzZ (Subtype.ext he)
  have hzV : (z : G) ∈ VZ T M := le_conjClosure _ _ z.2
  have hy₁z : y₁ * z * y₁⁻¹ = z := by
    have := Subgroup.mem_centralizer_iff.mp (S1421.K1_le_mcOf c.st hy₁K) z z.2
    calc y₁ * z * y₁⁻¹ = (z * y₁) * y₁⁻¹ := by rw [this]
      _ = z := by group
  have hodd : Odd (orderOf y₁) := by rw [hy₁3]; decide
  have hy₁C := centralizes_VZ_of_fixes h1281 (hMV hy₁M) hodd hzV hz1 hy₁z
  have hy₁Y : y₁ ∉ yOfL22 T M := by
    intro hy
    have hmem : y₁ ∈ pCoreOf 2 (yOfL22 T M) := by
      rw [c.st.facts.y_oTwo]
      exact ⟨hy, hy₁C⟩
    obtain ⟨j, hj⟩ := exists_pow_two_pow_eq_one_of_mem (pCoreOf_isPGroup 2 (yOfL22 T M)) hmem
    have h3 : 3 ∣ 2 ^ j := by rw [← hy₁3]; exact orderOf_dvd_of_pow_eq_one hj
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  set Y : Subgroup G := yOfL22 T M with hYdef
  have hYN : Y ≤ Subgroup.normalizer (VZ T M : Set G) := (yOfL22_le T M).trans hMV
  have hY3 : 3 ∣ Nat.card ↥Y := by
    have h1 := Subgroup.card_map_dvd (Y.subgroupOf (Subgroup.normalizer (VZ T M : Set G)))
      (conjAct (VZ T M))
    have h2 : Nat.card ↥(autOn Y (VZ T M)) = 3 := c.st.facts.y_card
    have h3 : Nat.card ↥(Y.subgroupOf (Subgroup.normalizer (VZ T M : Set G))) = Nat.card ↥Y :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYN).toEquiv
    rw [h3] at h1
    unfold autOn at h2
    rwa [h2] at h1
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨w, hw3⟩ := exists_prime_orderOf_dvd_card' (G := ↥Y) 3 hY3
  set H' : Subgroup G := Y ⊔ Subgroup.zpowers y₁ with hH'
  have hHL : H' ≤ L := sup_le hY (Subgroup.zpowers_le.mpr hy₁L)
  have hHN : H' ≤ Subgroup.normalizer (Y : Set G) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hy₁NY)
  have hy₁H : y₁ ∈ H' := Subgroup.mem_sup_right (Subgroup.mem_zpowers y₁)
  have hwH : (w : G) ∈ H' := Subgroup.mem_sup_left w.2
  let a : ↥H' := ⟨y₁, hy₁H⟩
  let b : ↥H' := ⟨(w : G), hwH⟩
  have ha3 : orderOf a = 3 := (Subgroup.orderOf_coe a).symm.trans hy₁3
  have hb3 : orderOf b = 3 :=
    ((Subgroup.orderOf_coe b).symm.trans (Subgroup.orderOf_coe w)).trans hw3
  have hpa : IsPGroup 3 (Subgroup.zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha3]; norm_num)
  have hpb : IsPGroup 3 (Subgroup.zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb3]; norm_num)
  obtain ⟨P₁, hP₁⟩ := hpa.exists_le_sylow
  obtain ⟨P₂, hP₂⟩ := hpb.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥H' P₁ P₂
  have hbP₂ : b ∈ (P₂ : Subgroup ↥H') := hP₂ (Subgroup.mem_zpowers b)
  have hbP₁ : g⁻¹ * b * g ∈ (P₁ : Subgroup ↥H') := inv_mul_mul_mem_of_smul_eq hg hbP₂
  have haP₁ : a ∈ (P₁ : Subgroup ↥H') := hP₁ (Subgroup.mem_zpowers a)
  set P : Subgroup G := (P₁ : Subgroup ↥H').map H'.subtype with hP
  have hPp : IsPGroup 3 P := IsPGroup.map (H := (P₁ : Subgroup ↥H')) P₁.isPGroup' H'.subtype
  have hPL : P ≤ L := by
    rintro _ ⟨x, -, rfl⟩
    exact hHL x.2
  have hcyc : IsCyclic ↥P :=
    CFSG.RankThree.PartOne.isCyclic_of_pRank_le_one Nat.prime_three (by norm_num) hPL hPp hr1
  let b' : ↥H' := g⁻¹ * b * g
  have hb'Y : (b' : G) ∈ Y := by
    have := (Subgroup.mem_normalizer_iff.mp (hHN (g⁻¹ : ↥H').2) (w : G)).mp w.2
    simpa [b', b, mul_assoc] using this
  have hb'3 : orderOf b' = 3 := by
    rw [← hb3]
    have := (MulAut.conj g⁻¹).orderOf_eq b
    rw [MulAut.conj_apply, inv_inv] at this
    exact this
  let a₀ : ↥P := ⟨y₁, Subgroup.mem_map.mpr ⟨a, haP₁, rfl⟩⟩
  let b₀ : ↥P := ⟨(b' : G), Subgroup.mem_map.mpr ⟨b', hbP₁, rfl⟩⟩
  have hb'1 : (b' : G) ≠ 1 := by
    intro h
    have : b' = 1 := Subtype.ext h
    rw [this, orderOf_one] at hb'3
    omega
  have hb'cube : (b' : G) ^ 3 = 1 := by
    have : b' ^ 3 = 1 := by rw [← hb'3]; exact pow_orderOf_eq_one b'
    simpa using congrArg Subtype.val this
  have hy₁cube : y₁ ^ 3 = 1 := by rw [← hy₁3]; exact pow_orderOf_eq_one y₁
  have hy₁1 : y₁ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hy₁3
    omega
  refine false_of_four_cube_roots (P := ↥P) (a := a₀) (b := b₀) ?_ ?_ ?_ ?_ ?_ ?_
  · intro h
    exact hb'1 (congrArg (fun x : ↥P => (x : G)) h)
  · exact Subtype.ext (by simpa [b₀] using hb'cube)
  · exact Subtype.ext (by simpa [a₀] using hy₁cube)
  · intro h
    exact hy₁1 (congrArg (fun x : ↥P => (x : G)) h)
  · intro h
    apply hy₁Y
    have := congrArg (fun x : ↥P => (x : G)) h
    simp only [a₀, b₀] at this
    rw [this]
    exact hb'Y
  · intro h
    apply hy₁Y
    have := congrArg (fun x : ↥P => (x : G)) h
    simp only [a₀, b₀, Subgroup.coe_pow] at this
    rw [this]
    exact Y.pow_mem hb'Y 2

end Context
