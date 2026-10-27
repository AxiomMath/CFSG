module

public import CFSG.LocalAnalysis.SteinbergSFRootAxisNormalizerTwoCore

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace OneAxisRadical

open Subgroup GomiFusion RootAxisTwoCore
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis

section Model

variable {K : Type} [Field K] [CharP K 2]

theorem rootU_le_center (i : Axis) : rootU K i ≤ antiUnipotentCenter K := by
  cases i
  · rintro _ ⟨b, rfl⟩
    exact ⟨b, 0, rfl⟩
  · rintro _ ⟨c, rfl⟩
    exact ⟨0, c, rfl⟩

theorem center_le_rootA (i : Axis) : antiUnipotentCenter K ≤ rootA K i := by
  cases i
  exacts [antiUnipotentCenter_le_radA1, antiUnipotentCenter_le_radA2]

theorem rootA_mul_self (i : Axis) {a : antiSp K} (ha : a ∈ rootA K i) : a * a = 1 := by
  cases i
  exacts [mul_self_of_mem_radA1 ha, mul_self_of_mem_radA2 ha]

theorem exists_conj_mem_antiUnipotentCenter [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n)
    (hn : 2 ≤ n) (i : Axis) {a : antiSp K} (ha : a ∈ rootA K i) :
    ∃ y ∈ rootC K i, y * a * y⁻¹ ∈ antiUnipotentCenter K := by
  have hst := even_symplectic_four_root_axis_centralizer_structure hK hn i
  obtain ⟨z₀, hz₀Z, hz₀U⟩ : ∃ z₀ ∈ antiUnipotentCenter K, z₀ ∉ rootU K i := by
    cases i
    · refine ⟨uElt 0 0 1 0, ⟨0, 1, rfl⟩, ?_⟩
      rintro ⟨b, hb⟩
      exact one_ne_zero (uElt_inj hb).2.2.1
    · refine ⟨uElt 0 1 0 0, ⟨1, 0, rfl⟩, ?_⟩
      rintro ⟨c, hc⟩
      exact one_ne_zero (uElt_inj hc).2.1
  have hz₀A := center_le_rootA i hz₀Z
  by_cases hv : vecOf K i a = 0
  · refine ⟨1, one_mem _, ?_⟩
    rw [one_mul, inv_one, mul_one]
    exact rootU_le_center i ((hst.vec_ker a ha).mp hv)
  · have hv₀ : vecOf K i z₀ ≠ 0 := fun h => hz₀U ((hst.vec_ker z₀ hz₀A).mp h)
    obtain ⟨M, hM⟩ := exists_sl2_mulVec_eq hv hv₀
    have hb : sHom K i M * a * (sHom K i M)⁻¹ ∈ rootA K i :=
      hst.A_normal_C _ (hst.s_mem_C M) a ha
    have h1 : vecOf K i (sHom K i M * a * (sHom K i M)⁻¹ * z₀) = 0 := by
      rw [hst.vec_add _ hb _ hz₀A, hst.vec_conj M a ha, hM]
      funext j
      exact CharTwo.add_self_eq_zero _
    have h2 := rootU_le_center i ((hst.vec_ker _ (mul_mem hb hz₀A)).mp h1)
    refine ⟨sHom K i M, hst.s_mem_C M, ?_⟩
    have e : sHom K i M * a * (sHom K i M)⁻¹ =
        sHom K i M * a * (sHom K i M)⁻¹ * z₀ * z₀⁻¹ := by group
    rw [e]
    exact mul_mem h2 (inv_mem hz₀Z)

theorem conj_uElt_of_mem_normalizer {h : antiSp K}
    (hh : h ∈ normalizer (radA2 K : Set (antiSp K))) (b : K) :
    ∃ a' b' : K, h * uElt 0 b 0 0 * h⁻¹ = uElt a' b' 0 0 := by
  obtain ⟨w, e, l, M, rfl⟩ := exists_normalForm (mem_normalizer_radA2_iff.mp hh)
  have h1 : uElt (0 : K) b 0 0 = aElt ![b, 0] 0 := by simp [aElt]
  rw [h1, conj_aElt_normalForm, mul_zero]
  exact ⟨_, _, rfl⟩

theorem exists_conj_uElt (a b : K) :
    ∃ h ∈ normalizer (radA2 K : Set (antiSp K)), ∃ b₀ : K,
      h * uElt 0 b₀ 0 0 * h⁻¹ = uElt a b 0 0 := by
  by_cases hv : (![b, a] : Fin 2 → K) = 0
  · have hb : b = 0 := congrFun hv 0
    have ha : a = 0 := congrFun hv 1
    exact ⟨1, one_mem _, 0, by rw [ha, hb]; group⟩
  · have h10 : (![1, 0] : Fin 2 → K) ≠ 0 := fun h => one_ne_zero (congrFun h 0)
    obtain ⟨M, hM⟩ := exists_sl2_mulVec_eq h10 hv
    refine ⟨sElt M, mem_normalizer_radA2_iff.mpr (firstCol_sElt M), 1, ?_⟩
    have h1 : uElt (0 : K) 1 0 0 = aElt ![1, 0] 0 := by simp [aElt]
    rw [h1, sElt_mul_aElt, mul_inv_cancel_right, hM]
    simp [aElt]

theorem rootA_le_antiUnipotent (i : Axis) : rootA K i ≤ antiUnipotent K := by
  cases i
  exacts [radA1_le_antiUnipotent, radA2_le_antiUnipotent]

theorem rootU_one_le_rootA_two : rootU K Axis.one ≤ rootA K Axis.two := by
  rintro _ ⟨b, rfl⟩
  exact ⟨0, b, 0, rfl⟩

theorem rootU_inf_eq_bot : rootU K Axis.one ⊓ rootU K Axis.two = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨⟨b, rfl⟩, ⟨c, h⟩⟩
  obtain ⟨-, hb, -, -⟩ := uElt_inj h
  rw [hb, uElt_zero_eq_one]
  exact one_mem _

end Model

section General

variable {G : Type*} [Group G]

theorem mul_conj_eq {t g a h : G} (hgt : g * t = t * g) (hah : t * a = h⁻¹ * t * h) :
    t * (g * a * g⁻¹) = (h * g⁻¹)⁻¹ * t * (h * g⁻¹) := by
  calc t * (g * a * g⁻¹) = (t * g) * a * g⁻¹ := by group
    _ = g * (t * a) * g⁻¹ := by rw [← hgt]; group
    _ = (h * g⁻¹)⁻¹ * t * (h * g⁻¹) := by rw [hah]; group

theorem card_mul_left_set (U : Subgroup G) (t : G) :
    Nat.card {x : G | ∃ u ∈ U, x = t * u} = Nat.card U := by
  have e : {x : G | ∃ u ∈ U, x = t * u} = (t * ·) '' (U : Set G) := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u, hu, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u, hu, rfl⟩
  rw [e, Nat.card_image_of_injective (mul_right_injective t)]
  rfl

variable {L : Subgroup G} {X : Type*} [Group X]

theorem symm_mem_normalizer_pull [Finite G] {φ : L ≃* X} {S : Subgroup X} {y : X}
    (hy : y ∈ normalizer (S : Set X)) : ((φ.symm y : L) : G) ∈ normalizer (pull φ S : Set G) := by
  refine mem_normalizer_of_conj_le fun x hx => ?_
  obtain ⟨x', hx', rfl⟩ := exists_eq_symm_of_mem_pull hx
  rw [symm_conj_eq]
  exact symm_mem_pull.mpr ((mem_normalizer_iff.mp hy x').mp hx')

theorem apply_mem_normalizer {φ : L ≃* X} {S : Subgroup X} {l : L}
    (hl : (l : G) ∈ normalizer (pull φ S : Set G)) : φ l ∈ normalizer (S : Set X) := by
  have h := (mem_normalizer_pull_iff φ S ⟨l, le_normalizer l.2⟩).mp hl
  rw [normAct_of_mem, mem_autStab] at h
  exact mem_normalizer_iff.mpr fun x => (h x).symm

end General

structure Hyp {G : Type} [Group G] (L : Subgroup G) (K : Type) [Field K] [CharP K 2] (n : ℕ)
    (φ : L ≃* antiSp K) (TG : Subgroup G) (t : G) : Prop where
  setup : Setup L K n φ TG t
  two : TwoCoreSetup L K n t
  T_eq : TG = zpowers t
  axis : {x : G | ∃ m ∈ normalizer ((pull φ (antiUnipotent K) ⊔ TG : Subgroup G) : Set G),
    x = m⁻¹ * t * m} = {x | ∃ u ∈ pull φ (rootU K Axis.one), x = t * u}

namespace Hyp

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2] {n : ℕ}
  {φ : L ≃* antiSp K} {TG : Subgroup G} {t : G}

theorem mem_U_of_conj [Finite G] [Finite K]
    (hH : Hyp L K n φ TG t) {z : G} (hz : z ∈ pull φ (antiUnipotentCenter K)) {h : G}
    (hzh : t * z = h⁻¹ * t * h) : z ∈ pull φ (rootU K Axis.one) := by
  have hZ : h⁻¹ * t * h ∈ (center ↥(pull φ (antiUnipotent K) ⊔ TG)).map
      (pull φ (antiUnipotent K) ⊔ TG).subtype := by
    have := hH.setup.mul_mem_ZQ hz hH.setup.t_mem
    rwa [hH.setup.comm_L_T (pull_le φ _ hz) hH.setup.t_mem, hzh] at this
  obtain ⟨m, hm, hhm⟩ := hH.setup.mem_conj_normalizer hZ
  have hmem : t * z ∈ {x : G | ∃ m ∈ normalizer ((pull φ (antiUnipotent K) ⊔ TG :
      Subgroup G) : Set G), x = m⁻¹ * t * m} := ⟨m, hm, hzh.trans hhm⟩
  rw [hH.axis] at hmem
  obtain ⟨u, hu, hzu⟩ := hmem
  rwa [mul_left_cancel hzu]

theorem mul_mem_of_conj (hH : Hyp L K n φ TG t) {A : Subgroup G} (hAL : A ≤ L) {x h : G}
    (hx : x = h⁻¹ * t * h) (hxB : x ∈ zpowers t ⊔ A) : t * x ∈ A := by
  subst hx
  rcases (mem_zpowers_sup_iff hH.two.t_mul_t fun w hw => hH.two.comm (hAL hw)).mp hxB with
    h1 | h1
  · exact absurd (hAL h1) (hH.two.not_conj h)
  · exact h1

theorem eq_mul_mul (hH : Hyp L K n φ TG t) (x : G) : x = t * (t * x) := by
  rw [← mul_assoc, hH.two.t_mul_t, one_mul]

theorem mem_U_one_of_mem_A_one [Finite G] [Finite K]
    (hH : Hyp L K n φ TG t) {a : G} (ha : a ∈ pull φ (rootA K Axis.one)) {h : G}
    (hah : t * a = h⁻¹ * t * h) : a ∈ pull φ (rootU K Axis.one) := by
  obtain ⟨a', ha', rfl⟩ := exists_eq_symm_of_mem_pull ha
  obtain ⟨y, hy, hyZ⟩ := exists_conj_mem_antiUnipotentCenter hH.two.card_K hH.two.two_le
    Axis.one ha'
  have hgt : ((φ.symm y : L) : G) * t = t * ((φ.symm y : L) : G) :=
    (hH.two.comm (φ.symm y).2).symm
  have h1 := hH.mem_U_of_conj (by rw [symm_conj_eq]; exact symm_mem_pull.mpr hyZ)
    (mul_conj_eq hgt hah)
  rw [symm_conj_eq] at h1
  have h2 := symm_mem_pull.mp h1
  have hc := mem_centralizer_iff.mp hy _ h2
  have e : y * a' = y * (y * a' * y⁻¹) := by rw [← hc]; group
  rwa [← mul_left_cancel e] at h1

theorem fus_one [Finite G] [Finite K] (hH : Hyp L K n φ TG t) :
    {x : G | (∃ g : G, x = g⁻¹ * t * g) ∧ x ∈ zpowers t ⊔ pull φ (rootA K Axis.one)} =
      {x | ∃ u ∈ pull φ (rootU K Axis.one), x = t * u} := by
  ext x
  constructor
  · rintro ⟨⟨h, hx⟩, hxB⟩
    have ha := hH.mul_mem_of_conj (pull_le φ _) hx hxB
    refine ⟨t * x, hH.mem_U_one_of_mem_A_one ha (h := h) ?_, hH.eq_mul_mul x⟩
    rw [← hH.eq_mul_mul]
    exact hx
  · rintro ⟨u, hu, rfl⟩
    have hmem : t * u ∈ {x | ∃ u ∈ pull φ (rootU K Axis.one), x = t * u} := ⟨u, hu, rfl⟩
    rw [← hH.axis] at hmem
    obtain ⟨m, -, hm⟩ := hmem
    exact ⟨⟨m, hm⟩, mul_mem (mem_sup_left (mem_zpowers t))
      (mem_sup_right (pull_mono φ rootU₁_le_radA1 hu))⟩

theorem fus_two_subset [Finite G] [Finite K]
    (hH : Hyp L K n φ TG t) {x h : G} (hx : x = h⁻¹ * t * h)
    (hxB : x ∈ zpowers t ⊔ pull φ (rootA K Axis.two)) :
    ∃ g ∈ L ⊓ normalizer (pull φ (rootA K Axis.two) : Set G), ∃ u ∈ pull φ (rootU K Axis.one),
      x = g⁻¹ * (t * u) * g := by
  have ha := hH.mul_mem_of_conj (pull_le φ _) hx hxB
  obtain ⟨a', ha', ha'x⟩ := exists_eq_symm_of_mem_pull ha
  obtain ⟨y, hy, hyZ⟩ := exists_conj_mem_antiUnipotentCenter hH.two.card_K hH.two.two_le
    Axis.two ha'
  have hgt : ((φ.symm y : L) : G) * t = t * ((φ.symm y : L) : G) :=
    (hH.two.comm (φ.symm y).2).symm
  have hah : t * (t * x) = h⁻¹ * t * h := by rw [← hH.eq_mul_mul]; exact hx
  have h1 := hH.mem_U_of_conj (z := ((φ.symm y : L) : G) * (t * x) * ((φ.symm y : L) : G)⁻¹)
    (by rw [← ha'x, symm_conj_eq]; exact symm_mem_pull.mpr hyZ) (mul_conj_eq hgt hah)
  have hst := even_symplectic_four_root_axis_centralizer_structure hH.two.card_K hH.two.two_le
    Axis.two
  have hyN : y ∈ normalizer (rootA K Axis.two : Set (antiSp K)) := by
    rw [← hst.N_eq]
    exact centralizer_le_normalizer _ hy
  refine ⟨_, ⟨(φ.symm y).2, symm_mem_normalizer_pull hyN⟩, _, h1, ?_⟩
  have e2 : ((φ.symm y : L) : G)⁻¹ * t * ((φ.symm y : L) : G) = t := by
    rw [mul_assoc, ← hgt, inv_mul_cancel_left]
  calc x = t * (t * x) := hH.eq_mul_mul x
    _ = (((φ.symm y : L) : G)⁻¹ * t * ((φ.symm y : L) : G)) * (t * x) := by rw [e2]
    _ = _ := by group

theorem union_subset (hH : Hyp L K n φ TG t) {g u : G}
    (hg : g ∈ L ⊓ normalizer (pull φ (rootA K Axis.two) : Set G))
    (hu : u ∈ pull φ (rootU K Axis.one)) :
    ∃ a b : K, g⁻¹ * (t * u) * g = t * ((φ.symm (uElt a b 0 0) : L) : G) := by
  obtain ⟨hgL, hgN⟩ := hg
  have hN := apply_mem_normalizer (l := ⟨g, hgL⟩) hgN
  obtain ⟨_, ⟨b, rfl⟩, rfl⟩ := exists_eq_symm_of_mem_pull hu
  obtain ⟨a', b', hab⟩ := conj_uElt_of_mem_normalizer (inv_mem hN) b
  refine ⟨a', b', ?_⟩
  have hg't : g⁻¹ * t = t * g⁻¹ := (hH.two.comm (inv_mem hgL)).symm
  have e1 : g⁻¹ * (t * ((φ.symm (uElt 0 b 0 0) : L) : G)) * g =
      t * ((φ.symm ((φ ⟨g, hgL⟩)⁻¹ * uElt 0 b 0 0 * ((φ ⟨g, hgL⟩)⁻¹)⁻¹) : L) : G) := by
    rw [← symm_conj_eq]
    simp only [map_inv, MulEquiv.symm_apply_apply, coe_inv, inv_inv]
    calc g⁻¹ * (t * ((φ.symm (uElt 0 b 0 0) : L) : G)) * g
        = (g⁻¹ * t) * ((φ.symm (uElt 0 b 0 0) : L) : G) * g := by group
      _ = _ := by rw [hg't]; group
  rw [e1, hab]

theorem subset_union [Finite G] (hH : Hyp L K n φ TG t) (a b : K) :
    ∃ g ∈ L ⊓ normalizer (pull φ (rootA K Axis.two) : Set G), ∃ u ∈ pull φ (rootU K Axis.one),
      t * ((φ.symm (uElt a b 0 0) : L) : G) = g⁻¹ * (t * u) * g := by
  obtain ⟨h, hh, b₀, hb₀⟩ := exists_conj_uElt a b
  have hkL : ((φ.symm h : L) : G) ∈ L := (φ.symm h).2
  have hkt : ((φ.symm h : L) : G) * t = t * ((φ.symm h : L) : G) := (hH.two.comm hkL).symm
  refine ⟨((φ.symm h : L) : G)⁻¹,
    mem_inf.mpr ⟨inv_mem hkL, inv_mem (symm_mem_normalizer_pull hh)⟩, _,
    symm_mem_pull.mpr ⟨b₀, rfl⟩, ?_⟩
  rw [inv_inv, ← hb₀, ← symm_conj_eq]
  calc t * (((φ.symm h : L) : G) * ((φ.symm (uElt 0 b₀ 0 0) : L) : G) * ((φ.symm h : L) : G)⁻¹)
      = (t * ((φ.symm h : L) : G)) * ((φ.symm (uElt 0 b₀ 0 0) : L) : G) *
          ((φ.symm h : L) : G)⁻¹ := by group
    _ = _ := by rw [← hkt]; group

theorem union_mem (hH : Hyp L K n φ TG t) {g u : G}
    (hg : g ∈ L ⊓ normalizer (pull φ (rootA K Axis.two) : Set G))
    (hu : u ∈ pull φ (rootU K Axis.one)) :
    g⁻¹ * (t * u) * g ∈
      {x : G | (∃ k : G, x = k⁻¹ * t * k) ∧ x ∈ zpowers t ⊔ pull φ (rootA K Axis.two)} := by
  obtain ⟨hgL, hgN⟩ := hg
  have hmem : t * u ∈ {x | ∃ u ∈ pull φ (rootU K Axis.one), x = t * u} := ⟨u, hu, rfl⟩
  rw [← hH.axis] at hmem
  obtain ⟨m, -, hm⟩ := hmem
  refine ⟨⟨m * g, by rw [hm]; group⟩, ?_⟩
  have hg't : g⁻¹ * t = t * g⁻¹ := (hH.two.comm (inv_mem hgL)).symm
  have e : g⁻¹ * (t * u) * g = t * (g⁻¹ * u * g) := by
    calc g⁻¹ * (t * u) * g = (g⁻¹ * t) * u * g := by group
      _ = t * (g⁻¹ * u * g) := by rw [hg't]; group
  rw [e]
  exact mul_mem (mem_sup_left (mem_zpowers t)) (mem_sup_right
    ((mem_normalizer_iff''.mp hgN u).mp (pull_mono φ rootU_one_le_rootA_two hu)))

theorem fus_two [Finite G] [Finite K] (hH : Hyp L K n φ TG t) :
    {x : G | (∃ g : G, x = g⁻¹ * t * g) ∧ x ∈ zpowers t ⊔ pull φ (rootA K Axis.two)} =
        {x | ∃ a b : K, x = t * ((φ.symm (uElt a b 0 0) : L) : G)} ∧
      {x : G | ∃ a b : K, x = t * ((φ.symm (uElt a b 0 0) : L) : G)} =
        {x | ∃ g ∈ L ⊓ normalizer (pull φ (rootA K Axis.two) : Set G),
          ∃ u ∈ pull φ (rootU K Axis.one), x = g⁻¹ * (t * u) * g} := by
  constructor
  · ext x
    constructor
    · rintro ⟨⟨h, hx⟩, hxB⟩
      obtain ⟨g, hg, u, hu, rfl⟩ := hH.fus_two_subset hx hxB
      exact hH.union_subset hg hu
    · rintro ⟨a, b, rfl⟩
      obtain ⟨g, hg, u, hu, e⟩ := hH.subset_union a b
      rw [e]
      exact hH.union_mem hg hu
  · ext x
    constructor
    · rintro ⟨a, b, rfl⟩
      exact hH.subset_union a b
    · rintro ⟨g, hg, u, hu, rfl⟩
      exact hH.union_subset hg hu

theorem card_fus_one [Finite G] [Finite K]
    (hH : Hyp L K n φ TG t) :
    Nat.card {x : G | (∃ g : G, x = g⁻¹ * t * g) ∧ x ∈ zpowers t ⊔ pull φ (rootA K Axis.one)} =
      Nat.card K := by
  rw [hH.fus_one, card_mul_left_set, card_U φ Axis.one]

theorem card_pair_set (φ : L ≃* antiSp K) (t : G) :
    Nat.card {x : G | ∃ a b : K, x = t * ((φ.symm (uElt a b 0 0) : L) : G)} =
      Nat.card K ^ 2 := by
  have e : {x : G | ∃ a b : K, x = t * ((φ.symm (uElt a b 0 0) : L) : G)} =
      Set.range fun p : K × K => t * ((φ.symm (uElt p.1 p.2 0 0) : L) : G) := by
    ext x
    constructor
    · rintro ⟨a, b, rfl⟩
      exact ⟨(a, b), rfl⟩
    · rintro ⟨⟨a, b⟩, rfl⟩
      exact ⟨a, b, rfl⟩
  have hinj : Function.Injective fun p : K × K => t * ((φ.symm (uElt p.1 p.2 0 0) : L) : G) := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    obtain ⟨ha, hb, -, -⟩ := uElt_inj (φ.symm.injective (Subtype.ext (mul_left_cancel h)))
    exact Prod.ext ha hb
  rw [e, Nat.card_range_of_injective hinj, Nat.card_prod, sq]

theorem card_fus_two [Finite G] [Finite K]
    (hH : Hyp L K n φ TG t) :
    Nat.card {x : G | (∃ g : G, x = g⁻¹ * t * g) ∧ x ∈ zpowers t ⊔ pull φ (rootA K Axis.two)} =
      Nat.card K ^ 2 := by
  rw [hH.fus_two.1, card_pair_set]

theorem B_le_Q (hH : Hyp L K n φ TG t) (i : Axis) :
    zpowers t ⊔ pull φ (rootA K i) ≤ pull φ (antiUnipotent K) ⊔ TG := by
  rw [hH.T_eq]
  exact sup_le le_sup_right ((pull_mono φ (rootA_le_antiUnipotent i)).trans le_sup_left)

theorem mul_self_of_mem_B (hH : Hyp L K n φ TG t) (i : Axis) {b : G}
    (hb : b ∈ zpowers t ⊔ pull φ (rootA K i)) : b * b = 1 := by
  have hA : ∀ a ∈ pull φ (rootA K i), a * a = 1 := by
    intro a ha
    obtain ⟨a', ha', rfl⟩ := exists_eq_symm_of_mem_pull ha
    rw [← coe_mul, ← map_mul, rootA_mul_self i ha', map_one, coe_one]
  rcases (mem_zpowers_sup_iff hH.two.t_mul_t (TwoCoreSetup.comm_pull φ hH.two)).mp hb with h | h
  · exact hA b h
  · obtain ⟨a, ha, rfl⟩ : ∃ a ∈ pull φ (rootA K i), t * a = b := ⟨t * b, h, (hH.eq_mul_mul b).symm⟩
    have hc := TwoCoreSetup.comm_pull φ hH.two a ha
    calc t * a * (t * a) = t * (a * t) * a := by group
      _ = t * (t * a) * a := by rw [hc]
      _ = (t * t) * (a * a) := by group
      _ = 1 := by rw [hH.two.t_mul_t, hA a ha, one_mul]

theorem mem_B_of_mul_self (hH : Hyp L K n φ TG t) {x : G}
    (hx : x ∈ pull φ (antiUnipotent K) ⊔ TG) (hxx : x * x = 1) :
    x ∈ zpowers t ⊔ pull φ (rootA K Axis.one) ∨ x ∈ zpowers t ⊔ pull φ (rootA K Axis.two) := by
  rw [hH.T_eq, sup_comm] at hx
  have hc := TwoCoreSetup.comm_pull (S := antiUnipotent K) φ hH.two
  obtain ⟨p, hpP, hpx, hpp⟩ : ∃ p ∈ pull φ (antiUnipotent K), (x = p ∨ x = t * p) ∧ p * p = 1 := by
    rcases (mem_zpowers_sup_iff hH.two.t_mul_t hc).mp hx with h | h
    · exact ⟨x, h, Or.inl rfl, hxx⟩
    · refine ⟨t * x, h, Or.inr (hH.eq_mul_mul x), ?_⟩
      have htx := hc _ h
      calc t * x * (t * x) = (t * (t * x)) * x := by rw [htx]; group
        _ = 1 := by rw [← hH.eq_mul_mul, hxx]
  obtain ⟨a, ha, rfl⟩ := exists_eq_symm_of_mem_pull hpP
  have haa : a * a = 1 := by
    have h1 : ((φ.symm (a * a) : L) : G) = 1 := by rw [map_mul, coe_mul, hpp]
    exact φ.symm.map_eq_one_iff.mp (Subtype.ext h1)
  have hmem : ∀ i : Axis, a ∈ rootA K i →
      x ∈ zpowers t ⊔ pull φ (rootA K i) := by
    intro i hai
    rcases hpx with rfl | rfl
    · exact mem_sup_right (symm_mem_pull.mpr hai)
    · exact mul_mem (mem_sup_left (mem_zpowers t)) (mem_sup_right (symm_mem_pull.mpr hai))
  rcases (mul_self_eq_one_iff ha).mp haa with h | h
  · exact Or.inl (hmem Axis.one h)
  · exact Or.inr (hmem Axis.two h)

theorem conj_B_le_or (hH : Hyp L K n φ TG t) {g : G}
    (hg : g ∈ normalizer ((pull φ (antiUnipotent K) ⊔ TG : Subgroup G) : Set G)) (i : Axis) :
    (∀ b ∈ zpowers t ⊔ pull φ (rootA K i),
        g * b * g⁻¹ ∈ zpowers t ⊔ pull φ (rootA K Axis.one)) ∨
      ∀ b ∈ zpowers t ⊔ pull φ (rootA K i),
        g * b * g⁻¹ ∈ zpowers t ⊔ pull φ (rootA K Axis.two) := by
  have h := subgroup_le_of_subset_union (E := (zpowers t ⊔ pull φ (rootA K i)).map
    (MulAut.conj g).toMonoidHom) (P := zpowers t ⊔ pull φ (rootA K Axis.one))
    (Q := zpowers t ⊔ pull φ (rootA K Axis.two)) (by
      rintro _ ⟨b, hb, rfl⟩
      refine hH.mem_B_of_mul_self ((mem_normalizer_iff.mp hg b).mp (hH.B_le_Q i hb)) ?_
      have hbb := hH.mul_self_of_mem_B i hb
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc g * b * g⁻¹ * (g * b * g⁻¹) = g * (b * b) * g⁻¹ := by group
        _ = 1 := by rw [hbb]; group)
  rcases h with h | h
  · exact Or.inl fun b hb => h ⟨b, hb, rfl⟩
  · exact Or.inr fun b hb => h ⟨b, hb, rfl⟩

theorem not_conj_B_two_le [Finite G] [Finite K]
    (hH : Hyp L K n φ TG t) {g : G}
    (hg : ∀ b ∈ zpowers t ⊔ pull φ (rootA K Axis.two),
      g * b * g⁻¹ ∈ zpowers t ⊔ pull φ (rootA K Axis.one)) : False := by
  have hmap : ∀ x ∈ {x : G | (∃ h : G, x = h⁻¹ * t * h) ∧
      x ∈ zpowers t ⊔ pull φ (rootA K Axis.two)},
      g * x * g⁻¹ ∈ {x : G | (∃ h : G, x = h⁻¹ * t * h) ∧
        x ∈ zpowers t ⊔ pull φ (rootA K Axis.one)} := by
    rintro x ⟨⟨h, rfl⟩, hx⟩
    exact ⟨⟨h * g⁻¹, by group⟩, hg _ hx⟩
  have hinj : Function.Injective fun x : {x : G | (∃ h : G, x = h⁻¹ * t * h) ∧
      x ∈ zpowers t ⊔ pull φ (rootA K Axis.two)} =>
      (⟨g * x * g⁻¹, hmap x x.2⟩ : {x : G | (∃ h : G, x = h⁻¹ * t * h) ∧
        x ∈ zpowers t ⊔ pull φ (rootA K Axis.one)}) := by
    intro x y hxy
    apply Subtype.ext
    simpa using congrArg Subtype.val hxy
  have hle := Nat.card_le_card_of_injective _ hinj
  rw [hH.card_fus_two, hH.card_fus_one] at hle
  have h4 : 2 ≤ Nat.card K := by
    rw [hH.two.card_K]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by linarith [hH.two.two_le])
  nlinarith

theorem not_B_one_le (hH : Hyp L K n φ TG t) :
    ¬ zpowers t ⊔ pull φ (rootA K Axis.one) ≤ zpowers t ⊔ pull φ (rootA K Axis.two) := by
  intro hle
  have h1 : ((φ.symm (uElt 0 0 0 1) : L) : G) ∈ (zpowers t ⊔ pull φ (rootA K Axis.two)) ⊓ L :=
    ⟨hle (mem_sup_right (symm_mem_pull.mpr ⟨0, 0, 1, rfl⟩)), (φ.symm _).2⟩
  rw [zpowers_sup_inf_eq hH.two.t_mul_t (pull_le φ _) hH.two.t_not_mem
    (TwoCoreSetup.comm_pull φ hH.two)] at h1
  obtain ⟨a, b, c, h⟩ := symm_mem_pull.mp h1
  exact one_ne_zero (uElt_inj h).2.2.2

theorem normalizer_Q_le [Finite G] [Finite K]
    (hH : Hyp L K n φ TG t) :
    normalizer ((pull φ (antiUnipotent K) ⊔ TG : Subgroup G) : Set G) ≤
      normalizer ((zpowers t ⊔ pull φ (rootA K Axis.one) : Subgroup G) : Set G) ⊓
        normalizer ((zpowers t ⊔ pull φ (rootA K Axis.two) : Subgroup G) : Set G) := by
  have h2 : ∀ g ∈ normalizer ((pull φ (antiUnipotent K) ⊔ TG : Subgroup G) : Set G),
      g ∈ normalizer ((zpowers t ⊔ pull φ (rootA K Axis.two) : Subgroup G) : Set G) := by
    intro g hg
    rcases hH.conj_B_le_or hg Axis.two with h | h
    · exact (hH.not_conj_B_two_le h).elim
    · exact mem_normalizer_of_conj_le h
  intro g hg
  refine ⟨?_, h2 g hg⟩
  rcases hH.conj_B_le_or hg Axis.one with h | h
  · exact mem_normalizer_of_conj_le h
  · exact (hH.not_B_one_le fun b hb => (mem_normalizer_iff.mp (h2 g hg) b).mpr (h b hb)).elim

theorem normalizer_B_one_le [Finite G] [Finite K]
    (hH : Hyp L K n φ TG t) :
    normalizer ((zpowers t ⊔ pull φ (rootA K Axis.one) : Subgroup G) : Set G) ≤
      normalizer (pull φ (rootU K Axis.one) : Set G) ⊓
        normalizer ((zpowers t ⊔ pull φ (rootU K Axis.one) : Subgroup G) : Set G) := by
  intro g hg
  have hF : ∀ u ∈ pull φ (rootU K Axis.one), ∃ u' ∈ pull φ (rootU K Axis.one),
      g * (t * u) * g⁻¹ = t * u' := by
    intro u hu
    have h1 : t * u ∈ {x : G | (∃ g : G, x = g⁻¹ * t * g) ∧
        x ∈ zpowers t ⊔ pull φ (rootA K Axis.one)} := by
      rw [hH.fus_one]
      exact ⟨u, hu, rfl⟩
    obtain ⟨⟨h, hh⟩, hB⟩ := h1
    have h2 : g * (t * u) * g⁻¹ ∈ {x : G | (∃ g : G, x = g⁻¹ * t * g) ∧
        x ∈ zpowers t ⊔ pull φ (rootA K Axis.one)} :=
      ⟨⟨h * g⁻¹, by rw [hh]; group⟩, (mem_normalizer_iff.mp hg _).mp hB⟩
    rw [hH.fus_one] at h2
    exact h2
  obtain ⟨u₀, hu₀, h0⟩ := hF 1 (one_mem _)
  have hU : ∀ u ∈ pull φ (rootU K Axis.one), g * u * g⁻¹ ∈ pull φ (rootU K Axis.one) := by
    intro u hu
    obtain ⟨u₁, hu₁, h1⟩ := hF u hu
    have e : g * u * g⁻¹ = (g * (t * 1) * g⁻¹)⁻¹ * (g * (t * u) * g⁻¹) := by group
    rw [e, h0, h1, show (t * u₀)⁻¹ * (t * u₁) = u₀⁻¹ * u₁ by group]
    exact mul_mem (inv_mem hu₀) hu₁
  have htV : g * t * g⁻¹ ∈ zpowers t ⊔ pull φ (rootU K Axis.one) := by
    rw [show g * t * g⁻¹ = g * (t * 1) * g⁻¹ by group, h0]
    exact mul_mem (mem_sup_left (mem_zpowers t)) (mem_sup_right hu₀)
  have hle : zpowers t ⊔ pull φ (rootU K Axis.one) ≤
      (zpowers t ⊔ pull φ (rootU K Axis.one)).comap (MulAut.conj g).toMonoidHom :=
    sup_le (zpowers_le.mpr htV) fun u hu => mem_sup_right (hU u hu)
  exact ⟨mem_normalizer_of_conj_le hU, mem_normalizer_of_conj_le fun x hx => hle hx⟩

theorem normalizer_V_two_le [Finite G] [Finite K]
    (hH : Hyp L K n φ TG t) :
    normalizer ((zpowers t ⊔ pull φ (rootU K Axis.two) : Subgroup G) : Set G) ≤
      centralizer ({t} : Set G) := by
  intro g hg
  have h1 : g⁻¹ * t * g ∈ zpowers t ⊔ pull φ (rootU K Axis.two) :=
    (mem_normalizer_iff''.mp hg t).mp (mem_sup_left (mem_zpowers t))
  have h2 := hH.mul_mem_of_conj (pull_le φ _) rfl h1
  have h3 := hH.mem_U_of_conj (pull_mono φ (rootU_le_center Axis.two) h2)
    (hH.eq_mul_mul (g⁻¹ * t * g)).symm
  have h4 : t * (g⁻¹ * t * g) ∈ pull φ (rootU K Axis.one) ⊓ pull φ (rootU K Axis.two) := ⟨h3, h2⟩
  rw [← pull_inf, rootU_inf_eq_bot, pull_bot, mem_bot] at h4
  have h5 : g⁻¹ * t * g = t := by rw [hH.eq_mul_mul (g⁻¹ * t * g), h4, mul_one]
  rw [mem_centralizer_singleton_iff]
  calc g * t = g * (g⁻¹ * t * g) := by rw [h5]
    _ = t * g := by group

end Hyp

section Congr

open scoped Pointwise

theorem two_core_congr {G : Type*} [Group G] {C M M' B U : Subgroup G} {t : G} {n : ℕ}
    (hM : M = M')
    (h : let D := (CFSG.pCore 2 M).map M.subtype
      (D : Set G) * ((C ⊓ M : Subgroup G) : Set G) = M ∧
        D ⊓ (C ⊓ M) = B ∧ (B ≤ M ∧ (B.subgroupOf M).Normal) ∧
        ∃ _ : (B.subgroupOf D).Normal, ∃ e : (↥D ⧸ B.subgroupOf D) ≃* ↥U,
          (∀ d : D, (e d : G) = t⁻¹ * ((d : G)⁻¹ * t * d)) ∧
          (∀ h ∈ C ⊓ M, ∀ d : D, ∃ d' : D, (d' : G) = h⁻¹ * d * h ∧
            (e d' : G) = h⁻¹ * e d * h) ∧
          Nat.card (↥D ⧸ B.subgroupOf D) = 2 ^ n ∧
          IsElementaryAbelian 2 (↥D ⧸ B.subgroupOf D)) :
    let D := (CFSG.pCore 2 M').map M'.subtype
    (D : Set G) * ((C ⊓ M' : Subgroup G) : Set G) = M' ∧
      D ⊓ (C ⊓ M') = B ∧ (B ≤ M' ∧ (B.subgroupOf M').Normal) ∧
      ∃ _ : (B.subgroupOf D).Normal, ∃ e : (↥D ⧸ B.subgroupOf D) ≃* ↥U,
        (∀ d : D, (e d : G) = t⁻¹ * ((d : G)⁻¹ * t * d)) ∧
        (∀ h ∈ C ⊓ M', ∀ d : D, ∃ d' : D, (d' : G) = h⁻¹ * d * h ∧
          (e d' : G) = h⁻¹ * e d * h) ∧
        Nat.card (↥D ⧸ B.subgroupOf D) = 2 ^ n ∧
        IsElementaryAbelian 2 (↥D ⧸ B.subgroupOf D) := by
  subst hM
  exact h

end Congr

end OneAxisRadical

open Subgroup GomiFusion RootAxisTwoCore OneAxisRadical
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.RankThree.PartOne.KCRootAxis
open scoped Pointwise

theorem standard_symplectic_four_one_axis_radical_fusion_normalizers
    {G : Type} [Group G] [Finite G] (hO : CFSG.Open.standardComponentOddCore G = ⊥)
    {L : Subgroup G} (hL : CFSG.Open.standardComponentIsStandard L) (hLn : ¬ L.Normal)
    {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ n)
    (T : Sylow 2 (centralizer (L : Set G)))
    (hT : IsCyclic (T : Subgroup (centralizer (L : Set G))))
    {t : centralizer (L : Set G)} (htT : t ∈ T) (ht : orderOf t = 2)
    (hcore : CFSG.Open.standardComponentOddCore (centralizer ({(t : G)} : Set G)) = ⊥)
    (P : Sylow 2 L) (φ : L ≃* antiSp K)
    (hφP : (P : Subgroup L).map φ.toMonoidHom = antiUnipotent K) :
    let C := centralizer ({(t : G)} : Set G)
    let TG := (T : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype
    let PG := (P : Subgroup L).map L.subtype
    let Q := PG ⊔ TG
    let U₁ := ((rootU K Axis.one).comap φ.toMonoidHom).map L.subtype
    let U₂ := ((rootU K Axis.two).comap φ.toMonoidHom).map L.subtype
    let A₁ := ((rootA K Axis.one).comap φ.toMonoidHom).map L.subtype
    let A₂ := ((rootA K Axis.two).comap φ.toMonoidHom).map L.subtype
    let V₁ := zpowers (t : G) ⊔ U₁
    let V₂ := zpowers (t : G) ⊔ U₂
    let B₁ := zpowers (t : G) ⊔ A₁
    let B₂ := zpowers (t : G) ⊔ A₂
    let N₁ := normalizer (B₁ : Set G)
    let D₁ := (CFSG.pCore 2 N₁).map N₁.subtype
    {x : G | ∃ m ∈ normalizer (Q : Set G), x = m⁻¹ * t * m} = {x | ∃ u ∈ U₁, x = t * u} →
      {x : G | (∃ g : G, x = g⁻¹ * t * g) ∧ x ∈ B₁} = {x | ∃ u ∈ U₁, x = t * u} ∧
      {x : G | (∃ g : G, x = g⁻¹ * t * g) ∧ x ∈ B₂} =
        {x | ∃ a b : K, x = t * ((φ.symm (uElt a b 0 0) : L) : G)} ∧
      {x : G | ∃ a b : K, x = t * ((φ.symm (uElt a b 0 0) : L) : G)} =
        {x | ∃ g ∈ L ⊓ normalizer (A₂ : Set G), ∃ u ∈ U₁, x = g⁻¹ * (t * u) * g} ∧
      Nat.card {x : G | (∃ g : G, x = g⁻¹ * t * g) ∧ x ∈ B₁} = 2 ^ n ∧
      Nat.card {x : G | (∃ g : G, x = g⁻¹ * t * g) ∧ x ∈ B₂} = (2 ^ n) ^ 2 ∧
      normalizer (Q : Set G) ≤ normalizer (B₁ : Set G) ⊓ normalizer (B₂ : Set G) ∧
      (normalizer (V₁ : Set G) = normalizer (B₁ : Set G) ∧
        normalizer (B₁ : Set G) ≤ normalizer (U₁ : Set G)) ∧
      normalizer (V₂ : Set G) = C ⊓ normalizer (B₂ : Set G) ∧
      (D₁ : Set G) * ((C ⊓ N₁ : Subgroup G) : Set G) = N₁ ∧
      D₁ ⊓ (C ⊓ N₁) = B₁ ∧ (B₁ ≤ N₁ ∧ (B₁.subgroupOf N₁).Normal) ∧
      ∃ _ : (B₁.subgroupOf D₁).Normal, ∃ e : (↥D₁ ⧸ B₁.subgroupOf D₁) ≃* ↥U₁,
        (∀ d : D₁, (e d : G) = (t : G)⁻¹ * ((d : G)⁻¹ * t * d)) ∧
        (∀ h ∈ C ⊓ N₁, ∀ d : D₁, ∃ d' : D₁, (d' : G) = h⁻¹ * d * h ∧
          (e d' : G) = h⁻¹ * e d * h) ∧
        Nat.card (↥D₁ ⧸ B₁.subgroupOf D₁) = 2 ^ n ∧
        IsElementaryAbelian 2 (↥D₁ ⧸ B₁.subgroupOf D₁) := by
  intro C TG PG Q U₁ U₂ A₁ A₂ V₁ V₂ B₁ B₂ N₁ D₁ hone
  have hS := setup_of_standard hL hn hK φ T hT htT ht hcore
  have hT' := hS.T_eq_zpowers hO hLn
  have hS2 : TwoCoreSetup L K n (t : G) :=
    { two_le := hn
      card_K := hK
      t_mul_t := hS.t_mul_t
      L_le := hS.L_le
      cent_le := hS.cent_le
      cent_inf := hS.cent_inf.trans hT'
      not_conj := hS.conj_not_mem_L hO hLn }
  have hPG : PG = pull φ (antiUnipotent K) := by
    change (P : Subgroup L).map L.subtype = ((antiUnipotent K).comap φ.toMonoidHom).map L.subtype
    rw [← hφP, comap_map_eq_self_of_injective φ.injective]
  have hQ : Q = pull φ (antiUnipotent K) ⊔ TG := by
    show PG ⊔ TG = _
    rw [hPG]
  have hH : Hyp L K n φ TG t := ⟨hS, hS2, hT', by rw [← hQ]; exact hone⟩
  obtain ⟨hF2, hSU⟩ := hH.fus_two
  have hNQ := hH.normalizer_Q_le
  rw [← hQ] at hNQ
  have hB1 := hH.normalizer_B_one_le
  have hMeq : normalizer (V₁ : Set G) = N₁ :=
    le_antisymm (TwoCoreSetup.M_le_normalizer_B φ Axis.one hS2) fun g hg => (hB1 hg).2
  have hNC := (hS.orbits hO hLn).2.2.2.2
  rw [← hQ] at hNC
  have hMC : ¬ normalizer (V₁ : Set G) ≤ C := fun hle =>
    hNC fun g hg => hle (hMeq.ge (hNQ hg).1)
  obtain ⟨-, -, -, -, h5⟩ := standard_symplectic_four_root_axis_normalizer_two_core hO hL hLn hn
    hK T hT htT ht hcore φ Axis.one
  have hinf := TwoCoreSetup.inf_normalizer_eq φ Axis.two hS2
  refine ⟨hH.fus_one, hF2, hSU, hH.card_fus_one.trans hK, hH.card_fus_two.trans (by rw [hK]),
    hNQ, ⟨hMeq, fun g hg => (hB1 hg).1⟩, le_antisymm (fun g hg => ?_) fun g hg => (hinf.ge hg).2,
    two_core_congr hMeq (h5 hMC).2⟩
  exact hinf.le ⟨hH.normalizer_V_two_le hg, hg⟩

end CFSG.LocalAnalysis.SymplecticFourStandard
