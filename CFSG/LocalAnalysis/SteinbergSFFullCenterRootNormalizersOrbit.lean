module

public import CFSG.LocalAnalysis.SteinbergSFRootAxisNormalizerTwoCore

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace FullCenter

open Subgroup GomiFusion RootAxisTwoCore
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis
open scoped Matrix

section General

variable {G : Type*} [Group G]

theorem relIndex_centralizer_eq_card (H : Subgroup G) (t : G) :
    (centralizer ({t} : Set G)).relIndex H = Nat.card {x : G | ∃ h ∈ H, x = h⁻¹ * t * h} := by
  classical
  set S := {x : G | ∃ h ∈ H, x = h⁻¹ * t * h}
  let f : H → S := fun h => ⟨(h : G) * t * (h : G)⁻¹, (h : G)⁻¹, inv_mem h.2, by group⟩
  have hf : ∀ a b : H, f a = f b ↔ a⁻¹ * b ∈ (centralizer ({t} : Set G)).subgroupOf H := by
    intro a b
    rw [mem_subgroupOf, mem_centralizer_singleton_iff, Subtype.ext_iff]
    simp only [f, coe_mul, coe_inv]
    constructor
    · intro e
      calc (a : G)⁻¹ * b * t = (a : G)⁻¹ * (b * t * (b : G)⁻¹) * b := by group
        _ = (a : G)⁻¹ * (a * t * (a : G)⁻¹) * b := by rw [e]
        _ = t * ((a : G)⁻¹ * b) := by group
    · intro e
      calc (a : G) * t * (a : G)⁻¹ = a * (t * ((a : G)⁻¹ * b)) * (b : G)⁻¹ := by group
        _ = a * ((a : G)⁻¹ * b * t) * (b : G)⁻¹ := by rw [e]
        _ = b * t * (b : G)⁻¹ := by group
  rw [relIndex, index]
  refine Nat.card_congr (Equiv.ofBijective
    (Quotient.lift f fun a b hab => (hf a b).mpr (QuotientGroup.leftRel_apply.mp hab)) ⟨?_, ?_⟩)
  · rintro ⟨a⟩ ⟨b⟩ hab
    exact Quotient.sound (QuotientGroup.leftRel_apply.mpr ((hf a b).mp hab))
  · rintro ⟨x, h, hh, rfl⟩
    refine ⟨Quotient.mk'' ⟨h⁻¹, inv_mem hh⟩, Subtype.ext ?_⟩
    show h⁻¹ * t * h⁻¹⁻¹ = h⁻¹ * t * h
    rw [inv_inv]

theorem card_mul_set (A : Subgroup G) (t : G) :
    Nat.card {x : G | ∃ a ∈ A, x = t * a} = Nat.card A :=
  (Nat.card_congr (Equiv.ofBijective (fun a : A => (⟨t * a, a, a.2, rfl⟩ :
    {x : G | ∃ a ∈ A, x = t * a})) ⟨fun _ _ h => Subtype.ext (mul_left_cancel
      (congrArg Subtype.val h)), fun ⟨_, a, ha, hx⟩ => ⟨⟨a, ha⟩, Subtype.ext hx.symm⟩⟩)).symm

theorem exists_index_two [Finite G] {N X₁ X₂ : Subgroup G}
    (h : ∀ g ∈ N, (g ∈ normalizer (X₁ : Set G) ∧ g ∈ normalizer (X₂ : Set G)) ∨
      ((∀ x ∈ X₁, g * x * g⁻¹ ∈ X₂) ∧ ∀ x ∈ X₂, g * x * g⁻¹ ∈ X₁)) :
    ∃ a ∈ N, ∀ b ∈ N, b * a ∈ N ⊓ normalizer (X₁ : Set G) ⊓ normalizer (X₂ : Set G) ∨
      b ∈ N ⊓ normalizer (X₁ : Set G) ⊓ normalizer (X₂ : Set G) := by
  by_cases hsw : ∃ a ∈ N, ¬ (a ∈ normalizer (X₁ : Set G) ∧ a ∈ normalizer (X₂ : Set G))
  · obtain ⟨a, ha, hna⟩ := hsw
    obtain ⟨ha1, ha2⟩ := (h a ha).resolve_left hna
    refine ⟨a, ha, fun b hb => ?_⟩
    rcases h b hb with hfx | ⟨hb1, hb2⟩
    · exact Or.inr ⟨⟨hb, hfx.1⟩, hfx.2⟩
    · left
      refine ⟨⟨mul_mem hb ha, RootAxisTwoCore.mem_normalizer_of_conj_le fun x hx => ?_⟩,
        RootAxisTwoCore.mem_normalizer_of_conj_le fun x hx => ?_⟩
      · rw [show b * a * x * (b * a)⁻¹ = b * (a * x * a⁻¹) * b⁻¹ by group]
        exact hb2 _ (ha1 x hx)
      · rw [show b * a * x * (b * a)⁻¹ = b * (a * x * a⁻¹) * b⁻¹ by group]
        exact hb1 _ (ha2 x hx)
  · push Not at hsw
    exact ⟨1, one_mem N, fun b hb => Or.inr ⟨⟨hb, (hsw b hb).1⟩, (hsw b hb).2⟩⟩

theorem relIndex_le_two {H K : Subgroup G} (h : ∃ a ∈ K, ∀ b ∈ K, b * a ∈ H ∨ b ∈ H) :
    H.relIndex K ≤ 2 :=
  Nat.le_of_dvd two_pos (relIndex_dvd_two_iff.mpr h)

theorem mem_normalizer_zpowers_sup [Finite G] {t g : G} {W : Subgroup G}
    (ht : g * t * g⁻¹ ∈ zpowers t ⊔ W) (hW : ∀ w ∈ W, g * w * g⁻¹ ∈ W) :
    g ∈ normalizer ((zpowers t ⊔ W : Subgroup G) : Set G) := by
  refine RootAxisTwoCore.mem_normalizer_of_conj_le fun x hx => ?_
  have hle : zpowers t ⊔ W ≤ (zpowers t ⊔ W).comap (MulAut.conj g).toMonoidHom :=
    sup_le (zpowers_le.mpr ht) fun w hw => mem_sup_right (hW w hw)
  exact hle hx

end General

section Model

variable {K : Type} [Field K] [CharP K 2]

theorem rootU_le_center (i : Axis) : rootU K i ≤ antiUnipotentCenter K := by
  cases i
  · exact Setup.axisOne_le_center (K := K)
  · exact Setup.axisTwo_le_center (K := K)

theorem center_le_rootA (i : Axis) : antiUnipotentCenter K ≤ rootA K i := by
  cases i
  · exact antiUnipotentCenter_le_radA1
  · exact antiUnipotentCenter_le_radA2

theorem rootU_le_rootA (i : Axis) : rootU K i ≤ rootA K i :=
  (rootU_le_center i).trans (center_le_rootA i)

theorem rootA_le_antiUnipotent (i : Axis) : rootA K i ≤ antiUnipotent K := by
  cases i
  · exact radA1_le_antiUnipotent
  · exact radA2_le_antiUnipotent

theorem rootA_comm (i : Axis) {x y : antiSp K} (hx : x ∈ rootA K i) (hy : y ∈ rootA K i) :
    x * y = y * x := by
  cases i
  · exact radA1_comm hx hy
  · exact radA2_comm hx hy

theorem rootA_mul_self (i : Axis) {x : antiSp K} (hx : x ∈ rootA K i) : x * x = 1 := by
  cases i
  · exact mul_self_of_mem_radA1 hx
  · exact mul_self_of_mem_radA2 hx

theorem rootU_inf : rootU K Axis.one ⊓ rootU K Axis.two = ⊥ :=
  (antiUnipotentCenter_eq_axis (K := K)).2

theorem center_eq_rootU_sup : antiUnipotentCenter K = rootU K Axis.one ⊔ rootU K Axis.two :=
  (antiUnipotentCenter_eq_axis (K := K)).1

theorem card_rootA [Finite K] (i : Axis) : Nat.card (rootA K i) = Nat.card K ^ 3 := by
  obtain ⟨-, h1, h2, -⟩ := card_radicals (K := K)
  cases i
  · exact h1
  · exact h2

theorem card_rootU (i : Axis) : Nat.card (rootU K i) = Nat.card K := by
  cases i
  · exact (card_axis (K := K)).1
  · exact (card_axis (K := K)).2

theorem vecOf₂_uElt (a b c : K) : vecOf₂ (uElt a b c 0) = ![b, a] := by
  have h := vecOf₂_aElt ![b, a] c
  simpa [aElt] using h

theorem exists_center_vecOf [Finite K] (i : Axis) :
    ∃ z ∈ antiUnipotentCenter K, vecOf K i z = ![1, 0] := by
  cases i
  · refine ⟨uElt 0 0 1 0, ⟨0, 1, rfl⟩, ?_⟩
    have h : (minorAut K).symm (uElt 0 0 1 0) = uElt 0 1 0 0 := by
      rw [MulEquiv.symm_apply_eq, minorAut_uElt_radA2]
      congr 1 <;> ring
    show vecOf₂ ((minorAut K).symm (uElt 0 0 1 0)) = ![1, 0]
    rw [h, vecOf₂_uElt]
  · exact ⟨uElt 0 1 0 0, ⟨1, 0, rfl⟩, vecOf₂_uElt 0 1 0⟩

theorem uElt_mem_radA1_not_mem_radA2 :
    uElt (0 : K) 0 0 1 ∈ radA1 K ∧ uElt (0 : K) 0 0 1 ∉ radA2 K := by
  refine ⟨⟨0, 0, 1, rfl⟩, ?_⟩
  rintro ⟨a, b, c, h⟩
  exact one_ne_zero (uElt_inj h).2.2.2

end Model

section Torus

variable {K : Type} [Field K] [CharP K 2]

theorem diagTorus_conj_mem_rootA {δ : antiSp K} (hδ : δ ∈ diagTorus K) (i : Axis)
    {z : antiSp K} (hz : z ∈ rootA K i) : δ⁻¹ * z * δ ∈ rootA K i := by
  obtain ⟨r, s, hr, hs, hδm⟩ := hδ
  cases i
  · obtain ⟨b, c, d, rfl⟩ := hz
    rw [diagTorus_conj hr hs hδm]
    exact ⟨r * s * b, r ^ 2 * c, s ^ 2 * d, by rw [mul_zero]⟩
  · obtain ⟨a, b, c, rfl⟩ := hz
    rw [diagTorus_conj hr hs hδm]
    exact ⟨r * s⁻¹ * a, r * s * b, r ^ 2 * c, by rw [mul_zero]⟩

theorem diagTorus_conj_mem_rootU {δ : antiSp K} (hδ : δ ∈ diagTorus K) (i : Axis)
    {z : antiSp K} (hz : z ∈ rootU K i) : δ⁻¹ * z * δ ∈ rootU K i := by
  obtain ⟨r, s, hr, hs, hδm⟩ := hδ
  cases i
  · obtain ⟨b, rfl⟩ := hz
    rw [diagTorus_conj hr hs hδm]
    exact ⟨r * s * b, by simp⟩
  · obtain ⟨c, rfl⟩ := hz
    rw [diagTorus_conj hr hs hδm]
    exact ⟨r ^ 2 * c, by simp⟩

variable {G : Type*} [Group G] {L : Subgroup G}

omit [CharP K 2] in
theorem torus_le_normalizer_pull [Finite G] {φ : L ≃* antiSp K} {S : Subgroup (antiSp K)}
    (hS : ∀ δ ∈ diagTorus K, ∀ z ∈ S, δ⁻¹ * z * δ ∈ S) :
    pull φ (diagTorus K) ≤ normalizer (pull φ S : Set G) := by
  intro d hd
  obtain ⟨δ, hδ, rfl⟩ := exists_eq_symm_of_mem_pull hd
  refine RootAxisTwoCore.mem_normalizer_of_conj_le fun x hx => ?_
  obtain ⟨z, hz, rfl⟩ := exists_eq_symm_of_mem_pull hx
  rw [symm_conj_eq]
  have := hS δ⁻¹ (inv_mem hδ) z hz
  rw [inv_inv] at this
  exact symm_mem_pull.mpr this

end Torus

section Coord

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2] [Finite K]

omit [CharP K 2] [Finite K] in
theorem matrix_eq_one_of_mulVec {A : Matrix (Fin 2) (Fin 2) K}
    (h : ∀ v : Fin 2 → K, A *ᵥ v = v) : A = 1 := by
  ext i j
  have h1 := congrFun (h (Pi.single j 1)) i
  rw [Matrix.mulVec_single_one] at h1
  rw [Matrix.one_apply]
  simpa [Pi.single_apply, eq_comm] using h1

open Classical in
@[expose] noncomputable def psiG (φ : L ≃* antiSp K) (i : Axis) (w : G) : Fin 2 → K :=
  if hw : w ∈ L then vecOf K i (φ ⟨w, hw⟩) else 0

theorem psiG_symm (φ : L ≃* antiSp K) (i : Axis) (z : antiSp K) :
    psiG φ i ((φ.symm z : L) : G) = vecOf K i z := by
  simp [psiG]

variable {n : ℕ} {t : G} (hS : TwoCoreSetup L K n t) (φ : L ≃* antiSp K) (i : Axis)
include hS

theorem psiG_mul {a b : G} (ha : a ∈ pull φ (rootA K i)) (hb : b ∈ pull φ (rootA K i)) :
    psiG φ i (a * b) = psiG φ i a + psiG φ i b := by
  obtain ⟨a', ha', rfl⟩ := exists_eq_symm_of_mem_pull ha
  obtain ⟨b', hb', rfl⟩ := exists_eq_symm_of_mem_pull hb
  rw [← coe_mul, ← map_mul, psiG_symm, psiG_symm, psiG_symm]
  exact (hS.axisStr i).vec_add a' ha' b' hb'

theorem psiG_eq_zero_iff {a : G} (ha : a ∈ pull φ (rootA K i)) :
    psiG φ i a = 0 ↔ a ∈ pull φ (rootU K i) := by
  obtain ⟨a', ha', rfl⟩ := exists_eq_symm_of_mem_pull ha
  rw [psiG_symm, symm_mem_pull]
  exact (hS.axisStr i).vec_ker a' ha'

theorem exists_psiG_eq (v : Fin 2 → K) : ∃ a ∈ pull φ (rootA K i), psiG φ i a = v := by
  obtain ⟨z, hz, hzv⟩ := (hS.axisStr i).vec_surj v
  exact ⟨_, symm_mem_pull.mpr hz, by rw [psiG_symm, hzv]⟩

theorem psiG_inv {a : G} (ha : a ∈ pull φ (rootA K i)) : psiG φ i a⁻¹ = -psiG φ i a := by
  have h1 := psiG_mul hS φ i ha (inv_mem ha)
  rw [mul_inv_cancel, (psiG_eq_zero_iff hS φ i (one_mem _)).mpr (one_mem _)] at h1
  exact eq_neg_of_add_eq_zero_right h1.symm

theorem psiG_eq_iff {a b : G} (ha : a ∈ pull φ (rootA K i)) (hb : b ∈ pull φ (rootA K i)) :
    psiG φ i a = psiG φ i b ↔ a⁻¹ * b ∈ pull φ (rootU K i) := by
  rw [← psiG_eq_zero_iff hS φ i (mul_mem (inv_mem ha) hb), psiG_mul hS φ i (inv_mem ha) hb,
    psiG_inv hS φ i ha, neg_add_eq_zero]

theorem psiG_conj_s (M : SL₂ K) {a : G} (ha : a ∈ pull φ (rootA K i)) :
    ((φ.symm (sHom K i M) : L) : G) * a * ((φ.symm (sHom K i M) : L) : G)⁻¹ ∈
        pull φ (rootA K i) ∧
      psiG φ i (((φ.symm (sHom K i M) : L) : G) * a * ((φ.symm (sHom K i M) : L) : G)⁻¹) =
        (M : Matrix (Fin 2) (Fin 2) K) *ᵥ psiG φ i a := by
  obtain ⟨a', ha', rfl⟩ := exists_eq_symm_of_mem_pull ha
  rw [symm_conj_eq, psiG_symm, psiG_symm, symm_mem_pull]
  exact ⟨(hS.axisStr i).A_normal_C _ ((hS.axisStr i).s_mem_C M) a' ha',
    (hS.axisStr i).vec_conj M a' ha'⟩

theorem symm_s_mem_rootC (M : SL₂ K) :
    ((φ.symm (sHom K i M) : L) : G) ∈ pull φ (rootC K i) :=
  symm_mem_pull.mpr ((hS.axisStr i).s_mem_C M)

end Coord

structure FCHyp {G : Type} [Group G] (L : Subgroup G) (K : Type) [Field K] [CharP K 2] (n : ℕ)
    (φ : L ≃* antiSp K) (t : G) : Prop where
  setup : Setup L K n φ (zpowers t) t
  not_conj : ∀ g : G, g⁻¹ * t * g ∉ L
  conj_axis : ∀ g ∈ normalizer ((pull φ (antiUnipotent K) ⊔ zpowers t : Subgroup G) : Set G),
    ((∀ x ∈ pull φ (rootU K Axis.one), g * x * g⁻¹ ∈ pull φ (rootU K Axis.one)) ∧
        ∀ x ∈ pull φ (rootU K Axis.two), g * x * g⁻¹ ∈ pull φ (rootU K Axis.two)) ∨
      ((∀ x ∈ pull φ (rootU K Axis.one), g * x * g⁻¹ ∈ pull φ (rootU K Axis.two)) ∧
        ∀ x ∈ pull φ (rootU K Axis.two), g * x * g⁻¹ ∈ pull φ (rootU K Axis.one))
  orbit_shapes : ∀ Z : Subgroup G, pull φ (diagTorus K) ≤ Z →
    Z ≤ normalizer ((pull φ (antiUnipotent K) ⊔ zpowers t : Subgroup G) : Set G) →
    ¬ Z ≤ centralizer ({t} : Set G) →
    {x : G | ∃ m ∈ Z, x = m⁻¹ * t * m} = {x | ∃ u ∈ pull φ (rootU K Axis.one), x = t * u} ∨
      {x : G | ∃ m ∈ Z, x = m⁻¹ * t * m} = {x | ∃ u ∈ pull φ (rootU K Axis.two), x = t * u} ∨
      {x : G | ∃ m ∈ Z, x = m⁻¹ * t * m} =
        {x | ∃ z ∈ pull φ (antiUnipotentCenter K), x = t * z}
  full : {x : G | ∃ m ∈ normalizer ((pull φ (antiUnipotent K) ⊔ zpowers t : Subgroup G) : Set G),
      x = m⁻¹ * t * m} = {x | ∃ z ∈ pull φ (antiUnipotentCenter K), x = t * z}

namespace FCHyp

section Construction

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {TG : Subgroup G} {t : G}

theorem of_setup (hS : Setup L K n φ TG t) (hO : CFSG.oddCore G = ⊥)
    (hLn : ¬ L.Normal)
    (hfull : {x : G | ∃ m ∈ normalizer ((pull φ (antiUnipotent K) ⊔ TG : Subgroup G) : Set G),
      x = m⁻¹ * t * m} = {x | ∃ z ∈ pull φ (antiUnipotentCenter K), x = t * z}) :
    TG = zpowers t ∧ FCHyp L K n φ t := by
  have hT := hS.T_eq_zpowers hO hLn
  obtain ⟨-, -, -, h4, -⟩ := hS.orbits hO hLn
  refine ⟨hT, ?_⟩
  subst hT
  refine ⟨hS, hS.conj_not_mem_L hO hLn, fun g hg => ?_, fun Z h1 h2 h3 => h4 Z h1 h2 h3, hfull⟩
  rcases hS.conj_axis hO hLn (inv_mem hg) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · have : g * x * g⁻¹ ∈ (pull φ (axisOne K)).map (MulAut.conj g⁻¹⁻¹).toMonoidHom :=
        ⟨x, hx, by simp⟩
      rwa [h1] at this
    · have : g * x * g⁻¹ ∈ (pull φ (axisTwo K)).map (MulAut.conj g⁻¹⁻¹).toMonoidHom :=
        ⟨x, hx, by simp⟩
      rwa [h2] at this
  · right
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · have : g * x * g⁻¹ ∈ (pull φ (axisOne K)).map (MulAut.conj g⁻¹⁻¹).toMonoidHom :=
        ⟨x, hx, by simp⟩
      rwa [h1] at this
    · have : g * x * g⁻¹ ∈ (pull φ (axisTwo K)).map (MulAut.conj g⁻¹⁻¹).toMonoidHom :=
        ⟨x, hx, by simp⟩
      rwa [h2] at this

end Construction

section Basic

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  {n : ℕ} {φ : L ≃* antiSp K} {t : G}

local notation "𝐐" => (pull φ (antiUnipotent K) ⊔ zpowers t : Subgroup G)
local notation "𝐁[" i "]" => (zpowers t ⊔ pull φ (rootA K i) : Subgroup G)
local notation "𝐔[" i "]" => pull φ (rootU K i)
set_option quotPrecheck false in
local notation "𝐂" => centralizer ({t} : Set G)

theorem twoCore (h : FCHyp L K n φ t) : TwoCoreSetup L K n t where
  two_le := h.setup.two_le
  card_K := h.setup.card_K
  t_mul_t := h.setup.t_mul_t
  L_le := h.setup.L_le
  cent_le := h.setup.cent_le
  cent_inf := h.setup.cent_inf
  not_conj := h.not_conj

theorem four_le_card (h : FCHyp L K n φ t) : 4 ≤ Nat.card K := by
  rw [h.setup.card_K]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h.setup.two_le

theorem B_mul_self (h : FCHyp L K n φ t) (i : Axis) {x : G} (hx : x ∈ 𝐁[i]) : x * x = 1 := by
  have hA : ∀ a ∈ pull φ (rootA K i), a * a = 1 := by
    intro a ha
    obtain ⟨haL, haA⟩ := mem_pull.mp ha
    have h1 := rootA_mul_self i haA
    rw [← map_mul, φ.map_eq_one_iff] at h1
    exact congrArg Subtype.val h1
  rcases (mem_zpowers_sup_iff h.setup.t_mul_t (TwoCoreSetup.comm_pull φ h.twoCore)).mp hx with
    hx | hx
  · exact hA x hx
  · obtain ⟨a, ha, rfl⟩ : ∃ a ∈ pull φ (rootA K i), x = t * a :=
      ⟨t * x, hx, by rw [← mul_assoc, h.setup.t_mul_t, one_mul]⟩
    have hc : t * a = a * t := h.twoCore.comm (pull_le φ _ ha)
    calc t * a * (t * a) = t * (a * t) * a := by group
      _ = t * (t * a) * a := by rw [← hc]
      _ = (t * t) * (a * a) := by group
      _ = 1 := by rw [h.setup.t_mul_t, hA _ ha, one_mul]

theorem B_comm (h : FCHyp L K n φ t) (i : Axis) {x y : G} (hx : x ∈ 𝐁[i]) (hy : y ∈ 𝐁[i]) :
    x * y = y * x := by
  have hA : ∀ a ∈ pull φ (rootA K i), ∀ b ∈ pull φ (rootA K i), a * b = b * a := by
    intro a ha b hb
    obtain ⟨haL, haA⟩ := mem_pull.mp ha
    obtain ⟨hbL, hbA⟩ := mem_pull.mp hb
    have h1 := rootA_comm i haA hbA
    rw [← map_mul, ← map_mul] at h1
    exact congrArg Subtype.val (φ.injective h1)
  have hc : ∀ y ∈ zpowers t, ∀ a ∈ pull φ (rootA K i), y * a = a * y :=
    fun y hy a ha => h.twoCore.zpowers_comm hy (pull_le φ _ ha)
  obtain ⟨τ, hτ, a, ha, rfl⟩ := (mem_sup_of_commute hc).mp hx
  obtain ⟨τ', hτ', b, hb, rfl⟩ := (mem_sup_of_commute hc).mp hy
  have h1 : Commute τ τ' := by
    obtain ⟨j, rfl⟩ := hτ
    obtain ⟨j', rfl⟩ := hτ'
    exact Commute.zpow_zpow_self t j j'
  exact (Commute.mul_left (Commute.mul_right h1 (hc τ hτ b hb))
    (Commute.mul_right (hc τ' hτ' a ha).symm (hA a ha b hb))).eq

theorem B_le_Q (i : Axis) : 𝐁[i] ≤ 𝐐 :=
  sup_le le_sup_right ((pull_mono φ (rootA_le_antiUnipotent i)).trans le_sup_left)

theorem card_B [Finite G] [Finite K] (h : FCHyp L K n φ t) (i : Axis) :
    Nat.card 𝐁[i] = 2 * Nat.card K ^ 3 := by
  rw [card_sup_of_commute (fun y hy a ha => h.twoCore.zpowers_comm hy (pull_le φ _ ha))
    (h.twoCore.zpowers_inf (pull_le φ _)), Nat.card_zpowers, h.setup.order_t, card_pull,
    card_rootA]

theorem card_U (i : Axis) : Nat.card 𝐔[i] = Nat.card K := by
  rw [card_pull, card_rootU]

theorem card_ZP [Finite K] : Nat.card (pull φ (antiUnipotentCenter K)) = Nat.card K ^ 2 := by
  rw [card_pull, (card_radicals (K := K)).2.2.2]

theorem mem_B_of_sq (h : FCHyp L K n φ t) {x : G} (hxQ : x ∈ 𝐐) (hxx : x * x = 1) :
    x ∈ 𝐁[Axis.one] ∨ x ∈ 𝐁[Axis.two] := by
  obtain ⟨p, hp, c, hc, rfl⟩ := h.setup.mem_Q.mp hxQ
  have hpc : p * c = c * p := h.setup.comm_P_T hp hc
  have hcc : c * c = 1 := by
    obtain ⟨j, rfl⟩ := hc
    show t ^ j * t ^ j = 1
    rcases zpow_eq_one_or_eq h.setup.t_mul_t j with h1 | h1 <;> rw [h1]
    · rw [one_mul]
    · exact h.setup.t_mul_t
  have hpp : p * p = 1 := by
    calc p * p = p * p * (c * c) := by rw [hcc, mul_one]
      _ = p * c * (p * c) := by rw [mul_assoc p c, ← mul_assoc c p, ← hpc]; group
      _ = 1 := hxx
  obtain ⟨hpL, hpU⟩ := mem_pull.mp hp
  have hφp : φ ⟨p, hpL⟩ * φ ⟨p, hpL⟩ = 1 := by
    rw [← map_mul, φ.map_eq_one_iff]
    exact Subtype.ext hpp
  rcases (mul_self_eq_one_iff hpU).mp hφp with h1 | h1
  · exact Or.inl (mul_mem (mem_sup_right (mem_pull.mpr ⟨hpL, h1⟩)) (mem_sup_left hc))
  · exact Or.inr (mul_mem (mem_sup_right (mem_pull.mpr ⟨hpL, h1⟩)) (mem_sup_left hc))

theorem B_ne (h : FCHyp L K n φ t) : 𝐁[Axis.one] ≠ 𝐁[Axis.two] := by
  intro heq
  obtain ⟨h1, h2⟩ := uElt_mem_radA1_not_mem_radA2 (K := K)
  have hx : ((φ.symm (uElt 0 0 0 1) : L) : G) ∈ 𝐁[Axis.one] :=
    mem_sup_right (symm_mem_pull.mpr h1)
  rw [heq] at hx
  have hx' : ((φ.symm (uElt 0 0 0 1) : L) : G) ∈ 𝐁[Axis.two] ⊓ L := ⟨hx, (φ.symm _).2⟩
  rw [zpowers_sup_inf_eq h.setup.t_mul_t (pull_le φ _) h.twoCore.t_not_mem
    (TwoCoreSetup.comm_pull φ h.twoCore)] at hx'
  exact h2 (symm_mem_pull.mp hx')

theorem map_B [Finite G] [Finite K] (h : FCHyp L K n φ t) {g : G}
    (hg : g ∈ normalizer (𝐐 : Set G)) (j : Axis) :
    (𝐁[j]).map (MulAut.conj g).toMonoidHom = 𝐁[Axis.one] ∨
      (𝐁[j]).map (MulAut.conj g).toMonoidHom = 𝐁[Axis.two] := by
  have hsub : ∀ y ∈ (𝐁[j]).map (MulAut.conj g).toMonoidHom,
      y ∈ 𝐁[Axis.one] ∨ y ∈ 𝐁[Axis.two] := by
    rintro _ ⟨x, hx, rfl⟩
    have hxx := h.B_mul_self j hx
    refine h.mem_B_of_sq ((mem_normalizer_iff.mp hg x).mp (B_le_Q j hx)) ?_
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
      _ = 1 := by rw [hxx]; group
  have hcard : Nat.card ((𝐁[j]).map (MulAut.conj g).toMonoidHom) = 2 * Nat.card K ^ 3 := by
    rw [card_map_of_injective (MulAut.conj g).injective, h.card_B]
  rcases subgroup_le_of_subset_union hsub with h1 | h1
  · exact Or.inl (eq_of_le_of_card_ge h1 (by rw [hcard, h.card_B]))
  · exact Or.inr (eq_of_le_of_card_ge h1 (by rw [hcard, h.card_B]))

theorem conj_mem_of_map_eq {G : Type*} [Group G] {H H' : Subgroup G} {g : G}
    (e : H.map (MulAut.conj g).toMonoidHom = H') {x : G} (hx : x ∈ H) : g * x * g⁻¹ ∈ H' :=
  e ▸ ⟨x, hx, rfl⟩

theorem conj_B [Finite G] [Finite K] (h : FCHyp L K n φ t) {g : G}
    (hg : g ∈ normalizer (𝐐 : Set G)) :
    (g ∈ normalizer ((𝐁[Axis.one] : Subgroup G) : Set G) ∧
        g ∈ normalizer ((𝐁[Axis.two] : Subgroup G) : Set G)) ∨
      ((∀ x ∈ 𝐁[Axis.one], g * x * g⁻¹ ∈ 𝐁[Axis.two]) ∧
        ∀ x ∈ 𝐁[Axis.two], g * x * g⁻¹ ∈ 𝐁[Axis.one]) := by
  have hinj : ∀ j k : Axis, (𝐁[j]).map (MulAut.conj g).toMonoidHom =
      (𝐁[k]).map (MulAut.conj g).toMonoidHom → 𝐁[j] = 𝐁[k] :=
    fun j k e => map_injective (MulAut.conj g).injective e
  rcases h.map_B hg Axis.one with h1 | h1 <;> rcases h.map_B hg Axis.two with h2 | h2
  · exact absurd (hinj _ _ (h1.trans h2.symm)) h.B_ne
  · exact Or.inl ⟨RootAxisTwoCore.mem_normalizer_of_conj_le fun x hx => conj_mem_of_map_eq h1 hx,
      RootAxisTwoCore.mem_normalizer_of_conj_le fun x hx => conj_mem_of_map_eq h2 hx⟩
  · exact Or.inr ⟨fun x hx => conj_mem_of_map_eq h1 hx, fun x hx => conj_mem_of_map_eq h2 hx⟩
  · exact absurd (hinj _ _ (h1.trans h2.symm)) h.B_ne

theorem mem_normalizer_B_of [Finite G] [Finite K] (h : FCHyp L K n φ t) {g : G}
    (hg : g ∈ normalizer (𝐐 : Set G))
    (i : Axis) (hgi : g ∈ normalizer ((𝐁[i] : Subgroup G) : Set G)) :
    g ∈ normalizer ((𝐁[Axis.one] : Subgroup G) : Set G) ∧
      g ∈ normalizer ((𝐁[Axis.two] : Subgroup G) : Set G) := by
  rcases h.conj_B hg with hfx | ⟨h1, h2⟩
  · exact hfx
  · exfalso
    apply h.B_ne
    have hle : ∀ j k : Axis, (∀ x ∈ 𝐁[j], g * x * g⁻¹ ∈ 𝐁[k]) →
        g ∈ normalizer ((𝐁[j] : Subgroup G) : Set G) → 𝐁[j] = 𝐁[k] := by
      intro j k hjk hgj
      refine eq_of_le_of_card_ge (fun x hx => ?_) (by rw [h.card_B, h.card_B])
      have hx' : g⁻¹ * x * g ∈ 𝐁[j] := (mem_normalizer_iff''.mp hgj x).mp hx
      have := hjk _ hx'
      rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at this
    cases i
    · exact hle _ _ h1 hgi
    · exact (hle _ _ h2 hgi).symm

theorem conj_U [Finite G] (h : FCHyp L K n φ t) {g : G} (hg : g ∈ normalizer (𝐐 : Set G)) :
    (g ∈ normalizer ((𝐔[Axis.one] : Subgroup G) : Set G) ∧
        g ∈ normalizer ((𝐔[Axis.two] : Subgroup G) : Set G)) ∨
      ((∀ x ∈ 𝐔[Axis.one], g * x * g⁻¹ ∈ 𝐔[Axis.two]) ∧
        ∀ x ∈ 𝐔[Axis.two], g * x * g⁻¹ ∈ 𝐔[Axis.one]) := by
  rcases h.conj_axis g hg with ⟨h1, h2⟩ | h12
  · exact Or.inl ⟨RootAxisTwoCore.mem_normalizer_of_conj_le h1,
      RootAxisTwoCore.mem_normalizer_of_conj_le h2⟩
  · exact Or.inr h12

end Basic

section Orbits

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G}

local notation "𝐐" => (pull φ (antiUnipotent K) ⊔ zpowers t : Subgroup G)
local notation "𝐙" => pull φ (antiUnipotentCenter K)
local notation "𝐉" => pull φ (diagTorus K)
local notation "𝐁[" i "]" => (zpowers t ⊔ pull φ (rootA K i) : Subgroup G)
local notation "𝐔[" i "]" => pull φ (rootU K i)
local notation "𝐕[" i "]" => (zpowers t ⊔ pull φ (rootU K i) : Subgroup G)
local notation "𝐘" => normalizer ((pull φ (antiUnipotent K) ⊔ zpowers t : Subgroup G) : Set G) ⊓
  normalizer (((zpowers t ⊔ pull φ (rootA K Axis.one) : Subgroup G) : Subgroup G) : Set G) ⊓
  normalizer (((zpowers t ⊔ pull φ (rootA K Axis.two) : Subgroup G) : Subgroup G) : Set G)
set_option quotPrecheck false in
local notation "𝐂" => centralizer ({t} : Set G)

omit [Finite G] [Finite K] in
theorem torus_le_C (h : FCHyp L K n φ t) : 𝐉 ≤ 𝐂 :=
  (pull_le φ _).trans h.setup.L_le

omit [Finite K] in
theorem torus_le_normalizer_A (i : Axis) : 𝐉 ≤ normalizer (pull φ (rootA K i) : Set G) :=
  torus_le_normalizer_pull fun _ hδ _ hz => diagTorus_conj_mem_rootA hδ i hz

omit [Finite K] in
theorem torus_le_normalizer_U (i : Axis) : 𝐉 ≤ normalizer (𝐔[i] : Set G) :=
  torus_le_normalizer_pull fun _ hδ _ hz => diagTorus_conj_mem_rootU hδ i hz

omit [Finite K] in
theorem torus_le_N (h : FCHyp L K n φ t) (i : Axis) :
    𝐉 ≤ normalizer ((𝐁[i] : Subgroup G) : Set G) := fun _ hd =>
  (h.twoCore.mem_normalizer_zpowers_sup_iff (h.torus_le_C hd) (pull_le φ _)).mpr
    (torus_le_normalizer_A i hd)

omit [Finite K] in
theorem torus_le_M (h : FCHyp L K n φ t) (i : Axis) :
    𝐉 ≤ normalizer ((𝐕[i] : Subgroup G) : Set G) := fun _ hd =>
  (h.twoCore.mem_normalizer_zpowers_sup_iff (h.torus_le_C hd) (pull_le φ _)).mpr
    (torus_le_normalizer_U i hd)

omit [Finite K] in
theorem torus_le_Y (h : FCHyp L K n φ t) : 𝐉 ≤ 𝐘 := fun _ hd =>
  ⟨⟨h.setup.diagTorus_le_normalizer hd, h.torus_le_N Axis.one hd⟩, h.torus_le_N Axis.two hd⟩

theorem Y_index (h : FCHyp L K n φ t) :
    ∃ a ∈ normalizer (𝐐 : Set G), ∀ b ∈ normalizer (𝐐 : Set G), b * a ∈ 𝐘 ∨ b ∈ 𝐘 :=
  exists_index_two fun _ hg => h.conj_B hg

theorem relIndex_Y (h : FCHyp L K n φ t) : 𝐘.relIndex (normalizer (𝐐 : Set G)) ≤ 2 :=
  relIndex_le_two h.Y_index

theorem orbit_eq_of_index_two (h : FCHyp L K n φ t) {Z N : Subgroup G} (hJZ : 𝐉 ≤ Z)
    (hZN : Z ≤ N) (hNQ : N ≤ normalizer (𝐐 : Set G))
    (hN : {x : G | ∃ m ∈ N, x = m⁻¹ * t * m} = {x | ∃ z ∈ 𝐙, x = t * z})
    (hidx : ∃ a ∈ N, ∀ b ∈ N, b * a ∈ Z ∨ b ∈ Z) :
    {x : G | ∃ m ∈ Z, x = m⁻¹ * t * m} = {x | ∃ z ∈ 𝐙, x = t * z} := by
  by_contra hne
  obtain ⟨j, hj⟩ : ∃ j : Axis,
      {x : G | ∃ m ∈ Z, x = m⁻¹ * t * m} ⊆ {x | ∃ u ∈ 𝐔[j], x = t * u} := by
    by_cases hZC : Z ≤ 𝐂
    · refine ⟨Axis.one, ?_⟩
      rintro _ ⟨m, hm, rfl⟩
      refine ⟨1, one_mem _, ?_⟩
      rw [mul_one, mul_assoc, ← mem_centralizer_singleton_iff.mp (hZC hm), inv_mul_cancel_left]
    · rcases h.orbit_shapes Z hJZ (hZN.trans hNQ) hZC with h1 | h1 | h1
      · exact ⟨Axis.one, h1.le⟩
      · exact ⟨Axis.two, h1.le⟩
      · exact absurd h1 hne
  obtain ⟨a, -, hab⟩ := hidx
  have hsubN : {x : G | ∃ m ∈ N, x = m⁻¹ * t * m} ⊆ {x : G | ∃ m ∈ Z, x = m⁻¹ * t * m} ∪
      (fun x => a * x * a⁻¹) '' {x : G | ∃ m ∈ Z, x = m⁻¹ * t * m} := by
    rintro _ ⟨b, hb, rfl⟩
    rcases hab b hb with h1 | h1
    · right
      exact ⟨(b * a)⁻¹ * t * (b * a), ⟨b * a, h1, rfl⟩, by simp only; group⟩
    · exact Or.inl ⟨b, h1, rfl⟩
  have hZ : {x : G | ∃ m ∈ Z, x = m⁻¹ * t * m}.ncard ≤ Nat.card K := by
    calc _ ≤ {x : G | ∃ u ∈ 𝐔[j], x = t * u}.ncard := Set.ncard_le_ncard hj
      _ = Nat.card K := by rw [← Nat.card_coe_set_eq, card_mul_set, card_U]
  have h1 : {x : G | ∃ m ∈ N, x = m⁻¹ * t * m}.ncard ≤ 2 * Nat.card K := by
    calc _ ≤ _ := Set.ncard_le_ncard hsubN
      _ ≤ _ := Set.ncard_union_le _ _
      _ ≤ Nat.card K + Nat.card K := add_le_add hZ (le_trans Set.ncard_image_le hZ)
      _ = 2 * Nat.card K := by ring
  have h2 : {x : G | ∃ m ∈ N, x = m⁻¹ * t * m}.ncard = Nat.card K ^ 2 := by
    rw [hN, ← Nat.card_coe_set_eq, card_mul_set, card_ZP]
  have h4 := h.four_le_card
  rw [h2] at h1
  nlinarith

theorem orbit_Y (h : FCHyp L K n φ t) :
    {x : G | ∃ m ∈ 𝐘, x = m⁻¹ * t * m} = {x | ∃ z ∈ 𝐙, x = t * z} :=
  h.orbit_eq_of_index_two h.torus_le_Y (inf_le_left.trans inf_le_left) le_rfl h.full h.Y_index

theorem Y_le_normalizer_U (h : FCHyp L K n φ t) {y : G} (hy : y ∈ 𝐘) :
    y ∈ normalizer (𝐔[Axis.one] : Set G) ∧ y ∈ normalizer (𝐔[Axis.two] : Set G) := by
  set Y' := 𝐘 ⊓ normalizer (𝐔[Axis.one] : Set G) ⊓ normalizer (𝐔[Axis.two] : Set G) with hY'
  have hJ : 𝐉 ≤ Y' := fun d hd =>
    ⟨⟨h.torus_le_Y hd, torus_le_normalizer_U Axis.one hd⟩, torus_le_normalizer_U Axis.two hd⟩
  have hidx : ∃ a ∈ 𝐘, ∀ b ∈ 𝐘, b * a ∈ Y' ∨ b ∈ Y' :=
    exists_index_two fun g hg => h.conj_U hg.1.1
  have hY'orb := h.orbit_eq_of_index_two hJ (inf_le_left.trans inf_le_left)
    (inf_le_left.trans inf_le_left) h.orbit_Y hidx
  have hmem : y⁻¹ * t * y ∈ {x : G | ∃ m ∈ Y', x = m⁻¹ * t * m} := by
    rw [hY'orb, ← h.orbit_Y]
    exact ⟨y, hy, rfl⟩
  obtain ⟨y', hy', hyy'⟩ := hmem
  have hcC : y * y'⁻¹ ∈ 𝐂 := by
    rw [mem_centralizer_singleton_iff]
    calc y * y'⁻¹ * t = y * (y'⁻¹ * t * y') * y'⁻¹ := by group
      _ = y * (y⁻¹ * t * y) * y'⁻¹ := by rw [hyy']
      _ = t * (y * y'⁻¹) := by group
  have hcU : ∀ i : Axis, y * y'⁻¹ ∈ normalizer ((𝐁[i] : Subgroup G) : Set G) →
      y * y'⁻¹ ∈ normalizer (𝐔[i] : Set G) := by
    intro i hci
    have h1 : y * y'⁻¹ ∈ 𝐂 ⊓ normalizer ((𝐕[i] : Subgroup G) : Set G) := by
      rw [h.twoCore.inf_normalizer_eq φ i]
      exact ⟨hcC, hci⟩
    exact (h.twoCore.mem_normalizer_zpowers_sup_iff hcC (pull_le φ _)).mp h1.2
  have hc1 := hcU Axis.one (mul_mem hy.1.2 (inv_mem hy'.1.1.1.2))
  have hc2 := hcU Axis.two (mul_mem hy.2 (inv_mem hy'.1.1.2))
  have e : y = y * y'⁻¹ * y' := by group
  rw [e]
  exact ⟨mul_mem hc1 hy'.1.2, mul_mem hc2 hy'.2⟩

omit [Finite K] in
theorem mem_M_of {i : Axis} {g : G} (hgU : g ∈ normalizer (𝐔[i] : Set G)) {u : G}
    (hu : u ∈ 𝐔[i]) (hgt : g⁻¹ * t * g = t * u) :
    g ∈ normalizer ((𝐕[i] : Subgroup G) : Set G) := by
  rw [← inv_mem_iff]
  refine mem_normalizer_zpowers_sup ?_ fun w hw => ?_
  · rw [inv_inv, hgt]
    exact mul_mem (mem_sup_left (mem_zpowers t)) (mem_sup_right hu)
  · rw [inv_inv]
    exact (mem_normalizer_iff''.mp hgU w).mp hw

theorem M_not_le_C (h : FCHyp L K n φ t) (i : Axis) :
    ¬ normalizer ((𝐕[i] : Subgroup G) : Set G) ≤ 𝐂 := by
  intro hle
  have hu := coordG_mem φ i 1
  have huZ : coordG φ i 1 ∈ 𝐙 := pull_mono φ (rootU_le_center i) hu
  have hmem : t * coordG φ i 1 ∈ {x : G | ∃ m ∈ 𝐘, x = m⁻¹ * t * m} := by
    rw [h.orbit_Y]
    exact ⟨_, huZ, rfl⟩
  obtain ⟨y, hy, hyt⟩ := hmem
  have hyU : y ∈ normalizer (𝐔[i] : Set G) := by
    cases i
    · exact (h.Y_le_normalizer_U hy).1
    · exact (h.Y_le_normalizer_U hy).2
  have hyC := hle (mem_M_of hyU hu hyt.symm)
  have h1 : y⁻¹ * t * y = t := by
    rw [mul_assoc, ← mem_centralizer_singleton_iff.mp hyC, inv_mul_cancel_left]
  rw [h1] at hyt
  have h2 : coordG φ i 1 = coordG φ i 0 := by
    rw [coordG_zero]
    exact mul_left_cancel (hyt.trans (mul_one t).symm)
  exact one_ne_zero (coordG_injective φ i h2)

theorem orbit_M (h : FCHyp L K n φ t) (i : Axis) :
    {x : G | ∃ m ∈ normalizer ((𝐕[i] : Subgroup G) : Set G), x = m⁻¹ * t * m} =
      {x | ∃ u ∈ 𝐔[i], x = t * u} := by
  ext x
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨_, h.twoCore.conj_t_mem φ i hm, by rw [← mul_assoc, h.setup.t_mul_t, one_mul]⟩
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨m, hm, hmu⟩ := h.twoCore.exists_conj_eq φ i (h.M_not_le_C i) hu
    exact ⟨m, hm, hmu.symm⟩

theorem M_le_normalizer_U (h : FCHyp L K n φ t) (i : Axis) :
    normalizer ((𝐕[i] : Subgroup G) : Set G) ≤ normalizer (𝐔[i] : Set G) := fun _ hg =>
  RootAxisTwoCore.mem_normalizer_of_conj_le fun _ hu =>
    h.twoCore.conj_mem_U φ i (h.M_not_le_C i) hg hu

end Orbits

section Radical

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G}

local notation "𝐐" => (pull φ (antiUnipotent K) ⊔ zpowers t : Subgroup G)
local notation "𝐙" => pull φ (antiUnipotentCenter K)
local notation "𝐁[" i "]" => (zpowers t ⊔ pull φ (rootA K i) : Subgroup G)
local notation "𝐀[" i "]" => pull φ (rootA K i)
local notation "𝐔[" i "]" => pull φ (rootU K i)
local notation "𝐕[" i "]" => (zpowers t ⊔ pull φ (rootU K i) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐃[" i "]" => (CFSG.pCore 2 (normalizer
  (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Subgroup G) : Set G))).map
  (normalizer (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐂" => centralizer ({t} : Set G)

theorem symm_s_mem (h : FCHyp L K n φ t) (i : Axis) (M : SL₂ K) :
    ((φ.symm (sHom K i M) : L) : G) ∈ 𝐂 ∧
      ((φ.symm (sHom K i M) : L) : G) ∈ normalizer (𝐀[i] : Set G) ∧
      ((φ.symm (sHom K i M) : L) : G) ∈ normalizer (𝐔[i] : Set G) ∧
      ((φ.symm (sHom K i M) : L) : G) ∈ normalizer ((𝐁[i] : Subgroup G) : Set G) := by
  have hcC : ((φ.symm (sHom K i M) : L) : G) ∈ 𝐂 := h.setup.L_le (φ.symm _).2
  have hcA : ((φ.symm (sHom K i M) : L) : G) ∈ normalizer (𝐀[i] : Set G) :=
    RootAxisTwoCore.mem_normalizer_of_conj_le fun a ha => (psiG_conj_s h.twoCore φ i M ha).1
  have hcU : ((φ.symm (sHom K i M) : L) : G) ∈ normalizer (𝐔[i] : Set G) := by
    refine RootAxisTwoCore.mem_normalizer_of_conj_le fun u hu => ?_
    obtain ⟨-, hc⟩ := (TwoCoreSetup.mem_pull_rootC_iff φ i).mp (symm_s_mem_rootC h.twoCore φ i M)
    rw [← hc u hu, mul_inv_cancel_right]
    exact hu
  exact ⟨hcC, hcA, hcU,
    (h.twoCore.mem_normalizer_zpowers_sup_iff hcC (pull_le φ _)).mpr hcA⟩

theorem exists_conj_eq_t_mul (h : FCHyp L K n φ t) (i : Axis) {a : G} (ha : a ∈ 𝐀[i]) :
    ∃ x ∈ normalizer ((𝐁[i] : Subgroup G) : Set G) ⊓ normalizer (𝐔[i] : Set G),
      x⁻¹ * t * x = t * a := by
  have hM := h.M_not_le_C i
  have hMN : normalizer ((𝐕[i] : Subgroup G) : Set G) ≤ normalizer ((𝐁[i] : Subgroup G) : Set G) :=
    h.twoCore.M_le_normalizer_B φ i
  have hMU := h.M_le_normalizer_U i
  have hfib : ∀ x ∈ normalizer ((𝐁[i] : Subgroup G) : Set G) ⊓ normalizer (𝐔[i] : Set G),
      ∀ u ∈ 𝐔[i], x⁻¹ * t * x = t * (a * u) →
      ∃ x' ∈ normalizer ((𝐁[i] : Subgroup G) : Set G) ⊓ normalizer (𝐔[i] : Set G),
        x'⁻¹ * t * x' = t * a := by
    intro x hx u hu hxt
    have hu' : x * u⁻¹ * x⁻¹ ∈ 𝐔[i] := (mem_normalizer_iff.mp hx.2 _).mp (inv_mem hu)
    obtain ⟨m, hm, hmt⟩ := h.twoCore.exists_conj_eq φ i hM hu'
    refine ⟨m * x, mul_mem ⟨hMN hm, hMU hm⟩ hx, ?_⟩
    calc (m * x)⁻¹ * t * (m * x) = x⁻¹ * (m⁻¹ * t * m) * x := by group
      _ = x⁻¹ * (t * (x * u⁻¹ * x⁻¹)) * x := by rw [hmt]
      _ = (x⁻¹ * t * x) * u⁻¹ := by group
      _ = t * a := by rw [hxt]; group
  by_cases ha0 : psiG φ i a = 0
  · have haU := (psiG_eq_zero_iff h.twoCore φ i ha).mp ha0
    exact hfib 1 (one_mem _) a⁻¹ (inv_mem haU) (by group)
  · obtain ⟨z₀, hz₀, hvz₀⟩ := exists_center_vecOf (K := K) i
    have hwZ : ((φ.symm z₀ : L) : G) ∈ 𝐙 := symm_mem_pull.mpr hz₀
    have hwA : ((φ.symm z₀ : L) : G) ∈ 𝐀[i] := pull_mono φ (center_le_rootA i) hwZ
    have hψw : psiG φ i ((φ.symm z₀ : L) : G) = ![1, 0] := by rw [psiG_symm]; exact hvz₀
    have hmem : t * ((φ.symm z₀ : L) : G) ∈ {x : G | ∃ m ∈ normalizer (𝐐 : Set G) ⊓
        normalizer (((zpowers t ⊔ pull φ (rootA K Axis.one) : Subgroup G) : Subgroup G) : Set G) ⊓
        normalizer (((zpowers t ⊔ pull φ (rootA K Axis.two) : Subgroup G) : Subgroup G) : Set G),
        x = m⁻¹ * t * m} := by
      rw [h.orbit_Y]
      exact ⟨_, hwZ, rfl⟩
    obtain ⟨y, hy, hyt⟩ := hmem
    have hyX : y ∈ normalizer ((𝐁[i] : Subgroup G) : Set G) ⊓ normalizer (𝐔[i] : Set G) := by
      cases i
      · exact ⟨hy.1.2, (h.Y_le_normalizer_U hy).1⟩
      · exact ⟨hy.2, (h.Y_le_normalizer_U hy).2⟩
    have hne : (![1, 0] : Fin 2 → K) ≠ 0 := by
      intro h0
      have := congrFun h0 0
      simp at this
    obtain ⟨M, hM'⟩ := exists_sl2_mulVec_eq hne ha0
    obtain ⟨hcC, -, hcU, hcN⟩ := h.symm_s_mem i M
    set c : G := ((φ.symm (sHom K i M) : L) : G) with hc
    obtain ⟨hcwA, hcw⟩ := psiG_conj_s h.twoCore φ i M hwA
    rw [← hc, hψw, hM'] at hcw
    rw [← hc] at hcwA
    have hu : a⁻¹ * (c * ((φ.symm z₀ : L) : G) * c⁻¹) ∈ 𝐔[i] :=
      (psiG_eq_iff h.twoCore φ i ha hcwA).mp hcw.symm
    refine hfib (y * c⁻¹) (mul_mem hyX (mem_inf.mpr ⟨inv_mem hcN, inv_mem hcU⟩)) _ hu ?_
    have hct : c * t = t * c := mem_centralizer_singleton_iff.mp hcC
    calc (y * c⁻¹)⁻¹ * t * (y * c⁻¹) = c * (y⁻¹ * t * y) * c⁻¹ := by group
      _ = c * (t * ((φ.symm z₀ : L) : G)) * c⁻¹ := by rw [← hyt]
      _ = (c * t) * ((φ.symm z₀ : L) : G) * c⁻¹ := by group
      _ = t * (c * ((φ.symm z₀ : L) : G) * c⁻¹) := by rw [hct]; group
      _ = t * (a * (a⁻¹ * (c * ((φ.symm z₀ : L) : G) * c⁻¹))) := by group

omit [Finite G] [Finite K] in
theorem conj_t_mem_tA (h : FCHyp L K n φ t) (i : Axis) {x : G} (hxB : x ∈ 𝐁[i])
    (hx : ∃ g : G, x = g⁻¹ * t * g) : t * x ∈ 𝐀[i] := by
  rcases (mem_zpowers_sup_iff h.setup.t_mul_t (TwoCoreSetup.comm_pull φ h.twoCore)).mp hxB with
    h1 | h1
  · obtain ⟨g, rfl⟩ := hx
    exact absurd (pull_le φ _ h1) (h.not_conj g)
  · exact h1

theorem orbit_N (h : FCHyp L K n φ t) (i : Axis) :
    {x : G | ∃ g ∈ normalizer ((𝐁[i] : Subgroup G) : Set G), x = g⁻¹ * t * g} =
      {x | ∃ a ∈ 𝐀[i], x = t * a} := by
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    have hxB : g⁻¹ * t * g ∈ 𝐁[i] :=
      (mem_normalizer_iff''.mp hg t).mp (mem_sup_left (mem_zpowers t))
    exact ⟨_, h.conj_t_mem_tA i hxB ⟨g, rfl⟩, by rw [← mul_assoc, h.setup.t_mul_t, one_mul]⟩
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨g, hg, hgt⟩ := h.exists_conj_eq_t_mul i ha
    exact ⟨g, hg.1, hgt.symm⟩

theorem orbit_N_eq_inter (h : FCHyp L K n φ t) (i : Axis) :
    {x : G | ∃ g ∈ normalizer ((𝐁[i] : Subgroup G) : Set G), x = g⁻¹ * t * g} =
      {x : G | (∃ g : G, x = g⁻¹ * t * g) ∧ x ∈ 𝐁[i]} := by
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, rfl⟩, (mem_normalizer_iff''.mp hg t).mp (mem_sup_left (mem_zpowers t))⟩
  · rintro ⟨hx, hxB⟩
    rw [h.orbit_N i]
    exact ⟨_, h.conj_t_mem_tA i hxB hx, by rw [← mul_assoc, h.setup.t_mul_t, one_mul]⟩

theorem N_le_normalizer_U (h : FCHyp L K n φ t) (i : Axis) :
    normalizer ((𝐁[i] : Subgroup G) : Set G) ≤ normalizer (𝐔[i] : Set G) := by
  intro g hg
  have hxB : g⁻¹ * t * g ∈ 𝐁[i] :=
    (mem_normalizer_iff''.mp hg t).mp (mem_sup_left (mem_zpowers t))
  obtain ⟨x, hx, hxt⟩ := h.exists_conj_eq_t_mul i (h.conj_t_mem_tA i hxB ⟨g, rfl⟩)
  have hgt : g⁻¹ * t * g = x⁻¹ * t * x := by
    rw [hxt, ← mul_assoc, h.setup.t_mul_t, one_mul]
  have hcC : g * x⁻¹ ∈ 𝐂 := by
    rw [mem_centralizer_singleton_iff]
    calc g * x⁻¹ * t = g * (x⁻¹ * t * x) * x⁻¹ := by group
      _ = g * (g⁻¹ * t * g) * x⁻¹ := by rw [hgt]
      _ = t * (g * x⁻¹) := by group
  have h1 : g * x⁻¹ ∈ 𝐂 ⊓ normalizer ((𝐕[i] : Subgroup G) : Set G) := by
    rw [h.twoCore.inf_normalizer_eq φ i]
    exact mem_inf.mpr ⟨hcC, mul_mem hg (inv_mem hx.1)⟩
  have h2 := (h.twoCore.mem_normalizer_zpowers_sup_iff hcC (pull_le φ _)).mp h1.2
  have e : g = g * x⁻¹ * x := by group
  rw [e]
  exact mul_mem h2 hx.2

theorem N_le_normalizer_A (h : FCHyp L K n φ t) (i : Axis) :
    normalizer ((𝐁[i] : Subgroup G) : Set G) ≤ normalizer (𝐀[i] : Set G) := by
  intro g hg
  refine RootAxisTwoCore.mem_normalizer_of_conj_le fun a ha => ?_
  have hB : g * a * g⁻¹ ∈ 𝐁[i] := (mem_normalizer_iff.mp hg a).mp (mem_sup_right ha)
  rcases (mem_zpowers_sup_iff h.setup.t_mul_t (TwoCoreSetup.comm_pull φ h.twoCore)).mp hB with
    h1 | h1
  · exact h1
  · exfalso
    have hmem : g * a * g⁻¹ ∈ {x : G | ∃ a ∈ 𝐀[i], x = t * a} :=
      ⟨_, h1, by rw [← mul_assoc, h.setup.t_mul_t, one_mul]⟩
    rw [← h.orbit_N i] at hmem
    obtain ⟨k, -, hk⟩ := hmem
    apply h.not_conj (k * g)
    have e : (k * g)⁻¹ * t * (k * g) = a := by
      calc (k * g)⁻¹ * t * (k * g) = g⁻¹ * (k⁻¹ * t * k) * g := by group
        _ = a := by rw [← hk]; group
    rw [e]
    exact pull_le φ _ ha

theorem relIndex_M_N (h : FCHyp L K n φ t) (i : Axis) :
    (normalizer ((𝐕[i] : Subgroup G) : Set G)).relIndex
      (normalizer ((𝐁[i] : Subgroup G) : Set G)) = Nat.card K ^ 2 := by
  have hMN := h.twoCore.M_le_normalizer_B φ i
  have hN : (centralizer ({t} : Set G)).relIndex (normalizer ((𝐁[i] : Subgroup G) : Set G)) =
      Nat.card K ^ 3 := by
    rw [relIndex_centralizer_eq_card, h.orbit_N i, card_mul_set, card_pull, card_rootA]
  have hM : (centralizer ({t} : Set G)).relIndex (normalizer ((𝐕[i] : Subgroup G) : Set G)) =
      Nat.card K := by
    rw [relIndex_centralizer_eq_card, h.orbit_M i, card_mul_set, card_U]
  have key := relIndex_mul_relIndex (𝐂 ⊓ normalizer ((𝐕[i] : Subgroup G) : Set G))
    (normalizer ((𝐕[i] : Subgroup G) : Set G)) (normalizer ((𝐁[i] : Subgroup G) : Set G))
    inf_le_right hMN
  rw [inf_relIndex_right, hM, h.twoCore.inf_normalizer_eq φ i, inf_relIndex_right, hN] at key
  have hq : 0 < Nat.card K := Nat.card_pos
  have : Nat.card K * (normalizer ((𝐕[i] : Subgroup G) : Set G)).relIndex
      (normalizer ((𝐁[i] : Subgroup G) : Set G)) = Nat.card K * Nat.card K ^ 2 := by
    rw [key]; ring
  exact Nat.eq_of_mul_eq_mul_left hq this

omit [Finite G] in
theorem centralizer_B (h : FCHyp L K n φ t) (i : Axis) :
    centralizer ((𝐁[i] : Subgroup G) : Set G) = 𝐁[i] := by
  apply le_antisymm
  · intro g hg
    have hgK : g ∈ centralizer ((𝐕[i] : Subgroup G) : Set G) :=
      centralizer_le (SetLike.coe_subset_coe.mpr
        (sup_le_sup_left (pull_mono φ (rootU_le_rootA i)) _)) hg
    obtain ⟨τ, hτ, c, hc, rfl⟩ := (h.twoCore.mem_K_iff φ i).mp hgK
    obtain ⟨c', hc', rfl⟩ := exists_eq_symm_of_mem_pull hc
    have hcA : ∀ z ∈ rootA K i, c' * z = z * c' := by
      intro z hz
      have h1 := mem_centralizer_iff.mp hg _ (mem_sup_right (symm_mem_pull.mpr hz))
      have hτz : τ * ((φ.symm z : L) : G) = ((φ.symm z : L) : G) * τ :=
        h.twoCore.zpowers_comm hτ (φ.symm z).2
      have h2 : ((φ.symm z : L) : G) * ((φ.symm c' : L) : G) =
          ((φ.symm c' : L) : G) * ((φ.symm z : L) : G) := by
        have e1 : ((φ.symm z : L) : G) * (τ * ((φ.symm c' : L) : G)) =
            τ * (((φ.symm z : L) : G) * ((φ.symm c' : L) : G)) := by
          rw [← mul_assoc, ← hτz, mul_assoc]
        rw [e1, mul_assoc] at h1
        exact mul_left_cancel h1
      have h3 := congrArg φ (Subtype.ext h2 : (φ.symm z) * (φ.symm c') = (φ.symm c') * (φ.symm z))
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h3
      exact h3.symm
    have hst := h.twoCore.axisStr i
    obtain ⟨a, ha, M, rfl⟩ := hst.C_decomp c' hc'
    have hM : M = 1 := by
      apply Matrix.SpecialLinearGroup.ext
      intro p q
      have hmat : (M : Matrix (Fin 2) (Fin 2) K) = 1 := matrix_eq_one_of_mulVec fun v => by
        obtain ⟨z, hz, rfl⟩ := hst.vec_surj v
        have h1 : (a * sHom K i M) * z * (a * sHom K i M)⁻¹ = z := by
          rw [hcA z hz, mul_inv_cancel_right]
        have hsz : sHom K i M * z * (sHom K i M)⁻¹ ∈ rootA K i :=
          hst.A_normal_C _ (hst.s_mem_C M) z hz
        have h2 : a * (sHom K i M * z * (sHom K i M)⁻¹) * a⁻¹ =
            sHom K i M * z * (sHom K i M)⁻¹ := by
          rw [rootA_comm i ha hsz, mul_inv_cancel_right]
        have h3 : sHom K i M * z * (sHom K i M)⁻¹ = z := by
          calc sHom K i M * z * (sHom K i M)⁻¹ = a * (sHom K i M * z * (sHom K i M)⁻¹) * a⁻¹ :=
                h2.symm
            _ = (a * sHom K i M) * z * (a * sHom K i M)⁻¹ := by group
            _ = z := h1
        rw [← hst.vec_conj M z hz, h3]
      rw [hmat]
      rfl
    rw [hM, map_one, mul_one]
    exact mul_mem (mem_sup_left hτ) (mem_sup_right (symm_mem_pull.mpr ha))
  · intro b hb
    exact mem_centralizer_iff.mpr fun y hy => h.B_comm i hy hb

theorem D_inf_C (h : FCHyp L K n φ t) (i : Axis) : 𝐃[i] ⊓ 𝐂 = 𝐁[i] := by
  obtain ⟨-, h2, -, -⟩ := h.twoCore.cond φ i (h.M_not_le_C i)
  rw [← h2]
  ext x
  simp only [mem_inf]
  constructor
  · rintro ⟨hxD, hxC⟩
    exact ⟨hxD, hxC, map_subtype_le _ hxD⟩
  · rintro ⟨hxD, hxC, -⟩
    exact ⟨hxD, hxC⟩

theorem B_le_D (h : FCHyp L K n φ t) (i : Axis) : 𝐁[i] ≤ 𝐃[i] := by
  rw [← h.D_inf_C i]
  exact inf_le_left

theorem quotient_D (h : FCHyp L K n φ t) (i : Axis) :
    ∃ _ : ((𝐁[i]).subgroupOf 𝐃[i]).Normal, ∃ e : (↥𝐃[i] ⧸ (𝐁[i]).subgroupOf 𝐃[i]) ≃* ↥𝐔[i],
      (∀ d : 𝐃[i], (e d : G) = t⁻¹ * ((d : G)⁻¹ * t * d)) ∧
      ∀ h' ∈ 𝐂 ⊓ normalizer ((𝐁[i] : Subgroup G) : Set G), ∀ d : 𝐃[i], ∃ d' : 𝐃[i],
        (d' : G) = h'⁻¹ * d * h' ∧ (e d' : G) = h'⁻¹ * e d * h' := by
  have hMC := h.M_not_le_C i
  obtain ⟨-, h2, h3, h4⟩ := h.twoCore.cond φ i hMC
  have hMB := h.twoCore.M_le_normalizer_B φ i
  have hDM : 𝐃[i] ≤ normalizer ((𝐕[i] : Subgroup G) : Set G) := map_subtype_le _
  have hBD : ((𝐁[i]).subgroupOf 𝐃[i]).Normal := ⟨fun b hb d => mem_subgroupOf.mpr
    ((mem_normalizer_iff.mp (hMB (hDM d.2)) b).mp (mem_subgroupOf.mp hb))⟩
  have hUc : ∀ u ∈ 𝐔[i], ∀ v ∈ 𝐔[i], u * v = v * u := by
    intro u hu v hv
    obtain ⟨x, rfl⟩ := exists_coordG_eq φ i hu
    obtain ⟨y, rfl⟩ := exists_coordG_eq φ i hv
    rw [← coordG_add, ← coordG_add, add_comm]
  have hU : ∀ d ∈ 𝐃[i], t⁻¹ * (d⁻¹ * t * d) ∈ 𝐔[i] := fun d hd => by
    rw [h.twoCore.t_inv]
    exact h.twoCore.conj_t_mem φ i (hDM hd)
  have hker : ∀ d ∈ 𝐃[i], d⁻¹ * t * d = t ↔ d ∈ 𝐁[i] := by
    intro d hd
    rw [← h.D_inf_C i]
    constructor
    · intro e
      refine mem_inf.mpr ⟨hd, ?_⟩
      rw [mem_centralizer_singleton_iff]
      calc d * t = d * (d⁻¹ * t * d) := by rw [e]
        _ = t * d := by group
    · intro hdB
      have hdC := mem_centralizer_singleton_iff.mp (mem_inf.mp hdB).2
      rw [mul_assoc, ← hdC, inv_mul_cancel_left]
  obtain ⟨e, he⟩ := exists_quotient_mulEquiv hU h3 hUc hker h4
  refine ⟨hBD, e, he, fun h' hh d => ?_⟩
  have hh' : h' ∈ 𝐂 ⊓ normalizer ((𝐕[i] : Subgroup G) : Set G) := by
    rw [h.twoCore.inf_normalizer_eq φ i]
    exact hh
  have hd' : h'⁻¹ * d * h' ∈ 𝐃[i] := by
    obtain ⟨p, hp, hpd⟩ := d.2
    refine ⟨⟨h', hh'.2⟩⁻¹ * p * ⟨h', hh'.2⟩, ?_, by rw [← hpd]; rfl⟩
    simpa using CFSG.pCore_normal.conj_mem p hp ⟨h', hh'.2⟩⁻¹
  refine ⟨⟨_, hd'⟩, rfl, ?_⟩
  rw [he, he]
  have e1 : h' * t * h'⁻¹ = t := by
    rw [mem_centralizer_singleton_iff.mp hh'.1, mul_inv_cancel_right]
  have e2 : h' * t⁻¹ * h'⁻¹ = t⁻¹ := by
    calc h' * t⁻¹ * h'⁻¹ = (h' * t * h'⁻¹)⁻¹ := by group
      _ = t⁻¹ := by rw [e1]
  calc t⁻¹ * ((h'⁻¹ * d * h')⁻¹ * t * (h'⁻¹ * d * h'))
      = h'⁻¹ * (h' * t⁻¹ * h'⁻¹) * (d : G)⁻¹ * (h' * t * h'⁻¹) * d * h' := by group
    _ = h'⁻¹ * (t⁻¹ * ((d : G)⁻¹ * t * d)) * h' := by rw [e1, e2]; group

theorem card_D (h : FCHyp L K n φ t) (i : Axis) : Nat.card 𝐃[i] = 2 * Nat.card K ^ 4 := by
  obtain ⟨hBD, e, -, -⟩ := h.quotient_D i
  have h1 := card_eq_card_quotient_mul_card_subgroup ((𝐁[i]).subgroupOf 𝐃[i])
  rw [Nat.card_congr e.toEquiv, card_U,
    Nat.card_congr (subgroupOfEquivOfLe (h.B_le_D i)).toEquiv, h.card_B] at h1
  rw [h1]
  ring

end Radical




end FCHyp

end FullCenter

end CFSG.LocalAnalysis.SymplecticFourStandard
