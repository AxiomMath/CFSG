module

public import CFSG.LocalAnalysis.SteinbergSFFullCenterMutualCommutator
public import CFSG.LocalAnalysis.SteinbergSFFieldInvolutionRepresentative
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection10.lemma_10_12_a
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection10.lemma_10_13_b
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection10.proposition_10_14_d
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection10.theorem_10_1_c
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection10.theorem_10_1_e
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection11.corollary_11_4
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection11.corollary_11_6_b
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection11.theorem_11_7
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection5.theorem_5_5_c_2

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace BothTrivial

open Subgroup GomiFusion RootAxisTwoCore FullCenter FullCenterRadical FullCenterParabolic
  FullCenterTorus FullCenterWeyl FullCenterMutual
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis
open scoped Matrix Pointwise

section Model

variable {K : Type} [Field K] [CharP K 2]

theorem uElt_comm_cases {a b c d a' b' c' d' : K} (ha : a ≠ 0) (hd : d ≠ 0)
    (hc : uElt a b c d * uElt a' b' c' d' = uElt a' b' c' d' * uElt a b c d) :
    (a' = 0 ∧ d' = 0) ∨ (a' = a ∧ d' = d) := by
  rw [uElt_mul, uElt_mul] at hc
  obtain ⟨-, h2, h3, -⟩ := uElt_inj hc
  have e2 : a * d' = a' * d := by linear_combination h2
  have e3 : a * a' * (d' - d) = 0 := by linear_combination h3
  rcases mul_eq_zero.mp e3 with h4 | h4
  · have ha' : a' = 0 := (mul_eq_zero.mp h4).resolve_left ha
    rw [ha', zero_mul] at e2
    exact Or.inl ⟨ha', (mul_eq_zero.mp e2).resolve_left ha⟩
  · have hd' : d' = d := sub_eq_zero.mp h4
    rw [hd'] at e2
    exact Or.inr ⟨(mul_right_cancel₀ hd e2).symm, hd'⟩

open CFSG.QuasithinUnique.Fin257 in
theorem coord_one_of_mem {a b c d x y : K} {r s : Kˣ}
    (hmem : uElt a b c d * (Sp4.dSp r s * uElt y 0 0 0 * (Sp4.dSp r s)⁻¹) * (uElt a b c d)⁻¹ *
      (uElt x 0 0 0)⁻¹ ∈ radA1 K) : (r : K) * ((s⁻¹ : Kˣ) : K) * y = x := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [Sp4.dSp_conj_uElt, uElt_inv, uElt_inv, uElt_mul, uElt_mul, uElt_mul] at hmem
  obtain ⟨b', c', d', h'⟩ := hmem
  have := (uElt_inj h').1
  linear_combination this - (a + x) * h2

open CFSG.QuasithinUnique.Fin257 in
theorem coord_two_of_mem {a b c d x y : K} {r s : Kˣ}
    (hmem : uElt a b c d * (Sp4.dSp r s * uElt 0 0 0 y * (Sp4.dSp r s)⁻¹) * (uElt a b c d)⁻¹ *
      (uElt 0 0 0 x)⁻¹ ∈ radA2 K) : (s : K) ^ 2 * y = x := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [Sp4.dSp_conj_uElt, uElt_inv, uElt_inv, uElt_mul, uElt_mul, uElt_mul] at hmem
  obtain ⟨a', b', c', h'⟩ := hmem
  have := (uElt_inj h').2.2.2
  linear_combination this - (d + x) * h2

end Model

section General

variable {G : Type*} [Group G]

theorem mul_self_mul_of_comm {x y : G} (hxy : x * y = y * x) :
    x * y * (x * y) = x * x * (y * y) := by
  calc x * y * (x * y) = x * (y * x) * y := by group
    _ = x * (x * y) * y := by rw [← hxy]
    _ = x * x * (y * y) := by group

theorem comm_of_mul_self {S : Subgroup G} (h2 : ∀ x ∈ S, x * x = 1) {x y : G} (hx : x ∈ S)
    (hy : y ∈ S) : x * y = y * x := by
  have hxy := inv_eq_of_mul_eq_one_right (h2 _ (mul_mem hx hy))
  rw [← hxy, mul_inv_rev, inv_eq_of_mul_eq_one_right (h2 x hx),
    inv_eq_of_mul_eq_one_right (h2 y hy)]

theorem isElementaryAbelian_of_mul_self {S : Subgroup G} (h2 : ∀ x ∈ S, x * x = 1) :
    IsElementaryAbelian 2 S :=
  isElementaryAbelian_of (fun _ hx _ hy => comm_of_mul_self h2 hx hy) h2

theorem maximal_elem_quotient {Y : Type*} [Group Y] (N : Subgroup Y) [N.Normal]
    {A B : Subgroup Y} (hNA : N ≤ A) (hNB : N ≤ B) (hinv : ∀ y : Y, y * y ∈ N → y ∈ A ∨ y ∈ B)
    (hAc : ∀ a ∈ A, ∀ a' ∈ A, a⁻¹ * (a'⁻¹ * a * a') ∈ N) (hA2 : ∀ a ∈ A, a * a ∈ N)
    (hBc : ∀ b ∈ B, ∀ b' ∈ B, b⁻¹ * (b'⁻¹ * b * b') ∈ N) (hB2 : ∀ b ∈ B, b * b ∈ N)
    (hAB : ¬ A ≤ B) (hBA : ¬ B ≤ A) (S : Subgroup (Y ⧸ N)) :
    Maximal (fun S : Subgroup (Y ⧸ N) => IsElementaryAbelian 2 S) S ↔
      S = A.map (QuotientGroup.mk' N) ∨ S = B.map (QuotientGroup.mk' N) := by
  have elem : ∀ {C : Subgroup Y}, (∀ c ∈ C, ∀ c' ∈ C, c⁻¹ * (c'⁻¹ * c * c') ∈ N) →
      (∀ c ∈ C, c * c ∈ N) → IsElementaryAbelian 2 (C.map (QuotientGroup.mk' N)) := by
    intro C hCc hC2
    refine isElementaryAbelian_of (fun x hx y hy => ?_) (fun x hx => ?_)
    · obtain ⟨c, hc, rfl⟩ := hx
      obtain ⟨c', hc', rfl⟩ := hy
      simp only [QuotientGroup.mk'_apply]
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      have := hCc c' hc' c hc
      rwa [show (c * c')⁻¹ * (c' * c) = c'⁻¹ * (c⁻¹ * c' * c) by group]
    · obtain ⟨c, hc, rfl⟩ := hx
      simp only [QuotientGroup.mk'_apply]
      rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
      exact hC2 c hc
  have hEA := elem hAc hA2
  have hEB := elem hBc hB2
  have dich : ∀ S : Subgroup (Y ⧸ N), IsElementaryAbelian 2 S →
      S ≤ A.map (QuotientGroup.mk' N) ∨ S ≤ B.map (QuotientGroup.mk' N) := by
    intro S hS
    refine subgroup_le_of_subset_union fun x hx => ?_
    have hx2 : x ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian x hx
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    have hy : y * y ∈ N := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, ← pow_two]
      exact hx2
    rcases hinv y hy with h1 | h1
    · exact Or.inl ⟨y, h1, rfl⟩
    · exact Or.inr ⟨y, h1, rfl⟩
  have hnle : ∀ {C D : Subgroup Y}, N ≤ D → ¬ C ≤ D →
      ¬ C.map (QuotientGroup.mk' N) ≤ D.map (QuotientGroup.mk' N) := by
    intro C D hND hCD hle
    obtain ⟨c, hc, hcD⟩ := IsConcreteLE.not_le_iff_exists.mp hCD
    exact hcD ((mem_map_mk'_iff hND c).mp (hle ⟨c, hc, rfl⟩))
  have hAB' := hnle hNB hAB
  have hBA' := hnle hNA hBA
  constructor
  · rintro ⟨hS, hmax⟩
    rcases dich S hS with h1 | h1
    · exact Or.inl (le_antisymm h1 (hmax hEA h1))
    · exact Or.inr (le_antisymm h1 (hmax hEB h1))
  · rintro (rfl | rfl)
    · refine ⟨hEA, fun S' hS' hle => ?_⟩
      rcases dich S' hS' with h1 | h1
      · exact h1
      · exact absurd (hle.trans h1) hAB'
    · refine ⟨hEB, fun S' hS' hle => ?_⟩
      rcases dich S' hS' with h1 | h1
      · exact absurd (hle.trans h1) hBA'
      · exact h1

theorem card_map_mk' {Y : Type*} [Group Y] (N : Subgroup Y) [N.Normal] {A : Subgroup Y}
    (hNA : N ≤ A) : Nat.card (A.map (QuotientGroup.mk' N)) * Nat.card N = Nat.card A := by
  let f : A →* Y ⧸ N := (QuotientGroup.mk' N).comp A.subtype
  have hrange : f.range = A.map (QuotientGroup.mk' N) := by
    rw [MonoidHom.range_comp, range_subtype]
  have hker : f.ker = N.subgroupOf A := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    simp [f, QuotientGroup.eq_one_iff]
  have e1 := card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hrange, hker] at e1
  rw [e1, Nat.card_congr (subgroupOfEquivOfLe hNA).toEquiv]

end General

section Cent

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G}

local notation "𝐏" => pull φ (antiUnipotent K)
local notation "𝐐" => (pull φ (antiUnipotent K) ⊔ zpowers t : Subgroup G)
local notation "𝐙" => pull φ (antiUnipotentCenter K)
local notation "𝐁[" i "]" => (zpowers t ⊔ pull φ (rootA K i) : Subgroup G)
local notation "𝐀[" i "]" => pull φ (rootA K i)
local notation "𝐔[" i "]" => pull φ (rootU K i)
set_option quotPrecheck false in
local notation "𝐃[" i "]" => (CFSG.pCore 2 (normalizer
  (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Subgroup G) : Set G))).map
  (normalizer (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐄[" i "]" => (CFSG.pCore 2 (normalizer
  (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) : Subgroup G) : Set G))).map
  (normalizer (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) : Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐐[" i "]" => (pull φ (antiUnipotent K) ⊔ zpowers t ⊔ 𝐃[i] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐑[" i "]" => (pull φ (antiUnipotent K) ⊔ zpowers t ⊔ 𝐄[i] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐇" => (𝐐[Axis.one] ⊔ 𝐐[Axis.two] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐄₀" => (𝐄[Axis.one] ⊓ 𝐄[Axis.two] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐂" => centralizer ({t} : Set G)
set_option quotPrecheck false in
local notation "𝐅" => closure {x : G | ∃ e ∈ 𝐄₀, ∃ j ∈ pull φ (diagTorus K),
  x = e⁻¹ * (j⁻¹ * e * j)}
local notation "𝐉[" i "]" => pull φ (axisTorus K i)
set_option quotPrecheck false in
local notation "𝐖[" i "]" => (𝐅 ⊓ centralizer (𝐉[i] : Set G) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐊[" i "]" => (𝐀[i] ⊔ (𝐅 ⊓ 𝐃[i]) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐊⋆" => (𝐊[Axis.one] ⊔ 𝐊[Axis.two] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐋[" i "]" => (𝐅 ⊔ 𝐀[i] : Subgroup G)
local notation "𝐰[" i "]" => ((φ.symm (weylElt K i) : L) : G)
set_option quotPrecheck false in
local notation "𝐗[" i "]" => (𝐅 ⊔ 𝐅.map (MulAut.conj 𝐰[i]⁻¹).toMonoidHom : Subgroup G)

theorem F_comm_A (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥)
    (i : Axis) {f : G} (hf : f ∈ 𝐅) {a : G} (ha : a ∈ 𝐀[i]) : f * a = a * f := by
  obtain ⟨w, hw, w', hw', rfl⟩ := exists_W_swap_mul h i hf
  have h1 : w * a = a * w := (A_comm_D h i ha (W_le_Fi h i hw).2).symm
  have h2 : w' * a = a * w' := mem_centralizer_iff.mp
    (commutator_eq_bot_iff_le_centralizer.mp (hbt i) ha) w' (W_le_Fi h i.swap hw')
  exact (Commute.mul_left h1 h2).eq

theorem F_comm_P (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥)
    {f : G} (hf : f ∈ 𝐅) {p : G} (hp : p ∈ 𝐏) : f * p = p * f := by
  have hle : 𝐏 ≤ centralizer ({f} : Set G) := by
    rw [P_eq_A_sup_A]
    exact sup_le (fun a ha => mem_centralizer_singleton_iff.mpr (F_comm_A h hbt _ hf ha).symm)
      (fun a ha => mem_centralizer_singleton_iff.mpr (F_comm_A h hbt _ hf ha).symm)
  exact (mem_centralizer_singleton_iff.mp (hle hp)).symm

theorem F_comm_Ks (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥)
    {f : G} (hf : f ∈ 𝐅) {k : G} (hk : k ∈ 𝐊⋆) : f * k = k * f := by
  have hle : 𝐊⋆ ≤ centralizer ({f} : Set G) := by
    rw [Ks_eq h]
    exact sup_le (fun g hg => mem_centralizer_singleton_iff.mpr (F_comm h hf hg).symm)
      (fun p hp => mem_centralizer_singleton_iff.mpr (F_comm_P h hbt hf hp).symm)
  exact (mem_centralizer_singleton_iff.mp (hle hk)).symm

theorem L_comm (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥)
    (i : Axis) {x y : G} (hx : x ∈ 𝐋[i]) (hy : y ∈ 𝐋[i]) : x * y = y * x := by
  rw [← SetLike.mem_coe, ← L_mul h i] at hx hy
  obtain ⟨f, hf, a, ha, rfl⟩ := hx
  obtain ⟨g, hg, b, hb, rfl⟩ := hy
  have h1 : Commute f g := F_comm h hf hg
  have h2 : Commute f b := F_comm_A h hbt i hf hb
  have h3 : Commute a g := (F_comm_A h hbt i hg ha).symm
  have h4 : Commute a b := A_mul_comm h i ha hb
  exact (Commute.mul_left (Commute.mul_right h1 h2) (Commute.mul_right h3 h4)).eq

omit [Finite G] [Finite K] in
theorem mem_ZP_of_comm {p : G} (hp : p ∈ 𝐏) (hp1 : p ∉ 𝐀[Axis.one]) (hp2 : p ∉ 𝐀[Axis.two])
    {p' : G} (hp' : p' ∈ 𝐏) (hc : p * p' = p' * p) : p' ∈ 𝐙 ∨ p⁻¹ * p' ∈ 𝐙 := by
  obtain ⟨u, ⟨a, b, c, d, rfl⟩, rfl⟩ := exists_eq_symm_of_mem_pull hp
  obtain ⟨u', ⟨a', b', c', d', rfl⟩, rfl⟩ := exists_eq_symm_of_mem_pull hp'
  have ha : a ≠ 0 := fun h0 => hp1 (symm_mem_pull.mpr (by
    show uElt a b c d ∈ radA1 K
    exact ⟨b, c, d, by rw [h0]⟩))
  have hd : d ≠ 0 := fun h0 => hp2 (symm_mem_pull.mpr (by
    show uElt a b c d ∈ radA2 K
    exact ⟨a, b, c, by rw [h0]⟩))
  have hc' : uElt a b c d * uElt a' b' c' d' = uElt a' b' c' d' * uElt a b c d := by
    apply φ.symm.injective
    apply Subtype.ext
    simpa only [map_mul, coe_mul] using hc
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rcases uElt_comm_cases ha hd hc' with ⟨ha', hd'⟩ | ⟨ha', hd'⟩
  · rw [ha', hd']
    exact Or.inl (symm_mem_pull.mpr ⟨b', c', rfl⟩)
  · right
    rw [ha', hd']
    have e : ((φ.symm (uElt a b c d) : L) : G)⁻¹ * ((φ.symm (uElt a b' c' d) : L) : G) =
        ((φ.symm ((uElt a b c d)⁻¹ * uElt a b' c' d) : L) : G) := by
      simp only [map_mul, map_inv, coe_mul, coe_inv]
    rw [e, uElt_inv, uElt_mul]
    refine symm_mem_pull.mpr ⟨b + a * d + b' + a * d, c + c' + a * b' + a * a * d +
      (b + a * d) * a, ?_⟩
    congr 1
    · linear_combination a * h2
    · linear_combination d * h2

theorem mem_F_of_comm (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥)
    {x : G} (hx : x ∈ 𝐊⋆) (hx1 : x ∉ 𝐋[Axis.one]) (hx2 : x ∉ 𝐋[Axis.two]) {y : G}
    (hy : y ∈ 𝐊⋆) (hc : x * y = y * x) : y ∈ 𝐅 ∨ x⁻¹ * y ∈ 𝐅 := by
  rw [← SetLike.mem_coe, ← F_mul_P h] at hx hy
  obtain ⟨f, hf, p, hp, rfl⟩ := hx
  obtain ⟨f', hf', p', hp', rfl⟩ := hy
  have hp1 : p ∉ 𝐀[Axis.one] := fun hpA => hx1 (mul_mem (F_le_L _ hf) (A_le_L _ hpA))
  have hp2 : p ∉ 𝐀[Axis.two] := fun hpA => hx2 (mul_mem (F_le_L _ hf) (A_le_L _ hpA))
  have hpp : p * p' = p' * p := by
    have h1 : f * p * (f' * p') = (f * f') * (p * p') := by
      rw [show f * p * (f' * p') = f * (p * f') * p' by group, ← F_comm_P h hbt hf' hp]
      group
    have h2 : f' * p' * (f * p) = (f' * f) * (p' * p) := by
      rw [show f' * p' * (f * p) = f' * (p' * f) * p by group, ← F_comm_P h hbt hf hp']
      group
    rw [h1, h2, F_comm h hf' hf] at hc
    exact mul_left_cancel hc
  rcases mem_ZP_of_comm hp hp1 hp2 hp' hpp with hz | hz
  · exact Or.inl (mul_mem hf' (ZP_le_F h hz))
  · right
    have e : (f * p)⁻¹ * (f' * p') = f⁻¹ * f' * (p⁻¹ * p') := by
      have h3 : p⁻¹ * (f⁻¹ * f') = (f⁻¹ * f') * p⁻¹ :=
        (F_comm_P h hbt (mul_mem (inv_mem hf) hf') (inv_mem hp)).symm
      calc (f * p)⁻¹ * (f' * p') = p⁻¹ * (f⁻¹ * f') * p' := by group
        _ = f⁻¹ * f' * (p⁻¹ * p') := by rw [h3]; group
    rw [e]
    exact mul_mem (mul_mem (inv_mem hf) hf') (ZP_le_F h hz)

theorem card_le_of_mixed (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥)
    {S : Subgroup G} (hSK : S ≤ 𝐊⋆) (hS : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) {x : G}
    (hxS : x ∈ S) (hx1 : x ∉ 𝐋[Axis.one]) (hx2 : x ∉ 𝐋[Axis.two]) :
    Nat.card S ≤ 2 * Nat.card K ^ 4 := by
  have hidx : 𝐅.relIndex S ≤ 2 := relIndex_le_two ⟨x⁻¹, inv_mem hxS, fun b hb => by
    rcases mem_F_of_comm h hbt (hSK hxS) hx1 hx2 (hSK hb) (hS x hxS b hb) with h1 | h1
    · exact Or.inr h1
    · left
      rwa [hS b hb x⁻¹ (inv_mem hxS)]⟩
  have h1 := relIndex_mul_card 𝐅 S
  have h2 : Nat.card (𝐅 ⊓ S : Subgroup G) ≤ Nat.card K ^ 4 := by
    rw [← card_F h]
    exact card_le_of_le inf_le_left
  rw [← h1]
  exact Nat.mul_le_mul hidx h2

omit [Finite G] [Finite K] in
theorem two_mul_pow_four_lt (h : FCHyp L K n φ t) : 2 * Nat.card K ^ 4 < Nat.card K ^ 5 := by
  have := h.four_le_card
  have h7 : 0 < Nat.card K ^ 4 := by positivity
  calc 2 * Nat.card K ^ 4 < Nat.card K * Nat.card K ^ 4 :=
        Nat.mul_lt_mul_of_pos_right (by omega) h7
    _ = Nat.card K ^ 5 := by ring

theorem L_le_Ks (h : FCHyp L K n φ t) (i : Axis) : 𝐋[i] ≤ 𝐊⋆ := by
  rw [Ks_eq h]
  exact sup_le le_sup_left ((pull_mono φ (rootA_le_antiUnipotent i)).trans le_sup_right)

theorem abelian_Ks (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥)
    {S : Subgroup G} (hSK : S ≤ 𝐊⋆) (hS : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) :
    Nat.card S ≤ Nat.card K ^ 5 ∧
      (Nat.card S = Nat.card K ^ 5 → S = 𝐋[Axis.one] ∨ S = 𝐋[Axis.two]) := by
  have hlt := two_mul_pow_four_lt h
  by_cases hmix : ∃ x ∈ S, x ∉ 𝐋[Axis.one] ∧ x ∉ 𝐋[Axis.two]
  · obtain ⟨x, hxS, hx1, hx2⟩ := hmix
    have h1 := card_le_of_mixed h hbt hSK hS hxS hx1 hx2
    exact ⟨by omega, fun he => absurd he (by omega)⟩
  · push Not at hmix
    have hsub : ∀ x ∈ S, x ∈ 𝐋[Axis.one] ∨ x ∈ 𝐋[Axis.two] := fun x hx => by
      by_cases h1 : x ∈ 𝐋[Axis.one]
      · exact Or.inl h1
      · exact Or.inr (hmix x hx h1)
    rcases subgroup_le_of_subset_union hsub with hle | hle
    · refine ⟨(card_le_of_le hle).trans (card_L h _).le, fun he => Or.inl ?_⟩
      exact eq_of_le_of_card_ge hle (by rw [he, card_L h])
    · refine ⟨(card_le_of_le hle).trans (card_L h _).le, fun he => Or.inr ?_⟩
      exact eq_of_le_of_card_ge hle (by rw [he, card_L h])

theorem L_inf_P (h : FCHyp L K n φ t) (i : Axis) : 𝐋[i] ⊓ 𝐏 = 𝐀[i] := by
  refine le_antisymm (fun x hx => ?_)
    (le_inf (A_le_L i) (pull_mono φ (rootA_le_antiUnipotent i)))
  obtain ⟨hxL, hxP⟩ := mem_inf.mp hx
  rw [← SetLike.mem_coe, ← L_mul h i] at hxL
  obtain ⟨f, hf, a, ha, rfl⟩ := hxL
  have hfP : f ∈ 𝐏 := by
    simpa using mul_mem hxP (inv_mem (pull_mono φ (rootA_le_antiUnipotent i) ha))
  have hfZ : f ∈ 𝐙 := by
    rw [← F_inf_P h]
    exact mem_inf.mpr ⟨hf, hfP⟩
  exact mul_mem (pull_mono φ (center_le_rootA i) hfZ) ha

theorem L_ne (h : FCHyp L K n φ t) : 𝐋[Axis.one] ≠ 𝐋[Axis.two] := fun heq => by
  obtain ⟨h1, h2⟩ := uElt_mem_radA1_not_mem_radA2 (K := K)
  have hx : ((φ.symm (uElt 0 0 0 1) : L) : G) ∈ 𝐀[Axis.one] := symm_mem_pull.mpr h1
  have hx' : ((φ.symm (uElt 0 0 0 1) : L) : G) ∈ 𝐋[Axis.two] ⊓ 𝐏 :=
    ⟨heq ▸ A_le_L _ hx, pull_mono φ (rootA_le_antiUnipotent _) hx⟩
  rw [L_inf_P h] at hx'
  exact h2 (symm_mem_pull.mp hx')

theorem conj_R_mem_L' (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥)
    (i j : Axis) {r : G} (hr : r ∈ 𝐑[i]) {l : G} (hl : l ∈ 𝐋[j]) : r * l * r⁻¹ ∈ 𝐋[j] := by
  by_cases hij : j = i
  · subst hij
    exact conj_R_mem_L h j hr hl
  set S := 𝐋[j].map (MulAut.conj r).toMonoidHom with hS
  have hSK : S ≤ 𝐊⋆ := by
    rintro _ ⟨x, hx, rfl⟩
    exact conj_R_mem_Ks h i hr (L_le_Ks h j hx)
  have hSc : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show r * x * r⁻¹ * (r * y * r⁻¹) = r * (x * y) * r⁻¹ by group, L_comm h hbt j hx hy]
    group
  have hcard : Nat.card S = Nat.card K ^ 5 := by
    rw [card_map_of_injective (MulAut.conj r).injective, card_L h j]
  have hmem : r * l * r⁻¹ ∈ S := ⟨l, hl, rfl⟩
  have hne : S ≠ 𝐋[i] := by
    intro hSi
    have hle : 𝐋[j] ≤ 𝐋[i] := fun x hx => by
      have h1 : r * x * r⁻¹ ∈ 𝐋[i] := hSi ▸ (⟨x, hx, rfl⟩ : r * x * r⁻¹ ∈ S)
      have h2 := conj_R_mem_L h i (inv_mem hr) h1
      rwa [show r⁻¹ * (r * x * r⁻¹) * r⁻¹⁻¹ = x by group] at h2
    have heq : 𝐋[j] = 𝐋[i] := eq_of_le_of_card_ge hle (by rw [card_L h, card_L h])
    cases i <;> cases j
    · exact hij rfl
    · exact L_ne h heq.symm
    · exact L_ne h heq
    · exact hij rfl
  rcases (abelian_Ks h hbt hSK hSc).2 hcard with h1 | h1
  · cases j
    · rw [← h1]
      exact hmem
    · cases i
      · exact absurd h1 hne
      · exact absurd rfl hij
  · cases j
    · cases i
      · exact absurd rfl hij
      · exact absurd h1 hne
    · rw [← h1]
      exact hmem

theorem sq_W_mem_U (h : FCHyp L K n φ t) (i : Axis) {w : G} (hw : w ∈ 𝐖[i]) :
    w * w ∈ 𝐔[i] := by
  obtain ⟨lam, hlam, -⟩ := (square_map h i).2
  obtain ⟨a, ha⟩ := exists_coordG_eq φ i (kappa_mem_U h i (W_le_Fi h i hw).2)
  rw [hlam w hw a ha.symm]
  exact coordG_mem φ i _

theorem false_of_homocyclic (h : FCHyp L K n φ t)
    (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥) (i : Axis)
    (hset : {x : G | x ∈ 𝐖[i.swap] ∧ x * x = 1} = (𝐔[i.swap] : Set G)) : False := by
  have hA2 : ∀ a ∈ 𝐀[i.swap], a * a = 1 := fun a ha => h.B_mul_self i.swap (mem_sup_right ha)
  have key : ∀ x ∈ 𝐋[i.swap], x * x ∈ 𝐔[i] → x ∈ (𝐅 ⊓ 𝐃[i]) ⊔ 𝐀[i.swap] := by
    intro x hx hxx
    rw [← SetLike.mem_coe, ← L_mul h i.swap] at hx
    obtain ⟨f, hf, a, ha, rfl⟩ := hx
    obtain ⟨w, hw, w', hw', rfl⟩ := exists_W_swap_mul h i hf
    have hsq : w * w' * a * (w * w' * a) = w * w * (w' * w') := by
      rw [mul_self_mul_of_comm (F_comm_A h hbt i.swap hf ha), hA2 a ha, mul_one,
        mul_self_mul_of_comm (F_comm h (W_le_F i hw) (W_le_F i.swap hw'))]
    have h1 : w' * w' ∈ 𝐔[i] := by
      have := mul_mem (inv_mem (sq_W_mem_U h i hw)) (hsq ▸ hxx)
      rwa [inv_mul_cancel_left] at this
    have h2 : w' * w' = 1 := by
      have := mem_inf.mpr ⟨h1, sq_W_mem_U h i.swap hw'⟩
      rwa [U_inf_U_swap i, mem_bot] at this
    have hw'U : w' ∈ 𝐔[i.swap] := by
      have hmem : w' ∈ {x : G | x ∈ 𝐖[i.swap] ∧ x * x = 1} := ⟨hw', h2⟩
      rw [hset] at hmem
      exact hmem
    exact mul_mem (mul_mem (mem_sup_left (W_le_Fi h i hw))
      (mem_sup_right (pull_mono φ (rootU_le_rootA _) hw'U))) (mem_sup_right ha)
  have key' : ∀ x ∈ (𝐅 ⊓ 𝐃[i]) ⊔ 𝐀[i.swap], x ∈ 𝐋[i.swap] ∧ x * x ∈ 𝐔[i] := by
    intro x hx
    have hc : ∀ y ∈ 𝐅 ⊓ 𝐃[i], ∀ a ∈ 𝐀[i.swap], y * a = a * y :=
      fun y hy a ha => F_comm_A h hbt i.swap hy.1 ha
    obtain ⟨y, hy, a, ha, rfl⟩ := (mem_sup_of_commute hc).mp hx
    refine ⟨mul_mem (F_le_L _ hy.1) (A_le_L _ ha), ?_⟩
    rw [mul_self_mul_of_comm (hc y hy a ha), hA2 a ha, mul_one]
    rw [← SetLike.mem_coe, ← W_mul_U h i] at hy
    obtain ⟨w, hw, u, hu, rfl⟩ := hy
    have huZ : u ∈ 𝐙 := pull_mono φ (rootU_le_center _) hu
    rw [mul_self_mul_of_comm (comm_ZP h (F_le_H h (W_le_F i hw)) huZ), Setup.ZP_mul_self huZ,
      mul_one]
    exact sq_W_mem_U h i hw
  have hT : ∀ r ∈ 𝐑[i], ∀ x ∈ (𝐅 ⊓ 𝐃[i]) ⊔ 𝐀[i.swap],
      r * x * r⁻¹ ∈ (𝐅 ⊓ 𝐃[i]) ⊔ 𝐀[i.swap] := by
    intro r hr x hx
    obtain ⟨hxL, hxx⟩ := key' x hx
    refine key _ (conj_R_mem_L' h hbt i i.swap hr hxL) ?_
    rw [show r * x * r⁻¹ * (r * x * r⁻¹) = r * (x * x) * r⁻¹ by group]
    exact (mem_normalizer_iff.mp (h.N_le_normalizer_U i (R_le_N h i hr)) _).mp hxx
  have hQi : 𝐐[i] = 𝐃[i] ⊔ ((𝐅 ⊓ 𝐃[i]) ⊔ 𝐀[i.swap]) := by
    apply le_antisymm
    · refine sup_le ?_ le_sup_left
      rw [← B_sup_A_eq_Q i]
      exact sup_le ((h.B_le_D i).trans le_sup_left) (le_sup_right.trans le_sup_right)
    · refine sup_le le_sup_right (sup_le (inf_le_right.trans le_sup_right) ?_)
      exact ((pull_mono φ (rootA_le_antiUnipotent _)).trans le_sup_left).trans le_sup_left
  have hRN : 𝐑[i] ≤ normalizer ((𝐐[i] : Subgroup G) : Set G) := fun r hr =>
    mem_normalizer_of_conj_le fun x hx => by
      rw [hQi] at hx ⊢
      exact conj_mem_sup (fun d hd => h.conj_mem_D i (R_le_N h i hr) hd) (hT r hr) hx
  have hRH : 𝐑[i] ≤ 𝐇 := by
    rw [← R_inf_normalizer_Qi h i]
    exact le_inf le_rfl hRN
  have h1 := relIndex_H h i
  rw [relIndex_eq_one.mpr hRH] at h1
  have := h.four_le_card
  omega

theorem W_mul_self (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥)
    (j : Axis) {w : G} (hw : w ∈ 𝐖[j]) : w * w = 1 := by
  obtain ⟨lam, -, -, h0, hne⟩ := (square_map h j).2
  by_cases hl : lam = 0
  · have hE := (h0 hl).1
    rw [← pow_two]
    exact elemPow_eq_one_of_isElementaryAbelian w hw
  · exfalso
    obtain ⟨-, -, hset, -⟩ := hne hl
    refine false_of_homocyclic h hbt j.swap ?_
    rw [swap_swap_axis]
    exact hset

theorem F_mul_self (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥)
    {f : G} (hf : f ∈ 𝐅) : f * f = 1 := by
  obtain ⟨w, hw, w', hw', rfl⟩ := exists_W_swap_mul h Axis.one hf
  rw [mul_self_mul_of_comm (F_comm h (W_le_F _ hw) (W_le_F _ hw')), W_mul_self h hbt _ hw,
    W_mul_self h hbt _ hw', one_mul]

theorem L_mul_self (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥)
    (i : Axis) {x : G} (hx : x ∈ 𝐋[i]) : x * x = 1 := by
  rw [← SetLike.mem_coe, ← L_mul h i] at hx
  obtain ⟨f, hf, a, ha, rfl⟩ := hx
  rw [mul_self_mul_of_comm (F_comm_A h hbt i hf ha), F_mul_self h hbt hf,
    h.B_mul_self i (mem_sup_right ha), one_mul]

theorem Hi_eq (h : FCHyp L K n φ t) (i : Axis) : 𝐇 ⊓ 𝐄[i] = 𝐅 ⊔ 𝐁[i] := by
  rw [← L_sup_t h i, sup_assoc, sup_comm 𝐀[i] (zpowers t)]

theorem F_mul_B (h : FCHyp L K n φ t) (i : Axis) :
    (𝐅 : Set G) * (𝐁[i] : Set G) = ((𝐇 ⊓ 𝐄[i] : Subgroup G) : Set G) := by
  rw [Hi_eq h i]
  exact (coe_mul_of_right_le_normalizer_left _ _
    (((h.B_le_D i).trans (D_le_H i)).trans (H_le_normalizer_F h))).symm

theorem X_inf_H (h : FCHyp L K n φ t) (i : Axis) : 𝐗[i] ⊓ 𝐇 = 𝐋[i] := by
  refine le_antisymm (fun x hx => ?_) (le_inf (L_le_X h i) ((L_le_Hi h i).trans inf_le_left))
  obtain ⟨hxX, hxH⟩ := mem_inf.mp hx
  have htN : t ∈ normalizer (𝐋[i] : Set G) :=
    mem_normalizer_of_conj_le fun _ hl => conj_H_mem_L h i t_mem_H hl
  have hxHi : x ∈ 𝐋[i] ⊔ zpowers t := by
    rw [L_sup_t h i]
    exact mem_inf.mpr ⟨hxH, X_le_E h i hxX⟩
  rcases mem_or_mul_mem h.setup.t_mul_t htN hxHi with h1 | h1
  · exact h1
  · exfalso
    apply t_not_mem_X h i
    have := mul_mem (L_le_X h i h1) (inv_mem hxX)
    rwa [mul_inv_cancel_right] at this

theorem X_mul_self (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥)
    (i : Axis) {x : G} (hx : x ∈ 𝐗[i]) : x * x = 1 := by
  have hXR := (X_normal_R h i).1
  have hH : ∀ y ∈ 𝐗[i], psiG φ i (t⁻¹ * (y * t * y⁻¹)) 1 = 0 → y * y = 1 := by
    intro y hy hy0
    have hyH : y ∈ 𝐇 := (mem_H_iff_y h i (hXR hy)).mpr hy0
    have hyL : y ∈ 𝐋[i] := by
      rw [← X_inf_H h i]
      exact mem_inf.mpr ⟨hy, hyH⟩
    exact L_mul_self h hbt i hyL
  have hκ := conj_t_mem_A h i (hXR hx)
  set v := psiG φ i (t⁻¹ * (x * t * x⁻¹)) with hv
  by_cases h0 : v 1 = 0
  · exact hH x hx h0
  obtain ⟨p, hpP, hpc⟩ := exists_rootAct_P h i (v 0 / v 1)
  have hpX : p * x * p⁻¹ ∈ 𝐗[i] :=
    (mem_normalizer_iff.mp (R_le_normalizer_X h i (mem_sup_left (mem_sup_left hpP))) x).mp hx
  have hyX : 𝐰[i] * (p * x * p⁻¹) * 𝐰[i]⁻¹ ∈ 𝐗[i] :=
    (mem_normalizer_iff.mp (w_mem_normalizer_X i) _).mp hpX
  have htwp : 𝐰[i] * (p * t * p⁻¹) * 𝐰[i]⁻¹ = t := by
    rw [← h.twoCore.comm (pull_le φ _ hpP), mul_inv_cancel_right,
      ← h.twoCore.comm (w_mem_L i), mul_inv_cancel_right]
  have e1 : t⁻¹ * ((𝐰[i] * (p * x * p⁻¹) * 𝐰[i]⁻¹) * t * (𝐰[i] * (p * x * p⁻¹) * 𝐰[i]⁻¹)⁻¹) =
      𝐰[i] * (p * (t⁻¹ * (x * t * x⁻¹)) * p⁻¹) * 𝐰[i]⁻¹ := by
    conv_lhs => rw [← htwp]
    group
  have hκp : p * (t⁻¹ * (x * t * x⁻¹)) * p⁻¹ ∈ 𝐀[i] := conj_H_mem_A h i (P_le_H hpP) hκ
  have hψ : psiG φ i (t⁻¹ * ((𝐰[i] * (p * x * p⁻¹) * 𝐰[i]⁻¹) * t *
      (𝐰[i] * (p * x * p⁻¹) * 𝐰[i]⁻¹)⁻¹)) 1 = 0 := by
    rw [e1, psiG_conj_w h i hκp, hpc _ hκ, ← hv]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [div_mul_cancel₀ _ h0]
    exact CharTwo.add_self_eq_zero _
  have hy2 := hH _ hyX hψ
  calc x * x = (𝐰[i] * p)⁻¹ * ((𝐰[i] * (p * x * p⁻¹) * 𝐰[i]⁻¹) *
        (𝐰[i] * (p * x * p⁻¹) * 𝐰[i]⁻¹)) * (𝐰[i] * p) := by group
    _ = 1 := by rw [hy2]; group

theorem X_elem (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥)
    (i : Axis) : IsElementaryAbelian 2 𝐗[i] :=
  isElementaryAbelian_of_mul_self fun _ hx => X_mul_self h hbt i hx

omit [Finite G] [Finite K] in
variable (φ t) in
@[expose] def kerY (i : Axis) : Subgroup G where
  carrier := {g | g ∈ normalizer (𝐇 : Set G) ∧ g ∈ normalizer (𝐋[i] : Set G) ∧
    ∀ x ∈ 𝐇, g * x * g⁻¹ * x⁻¹ ∈ 𝐋[i]}
  mul_mem' := by
    rintro g g' ⟨hgH, hgL, hg⟩ ⟨hgH', hgL', hg'⟩
    refine ⟨mul_mem hgH hgH', mul_mem hgL hgL', fun x hx => ?_⟩
    have h1 : g * (g' * x * g'⁻¹ * x⁻¹) * g⁻¹ ∈ 𝐋[i] :=
      (mem_normalizer_iff.mp hgL _).mp (hg' x hx)
    rw [show g * g' * x * (g * g')⁻¹ * x⁻¹ =
      g * (g' * x * g'⁻¹ * x⁻¹) * g⁻¹ * (g * x * g⁻¹ * x⁻¹) by group]
    exact mul_mem h1 (hg x hx)
  one_mem' := ⟨one_mem _, one_mem _, fun x _ => by
    rw [one_mul, inv_one, mul_one, mul_inv_cancel]
    exact one_mem _⟩
  inv_mem' := by
    rintro g ⟨hgH, hgL, hg⟩
    refine ⟨inv_mem hgH, inv_mem hgL, fun x hx => ?_⟩
    have hx' : g⁻¹ * x * g⁻¹⁻¹ ∈ 𝐇 := (mem_normalizer_iff.mp (inv_mem hgH) x).mp hx
    have h1 := inv_mem (hg _ hx')
    rwa [show (g * (g⁻¹ * x * g⁻¹⁻¹) * g⁻¹ * (g⁻¹ * x * g⁻¹⁻¹)⁻¹)⁻¹ =
      g⁻¹ * x * g⁻¹⁻¹ * x⁻¹ by group] at h1

omit [Finite G] [Finite K] in
theorem mem_kerY {i : Axis} {g : G} :
    g ∈ kerY φ t i ↔ g ∈ normalizer (𝐇 : Set G) ∧ g ∈ normalizer (𝐋[i] : Set G) ∧
      ∀ x ∈ 𝐇, g * x * g⁻¹ * x⁻¹ ∈ 𝐋[i] :=
  Iff.rfl

omit [Finite G] [Finite K] in
theorem conj_mem_kerY {i : Axis} {r : G} (hrH : r ∈ normalizer (𝐇 : Set G))
    (hrL : r ∈ normalizer (𝐋[i] : Set G)) {y : G} (hy : y ∈ kerY φ t i) :
    r * y * r⁻¹ ∈ kerY φ t i := by
  obtain ⟨hyH, hyL, hy⟩ := hy
  refine ⟨mul_mem (mul_mem hrH hyH) (inv_mem hrH), mul_mem (mul_mem hrL hyL) (inv_mem hrL),
    fun x hx => ?_⟩
  have hx' : r⁻¹ * x * r⁻¹⁻¹ ∈ 𝐇 := (mem_normalizer_iff.mp (inv_mem hrH) x).mp hx
  have h1 := (mem_normalizer_iff.mp hrL _).mp (hy _ hx')
  rwa [show r * (y * (r⁻¹ * x * r⁻¹⁻¹) * y⁻¹ * (r⁻¹ * x * r⁻¹⁻¹)⁻¹) * r⁻¹ =
    r * y * r⁻¹ * x * (r * y * r⁻¹)⁻¹ * x⁻¹ by group] at h1

theorem R_le_kerY (h : FCHyp L K n φ t) (i : Axis) : 𝐑[i] ≤ kerY φ t i := fun r hr =>
  ⟨R_le_normalizer_H h i hr, R_le_normalizer_L h i hr, fun x hx => by
    have h1 := commutator_mem_closure_sq (inv_mem hr) (inv_mem (H_le_R h i hx))
    simp only [inv_inv] at h1
    have h2 := sq_R_le_L h i h1
    rwa [show r * (x * r⁻¹ * x⁻¹) = r * x * r⁻¹ * x⁻¹ by group] at h2⟩

theorem mem_A_of_sq (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥)
    (i : Axis) {x : G} (hx : x ∈ 𝐋[i]) (hsq : t * x * (t * x) = 1) : x ∈ 𝐀[i] := by
  rw [← SetLike.mem_coe, ← L_mul h i] at hx
  obtain ⟨f, hf, a, ha, rfl⟩ := hx
  have hta : t * a = a * t := h.twoCore.comm (pull_le φ _ ha)
  have hfa : f * a = a * f := F_comm_A h hbt i hf ha
  have ha2 : a * a = 1 := h.B_mul_self i (mem_sup_right ha)
  have h1 : t * f * (t * f) = 1 := by
    have e : t * (f * a) * (t * (f * a)) = t * f * (t * f) * (a * a) := by
      calc t * (f * a) * (t * (f * a)) = t * f * (a * t) * f * a := by group
        _ = t * f * (t * a) * f * a := by rw [hta]
        _ = t * f * t * (a * f) * a := by group
        _ = t * f * t * (f * a) * a := by rw [hfa]
        _ = t * f * (t * f) * (a * a) := by group
    rw [e, ha2, mul_one] at hsq
    exact hsq
  have hf2 : f * f = 1 := F_mul_self h hbt hf
  have hft : f * t = t * f := by
    calc f * t = f * t * (t * f * (t * f)) := by rw [h1, mul_one]
      _ = f * (t * t) * f * t * f := by group
      _ = f * f * t * f := by rw [h.setup.t_mul_t]; group
      _ = t * f := by rw [hf2, one_mul]
  have hfZ : f ∈ 𝐙 := mem_ZP_of_mem_F h hf (mem_centralizer_singleton_iff.mpr hft)
  exact mul_mem (pull_mono φ (center_le_rootA i) hfZ) ha

theorem kerY_le_N (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥)
    (i : Axis) {g : G} (hg : g ∈ kerY φ t i) :
    g ∈ normalizer (𝐁[i] : Set G) := by
  obtain ⟨hgH, -, hg⟩ := hg
  have htt := h.setup.t_mul_t
  have hc := TwoCoreSetup.comm_pull (S := rootA K i) φ h.twoCore
  have hB : ∀ a ∈ 𝐀[i], g * (t * a) * g⁻¹ ∈ 𝐁[i] := by
    intro a ha
    have h1 := hg _ (mul_mem t_mem_H (A_le_H h i ha))
    have hx : t * (g * (t * a) * g⁻¹) ∈ 𝐋[i] := by
      have e : t * (g * (t * a) * g⁻¹) =
          t * (g * (t * a) * g⁻¹ * (t * a)⁻¹) * t⁻¹ * (t * t * a) := by group
      rw [e, htt, one_mul]
      exact mul_mem (conj_H_mem_L h i t_mem_H h1) (A_le_L i ha)
    have hta2 : t * a * (t * a) = 1 :=
      h.B_mul_self i (mul_mem (mem_sup_left (mem_zpowers t)) (mem_sup_right ha))
    have hsq : t * (t * (g * (t * a) * g⁻¹)) * (t * (t * (g * (t * a) * g⁻¹))) = 1 := by
      rw [← mul_assoc t t, htt, one_mul]
      calc g * (t * a) * g⁻¹ * (g * (t * a) * g⁻¹) = g * (t * a * (t * a)) * g⁻¹ := by group
        _ = 1 := by rw [hta2]; group
    exact (mem_zpowers_sup_iff htt hc).mpr (Or.inr (mem_A_of_sq h hbt i hx hsq))
  refine mem_normalizer_of_conj_le fun b hb => ?_
  rcases (mem_zpowers_sup_iff htt hc).mp hb with hbA | hbA
  · have e : g * b * g⁻¹ = (g * (t * 1) * g⁻¹)⁻¹ * (g * (t * b) * g⁻¹) := by group
    rw [e]
    exact mul_mem (inv_mem (hB 1 (one_mem _))) (hB b hbA)
  · have e : g * b * g⁻¹ = g * (t * (t * b)) * g⁻¹ := by rw [← mul_assoc t t, htt, one_mul]
    rw [e]
    exact hB _ hbA

theorem kerY_le_normalizer_R (h : FCHyp L K n φ t)
    (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥) (i : Axis) {g : G} (hg : g ∈ kerY φ t i) :
    g ∈ normalizer (𝐑[i] : Set G) := by
  have hgN := kerY_le_N h hbt i hg
  have hR : 𝐑[i] = 𝐇 ⊔ 𝐄[i] :=
    le_antisymm (sup_le (Q_le_H.trans le_sup_left) le_sup_right) (sup_le (H_le_R h i) le_sup_right)
  refine mem_normalizer_of_conj_le fun x hx => ?_
  rw [hR] at hx ⊢
  exact conj_mem_sup (fun y hy => (mem_normalizer_iff.mp hg.1 y).mp hy)
    (fun e he => conj_mem_pCore_map hgN he) hx

open CFSG.QuasithinUnique.Fin257 in
theorem mem_Q_of_aut (h : FCHyp L K n φ t) (i : Axis) {c : G} (hcC : c ∈ 𝐂)
    (hc2 : ∃ m : ℕ, c ^ 2 ^ m = 1) (hcA1 : c ∈ normalizer (𝐀[Axis.one] : Set G))
    (hcA2 : c ∈ normalizer (𝐀[Axis.two] : Set G))
    (htriv : ∀ p ∈ 𝐏, c * p * c⁻¹ * p⁻¹ ∈ 𝐀[i]) : c ∈ 𝐐 := by
  set c' : normalizer (L : Set G) := ⟨c, h.setup.cent_le hcC⟩ with hc'
  have hcP : c ∈ normalizer (𝐏 : Set G) := mem_normalizer_of_conj_le fun p hp => by
    rw [P_eq_A_sup_A] at hp ⊢
    exact conj_mem_sup (fun a ha => (mem_normalizer_iff.mp hcA1 a).mp ha)
      (fun a ha => (mem_normalizer_iff.mp hcA2 a).mp ha) hp
  have hαA2 : ∀ x, normAct φ c' x ∈ radA2 K ↔ x ∈ radA2 K :=
    mem_autStab.mp ((mem_normalizer_pull_iff φ (radA2 K) c').mp hcA2)
  have hαU : ∀ x ∈ antiUnipotent K, normAct φ c' x ∈ antiUnipotent K := fun x hx =>
    (mem_autStab.mp ((mem_normalizer_pull_iff φ (antiUnipotent K) c').mp hcP) x).mpr hx
  obtain ⟨p', hp', r, s, k, hk, hα⟩ := FieldInvolution.exists_conj_mul_dSp_frobAut_pow
    h.setup.two_le h.setup.card_K _ hαA2 hαU
  obtain ⟨a, b, c₀, d, rfl⟩ := hp'
  have hact : ∀ e : antiSp K, e ∈ antiUnipotent K → normAct φ c' e * e⁻¹ ∈ rootA K i := by
    intro e he
    have h1 := htriv _ (symm_mem_pull.mpr he)
    have he1 : ((φ.symm (normAct φ c' e) : L) : G) = c * ((φ.symm e : L) : G) * c⁻¹ :=
      normAct_symm_apply φ c' e
    rw [← he1] at h1
    have e2 : ((φ.symm (normAct φ c' e) : L) : G) * ((φ.symm e : L) : G)⁻¹ =
        ((φ.symm (normAct φ c' e * e⁻¹) : L) : G) := by
      simp only [map_mul, map_inv, coe_mul, coe_inv]
    rw [e2] at h1
    exact symm_mem_pull.mp h1
  have hz : (0 : K) ^ 2 ^ k = 0 := zero_pow (pow_ne_zero _ two_ne_zero)
  have hμ : ∃ μ : K, ∀ x : K, μ * x ^ 2 ^ k = x := by
    cases i
    · refine ⟨(r : K) * ((s⁻¹ : Kˣ) : K), fun x => ?_⟩
      have h1 := hact _ (uElt_mem_antiUnipotent x 0 0 0)
      rw [hα, MulAut.mul_apply, MulAut.conj_apply, FieldInvolution.frobAut_pow_uElt, hz] at h1
      change _ ∈ radA1 K at h1
      rw [show uElt a b c₀ d * Sp4.dSp r s * uElt (x ^ 2 ^ k) 0 0 0 *
          (uElt a b c₀ d * Sp4.dSp r s)⁻¹ * (uElt x 0 0 0)⁻¹ =
        uElt a b c₀ d * (Sp4.dSp r s * uElt (x ^ 2 ^ k) 0 0 0 * (Sp4.dSp r s)⁻¹) *
          (uElt a b c₀ d)⁻¹ * (uElt x 0 0 0)⁻¹ by group] at h1
      exact coord_one_of_mem h1
    · refine ⟨(s : K) ^ 2, fun x => ?_⟩
      have h1 := hact _ (uElt_mem_antiUnipotent 0 0 0 x)
      rw [hα, MulAut.mul_apply, MulAut.conj_apply, FieldInvolution.frobAut_pow_uElt, hz] at h1
      change _ ∈ radA2 K at h1
      rw [show uElt a b c₀ d * Sp4.dSp r s * uElt 0 0 0 (x ^ 2 ^ k) *
          (uElt a b c₀ d * Sp4.dSp r s)⁻¹ * (uElt 0 0 0 x)⁻¹ =
        uElt a b c₀ d * (Sp4.dSp r s * uElt 0 0 0 (x ^ 2 ^ k) * (Sp4.dSp r s)⁻¹) *
          (uElt a b c₀ d)⁻¹ * (uElt 0 0 0 x)⁻¹ by group] at h1
      exact coord_two_of_mem h1
  obtain ⟨μ, hμ⟩ := hμ
  have hμ1 : μ = 1 := by simpa using hμ 1
  have hk0 : k = 0 := eq_zero_of_frobRingEquiv_pow_eq_one (by have := h.setup.two_le; omega)
    h.setup.card_K hk (RingEquiv.ext fun x => by
      have := hμ x
      rw [hμ1, one_mul] at this
      rw [frobRingEquiv_pow_apply, this]
      rfl)
  subst hk0
  rw [pow_zero, mul_one] at hα
  obtain ⟨m, hm⟩ := hc2
  have hcm : c' ^ 2 ^ m = 1 := Subtype.ext (by simp [hc', hm])
  have hαm : MulAut.conj ((uElt a b c₀ d * Sp4.dSp r s) ^ 2 ^ m) = 1 := by
    rw [map_pow, ← hα, ← map_pow, hcm, map_one]
  have hone : (uElt a b c₀ d * Sp4.dSp r s) ^ 2 ^ m = 1 := eq_one_of_forall_commute fun y => by
    have h1 := congrArg (fun σ : MulAut (antiSp K) => σ y) hαm
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc (uElt a b c₀ d * Sp4.dSp r s) ^ 2 ^ m * y =
        ((uElt a b c₀ d * Sp4.dSp r s) ^ 2 ^ m * y * ((uElt a b c₀ d * Sp4.dSp r s) ^ 2 ^ m)⁻¹) *
          (uElt a b c₀ d * Sp4.dSp r s) ^ 2 ^ m := by group
      _ = y * (uElt a b c₀ d * Sp4.dSp r s) ^ 2 ^ m := by rw [h1]
  have hpow : ∀ N : ℕ, ∃ u ∈ antiUnipotent K,
      (uElt a b c₀ d * Sp4.dSp r s) ^ N = u * Sp4.dSp r s ^ N := by
    intro N
    induction N with
    | zero => exact ⟨1, one_mem _, by rw [pow_zero, pow_zero, mul_one]⟩
    | succ N ih =>
      obtain ⟨u, hu, hN⟩ := ih
      refine ⟨u * (Sp4.dSp r s ^ N * uElt a b c₀ d * (Sp4.dSp r s ^ N)⁻¹), mul_mem hu ?_, ?_⟩
      · rw [Sp4.dSp_pow]
        exact FieldInvolution.dSp_conj_mem_antiUnipotent _ _ (uElt_mem_antiUnipotent _ _ _ _)
      · rw [pow_succ (uElt a b c₀ d * Sp4.dSp r s), hN, pow_succ (Sp4.dSp r s)]
        group
  obtain ⟨u', hu', hN⟩ := hpow (2 ^ m)
  rw [hone] at hN
  have hjN : Sp4.dSp r s ^ 2 ^ m ∈ antiUnipotent K := by
    rw [eq_inv_of_mul_eq_one_right hN.symm]
    exact inv_mem hu'
  rw [Sp4.dSp_pow] at hjN
  obtain ⟨hr, hs⟩ := FieldInvolution.eq_one_of_dSp_mem_antiUnipotent hjN
  have hunit : ∀ x : Kˣ, x ^ 2 ^ m = 1 → x = 1 := fun x hx => by
    have h1 : ((x : K) - 1) ^ 2 ^ m = 0 := by
      rw [sub_pow_char_pow, ← Units.val_pow_eq_pow_val, hx, Units.val_one, one_pow, sub_self]
    exact Units.ext (sub_eq_zero.mp ((pow_eq_zero_iff (pow_ne_zero _ two_ne_zero)).mp h1))
  rw [hunit r hr, hunit s hs, Sp4.dSp_one, mul_one] at hα
  have hα' : normAct φ c' = MulAut.conj (φ (φ.symm (uElt a b c₀ d))) := by
    rw [MulEquiv.apply_symm_apply]
    exact hα
  have h0 := inv_mul_mem_centralizer φ c' _ hα'
  have hτ : ((φ.symm (uElt a b c₀ d) : L) : G)⁻¹ * c ∈ zpowers t :=
    h.twoCore.mem_zpowers_of_mem h0 (mul_mem (inv_mem (h.setup.L_le (φ.symm _).2)) hcC)
  have e : c = ((φ.symm (uElt a b c₀ d) : L) : G) * (((φ.symm (uElt a b c₀ d) : L) : G)⁻¹ * c) := by
    group
  rw [e]
  exact mul_mem (mem_sup_left (symm_mem_pull.mpr (uElt_mem_antiUnipotent _ _ _ _)))
    (mem_sup_right hτ)

theorem le_R_of_le_kerY (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥)
    (i : Axis) {S : Subgroup G} (hS2 : IsPGroup 2 S) (hRS : 𝐑[i] ≤ S)
    (hSY : S ≤ kerY φ t i) : S ≤ 𝐑[i] := by
  intro s hs
  have hsN : s ∈ normalizer (𝐁[i] : Set G) := kerY_le_N h hbt i (hSY hs)
  have hmem : s⁻¹ * t * s ∈ {x : G | ∃ a ∈ 𝐀[i], x = t * a} := by
    rw [← h.orbit_N i]
    exact ⟨s, hsN, rfl⟩
  rw [← orbit_R h i] at hmem
  obtain ⟨r, hr, hrt⟩ := hmem
  have hcC : s * r⁻¹ ∈ 𝐂 := by
    rw [mem_centralizer_singleton_iff]
    calc s * r⁻¹ * t = s * (r⁻¹ * t * r) * r⁻¹ := by group
      _ = s * (s⁻¹ * t * s) * r⁻¹ := by rw [hrt]
      _ = t * (s * r⁻¹) := by group
  have hcS : s * r⁻¹ ∈ S := mul_mem hs (inv_mem (hRS hr))
  obtain ⟨hcH, -, hctriv⟩ := hSY hcS
  have hcNi := kerY_le_N h hbt i (hSY hcS)
  have hcQ : s * r⁻¹ ∈ normalizer (𝐐 : Set G) := by
    refine mem_normalizer_of_conj_le fun q hq => ?_
    rw [← FCHyp.H_inf_C h] at hq ⊢
    obtain ⟨hqH, hqC⟩ := mem_inf.mp hq
    exact mem_inf.mpr ⟨(mem_normalizer_iff.mp hcH q).mp hqH,
      mul_mem (mul_mem hcC hqC) (inv_mem hcC)⟩
  obtain ⟨hB1, hB2⟩ := h.mem_normalizer_B_of hcQ i hcNi
  have hcA1 := h.N_le_normalizer_A _ hB1
  have hcA2 := h.N_le_normalizer_A _ hB2
  have htriv : ∀ p ∈ 𝐏, s * r⁻¹ * p * (s * r⁻¹)⁻¹ * p⁻¹ ∈ 𝐀[i] := by
    intro p hp
    have hcp : s * r⁻¹ * p * (s * r⁻¹)⁻¹ ∈ 𝐏 := by
      rw [P_eq_A_sup_A] at hp ⊢
      exact conj_mem_sup (fun a ha => (mem_normalizer_iff.mp hcA1 a).mp ha)
        (fun a ha => (mem_normalizer_iff.mp hcA2 a).mp ha) hp
    rw [← L_inf_P h i]
    exact mem_inf.mpr ⟨hctriv p (P_le_H hp), mul_mem hcp (inv_mem hp)⟩
  have hc := mem_Q_of_aut h i hcC (exists_two_pow_eq_one hS2 hcS) hcA1 hcA2 htriv
  have e : s = s * r⁻¹ * r := by group
  rw [e]
  exact mul_mem (mem_sup_left hc) hr

theorem R_le_normalizer_R (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥)
    (i : Axis) : 𝐑[i.swap] ≤ normalizer (𝐑[i] : Set G) := by
  intro r hr
  set S := 𝐑[i].map (MulAut.conj r).toMonoidHom with hS
  have hrL : r ∈ normalizer (𝐋[i] : Set G) :=
    mem_normalizer_of_conj_le fun l hl => conj_R_mem_L' h hbt i.swap i hr hl
  have hSY : S ≤ kerY φ t i := by
    rintro _ ⟨y, hy, rfl⟩
    exact conj_mem_kerY (R_le_normalizer_H h i.swap hr) hrL (R_le_kerY h i hy)
  have hS2 : IsPGroup 2 S := (R_isPGroup h i).map _
  have hSN : S ≤ normalizer (𝐑[i] : Set G) := fun x hx =>
    kerY_le_normalizer_R h hbt i (hSY hx)
  have hT2 : IsPGroup 2 (S ⊔ 𝐑[i] : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' hS2 (R_isPGroup h i) hSN
  have hle := le_R_of_le_kerY h hbt i hT2 le_sup_right (sup_le hSY (R_le_kerY h i))
  exact mem_normalizer_of_conj_le fun x hx => hle (mem_sup_left ⟨x, hx, rfl⟩)

theorem T_le_normalizer_R (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥)
    (i : Axis) : (𝐑[Axis.one] ⊔ 𝐑[Axis.two] : Subgroup G) ≤ normalizer (𝐑[i] : Set G) := by
  cases i
  · exact sup_le le_normalizer (R_le_normalizer_R h hbt Axis.one)
  · exact sup_le (R_le_normalizer_R h hbt Axis.two) le_normalizer

theorem ZP_le_center_T (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥) :
    𝐙 ≤ (center (𝐑[Axis.one] ⊔ 𝐑[Axis.two] : Subgroup G)).map
      (𝐑[Axis.one] ⊔ 𝐑[Axis.two] : Subgroup G).subtype := by
  intro z hz
  have hcomm : ∀ i : Axis, ∀ y ∈ 𝐑[i], y * z = z * y := fun i y hy => by
    have hz' : z ∈ (center 𝐑[i]).map 𝐑[i].subtype := by
      rw [(centers_of_bot h i (hbt i)).2]
      exact hz
    exact (mem_center_map_iff.mp hz').2 y hy
  have hle : (𝐑[Axis.one] ⊔ 𝐑[Axis.two] : Subgroup G) ≤ centralizer ({z} : Set G) :=
    sup_le (fun y hy => mem_centralizer_singleton_iff.mpr (hcomm _ y hy))
      (fun y hy => mem_centralizer_singleton_iff.mpr (hcomm _ y hy))
  exact mem_center_map_iff.mpr ⟨mem_sup_left (mem_sup_left (mem_sup_left (Setup.ZP_le_PG hz))),
    fun y hy => mem_centralizer_singleton_iff.mp (hle hy)⟩

theorem ZP_comm_R (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥)
    (i : Axis) {r : G} (hr : r ∈ 𝐑[i]) {z : G} (hz : z ∈ 𝐙) : r * z = z * r := by
  have hz' : z ∈ (center 𝐑[i]).map 𝐑[i].subtype := by
    rw [(centers_of_bot h i (hbt i)).2]
    exact hz
  exact (mem_center_map_iff.mp hz').2 r hr

theorem mem_X_or_Hi (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥)
    (i : Axis) {e : G} (he : e ∈ 𝐄[i]) (hsq : e * e ∈ 𝐙) : e ∈ 𝐗[i] ∨ e ∈ 𝐇 ⊓ 𝐄[i] := by
  have htN : t ∈ normalizer ((𝐗[i] : Subgroup G) : Set G) := D_le_normalizer_X h i (t_mem_D h i)
  have he' : e ∈ 𝐗[i] ⊔ zpowers t := by
    rw [(X_sup_t h i).2]
    exact he
  rcases mem_or_mul_mem h.setup.t_mul_t htN he' with h1 | h1
  · exact Or.inl h1
  · right
    have hex : e = t * (t * e) := by rw [← mul_assoc, h.setup.t_mul_t, one_mul]
    have hxE : t * e ∈ 𝐄[i] := X_le_E h i h1
    have hxinv : (t * e)⁻¹ = t * e := inv_eq_of_mul_eq_one_right (X_mul_self h hbt i h1)
    have hxH : t * e ∈ 𝐇 := by
      rw [mem_H_iff_E h i hxE, hxinv, h.twoCore.t_inv]
      have e1 : t * (t * e * t * (t * e)) = e * e := by
        calc t * (t * e * t * (t * e)) = (t * t) * e * (t * t) * e := by group
          _ = e * e := by rw [h.setup.t_mul_t]; group
      rw [e1]
      exact hsq
    rw [hex]
    exact mem_inf.mpr ⟨mul_mem t_mem_H hxH, hex ▸ he⟩

theorem mem_X_or_H (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥)
    (i : Axis) {r : G} (hr : r ∈ 𝐑[i]) (hsq : r * r ∈ 𝐙) : r ∈ 𝐗[i] ∨ r ∈ 𝐇 := by
  set r' : 𝐑[i] := ⟨r, hr⟩
  have hD : (r' * r' : 𝐑[i]) ∈ (parabolicHom h i).ker := by
    rw [ker_parabolicHom h i, mem_subgroupOf]
    exact (h.B_le_D i) (ZP_le_B i hsq)
  have h1 : parabolicHom h i r' * parabolicHom h i r' = 1 := by
    rw [← map_mul]
    exact hD
  rcases mul_eq_zero.mp ((Heis.mul_self_eq_one_iff _).mp h1) with hz | hy
  · rcases mem_X_or_Hi h hbt i ((parabolicHom_z_eq_zero_iff h i r').mp hz) hsq with h2 | h2
    · exact Or.inl h2
    · exact Or.inr h2.1
  · exact Or.inr ((mem_H_iff h i r').mpr hy)

theorem X_not_le_H (h : FCHyp L K n φ t) (i : Axis) : ¬ 𝐗[i] ≤ 𝐇 := fun hle => by
  have h1 : 𝐗[i] ≤ 𝐋[i] := by
    rw [← X_inf_H h i]
    exact le_inf le_rfl hle
  have h2 := card_le_of_le h1
  rw [card_X h i, card_L h i] at h2
  have := h.four_le_card
  have h3 : Nat.card K ^ 5 < Nat.card K ^ 6 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  omega

theorem conj_T_mem_X (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥)
    (i : Axis) {g : G} (hg : g ∈ (𝐑[Axis.one] ⊔ 𝐑[Axis.two] : Subgroup G)) {x : G}
    (hx : x ∈ 𝐗[i]) : g * x * g⁻¹ ∈ 𝐗[i] := by
  have hgR : g ∈ normalizer (𝐑[i] : Set G) := T_le_normalizer_R h hbt i hg
  set S := 𝐗[i].map (MulAut.conj g).toMonoidHom with hS
  have hSR : S ≤ 𝐑[i] := by
    rintro _ ⟨y, hy, rfl⟩
    exact (mem_normalizer_iff.mp hgR y).mp ((X_normal_R h i).1 hy)
  have hS2 : ∀ s ∈ S, s * s = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show g * y * g⁻¹ * (g * y * g⁻¹) = g * (y * y) * g⁻¹ by group, X_mul_self h hbt i hy]
    group
  have hsub : ∀ s ∈ S, s ∈ 𝐗[i] ∨ s ∈ 𝐇 := fun s hs =>
    mem_X_or_H h hbt i (hSR hs) (by rw [hS2 s hs]; exact one_mem _)
  have hcard : Nat.card S = Nat.card K ^ 6 := by
    rw [card_map_of_injective (MulAut.conj g).injective, card_X h i]
  rcases subgroup_le_of_subset_union hsub with hle | hle
  · have heq : S = 𝐗[i] := eq_of_le_of_card_ge hle (by rw [hcard, card_X h i])
    rw [← heq]
    exact ⟨x, hx, rfl⟩
  · exfalso
    have hSK : S ≤ normalizer (𝐊⋆ : Set G) := fun s hs =>
      mem_normalizer_of_conj_le fun k hk => conj_H_mem_Ks h (hle hs) hk
    have h1 := card_sup_mul_card_inf 𝐊⋆ S hSK
    have h2 : Nat.card (𝐊⋆ ⊔ S : Subgroup G) ≤ 2 * Nat.card K ^ 6 := by
      rw [← h.H_facts.2.2]
      exact card_le_of_le (sup_le (Ks_le_H h) hle)
    have h3 : Nat.card (𝐊⋆ ⊓ S : Subgroup G) ≤ Nat.card K ^ 5 :=
      (abelian_Ks h hbt inf_le_left fun x hx y hy => comm_of_mul_self hS2 hx.2 hy.2).1
    rw [card_Ks h, hcard] at h1
    have h4 : Nat.card K ^ 6 * Nat.card K ^ 6 ≤ Nat.card K ^ 6 * (2 * Nat.card K ^ 5) := by
      rw [← h1]
      calc Nat.card (𝐊⋆ ⊔ S : Subgroup G) * Nat.card (𝐊⋆ ⊓ S : Subgroup G)
          ≤ (2 * Nat.card K ^ 6) * Nat.card K ^ 5 := Nat.mul_le_mul h2 h3
        _ = Nat.card K ^ 6 * (2 * Nat.card K ^ 5) := by ring
    have hq6 : 0 < Nat.card K ^ 6 := by have : 0 < Nat.card K := Nat.card_pos; positivity
    have h5 := Nat.le_of_mul_le_mul_left h4 hq6
    have := h.four_le_card
    have h7 : 0 < Nat.card K ^ 5 := by positivity
    have h6 : 2 * Nat.card K ^ 5 < Nat.card K ^ 6 := by
      calc 2 * Nat.card K ^ 5 < Nat.card K * Nat.card K ^ 5 :=
            Nat.mul_lt_mul_of_pos_right (by omega) h7
        _ = Nat.card K ^ 6 := by ring
    omega

theorem ZP_normal_R (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥)
    (i : Axis) : (𝐙.subgroupOf 𝐑[i]).Normal :=
  ⟨fun z hz r => mem_subgroupOf.mpr (by
    rw [coe_mul, coe_mul, coe_inv, ZP_comm_R h hbt i r.2 (mem_subgroupOf.mp hz),
      mul_inv_cancel_right]
    exact mem_subgroupOf.mp hz)⟩

theorem ZP_normal_E (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥)
    (i : Axis) : (𝐙.subgroupOf 𝐄[i]).Normal :=
  ⟨fun z hz e => mem_subgroupOf.mpr (by
    rw [coe_mul, coe_mul, coe_inv, ZP_comm_R h hbt i (mem_sup_right e.2) (mem_subgroupOf.mp hz),
      mul_inv_cancel_right]
    exact mem_subgroupOf.mp hz)⟩

theorem X_commutator (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥)
    (i : Axis) {a a' : G} (ha : a ∈ 𝐗[i]) (ha' : a' ∈ 𝐗[i]) : a⁻¹ * (a'⁻¹ * a * a') = 1 := by
  have hc := comm_of_mul_self (fun x hx => X_mul_self h hbt i hx) ha ha'
  rw [mul_assoc a'⁻¹, hc, inv_mul_cancel_left, inv_mul_cancel]

theorem maximal_E (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥)
    (i : Axis) :
    ∃ _ : (𝐙.subgroupOf 𝐄[i]).Normal, ∀ S : Subgroup (↥𝐄[i] ⧸ 𝐙.subgroupOf 𝐄[i]),
      Maximal (fun S : Subgroup (↥𝐄[i] ⧸ 𝐙.subgroupOf 𝐄[i]) => IsElementaryAbelian 2 S) S ↔
        S = (𝐗[i].subgroupOf 𝐄[i]).map (QuotientGroup.mk' (𝐙.subgroupOf 𝐄[i])) ∨
          S = ((𝐇 ⊓ 𝐄[i]).subgroupOf 𝐄[i]).map (QuotientGroup.mk' (𝐙.subgroupOf 𝐄[i])) := by
  have := ZP_normal_E h hbt i
  have hZX : 𝐙 ≤ 𝐗[i] := (ZP_le_F h).trans le_sup_left
  have hZH : 𝐙 ≤ 𝐇 ⊓ 𝐄[i] := ((ZP_le_B i).trans (h.B_le_D i)).trans (D_le_Hi h i)
  refine ⟨this, fun S => maximal_elem_quotient _
    (fun x hx => mem_subgroupOf.mpr (hZX (mem_subgroupOf.mp hx)))
    (fun x hx => mem_subgroupOf.mpr (hZH (mem_subgroupOf.mp hx)))
    (fun y hy => ?_) (fun a ha a' ha' => ?_) (fun a ha => ?_) (fun b hb b' hb' => ?_)
    (fun b hb => ?_) ?_ ?_ S⟩
  · rcases mem_X_or_Hi h hbt i y.2 (mem_subgroupOf.mp hy) with h1 | h1
    · exact Or.inl (mem_subgroupOf.mpr h1)
    · exact Or.inr (mem_subgroupOf.mpr h1)
  · rw [mem_subgroupOf, coe_mul, coe_mul, coe_mul, coe_inv, coe_inv,
      X_commutator h hbt i (mem_subgroupOf.mp ha) (mem_subgroupOf.mp ha')]
    exact one_mem _
  · rw [mem_subgroupOf, coe_mul, X_mul_self h hbt i (mem_subgroupOf.mp ha)]
    exact one_mem _
  · rw [mem_subgroupOf, coe_mul, coe_mul, coe_mul, coe_inv, coe_inv]
    exact commutator_mem_ZP h (mem_subgroupOf.mp hb).1 (mem_subgroupOf.mp hb').1
  · rw [mem_subgroupOf, coe_mul]
    exact mul_self_mem_ZP h (mem_subgroupOf.mp hb).1
  · intro hle
    refine X_not_le_H h i fun x hx => ?_
    have h1 : (⟨x, X_le_E h i hx⟩ : 𝐄[i]) ∈ (𝐇 ⊓ 𝐄[i]).subgroupOf 𝐄[i] :=
      hle (mem_subgroupOf.mpr hx)
    exact (mem_subgroupOf.mp h1).1
  · intro hle
    refine t_not_mem_X h i ?_
    have h1 : (⟨t, t_mem_E h i⟩ : 𝐄[i]) ∈ 𝐗[i].subgroupOf 𝐄[i] :=
      hle (mem_subgroupOf.mpr (mem_inf.mpr ⟨t_mem_H, t_mem_E h i⟩))
    exact mem_subgroupOf.mp h1

theorem maximal_R (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥)
    (i : Axis) :
    ∃ _ : (𝐙.subgroupOf 𝐑[i]).Normal,
      (∀ S : Subgroup (↥𝐑[i] ⧸ 𝐙.subgroupOf 𝐑[i]),
        Maximal (fun S : Subgroup (↥𝐑[i] ⧸ 𝐙.subgroupOf 𝐑[i]) => IsElementaryAbelian 2 S) S ↔
          S = (𝐗[i].subgroupOf 𝐑[i]).map (QuotientGroup.mk' (𝐙.subgroupOf 𝐑[i])) ∨
            S = (𝐇.subgroupOf 𝐑[i]).map (QuotientGroup.mk' (𝐙.subgroupOf 𝐑[i]))) ∧
      Nat.card ((𝐗[i].subgroupOf 𝐑[i]).map (QuotientGroup.mk' (𝐙.subgroupOf 𝐑[i]))) =
        Nat.card K ^ 4 ∧
      Nat.card ((𝐇.subgroupOf 𝐑[i]).map (QuotientGroup.mk' (𝐙.subgroupOf 𝐑[i]))) =
        2 * Nat.card K ^ 4 := by
  have := ZP_normal_R h hbt i
  have hZX : 𝐙 ≤ 𝐗[i] := (ZP_le_F h).trans le_sup_left
  have hXR : 𝐗[i] ≤ 𝐑[i] := (X_normal_R h i).1
  have hZR : 𝐙 ≤ 𝐑[i] := hZX.trans hXR
  have hNX : 𝐙.subgroupOf 𝐑[i] ≤ 𝐗[i].subgroupOf 𝐑[i] :=
    fun x hx => mem_subgroupOf.mpr (hZX (mem_subgroupOf.mp hx))
  have hNH : 𝐙.subgroupOf 𝐑[i] ≤ 𝐇.subgroupOf 𝐑[i] :=
    fun x hx => mem_subgroupOf.mpr (ZP_le_H (mem_subgroupOf.mp hx))
  have hcardZ : Nat.card (𝐙.subgroupOf 𝐑[i]) = Nat.card K ^ 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hZR).toEquiv, FCHyp.card_ZP]
  have hq2 : 0 < Nat.card K ^ 2 := by have : 0 < Nat.card K := Nat.card_pos; positivity
  refine ⟨this, fun S => maximal_elem_quotient _ hNX hNH
    (fun y hy => ?_) (fun a ha a' ha' => ?_) (fun a ha => ?_) (fun b hb b' hb' => ?_)
    (fun b hb => ?_) ?_ ?_ S, ?_, ?_⟩
  · rcases mem_X_or_H h hbt i y.2 (mem_subgroupOf.mp hy) with h1 | h1
    · exact Or.inl (mem_subgroupOf.mpr h1)
    · exact Or.inr (mem_subgroupOf.mpr h1)
  · rw [mem_subgroupOf, coe_mul, coe_mul, coe_mul, coe_inv, coe_inv,
      X_commutator h hbt i (mem_subgroupOf.mp ha) (mem_subgroupOf.mp ha')]
    exact one_mem _
  · rw [mem_subgroupOf, coe_mul, X_mul_self h hbt i (mem_subgroupOf.mp ha)]
    exact one_mem _
  · rw [mem_subgroupOf, coe_mul, coe_mul, coe_mul, coe_inv, coe_inv]
    exact commutator_mem_ZP h (mem_subgroupOf.mp hb) (mem_subgroupOf.mp hb')
  · rw [mem_subgroupOf, coe_mul]
    exact mul_self_mem_ZP h (mem_subgroupOf.mp hb)
  · intro hle
    refine X_not_le_H h i fun x hx => ?_
    have h1 : (⟨x, hXR hx⟩ : 𝐑[i]) ∈ 𝐇.subgroupOf 𝐑[i] := hle (mem_subgroupOf.mpr hx)
    exact mem_subgroupOf.mp h1
  · intro hle
    refine t_not_mem_X h i ?_
    have h1 : (⟨t, H_le_R h i t_mem_H⟩ : 𝐑[i]) ∈ 𝐗[i].subgroupOf 𝐑[i] :=
      hle (mem_subgroupOf.mpr t_mem_H)
    exact mem_subgroupOf.mp h1
  · have h1 := card_map_mk' (𝐙.subgroupOf 𝐑[i]) hNX
    rw [hcardZ, Nat.card_congr (subgroupOfEquivOfLe hXR).toEquiv, card_X h i] at h1
    exact Nat.eq_of_mul_eq_mul_right hq2 (by rw [h1]; ring)
  · have h1 := card_map_mk' (𝐙.subgroupOf 𝐑[i]) hNH
    rw [hcardZ, Nat.card_congr (subgroupOfEquivOfLe (H_le_R h i)).toEquiv, h.H_facts.2.2] at h1
    exact Nat.eq_of_mul_eq_mul_right hq2 (by rw [h1]; ring)

end Cent

end BothTrivial

open Subgroup GomiFusion RootAxisTwoCore FullCenter FullCenterRadical FullCenterParabolic
  FullCenterTorus FullCenterWeyl FullCenterMutual BothTrivial
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis
open scoped Matrix Pointwise

theorem standard_symplectic_four_both_trivial_Weyl_products_mutual_normality
    {G : Type} [Group G] [Finite G] (hO : CFSG.Open.standardComponentOddCore G = ⊥)
    {L : Subgroup G} (hL : CFSG.Open.standardComponentIsStandard L) (hLn : ¬ L.Normal)
    {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ n)
    (T : Sylow 2 (centralizer (L : Set G)))
    (hT : IsCyclic (T : Subgroup (centralizer (L : Set G))))
    {t : centralizer (L : Set G)} (htT : t ∈ T) (ht : orderOf t = 2)
    (hcore : CFSG.Open.standardComponentOddCore (centralizer ({(t : G)} : Set G)) = ⊥)
    (P : Sylow 2 L) (φ : L ≃* antiSp K)
    (hφP : (P : Subgroup L).map φ.toMonoidHom = antiUnipotent K) :
    let TG := (T : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype
    let PG := (P : Subgroup L).map L.subtype
    let Q := PG ⊔ TG
    let ZP := (center PG).map PG.subtype
    let U : Axis → Subgroup G := fun i => ((rootU K i).comap φ.toMonoidHom).map L.subtype
    let A : Axis → Subgroup G := fun i => ((rootA K i).comap φ.toMonoidHom).map L.subtype
    let V : Axis → Subgroup G := fun i => zpowers (t : G) ⊔ U i
    let B : Axis → Subgroup G := fun i => zpowers (t : G) ⊔ A i
    let M : Axis → Subgroup G := fun i => normalizer (V i : Set G)
    let N : Axis → Subgroup G := fun i => normalizer (B i : Set G)
    let D : Axis → Subgroup G := fun i => (CFSG.pCore 2 (M i)).map (M i).subtype
    let E : Axis → Subgroup G := fun i => (CFSG.pCore 2 (N i)).map (N i).subtype
    let Qi : Axis → Subgroup G := fun i => Q ⊔ D i
    let R : Axis → Subgroup G := fun i => Q ⊔ E i
    let H := Qi Axis.one ⊔ Qi Axis.two
    let Hi : Axis → Subgroup G := fun i => H ⊓ E i
    let E₀ := E Axis.one ⊓ E Axis.two
    let J₀ := ((diagTorus K).comap φ.toMonoidHom).map L.subtype
    let J : Axis → Subgroup G := fun i => ((axisTorus K i).comap φ.toMonoidHom).map L.subtype
    let F := closure {x : G | ∃ e ∈ E₀, ∃ j ∈ J₀, x = e⁻¹ * (j⁻¹ * e * j)}
    let Fi : Axis → Subgroup G := fun i => F ⊓ D i
    let W : Axis → Subgroup G := fun i => F ⊓ centralizer (J i : Set G)
    let w : Axis → G := fun i => ((φ.symm (weylElt K i) : L) : G)
    let Kc : Axis → Subgroup G := fun i => A i ⊔ Fi i
    let Ks := Kc Axis.one ⊔ Kc Axis.two
    let L₀ : Axis → Subgroup G := fun i => F ⊔ A i
    let Fw : Axis → Subgroup G := fun i => F.map (MulAut.conj (w i)⁻¹).toMonoidHom
    let X : Axis → Subgroup G := fun i => F ⊔ Fw i
    let T₀ := R Axis.one ⊔ R Axis.two
    {x : G | ∃ m ∈ normalizer (Q : Set G), x = m⁻¹ * t * m} = {x | ∃ z ∈ ZP, x = t * z} →
    ⁅A Axis.one, Fi Axis.two⁆ = ⊥ → ⁅A Axis.two, Fi Axis.one⁆ = ⊥ →
    ((Kc Axis.one : Set G) * (Kc Axis.two : Set G) = Ks ∧ (F : Set G) * (PG : Set G) = Ks) ∧
      (∀ i : Axis, L₀ i ≤ Ks ∧ (∀ x ∈ L₀ i, ∀ y ∈ L₀ i, x * y = y * x) ∧
        Nat.card (L₀ i) = (2 ^ n) ^ 5) ∧ L₀ Axis.one ≠ L₀ Axis.two ∧
      (∀ S : Subgroup G, S ≤ Ks → (∀ x ∈ S, ∀ y ∈ S, x * y = y * x) →
        Nat.card S ≤ (2 ^ n) ^ 5 ∧
          (Nat.card S = (2 ^ n) ^ 5 → S = L₀ Axis.one ∨ S = L₀ Axis.two)) ∧
      (∀ i j : Axis, L₀ j ≤ R i ∧ ((L₀ j).subgroupOf (R i)).Normal) ∧
      (∀ i : Axis, IsElementaryAbelian 2 (W i)) ∧ IsElementaryAbelian 2 F ∧
      (∀ i : Axis, (F : Set G) * (Fw i : Set G) = X i ∧ IsElementaryAbelian 2 (X i) ∧
        Nat.card (X i) = (2 ^ n) ^ 6) ∧
      (∀ i : Axis, Hi i = F ⊔ B i ∧ (F : Set G) * (B i : Set G) = Hi i ∧ X i ⊓ H = L₀ i ∧
        (F : Set G) * (A i : Set G) = L₀ i) ∧
      R Axis.one ≤ normalizer (R Axis.two : Set G) ∧
      R Axis.two ≤ normalizer (R Axis.one : Set G) ∧
      ((R Axis.one : Set G) * (R Axis.two : Set G) = T₀ ∧ IsPGroup 2 T₀ ∧
        (∀ i : Axis, R i ≤ T₀ ∧ ((R i).subgroupOf T₀).Normal) ∧
        ZP ≤ (center T₀).map T₀.subtype) ∧
      (∀ i : Axis,
        (∃ _ : (ZP.subgroupOf (E i)).Normal, ∀ S : Subgroup (↥(E i) ⧸ ZP.subgroupOf (E i)),
          Maximal (fun S : Subgroup (↥(E i) ⧸ ZP.subgroupOf (E i)) => IsElementaryAbelian 2 S)
              S ↔
            S = ((X i).subgroupOf (E i)).map (QuotientGroup.mk' (ZP.subgroupOf (E i))) ∨
              S = ((Hi i).subgroupOf (E i)).map (QuotientGroup.mk' (ZP.subgroupOf (E i)))) ∧
        (∃ _ : (ZP.subgroupOf (R i)).Normal,
          (∀ S : Subgroup (↥(R i) ⧸ ZP.subgroupOf (R i)),
            Maximal (fun S : Subgroup (↥(R i) ⧸ ZP.subgroupOf (R i)) =>
                IsElementaryAbelian 2 S) S ↔
              S = ((X i).subgroupOf (R i)).map (QuotientGroup.mk' (ZP.subgroupOf (R i))) ∨
                S = (H.subgroupOf (R i)).map (QuotientGroup.mk' (ZP.subgroupOf (R i)))) ∧
          Nat.card (((X i).subgroupOf (R i)).map (QuotientGroup.mk' (ZP.subgroupOf (R i)))) =
            (2 ^ n) ^ 4 ∧
          Nat.card ((H.subgroupOf (R i)).map (QuotientGroup.mk' (ZP.subgroupOf (R i)))) =
            2 * (2 ^ n) ^ 4)) ∧
      ∀ i : Axis, X i ≤ T₀ ∧ ((X i).subgroupOf T₀).Normal := by
  intro TG PG Q ZP U A V B M N D E Qi R H Hi E₀ J₀ J F Fi W w Kc Ks L₀ Fw X T₀ hfull hb1 hb2
  have hS := setup_of_standard hL hn hK φ T hT htT ht hcore
  have hPG : PG = pull φ (antiUnipotent K) := by
    change (P : Subgroup L).map L.subtype = ((antiUnipotent K).comap φ.toMonoidHom).map L.subtype
    rw [← hφP, comap_map_eq_self_of_injective φ.injective]
  have hZP : ZP = pull φ (antiUnipotentCenter K) := by
    change (center ↥PG).map PG.subtype = _
    rw [hPG, center_pull_antiUnipotent]
  have hfull' : {x : G | ∃ m ∈ normalizer ((pull φ (antiUnipotent K) ⊔ TG : Subgroup G) :
      Set G), x = m⁻¹ * t * m} = {x | ∃ z ∈ pull φ (antiUnipotentCenter K), x = t * z} := by
    rw [← hPG, ← hZP]
    exact hfull
  obtain ⟨hTG₀, hF⟩ := FCHyp.of_setup hS (hO := hO) hLn hfull'
  have hTG : TG = zpowers (t : G) := hTG₀
  clear_value ZP PG TG
  subst hTG hPG hZP
  have hbt : ∀ i : Axis, ⁅A i, F ⊓ D i.swap⁆ = ⊥ := fun i => by
    cases i
    · exact hb1
    · exact hb2
  have hRN1 : R Axis.one ≤ normalizer (R Axis.two : Set G) := R_le_normalizer_R hF hbt Axis.two
  have hRN2 : R Axis.two ≤ normalizer (R Axis.one : Set G) := R_le_normalizer_R hF hbt Axis.one
  refine ⟨⟨K_mul_K hF, F_mul_P hF⟩, fun i => ⟨L_le_Ks hF i,
      fun x hx y hy => L_comm hF hbt i hx hy, (card_L hF i).trans (by rw [hK])⟩, L_ne hF,
    fun S hSK hSc => ?_,
    fun i j => ⟨(L_le_Ks hF j).trans (Ks_normal_R hF i).1, normal_subgroupOf_of_le_normalizer
      fun r hr => mem_normalizer_of_conj_le fun l hl => conj_R_mem_L' hF hbt i j hr hl⟩,
    fun i => isElementaryAbelian_of (fun x hx y hy => F_comm hF hx.1 hy.1)
      (fun x hx => W_mul_self hF hbt i hx),
    isElementaryAbelian_of (fun x hx y hy => F_comm hF hx hy) (fun x hx => F_mul_self hF hbt hx),
    fun i => ⟨F_mul_Fw' hF i, X_elem hF hbt i, (card_X hF i).trans (by rw [hK])⟩,
    fun i => ⟨Hi_eq hF i, F_mul_B hF i, X_inf_H hF i, L_mul hF i⟩, hRN1, hRN2,
    ⟨(coe_mul_of_left_le_normalizer_right _ _ hRN1).symm,
      IsPGroup.to_sup_of_normal_right' (R_isPGroup hF _) (R_isPGroup hF _) hRN1,
      fun i => ⟨?_, normal_subgroupOf_of_le_normalizer (T_le_normalizer_R hF hbt i)⟩,
      ZP_le_center_T hF hbt⟩, fun i => ⟨maximal_E hF hbt i, ?_⟩, fun i => ⟨?_, ?_⟩⟩
  · obtain ⟨h1, h2⟩ := abelian_Ks hF hbt hSK hSc
    rw [hK] at h1 h2
    exact ⟨h1, h2⟩
  · cases i
    · exact le_sup_left
    · exact le_sup_right
  · obtain ⟨hN, hmax, h1, h2⟩ := maximal_R hF hbt i
    exact ⟨hN, hmax, h1.trans (by rw [hK]), h2.trans (by rw [hK])⟩
  · have hXR : X i ≤ R i := (X_normal_R hF i).1
    cases i
    · exact hXR.trans le_sup_left
    · exact hXR.trans le_sup_right
  · exact normal_subgroupOf_of_le_normalizer fun g hg =>
      mem_normalizer_of_conj_le fun x hx => conj_T_mem_X hF hbt i hg hx

end CFSG.LocalAnalysis.SymplecticFourStandard
