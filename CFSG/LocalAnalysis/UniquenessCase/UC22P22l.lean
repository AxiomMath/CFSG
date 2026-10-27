module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22j
import CFSG.LocalAnalysis.UniquenessCase.UC22P20d
import CFSG.LocalAnalysis.UniquenessCase.UC22P20e
import CFSG.GH74.KGroups.PSL2
import CFSG.Blueprint.LieModelAPI
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aResidual
public import CFSG.Quasithin.H13.QRCEvenRankTwoOddCyclic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aResidualLin
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aResidualSp

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup CFSG.Goldschmidt
open scoped commutatorElement MatrixGroups Pointwise

section Abstract

@[expose] def OddAbelianIn {X : Type} [Group X] (Y : Subgroup X) : Prop :=
  ∀ W : Subgroup X, W ≤ Y → Odd (Nat.card W) → ∀ a ∈ W, ∀ b ∈ W, a * b = b * a

@[expose] def OddCyclicProper (H : Type) [Group H] : Prop :=
  (∀ S : Sylow 2 H, (S : Subgroup H) ≠ ⊥) ∧
    ∀ (S : Sylow 2 H) (Y : Subgroup H), (S : Subgroup H) ≤ Y → Y ≠ ⊤ → ∀ W : Subgroup H, W ≤ Y →
      Odd (Nat.card W) → IsCyclic W

theorem uc22p22l_ocp_typeI
    {H : Type} [Group H] [Finite H] [IsSimpleGroup H] (hI : IsGoldTypeI H) :
    OddCyclicProper H := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨fun S hbot => ?_, fun S Y hSY hY W hWY hW => ?_⟩
  · obtain ⟨D, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hcoat, -⟩ := G32 H hI S
    have htop : Subgroup.normalizer ((S : Subgroup H) : Set H) = ⊤ := by
      rw [hbot]
      exact Subgroup.normalizer_eq_top_iff.2 inferInstance
    exact hcoat.1 htop
  · obtain ⟨D, hDN, hDcyc, -, -, hsup, -, -, -, -, -, -, -, -, -, -, -, -, hmax⟩ := G32 H hI S
    have hYN : Y ≤ (S : Subgroup H) ⊔ D := by
      rw [hsup]
      exact hmax _ hSY hY
    set N : Subgroup H := (S : Subgroup H) ⊔ D with hNdef
    haveI hnorm : ((S : Subgroup H).subgroupOf N).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
        (sup_le Subgroup.le_normalizer hDN)
    have hsurjD : Function.Surjective ((QuotientGroup.mk' ((S : Subgroup H).subgroupOf N)).comp
        (Subgroup.inclusion (le_sup_right : D ≤ N))) := by
      intro z
      obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk'_surjective ((S : Subgroup H).subgroupOf N) z
      have hy' : y ∈ ((S : Subgroup H) : Set H) * (D : Set H) := by
        rw [← Subgroup.coe_mul_of_right_le_normalizer_left (S : Subgroup H) D hDN]
        exact hy
      obtain ⟨u, hu, v, hv, rfl⟩ := hy'
      refine ⟨⟨v, hv⟩, ?_⟩
      rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
        Subgroup.mem_subgroupOf]
      have h := (Subgroup.mem_normalizer_iff''.mp (hDN hv) u).mp hu
      simpa [mul_assoc] using h
    haveI : IsCyclic ↥D := hDcyc
    haveI : IsCyclic (↥N ⧸ (S : Subgroup H).subgroupOf N) := isCyclic_of_surjective _ hsurjD
    have hWN : ∀ w : W, (w : H) ∈ N := fun w => hYN (hWY w.2)
    let g : W →* N := W.subtype.codRestrict N hWN
    let f : W →* ↥N ⧸ (S : Subgroup H).subgroupOf N := (QuotientGroup.mk' _).comp g
    have hinj : Function.Injective f := by
      rw [injective_iff_map_eq_one]
      intro w hw
      have h1 : (w : H) ∈ (S : Subgroup H) := by
        have : g w ∈ (S : Subgroup H).subgroupOf N := (QuotientGroup.eq_one_iff _).1 hw
        exact this
      have h2 : Odd (orderOf (w : H)) := hW.of_dvd_nat (Subgroup.orderOf_dvd_natCard W w.2)
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 S.isPGroup') ⟨(w : H), h1⟩
      rw [Subgroup.orderOf_mk] at hk
      have hk0 : k = 0 := by
        by_contra hk0
        rw [hk] at h2
        exact (Nat.not_even_iff_odd.2 h2) (Nat.even_pow.2 ⟨even_two, hk0⟩)
      rw [hk0, pow_zero] at hk
      exact Subtype.ext (orderOf_eq_one_iff.1 hk)
    exact isCyclic_of_injective f hinj

theorem uc22p22l_ocp_sixty {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (hX : Nat.card X = 60) : OddCyclicProper X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : ∀ S : Sylow 2 X, Nat.card (S : Subgroup X) = 4 := by
    intro S
    rw [Sylow.card_eq_multiplicity, hX]
    have h60 : (60 : ℕ) = 2 ^ 2 * 15 := by norm_num
    have hf : (Nat.factorization 60) 2 = 2 := by
      rw [h60, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
        Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    rw [hf]
    norm_num
  refine ⟨fun S hbot => ?_, fun S Y hSY hY W hWY hW => ?_⟩
  · have := hS S
    rw [hbot, Subgroup.card_bot] at this
    omega
  have h4 : 4 ∣ Nat.card Y := hS S ▸ Subgroup.card_dvd_of_le hSY
  have h60 : Nat.card Y ∣ 60 := hX ▸ Subgroup.card_subgroup_dvd_card Y
  have hne60 : Nat.card Y ≠ 60 := fun h =>
    hY ((Subgroup.card_eq_iff_eq_top Y).1 (h.trans hX.symm))
  have hne20 : Nat.card Y ≠ 20 := by
    intro h20
    have hidx : Y.index = 3 := by
      have := Subgroup.card_mul_index Y
      rw [h20, hX] at this
      omega
    haveI : Y.FiniteIndex := ⟨by omega⟩
    have hcore : Y.normalCore = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Y.normalCore with h | h
      · exact h
      · exact absurd (eq_top_iff.2 (h ▸ Y.normalCore_le)) hY
    have h1 := Subgroup.index_normalCore_dvd_factorial_index Y
    rw [hcore, Subgroup.index_bot, hX, hidx] at h1
    norm_num [Nat.factorial] at h1
  have hm : Nat.card Y = 4 ∨ Nat.card Y = 12 := by
    have hmem : Nat.card Y ∈ Nat.divisors 60 := Nat.mem_divisors.2 ⟨h60, by norm_num⟩
    have hdiv : Nat.divisors 60 = {1, 2, 3, 4, 5, 6, 10, 12, 15, 20, 30, 60} := by decide
    rw [hdiv] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    omega
  have hW12 : Nat.card W ∣ 12 := by
    have := Subgroup.card_dvd_of_le hWY
    rcases hm with h | h <;> rw [h] at this <;> exact this.trans (by norm_num)
  have hW13 : Nat.card W = 1 ∨ Nat.card W = 3 := by
    have hmem : Nat.card W ∈ Nat.divisors 12 := Nat.mem_divisors.2 ⟨hW12, by norm_num⟩
    have hdiv : Nat.divisors 12 = {1, 2, 3, 4, 6, 12} := by decide
    rw [hdiv] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    obtain ⟨k, hk⟩ := hW
    omega
  rcases hW13 with h | h
  · haveI : Subsingleton W := (Nat.card_eq_one_iff_unique.1 h).1
    infer_instance
  · haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact isCyclic_of_prime_card h

theorem uc22p22l_commutator_le {A : Type*} [Group A] {Y : Subgroup A}
    (h : ∀ a : A, ∃ y ∈ Y, y⁻¹ * a ∈ center A) : _root_.commutator A ≤ Y := by
  rw [_root_.commutator_def]
  refine Subgroup.commutator_le.2 fun g₁ _ g₂ _ => ?_
  obtain ⟨y₁, hy₁, hz₁⟩ := h g₁
  obtain ⟨y₂, hy₂, hz₂⟩ := h g₂
  have e : ⁅g₁, g₂⁆ = ⁅y₁, y₂⁆ := by
    have h1 : g₁ = y₁ * (y₁⁻¹ * g₁) := by group
    have h2 : g₂ = y₂ * (y₂⁻¹ * g₂) := by group
    calc ⁅g₁, g₂⁆ = ⁅y₁ * (y₁⁻¹ * g₁), g₂⁆ := by rw [← h1]
      _ = ⁅y₁, g₂⁆ := uc22p22j_comm_mul_central hz₁ g₂
      _ = ⁅y₁, y₂ * (y₂⁻¹ * g₂)⁆ := by rw [← h2]
      _ = ⁅y₁, y₂⁆ := uc22p22j_comm_central_mul hz₂ y₁
  rw [e]
  simp only [commutatorElement_def]
  exact Y.mul_mem (Y.mul_mem (Y.mul_mem hy₁ hy₂) (Y.inv_mem hy₁)) (Y.inv_mem hy₂)

theorem uc22p22l_normal_of_commuting {X : Type*} [Group X] {X₁ X₂ : Subgroup X}
    (hsup : X₁ ⊔ X₂ = ⊤) (hcomm : ∀ a ∈ X₁, ∀ b ∈ X₂, a * b = b * a) : X₁.Normal := by
  rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hsup]
  refine sup_le Subgroup.le_normalizer fun b hb => ?_
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    have : b * a * b⁻¹ = a := by
      rw [← hcomm a ha b hb]
      group
    rw [this]
    exact ha
  · intro ha
    have h1 := hcomm _ ha b⁻¹ (X₂.inv_mem hb)
    have : a = b * a * b⁻¹ := by
      have h2 : b⁻¹ * (b * a * b⁻¹) * b = b * a * b⁻¹ := by
        rw [← h1]
        group
      calc a = b⁻¹ * (b * a * b⁻¹) * b := by group
        _ = b * a * b⁻¹ := h2
    rw [this]
    exact ha

theorem uc22p22l_extend {X : Type*} [Group X] {X₁ X₂ : Subgroup X}
    (hsup : X₁ ⊔ X₂ = ⊤) (hcomm : ∀ a ∈ X₁, ∀ b ∈ X₂, a * b = b * a)
    {H : Type*} [Group H] (q : ↥X₁ →* H) (hq : ∀ a : ↥X₁, (a : X) ∈ X₂ → q a = 1) :
    ∃ ρ : X →* H, (∀ a : ↥X₁, ρ (a : X) = q a) ∧ ∀ b ∈ X₂, ρ b = 1 := by
  have hN₂ : X₂.Normal := uc22p22l_normal_of_commuting (by rwa [sup_comm])
    (fun b hb a ha => (hcomm a ha b hb).symm)
  have hle : X₁ ≤ Subgroup.normalizer (X₂ : Set X) := by
    rw [Subgroup.normalizer_eq_top_iff.2 hN₂]
    exact le_top
  let φ : ↥X₁ × ↥X₂ →* X := X₁.subtype.noncommCoprod X₂.subtype (fun a b => hcomm a a.2 b b.2)
  have hφ : Function.Surjective φ := by
    intro x
    have hx : x ∈ X₁ ⊔ X₂ := hsup ▸ Subgroup.mem_top x
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right X₁ X₂ hle] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  have hker : φ.ker ≤ (q.comp (MonoidHom.fst ↥X₁ ↥X₂)).ker := by
    rintro ⟨a, b⟩ hab
    have h1 : (a : X) * (b : X) = 1 := hab
    have h2 : (a : X) = ((b : ↥X₂) : X)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have h3 : (a : X) ∈ X₂ := by
      rw [h2]
      exact X₂.inv_mem b.2
    exact hq a h3
  refine ⟨MonoidHom.liftOfSurjective φ hφ ⟨q.comp (MonoidHom.fst ↥X₁ ↥X₂), hker⟩, fun a => ?_,
    fun b hb => ?_⟩
  · have h : (a : X) = φ (a, 1) := by
      show (a : X) = X₁.subtype a * X₂.subtype 1
      simp
    rw [h, MonoidHom.liftOfRightInverse_comp_apply]
    simp
  · have h : b = φ (1, ⟨b, hb⟩) := by
      show b = X₁.subtype 1 * X₂.subtype ⟨b, hb⟩
      simp
    rw [h, MonoidHom.liftOfRightInverse_comp_apply]
    simp

theorem uc22p22l_factor_cyclic {X : Type} [Group X] [Finite X] {H : Type} [Group H]
    [IsSimpleGroup H] (hH : OddCyclicProper H) {X₁ : Subgroup X} [hX₁ : X₁.Normal]
    (hperf : ⁅X₁, X₁⁆ = X₁) (ρ : X →* H) (hρ : Function.Surjective (ρ.comp X₁.subtype))
    (hker : ∀ a : ↥X₁, ρ (a : X) = 1 → a ∈ center ↥X₁) (S : Sylow 2 X) {Y : Subgroup X}
    (hSY : (S : Subgroup X) ≤ Y) (hY : ¬ X₁ ≤ Y) {W : Subgroup X} (hWY : W ≤ Y)
    (hW : Odd (Nat.card W)) : IsCyclic ↥(W.map ρ) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hρs : Function.Surjective ρ := fun h => by
    obtain ⟨a, ha⟩ := hρ h
    exact ⟨(a : X), ha⟩
  haveI : Finite H := Finite.of_surjective ρ hρs
  let S' : Sylow 2 H := S.mapSurjective hρs
  have hS'Y : (S' : Subgroup H) ≤ Y.map ρ := by
    rw [Sylow.coe_mapSurjective]
    exact Subgroup.map_mono hSY
  have hYtop : Y.map ρ ≠ ⊤ := by
    intro htop
    apply hY
    set K : Subgroup H := (Y ⊓ X₁).map ρ with hK
    haveI hKn : K.Normal := by
      refine ⟨fun k hk h => ?_⟩
      obtain ⟨z, hz, rfl⟩ := hk
      have hh : h ∈ Y.map ρ := htop ▸ Subgroup.mem_top h
      obtain ⟨y, hy, rfl⟩ := hh
      refine ⟨y * z * y⁻¹, ⟨Y.mul_mem (Y.mul_mem hy hz.1) (Y.inv_mem hy), ?_⟩, by simp⟩
      exact hX₁.conj_mem z hz.2 y
    have hKbot : K ≠ ⊥ := by
      intro hbot
      have hSyl : CFSG.ABGLocalTools.IsSylowOf 2 (S : Subgroup X) ⊤ := by
        rw [CFSG.ABGLocalTools.isSylowOf_iff]
        refine ⟨le_top, S.isPGroup', ?_⟩
        rw [Subgroup.relIndex_top_right]
        exact S.not_dvd_index
      have hSyl1 := hSyl.inf_of_le_normalizer (le_top : X₁ ≤ ⊤)
        (by rw [Subgroup.normalizer_eq_top_iff.2 hX₁])
      obtain ⟨Q, hQ⟩ := hSyl1.exists_sylow_eq_subgroupOf
      let Q' : Sylow 2 H := Q.mapSurjective hρ
      have hQ'ne := hH.1 Q'
      obtain ⟨⟨h, hhQ⟩, hh1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hQ'ne
      rw [Sylow.coe_mapSurjective] at hhQ
      obtain ⟨t, htQ, rfl⟩ := hhQ
      have htS : (t : X) ∈ (S : Subgroup X) ⊓ X₁ := by
        have : t ∈ (Q : Subgroup ↥X₁) := htQ
        rw [hQ] at this
        exact this
      have hmem : ρ (t : X) ∈ K := ⟨(t : X), ⟨hSY htS.1, htS.2⟩, rfl⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hh1 (Subtype.ext hmem)
    have hKtop : K = ⊤ := (IsSimpleGroup.eq_bot_or_eq_top_of_normal K).resolve_left hKbot
    set Y₁ : Subgroup ↥X₁ := (Y ⊓ X₁).subgroupOf X₁ with hY₁
    have hcom : _root_.commutator ↥X₁ ≤ Y₁ := by
      refine uc22p22l_commutator_le fun a => ?_
      have ha : ρ (a : X) ∈ K := hKtop ▸ Subgroup.mem_top _
      obtain ⟨z, hz, hza⟩ := ha
      refine ⟨⟨z, hz.2⟩, hz, hker _ ?_⟩
      simp [hza]
    haveI : Group.IsPerfect ↥X₁ := Subgroup.isPerfect_iff.2 hperf
    have hY₁top : Y₁ = ⊤ := top_unique (Group.IsPerfect.commutator_eq_top.symm.le.trans hcom)
    intro x hx
    have : (⟨x, hx⟩ : ↥X₁) ∈ Y₁ := hY₁top ▸ Subgroup.mem_top _
    exact this.1
  have hodd : Odd (Nat.card (W.map ρ)) := by
    have hsurj : Function.Surjective (ρ.subgroupMap W) := MonoidHom.subgroupMap_surjective _ _
    exact hW.of_dvd_nat (Subgroup.card_dvd_of_surjective hsurj)
  exact hH.2 S' (Y.map ρ) hS'Y hYtop (W.map ρ) (Subgroup.map_mono hWY) hodd

theorem uc22p22l_comm_of_cyclic_image {A H : Type*} [Group A] [Group H] (q : A →* H)
    (hk : q.ker ≤ center A) (C : Subgroup H) [IsCyclic C] {a a' : A} (ha : q a ∈ C)
    (ha' : q a' ∈ C) : a * a' = a' * a := by
  let f : ↥(C.comap q) →* ↥C := q.subgroupComap C
  have hf : f.ker ≤ center ↥(C.comap q) := by
    intro x hx
    have h1 : q (x : A) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
    have h2 : (x : A) ∈ center A := hk (MonoidHom.mem_ker.2 h1)
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.1 h2 y)
  exact congrArg Subtype.val (commutative_of_cyclic_center_quotient f hf ⟨a, ha⟩ ⟨a', ha'⟩)

theorem uc22p22l_oddAbelianIn_product {X : Type} [Group X] [Finite X] {X₁ X₂ : Subgroup X}
    (hsup : X₁ ⊔ X₂ = ⊤) (hcomm : ∀ a ∈ X₁, ∀ b ∈ X₂, a * b = b * a)
    (hperf₁ : ⁅X₁, X₁⁆ = X₁) (hperf₂ : ⁅X₂, X₂⁆ = X₂)
    {H₁ H₂ : Type} [Group H₁] [Group H₂] [IsSimpleGroup H₁] [IsSimpleGroup H₂]
    (hH₁ : OddCyclicProper H₁) (hH₂ : OddCyclicProper H₂)
    (q₁ : ↥X₁ →* H₁) (q₂ : ↥X₂ →* H₂) (hq₁ : Function.Surjective q₁)
    (hq₂ : Function.Surjective q₂) (hk₁ : q₁.ker = center ↥X₁) (hk₂ : q₂.ker = center ↥X₂)
    (S : Sylow 2 X) {Y : Subgroup X} (hSY : (S : Subgroup X) ≤ Y) (hY₁ : ¬ X₁ ≤ Y)
    (hY₂ : ¬ X₂ ≤ Y) : OddAbelianIn Y := by
  classical
  have hsup' : X₂ ⊔ X₁ = ⊤ := by rwa [sup_comm]
  have hcomm' : ∀ b ∈ X₂, ∀ a ∈ X₁, b * a = a * b := fun b hb a ha => (hcomm a ha b hb).symm
  haveI hN₁ : X₁.Normal := uc22p22l_normal_of_commuting hsup hcomm
  haveI hN₂ : X₂.Normal := uc22p22l_normal_of_commuting hsup' hcomm'
  have hle : X₁ ≤ Subgroup.normalizer (X₂ : Set X) := by
    rw [Subgroup.normalizer_eq_top_iff.2 hN₂]
    exact le_top
  obtain ⟨ρ₁, hρ₁a, hρ₁b⟩ := uc22p22l_extend hsup hcomm q₁ (fun a ha => by
    have : a ∈ center ↥X₁ := by
      rw [Subgroup.mem_center_iff]
      intro c
      exact Subtype.ext (hcomm c c.2 a ha)
    rw [← hk₁] at this
    exact this)
  obtain ⟨ρ₂, hρ₂b, hρ₂a⟩ := uc22p22l_extend hsup' hcomm' q₂ (fun b hb => by
    have : b ∈ center ↥X₂ := by
      rw [Subgroup.mem_center_iff]
      intro c
      exact Subtype.ext (hcomm' c c.2 b hb)
    rw [← hk₂] at this
    exact this)
  have hρ₁s : Function.Surjective (ρ₁.comp X₁.subtype) := by
    have : ρ₁.comp X₁.subtype = q₁ := MonoidHom.ext fun a => hρ₁a a
    rw [this]
    exact hq₁
  have hρ₂s : Function.Surjective (ρ₂.comp X₂.subtype) := by
    have : ρ₂.comp X₂.subtype = q₂ := MonoidHom.ext fun a => hρ₂b a
    rw [this]
    exact hq₂
  intro W hWY hW w hw w' hw'
  have hc₁ : IsCyclic ↥(W.map ρ₁) :=
    uc22p22l_factor_cyclic hH₁ hperf₁ ρ₁ hρ₁s (fun a ha => by
      rw [hρ₁a] at ha
      rw [← hk₁]
      exact ha) S hSY hY₁ hWY hW
  have hc₂ : IsCyclic ↥(W.map ρ₂) :=
    uc22p22l_factor_cyclic hH₂ hperf₂ ρ₂ hρ₂s (fun a ha => by
      rw [hρ₂b] at ha
      rw [← hk₂]
      exact ha) S hSY hY₂ hWY hW
  have hdec : ∀ x : X, ∃ a ∈ X₁, ∃ b ∈ X₂, x = a * b := by
    intro x
    have hx : x ∈ X₁ ⊔ X₂ := hsup ▸ Subgroup.mem_top x
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right X₁ X₂ hle] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    exact ⟨a, ha, b, hb, rfl⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := hdec w
  obtain ⟨a', ha', b', hb', rfl⟩ := hdec w'
  have hr₁ : ∀ (c : X) (hc : c ∈ X₁) (d : X) (hd : d ∈ X₂), c * d ∈ W →
      q₁ ⟨c, hc⟩ ∈ W.map ρ₁ := by
    intro c hc d hd hcd
    refine ⟨c * d, hcd, ?_⟩
    rw [map_mul, hρ₁b d hd, mul_one]
    exact hρ₁a ⟨c, hc⟩
  have hr₂ : ∀ (c : X) (hc : c ∈ X₁) (d : X) (hd : d ∈ X₂), c * d ∈ W →
      q₂ ⟨d, hd⟩ ∈ W.map ρ₂ := by
    intro c hc d hd hcd
    refine ⟨c * d, hcd, ?_⟩
    rw [map_mul, hρ₂a c hc, one_mul]
    exact hρ₂b ⟨d, hd⟩
  haveI := hc₁
  haveI := hc₂
  have haa : a * a' = a' * a :=
    congrArg Subtype.val (uc22p22l_comm_of_cyclic_image q₁ hk₁.le (W.map ρ₁)
      (a := ⟨a, ha⟩) (a' := ⟨a', ha'⟩) (hr₁ a ha b hb hw) (hr₁ a' ha' b' hb' hw'))
  have hbb : b * b' = b' * b :=
    congrArg Subtype.val (uc22p22l_comm_of_cyclic_image q₂ hk₂.le (W.map ρ₂)
      (a := ⟨b, hb⟩) (a' := ⟨b', hb'⟩) (hr₂ a ha b hb hw) (hr₂ a' ha' b' hb' hw'))
  calc a * b * (a' * b') = a * (b * a') * b' := by group
    _ = a * (a' * b) * b' := by rw [← hcomm a' ha' b hb]
    _ = (a * a') * (b * b') := by group
    _ = (a' * a) * (b' * b) := by rw [haa, hbb]
    _ = a' * (a * b') * b := by group
    _ = a' * (b' * a) * b := by rw [hcomm a ha b' hb']
    _ = a' * b' * (a * b) := by group

theorem uc22p22l_mem_center_equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) (x : B) :
    e.symm x ∈ center A ↔ x ∈ center B := by
  rw [Subgroup.mem_center_iff, Subgroup.mem_center_iff]
  constructor
  · intro h y
    have := h (e.symm y)
    simpa using congrArg e this
  · intro h a
    have := h (e a)
    apply e.injective
    simpa using this

theorem uc22p22l_ocp_of_shape
    {B : Type} [Group B] [Finite B] (hperf : _root_.commutator B = ⊤) {n : ℕ}
    (h : IsSz B n ∨ IsL2 B n ∨ IsSU3 B n) :
    IsSimpleGroup (B ⧸ center B) ∧ OddCyclicProper (B ⧸ center B) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases h with hSz | hL2 | hU
  · obtain ⟨hs, hI⟩ := uc22p22j_typeI_of_shape hperf (Or.inl hSz)
    haveI := hs
    exact ⟨hs, uc22p22l_ocp_typeI hI⟩
  · have hn2 : 2 ≤ n := by
      obtain ⟨-, h1n, -, hne, -⟩ := CFSG.Blueprint.LieModel.admissible hL2
      by_contra hlt
      have : n = 1 := by omega
      subst this
      exact hne rfl
    rcases Nat.lt_or_ge n 3 with h3 | h3
    · obtain rfl : n = 2 := by omega
      obtain ⟨E⟩ := CFSG.GH74.KGroups.PSL2.psl2_equiv_of_lieModel (F := GaloisField 2 2) 2 2
        (by omega) (GaloisField.card 2 2 (by omega)) hL2
      have hB : fusionIsBenderGroup B := Or.inl ⟨2, le_rfl, ⟨E⟩⟩
      haveI hsB := CFSG.QuasithinUnique.RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup hB
      have hZ : center B = ⊥ := uc22p22j_center_bot hperf hB
      let e1 : B ⧸ center B ≃* B :=
        (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
      haveI hsq : IsSimpleGroup (B ⧸ center B) := e1.isSimpleGroup
      have hcard : Nat.card (B ⧸ center B) = 60 := by
        rw [Nat.card_congr e1.toEquiv, Nat.card_congr E.toEquiv,
          CFSG.Walter.psl2_even_card (by omega)]
        norm_num
      exact ⟨hsq, uc22p22l_ocp_sixty hcard⟩
    · obtain ⟨hs, hI⟩ := uc22p22j_typeI_of_shape hperf (Or.inr (Or.inl ⟨hL2, h3⟩))
      haveI := hs
      exact ⟨hs, uc22p22l_ocp_typeI hI⟩
  · obtain ⟨hs, hI⟩ := uc22p22j_typeI_of_shape hperf (Or.inr (Or.inr hU))
    haveI := hs
    exact ⟨hs, uc22p22l_ocp_typeI hI⟩

theorem uc22p22l_lift {Λ : Type} [Group Λ] [Finite Λ] {Ω : Subgroup Λ}
    (hOΩ : CFSG.pCore 2 Λ ≤ Ω)
    (hX : OddAbelianIn (Ω.map (QuotientGroup.mk' (CFSG.pCore 2 Λ)))) {V : Subgroup Λ}
    (hVΩ : V ≤ Ω) (hV : Odd (Nat.card V)) {a b : Λ} (ha : a ∈ V) (hb : b ∈ V) :
    a * b = b * a := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O : Subgroup Λ := CFSG.pCore 2 Λ with hO
  let π : Λ →* Λ ⧸ O := QuotientGroup.mk' O
  have hW : Odd (Nat.card (V.map π)) := by
    have hsurj : Function.Surjective (π.subgroupMap V) := MonoidHom.subgroupMap_surjective _ _
    exact hV.of_dvd_nat (Subgroup.card_dvd_of_surjective hsurj)
  have habel := hX (V.map π) (Subgroup.map_mono hVΩ) hW (π a) ⟨a, ha, rfl⟩ (π b) ⟨b, hb, rfl⟩
  have hκO : ⁅a, b⁆ ∈ O := by
    have h1 : π ⁅a, b⁆ = ⁅π a, π b⁆ := map_commutatorElement π a b
    rw [commutatorElement_eq_one_iff_mul_comm.2 habel] at h1
    exact (QuotientGroup.eq_one_iff _).1 h1
  have hκV : ⁅a, b⁆ ∈ V := by
    simp only [commutatorElement_def]
    exact V.mul_mem (V.mul_mem (V.mul_mem ha hb) (V.inv_mem ha)) (V.inv_mem hb)
  have hodd : Odd (orderOf ⁅a, b⁆) := hV.of_dvd_nat (Subgroup.orderOf_dvd_natCard V hκV)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 (CFSG.pCore_isPGroup (p := 2) (G := Λ)))
    ⟨⁅a, b⁆, hκO⟩
  rw [Subgroup.orderOf_mk] at hk
  have hk0 : k = 0 := by
    by_contra hk0
    rw [hk] at hodd
    exact (Nat.not_even_iff_odd.2 hodd) (Nat.even_pow.2 ⟨even_two, hk0⟩)
  rw [hk0, pow_zero, orderOf_eq_one_iff] at hk
  exact commutatorElement_eq_one_iff_mul_comm.1 hk

end Abstract

section GL2

variable {F : Type*} [Field F]

theorem uc22p22l_commute_mem_span {x y : Matrix (Fin 2) (Fin 2) F}
    (hx : ∀ c : F, x ≠ c • (1 : Matrix (Fin 2) (Fin 2) F)) (hxy : x * y = y * x) :
    ∃ α β : F, y = α • (1 : Matrix (Fin 2) (Fin 2) F) + β • x := by
  obtain ⟨p, q, r, s, rfl⟩ : ∃ p q r s, x = !![p, q; r, s] :=
    ⟨x 0 0, x 0 1, x 1 0, x 1 1, Matrix.eta_fin_two x⟩
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d, y = !![a, b; c, d] :=
    ⟨y 0 0, y 0 1, y 1 0, y 1 1, Matrix.eta_fin_two y⟩
  have h11 := congrFun (congrFun hxy 0) 0
  have h12 := congrFun (congrFun hxy 0) 1
  have h21 := congrFun (congrFun hxy 1) 0
  have h22 := congrFun (congrFun hxy 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h11 h12 h21 h22
  by_cases hq : q = 0
  · by_cases hr : r = 0
    · have hps : p ≠ s := by
        intro h
        apply hx p
        ext i j
        fin_cases i <;> fin_cases j <;> simp [h, hq, hr]
      have hps' : p - s ≠ 0 := sub_ne_zero.2 hps
      have hb : b = 0 := by
        subst hq
        have : b * (p - s) = 0 := by linear_combination h12
        exact (mul_eq_zero.1 this).resolve_right hps'
      have hc : c = 0 := by
        subst hr
        have : c * (p - s) = 0 := by linear_combination -h21
        exact (mul_eq_zero.1 this).resolve_right hps'
      refine ⟨a - (a - d) / (p - s) * p, (a - d) / (p - s), ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hb, hc, hq, hr] <;> field_simp <;> ring
    · have hb : b = 0 := by
        subst hq
        have : r * b = 0 := by linear_combination h22
        exact (mul_eq_zero.1 this).resolve_left hr
      refine ⟨a - c / r * p, c / r, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hb, hq] <;> field_simp
      · linear_combination -h21
  · refine ⟨a - b / q * p, b / q, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> field_simp
    · linear_combination h11
    · linear_combination h12

theorem uc22p22l_trace_ne_zero [CharP F 2] {x : GL (Fin 2) F}
    (hx : ∀ c : F, (x : Matrix (Fin 2) (Fin 2) F) ≠ c • (1 : Matrix (Fin 2) (Fin 2) F))
    (hxo : Odd (orderOf x)) : (x : Matrix (Fin 2) (Fin 2) F).trace ≠ 0 := by
  intro ht
  obtain ⟨k, hk⟩ := hxo
  have hxk : x ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one x
  have hCH := CFSG.LinearAlgebra.SteinbergBQ.mul_self_fin_two (x : Matrix (Fin 2) (Fin 2) F)
  rw [ht, zero_smul, zero_sub, CharTwo.neg_eq] at hCH
  have h3 : x = x ^ (2 * (k + 1)) := by
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 by ring, pow_succ, hxk, one_mul]
  have h4 : (x : Matrix (Fin 2) (Fin 2) F) = (x : Matrix (Fin 2) (Fin 2) F) ^ (2 * (k + 1)) := by
    conv_lhs => rw [h3]
    exact Units.val_pow_eq_pow_val _ _
  refine hx ((x : Matrix (Fin 2) (Fin 2) F).det ^ (k + 1)) ?_
  calc (x : Matrix (Fin 2) (Fin 2) F) = (x : Matrix (Fin 2) (Fin 2) F) ^ (2 * (k + 1)) := h4
    _ = ((x : Matrix (Fin 2) (Fin 2) F) ^ 2) ^ (k + 1) := by rw [pow_mul]
    _ = ((x : Matrix (Fin 2) (Fin 2) F).det • (1 : Matrix (Fin 2) (Fin 2) F)) ^ (k + 1) := by
        rw [pow_two, hCH]
    _ = (x : Matrix (Fin 2) (Fin 2) F).det ^ (k + 1) • (1 : Matrix (Fin 2) (Fin 2) F) := by
        rw [smul_pow, one_pow]

theorem uc22p22l_gl2_odd_commute [CharP F 2] {x g : GL (Fin 2) F}
    (hx : ∀ c : F, (x : Matrix (Fin 2) (Fin 2) F) ≠ c • (1 : Matrix (Fin 2) (Fin 2) F))
    (hxo : Odd (orderOf x)) (hgo : Odd (orderOf g)) {α β : F}
    (h : ((g * x * g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      α • (1 : Matrix (Fin 2) (Fin 2) F) + β • (x : Matrix (Fin 2) (Fin 2) F)) :
    g * x = x * g := by
  have ht := uc22p22l_trace_ne_zero hx hxo
  have htr : ((g * x * g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).trace =
      (x : Matrix (Fin 2) (Fin 2) F).trace := by
    rw [Units.val_mul, Units.val_mul]
    exact Matrix.trace_units_conj g _
  have hdet : ((g * x * g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det =
      (x : Matrix (Fin 2) (Fin 2) F).det := by
    rw [Units.val_mul, Units.val_mul]
    exact Matrix.det_units_conj g _
  rw [h] at htr hdet
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  obtain ⟨p, q, r, s, hXdef⟩ : ∃ p q r s, (x : Matrix (Fin 2) (Fin 2) F) = !![p, q; r, s] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  rw [hXdef] at htr hdet ht
  simp [Matrix.trace_fin_two, Matrix.det_fin_two] at htr hdet ht
  have hps : p + s ≠ 0 := ht
  have hβ : β = 1 := by
    have : (β - 1) * (p + s) = 0 := by linear_combination htr - α * h2
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hps)
  subst hβ
  have hα : α * (α + (p + s)) = 0 := by linear_combination hdet
  rcases mul_eq_zero.1 hα with hα0 | hα1
  · subst hα0
    have hgx : g * x * g⁻¹ = x := Units.ext (by simpa using h)
    calc g * x = (g * x * g⁻¹) * g := by group
      _ = x * g := by rw [hgx]
  · exfalso
    have hαt : α = p + s := by
      have : α - (p + s) = 0 := by linear_combination hα1 - (p + s) * h2
      exact sub_eq_zero.1 this
    set y : GL (Fin 2) F := g * x * g⁻¹ with hy
    have hyM : (y : Matrix (Fin 2) (Fin 2) F) = (p + s) • 1 + (x : Matrix (Fin 2) (Fin 2) F) := by
      rw [hy, h, hαt, one_smul]
    have hgyg : g * y * g⁻¹ = x := by
      apply Units.ext
      have e1 : ((g * y * g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
          (g : Matrix (Fin 2) (Fin 2) F) * (y : Matrix (Fin 2) (Fin 2) F) *
            ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
        rw [Units.val_mul, Units.val_mul]
      have e2 : (y : Matrix (Fin 2) (Fin 2) F) =
          (g : Matrix (Fin 2) (Fin 2) F) * (x : Matrix (Fin 2) (Fin 2) F) *
            ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
        rw [hy, Units.val_mul, Units.val_mul]
      have e3 : (g : Matrix (Fin 2) (Fin 2) F) * ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
          = 1 := Units.mul_inv g
      rw [e1, hyM, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_one,
        Matrix.smul_mul, e3, ← e2, hyM]
      have h3 : (p + s) • (1 : Matrix (Fin 2) (Fin 2) F) + ((p + s) • 1 + (x : Matrix (Fin 2) (Fin 2) F))
          = ((p + s) + (p + s)) • (1 : Matrix (Fin 2) (Fin 2) F) + (x : Matrix (Fin 2) (Fin 2) F) := by
        rw [← add_assoc, ← add_smul]
      rw [h3, CharTwo.add_self_eq_zero, zero_smul, zero_add]
    have hcomm2 : Commute (g ^ 2) x := by
      show g ^ 2 * x = x * g ^ 2
      have hh : g * (g * x * g⁻¹) * g⁻¹ = x := hgyg
      rw [pow_two]
      calc g * g * x = (g * (g * x * g⁻¹) * g⁻¹) * (g * g) := by group
        _ = x * (g * g) := by rw [hh]
    obtain ⟨k, hk⟩ := hgo
    have hgk : g ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one g
    have hgpow : g = (g ^ 2) ^ (k + 1) := by
      rw [← pow_mul, show 2 * (k + 1) = (2 * k + 1) + 1 by ring, pow_succ, hgk, one_mul]
    have hcomm1 : g * x = x * g := by
      have := (hcomm2.pow_left (k + 1)).eq
      rw [← hgpow] at this
      exact this
    have hyx : y = x := by
      rw [hy]
      calc g * x * g⁻¹ = (x * g) * g⁻¹ := by rw [hcomm1]
        _ = x := by group
    rw [hyx] at hyM
    have h0 := congrFun (congrFun hyM 0) 0
    simp [hXdef] at h0
    exact hps (by simpa using h0)

theorem uc22p22l_gl2_odd_abelian_aux [CharP F 2] :
    ∀ (n : ℕ) (E : Subgroup (GL (Fin 2) F)), Nat.card E ≤ n → Odd (Nat.card E) →
      ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro E hEn hEodd
    by_contra hnc
    push Not at hnc
    obtain ⟨a, ha, b, hb, hab⟩ := hnc
    haveI : Finite E := Nat.finite_of_card_ne_zero hEodd.pos.ne'
    haveI : Group.IsSolvable E := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hEodd
    haveI : Nontrivial E := ⟨⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (by
      have : a = b := congrArg Subtype.val h
      rw [this])⟩⟩
    set D : Subgroup (GL (Fin 2) F) := ⁅E, E⁆ with hD
    have hDE : D ≤ E := Subgroup.commutator_le_self E
    have hDne : D ≠ E := by
      intro h
      haveI : Group.IsPerfect E := Subgroup.isPerfect_iff.2 h
      exact Group.IsPerfect.not_isSolvable E inferInstance
    have hlt : Nat.card D < Nat.card E := by
      refine lt_of_le_of_ne (Subgroup.card_le_of_le hDE) fun h => hDne ?_
      exact Subgroup.eq_of_le_of_card_ge hDE h.ge
    have hDodd : Odd (Nat.card D) := Odd.of_dvd_nat hEodd (Subgroup.card_dvd_of_le hDE)
    have hDab : ∀ u ∈ D, ∀ v ∈ D, u * v = v * u :=
      ih (Nat.card D) (lt_of_lt_of_le hlt hEn) D le_rfl hDodd
    set x : GL (Fin 2) F := ⁅a, b⁆ with hxdef
    have hxD : x ∈ D := Subgroup.commutator_mem_commutator ha hb
    have hx1 : x ≠ 1 := fun h => hab (commutatorElement_eq_one_iff_mul_comm.1 h)
    have hxdet : (x : Matrix (Fin 2) (Fin 2) F).det = 1 := by
      have h1 : Matrix.GeneralLinearGroup.det x = 1 := by
        rw [hxdef, map_commutatorElement]
        exact commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _)
      have h2 := congrArg Units.val h1
      simpa [Matrix.GeneralLinearGroup.det] using h2
    have hxs : ∀ γ : F, (x : Matrix (Fin 2) (Fin 2) F) ≠ γ • (1 : Matrix (Fin 2) (Fin 2) F) := by
      intro γ hγ
      have hdetγ : γ ^ 2 = 1 := by
        have := congrArg Matrix.det hγ
        rw [hxdet, Matrix.det_smul, Matrix.det_one] at this
        simpa using this.symm
      have hγ1 : γ = 1 := by
        have h2 : (γ - 1) ^ 2 = 0 := by
          have h3 : (2 : F) = 0 := CharTwo.two_eq_zero
          linear_combination hdetγ - (γ - 1) * h3
        exact sub_eq_zero.1 (pow_eq_zero_iff (two_ne_zero) |>.1 h2)
      apply hx1
      apply Units.ext
      rw [hγ, hγ1, one_smul]
      rfl
    have hxo : Odd (orderOf x) :=
      Odd.of_dvd_nat hEodd (Subgroup.orderOf_dvd_natCard E (show x ∈ E from hDE hxD))
    have hgx : ∀ g ∈ E, g * x = x * g := by
      intro g hg
      have hgxg : g * x * g⁻¹ ∈ D := by
        have h1 : ⁅g, x⁆ ∈ D := Subgroup.commutator_mem_commutator hg (hDE hxD)
        have h2 : g * x * g⁻¹ = ⁅g, x⁆ * x := by
          simp only [commutatorElement_def]; group
        rw [h2]
        exact D.mul_mem h1 hxD
      have hc : g * x * g⁻¹ * x = x * (g * x * g⁻¹) := hDab _ hgxg x hxD
      obtain ⟨α, β, hαβ⟩ := uc22p22l_commute_mem_span (x := (x : Matrix (Fin 2) (Fin 2) F))
        (y := ((g * x * g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) hxs (by
          have := congrArg Units.val hc
          simpa [Units.val_mul] using this.symm)
      have hgo : Odd (orderOf g) :=
        Odd.of_dvd_nat hEodd (Subgroup.orderOf_dvd_natCard E hg)
      exact uc22p22l_gl2_odd_commute hxs hxo hgo hαβ
    have hspan : ∀ g ∈ E, ∃ α β : F, (g : Matrix (Fin 2) (Fin 2) F) =
        α • (1 : Matrix (Fin 2) (Fin 2) F) + β • (x : Matrix (Fin 2) (Fin 2) F) := by
      intro g hg
      refine uc22p22l_commute_mem_span hxs ?_
      have := congrArg Units.val (hgx g hg)
      simpa [Units.val_mul] using this.symm
    obtain ⟨α₁, β₁, h₁⟩ := hspan a ha
    obtain ⟨α₂, β₂, h₂⟩ := hspan b hb
    apply hab
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, h₁, h₂]
    have key : Commute (α₁ • (1 : Matrix (Fin 2) (Fin 2) F) + β₁ • (x : Matrix (Fin 2) (Fin 2) F))
        (α₂ • (1 : Matrix (Fin 2) (Fin 2) F) + β₂ • (x : Matrix (Fin 2) (Fin 2) F)) := by
      refine Commute.add_left (Commute.add_right ?_ ?_) (Commute.add_right ?_ ?_)
      · exact ((Commute.refl (1 : Matrix (Fin 2) (Fin 2) F)).smul_left α₁).smul_right α₂
      · exact (((Commute.one_left (x : Matrix (Fin 2) (Fin 2) F))).smul_left α₁).smul_right β₂
      · exact (((Commute.one_right (x : Matrix (Fin 2) (Fin 2) F))).smul_left β₁).smul_right α₂
      · exact ((Commute.refl (x : Matrix (Fin 2) (Fin 2) F)).smul_left β₁).smul_right β₂
    exact key.eq

end GL2

section Cover

theorem uc22p22l_oddAbelianProper_of_cover {Gt X : Type} [Group Gt] [Finite Gt] [Group X]
    [Finite X] (π : Gt →* X) (hπ : Function.Surjective π) (Ut : Subgroup Gt)
    (hUt : ∃ T : Sylow 2 Gt, (T : Subgroup Gt) = Ut) (Q : Fin 2 → Subgroup Gt)
    (hQ : ∀ A : Subgroup Gt, Ut ≤ A → A ≠ ⊤ → ∃ j, A ≤ Q j) (hkodd : Odd (Nat.card π.ker))
    (hab : ∀ (j : Fin 2) (V : Subgroup Gt), V ≤ Q j → Odd (Nat.card V) →
      ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) :
    OddAbelianProper X := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro S Y hSY hY W hWY hW a ha b hb
  obtain ⟨T, hT⟩ := hUt
  let T' : Sylow 2 X := T.mapSurjective hπ
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq X T' S
  have hT'ge : ∀ u ∈ Ut, π u ∈ (T' : Subgroup X) := by
    intro u hu
    rw [Sylow.coe_mapSurjective, hT]
    exact ⟨u, hu, rfl⟩
  have hSconj : ∀ t ∈ (T' : Subgroup X), x * t * x⁻¹ ∈ S := by
    intro t ht
    have h1 : x * t * x⁻¹ ∈ ((x • T' : Sylow 2 X) : Subgroup X) := by
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
      exact ⟨t, ht, by simp [MulAut.smul_def]⟩
    rw [hx] at h1
    exact h1
  let c : X →* X := (MulAut.conj x⁻¹).toMonoidHom
  have hc : ∀ y, c y = x⁻¹ * y * x := fun y => by simp [c, MulAut.conj_apply]
  set Y₁ : Subgroup X := Y.map c with hY₁
  set W₁ : Subgroup X := W.map c with hW₁
  have hY₁mem : ∀ z, z ∈ Y₁ ↔ x * z * x⁻¹ ∈ Y := by
    intro z
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [hc]
      simpa [mul_assoc] using hy
    · intro hz
      exact ⟨x * z * x⁻¹, hz, by rw [hc]; group⟩
  have hW₁mem : ∀ z, z ∈ W₁ ↔ x * z * x⁻¹ ∈ W := by
    intro z
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [hc]
      simpa [mul_assoc] using hy
    · intro hz
      exact ⟨x * z * x⁻¹, hz, by rw [hc]; group⟩
  have hY₁top : Y₁ ≠ ⊤ := by
    intro h
    apply hY
    rw [eq_top_iff]
    intro y _
    have : x⁻¹ * y * x ∈ Y₁ := h ▸ Subgroup.mem_top _
    rw [hY₁mem] at this
    simpa [mul_assoc] using this
  have hW₁Y₁ : W₁ ≤ Y₁ := fun z hz => (hY₁mem z).2 (hWY ((hW₁mem z).1 hz))
  set A : Subgroup Gt := Y₁.comap π with hA
  have hUA : Ut ≤ A := by
    intro u hu
    rw [hA, Subgroup.mem_comap, hY₁mem]
    exact hSY (hSconj _ (hT'ge u hu))
  have hAtop : A ≠ ⊤ := by
    intro h
    apply hY₁top
    rw [eq_top_iff]
    intro z _
    obtain ⟨g, rfl⟩ := hπ z
    have : g ∈ A := h ▸ Subgroup.mem_top g
    exact this
  obtain ⟨j, hj⟩ := hQ A hUA hAtop
  set Wt : Subgroup Gt := W₁.comap π with hWt
  have hWtQ : Wt ≤ Q j := fun g hg => hj (hW₁Y₁ hg)
  have hW₁odd : Odd (Nat.card W₁) := by
    rw [hW₁, Subgroup.card_map_of_injective (MulAut.conj x⁻¹).injective]
    exact hW
  have hWtodd : Odd (Nat.card Wt) := by
    let f : Wt →* W₁ := (π.comp Wt.subtype).codRestrict W₁ (fun g => g.2)
    have hf : Function.Surjective f := by
      intro z
      obtain ⟨g, hg⟩ := hπ (z : X)
      exact ⟨⟨g, by rw [hWt, Subgroup.mem_comap, hg]; exact z.2⟩, Subtype.ext hg⟩
    have h1 := Subgroup.card_ker_mul_card_of_surjective hf
    let ι : f.ker →* π.ker :=
      { toFun := fun g => ⟨((g : Wt) : Gt), by
          have h3 := g.2
          rw [MonoidHom.mem_ker] at h3 ⊢
          have h2 : ((f (g : Wt) : W₁) : X) = 1 := congrArg Subtype.val h3
          exact h2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hι : Function.Injective ι := by
      intro g h hgh
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : π.ker => (z : Gt)) hgh
    have hdvd : Nat.card f.ker ∣ Nat.card π.ker := Subgroup.card_dvd_of_injective ι hι
    rw [← h1]
    exact (Odd.of_dvd_nat hkodd hdvd).mul hW₁odd
  have hWtab := hab j Wt hWtQ hWtodd
  have ha₁ : x⁻¹ * a * x ∈ W₁ := (hW₁mem _).2 (by simpa [mul_assoc] using ha)
  have hb₁ : x⁻¹ * b * x ∈ W₁ := (hW₁mem _).2 (by simpa [mul_assoc] using hb)
  obtain ⟨ga, hga⟩ := hπ (x⁻¹ * a * x)
  obtain ⟨gb, hgb⟩ := hπ (x⁻¹ * b * x)
  have hgaW : ga ∈ Wt := by rw [hWt, Subgroup.mem_comap, hga]; exact ha₁
  have hgbW : gb ∈ Wt := by rw [hWt, Subgroup.mem_comap, hgb]; exact hb₁
  have hcomm := hWtab ga hgaW gb hgbW
  have h2 : (x⁻¹ * a * x) * (x⁻¹ * b * x) = (x⁻¹ * b * x) * (x⁻¹ * a * x) := by
    rw [← hga, ← hgb, ← map_mul, ← map_mul, hcomm]
  calc a * b = x * ((x⁻¹ * a * x) * (x⁻¹ * b * x)) * x⁻¹ := by group
    _ = x * ((x⁻¹ * b * x) * (x⁻¹ * a * x)) * x⁻¹ := by rw [h2]
    _ = b * a := by group

end Cover

section Levi

theorem uc22p22l_odd_comm_of_block {F : Type*} [Field F] [CharP F 2] {X : Type*} [Group X]
    {A : Type*} [CommGroup A] (ψ : X →* GL (Fin 2) F) (χ : X →* A)
    (hker : ∀ x : X, ψ x = 1 → χ x = 1 → ∃ n : ℕ, x ^ 2 ^ n = 1) {E : Subgroup X}
    (hE : Odd (Nat.card E)) {a b : X} (ha : a ∈ E) (hb : b ∈ E) : a * b = b * a := by
  have hinj : ∀ e ∈ E, ψ e = 1 → χ e = 1 → e = 1 := by
    intro e he h1 h2
    obtain ⟨n, hn⟩ := hker e h1 h2
    have hodd : Odd (orderOf e) := Odd.of_dvd_nat hE (Subgroup.orderOf_dvd_natCard E he)
    have hdvd : orderOf e ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn
    have h2' : ¬ 2 ∣ orderOf e := fun h => (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h)
    have hcop : Nat.Coprime (orderOf e) (2 ^ n) :=
      Nat.Coprime.pow_right n ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 h2').symm
    exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hcop hdvd)
  have hodd' : Odd (Nat.card (E.map ψ)) := by
    have hsurj : Function.Surjective (ψ.subgroupMap E) := MonoidHom.subgroupMap_surjective _ _
    exact hE.of_dvd_nat (Subgroup.card_dvd_of_surjective hsurj)
  have hψ := uc22p22l_gl2_odd_abelian_aux _ (E.map ψ) le_rfl hodd' (ψ a) ⟨a, ha, rfl⟩ (ψ b)
    ⟨b, hb, rfl⟩
  have hcE : ⁅a, b⁆ ∈ E := by
    simp only [commutatorElement_def]
    exact E.mul_mem (E.mul_mem (E.mul_mem ha hb) (E.inv_mem ha)) (E.inv_mem hb)
  have h1 : ψ ⁅a, b⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 hψ
  have h2 : χ ⁅a, b⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _)
  exact commutatorElement_eq_one_iff_mul_comm.1 (hinj _ hcE h1 h2)

theorem uc22p22l_comm_of_subgroupOf {G : Type*} [Group G] {S V : Subgroup G} (hVS : V ≤ S)
    (h : ∀ E : Subgroup S, Odd (Nat.card E) → ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hodd : Odd (Nat.card V)) : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := by
  intro a ha b hb
  have hodd' : Odd (Nat.card (V.subgroupOf S)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVS).toEquiv]
    exact hodd
  exact congrArg Subtype.val (h _ hodd' (a := ⟨a, hVS ha⟩) (b := ⟨b, hVS hb⟩) ha hb)

end Levi

section LeviLie

open CFSG.QuasithinUnique.Setup.X7a CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.Quasithin.H13.QRC

variable {K : Type} [Field K] [CharP K 2]

theorem uc22p22l_Q3_odd_comm (j : Fin 2) {V : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K)}
    (hV : V ≤ Q3 K j) (hodd : Odd (Nat.card V)) : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := by
  fin_cases j
  · refine uc22p22l_comm_of_subgroupOf (S := stabilizer (flagSpace 3 K 1))
      (by simpa [Q3] using hV) ?_ hodd
    intro E hE a ha b hb
    exact uc22p22l_odd_comm_of_block (lowerBlockHom (k := K)).toHomUnits (1 : _ →* ℤˣ)
      (fun x hx _ => ⟨1, by
        rw [pow_one]
        exact sq_eq_one_of_lowerBlockHom_eq_one x (by
          have := congrArg Units.val hx
          simpa using this)⟩) hE ha hb
  · refine uc22p22l_comm_of_subgroupOf (S := stabilizer (flagSpace 3 K 2))
      (by simpa [Q3] using hV) ?_ hodd
    intro E hE a ha b hb
    exact uc22p22l_odd_comm_of_block (upperBlockHom (k := K)).toHomUnits (1 : _ →* ℤˣ)
      (fun x hx _ => ⟨1, by
        rw [pow_one]
        exact sq_eq_one_of_upperBlockHom_eq_one x (by
          have := congrArg Units.val hx
          simpa using this)⟩) hE ha hb

theorem uc22p22l_Q2_odd_comm (j : Fin 2) {V : Subgroup (StatedSp 2 K)}
    (hV : V ≤ Q2 K j) (hodd : Odd (Nat.card V)) : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := by
  fin_cases j
  · refine uc22p22l_comm_of_subgroupOf (S := stabilizer 2 K (flag 2 K 1))
      (by simpa [Q2] using hV) ?_ hodd
    intro E hE a ha b hb
    exact uc22p22l_odd_comm_of_block (midBlockHom (k := K)).toHomUnits
      (cornerHom (k := K)).toHomUnits
      (fun x hψ hχ => ⟨2, pow_four_eq_one_of_line x (by
          have := congrArg Units.val hχ
          simpa using this) (by
          have := congrArg Units.val hψ
          simpa using this)⟩) hE ha hb
  · refine uc22p22l_comm_of_subgroupOf (S := stabilizer 2 K (flag 2 K 2))
      (by simpa [Q2] using hV) ?_ hodd
    intro E hE a ha b hb
    exact uc22p22l_odd_comm_of_block (lagrangianBlockHom (k := K)).toHomUnits (1 : _ →* ℤˣ)
      (fun x hx _ => ⟨1, by
        rw [pow_one]
        exact sq_eq_one_of_lagrangianBlockHom_eq_one x (by
          have := congrArg Units.val hx
          simpa using this)⟩) hE ha hb

end LeviLie

section LieCover

open CFSG.QuasithinUnique.Setup.X7a CFSG.LocalAnalysis.ComponentInitial
  CFSG.Assembly.LowTwoRank

theorem uc22p22l_oddAbelianProper_sl3
    {X : Type} [Group X] [Finite X]
    (hperf : _root_.commutator X = ⊤) (hodd : Odd (Nat.card (Subgroup.center X))) {n : ℕ}
    (h : IsSL3 X n) : OddAbelianProper X := by
  classical
  haveI : Group.IsPerfect X := ⟨hperf⟩
  obtain ⟨-, hL3⟩ := h
  have hcl := (CFSG.Blueprint.LieModel.classical_iff (t := .PSL) (by decide)).1 hL3
  obtain ⟨⟨-, hf, -⟩, K, hF, hFin, hcard, ⟨e⟩⟩ := hcl
  haveI : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hcard
  have e' : X ⧸ Subgroup.center X ≃* LinearFlag.projectiveSL 3 K :=
    e.trans (statedSLEquivProjectiveSL 3 K)
  obtain ⟨φ, hφs, hφk, -⟩ := CFSG.QuasithinUnique.Ch1.exists_cover_map_of_odd_splitting
    (D := LinearFlag.scalars 3 K) hodd e' (fun E _ _ π hπ hcen hoddk => by
      obtain ⟨s, hs, -⟩ := CFSG.SectionRank.EvenCover.even_linear_central_odd_extension_splitting
        (by norm_num) hπ hcen hoddk
      exact ⟨s, hs⟩)
  obtain ⟨T, hT⟩ := LinearFlag.exists_sylow_unitriangular (K := K) 2 (n := 3) (by norm_num)
  refine uc22p22l_oddAbelianProper_of_cover φ hφs (LinearFlag.unitriangular 3 K) ⟨T, hT⟩ (Q3 K)
    (fun A hUA hAt => (contained_in_Q3 hUA hAt).elim (fun h => ⟨0, h⟩) (fun h => ⟨1, h⟩)) ?_
    (fun j V hV hVodd => uc22p22l_Q3_odd_comm j hV hVodd)
  have h1 : Nat.card φ.ker ∣ Nat.card K - 1 :=
    (Subgroup.card_dvd_of_le hφk).trans (LinearFlag.card_scalars_dvd (by norm_num))
  have hn0 : n ≠ 0 := by
    rintro rfl
    have : Nat.card K = 1 := by simpa using hcard
    exact absurd this (Nat.card_eq_one_iff_unique.not.2 (by
      intro ⟨hs, _⟩
      exact not_subsingleton K hs))
  have h2 : Odd (Nat.card K - 1) := by
    have hpos : 0 < 2 ^ n := pow_pos two_pos n
    have hev : 2 ∣ 2 ^ n := dvd_pow_self 2 hn0
    rw [hcard]
    exact Nat.odd_iff.2 (by omega)
  exact h2.of_dvd_nat h1

theorem uc22p22l_oddAbelianProper_sp4 {X : Type} [Group X] [Finite X] {n : ℕ}
    (h : IsSp4 X n) : OddAbelianProper X := by
  classical
  have hcl := (CFSG.Blueprint.LieModel.classical_iff (t := .PSp) (by decide)).1 h
  obtain ⟨⟨-, hf, -⟩, K, hF, hFin, hcard, ⟨e⟩⟩ := hcl
  haveI : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hcard
  let π : StatedSp 2 K →* X := e.symm.toMonoidHom.comp (SymplecticFlag.proj 2 K)
  have hπ : Function.Surjective π :=
    e.symm.surjective.comp (SymplecticHigher.proj_surjective (r := 2) (K := K))
  have hker : π.ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have h1 : SymplecticFlag.proj 2 K x = 1 :=
      e.symm.injective (by simpa [π] using hx)
    have h2 : x ∈ (SymplecticFlag.proj 2 K).ker := h1
    rw [SymplecticHigher.ker_proj, UnitaryHigher.spScalars_eq_bot_of_charTwo] at h2
    exact h2
  obtain ⟨T, hT⟩ := SymplecticFlag.exists_sylow_unipotent (K := K) 2 2
  refine uc22p22l_oddAbelianProper_of_cover π hπ (SymplecticFlag.unipotent 2 K) ⟨T, hT⟩ (Q2 K)
    (fun A hUA hAt => (contained_in_Q2 hUA hAt).elim (fun h => ⟨0, h⟩) (fun h => ⟨1, h⟩))
    (by rw [hker]; simp)
    (fun j V hV hVodd => uc22p22l_Q2_odd_comm j hV hVodd)

end LieCover

section OddCentre

theorem uc22p22l_pCore_quotient {Λ : Type} [Group Λ] [Finite Λ] :
    CFSG.pCore 2 (Λ ⧸ CFSG.pCore 2 Λ) = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup Λ := CFSG.pCore 2 Λ
  set M : Subgroup (Λ ⧸ N) := CFSG.pCore 2 (Λ ⧸ N)
  have hMp : IsPGroup 2 (M.comap (QuotientGroup.mk' N)) := by
    refine IsPGroup.comap_of_ker_isPGroup (CFSG.pCore_isPGroup) _ ?_
    rw [QuotientGroup.ker_mk']
    exact CFSG.pCore_isPGroup
  haveI : (M.comap (QuotientGroup.mk' N)).Normal := Subgroup.Normal.comap inferInstance _
  have hle : M.comap (QuotientGroup.mk' N) ≤ N :=
    le_sSup (show M.comap (QuotientGroup.mk' N) ∈ {K : Subgroup Λ | K.Normal ∧ IsPGroup 2 K} from
      ⟨inferInstance, hMp⟩)
  rw [eq_bot_iff]
  intro m hm
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective m
  have hl : l ∈ M.comap (QuotientGroup.mk' N) := hm
  exact (QuotientGroup.eq_one_iff l).2 (hle hl)

theorem uc22p22l_odd_center_quotient {Λ : Type} [Group Λ] [Finite Λ] :
    Odd (Nat.card (Subgroup.center (Λ ⧸ CFSG.pCore 2 Λ))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := Λ ⧸ CFSG.pCore 2 Λ
  by_contra hne
  have h2 : 2 ∣ Nat.card (Subgroup.center Q) := by
    rw [Nat.not_odd_iff_even] at hne
    exact even_iff_two_dvd.1 hne
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hcQ : orderOf (c : Q) = 2 := (Subgroup.orderOf_coe c).trans hc
  set H : Subgroup Q := Subgroup.zpowers (c : Q) with hH
  have hHp : IsPGroup 2 H := IsPGroup.of_card (n := 1) (by
    rw [hH, Nat.card_zpowers, hcQ]; rfl)
  have hHn : H.Normal := ⟨by
    intro n hn g
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    have hcj : (c : Q) ^ j ∈ Subgroup.center Q := Subgroup.zpow_mem _ c.2 j
    rw [Subgroup.mem_center_iff.1 hcj g, mul_inv_cancel_right]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) j⟩
  have hle : H ≤ CFSG.pCore 2 Q := le_sSup ⟨hHn, hHp⟩
  rw [uc22p22l_pCore_quotient] at hle
  have : (c : Q) ∈ (⊥ : Subgroup Q) := hle (Subgroup.mem_zpowers _)
  rw [Subgroup.mem_bot] at this
  rw [this, orderOf_one] at hcQ
  exact absurd hcQ (by norm_num)

end OddCentre

section Main

variable {G : Type} [Group G] [Finite G]

theorem uc22p22l_oddAbelianL0_of_overgroups (D : Data G) {L : Subgroup G}
    (hL : L ∈ calL D.T D.M)
    (h : ∀ (S : Sylow 2 (Bar2 L)) (Y : Subgroup (Bar2 L)), (S : Subgroup (Bar2 L)) ≤ Y →
      (∀ l : ↥L, (QuotientGroup.mk l : Bar2 L) ∈ Y → (l : G) ∈ D.M) → OddAbelianIn Y) :
    OddAbelianL0 D L := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro V hVL hVM hVodd a ha b hb
  obtain ⟨hTN, -, hLT, -⟩ := hL
  have hTM : D.T ≤ D.M := D.sylowM.le
  have h1 : CFSG.ABGLocalTools.IsSylowOf 2 D.T (L ⊔ D.T) := D.sylowG.of_le le_sup_right le_top
  have h2 : CFSG.ABGLocalTools.IsSylowOf 2 (D.T ⊓ L) L :=
    h1.inf_of_le_normalizer le_sup_left (sup_le Subgroup.le_normalizer hTN)
  obtain ⟨T₁, hT₁⟩ := h2.exists_sylow_eq_subgroupOf
  set Ω : Subgroup ↥L := D.M.subgroupOf L with hΩ
  have hT₁M : (T₁ : Subgroup ↥L) ≤ Ω := by
    intro x hx
    rw [hT₁] at hx
    exact hTM (Subgroup.mem_inf.1 hx).1
  set O : Subgroup ↥L := CFSG.pCore 2 ↥L with hO
  let π : ↥L →* ↥L ⧸ O := QuotientGroup.mk' O
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective O
  have hOT : O ≤ (T₁ : Subgroup ↥L) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).le_sylow_of_normal T₁
  have hOΩ : O ≤ Ω := hOT.trans hT₁M
  let S : Sylow 2 (↥L ⧸ O) := T₁.mapSurjective hπ
  have hSY : (S : Subgroup (↥L ⧸ O)) ≤ Ω.map π := by
    rw [Sylow.coe_mapSurjective]
    exact Subgroup.map_mono hT₁M
  have hpre : ∀ l : ↥L, (QuotientGroup.mk l : ↥L ⧸ O) ∈ Ω.map π → (l : G) ∈ D.M := by
    intro l hl
    obtain ⟨ω, hω, hωl⟩ := hl
    have hωO : ω⁻¹ * l ∈ O := (QuotientGroup.eq (a := ω) (b := l)).1 hωl
    have hl' : l ∈ Ω := by
      have : l = ω * (ω⁻¹ * l) := by group
      rw [this]
      exact Ω.mul_mem hω (hOΩ hωO)
    exact hl'
  have hOA : OddAbelianIn (Ω.map π) := h S (Ω.map π) hSY hpre
  have hVodd' : Odd (Nat.card (V.subgroupOf L)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVL).toEquiv]
    exact hVodd
  exact congrArg Subtype.val (uc22p22l_lift hOΩ hOA (V := V.subgroupOf L)
    (fun y hy => hVM hy) hVodd' (a := ⟨a, hVL ha⟩) (b := ⟨b, hVL hb⟩) ha hb)

theorem uc22p22l_not_le_M (D : Data G) {L : Subgroup G} (hL : L ∈ calL D.T D.M) :
    ¬ L ≤ D.M := fun h => hL.2.2.1.2.1 (sup_le h D.sylowM.le)

theorem uc22p22l_barImage_equiv {L K : Subgroup G} (hK : K ∈ calC L) :
    ∃ e : Bar2 K ≃* ↥(barImage L K), ∀ k : ↥K, ((e (QuotientGroup.mk k) : ↥(barImage L K)) :
      Bar2 L) = QuotientGroup.mk (Subgroup.inclusion (CFSG.Quasithin.A3.subnormal_le hK.1) k) :=
  uc22p20d_bar2Equiv (CFSG.Quasithin.A3.subnormal_le hK.1) hK.1

theorem uc22p22l_barImage_isComponent {L K : Subgroup G} (hK : K ∈ calC L) :
    CFSG.IsComponent (barImage L K) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hPn : (CFSG.pCore 2 ↥L).Normal := CFSG.pCore_normal
  haveI hPs := uc22p20d_pCore_solvable L
  obtain ⟨e, -⟩ := uc22p22l_barImage_equiv hK
  have hqs : CFSG.Open.IsQuasisimple ↥(barImage L K) := CFSG.Open.IsQuasisimple.of_mulEquiv e.symm hK.2.2
  have hKc := uc22p20e_cComp_of_calC hK
  have hKbar := CFSG.Quasithin.map_mem_cComp_top (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']; exact hPs)
    (CFSG.Quasithin.subgroupOf_mem_cComp hKc)
  exact ⟨CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hqs,
    CFSG.Quasithin.A3.subnormal_top_iff.mp (CFSG.Quasithin.subnormal_of_mem_cComp hKbar)⟩

theorem uc22p22l_barImage_commute {L L₁ L₂ : Subgroup G} (h₁ : L₁ ∈ calC L) (h₂ : L₂ ∈ calC L)
    (hne : L₁ ≠ L₂) : ∀ a ∈ barImage L L₁, ∀ b ∈ barImage L L₂, a * b = b * a := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hPn : (CFSG.pCore 2 ↥L).Normal := CFSG.pCore_normal
  haveI hPs := uc22p20d_pCore_solvable L
  have hA := uc22p22l_barImage_isComponent h₁
  have hA' := uc22p22l_barImage_isComponent h₂
  have hc₁ := uc22p20e_cComp_of_calC h₁
  have hc₂ := uc22p20e_cComp_of_calC h₂
  rcases CFSG.LocalCores.distinct_components_commute hA hA' with h | h
  · exfalso
    apply hne
    have hbij := CFSG.Quasithin.cComp_quotient_bijOn (CFSG.pCore 2 ↥L) hPs
    have h1 := hbij.injOn (CFSG.Quasithin.subgroupOf_mem_cComp hc₁)
      (CFSG.Quasithin.subgroupOf_mem_cComp hc₂) h
    have h2 : L₁ ⊓ L = L₂ ⊓ L := Subgroup.subgroupOf_inj.mp h1
    rwa [inf_eq_left.mpr (CFSG.Quasithin.le_of_mem_cComp hc₁),
      inf_eq_left.mpr (CFSG.Quasithin.le_of_mem_cComp hc₂)] at h2
  · intro a ha b hb
    exact (Subgroup.mem_centralizer_iff.mp
      ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp h) ha) b hb).symm

theorem uc22p22l_factor_data
    {L K : Subgroup G} (hK : K ∈ calC L) {m : ℕ}
    (hm : IsSz (Bar2 K) m ∨ IsL2 (Bar2 K) m ∨ IsSU3 (Bar2 K) m) :
    IsSimpleGroup (Bar2 K ⧸ center (Bar2 K)) ∧ OddCyclicProper (Bar2 K ⧸ center (Bar2 K)) ∧
      ∃ q : ↥(barImage L K) →* (Bar2 K ⧸ center (Bar2 K)),
        Function.Surjective q ∧ q.ker = center ↥(barImage L K) := by
  obtain ⟨e, -⟩ := uc22p22l_barImage_equiv hK
  obtain ⟨hs, hocp⟩ := uc22p22l_ocp_of_shape (uc22p22j_perfect_bar2 K hK.2.1) hm
  refine ⟨hs, hocp, (QuotientGroup.mk' (center (Bar2 K))).comp e.symm.toMonoidHom,
    (QuotientGroup.mk'_surjective _).comp e.symm.surjective, ?_⟩
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact uc22p22l_mem_center_equiv e x

theorem uc22p22l_oddAbelianL0_product
    (D : Data G) {L : Subgroup G} (hL : L ∈ calL D.T D.M) (hsh : S2010Product D L) :
    OddAbelianL0 D L := by
  classical
  obtain ⟨L₁, L₂, h₁, h₂, hsup, hne, ⟨t, ht, hL₂⟩, n, hn⟩ := hsh
  have hLM := uc22p22l_not_le_M D hL
  have hTM : D.T ≤ D.M := D.sylowM.le
  have hshape : ∀ L' ∈ ({L₁, L₂} : Set (Subgroup G)),
      ∃ m : ℕ, IsSz (Bar2 L') m ∨ IsL2 (Bar2 L') m ∨ IsSU3 (Bar2 L') m := by
    intro L' hL'
    rcases hn L' hL' with h | h | ⟨-, h⟩
    · exact ⟨n, Or.inl h⟩
    · exact ⟨n, Or.inr (Or.inl h)⟩
    · exact ⟨3, Or.inr (Or.inr h)⟩
  obtain ⟨m₁, hm₁⟩ := hshape L₁ (by simp)
  obtain ⟨m₂, hm₂⟩ := hshape L₂ (by simp)
  obtain ⟨hsim₁, hocp₁, q₁, hq₁, hk₁⟩ := uc22p22l_factor_data (L := L) h₁ hm₁
  obtain ⟨hsim₂, hocp₂, q₂, hq₂, hk₂⟩ := uc22p22l_factor_data (L := L) h₂ hm₂
  have hL₁L : L₁ ≤ L := CFSG.Quasithin.A3.subnormal_le h₁.1
  have hL₂L : L₂ ≤ L := CFSG.Quasithin.A3.subnormal_le h₂.1
  have hcomp₁ := uc22p22l_barImage_isComponent h₁
  have hcomp₂ := uc22p22l_barImage_isComponent h₂
  have hperf₁ : ⁅barImage L L₁, barImage L L₁⁆ = barImage L L₁ :=
    Subgroup.isPerfect_iff.1 (CFSG.Quasithin.A3.isQuasisimple_iff_open.2
      (CFSG.Quasithin.A3.isQuasisimple_iff_open.1 hcomp₁.1) |>.1)
  have hperf₂ : ⁅barImage L L₂, barImage L L₂⁆ = barImage L L₂ :=
    Subgroup.isPerfect_iff.1 hcomp₂.1.1
  have hsupX : barImage L L₁ ⊔ barImage L L₂ = ⊤ := by
    unfold barImage
    rw [← Subgroup.map_sup, ← Subgroup.subgroupOf_sup hL₁L hL₂L, ← hsup,
      Subgroup.subgroupOf_self, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have hconj : ∀ y, y ∈ L₂ ↔ ∃ x ∈ L₁, t * x * t⁻¹ = y := by
    intro y
    rw [hL₂]
    simp [Subgroup.mem_map]
  have hL₁M_of : L₁ ≤ D.M → L₂ ≤ D.M := by
    intro h y hy
    obtain ⟨x, hx, rfl⟩ := (hconj y).1 hy
    exact D.M.mul_mem (D.M.mul_mem (hTM ht) (h hx)) (D.M.inv_mem (hTM ht))
  have hL₂M_of : L₂ ≤ D.M → L₁ ≤ D.M := by
    intro h x hx
    have h1 : t * x * t⁻¹ ∈ D.M := h ((hconj _).2 ⟨x, hx, rfl⟩)
    have h2 : x = t⁻¹ * (t * x * t⁻¹) * t := by group
    rw [h2]
    exact D.M.mul_mem (D.M.mul_mem (D.M.inv_mem (hTM ht)) h1) (hTM ht)
  refine uc22p22l_oddAbelianL0_of_overgroups D hL fun S Y hSY hpre => ?_
  have hLle_of : L₁ ≤ D.M → L ≤ D.M := fun h => hsup ▸ sup_le h (hL₁M_of h)
  have hX₁ : ¬ barImage L L₁ ≤ Y := by
    intro hXY
    refine hLM (hLle_of fun x hx => ?_)
    exact hpre ⟨x, hL₁L hx⟩ (hXY ⟨⟨x, hL₁L hx⟩, hx, rfl⟩)
  have hX₂ : ¬ barImage L L₂ ≤ Y := by
    intro hXY
    refine hLM (hLle_of (hL₂M_of fun x hx => ?_))
    exact hpre ⟨x, hL₂L hx⟩ (hXY ⟨⟨x, hL₂L hx⟩, hx, rfl⟩)
  haveI := hsim₁
  haveI := hsim₂
  exact uc22p22l_oddAbelianIn_product hsupX (uc22p22l_barImage_commute h₁ h₂ hne) hperf₁ hperf₂
    hocp₁ hocp₂ q₁ q₂ hq₁ hq₂ hk₁ hk₂ S hSY hX₁ hX₂

theorem uc22p22l_oddAbelianL0_of_proper (D : Data G) {L : Subgroup G} (hL : L ∈ calL D.T D.M)
    (hX : OddAbelianProper (Bar2 L)) : OddAbelianL0 D L :=
  uc22p22l_oddAbelianL0_of_overgroups D hL fun S Y hSY hpre => by
    have hY : Y ≠ ⊤ := by
      intro htop
      exact uc22p22l_not_le_M D hL fun x hx => hpre ⟨x, hx⟩ (htop ▸ Subgroup.mem_top _)
    exact fun W hWY hW a ha b hb => hX S Y hSY hY W hWY hW a ha b hb

@[expose] def OddAbelianGraphOnly (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, S2010Graph D c.L0 → ¬ S2010RankOne c.L0 → ¬ S2010Product D c.L0 →
    OddAbelianL0 D c.L0

theorem uc22p22l_oddAbelianRest_of
    (D : Data G) (Ch : Choice2011 G) (hg : OddAbelianGraphOnly D Ch) : OddAbelianRest D Ch := by
  intro h1930 c hc
  by_cases h1 : S2010RankOne c.L0
  · exact uc22p22j_oddAbelianL0_rankOne D c.hL0.1 h1
  by_cases h2 : S2010Product D c.L0
  · exact uc22p22l_oddAbelianL0_product D c.hL0.1 h2
  · rcases hc with hc | hc
    · exact absurd hc h2
    · exact hg h1930 c hc h1 h2

theorem uc22p22l_oddAbelianL0_graph_shape
    (D : Data G) {L : Subgroup G} (hL : L ∈ calL D.T D.M)
    (hsh : S2010Graph D L) : OddAbelianL0 D L := by
  obtain ⟨n, hn, -⟩ := hsh
  have hperf := uc22p22j_perfect_bar2 L hL.2.1
  refine uc22p22l_oddAbelianL0_of_proper D hL ?_
  rcases hn with h | h
  · exact uc22p22l_oddAbelianProper_sl3 hperf uc22p22l_odd_center_quotient h
  · exact uc22p22l_oddAbelianProper_sp4 h

theorem uc22p22l_oddAbelianRest
    (D : Data G)
    (Ch : Choice2011 G) : OddAbelianRest D Ch :=
  uc22p22l_oddAbelianRest_of D Ch fun _ c hg _ _ =>
    uc22p22l_oddAbelianL0_graph_shape D c.hL0.1 hg

theorem uc22p22l_cent2010_rest_proved
    (D : Data G)
    (Ch : Choice2011 G) : Cent2010Rest D Ch :=
  uc22p22j_centRest_of_oddAbelianRest D Ch (uc22p22l_oddAbelianRest D Ch)

theorem uc22p22l_cent2010_proved
    (D : Data G)
    (Ch : Choice2011 G) (h20_10 : S20_10 D) : Cent2010 D Ch :=
  uc22p22j_cent2010_of D Ch h20_10 (uc22p22l_cent2010_rest_proved D Ch)

theorem uc22p22l_s22_12_proved
    (D : Data G)
    (Ch : Choice2011 G) (h10 : S22_10 D Ch) (h11 : S22_11 D Ch) (h2123 : S21_23 D Ch)
    (hV : S22_V D Ch) (h8 : S22_8 D Ch)
    (hsp : ∀ p ∈ D.sig1, CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M)
    (hN : NormL0 D Ch) (h20_10 : S20_10 D) : S22_12 D Ch :=
  s22_12_of D Ch h10 h11 h2123 hV h8 hsp hN (uc22p22l_cent2010_proved D Ch h20_10)

end Main

end CFSG.LocalAnalysis.UniquenessCase.UC22
