module

public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem528EHerm
public import CFSG.Quasithin.Vol2.Ch5ModulesNat
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListRank2

public section

namespace CFSG.Quasithin.H13.Omega4

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.LieType.BorelTits
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem blockU_mul_self {L : Subgroup G} (hL : IsShort2 L) {u : G} (hu : u ∈ blockU L) :
    u * u = 1 := by
  have := hL.2.2.1.2 u hu
  rwa [sq] at this

theorem blockU_comm {L : Subgroup G} (hL : IsShort2 L) {a b : G} (ha : a ∈ blockU L)
    (hb : b ∈ blockU L) : a * b = b * a :=
  Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hL.2.2.1.1 hb)).2 a
    (Subgroup.mem_inf.mp (hL.2.2.1.1 ha)).1

theorem le_normalizer_blockU (L : Subgroup G) :
    L ≤ Subgroup.normalizer (blockU L : Set G) :=
  le_normalizer_commutator_of (le_normalizer_pCoreOf 2 L) Subgroup.le_normalizer

theorem card_blockU_ge [Finite G] {L : Subgroup G} {m : ℕ} (hL : IsOmega4MinusBlock L m) :
    (2 ^ m) ^ 4 ≤ Nat.card (blockU L) := by
  obtain ⟨-, -, hc, K, _, _, _, hK, π, -, -, -, -, -, -, -, β, hβs, -, -⟩ := hL
  have h1 := Nat.card_le_card_of_surjective β hβs
  have hbot : Nat.card ((FFModel.twistTensor m (StatedSL 2 K)).ker.subgroupOf
      (FFModel.twistTensor m (StatedSL 2 K)).sec) = 1 := by
    rw [show (FFModel.twistTensor m (StatedSL 2 K)).ker = ⊥ from rfl, Subgroup.bot_subgroupOf,
      Subgroup.card_bot]
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((FFModel.twistTensor m (StatedSL 2 K)).ker.subgroupOf
      (FFModel.twistTensor m (StatedSL 2 K)).sec)
  rw [hbot, mul_one] at h2
  rw [← h2, Subgroup.card_top] at h1
  calc (2 ^ m) ^ 4 = 2 ^ (4 * m) := by rw [← pow_mul, mul_comm]
    _ ≤ Nat.card (hermSub m (Fin 2) K) := Herm.card_hermSub_ge hK
    _ ≤ Nat.card ↥(blockU L) := h1

theorem exists_fixed_of_pow [Finite G] {L : Subgroup G} {m : ℕ} (hm : 1 ≤ m)
    (hL : IsOmega4MinusBlock L m) {y : G} (hy : y ∈ L) (hyq : y ^ (2 ^ m - 1) = 1) :
    ∃ u ∈ blockU L, u ≠ 1 ∧ y * u * y⁻¹ = u := by
  obtain ⟨⟨hS, -, -⟩, -, hc, K, _, _, _, hK, π, hπs, -, -, -, -, -, -, β, hβs, -, hβe⟩ := hL
  set U := blockU L with hU
  have hLN : L ≤ Subgroup.normalizer (U : Set G) := le_normalizer_blockU L
  have hyN : y ∈ Subgroup.normalizer (U : Set G) := hLN hy
  set cy : MulAut ↥U := conjAct U ⟨y, hyN⟩ with hcy
  have hcy_apply : ∀ u : ↥U, ((cy u : ↥U) : G) = y * u * y⁻¹ := fun u => by
    simp [hcy, conjAct]
  have hcyL : cy ∈ autOn L U := ⟨⟨y, hyN⟩, hy, rfl⟩
  have hcyq : cy ^ (2 ^ m - 1) = 1 := by
    rw [hcy, ← map_pow]
    have : (⟨y, hyN⟩ : ↥(Subgroup.normalizer (U : Set G))) ^ (2 ^ m - 1) = 1 :=
      Subtype.ext (by simp [hyq])
    rw [this, map_one]
  set π' : ↥(StatedSL 2 K) →* ↥(autOn L U) := π with hπ'
  have hπs' : Function.Surjective π' := hπs
  obtain ⟨A, hA⟩ := hπs' ⟨cy, hcyL⟩
  obtain ⟨u₁, hu₁U, hu₁Z⟩ := IsConcreteLE.exists_of_lt hS.2.2.2.2.1
  have hK4 : ∃ s : Finset K, s.card = 4 := by
    have := Fintype.ofFinite K
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K)) (n := 4) (by
      rw [Finset.card_univ, Fintype.card_eq_nat_card, hK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (2 * m) := Nat.pow_le_pow_right (by norm_num) (by omega))
    exact ⟨s, hs⟩
  have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) K) :=
    Vol2Native.A312L.sl2_isSimple hK4
  have hsimp : IsSimpleGroup ↥(StatedSL 2 K) :=
    (specialLinearGroupEquivStatedSL 2 K).symm.isSimpleGroup
  have hπi : Function.Injective π' := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π'.ker with h | h
    · exact (MonoidHom.ker_eq_bot_iff π').mp h
    · exfalso
      apply hu₁Z
      refine Subgroup.mem_inf.mpr ⟨hu₁U, Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
      obtain ⟨γ, hγ⟩ := hπs' ⟨conjAct U ⟨l, hLN hl⟩, ⟨⟨l, hLN hl⟩, hl, rfl⟩⟩
      have h1 : π' γ = 1 := (MonoidHom.mem_ker).mp (h ▸ Subgroup.mem_top γ)
      rw [h1] at hγ
      have h2 := congrArg (fun a : ↥(autOn L U) => (((a : MulAut ↥U) ⟨u₁, hu₁U⟩ : ↥U) : G)) hγ
      simp only [OneMemClass.coe_one, MulAut.one_apply] at h2
      have h4 : (((conjAct U ⟨l, hLN hl⟩) ⟨u₁, hu₁U⟩ : ↥U) : G) = l * u₁ * l⁻¹ := by
        simp [conjAct]
      have h3 : l * u₁ * l⁻¹ = u₁ := h4.symm.trans h2.symm
      calc l * u₁ = (l * u₁ * l⁻¹) * l := by group
        _ = u₁ * l := by rw [h3]
  have hApow : A ^ (2 ^ m - 1) = 1 := by
    apply hπi
    have h1 : π' (A ^ (2 ^ m - 1)) = π' A ^ (2 ^ m - 1) := map_pow π' A _
    have h2 : (⟨cy, hcyL⟩ : ↥(autOn L U)) ^ (2 ^ m - 1) = 1 := by
      apply Subtype.ext
      rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
      exact hcyq
    rw [h1, hA, h2]
    exact (map_one π').symm
  by_cases hA1 : A = 1
  ·
    refine ⟨u₁, hu₁U, fun h1 => hu₁Z (h1 ▸ one_mem _), ?_⟩
    rw [hA1, map_one] at hA
    have h2 := congrArg (fun a : ↥(autOn L U) => (((a : MulAut ↥U) ⟨u₁, hu₁U⟩ : ↥U) : G)) hA
    simp only [OneMemClass.coe_one, MulAut.one_apply] at h2
    rw [← hcy_apply ⟨u₁, hu₁U⟩]
    exact h2.symm
  set M := ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) with hMdef
  have hMSL : M = (((specialLinearGroupEquivStatedSL 2 K).symm A :
      Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
    have h := specialLinearGroupEquivStatedSL_coe 2 K ((specialLinearGroupEquivStatedSL 2 K).symm A)
    rw [MulEquiv.apply_symm_apply] at h
    exact h
  have hdet : M.det = 1 := by
    rw [hMSL]
    exact ((specialLinearGroupEquivStatedSL 2 K).symm A).2
  have hM1 : M ≠ 1 := by
    intro h
    apply hA1
    apply Subtype.ext
    apply Units.ext
    simpa [hMdef] using h
  have hA' : A ^ 2 ^ m = A := by
    rw [← Nat.sub_add_cancel (Nat.one_le_two_pow (n := m)), pow_succ, hApow, one_mul]
  have hpow : M ^ 2 ^ m = M := by
    have := congrArg (fun B : ↥(StatedSL 2 K) => ((B : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))
      hA'
    simpa [hMdef] using this
  obtain ⟨X, hX0, hXh, hXA⟩ :=
    Herm.exists_herm_fixed (Herm.pow_two_pow_two_pow_eq hK) hdet hM1 hpow
  have hXD : Multiplicative.ofAdd X ∈ (FFModel.twistTensor m (StatedSL 2 K)).sec := hXh
  set m₀ : ↥(FFModel.twistTensor m (StatedSL 2 K)).sec := ⟨Multiplicative.ofAdd X, hXD⟩ with hm₀
  have hact : (FFModel.twistTensor m (StatedSL 2 K)).act A (Multiplicative.ofAdd X) =
      Multiplicative.ofAdd X := by
    show twistAct m (StatedSL 2 K) A (Multiplicative.ofAdd X) = Multiplicative.ofAdd X
    simp only [twistAct, toAdd_ofAdd]
    rw [← hMdef, hXA]
  have hmem : (FFModel.twistTensor m (StatedSL 2 K)).act A
      (m₀ : (FFModel.twistTensor m (StatedSL 2 K)).Amb) ∈
      (FFModel.twistTensor m (StatedSL 2 K)).sec := by
    show (FFModel.twistTensor m (StatedSL 2 K)).act A (Multiplicative.ofAdd X) ∈
      (FFModel.twistTensor m (StatedSL 2 K)).sec
    rw [hact]
    exact hXD
  set β' : ↥U →* ↥(FFModel.twistTensor m (StatedSL 2 K)).sec ⧸
      (FFModel.twistTensor m (StatedSL 2 K)).ker.subgroupOf
        (FFModel.twistTensor m (StatedSL 2 K)).sec :=
    β.comp (Subgroup.topEquiv (G := ↥U)).symm.toMonoidHom with hβ'
  have hstep : ∀ u : ↥U, β' u = QuotientGroup.mk m₀ → β' (cy u) = QuotientGroup.mk m₀ := by
    intro u hu
    have h1 := hβe A ⟨u, Subgroup.mem_top u⟩ m₀ (Subgroup.mem_top _) hmem hu
    have e1 : β' (cy u) = β ⟨((π A : ↥(autOn L U)) : MulAut ↥U)
        ((⟨u, Subgroup.mem_top u⟩ : ↥(⊤ : Subgroup ↥U)) : ↥U), Subgroup.mem_top _⟩ := by
      show β ((Subgroup.topEquiv (G := ↥U)).symm (cy u)) = _
      congr 1
      apply Subtype.ext
      show cy u = ((π' A : ↥(autOn L U)) : MulAut ↥U) u
      rw [hA]
    have e2 : (QuotientGroup.mk ⟨(FFModel.twistTensor m (StatedSL 2 K)).act A
        (m₀ : (FFModel.twistTensor m (StatedSL 2 K)).Amb), hmem⟩ :
          ↥(FFModel.twistTensor m (StatedSL 2 K)).sec ⧸
          (FFModel.twistTensor m (StatedSL 2 K)).ker.subgroupOf
            (FFModel.twistTensor m (StatedSL 2 K)).sec) =
        QuotientGroup.mk m₀ := by
      congr 1
      exact Subtype.ext hact
    exact e1.trans (h1.trans e2)
  obtain ⟨u₀, hu₀⟩ := hβs (QuotientGroup.mk m₀)
  set v₀ : ↥U := (u₀ : ↥U) with hv₀
  have hv₀β : β' v₀ = QuotientGroup.mk m₀ := hu₀
  have hiter : ∀ i : ℕ, β' ((cy ^ i) v₀) = QuotientGroup.mk m₀ := by
    intro i
    induction i with
    | zero => simpa using hv₀β
    | succ i ih =>
      rw [pow_succ', MulAut.mul_apply]
      exact hstep _ ih
  set N : ↥U := ∏ i ∈ Finset.range (2 ^ m - 1), (cy ^ i) v₀ with hN
  have hNfix : cy N = N := by
    rw [hN, map_prod]
    have e1 := Finset.prod_range_succ' (fun i => (cy ^ i) v₀) (2 ^ m - 1)
    have e2 := Finset.prod_range_succ (fun i => (cy ^ i) v₀) (2 ^ m - 1)
    simp only [hcyq, pow_zero, MulAut.one_apply] at e1 e2
    have e3 : ∏ i ∈ Finset.range (2 ^ m - 1), (cy ^ (i + 1)) v₀ =
        ∏ i ∈ Finset.range (2 ^ m - 1), (cy ^ i) v₀ := mul_right_cancel (e1.symm.trans e2)
    rw [← e3]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [pow_succ', MulAut.mul_apply]
  have hm₀2 : m₀ * m₀ = 1 := by
    apply Subtype.ext
    show (Multiplicative.ofAdd X * Multiplicative.ofAdd X :
      Multiplicative (Matrix (Fin 2) (Fin 2) K)) = 1
    rw [← ofAdd_add, CharTwo.add_self_eq_zero, ofAdd_zero]
  have hodd : Odd (2 ^ m - 1) := by
    have h2 : 2 ≤ 2 ^ m := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    have : Even (2 ^ m) := (Nat.even_pow.mpr ⟨even_two, by omega⟩)
    obtain ⟨k, hk⟩ := this
    exact ⟨k - 1, by omega⟩
  have hNβ : β' N = QuotientGroup.mk m₀ := by
    rw [hN, map_prod, Finset.prod_congr rfl (fun i _ => hiter i), Finset.prod_const,
      Finset.card_range]
    obtain ⟨k, hk⟩ := hodd
    rw [hk, pow_succ, pow_mul, ← QuotientGroup.mk_pow, sq, hm₀2, QuotientGroup.mk_one, one_pow,
      one_mul]
  have hmk : (QuotientGroup.mk m₀ : ↥(FFModel.twistTensor m (StatedSL 2 K)).sec ⧸
      (FFModel.twistTensor m (StatedSL 2 K)).ker.subgroupOf
        (FFModel.twistTensor m (StatedSL 2 K)).sec) ≠ 1 := by
    intro h
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
    have h1 : (Multiplicative.ofAdd X : Multiplicative (Matrix (Fin 2) (Fin 2) K)) = 1 := h
    apply hX0
    exact congrArg Multiplicative.toAdd h1
  refine ⟨(N : G), N.2, fun h1 => ?_, ?_⟩
  · apply hmk
    rw [← hNβ, show N = 1 from Subtype.ext h1, map_one]
  · rw [← hcy_apply N, hNfix]

end CFSG.Quasithin.H13.Omega4
