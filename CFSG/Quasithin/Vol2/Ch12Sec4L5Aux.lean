module

public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitAltNatural
public import CFSG.Quasithin.Background.B4ModelsWitness
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.B4ModelsApi
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin

theorem card_mod_nat {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K]
    (Γ : Subgroup (Matrix.GeneralLinearGroup ι K)) :
    Nat.card (FFModel.nat Γ).Mod = Nat.card K ^ Fintype.card ι := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((FFModel.nat Γ).ker.subgroupOf (FFModel.nat Γ).sec)
  have h1 : Nat.card ↥((FFModel.nat Γ).ker.subgroupOf (FFModel.nat Γ).sec) = 1 := by
    rw [Subgroup.card_eq_one]
    exact Subgroup.bot_subgroupOf _
  rw [h1, mul_one] at h
  rw [← h]
  show Nat.card ↥(⊤ : Subgroup (Multiplicative (ι → K))) = _
  rw [Subgroup.card_top, Nat.card_congr Multiplicative.toAdd, Nat.card_fun,
    Nat.card_eq_fintype_card (α := ι)]

theorem card_mod_altDn {n : ℕ} (hn : Even n) (hn2 : 2 ≤ n) :
    Nat.card (FFModel.altDn n).Mod = 2 ^ (n - 2) := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((FFModel.altDn n).ker.subgroupOf (FFModel.altDn n).sec)
  have hk : Nat.card ↥((FFModel.altDn n).ker.subgroupOf (FFModel.altDn n).sec) = 2 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_right : (FFModel.altDn n).ker ≤ (FFModel.altDn n).sec)).toEquiv).trans
      (Orbit.altDn_card_ker_even hn (by omega))
  have hs : Nat.card ↥(FFModel.altDn n).sec = 2 ^ (n - 1) := Explicit.card_coreMod (by omega)
  rw [hk, hs] at h
  have h2 : 2 ^ (n - 1) = 2 ^ (n - 2) * 2 := by
    rw [← pow_succ]
    congr 1
    omega
  rw [h2] at h
  exact (Nat.eq_of_mul_eq_mul_right (by norm_num) h).symm

variable {H : Type*} [Group H]

theorem pCoreOf_eq_bot_of_simple [Finite H] {X : Subgroup H} (hs : IsSimpleGroup X)
    (hX : ¬ IsPGroup 2 X) :
    pCoreOf 2 X = ⊥ := by
  have hle := LieType.BorelTits.pCoreOf_le 2 X
  have hnormal : ((pCoreOf 2 X).subgroupOf X).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (LieType.BorelTits.le_normalizer_pCoreOf 2 X)
  rcases hs.eq_bot_or_eq_top_of_normal ((pCoreOf 2 X).subgroupOf X) with h | h
  · rw [← Subgroup.map_subgroupOf_eq_of_le hle, h, Subgroup.map_bot]
  · exfalso
    apply hX
    have hXP : X ≤ pCoreOf 2 X := by
      intro x hx
      have h1 : (⟨x, hx⟩ : X) ∈ (pCoreOf 2 X).subgroupOf X := h ▸ Subgroup.mem_top _
      exact h1
    exact (LieType.BorelTits.pCoreOf_isPGroup 2 X).to_le hXP

theorem not_isPGroup_of_card_eq_168 {X : Subgroup H} (hX : Nat.card X = 168) : ¬ IsPGroup 2 X := by
  have : Finite X := Nat.finite_of_card_ne_zero (by rw [hX]; norm_num)
  intro hp
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  rw [hX] at hn
  have h8 : n < 8 := by
    by_contra h
    push Not at h
    have := Nat.pow_le_pow_right (by norm_num : 0 < 2) h
    omega
  interval_cases n <;> omega

theorem inf_centralizer_eq_bot_of_simple {X : Subgroup H} (hs : IsSimpleGroup X)
    (hnab : ∃ a b : X, a * b ≠ b * a) : X ⊓ Subgroup.centralizer (X : Set H) = ⊥ := by
  have hnorm : ((Subgroup.centralizer (X : Set H)).subgroupOf X).Normal := by
    refine ⟨fun n hn x => ?_⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at hn ⊢
    intro y hy
    have h1 := hn y hy
    have h2 := hn (x : H) x.2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc y * (↑x * ↑n * (↑x)⁻¹) = y * (↑n * ↑x * (↑x)⁻¹) := by rw [← h2]
      _ = y * n := by group
      _ = n * y := h1
      _ = ↑n * ↑x * (↑x)⁻¹ * y := by group
      _ = ↑x * ↑n * (↑x)⁻¹ * y := by rw [h2]
  rcases hs.eq_bot_or_eq_top_of_normal ((Subgroup.centralizer (X : Set H)).subgroupOf X)
    with hb | ht
  · refine eq_bot_iff.2 fun y hy => ?_
    have h1 : (⟨y, hy.1⟩ : X) ∈ (Subgroup.centralizer (X : Set H)).subgroupOf X :=
      Subgroup.mem_subgroupOf.2 hy.2
    rw [hb, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.2 (congrArg Subtype.val h1)
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    have h1 : a ∈ (Subgroup.centralizer (X : Set H)).subgroupOf X := ht ▸ Subgroup.mem_top a
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at h1
    exact Subtype.ext (h1 b b.2).symm

theorem commutator_eq_of_simple {X A : Subgroup H} (hs : IsSimpleGroup X)
    (hnab : ∃ a b : X, a * b ≠ b * a) (hAX : A ≤ X) (hA : A ≠ ⊥) : ⁅X, A⁆ = X := by
  have hle : ⁅X, A⁆ ≤ X := by
    rw [Subgroup.commutator_le]
    intro x hx a ha
    rw [commutatorElement_def]
    exact X.mul_mem (X.mul_mem (X.mul_mem hx (hAX ha)) (X.inv_mem hx)) (X.inv_mem (hAX ha))
  have hnormal : ((⁅X, A⁆ : Subgroup H).subgroupOf X).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (Subgroup.normalizer_commutator_ge_left X A)
  rcases hs.eq_bot_or_eq_top_of_normal ((⁅X, A⁆ : Subgroup H).subgroupOf X) with h | h
  · exfalso
    apply hA
    have hbot : ⁅X, A⁆ = ⊥ := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hle, h, Subgroup.map_bot]
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hbot
    have h1 := inf_centralizer_eq_bot_of_simple hs hnab
    refine eq_bot_iff.2 fun a ha => ?_
    have h2 : a ∈ X ⊓ Subgroup.centralizer (X : Set H) := by
      refine ⟨hAX ha, Subgroup.mem_centralizer_iff.2 fun x hx => ?_⟩
      exact (Subgroup.mem_centralizer_iff.1 (hbot hx) a ha).symm
    rw [h1] at h2
    exact h2
  · refine le_antisymm hle fun x hx => ?_
    have h1 : (⟨x, hx⟩ : X) ∈ (⁅X, A⁆ : Subgroup H).subgroupOf X := h ▸ Subgroup.mem_top _
    exact h1

theorem eq_of_isSylowTwoOf_le [Finite H] {S S' P : Subgroup H}
    (hS : QuasithinUnique.IsSylowTwoOf S P) (hSS' : S ≤ S') (hS'P : S' ≤ P)
    (hS' : IsPGroup 2 S') : S' = S := by
  obtain ⟨S'', hS'S'', hS''⟩ := QuasithinUnique.exists_isSylowTwoOf_of_le hS'P hS'
  have h1 : S = S'' := Subgroup.eq_of_le_of_card_ge (hSS'.trans hS'S'')
    (by rw [hS''.card_eq, hS.card_eq])
  exact le_antisymm (h1 ▸ hS'S'') hSS'

end CFSG.Quasithin.H13
