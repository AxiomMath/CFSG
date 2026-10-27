module

public import CFSG.Timmesfeld.Bridge.OddRootSzMainTwoTrans

import CFSG.StronglyEmbedded.BenderCentre
import CFSG.Timmesfeld.Bridge.Asc72Bender
import CFSG.Goldschmidt.Steps.GoldTypeBender
import CFSG.LocalAnalysis.ComponentClassification.Asc76BenderFactsBasic
import CFSG.GroupTheory.IrreducibleAbelianAction
import CFSG.Quasithin.Recognition.St84.WeissB
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.Timmesfeld.Bridge.OddRoot

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge

variable {Ω : Type} [Finite Ω] {X T : Subgroup (Equiv.Perm Ω)} {α : Ω}

namespace TwoTransHyp


private lemma tSub_le_twoTransY (h : TwoTransHyp X T α) (β : Ω) :
    h.tSub β ≤ twoTransY X T := by
  intro s hs
  rw [h.mem_tSub_iff] at hs
  obtain ⟨t, ht, rfl⟩ := hs
  exact conj_mem_twoTransY (h.pointRep_mem β) (le_twoTransY ht)

private lemma isElemAbelian_tSub (h : TwoTransHyp X T α) (β : Ω) :
    CFSG.Open.IsElemAbelian 2 (h.tSub β) := by
  rw [h.tSub_eq_conj (x := h.pointRep β) (h.pointRep_mem β) (h.pointRep_alpha β)]
  exact h.elemAb.map _

private lemma tSub_alpha_eq (h : TwoTransHyp X T α) : h.tSub α = T := by
  rw [h.tSub_eq_conj (x := 1) X.one_mem (by simp)]
  ext s
  simp [Subgroup.mem_map, MulAut.conj_apply]

private lemma exists_mem_tSub_ne_one (h : TwoTransHyp X T α) (β : Ω) :
    ∃ t ∈ h.tSub β, t ≠ 1 := by
  obtain ⟨t, ht, ht1⟩ := h.exists_ne_one
  refine ⟨h.pointRep β * t * (h.pointRep β)⁻¹, ?_, ?_⟩
  · rw [h.mem_tSub_iff]
    exact ⟨t, ht, rfl⟩
  · intro hconj
    apply ht1
    have h2 : (h.pointRep β)⁻¹ * (h.pointRep β * t * (h.pointRep β)⁻¹) *
        h.pointRep β = t := by group
    rw [hconj] at h2
    simpa using h2.symm

private lemma exists_sylow_le_tSub (h : TwoTransHyp X T α) (β : Ω) :
    ∃ Q : Sylow 2 ↥(twoTransY X T),
      (h.tSub β).subgroupOf (twoTransY X T) ≤ (Q : Subgroup ↥(twoTransY X T)) := by
  have hY : CFSG.BenderSuzuki.IsBenderGroup ↥(twoTransY X T) := h.isBenderGroup
  have hE : CFSG.Open.IsElemAbelian 2
      ((h.tSub β).subgroupOf (twoTransY X T)) :=
    (h.isElemAbelian_tSub β).subgroupOf _
  obtain ⟨Q, hQ⟩ :=
    CFSG.StronglyEmbedded.BenderCentre.exists_le_sylowCenter hY hE
  exact ⟨Q, hQ.trans
    (CFSG.ComponentClassification.AschbacherToolkit.Bender.sylowCenter_le _)⟩

private noncomputable def sylowAt (h : TwoTransHyp X T α) (β : Ω) :
    Sylow 2 ↥(twoTransY X T) :=
  Classical.choose (h.exists_sylow_le_tSub β)

private lemma tSub_subgroupOf_le_sylowAt (h : TwoTransHyp X T α) (β : Ω) :
    (h.tSub β).subgroupOf (twoTransY X T) ≤
      (h.sylowAt β : Subgroup ↥(twoTransY X T)) :=
  Classical.choose_spec (h.exists_sylow_le_tSub β)

private lemma eq_sylowAt_of_tSub_le (h : TwoTransHyp X T α) {β : Ω}
    {Q : Sylow 2 ↥(twoTransY X T)}
    (hQ : (h.tSub β).subgroupOf (twoTransY X T) ≤
      (Q : Subgroup ↥(twoTransY X T))) :
    Q = h.sylowAt β := by
  by_contra hne
  have hY : CFSG.BenderSuzuki.IsBenderGroup ↥(twoTransY X T) := h.isBenderGroup
  obtain ⟨q, k, hB, -⟩ :=
    CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.exists_fusionBenderBorel hY
  have hbot :=
    CFSG.ComponentClassification.Asc76X.inf_eq_bot_of_fusionBenderBorel hB hne
  obtain ⟨t, ht, ht1⟩ := h.exists_mem_tSub_ne_one β
  have htY : t ∈ twoTransY X T := h.tSub_le_twoTransY β ht
  have hmemQ : (⟨t, htY⟩ : ↥(twoTransY X T)) ∈
      (Q : Subgroup ↥(twoTransY X T)) := hQ ht
  have hmemS : (⟨t, htY⟩ : ↥(twoTransY X T)) ∈
      (h.sylowAt β : Subgroup ↥(twoTransY X T)) :=
    h.tSub_subgroupOf_le_sylowAt β ht
  have hmem : (⟨t, htY⟩ : ↥(twoTransY X T)) ∈
      ((Q : Subgroup ↥(twoTransY X T)) ⊓
        (h.sylowAt β : Subgroup ↥(twoTransY X T))) := ⟨hmemQ, hmemS⟩
  rw [hbot] at hmem
  exact ht1 (congrArg Subtype.val (Subgroup.mem_bot.mp hmem))

private lemma sylowAt_injective (h : TwoTransHyp X T α) : Function.Injective h.sylowAt := by
  intro β γ hβγ
  by_contra hne
  obtain ⟨t, ht, ht1⟩ := h.exists_mem_tSub_ne_one β
  obtain ⟨u, hu, hu1⟩ := h.exists_mem_tSub_ne_one γ
  have htY : t ∈ twoTransY X T := h.tSub_le_twoTransY β ht
  have huY : u ∈ twoTransY X T := h.tSub_le_twoTransY γ hu
  have htQ : (⟨t, htY⟩ : ↥(twoTransY X T)) ∈
      (h.sylowAt β : Subgroup ↥(twoTransY X T)) :=
    h.tSub_subgroupOf_le_sylowAt β ht
  have huQ : (⟨u, huY⟩ : ↥(twoTransY X T)) ∈
      (h.sylowAt β : Subgroup ↥(twoTransY X T)) := by
    rw [hβγ]
    exact h.tSub_subgroupOf_le_sylowAt γ hu
  have htD : t ∈ twoTransD X T := h.tSub_subset_twoTransD ht ht1
  have huD : u ∈ twoTransD X T := h.tSub_subset_twoTransD hu hu1
  have ht2 : t * t = 1 := h.mul_self_of_mem_twoTransD htD
  have hu2 : u * u = 1 := h.mul_self_of_mem_twoTransD huD
  have hcomplex : Commute (⟨t, htY⟩ : ↥(twoTransY X T))
      (⟨u, huY⟩ : ↥(twoTransY X T)) :=
    CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.commute_of_mul_self_eq_one
      h.isBenderGroup (h.sylowAt β) htQ (by simpa using ht2) ⟨u, huY⟩ huQ
  have hcomm : t * u = u * t := congrArg Subtype.val hcomplex.eq
  obtain ⟨δ, hδt, hδu⟩ := (h.commute_iff htD huD).mp hcomm
  have hδβ : δ = β := h.tSub_unique_fixed ht ht1 δ hδt
  have hδγ : δ = γ := h.tSub_unique_fixed hu hu1 δ hδu
  exact hne (hδβ.symm.trans hδγ)

private lemma sylowAt_surjective (h : TwoTransHyp X T α) : Function.Surjective h.sylowAt := by
  intro Q
  obtain ⟨y, hy⟩ :=
    MulAction.exists_smul_eq ↥(twoTransY X T) (h.sylowAt α) Q
  refine ⟨(y : Equiv.Perm Ω) α, ?_⟩
  have hyX : (y : Equiv.Perm Ω) ∈ X := h.twoTransY_le_X y.2
  have hle : (h.tSub ((y : Equiv.Perm Ω) α)).subgroupOf (twoTransY X T) ≤
      (Q : Subgroup ↥(twoTransY X T)) := by
    rw [← hy]
    intro s hs
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    have hsD : (s : Equiv.Perm Ω) ∈ h.tSub ((y : Equiv.Perm Ω) α) := hs
    have hconj := h.conj_mem_tSub (X.inv_mem hyX) hsD
    have hα : (y : Equiv.Perm Ω)⁻¹ ((y : Equiv.Perm Ω) α) = α := by simp
    rw [hα, h.tSub_alpha_eq] at hconj
    let z : Equiv.Perm Ω := (y : Equiv.Perm Ω)⁻¹ * (s : Equiv.Perm Ω) * (y : Equiv.Perm Ω)
    have hzT : z ∈ T := hconj
    have hzT' : z ∈ h.tSub α := by
      rw [h.tSub_alpha_eq]
      exact hzT
    have hzY : z ∈ twoTransY X T := le_twoTransY hzT
    have hzS : (⟨z, hzY⟩ : ↥(twoTransY X T)) ∈
        (h.sylowAt α : Subgroup ↥(twoTransY X T)) :=
      h.tSub_subgroupOf_le_sylowAt α hzT'

    refine ⟨⟨z, hzY⟩, hzS, ?_⟩
    ext
    simp [z, MulAut.conj_apply, mul_assoc]
  exact (h.eq_sylowAt_of_tSub_le hle).symm

private lemma card_sylow_eq_card (h : TwoTransHyp X T α) :
    Nat.card (Sylow 2 ↥(twoTransY X T)) = Nat.card Ω :=
  (Nat.card_congr (Equiv.ofBijective h.sylowAt
    ⟨h.sylowAt_injective, h.sylowAt_surjective⟩)).symm

theorem exists_card_eq (h : TwoTransHyp X T α) : ∃ j : ℕ, Nat.card Ω = 2 ^ j + 1 := by
  have hY : CFSG.BenderSuzuki.IsBenderGroup ↥(twoTransY X T) := h.isBenderGroup
  have hB : CFSG.Open.fusionIsBenderGroup ↥(twoTransY X T) :=
    CFSG.StronglyEmbedded.BenderCentre.fusionIsBenderGroup_of_isBenderGroup hY
  have hcard : Nat.card (Sylow 2 ↥(twoTransY X T)) =
      Nat.card (h.sylowAt α : Subgroup ↥(twoTransY X T)) + 1 :=
    CFSG.Goldschmidt.GoldType.card_sylow_of_bender hB (h.sylowAt α)
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp (h.sylowAt α).isPGroup'
  refine ⟨j, ?_⟩
  rw [← h.card_sylow_eq_card, hcard, hj]

end TwoTransHyp

private lemma card_subtype_ne {j : ℕ} (hcard : Nat.card Ω = 2 ^ j + 1) :
    Nat.card {β : Ω // β ≠ α} = 2 ^ j := by
  classical
  haveI : Fintype Ω := Fintype.ofFinite Ω
  haveI : Fintype {β : Ω // β ≠ α} := Fintype.ofFinite _
  haveI : Fintype {β : Ω // β = α} := Fintype.ofFinite _
  have hc : Fintype.card {β : Ω // β ≠ α} = Fintype.card Ω - 1 := by
    have h := Fintype.card_subtype_compl (p := fun β : Ω => β = α)
    rwa [Fintype.card_subtype_eq] at h
  have hcardF : Fintype.card Ω = 2 ^ j + 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  have hpow : 0 < 2 ^ j := Nat.pow_pos (by norm_num)
  rw [Nat.card_eq_fintype_card]
  omega

@[instance_reducible]
private noncomputable def actionOnComplement {N : Type} [Group N]
    (φ : N →* Equiv.Perm Ω) (hNα : ∀ x : N, φ x α = α) :
    MulAction N {β : Ω // β ≠ α} :=
  { smul := fun n β => ⟨(φ n) β.1, by
      intro h
      have h2 : (φ n)⁻¹ α = α := by
        have := congrArg (⇑((φ n)⁻¹)) (hNα n)
        simpa using this.symm
      have h3 : (φ n)⁻¹ ((φ n) β.1) = (φ n)⁻¹ α := congrArg (⇑((φ n)⁻¹)) h
      have h1 : (φ n)⁻¹ ((φ n) β.1) = β.1 := by simp
      rw [h1, h2] at h3
      exact β.2 h3⟩
    one_smul := fun β => Subtype.ext (by
      change (φ 1) β.1 = β.1
      rw [map_one]
      rfl)
    mul_smul := fun n m β => Subtype.ext (by
      change (φ (n * m)) β.1 = (φ n) ((φ m) β.1)
      rw [map_mul]
      rfl) }

private lemma card_add_one_of_transitive {T : Subgroup (Equiv.Perm Ω)} {α : Ω} {j : ℕ}
    [MulAction T {β : Ω // β ≠ α}]
    (hsemi : ∀ t ∈ T, ∀ β : Ω, β ≠ α → t β = β → t = 1)
    (hcard : Nat.card Ω = 2 ^ j + 1)
    (hΩ'card : Nat.card {β : Ω // β ≠ α} = 2 ^ j)
    (hact : ∀ (t : T) (β : {β : Ω // β ≠ α}),
      ((t • β : {β : Ω // β ≠ α}) : Ω) = t.1 β.1)
    (hTtrans : ∀ a b : {β : Ω // β ≠ α}, ∃ t : T, t • a = b) :
    Nat.card T + 1 = Nat.card Ω := by
  have hpow : 0 < 2 ^ j := Nat.pow_pos (by norm_num)
  haveI : Nontrivial Ω :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; omega)
  obtain ⟨β0, hβ0⟩ := exists_ne α
  let β0' : {β : Ω // β ≠ α} := ⟨β0, hβ0⟩
  have hinj : Function.Injective (fun t : T => t • β0') := by
    intro t1 t2 h
    have h' : t1 • β0' = t2 • β0' := h
    have hfix : (t2⁻¹ * t1) • β0' = β0' := by
      calc (t2⁻¹ * t1) • β0' = t2⁻¹ • (t1 • β0') := by rw [mul_smul]
        _ = t2⁻¹ • (t2 • β0') := by rw [h']
        _ = β0' := by rw [← mul_smul, inv_mul_cancel, one_smul]
    have hfixval : (t2⁻¹ * t1).1 β0'.1 = β0'.1 := by
      rw [← hact (t2⁻¹ * t1) β0']
      exact congrArg Subtype.val hfix
    have h1 : (t2⁻¹ * t1).1 = 1 :=
      hsemi (t2⁻¹ * t1).1 (t2⁻¹ * t1).2 β0'.1 β0'.2 hfixval
    apply Subtype.ext
    have h2 : (t2.1)⁻¹ * t1.1 = 1 := by simpa using h1
    calc t1.1 = t2.1 * ((t2.1)⁻¹ * t1.1) := by group
      _ = t2.1 := by rw [h2, mul_one]
  have hsurj : Function.Surjective (fun t : T => t • β0') := by
    intro b
    obtain ⟨t, ht⟩ := hTtrans β0' b
    exact ⟨t, ht⟩
  have hcardT : Nat.card T = Nat.card {β : Ω // β ≠ α} :=
    Nat.card_congr (Equiv.ofBijective _ ⟨hinj, hsurj⟩)
  rw [hcardT, hΩ'card, hcard]

theorem card_add_one_of_semireg {N : Type} [Group N] [Finite N] (φ : N →* Equiv.Perm Ω)
    {T : Subgroup (Equiv.Perm Ω)} {α : Ω} {j : ℕ}
    (hsemi : ∀ t ∈ T, ∀ β : Ω, β ≠ α → t β = β → t = 1)
    (hTα : ∀ t ∈ T, t α = α)
    (hcard : Nat.card Ω = 2 ^ j + 1) (hNα : ∀ x : N, φ x α = α)
    (hN : ∀ β γ : Ω, β ≠ α → γ ≠ α → ∃ x : N, φ x β = γ)
    {P : Subgroup N} (hP : IsPGroup 2 P) (hidx : ¬ 2 ∣ P.index)
    (horb : ∀ p ∈ P, ∀ β : Ω, β ≠ α → ∃ t ∈ T, φ p β = t β) :
    Nat.card T + 1 = Nat.card Ω := by
  classical
  let Ω' := {β : Ω // β ≠ α}
  have hΩ'card : Nat.card Ω' = 2 ^ j := card_subtype_ne (α := α) hcard
  letI : MulAction N Ω' := actionOnComplement φ hNα
  letI : MulAction T Ω' := actionOnComplement T.subtype (fun t => hTα t.1 t.2)
  have hTtrans : ∀ a b : Ω', ∃ t : T, t • a = b := by
    intro a b
    have htrans : ∀ a b : Ω', ∃ x : N, x • a = b := by
      intro a b
      obtain ⟨x, hx⟩ := hN a.1 b.1 a.2 b.2
      exact ⟨x, Subtype.ext hx⟩
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨p, hpP, hpab⟩ := CFSG.Quasithin.St84.sylow_pretransitive_of_card_prime_pow
      (p := 2) (k := j) hΩ'card htrans hP hidx a b
    have hpval : (φ p) a.1 = b.1 := congrArg Subtype.val hpab
    obtain ⟨t, htT, ht⟩ := horb p hpP a.1 a.2
    refine ⟨⟨t, htT⟩, Subtype.ext ?_⟩
    show t a.1 = b.1
    rw [← ht, hpval]
  exact card_add_one_of_transitive (T := T) hsemi hcard hΩ'card
    (fun t β => rfl) hTtrans

namespace TwoTransHyp

section Certificates


private lemma sylowAt_alpha_eq_tSub (h : TwoTransHyp X T α)
    (hreg : Nat.card T + 1 = Nat.card Ω) :
    (h.sylowAt α : Subgroup ↥(twoTransY X T)) = T.subgroupOf (twoTransY X T) := by
  have hY : CFSG.BenderSuzuki.IsBenderGroup ↥(twoTransY X T) := h.isBenderGroup
  have hB : CFSG.Open.fusionIsBenderGroup ↥(twoTransY X T) :=
    CFSG.StronglyEmbedded.BenderCentre.fusionIsBenderGroup_of_isBenderGroup hY
  have hcardSyl : Nat.card (Sylow 2 ↥(twoTransY X T)) =
      Nat.card (h.sylowAt α : Subgroup ↥(twoTransY X T)) + 1 :=
    CFSG.Goldschmidt.GoldType.card_sylow_of_bender hB (h.sylowAt α)
  have hcardQ : Nat.card (h.sylowAt α : Subgroup ↥(twoTransY X T)) = Nat.card T := by
    have h1 : Nat.card (h.sylowAt α : Subgroup ↥(twoTransY X T)) + 1 =
        Nat.card T + 1 := by
      calc Nat.card (h.sylowAt α : Subgroup ↥(twoTransY X T)) + 1
          = Nat.card (Sylow 2 ↥(twoTransY X T)) := hcardSyl.symm
        _ = Nat.card Ω := h.card_sylow_eq_card
        _ = Nat.card T + 1 := hreg.symm
    omega
  have hTeq : T.subgroupOf (twoTransY X T) =
      (h.tSub α).subgroupOf (twoTransY X T) := by
    rw [h.tSub_alpha_eq]
  have hle : T.subgroupOf (twoTransY X T) ≤
      (h.sylowAt α : Subgroup ↥(twoTransY X T)) := by
    rw [hTeq]
    exact h.tSub_subgroupOf_le_sylowAt α
  have hcardTY : Nat.card (T.subgroupOf (twoTransY X T)) = Nat.card T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (le_twoTransY (X := X) (T := T))).toEquiv
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcardQ, hcardTY])).symm

end Certificates

private noncomputable def normalizerT (h : TwoTransHyp X T α) :
    Subgroup (Equiv.Perm Ω) :=
  Subgroup.normalizer (T : Set (Equiv.Perm Ω)) ⊓ twoTransY X T

private lemma normalizerT_eq_map (h : TwoTransHyp X T α) :
    normalizerT h =
      (Subgroup.normalizer
        ((T.subgroupOf (twoTransY X T)) : Set ↥(twoTransY X T))).map
        (twoTransY X T).subtype := by
  change Subgroup.normalizer (T : Set (Equiv.Perm Ω)) ⊓ twoTransY X T =
    (Subgroup.normalizer
      ((T.subgroupOf (twoTransY X T)) : Set ↥(twoTransY X T))).map
      (twoTransY X T).subtype
  rw [← Subgroup.subgroupOf_normalizer_eq (le_twoTransY (X := X) (T := T)),
    Subgroup.subgroupOf_map_subtype]

private lemma mem_normalizer_T (h : TwoTransHyp X T α) {p : Equiv.Perm Ω}
    (hpX : p ∈ X) (hpα : p α = α) :
    p ∈ Subgroup.normalizer (T : Set (Equiv.Perm Ω)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro t
  constructor
  · intro ht
    exact h.normal p hpX hpα t ht
  · intro ht
    have hp'X : p⁻¹ ∈ X := X.inv_mem hpX
    have hp'α : p⁻¹ α = α := by
      have := congrArg (⇑p⁻¹) hpα
      simpa using this.symm
    have hmem := h.normal p⁻¹ hp'X hp'α (p * t * p⁻¹) ht
    simpa [mul_assoc] using hmem

private lemma le_normalizer_twoTransY {P : Subgroup (Equiv.Perm Ω)} (hPX : P ≤ X) :
    P ≤ Subgroup.normalizer (twoTransY X T : Set (Equiv.Perm Ω)) := by
  intro p hp
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact conj_mem_twoTransY (hPX hp) hy
  · intro hy
    have hp'X : p⁻¹ ∈ X := X.inv_mem (hPX hp)
    have hmem := conj_mem_twoTransY hp'X hy
    simpa [mul_assoc] using hmem

private lemma conj_mem_normalizer_T (h : TwoTransHyp X T α) {p a : Equiv.Perm Ω}
    (hpX : p ∈ X) (hpα : p α = α)
    (ha : a ∈ Subgroup.normalizer (T : Set (Equiv.Perm Ω))) :
    p * a * p⁻¹ ∈ Subgroup.normalizer (T : Set (Equiv.Perm Ω)) := by
  have hpN : p ∈ Subgroup.normalizer (T : Set (Equiv.Perm Ω)) :=
    mem_normalizer_T h hpX hpα
  have hp'X : p⁻¹ ∈ X := X.inv_mem hpX
  have hp'α : p⁻¹ α = α := by
    have := congrArg (⇑p⁻¹) hpα
    simpa using this.symm
  have hp'N : p⁻¹ ∈ Subgroup.normalizer (T : Set (Equiv.Perm Ω)) :=
    mem_normalizer_T h hp'X hp'α
  rw [Subgroup.mem_normalizer_iff] at ha ⊢
  intro t
  constructor
  · intro ht
    have hpt : p⁻¹ * t * p ∈ T := by
      have := (Subgroup.mem_normalizer_iff.mp hpN (p⁻¹ * t * p)).mpr ?_
      · exact this
      · simpa [mul_assoc] using ht
    have hat : a * (p⁻¹ * t * p) * a⁻¹ ∈ T := (ha _).mp hpt
    have hpat : p * (a * (p⁻¹ * t * p) * a⁻¹) * p⁻¹ ∈ T :=
      (Subgroup.mem_normalizer_iff.mp hpN _).mp hat
    convert hpat using 1
    group
  · intro ht
    have h1 : p⁻¹ * ((p * a * p⁻¹) * t * (p * a * p⁻¹)⁻¹) * p ∈ T :=
      (Subgroup.mem_normalizer_iff.mp hp'N _).mp ht
    have h1' : a * (p⁻¹ * t * p) * a⁻¹ ∈ T := by
      convert h1 using 1
      group
    have h2 : p⁻¹ * t * p ∈ T := (ha _).mpr h1'
    exact (Subgroup.mem_normalizer_iff.mp hp'N t).mpr h2

private lemma le_normalizer_normalizer_T (h : TwoTransHyp X T α)
    {P : Subgroup (Equiv.Perm Ω)} (hPX : P ≤ X)
    (hPα : ∀ p ∈ P, p α = α) :
    P ≤ Subgroup.normalizer
      (Subgroup.normalizer (T : Set (Equiv.Perm Ω)) : Set (Equiv.Perm Ω)) := by
  intro p hp
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    exact conj_mem_normalizer_T h (hPX hp) (hPα p hp) ha
  · intro ha
    have hp'X : p⁻¹ ∈ X := X.inv_mem (hPX hp)
    have hp'α : p⁻¹ α = α := by
      have := congrArg (⇑p⁻¹) (hPα p hp)
      simpa using this.symm
    have hmem := conj_mem_normalizer_T h hp'X hp'α ha
    simpa [mul_assoc] using hmem

private lemma le_normalizer_normalizerT (h : TwoTransHyp X T α)
    {P : Subgroup (Equiv.Perm Ω)} (hPX : P ≤ X)
    (hPα : ∀ p ∈ P, p α = α) :
    P ≤ Subgroup.normalizer (normalizerT h : Set (Equiv.Perm Ω)) := by
  intro p hp
  have h1 : p ∈ Subgroup.normalizer
      (Subgroup.normalizer (T : Set (Equiv.Perm Ω)) : Set (Equiv.Perm Ω)) :=
    le_normalizer_normalizer_T h hPX hPα hp
  have h2 : p ∈ Subgroup.normalizer (twoTransY X T : Set (Equiv.Perm Ω)) :=
    le_normalizer_twoTransY hPX hp
  exact Subgroup.inf_normalizer_le_normalizer_inf (Subgroup.mem_inf.mpr ⟨h1, h2⟩)

end TwoTransHyp

namespace TwoTransHyp


private lemma normalizerT_transitive (h : TwoTransHyp X T α)
    (hreg : Nat.card T + 1 = Nat.card Ω) {x y : Equiv.Perm Ω}
    (hx : x ∈ T) (hx1 : x ≠ 1) (hy : y ∈ T) (hy1 : y ≠ 1) :
    ∃ a ∈ normalizerT h, a * x * a⁻¹ = y := by
  let Y := twoTransY X T
  have hY : CFSG.BenderSuzuki.IsBenderGroup Y := h.isBenderGroup
  have hTY : (h.sylowAt α : Subgroup Y) = T.subgroupOf Y :=
    sylowAt_alpha_eq_tSub h hreg
  let Q : Sylow 2 Y := h.sylowAt α
  have hxY : x ∈ Y := le_twoTransY hx
  have hyY : y ∈ Y := le_twoTransY hy
  have hxQ : (⟨x, hxY⟩ : Y) ∈ (Q : Subgroup Y) := by
    rw [show (Q : Subgroup Y) = T.subgroupOf Y from hTY]
    exact hx
  have hyQ : (⟨y, hyY⟩ : Y) ∈ (Q : Subgroup Y) := by
    rw [show (Q : Subgroup Y) = T.subgroupOf Y from hTY]
    exact hy
  have hxcen : (⟨x, hxY⟩ : Y) ∈ (Q : Subgroup Y) ∧
      ∀ q ∈ (Q : Subgroup Y), Commute q ⟨x, hxY⟩ := by
    refine ⟨hxQ, ?_⟩
    intro q hq
    have hqT : (q : Equiv.Perm Ω) ∈ T := by
      rw [show (Q : Subgroup Y) = T.subgroupOf Y from hTY] at hq
      exact hq
    have hc : Commute (q : Equiv.Perm Ω) x := by
      have h := h.elemAb.1.is_comm.comm (⟨(q : Equiv.Perm Ω), hqT⟩ : T) ⟨x, hx⟩
      exact congrArg Subtype.val h
    exact Subtype.ext hc.eq
  have hycen : (⟨y, hyY⟩ : Y) ∈ (Q : Subgroup Y) ∧
      ∀ q ∈ (Q : Subgroup Y), Commute q ⟨y, hyY⟩ := by
    refine ⟨hyQ, ?_⟩
    intro q hq
    have hqT : (q : Equiv.Perm Ω) ∈ T := by
      rw [show (Q : Subgroup Y) = T.subgroupOf Y from hTY] at hq
      exact hq
    have hc : Commute (q : Equiv.Perm Ω) y := by
      have h := h.elemAb.1.is_comm.comm (⟨(q : Equiv.Perm Ω), hqT⟩ : T) ⟨y, hy⟩
      exact congrArg Subtype.val h
    exact Subtype.ext hc.eq
  have hx1' : (⟨x, hxY⟩ : Y) ≠ 1 := fun h1 => hx1 (congrArg Subtype.val h1)
  have hy1' : (⟨y, hyY⟩ : Y) ≠ 1 := fun h1 => hy1 (congrArg Subtype.val h1)
  obtain ⟨aY, haN, ha⟩ :=
    CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.exists_normalizer_conj hY Q hxcen hx1' hycen hy1'
  have haN' : aY ∈ Subgroup.normalizer ((T.subgroupOf Y) : Set Y) := by
    have hQ : (Q : Set Y) = (T.subgroupOf Y : Set Y) := by
      exact congrArg (fun S : Subgroup Y => (S : Set Y)) hTY
    rw [hQ] at haN
    exact haN
  refine ⟨(aY : Equiv.Perm Ω), ?_, congrArg Subtype.val ha⟩
  rw [normalizerT_eq_map h]
  exact Subgroup.mem_map.mpr ⟨aY, haN', rfl⟩

private lemma commutator_normalizerT_le (h : TwoTransHyp X T α)
    (hreg : Nat.card T + 1 = Nat.card Ω) :
    ⁅normalizerT h, normalizerT h⁆ ≤ T := by
  let Y := twoTransY X T
  have hY : CFSG.BenderSuzuki.IsBenderGroup Y := h.isBenderGroup
  have hTY : (h.sylowAt α : Subgroup Y) = T.subgroupOf Y :=
    sylowAt_alpha_eq_tSub h hreg
  let Q : Subgroup Y := h.sylowAt α
  let AY : Subgroup Y := Subgroup.normalizer (Q : Set Y)
  have hAeq : normalizerT h = AY.map Y.subtype := by
    rw [normalizerT_eq_map h]
    congr 1
    change Subgroup.normalizer (T.subgroupOf Y) = Subgroup.normalizer (Q : Set Y)
    rw [← hTY]
  obtain ⟨q, k, hB, -⟩ :=
    CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.exists_fusionBenderBorel hY
  obtain ⟨D, hDcyc, -, -, hDsup⟩ := (hB (h.sylowAt α)).2.1
  have hQAY : Q ≤ AY := Subgroup.le_normalizer
  have hDAY : D ≤ AY := by
    have h : D ≤ Q ⊔ D := le_sup_right
    have h' : Q ⊔ D = AY := hDsup
    rwa [h'] at h
  haveI : (Q.subgroupOf AY).Normal := Subgroup.normal_in_normalizer
  have hsup : Q.subgroupOf AY ⊔ D.subgroupOf AY = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hQAY hDAY, hDsup, Subgroup.subgroupOf_self]
  haveI : IsCyclic D := hDcyc
  haveI : IsCyclic (D.subgroupOf AY) :=
    (MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hDAY)).mpr hDcyc
  haveI : IsMulCommutative (D.subgroupOf AY) := IsCyclic.isMulCommutative
  have hcommA : _root_.commutator AY ≤ Q.subgroupOf AY :=
    Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup
      (inferInstance : IsMulCommutative (D.subgroupOf AY))
  have hcommY : ⁅AY, AY⁆ ≤ Q := by
    have hmap : ⁅AY, AY⁆ = (_root_.commutator AY).map AY.subtype := by
      have htop : _root_.commutator AY =
          ⁅(⊤ : Subgroup AY), (⊤ : Subgroup AY)⁆ := rfl
      rw [htop, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
    rw [hmap]
    calc (_root_.commutator AY).map AY.subtype ≤ (Q.subgroupOf AY).map AY.subtype :=
          Subgroup.map_mono hcommA
      _ = Q ⊓ AY := Subgroup.subgroupOf_map_subtype _ _
      _ = Q := inf_eq_left.mpr hQAY
  calc ⁅normalizerT h, normalizerT h⁆ = (⁅AY, AY⁆).map Y.subtype := by
        rw [hAeq, Subgroup.map_commutator]
    _ ≤ Q.map Y.subtype := Subgroup.map_mono hcommY
    _ = T := by
        change (h.sylowAt α : Subgroup Y).map Y.subtype = T
        rw [hTY, Subgroup.subgroupOf_map_subtype]
        exact inf_of_le_left (le_twoTransY (X := X) (T := T))

private lemma normalizerT_irreducible (h : TwoTransHyp X T α)
    (hreg : Nat.card T + 1 = Nat.card Ω) :
    ∀ W : Subgroup (Equiv.Perm Ω), W ≤ T →
      normalizerT h ≤ Subgroup.normalizer (W : Set (Equiv.Perm Ω)) →
      W = ⊥ ∨ W = T := by
  intro W hWT hAW
  by_cases hW : W = ⊥
  · exact Or.inl hW
  · right
    apply le_antisymm hWT
    intro t ht
    by_cases ht1 : t = 1
    · rw [ht1]
      exact W.one_mem
    · obtain ⟨w, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hW
      have hwT : (w : Equiv.Perm Ω) ∈ T := hWT w.2
      have hw1' : (w : Equiv.Perm Ω) ≠ 1 := fun h1 => hw1 (Subtype.ext h1)
      obtain ⟨a, haA, ha⟩ := normalizerT_transitive h hreg hwT hw1' ht ht1
      have haW : a * (w : Equiv.Perm Ω) * a⁻¹ ∈ W :=
        (Subgroup.mem_normalizer_iff.mp (hAW haA) w.1).mp w.2
      rwa [ha] at haW

theorem exists_mod_centralizer (h : TwoTransHyp X T α)
    (hreg : Nat.card T + 1 = Nat.card Ω) {P : Subgroup (Equiv.Perm Ω)} (hPX : P ≤ X)
    (hPα : ∀ p ∈ P, p α = α) (hP : IsPGroup 2 P) :
    ∃ x ∈ P, ∀ y ∈ P, ∃ k : ℕ,
      y⁻¹ * x ^ k ∈ Subgroup.centralizer (T : Set (Equiv.Perm Ω)) := by
  haveI : IsMulCommutative T := h.elemAb.1
  have hTne : T ≠ ⊥ := by
    have h4 : 1 < Nat.card T := lt_of_lt_of_le (by norm_num) h.four_le
    exact (Subgroup.one_lt_card_iff_ne_bot T).mp h4
  have hAcomm : ⁅normalizerT h, normalizerT h⁆ ≤
      Subgroup.centralizer (T : Set (Equiv.Perm Ω)) :=
    (commutator_normalizerT_le h hreg).trans (Subgroup.le_centralizer T)
  have hAnorm : normalizerT h ≤ Subgroup.normalizer (T : Set (Equiv.Perm Ω)) := by
    change Subgroup.normalizer (T : Set (Equiv.Perm Ω)) ⊓ twoTransY X T ≤ _
    exact inf_le_left
  have hPnormT : P ≤ Subgroup.normalizer (T : Set (Equiv.Perm Ω)) :=
    fun p hp => mem_normalizer_T h (hPX hp) (hPα p hp)
  have hPnormA : P ≤ Subgroup.normalizer (normalizerT h : Set (Equiv.Perm Ω)) :=
    le_normalizer_normalizerT h hPX hPα
  exact CFSG.GroupTheory.isCyclic_mod_centralizer_of_isPGroup_normalizer
    (p := 2) h.elemAb hTne hAnorm hAcomm
    (normalizerT_irreducible h hreg) hP hPnormT hPnormA

end TwoTransHyp

end CFSG.Timmesfeld.Bridge.OddRoot
