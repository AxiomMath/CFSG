module

public import CFSG.RankThree.PartTwo.Sec16.Item168StepsProofEmpty
public import CFSG.RankThree.PartTwo.Sec16.Item166Res3ProofEmpty
import CFSG.RankThree.PartTwo.Sec16.Item166Res3ProofComm
import CFSG.RankThree.PartTwo.Sec16.Item1617StepsProofTools
import CFSG.RankThree.PartTwo.Sec16.Item1617StepsProofCore
import CFSG.RankThree.PartTwo.Sec16.Item16Tail19
import CFSG.RankThree.PartTwo.Sec16.Item16Tail
import CFSG.Goldschmidt.Steps.G310Basic

public section

namespace CFSG.RankThree.PartTwo.Sec16

@[expose] def KS168NoE4 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), 2 < n → ¬ 3 ∣ n → Sec4.IsoLThreePi X 2 n →
    ∀ D : Subgroup X, CFSG.Assembly.IsElemAbelian 3 D → Nat.card D = 9 →
      ∀ α β : MulAut X, (∀ d ∈ D, α d = d) → (∀ d ∈ D, β d = d) → α ^ 2 = 1 → β ^ 2 = 1 →
        α * β = β * α → α ≠ 1 → β ≠ 1 → α = β

end CFSG.RankThree.PartTwo.Sec16

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec16
  CFSG.RankThree.PartTwo.Late CFSG.RankThree.LocalRank CFSG.GH74.GLS

namespace Proof168Res5

open Sec16.Proof165

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G}

theorem exists_involution {P : Subgroup G} (hP : IsPGroup 2 P) (hP1 : P ≠ ⊥) :
    ∃ t ∈ P, t ≠ 1 ∧ t ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hP1 (Subgroup.eq_bot_of_card_eq P (by rw [hk, pow_zero]))
  have h2 : 2 ∣ Nat.card P := by
    rw [hk]
    exact dvd_pow_self 2 hk0
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥P) 2 h2
  refine ⟨x, x.2, fun h1 => ?_, ?_⟩
  · have : x = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hx
    omega
  · have := pow_orderOf_eq_one x
    rw [hx] at this
    exact congrArg Subtype.val this

omit [Finite G] in
theorem le_of_fusionIsSylowIn {I T P : Subgroup G} (hT : CFSG.Open.fusionIsSylowIn 2 T I)
    (hP2 : IsPGroup 2 P) (hPI : P ≤ I) (hIP : I ≤ Subgroup.normalizer (P : Set G)) : P ≤ T := by
  have hsup : IsPGroup 2 (P ⊔ T : Subgroup G) :=
    hP2.to_sup_of_normal_left' hT.2.1 (hT.1.trans hIP)
  have heq := hT.2.2 (P ⊔ T) (sup_le hPI hT.1) hsup le_sup_right
  exact heq ▸ le_sup_left

omit [Finite G] in
theorem conj_eq_of_unique {T P : Subgroup G} (huniq : ∀ s ∈ T, s ≠ 1 → s ^ 2 = 1 → ∀ s' ∈ T,
      s' ≠ 1 → s' ^ 2 = 1 → s = s') {t : G} (htP : t ∈ P) (ht1 : t ≠ 1) (ht2 : t ^ 2 = 1)
    (hPT : P ≤ T) {g : G} (hg : g ∈ Subgroup.normalizer (P : Set G)) : g * t * g⁻¹ = t := by
  have hmem : g * t * g⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hg t).mp htP
  refine huniq _ (hPT hmem) ?_ ?_ t (hPT htP) ht1 ht2
  · intro h
    apply ht1
    have : t = g⁻¹ * (g * t * g⁻¹) * g := by group
    rw [this, h]
    group
  · rw [sq, show g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ by group, ← sq, ht2]
    group

theorem eq_of_involutions (h : Empty168 G A c L) (h138 : Item138N) (h1612 : Step1612)
    (hK : KS168NoE4) {T : Subgroup G} (hT2 : IsPGroup 2 T)
    (hTA : T ≤ Subgroup.centralizer (A : Set G)) :
    ∀ t₁ ∈ T, t₁ ≠ 1 → t₁ ^ 2 = 1 → ∀ t₂ ∈ T, t₂ ≠ 1 → t₂ ^ 2 = 1 → t₁ = t₂ := by
  obtain ⟨hR, h0, -, n, hn2, hiso, hprod⟩ := h
  have hctx : Ctx169 G A c L := ⟨hR, h0⟩
  have hz3 : IsZ3LThreeTwo A c L n := ⟨by omega, hiso, hprod⟩
  have hn3 : ¬ 3 ∣ n := Proof1617.not_three_dvd_of_isZ3 hctx h138 hz3
  have h34 := Proof166Res3.isEmpty_l34_of_two_lt hiso hn2
  obtain ⟨hLs, hnoT⟩ := Proof1619.simple_of_steps hctx (h1612 G A c L hctx) h34 hprod
  have hXL : Sec4.IsoLThreePi ↥L 2 n := Proof1617.isoLThreePi_of_isSimpleGroup hLs hz3.1 hiso
  obtain ⟨-, h9, -⟩ := Proof1617.facts_of_isZ3 hctx hz3
  have hCN := Proof1617.centralizer_le_normalizer_L hctx hz3
  have hcA : c ∈ A := hR.mem_A
  have hTN : ∀ t ∈ T, t ∈ Subgroup.normalizer (L : Set G) := fun t ht =>
    hCN (Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (hTA ht) c hcA).symm)
  have hCT : T ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
    refine hnoT _ ⟨inf_le_right, (isPiSubgroup_piOf_iff Nat.prime_two _).mpr
      (hT2.to_le inf_le_left), ?_⟩
    have hAT : A ≤ Subgroup.centralizer (T : Set G) := Subgroup.le_centralizer_iff.mp hTA
    exact (hAT.trans (Subgroup.centralizer_le inf_le_left)).trans
      (Subgroup.centralizer_le_normalizer _)
  set ρ := L.normalizerMonoidHom with hρ
  have hρapp : ∀ (g : G) (hg : g ∈ Subgroup.normalizer (L : Set G)) (l : ↥L),
      ((ρ ⟨g, hg⟩ l : ↥L) : G) = g * l * g⁻¹ := fun g hg l => rfl
  set D : Subgroup ↥L := (A ⊓ L).subgroupOf L with hD
  have hDab : CFSG.Assembly.IsElemAbelian 3 D :=
    Proof1617.isElemAbelian_subgroupOf
      (Sec16.Proof169.isElemAbelian_of_le hR.isElemAbelian inf_le_left) L
  have hD9 : Nat.card D = 9 := by rw [hD, Proof1617.card_subgroupOf_of_le inf_le_right, h9]
  have hfix : ∀ (t : G) (ht : t ∈ T) (d : ↥L), d ∈ D → ρ ⟨t, hTN t ht⟩ d = d := by
    intro t ht d hd
    apply Subtype.ext
    rw [hρapp]
    have hdA : (d : G) ∈ A := (Subgroup.mem_subgroupOf.mp hd).1
    rw [← Subgroup.mem_centralizer_iff.mp (hTA ht) (d : G) hdA, mul_inv_cancel_right]
  have htriv : ∀ (t : G) (ht : t ∈ T), ρ ⟨t, hTN t ht⟩ = 1 → t = 1 := by
    intro t ht h1
    have htC : t ∈ Subgroup.centralizer (L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have h2 := congrArg (fun σ : MulAut ↥L => ((σ ⟨l, hl⟩ : ↥L) : G)) h1
      simp only [hρapp, MulAut.one_apply] at h2
      calc l * t = t * l * t⁻¹ * t := by rw [h2]
        _ = t * l := by group
    have : t ∈ T ⊓ Subgroup.centralizer (L : Set G) := ⟨ht, htC⟩
    rwa [hCT, Subgroup.mem_bot] at this
  intro t₁ h₁ h₁1 h₁2 t₂ h₂ h₂1 h₂2
  set α := ρ ⟨t₁, hTN t₁ h₁⟩ with hα
  set β := ρ ⟨t₂, hTN t₂ h₂⟩ with hβ
  have hα2 : α ^ 2 = 1 := by
    rw [hα, ← map_pow]
    have : (⟨t₁, hTN t₁ h₁⟩ : Subgroup.normalizer (L : Set G)) ^ 2 = 1 := Subtype.ext h₁2
    rw [this, map_one]
  have hβ2 : β ^ 2 = 1 := by
    rw [hβ, ← map_pow]
    have : (⟨t₂, hTN t₂ h₂⟩ : Subgroup.normalizer (L : Set G)) ^ 2 = 1 := Subtype.ext h₂2
    rw [this, map_one]
  have hα1 : α ≠ 1 := fun h1 => h₁1 (htriv t₁ h₁ h1)
  have hβ1 : β ≠ 1 := fun h1 => h₂1 (htriv t₂ h₂ h1)
  set w := t₁ * t₂ * t₁⁻¹ * t₂⁻¹ with hw
  have hwT : w ∈ T := T.mul_mem (T.mul_mem (T.mul_mem h₁ h₂) (T.inv_mem h₁)) (T.inv_mem h₂)
  have hγ : α * β * α⁻¹ * β⁻¹ = ρ ⟨w, hTN w hwT⟩ := by
    rw [hα, hβ, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    rfl
  have hcop : Nat.Coprime 3 (orderOf (α * β * α⁻¹ * β⁻¹)) := by
    rw [hγ]
    have h1 : orderOf (ρ ⟨w, hTN w hwT⟩) ∣ orderOf w := by
      have := orderOf_map_dvd ρ (⟨w, hTN w hwT⟩ : Subgroup.normalizer (L : Set G))
      rwa [Subgroup.orderOf_mk] at this
    obtain ⟨k, hk⟩ := hT2 ⟨w, hwT⟩
    have h2 : orderOf w ∣ 2 ^ k := by
      rw [← Subgroup.orderOf_mk (ha := hwT)]
      exact orderOf_dvd_of_pow_eq_one hk
    exact Nat.Coprime.coprime_dvd_right (h1.trans h2)
      (Nat.Coprime.pow_right k (by norm_num))
  have hcomm1 := ks167OutComm ↥L n (by omega) hn3 hXL D hDab hD9 α β (hfix t₁ h₁)
    (hfix t₂ h₂) hcop
  have hcomm : α * β = β * α := by
    have := congrArg (· * β * α) hcomm1
    simpa [mul_assoc] using this
  have hαβ := hK ↥L n hn2 hn3 hXL D hDab hD9 α β (hfix t₁ h₁) (hfix t₂ h₂) hα2 hβ2 hcomm hα1 hβ1
  have hmem : t₁ * t₂⁻¹ ∈ T := T.mul_mem h₁ (T.inv_mem h₂)
  have hρ1 : ρ ⟨t₁ * t₂⁻¹, hTN _ hmem⟩ = 1 := by
    have : (⟨t₁ * t₂⁻¹, hTN _ hmem⟩ : Subgroup.normalizer (L : Set G)) =
        ⟨t₁, hTN t₁ h₁⟩ * (⟨t₂, hTN t₂ h₂⟩)⁻¹ := rfl
    rw [this, map_mul, map_inv, ← hα, ← hβ, hαβ, mul_inv_cancel]
  have := htriv _ hmem hρ1
  rwa [mul_inv_eq_one] at this

theorem oneZero168_of_noE4 (h : Empty168 G A c L) (h138 : Item138N) (h1612 : Step1612)
    (h146 : Item146 A (lB A)) (hK : KS168NoE4) :
    ∀ Y ∈ scriptY3 A (lB A), ∀ T : Subgroup G, CFSG.Open.fusionIsSylowIn 2 T Y →
      A ≤ Subgroup.normalizer (T : Set G) →
      ∀ I₁ ∈ scriptY3Star A (lB A), ∀ I₂ ∈ scriptY3Star A (lB A), Y ≤ I₁ → Y ≤ I₂ →
        CFSG.Open.fusionIsSylowIn 2 T I₁ → deltaZero A (lB A) I₁ = ⊥ → I₁ = I₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro Y _ T hT hAT I₁ hI₁ I₂ hI₂ _ hYI₂ hT₁ hΔ
  have hR : Sec15R G A c L := h.1
  have hA : IsE27 A := hR.toSec14Std.isE27
  have hA3 : IsPGroup 3 A := hA.isPGroup
  have h3s := h.2.2.1
  have hI₁3 : ¬ 3 ∣ Nat.card I₁ :=
    not_three_dvd_of_mem_scriptY1 (h3s ▸ hI₁.prop : I₁ ∈ scriptYs A (lB A)).1
  have hI₂3 : ¬ 3 ∣ Nat.card I₂ :=
    not_three_dvd_of_mem_scriptY1 (h3s ▸ hI₂.prop : I₂ ∈ scriptYs A (lB A)).1
  have hI₁Q : I₁ ∈ scriptQ A (lB A) :=
    mem_scriptQ_of_three hA h146 hI₁.prop.2 hI₁.prop.1.1.2 hI₁3
  have hI₂Q : I₂ ∈ scriptQ A (lB A) :=
    mem_scriptQ_of_three hA h146 hI₂.prop.2 hI₂.prop.1.1.2 hI₂3
  have hAI₁ : A ≤ Subgroup.normalizer (I₁ : Set G) := hI₁.prop.1.1.2
  have hI₁A : I₁ ≤ Subgroup.centralizer (A : Set G) := by
    have hcomm : ⁅I₁, A⁆ ≤ I₁ := Subgroup.le_normalizer_iff_commutator_le_left.mp hAI₁
    have hAcomm : A ≤ Subgroup.normalizer ((⁅I₁, A⁆ : Subgroup G) : Set G) := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.normalizer_commutator_ge_left A I₁
    have hle : ⁅I₁, A⁆ ≤ deltaZero A (lB A) I₁ :=
      le_deltaZero ⟨mem_scriptQ_of_le hI₁Q hcomm hAcomm,
        (CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent 3 Nat.prime_three
          A I₁ hA3 hI₁3 hAI₁).symm⟩ hcomm
    rw [hΔ] at hle
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp (le_bot_iff.mp hle)
  have hT2 : IsPGroup 2 T := hT₁.2.1
  have hTA : T ≤ Subgroup.centralizer (A : Set G) := hT₁.1.trans hI₁A
  have huniq := eq_of_involutions h h138 h1612 hK hT2 hTA
  set P₁ := CFSG.Open.pCoreOf 2 I₁ with hP₁
  have hP₁2 : IsPGroup 2 P₁ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 I₁
  have hP₁I : P₁ ≤ I₁ := CFSG.LieType.BorelTits.pCoreOf_le 2 I₁
  have hI₁P : I₁ ≤ Subgroup.normalizer (P₁ : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 I₁
  have hP₁T : P₁ ≤ T := le_of_fusionIsSylowIn hT₁ hP₁2 hP₁I hI₁P
  obtain ⟨t, htP, ht1, ht2⟩ := exists_involution hP₁2 hI₁.prop.1.2
  have htT : t ∈ T := hP₁T htP
  have huniq' : ∀ s ∈ T, s ≠ 1 → s ^ 2 = 1 → ∀ s' ∈ T, s' ≠ 1 → s' ^ 2 = 1 → s = s' :=
    fun s hs hs1 hs2 s' hs' hs'1 hs'2 => huniq s hs hs1 hs2 s' hs' hs'1 hs'2
  set C := Subgroup.zpowers t with hCdef
  have hfixN : ∀ g : G, g * t * g⁻¹ = t → g ∈ Subgroup.normalizer (C : Set G) := by
    intro g hg
    refine centralizer_singleton_le_normalizer_zpowers t ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * t = g * t * g⁻¹ * g := by group
      _ = t * g := by rw [hg]
  have hI₁C : I₁ ≤ Subgroup.normalizer (C : Set G) := fun g hg =>
    hfixN g (conj_eq_of_unique huniq' htP ht1 ht2 hP₁T (hI₁P hg))
  have hNTC : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (C : Set G) := fun g hg =>
    hfixN g (conj_eq_of_unique huniq' htT ht1 ht2 le_rfl hg)
  have hC1 : C ≠ ⊥ := by
    intro h0
    apply ht1
    have : t ∈ C := Subgroup.mem_zpowers t
    rwa [h0, Subgroup.mem_bot] at this
  have hCT : C ≤ T := Subgroup.zpowers_le.mpr htT
  have hC2 : IsPGroup 2 C := hT2.to_le hCT
  have hAC : A ≤ Subgroup.normalizer (C : Set G) := by
    intro a ha
    refine hfixN a ?_
    rw [Subgroup.mem_centralizer_iff.mp (hTA htT) a ha, mul_inv_cancel_right]
  have hCQ : C ∈ scriptQ A (lB A) := mem_scriptQ_of_le hI₁Q (hCT.trans hT₁.1) hAC
  have hD3 := delta_normalizer_mem_scriptY3 hR.isSimpleGroup hR.nonabelian hC1 hC2 hCQ
  have hDI₁ : delta A (lB A) (Subgroup.normalizer (C : Set G)) ≤ I₁ :=
    hI₁.2 hD3 (le_delta hI₁Q hI₁C)
  have hJ : I₂ ⊓ Subgroup.normalizer (T : Set G) ≤ I₁ := by
    have hAJ : A ≤ Subgroup.normalizer ((I₂ ⊓ Subgroup.normalizer (T : Set G) : Subgroup G) :
        Set G) := le_normalizer_inf hI₂.prop.1.1.2 (hAT.trans Subgroup.le_normalizer)
    exact (le_delta (mem_scriptQ_of_le hI₂Q inf_le_left hAJ) (inf_le_right.trans hNTC)).trans hDI₁
  have hT₂ : CFSG.Open.fusionIsSylowIn 2 T I₂ := by
    refine ⟨hT.1.trans hYI₂, hT2, fun P hPI hP2 hTP => ?_⟩
    by_contra hne
    have hlt : T < P ⊓ Subgroup.normalizer (T : Set G) :=
      CFSG.Goldschmidt.G310.lt_inf_normalizer hP2 hTP (Ne.symm hne)
    have heq := hT₁.2.2 (P ⊓ Subgroup.normalizer (T : Set G))
      ((inf_le_inf_right _ hPI).trans hJ) (hP2.to_le inf_le_left) hlt.le
    exact hlt.ne heq.symm
  set P₂ := CFSG.Open.pCoreOf 2 I₂ with hP₂
  have hP₂2 : IsPGroup 2 P₂ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 I₂
  have hP₂I : P₂ ≤ I₂ := CFSG.LieType.BorelTits.pCoreOf_le 2 I₂
  have hI₂P : I₂ ≤ Subgroup.normalizer (P₂ : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 I₂
  have hP₂T : P₂ ≤ T := le_of_fusionIsSylowIn hT₂ hP₂2 hP₂I hI₂P
  obtain ⟨s, hsP, hs1, hs2⟩ := exists_involution hP₂2 hI₂.prop.1.2
  have hst : s = t := huniq' s (hP₂T hsP) hs1 hs2 t htT ht1 ht2
  rw [hst] at hsP
  have hI₂C : I₂ ≤ Subgroup.normalizer (C : Set G) := fun g hg =>
    hfixN g (conj_eq_of_unique huniq' hsP ht1 ht2 hP₂T (hI₂P hg))
  have hI₂I₁ : I₂ ≤ I₁ := (le_delta hI₂Q hI₂C).trans hDI₁
  exact le_antisymm (hI₂.2 hI₁.prop hI₂I₁) hI₂I₁

end Proof168Res5

theorem step168OneZero_of_noE4 (h138 : Item138N) (h1612 : Step1612) (h146 : Item146S14)
    (hK : KS168NoE4) :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Empty168 G A c L → ∀ Y ∈ scriptY3 A (lB A), ∀ T : Subgroup G,
        CFSG.Open.fusionIsSylowIn 2 T Y → A ≤ Subgroup.normalizer (T : Set G) →
        ∀ I₁ ∈ scriptY3Star A (lB A), ∀ I₂ ∈ scriptY3Star A (lB A), Y ≤ I₁ → Y ≤ I₂ →
          CFSG.Open.fusionIsSylowIn 2 T I₁ → deltaZero A (lB A) I₁ = ⊥ → I₁ = I₂ :=
  fun G _ _ A c L h =>
    Proof168Res5.oneZero168_of_noE4 h h138 h1612 (h146 G A c L h.1.toSec14Std) hK

end CFSG.RankThree.PartTwo.Sec17
