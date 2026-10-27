module

public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsSU
public import CFSG.LocalAnalysis.StandardType.GGPRankBoundsBasic
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryDiagonalOuterOrder
public import CFSG.LieType.Universal.Unitary.Clause0
public import CFSG.Open.StatedAPI
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField

public section

namespace CFSG.StandardType

namespace PRankBounds

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

section Model

theorem card_outer_psu5 {X : Type} [Group X] (hmod : StatedClassicalModel X .PSU 5 2 1) :
    Nat.card (Outer X) = 2 := by
  obtain ⟨⟨hℓ, hm, hn3, hne⟩, K, _, _, hK, ⟨e⟩⟩ := hmod
  have hU : UnitaryFieldData 2 1 K := ⟨hℓ, hm, by rw [hK]; norm_num⟩
  have hq : ¬(5 = 3 ∧ 2 ^ 1 = 2) := fun ⟨h1, _⟩ => absurd h1 (by norm_num)
  have h1 := (unitary_full_diagonal_outer_order hU (n := 5) (by norm_num) hq).2.2.2.2.1
  have e' : X ≃* unitaryPSU hU 5 := e.trans (unitaryPSUEquiv hU (by norm_num)).symm
  rw [Nat.card_congr (equivalence e').toEquiv, h1]
  norm_num

theorem statedClassicalModel_of_mulEquiv_psu {X Y : Type} [Group X] [Group Y] {n p f : ℕ}
    (e : X ≃* Y) (h : StatedClassicalModel Y .PSU n p f) : StatedClassicalModel X .PSU n p f :=
  CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e.symm h

theorem statedClassicalModel_range_of_su5 {G : Type} [Group G]
    (ψ : CFSG.LieType.Universal.Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * 1)) 2 1) 5 →* G)
    (hker : ψ.ker ≤ Subgroup.center _)
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) :
    StatedClassicalModel ψ.range .PSU 5 2 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hadm : StatedLieAdmissible .PSU 5 2 1 := ⟨Nat.prime_two, le_rfl, by norm_num, by decide⟩
  have hF : Nat.card (GaloisField 2 (2 * 1)) = (2 ^ 1) ^ 2 := by
    rw [GaloisField.card 2 (2 * 1) (by norm_num)]
    norm_num
  have hmod := CFSG.LieType.Universal.Unitary.statedClassicalModel_center_quotient hadm hF
  have hkerEq : ψ.ker = Subgroup.center _ := by
    refine le_antisymm hker fun z hz => ?_
    have hzC : ψ z ∈ Subgroup.centralizer (ψ.range : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨k, rfl⟩
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz k]
    rw [hC, Subgroup.mem_bot] at hzC
    exact hzC
  refine statedClassicalModel_of_mulEquiv_psu ?_ hmod
  exact (QuotientGroup.quotientKerEquivRange ψ).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hkerEq)

end Model

@[expose] def GGUFiveTwoLocalInnerInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X], StatedClassicalModel X .PSU 5 2 1 →
    ∀ E T : Subgroup X, IsElemAbelian 3 E → 3 ^ 4 ≤ Nat.card E → T ≠ ⊥ → IsPGroup 2 T →
      E ≤ Subgroup.normalizer (T : Set X) → False

@[expose] def GGUFiveTwoOuterCentInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X], StatedClassicalModel X .PSU 5 2 1 →
    ∀ α : MulAut X, α ^ 2 = 1 → α ∉ inner X →
      ∀ E : Subgroup X, IsElemAbelian 3 E → (∀ e ∈ E, α e = e) → Nat.card E < 3 ^ 4

section Normalizer

variable {G : Type} [Group G]

theorem mem_normalizer_inf {T H : Subgroup G} {e : G}
    (hT : e ∈ Subgroup.normalizer (T : Set G)) (hH : e ∈ Subgroup.normalizer (H : Set G)) :
    e ∈ Subgroup.normalizer ((T ⊓ H : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have h1 := Subgroup.mem_normalizer_iff.mp hT x
  have h2 := Subgroup.mem_normalizer_iff.mp hH x
  simp only [Subgroup.mem_inf] at h1 h2 ⊢
  exact and_congr h1 h2

theorem not_twoLocalRankFour_of_psu5 [Finite G] (hI : GGUFiveTwoLocalInnerInput)
    (hO : GGUFiveTwoOuterCentInput) {H : Subgroup G}
    (hC : Subgroup.centralizer (H : Set G) = ⊥) (hmod : StatedClassicalModel H .PSU 5 2 1) :
    ¬ GGTwoLocalRankFour 3 (Subgroup.normalizer (H : Set G)) := by
  rintro ⟨E, T, hEM, hE, h81, hTM, hT1, hT2, hET⟩
  have hOut := card_outer_psu5 hmod
  have hEH : E ≤ H := by
    intro e he
    refine mem_of_normConj_mem_inner hC (m := ⟨e, hEM he⟩) ?_
    have h3 : normConj H ⟨e, hEM he⟩ ^ 3 = 1 := by
      rw [← map_pow]
      have : (⟨e, hEM he⟩ : Subgroup.normalizer (H : Set G)) ^ 3 = 1 :=
        Subtype.ext (by simpa using hE.2 e he)
      rw [this, map_one]
    have hq : (QuotientGroup.mk (normConj H ⟨e, hEM he⟩) : Outer H) = 1 := by
      have h1 : (QuotientGroup.mk (normConj H ⟨e, hEM he⟩) : Outer H) ^ 3 = 1 := by
        rw [← QuotientGroup.mk_pow, h3, QuotientGroup.mk_one]
      have h2 := orderOf_dvd_of_pow_eq_one h1
      have h4 : orderOf (QuotientGroup.mk (normConj H ⟨e, hEM he⟩) : Outer H) ∣ 2 :=
        hOut ▸ orderOf_dvd_natCard _
      exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (by norm_num) h2 h4)
    exact (QuotientGroup.eq_one_iff _).mp hq
  have hE' : IsElemAbelian 3 (E.subgroupOf H) := isElemAbelian_comap_of_inj H.subtype
    (Subgroup.subtype_injective H) hE
  have hcardE : Nat.card (E.subgroupOf H) = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEH).toEquiv
  by_cases hT0 : T ⊓ H = ⊥
  ·
    have hcomm : ∀ τ ∈ T, ∀ e ∈ E, e * τ * e⁻¹ = τ := by
      intro τ hτ e he
      set mτ : Subgroup.normalizer (H : Set G) := ⟨τ, hTM hτ⟩
      set me : Subgroup.normalizer (H : Set G) := ⟨e, hEM he⟩
      set c : Subgroup.normalizer (H : Set G) := mτ⁻¹ * (me * mτ * me⁻¹)
      have hcT : (c : G) ∈ T :=
        mul_mem (inv_mem hτ) (conj_mem_of_mem_normalizer (hET he) hτ)
      have hme : normConj H me ∈ inner H := by
        refine ⟨⟨e, hEH he⟩, ?_⟩
        ext x
        rfl
      have hcinner : normConj H c ∈ inner H := by
        have : normConj H c = (normConj H mτ)⁻¹ * normConj H me * normConj H mτ *
            (normConj H me)⁻¹ := by
          simp only [c, map_mul, map_inv]
          group
        rw [this]
        refine mul_mem ?_ (inv_mem hme)
        have := (inner_normal H).conj_mem _ hme (normConj H mτ)⁻¹
        simpa using this
      have hcH := mem_of_normConj_mem_inner hC hcinner
      have hc1 : (c : G) = 1 := by
        have h' : (c : G) ∈ T ⊓ H := ⟨hcT, hcH⟩
        rw [hT0, Subgroup.mem_bot] at h'
        exact h'
      have : (τ : G)⁻¹ * (e * τ * e⁻¹) = 1 := hc1
      rw [inv_mul_eq_one] at this
      exact this.symm
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h2T : 2 ∣ Nat.card T := by
      rcases hT2.card_eq_or_dvd with h | h
      · exact absurd (Subgroup.card_eq_one.mp h) hT1
      · exact h
    obtain ⟨τ, hτ⟩ := exists_prime_orderOf_dvd_card' 2 h2T
    have hτ2 : (τ : G) ^ 2 = 1 := by
      rw [← Subgroup.coe_pow, ← hτ, pow_orderOf_eq_one, Subgroup.coe_one]
    have hτ1 : (τ : G) ≠ 1 := fun h => by
      have : τ = 1 := Subtype.ext h
      rw [this, orderOf_one] at hτ
      exact absurd hτ (by norm_num)
    set mτ : Subgroup.normalizer (H : Set G) := ⟨τ, hTM τ.2⟩
    have hα2 : normConj H mτ ^ 2 = 1 := by
      rw [← map_pow]
      have : mτ ^ 2 = 1 := Subtype.ext hτ2
      rw [this, map_one]
    have hαout : normConj H mτ ∉ inner H := fun h => by
      have hτH := mem_of_normConj_mem_inner hC h
      have h' : (τ : G) ∈ T ⊓ H := ⟨τ.2, hτH⟩
      rw [hT0, Subgroup.mem_bot] at h'
      exact hτ1 h'
    have hfix : ∀ e ∈ E.subgroupOf H, normConj H mτ e = e := by
      intro e he
      apply Subtype.ext
      rw [normConj_apply]
      have h := hcomm τ τ.2 e he
      change (τ : G) * e * (τ : G)⁻¹ = e
      have h' : (e : G) * τ = τ * e := by
        calc (e : G) * τ = ((e : G) * τ * (e : G)⁻¹) * e := by group
          _ = τ * e := by rw [h]
      calc (τ : G) * e * (τ : G)⁻¹ = (e : G) * τ * (τ : G)⁻¹ := by rw [h']
        _ = e := by group
    have := hO H hmod (normConj H mτ) hα2 hαout _ hE' hfix
    omega
  ·
    have hT'1 : (T ⊓ H).subgroupOf H ≠ ⊥ := by
      intro h
      apply hT0
      rw [eq_bot_iff]
      intro x hx
      have hx' : (⟨x, hx.2⟩ : H) ∈ (T ⊓ H).subgroupOf H := hx
      rw [h, Subgroup.mem_bot] at hx'
      exact (Subgroup.mem_bot).mpr (congrArg Subtype.val hx')
    have hT'2 : IsPGroup 2 ((T ⊓ H).subgroupOf H) := hT2.to_inf_left.comap_subtype
    have hETH : E ≤ Subgroup.normalizer ((T ⊓ H : Subgroup G) : Set G) := fun e he =>
      mem_normalizer_inf (hET he) (Subgroup.le_normalizer (hEH he))
    exact hI H hmod _ _ hE' (hcardE ▸ h81) hT'1 hT'2 (comap_le_normalizer_comap H.subtype hETH)

end Normalizer

end PRankBounds

section Tag

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank PRankBounds

theorem ggUFiveTwoRankInput_of_inner_outer (hI : GGUFiveTwoLocalInnerInput)
    (hO : GGUFiveTwoOuterCentInput) : GGUFiveTwoRankInput := by
  intro G _ _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have e : ggU .PSU 5 1 =
      ⟨Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * 1)) 2 1) 5,
        Unitary.rootDatum (card_galoisField_two_mul 2 1 le_rfl) 5⟩ := by
    simp only [ggU, lieUniversal, le_refl, ↓reduceDIte]
  rw [e]
  intro ψ hker hC
  exact not_twoLocalRankFour_of_psu5 hI hO hC (statedClassicalModel_range_of_su5 ψ hker hC)

end Tag

end CFSG.StandardType
