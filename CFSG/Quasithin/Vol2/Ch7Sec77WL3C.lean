module

public import CFSG.Quasithin.Vol2.Ch7Sec77L3C
public import CFSG.Quasithin.Background.C134L32CorrM
public import CFSG.Quasithin.EmptyFaithful.SBd5Dec

public section

namespace CFSG.Quasithin.H13.Sec77

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.H.S77
  CFSG.Quasithin.H.SL3Pair CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.H.BlkW
  CFSG.Quasithin.SBc17 CFSG.Assembly.LowTwoRank
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem exists_c134CaseW (hMS : C134L32CorrM) {H K R : Subgroup G} (hK : K ∈ cComp H)
    (hRN : R ≤ Subgroup.normalizer (K : Set G)) (hMSp : IsMSPair (K ⊔ R) R)
    (eX : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2))) :
    ∃ i : ℕ, CFSG.Quasithin.IsC134CaseM i (K ⊔ R) R K := by
  have hcomp : K ∈ cComp (K ⊔ R) := SBd5.mem_cComp_sup' hK hRN
  have hset : ((K ⊔ R : Subgroup G) : Set G) = (K : Set G) * (R : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left K R hRN
  let α : ↥K →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)) :=
    eX.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥K))
  have hα : IsModO2Surj K α := by
    refine ⟨eX.surjective.comp (QuotientGroup.mk'_surjective _), ?_⟩
    show (eX.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥K))).ker = CFSG.pCore 2 ↥K
    rw [MonoidHom.ker_comp_of_injective (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) eX.toMonoidHom
      eX.injective, QuotientGroup.ker_mk']
  exact hMS G (K ⊔ R) R K hMSp hcomp hset ⟨ZMod 2, inferInstance, inferInstance, α, by simp, hα⟩

theorem false_of_c134CaseW {K R W : Subgroup G} (hW16 : Nat.card W = 16)
    (hWQ : W ≤ c134Q (K ⊔ R) K)
    (hWC : ∀ w ∈ W, w ∈ Subgroup.centralizer (K : Set G) → w = 1)
    (hWZ : W ≤ Subgroup.centralizer (pCoreOf 2 (K ⊔ R) : Set G))
    (hKX : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 168) {i : ℕ}
    (hi : CFSG.Quasithin.IsC134CaseM i (K ⊔ R) R K) (hi2 : i ≠ 2) : False := by
  have hQO := c134Q_le_pCoreOf (le_sup_left : K ≤ K ⊔ R)
  have hWZQ : W ≤ centerOf (c134Q (K ⊔ R) K) := fun w hw =>
    ⟨hWQ hw, Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hQO) (hWZ hw)⟩
  have hWCQ : W ⊓ c134CQ (K ⊔ R) K = ⊥ := by
    rw [eq_bot_iff]
    rintro w ⟨hw, -, hwK⟩
    exact (Subgroup.mem_bot).2 (hWC w hw hwK)
  have hcardF : ∀ {F : Type} [Field F] [Finite F] (k : ℕ),
      Nat.card (Multiplicative (Fin k → Fin 3 → F)) = Nat.card F ^ (3 * k) := fun k => by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_fun, Nat.card_fin,
      Nat.card_fin, ← pow_mul, mul_comm]
  have hcardF1 : ∀ {F : Type} [Field F] [Finite F],
      Nat.card (Multiplicative (Fin 3 → F)) = Nat.card F ^ 3 := fun {F} _ _ => by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_fin]
  rcases i with _ | _ | _ | _ | _ | _ | i
  · exact hi
  ·
    obtain ⟨-, n, F, hFf, hFt, -, -, α, hαs, hαk, β, hβs, hβk, -⟩ := hi
    have hF2 : Nat.card F = 2 := card_eq_two_of_isModO2Surj ⟨hαs, hαk⟩ hKX
    have h1 := card_eq_of_surjective_ker bot_le β hβs hβk
    rw [Subgroup.card_bot, one_mul, hcardF1, hF2] at h1
    have h2 := Subgroup.card_le_of_le hWQ
    rw [hW16, h1] at h2
    norm_num at h2
  · exact hi2 rfl
  ·
    obtain ⟨⟨n, F, hFf, hFt, α, -, hα, ⟨-, -, β, hβs, hβk, -⟩, -⟩, -⟩ := hi
    have hF2 : Nat.card F = 2 := card_eq_two_of_isModO2Surj hα hKX
    have h1 := card_eq_of_surjective_ker bot_le β hβs hβk
    rw [Subgroup.card_bot, one_mul, hcardF, hF2] at h1
    have h2 := Subgroup.card_le_of_le hWZQ
    rw [hW16, h1] at h2
    norm_num at h2
  ·
    obtain ⟨⟨n, F, hFf, hFt, α, -, hα, hZeq, hinf, ⟨-, -, β, hβs, hβk, -⟩, -, -⟩, -⟩ := hi
    have hF2 : Nat.card F = 2 := card_eq_two_of_isModO2Surj hα hKX
    have h1 := card_eq_of_surjective_ker bot_le β hβs hβk
    rw [Subgroup.card_bot, one_mul, hcardF, hF2] at h1
    set Z := centerOf (c134Q (K ⊔ R) K) with hZ
    set U := ⁅Z, K⁆ with hU
    set CQ := c134CQ (K ⊔ R) K with hCQ
    have hCQZ' : CQ ≤ Z := hZeq ▸ le_sup_left
    have h2 := card_mul_card_le_of_inf_eq_bot hWZQ hCQZ' hWCQ
    have hUN : U ≤ Subgroup.normalizer (CQ : Set G) := by
      intro x hx
      have hUZ : U ≤ Z := hZeq ▸ le_sup_right
      refine Subgroup.mem_normalizer_fintype fun c hc => ?_
      have e : x * c * x⁻¹ = c := by
        rw [Subgroup.mem_centralizer_iff.1 (hCQZ' hc).2 x (hUZ hx).1, mul_inv_cancel_right]
      rw [e]
      exact hc
    have h3 : Nat.card Z ≤ Nat.card CQ * Nat.card U := by
      have e : ((Z : Subgroup G) : Set G) = (CQ : Set G) * (U : Set G) := by
        rw [hZeq]
        exact Subgroup.coe_mul_of_right_le_normalizer_left CQ U hUN
      rw [← SetLike.coe_sort_coe, e]
      exact Set.natCard_mul_le
    have h1' : Nat.card U = 8 := by rw [h1]; norm_num
    rw [hW16] at h2
    rw [h1'] at h3
    have hpos : 0 < Nat.card CQ := Nat.card_pos
    nlinarith
  ·
    obtain ⟨⟨α, hα, hcard2, ⟨-, hCQle, β, hβs, hβk, -⟩⟩, -⟩ := hi
    have h1 := card_eq_of_surjective_ker hCQle β hβs hβk
    rw [hcard2, hcardF, Nat.card_zmod] at h1
    have h2 := card_mul_card_le_of_inf_eq_bot hWQ hCQle hWCQ
    rw [hW16, hcard2, h1] at h2
    norm_num at h2
  · exact hi


end CFSG.Quasithin.H13.Sec77
