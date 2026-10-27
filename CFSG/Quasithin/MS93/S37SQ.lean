module

public import CFSG.Quasithin.MS93.S37Bad4
public import CFSG.Quasithin.MS93.S37Crit
public import CFSG.Quasithin.MS93.S37Res

public section

namespace CFSG.Quasithin.MS93.S37

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.MSP
open CFSG.QuasithinUnique CFSG.Quasithin.MS93.S36 CFSG.Quasithin.Vol2
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G]

namespace Cfg

variable {M T L : Subgroup G} {F : Type} [Field F] [Fintype F] (C : Cfg M T L F)
include C

theorem eq_pt₀_of_caseI (hT : Q₂ F ≤ C.T0bar) (ψ : MulAut ↥T) {p : Submodule F (V4 F)}
    (hp : IsPoint p) (hE : C.rhoIm (Ut M T L ψ) = xPoint p) : p = pt₀ F := by
  have : CharP F 2 := charP_of_card_eq_prime_pow C.hF
  obtain ⟨x, hx0, rfl⟩ := exists_eq_span_of_isPoint hp
  have hfix : ∀ g ∈ Q₂ F, mat g *ᵥ x = x := by
    intro g hg
    obtain ⟨t, rfl⟩ := hT hg
    obtain ⟨n, hn⟩ := C.h.isPGroup ⟨t, T1_le_T t.2⟩
    have htn : t ^ 2 ^ n = 1 := Subtype.ext (by simpa using congrArg Subtype.val hn)
    have hρn : C.rho1 t ^ 2 ^ n = 1 := by rw [← map_pow, htn, map_one]
    have hN := C.rho1_mem_normalizer le_rfl ψ t.2 (T1_le_T t.2)
    rw [hE] at hN
    exact mulVec_eq_of_normalizes_xPoint hx0 hρn hN
  have hx : x ∈ pt₀ F := by
    rw [← fixSp_Q₂]
    exact mem_fixSp.2 hfix
  refine eq_pt₀_of_le ((Submodule.span_singleton_le_iff_mem _ _).2 hx) ?_
  rw [Ne, Submodule.span_singleton_eq_bot]
  exact hx0

theorem exists_critical_le (hb : critDist (puAmalgam C.h.le) = 2) :
    ∃ ψ : MulAut ↥T, ¬ Uq M T L ≤ Qt M ψ ∧
      (pCoreOf 2 M).relIndex (Ut M T L ψ⁻¹) ≤ (pCoreOf 2 M).relIndex (Ut M T L ψ) := by
  obtain ⟨ψ₀, hψ₀⟩ := exists_critical C.h hb
  have hc₀ : ¬ Uq M T L ≤ Qt M ψ₀ := fun h => hψ₀ ((C.Z0q_le_Qt_iff ψ₀).2 h)
  rcases le_total ((pCoreOf 2 M).relIndex (Ut M T L ψ₀⁻¹))
      ((pCoreOf 2 M).relIndex (Ut M T L ψ₀)) with h | h
  · exact ⟨ψ₀, hc₀, h⟩
  · refine ⟨ψ₀⁻¹, C.crit_inv C.h.pCore_le le_rfl ψ₀ hc₀, ?_⟩
    rw [inv_inv]
    exact h

theorem false_of_T0bar_bot (hT : C.T0bar = ⊥) (hb : critDist (puAmalgam C.h.le) = 2) : False := by
  obtain ⟨ψ, hcrit, hle⟩ := C.exists_critical_le hb
  obtain ⟨hU, -⟩ := C.Ut_le_T1 C.h.pCore_le le_rfl ψ hcrit hle
  apply C.rhoIm_ne_bot C.h.pCore_le le_rfl ψ hcrit hU
  rw [eq_bot_iff, ← hT]
  intro g hg
  obtain ⟨x, hxK, hx, rfl⟩ := (C.mem_rhoIm).1 hg
  exact ⟨⟨x, hU hx⟩, rfl⟩

theorem false_of_SQ₂ (hT : C.T0bar = sylS F ∨ C.T0bar = Q₂ F)
    (hb : critDist (puAmalgam C.h.le) = 2) (hk : 3 ≤ C.k) : False := by
  have : CharP F 2 := charP_of_card_eq_prime_pow C.hF
  have hQ₂T : Q₂ F ≤ C.T0bar := by
    rcases hT with h | h
    · rw [h]
      exact Q₂_le_sylS
    · rw [h]
  obtain ⟨ψ, hcrit, hle⟩ := C.exists_critical_le hb
  obtain ⟨hU, hU'⟩ := C.Ut_le_T1 C.h.pCore_le le_rfl ψ hcrit hle
  have hcrit' := C.crit_inv C.h.pCore_le le_rfl ψ hcrit
  have heq := (C.relIndex_inv_eq C.h.pCore_le le_rfl ψ hcrit hU hU' hle).1
  have hle' : (pCoreOf 2 M).relIndex (Ut M T L ψ⁻¹⁻¹) ≤
      (pCoreOf 2 M).relIndex (Ut M T L ψ⁻¹) := by rw [inv_inv, heq]
  have hcaseI : ∀ φ : MulAut ↥T, ¬ Uq M T L ≤ Qt M φ → Ut M T L φ ≤ T1 M T L →
      Ut M T L φ⁻¹ ≤ T1 M T L →
      (pCoreOf 2 M).relIndex (Ut M T L φ⁻¹) ≤ (pCoreOf 2 M).relIndex (Ut M T L φ) →
        C.rhoIm (Ut M T L φ) = X₂ F := by
    intro φ hc hφ hφ' hl
    rcases C.case_I_or_II C.h.pCore_le le_rfl φ hc hφ hl with ⟨p, hp, hpE⟩ | ⟨hII, -⟩
    · rw [hpE, C.eq_pt₀_of_caseI hQ₂T φ hp hpE]
    · exfalso
      rcases hT with h | h
      · exact C.not_caseII_S h φ hc hφ hφ' hl hII
      · exact C.not_caseII_Q₂ h φ hc hφ hφ' hl hII
  have hE₀ := hcaseI ψ hcrit hU hU' hle
  have hE₀' := hcaseI ψ⁻¹ hcrit' hU' (by rw [inv_inv]; exact hU) hle'
  have hT1 : tImage ψ (T1 M T L) = T1 M T L := by
    refine (tImage_T1_eq ψ fun t ht => ?_).2
    refine C.mem_T1_of_comm ψ hcrit hU' (T1_le_T ht) fun x hx => ?_
    exact C.comm_of_xPoint le_rfl ψ hU isPoint_pt₀ hE₀ ht (T1_le_T ht) hx
  set θ := restr ψ T1_le_T hT1 with hθ
  have hE : C.rhoIm (Ut M T L θ) = X₂ F := by
    have e : Ut M T L θ = Ut M T L ψ := tImage_restr ψ T1_le_T hT1 C.Uq_le_T1
    rw [e, hE₀]
  have hE' : C.rhoIm (Ut M T L θ⁻¹) = X₂ F := by
    have e : Ut M T L θ⁻¹ = Ut M T L ψ⁻¹ := tImage_restr_inv ψ T1_le_T hT1 C.Uq_le_T1
    rw [e, hE₀']
  have hE'' : C.rhoIm (Ut M T L θ⁻¹⁻¹) = X₂ F := by
    rw [inv_inv]
    exact hE
  have hgood : ∀ φ : MulAut ↥(T1 M T L), C.rhoIm (Ut M T L φ) = X₂ F →
      C.rhoIm (Ut M T L φ⁻¹) = X₂ F → C.rhoIm (Qt M φ) = X₂ F := by
    intro φ h1 h2
    have hd : (∀ (z : G) (hz : z ∈ Qt M φ), C.rho ⟨z, Qt_le_sup φ hz⟩ ∈ X₂ F) ∨
        ∀ (t : G) (ht : t ∈ T ⊓ L), C.rho1 (φ ⟨t, T_inf_L_le_T1 ht⟩) ∈ X₂ F := by
      rcases hT with h | h
      · exact C.rhoIm_Qt_or_S h φ h1 h2
      · exact C.rhoIm_Qt_or_Q₂ h φ h1 h2
    rcases hd with hN | hK
    · exact C.rhoIm_Qt_eq_X₂ φ h1 hN
    · exfalso
      rcases hT with h | h
      · exact C.false_of_bad_S h φ h1 h2 hK
      · exact C.false_of_bad_Q₂ h φ h1 h2 hK
  have hN := hgood θ hE hE'
  have hN' := hgood θ⁻¹ hE' hE''
  have hN'' : C.rhoIm (Qt M θ⁻¹⁻¹) = X₂ F := by
    rw [inv_inv]
    exact hN
  have hθg := C.isGood_of_rhoIm θ hE hN hE' hN'
  have hθg' := C.isGood_of_rhoIm θ⁻¹ hE' hN' hE'' hN''
  have hQUD := C.exists_of_sup_eq (C.pCore_eq_of_rhoIm θ hE hN).1
  have hq : 8 ≤ Nat.card F := by
    rw [Nat.card_eq_fintype_card, C.hF]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ C.k := Nat.pow_le_pow_right (by norm_num) hk
  exact C.false_of_isGood hQUD hQ₂T hq θ hθg hθg'

end Cfg

end CFSG.Quasithin.MS93.S37
