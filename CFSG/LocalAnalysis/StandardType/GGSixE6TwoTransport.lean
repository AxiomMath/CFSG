module

public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoModel
import CFSG.LocalAnalysis.StandardType.GGSixE6TwoCent
import CFSG.LocalAnalysis.StandardType.GGSixE6TwoLevi
import CFSG.LocalAnalysis.StandardType.GGSixE6TwoJEq
import CFSG.LocalAnalysis.StandardType.GGSixE6TwoJProps
import CFSG.LocalAnalysis.StandardType.GGSixE6TwoOrder3
import CFSG.LocalAnalysis.StandardType.GGSixE6TwoComponent
import CFSG.LocalAnalysis.StandardType.GGSixE6TwoConclMap
import CFSG.LocalAnalysis.StandardType.GGSixE6TwoTransAux

public section

namespace CFSG.StandardType.GGSixE6Two

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open CFSG.SeitzReduction
  CFSG.StandardType.GGHalf CFSG.Timmesfeld.LieEmbed

section Transport

private theorem map_centralizer_singleton {G H : Type*} [Group G] [Group H] (e : G ≃* H) (x : G) :
    (Subgroup.centralizer ({x} : Set G)).map e.toMonoidHom =
      Subgroup.centralizer ({e x} : Set H) := by
  ext y
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h' := congrArg e h
    simp only [map_mul, MulEquiv.apply_symm_apply] at h'
    first | exact h' | exact h'.symm
  · intro h
    apply e.injective
    simp only [map_mul, MulEquiv.apply_symm_apply]
    first | exact h | exact h.symm

private theorem isComponentOf_map {G H : Type} [Group G] [Group H] (e : G ≃* H)
    {K C : Subgroup G} (h : CFSG.Assembly.IsComponentOf K C) :
    CFSG.Assembly.IsComponentOf (K.map e.toMonoidHom) (C.map e.toMonoidHom) :=
  ⟨Subgroup.map_mono h.1, h.2.1.map e.toMonoidHom, isQuasisimple_map_mulEquiv e h.2.2⟩

theorem ggSixE6A24RootDataRest_of_jUnique (hJ : E6TwoJUnique) (hM : GGSixE6A24ModelKnown) :
    GGSixE6A24RootDataRest := by
  intro E _ _ hperf hLM x₀ L' J' hx3 hcomp hL'M hJL hJq hJM
  obtain ⟨θ₀⟩ := nonempty_mulEquiv_EC hperf hLM
  have hx1 : x₀ ≠ 1 := ne_one_of_isComponentOf θ₀ hcomp hL'M
  have h31 := thirtyOne_dvd_card_centralizer hcomp hL'M
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf (θ₀ x₀) = 3 := by
    rw [MulEquiv.orderOf_eq]
    exact orderOf_eq_prime hx3 hx1
  have h31' : 31 ∣ Nat.card (Subgroup.centralizer ({θ₀ x₀} : Set EC)) := by
    rw [← map_centralizer_singleton θ₀ x₀, Subgroup.card_map_of_injective θ₀.injective]
    exact h31
  obtain ⟨g, hg⟩ := e6Two_order3Conj hM.1 (θ₀ x₀) hord h31'
  let θ₁ : E ≃* EC := θ₀.trans (MulAut.conj g)
  have hθ₁x : θ₁ x₀ = zE ∨ θ₁ x₀ = zE⁻¹ := by
    have h1 : θ₁ x₀ = g * θ₀ x₀ * g⁻¹ := rfl
    rw [h1]
    exact hg
  have hcomp₁ : CFSG.Assembly.IsComponentOf (L'.map θ₁.toMonoidHom)
      (Subgroup.centralizer ({zE} : Set EC)) := by
    have h := isComponentOf_map θ₁ hcomp
    rw [map_centralizer_singleton] at h
    rcases hθ₁x with h' | h'
    · rwa [h'] at h
    · rwa [h', centralizer_zE_inv] at h
  have hL₁ : L'.map θ₁.toMonoidHom = lE := eq_lE_of_isComponentOf hcomp₁
  have hJ₁le : J'.map θ₁.toMonoidHom ≤ lE := hL₁ ▸ Subgroup.map_mono hJL
  obtain ⟨l, hl, hlJ⟩ := hJ _ hJ₁le (isQuasisimple_map_mulEquiv θ₁ hJq)
    (lieModel_map_mulEquiv θ₁ hJM)
  let θ : E ≃* EC := θ₁.trans (MulAut.conj l)
  have hθJ : J'.map θ.toMonoidHom = jE := by
    rw [← hlJ, Subgroup.map_map]
    rfl
  have hlz : l * zE * l⁻¹ = zE := by
    have h := Subgroup.mem_centralizer_singleton_iff.1 (lE_le_centralizer_zE hl)
    rw [mul_inv_eq_iff_eq_mul]
    first | exact h | exact h.symm
  have hθx : θ x₀ = zE ∨ θ x₀ = zE⁻¹ := by
    have h1 : θ x₀ = l * θ₁ x₀ * l⁻¹ := rfl
    rcases hθ₁x with h' | h'
    · left
      rw [h1, h', hlz]
    · right
      have h2 : l * zE⁻¹ * l⁻¹ = (l * zE * l⁻¹)⁻¹ := by group
      rw [h1, h', h2, hlz]
  have hC : GGSixE6A24Concl (θ x₀) jE := by
    rcases hθx with h | h
    · rw [h]
      exact hM.2
    · rw [h]
      exact (GGSixE6A24Concl.congr_centralizer centralizer_zE_inv).2 hM.2
  have h2 := GGSixE6A24Concl.map_mulEquiv θ.symm hC
  rw [MulEquiv.symm_apply_apply] at h2
  have hJ' : jE.map θ.symm.toMonoidHom = J' := by
    rw [← hθJ]
    exact GGRootNorm.map_symm_map θ J'
  rwa [hJ'] at h2

end Transport

end CFSG.StandardType.GGSixE6Two
