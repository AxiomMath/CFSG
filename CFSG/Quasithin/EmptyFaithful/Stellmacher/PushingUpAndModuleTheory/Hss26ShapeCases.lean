module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.Hss26ShapeImage
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.Hss26ShapeTransv
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.Hss26ShapeCore

public section

namespace CFSG.Quasithin.F53

open CFSG.Open CFSG.QuasithinUnique.Setup.Campbell CFSG.Quasithin.F7 CFSG.Quasithin.F53Push
  CosetGeom Equiv
open CFSG.QuasithinUnique (IsSylowTwoOf)

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

namespace SitSigma

variable {δ μ : Geo H M} {X : Subgroup G}

omit [Finite G] in
theorem stab_le_normalizer_of_le (hQ : Qv μ ≤ X) :
    stab μ ≤ Subgroup.normalizer ((Qv μ ⊓ X : Subgroup G) : Set G) := by
  rw [inf_eq_left.mpr hQ]
  exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (stab μ)

theorem not_le_pCore (hA : F53Amalgam H M S) (h : SitSigma δ μ X)
    (hPn : stab μ ≤ Subgroup.normalizer ((Qv μ ⊓ X : Subgroup G) : Set G)) :
    ¬ Qv μ ⊓ X ≤ pCoreOf 2 X := by
  intro hle
  have heq : pCoreOf 2 X = Qv μ ⊓ X := le_antisymm h.R_le_P hle
  have hP0 : Qv μ ⊓ X ≠ ⊥ := fun hb => by
    have : Zv μ ≤ Qv μ ⊓ X := fun z hz => h.R_le_P (h.zle hz)
    rw [hb] at this
    exact Zv_ne_bot hA μ (le_bot_iff.mp this)
  refine h.noCharNormal hA hPn (Qv μ ⊓ X) le_rfl hP0 ?_ ?_
  · rw [Subgroup.subgroupOf_self]
    infer_instance
  · rw [← heq]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X

theorem shape_five (hBau3 : BaumannS3 G) (hBau5 : BaumannA5 G) (hA : F53Amalgam H M S)
    (h : SitSigma δ μ X)
    (hPn : stab μ ≤ Subgroup.normalizer ((Qv μ ⊓ X : Subgroup G) : Set G))
    (hRQ : pCoreOf 2 X ≤ Qv δ) (φ : ↥X →* Perm (Fin 5))
    (hφ : ∀ x : ↥X, φ x = 1 ↔ (x : G) ∈ pCoreOf 2 X) :
    φ.range = ⊤ ∧ Nonempty (OTwoQuot X ≃* Perm (Fin 5)) := by
  have hPR := h.not_le_pCore hA hPn
  have hPH := h.pushHyp hA
  have hnc := h.noCharNormal hA hPn
  have hP0 : Qv μ ⊓ X ≠ ⊥ := fun hb => by
    have : Zv μ ≤ Qv μ ⊓ X := fun z hz => h.R_le_P (h.zle hz)
    rw [hb] at this
    exact Zv_ne_bot hA μ (le_bot_iff.mp this)
  have hJ := not_le_core_of_noCharNormal hPH hP0 hnc
  rcases shape_of_hom_five h.sylow φ hφ hPR with he3 | ⟨-, he5⟩ | hS5 | ⟨x, y, hxy, hy5, hinv⟩
  · exact (h.false_of_S3 hBau3 hA hPn hRQ he3).elim
  · exact (h.false_of_A5 hBau5 hA hPn hRQ he5).elim
  · exact hS5
  · exact (false_of_inverted hPH φ hφ hJ hxy hy5 hinv).elim

end SitSigma

end CFSG.Quasithin.F53
