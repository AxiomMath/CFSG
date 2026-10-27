module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20
import CFSG.HardMathSupport.Solomon.Coordinator.T112MM22
import CFSG.LocalAnalysis.RankThreeTheoremC.ConstrainedStructure3Aux
import CFSG.LocalAnalysis.UniquenessCase.UC22S2113
import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
import CFSG.LocalAnalysis.UniquenessCase.UC22S216Spor
import CFSG.LocalAnalysis.UniquenessCase.UCFront10K101
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {G : Type} [Group G] [Finite G]

theorem uc22s213_sylow_of_cover {X : Type} [Group X] [Finite X]
    (hcov : F08.IsA6Z3 X ∨ F08.IsA7Z3 X ∨ F08.IsM22Z3 X) (R : Sylow 3 X) :
    Nat.card ↥(R : Subgroup X) = 27 ∧ ∀ r ∈ (R : Subgroup X), r ^ 3 = 1 := by
  rcases hcov with ⟨hq, hZ, ⟨e⟩⟩ | ⟨hq, hZ, ⟨e⟩⟩ | ⟨hq, hZ, ⟨e⟩⟩
  · obtain ⟨h27, -, h3⟩ :=
      HardMathSupport.Solomon.Coordinator.t112m_sylow_hatSix ⟨hq.1.commutator_eq_top, hZ, ⟨e⟩⟩ R
    exact ⟨h27, h3⟩
  · obtain ⟨h27, -, h3⟩ :=
      HardMathSupport.Solomon.Coordinator.t112m_sylow_hatSeven ⟨hq.1.commutator_eq_top, hZ, ⟨e⟩⟩ R
    exact ⟨h27, h3⟩
  · obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv
    obtain ⟨h27, -, h3⟩ := HardMathSupport.Solomon.Coordinator.t112m_sylow_hatM22
      ⟨hq.1.commutator_eq_top, hZ, ⟨e.trans b⟩⟩ R
    exact ⟨h27, h3⟩

theorem uc22s213_card_sylow_of_cover {L Q : Subgroup G}
    (hcov : F08.IsA6Z3 (Bar2 L) ∨ F08.IsA7Z3 (Bar2 L) ∨ F08.IsM22Z3 (Bar2 L))
    (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q L) :
    Nat.card Q = 27 ∧ (∀ x ∈ Q, x ^ 3 = 1) ∧
      ∃ E ≤ Q, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨R, rfl⟩ := hQ
  obtain ⟨h27, h3⟩ :=
    uc22s213_sylow_of_cover hcov (R.mapSurjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L)))
  rw [Sylow.coe_mapSurjective] at h27 h3
  have hinj : Function.Injective
      ((QuotientGroup.mk' (CFSG.pCore 2 ↥L)).domRestrict (R : Subgroup ↥L)) := by
    rw [← MonoidHom.ker_eq_bot_iff, MonoidHom.ker_domRestrict, QuotientGroup.ker_mk',
      subgroupOf_eq_bot]
    exact IsPGroup.disjoint_of_ne 2 3 (by norm_num) _ _ CFSG.pCore_isPGroup R.isPGroup'
  have hRc : Nat.card (R : Subgroup ↥L) = 27 := by
    rw [← h27, ← MonoidHom.domRestrict_range]
    exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  have hR3 : ∀ r ∈ (R : Subgroup ↥L), r ^ 3 = 1 := by
    intro r hr
    have h1 := h3 _ (mem_map_of_mem (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) hr)
    rw [← map_pow] at h1
    have h2 : ((QuotientGroup.mk' (CFSG.pCore 2 ↥L)).domRestrict (R : Subgroup ↥L))
        ⟨r ^ 3, pow_mem hr 3⟩ =
          (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).domRestrict (R : Subgroup ↥L) 1 := by
      rw [MonoidHom.domRestrict_apply, map_one]
      exact h1
    exact congrArg Subtype.val (hinj h2)
  have hQc : Nat.card ((R : Subgroup ↥L).map L.subtype) = 27 := by
    rw [card_map_of_injective L.subtype_injective, hRc]
  have hQ3 : ∀ x ∈ (R : Subgroup ↥L).map L.subtype, x ^ 3 = 1 := by
    rintro _ ⟨r, hr, rfl⟩
    have h := congrArg L.subtype (hR3 r hr)
    rwa [map_pow, map_one] at h
  exact ⟨hQc, hQ3, CFSG.LocalAnalysis.RankThreeTheoremC.exists_isElemAbelian_card_sq_of_card_cube
    (p := 3) (by rw [hQc]; norm_num) hQ3⟩

theorem uc22s213_inner_of_cover
    (hout : ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → (∃ a b : X, a * b ≠ b * a) →
      ∀ s : TauCeti.SporadicName, IsSpor X s → Nat.card (Outer X) ≤ 2)
    {M L : Subgroup G} (hL : L ∈ calC M)
    (hcov : F08.IsA6Z3 (Bar2 L) ∨ F08.IsA7Z3 (Bar2 L) ∨ F08.IsM22Z3 (Bar2 L))
    (σ : MulAut (BarInf L)) (hσ : Odd (orderOf σ)) :
    σ ∈ (MulAut.conj : BarInf L →* MulAut (BarInf L)).range := by
  obtain ⟨e⟩ := uc22p21k_barInf_equiv_of_calC hL
  rcases hcov with ⟨-, -, ⟨f⟩⟩ | ⟨-, -, ⟨f⟩⟩ | ⟨-, -, ⟨f⟩⟩
  · obtain ⟨x, hx⟩ := F10.exists_conj_of_odd_orderOf_alt (by norm_num) (e.trans f) σ hσ
    exact ⟨x, hx.symm⟩
  · obtain ⟨x, hx⟩ := F10.exists_conj_of_odd_orderOf_alt (by norm_num) (e.trans f) σ hσ
    exact ⟨x, hx.symm⟩
  · exact uc22s216_mem_range_conj_of_isSpor hout hL (s := .M22) ⟨e.trans f⟩ hσ

theorem uc22s213_exists_inner_of_odd {L : Subgroup G} (hq : CFSG.Open.IsQuasisimple (Bar2 L))
    (hinn : ∀ σ : MulAut (BarInf L), Odd (orderOf σ) →
      σ ∈ (MulAut.conj : BarInf L →* MulAut (BarInf L)).range)
    {x : G} (hxN : x ∈ normalizer (L : Set G)) (hx : Odd (orderOf x)) :
    ∃ l ∈ L, ∀ y ∈ L, (x * y * x⁻¹) * (l * y * l⁻¹)⁻¹ ∈ CFSG.Open.pCoreOf 2 L := by
  have hσ : Odd (orderOf (inducedBarInfAutHom L ⟨x, hxN⟩)) := by
    have h := orderOf_map_dvd (inducedBarInfAutHom L) ⟨x, hxN⟩
    rw [Subgroup.orderOf_mk] at h
    exact hx.of_dvd_nat h
  obtain ⟨lb, hlb⟩ := MonoidHom.mem_range.mp (hinn _ hσ)
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective lb
  have hlN : (l : G) ∈ normalizer (L : Set G) := le_normalizer l.2
  have hc : x * (l : G)⁻¹ ∈ normalizer (L : Set G) := mul_mem hxN (inv_mem hlN)
  have h1 : inducedBarInfAutHom L ⟨x * (l : G)⁻¹, hc⟩ = 1 := by
    rw [show (⟨x * (l : G)⁻¹, hc⟩ : ↥(normalizer (L : Set G))) = ⟨x, hxN⟩ * (⟨l, hlN⟩)⁻¹ from rfl,
      map_mul, map_inv, ← hlb, uc22s2113_inducedBarInfAutHom_of_mem l.2]
    exact mul_inv_cancel _
  refine ⟨l, l.2, fun y hy => ?_⟩
  have h := (uc22s2113_centralizesBar_of_inducedBarInfAutHom_eq_one hq hc h1).2
    ((l : G) * y * (l : G)⁻¹) (L.mul_mem (L.mul_mem l.2 hy) (L.inv_mem l.2))
  rw [show x * y * x⁻¹ * ((l : G) * y * (l : G)⁻¹)⁻¹ =
      x * (l : G)⁻¹ * ((l : G) * y * (l : G)⁻¹) * (x * (l : G)⁻¹)⁻¹ *
        ((l : G) * y * (l : G)⁻¹)⁻¹ by group]
  exact h

end CFSG.LocalAnalysis.UniquenessCase.UC22
