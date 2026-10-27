module

public import CFSG.LocalAnalysis.StandardType.GGRootCentKGTagsDefs
import CFSG.LocalAnalysis.StandardType.GGRootCentKGSummand
import CFSG.LocalAnalysis.StandardType.GGRootCentKGSpCent
import CFSG.Assembly.Subnormal

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

namespace KGExc

@[expose] def KGPieces {U : Type} [Group U] (z : U) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (ψ : U →* G), Function.Injective ψ →
    ∀ E : Subgroup G, E ≤ ψ.range ⊓ Subgroup.centralizer {ψ z} →
      ∃ 𝒥 : Set (Subgroup G),
        (∀ P : Subgroup G, P ≤ ψ.range ⊓ Subgroup.centralizer {ψ z} → ⁅P, P⁆ = P →
          P ≤ sSup 𝒥) ∧
        ∀ J ∈ 𝒥, GGRCSKGPiece (ψ.range ⊓ Subgroup.centralizer {ψ z}) E J

theorem KGPieces.of_mulEquiv {U V : Type} [Group U] [Group V] {z : U} (e : U ≃* V)
    (h : KGPieces (e z)) : KGPieces z := by
  intro G _ _ ψ hψ E hE
  have hr : (ψ.comp e.symm.toMonoidHom).range = ψ.range := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨e.symm y, rfl⟩
    · rintro ⟨y, rfl⟩
      exact ⟨e y, by simp⟩
  have hz : (ψ.comp e.symm.toMonoidHom) (e z) = ψ z := by simp
  have h' := h G (ψ.comp e.symm.toMonoidHom) (hψ.comp e.symm.injective) E
    (by rw [hr, hz]; exact hE)
  rw [hr, hz] at h'
  exact h'

theorem KGPieces.map {U : Type} [Group U] {z : U} (h : KGPieces z) (α : MulAut U) :
    KGPieces (α z) :=
  KGPieces.of_mulEquiv (MulEquiv.symm α) (by rwa [MulEquiv.symm_apply_apply])

theorem largeEvenMarking_inn_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : LargeEvenMarking Y (fun lab R _ I _ _ => GGChevStTag lab ∧ LargeEvenInnSet R ⊆ I)) :
    LargeEvenMarking X (fun lab R _ I _ _ => GGChevStTag lab ∧ LargeEvenInnSet R ⊆ I) := by
  obtain ⟨hY, lab, hlab, hraw⟩ := h
  have hperf : Group.IsPerfect Y := ⟨hY⟩
  have hX : commutator X = ⊤ :=
    (Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective).commutator_eq_top
  refine ⟨hX, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, hθ⟩
  exact ⟨hs, hna, (QuotientGroup.congr (Subgroup.center X) (Subgroup.center Y) e
    (Subgroup.map_center_eq e)).trans θ, hθ⟩

theorem kgPieces_of_decomp {U : Type} [Group U] {z : U} {Q L : Subgroup U}
    (hC : Subgroup.centralizer ({z} : Set U) = Q ⊔ L)
    (hQ : pCoreOf 2 (Subgroup.centralizer ({z} : Set U)) = Q)
    (hLQ : L ≤ Subgroup.normalizer (Q : Set U)) (hQL : Q ⊓ L = ⊥)
    (hperf : ⁅Subgroup.centralizer ({z} : Set U), Subgroup.centralizer ({z} : Set U)⁆ =
      Subgroup.centralizer ({z} : Set U))
    (hLq : CFSG.Assembly.IsQuasisimple ↥L)
    (hLm : LargeEvenMarking ↥L
      (fun lab R _ I _ _ => GGChevStTag lab ∧ LargeEvenInnSet R ⊆ I)) :
    KGPieces z := by
  intro G _ _ ψ hψ E hE
  have hmap : ψ.range ⊓ Subgroup.centralizer {ψ z} = Q.map ψ ⊔ L.map ψ := by
    rw [RCSTSp.range_inf_centralizer_of_injective hψ, hC, Subgroup.map_sup]
  have hC₀ : ψ.range ⊓ Subgroup.centralizer {ψ z} = Q.map ψ ⊔ (L.map ψ ⊔ ⊥) := by
    rw [hmap, sup_bot_eq]
  have hQ₀ : pCoreOf 2 (ψ.range ⊓ Subgroup.centralizer {ψ z}) = Q.map ψ := by
    rw [KGSp.pCoreOf_range_inf_centralizer hψ, hQ]
  have hperf₀ : ⁅Q.map ψ ⊔ L.map ψ, Q.map ψ ⊔ L.map ψ⁆ = Q.map ψ ⊔ L.map ψ := by
    have hm : (Subgroup.centralizer ({z} : Set U)).map ψ = Q.map ψ ⊔ L.map ψ := by
      rw [hC, Subgroup.map_sup]
    rw [← hm, ← Subgroup.map_commutator, hperf]
  have hLQ₀ : L.map ψ ≤ Subgroup.normalizer ((Q.map ψ : Subgroup G) : Set G) :=
    ggRCST_map_le_normalizer ψ hLQ
  have hQL₀ : Q.map ψ ⊓ L.map ψ = ⊥ :=
    disjoint_iff.mp (Subgroup.disjoint_map hψ (disjoint_iff.mpr hQL))
  have hLM : L.map ψ ≤ Subgroup.centralizer ((⊥ : Subgroup G) : Set G) := by
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hy
    rw [hy, one_mul, mul_one]
  have eL : ↥(L.map ψ) ≃* ↥L := (L.equivMapOfInjective ψ hψ).symm
  have hLq₀ : CFSG.Assembly.IsQuasisimple ↥(L.map ψ) :=
    CFSG.Assembly.IsQuasisimple.of_mulEquiv eL hLq
  have hLm₀ := largeEvenMarking_inn_of_mulEquiv eL hLm
  refine ⟨{Q.map ψ ⊔ L.map ψ}, ?_, ?_⟩
  · intro P hP _
    rw [sSup_singleton, ← hmap]
    exact hP
  · intro J hJ
    rw [Set.mem_singleton_iff] at hJ
    subst hJ
    exact ggRCSKGPiece_of_summand hC₀ hQ₀ hLQ₀ bot_le hLM hQL₀ hperf₀ hLq₀ hLm₀ hE

end KGExc

end CFSG.StandardType
