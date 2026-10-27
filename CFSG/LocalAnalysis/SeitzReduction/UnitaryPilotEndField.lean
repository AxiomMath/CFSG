module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotUnique
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotEndField
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotSylowUnique

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.EvenSmallLie (StandardSetting)
open CFSG.SeitzReduction.LinearPilot (normalizerQuotientAut normalizerQuotientAut_apply)

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {n : ℕ}

section GraphCoordinate

include h in
theorem semilinearAutGroup_normal (hn : 3 ≤ n) : (semilinearAutGroup n K).Normal := by
  have := h.finite
  exact ⟨fun _ he g => LinearPilot.mul_mem_semilinearAutGroup_mul_inv hn g he⟩

theorem graphFieldAut_not_mem_semilinearAutGroup (hn : 3 ≤ n) :
    graphFieldAut h n ∉ semilinearAutGroup n K := by
  have := h.finite
  intro hθ
  apply ProjectivePlane.dualAut_not_mem_semilinearAutGroup (K := K) hn
  have hδ : dualAut n K = (fieldAut n K (barRingEquiv h))⁻¹ * graphFieldAut h n := by
    rw [graphFieldAut, inv_mul_cancel_left]
  rw [hδ]
  exact mul_mem (inv_mem (fieldAut_mem_semilinearAutGroup _)) hθ

theorem mem_or_mul_inv_graphFieldAut_mem (hn : 3 ≤ n) (α : MulAut (projectiveSL n K)) :
    α ∈ semilinearAutGroup n K ∨ α * (graphFieldAut h n)⁻¹ ∈ semilinearAutGroup n K := by
  have := h.finite
  have hα : α ∈ standardAutGroup n K := by
    rw [(automorphism_generation (K := K) hn).1]
    exact mem_top α
  rcases mem_or_mul_dualAut_mem hα with hE | hE
  · exact Or.inl hE
  · right
    have hδδ : dualAut n K * dualAut n K = 1 :=
      (standard_automorphism_transport (K := K) (n := n)).2.2.2.1
    have hθinv : (graphFieldAut h n)⁻¹ =
        dualAut n K * (fieldAut n K (barRingEquiv h))⁻¹ := by
      rw [graphFieldAut, mul_inv_rev, inv_eq_of_mul_eq_one_right hδδ]
    have hcomm : dualAut n K * (fieldAut n K (barRingEquiv h))⁻¹ =
        (fieldAut n K (barRingEquiv h))⁻¹ * dualAut n K := by
      rw [← map_inv]
      exact LinearFlag.dualAut_mul_fieldAut _
    rw [hθinv, hcomm, ← mul_assoc]
    have hkey : α * (fieldAut n K (barRingEquiv h))⁻¹ * dualAut n K =
        α * dualAut n K * (fieldAut n K (barRingEquiv h))⁻¹ := by
      rw [mul_assoc, ← hcomm, ← mul_assoc]
    rw [hkey]
    exact mul_mem hE (inv_mem (fieldAut_mem_semilinearAutGroup _))

end GraphCoordinate

theorem normalizerQuotientAut_eq_graphFieldAut {G : Type*} [Group G] {G₀ : Subgroup G}
    (ψ : G₀ ⧸ center G₀ ≃* projectiveSL n K) {t : G} (htG₀ : t ∈ normalizer (G₀ : Set G))
    (hψt : ∀ x : G₀, ψ ((G₀.normalizerMonoidHom ⟨t, htG₀⟩ x : G₀) : G₀ ⧸ center G₀) =
      graphFieldAut h n (ψ (x : G₀ ⧸ center G₀))) :
    normalizerQuotientAut ψ ⟨t, htG₀⟩ = graphFieldAut h n := by
  ext y
  obtain ⟨q, rfl⟩ := ψ.surjective y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  rw [normalizerQuotientAut_apply, hψt]

section Endgame

variable {G : Type} [Group G] [Finite G] {G₀ : Subgroup G}

theorem exists_normal_index_two_of_globalGraphField (hn : 3 ≤ n) {t : G} (ht : orderOf t = 2)
    (htG₀ : t ∈ normalizer (G₀ : Set G)) (ψ : G₀ ⧸ center G₀ ≃* projectiveSL n K)
    (hψt : ∀ x : G₀, ψ ((G₀.normalizerMonoidHom ⟨t, htG₀⟩ x : G₀) : G₀ ⧸ center G₀) =
      graphFieldAut h n (ψ (x : G₀ ⧸ center G₀)))
    (huniq : ∀ g : G, g⁻¹ * t * g ∈ normalizer (G₀ : Set G) → g ∈ normalizer (G₀ : Set G)) :
    ∃ N : Subgroup G, N.Normal ∧ N.index = 2 := by
  set N := normalizer (G₀ : Set G) with hN
  set ρ := normalizerQuotientAut ψ with hρ
  set t₀ : N := ⟨t, htG₀⟩ with ht₀
  have hρt : ρ t₀ = graphFieldAut h n := normalizerQuotientAut_eq_graphFieldAut h ψ htG₀ hψt
  have hEn := semilinearAutGroup_normal h (K := K) hn
  set Y₀ : Subgroup N := (semilinearAutGroup n K).comap ρ with hY₀
  set Y : Subgroup G := Y₀.map N.subtype with hY
  have hY₀n : Y₀.Normal := hEn.comap ρ
  have htY : t ∈ normalizer (Y : Set G) := by
    have hle := Subgroup.le_normalizer_map (H := Y₀) N.subtype
    rw [normalizer_eq_top_iff.2 hY₀n, ← MonoidHom.range_eq_map, range_subtype] at hle
    exact hle htG₀
  have hmemY : ∀ y : N, (y : G) ∈ Y ↔ ρ y ∈ semilinearAutGroup n K := by
    intro y
    constructor
    · rintro ⟨y', hy', hyy'⟩
      have : y' = y := Subtype.ext hyy'
      rw [← this]
      exact hy'
    · intro hy
      exact ⟨y, hy, rfl⟩
  have htnY : t ∉ Y := by
    intro htY'
    have h1 := (hmemY t₀).1 htY'
    rw [hρt] at h1
    exact graphFieldAut_not_mem_semilinearAutGroup h hn h1
  have hNle : N ≤ Y ⊔ zpowers t := by
    intro x hx
    rcases mem_or_mul_inv_graphFieldAut_mem h hn (ρ ⟨x, hx⟩) with hE | hE
    · exact (le_sup_left : Y ≤ Y ⊔ zpowers t) ((hmemY ⟨x, hx⟩).2 hE)
    · have hxt : x * t⁻¹ ∈ Y := by
        have h1 := (hmemY (⟨x, hx⟩ * t₀⁻¹)).2 (by rw [map_mul, map_inv, hρt]; exact hE)
        exact h1
      have hx' : x = (x * t⁻¹) * t := by group
      rw [hx']
      exact mul_mem ((le_sup_left : Y ≤ Y ⊔ zpowers t) hxt)
        ((le_sup_right : zpowers t ≤ Y ⊔ zpowers t) (mem_zpowers t))
  obtain ⟨-, ⟨S, hS⟩, -, -⟩ := F4Pilot.centralizer_le_and_sylow_le_of_unique ht htG₀ huniq
  have hfus : ∀ g : G, g⁻¹ * t * g ∉ Y := by
    intro g hgY
    have hgN : g⁻¹ * t * g ∈ N := map_subtype_le Y₀ hgY
    have hg := huniq g hgN
    set g₀ : N := ⟨g, hg⟩ with hg₀
    have hy : ((g₀⁻¹ * t₀ * g₀ : N) : G) ∈ Y := hgY
    rw [hmemY, map_mul, map_mul, map_inv, hρt] at hy
    apply graphFieldAut_not_mem_semilinearAutGroup h hn
    have h2 := hEn.conj_mem _ hy (ρ g₀)
    rwa [show ρ g₀ * ((ρ g₀)⁻¹ * graphFieldAut h n * ρ g₀) * (ρ g₀)⁻¹ = graphFieldAut h n
      by group] at h2
  exact exists_normal_index_two_of_not_fused_of_sylow_le ht htY htnY ⟨S, hS.trans hNle⟩ hfus

theorem false_of_simple_globalGraphField [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hn : 3 ≤ n) {t : G} (ht : orderOf t = 2) (htG₀ : t ∈ normalizer (G₀ : Set G))
    (ψ : G₀ ⧸ center G₀ ≃* projectiveSL n K)
    (hψt : ∀ x : G₀, ψ ((G₀.normalizerMonoidHom ⟨t, htG₀⟩ x : G₀) : G₀ ⧸ center G₀) =
      graphFieldAut h n (ψ (x : G₀ ⧸ center G₀)))
    (huniq : ∀ g : G, g⁻¹ * t * g ∈ normalizer (G₀ : Set G) → g ∈ normalizer (G₀ : Set G)) :
    False :=
  CFSG.SeitzReduction.RankOne.Endings.not_exists_normal_index_two hnonab
    (exists_normal_index_two_of_globalGraphField h hn ht htG₀ ψ hψt huniq)

end Endgame

section FieldRow

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {m : ℕ}

theorem false_of_globalGraphField (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) (hm : 2 ≤ m) (hnq : (m + 1, 2 ^ f) ≠ (3, 2))
    (e : L ≃* unitaryPSU h (m + 1)) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hTD : GraphFieldCoreTypeDet h (m + 1)) {G₀ : Subgroup G}
    (hG₀ : G₀ = ⨆ i : Fin m, pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1))))
    (hq : CFSG.IsQuasisimple G₀) (htG₀ : t ∈ normalizer (G₀ : Set G))
    (ψ : G₀ ⧸ center G₀ ≃* projectiveSL (m + 1) K)
    (hψt : ∀ x : G₀, ψ ((G₀.normalizerMonoidHom ⟨t, htG₀⟩ x : G₀) : G₀ ⧸ center G₀) =
      graphFieldAut h (m + 1) (ψ (x : G₀ ⧸ center G₀))) : False := by
  have := hset.simple
  exact false_of_simple_globalGraphField h hset.nonab (by omega) ht htG₀ ψ hψt
    (unique_of_graphFieldCoreTypeDet h hset hOut hm hnq e ht hKt hTD hG₀ hq ψ)

theorem false_of_graphFieldNeighbourParam_unitaryRootTorus (hset : SeitzSetting G L)
    (e : L ≃* unitaryPSU h (m + 1)) (hm : 5 ≤ m) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hTD : GraphFieldCoreTypeDet h (m + 1))
    (hparam : ∀ (a b : Fin (m + 1)) (hab : a ≠ b),
      Nonempty (GraphFieldNeighbourParam e t (modelToG e (unitaryRootTorus h hab))
        ({a, b}ᶜ : Finset (Fin (m + 1))))) : False := by
  have htC := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hnq : (m + 1, 2 ^ f) ≠ (3, 2) := fun h' => by
    have := congrArg Prod.fst h'
    simp only at this
    omega
  obtain ⟨-, htG₀, hq, -, ψ, -, hψt⟩ :=
    exists_globalGraphField_unitaryRootTorus hset e hm htC ht hparam rfl
  exact false_of_globalGraphField h hset.standardSetting
    (isSolvable_outer_of_mulEquiv h (by omega) hnq e) (by omega) hnq e ht hKt hTD rfl hq htG₀ ψ
    hψt

theorem false_of_graphFieldNeighbourParam_unitaryRootTorus_of_nonempty (hset : SeitzSetting G L)
    (e : L ≃* unitaryPSU h (m + 1)) (hm : 5 ≤ m) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hTD : GraphFieldCoreTypeDet h (m + 1)) {a b : Fin (m + 1)} (hab : a ≠ b)
    (hP : Nonempty (GraphFieldNeighbourParam e t (modelToG e (unitaryRootTorus h hab))
      ({a, b}ᶜ : Finset (Fin (m + 1))))) : False :=
  false_of_graphFieldNeighbourParam_unitaryRootTorus h hset e hm ht hKt hTD fun _ _ hab' =>
    nonempty_graphFieldNeighbourParam_rootTorus_of_nonempty
      (LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt) hab hP hab'

end FieldRow

end CFSG.SeitzReduction.UnitaryPilot
