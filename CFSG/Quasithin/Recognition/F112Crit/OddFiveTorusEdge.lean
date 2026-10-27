module

public import CFSG.Quasithin.Recognition.F112Crit.OddFiveDefs
public import CFSG.Quasithin.Recognition.F112Crit.BenderCartan
public import CFSG.Quasithin.EmptyFaithful.SzF53BasGeo

public section

namespace CFSG.Quasithin.F112Crit

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open CFSG.Quasithin.MS93 (oddGen)

variable {G : Type} [Group G]

open CosetGeom (graph stab ballStab nbrs vtype γ₀ γ₁)

section Local

variable {G₀ G₁ G₂ : Subgroup G} {μ : CosetGeom G₀ G₁ G₂} {L : Subgroup G}

theorem BenderLocal.exists_smul_eq_of_ne (hL : BenderLocal μ L) {δ ε ε' : CosetGeom G₀ G₁ G₂}
    (hδ : δ ∈ nbrs μ) (hε : ε ∈ nbrs μ) (hε' : ε' ∈ nbrs μ) (h : ε ≠ δ) (h' : ε' ≠ δ) :
    ∃ g : ↥G₀, (g : G) ∈ stab μ ⊓ stab δ ∧ g • ε = ε' := by
  obtain ⟨U, hUL, -, hUδ, hUtr, -⟩ := hL.unipotent δ hδ
  obtain ⟨g, hgU, hg⟩ := hUtr ε hε ε' hε' h h'
  exact ⟨g, ⟨hL.le_stab (hUL hgU), hUδ hgU⟩, hg⟩

theorem BenderLocal.exists_swap (hL : BenderLocal μ L) {δ δ' : CosetGeom G₀ G₁ G₂}
    (hδ : δ ∈ nbrs μ) (hδ' : δ' ∈ nbrs μ) (hne : δ ≠ δ') :
    ∃ g : ↥G₀, (g : G) ∈ stab μ ∧ g • δ = δ' ∧ g • δ' = δ := by
  obtain ⟨g₁, hg₁L, hg₁⟩ := hL.trans δ hδ δ' hδ'
  have hg₁μ : (g₁ : G) ∈ stab μ := hL.le_stab hg₁L
  have hμ : g₁ • μ = μ := CosetGeom.smul_eq_of_mem_stab hg₁μ
  have hw : g₁ • δ' ∈ nbrs μ := by
    rw [← hμ]
    exact (CosetGeom.smul_adj g₁).mpr hδ'
  by_cases hwδ : g₁ • δ' = δ
  · exact ⟨g₁, hg₁μ, hg₁, hwδ⟩
  · have hwne : g₁ • δ' ≠ δ' := by
      intro h
      have h2 : g₁ • δ' = g₁ • δ := by rw [hg₁]; exact h
      exact hne (smul_left_cancel g₁ h2).symm
    obtain ⟨u, hu, hueq⟩ := BenderLocal.exists_smul_eq_of_ne hL hδ' hw hδ hwne hne
    refine ⟨u * g₁, (stab μ).mul_mem hu.1 hg₁μ, ?_, ?_⟩
    · rw [mul_smul, hg₁]
      exact CosetGeom.smul_eq_of_mem_stab hu.2
    · rw [mul_smul, hueq]

theorem IsEdgeHall.of_le [Finite G] {X : Subgroup G} {δ ν y : CosetGeom G₀ G₁ G₂}
    (hX : IsEdgeHall μ δ X) (hμ : vtype μ = false) (hδ : δ ∈ nbrs μ) (hν : vtype ν = false)
    (hy : y ∈ nbrs ν) (hXν : X ≤ stab ν) (hXy : X ≤ stab y) : IsEdgeHall ν y X := by
  obtain ⟨hXe, hXodd, k, hXk⟩ := hX
  have hcard : Nat.card (stab ν ⊓ stab y : Subgroup G) =
      Nat.card (stab μ ⊓ stab δ : Subgroup G) := by
    have key : ∀ (a : ↥G₀) (u v : CosetGeom G₀ G₁ G₂),
        u = a • γ₀ G₀ G₁ G₂ → v = a • γ₁ G₀ G₁ G₂ →
        Nat.card (stab u ⊓ stab v : Subgroup G) =
          Nat.card (stab (γ₀ G₀ G₁ G₂) ⊓ stab (γ₁ G₀ G₁ G₂) : Subgroup G) := by
      rintro a u v rfl rfl
      have hc : Nat.card ↥(conjSub (a : G) (stab (γ₀ G₀ G₁ G₂) ⊓ stab (γ₁ G₀ G₁ G₂))) =
          Nat.card (stab (γ₀ G₀ G₁ G₂) ⊓ stab (γ₁ G₀ G₁ G₂) : Subgroup G) :=
        Subgroup.card_map_of_injective (f := (MulAut.conj (a : G)).toMonoidHom)
          (MulAut.conj (a : G)).injective
      rw [CosetGeom.stab_smul, CosetGeom.stab_smul, ← conjSub_inf, hc]
    obtain ⟨g, hμg, hδg⟩ := exists_edge_conj hμ hδ
    obtain ⟨h, hνh, hyh⟩ := exists_edge_conj hν hy
    rw [key g μ δ hμg hδg, key h ν y hνh hyh]
  have h1 : X.relIndex (stab μ ⊓ stab δ) * Nat.card X =
      Nat.card (stab μ ⊓ stab δ : Subgroup G) := by
    have h := Subgroup.relIndex_mul_card X (stab μ ⊓ stab δ)
    rwa [inf_eq_left.mpr hXe] at h
  have h2 : X.relIndex (stab ν ⊓ stab y) * Nat.card X =
      Nat.card (stab ν ⊓ stab y : Subgroup G) := by
    have h := Subgroup.relIndex_mul_card X (stab ν ⊓ stab y)
    rwa [inf_eq_left.mpr (le_inf hXν hXy)] at h
  have heq : X.relIndex (stab ν ⊓ stab y) = X.relIndex (stab μ ⊓ stab δ) :=
    Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥X)) (by rw [h2, h1, hcard])
  exact ⟨le_inf hXν hXy, hXodd, k, heq.trans hXk⟩

end Local

namespace Setting

variable [Finite G] {L₁ L₂ S Z : Subgroup G}

theorem exists_benderLocal (hs : Setting L₁ L₂ S Z) {q i : ℕ}
    (hK : IsBenderQuot (oTwoQuot ↥L₂) q i)
    {ν : CosetGeom (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S)} (hν : vtype ν = false) :
    ∃ L : Subgroup G, BenderLocal ν L := by
  obtain ⟨g, rfl⟩ := CosetGeom.exists_smul_eq_γ₀ hν
  exact ⟨_, (hs.benderLocal hK).smul g⟩

theorem exists_benderLocal_cartanLocal (hs : Setting L₁ L₂ S Z) {q i : ℕ}
    (hK : IsBenderQuot (oTwoQuot ↥L₂) q i) (hC : IsCartanQuot (oTwoQuot ↥L₂))
    {ν : CosetGeom (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S)} (hν : vtype ν = false) :
    ∃ L : Subgroup G, BenderLocal ν L ∧ CartanLocal ν L := by
  obtain ⟨g, rfl⟩ := CosetGeom.exists_smul_eq_γ₀ hν
  exact ⟨_, (hs.benderLocal hK).smul g, (hs.cartanLocal hK hC).smul g⟩

theorem exists_nbrs_ne (hs : Setting L₁ L₂ S Z)
    {ν y : CosetGeom (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S)} (hν : vtype ν = false)
    (hy : y ∈ nbrs ν) : ∃ y' ∈ nbrs ν, y' ≠ y := by
  have hgt : 1 < Nat.card (nbrs ν) := by
    rw [CosetGeom.card_nbrs_eq_relIndex_geom hy]
    obtain ⟨g, hνg, hyg⟩ := exists_edge_conj hν hy
    have hstab : stab ν = conjSub (g : G)
        (stab (γ₀ (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S))) := by
      rw [hνg, CosetGeom.stab_smul]
    have hedge : stab ν ⊓ stab y = conjSub (g : G)
        (stab (γ₀ (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S)) ⊓
          stab (γ₁ (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S))) := by
      rw [hνg, hyg, CosetGeom.stab_smul, CosetGeom.stab_smul, ← conjSub_inf]
    have hmap : (conjSub (g : G)
        (stab (γ₀ (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S)) ⊓
          stab (γ₁ (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S)))).relIndex
        (conjSub (g : G) (stab (γ₀ (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S)))) =
        (stab (γ₀ (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S)) ⊓
          stab (γ₁ (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S))).relIndex
          (stab (γ₀ (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S))) :=
      Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj (g : G)).injective
    rw [hedge, hstab, hmap, BenderLocalOf.stab_γ₀_eq hs, BenderLocalOf.stab_γ₁_eq hs,
      F112W.inf_alpha_beta hs.hyp]
    have hlt : bigB L₁ L₂ S < P₂ L₁ L₂ S := F112W.bigB_lt_parabolic' hs.hyp
    have hne : (bigB L₁ L₂ S).relIndex (P₂ L₁ L₂ S) ≠ 1 := by
      intro h
      exact hlt.ne (le_antisymm hlt.le (Subgroup.relIndex_eq_one.mp h))
    have hpos : 0 < (bigB L₁ L₂ S).relIndex (P₂ L₁ L₂ S) := by
      by_contra h
      have h0 : (bigB L₁ L₂ S).relIndex (P₂ L₁ L₂ S) = 0 := Nat.eq_zero_of_not_pos h
      have hc := Subgroup.relIndex_mul_card (bigB L₁ L₂ S) (P₂ L₁ L₂ S)
      rw [h0, zero_mul] at hc
      exact (Nat.card_pos (α := ↥(P₂ L₁ L₂ S))).ne' hc.symm
    omega
  by_contra h
  push Not at h
  have hsub : nbrs ν ⊆ {y} := fun z hz => by
    rw [Set.mem_singleton_iff]
    exact h z hz
  have heq : nbrs ν = {y} := Set.Subset.antisymm hsub (Set.singleton_subset_iff.mpr hy)
  have h1 : Nat.card (nbrs ν) = 1 := by
    rw [heq]
    exact Nat.card_unique
  omega

theorem exists_normal_two_edge (hs : Setting L₁ L₂ S Z)
    {ν y : CosetGeom (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S)} (hν : vtype ν = false)
    (hy : y ∈ nbrs ν) :
    ∃ T : Subgroup G, T ≤ stab ν ⊓ stab y ∧
      stab ν ⊓ stab y ≤ Subgroup.normalizer (T : Set G) ∧ IsPGroup 2 T ∧
      Odd (T.relIndex (stab ν ⊓ stab y)) := by
  have hS2 : IsPGroup 2 S := hs.hyp.hyp.h2.pgroup
  have hSle : S ≤ stab (γ₀ (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S)) ⊓
      stab (γ₁ (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S)) := by
    rw [BenderLocalOf.stab_γ₀_eq hs, BenderLocalOf.stab_γ₁_eq hs]
    exact le_inf (BenderLocalOf.S_le_bigB.trans BenderLocalOf.bigB_le_P₂)
      (hs.S_le.trans le_sup_left)
  have hSN : stab (γ₀ (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S)) ⊓
      stab (γ₁ (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S)) ≤
      Subgroup.normalizer (S : Set G) := by
    rw [BenderLocalOf.stab_γ₀_eq hs, BenderLocalOf.stab_γ₁_eq hs, F112W.inf_alpha_beta hs.hyp]
    have h := (F1.bigB_le_normalizer_sylow hs.hyp).1
    rwa [inf_eq_left.mpr hs.S_le] at h
  have hSodd : Odd (S.relIndex (stab (γ₀ (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S)) ⊓
      stab (γ₁ (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S)))) := by
    rw [BenderLocalOf.stab_γ₀_eq hs, BenderLocalOf.stab_γ₁_eq hs, F112W.inf_alpha_beta hs.hyp]
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (F112W.isSylowTwoOf_bigB hs.hyp).2.2)
  obtain ⟨g, hνg, hyg⟩ := exists_edge_conj hν hy
  have hedge : stab ν ⊓ stab y = conjSub (g : G)
      (stab (γ₀ (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S)) ⊓
        stab (γ₁ (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S))) := by
    rw [hνg, hyg, CosetGeom.stab_smul, CosetGeom.stab_smul, ← conjSub_inf]
  have hmap : (conjSub (g : G) S).relIndex (conjSub (g : G)
      (stab (γ₀ (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S)) ⊓
        stab (γ₁ (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S)))) =
      S.relIndex (stab (γ₀ (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S)) ⊓
        stab (γ₁ (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S))) :=
    Subgroup.relIndex_map_map_of_injective S _ (MulAut.conj (g : G)).injective
  refine ⟨conjSub (g : G) S, ?_, ?_, F7.isPGroup_conjSub hS2, ?_⟩
  · rw [hedge]
    exact conjSub_mono _ hSle
  · rw [hedge]
    exact conjSub_le_normalizer hSN
  · rw [hedge, hmap]
    exact hSodd

end Setting

end CFSG.Quasithin.F112Crit

end
