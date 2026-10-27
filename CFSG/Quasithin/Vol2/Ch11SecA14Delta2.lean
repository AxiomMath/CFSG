module

public import CFSG.Quasithin.Vol2.Ch11SecA14Delta
public import CFSG.Quasithin.Vol2.Ch11SecA14Conj
public import CFSG.Quasithin.Vol2.Ch11SecAFactsDelta

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem deltaFacts (hD : FactDeltaSp4) (hD' : FactDeltaG2) (h1102 : Stmt11_0_2)
    (h : Hyp11 G T L I n) (hk : ¬ KindSL3 L (fsuV T I) n) {U₁ U₂ U₃ : Subgroup G}
    (hU₁ : IsVi T L I n 1 U₁) (hU₂ : IsVi T L I n 2 U₂) (hU₃ : IsVi T L I n 3 U₃) :
    DeltaFacts (autOn L (fsuV T I)) (autOn (T ⊓ L) (fsuV T I)) (2 ^ n)
      (U₁.subgroupOf (fsuV T I)) (U₂.subgroupOf (fsuV T I)) (U₃.subgroupOf (fsuV T I)) := by
  have hZ : ∀ g ∈ autOn L (fsuV T I),
      ∀ z ∈ (Subgroup.centralizer (L : Set G)).subgroupOf (fsuV T I), g z = z := by
    intro g hg z hz
    obtain ⟨x, hx, hxV, rfl⟩ := mem_autOn_iff.mp hg
    apply Subtype.ext
    rw [conjV_apply_coe]
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at hz
    rw [hz x hx, mul_inv_cancel_right]
  have hsq : ∀ w : ↥(fsuV T I), w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using (isElemAbelian_fsuV h).2 w w.2)
  have f₁ := isFlagW_of_isVi h hU₁
  have f₂ := isFlagW_of_isVi h hU₂
  have f₃ := isFlagW_of_isVi h hU₃
  obtain ⟨_, -, -, -, hc⟩ := h1102 G T L I n h
  rcases hc with ⟨K, _, _, hK, he, -⟩ | ⟨K, _, _, hK, -, π, hπ, -⟩ | ⟨-, -, -, -, -, hG2⟩
  · exact (hk ⟨K, inferInstance, inferInstance, hK, he⟩).elim
  · exact hD K n h.one_lt hK _ hsq _ _ π hπ hZ _ (isSylowTwoOf_P h) _ _ _ f₁ f₂ f₃
  · obtain ⟨K, _, _, hK, π, hπ⟩ := hG2
    exact hD' K n h.one_lt hK _ hsq _ _ π hπ hZ _ (isSylowTwoOf_P h) _ _ _ f₁ f₂ f₃

omit [Finite G] in
theorem lOf_le (L U : Subgroup G) : LOf L U ≤ L :=
  (iInf_le (derivedSeriesOf (L ⊓ Subgroup.normalizer (U : Set G))) 0).trans inf_le_left

theorem le_normalizer_lOf {L U X : Subgroup G} (hL : X ≤ Subgroup.normalizer (L : Set G))
    (hU : X ≤ Subgroup.normalizer (U : Set G)) :
    X ≤ Subgroup.normalizer (LOf L U : Set G) := by
  intro t ht
  refine mem_normalizer_of_map_le ?_
  rw [map_conj_lOf U (hL ht)]
  rw [map_conj_eq_of_mem_normalizer (hU ht)]

theorem isPGroup_lOf_inf (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n) (U : Subgroup G) :
    IsPGroup 2 ↥(LOf L U ⊓ Subgroup.centralizer (fsuV T I : Set G)) := by
  have hC : IsPGroup 2 ↥(L ⊓ Subgroup.centralizer (fsuV T I : Set G)) := by
    rw [centralizer_eq_pCoreOf h1102 h]
    exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
  exact hC.to_le (inf_le_inf_right _ (lOf_le L U))

theorem centralizer_pCoreOf_lOf (hD : FactDeltaSp4) (hD' : FactDeltaG2) (h1102 : Stmt11_0_2)
    (h : Hyp11 G T L I n) (hk : ¬ KindSL3 L (fsuV T I) n) {U₁ U₂ U₃ : Subgroup G}
    (hU₁ : IsVi T L I n 1 U₁) (hU₂ : IsVi T L I n 2 U₂) (hU₃ : IsVi T L I n 3 U₃) {u : G}
    (hu : u ∈ U₃) : (∀ y ∈ pCoreOf 2 (LOf L U₁), y * u * y⁻¹ = u) ↔ u ∈ U₁ := by
  have hL := L_le_normalizer_fsuV h
  have hV : u ∈ fsuV T I := IsVi.le_fsuV hU₃ hu
  have hD0 := (deltaFacts hD hD' h1102 h hk hU₁ hU₂ hU₃).1 ⟨u, hV⟩ hu
  have hX : LOf L U₁ ≤ Subgroup.normalizer (fsuV T I : Set G) := (lOf_le L U₁).trans hL
  rw [← autOn_lOf hL (IsVi.le_fsuV hU₁), ← autOn_pCoreOf hX (isPGroup_lOf_inf h1102 h U₁),
    Subgroup.mem_subgroupOf] at hD0
  rw [← hD0]
  have hPX : pCoreOf 2 (LOf L U₁) ≤ Subgroup.normalizer (fsuV T I : Set G) :=
    (Subgroup.map_subtype_le _).trans hX
  constructor
  · intro hy s hs
    obtain ⟨y, hy', hyV, rfl⟩ := mem_autOn_iff.mp hs
    apply Subtype.ext
    rw [conjV_apply_coe]
    exact hy y hy'
  · intro hs y hy
    have h1 := hs (conjV (fsuV T I) y (hPX hy)) (conjV_mem_autOn hy _)
    have h2 := congrArg Subtype.val h1
    rwa [conjV_apply_coe] at h2

end CFSG.Quasithin.Vol2.Ch11.SecA
