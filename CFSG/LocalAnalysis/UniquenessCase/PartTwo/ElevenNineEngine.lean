module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenNineFrattini
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenNineEngineCore
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ui

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace ElevenNine

theorem le_centralizer_of_perfect_of_card_le_four {X Z : Subgroup G} (hX : ⁅X, X⁆ = X)
    (hXZ : X ≤ normalizer (Z : Set G)) (hZ : Nat.card Z ≤ 4) :
    X ≤ centralizer (Z : Set G) := by
  classical
  set N := Subgroup.normalizer (Z : Set G) with hNdef
  let ρ : N →* Equiv.Perm Z := (MulAut.toPerm Z).comp Z.normalizerMonoidHom
  set X' : Subgroup N := X.subgroupOf N with hX'def
  have hX'map : X'.map N.subtype = X := by
    rw [hX'def, Subgroup.subgroupOf_map_subtype]
    exact inf_eq_left.2 hXZ
  have hX' : ⁅X', X'⁆ = X' := by
    apply Subgroup.map_injective N.subtype_injective
    rw [Subgroup.map_commutator, hX'map, hX]
  set H := X'.map ρ with hHdef
  have hH : ⁅H, H⁆ = H := by rw [hHdef, ← Subgroup.map_commutator, hX']
  obtain ⟨n, hn⟩ := (Equiv.Perm.isSolvable (α := Z) hZ).solvable
  have hle : ∀ k, H ≤ derivedSeries (Equiv.Perm Z) k := by
    intro k
    induction k with
    | zero => exact le_top
    | succ k ih =>
      rw [derivedSeries_succ, ← hH]
      exact Subgroup.commutator_mono ih ih
  have hbot : H = ⊥ := eq_bot_iff.2 (hn ▸ hle n)
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hρ : ρ ⟨x, hXZ hx⟩ = 1 := by
    have h : ρ ⟨x, hXZ hx⟩ ∈ H := ⟨⟨x, hXZ hx⟩, hx, rfl⟩
    rw [hbot] at h
    exact h
  have h1 : ρ ⟨x, hXZ hx⟩ ⟨z, hz⟩ = ⟨z, hz⟩ := by rw [hρ]; rfl
  have h2 : x * z * x⁻¹ = z := by
    have h3 : ((Z.normalizerMonoidHom ⟨x, hXZ hx⟩ ⟨z, hz⟩ : Z) : G) = z := congrArg Subtype.val h1
    rwa [Subgroup.normalizerMonoidHom_apply_apply_coe] at h3
  calc z * x = x * z * x⁻¹ * x := by rw [h2]
    _ = x * z := by group

theorem conjClosure_le_of_le {M K W : Subgroup G} (hW : M ≤ normalizer (W : Set G))
    (hKW : K ≤ W) : conjClosure M K ≤ W := by
  refine iSup₂_le fun A hA => ?_
  obtain ⟨g, hg, rfl⟩ := hA
  rintro _ ⟨z, hz, rfl⟩
  have := (mem_normalizer_iff.1 (hW hg) z).1 (hKW hz)
  simpa [MulAut.conj_apply] using this

theorem conjClosure_isPerfect {M K : Subgroup G} (hK : K ∈ calC M) :
    ⁅conjClosure M K, conjClosure M K⁆ = conjClosure M K := by
  obtain ⟨-, -, hS⟩ := conjSetOf_subset_calC_conjClosure hK
  refine le_antisymm (Subgroup.commutator_le.2 fun a ha b hb => ?_) ?_
  · rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb)
      (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hb)
  · refine iSup₂_le fun A hA => ?_
    have hAY : A ≤ conjClosure M K :=
      le_iSup₂ (f := fun A (_ : A ∈ conjSetOf M K) => A) A hA
    calc A = ⁅A, A⁆ := ((hS A hA).2.1).symm
      _ ≤ ⁅conjClosure M K, conjClosure M K⁆ := Subgroup.commutator_mono hAY hAY

theorem le_centralizer_of_not_thin (D : Data G) (h869 : F08.R869 D) {V₀ : Subgroup G}
    (hV₀n : D.M ≤ normalizer (V₀ : Set G)) (hcard : Nat.card V₀ ≤ 4 ∨ 8 ≤ Nat.card V₀)
    (h8 : 8 ≤ Nat.card V₀ →
      ¬ UniqueMax D.M (D.M ⊓ normalizer ((D.T ⊓ centralizer (V₀ : Set G) : Subgroup G) : Set G)))
    {K : Subgroup G} (hK : K ∈ calC D.M) {Y : Subgroup G} (hY : Y = conjClosure D.M K)
    (hnt : ¬ F08.Thin8 Y) : Y ≤ centralizer (V₀ : Set G) := by
  have hKM : K ≤ D.M := CFSG.Quasithin.A3.subnormal_le hK.1
  have hMC : D.M ≤ normalizer ((centralizer (V₀ : Set G) : Subgroup G) : Set G) := by
    intro m hm
    rw [mem_normalizer_iff]
    intro c
    have key : ∀ m ∈ D.M, ∀ c ∈ centralizer (V₀ : Set G),
        m * c * m⁻¹ ∈ centralizer (V₀ : Set G) := by
      intro m hm c hc
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hv' : m⁻¹ * v * m ∈ V₀ := by
        have := (mem_normalizer_iff.1 (hV₀n (D.M.inv_mem hm)) v).1 hv
        simpa using this
      have := Subgroup.mem_centralizer_iff.1 hc _ hv'
      calc v * (m * c * m⁻¹) = m * ((m⁻¹ * v * m) * c) * m⁻¹ := by group
        _ = m * (c * (m⁻¹ * v * m)) * m⁻¹ := by rw [this]
        _ = m * c * m⁻¹ * v := by group
    exact ⟨key m hm c, fun h => by simpa [mul_assoc] using key m⁻¹ (D.M.inv_mem hm) _ h⟩
  subst hY
  rcases hcard with h4 | h8'
  · have hKc : K ≤ centralizer (V₀ : Set G) :=
      le_centralizer_of_perfect_of_card_le_four hK.2.1 (hKM.trans hV₀n) h4
    exact conjClosure_le_of_le hMC hKc
  · by_cases hKW : K ≤ centralizer (V₀ : Set G)
    · exact conjClosure_le_of_le hMC hKW
    · exfalso
      obtain ⟨hYM, hMY, hprod⟩ :=
        uc22p22u_conjClosure_isProd (M := D.M) (X := D.M) (K := K) le_rfl Subgroup.le_normalizer hK
      set Y := conjClosure D.M K with hYdef
      set W : Subgroup G := Y ⊓ centralizer (V₀ : Set G) with hWdef
      set X₀ : Subgroup G :=
        Y ⊓ normalizer ((D.T ⊓ centralizer (V₀ : Set G) : Subgroup G) : Set G) with hX₀def
      have hWn : D.M ≤ normalizer (W : Set G) := by
        intro m hm
        rw [mem_normalizer_iff]
        intro x
        have h1 := mem_normalizer_iff.1 (hMY hm) x
        have h2 := mem_normalizer_iff.1 (hMC hm) x
        exact ⟨fun hx => ⟨h1.1 hx.1, h2.1 hx.2⟩, fun hx => ⟨h1.2 hx.1, h2.2 hx.2⟩⟩
      have hfr : Y ≤ W ⊔ X₀ :=
        le_centralizer_sup_normalizer_of_sylow D.sylowM hYM hMY hV₀n
      have hKnW : ¬ K ≤ W := fun h => hKW (h.trans inf_le_right)
      have hX₀sup : X₀ ⊔ pCoreOf 2 Y = Y :=
        sup_pCoreOf_eq_of_components hK hYdef hWn inf_le_left inf_le_left hfr hKnW
      have hN := h869 Y (Or.inr ⟨hYM, hMY, hprod⟩) X₀ inf_le_left hX₀sup hnt
      have hX₀M : X₀ ≤ D.M := inf_le_left.trans hYM
      have hU : UniqueMax D.M X₀ := uc22p22u_uniqueMax_of_calN D hX₀M hN
      exact h8 h8' (uc22p22u_uniqueMax_mono D (le_inf hX₀M inf_le_right) inf_le_left hU)

end ElevenNine

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
