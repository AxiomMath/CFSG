module

public import CFSG.Timmesfeld.ARS.CaseHRootGroups

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace CaseH

section Interval

variable (h : Hyp G R) (hH : SigmaEqLambda R)
include h hH

theorem card_M_inf_M_le {X Y Z : Subgroup G} (hX : X ∈ R) (hY : Y ∈ omegaSet R X)
    (hZ : Z ∈ lambdaStar R X Y) :
    Nat.card ↥(M R Z ⊓ M R ⁅Y, Z⁆) ≤
      Nat.card X * (Nat.card X * ((linesThrough R X).ncard - 1)) := by
  classical
  have := h.finite
  have hR := h.root
  have hYR : Y ∈ R := hY.1
  have hZR : Z ∈ R := hZ.2.1
  have hsYZ : Special R Y Z := hZ.2.2
  obtain ⟨hZ'Y, hZ'Z⟩ := commutator_mem_lambdaSet h hYR hZR hsYZ
  have hZ'R : ⁅Y, Z⁆ ∈ R := hZ'Y.1.1
  have hYZ' : Y ∈ lambdaSet R ⁅Y, Z⁆ := mem_lambdaSet_comm hYR hZ'Y
  have hq : ∀ W ∈ R, Nat.card W = Nat.card X := fun W hW => hR.card_eq hW hX
  have hLW : ∀ W ∈ R, (linesThrough R W).ncard = (linesThrough R X).ncard := fun W hW =>
    ncard_linesThrough_eq h hX hW
  have hΛ : ∀ W ∈ R, (lambdaSet R W).ncard = (linesThrough R X).ncard * Nat.card X := fun W hW => by
    rw [ncard_lambdaSet h hW, hLW W hW, hq W hW]
  have hYψ : Y ∈ psiSet R Z := ⟨hYR, hsYZ.symm⟩
  have hset := setOf_omegaSet_lambdaSet h hH hZR hYψ
  obtain ⟨-, hZYY⟩ := commutator_mem_lambdaSet h hZR hYR hsYZ.symm
  have hL2 : 2 ≤ (linesThrough R X).ncard := by
    have hΩ := ncard_omegaSet h hH hX rfl rfl
    have hpos : 0 < (omegaSet R X).ncard := (Set.ncard_pos (Set.toFinite _)).2 ⟨Y, hY⟩
    by_contra hlt
    rw [hΩ, show (linesThrough R X).ncard - 1 = 0 by omega] at hpos
    simp at hpos
  obtain ⟨B, hBΩ, hYB⟩ : {B | B ∈ omegaSet R Z ∧ Y ∈ lambdaSet R B}.Nonempty := by
    rw [hset, ← Set.ncard_pos (Set.toFinite _), ncard_lambdaSet_diff_pointsOn' h hYR hZYY,
      hΛ Y hYR, hq Y hYR]
    have : 0 < Nat.card X := Nat.card_pos
    have h2 := Nat.mul_le_mul_right (Nat.card X) hL2
    generalize (linesThrough R X).ncard * Nat.card X = m at h2 ⊢
    omega
  have hBY : B ∈ lambdaSet R Y := mem_lambdaSet_comm hBΩ.1 hYB
  have hBZ' : B ∉ lambdaSet R ⁅Y, Z⁆ := fun hl =>
    notMem_lambdaSet_of_opposite h hZR hBΩ.2 hZ'Z (mem_lambdaSet_comm hZ'R hl)
  have hBne : B ≠ ⁅Y, Z⁆ := by
    rintro rfl
    exact hBΩ.2.not_commuting (hR.ne_bot Z hZR) hZ'Z.1.2.2
  obtain ⟨hsZ'B, hcZ'B⟩ := special_of_mem_lambdaSet h hH hZ'R hYZ' hBY hBZ' hBne
  let f : ↥(M R Z ⊓ M R ⁅Y, Z⁆) → Subgroup G := fun g => conjSub B (g : G)
  have hfinj : Function.Injective f := fun g g' e => by
    have := orbitMap_injective h hZR hBΩ (a₁ := ⟨g, g.2.1⟩) (a₂ := ⟨g', g'.2.1⟩) e
    exact Subtype.ext (congrArg (fun m : M R Z => (m : G)) this)
  have hmapsto : ∀ x ∈ M R ⁅Y, Z⁆, conjSub B x ∈
      {C | C ∈ psiSet R ⁅Y, Z⁆ ∧ ⁅⁅Y, Z⁆, C⁆ ≤ ⁅Y, Z⁆ ⊔ Y ∧ ⁅⁅Y, Z⁆, C⁆ ≠ ⁅Y, Z⁆} := by
    intro x hx
    have hxZ' : conjSub ⁅Y, Z⁆ x = ⁅Y, Z⁆ := conjSub_eq_self_iff.2 ((isPGroup_M hR hZ'R).2.1 hx)
    have hsp := Sec3.special_conjSub hR hsZ'B x
    rw [hxZ'] at hsp
    have hc : ⁅⁅Y, Z⁆, conjSub B x⁆ = conjSub Y x := by
      calc ⁅⁅Y, Z⁆, conjSub B x⁆ = ⁅conjSub ⁅Y, Z⁆ x, conjSub B x⁆ := by rw [hxZ']
        _ = conjSub ⁅⁅Y, Z⁆, B⁆ x := (Subgroup.map_commutator _ _ _).symm
        _ = conjSub Y x := by rw [hcZ'B]
    refine ⟨⟨hR.conjSub_mem hBΩ.1 _, hsp⟩, ?_, ?_⟩
    · rw [hc, ← conjSub_sup_eq_of_mem_M h hZ'R hYZ' hx]
      exact Subgroup.map_mono le_sup_right
    · rw [hc]
      intro e
      apply hZ'Y.1.2.1
      have h1 : Y = conjSub (conjSub Y x) x⁻¹ := (Plane.conjSub_conjSub_inv Y x).symm
      have h2 : conjSub ⁅Y, Z⁆ x⁻¹ = ⁅Y, Z⁆ := by
        conv_lhs => rw [← hxZ']
        exact Plane.conjSub_conjSub_inv _ x
      rw [e, h2] at h1
      exact h1.symm
  have hrange : Set.range f ⊆
      {C | C ∈ psiSet R ⁅Y, Z⁆ ∧ ⁅⁅Y, Z⁆, C⁆ ≤ ⁅Y, Z⁆ ⊔ Y ∧ ⁅⁅Y, Z⁆, C⁆ ≠ ⁅Y, Z⁆} := by
    rintro _ ⟨g, rfl⟩
    exact hmapsto g g.2.2
  have hcard := Set.ncard_le_ncard hrange (Set.toFinite _)
  rw [ncard_setOf_psiSet_le_sup h hH hZ'R hYZ', hΛ _ hZ'R, hq _ hZ'R, ← Nat.card_coe_set_eq,
    Nat.card_range_of_injective hfinj] at hcard
  calc Nat.card ↥(M R Z ⊓ M R ⁅Y, Z⁆)
      ≤ Nat.card X * ((linesThrough R X).ncard * Nat.card X - Nat.card X) := hcard
    _ = Nat.card X * (Nat.card X * ((linesThrough R X).ncard - 1)) := by
        rw [Nat.mul_sub_one, mul_comm ((linesThrough R X).ncard)]

theorem injective_mul_shortRoot (hT : MTransitive R) {X Y Z : Subgroup G} (hX : X ∈ R)
    (hY : Y ∈ omegaSet R X) (hZ : Z ∈ lambdaStar R X Y) :
    Function.Injective fun p : ↥Z × ↥⁅Y, Z⁆ × ↥(shortRoot R X Y Z) =>
      (p.1 : G) * p.2.1 * p.2.2 := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hYR : Y ∈ R := hY.1
  have hZR : Z ∈ R := hZ.2.1
  have hop : Opposite X Y := hY.2
  obtain ⟨hZ'Y, hZ'Z⟩ := commutator_mem_lambdaSet h hYR hZR hZ.2.2
  have hZ'R : ⁅Y, Z⁆ ∈ R := hZ'Y.1.1
  have hZ'X : ⁅Y, Z⁆ ∉ lambdaSet R X := fun hl => notMem_lambdaSet_of_opposite h hX hop hl hZ'Y
  have hZ'ne : ⁅Y, Z⁆ ≠ X := by
    intro e
    rw [e] at hZ'Y
    exact hop.not_commuting (hR.ne_bot X hX) hZ'Y.1.2.2.symm
  have hsXZ' := (special_of_mem_lambdaSet h hH hX hZ.1 hZ'Z hZ'X hZ'ne).1
  have hcZZ' : Commuting Z ⁅Y, Z⁆ := hZ'Z.1.2.2
  have hcUZ : Commuting (shortRoot R X Y Z) Z := commuting_shortRoot_mid h hZR
  have hcUZ' : Commuting (shortRoot R X Y Z) ⁅Y, Z⁆ := commuting_shortRoot_mid' h hZR
  have hU : ∀ (z : G), z ∈ Z → ∀ z' ∈ ⁅Y, Z⁆, z * z' ∈ shortRoot R X Y Z → z * z' = 1 := by
    intro z hz z' hz' hzu
    have hzX : conjSub X z = X := conjSub_of_forall_commute fun x hx =>
      (hZ.1.1.2.2 x hx z hz).symm
    have huX : conjSub X (z * z') = X := conjSub_left_of_mem_shortRoot hzu
    have hz'X : conjSub X z' = X := by
      have : conjSub X z' = conjSub (conjSub X (z * z')) z⁻¹ := by
        rw [← conjSub_mul]
        congr 1
        group
      rw [this, huX]
      conv_lhs => rw [← hzX]
      exact Plane.conjSub_conjSub_inv X z
    have hz'1 : z' = 1 := by
      by_contra hz'1
      exact Sec3.conjSub_ne_of_special hR hiso hZ'R hX hsXZ'.symm hz' hz'1 hz'X
    subst hz'1
    rw [mul_one] at hzu ⊢
    obtain ⟨-, -, hreg⟩ := shortRoot_moufang_of h hH hT hX hY hZ
    obtain ⟨W, hW, hWZ⟩ : ∃ W ∈ linesThrough R X, ¬ Z ≤ W := by
      have hL2 : 2 ≤ (linesThrough R X).ncard := by
        have hΩ := ncard_omegaSet h hH hX rfl rfl
        have hpos : 0 < (omegaSet R X).ncard := (Set.ncard_pos (Set.toFinite _)).2 ⟨Y, hY⟩
        by_contra hlt
        rw [hΩ, show (linesThrough R X).ncard - 1 = 0 by omega] at hpos
        simp at hpos
      by_contra hno
      push Not at hno
      have hsub : linesThrough R X ⊆ {X ⊔ Z} := fun W hW =>
        eq_sup_of_le h hX hZ.1 hW (hno W hW)
      have := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [Set.ncard_singleton] at this
      omega
    obtain ⟨D, hD, rfl⟩ := (mem_linesThrough_iff h hX).1 hW
    have hzW : conjSub (X ⊔ D) z = X ⊔ D := conjSub_sup_eq_of_mem_M h hX hD (QD.le_M hZ.1 hz)
    obtain ⟨u₀, -, huniq⟩ := hreg (X ⊔ D) hW (X ⊔ D) hW hWZ hWZ
    have h1 := huniq ⟨z, hzu⟩ hzW
    have h2 := huniq 1 (conjSub_one _)
    exact congrArg Subtype.val (h1.trans h2.symm)
  rintro ⟨⟨z₁, hz₁⟩, ⟨z₁', hz₁'⟩, ⟨u₁, hu₁⟩⟩ ⟨⟨z₂, hz₂⟩, ⟨z₂', hz₂'⟩, ⟨u₂, hu₂⟩⟩ e
  simp only at e
  have key0 : z₂'⁻¹ * z₂⁻¹ * z₁ * z₁' = u₂ * u₁⁻¹ := by
    calc z₂'⁻¹ * z₂⁻¹ * z₁ * z₁' = z₂'⁻¹ * z₂⁻¹ * (z₁ * z₁' * u₁) * u₁⁻¹ := by group
      _ = z₂'⁻¹ * z₂⁻¹ * (z₂ * z₂' * u₂) * u₁⁻¹ := by rw [e]
      _ = u₂ * u₁⁻¹ := by group
  have hcomm : Commute z₂'⁻¹ (z₂⁻¹ * z₁) :=
    ((hcZZ' _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hz₂) hz₁) _ hz₂').inv_right).symm
  have key : (z₂⁻¹ * z₁) * (z₂'⁻¹ * z₁') = u₂ * u₁⁻¹ := by
    calc (z₂⁻¹ * z₁) * (z₂'⁻¹ * z₁') = (z₂'⁻¹ * (z₂⁻¹ * z₁)) * z₁' := by
          rw [hcomm.eq]; group
      _ = z₂'⁻¹ * z₂⁻¹ * z₁ * z₁' := by group
      _ = u₂ * u₁⁻¹ := key0
  have hmem : (z₂⁻¹ * z₁) * (z₂'⁻¹ * z₁') ∈ shortRoot R X Y Z := by
    rw [key]
    exact Subgroup.mul_mem _ hu₂ (Subgroup.inv_mem _ hu₁)
  have h1 := hU _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hz₂) hz₁) _
    (Subgroup.mul_mem _ (Subgroup.inv_mem _ hz₂') hz₁') hmem
  have hZZ' : Z ⊓ ⁅Y, Z⁆ = ⊥ := inf_eq_bot hR hiso hZR hZ'R hZ'Z.1.2.1.symm
  have h2 : z₂⁻¹ * z₁ = (z₂'⁻¹ * z₁')⁻¹ := eq_inv_of_mul_eq_one_left h1
  have h3 : z₂⁻¹ * z₁ ∈ Z ⊓ ⁅Y, Z⁆ := ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hz₂) hz₁,
    h2 ▸ Subgroup.inv_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hz₂') hz₁')⟩
  rw [hZZ', Subgroup.mem_bot] at h3
  have hz : z₁ = z₂ := (inv_mul_eq_one.mp h3).symm
  have hz' : z₁' = z₂' := by
    rw [h3, eq_comm, inv_eq_one] at h2
    exact (inv_mul_eq_one.mp h2).symm
  have hu : u₁ = u₂ := by
    rw [hz, hz'] at e
    exact mul_left_cancel e
  subst hz hz' hu
  rfl

theorem M_inf_M (hT : MTransitive R) {X Y Z : Subgroup G} (hX : X ∈ R)
    (h3 : 3 ≤ (linesThrough R X).ncard) (hY : Y ∈ omegaSet R X) (hZ : Z ∈ lambdaStar R X Y) {g : G}
    (hg : g ∈ M R Z ⊓ M R ⁅Y, Z⁆) :
    ∃ p : ↥Z × ↥⁅Y, Z⁆ × ↥(shortRoot R X Y Z), (p.1 : G) * p.2.1 * p.2.2 = g := by
  classical
  have := h.finite
  have hR := h.root
  obtain ⟨hZ'Y, hZ'Z⟩ := commutator_mem_lambdaSet h hY.1 hZ.2.1 hZ.2.2
  have hZ'R : ⁅Y, Z⁆ ∈ R := hZ'Y.1.1
  have hinj := injective_mul_shortRoot h hH hT hX hY hZ
  have hU' : shortRoot R X Y Z ≤ M R ⁅Y, Z⁆ := by
    rw [shortRoot_eq_shortRoot h hH hT hX h3 hY hZ]
    exact shortRoot_le_M _ _ _
  have hmem : ∀ p : ↥Z × ↥⁅Y, Z⁆ × ↥(shortRoot R X Y Z),
      (p.1 : G) * p.2.1 * p.2.2 ∈ M R Z ⊓ M R ⁅Y, Z⁆ := fun p =>
    ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ (QD.le_M_self p.1.2) (QD.le_M hZ'Z p.2.1.2))
        p.2.2.2.2,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (QD.le_M (mem_lambdaSet_comm hZ.2.1 hZ'Z) p.1.2)
        (QD.le_M_self p.2.1.2)) (hU' p.2.2.2)⟩
  let f : ↥Z × ↥⁅Y, Z⁆ × ↥(shortRoot R X Y Z) → ↥(M R Z ⊓ M R ⁅Y, Z⁆) := fun p =>
    ⟨_, hmem p⟩
  have hfinj : Function.Injective f := fun p p' e => hinj (congrArg Subtype.val e)
  have hcard : Nat.card (↥Z × ↥⁅Y, Z⁆ × ↥(shortRoot R X Y Z)) =
      Nat.card X * (Nat.card X * ((linesThrough R X).ncard - 1)) := by
    rw [Nat.card_prod, Nat.card_prod, hR.card_eq hZ.2.1 hX, hR.card_eq hZ'R hX,
      card_shortRoot h hH hT hX hY hZ]
  have hsurj : Function.Surjective f := by
    refine ((Nat.bijective_iff_injective_and_card f).2 ⟨hfinj, le_antisymm
      (Nat.card_le_card_of_injective f hfinj) ?_⟩).2
    rw [hcard]
    exact card_M_inf_M_le h hH hX hY hZ
  obtain ⟨p, hp⟩ := hsurj ⟨g, hg⟩
  exact ⟨p, congrArg Subtype.val hp⟩

theorem M_inf_M_eq (hT : MTransitive R) {X Y Z : Subgroup G} (hX : X ∈ R)
    (h3 : 3 ≤ (linesThrough R X).ncard) (hY : Y ∈ omegaSet R X) (hZ : Z ∈ lambdaStar R X Y) :
    M R Z ⊓ M R ⁅Y, Z⁆ = Z ⊔ ⁅Y, Z⁆ ⊔ shortRoot R X Y Z := by
  obtain ⟨hZ'Y, hZ'Z⟩ := commutator_mem_lambdaSet h hY.1 hZ.2.1 hZ.2.2
  refine le_antisymm (fun g hg => ?_) (sup_le (sup_le ?_ ?_) ?_)
  · obtain ⟨p, rfl⟩ := M_inf_M h hH hT hX h3 hY hZ hg
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_sup_left
      p.1.2)) (Subgroup.mem_sup_left (Subgroup.mem_sup_right p.2.1.2)))
      (Subgroup.mem_sup_right p.2.2.2)
  · exact le_inf QD.le_M_self (QD.le_M (mem_lambdaSet_comm hZ.2.1 hZ'Z))
  · exact le_inf (QD.le_M hZ'Z) QD.le_M_self
  · refine le_inf (shortRoot_le_M _ _ _) ?_
    rw [shortRoot_eq_shortRoot h hH hT hX h3 hY hZ]
    exact shortRoot_le_M _ _ _

end Interval

end CaseH

end CFSG.Timmesfeld.ARS
