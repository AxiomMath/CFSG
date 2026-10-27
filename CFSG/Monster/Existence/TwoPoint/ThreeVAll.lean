module

public import CFSG.Monster.Existence.TwoPoint.ThreeV
public import CFSG.Monster.Existence.TwoPoint.GriessGraph
import all CFSG.Monster.Existence.TwoPointConj

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster.GMS CFSG.Blueprint.NativeSporadic

section General

variable {G : Type} [Group G]

@[expose] def commonNbrs (a α β : G) : Set G :=
  {γ | IsConj a γ ∧ IsConj a (α * γ) ∧ IsConj a (β * γ)}

@[expose] def ThreeVData (a α β : G) : Prop :=
  (∃ D : Set ↥(cent2 α β), CFSG.Blueprint.Fischer.Pair ↥(cent2 α β) D ∧
    commonNbrs a α β = Subtype.val '' D ∧
    ∀ γ ∈ D, Nat.card ↥(Subgroup.centralizer ({γ} : Set ↥(cent2 α β))) =
      2 ^ 18 * 3 ^ 9 * 5 ^ 2 * 7 * 11 * 13) ∧
  Set.ncard (commonNbrs a α β) = 31671

theorem pair_image_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {D : Set X}
    (h : CFSG.Blueprint.Fischer.Pair X D) : CFSG.Blueprint.Fischer.Pair Y (e '' D) := by
  obtain ⟨hfin, ⟨d, rfl⟩, hinv, hprod, hgen⟩ := h
  refine ⟨Finite.of_equiv X e.toEquiv, ⟨e d, ?_⟩, ?_, ?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (isConj_iff.2 (by obtain ⟨c, hc⟩ := isConj_iff.1 hx; exact ⟨e c, by
        rw [← hc]; simp⟩))
    · intro hy
      obtain ⟨c, hc⟩ := isConj_iff.1 hy
      refine ⟨e.symm y, isConj_iff.2 ⟨e.symm c, ?_⟩, by simp⟩
      apply e.injective
      simp [← hc]
  · rintro _ ⟨x, hx, rfl⟩
    rw [MulEquiv.orderOf_eq]
    exact hinv x hx
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩
    rw [← map_mul, MulEquiv.orderOf_eq]
    exact hprod x hx x' hx'
  · rw [← Subgroup.map_equiv_top e, ← hgen, MonoidHom.map_closure]
    rfl

theorem commonNbrs_conj (g a α β : G) :
    commonNbrs a (g * α * g⁻¹) (g * β * g⁻¹) = conjSet g (commonNbrs a α β) := by
  ext γ
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨g⁻¹ * γ * g, ⟨?_, ?_, ?_⟩, by group⟩
    · exact h1.trans (isConj_iff.2 ⟨g⁻¹, by group⟩)
    · have : α * (g⁻¹ * γ * g) = g⁻¹ * (g * α * g⁻¹ * γ) * g := by group
      rw [this]; exact h2.trans (isConj_iff.2 ⟨g⁻¹, by group⟩)
    · have : β * (g⁻¹ * γ * g) = g⁻¹ * (g * β * g⁻¹ * γ) * g := by group
      rw [this]; exact h3.trans (isConj_iff.2 ⟨g⁻¹, by group⟩)
  · rintro ⟨δ, ⟨h1, h2, h3⟩, rfl⟩
    refine ⟨h1.trans (isConj_iff.2 ⟨g, rfl⟩), ?_, ?_⟩
    · have : g * α * g⁻¹ * (g * δ * g⁻¹) = g * (α * δ) * g⁻¹ := by group
      rw [this]; exact h2.trans (isConj_iff.2 ⟨g, rfl⟩)
    · have : g * β * g⁻¹ * (g * δ * g⁻¹) = g * (β * δ) * g⁻¹ := by group
      rw [this]; exact h3.trans (isConj_iff.2 ⟨g, rfl⟩)

private theorem cent2ConjEquiv_apply (g α β : G) (x : ↥(cent2 α β)) :
    ((cent2ConjEquiv g α β x : ↥(cent2 (g * α * g⁻¹) (g * β * g⁻¹))) : G) = g * x * g⁻¹ := rfl

theorem ThreeVData.conj {a α β : G} (g : G) (h : ThreeVData a α β) :
    ThreeVData a (g * α * g⁻¹) (g * β * g⁻¹) := by
  obtain ⟨⟨D, hP, hN, hC⟩, hcard⟩ := h
  set e := cent2ConjEquiv g α β with he
  refine ⟨⟨e '' D, pair_image_mulEquiv e hP, ?_, ?_⟩, ?_⟩
  · rw [commonNbrs_conj, hN]
    ext γ
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨e x, ⟨x, hx, rfl⟩, (cent2ConjEquiv_apply g α β x).symm⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, ⟨x, hx, rfl⟩, cent2ConjEquiv_apply g α β x⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [← hC x hx]
    exact (Nat.card_congr (centralizerMulEquiv e x).toEquiv).symm
  · rw [commonNbrs_conj, conjSet, Set.ncard_image_of_injective _ (fun u v huv => by
      simpa using huv), hcard]

end General

section MGriess

open CFSG.Monster CFSG.Monster.Griess

theorem threeVData_MGriess
    (I : GMSInterfaces (phiB uBar) MGriess)
    (hex : OddExhaustive tGriess xGriess) (hcard : Nat.card MGriess = CFSG.Open.monsterOrder)
    (hA : IsTwoACentralizer tGriess)
    (hTh : Finite TauCeti.SporadicName.Th.Group ∧
      Nat.card TauCeti.SporadicName.Th.Group ≤ 90745943887872000) :
    ∀ α β : MGriess, IsConj tGriess α → IsConj tGriess β → IsConj (α * β) threeARep →
      ThreeVData tGriess α β := by
  have hG := gmsF1Type_MGriess_uncond
  have hCa := natCard_cent_tGriess_of hA
  obtain ⟨y, hy, hs3, -, -, h3A, h3C⟩ :=
    oddShapes_MGriess I hex hcard hCa hTh CFSG.Monster.Existence.Compat.card_nativeTh
      exists_hn_two_point'
  have hsep := oddTypesSeparated_MGriess I (hy 0).1 (hy 0).2 (hy 1).1 (hy 1).2 h3A h3C
  have hy0 : IsConj tGriess (y 0) := (hy 0).1.1
  have hfr : IsConj (fiAlpha * fiBeta) (tGriess * y 0) :=
    isConj_fiAlpha_mul_fiBeta.trans h3A.symm
  have hshape := twoPointShape_of_isConj I hG hex hsep isConj_fiAlpha isConj_fiBeta hy0 hfr hs3
  obtain ⟨ψ⟩ := hshape
  have hKeq : fiK = cent2 fiAlpha fiBeta := fiK_eq_cent2_of_card (by
    rw [Nat.card_congr ψ.toEquiv, CFSG.Sporadic.Fi23.card_Fi23])
  have htrans := (s342_three I.sls I.tableV I.leech I.tableIII I.tableIVBaby I.threeSwap
    I.leechPair hG isConj_fiAlpha isConj_fiBeta orderOf_fiAlpha_mul_fiBeta).1
  have hframe : ThreeVData tGriess fiAlpha fiBeta := by
    refine exists_threeV_nbrs hKeq ?_
    intro b₁ hb₁ b₂ hb₂
    exact htrans b₁ ⟨⟨hb₁.1, hb₁.2.1⟩, ⟨hb₁.1, hb₁.2.2⟩⟩ b₂ ⟨⟨hb₂.1, hb₂.2.1⟩, ⟨hb₂.1, hb₂.2.2⟩⟩
  intro α β hα hβ hαβ
  obtain ⟨g₁, hg₁a, hg₁y⟩ := exists_conj_pair_of_isConj I hG hex hsep isConj_fiAlpha
    isConj_fiBeta hy0 hfr
  obtain ⟨g₂, hg₂a, hg₂y⟩ := exists_conj_pair_of_isConj I hG hex hsep hα hβ hy0
    (hαβ.trans h3A.symm)
  have := hframe.conj (g₂ * g₁⁻¹)
  have e1 : g₂ * g₁⁻¹ * fiAlpha * (g₂ * g₁⁻¹)⁻¹ = α := by
    rw [← hg₁a, ← hg₂a]; group
  have e2 : g₂ * g₁⁻¹ * fiBeta * (g₂ * g₁⁻¹)⁻¹ = β := by
    rw [← hg₁y, ← hg₂y]; group
  rwa [e1, e2] at this

end MGriess

end CFSG.Monster.Existence
