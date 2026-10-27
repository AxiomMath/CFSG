module

public import CFSG.LocalAnalysis.StandardType.GGHalfInnerNbr
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSpProofHalf
public import CFSG.LocalAnalysis.StandardType.GGCompatNbrSomeDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix GGHalf

namespace GGHalfCtx

theorem secFiveData_of_alphaInner
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J K : Subgroup G} {m : ℕ} {y : G}
    {φ₁ φ₂ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 →* G}
    (h : GGHalfCtx p B Bs x L D J m y K φ₁ φ₂) (hα : GGHalfAlphaInner φ₁ φ₂)
    (hRig : GGLabelRigidInput) (hTP : GGNbrTablePNbrInputOn GGRegimeAm2) (hLB : GGLBalanceInput)
    (hKG : GGHalfNbrCentInput) : GGSecFiveData p B x L D J := by
  have hm3 : 3 ≤ m := by have := h.nbr.2.2.1; omega
  have hK1 : GGHalfNormSL014 φ₁ φ₂ := h.normSL014_of_alphaInner_of_three_le hm3 hα
  obtain ⟨hT, hKle⟩ := h.twoEndNodes hK1
  have hK0 : K ≤ ggG0 p B x L D J := le_ggG0_of_ggNbr h.nbr.2.2.2.2.1
  have hT₁K : endT₁ φ₂ ∈ K := by
    rw [← h.coords.range₂]
    exact MonoidHom.mem_range.mpr ⟨weylRep (m + 1 + 1) F2 ⟨m, by omega⟩, rfl⟩
  have hT₂K : endT₂ φ₂ ∈ K := by
    rw [← h.coords.range₂]
    exact MonoidHom.mem_range.mpr ⟨weylRep (m + 1 + 1) F2 ⟨m + 1, by omega⟩, rfl⟩
  have hker : φ₁.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) := by
    rw [(MonoidHom.ker_eq_bot_iff φ₁).mpr h.coords.inj₁]
    exact bot_le
  have hnbr : ∀ (y' : G) (K' : Subgroup G), GGNbr p B x D J y' K' →
      K' ≤ L ⊔ L.map (MulAut.conj (endT₁ φ₂)).toMonoidHom ⊔
        L.map (MulAut.conj (endT₂ φ₂ * endT₁ φ₂)).toMonoidHom ⊔
          L.map (MulAut.conj (endT₁ φ₂ * endT₂ φ₂ * endT₁ φ₂)).toMonoidHom := by
    intro y' K' hK'
    rw [nbr_eq_of_alphaInner h hα hRig hTP hLB hKG hK']
    exact hKle
  exact Or.inl ⟨m + 1 + 1 + 1 + 1, m + 1 + 1 + 1, 1, by omega, by omega, le_rfl,
    ggSecFiveTypeA_of_twoEndNodes (n := m + 1 + 1) (by omega) le_rfl φ₁ h.coords.range₁ hker hT
      (hK0 hT₁K) (hK0 hT₂K) hnbr⟩

theorem secFiveCompat_of_alphaInner
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J K : Subgroup G} {m : ℕ} {y : G}
    {φ₁ φ₂ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 →* G}
    (h : GGHalfCtx p B Bs x L D J m y K φ₁ φ₂) (hα : GGHalfAlphaInner φ₁ φ₂)
    (hRig : GGLabelRigidInput) (hTP : GGNbrTablePNbrInputOn GGRegimeAm2) (hLB : GGLBalanceInput)
    (hKG : GGHalfNbrCentInput) : GGSecFiveCompat p B x L D J := by
  have hm3 : 3 ≤ m := by have := h.nbr.2.2.1; omega
  have hK1 : GGHalfNormSL014 φ₁ φ₂ := h.normSL014_of_alphaInner_of_three_le hm3 hα
  obtain ⟨hT, hKle⟩ := h.twoEndNodes hK1
  have hK0 : K ≤ ggG0 p B x L D J := le_ggG0_of_ggNbr h.nbr.2.2.2.2.1
  have hT₁K : endT₁ φ₂ ∈ K := by
    rw [← h.coords.range₂]
    exact MonoidHom.mem_range.mpr ⟨weylRep (m + 1 + 1) F2 ⟨m, by omega⟩, rfl⟩
  have hT₂K : endT₂ φ₂ ∈ K := by
    rw [← h.coords.range₂]
    exact MonoidHom.mem_range.mpr ⟨weylRep (m + 1 + 1) F2 ⟨m + 1, by omega⟩, rfl⟩
  have hker : φ₁.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) := by
    rw [(MonoidHom.ker_eq_bot_iff φ₁).mpr h.coords.inj₁]
    exact bot_le
  have hnbr : ∀ (y' : G) (K' : Subgroup G), GGNbr p B x D J y' K' →
      K' ≤ L ⊔ L.map (MulAut.conj (endT₁ φ₂)).toMonoidHom ⊔
        L.map (MulAut.conj (endT₂ φ₂ * endT₁ φ₂)).toMonoidHom ⊔
          L.map (MulAut.conj (endT₁ φ₂ * endT₂ φ₂ * endT₁ φ₂)).toMonoidHom := by
    intro y' K' hK'
    rw [nbr_eq_of_alphaInner h hα hRig hTP hLB hKG hK']
    exact hKle
  obtain ⟨ψ₀, hpres, hcomp⟩ := ggSecFiveCompat_of_twoEndNodesAt (n := m + 1 + 1) (by omega)
    le_rfl φ₁ h.coords.range₁ hker hT (le_ggG0_left p B x L D J) (hK0 hT₁K) (hK0 hT₂K)
    (le_sup_left.trans (le_sup_left.trans le_sup_left)) hnbr
  exact ⟨.PSL, m + 1 + 1 + 1 + 1 + 1, 1, ψ₀, hpres, L, Or.inl rfl, hcomp⟩

end GGHalfCtx

end CFSG.StandardType

end
