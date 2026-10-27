module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerBasic

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Inputs

@[expose] def GGStepTwoChoiceThreeInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
    ¬ GGStepTwoLinearType p t f →
      ∀ (b : G) (L₁ : Subgroup G), GGStepTwoPair p B Bs x L D J b L₁ → p = 3 →
        GGStepTwoExcThreeType L₁ →
          ∃ m ∈ ggG0 p B x L D J ⊓ Subgroup.normalizer (Bs : Set G),
            ∃ g ∈ L₁, (∃ l ∈ L₁, g * l ≠ l * g) ∧
              g ∈ Subgroup.centralizer (D.map (MulAut.conj m⁻¹).toMonoidHom : Set G) ∧
              Nat.Coprime (orderOf g) p

end Inputs

section Steps

variable {G : Type} [Group G]

theorem ggAKF_map_conj_le_centralizer {p : ℕ} {Bs D : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hDBs : D ≤ Bs) {b m : G} (hb : b ∈ Bs) (hm : m ∈ Subgroup.normalizer (Bs : Set G)) :
    D.map (MulAut.conj m⁻¹).toMonoidHom ≤ Subgroup.centralizer {b} := by
  have := hBs.1
  rintro _ ⟨d, hd, rfl⟩
  have hmem : m⁻¹ * d * m⁻¹⁻¹ ∈ Bs :=
    (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hm) d).mp (hDBs hd)
  rw [inv_inv] at hmem
  rw [Subgroup.mem_centralizer_singleton_iff]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  exact congrArg Subtype.val (mul_comm' (⟨m⁻¹ * d * m, hmem⟩ : Bs) ⟨b, hb⟩)

theorem ggStepTwoChoiceThree_of_le_centralizer [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {b : G} {L₁ : Subgroup G}
    (hpair : GGStepTwoPair p B Bs x L D J b L₁) (hp : p.Prime) {m : G}
    (hm : m ∈ ggG0 p B x L D J ⊓ Subgroup.normalizer (Bs : Set G))
    (hmL : D.map (MulAut.conj m⁻¹).toMonoidHom ≤ Subgroup.centralizer (L₁ : Set G)) :
    ∃ m ∈ ggG0 p B x L D J ⊓ Subgroup.normalizer (Bs : Set G),
      ∃ g ∈ L₁, (∃ l ∈ L₁, g * l ≠ l * g) ∧
        g ∈ Subgroup.centralizer (D.map (MulAut.conj m⁻¹).toMonoidHom : Set G) ∧
        Nat.Coprime (orderOf g) p := by
  obtain ⟨g, hgL, hgZ, hgp⟩ := ggAKF_exists_noncentral_coprime_mem hpair.2.2.1.2.2 hp
  refine ⟨m, hm, g, hgL, hgZ, ?_, hgp⟩
  rw [Subgroup.mem_centralizer_iff]
  intro e he
  exact (Subgroup.mem_centralizer_iff.mp (hmL he) g hgL).symm

end Steps

section Reductions

theorem ggStepTwoAutKThreeInput_of_choice (h : GGStepTwoChoiceThreeInput) :
    GGStepTwoAutKThreeInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx s1 hlin b L₁ hpair _ _ _ _ hp3 hT
  obtain ⟨m, hm, g, hgL, hgZ, hgE, hgp⟩ := h G p B Bs x L D J t n f ψ hctx s1 hlin b L₁ hpair hp3 hT
  obtain ⟨hmG, hmN⟩ := Subgroup.mem_inf.mp hm
  exact ⟨m, Subgroup.le_normalizer hmG,
    ggAKF_map_conj_le_centralizer hctx.bstar.2.1 hctx.d_le_bstar hpair.1 hmN, g, hgL, hgZ, hgE, hgp⟩

end Reductions

end CFSG.StandardType
