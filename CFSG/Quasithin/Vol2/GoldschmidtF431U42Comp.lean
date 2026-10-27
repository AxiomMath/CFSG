module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42A0Set
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Am

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Quasithin CFSG.QuasithinUnique U42F431

section Iso

variable {G : Type} [Group G] {M₁ M₂ : Subgroup G}

@[expose] def isoP1
    (iso : (RankTwoAmalgam.ofSubgroups P1 P2).Iso (RankTwoAmalgam.ofSubgroups M₁ M₂)) :
    ↥P1 ≃* ↥M₁ := iso.φ1

@[expose] def isoP2
    (iso : (RankTwoAmalgam.ofSubgroups P1 P2).Iso (RankTwoAmalgam.ofSubgroups M₁ M₂)) :
    ↥P2 ≃* ↥M₂ := iso.φ2

@[expose] def isoB
    (iso : (RankTwoAmalgam.ofSubgroups P1 P2).Iso (RankTwoAmalgam.ofSubgroups M₁ M₂)) :
    ↥(P1 ⊓ P2) ≃* ↥(M₁ ⊓ M₂) := iso.φ12

theorem isoB_comm1 (iso : (RankTwoAmalgam.ofSubgroups P1 P2).Iso (RankTwoAmalgam.ofSubgroups M₁ M₂))
    (g : ↥(P1 ⊓ P2)) :
    (Subgroup.inclusion (inf_le_left : M₁ ⊓ M₂ ≤ M₁) (isoB iso g) : ↥M₁) =
      isoP1 iso (Subgroup.inclusion (inf_le_left : P1 ⊓ P2 ≤ P1) g) := iso.comm1 g

theorem isoB_comm2 (iso : (RankTwoAmalgam.ofSubgroups P1 P2).Iso (RankTwoAmalgam.ofSubgroups M₁ M₂))
    (g : ↥(P1 ⊓ P2)) :
    (Subgroup.inclusion (inf_le_right : M₁ ⊓ M₂ ≤ M₂) (isoB iso g) : ↥M₂) =
      isoP2 iso (Subgroup.inclusion (inf_le_right : P1 ⊓ P2 ≤ P2) g) := iso.comm2 g

end Iso

theorem conj_injective :
    Function.Injective (MulAut.conj : Y →* MulAut Y) := fun _ _ h =>
  toG0_injective (Gv_injective h)

@[expose] noncomputable def isoConj :
    (RankTwoAmalgam.ofSubgroups P1 P2).Iso u42Setting.α :=
  Am.isoTrans (Am.ofSubgroupsMapInj (MulAut.conj : Y →* MulAut Y) conj_injective P1 P2)
    (Am.ofSubgroupsCongr (A0_N1).symm (A0_N2).symm)

@[expose] noncomputable def isoConj1 :
    ↥P1 ≃* ↥A0.N1 := isoConj.φ1

@[expose] noncomputable def isoConj2 :
    ↥P2 ≃* ↥A0.N2 := isoConj.φ2

theorem isoConj1_apply {y : Y}
    (hy : y ∈ P1) (hN : MulAut.conj y ∈ A0.N1) : isoConj1 ⟨y, hy⟩ = ⟨MulAut.conj y, hN⟩ :=
  Subtype.ext rfl

theorem isoConj2_apply {y : Y}
    (hy : y ∈ P2) (hN : MulAut.conj y ∈ A0.N2) : isoConj2 ⟨y, hy⟩ = ⟨MulAut.conj y, hN⟩ :=
  Subtype.ext rfl

section Completion

variable {G : Type} [Group G]
  {M₁ M₂ : Subgroup G}

@[expose] noncomputable def isoN
    (iso : (RankTwoAmalgam.ofSubgroups P1 P2).Iso (RankTwoAmalgam.ofSubgroups M₁ M₂)) :
    u42Setting.α.Iso (RankTwoAmalgam.ofSubgroups M₁ M₂) :=
  Am.isoTrans (Am.isoSymm isoConj) iso

@[expose] noncomputable def betaOf
    (iso : (RankTwoAmalgam.ofSubgroups P1 P2).Iso (RankTwoAmalgam.ofSubgroups M₁ M₂)) :
    u42Setting.α.Completion ↥(M₁ ⊔ M₂) :=
  Am.precompIso (isoN iso) (Am.subCompletion M₁ M₂)

theorem betaOf_faithful
    (iso : (RankTwoAmalgam.ofSubgroups P1 P2).Iso (RankTwoAmalgam.ofSubgroups M₁ M₂)) :
    (betaOf iso).IsFaithful :=
  Am.precompIso_isFaithful _ (Am.subCompletion_isFaithful M₁ M₂)

end Completion

end CFSG.Quasithin.H13.F431.U42
