module

public import CFSG.Quasithin.EmptyFaithful.S153E61DA
public import CFSG.Quasithin.EmptyFaithful.S153E61DG
public import CFSG.Quasithin.EmptyFaithful.S153E61DF

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits
open CFSG.Quasithin.S153E
open scoped commutatorElement Pointwise MatrixGroups

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace S153E61D

section Assembly

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {N N' : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ}

theorem star_of_dat {cx : Ctx15350 T Mc M V₁ V₂ t} (hD : S153E61.Data61 cx) (d : Dat61 cx N N' g s)
    (hel : ∀ a ∈ Pi153 T Mc M V₁ N g, ∀ b ∈ Pi153 T Mc M V₁ N g, a * b = b * a ∧ a * a = 1) :
    ∀ x ∈ Pi153 T Mc M V₁ N g, ∃ γ ∈ Igp153 T M V₁ Mc g, γ * x * γ⁻¹ ∈ UH153 T M V₁ Mc := by
  have hI : Igp153 T M V₁ Mc g = Y153 Mc M ⊔ UH153 T M V₁ Mc := d.c54.h54.one
  obtain ⟨δ, hδN', hδ3, hδfix⟩ := exists_d d
  obtain ⟨τ, hτU, hτd, ℓ, hℓV, hℓU, hℓτ⟩ := exists_tau d hδN' hδ3 hδfix
  obtain ⟨Z, hZ, hZc, hZsq, hZ2⟩ := exists_Z d.h55.1
  obtain ⟨e, heB, heU, heV⟩ := exists_E hD d hel
  have hδI : δ ∈ Y153 Mc M ⊔ UH153 T M V₁ Mc := preAut153_le hδN'
  refine star_abstract (I := Igp153 T M V₁ Mc g) (B := Pi153 T Mc M V₁ N g) (P := Pgp153 T M V₁ Mc g)
    (V := VZ T M) (U := UH153 T M V₁ Mc) (Z := Z) (d := δ) (τ := τ)
    d.pd.symm.V_le_P₂ (fun v hv x hx => d.pd.V_central v hv x (d.pd.symm.P₂_le_P hx))
    (by rw [hI]; exact hδI) hδ3 (fun v hv => d.pd.conj_V hδI hv) hδfix ?_ hτU hτd ?_
    (mul_mem_VU d) ⟨ℓ, hℓV, hℓU, hℓτ⟩ hZ hZc hZsq hZ2 ⟨e, heB, heU, heV⟩ ?_
  · intro x hx
    have hx' := hx
    rw [d.pd.cent₁] at hx'
    have h1 := hx'.2.2 δ hδN'
    have e1 : δ * x * δ⁻¹ * x⁻¹ = (x * δ * x⁻¹ * δ⁻¹)⁻¹ := by group
    rw [e1]
    exact (VZ T M).inv_mem h1
  · intro p hp u hu
    have hpT : p ∈ T := S153E55.P_le_T hI cx hp
    exact ((Subgroup.mem_normalizer_iff.1 (S153E55.T_le_normalizer_U cx hpT) u).1 hu)
  · intro a ha haV b hb hbV
    obtain ⟨γ, hγ, h⟩ := transitive_Pi d a ha haV b hb hbV
    refine ⟨γ, ?_, h⟩
    rw [hI]
    exact preAut153_le hγ

end Assembly

end S153E61D

namespace S153E

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ} {y t₁ : G}

theorem inv_P_conj_U_of (cx : Ctx15350 T Mc M V₁ V₂ t) (hD : S153E61.Data61 cx)
    (c : Chain15359 cx N₁ N₂ g s y t₁)
    (hD1 : (∀ a ∈ Pi153 T Mc M V₁ N₁ g, ∀ b ∈ Pi153 T Mc M V₁ N₁ g, a * b = b * a ∧ a * a = 1) ∧
      (∀ a ∈ Pi153 T Mc M V₁ N₂ g, ∀ b ∈ Pi153 T Mc M V₁ N₂ g, a * b = b * a ∧ a * a = 1))
    (hB1 : ∀ x ∈ Pgp153 T M V₁ Mc g, x * x = 1 →
      x ∈ Pi153 T Mc M V₁ N₁ g ∨ x ∈ Pi153 T Mc M V₁ N₂ g) :
    ∀ x ∈ Pgp153 T M V₁ Mc g, x * x = 1 →
      ∃ γ ∈ Igp153 T M V₁ Mc g, γ * x * γ⁻¹ ∈ UH153 T M V₁ Mc := by
  intro x hx hx2
  have d := S153E61D.dat61_of_chain c
  rcases hB1 x hx hx2 with h | h
  · exact S153E61D.star_of_dat hD d hD1.1 x h
  · exact S153E61D.star_of_dat hD d.symm hD1.2 x h

end S153E

end CFSG.Quasithin
