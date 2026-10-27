module

public import CFSG.Quasithin.EmptyFaithful.SzN31Cover
public import CFSG.Quasithin.EmptyFaithful.SzN31Top
public import CFSG.Quasithin.EmptyFaithful.SzN31FactRStmt

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.SzN31

open CFSG.Quasithin.G11

theorem card_le_four_of_cover {G : Type*} [Group G] {Bhat : Type*} [Group Bhat] [Finite Bhat]
    (β : Bhat →* G) (K : Subgroup Bhat) (hK : Nat.card Bhat ≤ 4 * Nat.card K) (B D : Subgroup G)
    (hrange : β.range = B) (hDB : D ≤ B) (hKD : K ≤ D.comap β) : Nat.card B ≤ 4 * Nat.card D := by
  have hKpos : 0 < Nat.card K := Nat.card_pos
  have h2 : Nat.card K * K.index ≤ Nat.card K * 4 := by
    rw [Subgroup.card_mul_index]
    omega
  have h3 : K.index ≤ 4 := Nat.le_of_mul_le_mul_left h2 hKpos
  have h4 : (D.comap β).index ≤ 4 :=
    (Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.index_dvd_of_le hKD)).trans h3
  rw [Subgroup.index_comap, hrange] at h4
  have h5 := Subgroup.relIndex_mul_card (H := D) (K := B)
  rw [inf_of_le_left hDB] at h5
  rw [← h5]
  exact Nat.mul_le_mul_right _ h4

theorem g94KC_of_factR (hR : FactRStmt) : G94KC := by
  intro V _ _ _ Γ hq p hp hp2 P B hPΓ hBΓ hP hB hBP
  have hfin : Finite (GLV V) :=
    Finite.of_injective (fun g : GLV V => (g : V → V)) DFunLike.coe_injective
  have hP' : IsPGroup p (P.subgroupOf Γ) := hP.comap_subtype
  have hB' : ∀ b ∈ B.subgroupOf Γ, b * b = 1 ∧ ∀ c ∈ B.subgroupOf Γ, b * c = c * b := by
    intro b hb
    refine ⟨Subtype.ext (hB b hb).1, fun c hc => Subtype.ext ((hB b hb).2 c hc)⟩
  have hBP' : ∀ b ∈ B.subgroupOf Γ, ∀ x ∈ P.subgroupOf Γ, b * x * b⁻¹ ∈ P.subgroupOf Γ := by
    intro b hb x hx
    exact hBP b hb x hx
  obtain ⟨Phat, Bhat, _, _, _, _, act, π, β, hPg, hrank, hBg, hπ, hβ, heq⟩ :=
    sqtk_cover_equivariant hq hp hp2 (P.subgroupOf Γ) (B.subgroupOf Γ) hP' hB' hBP'
  have hcard := hR p hp hp2 Phat hPg hrank Bhat act (fun b => (hBg b).1)
  have hrangeP : (Γ.subtype.comp π).range = P := by
    rw [MonoidHom.range_comp, hπ, Subgroup.subgroupOf_map_subtype, inf_of_le_left hPΓ]
  have hrangeB : (Γ.subtype.comp β).range = B := by
    rw [MonoidHom.range_comp, hβ, Subgroup.subgroupOf_map_subtype, inf_of_le_left hBΓ]
  have heq' : ∀ (b : Bhat) (x : Phat), (Γ.subtype.comp π) (act b x) =
      (Γ.subtype.comp β) b * (Γ.subtype.comp π) x * ((Γ.subtype.comp β) b)⁻¹ := by
    intro b x
    simp [heq b x]
  refine card_le_four_of_cover (Γ.subtype.comp β) act.ker hcard B _ hrangeB inf_le_left ?_
  intro b hb
  have hb1 : act b = 1 := hb
  refine ⟨hrangeB ▸ MonoidHom.mem_range.2 ⟨b, rfl⟩, ?_⟩
  show (Γ.subtype.comp β) b ∈ Subgroup.centralizer (P : Set (GLV V))
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have hh' : h ∈ (Γ.subtype.comp π).range := hrangeP ▸ hh
  obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hh'
  have e := heq' b x
  rw [hb1] at e
  change (Γ.subtype.comp π) x = _ at e
  calc (Γ.subtype.comp π) x * (Γ.subtype.comp β) b
      = ((Γ.subtype.comp β) b * (Γ.subtype.comp π) x * ((Γ.subtype.comp β) b)⁻¹) *
        (Γ.subtype.comp β) b := by rw [← e]
    _ = (Γ.subtype.comp β) b * (Γ.subtype.comp π) x := by group

end CFSG.Quasithin.SzN31
