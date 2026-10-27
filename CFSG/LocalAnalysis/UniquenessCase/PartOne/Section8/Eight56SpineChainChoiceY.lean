module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight56Spine
import CFSG.LocalAnalysis.UniquenessCase.UC6Syl

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

theorem exists_choiceY_of_choiceX {G : Type} [Group G] [Finite G] (D : Data G)
    {L Q P X : Subgroup G} (hX : ChoiceX D L Q P X) :
    ∃ X' Y : Subgroup G, ChoiceY D L Q P X' Y := by
  classical
  let S : Set (Subgroup G) := {Z | Z ≤ P ∧
    (∃ X' : Subgroup G, X' ≤ Z ∧ Nat.card X' = 3 ∧ ¬ centralizer (X' : Set G) ≤ D.M) ∧
    ¬ normalizer (Z : Set G) ≤ D.M}
  have hfin : Finite (Subgroup G) :=
    Finite.of_injective (SetLike.coe : Subgroup G → Set G) SetLike.coe_injective
  have hXS : X ∈ S := ⟨hX.le, ⟨X, le_rfl, hX.card, hX.notLe⟩, fun hle =>
    hX.notLe ((Subgroup.centralizer_le_normalizer (X : Set G)).trans hle)⟩
  obtain ⟨Y, hYS, hYmax⟩ := Set.exists_max_image S (fun Z => Nat.card Z) (Set.toFinite S)
    ⟨X, hXS⟩
  obtain ⟨hYP, ⟨X', hX'Y, hX'card, hX'nc⟩, hYN⟩ := hYS
  have hlt : ∀ {A B : Subgroup G}, A < B → Nat.card A < Nat.card B := fun {A B} hAB => by
    by_contra h
    exact hAB.ne (Subgroup.eq_of_le_of_card_ge hAB.le (not_lt.mp h))
  refine ⟨X', Y, ⟨hX.cex, hX'Y.trans hYP, hX'card, hX'nc⟩, hX'Y, hYP, hYN, ?_⟩
  intro Z hYZ hZM hZ3
  by_contra hN
  obtain ⟨k, hkM, hk⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC6.exists_conj_le_of_isSylowOf hX.cex.sylowP hZM hZ3
  have hmem : ∀ (A : Subgroup G) (y : G),
      y ∈ A.map (MulAut.conj k⁻¹).toMonoidHom ↔ k * y * k⁻¹ ∈ A := fun A y => by
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨a, ha, rfl⟩
      have e : k * ((MulAut.conj k⁻¹).toMonoidHom a) * k⁻¹ = a := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [e]
      exact ha
    · intro h
      refine ⟨k * y * k⁻¹, h, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  have hconj_mem : ∀ m : G, k⁻¹ * m * k ∈ D.M → m ∈ D.M := fun m hm => by
    have := D.M.mul_mem (D.M.mul_mem hkM hm) (D.M.inv_mem hkM)
    have e : k * (k⁻¹ * m * k) * k⁻¹ = m := by group
    rwa [e] at this
  let Z' : Subgroup G := Z.map (MulAut.conj k⁻¹).toMonoidHom
  let X'' : Subgroup G := X'.map (MulAut.conj k⁻¹).toMonoidHom
  have hinj : Function.Injective (MulAut.conj k⁻¹).toMonoidHom := (MulAut.conj k⁻¹).injective
  have hZ'P : Z' ≤ P := fun y hy => by
    have h1 := hk (k * y * k⁻¹) ((hmem Z y).1 hy)
    have e : k⁻¹ * (k * y * k⁻¹) * k = y := by group
    rwa [e] at h1
  have hX''Z' : X'' ≤ Z' := Subgroup.map_mono (hX'Y.trans hYZ.le)
  have hX''card : Nat.card X'' = 3 := (Subgroup.card_map_of_injective hinj).trans hX'card
  have hX''nc : ¬ centralizer (X'' : Set G) ≤ D.M := fun hle => by
    obtain ⟨c, hc, hcM⟩ := SetLike.not_le_iff_exists.1 hX'nc
    refine hcM (hconj_mem c (hle ?_))
    refine Subgroup.mem_centralizer_iff.2 fun x'' hx'' => ?_
    have ha := Subgroup.mem_centralizer_iff.1 hc (k * x'' * k⁻¹) ((hmem X' x'').1 hx'')
    calc x'' * (k⁻¹ * c * k) = k⁻¹ * (k * x'' * k⁻¹ * c) * k := by group
      _ = k⁻¹ * (c * (k * x'' * k⁻¹)) * k := by rw [ha]
      _ = k⁻¹ * c * k * x'' := by group
  have hZ'N : ¬ normalizer (Z' : Set G) ≤ D.M := fun hle => by
    obtain ⟨n, hn, hnM⟩ := SetLike.not_le_iff_exists.1 hN
    refine hnM (hconj_mem n (hle ?_))
    refine Subgroup.mem_normalizer_iff.2 fun h => ?_
    have hn' := Subgroup.mem_normalizer_iff.1 hn (k * h * k⁻¹)
    have e : k * (k⁻¹ * n * k * h * (k⁻¹ * n * k)⁻¹) * k⁻¹ = n * (k * h * k⁻¹) * n⁻¹ := by
      group
    rw [hmem Z h, hmem Z _, e]
    exact hn'
  have hZ'S : Z' ∈ S := ⟨hZ'P, ⟨X'', hX''Z', hX''card, hX''nc⟩, hZ'N⟩
  have h1 := hYmax Z' hZ'S
  have h2 := hlt hYZ
  have h3 : Nat.card Z' = Nat.card Z := Subgroup.card_map_of_injective hinj
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
