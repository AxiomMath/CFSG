module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6FourFacts
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourAutomorphisms
public import CFSG.Blueprint.Catalog
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6FourWith
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6L34Model
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6L34Aut
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6L34Base
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6L34Base4
import CFSG.GroupTheory.MulAutCongr

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch6.L34

open CFSG.Blueprint (LieModel)
open CFSG.ComponentClassification.PSL3Four

private lemma map_congr_inv_map (γ : MulAut S) (B : Subgroup (MulAut S)) :
    (B.map (MulAut.congr γ⁻¹).toMonoidHom).map (MulAut.congr γ).toMonoidHom = B := by
  have hcomp : (MulAut.congr γ).toMonoidHom.comp (MulAut.congr γ⁻¹).toMonoidHom =
      MonoidHom.id (MulAut S) :=
    MonoidHom.ext fun α => show γ * (γ⁻¹ * α * γ⁻¹⁻¹) * γ⁻¹ = α by group
  rw [Subgroup.map_map, hcomp, Subgroup.map_id]

private lemma card_map_congr_inv {γ : MulAut S} {B : Subgroup (MulAut S)}
    (hB4 : Nat.card B = 4) :
    Nat.card (B.map (MulAut.congr γ⁻¹).toMonoidHom) = 4 := by
  rw [Subgroup.card_map_of_injective (f := (MulAut.congr γ⁻¹).toMonoidHom)
    (MulAut.congr γ⁻¹).injective, hB4]

private lemma sq_eq_one_map_congr_inv {γ : MulAut S} {B : Subgroup (MulAut S)}
    (hB2 : ∀ b ∈ B, b * b = 1) :
    ∀ b ∈ B.map (MulAut.congr γ⁻¹).toMonoidHom, b * b = 1 := by
  intro b hb
  obtain ⟨b₀, hb₀, rfl⟩ := Subgroup.mem_map.mp hb
  have h := congrArg (MulAut.congr γ⁻¹) (hB2 b₀ hb₀)
  rwa [map_mul, map_one] at h

private lemma conjAutS_mem_map_congr_inv
    {B : Subgroup (MulAut S)} {c r : R} (hb : c * r * c⁻¹ ∈ B.comap conjAutS) :
    conjAutS r ∈ B.map (MulAut.congr (conjAutS c)⁻¹).toMonoidHom := by
  convert Subgroup.mem_map_of_mem (MulAut.congr (conjAutS c)⁻¹).toMonoidHom hb using 1
  change _ = (conjAutS c)⁻¹ * conjAutS (c * r * c⁻¹) * (conjAutS c)⁻¹⁻¹
  rw [map_mul, map_mul, map_inv]
  group

private lemma exists_fourGen_of_transport {B : Subgroup (MulAut S)} {γ α : MulAut S}
    (hgen : ∃ x₀ : S,
      orderOf (α * (MulAut.conj x₀ * α * (MulAut.conj x₀)⁻¹)) = 4 ∧
      FourGen (B.map (MulAut.congr γ⁻¹).toMonoidHom) α x₀ ∧
      FourGen (B.map (MulAut.congr γ⁻¹).toMonoidHom) α x₀⁻¹) :
    ∃ x : S,
      orderOf (MulAut.congr γ α * (MulAut.conj x * MulAut.congr γ α * (MulAut.conj x)⁻¹)) = 4 ∧
      FourGen B (MulAut.congr γ α) x ∧ FourGen B (MulAut.congr γ α) x⁻¹ := by
  obtain ⟨x₀, hord, h1, h2⟩ := hgen
  have h1' := FourGen.map γ h1
  have h2' := FourGen.map γ h2
  rw [map_congr_inv_map] at h1'
  rw [map_congr_inv_map, map_inv] at h2'
  exact ⟨γ x₀, (orderOf_congr_mul_conj γ α x₀).trans hord, h1', h2'⟩

private lemma fourFacts_case {B : Subgroup (MulAut S)} {c r : R}
    (hb : c * r * c⁻¹ ∈ B.comap conjAutS)
    (hgen : ∃ x₀ : S,
      orderOf (conjAutS r * (MulAut.conj x₀ * conjAutS r * (MulAut.conj x₀)⁻¹)) = 4 ∧
      FourGen (B.map (MulAut.congr (conjAutS c)⁻¹).toMonoidHom) (conjAutS r) x₀ ∧
      FourGen (B.map (MulAut.congr (conjAutS c)⁻¹).toMonoidHom) (conjAutS r) x₀⁻¹) :
    ∃ β ∈ B, ∃ x : S,
      Even (orderOf (β * (MulAut.conj x * β * (MulAut.conj x)⁻¹))) ∧
      4 ≤ orderOf (β * (MulAut.conj x * β * (MulAut.conj x)⁻¹)) ∧
      FourGen B β x ∧ FourGen B β x⁻¹ := by
  have hβ : MulAut.congr (conjAutS c) (conjAutS r) = conjAutS (c * r * c⁻¹) := by
    rw [map_mul, map_mul, map_inv]
    rfl
  obtain ⟨x, hord, h1, h2⟩ := exists_fourGen_of_transport hgen
  rw [hβ] at hord h1 h2
  refine ⟨_, hb, x, ?_, hord.ge, h1, h2⟩
  rw [hord]
  exact ⟨2, rfl⟩

theorem fourFacts_S :
    FourFacts S := by
  intro B hB4 hB2 hBnot
  have hcard : Nat.card (B.comap conjAutS) = 4 := by
    have hc := Subgroup.card_map_of_injective (K := B.comap conjAutS) conjAutS_injective
    rwa [Subgroup.map_comap_eq_self_of_surjective conjAutS_surjective, hB4, eq_comm] at hc
  have h2 : ∀ b ∈ B.comap conjAutS, b * b = 1 := fun b hb =>
    conjAutS_injective (by rw [map_mul, map_one]; exact hB2 _ hb)
  have hnot : ¬ B.comap conjAutS ≤ S.subgroupOf R := fun hle => hBnot fun β hβ => by
    obtain ⟨b, rfl⟩ := conjAutS_surjective β
    have hb : (b : Equiv.Perm (Fin 42)) ∈ S := hle (show b ∈ B.comap conjAutS from hβ)
    exact ⟨⟨b, hb⟩, (conjAutS_mk ⟨b, hb⟩).symm⟩
  obtain ⟨b, hbB', hconj | hconj | ⟨hconj, s, hsB', hsS, hsne⟩⟩ :=
    exists_rep hcard h2 hnot
  all_goals obtain ⟨c, rfl⟩ := isConj_iff.mp (isConj_comm.mp hconj)
  · exact fourFacts_case hbB' (fourGen_r₂ (card_map_congr_inv hB4)
      (sq_eq_one_map_congr_inv hB2) (conjAutS_mem_map_congr_inv hbB'))
  · exact fourFacts_case hbB' (fourGen_r₃ (card_map_congr_inv hB4)
      (sq_eq_one_map_congr_inv hB2) (conjAutS_mem_map_congr_inv hbB'))
  · have hs : conjAutS s = MulAut.conj (⟨s, hsS⟩ : S) := conjAutS_mk ⟨s, hsS⟩
    have htB : MulAut.conj ((conjAutS c)⁻¹ ⟨s, hsS⟩) ∈
        B.map (MulAut.congr (conjAutS c)⁻¹).toMonoidHom := by
      have h : MulAut.congr (conjAutS c)⁻¹ (conjAutS s) ∈
          B.map (MulAut.congr (conjAutS c)⁻¹).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hsB'
      rwa [hs, CFSG.mulAut_congr_conj] at h
    have htne : (conjAutS c)⁻¹ ⟨s, hsS⟩ ≠ 1 := by
      rw [ne_eq, EmbeddingLike.map_eq_one_iff]
      exact fun h => hsne (Subtype.ext (Subtype.ext_iff.mp h :))
    exact fourFacts_case hbB' (fourGen_r₄ (sq_eq_one_map_congr_inv hB2)
      (conjAutS_mem_map_congr_inv hbB') htB htne)

end CFSG.LocalAnalysis.WeakClosure81.Asch6.L34

namespace CFSG.LocalAnalysis.WeakClosure81.Asch6

open CFSG.Blueprint (LieModel)

theorem fourFacts_of_l34
    {Y : Type} [Group Y] (hY : LieModel Y .PSL 3 2 2) : FourFacts Y := by
  obtain ⟨e⟩ := CFSG.ComponentClassification.CatFactsSmall.nonempty_equiv_psl34_of_lieModel hY
  exact L34.fourFacts_S.of_mulEquiv e.symm

end CFSG.LocalAnalysis.WeakClosure81.Asch6

end
