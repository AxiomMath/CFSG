module

public import CFSG.RankThree.PartTwo.Toolkit.BloomMonoStd
public import Certificates.Certificate8172

public section

namespace CFSG.RankThree.PartTwo.Toolkit

open Raw Subgroup CFSG.RankThree.SubgroupLists
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

local notation "GL33" => GL (Fin 3) (ZMod 3)

theorem exists_basis_gl {L : Fin 3 → Submodule (ZMod 3) (Fin 3 → ZMod 3)}
    (hL : DirectSum.IsInternal L) (h1 : ∀ i, Module.finrank (ZMod 3) (L i) = 1) :
    ∃ B : GL33, ∀ i, translate B (Lstd i) = L i := by
  have hv : ∀ i, ∃ v : Fin 3 → ZMod 3, v ≠ 0 ∧ L i = Submodule.span (ZMod 3) {v} := by
    intro i
    obtain ⟨w, hw0, hw⟩ := finrank_eq_one_iff'.1 (h1 i)
    refine ⟨w, fun h => hw0 (Subtype.ext h), le_antisymm (fun u hu => ?_) ?_⟩
    · obtain ⟨c, hc⟩ := hw ⟨u, hu⟩
      exact Submodule.mem_span_singleton.2 ⟨c, congrArg Subtype.val hc⟩
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact w.2
  choose v hv0 hvL using hv
  have hli : LinearIndependent (ZMod 3) v :=
    hL.submodule_iSupIndep.linearIndependent L
      (fun i => by rw [hvL i]; exact Submodule.mem_span_singleton_self (v i)) hv0
  have hcol : ((Matrix.of v)ᵀ : Matrix (Fin 3) (Fin 3) (ZMod 3)).col = v := by
    ext j i
    rfl
  have hM : IsUnit ((Matrix.of v)ᵀ : Matrix (Fin 3) (Fin 3) (ZMod 3)) := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit, hcol]
    exact hli
  refine ⟨hM.unit, fun i => ?_⟩
  rw [translate_span_singleton, hvL i, IsUnit.unit_spec, Matrix.mulVec_single_one, hcol]

variable {L : Fin 3 → Submodule (ZMod 3) (Fin 3 → ZMod 3)} {B : GL33}

theorem translate_cancel (g : GL33) (W : Submodule (ZMod 3) (Fin 3 → ZMod 3)) :
    translate g (translate g⁻¹ W) = W := by
  rw [← translate_mul, mul_inv_cancel, translate_one]

theorem translate_conj_eq_iff (hB : ∀ i, translate B (Lstd i) = L i) (g : GL33) (i j : Fin 3) :
    translate (B⁻¹ * g * B) (Lstd i) = Lstd j ↔ translate g (L i) = L j := by
  rw [translate_mul, translate_mul, hB i]
  constructor
  · intro h
    rw [← hB j, ← h, translate_cancel]
  · intro h
    rw [h, ← hB j, translate_inv_translate]

theorem mem_linePermuting_iff (L : Fin 3 → Submodule (ZMod 3) (Fin 3 → ZMod 3)) (g : GL33) :
    g ∈ linePermuting L ↔
      ∀ i, (∃ j, translate g (L i) = L j) ∧ ∃ j, translate g⁻¹ (L i) = L j :=
  Iff.rfl

theorem mem_linePermuting_conj_iff (hB : ∀ i, translate B (Lstd i) = L i) (g : GL33) :
    B⁻¹ * g * B ∈ linePermuting Lstd ↔ g ∈ linePermuting L := by
  have hinv : (B⁻¹ * g * B)⁻¹ = B⁻¹ * g⁻¹ * B := by group
  rw [mem_linePermuting_iff, mem_linePermuting_iff, hinv]
  simp only [translate_conj_eq_iff hB]

theorem conj_mem_statedSL_iff (B g : GL33) :
    B⁻¹ * g * B ∈ CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 3) ↔
      g ∈ CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 3) := by
  have hN := CFSG.RankThree.SubgroupLists.statedSL_normal 3 (ZMod 3)
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simpa [mul_assoc] using hN.conj_mem _ h B
  · simpa using hN.conj_mem _ h B⁻¹

theorem mem_monomialDetOne_conj_iff (hB : ∀ i, translate B (Lstd i) = L i) (g : GL33) :
    B⁻¹ * g * B ∈ monomialDetOne Lstd ↔ g ∈ monomialDetOne L := by
  rw [monomialDetOne, monomialDetOne, Subgroup.mem_inf, Subgroup.mem_inf,
    mem_linePermuting_conj_iff hB, conj_mem_statedSL_iff]

theorem eq_map_conj_of_mem_iff {H K : Subgroup GL33} (h : ∀ g, B⁻¹ * g * B ∈ H ↔ g ∈ K) :
    K = H.map (MulAut.conj B).toMonoidHom := by
  ext g
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, h]

theorem mem_map_conj_inv_iff (G : Subgroup GL33) (B g : GL33) :
    g ∈ G.map (MulAut.conj B⁻¹).toMonoidHom ↔ B * g * B⁻¹ ∈ G := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, inv_inv]

theorem monomialDetOne_eq_map (hB : ∀ i, translate B (Lstd i) = L i) :
    monomialDetOne L = (monomialDetOne Lstd).map (MulAut.conj B).toMonoidHom :=
  eq_map_conj_of_mem_iff (mem_monomialDetOne_conj_iff hB)

theorem map_conj_neg_one (B : GL33) :
    (zpowers (-1 : GL33)).map (MulAut.conj B).toMonoidHom = zpowers (-1) := by
  rw [MonoidHom.map_zpowers]
  congr 1
  simp

theorem isIrreducibleOn_map_conj {G : Subgroup GL33} (hG : IsIrreducibleOn G) (B : GL33) :
    IsIrreducibleOn (G.map (MulAut.conj B⁻¹).toMonoidHom) := by
  intro W hW
  have hW₁ : ∀ g ∈ G, ∀ u ∈ translate B W,
      (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ u ∈ translate B W := by
    intro g hg u hu
    obtain ⟨w, hw, rfl⟩ := mem_translate.1 hu
    have hx : B⁻¹ * g * B ∈ G.map (MulAut.conj B⁻¹).toMonoidHom := by
      rw [mem_map_conj_inv_iff, show B * (B⁻¹ * g * B) * B⁻¹ = g by group]
      exact hg
    have := mulVec_mem_translate (g := B) (hW _ hx w hw)
    rwa [Matrix.mulVec_mulVec, ← Units.val_mul, show B * (B⁻¹ * g * B) = g * B by group,
      Units.val_mul, ← Matrix.mulVec_mulVec] at this
  rcases hG _ hW₁ with h | h
  · left
    rw [← translate_inv_translate B W, h, translate_bot]
  · right
    apply Submodule.eq_top_of_finrank_eq
    rw [← finrank_translate B W, h, finrank_top]

theorem bloomCaseC_of_transitiveMonomial {G : Subgroup GL33} (hG : IsIrreducibleOn G)
    (hmono : IsTransitiveMonomial G) : BloomCaseC G := by
  obtain ⟨L, hL, h1, hperm, htr⟩ := hmono
  obtain ⟨B, hB⟩ := exists_basis_gl hL h1
  obtain ⟨G', hG'⟩ : ∃ G', G' = G.map (MulAut.conj B⁻¹).toMonoidHom := ⟨_, rfl⟩
  have hlp : ∀ g ∈ G, g ∈ linePermuting L := fun g hg i =>
    ⟨hperm g hg i, hperm g⁻¹ (G.inv_mem hg) i⟩
  have hG'le : G' ≤ linePermuting Lstd := by
    intro x hx
    rw [hG', mem_map_conj_inv_iff] at hx
    have := (mem_linePermuting_conj_iff hB (B * x * B⁻¹)).2 (hlp _ hx)
    rwa [show B⁻¹ * (B * x * B⁻¹) * B = x by group] at this
  have htr' : ∀ i j, ∃ x ∈ G', translate x (Lstd i) = Lstd j := by
    intro i j
    obtain ⟨g, hg, hgij⟩ := htr i j
    refine ⟨B⁻¹ * g * B, ?_, (translate_conj_eq_iff hB g i j).2 hgij⟩
    rw [hG', mem_map_conj_inv_iff, show B * (B⁻¹ * g * B) * B⁻¹ = g by group]
    exact hg
  have hirr' : IsIrreducibleOn G' := hG' ▸ isIrreducibleOn_map_conj hG B
  have hGeq : G = G'.map (MulAut.conj B).toMonoidHom :=
    eq_map_conj_of_mem_iff fun g => by
      rw [hG', mem_map_conj_inv_iff, show B * (B⁻¹ * g * B) * B⁻¹ = g by group]
  have hinj : Function.Injective (MulAut.conj B).toMonoidHom := (MulAut.conj B).injective
  have hN := monomialDetOne_eq_map hB
  refine ⟨L, hL, h1, hperm, htr, ⟨(MulEquiv.subgroupCongr hN).trans
    (((monomialDetOne Lstd).equivMapOfInjective _ hinj).symm.trans psiEquiv)⟩,
    N0_inf_neg_one L, G0std.map (MulAut.conj B).toMonoidHom, ?_, ?_,
    ⟨(G0std.equivMapOfInjective _ hinj).symm.trans G0Equiv⟩, ?_, ?_⟩
  · rw [hN]
    exact Subgroup.map_mono G0std_le
  · rw [hN]
    exact (Subgroup.relIndex_map_map_of_injective _ _ hinj).trans index_G0std
  · rw [hGeq]
    exact Subgroup.map_mono (G0std_le_of hG'le htr' hirr')
  · rw [hN, ← map_conj_neg_one B, ← Subgroup.map_sup, hGeq]
    exact Subgroup.map_mono (le_N0std_sup hG'le)

end CFSG.RankThree.PartTwo.Toolkit
