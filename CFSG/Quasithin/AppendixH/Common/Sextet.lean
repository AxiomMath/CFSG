module

public import CFSG.Milestones.ASVolI.H13
public import CFSG.Quasithin.Background.H158N2
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

open scoped Pointwise

namespace CFSG.ASVolI.AppH

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Monster.Code CFSG.Open

private theorem card_smul_finset_eq (g : S24) (S : Finset (Finset (Fin 24))) :
    (g • S).card = S.card := by
  refine le_antisymm Finset.card_smul_finset_le ?_
  have := Finset.card_smul_finset_le (a := g⁻¹) (s := g • S)
  simpa using this

private theorem isOctad_map_iff {g : S24} (hg : g ∈ M24g) (O : Finset (Fin 24)) :
    IsOctad (O.map g.toEmbedding) ↔ IsOctad O := by
  simp only [IsOctad, Finset.card_map, ← permAct_eY,
    CFSG.Quasithin.H158N.permAct_mem_golay_iff hg]

theorem isSextet_smul {g : S24} (hg : g ∈ M24g) {S : Finset (Finset (Fin 24))}
    (hS : IsSextet S) : IsSextet (g • S) := by
  obtain ⟨hcard, htet, hdisj, hcov, hoct⟩ := hS
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (card_smul_finset_eq g S).trans hcard
  · intro B hB
    rw [Finset.mem_smul_finset] at hB
    obtain ⟨T, hT, rfl⟩ := hB
    rw [smul_finset_eq_map, Finset.card_map]
    exact htet T hT
  · intro B hB B' hB' hne
    rw [Finset.mem_smul_finset] at hB hB'
    obtain ⟨T, hT, rfl⟩ := hB
    obtain ⟨T', hT', rfl⟩ := hB'
    rw [smul_finset_eq_map g T, smul_finset_eq_map g T']
    exact (Finset.disjoint_map _).2 (hdisj T hT T' hT' fun h => hne (by rw [h]))
  · rw [Finset.eq_univ_iff_forall]
    intro x
    have hxU : g.symm x ∈ S.biUnion id := by
      rw [hcov]; exact Finset.mem_univ _
    obtain ⟨T, hT, hxT⟩ := Finset.mem_biUnion.1 hxU
    rw [Finset.mem_biUnion]
    refine ⟨T.map g.toEmbedding, ?_, ?_⟩
    · exact Finset.mem_smul_finset.2 ⟨T, hT, smul_finset_eq_map g T⟩
    · show x ∈ T.map g.toEmbedding
      rw [Finset.mem_map_equiv]
      exact hxT
  · intro B hB B' hB' hne
    rw [Finset.mem_smul_finset] at hB hB'
    obtain ⟨T, hT, rfl⟩ := hB
    obtain ⟨T', hT', rfl⟩ := hB'
    have hTT : T ≠ T' := fun h => hne (by rw [h])
    rw [← Finset.smul_finset_union, smul_finset_eq_map]
    exact (isOctad_map_iff hg _).2 (hoct T hT T' hT' hTT)

private theorem hammingNorm_eY_mul_inv (A B : Finset (Fin 24)) :
    hammingNorm (Multiplicative.toAdd (eY A * (eY B)⁻¹)) + 2 * (A ∩ B).card =
      A.card + B.card := by
  have hset : Finset.univ.filter (fun i : Fin 24 =>
      Multiplicative.toAdd (eY A * (eY B)⁻¹) i ≠ 0) = (A \ B) ∪ (B \ A) := by
    ext i
    by_cases hA : i ∈ A <;> by_cases hB : i ∈ B <;>
      simp [toAdd_eY, hA, hB, toAdd_mul, toAdd_inv] <;> decide
  have hdisj : Disjoint (A \ B) (B \ A) := by
    rw [Finset.disjoint_left]
    intro i hi hi'
    exact (Finset.mem_sdiff.1 hi).2 (Finset.mem_sdiff.1 hi').1
  have h1 := Finset.card_union_of_disjoint hdisj
  have h2 := Finset.card_sdiff_add_card_inter A B
  have h3 := Finset.card_sdiff_add_card_inter B A
  rw [Finset.inter_comm B A] at h3
  unfold hammingNorm
  rw [hset, h1]
  omega

private theorem octad_inter_card {O O' : Finset (Fin 24)} (hO : IsOctad O) (hO' : IsOctad O')
    (hne : O ≠ O') : (O ∩ O').card = 0 ∨ (O ∩ O').card = 2 ∨ (O ∩ O').card = 4 := by
  have hc : eY O * (eY O')⁻¹ ∈ golayC := mul_mem hO.2 (inv_mem hO'.2)
  have hw := hammingNorm_eY_mul_inv O O'
  have hwt := CFSG.Monster.Code.wt_mem (x := Multiplicative.toAdd (eY O * (eY O')⁻¹)) hc
  simp only [Finset.mem_insert, Finset.mem_singleton] at hwt
  have hc8 : O.card = 8 := hO.1
  have hc8' : O'.card = 8 := hO'.1
  rw [hc8, hc8'] at hw
  have h8 : (O ∩ O').card ≠ 8 := by
    intro h8
    have hsub : O ∩ O' = O := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
    have hOO' : O ⊆ O' := by
      intro x hx
      have hx' : x ∈ O ∩ O' := by rw [hsub]; exact hx
      exact (Finset.mem_inter.1 hx').2
    exact hne (Finset.eq_of_subset_of_card_le hOO' (by omega))
  omega

private theorem sext_mem_of_octad {S : Finset (Finset (Fin 24))} (hS : IsSextet S)
    {B T : Finset (Fin 24)} (hB : B ∈ S) (hT : T.card = 4) (hO : IsOctad (B ∪ T)) : T ∈ S := by
  obtain ⟨-, htet, hdisj, hcov, hoct⟩ := hS
  have hB4 : B.card = 4 := htet B hB
  by_contra hTS
  have hBT : Disjoint B T := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    have h1 := Finset.card_union_add_card_inter B T
    have hc8 : (B ∪ T).card = 8 := hO.1
    have h0 : (B ∩ T).card = 0 := by omega
    exact Finset.card_eq_zero.1 h0
  have hTdisj : ∀ T'' ∈ S, Disjoint T T'' := by
    intro T'' hT''
    by_cases hBT'' : T'' = B
    · rw [hBT'']
      exact hBT.symm
    · have hne : B ∪ T ≠ B ∪ T'' := by
        intro heq
        have hBT2 : Disjoint B T'' := hdisj B hB T'' hT'' (Ne.symm hBT'')
        have e1 : (B ∪ T) \ B = T := Finset.union_sdiff_cancel_left hBT
        have e2 : (B ∪ T'') \ B = T'' := Finset.union_sdiff_cancel_left hBT2
        have hTT : T = T'' := by
          calc T = (B ∪ T) \ B := e1.symm
            _ = (B ∪ T'') \ B := by rw [heq]
            _ = T'' := e2
        exact hTS (hTT ▸ hT'')
      have hk := octad_inter_card hO (hoct B hB T'' hT'' (Ne.symm hBT'')) hne
      have hsub : B ⊆ (B ∪ T) ∩ (B ∪ T'') := fun x hx =>
        Finset.mem_inter.2 ⟨Finset.mem_union_left _ hx, Finset.mem_union_left _ hx⟩
      have hinter : (B ∪ T) ∩ (B ∪ T'') = B :=
        (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
      rw [Finset.disjoint_left]
      intro x hxT hxT''
      have hx : x ∈ (B ∪ T) ∩ (B ∪ T'') :=
        Finset.mem_inter.2 ⟨Finset.mem_union_right _ hxT, Finset.mem_union_right _ hxT''⟩
      rw [hinter] at hx
      exact (Finset.disjoint_left.1 hBT hx) hxT
  have hTempty : T = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro x hx
    have hxU : x ∈ S.biUnion id := by
      rw [hcov]
      exact Finset.mem_univ x
    obtain ⟨T'', hT'', hxT''⟩ := Finset.mem_biUnion.1 hxU
    exact (Finset.disjoint_left.1 (hTdisj T'' hT'') hx) hxT''
  rw [hTempty] at hT
  simp at hT

theorem sextet_eq_of_mem {S S' : Finset (Finset (Fin 24))} (hS : IsSextet S)
    (hS' : IsSextet S') {B : Finset (Fin 24)} (hB : B ∈ S) (hB' : B ∈ S') : S = S' := by
  have hsub : S' ⊆ S := by
    intro T hT
    by_cases hTB : T = B
    · rw [hTB]
      exact hB
    · exact sext_mem_of_octad hS hB (hS'.2.1 T hT) (hS'.2.2.2.2 B hB' T hT (Ne.symm hTB))
  exact (Finset.eq_of_subset_of_card_le hsub (by rw [hS.1, hS'.1])).symm

end CFSG.ASVolI.AppH
