module

public import CFSG.Quasithin.Background.RonanH143Data

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH143

open CFSG.Quasithin CFSG.Monster.Code CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H16Pf

open scoped Classical in
@[expose] noncomputable def eSetR (Y : Finset (Fin 24)) : G6.PermMod 24 :=
  Multiplicative.ofAdd fun i => if i ∈ Y then 1 else 0

@[expose] def IsOctR (O : Finset (Fin 24)) : Prop := O.card = 8 ∧ eSetR O ∈ golayC

@[expose] def IsSextR (S : Finset (Finset (Fin 24))) : Prop :=
  S.card = 6 ∧ (∀ B ∈ S, B.card = 4) ∧ (∀ B ∈ S, ∀ B' ∈ S, B ≠ B' → Disjoint B B') ∧
    S.biUnion id = Finset.univ ∧ (∀ B ∈ S, ∀ B' ∈ S, B ≠ B' → IsOctR (B ∪ B'))

theorem mem_golay_iff' (m : G6.PermMod 24) : m ∈ golayC ↔ Multiplicative.toAdd m ∈ C := Iff.rfl

theorem toAdd_eSet (Y : Finset (Fin 24)) (i : Fin 24) :
    Multiplicative.toAdd (eSetR Y) i = if i ∈ Y then 1 else 0 := by
  unfold eSetR
  by_cases h : i ∈ Y <;> simp [h]

theorem permAct_eSet (g : Equiv.Perm (Fin 24)) (Y : Finset (Fin 24)) :
    G6.permAct 24 g (eSetR Y) = eSetR (Y.map g.toEmbedding) := by
  apply Multiplicative.toAdd.injective
  funext i
  simp [G6.permAct_apply, toAdd_eSet, Finset.mem_map_equiv, Equiv.Perm.inv_def]

theorem permAct_mem_golay_iff {g : Equiv.Perm (Fin 24)} (hg : g ∈ CFSG.Monster.Code.AutPerm)
    (c : G6.PermMod 24) : G6.permAct 24 g c ∈ golayC ↔ c ∈ golayC := by
  have hinv := (mem_AutPerm_iff.1 (inv_mem hg) (Multiplicative.toAdd c))
  have e : Multiplicative.toAdd (G6.permAct 24 g c) = Multiplicative.toAdd c ∘ ⇑g⁻¹ := by
    funext i
    rfl
  rw [mem_golay_iff', mem_golay_iff', e]
  exact hinv.symm

theorem isOct_map_iff {g : Equiv.Perm (Fin 24)} (hg : g ∈ CFSG.Monster.Code.AutPerm)
    (O : Finset (Fin 24)) : IsOctR (O.map g.toEmbedding) ↔ IsOctR O := by
  unfold IsOctR
  rw [Finset.card_map, ← permAct_eSet, permAct_mem_golay_iff hg]

theorem hammingNorm_eSet_mul_inv (A B : Finset (Fin 24)) :
    hammingNorm (Multiplicative.toAdd (eSetR A * (eSetR B)⁻¹)) + 2 * (A ∩ B).card =
      A.card + B.card := by
  have hset : Finset.univ.filter (fun i : Fin 24 =>
      Multiplicative.toAdd (eSetR A * (eSetR B)⁻¹) i ≠ 0) = (A \ B) ∪ (B \ A) := by
    ext i
    by_cases hA : i ∈ A <;> by_cases hB : i ∈ B <;>
      simp [toAdd_eSet, hA, hB, toAdd_mul, toAdd_inv] <;> decide
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

theorem octad_inter_card {O O' : Finset (Fin 24)} (hO : IsOctR O) (hO' : IsOctR O')
    (hne : O ≠ O') : (O ∩ O').card = 0 ∨ (O ∩ O').card = 2 ∨ (O ∩ O').card = 4 := by
  have hc : eSetR O * (eSetR O')⁻¹ ∈ golayC := mul_mem hO.2 (inv_mem hO'.2)
  have hw := hammingNorm_eSet_mul_inv O O'
  have hwt := CFSG.Monster.Code.wt_mem (x := Multiplicative.toAdd (eSetR O * (eSetR O')⁻¹)) hc
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

theorem sext_mem_of_octad {S : Finset (Finset (Fin 24))} (hS : IsSextR S) {B T : Finset (Fin 24)}
    (hB : B ∈ S) (hT : T.card = 4) (hO : IsOctR (B ∪ T)) : T ∈ S := by
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

theorem sext_eq_of_mem {S S' : Finset (Finset (Fin 24))} (hS : IsSextR S) (hS' : IsSextR S')
    {B : Finset (Fin 24)} (hB : B ∈ S) (hB' : B ∈ S') : S = S' := by
  have hsub : S' ⊆ S := by
    intro T hT
    by_cases hTB : T = B
    · rw [hTB]
      exact hB
    · exact sext_mem_of_octad hS hB (hS'.2.1 T hT) (hS'.2.2.2.2 B hB' T hT (Ne.symm hTB))
  exact (Finset.eq_of_subset_of_card_le hsub (by rw [hS.1, hS'.1])).symm

@[expose] def sMap (g : Equiv.Perm (Fin 24)) (S : Finset (Finset (Fin 24))) :
    Finset (Finset (Fin 24)) :=
  S.image fun T => T.map g.toEmbedding

theorem isSext_sMap {g : Equiv.Perm (Fin 24)} (hg : g ∈ CFSG.Monster.Code.AutPerm)
    {S : Finset (Finset (Fin 24))} (hS : IsSextR S) : IsSextR (sMap g S) := by
  obtain ⟨hcard, htet, hdisj, hcov, hoct⟩ := hS
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [sMap, Finset.card_image_of_injective _ (Finset.map_injective _), hcard]
  · intro B hB
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.1 hB
    rw [Finset.card_map, htet T hT]
  · intro B hB B' hB' hne
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.1 hB
    obtain ⟨T', hT', rfl⟩ := Finset.mem_image.1 hB'
    have hTT : T ≠ T' := fun h => hne (by rw [h])
    exact (Finset.disjoint_map _).2 (hdisj T hT T' hT' hTT)
  · rw [Finset.eq_univ_iff_forall]
    intro x
    have hxU : g.symm x ∈ S.biUnion id := by
      rw [hcov]
      exact Finset.mem_univ _
    obtain ⟨T, hT, hxT⟩ := Finset.mem_biUnion.1 hxU
    rw [Finset.mem_biUnion]
    refine ⟨T.map g.toEmbedding, Finset.mem_image_of_mem _ hT, ?_⟩
    show x ∈ T.map g.toEmbedding
    rw [Finset.mem_map_equiv]
    exact hxT
  · intro B hB B' hB' hne
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.1 hB
    obtain ⟨T', hT', rfl⟩ := Finset.mem_image.1 hB'
    have hTT : T ≠ T' := fun h => hne (by rw [h])
    rw [← Finset.map_union]
    exact (isOct_map_iff hg _).2 (hoct T hT T' hT' hTT)

theorem sextStd_toAdd_eSet (m : ℕ) :
    Multiplicative.toAdd (eSetR (maskSet m)) = bvec 24 m := by
  funext i
  simp [toAdd_eSet, bvec_apply, mem_maskSet]

theorem sextStd_maskSet_or (a b : ℕ) : maskSet a ∪ maskSet b = maskSet (a ||| b) := by
  ext i
  simp [mem_maskSet, Nat.testBit_or]

theorem sextStd_mem_iff (B : Finset (Fin 24)) : B ∈ Sstd ↔ B = Bstd ∨ ∃ i, Zq i = B := by
  rw [Sstd, Finset.mem_insert, mem_Qstd_iff]

theorem sextStd_Bstd_card : Bstd.card = 4 := by decide +kernel

theorem sextStd_Zq_card : ∀ i : Fin 5, (Zq i).card = 4 := by decide +kernel

theorem sextStd_Zq_disjoint : ∀ i j : Fin 5, i ≠ j → Disjoint (Zq i) (Zq j) := by
  decide +kernel

theorem sextStd_Bstd_disjoint : ∀ j : Fin 5, Disjoint Bstd (Zq j) := by decide +kernel

theorem sextStd_biUnion : Sstd.biUnion id = Finset.univ := by decide +kernel

theorem sextStd_card : Sstd.card = 6 := by
  rw [Sstd, Finset.card_insert_of_notMem Bstd_notMem_Qstd, Qstd_card]

theorem sextStd_card4 : ∀ B ∈ Sstd, B.card = 4 := by
  intro B hB
  rcases (sextStd_mem_iff B).1 hB with rfl | ⟨i, rfl⟩
  · exact sextStd_Bstd_card
  · exact sextStd_Zq_card i

theorem sextStd_disjoint : ∀ B ∈ Sstd, ∀ B' ∈ Sstd, B ≠ B' → Disjoint B B' := by
  intro B hB B' hB' hne
  rcases (sextStd_mem_iff B).1 hB with rfl | ⟨i, rfl⟩ <;>
    rcases (sextStd_mem_iff B').1 hB' with rfl | ⟨j, rfl⟩
  · exact (hne rfl).elim
  · exact sextStd_Bstd_disjoint j
  · exact (sextStd_Bstd_disjoint i).symm
  · exact sextStd_Zq_disjoint i j (fun h => hne (by rw [h]))

theorem sextStd_octad_assembly (P : Finset (Fin 24) → Prop)
    (hB : ∀ j : Fin 5, P (Bstd ∪ Zq j)) (hZ : ∀ i j : Fin 5, i ≠ j → P (Zq i ∪ Zq j)) :
    ∀ B ∈ Sstd, ∀ B' ∈ Sstd, B ≠ B' → P (B ∪ B') := by
  intro B hB₀ B' hB' hne
  rcases (sextStd_mem_iff B).1 hB₀ with rfl | ⟨i, rfl⟩ <;>
    rcases (sextStd_mem_iff B').1 hB' with rfl | ⟨j, rfl⟩
  · exact (hne rfl).elim
  · exact hB j
  · rw [Finset.union_comm]
    exact hB i
  · exact hZ i j (fun h => hne (by rw [h]))

theorem sextStd_bstd_check : ∀ j : Fin 5,
    (maskSet (195 ||| zMask j)).card = 8 ∧ syndM (195 ||| zMask j) = 0 := by
  decide +kernel

theorem sextStd_zq_check : ∀ i j : Fin 5, i ≠ j →
    (maskSet (zMask i ||| zMask j)).card = 8 ∧ syndM (zMask i ||| zMask j) = 0 := by
  decide +kernel

theorem sextStd_isOct_maskSet {m : ℕ} (hc : (maskSet m).card = 8) (hs : syndM m = 0) :
    IsOctR (maskSet m) := by
  unfold IsOctR
  refine ⟨hc, ?_⟩
  rw [mem_golay_iff', sextStd_toAdd_eSet, bvec_mem_C_iff]
  exact hs

theorem sextStd_isOct_of_union {X Y : Finset (Fin 24)} {m : ℕ} (hXY : X ∪ Y = maskSet m)
    (hc : (maskSet m).card = 8) (hs : syndM m = 0) :
    IsOctR (X ∪ Y) := by
  rw [hXY]
  exact sextStd_isOct_maskSet hc hs

theorem sextStd_isOct_Bstd (j : Fin 5) : IsOctR (Bstd ∪ Zq j) :=
  sextStd_isOct_of_union (X := Bstd) (Y := Zq j) (sextStd_maskSet_or 195 (zMask j))
    (sextStd_bstd_check j).1 (sextStd_bstd_check j).2

theorem sextStd_isOct_Zq (i j : Fin 5) (hij : i ≠ j) :
    IsOctR (Zq i ∪ Zq j) :=
  sextStd_isOct_of_union (X := Zq i) (Y := Zq j) (sextStd_maskSet_or (zMask i) (zMask j))
    (sextStd_zq_check i j hij).1 (sextStd_zq_check i j hij).2

theorem isSext_Sstd : IsSextR Sstd :=
  ⟨sextStd_card, sextStd_card4, sextStd_disjoint, sextStd_biUnion,
    sextStd_octad_assembly IsOctR sextStd_isOct_Bstd sextStd_isOct_Zq⟩

end CFSG.Quasithin.RonanH143
