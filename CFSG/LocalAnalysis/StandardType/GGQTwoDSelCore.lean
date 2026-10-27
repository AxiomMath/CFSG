module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDGenAbsorb
public import CFSG.LocalAnalysis.StandardType.GGQTwoDSlPair

public section

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn.QTwo

section Pure

variable {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {𝒦 : Finset (Subgroup G)}
  {ι : Type} {M : CoxeterMatrix ι} (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)) {m : ℕ}
  (e' : Fin m ≃ ι)

theorem qtwoW_le_iSup (r : Fin m → MulAut ↥Bs) {i j : Fin m} (hij : i ≠ j) :
    qtwoW Bs r i j ≤ ⨆ (i : Fin m) (j : Fin m) (_ : i < j), qtwoW Bs r i j := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact le_iSup_of_le i (le_iSup_of_le j (le_iSup (fun _ : i < j => qtwoW Bs r i j) h))
  · rw [qtwoW_symm Bs r i j]
    exact le_iSup_of_le j (le_iSup_of_le i (le_iSup (fun _ : j < i => qtwoW Bs r j i) h))

theorem ggRankTwo_le_nodes (hm : 4 ≤ m) (hM : M = (ggCoxeterMatrixD m).reindex e')
    {r r' : MulAut ↥Bs} (hr : r ∈ ggCoxRefl M e) (hr' : r' ∈ ggCoxRefl M e)
    (hne : r * r' ≠ r' * r) :
    ggRankTwo Bs r r' ≤ ⨆ (i : Fin m) (j : Fin m) (_ : i < j), qtwoW Bs (qtwoRefl e e') i j := by
  obtain ⟨a, haA, i, j, h3, rfl, rfl⟩ := exists_simple_pair_conj_mem e e' hm hM hr hr' hne
  obtain ⟨g, hgP, -, hg⟩ := mem_ggAutomizer_iff.mp
    (ggAutomizerJoin_le_ggAutomizer_nodes e (by omega) e' haA)
  rw [← ggRankTwo_map_conj hg]
  have hij : i ≠ j := by
    rintro rfl
    have h1 : ggCoxeterMatrixD m i i = 1 := (ggCoxeterMatrixD m).diagonal i
    omega
  have hW : ggRankTwo Bs (qtwoRefl e e' i) (qtwoRefl e e' j) ≤
      ⨆ (i : Fin m) (j : Fin m) (_ : i < j), qtwoW Bs (qtwoRefl e e') i j := by
    rw [← qtwoW_of_edge (qtwoRefl e e') h3]
    exact qtwoW_le_iSup _ hij
  rintro _ ⟨s, hs, rfl⟩
  show g * s * g⁻¹ ∈ _
  exact mul_mem (mul_mem hgP (hW hs)) (inv_mem hgP)

end Pure

section Inputs


@[expose] def GGQTwoLGenRankTwoInputOn (R : ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)) (ι : Type) (M : CoxeterMatrix ι)
    (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)), GGQTwoDCfg p B Bs x L D J 𝒦 M e →
      ∀ (m : ℕ) (e' : Fin m ≃ ι), R m → M = (ggCoxeterMatrixD m).reindex e' →
        L ≤ ⨆ (r : MulAut ↥Bs) (_ : r ∈ ggAutomizer L Bs ∧ r ∈ ggCoxRefl M e)
          (r' : MulAut ↥Bs) (_ : r' ∈ ggAutomizer L Bs ∧ r' ∈ ggCoxRefl M e)
          (_ : r * r' ≠ r' * r), ggRankTwoIn L Bs r r'

@[expose] def GGQTwoLGenRankTwoInput : Prop :=
  GGQTwoLGenRankTwoInputOn fun m => 7 ≤ m

@[expose] def GGQTwoEdgeAmbientLInputOn (R : ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)) (ι : Type) (M : CoxeterMatrix ι)
    (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)), GGQTwoDCfg p B Bs x L D J 𝒦 M e →
      ∀ (m : ℕ) (e' : Fin m ≃ ι), R m → M = (ggCoxeterMatrixD m).reindex e' →
        ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → ∀ r' ∈ ggAutomizer L Bs,
          r' ∈ ggCoxRefl M e → r * r' ≠ r' * r → ggRankTwo Bs r r' = ggRankTwoIn L Bs r r'

theorem GGQTwoEdgeAmbientInputOn.toL {R : ℕ → Prop} (h : GGQTwoEdgeAmbientInputOn R) :
    GGQTwoEdgeAmbientLInputOn R :=
  fun G _ _ p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM =>
    h G p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM L (Or.inl rfl)

theorem ggQTwoSelLInputOn_of_rankTwoGen_L {R : ℕ → Prop} (hR : ∀ m, R m → 4 ≤ m)
    (hEdge : GGQTwoEdgeAmbientLInputOn R) (hGenL : GGQTwoLGenRankTwoInputOn R) :
    GGQTwoSelLInputOn R := by
  intro G _ _ p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM
  refine (hGenL G p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM).trans ?_
  refine iSup_le fun r => iSup_le fun hr => iSup_le fun r' => iSup_le fun hr' =>
    iSup_le fun hne => ?_
  rw [← hEdge G p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM r hr.1 hr.2 r' hr'.1 hr'.2 hne]
  exact ggRankTwo_le_nodes e e' (hR m hm) hM hr.2 hr'.2 hne

theorem ggQTwoSelLInputOn_of_rankTwoGen {R : ℕ → Prop} (hR : ∀ m, R m → 4 ≤ m)
    (hEdge : GGQTwoEdgeAmbientInputOn R) (hGenL : GGQTwoLGenRankTwoInputOn R) :
    GGQTwoSelLInputOn R :=
  ggQTwoSelLInputOn_of_rankTwoGen_L hR hEdge.toL hGenL

theorem ggQTwoSelLInput_of_rankTwoGen (hEdge : GGQTwoEdgeAmbientInput)
    (hGenL : GGQTwoLGenRankTwoInput) : GGQTwoSelLInput :=
  ggQTwoSelLInputOn_of_rankTwoGen (fun m hm => by omega) hEdge hGenL

theorem GGQTwoSelLInputOn.or {R R' : ℕ → Prop} (h : GGQTwoSelLInputOn R)
    (h' : GGQTwoSelLInputOn R') : GGQTwoSelLInputOn fun m => R m ∨ R' m := by
  intro G _ _ p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM
  rcases hm with hm | hm
  · exact h G p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM
  · exact h' G p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM

end Inputs

end CFSG.StandardType.QTwo

end
