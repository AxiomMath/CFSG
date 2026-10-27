module

public import CFSG.Monster.B.Geometry.OrthResidue
public import CFSG.Monster.B.Geometry.GlobalExtension

public section

namespace CFSG.Monster.B.Geometry

open Module CoxeterSystem CFSG.LieType.Chevalley CFSG.LieType.Chevalley.CosetBuilding
open CFSG.LieType.Chevalley.C2E6Overlap (X Q QVertex)

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Building

variable {ι : Type*} {M : CoxeterMatrix ι} {W : Type*} [Group W] {cs : CoxeterSystem M W}
  [Finite W] {C : Type*} {δ : C → C → W} (hδ : IsWeylDistanceBuilding cs δ) {p l π : ι}
  (hpl : p ≠ l) (hlπ : l ≠ π) (hpπ : p ≠ π) (hι : ∀ i, i = p ∨ i = l ∨ i = π)
  (hMpl : M p l = 3) (hMlπ : M l π = 4) (hMpπ : M p π = 2) {f : C → PFlag OData}
  (hf : IsChamberModel cs δ (polarChamber OData p l π) f) {c₀ d₀ : C} (hc₀ : f c₀ = oC0)
  (hd₀ : f d₀ = oD0)
include hδ hpl hlπ hpπ hι hMpl hMlπ hMpπ hf hc₀ hd₀

theorem orth_oppChamber_quad :
    f (oppChamber cs δ c₀ d₀ (longest cs {l, π})) = oFlag {0} {0, 4} {0, 4, 5} := by
  have hcd := orth_standard_opposite hδ hpl hlπ hpπ hι hMpl hMlπ hMpπ hf hc₀ hd₀
  obtain ⟨q, hq⟩ := hf.1.2 (oFlag {0} {0, 4} {0, 4, 5})
  have hqR : q ∈ residue cs δ {l, π} c₀ :=
    (mem_residue_lπ_oC0 hpl hlπ hpπ hf hc₀).mpr (by rw [hq]; rfl)
  have hγ : (polarChamber OData p l π).IsGallery (f q) [(p, oFlag {4} {0, 4} {0, 4, 5}),
      (l, oFlag {4} {4, 5} {0, 4, 5}), (π, oFlag {4} {4, 5} {3, 4, 5}),
      (l, oFlag {4} {3, 4} {3, 4, 5}), (p, oD0)] := by
    rw [hq]
    refine ⟨?_, ?_, ?_, ?_, ?_, trivial⟩
    · rw [polarChamber_adj_p]; exact ⟨rfl, rfl⟩
    · rw [polarChamber_adj_l hpl]; exact ⟨rfl, rfl⟩
    · rw [polarChamber_adj_π hpπ hlπ]; exact ⟨rfl, rfl⟩
    · rw [polarChamber_adj_l hpl]; exact ⟨rfl, rfl⟩
    · rw [polarChamber_adj_p]; exact ⟨rfl, rfl⟩
  have hlen := hf.length_le hδ hγ (by rw [hd₀]; rfl)
  have h9 := nine_le_length_longest_C3 (cs := cs) hpl hlπ hpπ hι hMpl hMlπ hMpπ
  have h4 : cs.length (longest cs {l, π}) = 4 := by
    rw [length_longest_pair hlπ (by omega), hMlπ]
  simp only [List.length_cons, List.length_nil] at hlen
  rw [← eq_oppChamber_of_length_le hδ hcd hqR (by omega), hq]

theorem orth_realize (Ψ : C → C)
    (hΨ : IsWeylIsometry δ δ (foundation cs δ 2 c₀ ∪ {d₀}) (foundation cs δ 2 c₀ ∪ {d₀}) Ψ)
    (hΨc : Ψ c₀ = c₀) (hΨd : Ψ d₀ = d₀) :
    ∃ A : GL (Fin 2) (ZMod 2),
      Set.EqOn (hf.perm (oTailPerm A)) Ψ (foundation cs δ 2 c₀ ∪ {d₀}) := by
  have hcd := orth_standard_opposite hδ hpl hlπ hpπ hι hMpl hMlπ hMpπ hf hc₀ hd₀
  have hRq := fun y => mem_residue_lπ_oC0 hpl hlπ hpπ hf hc₀ (y := y)
  have hqm := isModelResidue_oQuadModel hpl hlπ hpπ hf hc₀
  have hiso_q := hΨ.isTypeIso_residue hδ hΨc (encard_pair_le_two l π)
  obtain ⟨G, hG, hG1, hG2⟩ := hqm.exists_perm (fun _ => rfl) (fun _ => rfl) hiso_q
  have hGmem : G ∈ qflagTypeAut := fun u v => ⟨hG2 u v, hG1 u v⟩
  have hp₀ := orth_oppChamber_quad hδ hpl hlπ hpπ hι hMpl hMlπ hMpπ hf hc₀ hd₀
  have hp₀R : oppChamber cs δ c₀ d₀ (longest cs {l, π}) ∈ residue cs δ {l, π} c₀ :=
    (hRq _).mpr (by rw [hp₀]; rfl)
  have hΨp := hΨ.fix_oppChamber hδ hcd hΨc hΨd (encard_pair_le_two l π)
    (isLongest_of_finite (cs := cs) {l, π}).1
  have hGc : G (oQuadModel f c₀) = oQuadModel f c₀ := by
    rw [hG c₀ (self_mem_residue _ c₀), hΨc]
  have hGp : G (oQuadModel f (oppChamber cs δ c₀ d₀ (longest cs {l, π}))) =
      oQuadModel f (oppChamber cs δ c₀ d₀ (longest cs {l, π})) := by
    rw [hG _ hp₀R, hΨp]
  obtain ⟨hc1, hc2⟩ := oQuadModel_c0 hc₀
  obtain ⟨hq1, hq2⟩ := oQuadModel_p0 hp₀
  have hσ : qVertexPerm hGmem ∈ C2E6Overlap.vertexStabilizer C2E6Overlap.baseFlagSpaces := by
    refine ⟨qVertexPerm_mem_typeAut hGmem, fun x hx => ?_⟩
    simp only [C2E6Overlap.baseFlagSpaces, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rw [qVertexPerm_apply]
    rcases hx with hx | hx | hx | hx
    · rw [show x = (oQuadModel f c₀).pt from Subtype.ext (hx.trans hc1.symm),
        qVertexMap_pt hGmem, hGc]
    · rw [show x = (oQuadModel f c₀).line from Subtype.ext (hx.trans hc2.symm),
        qVertexMap_line hGmem, hGc]
    · rw [show x = (oQuadModel f (oppChamber cs δ c₀ d₀ (longest cs {l, π}))).pt from
        Subtype.ext (hx.trans hq1.symm), qVertexMap_pt hGmem, hGp]
    · rw [show x = (oQuadModel f (oppChamber cs δ c₀ d₀ (longest cs {l, π}))).line from
        Subtype.ext (hx.trans hq2.symm), qVertexMap_line hGmem, hGp]
  obtain ⟨A, hA⟩ := C2E6Overlap.mem_baseStabilizer_iff.mp hσ
  have hgmem : hf.perm (oTailPerm A) ∈ typeAut cs δ :=
    hf.perm_mem_typeAut (polarFlagPerm_mem_typeAut _ _ _ p l π)
  have hgc : hf.perm (oTailPerm A) c₀ = c₀ :=
    hf.1.1 (by rw [hf.apply_perm, hc₀, oTailPerm_oC0])
  have hgd : hf.perm (oTailPerm A) d₀ = d₀ :=
    hf.1.1 (by rw [hf.apply_perm, hd₀, oTailPerm_oD0])
  have hagQ : ∀ y ∈ residue cs δ {l, π} c₀, hf.perm (oTailPerm A) y = Ψ y := by
    intro y hy
    obtain ⟨hg1, hgpt, hgline⟩ := oQuadModel_oTailPerm hf A ((hRq y).mp hy)
    refine hqm.1.injOn ((hRq _).mpr hg1) (hiso_q.1.mapsTo hy) ?_
    rw [← hG y hy]
    refine QFlag.ext ?_ ?_
    · rw [hgpt, ← hA, qVertexPerm_apply, qVertexMap_pt hGmem]
    · rw [hgline, ← hA, qVertexPerm_apply, qVertexMap_line hGmem]
  set g := hf.perm (oTailPerm A) with hgdef
  have hϑ := hΨ.inv_comp hδ hgmem hgc hgd
  have hϑc : g⁻¹ (Ψ c₀) = c₀ := by rw [hΨc, Equiv.Perm.inv_eq_iff_eq, hgc]
  have hϑd : g⁻¹ (Ψ d₀) = d₀ := by rw [hΨd, Equiv.Perm.inv_eq_iff_eq, hgd]
  have hϑQ : ∀ y ∈ residue cs δ {l, π} c₀, g⁻¹ (Ψ y) = y := fun y hy => by
    rw [Equiv.Perm.inv_eq_iff_eq, hagQ y hy]
  have hϑP : ∀ y ∈ residue cs δ {p, l} c₀, g⁻¹ (Ψ y) = y := by
    have hk : Nat.card (ZMod 2) = 2 := by rw [Nat.card_eq_fintype_card, ZMod.card]
    have hpp := oppChamber_spec hδ hcd (longest cs {p, l})
    have hpR : oppChamber cs δ c₀ d₀ (longest cs {p, l}) ∈ residue cs δ {p, l} c₀ :=
      (mem_residue_iff_mem_parabolic hδ).mpr (by rw [hpp.1]; exact (isLongest_of_finite _).1)
    exact (isPlaneFlagResidue_oC0 hpl hlπ hpπ hf hc₀).fix_of_card_two hδ hk hpl hMpl hpR hpp.1
      (hϑ.isTypeIso_residue hδ hϑc (encard_pair_le_two p l)) hϑc
      (hϑ.fix_oppChamber hδ hcd hϑc hϑd (encard_pair_le_two p l)
        (isLongest_of_finite (cs := cs) _).1)
  have hϑR : ∀ y ∈ residue cs δ {p, π} c₀, g⁻¹ (Ψ y) = y :=
    fix_residue_of_commute hδ hpπ hMpπ (hϑ.isTypeIso_residue hδ hϑc (encard_pair_le_two p π))
      (by
        rintro y (hy | hy)
        · exact hϑP y (residue_mono (Set.singleton_subset_iff.mpr (by simp)) c₀ hy)
        · exact hϑQ y (residue_mono (Set.singleton_subset_iff.mpr (by simp)) c₀ hy))
  refine ⟨A, fun y hy => ?_⟩
  have key : g⁻¹ (Ψ y) = y := by
    rcases hy with hy | hy
    · rcases mem_foundation_two_of_three hpl hlπ hpπ hι hy with h | h | h
      · exact hϑP y h
      · exact hϑQ y h
      · exact hϑR y h
    · rw [Set.mem_singleton_iff.mp hy]
      exact hϑd
  rw [Equiv.Perm.inv_eq_iff_eq] at key
  exact key.symm

theorem orth_rig₂ : Rig₂ cs δ := by
  have hcd := orth_standard_opposite hδ hpl hlπ hpπ hι hMpl hMlπ hMpπ hf hc₀ hd₀
  refine rig₂_of_transitive hδ (orth_transitive hδ hpl hlπ hpπ hι hMpl hMlπ hMpπ hf hc₀ hd₀) ?_
  intro i j hij g hg hgb hfix
  have hmem : ∀ i j : ι,
      oppChamber cs δ c₀ d₀ (longest cs {i, j}) ∈ residue cs δ {i, j} c₀ := fun i j =>
    (mem_residue_iff_mem_parabolic hδ).mpr
      ((oppChamber_spec hδ hcd _).1 ▸ (isLongest_of_finite (cs := cs) _).1)
  have hspec := fun i j : ι => (oppChamber_spec hδ hcd (longest cs {i, j})).1
  have hP := isPlaneFlagResidue_oC0 hpl hlπ hpπ hf hc₀
  have hQ := isQuadrangleFlagResidue_oC0 hpl hlπ hpπ hf hc₀
  rcases hι i with hi | hi | hi <;> rcases hι j with hj | hj | hj <;>
    rw [hi, hj] at hij hg hgb hfix ⊢
  · exact absurd rfl hij
  · exact hP.fix hδ hij hMpl (hmem p l) (hspec p l) hg hgb hfix
  · exact fix_residue_of_commute hδ hij hMpπ hg hfix
  · exact hP.swap.fix hδ hij (by rw [M.symmetric]; exact hMpl) (hmem l p) (hspec l p) hg hgb
      hfix
  · exact absurd rfl hij
  · exact hQ.fix hδ hij hMlπ (hmem l π) (hspec l π) hg hgb fun y hy => hfix y (Or.inr hy)
  · exact fix_residue_of_commute hδ hij (by rw [M.symmetric]; exact hMpπ) hg hfix
  · rw [Set.pair_comm π l] at hg hgb ⊢
    exact hQ.fix hδ hlπ hMlπ (hmem l π) (hspec l π) hg hgb fun y hy => hfix y (Or.inl hy)
  · exact absurd rfl hij

theorem orth_stabilizer :
    (∀ A : GL (Fin 2) (ZMod 2), hf.perm (oTailPerm A) ∈ typeAut cs δ ∧
      hf.perm (oTailPerm A) c₀ = c₀ ∧ hf.perm (oTailPerm A) d₀ = d₀) ∧
    (∀ g ∈ typeAut cs δ, g c₀ = c₀ → g d₀ = d₀ →
      ∃ A : GL (Fin 2) (ZMod 2), Set.EqOn g (hf.perm (oTailPerm A)) (foundation cs δ 2 c₀)) ∧
    (∀ A B : GL (Fin 2) (ZMod 2), Set.EqOn (hf.perm (oTailPerm A)) (hf.perm (oTailPerm B))
      (foundation cs δ 2 c₀) → A = B) ∧
    Nat.card {φ : foundation cs δ 2 c₀ → C //
      ∃ g ∈ typeAut cs δ, g c₀ = c₀ ∧ g d₀ = d₀ ∧ ∀ x, φ x = g x} = 6 := by
  have hfix : ∀ A : GL (Fin 2) (ZMod 2), hf.perm (oTailPerm A) ∈ typeAut cs δ ∧
      hf.perm (oTailPerm A) c₀ = c₀ ∧ hf.perm (oTailPerm A) d₀ = d₀ := fun A =>
    ⟨hf.perm_mem_typeAut (polarFlagPerm_mem_typeAut _ _ _ p l π),
      hf.1.1 (by rw [hf.apply_perm, hc₀, oTailPerm_oC0]),
      hf.1.1 (by rw [hf.apply_perm, hd₀, oTailPerm_oD0])⟩
  have hreal : ∀ g ∈ typeAut cs δ, g c₀ = c₀ → g d₀ = d₀ →
      ∃ A : GL (Fin 2) (ZMod 2), Set.EqOn g (hf.perm (oTailPerm A)) (foundation cs δ 2 c₀) := by
    intro g hg hgc hgd
    have hiso : IsWeylIsometry δ δ (foundation cs δ 2 c₀ ∪ {d₀})
        (foundation cs δ 2 c₀ ∪ {d₀}) g := by
      have hmem : ∀ y, g y ∈ foundation cs δ 2 c₀ ∪ {d₀} ↔
          y ∈ foundation cs δ 2 c₀ ∪ {d₀} := fun y => by
        have := apply_mem_foundation_union_iff hδ hg (x := c₀) (d := d₀) (y := y)
        rwa [hgc, hgd] at this
      refine isWeylIsometry_of hδ hδ (fun y hy => (hmem y).mpr hy) (fun y hy => ?_)
        (fun y _ z _ => dist_typeAut hδ hg y z)
      refine ⟨g⁻¹ y, (hmem _).mp ?_, Equiv.apply_symm_apply g y⟩
      rwa [show g (g⁻¹ y) = y from Equiv.apply_symm_apply g y]
    obtain ⟨A, hA⟩ := orth_realize hδ hpl hlπ hpπ hι hMpl hMlπ hMpπ hf hc₀ hd₀ g hiso hgc hgd
    exact ⟨A, fun y hy => (hA (Or.inl hy)).symm⟩
  have hinj : ∀ A B : GL (Fin 2) (ZMod 2), Set.EqOn (hf.perm (oTailPerm A))
      (hf.perm (oTailPerm B)) (foundation cs δ 2 c₀) → A = B := by
    intro A B hAB
    have hRq := fun y => mem_residue_lπ_oC0 hpl hlπ hpπ hf hc₀ (y := y)
    have hqm := isModelResidue_oQuadModel hpl hlπ hpπ hf hc₀
    have hR : residue cs δ {l, π} c₀ ⊆ foundation cs δ 2 c₀ :=
      residue_subset_foundation (encard_pair_le_two l π) c₀
    have hflag : ∀ F : QFlag,
        C2E6Overlap.inducedPerm (C2E6Overlap.tailIso A) F.pt =
          C2E6Overlap.inducedPerm (C2E6Overlap.tailIso B) F.pt ∧
        C2E6Overlap.inducedPerm (C2E6Overlap.tailIso A) F.line =
          C2E6Overlap.inducedPerm (C2E6Overlap.tailIso B) F.line := by
      intro F
      obtain ⟨y, hy, rfl⟩ := hqm.1.surjOn (Set.mem_univ F)
      obtain ⟨-, hA1, hA2⟩ := oQuadModel_oTailPerm hf A ((hRq y).mp hy)
      obtain ⟨-, hB1, hB2⟩ := oQuadModel_oTailPerm hf B ((hRq y).mp hy)
      rw [← hA1, ← hB1, ← hA2, ← hB2, hAB (hR hy)]
      exact ⟨rfl, rfl⟩
    refine C2E6Overlap.inducedPerm_tailIso_injective (Equiv.ext fun v => ?_)
    rcases finrank_qvertex v with hv | hv
    · obtain ⟨F, rfl⟩ := exists_qflag_pt hv
      exact (hflag F).1
    · obtain ⟨F, rfl⟩ := exists_qflag_line hv
      exact (hflag F).2
  refine ⟨hfix, hreal, hinj, ?_⟩
  rw [← C2E6Overlap.card_GL_two_zmod_two]
  refine (Nat.card_congr (Equiv.ofBijective
    (fun A : GL (Fin 2) (ZMod 2) => (⟨fun x => hf.perm (oTailPerm A) x.1,
      hf.perm (oTailPerm A), (hfix A).1, (hfix A).2.1, (hfix A).2.2, fun _ => rfl⟩ :
        {φ : foundation cs δ 2 c₀ → C //
          ∃ g ∈ typeAut cs δ, g c₀ = c₀ ∧ g d₀ = d₀ ∧ ∀ x, φ x = g x}))
    ⟨fun A B h => hinj A B fun y hy => congrFun (congrArg Subtype.val h) ⟨y, hy⟩,
      fun φ => ?_⟩)).symm
  obtain ⟨g, hg, hgc, hgd, hφ⟩ := φ.2
  obtain ⟨A, hA⟩ := hreal g hg hgc hgd
  exact ⟨A, Subtype.ext (funext fun x => by rw [hφ x, hA x.2])⟩

end Building

theorem orth_extension {ι : Type*} {M : CoxeterMatrix ι} {W : Type*} [Group W]
    {cs : CoxeterSystem M W} [Finite W] {C C' : Type*} {δ : C → C → W} {δ' : C' → C' → W}
    (hδ : IsWeylDistanceBuilding cs δ) (hδ' : IsWeylDistanceBuilding cs δ') {p l π : ι}
    (hpl : p ≠ l) (hlπ : l ≠ π) (hpπ : p ≠ π) (hι : ∀ i, i = p ∨ i = l ∨ i = π)
    (hMpl : M p l = 3) (hMlπ : M l π = 4) (hMpπ : M p π = 2) {f : C → PFlag OData}
    (hf : IsChamberModel cs δ (polarChamber OData p l π) f) {f' : C' → PFlag OData}
    (hf' : IsChamberModel cs δ' (polarChamber OData p l π) f') :
    Rig₂ cs δ ∧ Rig₂ cs δ' ∧
    ∀ (c d : C) (c' d' : C'), δ c d = longest cs Set.univ → δ' c' d' = longest cs Set.univ →
      ∀ φ : C → C', IsWeylIsometry δ δ' (foundation cs δ 2 c ∪ {d})
          (foundation cs δ' 2 c' ∪ {d'}) φ → φ c = c' → φ d = d' →
        ∃ F : C → C', IsTypeIso cs δ δ' Set.univ Set.univ F ∧
          Set.EqOn F φ (foundation cs δ 2 c ∪ {d}) ∧
          ∀ F' : C → C', IsTypeIso cs δ δ' Set.univ Set.univ F' →
            Set.EqOn F' φ (foundation cs δ 2 c ∪ {d}) → F' = F := by
  obtain ⟨c₀, hc₀⟩ := hf.1.2 oC0
  obtain ⟨d₀, hd₀⟩ := hf.1.2 oD0
  obtain ⟨c₀', hc₀'⟩ := hf'.1.2 oC0
  obtain ⟨d₀', hd₀'⟩ := hf'.1.2 oD0
  have hrig := orth_rig₂ hδ hpl hlπ hpπ hι hMpl hMlπ hMpπ hf hc₀ hd₀
  refine ⟨hrig, orth_rig₂ hδ' hpl hlπ hpπ hι hMpl hMlπ hMpπ hf' hc₀' hd₀', ?_⟩
  intro c d c' d' hcd hcd' φ hφ hφc hφd
  have htrans := orth_transitive hδ hpl hlπ hpπ hι hMpl hMlπ hMpπ hf hc₀ hd₀
  refine ext_of_transitive hδ hrig (transitive_of_standard htrans)
    (real_of_transitive hδ htrans fun Ψ hΨ hΨc hΨd => ?_) hδ' (hf.isTypeIso hf') hcd hcd' hφ
    hφc hφd
  obtain ⟨A, hA⟩ := orth_realize hδ hpl hlπ hpπ hι hMpl hMlπ hMpπ hf hc₀ hd₀ Ψ hΨ hΨc hΨd
  exact ⟨_, hf.perm_mem_typeAut (polarFlagPerm_mem_typeAut _ _ _ p l π), hA⟩

end CFSG.Monster.B.Geometry
