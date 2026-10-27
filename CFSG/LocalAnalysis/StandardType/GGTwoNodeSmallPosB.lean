module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallPosK
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallPosModel
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallPosCycle
public import Certificates.Certificate708601
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallTransport

public section

namespace CFSG.TwoNodeSmall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma pgb_posBCell_bound {p N : ℕ} {P : SPt} (h : P ∈ posBCell p N) :
    P.pt.bound = posBound p N := by
  simp only [posBCell, List.mem_flatMap, List.mem_map] at h
  obtain ⟨s, -, o, -, fr, -, rfl⟩ := h
  rfl

theorem lr6SmallRankPosB_of_closed
    (hcl : ∀ Q ∈ posBPts (), ∀ [Fact Q.pt.p.Prime], Q.ClosedPosB) : CFSG.StandardType.LR6SmallRankPosB := by
  intro p N _ hcell V _ _ hV h α x r ha αa t hF hr ht hha hx hsp hK hnt hcard
  obtain ⟨S, MK, CK, ⟨s, hs, hS⟩, hW, hC, hpair, hc, htri, -⟩ := hK
  have hchain : ∀ i j : ↥S, ((CK (some i) (some j) : ℤ) : ZMod p) =
      ((CartanMatrix.A (N - 1) (i : Fin (N - 1)) (j : Fin (N - 1)) : ℤ) : ZMod p) := by
    intro i j
    rw [hpair (some i) (some j)]
    exact hF.pair i j
  have hself : ((CK none none : ℤ) : ZMod p) = 2 := by
    rw [hpair none none]
    exact hha
  obtain ⟨o, ho, hoCK⟩ := cellA_kopts p N hcell s hs S hS MK CK hW hC hchain hself hc
  have hH : ∀ j : Fin (N - 1), s ≤ (j : ℕ) → (j : ℕ) < s + (N - 3) →
      α j ha = (((if (j : ℕ) - s = o.1 then o.2.1 else 0 : ℕ)) : ZMod p) := by
    intro j h1 h2
    have hj : j ∈ S := (hS j).2 ⟨h1, h2⟩
    have h3 := (hoCK ⟨j, hj⟩).1
    rw [hpair (some ⟨j, hj⟩) none] at h3
    exact h3
  have hA : ∀ j : Fin (N - 1), s ≤ (j : ℕ) → (j : ℕ) < s + (N - 3) →
      αa (h j) = (((if (j : ℕ) - s = o.1 then o.2.2 else 0 : ℕ)) : ZMod p) := by
    intro j h1 h2
    have hj : j ∈ S := (hS j).2 ⟨h1, h2⟩
    have h3 := (hoCK ⟨j, hj⟩).2
    rw [hpair none (some ⟨j, hj⟩)] at h3
    exact h3
  obtain ⟨D, nF, gens, x', b, hmemL, c, hc0, e, hM⟩ :=
    posb_model p N hcell hV h α x ha αa hF hha hsp s hs o ho hH hA
  let P : Pt := ⟨p, D, nF, gens, x', b⟩
  let Q : SPt := ⟨P, s⟩
  have hb : P.bound = posBound p N := pgb_posBCell_bound hmemL
  haveI : Fact P.p.Prime := ‹Fact p.Prime›
  have hQ : Q ∈ posBPts () := by
    simp only [posBPts, List.mem_append, or_assoc]
    rcases hcell with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl hmemL
    · exact Or.inr (Or.inl hmemL)
    · exact Or.inr (Or.inr hmemL)
  have hQcl : Q.ClosedPosB := hcl Q hQ
  have hfinish : (∃ g ∈ CFSG.StandardType.lr6Group r t, IsTransv g) ∨
      P.bound < Nat.card ↥(CFSG.StandardType.lr6Group r t) ∨
      (∃ v : V, (∀ i, α i v = 0) ∧ v ∉ Submodule.span (ZMod p) {c • x}) ∨
      CFSG.StandardType.ZS.LinWeyl p (CFSG.StandardType.lr6Group r t) →
      CFSG.StandardType.ZS.LinWeyl p (CFSG.StandardType.lr6Group r t) := by
    rintro (⟨g, hg, hgt⟩ | hlt | ⟨v, hv, hvx⟩ | hweyl)
    · exact absurd hgt (hnt g hg)
    · exfalso
      have hlt' : posBound p N < Nat.card ↥(CFSG.StandardType.lr6Group r t) := hb ▸ hlt
      rw [posBound_eq] at hlt'
      exact absurd hcard (not_le.mpr hlt')
    · exfalso
      apply hvx
      have hxmem : x ∈ Submodule.span (ZMod p) {c • x} := by
        have h1 : c⁻¹ • (c • x) ∈ Submodule.span (ZMod p) {c • x} :=
          Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton (c • x)))
        rwa [inv_smul_smul₀ hc0] at h1
      exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hxmem) (hF.fix v hv)
    · exact hweyl
  rcases hQcl with hfix | hnwf | htransv | hcyc | hbound | hweyl
  · exfalso
    have hz : αa (c • x) = 0 := alphaFixed_models hM hfix
    rw [map_smul, smul_eq_mul] at hz
    exact (mul_eq_zero.mp hz).elim hc0 hx
  · exfalso
    apply hnwf
    refine wf_of_models hM (fun i => ?_) hha
    rw [hF.pair i i]
    simp [CartanMatrix.A]
  · exact hfinish (Pt.facts_transport P h α (c • x) r ha αa t hr ht e hM (Or.inl htransv))
  · exfalso
    have hS' : ∀ i : Fin (N - 1), i ∈ S ↔ s ≤ (i : ℕ) ∧ (i : ℕ) < s + ((N - 1) - 2) := by
      intro i
      rw [hS i]
      have hN' : (N - 1) - 2 = N - 3 := by omega
      rw [hN']
    exact (cycleAt_models hM r t hr ht s hs S hS' hcyc) (htri hcyc.1)
  · exact hfinish (Pt.facts_transport P h α (c • x) r ha αa t hr ht e hM (Or.inr (Or.inl hbound)))
  · exact hfinish (Pt.facts_transport P h α (c • x) r ha αa t hr ht e hM
      (Or.inr (Or.inr (Or.inr hweyl))))

end CFSG.TwoNodeSmall

namespace CFSG.StandardType

theorem lr6SmallRankPosB_of_certificate :
    LR6SmallRankPosB :=
  CFSG.TwoNodeSmall.lr6SmallRankPosB_of_closed Certificates.certificate708601

end CFSG.StandardType
