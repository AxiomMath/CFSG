module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection2.Basic

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 2, Proposition (2.3)

This file proves Peterfalvi (2.3).  No result from BG is imported here.
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section2

universe u

private theorem elementCentralizer_le_L_of_trivial_Hypothesis2 {G : Type u}
    [Group G] [Finite G] {A : Set G} {L : Subgroup G}
    (h : Hypothesis2 A L (fun _ : G => ⊥)) {a : G} (ha : a ∈ A) :
    elementCentralizer a ≤ L := by
  intro c hc
  have hprod := h.centralizer_eq_product ha
  rcases hprod.mul_surjective c hc with ⟨z, hz, k, hk, hkEq⟩
  have hz1 : z = 1 := by simpa using hz
  subst z
  have hkEq' : c = k := by simpa using hkEq
  have hkL : (k : G) ∈ L := (Subgroup.mem_inf.mp hk).1
  simpa [hkEq'] using hkL

private theorem mem_L_of_intersection_of_trivial_Hypothesis2 {G : Type u}
    [Group G] [Finite G] {A : Set G} {L : Subgroup G}
    (h : Hypothesis2 A L (fun _ : G => ⊥)) {g : G}
    (hg : (A ∩ conjugateImage A g).Nonempty) : g ∈ L := by
  rcases hg with ⟨z, hzA, hzconj⟩
  rcases hzconj with ⟨a, ha, hza⟩
  have hconj : conjugateIn a z := ⟨g, hza.symm⟩
  rcases h.G_conjugate_imp_L_conjugate ha hzA hconj with ⟨x, hxeq⟩
  have hxeq' : conjBy (x : G) a = conjBy g a := hxeq.trans hza
  have hcomm : (x : G)⁻¹ * g * a = a * ((x : G)⁻¹ * g) := by
    have := congrArg (fun t : G => (x : G)⁻¹ * t * g) hxeq'
    simpa [conjBy, mul_assoc] using this.symm
  have hxgCent : (x : G)⁻¹ * g ∈ elementCentralizer a := by
    unfold elementCentralizer
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    rw [Set.mem_singleton_iff] at hb
    subst hb
    simpa [mul_assoc] using hcomm.symm
  have hxgL : (x : G)⁻¹ * g ∈ L :=
    elementCentralizer_le_L_of_trivial_Hypothesis2 h ha hxgCent
  have hgL : g ∈ L := by
    have := L.mul_mem x.2 hxgL
    simpa [mul_assoc] using this
  exact hgL

public theorem proposition_2_3 {G : Type u} [Group G] [Finite G]
    (A : Set G) (L : Subgroup G) :
    A.Nonempty →
      (IsTISubsetWithNormalizer A L ↔ Hypothesis2 A L (fun _ : G => ⊥)) := by
  intro hAne
  constructor
  · intro hTIL
    rcases hTIL with ⟨hAne', hnontriv, hTI, hnormEq⟩
    refine ⟨?subset_punctured, ?subset_L, ?L_le_normalizer,
      ?G_conjugate_imp_L_conjugate, ?centralizer_eq_product, ?coprime_orders⟩
    · exact hnontriv
    · intro a ha
      have hinter : (A ∩ conjugateImage A a).Nonempty := by
        refine ⟨a, ha, ?_⟩
        refine ⟨a, ha, ?_⟩
        simp [conjBy]
      have hnorm : a ∈ setNormalizer A := by
        simpa [setNormalizer] using hTI a hinter
      simpa [hnormEq] using hnorm
    ·
      simp [hnormEq]
    · intro a b ha hb hconj
      rcases hconj with ⟨g, hg⟩
      have hinter : (A ∩ conjugateImage A g).Nonempty := by
        refine ⟨b, hb, ?_⟩
        exact ⟨a, ha, hg.symm⟩
      have hnorm : g ∈ setNormalizer A := by
        simpa [setNormalizer] using hTI g hinter
      have hgL : g ∈ L := by
        simpa [hnormEq] using hnorm
      exact ⟨⟨g, hgL⟩, hg⟩
    · intro a ha
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro x hx
        have hx1 : x = 1 := by simpa using hx
        subst hx1
        simp [elementCentralizer]
      · simp [centralizerIn]
      · intro k hk h hh
        have hh1 : h = 1 := by simpa using hh
        subst h
        simp [conjBy]
      · simp [centralizerIn]
      · intro c hc
        have hcomm : a * c = c * a := by
          unfold elementCentralizer at hc
          rw [Subgroup.mem_centralizer_iff] at hc
          exact hc a (by simp)
        have hfix : conjBy c a = a := by
          calc
            conjBy c a = c * a * c⁻¹ := by rfl
            _ = a := by
              calc
                c * a * c⁻¹ = a * c * c⁻¹ := by rw [← hcomm]
                _ = a := by simp [mul_assoc]
        have hinter : (A ∩ conjugateImage A c).Nonempty := by
          refine ⟨a, ha, ?_⟩
          exact ⟨a, ha, hfix.symm⟩
        have hnorm : c ∈ setNormalizer A := by
          simpa [setNormalizer] using hTI c hinter
        have hcL : c ∈ L := by
          simpa [hnormEq] using hnorm
        refine ⟨1, by simp, c, ⟨hcL, hc⟩, by simp⟩
    · intro a b ha hb
      simp
  · intro hH2
    refine ⟨hAne, ?_, ?_, ?_⟩
    · exact hH2.subset_punctured
    · intro g hg
      have hgL : g ∈ L := mem_L_of_intersection_of_trivial_Hypothesis2 hH2 hg
      have hnorm : g ∈ setNormalizer A := hH2.L_le_normalizer hgL
      simpa [setNormalizer] using hnorm
    ·
      apply le_antisymm
      · intro g hg
        rcases hAne with ⟨a, ha⟩
        have hgaA : conjBy g a ∈ A := (hg a).2 ha
        have hinter : (A ∩ conjugateImage A g).Nonempty := by
          refine ⟨conjBy g a, hgaA, ?_⟩
          exact ⟨a, ha, rfl⟩
        exact mem_L_of_intersection_of_trivial_Hypothesis2 hH2 hinter
      · exact hH2.L_le_normalizer

end CFSG.Section2
