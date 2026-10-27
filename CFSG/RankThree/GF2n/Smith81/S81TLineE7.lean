module

public import CFSG.RankThree.GF2n.Smith81.S81TLineGen
public import CFSG.RankThree.GF2n.Smith81.S81WGeomE7

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.MinuscT

open CFSG.RankThree.GF2n.Smith81.E7Model CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley
  CFSG.RankThree.GF2n.Smith81.EGeom


@[expose] def allRoots : Set Rt := {γ | IsRoot .E7 γ}

theorem allRoots_root : ∀ β ∈ allRoots, IsRoot .E7 β := fun _ h => h

theorem allRoots_add : ∀ β ∈ allRoots, ∀ γ ∈ allRoots, IsRoot .E7 (β + γ) → β + γ ∈ allRoots :=
  fun _ _ _ _ h => h

theorem fin_F1 : ∀ k : Fin 126, pr i7 (rt k) = -1 →
    e7Data.wt i7 + e7Data.wt i7 + MinData.toWeight (rt k) ≠ 0 := by
  unfold pr
  decide +kernel

theorem fin_F2 : ∀ k k' : Fin 126, pr i7 (rt k) = -1 → pr i7 (rt k') = -1 →
    e7Data.wt i7 + MinData.toWeight (rt k) + (e7Data.wt i7 + MinData.toWeight (rt k')) ≠ 0 := by
  unfold pr
  decide +kernel

theorem fin_E2 : ∀ b : Fin e7Data.d, Far7 b →
    e7Data.wt b = -e7Data.wt i7 ∨
    ((∃ k : Fin 126, pr i7 (rt k) = -1 ∧
        e7Data.wt b = -(e7Data.wt i7 + MinData.toWeight (rt k))) ∧
      (∃ k : Fin 126, pr i7 (rt k) = 0 ∧ pr b (rt k) ≠ 0)) := by
  unfold Far7 pr
  decide +kernel

theorem fin_F1' {γ : Rt} (hγ : IsRoot .E7 γ) (h : pr i7 γ = -1) :
    e7Data.wt i7 + e7Data.wt i7 + MinData.toWeight γ ≠ 0 := by
  have hlen : (Tag.rootCertificate .E7).roots.length = 126 := Tag.rootCertificate_length .E7
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .E7) hγ
  exact fin_F1 ⟨k, by omega⟩ h

theorem fin_F2' {γ γ' : Rt} (hγ : IsRoot .E7 γ) (hγ' : IsRoot .E7 γ') (h : pr i7 γ = -1)
    (h' : pr i7 γ' = -1) :
    e7Data.wt i7 + MinData.toWeight γ + (e7Data.wt i7 + MinData.toWeight γ') ≠ 0 := by
  have hlen : (Tag.rootCertificate .E7).roots.length = 126 := Tag.rootCertificate_length .E7
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .E7) hγ
  obtain ⟨k', hk', rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .E7) hγ'
  exact fin_F2 ⟨k, by omega⟩ ⟨k', by omega⟩ h h'

section Near

variable {K : Type} [Field K]

theorem near7_hμ {b : Fin e7Data.d} (hb : ¬ Far7 b) :
    ∀ δ : Rt, IsRoot .E7 δ → pr i7 δ = 1 → pr b δ = -1 → shift δ b = i7 := by
  intro δ hδ h1 h2
  have hlen : (Tag.rootCertificate .E7).roots.length = 126 := Tag.rootCertificate_length .E7
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .E7) hδ
  by_contra hne
  exact hb ⟨⟨k, by omega⟩, h1, h2, fun hw => hne (shift_eq hw)⟩

theorem single_mem_Wsp7 [CharP K 2] {b : Fin e7Data.d} (hb : b ∈ Near7) :
    (Finsupp.single b 1 : V K) ∈ Wsp (Submodule.span K {(w0 : V K)}) (rootRad7 K) := by
  have hb' : ¬ Far7 b := by simpa [Near7] using hb
  exact (mem_Wsp_closure_iff rootSet7_fix).2 (mu7_W (near7_hμ hb'))

theorem mem_Wsp7_of_supported [CharP K 2] {v : V K} (hv : ∀ b, b ∉ Near7 → v b = 0) :
    v ∈ Wsp (Submodule.span K {(w0 : V K)}) (rootRad7 K) := by
  have hmem : v ∈ Finsupp.supported K K (↑Near7 : Set (Fin e7Data.d)) := by
    rw [Finsupp.mem_supported']
    intro b hb
    exact hv b (by simpa using hb)
  rw [Finsupp.supported_eq_span_single] at hmem
  refine (Submodule.span_le.2 ?_) hmem
  rintro _ ⟨b, hb, rfl⟩
  exact single_mem_Wsp7 (by simpa using hb)

end Near

theorem near7_pairs : ∀ b₁ b₂, NearP allRoots i7 b₁ → NearP allRoots i7 b₂ → opp b₁ ≠ b₂ := by
  rintro b₁ b₂ (rfl | ⟨γ, hγ, h1, rfl⟩) (rfl | ⟨γ', hγ', h1', rfl⟩) heq
  · exact opp_ne_self _ heq
  · have hs := opp_wt_eq heq
    rw [wt_shift hγ' h1', ← add_assoc] at hs
    exact fin_F1' hγ' h1' hs
  · have hs := opp_wt_eq heq
    rw [wt_shift hγ h1, add_right_comm] at hs
    exact fin_F1' hγ h1 hs
  · have hs := opp_wt_eq heq
    rw [wt_shift hγ h1, wt_shift hγ' h1'] at hs
    exact fin_F2' hγ hγ' h1 h1' hs

section Core

variable {K : Type} [Field K]

theorem e7_core [CharP K 2] {g g' : V K ≃ₗ[K] V K} (hg : g ∈ EAut K) (hg' : g' ∈ EAut K)
    {α β γ : K} (hα : α ≠ 0) (hβ : β ≠ 0) (hγ : γ ≠ 0)
    (h : α • (w0 : V K) + β • g (w0 : V K) = γ • g' (w0 : V K)) :
    g (w0 : V K) ∈ Wsp (Submodule.span K {(w0 : V K)}) (rootRad7 K) := by
  obtain ⟨l, hl, rfl⟩ := hg
  obtain ⟨l', hl', rfl⟩ := hg'
  have hlP : l ∈ GrpP K allRoots := hl
  have hlP' : l' ∈ GrpP K allRoots := hl'
  have h' : α • (Finsupp.single i7 1 : V K) + β • (l : Module.End K (V K)) (Finsupp.single i7 1) =
      γ • (l' : Module.End K (V K)) (Finsupp.single i7 1) := h
  obtain ⟨h1, h2⟩ := line_coord_vanish allRoots_root allRoots_add near7_pairs hlP hlP' hα hβ hγ h'
  refine mem_Wsp7_of_supported fun b hb => ?_
  have hfar : Far7 b := by simpa [Near7] using hb
  show ((l : Module.End K (V K)) (Finsupp.single i7 1)) b = 0
  rcases fin_E2 b hfar with hopp | ⟨⟨k, hk1, hk2⟩, ⟨k', hk1', hk2'⟩⟩
  · have hb' : opp i7 = b := opp_eq hopp
    rw [← hb']
    exact h1
  · have hgr : IsRoot .E7 (rt k) := isRoot_rt k
    have hbeq : opp (shift (rt k) i7) = b := by
      apply opp_eq
      rw [wt_shift hgr hk1]
      exact hk2
    rw [← hbeq]
    exact h2 (rt k) hgr hk1 (rt k') (isRoot_rt k') hk1' (by rw [hbeq]; exact hk2')

theorem e7MinuscLine [CharP K 2] : MinuscLine (EAut K) (w0 : V K) (rootRad7 K) :=
  minuscLine_of_core fun _ hg _ hg' _ _ _ hα hβ hγ h => e7_core hg hg' hα hβ hγ h

end Core

end CFSG.RankThree.GF2n.Smith81.MinuscT
