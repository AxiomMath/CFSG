module

public import CFSG.RankThree.GF2n.Smith81.S81TLineGen
public import CFSG.RankThree.GF2n.Smith81.S81WGeomD6
public import CFSG.RankThree.GF2n.Smith81.S81D6Basic

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.MinuscT

open CFSG.RankThree.GF2n.Smith81.E7Model CFSG.RankThree.GF2n.Smith81.D6Spin
  CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.RankThree.GF2n.Smith81.EGeom


theorem perp_root : ∀ β ∈ Perp, IsRoot .E7 β := fun _ h => h.1

theorem perp_add : ∀ β ∈ Perp, ∀ γ ∈ Perp, IsRoot .E7 (β + γ) → β + γ ∈ Perp := by
  intro β hβ γ hγ hr
  have hβ' : IsRoot .E7 β ∧ MinData.toWeight β ⬝ᵥ theta = 0 := hβ
  have hγ' : IsRoot .E7 γ ∧ MinData.toWeight γ ⬝ᵥ theta = 0 := hγ
  show IsRoot .E7 (β + γ) ∧ MinData.toWeight (β + γ) ⬝ᵥ theta = 0
  refine ⟨hr, ?_⟩
  rw [MinData.toWeight_add, add_dotProduct, hβ'.2, hγ'.2, add_zero]

theorem fin_F1_6 : ∀ k : Fin 126, pr (⟨8, by decide⟩ : Fin e7Data.d) (rt k) = -1 →
    e7Data.wt (⟨8, by decide⟩ : Fin e7Data.d) + e7Data.wt (⟨8, by decide⟩ : Fin e7Data.d) +
      MinData.toWeight (rt k) ≠ 0 := by
  unfold pr
  decide +kernel

theorem fin_F2_6 : ∀ k k' : Fin 126, pr (⟨8, by decide⟩ : Fin e7Data.d) (rt k) = -1 →
    pr (⟨8, by decide⟩ : Fin e7Data.d) (rt k') = -1 →
    e7Data.wt (⟨8, by decide⟩ : Fin e7Data.d) + MinData.toWeight (rt k) +
      (e7Data.wt (⟨8, by decide⟩ : Fin e7Data.d) + MinData.toWeight (rt k')) ≠ 0 := by
  unfold pr
  decide +kernel

theorem fin_E2_6 : ∀ b : Fin e7Data.d, pr b theta = 0 →
    (∃ k : Fin 126, MinData.toWeight (rt k) ⬝ᵥ theta = 0 ∧
      pr (⟨8, by decide⟩ : Fin e7Data.d) (rt k) = 1 ∧ pr b (rt k) = -1 ∧
      ¬ (e7Data.wt (⟨8, by decide⟩ : Fin e7Data.d) = e7Data.wt b + MinData.toWeight (rt k))) →
    e7Data.wt b = -e7Data.wt (⟨8, by decide⟩ : Fin e7Data.d) ∨
    ((∃ k : Fin 126, MinData.toWeight (rt k) ⬝ᵥ theta = 0 ∧
        pr (⟨8, by decide⟩ : Fin e7Data.d) (rt k) = -1 ∧
        e7Data.wt b = -(e7Data.wt (⟨8, by decide⟩ : Fin e7Data.d) + MinData.toWeight (rt k))) ∧
      (∃ k : Fin 126, MinData.toWeight (rt k) ⬝ᵥ theta = 0 ∧
        pr (⟨8, by decide⟩ : Fin e7Data.d) (rt k) = 0 ∧ pr b (rt k) ≠ 0)) := by
  unfold pr
  decide +kernel

theorem fin_F1_6' {γ : Rt} (hγ : IsRoot .E7 γ) (h : pr (a0 : Fin e7Data.d) γ = -1) :
    e7Data.wt (a0 : Fin e7Data.d) + e7Data.wt (a0 : Fin e7Data.d) + MinData.toWeight γ ≠ 0 := by
  have hlen : (Tag.rootCertificate .E7).roots.length = 126 := Tag.rootCertificate_length .E7
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .E7) hγ
  exact fin_F1_6 ⟨k, by omega⟩ h

theorem fin_F2_6' {γ γ' : Rt} (hγ : IsRoot .E7 γ) (hγ' : IsRoot .E7 γ')
    (h : pr (a0 : Fin e7Data.d) γ = -1) (h' : pr (a0 : Fin e7Data.d) γ' = -1) :
    e7Data.wt (a0 : Fin e7Data.d) + MinData.toWeight γ +
      (e7Data.wt (a0 : Fin e7Data.d) + MinData.toWeight γ') ≠ 0 := by
  have hlen : (Tag.rootCertificate .E7).roots.length = 126 := Tag.rootCertificate_length .E7
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .E7) hγ
  obtain ⟨k', hk', rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .E7) hγ'
  exact fin_F2_6 ⟨k, by omega⟩ ⟨k', by omega⟩ h h'

section Near

variable {K : Type} [Field K]

theorem near6_hμ {b : Idx0} (hb : ¬ Far6 (b : Fin e7Data.d)) :
    ∀ δ ∈ Perp, pr (a0 : Fin e7Data.d) δ = 1 → pr (b : Fin e7Data.d) δ = -1 →
      shift δ (b : Fin e7Data.d) = (a0 : Fin e7Data.d) := by
  intro δ hδ h1 h2
  have hδ' : IsRoot .E7 δ ∧ MinData.toWeight δ ⬝ᵥ theta = 0 := hδ
  have hlen : (Tag.rootCertificate .E7).roots.length = 126 := Tag.rootCertificate_length .E7
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .E7) hδ'.1
  by_contra hne
  exact hb ⟨⟨k, by omega⟩, hδ'.2, h1, h2, fun hw => hne (shift_eq hw)⟩

theorem single_mem_Wsp6 [CharP K 2] {b : Idx0} (hb : b ∈ Near6) :
    (Finsupp.single b 1 : W K) ∈ Wsp (Submodule.span K {p0 K}) (rootRad0 K) := by
  have hb' : ¬ Far6 (b : Fin e7Data.d) := by simpa [Near6] using hb
  exact (mem_Wsp_closure_iff rootSet0_fix).2 (mu6_W (near6_hμ hb'))

theorem mem_Wsp6_of_supported [CharP K 2] {v : W K} (hv : ∀ b : Idx0, b ∉ Near6 → v b = 0) :
    v ∈ Wsp (Submodule.span K {p0 K}) (rootRad0 K) := by
  have hmem : v ∈ Finsupp.supported K K (↑Near6 : Set Idx0) := by
    rw [Finsupp.mem_supported']
    intro b hb
    exact hv b (by simpa using hb)
  rw [Finsupp.supported_eq_span_single] at hmem
  refine (Submodule.span_le.2 ?_) hmem
  rintro _ ⟨b, hb, rfl⟩
  exact single_mem_Wsp6 (by simpa using hb)

end Near

theorem near6_pairs : ∀ b₁ b₂, NearP Perp (a0 : Fin e7Data.d) b₁ → NearP Perp (a0 : Fin e7Data.d) b₂ →
    opp b₁ ≠ b₂ := by
  rintro b₁ b₂ (rfl | ⟨γ, hγ, h1, rfl⟩) (rfl | ⟨γ', hγ', h1', rfl⟩) heq
  · exact opp_ne_self _ heq
  · have hs := opp_wt_eq heq
    rw [wt_shift (perp_root _ hγ') h1', ← add_assoc] at hs
    exact fin_F1_6' (perp_root _ hγ') h1' hs
  · have hs := opp_wt_eq heq
    rw [wt_shift (perp_root _ hγ) h1, add_right_comm] at hs
    exact fin_F1_6' (perp_root _ hγ) h1 hs
  · have hs := opp_wt_eq heq
    rw [wt_shift (perp_root _ hγ) h1, wt_shift (perp_root _ hγ') h1'] at hs
    exact fin_F2_6' (perp_root _ hγ) (perp_root _ hγ') h1 h1' hs

section Core

variable {K : Type} [Field K]

theorem d6_core [CharP K 2] {g g' : W K ≃ₗ[K] W K} (hg : g ∈ EAut0 K) (hg' : g' ∈ EAut0 K)
    {α β γ : K} (hα : α ≠ 0) (hβ : β ≠ 0) (hγ : γ ≠ 0)
    (h : α • p0 K + β • g (p0 K) = γ • g' (p0 K)) :
    g (p0 K) ∈ Wsp (Submodule.span K {p0 K}) (rootRad0 K) := by
  obtain ⟨u, hu, rfl⟩ := hg
  obtain ⟨u', hu', rfl⟩ := hg'
  obtain ⟨l, hl, hind⟩ := hu
  obtain ⟨l', hl', hind'⟩ := hu'
  have hlP : l ∈ GrpP K Perp := hl
  have hlP' : l' ∈ GrpP K Perp := hl'
  have hemb : α • (Finsupp.single (a0 : Fin e7Data.d) 1 : V K) +
      β • (l : Module.End K (V K)) (Finsupp.single (a0 : Fin e7Data.d) 1) =
      γ • (l' : Module.End K (V K)) (Finsupp.single (a0 : Fin e7Data.d) 1) := by
    have h1 := congrArg (emb K) h
    have e0 : emb K (p0 K) = Finsupp.single (a0 : Fin e7Data.d) 1 := emb_single a0 1
    have e1 : emb K ((vAut0 K).toMonoidHom u (p0 K)) =
        (l : Module.End K (V K)) (Finsupp.single (a0 : Fin e7Data.d) 1) := by
      rw [← e0]
      exact hind (p0 K)
    have e2 : emb K ((vAut0 K).toMonoidHom u' (p0 K)) =
        (l' : Module.End K (V K)) (Finsupp.single (a0 : Fin e7Data.d) 1) := by
      rw [← e0]
      exact hind' (p0 K)
    rw [map_add, map_smul, map_smul, map_smul, e0, e1, e2] at h1
    exact h1
  obtain ⟨h1, h2⟩ := line_coord_vanish perp_root perp_add near6_pairs hlP hlP' hα hβ hγ hemb
  refine mem_Wsp6_of_supported fun b hb => ?_
  have hfar : Far6 (b : Fin e7Data.d) := by simpa [Near6] using hb
  have hcoord : ((vAut0 K).toMonoidHom u (p0 K)) b =
      ((l : Module.End K (V K)) (Finsupp.single (a0 : Fin e7Data.d) 1)) (b : Fin e7Data.d) := by
    rw [← emb_apply_coe]
    have e0 : emb K (p0 K) = Finsupp.single (a0 : Fin e7Data.d) 1 := emb_single a0 1
    have := hind (p0 K)
    rw [e0] at this
    exact congrArg (fun w => w (b : Fin e7Data.d)) this
  rw [hcoord]
  have hθ : pr (b : Fin e7Data.d) theta = 0 := mem_idx0.1 b.2
  rcases fin_E2_6 (b : Fin e7Data.d) hθ hfar with hopp | ⟨⟨k, hk0, hk1, hk2⟩, ⟨k', hk0', hk1', hk2'⟩⟩
  · have hb' : opp (a0 : Fin e7Data.d) = (b : Fin e7Data.d) := opp_eq hopp
    rw [← hb']
    exact h1
  · have hgr : IsRoot .E7 (rt k) := isRoot_rt k
    have hgP : rt k ∈ Perp := ⟨hgr, hk0⟩
    have hdP : rt k' ∈ Perp := ⟨isRoot_rt k', hk0'⟩
    have hk1a : pr (a0 : Fin e7Data.d) (rt k) = -1 := hk1
    have hk2a : e7Data.wt (b : Fin e7Data.d) =
        -(e7Data.wt (a0 : Fin e7Data.d) + MinData.toWeight (rt k)) := hk2
    have hk1b : pr (a0 : Fin e7Data.d) (rt k') = 0 := hk1'
    have hbeq : opp (shift (rt k) (a0 : Fin e7Data.d)) = (b : Fin e7Data.d) := by
      apply opp_eq
      rw [wt_shift hgr hk1a]
      exact hk2a
    rw [← hbeq]
    exact h2 (rt k) hgP hk1a (rt k') hdP hk1b (by rw [hbeq]; exact hk2')

theorem d6MinuscLine [CharP K 2] : MinuscLine (EAut0 K) (p0 K) (rootRad0 K) :=
  minuscLine_of_core fun _ hg _ hg' _ _ _ hα hβ hγ h => d6_core hg hg' hα hβ hγ h

end Core

end CFSG.RankThree.GF2n.Smith81.MinuscT
