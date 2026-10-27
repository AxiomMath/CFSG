module

public import CFSG.Monster.B.GSide.MuFourOmega
public import CFSG.Monster.B.GSide.HomotopyRonanNative

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open SimpleGraph CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam CFSG.Monster.B.TwoA.Unitary

def cvMulHom
    (s : Shat) : cgraph →g cgraph where
  toFun x := cvMul x s
  map_rel' h := (cgraph_adj_cvMul _ _ s).2 h

theorem cpsi_mem_commonNeighbors
    {v w a : cPi0} (hxy : cpsi v ≠ cpsi w)
    (hn : ¬ omegaGraph.Adj (cpsi v) (cpsi w)) (hv : cgraph.Adj v.1 a.1) (hw : cgraph.Adj w.1 a.1) :
    cpsi a ∈ omegaGraph.commonNeighbors (cpsi v) (cpsi w) := by
  have hv' := (cgraphPi_adj_iff (fun e => hv.ne (congrArg Subtype.val e))).1 hv
  have hw' := (cgraphPi_adj_iff (fun e => hw.ne (congrArg Subtype.val e))).1 hw
  rw [SimpleGraph.mem_commonNeighbors]
  rcases hv' with e | hva
  · rcases hw' with e' | hwa
    · exact absurd (e.trans e'.symm) hxy
    · exact absurd (e ▸ hwa).symm hn
  · rcases hw' with e' | hwa
    · exact absurd (e' ▸ hva) hn
    · exact ⟨hva, hwa⟩

theorem preconnected_mu_cPi0
    {v w : cPi0} (hvw : v ≠ w) (hn : ¬ cgraph.Adj v.1 w.1)
    (hsub : cgraph.commonNeighbors v.1 w.1 ⊆ cPi0) :
    (cgraph.induce (cgraph.commonNeighbors v.1 w.1)).Preconnected := by
  have hxy : cpsi v ≠ cpsi w ∧ ¬ omegaGraph.Adj (cpsi v) (cpsi w) := by
    have h := (cgraphPi_adj_iff hvw).not.1 hn
    exact ⟨fun e => h (Or.inl e), fun e => h (Or.inr e)⟩
  have hsurj : Function.Surjective cpsi := fun x => by
    obtain ⟨k, hk⟩ := piPt_surjective x
    exact ⟨piV k, (cpsi_piV k).trans hk⟩
  have hS := preconnected_induce_preimage (G := cgraphPi) hsurj (fun _ _ h => cgraphPi_adj_iff h)
    (preconnected_mu_omega hxy.1 hxy.2)
  refine preconnected_induce_of_surjOn (Embedding.induce cPi0).toHom (fun a ha => ?_)
    (fun u hu => ?_) hS
  · rw [Set.mem_preimage, SimpleGraph.mem_commonNeighbors] at ha
    have hva : v ≠ a := fun e => ha.1.ne (by rw [e])
    have hwa : w ≠ a := fun e => ha.2.ne (by rw [e])
    exact ⟨(cgraphPi_adj_iff hva).2 (Or.inr ha.1), (cgraphPi_adj_iff hwa).2 (Or.inr ha.2)⟩
  · exact ⟨⟨u, hsub hu⟩, cpsi_mem_commonNeighbors hxy.1 hxy.2 hu.1 hu.2, rfl⟩

theorem cgraph_mu_connected_of_mem_sphereFour
    (v w : CVert) (hw : w ∈ sphereFour v) :
    (cgraph.induce (cgraph.commonNeighbors v w)).Connected := by
  obtain ⟨-, hcard, ⟨s, hvs, hws⟩, -, hsub⟩ :=
    native_coset_graph_order_four_common_neighbors.1 v w hw
  obtain ⟨hne, hna, -⟩ := cgraph_dist_eq_two_iff.1 hw.1
  have hv' : cvMul v s⁻¹ ∈ cPi0 := mem_cPi_iff.1 hvs
  have hw' : cvMul w s⁻¹ ∈ cPi0 := mem_cPi_iff.1 hws
  have hsub' : cgraph.commonNeighbors (cvMul v s⁻¹) (cvMul w s⁻¹) ⊆ cPi0 := by
    intro u hu
    rw [SimpleGraph.mem_commonNeighbors] at hu
    have hu' : cvMul u s ∈ cgraph.commonNeighbors v w := by
      rw [SimpleGraph.mem_commonNeighbors, ← cvMul_inv_cancel' v s, ← cvMul_inv_cancel' w s]
      exact ⟨(cgraph_adj_cvMul _ _ s).2 hu.1, (cgraph_adj_cvMul _ _ s).2 hu.2⟩
    have h := mem_cPi_iff.1 (hsub s hvs hws hu')
    rwa [cvMul_inv_cancel] at h
  have hpre := preconnected_mu_cPi0 (v := ⟨_, hv'⟩) (w := ⟨_, hw'⟩)
    (fun e => hne (cvMul_injective _ (congrArg Subtype.val e)))
    (fun h => hna ((cgraph_adj_cvMul _ _ _).1 h)) hsub'
  have hpre' : (cgraph.induce (cgraph.commonNeighbors v w)).Preconnected := by
    refine preconnected_induce_of_surjOn (cvMulHom s) (fun u hu => ?_) (fun u hu => ?_) hpre
    · rw [SimpleGraph.mem_commonNeighbors] at hu ⊢
      rw [← cvMul_inv_cancel' v s, ← cvMul_inv_cancel' w s]
      exact ⟨(cgraph_adj_cvMul _ _ s).2 hu.1, (cgraph_adj_cvMul _ _ s).2 hu.2⟩
    · refine ⟨cvMul u s⁻¹, ?_, cvMul_inv_cancel' u s⟩
      rw [SimpleGraph.mem_commonNeighbors] at hu ⊢
      exact ⟨(cgraph_adj_cvMul _ _ _).2 hu.1, (cgraph_adj_cvMul _ _ _).2 hu.2⟩
  have : Nonempty (cgraph.commonNeighbors v w) :=
    (Set.nonempty_of_ncard_ne_zero (by rw [hcard]; norm_num)).to_subtype
  exact ⟨hpre'⟩

theorem cgraph_triangulable_of_local
    (B0 : ∀ x y : CVert, cgraph.dist x y ≤ 3)
    (B2tri : ∀ v x y : CVert, cgraph.dist v x = 2 → cgraph.dist v y = 2 → cgraph.Adj x y →
      ∃ c, cgraph.Adj v c ∧ cgraph.Adj c x ∧ cgraph.Adj c y)
    (B3loc : ∀ v u c : CVert, cgraph.dist v u = 3 → cgraph.Adj u c → cgraph.dist v c = 2 →
      c ∈ sphereFour v)
    (B3con : ∀ v u : CVert, cgraph.dist v u = 3 →
      (cgraph.induce (cgraph.neighborSet u ∩ sphereFour v)).Connected)
    (B3tri : ∀ v x y : CVert, cgraph.dist v x = 3 → cgraph.dist v y = 3 → cgraph.Adj x y →
      ∃ h, cgraph.dist v h = 2 ∧ cgraph.Adj h x ∧ cgraph.Adj h y) :
    CFSG.Monster.B.Recog.Triangulable cgraph :=
  cgraph_triangulable_of B0 cgraph_mu_connected_of_mem_sphereFour B2tri B3loc B3con B3tri

end CFSG.Monster.B.GSide
