module

public import CFSG.Sporadic.Recognition.HSGraphAut

public section

namespace CFSG.Sporadic.Recognition.HSGraph

open CFSG.ComponentClassification.WittDesign

universe u v

theorem isSRGWith_of_equiv {V : Type u} {V' : Type v} [Fintype V] [Fintype V']
    {G : SimpleGraph V} {G' : SimpleGraph V'} [DecidableRel G.Adj] [DecidableRel G'.Adj]
    (φ : V ≃ V') (hφ : ∀ u w, G'.Adj (φ u) (φ w) ↔ G.Adj u w) {n k l m : ℕ}
    (h : G'.IsSRGWith n k l m) : G.IsSRGWith n k l m := by
  have hcn : ∀ u w, Fintype.card (G.commonNeighbors u w) =
      Fintype.card (G'.commonNeighbors (φ u) (φ w)) := fun u w =>
    Fintype.card_congr (φ.subtypeEquiv fun x => by
      simp only [SimpleGraph.mem_commonNeighbors, hφ])
  refine ⟨(Fintype.card_congr φ).trans h.card, fun u => ?_, fun u w hadj => ?_,
    fun u w hne hnadj => ?_⟩
  · have e : Fintype.card (G.neighborSet u) = Fintype.card (G'.neighborSet (φ u)) :=
      Fintype.card_congr (φ.subtypeEquiv fun x => by simp only [SimpleGraph.mem_neighborSet, hφ])
    rw [← SimpleGraph.card_neighborSet_eq_degree, e, SimpleGraph.card_neighborSet_eq_degree]
    exact h.regular (φ u)
  · rw [hcn]
    exact h.of_adj _ _ ((hφ u w).2 hadj)
  · rw [hcn]
    exact h.of_not_adj (fun e => hne (φ.injective e)) (fun hh => hnadj ((hφ u w).1 hh))

variable {Ω : Type u} {Ω' : Type v} {𝓑 : Finset (Finset Ω)} {𝓑' : Finset (Finset Ω')}

@[expose] def blockEquiv (e : Ω ≃ Ω') (he : ∀ B : Finset Ω, B ∈ 𝓑 ↔ B.map e.toEmbedding ∈ 𝓑') :
    {B // B ∈ 𝓑} ≃ {B // B ∈ 𝓑'} :=
  (Equiv.finsetCongr e).subtypeEquiv he

@[expose] def vertEquiv (e : Ω ≃ Ω') (he : ∀ B : Finset Ω, B ∈ 𝓑 ↔ B.map e.toEmbedding ∈ 𝓑') :
    Vert 𝓑 ≃ Vert 𝓑' :=
  Equiv.optionCongr (Equiv.sumCongr e (blockEquiv e he))

section Transport

variable (e : Ω ≃ Ω') (he : ∀ B : Finset Ω, B ∈ 𝓑 ↔ B.map e.toEmbedding ∈ 𝓑')

theorem vertEquiv_vInf : vertEquiv e he (vInf : Vert 𝓑) = vInf := rfl

theorem vertEquiv_vPt (a : Ω) : vertEquiv e he (vPt a : Vert 𝓑) = vPt (e a) := rfl

theorem vertEquiv_vBlk (B : {B // B ∈ 𝓑}) :
    vertEquiv e he (vBlk B : Vert 𝓑) = vBlk (blockEquiv e he B) := rfl

theorem blockEquiv_coe (B : {B // B ∈ 𝓑}) :
    ((blockEquiv e he B : {B // B ∈ 𝓑'}) : Finset Ω') = B.1.map e.toEmbedding := rfl

theorem adj_vertEquiv (u v : Vert 𝓑) :
    (hsGraph 𝓑').Adj (vertEquiv e he u) (vertEquiv e he v) ↔ (hsGraph 𝓑).Adj u v := by
  rcases u with _ | a | B <;> rcases v with _ | b | C <;>
    simp only [vertEquiv_vInf, vertEquiv_vPt, vertEquiv_vBlk, adj_vInf_vPt, adj_vPt_vInf,
      adj_vPt_vBlk, adj_vBlk_vPt, adj_vBlk_vBlk, not_adj_vInf_vInf, not_adj_vInf_vBlk,
      not_adj_vBlk_vInf, not_adj_vPt_vPt, blockEquiv_coe, Finset.mem_map_equiv,
      Equiv.symm_apply_apply, Finset.disjoint_map, (blockEquiv e he).injective.ne_iff]

theorem permCongr_mem_autGroup {ψ : Equiv.Perm (Vert 𝓑')} (hψ : ψ ∈ autGroup 𝓑') :
    (vertEquiv e he).permCongr.symm ψ ∈ autGroup 𝓑 := by
  intro u v
  rw [← adj_vertEquiv e he, Equiv.permCongr_symm, Equiv.permCongr_apply, Equiv.permCongr_apply]
  simp only [Equiv.symm_symm, Equiv.apply_symm_apply]
  exact (hψ _ _).trans (adj_vertEquiv e he u v)

theorem vertEquiv_symm_vInf : (vertEquiv e he).symm (vInf : Vert 𝓑') = vInf := by
  rw [Equiv.symm_apply_eq]
  rfl

theorem vertEquiv_symm_vPt (a : Ω') : (vertEquiv e he).symm (vPt a : Vert 𝓑') = vPt (e.symm a) := by
  rw [Equiv.symm_apply_eq, vertEquiv_vPt, Equiv.apply_symm_apply]

theorem vertEquiv_symm_vBlk (B : {B // B ∈ 𝓑'}) :
    (vertEquiv e he).symm (vBlk B : Vert 𝓑') = vBlk ((blockEquiv e he).symm B) := by
  rw [Equiv.symm_apply_eq, vertEquiv_vBlk, Equiv.apply_symm_apply]

theorem map_permCongrHom (σ : Equiv.Perm Ω) (B : Finset Ω) :
    (B.map e.toEmbedding).map (e.permCongrHom σ).toEmbedding =
      (B.map σ.toEmbedding).map e.toEmbedding := by
  rw [Finset.map_map, Finset.map_map]
  congr 1
  ext x
  simp [Equiv.permCongrHom]

include he in
theorem mem_blockAut_iff (σ : Equiv.Perm Ω) :
    σ ∈ blockAut 𝓑 ↔ e.permCongrHom σ ∈ blockAut 𝓑' := by
  constructor
  · intro hσ B'
    obtain ⟨B, rfl⟩ : ∃ B : Finset Ω, B' = B.map e.toEmbedding :=
      ⟨B'.map e.symm.toEmbedding, by ext x; simp [Finset.mem_map_equiv]⟩
    rw [map_permCongrHom, ← he, ← he]
    exact hσ B
  · intro hσ B
    have := hσ (B.map e.toEmbedding)
    rw [map_permCongrHom, ← he, ← he] at this
    exact this

end Transport

section Facts

variable [Fintype Ω] [DecidableEq Ω] [Fintype Ω'] [DecidableEq Ω'] (e : Ω ≃ Ω')
  (he : ∀ B : Finset Ω, B ∈ 𝓑 ↔ B.map e.toEmbedding ∈ 𝓑')

noncomputable def MData.ofEquiv (D' : MData 𝓑') : MData 𝓑 where
  carrier := D'.carrier.comap e.permCongrHom.toMonoidHom
  le σ hσ := (mem_blockAut_iff e he σ).2 (D'.le hσ)
  card := by
    have h : Nat.card (D'.carrier.comap e.permCongrHom.toMonoidHom) = Nat.card D'.carrier :=
      Nat.card_congr (e.permCongrHom.toEquiv.subtypeEquiv fun σ => Iff.rfl)
    rw [h, D'.card]
  simple := by
    have := D'.simple
    exact (MulEquiv.ofBijective (e.permCongrHom.toMonoidHom.subgroupComap D'.carrier)
      ⟨e.permCongrHom.toMonoidHom.subgroupComap_injective _ e.permCongrHom.injective,
        e.permCongrHom.toMonoidHom.subgroupComap_surjective _ e.permCongrHom.surjective⟩
      ).isSimpleGroup
  pt a b := by
    obtain ⟨τ, hτ, h⟩ := D'.pt (e a) (e b)
    refine ⟨e.permCongrHom.symm τ, ?_, ?_⟩
    · change e.permCongrHom (e.permCongrHom.symm τ) ∈ D'.carrier
      rwa [MulEquiv.apply_symm_apply]
    · simp only [Equiv.permCongrHom_symm]
      change e.symm (τ (e a)) = b
      rw [h, Equiv.symm_apply_apply]
  blk B hB C hC := by
    obtain ⟨τ, hτ, h⟩ := D'.blk _ ((he B).1 hB) _ ((he C).1 hC)
    refine ⟨e.permCongrHom.symm τ, ?_, ?_⟩
    · change e.permCongrHom (e.permCongrHom.symm τ) ∈ D'.carrier
      rwa [MulEquiv.apply_symm_apply]
    · have := map_permCongrHom e (e.permCongrHom.symm τ) B
      rw [MulEquiv.apply_symm_apply, h] at this
      exact Finset.map_inj.1 this.symm

include he in
theorem HSFacts.of_equiv (F : HSFacts 𝓑') : HSFacts 𝓑 where
  card_aut := by
    have h : Nat.card (blockAut 𝓑) = Nat.card (blockAut 𝓑') :=
      Nat.card_congr (e.permCongrHom.toEquiv.subtypeEquiv (mem_blockAut_iff e he))
    rw [h, F.card_aut]
  mdata := by
    obtain ⟨D'⟩ := F.mdata
    exact ⟨MData.ofEquiv e he D'⟩
  srg := isSRGWith_of_equiv (vertEquiv e he) (adj_vertEquiv e he) F.srg
  psi := by
    obtain ⟨ψ, hψ, a, B, h1, h2⟩ := F.psi
    refine ⟨(vertEquiv e he).permCongr.symm ψ, permCongr_mem_autGroup e he hψ, e.symm a,
      (blockEquiv e he).symm B, ?_, ?_⟩
    · change (vertEquiv e he).symm (ψ (vertEquiv e he vInf)) = _
      rw [vertEquiv_vInf, h1, vertEquiv_symm_vPt]
    · change (vertEquiv e he).symm (ψ (vertEquiv e he (vPt (e.symm a)))) = _
      rw [vertEquiv_vPt, Equiv.apply_symm_apply, h2, vertEquiv_symm_vBlk]
  odd := by
    obtain ⟨s, hs, hsinf, hsign⟩ := F.odd
    refine ⟨(vertEquiv e he).permCongr.symm s, permCongr_mem_autGroup e he hs, ?_, ?_⟩
    · change (vertEquiv e he).symm (s (vertEquiv e he vInf)) = vInf
      rw [vertEquiv_vInf, hsinf, vertEquiv_symm_vInf]
    · rw [Equiv.permCongr_symm, Equiv.Perm.sign_permCongr]
      exact hsign

end Facts

end CFSG.Sporadic.Recognition.HSGraph
