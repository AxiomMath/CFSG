module

public import CFSG.Sporadic.Schreier.PairClasses

public noncomputable section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates CFSG.Certificates.ChainArrays CFSG.Certificates.Native CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.PairNative

variable {n : ℕ}

theorem closureEntries_perm {Q : RawSchreierDatum n} {O S : Array (Array ℕ)} {base : Array ℕ}
    {W : Array (List ℤ)} {chunks : ℕ} (hA : ChainArrays Q O S base W)
    (hF : ChainCheckFacts n O S base W chunks) (hQ : ValidSchreier Q) {bs : List ℕ}
    (hH : BaseFaithful Q.originalSubgroup bs) (hbs : ∀ b ∈ bs, b < n)
    {gens gensInv : Array (Array ℕ)} {gg : ℕ → Equiv.Perm (Fin n)}
    (hg : ∀ l < gens.size,
      Rep n gens[l]! (gg l) ∧ Rep n gensInv[l]! (gg l)⁻¹ ∧ gg l ∈ Q.originalSubgroup)
    (XG : List (Equiv.Perm (Fin n)))
    (hclosed : ∀ c ∈ Q.originalSubgroup, ∀ x ∈ XG, c * x * c⁻¹ ∈ XG)
    (cl : List (List (Array ℕ) × Array (Array ℕ) × Array ℕ × Array ℕ))
    (h1 : ∀ c ∈ cl, ∃ x ∈ XG, RepW n c.1 x ∧ x ∈ Q.originalSubgroup)
    (h2 : ∀ c ∈ cl,
      closureOK (rawLevels n S base) bs gens gensInv c.1 c.2.1 c.2.2.1 c.2.2.2 = true)
    (h3 : keysDistinctNF n (rawLevels n S base) bs (cl.map fun c => c.2.1) = true)
    (h4 : (cl.map fun c => c.2.1.size).sum = XG.length) :
    ((cl.flatMap fun c => c.2.1.toList).map (nfElt n S base)).Perm XG := by
  set U := cl.flatMap fun c => c.2.1.toList
  have hentry : ∀ c ∈ cl, ∃ x ∈ XG, RepW n c.1 x ∧ x ∈ Q.originalSubgroup ∧
      ∀ nf ∈ c.2.1.toList, nfOK (rawLevels n S base) nf = true ∧
        ∃ d ∈ Q.originalSubgroup, nfElt n S base nf = d * x * d⁻¹ := by
    intro c hc
    obtain ⟨x, hx, hrep, hxH⟩ := h1 c hc
    refine ⟨x, hx, hrep, hxH, fun nf hnf => ?_⟩
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hnf
    rw [Array.length_toList] at hk
    have := closureOK_spec hA hF hQ hH hbs hg hrep hxH (h2 c hc) k hk
    rw [getElem!_pos c.2.1 k hk] at this
    simpa [Array.getElem_toList] using this
  have hU : ∀ nf ∈ U, nfOK (rawLevels n S base) nf = true ∧ nfElt n S base nf ∈ XG := by
    intro nf hnf
    obtain ⟨c, hc, hnf⟩ := List.mem_flatMap.1 hnf
    obtain ⟨x, hx, -, -, hall⟩ := hentry c hc
    obtain ⟨hok, d, hd, he⟩ := hall nf hnf
    exact ⟨hok, he ▸ hclosed d hd x hx⟩
  have hkeys : (U.map fun nf => keyElt n bs (nfElt n S base nf)).Nodup := by
    have hsorted := (pairwise_of_strictInc h3).imp (fun hab => Nat.ne_of_lt hab)
    have hk := (List.mergeSort_perm _ _).nodup_iff.1 hsorted
    rw [List.flatMap_map] at hk
    have e : (cl.flatMap fun c => c.2.1.toList.map fun nf =>
        imgKey n (baseImgs bs (nfWord (rawLevels n S base) nf))) =
        U.map fun nf => keyElt n bs (nfElt n S base nf) := by
      rw [List.map_flatMap]
      refine List.flatMap_congr fun c hc => List.map_congr_left fun nf hnf => ?_
      exact imgKey_baseImgs hbs (repW_nfWord hA hF (hU nf (List.mem_flatMap.2 ⟨c, hc, hnf⟩)).1)
    rwa [e] at hk
  have hnodup : (U.map (nfElt n S base)).Nodup := by
    have h' : ((U.map (nfElt n S base)).map (keyElt n bs)).Nodup := by
      rw [List.map_map]
      exact hkeys
    exact h'.of_map _
  have hsub : U.map (nfElt n S base) ⊆ XG := by
    intro y hy
    obtain ⟨nf, hnf, rfl⟩ := List.mem_map.1 hy
    exact (hU nf hnf).2
  have hlen : XG.length ≤ (U.map (nfElt n S base)).length := by
    rw [List.length_map, List.length_flatMap, ← h4]
    simp
  exact (hnodup.subperm hsub).perm_of_length_le hlen

end CFSG.Sporadic.Schreier
