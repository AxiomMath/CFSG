module

public import CFSG.Sporadic.Schreier.ONSmallChains

public noncomputable section

namespace CFSG.ONSchreier

open CFSG.ONSchreier.Native CFSG.Certificates

variable {n : ℕ}

theorem smallGen_inv {ch : Data.SmallChain} (h : smallChainOK n ch = true) :
    ∀ j < ch.generators.size,
      pisInv n ch.generators[j]! (pinvCand n ch.generators[j]!) = true := by
  intro j hj
  simp only [smallChainOK, Bool.and_eq_true] at h
  have := allBelowN_spec h.1.2 hj
  simp only [Bool.and_eq_true] at this
  exact this.2

theorem prep_smallGen {ch : Data.SmallChain} (h : smallChainOK n ch = true) :
    ∀ j < ch.generators.size, PRep n ch.generators[j]! (permOfArr n ch.generators[j]!) :=
  fun j hj => (prep_permOfArr (smallGen_inv h j hj)).1

theorem smallChain_sub (hn : 0 < n) (ch : Data.SmallChain)
    (hk : ch.generators.size ≤ ch.strongGenerators.size) (hb : (smallBase n hn ch).Nodup) :
    (smallChain n hn ch hk hb).originalSubgroup = Subgroup.closure
      ((fun j => permOfArr n ch.generators[j]!) '' {j | j < ch.generators.size}) := by
  rw [smallChain, ofArrays_originalSubgroup]
  congr 1
  ext g
  simp only [Set.mem_range, Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨j, j.isLt, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨⟨j, hj⟩, rfl⟩

theorem smallChain_arrays (hn : 0 < n) (ch : Data.SmallChain)
    (hk : ch.generators.size ≤ ch.strongGenerators.size) (hb : (smallBase n hn ch).Nodup)
    (h : smallChainOK n ch = true) :
    CArrays (smallChain n hn ch hk hb) ch.generators.size ch.strongGenerators ch.base
        (Array.replicate ch.generators.size [] ++ ch.derivations) ∧
      fullChainOK n ch.generators.size ch.strongGenerators ch.base
        (Array.replicate ch.generators.size [] ++ ch.derivations) 2 = true := by
  simp only [smallChainOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨-, -⟩, hgens⟩, hfull⟩ := h
  have hF := chainFacts hfull
  exact ⟨ofArrays_arrays (smallBase_map_val hF.base_lt)
    (fun j hj => by simpa [Bool.and_eq_true] using allBelowN_spec hgens hj) hfull, hfull⟩

end CFSG.ONSchreier
