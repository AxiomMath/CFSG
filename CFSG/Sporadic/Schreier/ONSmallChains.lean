module

public import CFSG.Sporadic.Schreier.ONOuterDefs
public import CFSG.Sporadic.Schreier.ONCheckSmall

public noncomputable section

namespace CFSG.ONSchreier

open CFSG.ONSchreier.Native CFSG.Certificates

theorem smallBase_map_val {n : ℕ} {hn : 0 < n} {ch : Data.SmallChain}
    (h : ∀ i < ch.base.size, ch.base[i]! < n) :
    (smallBase n hn ch).map Fin.val = ch.base.toList := by
  apply List.ext_getElem (by simp [smallBase])
  intro k h1 h2
  simp only [smallBase, List.map_map, List.getElem_map, Function.comp_apply, Array.getElem_toList]
  have hk : k < ch.base.size := by simpa using h2
  have := h k hk
  rw [getElem!_pos _ k hk] at this
  exact Nat.mod_eq_of_lt this

theorem smallChain_facts {n : ℕ} (hn : 0 < n) (ch : Data.SmallChain)
    (hk : ch.generators.size ≤ ch.strongGenerators.size) (hb : (smallBase n hn ch).Nodup)
    (h : smallChainOK n ch = true) :
    ch.degree = n ∧ ValidSchreier (smallChain n hn ch hk hb) ∧
      Nat.card (smallChain n hn ch hk hb).originalSubgroup =
        (cOrbitSizes n ch.strongGenerators ch.base).prod := by
  simp only [smallChainOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hdeg, -⟩, hgens⟩, hfull⟩ := h
  have hF := chainFacts hfull
  have hA : CArrays (smallChain n hn ch hk hb) ch.generators.size ch.strongGenerators ch.base
      (Array.replicate ch.generators.size [] ++ ch.derivations) :=
    ofArrays_arrays (smallBase_map_val hF.base_lt)
      (fun j hj => by simpa [Bool.and_eq_true] using allBelowN_spec hgens hj) hfull
  obtain ⟨hV, horb⟩ := validSchreier_of_fullChainOK hA (by norm_num) hfull
  exact ⟨hdeg, hV, card_eq_prod_cOrbitSizes hV hA.base_size horb⟩

theorem t32_facts :
    Data.T32Chain.degree = 32 ∧ ValidSchreier onT32Chain ∧
    Nat.card onT32Chain.originalSubgroup =
      (cOrbitSizes 32 Data.T32Chain.strongGenerators Data.T32Chain.base).prod :=
  smallChain_facts (by norm_num) Data.T32Chain _ _ small_chain_certs.1

theorem m120_facts :
    Data.M120Chain.degree = 120 ∧ ValidSchreier onM120Chain ∧
    Nat.card onM120Chain.originalSubgroup =
      (cOrbitSizes 120 Data.M120Chain.strongGenerators Data.M120Chain.base).prod :=
  smallChain_facts (by norm_num) Data.M120Chain _ _ small_chain_certs.2.1

theorem l120_facts :
    Data.L120Chain.degree = 120 ∧ ValidSchreier onL120Chain ∧
    Nat.card onL120Chain.originalSubgroup =
      (cOrbitSizes 120 Data.L120Chain.strongGenerators Data.L120Chain.base).prod :=
  smallChain_facts (by norm_num) Data.L120Chain _ _ small_chain_certs.2.2.1

theorem psl21_facts :
    Data.PSL21Chain.degree = 21 ∧ ValidSchreier onPSL21Chain ∧
    Nat.card onPSL21Chain.originalSubgroup =
      (cOrbitSizes 21 Data.PSL21Chain.strongGenerators Data.PSL21Chain.base).prod :=
  smallChain_facts (by norm_num) Data.PSL21Chain _ _ small_chain_certs.2.2.2.1

theorem psl120_facts :
    Data.PSL120Chain.degree = 120 ∧ ValidSchreier onPSL120Chain ∧
    Nat.card onPSL120Chain.originalSubgroup =
      (cOrbitSizes 120 Data.PSL120Chain.strongGenerators Data.PSL120Chain.base).prod :=
  smallChain_facts (by norm_num) Data.PSL120Chain _ _ small_chain_certs.2.2.2.2.1

theorem card_onT32 : Nat.card onT32Chain.originalSubgroup = 512 := by
  rw [t32_facts.2.2, small_chain_certs.2.2.2.2.2.1]
  rfl

theorem card_onM120 :
    Nat.card onM120Chain.originalSubgroup = 40320 := by
  rw [m120_facts.2.2, small_chain_certs.2.2.2.2.2.2.1]
  rfl

theorem card_onL120 :
    Nat.card onL120Chain.originalSubgroup = 20160 := by
  rw [l120_facts.2.2, small_chain_certs.2.2.2.2.2.2.2.1]
  rfl

theorem card_onPSL21 :
    Nat.card onPSL21Chain.originalSubgroup = 20160 := by
  rw [psl21_facts.2.2, small_chain_certs.2.2.2.2.2.2.2.2.1]
  rfl

theorem card_onPSL120 :
    Nat.card onPSL120Chain.originalSubgroup = 20160 := by
  rw [psl120_facts.2.2, small_chain_certs.2.2.2.2.2.2.2.2.2]
  rfl

theorem card_onX : Nat.card onX = 20160 := card_onPSL120

theorem at_on_small_chain_orders :
    ValidSchreier onT32Chain ∧ ValidSchreier onM120Chain ∧ ValidSchreier onL120Chain ∧
      ValidSchreier onPSL21Chain ∧ ValidSchreier onPSL120Chain ∧
      Data.T32Chain.degree = 32 ∧ Data.M120Chain.degree = 120 ∧ Data.L120Chain.degree = 120 ∧
      Data.PSL21Chain.degree = 21 ∧ Data.PSL120Chain.degree = 120 ∧
      Nat.card onT32Chain.originalSubgroup = 512 ∧
      Nat.card onM120Chain.originalSubgroup = 40320 ∧
      Nat.card onL120Chain.originalSubgroup = 20160 ∧
      Nat.card onPSL21Chain.originalSubgroup = 20160 ∧
      Nat.card onPSL120Chain.originalSubgroup = 20160 :=
  ⟨t32_facts.2.1, m120_facts.2.1, l120_facts.2.1, psl21_facts.2.1, psl120_facts.2.1,
    t32_facts.1, m120_facts.1, l120_facts.1, psl21_facts.1, psl120_facts.1, card_onT32,
    card_onM120, card_onL120, card_onPSL21, card_onPSL120⟩

end CFSG.ONSchreier
