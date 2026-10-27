module

public import CFSG.Sporadic.Schreier.RuLocalFacts
public import Mathlib.Data.List.GetD
public import CFSG.Sporadic.Schreier.RuRestrict

public noncomputable section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native

theorem ruC0_memC : ruC0 ∈ ruC := Subgroup.subset_closure (Set.mem_insert _ _)

theorem ruC1_memC : ruC1 ∈ ruC := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem ruZ_memC : ruZ ∈ ruC := ruC.pow_mem ruC0_memC 10

theorem ruSGens_memC :
    ∀ g ∈ ruSGens, g ∈ ruC := by
  intro g hg
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hg
  have hi4 : i < 4 := by simpa [ruSGens, ruSWords] using hi
  rw [← List.getD_eq_getElem ruSGens 1 hi]
  exact mem_ruC_of_sift (rep_ruSGens i hi4) (ruChainC_check.2.2.1 i hi4)

theorem ruKGens_memC :
    ∀ g ∈ ruKGens, g ∈ ruC := by
  intro g hg
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hg
  have hi8 : i < 8 := by simpa [ruKGens, ruKWords] using hi
  rw [← List.getD_eq_getElem ruKGens 1 hi]
  exact mem_ruC_of_sift (rep_ruKGens i hi8) (ruChainC_check.2.2.2 i hi8)

theorem ruJGens_memC : ∀ g ∈ ruJGens, g ∈ ruC := by
  intro g hg
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
  exact evalSigned_mem (pair_mem ruC0_memC ruC1_memC) w

theorem ruRGens_memC :
    ∀ g ∈ ruRGens, g ∈ ruC := by
  intro g hg
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
  exact evalSigned_mem ruSGens_memC w

theorem ruS_leC :
    ruS ≤ ruC := closure_list_le ruSGens_memC

theorem ruK_leC :
    ruK ≤ ruC := closure_list_le ruKGens_memC

theorem ruJ_leC : ruJ ≤ ruC := closure_list_le ruJGens_memC

theorem ruR_leC :
    ruR ≤ ruC := closure_list_le ruRGens_memC

theorem ruR_leS : ruR ≤ ruS := closure_list_le fun g hg => by
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
  exact evalSigned_mem (fun g hg => Subgroup.subset_closure hg) w

theorem ruNs0_memN : ruNs0 ∈ ruN := Subgroup.subset_closure (Set.mem_insert _ _)

theorem ruNs1_memN : ruNs1 ∈ ruN := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem ruS_leN : ruS ≤ ruN := closure_list_le fun g hg => by
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
  exact evalSigned_mem (pair_mem ruNs0_memN ruNs1_memN) w

theorem ruK_leN : ruK ≤ ruN := closure_list_le fun g hg => by
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
  exact evalSigned_mem (pair_mem ruNs0_memN ruNs1_memN) w

theorem closure_res_list {m : ℕ} {M : Type*} [Group M] (f : ruC →* M)
    (f' : Equiv.Perm (Fin 4060) → M) (hf' : ∀ g (hg : g ∈ ruC), f' g = f ⟨g, hg⟩)
    {l : List (Equiv.Perm (Fin 4060))} (hl : ∀ g ∈ l, g ∈ ruC) (hm : l.length = m) :
    ((Subgroup.closure {g | g ∈ l}).subgroupOf ruC).map f =
      Subgroup.closure {h | h ∈ (List.range m).map fun i => f' (l.getD i 1)} := by
  rw [map_subgroupOf_closure f (X := {g | g ∈ l}) hl]
  congr 1
  ext h
  simp only [Set.mem_range, Set.mem_ofPred_eq, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨⟨g, hg⟩, rfl⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hg
    refine ⟨i, hm ▸ hi, ?_⟩
    rw [List.getD_eq_getElem l 1 hi, hf' _ (hl _ hg)]
  · rintro ⟨i, hi, rfl⟩
    have hi' : i < l.length := hm ▸ hi
    refine ⟨⟨l[i], List.getElem_mem hi'⟩, ?_⟩
    rw [List.getD_eq_getElem l 1 hi', hf' _ (hl _ (List.getElem_mem hi'))]

theorem rep_ruResF'
    {t : Array ℕ} {g : Equiv.Perm (Fin 4060)} (ht : Rep 4060 t g)
    (hg : g ∈ ruC) : Rep 1920 (resA ruF ruFPos t) (ruResF ⟨g, hg⟩) := by
  rw [← ruResFPerm_of_mem hg]
  exact rep_ruResF ht hg

theorem chain1920_original
    {f k : ℕ} {l : List (Equiv.Perm (Fin 4060))}
    {ts : Array (Array ℕ)} (hl : ∀ g ∈ l, g ∈ ruC) (hlen : l.length = k)
    (hrep : ∀ i < k, Rep 4060 ts[i]! (l.getD i 1))
    (hinv : ∀ i < k, isInvA 1920 (ruField1920 f)[i]! (invCand 1920 (ruField1920 f)[i]!) = true)
    (heq : ∀ i < k, eqA 1920 (ruField1920 f)[i]! (resA ruF ruFPos ts[i]!) = true) :
    ((List.range k).map fun i => permOfArr 1920 (ruField1920 f)[i]!) =
      (List.range k).map fun i => ruResFPerm (l.getD i 1) := by
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  have hmem : l.getD i 1 ∈ ruC := by
    rw [List.getD_eq_getElem l 1 (hlen ▸ hi)]
    exact hl _ (List.getElem_mem _)
  exact permOfArr_eq_of_eqA (hinv i hi) (rep_ruResF (hrep i hi) hmem) (heq i hi)

theorem ruChainCFaithful_original :
    ruChainCFaithful.original.toList = [ruResFPerm ruC0, ruResFPerm ruC1] := by
  have h := ruChainCFaithful_check.1
  rw [show ruChainCFaithful.original.toList = (List.range 2).map fun i => permOfArr 1920
    (ruField1920 0)[i]! from ofArrays_original_toList, show List.range 2 = [0, 1] from rfl,
    List.map_cons, List.map_cons, List.map_nil,
    permOfArr_eq_of_eqA (ruChain_strong_inv h (by decide)) (rep_ruResF rep_ruC0 ruC0_memC)
      ruGens_check.2.2.2.2.2.2.2.2.1,
    permOfArr_eq_of_eqA (ruChain_strong_inv h (by decide)) (rep_ruResF rep_ruC1 ruC1_memC)
      ruGens_check.2.2.2.2.2.2.2.2.2.1]

theorem ruChainCQuotient80_original :
    ruChainCQuotient80.original.toList = [ruResYPerm ruC0, ruResYPerm ruC1] := by
  have h := ruChainCQuotient80_check.1
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, y0, y1⟩ := ruGens_check
  rw [show ruChainCQuotient80.original.toList = (List.range 2).map fun i => permOfArr 80
    ruField80[i]! from ofArrays_original_toList, show List.range 2 = [0, 1] from rfl,
    List.map_cons, List.map_cons, List.map_nil,
    permOfArr_eq_of_eqA (ruChain_strong_inv h (by decide)) (rep_ruResY rep_ruC0 ruC0_memC) y0,
    permOfArr_eq_of_eqA (ruChain_strong_inv h (by decide)) (rep_ruResY rep_ruC1 ruC1_memC) y1]

theorem ruC_eq_closure_list : ruC = Subgroup.closure {g | g ∈ [ruC0, ruC1]} := by
  rw [setOf_mem_pair]
  rfl

theorem ruResF_range :
    ruResF.range = ruChainCFaithful.originalSubgroup := by
  rw [MonoidHom.range_eq_map, ← Subgroup.subgroupOf_self ruC]
  conv_lhs => rw [show ((ruC.subgroupOf ruC).map ruResF) =
    (((Subgroup.closure {g | g ∈ [ruC0, ruC1]}).subgroupOf ruC).map ruResF) by
      rw [← ruC_eq_closure_list]]
  rw [closure_res_list ruResF ruResFPerm (fun g hg => ruResFPerm_of_mem hg)
    (pair_mem ruC0_memC ruC1_memC) rfl, RawSchreierDatum.originalSubgroup,
    ruChainCFaithful_original]
  rfl

theorem ruResY_range :
    ruResY.range = ruChainCQuotient80.originalSubgroup := by
  rw [MonoidHom.range_eq_map, ← Subgroup.subgroupOf_self ruC]
  conv_lhs => rw [show ((ruC.subgroupOf ruC).map ruResY) =
    (((Subgroup.closure {g | g ∈ [ruC0, ruC1]}).subgroupOf ruC).map ruResY) by
      rw [← ruC_eq_closure_list]]
  rw [closure_res_list ruResY ruResYPerm (fun g hg => ruResYPerm_of_mem hg)
    (pair_mem ruC0_memC ruC1_memC) rfl, RawSchreierDatum.originalSubgroup,
    ruChainCQuotient80_original]
  rfl

theorem card_ruResF_range :
    Nat.card ruResF.range = 245760 := by
  have h : Nat.card ruChainCFaithful.originalSubgroup = _ := ruChain_card ruChainCFaithful_check.1
  rw [ruChainCFaithful_check.2] at h
  rw [ruResF_range]
  exact h

theorem card_ruResY_range :
    Nat.card ruResY.range = 122880 := by
  have h : Nat.card ruChainCQuotient80.originalSubgroup = _ :=
    ruChain_card ruChainCQuotient80_check.1
  rw [ruChainCQuotient80_check.2] at h
  rw [ruResY_range]
  exact h

instance :

    Finite ruC := Nat.finite_of_card_ne_zero (by rw [card_ruC]; norm_num)

theorem ruResF_injective :
    Function.Injective ruResF :=
  injective_of_card_range _ (by rw [card_ruResF_range, card_ruC])

end CFSG.Sporadic.RuSchreier
