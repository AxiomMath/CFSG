module

public import Certificates.Kernel.Co1Seven.Nodes
public import CFSG.LocalAnalysis.StandardType.GGSporKRestSeeds
public import CFSG.LocalAnalysis.StandardType.GGSporKRestOrderE
public import CFSG.Sporadic.Schreier.Co1AutTrivial

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1Seven

open CFSG.KC.Co1Cl CFSG.KC.Co1B CFSG.Sporadic.Co1Schreier CFSG.StandardType.SporadicShape

theorem closure_pair_eq_top {G : Type*} [Group G] (H : Subgroup G) {a b : G} (ha : a ∈ H)
    (hb : b ∈ H) (hH : H = Subgroup.closure {a, b}) :
    Subgroup.closure ({(⟨a, ha⟩ : ↥H), ⟨b, hb⟩} : Set ↥H) = ⊤ := by
  have h1 : Subgroup.map H.subtype (Subgroup.closure ({(⟨a, ha⟩ : ↥H), ⟨b, hb⟩} : Set ↥H)) = H := by
    rw [MonoidHom.map_closure, Set.image_pair]
    exact hH.symm
  have h2 : Subgroup.map H.subtype ⊤ = H := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  exact Subgroup.map_injective H.subtype_injective (h1.trans h2.symm)

theorem val_seven : (Nat.card ↥GA).factorization 7 = 2 := by
  rw [card_GA_eq]
  have e : (4157776806543360000 : ℕ) = 7 ^ 2 * 84852587888640000 := by norm_num
  rw [e, Nat.factorization_mul (by positivity) (by positivity), Finsupp.add_apply,
    Nat.Prime.factorization_pow (by norm_num), Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]

theorem SN_eq : SN = 617 := by decide +kernel


theorem s_pow : nodeG 617 ^ 7 = 1 := by
  have h := eqG (s := 49) (t := 9) (u := 4) (w := 4) (by decide +kernel) (by decide)
  norm_num [termG_eval, epM, nodeG_one] at h
  rwa [← pow_succ] at h

theorem u_pow : nodeG 1437 ^ 7 = 1 := by
  have h := eqG (s := 337) (t := 57) (u := 4) (w := 4) (by decide +kernel) (by decide)
  norm_num [termG_eval, epM, nodeG_one] at h
  rwa [← pow_succ] at h

theorem su_comm : nodeG 617 * nodeG 1437 = nodeG 1437 * nodeG 617 := by
  have h := eqG (s := 9) (t := 57) (u := 57) (w := 9) (by decide +kernel) (by decide)
  norm_num [termG_eval, epM] at h
  exact h

theorem sh_conj : nodeG 617 * nodeG 2017 = nodeG 2017 * (nodeG 617 ^ 4 * nodeG 1437) := by
  have h := eqG (s := 1234) (t := 4034) (u := 4034) (w := 89) (by decide +kernel) (by decide)
  norm_num [termG_eval, epM] at h
  exact h

theorem z₁s_comm : nodeG 592 * nodeG 617 = nodeG 617 * nodeG 592 := by
  have h := eqG (s := 1184) (t := 1234) (u := 1234) (w := 1184) (by decide +kernel) (by decide)
  norm_num [termG_eval, epM] at h
  exact h

theorem out_A₁ : nodeG 3500 = nodeG 0 := by
  have h := eqG (s := 7000) (t := 4) (u := 0) (w := 4) (by decide +kernel) (by decide)
  norm_num [termG_eval, epM, nodeG_one] at h
  exact h

theorem out_A₂ : nodeG 4188 = nodeG 1 := by
  have h := eqG (s := 8376) (t := 4) (u := 2) (w := 4) (by decide +kernel) (by decide)
  norm_num [termG_eval, epM, nodeG_one] at h
  exact h

theorem z₂_eq : nodeG 2020 = (nodeG 2017)⁻¹ * nodeG 592 * nodeG 2017 := by
  have hj : 3 < CH.length := by rw [CH_length]; norm_num
  have h0 := nodeG_inv (by norm_num) (by norm_num) (node_inv (j := 3) (i := 0) (k := 2018)
    (a := 2017) hj (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  have h1 := nodeG_mul (by norm_num) (by norm_num) (by norm_num) (node_mul (j := 3) (i := 1)
    (k := 2019) (a := 2018) (b := 592) hj (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel))
  have h2 := nodeG_mul (by norm_num) (by norm_num) (by norm_num) (node_mul (j := 3) (i := 2)
    (k := 2020) (a := 2019) (b := 2017) hj (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel))
  rw [h2, h1, h0]

theorem z₂_comm : nodeG 2020 * (nodeG 617 ^ 4 * nodeG 1437) =
    (nodeG 617 ^ 4 * nodeG 1437) * nodeG 2020 := by
  have hy : nodeG 617 ^ 4 * nodeG 1437 = (nodeG 2017)⁻¹ * nodeG 617 * nodeG 2017 := by
    rw [mul_assoc, sh_conj, inv_mul_cancel_left]
  rw [hy, z₂_eq]
  simp only [mul_assoc, mul_inv_cancel_left]
  rw [← mul_assoc (nodeG 592), z₁s_comm, mul_assoc]

@[expose] noncomputable def S0 : Subgroup ↥GA := Subgroup.closure {nodeG 617, nodeG 1437}

theorem S0_pgroup : IsPGroup 7 S0 := by
  refine @isPGroup_closure_of_commute ↥GA (Subgroup.toGroup GA) 7 _ ?_ ?_
  · intro x hx y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    exacts [Commute.refl _, su_comm, su_comm.symm, Commute.refl _]
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    exacts [s_pow, u_pow]

theorem s_mem : nodeG 617 ∈ S0 := Subgroup.subset_closure (Set.mem_insert _ _)

theorem u_mem : nodeG 1437 ∈ S0 := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem s_ne_one : nodeG 617 ≠ 1 := by
  have hs := ch1023013sne
  rw [SN_eq] at hs
  refine nodeG_ne_one (by norm_num) ?_ hs
  exact node_lt (j := 0) (i := 614) (by rw [CH_length]; norm_num) (by decide +kernel)
    (by decide +kernel)

theorem mem_closure_of_chunk {j n : Nat} (hj : j < CH.length) (hn : InChunk CH WL j n)
    (hnN : n < 4189) (hS : ∀ s ∈ (CH.getD j (0, 0, [])).2.2, s < 4189) :
    nodeG n ∈ Subgroup.closure {z | ∃ s ∈ (CH.getD j (0, 0, [])).2.2, nodeG s = z} := by
  obtain ⟨g, hg, hgr⟩ := nodeIn_chunk
    ((Subgroup.closure {z | ∃ s ∈ (CH.getD j (0, 0, [])).2.2, nodeG s = z}).map GA.subtype)
    ch1023013layout chunks n j hj hn fun s hs =>
      ⟨((nodeG s : ↥GA) : GL24), Subgroup.mem_map_of_mem _ (Subgroup.subset_closure ⟨s, hs, rfl⟩),
        matK_nodeG (hS s hs)⟩
  obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.1 hg
  rw [nodeG_eq hnN h hgr]
  exact hh

theorem closure_A : Subgroup.closure ({nodeG 0, nodeG 1} : Set ↥GA) = ⊤ := by
  rw [nodeG_A₁, nodeG_A₂]
  exact closure_pair_eq_top GA A₁_mem A₂_mem GA_eq

theorem out_mem {j n : Nat} (hj : j < CH.length) (hS : (CH.getD j (0, 0, [])).2.2 = [617, 1437, 592, 2020])
    (h1 : (CH.getD j (0, 0, [])).1 ≤ n) (h2 : n < (CH.getD j (0, 0, [])).1 + (WL j).length)
    (hnN : n < 4189) :
    nodeG n ∈ Subgroup.closure {z | ∃ s ∈ [617, 1437, 592, 2020], nodeG s = z} := by
  have h := mem_closure_of_chunk hj ⟨h1, h2⟩ hnN (by rw [hS]; decide)
  rwa [hS] at h

theorem gen {x : ↥GA} (hx : IsConj (nodeG 617) x) : SporKRestGenerating 7 x := by
  have : Finite ↥GA := Nat.finite_of_card_ne_zero (by rw [card_GA_eq]; norm_num)
  have ha := out_mem (j := 5) (n := 3500) (by rw [CH_length]; norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by norm_num)
  have hb := out_mem (j := 6) (n := 4188) (by rw [CH_length]; norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by norm_num)
  rw [out_A₁] at ha
  rw [out_A₂] at hb
  refine @sporKRest_generating_of_seeds ↥GA (Subgroup.toGroup GA) this 7 (by norm_num)
    (nodeG 0) (nodeG 1) closure_A S0 S0_pgroup (nodeG 617) _ ?_ ha hb x hx
  rintro z ⟨s, hs, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · exact Or.inl s_mem
  · exact Or.inl u_mem
  · exact Or.inr ⟨1, nodeG 617, s_mem, by rw [mul_one, one_mul], z₁s_comm⟩
  · exact Or.inr ⟨nodeG 2017, nodeG 617 ^ 4 * nodeG 1437,
      S0.mul_mem (S0.pow_mem s_mem 4) u_mem, sh_conj, z₂_comm⟩

theorem cover : SporKRestCover 7 ↥GA := by
  have : Finite ↥GA := Nat.finite_of_card_ne_zero (by rw [card_GA_eq]; norm_num)
  refine @sporKRest_cover_of_orderE ↥GA (Subgroup.toGroup GA) this 7 (by norm_num) val_seven
    (nodeG 617) s_ne_one ?_ (fun x hx => gen hx)
  exact S0_pgroup.to_le (Subgroup.zpowers_le.2 s_mem)

end CertificateChecks.KernelCo1Seven

end
