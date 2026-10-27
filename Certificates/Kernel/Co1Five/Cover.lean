module

public import Certificates.Kernel.Co1Five.Nodes
public import Certificates.Kernel.Co1Seven.Cover
public import CFSG.Certificates.Kernel.Co1Seven.ForestSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1Five

open CFSG.KC.Co1Cl CFSG.KC.Co1B CFSG.Sporadic.Co1Schreier CFSG.StandardType.SporadicShape

theorem val_five : (Nat.card ↥GA).factorization 5 = 4 := by
  rw [card_GA_eq]
  have e : (4157776806543360000 : ℕ) = 5 ^ 4 * 6652442890469376 := by norm_num
  rw [e, Nat.factorization_mul (by positivity) (by positivity), Finsupp.add_apply,
    Nat.Prime.factorization_pow (by norm_num), Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]


theorem zA_comm : nodeG 10139 * nodeG 21050 = nodeG 21050 * nodeG 10139 := by
  have h := eqG (s := 20278) (t := 42100) (u := 42100) (w := 20278) (by decide +kernel) (by decide)
  norm_num [termG_eval] at h
  exact h

theorem zB_comm : nodeG 10446 * nodeG 21088 = nodeG 21088 * nodeG 10446 := by
  have h := eqG (s := 20892) (t := 42176) (u := 42176) (w := 20892) (by decide +kernel) (by decide)
  norm_num [termG_eval] at h
  exact h

theorem zC_comm : nodeG 11500 * nodeG 21119 = nodeG 21119 * nodeG 11500 := by
  have h := eqG (s := 23000) (t := 42238) (u := 42238) (w := 23000) (by decide +kernel) (by decide)
  norm_num [termG_eval] at h
  exact h

theorem xC_conj : nodeG 21119 * nodeG 12017 = nodeG 12017 * nodeG 20747 := by
  have h := eqG (s := 42238) (t := 24034) (u := 24034) (w := 41494) (by decide +kernel) (by decide)
  norm_num [termG_eval] at h
  exact h

theorem zC₂_comm : nodeG 12413 * nodeG 20747 = nodeG 20747 * nodeG 12413 := by
  have h := eqG (s := 24826) (t := 41494) (u := 41494) (w := 24826) (by decide +kernel) (by decide)
  norm_num [termG_eval] at h
  exact h

theorem out_eq {s u : Nat} (hq : [s, 4, u, 4] ∈ getLLL Q 0) (hs : s % 2 = 0) (hs' : s / 2 < 21365)
    (hu : u % 2 = 0) (hu' : u / 2 < 21365) : nodeG (s / 2) = nodeG (u / 2) := by
  have h := eqG hq (by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> omega)
  rw [termG_eval, termG_eval, termG_eval, if_pos hs, if_pos hu, if_pos (by norm_num),
    nodeG_one, mul_one, mul_one] at h
  exact h

theorem QS_pgroup : IsPGroup 5 QS := IsPGroup.of_card (n := 4) (by rw [card_QS]; norm_num)

theorem q₁_mem : nodeG 7000 ∈ QS := by
  rw [QS_eq]
  exact Subgroup.subset_closure (by simp)

theorem q₂_mem : nodeG 7474 ∈ QS := by
  rw [QS_eq]
  exact Subgroup.subset_closure (by simp)

theorem mem_closure_of_chunk {j n : Nat} (hj : j < CH.length) (hn : InChunk CH WL j n)
    (hnN : n < 21365) (hS : ∀ s ∈ (CH.getD j (0, 0, [])).2.2, s < 21365) :
    nodeG n ∈ Subgroup.closure {z | ∃ s ∈ (CH.getD j (0, 0, [])).2.2, nodeG s = z} := by
  obtain ⟨g, hg, hgr⟩ := nodeIn_chunk
    ((Subgroup.closure {z | ∃ s ∈ (CH.getD j (0, 0, [])).2.2, nodeG s = z}).map GA.subtype)
    ch1023014layout chunks n j hj hn fun s hs =>
      ⟨((nodeG s : ↥GA) : GL24), Subgroup.mem_map_of_mem _ (Subgroup.subset_closure ⟨s, hs, rfl⟩),
        matK_nodeG (hS s hs)⟩
  obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.1 hg
  rw [nodeG_eq hnN h hgr]
  exact hh

theorem out_mem {j n : Nat} {L : List Nat} (hj : j < CH.length) (hS : (CH.getD j (0, 0, [])).2.2 = L)
    (h1 : (CH.getD j (0, 0, [])).1 ≤ n) (h2 : n < (CH.getD j (0, 0, [])).1 + (WL j).length)
    (hnN : n < 21365) (hL : ∀ s ∈ L, s < 21365) :
    nodeG n ∈ Subgroup.closure {z | ∃ s ∈ L, nodeG s = z} := by
  have h := mem_closure_of_chunk hj ⟨h1, h2⟩ hnN (by rw [hS]; exact hL)
  rwa [hS] at h

theorem closure_A : Subgroup.closure ({nodeG 0, nodeG 1} : Set ↥GA) = ⊤ := by
  rw [nodeG_A₁, nodeG_A₂]
  exact KernelCo1Seven.closure_pair_eq_top GA A₁_mem A₂_mem GA_eq

theorem gen_of {x₀ : ↥GA} {L : List Nat} {na nb : Nat}
    (ha : nodeG na ∈ Subgroup.closure {z | ∃ s ∈ L, nodeG s = z}) (hna : nodeG na = nodeG 0)
    (hb : nodeG nb ∈ Subgroup.closure {z | ∃ s ∈ L, nodeG s = z}) (hnb : nodeG nb = nodeG 1)
    (hU : ∀ s ∈ L, nodeG s ∈ QS ∨ ∃ g y, y ∈ QS ∧ x₀ * g = g * y ∧ nodeG s * y = y * nodeG s)
    {x : ↥GA} (hx : IsConj x₀ x) : SporKRestGenerating 5 x := by
  have := finite_GA
  rw [hna] at ha
  rw [hnb] at hb
  refine @sporKRest_generating_of_seeds ↥GA (Subgroup.toGroup GA) this 5 (by norm_num)
    (nodeG 0) (nodeG 1) closure_A QS QS_pgroup x₀ _ ?_ ha hb x hx
  rintro z ⟨s, hs, rfl⟩
  exact hU s hs

theorem centr {x₀ z : ↥GA} (hx : x₀ ∈ QS) (h : z * x₀ = x₀ * z) :
    z ∈ QS ∨ ∃ g y, y ∈ QS ∧ x₀ * g = g * y ∧ z * y = y * z :=
  Or.inr ⟨1, x₀, hx, by rw [mul_one, one_mul], h⟩

theorem genA {x : ↥GA} (hx : IsConj (nodeG 21050) x) : SporKRestGenerating 5 x := by
  refine gen_of (L := [7000, 7474, 10139]) (na := 14781) (nb := 15427)
    (out_mem (j := 15) (by rw [CH_length]; norm_num) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) (by decide))
    (out_eq (s := 29562) (u := 0) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num))
    (out_mem (j := 16) (by rw [CH_length]; norm_num) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) (by decide))
    (out_eq (s := 30854) (u := 2) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)) ?_ hx
  intro s hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl
  · exact Or.inl q₁_mem
  · exact Or.inl q₂_mem
  · exact centr (eQ_mem (k := 310) (by norm_num)) zA_comm

theorem genB {x : ↥GA} (hx : IsConj (nodeG 21088) x) : SporKRestGenerating 5 x := by
  refine gen_of (L := [7000, 7474, 10446]) (na := 17245) (nb := 17754)
    (out_mem (j := 18) (by rw [CH_length]; norm_num) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) (by decide))
    (out_eq (s := 34490) (u := 0) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num))
    (out_mem (j := 19) (by rw [CH_length]; norm_num) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) (by decide))
    (out_eq (s := 35508) (u := 2) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)) ?_ hx
  intro s hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl
  · exact Or.inl q₁_mem
  · exact Or.inl q₂_mem
  · exact centr (eQ_mem (k := 348) (by norm_num)) zB_comm

theorem genC {x : ↥GA} (hx : IsConj (nodeG 21119) x) : SporKRestGenerating 5 x := by
  refine gen_of (L := [7000, 7474, 11500, 12413]) (na := 20222) (nb := 20739)
    (out_mem (j := 22) (by rw [CH_length]; norm_num) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) (by decide))
    (out_eq (s := 40444) (u := 0) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num))
    (out_mem (j := 22) (by rw [CH_length]; norm_num) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) (by decide))
    (out_eq (s := 41478) (u := 2) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)) ?_ hx
  intro s hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · exact Or.inl q₁_mem
  · exact Or.inl q₂_mem
  · exact centr (eQ_mem (k := 379) (by norm_num)) zC_comm
  · exact Or.inr ⟨nodeG 12017, nodeG 20747, eQ_mem (k := 7) (by norm_num), xC_conj, zC₂_comm⟩

theorem GN_lt : ∀ g < GN.length, GN.getD g 0 < 21365 := by
  rw [GN_eq]
  intro g hg
  simp only [List.length_cons, List.length_nil] at hg
  interval_cases g <;> simp

theorem complete (s : ↥GA) (hs : orderOf s = 5) :
    ∃ r ∈ [nodeG 21050, nodeG 21088, nodeG 21119], IsConj r s := by
  have := finite_GA
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hsne : s ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hs
    exact absurd hs (by norm_num)
  have hsyl : IsPGroup 5 ↥(Subgroup.zpowers s) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hs, pow_one]
  obtain ⟨P, hP⟩ := IsPGroup.exists_le_sylow hsyl
  let S₀ : Sylow 5 ↥GA := Sylow.ofCard QS (by rw [card_QS, val_five]; norm_num)
  have : MulAction.IsPretransitive ↥GA (Sylow 5 ↥GA) := Sylow.isPretransitive_of_finite
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥GA P S₀
  have hsP : s ∈ (P : Subgroup ↥GA) := hP (Subgroup.mem_zpowers s)
  have htS : g * s * g⁻¹ ∈ QS := by
    change g * s * g⁻¹ ∈ (S₀ : Subgroup ↥GA)
    rw [← hg]
    change g * s * g⁻¹ ∈ (((g • P : Sylow 5 ↥GA) : Set ↥GA))
    rw [Sylow.coe_smul, Set.mem_smul_set]
    exact ⟨s, hsP, by rw [MulAut.smul_def, MulAut.conj_apply]⟩
  obtain ⟨k, hk, hke⟩ := eQ_all htS
  have hk0 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · rw [Nat.add_zero, eQ_zero] at hke
      have h1 : g * s * g⁻¹ = 1 := hke.symm
      exact absurd (by simpa using h1) hsne
    · exact h
  obtain ⟨r, hr, -, hrc⟩ := cforK_sound (matHom GA) (matHom_injective GA) ch1023014forest0
    (fun c => nodeG (20740 + c)) (fun c hc => matK_EQ hc) (fun g => nodeG (GN.getD g 0))
    (fun g hg => matK_nodeG (GN_lt g hg)) k hk0 hk
  have hcs : IsConj (nodeG (20740 + k)) s := by
    rw [hke]
    exact (isConj_iff.2 ⟨g, rfl⟩).symm
  rw [RT_eq] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> simp only [Nat.reduceAdd] at hrc
  · exact ⟨_, List.mem_cons_self .., hrc.trans hcs⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), hrc.trans hcs⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)),
      hrc.trans hcs⟩

theorem cover : SporKRestCover 5 ↥GA := by
  refine @sporKRest_cover_of_classes ↥GA (Subgroup.toGroup GA) 5 (by norm_num)
    [nodeG 21050, nodeG 21088, nodeG 21119] complete ?_
  intro r hr x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  exacts [genA hx, genB hx, genC hx]

end CertificateChecks.KernelCo1Five

end
