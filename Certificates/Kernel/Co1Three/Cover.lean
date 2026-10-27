module

public import Certificates.Kernel.Co1Three.Nodes
public import CFSG.LocalAnalysis.StandardType.GGSporKRestSeeds
public import CFSG.LocalAnalysis.StandardType.GGSporKRestClasses

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1Three

open CFSG.KC.Co1Cl CFSG.KC.Co1B CFSG.Sporadic.Co1Schreier
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.StandardType.SporadicShape

theorem isConj_of_mul {G : Type*} [Group G] {x y g : G} (h : x * g = g * y) : IsConj x y :=
  isConj_iff.2 ⟨g⁻¹, by rw [inv_inv, mul_assoc, h, inv_mul_cancel_left]⟩

theorem epM_mem {G : Type*} [Group G] (f : Nat → G) (H : Subgroup G) :
    ∀ (L : List Nat), (∀ x ∈ L, f x ∈ H) → ∀ (v : Nat) (acc : G), acc ∈ H → epM f 3 L v acc ∈ H
  | [], _, _, _, h => h
  | g :: L, hL, v, acc, h =>
    epM_mem f H L (fun x hx => hL x (List.mem_cons_of_mem g hx)) _ _
      (H.mul_mem h (H.pow_mem (hL g List.mem_cons_self) _))


@[expose] noncomputable def dG (v : Nat) : ↥GA := epM nodeG 3 [10, 13096] v 1

theorem termG_D (v : Nat) : termG (2 * (1 + 4 * v) + 1) = dG v := by
  rw [termG_pt (by norm_num), GL1, dG]

theorem eq_out {k n m : Nat} (hk : k < 4) (hq : [2 * n, 2 * 11, 2 * m, 2 * 11] ∈ Q.getD k []) :
    nodeG n = nodeG m := by
  have := eqG hk hq
  rw [termG_nd, termG_nd, termG_nd, nodeG_one] at this
  exact mul_right_cancel this

theorem eq_zE {k z v : Nat} (hk : k < 4)
    (hq : [2 * z, 2 * (0 + 4 * v) + 1, 2 * (0 + 4 * v) + 1, 2 * z] ∈ Q.getD k []) :
    nodeG z * eG v = eG v * nodeG z := by
  have := eqG hk hq
  rwa [termG_nd, termG_E] at this

theorem eq_zD {k z v : Nat} (hk : k < 4)
    (hq : [2 * z, 2 * (1 + 4 * v) + 1, 2 * (1 + 4 * v) + 1, 2 * z] ∈ Q.getD k []) :
    nodeG z * dG v = dG v * nodeG z := by
  have := eqG hk hq
  rwa [termG_nd, termG_D] at this

theorem eq_xE {k x h v : Nat} (hk : k < 4)
    (hq : [2 * x, 2 * h, 2 * h, 2 * (0 + 4 * v) + 1] ∈ Q.getD k []) :
    nodeG x * nodeG h = nodeG h * eG v := by
  have := eqG hk hq
  rwa [termG_nd, termG_nd, termG_E] at this

theorem eq_EE {k u h v : Nat} (hk : k < 4)
    (hq : [2 * (0 + 4 * u) + 1, 2 * h, 2 * h, 2 * (0 + 4 * v) + 1] ∈ Q.getD k []) :
    eG u * nodeG h = nodeG h * eG v := by
  have := eqG hk hq
  rwa [termG_nd, termG_E, termG_E] at this

theorem eq_xD {k x h v : Nat} (hk : k < 4)
    (hq : [2 * x, 2 * h, 2 * h, 2 * (1 + 4 * v) + 1] ∈ Q.getD k []) :
    nodeG x * nodeG h = nodeG h * dG v := by
  have := eqG hk hq
  rwa [termG_nd, termG_nd, termG_D] at this

theorem mem_closure_of_chunk {j n : Nat} (hj : j < CH.length) (hn : InChunk CH WL j n)
    (hnN : n < 28098) (hS : ∀ s ∈ (CH.getD j (0, 0, [])).2.2, s < 28098) :
    nodeG n ∈ Subgroup.closure {z | ∃ s ∈ (CH.getD j (0, 0, [])).2.2, nodeG s = z} := by
  obtain ⟨g, hg, hgr⟩ := nodeIn_chunk
    ((Subgroup.closure {z | ∃ s ∈ (CH.getD j (0, 0, [])).2.2, nodeG s = z}).map GA.subtype)
    layout chunks n j hj hn fun s hs =>
      ⟨((nodeG s : ↥GA) : GL24), Subgroup.mem_map_of_mem _ (Subgroup.subset_closure ⟨s, hs, rfl⟩),
        matK_nodeG (hS s hs)⟩
  obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.1 hg
  rw [nodeG_eq hnN h hgr]
  exact hh

theorem inChunk {j m : Nat} (h1 : (CH.getD j (0, 0, [])).1 ≤ m)
    (h2 : m < (CH.getD j (0, 0, [])).1 + (WL j).length) : InChunk CH WL j m := ⟨h1, h2⟩

theorem closure_pair_eq_top {G : Type*} [Group G] (H : Subgroup G) {a b : G} (ha : a ∈ H)
    (hb : b ∈ H) (hH : H = Subgroup.closure {a, b}) :
    Subgroup.closure ({(⟨a, ha⟩ : ↥H), ⟨b, hb⟩} : Set ↥H) = ⊤ := by
  have h1 : Subgroup.map H.subtype (Subgroup.closure ({(⟨a, ha⟩ : ↥H), ⟨b, hb⟩} : Set ↥H)) = H := by
    rw [MonoidHom.map_closure, Set.image_pair]
    exact hH.symm
  have h2 : Subgroup.map H.subtype ⊤ = H := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  exact Subgroup.map_injective H.subtype_injective (h1.trans h2.symm)

theorem closure_A : Subgroup.closure ({nodeG 0, nodeG 1} : Set ↥GA) = ⊤ := by
  rw [nodeG_A₁, nodeG_A₂]
  exact closure_pair_eq_top GA A₁_mem A₂_mem GA_eq

theorem class_gen (S₀ : Subgroup ↥GA) (hS₀ : IsPGroup 3 S₀) (x₀ : ↥GA) (S : List Nat)
    {j₁ j₂ n₁ n₂ : Nat} (hj₁ : j₁ < CH.length) (hj₂ : j₂ < CH.length)
    (hS₁ : (CH.getD j₁ (0, 0, [])).2.2 = S) (hS₂ : (CH.getD j₂ (0, 0, [])).2.2 = S)
    (hn₁ : InChunk CH WL j₁ n₁) (hn₂ : InChunk CH WL j₂ n₂) (hN₁ : n₁ < 28098) (hN₂ : n₂ < 28098)
    (hSlt : ∀ s ∈ S, s < 28098) (ha : nodeG n₁ = nodeG 0) (hb : nodeG n₂ = nodeG 1)
    (hU : ∀ s ∈ S, nodeG s ∈ S₀ ∨ ∃ g y, y ∈ S₀ ∧ x₀ * g = g * y ∧ nodeG s * y = y * nodeG s)
    {x : ↥GA} (hx : IsConj x₀ x) : SporKRestGenerating 3 x := by
  have h₁ := mem_closure_of_chunk hj₁ hn₁ hN₁ (by rw [hS₁]; exact hSlt)
  have h₂ := mem_closure_of_chunk hj₂ hn₂ hN₂ (by rw [hS₂]; exact hSlt)
  rw [hS₁, ha] at h₁
  rw [hS₂, hb] at h₂
  refine @sporKRest_generating_of_seeds ↥GA (Subgroup.toGroup GA) Co1T.finite_GA 3 Nat.prime_three
    (nodeG 0) (nodeG 1) closure_A S₀ hS₀ x₀ _ ?_ h₁ h₂ x hx
  rintro z ⟨s, hs, rfl⟩
  exact hU s hs

theorem E_pgroup : IsPGroup 3 KernelCo1ThreeK.eSplitK.T := fun g =>
  ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow, KernelCo1ThreeK.eSplitK.T_pow_three g g.2, Subgroup.coe_one])⟩

theorem nodeG_mem_T : ∀ x ∈ [2, 3, 4, 5, 6, 7], nodeG x ∈ KernelCo1ThreeK.eSplitK.T := fun x hx => by
  rw [Co1T.SplitData.T_eq_closure]
  exact Subgroup.subset_closure (nodeG_mem_aGA x hx)

theorem gen_A {x : ↥GA} (hx : IsConj (eG 721) x) : SporKRestGenerating 3 x := by
  refine class_gen KernelCo1ThreeK.eSplitK.T E_pgroup (eG 721) [2, 3, 4, 5, 6, 7, 13411, 13818, 14752, 15048]
    (j₁ := 20) (j₂ := 21) (n₁ := 20254) (n₂ := 20767) (by rw [CH_length]; norm_num)
    (by rw [CH_length]; norm_num) (by decide +kernel) (by decide +kernel)
    (inChunk (by decide +kernel) (by decide +kernel)) (inChunk (by decide +kernel) (by decide +kernel)) (by norm_num)
    (by norm_num) (by decide) (eq_out (k := 1) (by norm_num) (by decide +kernel))
    (eq_out (k := 1) (by norm_num) (by decide +kernel)) ?_ hx
  have h1 := eq_EE (k := 1) (u := 721) (h := 11) (v := 721) (by norm_num) (by decide +kernel)
  have h2 := eq_EE (k := 1) (u := 721) (h := 14360) (v := 257) (by norm_num) (by decide +kernel)
  intro s hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  iterate 6 exact Or.inl (nodeG_mem_T _ (by simp))
  · exact Or.inr ⟨_, _, eG_mem 721, h1, eq_zE (k := 1) (by norm_num) (by decide +kernel)⟩
  · exact Or.inr ⟨_, _, eG_mem 721, h1, eq_zE (k := 1) (by norm_num) (by decide +kernel)⟩
  · exact Or.inr ⟨_, _, eG_mem 257, h2, eq_zE (k := 1) (by norm_num) (by decide +kernel)⟩
  · exact Or.inr ⟨_, _, eG_mem 257, h2, eq_zE (k := 1) (by norm_num) (by decide +kernel)⟩

theorem conj_B : nodeG 9 * nodeG 11524 = nodeG 11524 * eG 12 :=
  eq_xE (k := 2) (by norm_num) (by decide +kernel)

theorem conj_C : nodeG 8 * nodeG 12941 = nodeG 12941 * eG 42 :=
  eq_xE (k := 2) (by norm_num) (by decide +kernel)

theorem gen_B {x : ↥GA} (hx : IsConj (nodeG 9) x) : SporKRestGenerating 3 x := by
  refine class_gen KernelCo1ThreeK.eSplitK.T E_pgroup (nodeG 9) [2, 3, 4, 5, 6, 7, 15198, 15328, 15570, 15879]
    (j₁ := 23) (j₂ := 24) (n₁ := 22606) (n₂ := 23001) (by rw [CH_length]; norm_num)
    (by rw [CH_length]; norm_num) (by decide +kernel) (by decide +kernel)
    (inChunk (by decide +kernel) (by decide +kernel)) (inChunk (by decide +kernel) (by decide +kernel)) (by norm_num)
    (by norm_num) (by decide) (eq_out (k := 2) (by norm_num) (by decide +kernel))
    (eq_out (k := 2) (by norm_num) (by decide +kernel)) ?_ hx
  have h2 := eq_xE (k := 2) (x := 9) (h := 15442) (v := 71) (by norm_num) (by decide +kernel)
  intro s hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  iterate 6 exact Or.inl (nodeG_mem_T _ (by simp))
  · exact Or.inr ⟨_, _, eG_mem 12, conj_B, eq_zE (k := 2) (by norm_num) (by decide +kernel)⟩
  · exact Or.inr ⟨_, _, eG_mem 12, conj_B, eq_zE (k := 2) (by norm_num) (by decide +kernel)⟩
  · exact Or.inr ⟨_, _, eG_mem 71, h2, eq_zE (k := 2) (by norm_num) (by decide +kernel)⟩
  · exact Or.inr ⟨_, _, eG_mem 71, h2, eq_zE (k := 2) (by norm_num) (by decide +kernel)⟩

theorem gen_C {x : ↥GA} (hx : IsConj (nodeG 8) x) : SporKRestGenerating 3 x := by
  refine class_gen KernelCo1ThreeK.eSplitK.T E_pgroup (nodeG 8) [2, 3, 4, 5, 6, 7, 15966, 16074, 16790, 16912]
    (j₁ := 26) (j₂ := 27) (n₁ := 24872) (n₂ := 25328) (by rw [CH_length]; norm_num)
    (by rw [CH_length]; norm_num) (by decide +kernel) (by decide +kernel)
    (inChunk (by decide +kernel) (by decide +kernel)) (inChunk (by decide +kernel) (by decide +kernel)) (by norm_num)
    (by norm_num) (by decide) (eq_out (k := 2) (by norm_num) (by decide +kernel))
    (eq_out (k := 2) (by norm_num) (by decide +kernel)) ?_ hx
  have h2 := eq_xE (k := 2) (x := 8) (h := 16481) (v := 573) (by norm_num) (by decide +kernel)
  intro s hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  iterate 6 exact Or.inl (nodeG_mem_T _ (by simp))
  · exact Or.inr ⟨_, _, eG_mem 42, conj_C, eq_zE (k := 2) (by norm_num) (by decide +kernel)⟩
  · exact Or.inr ⟨_, _, eG_mem 42, conj_C, eq_zE (k := 2) (by norm_num) (by decide +kernel)⟩
  · exact Or.inr ⟨_, _, eG_mem 573, h2, eq_zE (k := 2) (by norm_num) (by decide +kernel)⟩
  · exact Or.inr ⟨_, _, eG_mem 573, h2, eq_zE (k := 2) (by norm_num) (by decide +kernel)⟩

theorem dG_one : dG 1 = nodeG 10 := by simp [dG, epM]

theorem dG_two : dG 2 = nodeG 10 ^ 2 := by simp [dG, epM]

theorem dG_three : dG 3 = nodeG 13096 := by simp [dG, epM]

theorem dG_six : dG 6 = nodeG 13096 ^ 2 := by simp [dG, epM]

@[expose] noncomputable def DG : Subgroup ↥GA := Subgroup.closure {nodeG 10, nodeG 13096}

theorem D_pgroup : IsPGroup 3 DG := by
  have hc : nodeG 10 * nodeG 13096 = nodeG 13096 * nodeG 10 := by
    have := eqG (k := 1) (s := 2 * (1 + 4 * 1) + 1) (t := 2 * (1 + 4 * 3) + 1)
      (u := 2 * (1 + 4 * 3) + 1) (w := 2 * (1 + 4 * 1) + 1) (by norm_num) (by decide +kernel)
    rwa [termG_D, termG_D, dG_one, dG_three] at this
  have h1 : nodeG 10 ^ 3 = 1 := by
    have := eqG (k := 1) (s := 2 * (1 + 4 * 2) + 1) (t := 2 * (1 + 4 * 1) + 1) (u := 2 * 11)
      (w := 2 * 11) (by norm_num) (by decide +kernel)
    rwa [termG_D, termG_D, termG_nd, dG_one, dG_two, nodeG_one, mul_one, ← pow_succ] at this
  have h2 : nodeG 13096 ^ 3 = 1 := by
    have := eqG (k := 1) (s := 2 * (1 + 4 * 6) + 1) (t := 2 * (1 + 4 * 3) + 1) (u := 2 * 11)
      (w := 2 * 11) (by norm_num) (by decide +kernel)
    rwa [termG_D, termG_D, termG_nd, dG_three, dG_six, nodeG_one, mul_one, ← pow_succ] at this
  refine @isPGroup_closure_of_commute ↥GA (Subgroup.toGroup GA) 3 _ ?_ ?_
  · intro x hx y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    exacts [Commute.refl _, hc, hc.symm, Commute.refl _]
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    exacts [h1, h2]

theorem dG_mem (v : Nat) : dG v ∈ DG := by
  refine @epM_mem ↥GA (Subgroup.toGroup GA) nodeG DG _ (fun x hx => Subgroup.subset_closure ?_) v 1
    DG.one_mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ rfl

theorem gen_D {x : ↥GA} (hx : IsConj (nodeG 10) x) : SporKRestGenerating 3 x := by
  refine class_gen DG D_pgroup (nodeG 10) [10, 13096, 17179, 17545, 18121, 18256]
    (j₁ := 30) (j₂ := 30) (n₁ := 27605) (n₂ := 28097) (by rw [CH_length]; norm_num)
    (by rw [CH_length]; norm_num) (by decide +kernel) (by decide +kernel)
    (inChunk (by decide +kernel) (by decide +kernel)) (inChunk (by decide +kernel) (by decide +kernel)) (by norm_num)
    (by norm_num) (by decide) (eq_out (k := 3) (by norm_num) (by decide +kernel))
    (eq_out (k := 3) (by norm_num) (by decide +kernel)) ?_ hx
  have h1 := eq_xD (k := 3) (x := 10) (h := 11) (v := 1) (by norm_num) (by decide +kernel)
  have h2 := eq_xD (k := 3) (x := 10) (h := 17786) (v := 3) (by norm_num) (by decide +kernel)
  intro s hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (Subgroup.subset_closure (Set.mem_insert _ _))
  · exact Or.inl (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
  · exact Or.inr ⟨_, _, dG_mem 1, h1, eq_zD (k := 3) (by norm_num) (by decide +kernel)⟩
  · exact Or.inr ⟨_, _, dG_mem 1, h1, eq_zD (k := 3) (by norm_num) (by decide +kernel)⟩
  · exact Or.inr ⟨_, _, dG_mem 3, h2, eq_zD (k := 3) (by norm_num) (by decide +kernel)⟩
  · exact Or.inr ⟨_, _, dG_mem 3, h2, eq_zD (k := 3) (by norm_num) (by decide +kernel)⟩

theorem complete (s : ↥GA) (hs : orderOf s = 3) :
    ∃ r ∈ [eG 721, nodeG 9, nodeG 8, nodeG 10], IsConj r s := by
  haveI : Finite ↥GA := Co1T.finite_GA
  have hQcard : Nat.card Co1T.Qg = 3 ^ (Nat.card ↥(⊤ : Subgroup ↥GA)).factorization 3 := by
    rw [KernelCo1ThreeK.card_QgK, Co1T.factorization_card_GA]
  obtain ⟨g, -, hgq⟩ := @Co3T.exists_conj_mem_of_full ↥GA (Subgroup.toGroup GA) 3
    ⟨Nat.prime_three⟩ ⊤ Co1T.Qg inferInstance le_top hQcard s (Subgroup.mem_top s) hs
  have hto : orderOf (g⁻¹ * s * g) = 3 := by
    have h := Co1T.orderOf_conj_GA g⁻¹ s
    rw [inv_inv] at h
    rw [h, hs]
  have hts : IsConj (g⁻¹ * s * g) s := isConj_iff.2 ⟨g, by group⟩
  rcases KernelCo1ThreeK.fusion_rootK hgq hto with hT | ⟨j, hj, n, hn⟩
  · obtain ⟨v, hv, hve⟩ := mem_T_eG hT
    have hv1 : 1 ≤ v := by
      rcases Nat.eq_zero_or_pos v with rfl | h
      · rw [eG, epM_zero] at hve
        rw [hve, orderOf_one] at hto
        norm_num at hto
      · exact h
    obtain ⟨r, hr, hrc⟩ := orbit_E hv1 hv
    rw [← hve] at hrc
    rw [RT_eq] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨eG 721, by simp, hrc.trans hts⟩
    · exact ⟨nodeG 9, by simp,
        (@isConj_of_mul ↥GA (Subgroup.toGroup GA) _ _ _ conj_B).trans (hrc.trans hts)⟩
    · exact ⟨nodeG 8, by simp,
        (@isConj_of_mul ↥GA (Subgroup.toGroup GA) _ _ _ conj_C).trans (hrc.trans hts)⟩
  · have hconj_r : IsConj (Co1T.root j) (g⁻¹ * s * g) := by
      rw [isConj_iff]
      refine ⟨n, ?_⟩
      rw [hn]
    have hconj : IsConj (Co1T.root j) s := hconj_r.trans hts
    rcases hj with rfl | rfl | rfl
    · have h := nodeG_root (j := 0) (by norm_num)
      simp only [Nat.reduceAdd] at h
      exact ⟨nodeG 8, by simp, by rwa [h]⟩
    · have h := nodeG_root (j := 1) (by norm_num)
      simp only [Nat.reduceAdd] at h
      exact ⟨nodeG 9, by simp, by rwa [h]⟩
    · have h := nodeG_root (j := 2) (by norm_num)
      simp only [Nat.reduceAdd] at h
      exact ⟨nodeG 10, by simp, by rwa [h]⟩

theorem cover : SporKRestCover 3 ↥GA := by
  refine @sporKRest_cover_of_classes ↥GA (Subgroup.toGroup GA) 3 Nat.prime_three _ complete ?_
  intro r hr x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact gen_A hx
  · exact gen_B hx
  · exact gen_C hx
  · exact gen_D hx

end CertificateChecks.KernelCo1Three

end
