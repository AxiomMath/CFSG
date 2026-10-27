module

public import CFSG.Quasithin.AppendixH.H15.CocodeTwoFrame
public import CFSG.Quasithin.AppendixH.H15.CocodeTwoEngineXi

public section

open scoped Pointwise

namespace CFSG.ASVolI.AppH

open CFSG.ASVolI.ChH CFSG.Monster.Code CFSG.Quasithin CFSG.Quasithin.H.Mathieu

variable {d : ℕ} {a b : Fin 24} {O : Finset (Fin 24)} {Tr S : Finset (Finset (Fin 24))}
  {B : Finset (Fin 24)} {T₀ Γ : Subgroup S24} {V : Type} [CommGroup V] {ρ : ↥Γ →* MulAut V}
  {β : ↥(⊤ : Subgroup V) →* ↥(mathModel false d a b Γ).sec ⧸
    (mathModel false d a b Γ).ker.subgroupOf (mathModel false d a b Γ).sec}

private theorem exists_ne_one_ne {G : Type*} [Group G] (hnc : ¬ IsCyclic G) :
    ∃ g h : G, g ≠ 1 ∧ h ≠ 1 ∧ g ≠ h := by
  by_contra hcon
  apply hnc
  by_cases h : ∃ g : G, g ≠ 1
  · obtain ⟨g, hg⟩ := h
    refine isCyclic_iff_exists_zpowers_eq_top.2 ⟨g, ?_⟩
    rw [eq_top_iff]
    intro x _
    by_cases hx : x = 1
    · rw [hx]; exact (Subgroup.zpowers g).one_mem
    · have hxg : x = g := by
        by_contra hne
        exact hcon ⟨x, g, hx, hg, hne⟩
      rw [hxg]; exact Subgroup.mem_zpowers g
  · push Not at h
    haveI : Subsingleton G := ⟨fun a b => (h a).trans (h b).symm⟩
    exact isCyclic_of_subsingleton

theorem conj_mem_octFix {m k : S24} (hm : m ∈ octStab O) (hk : k ∈ octFix O) :
    m * k * m⁻¹ ∈ octFix O := by
  have hmem : (⟨k, octFix_le_octStab O hk⟩ : ↥(octStab O)) ∈
      (octFix O).subgroupOf (octStab O) := Subgroup.mem_subgroupOf.2 hk
  have hconj := (normal_octFix O).conj_mem ⟨k, octFix_le_octStab O hk⟩ hmem ⟨m, hm⟩
  rw [Subgroup.mem_subgroupOf] at hconj
  simpa using hconj

theorem kLayer_offender (hM : MCtx false d a b O Tr S B T₀ Γ ρ β) :
    H.IsFOneOffender ρ.range (rImg ρ (octFix O)) := by
  obtain ⟨D, c, hD, hn, hdU, hActs⟩ := exists_kFrame hM
  refine ⟨⟨Subgroup.map_le_range ρ _, engine_ne_bot hD hActs, engine_isElemAbelian2 hD hActs⟩, ?_⟩
  rw [engine_rkIdx_fixV hD hActs, engine_rk hD hActs, hn, hdU]
  by_cases hd : d = 22
  · norm_num [if_pos hd]
  · norm_num [if_neg hd]

theorem kLayer_rk_fixV (hM : MCtx false d a b O Tr S B T₀ Γ ρ β) :
    rk ↥(fixV (rImg ρ (octFix O))) = (if d = 22 then 5 else 6) := by
  obtain ⟨D, c, hD, hn, hdU, hActs⟩ := exists_kFrame hM
  rw [engine_rk_fixV hD hActs, hdU]

theorem kLayer_card_fixV (hM : MCtx false d a b O Tr S B T₀ Γ ρ β) :
    Nat.card ↥(fixV (rImg ρ (octFix O))) = 2 ^ (if d = 22 then 5 else 6) := by
  obtain ⟨D, c, hD, hn, hdU, hActs⟩ := exists_kFrame hM
  haveI : Finite V := c.finite
  rw [card_eq_two_pow c.sq_eq_one (fixV (rImg ρ (octFix O))), kLayer_rk_fixV hM]

theorem kLayer_rkIdx_xiSub (hM : MCtx false d a b O Tr S B T₀ Γ ρ β) :
    rkIdx (xiSub (rImg ρ (octFix O))) = 1 := by
  obtain ⟨D, c, hD, hn, hdU, hActs⟩ := exists_kFrame hM
  exact engine_rkIdx_xiSub hD hActs

theorem kLayer_noncyclic (hM : MCtx false d a b O Tr S B T₀ Γ ρ β) {A : Subgroup S24}
    (hA : A ≤ octFix O) (hnc : ¬ IsCyclic ↥A) :
    fixV (rImg ρ A) = fixV (rImg ρ (octFix O)) := by
  obtain ⟨D, c, hD, hn, hdU, hActs⟩ := exists_kFrame hM
  have hmono : (A.subgroupOf Γ) ≤ ((octFix O).subgroupOf Γ) := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hA hx
  have hle1 : fixV (rImg ρ (octFix O)) ≤ fixV (rImg ρ A) := by
    intro v hv
    rw [mem_fixV] at hv ⊢
    intro x hx
    exact hv x (Subgroup.map_mono hmono hx)
  refine le_antisymm ?_ hle1
  intro v hv
  obtain ⟨g1, g2, hg1ne, hg2ne, hg12⟩ := exists_ne_one_ne hnc
  let gg1 : ↥Γ := ⟨(g1 : S24), mctx_octFix_le hM (hA g1.2)⟩
  let gg2 : ↥Γ := ⟨(g2 : S24), mctx_octFix_le hM (hA g2.2)⟩
  have hg1A : ρ gg1 ∈ rImg ρ A :=
    Subgroup.mem_map.2 ⟨gg1, Subgroup.mem_subgroupOf.2 g1.2, rfl⟩
  have hg2A : ρ gg2 ∈ rImg ρ A :=
    Subgroup.mem_map.2 ⟨gg2, Subgroup.mem_subgroupOf.2 g2.2, rfl⟩
  have hg1A0 : ρ gg1 ∈ rImg ρ (octFix O) :=
    Subgroup.mem_map.2 ⟨gg1, Subgroup.mem_subgroupOf.2 (hA g1.2), rfl⟩
  have hg2A0 : ρ gg2 ∈ rImg ρ (octFix O) :=
    Subgroup.mem_map.2 ⟨gg2, Subgroup.mem_subgroupOf.2 (hA g2.2), rfl⟩
  have hg1ne' : ρ gg1 ≠ 1 := fun hρ =>
    hg1ne (Subtype.ext (by
      have h1 : gg1 = 1 := mctx_rho_injective hM (by rw [hρ, map_one])
      exact congrArg (fun x : ↥Γ => (x : S24)) h1))
  have hg2ne' : ρ gg2 ≠ 1 := fun hρ =>
    hg2ne (Subtype.ext (by
      have h1 : gg2 = 1 := mctx_rho_injective hM (by rw [hρ, map_one])
      exact congrArg (fun x : ↥Γ => (x : S24)) h1))
  have hg12' : ρ gg1 ≠ ρ gg2 := fun hρ =>
    hg12 (Subtype.ext (by
      have h1 : gg1 = gg2 := mctx_rho_injective hM hρ
      exact congrArg (fun x : ↥Γ => (x : S24)) h1))
  rw [mem_fixV] at hv
  exact engine_fixV_noncyclic hD hActs (ρ gg1) hg1A0 (ρ gg2) hg2A0 hg1ne' hg2ne' hg12'
    v (hv (ρ gg1) hg1A) (hv (ρ gg2) hg2A)

theorem kLayer_fullTransp (hM : MCtx false d a b O Tr S B T₀ Γ ρ β) :
    FullTranspAxis (rImg ρ (MY Γ (Yd d a b O))) (rImg ρ (octFix O)) (fixV (rImg ρ (octFix O)))
      (xiSub (rImg ρ (octFix O))) := by
  obtain ⟨D, c, hD, hn, hdU, hActs⟩ := exists_kFrame hM
  refine fullTranspAxis_of_engine hD hActs (G := rImg ρ (MY Γ (Yd d a b O))) ?_
  intro h hh g hg
  obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hh
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hg
  have hmO : (m : S24) ∈ octStab O :=
    mctx_mY_le hM (Subgroup.mem_subgroupOf.1 hm)
  have hkO : (k : S24) ∈ octFix O := Subgroup.mem_subgroupOf.1 hk
  have hconj : (m : S24) * (k : S24) * (m : S24)⁻¹ ∈ octFix O := conj_mem_octFix hmO hkO
  have hmem : m * k * m⁻¹ ∈ (octFix O).subgroupOf Γ := by
    rw [Subgroup.mem_subgroupOf]
    simpa using hconj
  have hgoal : ρ m * ρ k * (ρ m)⁻¹ = ρ (m * k * m⁻¹) := by
    rw [map_mul, map_mul, map_inv]
  rw [hgoal]
  exact Subgroup.mem_map.2 ⟨m * k * m⁻¹, hmem, rfl⟩

theorem kLayer_centralizes (hM : MCtx false d a b O Tr S B T₀ Γ ρ β) {z g : ↥Γ}
    (hz : (z : S24) ∈ octFix O) (hg : (g : S24) ∈ octFix O) (hz1 : z ≠ 1)
    (hfix : ∀ v : V, ρ z v = v → ρ g v = v) : g = 1 ∨ g = z := by
  obtain ⟨D, c, hD, hn, hdU, hActs⟩ := exists_kFrame hM
  have hzA : ρ z ∈ rImg ρ (octFix O) :=
    Subgroup.mem_map.2 ⟨z, Subgroup.mem_subgroupOf.2 hz, rfl⟩
  have hgA : ρ g ∈ rImg ρ (octFix O) :=
    Subgroup.mem_map.2 ⟨g, Subgroup.mem_subgroupOf.2 hg, rfl⟩
  have hz1' : ρ z ≠ 1 := fun hρ =>
    hz1 (mctx_rho_injective hM (by rw [hρ, map_one]))
  rcases engine_centralizes hD hActs (g := ρ z) (h := ρ g) hzA hgA hz1' hfix with h1 | h2
  · exact Or.inl (mctx_rho_injective hM (by rw [h1, map_one]))
  · exact Or.inr (mctx_rho_injective hM h2)

end CFSG.ASVolI.AppH
