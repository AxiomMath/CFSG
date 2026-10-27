module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148WM24
import CFSG.RankThree.PartTwo.Sec14.Ronan148WGroup
import CFSG.RankThree.PartTwo.Sec14.Ronan148WCard
import CFSG.RankThree.PartTwo.Sec14.Ronan148JInner
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.M24ThreeLocal

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148W

open CFSG CFSG.Blueprint


theorem exists_inv_mem_normalizer_of_m24 {M : Type} [Group M] [Finite M] {Aq Jq : Subgroup M}
    (hAab : ∀ x ∈ Aq, ∀ y ∈ Aq, x * y = y * x) (hA3 : ∀ x ∈ Aq, x ^ 3 = 1)
    (hAcard : Nat.card Aq = 27)
    (hF3 : ∀ w : M, w ∈ Subgroup.centralizer (Aq : Set M) → w ^ 3 = 1 → w ∈ Aq)
    (hAJ : Aq ≤ Subgroup.normalizer (Jq : Set M)) (e : ↥Jq ≃* NativeSporadic.M24)
    {dq : M} (hdA : dq ∈ Aq) (hdJ : dq ∈ Jq) (hd1 : dq ≠ 1)
    (hdC : 1080 ≤ Nat.card (Subgroup.centralizer ({(⟨dq, hdJ⟩ : ↥Jq)} : Set ↥Jq)))
    {wq : M} (hwA : wq ∈ Aq) (hwJ : wq ∈ Subgroup.centralizer (Jq : Set M)) (hw1 : wq ≠ 1) :
    ∃ y ∈ Jq, y ∈ Subgroup.normalizer (Aq : Set M) ∧ y * dq * y⁻¹ = dq⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ : Subgroup.center ↥Jq = ⊥ := by
    have h := Subgroup.map_center_eq e
    rw [CFSG.Sporadic.Schreier.m24_center_eq_bot'] at h
    exact Subgroup.map_injective (f := (e : ↥Jq →* NativeSporadic.M24)) e.injective
      (by rw [h, Subgroup.map_bot])
  have hJZ : Jq ⊓ Subgroup.centralizer (Jq : Set M) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hz : (⟨x, hx.1⟩ : ↥Jq) ∈ Subgroup.center ↥Jq := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx.2 g g.2)
    rw [hZ, Subgroup.mem_bot] at hz
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hz
  have hinner : ∀ g ∈ Aq, ∃ u ∈ Jq, ∀ x ∈ Jq, g * x * g⁻¹ = u * x * u⁻¹ := by
    intro g hg
    let τ : MulAut ↥Jq := Jq.normalizerMonoidHom ⟨g, hAJ hg⟩
    obtain ⟨u', hu'⟩ := AGLEmbeddingD2.Wilson.MaximalityAmbient.M24ThreeLocal.mulAut_eq_inner_of_m24
      e τ
    refine ⟨(u' : M), u'.2, fun x hx => ?_⟩
    have h1 := congrArg (fun σ : MulAut ↥Jq => ((σ ⟨x, hx⟩ : ↥Jq) : M)) hu'
    simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h1
    exact h1.symm
  have hCD := Ronan148J.sup_eq_of_forall_inner hAab hA3 hF3 hJZ hAJ hinner
  have hdE : dq ∈ Aq ⊓ Jq := ⟨hdA, hdJ⟩
  have hwo : Nat.card (Subgroup.zpowers wq) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hA3 wq hwA) hw1
  have hwE : Subgroup.zpowers wq ⊓ (Aq ⊓ Jq) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxC : x ∈ Subgroup.centralizer (Jq : Set M) :=
      (Subgroup.zpowers_le.mpr hwJ) hx.1
    have hmem : x ∈ Jq ⊓ Subgroup.centralizer (Jq : Set M) := ⟨hx.2.2, hxC⟩
    rw [hJZ] at hmem
    exact hmem
  have hcardE := card_mul_card_le_of_inf_eq_bot hwE (Subgroup.zpowers_le.mpr hwA) inf_le_left
  rw [hwo, hAcard] at hcardE
  have hE9 : Nat.card (Aq ⊓ Jq : Subgroup M) ≤ 9 := by omega
  obtain ⟨j, hjE, hEeq⟩ := exists_eq_sup_zpowers_of_card_le_nine hdE hd1
    (fun y hy => hA3 y hy.1) (fun y hy z hz => hAab y hy.1 z hz.1) hE9
  have hdo : orderOf (⟨dq, hdJ⟩ : ↥Jq) = 3 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime (hA3 dq hdA) hd1
  have hjd : (⟨j, hjE.2⟩ : ↥Jq) * ⟨dq, hdJ⟩ = ⟨dq, hdJ⟩ * ⟨j, hjE.2⟩ :=
    Subtype.ext (hAab j hjE.1 dq hdA)
  have hj3 : (⟨j, hjE.2⟩ : ↥Jq) ^ 3 = 1 := Subtype.ext (by simpa using hA3 j hjE.1)
  obtain ⟨y', hy'd, i, m, hy'j⟩ := exists_inv_of_m24 e hdo hdC hjd hj3
  have hyd : (y' : M) * dq * (y' : M)⁻¹ = dq⁻¹ := by
    have := congrArg Subtype.val hy'd
    simpa using this
  have hyj : (y' : M) * j * (y' : M)⁻¹ = dq ^ i * j ^ m := by
    have := congrArg Subtype.val hy'j
    simpa using this
  refine ⟨y', y'.2, ?_, hyd⟩
  rw [← hCD]
  refine mem_normalizer_sup_of (fun u hu => ?_) (fun v hv => ?_)
  · have h1 : (y' : M) * u = u * y' := Subgroup.mem_centralizer_iff.mp hu.2 y' y'.2
    calc (y' : M) * u * (y' : M)⁻¹ = u * y' * (y' : M)⁻¹ := by rw [h1]
      _ = u := by group
  · rw [hEeq] at hv ⊢
    refine conj_mem_sup_zpowers ?_ ?_ hv
    · rw [hyd]
      exact Subgroup.mem_sup_left (Subgroup.inv_mem _ (Subgroup.mem_zpowers dq))
    · rw [hyj]
      exact Subgroup.mul_mem _
        (Subgroup.mem_sup_left (Subgroup.pow_mem _ (Subgroup.mem_zpowers dq) i))
        (Subgroup.mem_sup_right (Subgroup.pow_mem _ (Subgroup.mem_zpowers j) m))

end CFSG.RankThree.PartTwo.Sec14.Ronan148W
