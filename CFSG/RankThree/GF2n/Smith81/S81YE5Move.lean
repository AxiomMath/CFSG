module

public import CFSG.RankThree.GF2n.Smith81.S81YE5Odd
public import CFSG.RankThree.GF2n.Smith81.S81YE5Mnf

public section

namespace CFSG.RankThree.GF2n.Smith81.RootGenE5

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.RankThree.GF2n.Smith81
  CFSG.RankThree.GF2n.Smith81.E7Model CFSG.RankThree.GF2n.Smith81.RootGen

variable
  {K : Type} [Field K]


theorem e7_move [Finite K] [CharP K 2] {r s : V K ≃ₗ[K] V K} (hr : IsRt5 r) (hs : IsRt5 s)
    (hB : ¬ (Odd (orderOf (r * s)) ∧ r * s ≠ 1)) {p : V K}
    (hp : IsPurePt (EAut K) (w0 : V K) p)
    (hpr : p ∈ LinearMap.range ((r : V K →ₗ[K] V K) - 1)) :
    ∃ c ∈ EAut K, c * r = r * c ∧ s (c p) = c p := by
  obtain ⟨gr, hgr, rfl⟩ := isRt5_iff.mp hr
  obtain ⟨gs, hgs, rfl⟩ := isRt5_iff.mp hs
  obtain ⟨e, a, b, δ, ha, hb, hδ, hea, heb⟩ := e7_pairNF hgr hgs
  have hord : ∀ x : G7 K, orderOf (act7 x) = orderOf x := fun x =>
    orderOf_injective (MonoidHom.mk' (act7 : G7 K → V K ≃ₗ[K] V K) act7_mul) act7_injective x
  have hconj : ∀ x : G7 K, orderOf (e * x * e⁻¹) = orderOf x := fun x =>
    orderOf_injective (MulAut.conj e).toMonoidHom (MulAut.conj e).injective x
  have hmulap : ∀ (g k : G7 K) (x : V K), act7 (g * k) x = act7 g (act7 k x) := fun g k x => by
    rw [act7_mul]
    exact LinearEquiv.mul_apply _ _ _
  have hδne : δ ≠ -theta := by
    intro hδeq
    subst hδeq
    have hprod : e * (gr * gs) * e⁻¹ =
        e7Data_valid.xm K theta a * e7Data_valid.xm K (-theta) b := by
      rw [show e * (gr * gs) * e⁻¹ = (e * gr * e⁻¹) * (e * gs * e⁻¹) by group, hea, heb]
    obtain ⟨hodd, hne1⟩ := xm_theta_neg_odd ha hb
    have hord' : orderOf (gr * gs) =
        orderOf (e7Data_valid.xm K theta a * e7Data_valid.xm K (-theta) b) := by
      rw [← hconj (gr * gs), hprod]
    have hgs1 : gr * gs ≠ 1 := by
      intro h1
      apply hne1
      rw [← hprod, h1]
      simp
    apply hB
    rw [← act7_mul]
    refine ⟨?_, ?_⟩
    · rw [hord, hord']
      exact hodd
    · intro h1
      apply hgs1
      apply act7_injective
      rw [act7_one]
      exact h1
  obtain ⟨g', hg'Γ, c, hc, rfl⟩ := hp
  obtain ⟨k, rfl⟩ := mem_EAut_iff_act7.mp hg'Γ
  obtain ⟨w, hw⟩ := hpr
  have hegr : e * gr = e7Data_valid.xm K theta a * e := by
    rw [← hea]
    group
  have h1' : e * gs = e7Data_valid.xm K δ b * e := by
    rw [← heb]
    group
  have hgr' : gr = e⁻¹ * (e7Data_valid.xm K theta a * e) := by
    rw [← hegr, inv_mul_cancel_left]
  have hq : ∃ (g : G7 K) (c' : K), c' ≠ 0 ∧
      act7 e (c • act7 k (w0 : V K)) = c' • act7 g (w0 : V K) :=
    ⟨e * k, c, hc, by rw [map_smul, hmulap]⟩
  have hA2 : act7 e (act7 gr w) = act7 (e7Data_valid.xm K theta a) (act7 e w) := by
    rw [← hmulap e gr w, hegr, hmulap]
  have hqr : act7 e (c • act7 k (w0 : V K)) ∈
      LinearMap.range ((act7 (e7Data_valid.xm K theta a) : V K →ₗ[K] V K) - 1) := by
    rw [LinearMap.mem_range]
    refine ⟨act7 e w, ?_⟩
    rw [← hw]
    simp only [LinearMap.sub_apply, Module.End.one_apply, LinearEquiv.coe_coe, map_sub, hA2]
  obtain ⟨n, hncomm, hnfix⟩ := move_normal_form ha hδ hδne b hq hqr
  have hfin1 : act7 (e⁻¹ * n * e) * act7 gr = act7 gr * act7 (e⁻¹ * n * e) := by
    rw [← act7_mul, ← act7_mul]
    congr 1
    rw [hgr']
    calc (e⁻¹ * n * e) * (e⁻¹ * (e7Data_valid.xm K theta a * e))
        = e⁻¹ * (n * e7Data_valid.xm K theta a) * e := by group
      _ = e⁻¹ * (e7Data_valid.xm K theta a * n) * e := by rw [hncomm a]
      _ = e⁻¹ * (e7Data_valid.xm K theta a * e) * (e⁻¹ * n * e) := by group
  refine ⟨act7 (e⁻¹ * n * e), mem_EAut_iff_act7.mpr ⟨e⁻¹ * n * e, rfl⟩, hfin1, ?_⟩
  apply (act7 e).injective
  have hA : ∀ x : V K, act7 e (act7 gs x) = act7 (e7Data_valid.xm K δ b) (act7 e x) := by
    intro x
    rw [← hmulap e gs x, h1', hmulap]
  have hC : ∀ x : V K, act7 e (act7 (e⁻¹ * n * e) x) = act7 n (act7 e x) := by
    intro x
    have h2 : e * (e⁻¹ * n * e) = n * e := by group
    rw [← hmulap e (e⁻¹ * n * e) x, h2, hmulap]
  rw [hA, hC, hnfix]

end CFSG.RankThree.GF2n.Smith81.RootGenE5
