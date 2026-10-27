module

public import CFSG.LocalAnalysis.ComponentInitial.SelfCentralizingCoreAutomorphisms
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.Sporadic.Schreier.TitsQT

open CFSG.LocalAnalysis.ComponentInitial

theorem selfCentralizing_sylow_pointwise_inner {M : Type*} [Group M] [Finite M] (p : ℕ)
    [Fact p.Prime] (Q : Subgroup M) [Q.Normal] (hQp : IsPGroup p Q)
    (hQ : Subgroup.centralizer (Q : Set M) ≤ Q) (T : Sylow p M) (α : MulAut M)
    (hα : ∀ t ∈ (T : Subgroup M), α t = t) :
    ∃ a ∈ Q, (∀ q ∈ Q, a * q = q * a) ∧ (∀ t ∈ (T : Subgroup M), a * t = t * a) ∧
      ∀ g : M, α g = a * g * a⁻¹ := by
  have hQT : Q ≤ (T : Subgroup M) := hQp.le_sylow_of_normal T
  have hαQ : α ∈ pointwiseFixingAut Q := fun q hq => hα q (hQT hq)
  set Z : Subgroup M := Subgroup.centralizer (Q : Set M) with hZdef
  have hZQ : Z ≤ Q := hQ
  have hZcomm : ∀ z ∈ Z, ∀ w ∈ Z, z * w = w * z := fun z hz w hw =>
    ((Subgroup.mem_centralizer_iff.1 hz) w (hZQ hw)).symm
  have hZnormal : ∀ m : M, ∀ z ∈ Z, m * z * m⁻¹ ∈ Z := by
    intro m z hz
    rw [hZdef, Subgroup.mem_centralizer_iff] at hz ⊢
    intro q hq
    have hq' : m⁻¹ * q * m ∈ Q := by
      simpa using (inferInstance : Q.Normal).conj_mem q hq m⁻¹
    have h1 := hz _ hq'
    calc q * (m * z * m⁻¹) = m * ((m⁻¹ * q * m) * z) * m⁻¹ := by group
      _ = m * (z * (m⁻¹ * q * m)) * m⁻¹ := by rw [h1]
      _ = (m * z * m⁻¹) * q := by group
  have hc : ∀ x : M, x⁻¹ * α x ∈ Z := fun x => inv_mul_apply_mem_centralizer hαQ x
  have hb : ∀ x : M, α x * x⁻¹ ∈ Z := fun x => by
    have := hZnormal x _ (hc x)
    simpa [mul_assoc] using this
  let _ : CommGroup Z := { (inferInstance : Group Z) with
    mul_comm := fun a b => Subtype.ext (hZcomm a a.2 b b.2) }
  have _ : Z.Normal := ⟨fun z hz m => hZnormal m z hz⟩
  have hZp : IsPGroup p Z := hQp.to_le hZQ
  let T' : Subgroup M := (T : Subgroup M)
  let _ : Fintype (M ⧸ T') := Fintype.ofFinite _
  let n := Fintype.card (M ⧸ T')
  have hn : ¬ p ∣ n := by
    have := T.not_dvd_index
    rwa [Subgroup.index_eq_card, Nat.card_eq_fintype_card] at this
  have hbinv : ∀ x t, t ∈ T' → α (x * t) * (x * t)⁻¹ = α x * x⁻¹ := by
    intro x t ht
    rw [map_mul, hα t ht]
    group
  let B : M ⧸ T' → Z := fun q => ⟨α q.out * q.out⁻¹, hb q.out⟩
  have hBmk : ∀ x : M, ((B (QuotientGroup.mk x) : Z) : M) = α x * x⁻¹ := by
    intro x
    obtain ⟨t, ht⟩ := QuotientGroup.mk_out_eq_mul T' x
    show α (QuotientGroup.mk x : M ⧸ T').out * ((QuotientGroup.mk x : M ⧸ T').out)⁻¹ =
      α x * x⁻¹
    rw [ht]
    exact hbinv x t t.2
  let v : Z := ∏ q : M ⧸ T', B q
  have hcocycle : ∀ g x : M, α (g * x) * (g * x)⁻¹ =
      (g * (α x * x⁻¹) * g⁻¹) * (α g * g⁻¹) := by
    intro g x
    have hw : (g⁻¹ * α g) * (α x * x⁻¹) = (α x * x⁻¹) * (g⁻¹ * α g) :=
      hZcomm _ (hc g) _ (hb x)
    calc α (g * x) * (g * x)⁻¹ = α g * (α x * x⁻¹) * g⁻¹ := by rw [map_mul]; group
      _ = g * ((g⁻¹ * α g) * (α x * x⁻¹)) * g⁻¹ := by group
      _ = g * ((α x * x⁻¹) * (g⁻¹ * α g)) * g⁻¹ := by rw [hw]
      _ = (g * (α x * x⁻¹) * g⁻¹) * (α g * g⁻¹) := by group
  have hv : ∀ g : M, v = (MulAut.conjNormal g : MulAut Z) v * (⟨α g * g⁻¹, hb g⟩ : Z) ^ n := by
    intro g
    have h1 : ∏ q : M ⧸ T', B (g • q) = ∏ q : M ⧸ T', B q :=
      Equiv.prod_comp (MulAction.toPerm g) B
    have h2 : ∀ q : M ⧸ T', B (g • q) =
        (MulAut.conjNormal g : MulAut Z) (B q) * ⟨α g * g⁻¹, hb g⟩ := by
      intro q
      induction q using QuotientGroup.induction_on with
      | H x =>
        apply Subtype.ext
        have e : g • (QuotientGroup.mk x : M ⧸ T') = QuotientGroup.mk (g * x) := rfl
        rw [e, Subgroup.coe_mul, hBmk, MulAut.conjNormal_apply, hBmk]
        exact hcocycle g x
    simp_rw [h2] at h1
    rw [Finset.prod_mul_distrib, ← map_prod, Finset.prod_const, Finset.card_univ] at h1
    exact h1.symm
  obtain ⟨a, ha⟩ : ∃ a : Z, a ^ n = v := ⟨(hZp.powEquiv' hn).symm v, by
    have := (hZp.powEquiv' hn).apply_symm_apply v
    rwa [IsPGroup.powEquiv_apply] at this⟩
  have hba : ∀ g : M, (⟨α g * g⁻¹, hb g⟩ : Z) =
      a * (MulAut.conjNormal g : MulAut Z) a⁻¹ := by
    intro g
    apply (hZp.powEquiv' hn).injective
    rw [IsPGroup.powEquiv_apply, IsPGroup.powEquiv_apply]
    have e1 : (⟨α g * g⁻¹, hb g⟩ : Z) ^ n = ((MulAut.conjNormal g : MulAut Z) v)⁻¹ * v :=
      (inv_mul_eq_iff_eq_mul.2 (hv g)).symm
    rw [e1, mul_pow, ha, ← map_pow, inv_pow, ha, map_inv, mul_comm]
  have hbM : ∀ g : M, α g * g⁻¹ = (a : M) * (g * (a : M)⁻¹ * g⁻¹) := by
    intro g
    have := congrArg Subtype.val (hba g)
    rw [Subgroup.coe_mul, MulAut.conjNormal_apply] at this
    simpa only [Subgroup.coe_inv] using this
  refine ⟨(a : M), hZQ a.2, fun q hq => (Subgroup.mem_centralizer_iff.1 a.2 q hq).symm,
    ?_, ?_⟩
  · intro t ht
    have e := hbM t
    rw [hα t ht, mul_inv_cancel] at e
    calc (a : M) * t = ((a : M) * (t * (a : M)⁻¹ * t⁻¹)) * (t * a) := by group
      _ = 1 * (t * a) := by rw [← e]
      _ = t * a := one_mul _
  · intro g
    calc α g = (α g * g⁻¹) * g := by group
      _ = ((a : M) * (g * (a : M)⁻¹ * g⁻¹)) * g := by rw [hbM g]
      _ = a * g * (a : M)⁻¹ := by group

end CFSG.Sporadic.Schreier.TitsQT
