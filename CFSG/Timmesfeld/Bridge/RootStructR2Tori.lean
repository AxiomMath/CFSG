module

public import CFSG.GH74.Uniqueness.Bender.Lemma32
public import CFSG.GH74.Uniqueness.Bender.Unitary36d

public section

namespace CFSG.Timmesfeld.Bridge.Tori

open CFSG.GH74.Uniqueness.Bender

variable {U : Type*} [Group U] [Finite U]

theorem psu3_exists_centralizing {m : ℕ} (hm : 2 ≤ m) (e : U ≃* CFSG.Theory.Comparator.PSU3Model m)
    {S S' : Sylow 2 U} (hSS' : S ≠ S') :
    ∃ g : U, orderOf g = (2 ^ m + 1) / Nat.gcd 3 (2 ^ m + 1) ∧
      (∀ z ∈ S, (∀ s ∈ S, Commute s z) → Commute g z) ∧
      (∀ z ∈ S', (∀ s ∈ S', Commute s z) → Commute g z) := by
  have hBT : BenderType U m 3 ((2 ^ m + 1) / Nat.gcd 3 (2 ^ m + 1)) := .unitary m hm e
  obtain ⟨t, I, -, htt, htS, -, hZI, -, hcomm, -⟩ := hBT.lemma_3_6_d_unitary S
  have hL := hBT.lemma_3_2 S htt htS
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  set B := GH74.Uniqueness.Bender.borel (S : Subgroup U) with hB
  have : IsCyclic (fixCartan (S : Subgroup U) t) := hL.isCyclic_fix
  obtain ⟨x, hx⟩ := IsCyclic.exists_generator (α := fixCartan (S : Subgroup U) t)
  have hxo : orderOf (x : U) = (2 ^ m + 1) / Nat.gcd 3 (2 ^ m + 1) := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hx, hL.card_fix]
  have hxZ : ∀ z ∈ rootCenter (S : Subgroup U), (x : U) * z = z * x := fun z hz =>
    hcomm x x.2 z (hZI hz)
  have hxt : (x : U) * t = t * x := by
    have := (Subgroup.mem_inf.mp x.2).2
    rw [Subgroup.mem_centralizer_iff] at this
    exact (this t rfl).symm
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq U S S'
  have hgS : g ∉ B := fun hgN => hSS' (by
    rw [← hg]
    exact (Sylow.smul_eq_iff_mem_normalizer.mpr hgN).symm)
  obtain ⟨p, hpS, m₀, hm₀, rfl⟩ := hL.bruhat g hgS
  have hmemS' : ∀ y : U, y ∈ (S' : Subgroup U) ↔ t * p⁻¹ * y * p * t ∈ (S : Subgroup U) := by
    intro y
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv,
      MulAut.smul_def, MulAut.conj_apply, inv_inv]
    have e1 : (p * t * m₀)⁻¹ * y * (p * t * m₀) = m₀⁻¹ * (t * p⁻¹ * y * p * t) * m₀⁻¹⁻¹ := by
      simp only [mul_inv_rev, hti, inv_inv]
      group
    rw [e1]
    exact (Subgroup.mem_normalizer_iff.mp (B.inv_mem hm₀) _).symm
  refine ⟨p * x * p⁻¹, ?_, ?_, ?_⟩
  · rw [← hxo, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
  · intro z hz hzc
    have hzZ : z ∈ rootCenter (S : Subgroup U) :=
      mem_rootCenter_iff.mpr ⟨hz, fun s hs => (hzc s hs).eq⟩
    have hpz : p * z = z * p := (hzc p hpS).eq
    show p * x * p⁻¹ * z = z * (p * x * p⁻¹)
    calc p * x * p⁻¹ * z = p * x * (p⁻¹ * z) := by group
      _ = p * x * (z * p⁻¹) := by rw [((hzc p hpS).inv_left).eq]
      _ = p * ((x : U) * z) * p⁻¹ := by group
      _ = p * (z * x) * p⁻¹ := by rw [hxZ z hzZ]
      _ = (p * z) * x * p⁻¹ := by group
      _ = z * (p * x * p⁻¹) := by rw [hpz]; group
  · intro z' hz' hzc'
    set w := t * p⁻¹ * z' * p * t with hw
    have hwS : w ∈ (S : Subgroup U) := (hmemS' z').mp hz'
    have hwZ : w ∈ rootCenter (S : Subgroup U) := by
      refine mem_rootCenter_iff.mpr ⟨hwS, fun s hs => ?_⟩
      set s₁ := p * t * s * t * p⁻¹ with hs₁
      have hss : s = t * p⁻¹ * s₁ * p * t := by
        rw [hs₁]
        calc s = (t * t) * s * (t * t) := by rw [htt, one_mul, mul_one]
          _ = t * p⁻¹ * (p * t * s * t * p⁻¹) * p * t := by group
      have hs' : s₁ ∈ (S' : Subgroup U) := by
        rw [hmemS', ← hss]
        exact hs
      have h1 := (hzc' _ hs').eq
      have hmid : ∀ a b : U, t * p⁻¹ * a * p * t * (t * p⁻¹ * b * p * t) =
          t * p⁻¹ * (a * b) * p * t := by
        intro a b
        calc t * p⁻¹ * a * p * t * (t * p⁻¹ * b * p * t) =
            t * p⁻¹ * a * p * (t * t) * p⁻¹ * b * p * t := by group
          _ = t * p⁻¹ * (a * b) * p * t := by rw [htt]; group
      rw [hss, hw, hmid, hmid, h1]
    have hz'w : z' = p * t * w * t * p⁻¹ := by
      rw [hw]
      calc z' = (p * p⁻¹) * z' * (p * p⁻¹) := by group
        _ = p * (t * t) * p⁻¹ * z' * p * (t * t) * p⁻¹ := by rw [htt]; group
        _ = p * t * (t * p⁻¹ * z' * p * t) * t * p⁻¹ := by group
    show p * x * p⁻¹ * z' = z' * (p * x * p⁻¹)
    rw [hz'w]
    have hxw := hxZ w hwZ
    have hxt' : (x : U) * t = t * x := hxt
    calc p * x * p⁻¹ * (p * t * w * t * p⁻¹) = p * ((x : U) * t) * w * t * p⁻¹ := by group
      _ = p * t * ((x : U) * w) * t * p⁻¹ := by rw [hxt']; group
      _ = p * t * w * ((x : U) * t) * p⁻¹ := by rw [hxw]; group
      _ = p * t * w * t * x * p⁻¹ := by rw [hxt']; group
      _ = p * t * w * t * p⁻¹ * (p * x * p⁻¹) := by group

end CFSG.Timmesfeld.Bridge.Tori
