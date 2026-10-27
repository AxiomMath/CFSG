module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeT79Cfg
public import CFSG.LocalAnalysis.WeakClosure81.EightSixBorelSpNormal
public import CFSG.RankThree.PartOne.KC.SymplecticFullRankTwo
public import CFSG.ClassicalGroups.Alternating.TransvectionGeneration

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.LocalAnalysis.WeakClosure81.SevenK
open CFSG.RankThree.PartOne.KCSpFull
open CFSG.RankThree.Classical
open CFSG.ClassicalGroups.Alternating

variable {k : ℕ} {F : Type} [Field F]

private theorem nine3_spTransvection_comm {p q : Fin k ⊕ Fin k → F}
    (h : spForm k F p q = 0) (lam mu : F) :
    spTransvection p lam * spTransvection q mu =
      spTransvection q mu * spTransvection p lam := by
  apply spLin_injective
  simp only [map_mul, spLin_spTransvection]
  exact symplecticTransvection_comm spForm_isAlt h lam mu

private theorem nine3_commute_condition {y : ↥(StatedSp k F)} {a : Fin k ⊕ Fin k → F} {c : F}
    (hc : c ≠ 0) (h : y * spTransvection a c = spTransvection a c * y) :
    ∀ z : Fin k ⊕ Fin k → F,
      spForm k F z a • spEnd y a = spForm k F (spEnd y z) a • a := by
  intro z
  have h1 := congrArg (fun g : ↥(StatedSp k F) => spEnd g z) h
  rw [spEnd_mul, spEnd_mul, Module.End.mul_apply, Module.End.mul_apply, spEnd_spTransvection,
    spEnd_spTransvection, map_add, map_smul] at h1
  have h2 : (c * spForm k F z a) • spEnd y a =
      (c * spForm k F (spEnd y z) a) • a := add_left_cancel h1
  rw [mul_smul, mul_smul] at h2
  exact smul_right_injective (Fin k ⊕ Fin k → F) hc h2

private theorem nine3_spForm_eq_zero_of_commute {p q : Fin k ⊕ Fin k → F} {lam mu : F}
    (hlam : lam ≠ 0) (hmu : mu ≠ 0)
    (hcomm : spTransvection p lam * spTransvection q mu =
      spTransvection q mu * spTransvection p lam) :
    spForm k F p q = 0 := by
  by_contra hpq
  have hp : p ≠ 0 := fun h0 => hpq (by simp [h0])
  have hz := nine3_commute_condition (y := spTransvection q mu) (a := p) hlam hcomm.symm p
  rw [spForm_isAlt.self_eq_zero, zero_smul] at hz
  have hval : spForm k F (spEnd (spTransvection q mu) p) p =
      -(mu * (spForm k F p q * spForm k F p q)) := by
    rw [spEnd_spTransvection, map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
      smul_eq_mul, spForm_isAlt.self_eq_zero, zero_add, ← spForm_isAlt.neg_eq p q]
    ring
  rw [hval] at hz
  have h1 : -(mu * (spForm k F p q * spForm k F p q)) = 0 := by
    rcases smul_eq_zero.mp hz.symm with h | h
    · exact h
    · exact absurd h hp
  have h2 : mu * (spForm k F p q * spForm k F p q) = 0 := neg_eq_zero.mp h1
  have h3 : spForm k F p q * spForm k F p q = 0 := (mul_eq_zero.mp h2).resolve_left hmu
  exact hpq (mul_self_eq_zero.mp h3)

private theorem nine3_spEnd_injective (g : ↥(StatedSp k F)) : Function.Injective (spEnd g) := by
  intro x y hxy
  have hx : spEnd g⁻¹ (spEnd g x) = x := by
    rw [← Module.End.mul_apply, ← spEnd_mul, inv_mul_cancel, spEnd_one, Module.End.one_apply]
  have hy : spEnd g⁻¹ (spEnd g y) = y := by
    rw [← Module.End.mul_apply, ← spEnd_mul, inv_mul_cancel, spEnd_one, Module.End.one_apply]
  rw [hxy] at hx
  exact hx.symm.trans hy

private theorem nine3_exists_transvection_repr {c g : ↥(StatedSp k F)} (hg : IsConj c g)
    {p : Fin k ⊕ Fin k → F} {lam : F} (hp : p ≠ 0) (hlam : lam ≠ 0)
    (hc_eq : c = spTransvection p lam) :
    ∃ q : Fin k ⊕ Fin k → F, q ≠ 0 ∧ ∃ mu : F, mu ≠ 0 ∧ g = spTransvection q mu := by
  obtain ⟨u, hu⟩ := hg
  refine ⟨spEnd (u : ↥(StatedSp k F)) p, ?_, lam, hlam, ?_⟩
  · intro h0
    exact hp (nine3_spEnd_injective _ (by rw [h0, map_zero]))
  · have h1 : (u : ↥(StatedSp k F)) * c * (u : ↥(StatedSp k F))⁻¹ = g := by
      rw [hu.eq, mul_assoc, mul_inv_cancel, mul_one]
    rw [← h1, hc_eq]
    exact spTransvection_conj _ _ _

private theorem nine3_isConj_spTransvection [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n)
    {p q : Fin k ⊕ Fin k → F} (hp : p ≠ 0) (hq : q ≠ 0) {lam mu : F}
    (hlam : lam ≠ 0) (hmu : mu ≠ 0) :
    IsConj (spTransvection p lam) (spTransvection q mu) := by
  rw [isConj_iff]
  obtain ⟨g, hg⟩ := exists_spEnd_eq (K := F) hp hq
  obtain ⟨h', hh'⟩ := borel86_spn_exists_conj_spTransvection (k := k) hF hq hlam hmu
  refine ⟨h' * g, ?_⟩
  rw [mul_inv_rev,
    show h' * g * spTransvection p lam * (g⁻¹ * h'⁻¹) =
      h' * (g * spTransvection p lam * g⁻¹) * h'⁻¹ by group,
    spTransvection_conj, hg, hh']

theorem nine3_prop710_sp {k : ℕ} {F : Type} [Field F] [Finite F]
    (hF : ∃ n : ℕ, 1 ≤ n ∧ Nat.card F = 2 ^ n)
    {c a e a' v : ↥(StatedSp k F)} (hc : IsSymplecticTransvectionIn k c)
    (h : Nine3Config c a e a' v) :
    ∃ d, IsConj c d ∧ d ≠ v ∧ d * a = a * d ∧ d * e = e * d := by
  obtain ⟨n, _hn1, hFn⟩ := hF
  obtain ⟨p, lam, hp, hlam, hc_eq⟩ := borel86_spn_eq_spTransvection hc
  obtain ⟨pa, hpa, α, hα, ha_eq⟩ := nine3_exists_transvection_repr h.conj_a hp hlam hc_eq
  obtain ⟨pb, hpb, β, hβ, he_eq⟩ := nine3_exists_transvection_repr h.conj_e hp hlam hc_eq
  obtain ⟨ps, hps, γ, hγ, hv_eq⟩ := nine3_exists_transvection_repr h.conj_v hp hlam hc_eq
  have hpq : spForm k F pa pb ≠ 0 := by
    intro h0
    refine Nine3Config.not_comm_ae h ?_
    rw [ha_eq, he_eq]
    exact nine3_spTransvection_comm h0 α β
  have hsp : spForm k F ps pa = 0 :=
    nine3_spForm_eq_zero_of_commute hγ hα (by rw [← hv_eq, ← ha_eq]; exact h.comm_va)
  have hspb : spForm k F ps pb = 0 :=
    nine3_spForm_eq_zero_of_commute hγ hβ (by rw [← hv_eq, ← he_eq]; exact h.comm_ve)
  obtain ⟨w, hw⟩ : ∃ w, spForm k F w ps ≠ 0 := by
    by_contra hh
    rw [not_exists] at hh
    exact hps (spForm_nondegenerate.2 ps fun w => not_not.mp (hh w))
  set s' : Fin k ⊕ Fin k → F :=
    w + (-(spForm k F w pb) / spForm k F pa pb) • pa +
      (spForm k F w pa / spForm k F pa pb) • pb with hs'def
  have hs'pa : spForm k F s' pa = 0 := by
    rw [hs'def]
    simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
      spForm_isAlt.self_eq_zero, mul_zero, add_zero]
    rw [← spForm_isAlt.neg_eq pa pb]
    field_simp
    ring
  have hs'pb : spForm k F s' pb = 0 := by
    rw [hs'def]
    simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
      spForm_isAlt.self_eq_zero, mul_zero, add_zero]
    field_simp
    ring
  have hs'ps : spForm k F s' ps ≠ 0 := by
    have hpa' : spForm k F pa ps = 0 := by
      rw [← spForm_isAlt.neg_eq ps pa, hsp, neg_zero]
    have hpb' : spForm k F pb ps = 0 := by
      rw [← spForm_isAlt.neg_eq ps pb, hspb, neg_zero]
    rw [hs'def]
    simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, hpa',
      hpb', mul_zero, add_zero]
    exact hw
  have hs'0 : s' ≠ 0 := fun h0 => hs'ps (by simp [h0])
  refine ⟨spTransvection s' 1, ?_, ?_, ?_, ?_⟩
  · rw [hc_eq]
    exact nine3_isConj_spTransvection hFn hp hs'0 hlam one_ne_zero
  · intro hEq
    have hEq' : spTransvection ps γ = spTransvection s' 1 := hv_eq.symm.trans hEq.symm
    obtain ⟨μ, _hμ0, hμs, -⟩ :=
      borel86_spn_exists_smul_of_spTransvection_eq (a := s') (b := ps) (s := γ) (t := 1)
        hs'0 one_ne_zero hEq'
    exact hs'ps (by rw [hμs, map_smul, spForm_isAlt.self_eq_zero, smul_zero])
  · rw [ha_eq]
    exact nine3_spTransvection_comm hs'pa 1 α
  · rw [he_eq]
    exact nine3_spTransvection_comm hs'pb 1 β

end CFSG.LocalAnalysis.WeakClosure81
