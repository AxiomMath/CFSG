module

public import CFSG.LocalAnalysis.UniquenessCase.UC6Mod

public section

namespace CFSG.LocalAnalysis.UniquenessCase

open Subgroup CFSG.Open CFSG.ABGLocalTools
open scoped IsMulCommutative
open CFSG.RankThree.FFModules (fixSub)

namespace UC6

section Module

variable {Mg : Type} [Group Mg] [Finite Mg] (Q₀ : Subgroup Mg) [Q₀.Normal]
  [IsElementaryAbelian 2 (↥Q₀ ⧸ frattini ↥Q₀)]

theorem frattiniRep_eq_one_of_mem_uc6 {q : Mg} (hq : q ∈ Q₀) : frattiniRep Q₀ q = 1 := by
  refine LinearMap.ext fun v => ?_
  obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
  have hv : v = Additive.ofMul (w : ↥Q₀ ⧸ frattini ↥Q₀) := by rw [hw]; rfl
  rw [hv, frattiniRep_apply_mk, Module.End.one_apply]
  congr 1
  have h1 : (MulAut.conjNormal q w : ↥Q₀) = ⟨q, hq⟩ * w * ⟨q, hq⟩⁻¹ :=
    Subtype.ext (by simp [MulAut.conjNormal_apply])
  rw [h1, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  have hc := (inferInstance : IsMulCommutative (↥Q₀ ⧸ frattini ↥Q₀)).is_comm.comm
  rw [hc (↑(⟨q, hq⟩ : ↥Q₀)) (↑w), mul_assoc, mul_inv_cancel, mul_one]

theorem exists_two_pow_orderOf_of_rep_eq_one_uc6 (hQ : IsPGroup 2 Q₀)
    (hchar : centralizer (Q₀ : Set Mg) ≤ Q₀) {x : Mg} (h : frattiniRep Q₀ x = 1) :
    ∃ c : ℕ, orderOf x = 2 ^ c := by
  obtain ⟨c, n, hn, hcn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  have hdvd : 2 ^ c ∣ orderOf x := ⟨n, hcn⟩
  have hord : orderOf (x ^ (2 ^ c)) = n := by
    rw [orderOf_pow_of_dvd (pow_ne_zero c two_ne_zero) hdvd, hcn]
    exact Nat.mul_div_cancel_left n (pow_pos two_pos c)
  have hy : x ^ (2 ^ c) = 1 :=
    eq_one_of_odd_of_rep_eq_one_uc6 Q₀ hQ hchar (by rw [hord]; exact hn)
      (by rw [map_pow, h, one_pow])
  rw [hy, orderOf_one] at hord
  exact ⟨c, by rw [hcn, ← hord, mul_one]⟩

theorem fixSub_frattini_eq_bot_uc6 (hQ : IsPGroup 2 Q₀) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (X : Subgroup Mg) (hX : IsPGroup p X) (hfix : Q₀ ⊓ centralizer (X : Set Mg) = ⊥) :
    fixSub (frattiniRep Q₀) X = ⊥ := by
  set F : Subgroup Mg := (frattini ↥Q₀).map Q₀.subtype with hF
  have hFQ : F ≤ Q₀ := Subgroup.map_subtype_le _
  have hFcard : ¬ p ∣ Nat.card F := by
    intro hdvd
    have h1 : Nat.card F ∣ Nat.card Q₀ := Subgroup.card_dvd_of_le hFQ
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hQ
    have : p ∣ 2 ^ n := by rw [← hn]; exact hdvd.trans h1
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).1
      (Fact.out (p := p.Prime) |>.dvd_of_dvd_pow this))
  have hFX : ∀ x ∈ X, ∀ f ∈ F, x * f * x⁻¹ ∈ F := by
    intro x _ f hf
    obtain ⟨φ, hφ, rfl⟩ := hf
    have hmap := Subgroup.characteristic_iff_map_eq.mp
      (inferInstance : (frattini ↥Q₀).Characteristic) (MulAut.conjNormal x)
    have : (MulAut.conjNormal x φ : ↥Q₀) ∈ frattini ↥Q₀ := by
      rw [← hmap]; exact ⟨φ, hφ, rfl⟩
    refine ⟨_, this, ?_⟩
    simp [MulAut.conjNormal_apply]
  have hsurj : ∀ v : Additive (↥Q₀ ⧸ frattini ↥Q₀), ∃ q : ↥Q₀,
      v = Additive.ofMul (q : ↥Q₀ ⧸ frattini ↥Q₀) := by
    intro v
    obtain ⟨q, hq⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
    exact ⟨q, by rw [hq]; rfl⟩
  have key : ∀ v ∈ fixSub (frattiniRep Q₀) X, ∃ n : ↥(Q₀ ⊓ centralizer (X : Set Mg)),
      v = Additive.ofMul ((⟨n.1, n.2.1⟩ : ↥Q₀) : ↥Q₀ ⧸ frattini ↥Q₀) := by
    intro v hv
    obtain ⟨q, rfl⟩ := hsurj v
    have hq : ∀ x ∈ X, (q : Mg)⁻¹ * (x * q * x⁻¹) ∈ F := by
      intro x hx
      have h1 := hv x hx
      rw [frattiniRep_apply_mk] at h1
      have h2 : ((MulAut.conjNormal x q : ↥Q₀) : ↥Q₀ ⧸ frattini ↥Q₀) =
          (q : ↥Q₀ ⧸ frattini ↥Q₀) := Additive.ofMul.injective h1
      have h3 := QuotientGroup.eq.1 h2.symm
      refine ⟨_, h3, ?_⟩
      simp [MulAut.conjNormal_apply]
    obtain ⟨n, hn1, hn2⟩ := exists_fixed_in_coset_uc6 X F hX hFcard hFX (q : Mg) hq
    have hnQ : n ∈ Q₀ := by
      have : (q : Mg)⁻¹ * n ∈ Q₀ := hFQ hn1
      have h2 := Q₀.mul_mem q.2 this
      simpa using h2
    have hnC : n ∈ centralizer (X : Set Mg) := by
      rw [mem_centralizer_iff]
      intro h hh
      have := hn2 h hh
      calc h * n = (h * n * h⁻¹) * h := by group
        _ = n * h := by rw [this]
    refine ⟨⟨n, hnQ, hnC⟩, ?_⟩
    congr 1
    apply QuotientGroup.eq.2
    obtain ⟨φ, hφ, hφn⟩ := hn1
    have : φ = ((⟨q, q.2⟩ : ↥Q₀))⁻¹ * ⟨n, hnQ⟩ := Subtype.ext (by simpa using hφn)
    rw [← this]; exact hφ
  classical
  choose s hs using key
  have hinj : Function.Injective
      (fun v : ↥(fixSub (frattiniRep Q₀) X) => s v.1 v.2) := by
    intro v w hvw
    have e : s v.1 v.2 = s w.1 w.2 := hvw
    apply Subtype.ext
    calc v.1 = Additive.ofMul ((⟨(s v.1 v.2).1, (s v.1 v.2).2.1⟩ : ↥Q₀) :
          ↥Q₀ ⧸ frattini ↥Q₀) := hs v.1 v.2
      _ = Additive.ofMul ((⟨(s w.1 w.2).1, (s w.1 w.2).2.1⟩ : ↥Q₀) :
          ↥Q₀ ⧸ frattini ↥Q₀) := by rw [e]
      _ = w.1 := (hs w.1 w.2).symm
  have hcard1 : Nat.card ↥(fixSub (frattiniRep Q₀) X) ≤ 1 := by
    have h2 := Nat.card_le_card_of_injective _ hinj
    rw [hfix, Subgroup.card_bot] at h2
    exact h2
  rw [eq_bot_iff]
  intro v hv
  haveI : Subsingleton ↥(fixSub (frattiniRep Q₀) X) := Finite.card_le_one_iff_subsingleton.1 hcard1
  have h0 : (⟨v, hv⟩ : ↥(fixSub (frattiniRep Q₀) X)) = 0 := Subsingleton.elim _ _
  exact (Submodule.mem_bot _).2 (congrArg Subtype.val h0)

end Module

end UC6

end CFSG.LocalAnalysis.UniquenessCase
