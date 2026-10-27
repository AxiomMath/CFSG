module

public import CFSG.RankThree.PartTwo.Sec11.Item116R2ZCent
public import CFSG.RankThree.PartTwo.Sec11.Item116R2ZCyc

public section

open Subgroup

namespace CFSG.RankThree.PartTwo.Sec11

theorem exists_z_of_quotient {X : Type} [Group X] [Finite X] (N : Subgroup X) [N.Normal]
    (hN : ¬ 3 ∣ Nat.card N) (φ : MulAut X) (hφ3 : φ ^ 3 = 1) (hφN : ∀ n ∈ N, φ n ∈ N)
    {d : X} (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1) (hφd : φ d = d)
    (hfact : ∀ Pb : Subgroup (X ⧸ N),
      Pb ≤ Subgroup.centralizer ({(QuotientGroup.mk d : X ⧸ N)} : Set (X ⧸ N)) →
      Nat.card Pb = 3 ^ (Nat.card (Subgroup.centralizer ({(QuotientGroup.mk d : X ⧸ N)} : Set (X ⧸ N)))).factorization 3 →
        IsCyclic ↥Pb ∧ 9 ≤ Nat.card Pb ∧
          ∃ y ∈ Pb, ∃ x : X, (QuotientGroup.mk x : X ⧸ N) = y ∧ (QuotientGroup.mk (φ x) : X ⧸ N) ≠ y) :
    ∃ (z : X) (v k : ℕ), 2 ≤ v ∧ orderOf z = 3 ^ v ∧ z ∈ Subgroup.centralizer ({d} : Set X) ∧
      z ^ 3 ^ (v - 1) = d ∧ φ z = z ^ k ∧ 3 ^ (v - 1) ∣ k - 1 ∧ ¬ 3 ^ v ∣ k - 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hPle, hPcard, hPφ⟩ := exists_invariant_sylow_centralizer φ hφ3 hφd
  obtain ⟨hcardbar, hPN⟩ := card_map_mk_sylow N hN hd3 P hPle hPcard
  have hPmap_le : P.map (QuotientGroup.mk' N) ≤
      Subgroup.centralizer ({(QuotientGroup.mk d : X ⧸ N)} : Set (X ⧸ N)) := by
    rw [← map_mk_centralizer_eq N hN hd3]
    exact Subgroup.map_mono hPle
  obtain ⟨hcyc, h9, y, hy, x, hxy, hnot⟩ := hfact _ hPmap_le hcardbar
  have hinj : Function.Injective ((QuotientGroup.mk' N).subgroupMap P) := by
    intro a b hab
    have h1 : (QuotientGroup.mk' N) (a : X) = (QuotientGroup.mk' N) (b : X) :=
      congrArg Subtype.val hab
    have h2 : ((a : X)⁻¹ * (b : X)) ∈ N := by
      rw [← QuotientGroup.eq]
      exact h1
    have h3 : ((a : X)⁻¹ * (b : X)) ∈ P ⊓ N := ⟨P.mul_mem (P.inv_mem a.2) b.2, h2⟩
    rw [hPN, Subgroup.mem_bot] at h3
    exact Subtype.ext (inv_mul_eq_one.mp h3)
  let e : P ≃* P.map (QuotientGroup.mk' N) :=
    MulEquiv.ofBijective ((QuotientGroup.mk' N).subgroupMap P)
      ⟨hinj, (QuotientGroup.mk' N).subgroupMap_surjective P⟩
  haveI hPcyc : IsCyclic P := by
    haveI := hcyc
    exact isCyclic_of_injective e.toMonoidHom e.injective
  have hcardP : Nat.card P = Nat.card (P.map (QuotientGroup.mk' N)) := Nat.card_congr e.toEquiv
  obtain ⟨v, hv⟩ : ∃ v, Nat.card P = 3 ^ v :=
    ⟨_, hPcard⟩
  have hv2 : 2 ≤ v := by
    by_contra hlt
    push Not at hlt
    have : 3 ^ v ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hdP : d ∈ P := mem_sylow_centralizer_of_pow_three hd3 P hPle hPcard
  have hmove : ∃ p ∈ P, φ p ≠ p := by
    obtain ⟨p, hp, hpy⟩ := Subgroup.mem_map.mp hy
    refine ⟨p, hp, fun hφp => ?_⟩
    apply hnot
    have hn : (p⁻¹ * x) ∈ N := by
      rw [← QuotientGroup.eq]
      exact hpy.trans hxy.symm
    have hφx : (QuotientGroup.mk (φ x) : X ⧸ N) = QuotientGroup.mk (φ p) := by
      rw [QuotientGroup.eq]
      have h1 : (φ x)⁻¹ * φ p = φ ((p⁻¹ * x)⁻¹) := by
        rw [mul_inv_rev, inv_inv, map_mul, map_inv]
      rw [h1]
      exact hφN _ (N.inv_mem hn)
    rw [hφx, hφp, ← hpy]
    rfl
  obtain ⟨z, k, hzP, hz, hzd, hzφ, hk1, hk2⟩ :=
    exists_z_of_cyclic φ hφ3 P hv2 hv hPφ hdP hd3 hd1 hmove
  exact ⟨z, v, k, hv2, hz, hPle hzP, hzd, hzφ, hk1, hk2⟩

end CFSG.RankThree.PartTwo.Sec11
