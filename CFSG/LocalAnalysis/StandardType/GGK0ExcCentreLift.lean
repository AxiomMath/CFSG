module

public import CFSG.LieType.CentralExt.CoprimeLift
public import CFSG.LocalAnalysis.StandardType.GGFixSub
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.StandardType.GGK0ExcCentreU

open CFSG.Open CFSG.StandardType CFSG.LieType.CentralExt

private lemma lk0xpc_orderOf_pow_p {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] {x : G}
    (hx : ∃ n : ℕ, orderOf x = p ^ n) : ∃ n : ℕ, orderOf (x ^ p) = p ^ n := by
  obtain ⟨n, hn⟩ := hx
  apply exists_orderOf_eq_pow_of_pow_eq_one (p := p) (x := x ^ p) (n := n)
  rw [← pow_mul, mul_comm p (p ^ n), pow_mul, ← hn, pow_orderOf_eq_one, one_pow]

private lemma lk0xpc_orderOf_conj {G : Type*} [Group G] (g x : G) :
    orderOf (g * x * g⁻¹) = orderOf x := by
  exact (SemiconjBy.orderOf_eq g (show SemiconjBy g x (g * x * g⁻¹) by
    unfold SemiconjBy
    group)).symm

theorem lift_elemAbelian_central
    {R L' : Type} [Group R] [Group L'] [Finite L'] {p : ℕ} (hp : p.Prime)
    (ψ : L' →* R) (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hcop : (Nat.card (Subgroup.center L')).Coprime p)
    (e : MulAut L') (phi : MulAut R) (hphi : ∀ l, phi (ψ l) = ψ (e l))
    (ER : Subgroup R) (hER : IsElemAbelian p ER)
    (hfix : ∀ y ∈ ER, phi y = y)
    (hcent : ∀ y ∈ ER, ∀ r : R, phi r = r → r * y = y * r) :
    ∃ E : Subgroup L', IsElemAbelian p E ∧ Nat.card E = Nat.card ER ∧ E ≤ ggFixSub e ∧
      (∀ z ∈ E, ∀ g ∈ ggFixSub e, g * z = z * g) ∧
      ∀ (a : MulAut L') (b : MulAut R), (∀ l, b (ψ l) = ψ (a l)) → (∀ y ∈ ER, b y = y) →
        ∀ z ∈ E, a z = z := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hC : ¬p ∣ Nat.card ψ.ker := by
    intro hpker
    exact (Nat.Prime.coprime_iff_not_dvd hp).1 hcop.symm
      (hpker.trans (Subgroup.card_dvd_of_le hker))
  have hU : IsPGroup p ER := by
    rw [IsPGroup.iff_orderOf]
    intro x
    have hx : (x : R) ^ p = 1 := hER.2 x x.2
    rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hx) with h | h
    · exact ⟨0, by rw [← Subgroup.orderOf_coe x, h, pow_zero]⟩
    · exact ⟨1, by rw [← Subgroup.orderOf_coe x, h, pow_one]⟩
  refine ⟨liftSubgroup p ψ ER, ?_, ?_, ?_, ?_, ?_⟩
  · constructor
    · exact Function.Surjective.isMulCommutative
        (f := (liftSubgroupEquiv hψ hker hC hU).symm)
        (liftSubgroupEquiv hψ hker hC hU).symm.surjective hER.1
    · intro x hx
      obtain ⟨hxER, hxord⟩ := (mem_liftSubgroup_iff hker hU).1 hx
      have hxp : ψ (x ^ p) = 1 := by
        rw [map_pow]
        exact hER.2 (ψ x) hxER
      apply eq_of_pElement hker hC (x := x ^ p) (y := 1) (?_) (lk0xpc_orderOf_pow_p hxord)
        ⟨0, by rw [orderOf_one, pow_zero]⟩
      simpa using hxp
  · exact Nat.card_congr (liftSubgroupEquiv hψ hker hC hU).toEquiv
  · intro x hx
    rw [mem_ggFixSub]
    obtain ⟨hxER, hxord⟩ := (mem_liftSubgroup_iff hker hU).1 hx
    apply eq_of_pElement hker hC (x := e x) (y := x) ?_ ?_ hxord
    · rw [← hphi x, hfix (ψ x) hxER]
    · obtain ⟨n, hn⟩ := hxord
      exact ⟨n, by rw [MulEquiv.orderOf_eq, hn]⟩
  · intro z hz g hg
    rw [mem_ggFixSub] at hg
    obtain ⟨hzER, hzord⟩ := (mem_liftSubgroup_iff hker hU).1 hz
    have hcomm : ψ g * ψ z = ψ z * ψ g :=
      hcent (ψ z) hzER (ψ g) (by rw [hphi, hg])
    have hpsi : ψ (g * z * g⁻¹) = ψ z := by
      rw [map_mul, map_mul, map_inv, hcomm]
      group
    have hconj : ∃ n : ℕ, orderOf (g * z * g⁻¹) = p ^ n := by
      obtain ⟨n, hn⟩ := hzord
      exact ⟨n, by rw [lk0xpc_orderOf_conj, hn]⟩
    have heq : g * z * g⁻¹ = z :=
      eq_of_pElement hker hC (x := g * z * g⁻¹) (y := z) hpsi hconj hzord
    calc g * z = g * z * g⁻¹ * g := by group
      _ = z * g := by rw [heq]
  · intro a b hab hb z hz
    obtain ⟨hzER, hzord⟩ := (mem_liftSubgroup_iff hker hU).1 hz
    apply eq_of_pElement hker hC (x := a z) (y := z) ?_ ?_ hzord
    · rw [← hab z, hb (ψ z) hzER]
    · obtain ⟨n, hn⟩ := hzord
      exact ⟨n, by rw [MulEquiv.orderOf_eq, hn]⟩

end CFSG.StandardType.GGK0ExcCentreU

end
