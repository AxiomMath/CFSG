module

public import CFSG.Quasithin.H13.NQCoreP134Normal

public section

namespace CFSG.Quasithin.Vol2.Ch11.OE6

open CFSG.Open CFSG.Quasithin

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem le_ker_of_isCyclic_map {M : Type*} [Group M] {p : ℕ} [hp : Fact p.Prime]
    {P N : Subgroup Γ} (hPp : IsPGroup p P) (hexp : ∀ x ∈ P, x ^ p = 1)
    (hc2 : p ^ 2 ≤ Nat.card P) (hNP : N ≤ Subgroup.normalizer (P : Set Γ))
    (hirr : ∀ U : Subgroup Γ, ⁅P, P⁆ ≤ U → U ≤ P → N ≤ Subgroup.normalizer (U : Set Γ) →
      U = ⁅P, P⁆ ∨ U = P)
    (φ : Γ →* M) (hN : N ≤ Subgroup.normalizer (φ.ker : Set Γ)) (hcyc : IsCyclic ↥(P.map φ)) :
    P ≤ φ.ker := by
  rcases H13.NQCore.inf_le_or_le_of_irreducible hPp hexp hNP hirr hN with h | h
  · exfalso
    obtain ⟨⟨y, hy⟩, hgen⟩ := hcyc.exists_generator
    obtain ⟨g, hgP, rfl⟩ := hy
    have hcP : ⁅P, P⁆ ≤ P := Subgroup.commutator_le.mpr fun a ha b hb =>
      P.mul_mem (P.mul_mem (P.mul_mem ha hb) (P.inv_mem ha)) (P.inv_mem hb)
    have hle : P ≤ Subgroup.zpowers g ⊔ ⁅P, P⁆ := by
      intro x hx
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hgen ⟨φ x, ⟨x, hx, rfl⟩⟩)
      have hk' : φ (g ^ k) = φ x := by
        rw [map_zpow]
        exact congrArg Subtype.val hk
      have hmem : x * (g ^ k)⁻¹ ∈ P ⊓ φ.ker :=
        Subgroup.mem_inf.mpr ⟨P.mul_mem hx (P.inv_mem (P.zpow_mem hgP k)),
          MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, hk', mul_inv_cancel])⟩
      have e : x = (x * (g ^ k)⁻¹) * g ^ k := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (h hmem))
        (Subgroup.mem_sup_left (Subgroup.zpow_mem_zpowers g k))
    have hgP' : Subgroup.zpowers g ≤ P := Subgroup.zpowers_le.mpr hgP
    have hΦ := Ch1Sec3.frattiniIn_eq_commutator hPp hexp
    have heq : Subgroup.zpowers g = P := Ch1Sec3.eq_of_sup_frattiniIn_eq hgP'
      (le_antisymm (sup_le hgP' (hΦ ▸ hcP)) (hΦ ▸ hle))
    have hcard : Nat.card P ≤ p := by
      rw [← heq, Nat.card_zpowers]
      exact Nat.le_of_dvd hp.out.pos (orderOf_dvd_of_pow_eq_one (hexp g hgP))
    have hp2 : p < p ^ 2 := by
      have := hp.out.two_le
      nlinarith
    omega
  · exact h

omit [Finite Γ] in
theorem mem_ker_conjNormal {K : Subgroup Γ} [K.Normal] {x : Γ} :
    x ∈ (MulAut.conjNormal : Γ →* MulAut ↥K).ker ↔ x ∈ Subgroup.centralizer (K : Set Γ) := by
  rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
  constructor
  · intro h k hk
    have h1 := congrArg (fun α : MulAut ↥K => ((α ⟨k, hk⟩ : ↥K) : Γ)) h
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
    calc k * x = (x * k * x⁻¹) * x := by rw [h1]
      _ = x * k := by group
  · intro h
    refine MulEquiv.ext fun k => Subtype.ext ?_
    rw [MulAut.conjNormal_apply, MulAut.one_apply, ← h k k.2, mul_inv_cancel_right]

theorem le_centralizer_of_isCyclic {p : ℕ} [Fact p.Prime] {P N K : Subgroup Γ} [K.Normal]
    (hPp : IsPGroup p P) (hexp : ∀ x ∈ P, x ^ p = 1) (hc2 : p ^ 2 ≤ Nat.card P)
    (hNP : N ≤ Subgroup.normalizer (P : Set Γ))
    (hirr : ∀ U : Subgroup Γ, ⁅P, P⁆ ≤ U → U ≤ P → N ≤ Subgroup.normalizer (U : Set Γ) →
      U = ⁅P, P⁆ ∨ U = P)
    (hcyc : IsCyclic ↥(P.map (MulAut.conjNormal : Γ →* MulAut ↥K))) :
    P ≤ Subgroup.centralizer (K : Set Γ) := by
  have hN : N ≤ Subgroup.normalizer
      ((MulAut.conjNormal : Γ →* MulAut ↥K).ker : Set Γ) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr (MonoidHom.normal_ker _)]
    exact le_top
  intro x hx
  exact mem_ker_conjNormal.mp (le_ker_of_isCyclic_map hPp hexp hc2 hNP hirr _ hN hcyc hx)

end CFSG.Quasithin.Vol2.Ch11.OE6
