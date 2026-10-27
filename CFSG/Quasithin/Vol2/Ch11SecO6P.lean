module

public import CFSG.Quasithin.Vol2.Ch11SecO6B
public import CFSG.Quasithin.Vol2.Ch11SecO6G
public import CFSG.Quasithin.Vol2.Ch11SecO6H
public import CFSG.Quasithin.Vol2.Ch11SecO6N
public import CFSG.Quasithin.Vol2.Ch11SecO6J
public import CFSG.Quasithin.Vol2.Ch11SecO6M

public section

namespace CFSG.Quasithin.Vol2.Ch11.O6

open CFSG.Quasithin
open scoped MatrixGroups

variable {X : Type} [Group X] [Finite X]

theorem out2Closed_of_case1 (hD : Case1Data X)
    (hX : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = ⊤)
    (hshape : ∀ r : ℕ, r.Prime → r ∣ Nat.card (CFSG.fittingSubgroup X) →
      IsPOnePlusTwo r ↥(CFSG.pCore r X) ∨
        ((∀ d ∈ CFSG.pCore r X, ∀ e ∈ CFSG.pCore r X, d * e = e * d) ∧
          ∀ u ∈ CFSG.pCore r X, u ∉ frattiniIn (CFSG.pCore r X) → ∀ b : ℤ, u ^ b = 1 →
            ∀ e ∈ CFSG.pCore r X, e ^ b = 1))
    (hinv : ∀ r : ℕ, ∀ _ : Fact r.Prime, r ∣ Nat.card (CFSG.fittingSubgroup X) → ∀ s : X,
      s ∉ CFSG.fittingSubgroup X → s ^ 2 ∈ CFSG.fittingSubgroup X →
      IsPGroup 2 (Subgroup.zpowers s) → ActsScalar r (MulAut.conj s) (r - 1)) :
    SecE.Out2Closed X := by
  obtain ⟨hCF, hprimes, q, hq, hq5, ψ, hψ, hker⟩ := hD.struct
  have : Fact q.Prime := ⟨hq⟩
  set F := CFSG.fittingSubgroup X with hFdef
  have hFodd : Odd (Nat.card F) := by
    rw [Nat.odd_iff]
    by_contra h
    have := hprimes 2 Nat.prime_two (Nat.dvd_of_mod_eq_zero (by omega))
    omega
  have hFchar : ∀ α : MulAut X, F.map α.toMonoidHom = F := fun α =>
    Subgroup.characteristic_iff_map_eq.mp inferInstance α
  have hFα : ∀ α : MulAut X, ∀ f ∈ F, α f ∈ F := fun α f hf => by
    rw [← hFchar α]
    exact Subgroup.mem_map_of_mem _ hf
  let InN : MulAut X → Prop := fun ν => ∀ y : X, y⁻¹ * ν y ∈ F
  have hNmul : ∀ ν₁ ν₂, InN ν₁ → InN ν₂ → InN (ν₁ * ν₂) := by
    intro ν₁ ν₂ h₁ h₂ y
    have e : y⁻¹ * (ν₁ * ν₂) y = (y⁻¹ * ν₂ y) * ((ν₂ y)⁻¹ * ν₁ (ν₂ y)) := by
      rw [MulAut.mul_apply]
      group
    rw [e]
    exact Subgroup.mul_mem _ (h₂ y) (h₁ (ν₂ y))
  have hNinv : ∀ ν, InN ν → InN ν⁻¹ := by
    intro ν h y
    have e : y⁻¹ * ν⁻¹ y = ((ν⁻¹ y)⁻¹ * ν (ν⁻¹ y))⁻¹ := by
      rw [MulAut.apply_inv_self]
      group
    rw [e]
    exact Subgroup.inv_mem _ (h _)
  have hNconj : ∀ α ν, InN ν → InN (α * ν * α⁻¹) := by
    intro α ν h y
    have e : y⁻¹ * (α * ν * α⁻¹) y = α ((α⁻¹ y)⁻¹ * ν (α⁻¹ y)) := by
      simp only [MulAut.mul_apply, map_mul, map_inv, MulAut.apply_inv_self]
    rw [e]
    exact hFα α _ (h _)
  obtain ⟨s, hs2, hsF, hsc⟩ := exists_involution (q := q) (by omega) hFodd hψ hker
  have hs2F : s ^ 2 ∈ F := by
    rw [hs2]
    exact one_mem _
  have hsP : IsPGroup 2 (Subgroup.zpowers s) := by
    rintro ⟨g, hg⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨1, Subtype.ext ?_⟩
    change (s ^ i) ^ 2 ^ 1 = 1
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hs2, one_zpow]
  have hplus : ∀ z ∈ F, (∀ f ∈ F, z * f = f * z) → z * s = s * z → ∀ y : X,
      y * z * y⁻¹ = z := by
    intro z hzF hzc hzs y
    refine conj_eq_of_forall_pCore (fun r hr hrF w hw hwc hws y' => ?_) hzF hzc hzs y
    have : Fact r.Prime := ⟨hr⟩
    rcases hshape r hr hrF with hE | ⟨hab, -⟩
    · exact conj_eq_of_mem_center hX hE hw
        (fun e he => hwc e (CFSG.pCore_le_fitting X r he)) y'
    · have hr2 : r ≠ 2 := by
        have := hprimes r hr hrF
        omega
      have hinvr := inv_of_actsScalar r hr2 hab hs2 (hinv r ⟨hr⟩ hrF s hsF hs2F hsP) w hw
      have h1 : s * w * s⁻¹ = w := by
        rw [← hws]
        group
      have hww : w * w = 1 := by
        calc w * w = w * w⁻¹ := by rw [← h1.symm.trans hinvr]
          _ = 1 := mul_inv_cancel w
      have hord : orderOf w ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hww)
      have hodd : Odd (orderOf w) :=
        hFodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard F (CFSG.pCore_le_fitting X r hw))
      have hw1 : w = 1 := by
        rcases (Nat.dvd_prime Nat.prime_two).mp hord with h | h
        · exact orderOf_eq_one_iff.mp h
        · rw [h] at hodd
          exact absurd hodd (by decide)
      rw [hw1]
      group
  have hstar : ∀ ν : MulAut X, InN ν → ∀ α : MulAut X,
      ν * α * ν⁻¹ * α⁻¹ ∈ (MulAut.conj : X →* MulAut X).range := by
    intro ν hν α
    set β := ν * α * ν⁻¹ * α⁻¹ with hβ
    have hβN : InN β := by
      have e : β = ν * (α * ν⁻¹ * α⁻¹) := by
        rw [hβ]
        group
      rw [e]
      exact hNmul _ _ hν (hNconj α _ (hNinv ν hν))
    have hloc : ∀ r : ℕ, r.Prime →
        ∃ f ∈ CFSG.pCore r X, ∀ d ∈ CFSG.pCore r X, β d = f * d * f⁻¹ := by
      intro r hr
      have : Fact r.Prime := ⟨hr⟩
      by_cases hrF : r ∣ Nat.card F
      · have hna := exists_not_triv r hD hrF (Or.inl hX)
        have hV := hD.rank r hr hrF
        obtain ⟨k, hk⟩ := actsScalar_of_comm r hV (fun f hf => fitting_acts_triv r hf) hna hν
        rcases hshape r hr hrF with hE | ⟨hab, hHC⟩
        · have h1 := actsScalar_comm r hk α
          exact exists_conj_of_pOnePlusTwo hE β fun d hd => by
            have := h1 d hd
            rwa [pow_one] at this
        · obtain ⟨a, ha⟩ := exists_zpow_of_comm r hV hab hHC hna
            (fun x d hd => conj_comm_of_fitting r hab hν x hd)
          exact ⟨1, one_mem _, fun d hd => by rw [comm_eq_of_zpow r ha α hd]; group⟩
      · refine ⟨1, one_mem _, fun d hd => ?_⟩
        have hd1 : d = 1 := by
          obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := r) (G := X) ⟨d, hd⟩
          have hdk : d ^ r ^ k = 1 := congrArg Subtype.val hk
          have h1 : orderOf d ∣ r ^ k := orderOf_dvd_of_pow_eq_one hdk
          have h2 : orderOf d ∣ Nat.card F :=
            Subgroup.orderOf_dvd_natCard F (CFSG.pCore_le_fitting X r hd)
          obtain ⟨j, -, hjd⟩ := (Nat.dvd_prime_pow hr).mp h1
          rcases j with _ | j
          · rw [pow_zero] at hjd
            exact orderOf_eq_one_iff.mp hjd
          · exact absurd ((dvd_pow_self r (Nat.succ_ne_zero j)).trans (hjd ▸ h2)) hrF
        rw [hd1, map_one]
        group
    obtain ⟨f, hfF, hf⟩ := exists_conj_fitting β hloc
    set τ := (MulAut.conj f)⁻¹ * β with hτ
    have hτa : ∀ y, τ y = f⁻¹ * β y * f := fun y => by
      rw [hτ, MulAut.mul_apply, MulAut.conj_inv_apply]
    have hτF : ∀ d ∈ F, τ d = d := fun d hd => by
      rw [hτa, hf d hd]
      group
    have hτN : InN τ := fun y => by
      rw [hτa]
      have e : y⁻¹ * (f⁻¹ * β y * f) = (y⁻¹ * f⁻¹ * y) * (y⁻¹ * β y) * f := by group
      rw [e]
      refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ (hβN y)) hfF
      have := Subgroup.Normal.conj_mem inferInstance _ (Subgroup.inv_mem _ hfF) y⁻¹
      rwa [inv_inv] at this
    have hτI := mem_range_conj_of_trivial hX hFodd hs2 hsc hplus hτF hτN
    have e : β = MulAut.conj f * τ := by rw [hτ, mul_inv_cancel_left]
    rw [e]
    exact Subgroup.mul_mem _ ⟨f, rfl⟩ hτI
  have hSL : ∀ a b : CFSG.ComponentClassification.OuterAutomorphisms.Outer SL(2, ZMod q),
      a * b = b * a := outer_sl2_mul_comm (ZMod q) (by rw [Nat.card_zmod]; omega)
  have hFk : ∀ α : MulAut X, ψ.ker.map α.toMonoidHom = ψ.ker := fun α => by
    rw [hker]
    exact hFchar α
  have hInn : ((MulAut.conj : X →* MulAut X).range).Normal :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_normal X
  refine out2Closed_of_comm_comm fun σ τ ρ => ?_
  obtain ⟨x, hx⟩ := exists_conj_comm ψ hFk hψ hSL σ τ
  set c := σ * τ * σ⁻¹ * τ⁻¹ with hc
  set ν := (MulAut.conj x)⁻¹ * c with hν
  have hνN : InN ν := fun y => by
    have h1 : ψ (y⁻¹ * ν y) = 1 := by
      rw [hν, MulAut.mul_apply, MulAut.conj_inv_apply, map_mul, map_mul, map_mul, map_inv,
        map_inv, hx y, map_mul, map_mul, map_inv]
      group
    rw [← hker]
    exact h1
  have hcν : c = MulAut.conj x * ν := by rw [hν, mul_inv_cancel_left]
  have e : c * ρ * c⁻¹ * ρ⁻¹ = MulAut.conj x * (ν * ρ * ν⁻¹ * ρ⁻¹) *
      (ρ * (MulAut.conj x)⁻¹ * ρ⁻¹) := by
    rw [hcν]
    group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ ⟨x, rfl⟩ (hstar ν hνN ρ))
    (hInn.conj_mem _ (Subgroup.inv_mem _ ⟨x, rfl⟩) ρ)

end CFSG.Quasithin.Vol2.Ch11.O6
