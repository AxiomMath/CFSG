module

public import CFSG.Quasithin.Background.F918L1
public import CFSG.Quasithin.Background.F918Z8Kg3
public import CFSG.Quasithin.Background.F918Z8Kg3a
public import CFSG.Quasithin.Background.F918Z8Kb

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.QuasithinUnique.Bridge
open scoped Pointwise

variable {Y : Type} [CommGroup Y] [Finite Y] {Γ Λ S : Subgroup (MulAut Y)} {V : Subgroup Y}

theorem loc_k_ge_four (h : LocCfg Γ Λ S V) (hΛ : IsPSL 3 2 1 ↥Λ)
    {k : ℕ} (hk2 : 2 ≤ k)
    (hds : DirectSumOfCopies Λ ⊤ ⊥ (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)))
      k) : 4 ≤ k := by
  by_contra hk4
  push Not at hk4
  obtain ⟨hZ, hAut⟩ := lkf_out_three hΛ
  have hcard : Nat.card ↥Λ = 168 := SBc11.card_of_isPSL_three_two hΛ
  have hgn : ∀ a ∈ Γ, ∀ y ∈ Λ, a * y * a⁻¹ ∈ Λ := fun a ha y hy =>
    (Subgroup.mem_normalizer_iff.1 (h.std.hyp.Mp_normal ha) y).1 hy
  set C : Subgroup (MulAut Y) := Γ ⊓ Subgroup.centralizer (Λ : Set (MulAut Y))
  have hCΓ : C ≤ Γ := inf_le_left
  have hCne : C ≠ ⊥ := by
    intro hCbot
    have hmem : ∀ g ∈ Γ, g ∈ Λ ⊔ S := by
      intro g hg
      obtain ⟨c, hcΓ, hcc, x, hx, hgx⟩ := loc_mul_cent h hZ hAut g hg
      have hc1 : c = 1 := by
        have hcC : c ∈ C := ⟨hcΓ, Subgroup.mem_centralizer_iff.2 fun l hl => (hcc l hl).symm⟩
        rw [hCbot, Subgroup.mem_bot] at hcC
        exact hcC
      rw [hgx, hc1, one_mul]
      exact hx
    have hLs : Λ ≤ stabSub V := le_stabSub_of_forall_mem (loc_irr_data h).1
    have hSs : S ≤ stabSub V := le_stabSub_of_forall_mem (loc_S_inv h)
    have hVtop : V = ⊤ := by
      refine eq_top_iff.2 ?_
      rw [← h.std.hyp.gen]
      refine iSup₂_le fun g hg => ?_
      rw [map_eq_of_mem_stabSub ((sup_le hLs hSs) (hmem g hg))]
    exact h.ne hVtop
  have hprimes : ∀ p : ℕ, p.Prime → p ∣ Nat.card ↥C → p = 2 := by
    intro p hp hpC
    by_contra hp2
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥C) p hpC
    obtain ⟨ψ, hψ⟩ := lkf_embed hds C fun c hc l hl =>
      (Subgroup.mem_centralizer_iff.1 hc.2 l hl).symm
    have h1 : p ∣ Nat.card (Matrix.GeneralLinearGroup (Fin k) (ZMod 2)) := by
      rw [← hx, ← orderOf_injective ψ hψ x]
      exact orderOf_dvd_natCard _
    have h2 : p ∣ Nat.card ↥Λ := hcard ▸ h1.trans (lkf_card_GL_dvd k hk2 hk4)
    have hxΛ : ∀ l ∈ Λ, (x : MulAut Y) * l = l * (x : MulAut Y) := fun l hl =>
      (Subgroup.mem_centralizer_iff.1 x.2.2 l hl).symm
    have hxp : (x : MulAut Y) ^ (p ^ 1) = 1 := by
      rw [pow_one, ← Subgroup.coe_pow, ← hx, pow_orderOf_eq_one]
      rfl
    have hx1 : (x : MulAut Y) = 1 := h.hK _ x.2.1 hxΛ p hp hp2 h2 ⟨1, hxp⟩
    have : orderOf x = 1 := by
      rw [orderOf_eq_one_iff]
      exact Subtype.ext hx1
    exact hp.one_lt.ne' (hx ▸ this)
  exact hCne (lkf_eq_bot_of_primes hCΓ (lkf_cent_normalizes hgn) h.std.hyp.pCoreOf_eq_bot hprimes)

end CFSG.Quasithin
