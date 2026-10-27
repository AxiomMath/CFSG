module

public import CFSG.Permutation.UnitaryThreeRecognition.AbelianQFiveAction
public import CFSG.Permutation.UnitaryThreeRecognition.AbelianQFiveModel
public import CFSG.Permutation.UnitaryThreeRecognition.SMapMoufang

public section

namespace CFSG.UnitaryThreeRecognition

open MulAction

namespace StdHyp

variable {G Ω : Type*} [Group G] [MulAction G Ω] {Q : Subgroup G} {a b : Ω} {j s : G}
  {p f : ℕ}

theorem exists_validTau_of_abelian (S : StdHyp G Q a b j s p f 3) [Finite G] [Finite Ω]
    (h5 : p ^ f = 5) (hQab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x)
    (hcyc : IsCyclic (pairStab G a b)) :
    ∃ (ν α β : ZMod 5) (m : ℕ) (τ : AbelianQFive.M → AbelianQFive.M), ν * ν = -1 ∧
      ((AbelianQFive.gen ν α β)^[4] (0, 1, 0) = (0, -1, 0) ∧
        (AbelianQFive.gen ν α β)^[4] (0, 0, 1) = (0, 0, -1)) ∧
      (m = 3 ∨ m = 7) ∧ AbelianQFive.ValidTau ν α β m τ := by
  classical
  obtain ⟨t, ht, hot, hgen⟩ := S.exists_torus_gen h5 hcyc
  obtain ⟨m, hm, hstm⟩ := S.exists_sigma_exponent h5 ht hot hgen
  obtain ⟨z₀, hz₀, hz₀1⟩ := S.exists_centQ_ne_one
  have hV : 1 < Nat.card (AbelianQ.invSub Q j hQab) := by
    rw [S.card_invSub_eq h5 hQab]; norm_num
  have : Nontrivial (AbelianQ.invSub Q j hQab) := Finite.one_lt_card_iff_nontrivial.mp hV
  obtain ⟨⟨v₀, hv₀⟩, hv₀1⟩ := exists_ne (1 : AbelianQ.invSub Q j hQab)
  have hv₀1' : v₀ ≠ 1 := fun e => hv₀1 (Subtype.ext e)
  obtain ⟨ν, α, β, hgf⟩ := S.exists_gen_formula h5 hQab ht hot hz₀ hz₀1 hv₀ hv₀1'
  set ψ := coord5 z₀ v₀ (t * v₀ * t⁻¹) with hψdef
  have hψmem : ∀ u, ψ u ∈ Q := S.coord5_mem hQab ht hz₀ hv₀
  have hψadd : ∀ u u', ψ (u + u') = ψ u * ψ u' := S.coord5_add' h5 hQab ht hz₀ hv₀
  have hψneg : ∀ u, ψ (-u) = (ψ u)⁻¹ := S.coord5_neg' h5 hQab ht hz₀ hv₀
  have hψinj : Function.Injective ψ := S.coord5_injective h5 hQab ht hot hz₀ hz₀1 hv₀ hv₀1'
  have hψsurj : ∀ {x : G}, x ∈ Q → ∃ u, ψ u = x := fun hx =>
    S.coord5_surjective h5 hQab ht hot hz₀ hz₀1 hv₀ hv₀1' hx
  have hψ0 : ψ 0 = 1 := coord5_zero
  have hψone : ∀ u, ψ u = 1 ↔ u = 0 := fun u =>
    ⟨fun h => S.coord5_eq_one h5 hQab ht hot hz₀ hz₀1 hv₀ hv₀1' h,
      fun h => by rw [h]; exact hψ0⟩
  have hψZ : ∀ u, ψ u ∈ centQ Q j ↔ u.2 = 0 := S.coord5_mem_centQ_iff h5 hQab ht hot hz₀ hv₀ hv₀1'
  have hconj : ∀ (k : ℕ) (u : AbelianQFive.M), t ^ k * ψ u * (t ^ k)⁻¹ =
      ψ ((AbelianQFive.gen ν α β)^[k] u) := fun k u => conj_pow_coord5 hgf k u
  have hex : ∀ u : AbelianQFive.M, u ≠ 0 → ∃ w, ψ w = sLeft Q a b s (ψ u) := fun u hu =>
    hψsurj (S.root.sLeft_mem S.hb S.hsa S.hs2 (hψmem u) (fun e => hu ((hψone u).mp e)))
  let τ : AbelianQFive.M → AbelianQFive.M := fun u =>
    if hu : u = 0 then 0 else Classical.choose (hex u hu)
  have hτ0 : τ 0 = 0 := by simp [τ]
  have hτψ : ∀ u, u ≠ 0 → ψ (τ u) = sLeft Q a b s (ψ u) := by
    intro u hu
    simp only [τ, dite_eq_right hu]
    exact Classical.choose_spec (hex u hu)
  have hψu1 : ∀ u, u ≠ 0 → ψ u ≠ 1 := fun u hu e => hu ((hψone u).mp e)
  have hτne : ∀ u, u ≠ 0 → τ u ≠ 0 := by
    intro u hu e
    have := hτψ u hu
    rw [e, hψ0] at this
    exact S.root.sLeft_ne_one S.hb S.hsa S.hs2 (hψmem u) (hψu1 u hu) this.symm
  refine ⟨ν, α, β, m, τ, S.nu_mul_nu h5 hQab ht hot hz₀ hz₀1 hv₀ hv₀1' hgf,
    S.gen5_four h5 hQab ht hot hz₀ hz₀1 hv₀ hv₀1' hgf, hm, ?_⟩
  refine ⟨hτ0, hτne, ?_, ?_, ?_, ?_⟩
  ·
    intro u hu
    apply hψinj
    rw [hτψ _ (hτne u hu), hτψ u hu]
    exact S.root.sLeft_sLeft S.hb S.hsa S.hs2 (hψmem u) (hψu1 u hu)
  ·
    intro u hu
    have hgu : AbelianQFive.gen ν α β u ≠ 0 := by
      intro e
      apply hψu1 u hu
      have h1 := hgf u
      change t * ψ u * t⁻¹ = ψ (gen5 ν α β u) at h1
      rw [show gen5 ν α β u = AbelianQFive.gen ν α β u from rfl, e, hψ0] at h1
      calc ψ u = t⁻¹ * (t * ψ u * t⁻¹) * t := by group
        _ = 1 := by rw [h1]; group
    apply hψinj
    rw [hτψ _ hgu]
    have h1 : ψ (AbelianQFive.gen ν α β u) = t * ψ u * t⁻¹ := (hgf u).symm
    rw [h1]
    obtain ⟨hL, -, -⟩ := S.root.sFactors_conj S.hb S.hsa S.hs2 (hψmem u) (hψu1 u hu) ht
    rw [hL, hstm, hτψ u hu |>.symm]
    exact hconj m (τ u)
  ·
    intro u hu hu2
    have h1 : ψ u ∈ centQ Q j := (hψZ u).mpr hu2
    have h2 := S.root.sLeft_mem_centQ S.hb S.hsa S.hs2 S.hj S.hsj h1 (hψu1 u hu)
    rw [← hτψ u hu] at h2
    exact (hψZ (τ u)).mp h2
  ·
    intro u hu
    have hτT := S.root.sTor_mem S.hb S.hsa S.hs2 (hψmem u) (hψu1 u hu)
    obtain ⟨k, -, hk⟩ := hgen _ hτT
    refine ⟨k, fun w hw huw hwu => ?_⟩
    apply hψinj
    have hnu : -u ≠ 0 := neg_ne_zero.mpr hu
    have hR : sRight Q a b s (ψ u) = ψ (-τ (-u)) := by
      have := (S.root.sFactors_inv S.hb S.hsa S.hs2 (Q.inv_mem (hψmem u))
        (inv_ne_one.mpr (hψu1 u hu))).2.2
      rw [inv_inv] at this
      rw [this, hψneg (τ (-u)), ← hψneg u, ← hτψ _ hnu]
    have hM := S.root.sLeft_mul_sLeft S.hb S.hsa S.hs2 (hψmem u) (hψu1 u hu) (hψmem w)
      (hψu1 w hw)
      (by rw [← hτψ w hw, ← hψadd]; exact hψu1 _ huw)
      (by rw [hR, ← hψadd, ← sub_eq_neg_add]; exact hψu1 _ hwu)
    rw [hτψ _ huw, hψadd, hτψ w hw, hM, hψadd, hτψ u hu, hk, hR, ← hψadd,
      show -τ (-u) + w = w - τ (-u) by abel, ← hτψ _ hwu]
    congr 1
    exact hconj k _

end StdHyp

end CFSG.UnitaryThreeRecognition
