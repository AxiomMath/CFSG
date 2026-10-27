module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K36Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G] {M E : Subgroup G} {p : ℕ}

namespace Hyp36

variable (h : Hyp36 G M p E)
include h

theorem le_of_relIndex_pow {K C : Subgroup G} (hEK : E ≤ Subgroup.normalizer (K : Set G))
    (hCM : C ≤ M) {n : ℕ} (hC : C.relIndex K = p ^ n) : K ≤ M := by
  classical
  haveI : Fact p.Prime := ⟨h.prime⟩
  set M₀ : G ⧸ M := ((1 : G) : G ⧸ M) with hM₀
  have hfix1 : ∀ e ∈ M, e • M₀ = M₀ := by
    intro e he
    rw [hM₀, MulAction.Quotient.smul_coe, QuotientGroup.eq]
    simpa using he
  let O : SubMulAction E (G ⧸ M) :=
    { carrier := MulAction.orbit K M₀
      smul_mem' := by
        intro e c hc
        obtain ⟨y, rfl⟩ := hc
        refine ⟨⟨(e : G) * y * (e : G)⁻¹, ?_⟩, ?_⟩
        · exact (Subgroup.mem_normalizer_iff.1 (hEK e.2) y).1 y.2
        · show ((e : G) * y * (e : G)⁻¹) • M₀ = (e : G) • ((y : G) • M₀)
          calc ((e : G) * y * (e : G)⁻¹) • M₀ = ((e : G) * y) • ((e : G)⁻¹ • M₀) := mul_smul _ _ _
            _ = ((e : G) * y) • M₀ := by rw [hfix1 _ (inv_mem (h.E_le e.2))]
            _ = (e : G) • ((y : G) • M₀) := mul_smul _ _ _ }
  have hmod : Nat.card O ≡ Nat.card (MulAction.fixedPoints E O) [MOD p] :=
    h.isPGroup.card_modEq_card_fixedPoints O
  have hfp : Nat.card (MulAction.fixedPoints E O) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    have hb0 : M₀ ∈ O := MulAction.mem_orbit_self M₀
    have hkey : ∀ b : MulAction.fixedPoints E O, (b : O).1 = M₀ := by
      intro b
      obtain ⟨y, hy⟩ := (b : O).2
      have hfixb : ∀ e : E, (e : G) • (b : O).1 = (b : O).1 := fun e => by
        have := b.2 e
        exact congrArg Subtype.val this
      have hyM : (y : G) ∈ M := by
        refine h.mem_of_conj_le fun x hx => ?_
        have h1 := hfixb ⟨x⁻¹, inv_mem hx⟩
        rw [← hy] at h1
        change ((x⁻¹ : G) • ((y : G) • M₀)) = (y : G) • M₀ at h1
        rw [hM₀, MulAction.Quotient.smul_coe, MulAction.Quotient.smul_coe, QuotientGroup.eq] at h1
        simpa [mul_assoc] using h1
      rw [← hy]
      exact hfix1 _ hyM |> fun _ => by
        change ((y : G) • M₀) = M₀
        rw [hM₀, MulAction.Quotient.smul_coe, QuotientGroup.eq]
        simpa using hyM
    refine ⟨⟨fun b b' => Subtype.ext (Subtype.ext ((hkey b).trans (hkey b').symm))⟩,
      ⟨⟨⟨M₀, hb0⟩, fun e => Subtype.ext (hfix1 _ (h.E_le e.2))⟩⟩⟩
  have hstab : MulAction.stabilizer K M₀ = M.subgroupOf K := by
    ext k
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
    show (k : G) • M₀ = M₀ ↔ (k : G) ∈ M
    rw [hM₀, MulAction.Quotient.smul_coe, QuotientGroup.eq]
    simp
  have hcard : Nat.card O = M.relIndex K := by
    have h1 := MulAction.index_stabilizer K M₀
    rw [hstab] at h1
    change (M.subgroupOf K).index = _ at h1
    change Nat.card (MulAction.orbit K M₀) = _
    rw [Nat.card_coe_set_eq, ← h1]
    rfl
  rw [hcard, hfp] at hmod
  have hdvd : M.relIndex K ∣ p ^ n := hC ▸ Subgroup.relIndex_dvd_of_le_left K hCM
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow h.prime).1 hdvd
  rcases Nat.eq_zero_or_pos i with rfl | hipos
  · exact Subgroup.relIndex_eq_one.1 (by simpa using hi)
  · exfalso
    have h0 : M.relIndex K ≡ 0 [MOD p] :=
      (Nat.modEq_zero_iff_dvd).2 (hi ▸ dvd_pow_self p hipos.ne')
    have h01 : 0 ≡ 1 [MOD p] := h0.symm.trans hmod
    have := (Nat.modEq_zero_iff_dvd).1 h01.symm
    exact h.prime.one_lt.ne' (Nat.dvd_one.1 this)

end Hyp36

end CFSG.LocalAnalysis.UniquenessCase.UCK
