module

public import CFSG.Quasithin.Vol2.KGNatSL2Borel
public import CFSG.Quasithin.Background.SmithB42G2Rank

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit Matrix

namespace BK4

variable {F : Type} [Field F] [CharP F 2]

theorem eq_one_of_sq_of_pow {M : Type*} [Monoid M] {g : M} {p : ℕ} (hp2 : Odd p)
    (h2 : g ^ 2 = 1) (hp : g ^ p = 1) : g = 1 := by
  obtain ⟨k, rfl⟩ := hp2
  rw [pow_succ, pow_mul, h2, one_pow, one_mul] at hp
  exact hp

theorem exists_decomp_F3 {γ : ↥(cayleyGroup F)} (hS : γ ∈ G2Q8.stabV0 F)
    (hN : ∀ s : Fin 2 → F, G2Q8.levi1Mat γ *ᵥ s = s → s = 0) {z : Ix3 → F}
    (hz : z ∈ G2Q8.stdF F 3) :
    ∃ z' ∈ G2Q8.stdF F 3, ∃ a : F, z = (g2Act γ z' - z') + a • G2Q8.eu 0 1 := by
  set N := G2Q8.levi1Mat γ - 1 with hNdef
  have hinj : Function.Injective N.mulVec := by
    intro s s' h
    have h1 : G2Q8.levi1Mat γ *ᵥ (s - s') = s - s' := by
      have : N *ᵥ (s - s') = 0 := by rw [Matrix.mulVec_sub, h, sub_self]
      rw [hNdef, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at this
      exact this
    exact sub_eq_zero.mp (hN _ h1)
  obtain ⟨s, hs⟩ := (Matrix.mulVec_surjective_iff_isUnit.mpr
    (Matrix.mulVec_injective_iff_isUnit.mp hinj)) (G2Q8.vpart z)
  set z' : Ix3 → F := q6 0 0 0 0 (s 0) (s 1) with hz'
  have hz'F : z' ∈ G2Q8.stdF F 3 := G2Q8.mem_stdF_three.mpr ⟨rfl, rfl, rfl⟩
  have hvz' : G2Q8.vpart z' = s := by
    funext i
    fin_cases i <;> rfl
  have hγz' : g2Act γ z' ∈ G2Q8.stdF F 3 := G2Q8.mapsF3_of_mem hS z' hz'F
  set r := z - (g2Act γ z' - z') with hr
  have hrF : r ∈ G2Q8.stdF F 3 :=
    (G2Q8.stdF F 3).sub_mem hz ((G2Q8.stdF F 3).sub_mem hγz' hz'F)
  have hvr : G2Q8.vpart r = 0 := by
    have h1 : G2Q8.vpart (g2Act γ z' - z') = N *ᵥ s := by
      have e : g2Act γ z' = (g2Act γ z' - z') + z' := (sub_add_cancel _ _).symm
      have h2 := G2Q8.vpart_act hS hz'F
      rw [hvz', e, G2Q8.vpart_add, hvz'] at h2
      rw [hNdef, Matrix.sub_mulVec, Matrix.one_mulVec, ← h2]
      abel
    have h3 : G2Q8.vpart r = G2Q8.vpart z - G2Q8.vpart (g2Act γ z' - z') := by
      have e : z = r + (g2Act γ z' - z') := by rw [hr, sub_add_cancel]
      conv_rhs => rw [e, G2Q8.vpart_add]
      abel
    rw [h3, h1, hs, sub_self]
  refine ⟨z', hz'F, r (.inl 0), ?_⟩
  have hr' : r = r (.inl 0) • G2Q8.eu 0 1 := by
    obtain ⟨h1, h2, h3⟩ := G2Q8.mem_stdF_three.mp hrF
    have h4 := congrFun hvr 0
    have h5 := congrFun hvr 1
    simp only [G2Q8.vpart, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply] at h4 h5
    funext k
    rcases k with k | k <;> fin_cases k <;> simp [G2Q8.eu_eq_q6, q6, h1, h2, h3, h4, h5]
  rw [← hr', hr]
  abel

theorem card_fixQ_le_of_odd [Finite F] {γ : ↥(cayleyGroup F)} {p : ℕ} (hp2 : Odd p)
    (hγp : γ ^ p = 1) (hγ1 : γ ≠ 1) : Nat.card (G2Q8.fixQ γ) ≤ Nat.card F ^ 2 := by
  by_cases h0 : ∀ w ∈ G2Q8.fixQ γ, w = 0
  · have h1 : Nat.card (G2Q8.fixQ γ) = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun a b => Subtype.ext ((h0 _ a.2).trans (h0 _ b.2).symm)⟩, ⟨0⟩⟩
    rw [h1]
    exact Nat.one_le_pow _ _ Nat.card_pos
  simp only [not_forall] at h0
  obtain ⟨w₀, hw₀, hw₀0⟩ := h0
  obtain ⟨g, hg⟩ := G2Q8.exists_g2Act_eu_eq hw₀0
  set γ' := g⁻¹ * γ * g with hγ'
  have hconj : g * γ' * g⁻¹ = γ := by rw [hγ']; group
  rw [← hconj, B42G2.card_fixQ_conj]
  have hS : γ' ∈ G2Q8.stabV0 F := by
    show g2Act γ' (G2Q8.eu 0 1) = G2Q8.eu 0 1
    rw [hγ', G2Q8.g2Act_mul_apply, G2Q8.g2Act_mul_apply, hg, G2Q8.mem_fixQ.mp hw₀, ← hg,
      G2Q8.g2Act_inv_apply]
  have hγ'p : γ' ^ p = 1 := by
    rw [hγ', show g⁻¹ * γ * g = g⁻¹ * γ * g⁻¹⁻¹ by rw [inv_inv], conj_pow, hγp, mul_one,
      inv_inv, inv_mul_cancel]
  have hγ'1 : γ' ≠ 1 := by
    intro h
    apply hγ1
    rw [← hconj, h, mul_one, mul_inv_cancel]
  have hN : ∀ s : Fin 2 → F, G2Q8.levi1Mat γ' *ᵥ s = s → s = 0 := by
    intro s hs
    by_contra hs0
    have h1 := KGNat.mul_self_eq_one_of_mulVec_eq (G2Q8.det_levi1Mat hS) hs hs0
    have hl2 : G2Q8.levi1 ⟨γ', hS⟩ ^ 2 = 1 := Subtype.ext (by
      rw [sq, Matrix.SpecialLinearGroup.coe_mul, G2Q8.levi1_apply, h1]
      rfl)
    have hlp : G2Q8.levi1 ⟨γ', hS⟩ ^ p = 1 := by
      rw [← map_pow]
      have : (⟨γ', hS⟩ : ↥(G2Q8.stabV0 F)) ^ p = 1 := Subtype.ext (by
        rw [SubmonoidClass.coe_pow]
        exact hγ'p)
      rw [this, map_one]
    have hU := G2Q8.ker_levi1_le (eq_one_of_sq_of_pow hp2 hl2 hlp)
    obtain ⟨k, hk⟩ := G2Q8.isPGroup_U0 ⟨γ', hU⟩
    have h2k : γ' ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      rwa [SubmonoidClass.coe_pow] at this
    apply hγ'1
    have hcop : Nat.Coprime (2 ^ k) p :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hp2)
    rw [← orderOf_eq_one_iff]
    exact Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one h2k)
      (orderOf_dvd_of_pow_eq_one hγ'p)
  have key : ∀ w ∈ G2Q8.fixQ γ', w (.inl 0) = 0 → w (.inr 0) = 0 → w = 0 := by
    intro w hw h00 hr0
    have hγw := G2Q8.mem_fixQ.mp hw
    have hperp : ∀ z ∈ G2Q8.stdF F 3, G2Q8.polarQ w z = 0 := by
      intro z hz
      obtain ⟨z', -, a, rfl⟩ := exists_decomp_F3 hS hN hz
      rw [G2Q8.polarQ_add_right, G2Q8.polarQ_sub_right, ← G2Q8.polarQ_g2Act γ' w z', hγw,
        sub_self, zero_add, G2Q8.polarQ_smul_right, G2Q8.eu_eq_q6]
      simp [G2Q8.polarQ, q6, hr0]
    have h1 : w (.inl 1) = 0 := by
      have := hperp (q6 0 0 0 0 1 0) (G2Q8.mem_stdF_three.mpr ⟨rfl, rfl, rfl⟩)
      simpa [G2Q8.polarQ, q6] using this
    have h2 : w (.inl 2) = 0 := by
      have := hperp (q6 0 0 0 0 0 1) (G2Q8.mem_stdF_three.mpr ⟨rfl, rfl, rfl⟩)
      simpa [G2Q8.polarQ, q6] using this
    have hwF : w ∈ G2Q8.stdF F 3 := G2Q8.mem_stdF_three.mpr ⟨h1, h2, hr0⟩
    have hv := G2Q8.vpart_act hS hwF
    rw [hγw] at hv
    have hv0 := hN _ hv.symm
    have h4 := congrFun hv0 0
    have h5 := congrFun hv0 1
    simp only [G2Q8.vpart, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply] at h4 h5
    funext k
    rcases k with k | k <;> fin_cases k <;> simp [h00, h1, h2, hr0, h4, h5]
  let ψ : G2Q8.fixQ γ' → F × F := fun w => (w.1 (.inl 0), w.1 (.inr 0))
  have hψ : Function.Injective ψ := by
    rintro ⟨w, hw⟩ ⟨w', hw'⟩ h
    simp only [ψ, Prod.mk.injEq] at h
    have h3 := key (w - w') ((G2Q8.fixQ γ').sub_mem hw hw') (by simp [h.1]) (by simp [h.2])
    exact Subtype.ext (sub_eq_zero.mp h3)
  have h6 := Nat.card_le_card_of_injective ψ hψ
  rwa [Nat.card_prod, ← sq] at h6

end BK4

end CFSG.Quasithin.Vol2.Ch11.SecB
