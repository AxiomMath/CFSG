module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4ZtMain

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem fan49_main_five (F : FanTree Γ G) (h40 : Fan40 F) (h33 : Fan33 F) (h48 : Fan48Two F)
    {T : Track Γ G} (hI : InPiStar T) : ∃ d, valence Γ (T.line.vert d) = 5 ∧ ZT T d = ⊥ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨a, b, hθ⟩ := fan42_2a T F h40
  have hPi := hI.1
  have hev := fan_4_3_2 T F hPi hθ
  obtain ⟨m, hm⟩ : ∃ m : ℤ, b - a = 2 * m := ⟨(b - a) / 2, by omega⟩
  have hab : Γ.Adj (T.line.vert a) (T.line.vert (a + 1)) := T.line.adj a
  have hac : T.line.vert a ≠ T.line.vert (a + 2) := T.line.nb a
  have hα3 : valence Γ (T.line.vert a) = 3 := fan47 T F h40 hPi hθ (Or.inl rfl)
  obtain ⟨hLam, -⟩ := fan45_2_lam T F hPi.1 hPi.2 hθ (c := a) (Or.inl rfl)
  obtain ⟨H, hS, hHnorm, hcentral⟩ := h48 T hI a b hθ
  have hv5 : valence Γ (T.line.vert (a + 1)) = 5 := by
    have h1 := F.alternating _ _ hab
    have h2 := F.valence (T.line.vert (a + 1))
    have h3 : Nat.card (Γ.neighborSet (T.line.vert a)) = 3 := hα3
    rcases h2 with h2 | h2
    · exact absurd (h3.trans h2.symm) h1
    · exact h2
  have hZne : ZT T (a + 1) ≠ ⊥ := hcon (a + 1) hv5
  obtain ⟨hfinL, htrL, hcardL, -⟩ := lamSet_setup F hab hLam
  have hdvd : 3 ∣ Nat.card ↥(Subgroup.normalizer (omega1 T.fixer : Set G) ⊓
      MulAction.stabilizer G (T.line.vert a)) := by
    rw [hcardL, hα3]
    exact dvd_mul_right _ _
  have h3p : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x₃, hx₃⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.normalizer
    (omega1 T.fixer : Set G) ⊓ MulAction.stabilizer G (T.line.vert a))) 3 hdvd
  have hx₃o : orderOf (x₃ : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hx₃
  have hx₃c : ∀ z ∈ ZT T (a + 1), (x₃ : G) * z = z * x₃ := fun z hz =>
    hcentral x₃ x₃.2 hx₃o z (mem_ZT_iff.1 hz).1
  have hx₃N : (x₃ : G) ∈ Subgroup.normalizer (ZT T (a + 1) : Set G) :=
    mem_normalizer_of_comm hx₃c
  obtain ⟨w, hwH, hwβ, hwα⟩ := hS.exists_swap F hm
  have hnormZ : ∀ w ∈ H, w • T.line.vert (a + 1) = T.line.vert (a + 1) →
      ∀ z ∈ ZT T (a + 1), w * z * w⁻¹ ∈ ZT T (a + 1) := by
    intro w hw hwb z hz
    obtain ⟨hzf, hzc⟩ := mem_ZT_iff.1 hz
    refine mem_ZT_iff.2 ⟨hHnorm w hw z hzf, fun k hk => ?_⟩
    have hk' : w⁻¹ * k * w ∈ nbrStab Γ G (T.line.vert (a + 1)) := by
      have := nbrStab_conj_mem F (g := w⁻¹) (v := T.line.vert (a + 1))
        (by rw [inv_smul_eq_iff]; exact hwb.symm) hk
      simpa using this
    have h1 := hzc _ hk'
    calc k * (w * z * w⁻¹) = w * ((w⁻¹ * k * w) * z) * w⁻¹ := by group
      _ = w * (z * (w⁻¹ * k * w)) * w⁻¹ := by rw [h1]
      _ = w * z * w⁻¹ * k := by group
  have hwN : w ∈ Subgroup.normalizer (ZT T (a + 1) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    refine ⟨fun hz => hnormZ w hwH hwβ z hz, fun hz => ?_⟩
    have := hnormZ w⁻¹ (H.inv_mem hwH) (by rw [inv_smul_eq_iff]; exact hwβ.symm) _ hz
    simpa [mul_assoc] using this
  have hNLam : Subgroup.normalizer (ZT T (a + 1) : Set G) ∈
      LamSet Γ G (T.line.vert a) (T.line.vert (a + 1)) (T.line.vert (a + 2)) := by
    refine ⟨ZT T (a + 1), hZne, fun g hg => ⟨MulAction.mem_stabilizer_iff.2
      ((T.mem_fixer).1 (mem_ZT_iff.1 hg).1 a), MulAction.mem_stabilizer_iff.2
      ((T.mem_fixer).1 (mem_ZT_iff.1 hg).1 (a + 1))⟩, rfl, ?_,
      ⟨w, ⟨hwN, MulAction.mem_stabilizer_iff.2 hwβ⟩, hwα⟩⟩
    intro u v hu hv
    obtain ⟨k, hk, hkα, hku⟩ := zpowers_transitive F (T.line.vert a) x₃.2.2 Nat.prime_three
      (by norm_num) hx₃o u v hu hv
    exact ⟨k, ⟨(Subgroup.zpowers_le.2 hx₃N) hk, MulAction.mem_stabilizer_iff.2 hkα⟩, hku⟩
  have hKβN : nbrStab Γ G (T.line.vert (a + 1)) ≤ Subgroup.normalizer (ZT T (a + 1) : Set G) := by
    intro k hk
    exact Subgroup.centralizer_le_normalizer _ (by
      rw [Subgroup.mem_centralizer_iff]
      exact fun z hz => ((mem_ZT_iff.1 hz).2 k hk).symm)
  have hN1 := fan41_1 F hab hac hNLam
  obtain ⟨Q, hQ0, hQ, hLQ, hloc, -⟩ := hNLam
  exact false_of_ball_eq F h33 h40 hab (nbrStab_inf_eq_ballStab F hab hKβN (fun u v hu hv => by
    obtain ⟨g, hg, hgu⟩ := hloc u v hu hv
    exact ⟨g, hg, hgu⟩) hN1)

end CFSG.Quasithin.Fan86
