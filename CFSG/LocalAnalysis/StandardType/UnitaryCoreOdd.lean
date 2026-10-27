module

public import CFSG.LocalAnalysis.StandardType.A8LiftBlocks
public import CFSG.LocalAnalysis.StandardType.CommutingOrderThreeDiag
public import CFSG.LocalAnalysis.StandardType.UnitaryWeightGram
public import CFSG.LocalAnalysis.StandardType.UnitaryWeightCount
public import CFSG.LocalAnalysis.StandardType.UnitaryCoreFibres

public section

namespace CFSG.StandardType

namespace UnitaryCore

open Matrix SpBlocks UnitaryWeight

variable {Γ : Type*} [Group Γ] [Finite Γ] {ι : Type} [Fintype ι] [DecidableEq ι] {Ω : Type}
  [Field Ω] [IsAlgClosed Ω] [CharP Ω 2]

theorem eq_one_of_commute_odd (h5 : HasOrderFiveData Γ) (h7 : HasOrderSevenData Γ) (σ : Ω ≃+* Ω)
    (hσ3 : ∀ η : Ω, η ^ 3 = 1 → σ η = η⁻¹) (hι : Fintype.card ι ≤ 6) {G : Matrix ι ι Ω}
    (hG : IsUnit G) (ρ : Γ →* Matrix ι ι Ω) (hρ : ∀ g, (ρ g)ᵀ * G * (ρ g).map σ = G)
    {A : Matrix ι ι Ω} (hA3 : A ^ 3 = 1) {s : Ω} (hAG : Aᵀ * G * A.map σ = s • G)
    (hcomm : ∀ g, ρ g * A = A * ρ g) (hnc : ∀ c : Ω, A ≠ c • 1) (g : Γ) : ρ g = 1 := by
  classical
  by_cases hne : Nonempty ι
  · haveI : Nonempty ι := hne
    obtain ⟨P, w, hw3, hAPw⟩ :=
      exists_diagonalizing_basis (κ := Unit) (X := fun _ : Unit => A)
        (fun _ _ => rfl) (fun _ => hA3)
    let a : ι → Ω := w ()
    have ha3 : ∀ α, a α ^ 3 = 1 := fun α => hw3 () α
    have hAP : A * (P : Matrix ι ι Ω) = (P : Matrix ι ι Ω) * diagonal a := hAPw ()
    have hPu : IsUnit (P : Matrix ι ι Ω) := P.isUnit
    let Q : Matrix ι ι Ω := ((P⁻¹ : GL ι Ω) : Matrix ι ι Ω)
    have hPQ : (P : Matrix ι ι Ω) * Q = 1 := by
      show (P : Matrix ι ι Ω) * ((P⁻¹ : GL ι Ω) : Matrix ι ι Ω) = 1
      exact Units.mul_inv P
    have hQP : Q * (P : Matrix ι ι Ω) = 1 := by
      show ((P⁻¹ : GL ι Ω) : Matrix ι ι Ω) * (P : Matrix ι ι Ω) = 1
      exact Units.inv_mul P
    let H : Matrix ι ι Ω := (P : Matrix ι ι Ω)ᵀ * G * (P : Matrix ι ι Ω).map σ
    have hHu : IsUnit H := UnitaryWeight.isUnit_gram_weight σ hPu hG
    have ha_ne : ∀ α, a α ≠ 0 := by
      intro α h0
      have h3 := ha3 α
      rw [h0] at h3
      rw [zero_pow (by norm_num : (3 : ℕ) ≠ 0)] at h3
      exact zero_ne_one h3
    have hEntry : ∀ α β, H α β ≠ 0 → a β = a α / s := by
      intro α β hH
      have he : a α * σ (a β) = s := UnitaryWeight.gram_weight_entry σ hAG hAP hH
      have h1 : a α * (a β)⁻¹ = s := by
        rw [← he, hσ3 (a β) (ha3 β)]
      have hα_eq : a α = s * a β := by
        have h := congrArg (fun x : Ω => x * a β) h1
        rwa [mul_assoc, inv_mul_cancel₀ (ha_ne β), mul_one] at h
      have hs0 : s ≠ 0 := fun hs => ha_ne α (by rw [hα_eq, hs, zero_mul])
      rw [eq_div_iff hs0]
      exact (mul_comm (a β) s).trans hα_eq.symm
    obtain ⟨α₀, β₀, hH0⟩ : ∃ α β, H α β ≠ 0 := by
      by_contra h
      have hzero : H = 0 := by
        ext α β
        by_contra hne
        exact h ⟨α, β, hne⟩
      exact hHu.ne_zero hzero
    have hs3 : s ^ 3 = 1 := by
      have he : a α₀ * σ (a β₀) = s := UnitaryWeight.gram_weight_entry σ hAG hAP hH0
      have hseq : s = a α₀ * (a β₀)⁻¹ := by rw [← he, hσ3 (a β₀) (ha3 β₀)]
      rw [hseq, mul_pow, inv_pow, ha3 α₀, ha3 β₀, inv_one, mul_one]
    have hna : ∀ c : Ω, ¬ ∀ α, a α = c := by
      intro c hconst
      apply hnc c
      have hdiag : diagonal a = c • (1 : Matrix ι ι Ω) := by
        have ha_eq : a = (fun _ : ι => c) := funext hconst
        rw [ha_eq, diagonal_const_eq_smul_one]
      have hAPc : A * (P : Matrix ι ι Ω) = c • (P : Matrix ι ι Ω) := by
        rw [hAP, hdiag, Matrix.mul_smul, Matrix.mul_one]
      calc A = A * 1 := (Matrix.mul_one A).symm
        _ = A * ((P : Matrix ι ι Ω) * Q) := by rw [hPQ]
        _ = (A * (P : Matrix ι ι Ω)) * Q := by rw [Matrix.mul_assoc]
        _ = (c • (P : Matrix ι ι Ω)) * Q := by rw [hAPc]
        _ = c • ((P : Matrix ι ι Ω) * Q) := by rw [Matrix.smul_mul]
        _ = c • 1 := by rw [hPQ]
    let I : Ω → Finset ι := fun m => Finset.univ.filter fun α => a α = m
    have hI0 : I 0 = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro α hα
      have hα' : a α = 0 := by
        simpa only [I, Finset.mem_filter, Finset.mem_univ, true_and] using hα
      exact ha_ne α hα'
    let R : Γ →* Matrix ι ι Ω := conjHom hPQ hQP ρ
    have hform : ∀ g, (R g)ᵀ * H * (R g).map σ = H := by
      intro g
      simpa only [H, R, conjHom_apply] using UnitaryWeight.transport_form σ hPQ hQP (hρ g)
    have hcommR : ∀ g, R g * diagonal a = diagonal a * R g := by
      intro g
      simpa only [R, conjHom_apply] using
        UnitaryWeight.commute_diagonal_conj hPQ hQP hAP (hcomm g)
    have hQs : ∀ g k, Splits (I k) (R g) := by
      intro g k
      exact splits_fibre_of_commute_diagonal (fun _ : Unit => a) (fun _ => hcommR g) a
        (fun α β hw => hw ()) k
    by_cases hs1 : s = 1
    · have hsplit_self : ∀ k, Splits (I k) H := by
        intro k
        apply SpBlocks.splits_fiber_of_forall a
        intro α β hH
        have hb : a β = a α / s := hEntry α β hH
        rw [hs1, div_one] at hb
        exact hb.symm
      have hne_univ : ∀ k, I k ≠ Finset.univ := by
        intro k hk
        apply hna k
        intro α
        have hα : α ∈ I k := by rw [hk]; exact Finset.mem_univ α
        simpa only [I, Finset.mem_filter, Finset.mem_univ, true_and] using hα
      have hsmall5 : ∀ k, (I k).card ≤ 5 := by
        intro k
        have hlt : (I k).card < Fintype.card ι := by
          have : (I k).card < (Finset.univ : Finset ι).card :=
            Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
              ⟨Finset.subset_univ (I k), hne_univ k⟩)
          simpa only [Finset.card_univ] using this
        omega
      have hRg : R g = 1 :=
        eq_one_of_fibres h5 h7 σ a hHu R hQs hform
          (fun k => Or.inr ⟨hsmall5 k, hsplit_self k⟩) g
      exact eq_one_of_conjHom hPQ hQP ρ g hRg
    · have hs0 : s ≠ 0 := by
        intro h0
        rw [h0] at hs3
        rw [zero_pow (by norm_num : (3 : ℕ) ≠ 0)] at hs3
        exact zero_ne_one hs3
      have hs2ne1 : s ^ 2 ≠ 1 := by
        intro h2
        apply hs1
        have h : s ^ 3 = s := by
          rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_add, h2, one_mul, pow_one]
        rw [hs3] at h
        exact h.symm
      have hkey : ∀ k : Ω, ((k / s) / s) / s = k := by
        intro k
        rw [div_eq_iff hs0, div_eq_iff hs0, div_eq_iff hs0]
        rw [show ((k * s) * s) * s = k * s ^ 3 by ring, hs3, mul_one]
      have hchain : ∀ m : Ω, (I m).card ≤ (I (m / s)).card := by
        intro m
        apply UnitaryWeight.card_le_card_of_isUnit_support hHu
        intro α hα β hβ
        by_contra hH
        apply hβ
        simp only [I, Finset.mem_filter, Finset.mem_univ, true_and]
        have hαm : a α = m := by
          simpa only [I, Finset.mem_filter, Finset.mem_univ, true_and] using hα
        rw [hEntry α β hH, hαm]
      have hdisj_ne : ∀ {m n : Ω}, m ≠ n → Disjoint (I m) (I n) := by
        intro m n hmn
        change Disjoint (Finset.univ.filter (fun x => a x = m))
          (Finset.univ.filter (fun x => a x = n))
        exact Finset.disjoint_filter.mpr (fun x _ hp hq => hmn (hp.symm.trans hq))
      have hsmall3 : ∀ k : Ω, (I k).card ≤ 3 := by
        intro k
        by_cases hk0 : k = 0
        · rw [hk0, hI0]
          simp
        · have h12 : (I k).card ≤ (I (k / s)).card := hchain k
          have h23 : (I (k / s)).card ≤ (I ((k / s) / s)).card := hchain (k / s)
          have h34 : (I ((k / s) / s)).card ≤ (I (((k / s) / s) / s)).card :=
            hchain ((k / s) / s)
          have h41 : (I ((k / s) / s)).card ≤ (I k).card := by
            rw [hkey k] at h34
            exact h34
          have hkm : k ≠ k / s := by
            intro h
            have hmul : k * s = k := by
              conv_lhs => rw [h]
              rw [div_mul_cancel₀ k hs0]
            have hzero : k * (s - 1) = 0 := by rw [mul_sub, mul_one, hmul, sub_self]
            rcases mul_eq_zero.mp hzero with hk | hs
            · exact hk0 hk
            · exact hs1 (sub_eq_zero.mp hs)
          have hkm2 : k ≠ (k / s) / s := by
            intro h
            have h' : k = k / (s * s) := h.trans (by rw [div_div])
            have hmul : k * (s * s) = k := by
              conv_lhs => rw [h']
              rw [div_mul_cancel₀ k (mul_ne_zero hs0 hs0)]
            have hzero : k * (s * s - 1) = 0 := by rw [mul_sub, mul_one, hmul, sub_self]
            rcases mul_eq_zero.mp hzero with hk | hs
            · exact hk0 hk
            · exact hs2ne1 (by rw [sq]; exact sub_eq_zero.mp hs)
          have hm0 : k / s ≠ 0 := div_ne_zero hk0 hs0
          have hm12 : k / s ≠ (k / s) / s := by
            intro h
            have hmul : (k / s) * s = k / s := by
              conv_lhs => rw [h]
              rw [div_mul_cancel₀ (k / s) hs0]
            have hzero : (k / s) * (s - 1) = 0 := by rw [mul_sub, mul_one, hmul, sub_self]
            rcases mul_eq_zero.mp hzero with hm | hs
            · exact hm0 hm
            · exact hs1 (sub_eq_zero.mp hs)
          have hdisj12 : Disjoint (I k) (I (k / s)) := hdisj_ne hkm
          have hdisj13 : Disjoint (I k) (I ((k / s) / s)) := hdisj_ne hkm2
          have hdisj23 : Disjoint (I (k / s)) (I ((k / s) / s)) := hdisj_ne hm12
          have hdisjU : Disjoint (I k ∪ I (k / s)) (I ((k / s) / s)) :=
            Finset.disjoint_union_left.mpr ⟨hdisj13, hdisj23⟩
          have hU := Finset.card_union_of_disjoint hdisjU
          have hU1 := Finset.card_union_of_disjoint hdisj12
          have huniv : (I k ∪ I (k / s) ∪ I ((k / s) / s)).card ≤ Fintype.card ι := by
            simpa only [Finset.card_univ] using
              Finset.card_le_card (Finset.subset_univ (I k ∪ I (k / s) ∪ I ((k / s) / s)))
          rw [hU, hU1] at huniv
          have h1eq2 : (I k).card = (I (k / s)).card := le_antisymm h12 (h23.trans h41)
          have h1eq3 : (I k).card = (I ((k / s) / s)).card := le_antisymm (h12.trans h23) h41
          rw [← h1eq2, ← h1eq3] at huniv
          omega
      have hRg : R g = 1 :=
        eq_one_of_fibres h5 h7 σ a hHu R hQs hform (fun k => Or.inl (hsmall3 k)) g
      exact eq_one_of_conjHom hPQ hQP ρ g hRg
  · haveI : IsEmpty ι := not_nonempty_iff.mp hne
    ext i j
    exact (IsEmpty.false j).elim

end UnitaryCore

end CFSG.StandardType
