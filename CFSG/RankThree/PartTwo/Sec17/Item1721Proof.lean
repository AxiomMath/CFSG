module

public import CFSG.RankThree.PartTwo.Sec17.Item1721ProofCore
public import CFSG.RankThree.PartTwo.Sec17.Item1722Proof
public import CFSG.RankThree.PartTwo.Sec17.Item1724Two
public import CFSG.RankThree.PartTwo.Sec17.Item17ParaS
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
public import CFSG.RankThree.PartTwo.Sec17.Item17HeadProof

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS

@[expose] def Claim1721T : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ Y₁ S : Subgroup G) (p : ℕ)
    (P : Subgroup G), Sec17Y1 G A c L Y₀ Y₁ S p P →
      ¬ Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
        ∃ t ∈ L ⊓ Subgroup.normalizer (A : Set G),
          t ∈ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) ∧
            ∀ x ∈ A ⊓ L, t * x * t⁻¹ = x⁻¹

@[expose] def Claim1721S : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ Y₁ S : Subgroup G) (p : ℕ)
    (P : Subgroup G), Sec17Y1 G A c L Y₀ Y₁ S p P →
      ¬ Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
        ∃ s ∈ Subgroup.normalizer (A : Set G),
          s ∈ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) ∧ s * c * s⁻¹ = c⁻¹

section Item1721

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ Y₁ S : Subgroup G}
  {p : ℕ} {P : Subgroup G}

theorem Sec17Y1.exists_normalizer_P (h : Sec17Y1 G A c L Y₀ Y₁ S p P) (h166 : Item166 A (lB A))
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥) (h168 : Item168 A (lB A) c L)
    (h146 : Item146 A (lB A))
    (h1720 : Sec4.autIn (Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G)) A ≤
      Sec4.autIn (Subgroup.normalizer (S : Set G)) A)
    {g : G} (hgA : g ∈ Subgroup.normalizer (A : Set G))
    (hgSL : g ∈ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G)) :
    ∃ g' ∈ Subgroup.normalizer (A : Set G), g' ∈ Subgroup.normalizer (P : Set G) ∧
      ∀ a ∈ A, g' * a * g'⁻¹ = g * a * g⁻¹ := by
  have hs := h.toSec17Std
  obtain ⟨-, -, -, hWS⟩ := h.item168_at h166 hbot h168
  obtain ⟨n, hnA, hnS, hn⟩ :=
    Sec4.mem_autIn_iff.mp (h1720 (Sec4.mem_autIn_iff.mpr ⟨g, hgA, hgSL, rfl⟩))
  have hnY : n ∈ Subgroup.normalizer (Y₁ : Set G) := hWS (Subgroup.mem_inf.mpr ⟨hnA, hnS⟩)
  have hPn : P.map (MulAut.conj n).toMonoidHom ∈ scriptQPiStar A (lB A) Y₁ (piOf p) := by
    have := HeadProof.map_conj_mem_scriptQPiStar hnA h.mem_qStar_p
    rwa [Late.map_conj_eq_of_mem_normalizer hnY] at this
  have hY₁3 : ¬ 3 ∣ Nat.card Y₁ := not_three_dvd_of_oPrimeResidualOf_eq_bot' h.mem_y1Star.prop.2
  have h3 : ¬ 3 ∣ Nat.card (oPrimeResidualOf p (delta A (lB A) Y₁)) := fun h3 =>
    hY₁3 (h3.trans (Subgroup.card_dvd_of_le
      ((oPrimeResidualOf_le_self p _).trans (delta_le Y₁))))
  obtain ⟨x, hx, hxP⟩ :=
    isConjIn_of_not_three_dvd hs.isE27 h146 hbot h.p_prime h3 h.mem_qStar_p hPn
  have hxC : x ∈ Subgroup.centralizer (A : Set G) := pPrimeCoreOf_le 3 _ (Subgroup.mem_inf.mp hx).1
  have hxA : x ∈ Subgroup.normalizer (A : Set G) := Subgroup.centralizer_le_normalizer _ hxC
  refine ⟨x⁻¹ * n, mul_mem (inv_mem hxA) hnA, inv_mul_mem_normalizer_of_map_conj_eq hxP.symm,
    fun a ha => ?_⟩
  have hna : n * a * n⁻¹ = g * a * g⁻¹ := by
    have h1 := congrArg (fun σ : MulAut A => ((σ ⟨a, ha⟩ : A) : G)) hn
    simp only [Sec4.normalizerMonoidHom_apply_coe] at h1
    exact h1
  have hnaA : n * a * n⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hnA a).mp ha
  have hxna : x⁻¹ * (n * a * n⁻¹) = (n * a * n⁻¹) * x⁻¹ :=
    (Subgroup.mem_centralizer_iff.mp (inv_mem hxC) _ hnaA).symm
  calc x⁻¹ * n * a * (x⁻¹ * n)⁻¹ = x⁻¹ * (n * a * n⁻¹) * x := by group
    _ = n * a * n⁻¹ := by rw [hxna, inv_mul_cancel_right]
    _ = g * a * g⁻¹ := hna

theorem rank3II_17_21_of (h : Sec17Y1 G A c L Y₀ Y₁ S p P) (h166 : Item166 A (lB A))
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥) (h168 : Item168 A (lB A) c L)
    (h146 : Item146 A (lB A)) (h9 : Nat.card (A ⊓ L : Subgroup G) = 9)
    (h1719 : A ⊓ L ≠ A ⊓ Subgroup.centralizer (P : Set G))
    (h1720 : Sec4.autIn (Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G)) A ≤
      Sec4.autIn (Subgroup.normalizer (S : Set G)) A)
    (hT : ¬ Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
      ∃ t ∈ L ⊓ Subgroup.normalizer (A : Set G),
        t ∈ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) ∧ ∀ x ∈ A ⊓ L, t * x * t⁻¹ = x⁻¹)
    (hS : ¬ Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
      ∃ s ∈ Subgroup.normalizer (A : Set G),
        s ∈ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) ∧ s * c * s⁻¹ = c⁻¹) :
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) := by
  by_contra hJ
  have : Fact p.Prime := ⟨h.p_prime⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hs := h.toSec17Std
  obtain ⟨t, htLA, htSL, htinv⟩ := hT hJ
  obtain ⟨s, hsA, hsSL, hsc⟩ := hS hJ
  have htL : t ∈ L := (Subgroup.mem_inf.mp htLA).1
  have htA : t ∈ Subgroup.normalizer (A : Set G) := (Subgroup.mem_inf.mp htLA).2
  obtain ⟨s₂, -, hs₂P, hs₂⟩ := h.exists_normalizer_P h166 hbot h168 h146 h1720 hsA hsSL
  obtain ⟨t₂, -, ht₂P, ht₂⟩ := h.exists_normalizer_P h166 hbot h168 h146 h1720 htA htSL
  have hcA : c ∈ A := hs.c_mem
  have hAP : A ≤ Subgroup.normalizer (P : Set G) := h.mem_qStar_p.prop.1.1.1.2.2
  have hcC : c ∉ Subgroup.centralizer (P : Set G) := by
    intro hcP
    apply h.commutator_not_le_M
    have hbot' : ⁅P, Subgroup.zpowers c⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.zpowers_eq_closure,
        Subgroup.centralizer_closure]
      intro x hx
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hcP x hx)
    rw [hbot']
    exact bot_le
  have h3L : 3 ∣ Nat.card L := by
    have := Subgroup.card_dvd_of_le (inf_le_right : A ⊓ L ≤ L)
    rw [h9] at this
    exact (by norm_num : 3 ∣ 9).trans this
  have hsH : s ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
    refine mem_normalizer_of_map_conj_eq' ?_
    rw [MonoidHom.map_zpowers]
    change Subgroup.zpowers (s * c * s⁻¹) = _
    rw [hsc, Subgroup.zpowers_inv]
  have hsL : s ∈ Subgroup.normalizer (L : Set G) :=
    Sec15R.normalizer_zpowers_le_normalizer_L hs.toSec15R h3L hsH
  have hrank : ∀ E : Subgroup G, E ≤ P → (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) →
      (∀ x ∈ E, x ^ p = 1) → Nat.card E ≤ p ^ 2 := fun E hEP hEc hEp =>
    HeadProof.card_le_sq_of_pCoreOf_ne_bot hs.toTheoremFourHyp h.mem_y1Star.prop.1.1.2
      (not_three_dvd_of_oPrimeResidualOf_eq_bot' h.mem_y1Star.prop.2) p h.p_prime
      (by have := h.three_lt_p; omega) E (hEP.trans h.mem_qStar_p.prop.1.2) hEc hEp
  have hFC := TailProof.le_centralizer_of_inverts_pGroup (P := P) (F := A ⊓ L)
    (by have := h.three_lt_p; omega) (by have := h.three_lt_p; omega)
    ((isPiSubgroup_piOf_iff h.p_prime P).mp h.mem_qStar_p.prop.2) hrank
    (fun f hf => HeadProof.pow_three_of_std hs hf.1)
    (fun a ha b hb => hs.commute_of_mem ha.1 hb.1) h9 (inf_le_left.trans hAP)
    (hs.c_pow_three) (fun f hf => hs.commute_of_mem hcA hf.1) (hAP hcA) hcC
    hs₂P (by rw [hs₂ c hcA, hsc])
    (fun f hf => by
      rw [hs₂ f hf.1]
      exact ⟨(Subgroup.mem_normalizer_iff.mp hsA f).mp hf.1,
        (Subgroup.mem_normalizer_iff.mp hsL f).mp hf.2⟩)
    ht₂P (by
      rw [ht₂ c hcA]
      have htc : t * c = c * t := Subgroup.mem_centralizer_singleton_iff.mp
        (hs.le_centralizer_c htL)
      rw [htc, mul_inv_cancel_right])
    (fun f hf => by rw [ht₂ f hf.1, htinv f hf])
  apply h1719
  have hle : A ⊓ L ≤ A ⊓ Subgroup.centralizer (P : Set G) := le_inf inf_le_left hFC
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [h9]
  have hdvd : Nat.card (A ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) ∣ 3 ^ 3 := by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hs.isE27.2]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨m, hm, hmc⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  have h9le : 9 ≤ Nat.card (A ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) := by
    rw [← h9]
    exact Subgroup.card_le_of_le hle
  have hm3 : m ≠ 3 := by
    rintro rfl
    apply hcC
    have heq : A ⊓ Subgroup.centralizer (P : Set G) = A :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hmc, hs.isE27.2]; norm_num)
    exact (heq.symm ▸ hcA : c ∈ A ⊓ Subgroup.centralizer (P : Set G)).2
  rw [hmc] at h9le ⊢
  interval_cases m <;> simp_all

end Item1721

end CFSG.RankThree.PartTwo.Sec17
