module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.Generic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg

open CFSG.Open Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.ABGLocalTools (IsSylowOf)

namespace OneComp

variable {K : Type} [Group K] [Finite K] {J M X P : Subgroup K}

theorem exists_index (h : OneComp J M X P) :
    ∃ m : ℕ, m ∣ Nat.card J ∧ Nat.Coprime m 6 ∧ m % 7 = 1 ∧ 1 < m := by
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have hJM : J ⊔ M = ⊤ := by
    rw [eq_top_iff, ← h.sup_normalizer_eq_top]
    exact sup_le_sup_left h.normalizer_le J
  haveI hJnormal : J.Normal := h.normal
  have hMJ : M.relIndex J = M.index := by
    rw [← CFSG.ABGLocalTools.relIndex_sup_eq_relIndex_of_normal (N := J) (P := M),
      hJM, Subgroup.relIndex_top_right]
  have hm_dvd : M.index ∣ Nat.card J := by
    rw [← hMJ]
    exact Subgroup.relIndex_dvd_card M J
  have h2 : ¬ 2 ∣ M.index := by
    obtain ⟨S, hSyl, hSM⟩ := h.exists_sylow_two
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hSJ : IsSylowOf 2 (S ⊓ J) J := by
      have htop : (⊤ : Subgroup K) ≤ normalizer (J : Set K) := by
        rw [Subgroup.normalizer_eq_top]
      simpa using IsSylowOf.inf_of_le_normalizer (p := 2) (P := S) (K := ⊤)
        (N := J) hSyl le_top htop
    have hnot : ¬ 2 ∣ (S ⊓ J).relIndex J :=
      (CFSG.ABGLocalTools.isSylowOf_iff.mp hSJ).2.2
    have hdvd : (M ⊓ J).relIndex J ∣ (S ⊓ J).relIndex J :=
      Subgroup.relIndex_dvd_of_le_left J
        (le_inf (le_trans inf_le_left hSM) inf_le_right)
    have hnot2 : ¬ 2 ∣ (M ⊓ J).relIndex J := fun hd => hnot (hd.trans hdvd)
    rwa [Subgroup.inf_relIndex_right (H := M) (K := J), hMJ] at hnot2
  have h3 : ¬ 3 ∣ M.index := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hXM : X ≤ M := le_trans Subgroup.le_normalizer h.normalizer_le
    have hXle : X ≤ M ⊓ J := le_inf hXM h.sylow.le
    have hnot : ¬ 3 ∣ X.relIndex J :=
      (CFSG.ABGLocalTools.isSylowOf_iff.mp h.sylow).2.2
    have hdvd : (M ⊓ J).relIndex J ∣ X.relIndex J :=
      Subgroup.relIndex_dvd_of_le_left J hXle
    have hnot3 : ¬ 3 ∣ (M ⊓ J).relIndex J := fun hd => hnot (hd.trans hdvd)
    rwa [Subgroup.inf_relIndex_right (H := M) (K := J), hMJ] at hnot3
  have h7P : 7 ∣ Nat.card P := by
    rw [h.sylowSeven.card_eq]
    exact dvd_pow_self 7 (Nat.Prime.factorization_pos_of_dvd Nat.prime_seven
      Nat.card_pos.ne' h.strong.2.1).ne'
  have hfixcard : Nat.card (MulAction.fixedPoints P (K ⧸ M)) = 1 := by
    apply Nat.card_eq_one_iff_exists.mpr
    refine ⟨⟨QuotientGroup.mk (1 : K), ?_⟩, ?_⟩
    · rw [MulAction.mem_fixedPoints]
      intro p
      rw [Subgroup.smul_def, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
      exact QuotientGroup.eq.mpr (by simpa using inv_mem (h.sylowSeven.le p.2))
    · rintro ⟨y, hy⟩
      apply Subtype.ext
      change y = QuotientGroup.mk (1 : K)
      have hyall : ∀ p : P, p • y = y := MulAction.mem_fixedPoints.mp hy
      let g : K := y.out
      have hyg : QuotientGroup.mk g = y := QuotientGroup.out_eq' y
      have hgM : g ∈ M := by
        by_contra hgm
        have hmem : ∀ p : P, ((p : K) * g)⁻¹ * g ∈ M := by
          intro p
          have hp : p • (QuotientGroup.mk g : K ⧸ M) = QuotientGroup.mk g := by
            have := hyall p
            rwa [← hyg] at this
          rw [Subgroup.smul_def, MulAction.Quotient.smul_mk, smul_eq_mul] at hp
          exact QuotientGroup.eq.mp hp
        have hconj : ∀ p : P, g⁻¹ * (p : K) * g ∈ M := by
          intro p
          have := hmem p⁻¹
          simpa [Subgroup.coe_inv, mul_assoc] using this
        let f : K →* K := (MulAut.conj g⁻¹).toMonoidHom
        let Q : Subgroup K := P.map f
        have hQleM : Q ≤ M := by
          rintro x ⟨p, hp, rfl⟩
          have := hconj ⟨p, hp⟩
          simpa [f, MulAut.conj_apply] using this
        have hQleMap : Q ≤ M.map f := Subgroup.map_mono h.sylowSeven.le
        have hQle : Q ≤ M ⊓ M.map f := le_inf hQleM hQleMap
        have hinj : Function.Injective f := fun x y hxy =>
          (MulAut.conj g⁻¹).injective (by simpa [f] using hxy)
        have hcardQ : Nat.card Q = Nat.card P :=
          Subgroup.card_map_of_injective (f := f) hinj
        have h7Q : 7 ∣ Nat.card Q := by
          rw [hcardQ]
          exact h7P
        have h7int : 7 ∣ Nat.card (M ⊓ M.map f : Subgroup K) :=
          dvd_trans h7Q (Subgroup.card_dvd_of_le hQle)
        have hginv : g⁻¹ ∉ M := by
          intro hg
          exact hgm (by simpa using inv_mem hg)
        exact h.strong.2.2 g⁻¹ hginv (by simpa [f] using h7int)
      rw [← hyg]
      exact QuotientGroup.eq.mpr (by simpa using inv_mem hgM)
  refine ⟨M.index, hm_dvd, ?_, ?_, ?_⟩
  · have h2c : Nat.Coprime M.index 2 :=
      (Nat.prime_two.coprime_iff_not_dvd.mpr h2).symm
    have h3c : Nat.Coprime M.index 3 :=
      (Nat.prime_three.coprime_iff_not_dvd.mpr h3).symm
    simpa [show (6 : ℕ) = 2 * 3 from rfl] using h2c.mul_right h3c
  · have hmod : Nat.card (K ⧸ M) ≡ (1 : ℕ) [MOD 7] := by
      simpa [hfixcard] using
        h.sylowSeven.isPGroup.card_modEq_card_fixedPoints (K ⧸ M)
    simpa [Nat.ModEq, Subgroup.index, Nat.mod_eq_of_lt (by norm_num : 1 < 7)] using hmod
  · have hne1 : M.index ≠ 1 := fun h1 => h.strong.1 (Subgroup.index_eq_one.mp h1)
    have hne0 : M.index ≠ 0 := Subgroup.index_ne_zero_of_finite (H := M)
    exact Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hne0, hne1⟩

end OneComp

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg
