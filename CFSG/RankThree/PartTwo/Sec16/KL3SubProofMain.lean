module

public import CFSG.RankThree.PartTwo.Sec16.KL3SubProofEnd
public import CFSG.RankThree.PartTwo.Sec16.KL3SubProofBlock
public import CFSG.RankThree.PartTwo.Sec16.Item166Res6ProofIrrW

public section

namespace CFSG.RankThree.PartTwo.Sec16

namespace KL3SubProof

open Matrix

variable {K : Type} [Field K]

section Sylow

variable [CharP K 2]

@[expose] def utmUnit (a b c : K) : GL (Fin 3) K where
  val := utm a b c
  inv := utm a b (c + a * b)
  val_inv := utm_mul_inv a b c
  inv_val := by
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    rw [utm_mul, utm_eq_one_iff]
    refine ⟨?_, ?_, ?_⟩
    · linear_combination a * h2
    · linear_combination b * h2
    · linear_combination (c + a * b) * h2

theorem coe_utmUnit (a b c : K) :
    ((utmUnit a b c : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = utm a b c := rfl

theorem card_utSub [Finite K] : Nat.card (utSub K) = Nat.card K ^ 3 := by
  set f : K × K × K → GL (Fin 3) K := fun x => utmUnit x.1 x.2.1 x.2.2 with hf
  have hinj : Function.Injective f := by
    rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
    have h' : utm a b c = utm a' b' c' :=
      congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) h
    obtain ⟨h1, h2, h3⟩ := utm_inj h'
    rw [h1, h2, h3]
  have hrange : Set.range f = (utSub K : Set (GL (Fin 3) K)) := by
    ext g
    constructor
    · rintro ⟨x, rfl⟩
      exact isUT_utm _ _ _
    · intro hg
      refine ⟨((g : Matrix (Fin 3) (Fin 3) K) 0 1, (g : Matrix (Fin 3) (Fin 3) K) 1 2,
        (g : Matrix (Fin 3) (Fin 3) K) 0 2), Units.ext ?_⟩
      exact (mem_utSub.mp hg).eq_utm.symm
  have h1 : Nat.card (utSub K) = Nat.card (Set.range f) := by
    rw [hrange]
    rfl
  rw [h1, Nat.card_range_of_injective hinj, Nat.card_prod, Nat.card_prod]
  ring

theorem isPGroup_utSub : IsPGroup 2 (utSub K) := fun g =>
  ⟨2, Subtype.ext (by simpa using pow_four_eq_one_of_mem_utSub g.2)⟩

theorem not_two_dvd_index_utSub [Finite K] : ¬ 2 ∣ (utSub K).index := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hq⟩ := FiniteField.card K 2
  have h := (utSub K).card_mul_index
  rw [card_utSub, Matrix.card_GL_field, Fin.prod_univ_three, Nat.card_eq_fintype_card] at h
  simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one] at h
  set q := Fintype.card K with hqdef
  have hq1 : 1 ≤ q := Fintype.card_pos
  have hqe : Even q := by
    rw [hq]
    exact (Nat.even_pow' n.pos.ne').mpr even_two
  have e1 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ hq1
  have e2 : q ≤ q ^ 3 := Nat.le_self_pow (by norm_num) q
  have e3 : q ^ 2 ≤ q ^ 3 := Nat.pow_le_pow_right hq1 (by norm_num)
  have e4 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq1
  have hidx : (utSub K).index = (q ^ 3 - 1) * (q ^ 2 - 1) * (q - 1) := by
    apply Nat.eq_of_mul_eq_mul_left (pow_pos hq1 3)
    rw [h]
    zify [e1, e2, e3, e4, hq1]
    ring
  have hodd : ∀ k : ℕ, 1 ≤ k → Odd (q ^ k - 1) := by
    intro k hk
    have hke : Even (q ^ k) := (Nat.even_pow' (by omega)).mpr hqe
    exact Nat.Even.sub_odd (Nat.one_le_pow _ _ hq1) hke odd_one
  rw [hidx, ← even_iff_two_dvd, Nat.not_even_iff_odd]
  refine Odd.mul (Odd.mul (hodd 3 (by norm_num)) (hodd 2 (by norm_num))) ?_
  simpa using hodd 1 le_rfl

theorem exists_conj_mem_utSub [Finite K] (P : Subgroup (GL (Fin 3) K)) (hP : IsPGroup 2 P) :
    ∃ B : GL (Fin 3) K, ∀ p ∈ P, B⁻¹ * p * B ∈ utSub K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (GL (Fin 3) K)
    (isPGroup_utSub.toSylow not_two_dvd_index_utSub) S
  refine ⟨g, fun p hp => ?_⟩
  have hp' : p ∈ ((g • isPGroup_utSub.toSylow not_two_dvd_index_utSub :
      Sylow 2 (GL (Fin 3) K)) : Subgroup (GL (Fin 3) K)) := by
    rw [hg]
    exact hS hp
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hp'
  simpa [MulAut.smul_def, MulAut.conj_apply] using hp'

end Sylow

theorem exists_dotProduct_mulVec_ne_zero {J : Subgroup (GL (Fin 3) K)}
    (hirr : KSL3TwoIrrProof.IsIrr J) {a φ : Fin 3 → K} (ha : a ≠ 0) (hφ : φ ≠ 0) :
    ∃ g ∈ J, φ ⬝ᵥ ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ a) ≠ 0 := by
  by_contra h
  push Not at h
  let W : Submodule K (Fin 3 → K) :=
    { carrier := {v | ∀ g ∈ J, φ ⬝ᵥ ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ v) = 0}
      add_mem' := fun {v w} hv hw g hg => by
        rw [Matrix.mulVec_add, dotProduct_add, hv g hg, hw g hg, add_zero]
      zero_mem' := fun g _ => by rw [Matrix.mulVec_zero, dotProduct_zero]
      smul_mem' := fun c v hv g hg => by
        rw [Matrix.mulVec_smul, dotProduct_smul, hv g hg, smul_zero] }
  have hinv : KSL3TwoIrrProof.IsInv J W := by
    intro g hg v hv g' hg'
    rw [Matrix.mulVec_mulVec, ← Units.val_mul]
    exact hv _ (J.mul_mem hg' hg)
  rcases hirr W hinv with hb | ht
  · have haW : a ∈ W := h
    rw [hb, Submodule.mem_bot] at haW
    exact ha haW
  · apply hφ
    funext i
    have hi : (Pi.single i 1 : Fin 3 → K) ∈ W := ht ▸ Submodule.mem_top
    have := hi 1 J.one_mem
    rw [Units.val_one, Matrix.one_mulVec, dotProduct_single, mul_one] at this
    rw [Pi.zero_apply]
    exact this

theorem exists_genPos_of_center {J : Subgroup (GL (Fin 3) K)} (hirr : KSL3TwoIrrProof.IsIrr J)
    {z t : GL (Fin 3) K} (hz : z ∈ J) (ht : t ∈ J) {a φ φ' : Fin 3 → K} (hzE : IsElat z a φ)
    (htE : IsElat t a φ') (hφ' : ∀ c : K, c • φ ≠ φ') :
    ∃ s ∈ J, ∃ a' ψ : Fin 3 → K, IsElat s a' ψ ∧ φ ⬝ᵥ a' ≠ 0 ∧ ψ ⬝ᵥ a ≠ 0 := by
  obtain ⟨g, hg, hga⟩ := exists_dotProduct_mulVec_ne_zero hirr hzE.1 hzE.2.1
  have hgJ : ∀ x ∈ J, g * x * g⁻¹ ∈ J := fun x hx => J.mul_mem (J.mul_mem hg hx) (J.inv_mem hg)
  by_cases h1 : φ ⬝ᵥ (((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ a) = 0
  · by_cases h2 : φ' ⬝ᵥ (((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ a) = 0
    · exfalso
      have hli : LinearIndependent K ![φ, φ'] := (LinearIndependent.pair_iff' hzE.2.1).mpr hφ'
      obtain ⟨c, hc⟩ :=
        exists_eq_smul_of_dotProduct_eq_zero hli hzE.2.2.1 htE.2.2.1 h1 h2 hzE.1
      have hgw : (g : Matrix (Fin 3) (Fin 3) K) *ᵥ
          (((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ a) = a := by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Matrix.one_mulVec]
      have hac : a = c • ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ a) := by
        rw [← Matrix.mulVec_smul, ← hc, hgw]
      have key : c * (φ ⬝ᵥ ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ a)) = 0 := by
        rw [← smul_eq_mul, ← dotProduct_smul, ← hac]
        exact hzE.2.2.1
      rcases mul_eq_zero.mp key with h0 | h0
      · apply hzE.1
        rw [hac, h0, zero_smul]
      · exact hga h0
    · refine ⟨g * t * g⁻¹, hgJ t ht, _, _, htE.conj g, hga, ?_⟩
      rwa [← Matrix.dotProduct_mulVec]
  · refine ⟨g * z * g⁻¹, hgJ z hz, _, _, hzE.conj g, hga, ?_⟩
    rwa [← Matrix.dotProduct_mulVec]

theorem exists_genPos_of_axis {J : Subgroup (GL (Fin 3) K)} (hirr : KSL3TwoIrrProof.IsIrr J)
    {z t : GL (Fin 3) K} (hz : z ∈ J) (ht : t ∈ J) {a b φ : Fin 3 → K} (hzE : IsElat z a φ)
    (htE : IsElat t b φ) (hb : ∀ c : K, c • a ≠ b) :
    ∃ s ∈ J, ∃ a' ψ : Fin 3 → K, IsElat s a' ψ ∧ φ ⬝ᵥ a' ≠ 0 ∧ ψ ⬝ᵥ a ≠ 0 := by
  obtain ⟨g, hg, hga⟩ := exists_dotProduct_mulVec_ne_zero hirr hzE.1 hzE.2.1
  have hgJ : ∀ x ∈ J, g⁻¹ * x * g⁻¹⁻¹ ∈ J := fun x hx =>
    J.mul_mem (J.mul_mem (J.inv_mem hg) hx) (J.inv_mem (J.inv_mem hg))
  have hψ : (φ ᵥ* ((g⁻¹⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) ⬝ᵥ a ≠ 0 := by
    rwa [inv_inv, ← Matrix.dotProduct_mulVec]
  have hgg : (g : Matrix (Fin 3) (Fin 3) K) * ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hback : ∀ v : Fin 3 → K, (g : Matrix (Fin 3) (Fin 3) K) *ᵥ
      (((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, hgg, Matrix.one_mulVec]
  by_cases h1 : φ ⬝ᵥ (((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ a) = 0
  · by_cases h2 : φ ⬝ᵥ (((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ b) = 0
    · exfalso
      have hha : ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ a ≠ 0 := by
        intro h0
        apply hzE.1
        rw [← hback a, h0, Matrix.mulVec_zero]
      have hli : LinearIndependent K ![((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ a,
          ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ b] := by
        refine (LinearIndependent.pair_iff' hha).mpr fun c hc => hb c ?_
        rw [← hback b, ← hc, Matrix.mulVec_smul, hback a]
      have e3 : (((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ a) ⬝ᵥ
          (φ ᵥ* (g : Matrix (Fin 3) (Fin 3) K)) = 0 := by
        rw [dotProduct_comm, ← Matrix.dotProduct_mulVec, hback a]
        exact hzE.2.2.1
      have e4 : (((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ b) ⬝ᵥ
          (φ ᵥ* (g : Matrix (Fin 3) (Fin 3) K)) = 0 := by
        rw [dotProduct_comm, ← Matrix.dotProduct_mulVec, hback b]
        exact htE.2.2.1
      obtain ⟨c, hc⟩ := exists_eq_smul_of_dotProduct_eq_zero hli
        (by rw [dotProduct_comm]; exact h1) (by rw [dotProduct_comm]; exact h2) e3 e4 hzE.2.1
      apply hga
      rw [Matrix.dotProduct_mulVec, hc, smul_dotProduct, hzE.2.2.1, smul_zero]
    · exact ⟨g⁻¹ * t * g⁻¹⁻¹, hgJ t ht, _, _, htE.conj g⁻¹, h2, hψ⟩
  · exact ⟨g⁻¹ * z * g⁻¹⁻¹, hgJ z hz, _, _, hzE.conj g⁻¹, h1, hψ⟩

theorem exists_genPos [CharP K 2] {J : Subgroup (GL (Fin 3) K)} (hirr : KSL3TwoIrrProof.IsIrr J)
    {z : GL (Fin 3) K} (hz : z ∈ J) {a φ : Fin 3 → K} (hzE : IsElat z a φ) :
    ∃ s ∈ J, ∃ a' ψ : Fin 3 → K, IsElat s a' ψ ∧ φ ⬝ᵥ a' ≠ 0 ∧ ψ ⬝ᵥ a ≠ 0 := by
  by_contra hno
  have hzE' := hzE
  obtain ⟨ha, hφ, hφa, hzm⟩ := hzE'
  have hzz : z * z = 1 := hzE.mul_self
  have hT : ∀ s ∈ J, s * s = 1 → s ≠ 1 →
      ∃ c : K, (s : Matrix (Fin 3) (Fin 3) K) = 1 + vecMulVec a (c • φ) := by
    intro s hs hss hs1
    obtain ⟨b, ψ, hsE⟩ := exists_isElat_of_mul_self hss hs1
    have hsE' := hsE
    obtain ⟨hb0, hψ0, hψb, hsm⟩ := hsE'
    by_cases hφb : φ ⬝ᵥ b = 0
    · by_cases hψa : ψ ⬝ᵥ a = 0
      ·
        have h1 : z * s * (z * s) = 1 := by
          apply Units.ext
          simp only [Units.val_mul, Units.val_one]
          rw [hzm, hsm, sq_mul_of_dotProduct_eq_zero hφa hψb hφb, hψa, zero_smul,
            vecMulVec_zero, add_zero]
        have h2 : z * s * (s * z) = 1 := by
          rw [mul_assoc, ← mul_assoc s s z, hss, one_mul, hzz]
        have hcomm : z * s = s * z := mul_left_cancel (h1.trans h2.symm)
        rcases IsElat.center_or_axis_of_commute hzE hsE hcomm with ⟨c, hc⟩ | ⟨c, hc⟩
        · by_cases hψφ : ∃ d : K, ψ = d • φ
          · obtain ⟨d, hd⟩ := hψφ
            exact ⟨c * d, by rw [hsm, hc, hd, smul_vecMulVec, vecMulVec_smul, vecMulVec_smul,
              mul_smul]⟩
          · exfalso
            have hc0 : c ≠ 0 := by
              rintro rfl
              exact hb0 (by rw [hc, zero_smul])
            apply hno
            refine exists_genPos_of_center hirr hz hs hzE
              ⟨ha, smul_ne_zero hc0 hψ0, by rw [smul_dotProduct, hψa, smul_zero], ?_⟩ ?_
            · rw [hsm, hc, smul_vecMulVec, vecMulVec_smul]
            · intro d hd
              apply hψφ
              refine ⟨c⁻¹ * d, ?_⟩
              rw [mul_smul, hd, smul_smul, inv_mul_cancel₀ hc0, one_smul]
        · by_cases hba : ∃ d : K, b = d • a
          · obtain ⟨d, hd⟩ := hba
            exact ⟨d * c, by rw [hsm, hc, hd, smul_vecMulVec, vecMulVec_smul, vecMulVec_smul,
              mul_smul]⟩
          · exfalso
            have hc0 : c ≠ 0 := by
              rintro rfl
              exact hψ0 (by rw [hc, zero_smul])
            apply hno
            refine exists_genPos_of_axis hirr hz hs hzE
              ⟨smul_ne_zero hc0 hb0, hφ, by rw [dotProduct_smul, hφb, smul_zero], ?_⟩ ?_
            · rw [hsm, hc, vecMulVec_smul, smul_vecMulVec]
            · intro d hd
              apply hba
              refine ⟨c⁻¹ * d, ?_⟩
              rw [mul_smul, hd, smul_smul, inv_mul_cancel₀ hc0, one_smul]
      ·
        exfalso
        apply hno
        have hba : ∀ d : K, d • a ≠ (ψ ⬝ᵥ a) • b := by
          intro d hd
          have h1 := congrArg (fun v => ψ ⬝ᵥ v) hd
          simp only [dotProduct_smul, smul_eq_mul, hψb, mul_zero] at h1
          have hd0 : d = 0 := (mul_eq_zero.mp h1).resolve_right hψa
          rw [hd0, zero_smul] at hd
          exact smul_ne_zero hψa hb0 hd.symm
        have hwE : IsElat (z * s * (z * s)) ((ψ ⬝ᵥ a) • b) φ := by
          refine ⟨smul_ne_zero hψa hb0, hφ, by rw [dotProduct_smul, hφb, smul_zero], ?_⟩
          simp only [Units.val_mul]
          rw [hzm, hsm, sq_mul_of_dotProduct_eq_zero hφa hψb hφb, vecMulVec_smul, smul_vecMulVec]
        exact exists_genPos_of_axis hirr hz (J.mul_mem (J.mul_mem hz hs) (J.mul_mem hz hs)) hzE
          hwE hba
    · by_cases hψa : ψ ⬝ᵥ a = 0
      ·
        exfalso
        apply hno
        have hψφ : ∀ d : K, d • φ ≠ (φ ⬝ᵥ b) • ψ := by
          intro d hd
          have h1 := congrArg (fun v => v ⬝ᵥ b) hd
          simp only [smul_dotProduct, smul_eq_mul, hψb, mul_zero] at h1
          have hd0 : d = 0 := (mul_eq_zero.mp h1).resolve_right hφb
          rw [hd0, zero_smul] at hd
          exact smul_ne_zero hφb hψ0 hd.symm
        have hwE : IsElat (s * z * (s * z)) a ((φ ⬝ᵥ b) • ψ) := by
          refine ⟨ha, smul_ne_zero hφb hψ0, by rw [smul_dotProduct, hψa, smul_zero], ?_⟩
          simp only [Units.val_mul]
          rw [hzm, hsm, sq_mul_of_dotProduct_eq_zero hψb hφa hψa]
        exact exists_genPos_of_center hirr hz (J.mul_mem (J.mul_mem hs hz) (J.mul_mem hs hz)) hzE
          hwE hψφ
      · exact absurd ⟨s, hs, b, ψ, hsE, hφb, hψa⟩ hno
  have hline : ∀ g ∈ J, ∃ d : K, (g : Matrix (Fin 3) (Fin 3) K) *ᵥ a = d • a := by
    intro g hg
    have hgE := hzE.conj g
    obtain ⟨c, hc⟩ := hT (g * z * g⁻¹) (J.mul_mem (J.mul_mem hg hz) (J.inv_mem hg)) hgE.mul_self
      hgE.ne_one
    have heq : vecMulVec a (c • φ) = vecMulVec ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ a)
        (φ ᵥ* ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) :=
      add_left_cancel (hc.symm.trans hgE.2.2.2)
    have hcφ : c • φ ≠ 0 := by
      intro h0
      rw [h0, vecMulVec_zero] at heq
      rcases vecMulVec_eq_zero.mp heq.symm with h | h
      · exact hgE.1 h
      · exact hgE.2.1 h
    exact exists_eq_smul_of_vecMulVec_eq ha hcφ heq
  have hinv : KSL3TwoIrrProof.IsInv J (K ∙ a) := by
    intro g hg v hv
    obtain ⟨e, rfl⟩ := Submodule.mem_span_singleton.mp hv
    obtain ⟨d, hd⟩ := hline g hg
    rw [Matrix.mulVec_smul, hd, smul_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self a)
  rcases hirr _ hinv with hb | ht
  · exact ha (Submodule.span_singleton_eq_bot.mp hb)
  · apply hφ
    funext i
    have hi : (Pi.single i 1 : Fin 3 → K) ∈ K ∙ a := ht ▸ Submodule.mem_top
    obtain ⟨e, he⟩ := Submodule.mem_span_singleton.mp hi
    have := congrArg (fun v => φ ⬝ᵥ v) he
    simp only [dotProduct_smul, hφa, smul_zero, dotProduct_single, mul_one] at this
    rw [Pi.zero_apply]
    exact this.symm

theorem exists_isElat_of_isZUT {u B : GL (Fin 3) K}
    (h : IsZUT ((B⁻¹ * u * B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) (hu : u ≠ 1) :
    ∃ c : K, c ≠ 0 ∧ ((B⁻¹ * u * B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = utm 0 0 c ∧
      IsElat u ((B : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single 0 1)
        (![0, 0, c] ᵥ* ((B⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
  obtain ⟨hUT, h01, h12⟩ := h
  set M := B⁻¹ * u * B with hM
  have hMeq : (M : Matrix (Fin 3) (Fin 3) K) = utm 0 0 ((M : Matrix (Fin 3) (Fin 3) K) 0 2) := by
    conv_lhs => rw [hUT.eq_utm]
    rw [h01, h12]
  set c := (M : Matrix (Fin 3) (Fin 3) K) 0 2 with hc
  have hBM : B * M * B⁻¹ = u := by
    rw [hM]
    group
  have hc0 : c ≠ 0 := by
    intro h0
    apply hu
    have hM1 : M = 1 := Units.ext (by rw [hMeq, h0, utm_zero, Units.val_one])
    rw [← hBM, hM1, mul_one, mul_inv_cancel]
  have hME : IsElat M (Pi.single 0 1) ![0, 0, c] := by
    refine ⟨Pi.single_ne_zero_iff.mpr one_ne_zero, ?_, by simp, ?_⟩
    · intro h0
      have := congrFun h0 2
      simp only [Matrix.cons_val, Pi.zero_apply] at this
      exact hc0 this
    · rw [hMeq, utm_eq_elat_col]
  refine ⟨c, hc0, hMeq, ?_⟩
  have := hME.conj B
  rwa [hBM] at this

theorem ksl3TwoIrrSimpleNonab : KSL3TwoIrrSimpleNonab := by
  intro K _ _ _ J hirr hsimp P hP
  by_contra h3
  obtain ⟨B, hB⟩ := exists_conj_mem_utSub (K := K) ((P : Subgroup ↥J).map J.subtype)
    (P.isPGroup'.map J.subtype)
  set ρ : ↥J →* GL (Fin 3) K := (MulAut.conj B⁻¹).toMonoidHom.comp J.subtype with hρdef
  have hρ : ∀ j : ↥J, ρ j = B⁻¹ * (j : GL (Fin 3) K) * B := fun j => by
    simp [hρdef]
  have hρinj : Function.Injective ρ :=
    (MulAut.conj B⁻¹).injective.comp J.subtype_injective
  refine false_of_unitriangular h3 ρ hρinj P hP (fun p hp => ?_) (fun u v hu hv hu1 hv1 => ?_)
  · rw [hρ]
    exact hB _ ⟨p, hp, rfl⟩
  · rw [hρ] at hu hv
    have hu1' : (u : GL (Fin 3) K) ≠ 1 := fun h => hu1 (Subtype.ext h)
    have hv1' : (v : GL (Fin 3) K) ≠ 1 := fun h => hv1 (Subtype.ext h)
    obtain ⟨c₁, hc₁, hMu, huE⟩ := exists_isElat_of_isZUT hu hu1'
    obtain ⟨c₂, -, hMv, hvE⟩ := exists_isElat_of_isZUT hv hv1'
    obtain ⟨s, hs, a', ψ, hsE, h1, h2⟩ := exists_genPos hirr u.2 huE
    have hφ : (![0, 0, c₂] : Fin 3 → K) ᵥ* ((B⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        (c₂ / c₁) • ((![0, 0, c₁] : Fin 3 → K) ᵥ*
          ((B⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
      rw [← Matrix.smul_vecMul]
      congr 1
      ext i
      fin_cases i <;> simp [div_mul_cancel₀ _ hc₁]
    rw [hφ] at hvE
    have hc := eq_one_of_elat_triple h3 u.2 v.2 hs huE hvE hsE h1 h2
    have hc12 : c₂ = c₁ := (div_eq_one_iff_eq hc₁).mp hc
    apply hρinj
    apply Units.ext
    rw [hρ, hρ, hMu, hMv, hc12]

theorem ksl3TwoIrrPerfect :
    KSL3TwoIrrPerfect :=
  ksl3TwoIrrPerfect_of_simpleNonab ksl3TwoIrrSimpleNonab

theorem ksl3TwoIrrThree :
    KSL3TwoIrrThree :=
  ksl3TwoIrrThree_of ksl3TwoIrrPerfect

end KL3SubProof

end CFSG.RankThree.PartTwo.Sec16
