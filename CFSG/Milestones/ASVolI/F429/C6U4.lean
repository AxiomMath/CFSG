module

public import CFSG.Milestones.ASVolI.F429.C6U4Mat
public import CFSG.Milestones.ASVolI.F429.aR5

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin
open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.Quasithin.H13.U4Par CFSG.Quasithin.H13.Sec53F.Unit

section Field

variable {m : ℕ} {K : Type} [Field K] [Finite K] (h : UnitaryFieldData 2 m K)

include h in
theorem burnsideF429_U4_card_fix_le {σ : K ≃+* K} (hσ : σ ≠ 1) :
    Nat.card {a : K // σ a = a} ≤ 2 ^ m := by
  let k : Subfield K := (σ : K →+* K).eqLocusField (RingHom.id K)
  have hk : k ≠ ⊤ := by
    intro htop
    apply hσ
    refine RingEquiv.ext fun x => ?_
    have hx : x ∈ k := by rw [htop]; exact Subfield.mem_top x
    exact hx
  have hcard : Nat.card {a : K // σ a = a} = Nat.card k :=
    Nat.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)
  have hsq := CFSG.Quasithin.H13.F431.SpOut2.card_sq_le_of_ne_top k hk
  rw [h.card, hcard.symm] at hsq
  by_contra hlt
  push Not at hlt
  have : (2 ^ m) ^ 2 < Nat.card {a : K // σ a = a} ^ 2 := Nat.pow_lt_pow_left hlt (by norm_num)
  have e : (2 ^ m) ^ 2 = 2 ^ (2 * m) := by ring
  omega

theorem burnsideF429_U4_card_fix_cube {σ : K ≃+* K} (hσ : σ ≠ 1) :
    Nat.card {a : K // barEquiv h a = a} * Nat.card {a : K // σ a = a} *
      Nat.card {a : K // barEquiv h a = a} ≤ (2 ^ m) ^ 3 := by
  have h1 := burnsideF429_U4_card_barFix_le h
  have h2 := burnsideF429_U4_card_fix_le h hσ
  calc _ ≤ 2 ^ m * 2 ^ m * 2 ^ m := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h1
    _ = (2 ^ m) ^ 3 := by ring

end Field

section Model

variable {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem burnsideF429_U4_borel_entries {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K)
    {g : hypSU h 2 0}
    (hg : g ∈ Subgroup.normalizer (hypUnitriangular h 2 0 : Set (hypSU h 2 0))) :
    ((g : GL Ix K) : Matrix Ix Ix K) ie2 ie1 = 0 ∧ ((g : GL Ix K) : Matrix Ix Ix K) ie1 ie1 ≠ 0 ∧
      ((g : GL Ix K) : Matrix Ix Ix K) ie2 ie2 ≠ 0 := by
  have hB := burnsideF429a_U4_normalizer_le_borel h hg
  have h21 : ((g : GL Ix K) : Matrix Ix Ix K) ie2 ie1 = 0 :=
    (mem_parP_iff h g).mp hB.1 ie2 (by simp)
  have hrho : rho2 h g * rho2 h g⁻¹ = 1 := by
    rw [← rho2_mul h ((parP2 h).inv_mem hB.2), mul_inv_cancel, rho2_one]
  have hdet := congrArg Matrix.det hrho
  rw [Matrix.det_mul, Matrix.det_one] at hdet
  have hne : (rho2 h g).det ≠ 0 := left_ne_zero_of_mul_eq_one hdet
  rw [rho2, Matrix.det_fin_two_of, h21, mul_zero, sub_zero] at hne
  exact ⟨h21, left_ne_zero_of_mul hne, right_ne_zero_of_mul hne⟩


theorem burnsideF429_c6_U4 {f : ℕ} (hyp : HypF_4_4 .U4 2 f Gp M₁ M₂) (hf : 2 ≤ f)
    {T : Subgroup E} (hT : ChF.IsSylowOf 2 T (M₁ ⊓ M₂)) : burnsideF429_C6 .U4 f Gp M₁ M₂ T := by
  haveI := hyp.finite
  haveI := hyp.normal
  obtain ⟨marking, e1, e2⟩ := burnsideF4g_marking (c := .U4) hyp.toHypF_4_4g
  obtain ⟨Φ, hΦ1, hΦ2⟩ := burnsideF4gU4_exists_equiv marking
  generalize burnsideF4gU4_fieldData marking = h at Φ hΦ1 hΦ2
  haveI : Finite marking.field := h.finite
  haveI : CharP marking.field 2 := h.charP
  haveI : Finite (hypSU h 2 0) := CFSG.Quasithin.H13.U4Par.finite_hypSU h
  have hP₁ : M₁.subgroupOf Gp = (parP h).map Φ.toMonoidHom := e1.trans hΦ1
  have hP₂ : M₂.subgroupOf Gp = (parP2 h).map Φ.toMonoidHom := e2.trans hΦ2
  set φ : hypSU h 2 0 →* E := Gp.subtype.comp Φ.toMonoidHom with hφdef
  have hφ : Function.Injective φ := Gp.subtype_injective.comp Φ.injective
  have hφx : ∀ x, φ x = ((Φ x : ↥Gp) : E) := fun x => rfl
  have hB : (M₁ ⊓ M₂).subgroupOf Gp = (parP h ⊓ parP2 h).map Φ.toMonoidHom := by
    rw [burnsideF429a_subgroupOf_inf, hP₁, hP₂, Subgroup.map_inf_eq _ _ _ Φ.injective]
  have hGB : Gp ⊓ (M₁ ⊓ M₂) = (parP h ⊓ parP2 h).map φ := burnsideF429_inf_eq_map Φ hB
  have hS : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) = (hypUnitriangular h 2 0).map φ := by
    rw [hGB, CFSG.Quasithin.H13.U4Par.pCoreOf_map_of_inj hφ, burnsideF4gU4Inv_pCore_borel]
  have hTG := burnsideF429_T_inf_Gp hyp hT
  have hST := burnsideF429_sbar_le (Gp := Gp) hT
  have hq4 := burnsideF429_U4_card_q2_ge h
  have hm1 : 1 ≤ f := le_trans (by norm_num) hf
  have hK : Nat.card marking.field = 2 ^ (2 * f) := h.card
  have hnf : ∀ e ∈ M₁ ⊓ M₂, ∃ g ∈ Subgroup.normalizer (hypUnitriangular h 2 0 :
      Set (hypSU h 2 0)), ∃ τ : marking.field ≃+* marking.field,
      ∀ x, ((Φ (g * fieldAut h τ x * g⁻¹) : ↥Gp) : E) = e * ((Φ x : ↥Gp) : E) * e⁻¹ :=
    fun e he => burnsideF429a_U4_nf h Φ hP₁ hP₂ he
  have hfA : ∀ σ τ : marking.field ≃+* marking.field,
      fieldAut h (σ * τ) = fieldAut h σ * fieldAut h τ :=
    fun σ τ => (fieldAutHom h 2 0).map_mul σ τ
  have hinv : ∀ t : E, t ∉ Gp → t * t = 1 → ∀ g : hypSU h 2 0, ∀ τ : marking.field ≃+* marking.field,
      (∀ x, ((Φ (g * fieldAut h τ x * g⁻¹) : ↥Gp) : E) = t * ((Φ x : ↥Gp) : E) * t⁻¹) →
      τ ≠ 1 ∧ τ * τ = 1 ∧ ∀ c, τ c = h.bar c := by
    intro t htG htt g τ hgt
    have hβ : ∀ x, ((Φ ((MulAut.conj g * fieldAut h τ : MulAut (hypSU h 2 0)) x) : ↥Gp) : E) =
        t * ((Φ x : ↥Gp) : E) * t⁻¹ := fun x => hgt x
    have hτ1 : τ ≠ 1 := by
      intro h1
      apply htG
      have e : ∀ x, ((Φ (g * x * g⁻¹) : ↥Gp) : E) = t * ((Φ x : ↥Gp) : E) * t⁻¹ := by
        intro x
        have := hgt x
        rwa [h1, fieldAut_apply, fieldHom_one] at this
      rw [burnsideF429a_eq_of_conj hyp.centralizer_trivial Φ e]
      exact (Φ g).2
    have hβ2 : (MulAut.conj g * fieldAut h τ : MulAut (hypSU h 2 0)) ^ 2 = 1 :=
      burnsideF429a_pow_eq_one_of_intertwine Φ hβ (n := 2) (by rw [pow_two]; exact htt)
    have hττ : τ * τ = 1 := by
      rw [pow_two, burnsideF429_conj_mul_conj, ← hfA] at hβ2
      refine burnsideF429a_U4_fieldAut_eq_one_of_inner h ⟨(g * fieldAut h τ g)⁻¹, ?_⟩
      rw [map_inv]
      exact (eq_inv_of_mul_eq_one_right hβ2).symm
    obtain ⟨-, hτc⟩ := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.even_and_eq_pow_of_involution
      (by omega : 1 ≤ 2 * f) hK hτ1 hττ
    refine ⟨hτ1, hττ, fun c => ?_⟩
    rw [hτc c, h.bar_apply]
    congr 2
    omega
  have hR : CFSG.Open.IsElemAbelian 2 ((radQ2 h).map φ) :=
    (burnsideF429_U4_isElemAbelian_q2 h).map φ
  have hRS : (radQ2 h).map φ ≤ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) := by
    rw [hS]
    exact Subgroup.map_mono (burnsideF429_U4_q2_le_U h)
  have hcardR : Nat.card ((radQ2 h).map φ) = Nat.card (radQ2 h) :=
    Subgroup.card_map_of_injective hφ
  have hq3 : (2 ^ f) ^ 3 < (2 ^ f) ^ 4 := Nat.pow_lt_pow_right (by
    calc 1 < 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hm1) (by norm_num)
  refine burnsideF429_c6_of_unique hST hRS hR ?_ ?_ ?_
  ·
    intro B hBS hBe
    have hBr : B ≤ φ.range := (hBS.trans hS.le).trans (Subgroup.map_le_range φ _)
    have hBB : (B.comap φ).map φ = B := Subgroup.map_comap_eq_self hBr
    have hB'U : B.comap φ ≤ hypUnitriangular h 2 0 := fun g hg =>
      (Subgroup.mem_map_iff_mem hφ).mp (by rw [← hS]; exact hBS hg)
    have hB'e : CFSG.Open.IsElemAbelian 2 (B.comap φ) := burnsideF429_isElemAbelian_comap hφ hBe
    by_cases hBQ : B.comap φ ≤ radQ2 h
    · left
      rw [← hBB]
      exact Subgroup.map_mono hBQ
    · right
      rw [← hBB, Subgroup.card_map_of_injective hφ, hcardR]
      exact lt_of_le_of_lt (burnsideF429_U4_card_elemAb_le h hB'U hB'e hBQ) (lt_of_lt_of_le hq3 hq4)
  ·
    intro A hAT hAe hAS
    obtain ⟨t, htA, htS⟩ := SetLike.not_le_iff_exists.mp hAS
    have htT := hAT htA
    have htt : t * t = 1 := by rw [← pow_two]; exact hAe.2 t htA
    have htG : t ∉ Gp := fun h' => htS (by rw [← hTG]; exact ⟨htT, h'⟩)
    have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := isMulCommutative_iff_of_setLike.mp hAe.1
    obtain ⟨g, hg, τ, hgt⟩ := hnf t (hT.1 htT)
    obtain ⟨hτ1, hττ, hτbar⟩ := hinv t htG htt g τ hgt
    have hsplit : ∀ a ∈ A, a ∉ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) →
        t * a ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) := by
      intro a haA haS
      have haa : a * a = 1 := by rw [← pow_two]; exact hAe.2 a haA
      have haG : a ∉ Gp := fun h' => haS (by rw [← hTG]; exact ⟨hAT haA, h'⟩)
      obtain ⟨g', -, τ', hga⟩ := hnf a (hT.1 (hAT haA))
      obtain ⟨-, -, hτ'bar⟩ := hinv a haG haa g' τ' hga
      have hττ' : τ' = τ := RingEquiv.ext fun c => by rw [hτ'bar, hτbar]
      have hconj : ∀ x, ((Φ ((g * fieldAut h τ g') * x * (g * fieldAut h τ g')⁻¹) : ↥Gp) : E) =
          (t * a) * ((Φ x : ↥Gp) : E) * (t * a)⁻¹ := by
        intro x
        have e : (g * fieldAut h τ g') * x * (g * fieldAut h τ g')⁻¹ =
            g * fieldAut h τ (g' * fieldAut h τ x * g'⁻¹) * g⁻¹ := by
          rw [map_mul, map_mul, map_inv, ← MulAut.mul_apply, ← hfA, hττ]
          show g * fieldAut h τ g' * x * (g * fieldAut h τ g')⁻¹ =
            g * (fieldAut h τ g' * fieldHom h 1 x * (fieldAut h τ g')⁻¹) * g⁻¹
          rw [fieldHom_one]
          group
        rw [e, hgt, ← hττ', hga]
        group
      have hta : t * a ∈ Gp := by
        rw [burnsideF429a_eq_of_conj hyp.centralizer_trivial Φ hconj]
        exact (Φ _).2
      rw [← hTG]
      exact ⟨T.mul_mem htT (hAT haA), hta⟩
    have hcardA := burnsideF429_card_le_two_mul_of htA htt hsplit
    set X : Subgroup E := A ⊓ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) with hXdef
    have hX : Nat.card X ≤ (2 ^ f) ^ 3 := by
      have hXr : X ≤ φ.range := (inf_le_right.trans hS.le).trans (Subgroup.map_le_range φ _)
      have hXX : (X.comap φ).map φ = X := Subgroup.map_comap_eq_self hXr
      have hX'U : X.comap φ ≤ hypUnitriangular h 2 0 := fun y hy =>
        (Subgroup.mem_map_iff_mem hφ).mp (by rw [← hS]; exact hy.2)
      have hX'e : CFSG.Open.IsElemAbelian 2 (X.comap φ) :=
        burnsideF429_isElemAbelian_comap hφ (hAe.mono inf_le_left)
      rw [← hXX, Subgroup.card_map_of_injective hφ]
      by_cases hXQ : X.comap φ ≤ radQ2 h
      · obtain ⟨h21, h11, h22⟩ := burnsideF429_U4_borel_entries h hg
        have hfix : ∀ y ∈ X.comap φ, g * fieldAut h τ y * g⁻¹ = y := by
          intro y hy
          apply hφ
          rw [hφx, hgt, ← hφx, hAcomm t htA _ hy.1, mul_inv_cancel_right]
        exact (burnsideF429_U4_card_fix_q2 h g h21 h11 h22 τ hXQ hfix).trans
          (burnsideF429_U4_card_fix_cube h hτ1)
      · exact burnsideF429_U4_card_elemAb_le h hX'U hX'e hXQ
    rw [hcardR]
    calc Nat.card A ≤ 2 * Nat.card X := hcardA
      _ ≤ 2 * (2 ^ f) ^ 3 := Nat.mul_le_mul_left 2 hX
      _ < (2 ^ f) ^ 4 := by
        have h4 : 4 ≤ 2 ^ f := by
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
        have e : (2 ^ f) ^ 4 = (2 ^ f) * (2 ^ f) ^ 3 := by ring
        rw [e]
        have hpos : 0 < (2 ^ f) ^ 3 := by positivity
        nlinarith
      _ ≤ Nat.card (radQ2 h) := hq4
  ·
    rintro r ⟨hrT, hrc⟩
    obtain ⟨g, hg, τ, hgr⟩ := hnf r (hT.1 hrT)
    obtain ⟨h21, h11, h22⟩ := burnsideF429_U4_borel_entries h hg
    have hfix : ∀ y ∈ radQ2 h, g * fieldAut h τ y * g⁻¹ = y := by
      intro y hy
      apply hφ
      have hc := Subgroup.mem_centralizer_iff.mp hrc (φ y) ⟨y, hy, rfl⟩
      rw [hφx, hgr, ← hφx, ← hc, mul_inv_cancel_right]
    have hτ : τ = 1 := by
      by_contra hτ1
      have := (burnsideF429_U4_card_fix_q2 h g h21 h11 h22 τ le_rfl hfix).trans
        (burnsideF429_U4_card_fix_cube h hτ1)
      omega
    have e : ∀ x, ((Φ (g * x * g⁻¹) : ↥Gp) : E) = r * ((Φ x : ↥Gp) : E) * r⁻¹ := by
      intro x
      have := hgr x
      rwa [hτ, fieldAut_apply, fieldHom_one] at this
    have hrG : r ∈ Gp := by
      rw [burnsideF429a_eq_of_conj hyp.centralizer_trivial Φ e]
      exact (Φ g).2
    rw [← hTG]
    exact ⟨hrT, hrG⟩

end Model

end CFSG.ASVolI
