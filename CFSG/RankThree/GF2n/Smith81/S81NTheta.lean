module

public import CFSG.RankThree.GF2n.Smith81.S81NSet

public section

namespace CFSG.RankThree.GF2n.Smith81.E3LCond

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G] {M Q Z X : Subgroup G} {x : G} {K : Type} [Field K] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ}


section Theta
variable [Finite G] [CharP K 2]

theorem theta_surj_of_root (hD : GlobalModelData M Q Z γ M₀) (hs : Sit M Q Z X x) (Tx : XAct M₀ x)
    {A : Subgroup G} (hA : IsZConjugate Z A) (hAQ : A ≤ Q) (hAZ : A ≠ Z) {a : G} (haA : a ∈ A)
    (haC : M₀.π a ∈ Cs Tx) (ha1 : ⁅a, x⁆ ≠ 1) : CaseI Q Z x := by
  have H := hs.hyp
  have h12 := smith_1_12 hs
  have hxZ := hs.x_cent h12
  have hZQ : Z ≤ Q := H.Z_normal.1
  have haQ : a ∈ Q := hAQ haA
  have haZ : a ∉ Z := by
    intro haZ
    apply ha1
    have h1 : x * a = a * x := mul_inv_eq_iff_eq_mul.mp (hxZ a haZ)
    exact commutatorElement_eq_one_iff_mul_comm.mpr h1.symm
  have hvZ : ⁅a, x⁆ ∈ Z := (comm_mem_Z_iff hs Tx haQ).mpr haC
  obtain ⟨g, rfl⟩ := hA
  have hΓ : IsZConjugate Z (conjSubgroup g Z) := ⟨g, rfl⟩
  obtain ⟨b, -, hline⟩ := hD.line g hAZ hAQ
  obtain ⟨s₀, hs₀⟩ := (hline _).mp (M₀.pi_mem_img haA haQ)
  have hs₀0 : s₀ ≠ 0 := by
    rintro rfl
    apply haZ
    exact (M₀.π_ker a haQ).mp (by rw [hs₀, zero_smul])
  have hTb : Tx.T b = b := by
    have h1 : s₀ • Tx.T b = s₀ • b := by
      rw [← map_smul, ← hs₀, mem_Cs.mp haC]
    exact smul_right_injective _ hs₀0 h1
  have hTΓ : ∀ γ' ∈ conjSubgroup g Z, ⁅γ', x⁆ ∈ Z := by
    intro γ' hγ'
    obtain ⟨s', hs'⟩ := (hline _).mp (M₀.pi_mem_img hγ' (hAQ hγ'))
    refine (comm_mem_Z_iff hs Tx (hAQ hγ')).mpr ?_
    rw [mem_Cs, hs', map_smul, hTb]
  let ψ : ↥(conjSubgroup g Z) →* ↥Z :=
    { toFun := fun γ' => ⟨⁅(γ' : G), x⁆, hTΓ γ' γ'.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun γ₁ γ₂ => Subtype.ext (by
        show ⁅((γ₁ * γ₂ : ↥(conjSubgroup g Z)) : G), x⁆ = ⁅(γ₁ : G), x⁆ * ⁅(γ₂ : G), x⁆
        rw [Subgroup.coe_mul, comm_mul hs (hAQ γ₁.2) (hTΓ γ₂ γ₂.2)]
        exact Z_central H (hTΓ γ₂ γ₂.2) (hZQ (hTΓ γ₁ γ₁.2))) }
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro γ₁ hγ₁
    have h1 : ⁅(γ₁ : G), x⁆ = 1 := congrArg Subtype.val hγ₁
    by_contra hne
    have hγ1 : (γ₁ : G) ≠ 1 := fun h => hne (Subtype.ext h)
    have hcomm : Commute x (γ₁ : G) := (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
    have hxN := hΓ.mem_normalizer_of_commute H hγ1 γ₁.2 hcomm
    have hxa : x * a * x⁻¹ ∈ conjSubgroup g Z :=
      (Subgroup.mem_normalizer_iff.mp hxN a).mp haA
    have hinv : ⁅a, x⁆⁻¹ ∈ conjSubgroup g Z := by
      have e : ⁅a, x⁆⁻¹ = (x * a * x⁻¹) * a⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact (conjSubgroup g Z).mul_mem hxa ((conjSubgroup g Z).inv_mem haA)
    have hbot : Z ⊓ conjSubgroup g Z = ⊥ := inf_conjSubgroup_eq_bot_of_isTI H.ti hAZ
    have hmem : ⁅a, x⁆⁻¹ ∈ Z ⊓ conjSubgroup g Z := ⟨Z.inv_mem hvZ, hinv⟩
    rw [hbot, Subgroup.mem_bot, inv_eq_one] at hmem
    exact ha1 hmem
  have hbij : Function.Bijective ψ :=
    Function.Injective.bijective_of_nat_card_le hinj (by rw [hΓ.card_eq])
  unfold CaseI
  intro z hz
  obtain ⟨γ₁, hγ₁⟩ := hbij.2 ⟨z, hz⟩
  exact ⟨γ₁, hAQ γ₁.2, congrArg Subtype.val hγ₁⟩

theorem RootPt.smul (hD : GlobalModelData M Q Z γ M₀) {e : M₀.E} (he : RootPt M₀ e) (s : K) :
    RootPt M₀ (s • e) := by
  unfold RootPt at he ⊢
  rcases he with rfl | ⟨A, hA, hAQ, hAZ, a, haA, rfl⟩
  · exact Or.inl (smul_zero s)
  · obtain ⟨g, rfl⟩ := hA
    obtain ⟨b, -, hline⟩ := hD.line g hAZ hAQ
    obtain ⟨t, ht⟩ := (hline _).mp (M₀.pi_mem_img haA (hAQ haA))
    have hmem : s • M₀.π a ∈ M₀.img (conjSubgroup g Z) :=
      (hline (s • M₀.π a)).mpr ⟨s * t, by rw [ht, smul_smul]⟩
    obtain ⟨a', ha'A, -, ha'π⟩ := (Tim79.QuadModel.mem_img M₀).mp hmem
    exact Or.inr ⟨conjSubgroup g Z, ⟨g, rfl⟩, hAQ, hAZ, a', ha'A, ha'π⟩

theorem theta_dichotomy (hD : GlobalModelData M Q Z γ M₀) (hs : Sit M Q Z X x) (Tx : XAct M₀ x)
    (hP1 : Cs Tx ≤ Submodule.span K {e | e ∈ Cs Tx ∧ RootPt M₀ e}) :
    CaseI Q Z x ∨ CaseII Q Z x := by
  have h12 := smith_1_12 hs
  have hZc : ∀ z ∈ Z, ⁅z, x⁆ = 1 := fun z hz =>
    commutatorElement_eq_one_iff_mul_comm.mpr
      (mul_inv_eq_iff_eq_mul.mp (hs.x_cent h12 z hz)).symm
  by_cases hII : CaseII Q Z x
  · exact Or.inr hII
  left
  have key : ∃ A : Subgroup G, IsZConjugate Z A ∧ A ≤ Q ∧ A ≠ Z ∧
      ∃ a ∈ A, M₀.π a ∈ Cs Tx ∧ ⁅a, x⁆ ≠ 1 := by
    by_contra hno
    apply hII
    have hno' : ∀ A : Subgroup G, IsZConjugate Z A → A ≤ Q → A ≠ Z → ∀ a ∈ A,
        M₀.π a ∈ Cs Tx → ⁅a, x⁆ = 1 := by
      intro A hA hAQ hAZ a haA haC
      by_contra ha1
      exact hno ⟨A, hA, hAQ, hAZ, a, haA, haC, ha1⟩
    have hP : ∀ e ∈ Submodule.span K {e | e ∈ Cs Tx ∧ RootPt M₀ e},
        e ∈ Cs Tx ∧ ∀ (s : K) (q : G), q ∈ Q → M₀.π q = s • e → ⁅q, x⁆ = 1 := by
      intro e he
      induction he using Submodule.span_induction with
      | mem e he =>
        obtain ⟨heC, heR⟩ : e ∈ Cs Tx ∧ RootPt M₀ e := he
        refine ⟨heC, fun s q hq hπq => ?_⟩
        have hsC : s • e ∈ Cs Tx := Submodule.smul_mem _ s heC
        have hR := RootPt.smul hD heR s
        unfold RootPt at hR
        rcases hR with h0 | ⟨A, hA, hAQ, hAZ, a, haA, hπa⟩
        · have hqZ : q ∈ Z := (M₀.π_ker q hq).mp (hπq.trans h0)
          exact hZc q hqZ
        · have haQ : a ∈ Q := hAQ haA
          rw [comm_eq_of_pi_eq hs hq haQ (hπq.trans hπa.symm)]
          exact hno' A hA hAQ hAZ a haA (by rw [hπa]; exact hsC)
      | zero =>
        refine ⟨Submodule.zero_mem _, fun s q hq hπq => ?_⟩
        rw [smul_zero] at hπq
        exact hZc q ((M₀.π_ker q hq).mp hπq)
      | add e₁ e₂ _ _ ih₁ ih₂ =>
        obtain ⟨h₁C, h₁⟩ := ih₁
        obtain ⟨h₂C, h₂⟩ := ih₂
        refine ⟨Submodule.add_mem _ h₁C h₂C, fun s q hq hπq => ?_⟩
        obtain ⟨q₁, hq₁Q, hq₁⟩ := M₀.π_surj (s • e₁)
        obtain ⟨q₂, hq₂Q, hq₂⟩ := M₀.π_surj (s • e₂)
        have hπq' : M₀.π q = M₀.π (q₁ * q₂) := by
          rw [M₀.π_mul q₁ hq₁Q q₂ hq₂Q, hq₁, hq₂, hπq, smul_add]
        have hq₂C : ⁅q₂, x⁆ ∈ Z :=
          (comm_mem_Z_iff hs Tx hq₂Q).mpr (by rw [hq₂]; exact Submodule.smul_mem _ s h₂C)
        rw [comm_eq_of_pi_eq hs hq (Q.mul_mem hq₁Q hq₂Q) hπq', comm_mul hs hq₁Q hq₂C,
          h₁ s q₁ hq₁Q hq₁, h₂ s q₂ hq₂Q hq₂, mul_one]
      | smul c e _ ih =>
        obtain ⟨heC, h⟩ := ih
        refine ⟨Submodule.smul_mem _ c heC, fun s q hq hπq => ?_⟩
        exact h (s * c) q hq (by rw [hπq, smul_smul])
    unfold CaseII
    intro q hq hqZ
    have hpi : M₀.π q ∈ Cs Tx := (comm_mem_Z_iff hs Tx hq).mp hqZ
    exact (hP _ (hP1 hpi)).2 1 q hq (by rw [one_smul])
  obtain ⟨A, hA, hAQ, hAZ, a, haA, haC, ha1⟩ := key
  exact theta_surj_of_root hD hs Tx hA hAQ hAZ haA haC ha1

theorem caseI_of_Qf_ne [Finite K] (hD : GlobalModelData M Q Z γ M₀) (hs : Sit M Q Z X x)
    (Tx : XAct M₀ x) (h : ∃ r ∈ Rs Tx, M₀.Qf r ≠ 0) : CaseI Q Z x := by
  obtain ⟨r, hr, hQr⟩ := h
  unfold CaseI
  intro z hz
  obtain ⟨l, hl0⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (γ z * (M₀.Qf r)⁻¹)
  have hl : l ^ 2 = γ z * (M₀.Qf r)⁻¹ := by
    rw [sq]; exact hl0.symm
  obtain ⟨e, he⟩ := mem_Rs.mp (Submodule.smul_mem (Rs Tx) l hr)
  obtain ⟨d, hdQ, hd⟩ := M₀.π_surj e
  have hyQ : ⁅d, x⁆ ∈ Q := comm_mem_Q hs.hyp hs.memM hdQ
  have hπy : M₀.π ⁅d, x⁆ = (-l) • r := by
    rw [Tx.pi_comm hs.hyp hs.memM hdQ, hd, neg_smul, ← he, neg_sub]
  have hyR : M₀.π ⁅d, x⁆ ∈ Rs Tx := by
    rw [hπy]; exact Submodule.smul_mem (Rs Tx) (-l) hr
  obtain ⟨hyZ, hγ⟩ := gamma_comm_of_mem_Rs hD hs Tx hyQ hyR
  have hγz : γ ⁅⁅d, x⁆, x⁆ = γ z := by
    rw [hγ, hπy, M₀.Qf_smul, neg_sq, hl, mul_assoc, inv_mul_cancel₀ hQr, mul_one]
  exact ⟨⁅d, x⁆, hyQ, GM.eq_of_γ_eq hD hyZ hz hγz⟩

end Theta
end CFSG.RankThree.GF2n.Smith81.E3LCond
