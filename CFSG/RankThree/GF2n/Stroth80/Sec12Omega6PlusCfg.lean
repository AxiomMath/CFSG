module

public import CFSG.RankThree.GF2n.Stroth80.Sec12SecondCases
import CFSG.RankThree.GF2n.Stroth80.Sec12SecondFalse
import CFSG.RankThree.GF2n.Stroth80.Sec12SecondGrp
import CFSG.RankThree.GF2n.Stroth80.Sec12SecondSL2

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {X : Type} [Group X]

@[expose] def SecondCfgCaseE6Four (N B₂ : Subgroup X) : Prop :=
  ¬ IsTIMod (Subgroup.normalizer ((cen N : Subgroup X) : Set X)) N
      (LB (Subgroup.normalizer ((cen N : Subgroup X) : Set X)) N B₂) ∧
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = Nat.card (cen N) ∧
    ∃ φ : ↥(Lgen (Subgroup.normalizer ((cen N : Subgroup X) : Set X))
        (LB (Subgroup.normalizer ((cen N : Subgroup X) : Set X)) N B₂)) →* GL (Fin 4) K,
      φ.range = StatedSL 4 K ∧
      φ.ker = N.subgroupOf (Lgen (Subgroup.normalizer ((cen N : Subgroup X) : Set X))
        (LB (Subgroup.normalizer ((cen N : Subgroup X) : Set X)) N B₂)) ∧
      ∃ V₁ V₂ : Subgroup X, cen N ≤ V₁ ∧ V₁ ≤ N ∧ cen N ≤ V₂ ∧ V₂ ≤ N ∧ V₁ ⊓ V₂ = cen N ∧
        V₁ ⊔ V₂ = N ∧
        SectionAct (ι := Fin 4) K (Lgen (Subgroup.normalizer ((cen N : Subgroup X) : Set X))
          (LB (Subgroup.normalizer ((cen N : Subgroup X) : Set X)) N B₂)) V₁ (cen N) φ
          (fun g => (g : Matrix (Fin 4) (Fin 4) K)) ∧
        SectionAct (ι := Fin 4) K (Lgen (Subgroup.normalizer ((cen N : Subgroup X) : Set X))
          (LB (Subgroup.normalizer ((cen N : Subgroup X) : Set X)) N B₂)) V₂ (cen N) φ
          (fun g => ((g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)ᵀ) ∧
        (∃ x ∈ Subgroup.normalizer ((cen N : Subgroup X) : Set X), conjSubgroup x V₁ = V₂) ∧
        CentDvd (Subgroup.normalizer ((cen N : Subgroup X) : Set X)) N (cen N)
          (Lgen (Subgroup.normalizer ((cen N : Subgroup X) : Set X))
            (LB (Subgroup.normalizer ((cen N : Subgroup X) : Set X)) N B₂))

variable [Finite X]

theorem card_of_sectionAct {n : ℕ} {K : Type} [Field K] [Finite K] {S V Z : Subgroup X}
    {φ : ↥S →* GL (Fin n) K} {act : GL (Fin n) K → Matrix (Fin n) (Fin n) K} (hZV : Z ≤ V)
    (h : SectionAct (ι := Fin n) K S V Z φ act) :
    Nat.card V = Nat.card Z * Nat.card K ^ n := by
  obtain ⟨-, hN, ψ, -⟩ := h
  haveI := hN
  have hq : Nat.card (↥V ⧸ Z.subgroupOf V) = Nat.card K ^ n := by
    rw [Nat.card_congr ψ.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun,
      Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin]
  have hZ : Nat.card (Z.subgroupOf V) = Nat.card Z :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZV).toEquiv
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf V), hq, hZ, mul_comm]


theorem caseVI_four {N B₂ : Subgroup X} (hS : ConfigSatz N) (hW : Width N (cen N) 4)
    (hnTI : ¬ IsTIMod (Subgroup.normalizer ((cen N : Subgroup X) : Set X)) N
      (LB (Subgroup.normalizer ((cen N : Subgroup X) : Set X)) N B₂))
    (hVI : CaseVI (Subgroup.normalizer ((cen N : Subgroup X) : Set X)) N (cen N)
      (Lgen (Subgroup.normalizer ((cen N : Subgroup X) : Set X))
        (LB (Subgroup.normalizer ((cen N : Subgroup X) : Set X)) N B₂))) :
    SecondCfgCaseE6Four N B₂ := by
  obtain ⟨n, K, iF, iK, hK, φ, hφr, hφk, V₁, V₂, hZV₁, hV₁N, hZV₂, hV₂N, hinf, hsup, hact₁,
    hact₂, hx, hCD⟩ := hVI
  have hc₁ := card_of_sectionAct hZV₁ hact₁
  have hc₂ := card_of_sectionAct hZV₂ hact₂
  have hcomm : ∀ x ∈ N, ∀ y ∈ N, ⁅x, y⁆ ∈ cen N := fun x hx y hy =>
    hS.1.toHyp79.comm_mem_V hx hy
  haveI hV₂n : (V₂.subgroupOf N).Normal := by
    refine ⟨fun v hv g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hv ⊢
    have e : ((g * v * g⁻¹ : ↥N) : X) = ⁅(g : X), (v : X)⁆ * (v : X) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
      group
    rw [e]
    exact V₂.mul_mem (hZV₂ (hcomm _ g.2 _ v.2)) hv
  have hsup' : V₁.subgroupOf N ⊔ V₂.subgroupOf N = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hV₁N hV₂N, hsup, Subgroup.subgroupOf_self]
  have hinf' : V₂.subgroupOf N ⊓ V₁.subgroupOf N = (cen N).subgroupOf N := by
    rw [← hinf]
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
    exact And.comm
  have hidx := Subgroup.relIndex_sup_right (H := V₁.subgroupOf N) (K := V₂.subgroupOf N)
  rw [hsup'] at hidx
  have h1 : (V₂.subgroupOf N).relIndex ⊤ * Nat.card (V₂.subgroupOf N) = Nat.card N := by
    rw [Subgroup.relIndex_top_right, mul_comm]
    exact Subgroup.card_mul_index _
  have h2 := Subgroup.relIndex_mul_card (H := V₂.subgroupOf N) (K := V₁.subgroupOf N)
  rw [hinf', hidx.symm] at h2
  have hcN : ∀ {A : Subgroup X}, A ≤ N → Nat.card (A.subgroupOf N) = Nat.card A := fun hA =>
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv
  rw [hcN hV₂N] at h1
  rw [hcN (le_trans hZV₁ hV₁N), hcN hV₁N] at h2
  have hNZ : Nat.card N * Nat.card (cen N) = Nat.card V₁ * Nat.card V₂ := by
    rw [← h1, ← h2]
    ring
  have hq : 2 ≤ Nat.card (cen N) := le_trans (by norm_num) hS.1.q4
  have hN : Nat.card N = Nat.card (cen N) ^ 9 := hW
  rw [hc₁, hc₂, hN, hK] at hNZ
  have hpow : Nat.card (cen N) ^ 10 = Nat.card (cen N) ^ (2 * n + 2) := by
    rw [show 2 * n + 2 = (n + 1) + (n + 1) by ring, pow_add, pow_succ, pow_succ]
    calc Nat.card (cen N) ^ 10 = Nat.card (cen N) ^ 9 * Nat.card (cen N) := by ring
      _ = _ := by rw [hNZ]; ring
  have hn : n = 4 := by
    have := Nat.pow_right_injective hq hpow
    omega
  subst hn
  exact ⟨hnTI, K, iF, iK, hK, φ, hφr, hφk, V₁, V₂, hZV₁, hV₁N, hZV₂, hV₂N, hinf, hsup, hact₁,
    hact₂, hx, hCD⟩


theorem secondCfgCaseE6Four_of_large {N R : Subgroup X} (hS : ConfigSatz N)
    (hW : Width N (cen N) 4) (hgen : StrothGenByBStatement) (hCi : Stroth4iStatement)
    (hNR : N ≤ R) (hRC : R ≤ Subgroup.centralizer ((cen N : Subgroup X) : Set X))
    (hnR : (N.subgroupOf R).Normal) [IsSimpleGroup (↥R ⧸ N.subgroupOf R)]
    (hRn : ∃ x y : ↥R ⧸ N.subgroupOf R, x * y ≠ y * x) {c : ℕ}
    (hRcard : Nat.card (↥R ⧸ N.subgroupOf R) = c)
    (hc1 : Nat.card (cen N) * (Nat.card (cen N) ^ 2 - 1) < c)
    (hc2 : Nat.card (cen N) ^ 3 * (Nat.card (cen N) ^ 6 - 1) < c)
    (hc3 : Nat.card (cen N) ^ 2 * (Nat.card (cen N) ^ 4 - 1) < c) {B₂ : Subgroup X}
    (hc : Ctx (Subgroup.normalizer ((cen N : Subgroup X) : Set X)) N (cen N) B₂) :
    SecondCfgCaseE6Four N B₂ := by
  haveI := hc.normal_Q_in_M
  haveI := hnR
  obtain ⟨a, ha2, haq⟩ := hS.card_cen
  have hqa : ∃ a' : ℕ, 2 ≤ a' ∧ Nat.card (cen N) = 2 ^ a' := ⟨a, ha2, haq⟩
  have hnc : ¬ IsMulCommutative (↥R ⧸ N.subgroupOf R) := fun h => by
    obtain ⟨x, y, hxy⟩ := hRn
    exact hxy (h.is_comm.comm x y)
  have hperf : QuotSat R N (fun Y _ => Group.IsPerfect Y) :=
    ⟨hnR, TauCeti.IsSimpleGroup.isPerfect_of_not_isMulCommutative hnc⟩
  have hQS : N ≤ Lgen (Subgroup.normalizer ((cen N : Subgroup X) : Set X))
      (LB (Subgroup.normalizer ((cen N : Subgroup X) : Set X)) N B₂) :=
    sec39_Q_le_LB.trans (le_Lgen _)
  have hSM := Lgen_le (M := Subgroup.normalizer ((cen N : Subgroup X) : Set X)) hc.LB_le_M
  have hSH := hc.Lgen_le_H0_sec4x
  have hSn := Lgen_normal (M := Subgroup.normalizer ((cen N : Subgroup X) : Set X)) hc.LB_le_M
  have hRM : R ≤ Subgroup.normalizer ((cen N : Subgroup X) : Set X) :=
    hRC.trans (Subgroup.centralizer_le_normalizer _)
  have hRH : R ≤ H0 (Subgroup.normalizer ((cen N : Subgroup X) : Set X)) (cen N) :=
    fun x hx => ⟨hRM hx, hRC hx⟩
  have hq : 2 ≤ Nat.card (cen N) := le_trans (by norm_num) hS.1.q4
  have hinj : ∀ a b : ℕ, Nat.card (cen N) ^ a = Nat.card (cen N) ^ b → a = b :=
    fun a b hab => Nat.pow_right_injective hq hab
  have hN : Nat.card N = Nat.card (cen N) ^ (2 * 4 + 1) := hW
  have hD3 : QuotSat (Lgen (Subgroup.normalizer ((cen N : Subgroup X) : Set X))
        (LB (Subgroup.normalizer ((cen N : Subgroup X) : Set X)) N B₂)) N
        (IsSLModel 2 (Nat.card (cen N) ^ 3)) →
      CentTrivial (Subgroup.normalizer ((cen N : Subgroup X) : Set X)) N (cen N)
        (Lgen (Subgroup.normalizer ((cen N : Subgroup X) : Set X))
          (LB (Subgroup.normalizer ((cen N : Subgroup X) : Set X)) N B₂)) → False := by
    intro hS3 hCT
    have hq3 : ∃ a' : ℕ, 2 ≤ a' ∧ Nat.card (cen N) ^ 3 = 2 ^ a' :=
      ⟨3 * a, by omega, by rw [haq, ← pow_mul, mul_comm]⟩
    have hOut := quotSat_mono (fun X _ h => (isSLModel_two_facts hq3 h).2.2.1) hS3
    have hRS := le_of_perfect_outer hQS hSM hSH hSn
      (solvable_centralizer_of_centTrivial hSM hSH hCT) hNR hRM hRH hperf hOut
    obtain ⟨hnS, hY⟩ := hS3
    haveI := hnS
    obtain ⟨-, -, -, hYcard⟩ := isSLModel_two_facts hq3 hY
    obtain ⟨ι, hι, -⟩ := exists_injective_quotient hNR hRS
    have hle : Nat.card (↥R ⧸ N.subgroupOf R) ≤ Nat.card (↥(Lgen (Subgroup.normalizer
        ((cen N : Subgroup X) : Set X)) (LB (Subgroup.normalizer ((cen N : Subgroup X) : Set X))
          N B₂)) ⧸ N.subgroupOf (Lgen (Subgroup.normalizer ((cen N : Subgroup X) : Set X))
            (LB (Subgroup.normalizer ((cen N : Subgroup X) : Set X)) N B₂))) :=
      Nat.card_le_card_of_injective ι hι
    rw [hRcard, hYcard, ← pow_mul] at hle
    exact absurd hle (not_le.mpr hc2)
  have hE2 : CentTrivial (Subgroup.normalizer ((cen N : Subgroup X) : Set X)) N (cen N)
        (Lgen (Subgroup.normalizer ((cen N : Subgroup X) : Set X))
          (LB (Subgroup.normalizer ((cen N : Subgroup X) : Set X)) N B₂)) →
      (QuotSat (Lgen (Subgroup.normalizer ((cen N : Subgroup X) : Set X))
          (LB (Subgroup.normalizer ((cen N : Subgroup X) : Set X)) N B₂)) N
          (IsProdOf (IsSLModel 2 (Nat.card (cen N))) (IsOmegaPlus 2 (Nat.card (cen N)))) ∨
        QuotSat (Lgen (Subgroup.normalizer ((cen N : Subgroup X) : Set X))
          (LB (Subgroup.normalizer ((cen N : Subgroup X) : Set X)) N B₂)) N
          (IsProdOf (IsSLModel 2 (Nat.card (cen N))) (IsOmegaMinus 2 (Nat.card (cen N))))) →
      False := by
    intro hCT hQ
    rcases hQ with hQp | hQm
    · have hRS := le_of_perfect_prod3 hQS hSM hSH hSn hCT hNR hRM hRH hperf
        (quotSat_mono (fun X _ h => isSimpleProd3_of_sl_omegaPlus_two hqa h) hQp)
      obtain ⟨hnS, A, B, _, _, hA, hB, ⟨e⟩⟩ := hQp
      haveI := hnS
      obtain ⟨B₁, B₂', _, _, hB₁, hB₂, ⟨e'⟩⟩ := isOmegaPlus_two_split hqa hB
      obtain ⟨-, -, -, hAc⟩ := isSLModel_two_facts hqa hA
      obtain ⟨-, -, -, hB₁c⟩ := isSLModel_two_facts hqa hB₁
      obtain ⟨-, -, -, hB₂c⟩ := isSLModel_two_facts hqa hB₂
      let e3 := e.trans (MulEquiv.prodCongr (MulEquiv.refl A) e')
      haveI : Finite (A × (B₁ × B₂')) := Finite.of_equiv _ e3.toEquiv
      haveI : Finite A := Finite.of_injective (fun x : A => (x, ((1 : B₁), (1 : B₂'))))
        (fun x y h => (Prod.mk.inj h).1)
      haveI : Finite B₁ := Finite.of_injective (fun b : B₁ => ((1 : A), (b, (1 : B₂'))))
        (fun x y h => (Prod.mk.inj (Prod.mk.inj h).2).1)
      haveI : Finite B₂' := Finite.of_injective (fun b : B₂' => ((1 : A), ((1 : B₁), b)))
        (fun x y h => (Prod.mk.inj (Prod.mk.inj h).2).2)
      obtain ⟨ι, hι, -⟩ := exists_injective_quotient hNR hRS
      rcases card_le_or_le_of_embeds3 (e3.toMonoidHom.comp ι) (e3.injective.comp hι) with
        h | h | h
      · rw [hRcard, hAc] at h
        exact absurd h (not_le.mpr hc1)
      · rw [hRcard, hB₁c] at h
        exact absurd h (not_le.mpr hc1)
      · rw [hRcard, hB₂c] at h
        exact absurd h (not_le.mpr hc1)
    · have hRS := le_of_perfect_prod2 hQS hSM hSH hSn hCT hNR hRM hRH hperf
        (quotSat_mono (fun X _ h => isSimpleProd2_of_sl_omegaMinus_two hqa h) hQm)
      obtain ⟨hnS, A, B, _, _, hA, hB, ⟨e⟩⟩ := hQm
      haveI := hnS
      obtain ⟨-, -, -, hAc⟩ := isSLModel_two_facts hqa hA
      obtain ⟨-, -, -, hBc⟩ := isOmegaMinus_two_facts hqa hB
      haveI : Finite (A × B) := Finite.of_equiv _ e.toEquiv
      haveI : Finite A := Finite.of_injective (fun x : A => (x, (1 : B)))
        (fun x y h => (Prod.mk.inj h).1)
      haveI : Finite B := Finite.of_injective (fun b : B => ((1 : A), b))
        (fun x y h => (Prod.mk.inj h).2)
      rcases quot_embeds_prod hNR hRS e with h | ⟨h, -⟩
      · rw [hRcard, hAc] at h
        exact absurd h (not_le.mpr hc1)
      · rw [hRcard, hBc] at h
        exact absurd h (not_le.mpr hc3)
  have hii : ∀ t : X, StrothCii (Subgroup.normalizer ((cen N : Subgroup X) : Set X)) N (cen N)
      B₂ t → CentTrivial (Subgroup.normalizer ((cen N : Subgroup X) : Set X)) N (cen N)
        (Lgen (Subgroup.normalizer ((cen N : Subgroup X) : Set X))
          (LB (Subgroup.normalizer ((cen N : Subgroup X) : Set X)) N B₂)) → False := by
    rintro t ⟨m, -, hm, -, hsum⟩ hCT
    have hm2 : m = 2 := by
      have := hinj _ _ (hN.symm.trans hm)
      omega
    subst hm2
    rcases hsum with ⟨-, h⟩ | ⟨-, h⟩
    · exact hE2 hCT (Or.inl h)
    · exact hE2 hCT (Or.inr h)
  obtain ⟨hcases, -⟩ := hS.2 B₂ hc
  rcases hcases with ⟨k0, hk0, ⟨e⟩⟩ | ⟨h5, -⟩ | ⟨h9, hS3, hCT⟩ |
    ⟨hnTI, (⟨hNoA2, t, htL, htQ, hCT, (hi | hii' | hiii | hiv | hv)⟩ | hVI)⟩
  · exfalso
    have hk00 : k0 ≠ 0 := by
      rintro rfl
      have := hS.1.q4
      rw [hk0] at this
      simp at this
    have hcard : Nat.card N = Nat.card (cen N) ^ 3 := by
      rw [Nat.card_congr e.toEquiv, Tim79.card_ut3, GaloisField.card 2 k0 hk00, hk0]
    have := hinj _ _ (hN.symm.trans hcard)
    omega
  · exfalso
    have := hinj _ _ (hN.symm.trans h5)
    omega
  · exact (hD3 hS3 hCT).elim
  · exfalso
    have hNoA2' : NoA2 N (cen N) (LB (Subgroup.normalizer ((cen N : Subgroup X) : Set X)) N B₂) :=
      hNoA2 B₂ hc.conj hc.le hc.ne
    have hgenB := hgen X _ N (cen N) B₂ hc 4 hW (by norm_num) hNoA2'
    exact hii t (hCi X _ N (cen N) B₂ hc 4 t ⟨hW, by norm_num, hNoA2', hgenB, htL, htQ⟩ hi) hCT
  · exact (hii t hii' hCT).elim
  · exfalso
    have := hinj _ _ (hN.symm.trans hiii.1)
    omega
  · exfalso
    have := hinj _ _ (hN.symm.trans hiv.1)
    omega
  · exfalso
    have := hinj _ _ (hN.symm.trans hv.1)
    omega
  · exact caseVI_four hS hW hnTI hVI

end CFSG.RankThree.GF2n.Stroth80
