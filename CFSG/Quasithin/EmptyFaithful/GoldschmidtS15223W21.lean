module

public import CFSG.Quasithin.EmptyFaithful.S152He12E
public import CFSG.Quasithin.EmptyFaithful.S152U21

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

structure Lemma15221ConclW (T Mc M H H₁ H₂ : Subgroup G)
    (B₀ : Subgroup (MulAut (V154 T Mc M))) (I : Subgroup G) : Prop where
  one : ¬ IsIrredOnSection (sOf152 T Mc M B₀) (oTwoUpper H) (pCoreOf 2 (oTwoUpper H)) →
    oTwoUpper H ⊔ sOf152 T Mc M B₀ = H₁ ⊔ H₂ ∧
      (∀ t ∈ T, t ∉ sOf152 T Mc M B₀ → conjSub t (oTwoUpper H₁) = oTwoUpper H₂) ∧
      conjClosure (oTwoUpper H) Mc ≤ Subgroup.centralizer (zSOf T Mc M B₀ : Set G) ∧
      (conjClosure (oTwoUpper H) Mc ≠ oTwoUpper H →
        conjClosure (oTwoUpper H) Mc = oPrimeResidualOf 3 (Mc ⊓ I))
  two : conjClosure (oTwoUpper H) Mc = oTwoUpper H →
    IsThreePrimeGroup (M ⊓ Subgroup.centralizer (V154 T Mc M : Set G))
  three : IsLnTwo 4 (OTwoQuot (conjClosure (oTwoUpper H) Mc)) → Concl15218ii T Mc M H B₀ I →
    (∃ Y₁ : Subgroup G, Y₁ = oTwoUpper Y₁ ∧ Y₁ ≤ M ⊓ I ∧
        sOf152 T Mc M B₀ ≤ Subgroup.normalizer (Y₁ : Set G) ∧
        Nonempty (OTwoQuot (Y₁ ⊔ sOf152 T Mc M B₀) ≃* Equiv.Perm (Fin 3)) ∧
        ¬ Y₁ ≤ Mc ⊓ I) →
    IsIrredOnSection (sOf152 T Mc M B₀) (oTwoUpper H) (pCoreOf 2 (oTwoUpper H))

@[expose] def StageLemma15221W : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ H : Subgroup G, IsHStar T M H → ∀ H₁ H₂ : Subgroup G, IsHPair H (V154 T Mc M) H₁ H₂ →
      ∀ B₀ : Subgroup (MulAut (V154 T Mc M)), IsB0 T Mc M B₀ →
        ∀ I : Subgroup G, Hyp15215 T Mc M B₀ I → Lemma15221ConclW T Mc M H H₁ H₂ B₀ I

section Main

variable {T Mc M H : Subgroup G} {B₀ : Subgroup (MulAut (V154 T Mc M))} {I : Subgroup G}

theorem Kc_eq_oPrime_inf_of_ne152 {B : Subgroup G} (h12 : He12.Lemma15212ConclW T Mc M H B)
    (hD : Inputs152 T Mc M H B₀ I)
    (hKc : conjClosure (oTwoUpper H) Mc ≤ Subgroup.centralizer (zSOf T Mc M B₀ : Set G))
    (hne : conjClosure (oTwoUpper H) Mc ≠ oTwoUpper H) :
    conjClosure (oTwoUpper H) Mc = oPrimeResidualOf 3 (Mc ⊓ I) := by
  have h3 := h12.eq_oThreePrime_of_ne hne
  have hI : oPrimeResidualOf 3 Mc ≤ I := by
    rw [← h3]
    exact fun x hx => (centralizer_zS_le_inf152 hD (hKc hx)).2
  have := oPrimeResidualOf_eq_inf152 (X := Mc) (Y := I) hI
  rw [h3]
  exact this

theorem lemma_15_2_21_one_W {H₁ H₂ : Subgroup G} (hs : Setting152 T Mc M) (hH : IsHStar T M H)
    (hP : IsHPair H (V154 T Mc M) H₁ H₂) (hB₀ : IsB0 T Mc M B₀) (hD : Inputs152 T Mc M H B₀ I)
    {B : Subgroup G} (h12 : He12.Lemma15212ConclW T Mc M H B)
    (hIrr : IsIrredOnSection T (oTwoUpper H) (pCoreOf 2 (oTwoUpper H)))
    (hJ : IsSylowTwoOf (thompsonJ T ⊔ pCoreOf 2 H) (H₁ ⊔ H₂) ∧
      (thompsonJ T ⊔ pCoreOf 2 H).relIndex T = 2)
    (hKc : conjClosure (oTwoUpper H) Mc ≠ oTwoUpper H →
      pCoreOf 2 (conjClosure (oTwoUpper H) Mc ⊔ T) ≤ sOf152 T Mc M B₀ →
        conjClosure (oTwoUpper H) Mc ≤ Subgroup.centralizer (zSOf T Mc M B₀ : Set G))
    (hnot : ¬ IsIrredOnSection (sOf152 T Mc M B₀) (oTwoUpper H) (pCoreOf 2 (oTwoUpper H))) :
    oTwoUpper H ⊔ sOf152 T Mc M B₀ = H₁ ⊔ H₂ ∧
      (∀ t ∈ T, t ∉ sOf152 T Mc M B₀ → conjSub t (oTwoUpper H₁) = oTwoUpper H₂) ∧
      conjClosure (oTwoUpper H) Mc ≤ Subgroup.centralizer (zSOf T Mc M B₀ : Set G) ∧
      (conjClosure (oTwoUpper H) Mc ≠ oTwoUpper H →
        conjClosure (oTwoUpper H) Mc = oPrimeResidualOf 3 (Mc ⊓ I)) := by
  have hQS := Q_le_S152 hs hH hD hIrr hnot
  have hSeq := J_sup_eq_S152 hD hQS hJ.2
  have hSyl : IsSylowTwoOf (sOf152 T Mc M B₀) (H₁ ⊔ H₂) := hSeq ▸ hJ.1
  have hT2 : IsPGroup 2 T := hs.qtfe.sylow.1
  have hKc' : conjClosure (oTwoUpper H) Mc ≤ Subgroup.centralizer (zSOf T Mc M B₀ : Set G) := by
    by_cases hK : conjClosure (oTwoUpper H) Mc = oTwoUpper H
    · rw [hK]
      exact K_le_centralizer_zS152 hB₀ hD
    apply hKc hK
    have hHK : H ≤ conjClosure (oTwoUpper H) Mc ⊔ T := by
      calc H = oTwoUpper H ⊔ T := H_eq152 hs hH
        _ ≤ conjClosure (oTwoUpper H) Mc ⊔ T := sup_le_sup_right (le_conjClosure _ _) T
    have hTK : T ≤ conjClosure (oTwoUpper H) Mc ⊔ T := le_sup_right
    have h1 : pCoreOf 2 (conjClosure (oTwoUpper H) Mc ⊔ T) ≤ pCoreOf 2 H :=
      pCoreOf_le_pCoreOf_of_sylow hHK hT2 hH.1.1 (isSylowTwoOf_of_le151 hs.qtfe.sylow hTK).2.2
    exact h1.trans hQS
  exact ⟨KS_eq_sup152 hP hSyl, fun t ht htS =>
    conjSub_oTwoUpper_eq152 hP hSyl hT2 S_le_T152 hH.1.1 ht htS, hKc',
    fun hne => Kc_eq_oPrime_inf_of_ne152 h12 hD hKc' hne⟩

theorem lemma_15_2_21_two_W (h15208 : StageLemma15208) (h15209 : StageNotation15209)
    (hs : Setting152 T Mc M) (hH : IsHStar T M H) (h14 : Lemma15214Concl T Mc M B₀)
    (hK : conjClosure (oTwoUpper H) Mc = oTwoUpper H) :
    IsThreePrimeGroup (M ⊓ Subgroup.centralizer (V154 T Mc M : Set G)) := by
  intro h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hxG : orderOf (x : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hx
  have hxM : (x : G) ∈ M := x.2.1
  have hxMc : (x : G) ∈ Mc := by
    have h1 : (x : G) ∈ M ⊓ Mc := by
      rw [h14.inf_eq.1, h14.inf_eq.2]
      exact Subgroup.mem_sup_left x.2
    exact h1.2
  exact He12.not_orderOf_three_of_mem_inf h15208 h15209 hs hH hK hxM hxMc hxG

end Main

theorem stageLemma15221W_of (h5 : StageLemma15205) (h159 : StageLemma1519)
    (h8 : StageLemma15208) (h11 : StageLemma15211) (h12 : He12.StageLemma15212W)
    (h13 : StageLemma15213) (h14 : StageLemma15214) (hN : StageNotation15209)
    (h16 : StageLemma15216) (h17 : StageLemma15217) (hIrr : Input15209Irr) (hJ : Input15112J)
    (hKc : Input1210Kc) (h3 : Input15221Three) : StageLemma15221W := by
  intro G _ _ T Mc M hs H hH H₁ H₂ hP B₀ hB₀ I hI
  have hD : Inputs152 T Mc M H B₀ I :=
    ⟨h5 G T Mc M hs, h159 G T Mc M hs.qtfe hs.mf hs.ce, h13 G T Mc M hs H hH,
      h14 G T Mc M hs B₀ hB₀, h11 G T Mc M hs H hH, hN G T Mc M hs H hH,
      h16 G T Mc M hs H hH B₀ hB₀ I hI, h17 G T Mc M hs B₀ hB₀ I hI⟩
  obtain ⟨B, hB⟩ := (hN G T Mc M hs H hH).sigmaPrime_nonempty
  have h12' := h12 G T Mc M hs H hH B hB
  exact ⟨fun hnot => lemma_15_2_21_one_W hs hH hP hB₀ hD h12' (hIrr G T Mc M hs H hH)
      (hJ G T Mc M hs H hH H₁ H₂ hP) (hKc G T Mc M hs B₀ hB₀ H hH) hnot,
    fun hK => lemma_15_2_21_two_W h8 hN hs hH hD.h14 hK,
    fun hL hii hY => h3 G T Mc M hs H hH H₁ H₂ hP B₀ hB₀ I hI hL hii hY⟩

end CFSG.Quasithin
