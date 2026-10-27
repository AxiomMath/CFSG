module

public import CFSG.Quasithin.Vol2.Ch11SecD556F
public import CFSG.Quasithin.Vol2.Ch11SecD551D
public import CFSG.Quasithin.Vol2.Ch11SecD556O
public import CFSG.Quasithin.Vol2.Ch11SecDFacts5

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem inf_sectionCentralizer_le_pCoreOf_of_le (h : Hyp11 G T L I n) {V₁ H₁ K' : Subgroup G}
    (hH₁ : InH (LOf L V₁ ⊔ T) H₁) (hH₁N : H₁ ≤ Subgroup.normalizer (V₁ : Set G))
    (hTK' : T ≤ Subgroup.normalizer (K' : Set G)) (hOK : oTwoUpper H₁ ≤ K') :
    ROf T L V₁ ⊓ sectionCentralizer K' (pCoreOf 2 (KOf L V₁ V₁)) ≤ pCoreOf 2 H₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := KOf L V₁ V₁ with hKdef
  set Q := pCoreOf 2 K with hQdef
  set R₁ := ROf T L V₁ with hR₁def
  set C := R₁ ⊓ sectionCentralizer K' Q with hCdef
  set D := Q ⊓ H₁ with hDdef
  have hT2 : IsPGroup 2 T := h.fsu.sylow.1
  have hTH : T ≤ H₁ := le_sup_right.trans hH₁.1
  have hsylH : QuasithinUnique.IsSylowTwoOf T H₁ :=
    isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow hTH
  have hR₁T : R₁ ≤ T := ROf_le_T h V₁
  have hNK := normalizer_le_normalizer_kOf L V₁ V₁
  have hH₁Q : H₁ ≤ Subgroup.normalizer (Q : Set G) :=
    (hH₁N.trans hNK).trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)
  have hDnorm : H₁ ≤ Subgroup.normalizer (D : Set G) := fun g hg =>
    mem_normalizer_inf (hH₁Q hg) (Subgroup.le_normalizer hg)
  have hDO : D ≤ pCoreOf 2 H₁ := CFSG.LieType.BorelTits.le_pCoreOf 2 inf_le_right
    ((Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr hDnorm)
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K).to_le inf_le_left)
  have hO2T : pCoreOf 2 H₁ ≤ T := pCoreOf_two_le_of_isSylowTwoOf hsylH
  have hCT : C ≤ T := inf_le_left.trans hR₁T
  have hNT : C ⊔ D ≤ T := sup_le hCT (hDO.trans hO2T)
  have hTC : T ≤ Subgroup.normalizer (C : Set G) := fun t ht =>
    mem_normalizer_inf ((le_sup_right.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)) ht)
      (mem_normalizer_sectionCentralizer (hTK' ht) (hH₁Q (hTH ht)))
  have hTN : T ≤ Subgroup.normalizer ((C ⊔ D : Subgroup G) : Set G) :=
    le_normalizer_sup hTC (hTH.trans hDnorm)
  have hON : oTwoUpper H₁ ≤ Subgroup.normalizer ((C ⊔ D : Subgroup G) : Set G) := by
    intro g hg
    have hgK : g ∈ K' := hOK hg
    have hgH : g ∈ H₁ := oTwoUpper_le H₁ hg
    apply A4.mem_normalizer_of_conj_mem
    have hle : C ⊔ D ≤ (C ⊔ D).comap (MulAut.conj g).toMonoidHom := by
      refine sup_le (fun c hc => ?_) (fun d hd => ?_)
      · show g * c * g⁻¹ ∈ C ⊔ D
        have h1 : c * g * c⁻¹ * g⁻¹ ∈ Q := hc.2.2.2 g hgK
        have hcH : c ∈ H₁ := hTH (hCT hc)
        have h2 : g * c * g⁻¹ * c⁻¹ ∈ D := by
          refine ⟨?_, H₁.mul_mem (H₁.mul_mem (H₁.mul_mem hgH hcH) (H₁.inv_mem hgH))
            (H₁.inv_mem hcH)⟩
          have e : g * c * g⁻¹ * c⁻¹ = (c * g * c⁻¹ * g⁻¹)⁻¹ := by group
          rw [e]
          exact Q.inv_mem h1
        have e : g * c * g⁻¹ = (g * c * g⁻¹ * c⁻¹) * c := by group
        rw [e]
        exact (C ⊔ D).mul_mem (Subgroup.mem_sup_right h2) (Subgroup.mem_sup_left hc)
      · show g * d * g⁻¹ ∈ C ⊔ D
        exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hDnorm hgH) d).mp hd)
    exact fun x hx => hle hx
  have hNn : H₁ ≤ Subgroup.normalizer ((C ⊔ D : Subgroup G) : Set G) := by
    rw [← oTwoUpper_sup_eq_of_sylow' hsylH]
    exact sup_le hON hTN
  have hNO : C ⊔ D ≤ pCoreOf 2 H₁ := CFSG.LieType.BorelTits.le_pCoreOf 2 (hNT.trans hTH)
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (hNT.trans hTH)).mpr hNn) (hT2.to_le hNT)
  exact le_sup_left.trans hNO

theorem stmt11_5_6_sixP (hM2 : FactM2Case1) (hM2P : FactM2Case1Prime) (hSig : L2pSignalizerFact)
    (hTI : PointsTIFact) (h1102 : Stmt11_0_2) (h1110 : Stmt11_1_0) (h1111 : Stmt11_1_1)
    (h1112 : Stmt11_1_2) (h1141 : Stmt11_4_1) (h1143 : Stmt11_4_3) (h : Hyp11 G T L I n)
    {V₁ X H₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁) (hX : IsCartanX T L X)
    (hH₁ : InH (LOf L V₁ ⊔ T) H₁) (hH₁M : ¬ H₁ ≤ Subgroup.normalizer (L : Set G))
    (hH₁N : H₁ ≤ Subgroup.normalizer (V₁ : Set G)) (hOK : oTwoUpper H₁ ≤ KOf L V₁ V₁)
    (hcase : Case11_1_2Two L (KOf L V₁ V₁) ∨
      (∃ p : ℕ, p.Prime ∧ IsPGroup p ↥(CFSG.fittingSubgroup
        (↥(KOf L V₁ V₁) ⧸ CFSG.pCore 2 ↥(KOf L V₁ V₁)))) ∨
      ∃ p : ℕ, p.Prime ∧ oTwoUpper H₁ ≤ oTwoPrime (KOf L V₁ V₁) p ⊔ LOf L V₁) :
    ∀ A : Subgroup G, A ≤ ROf T L V₁ → IsElemAbelian 2 A →
      E3.mQuot A (A ⊓ pCoreOf 2 H₁) ≤ 1 := by
  intro A hAR hA
  set K := KOf L V₁ V₁ with hKdef
  set L₁ := LOf L V₁ with hL₁def
  set R₁ := ROf T L V₁ with hR₁def
  have hT2 : IsPGroup 2 T := h.fsu.sylow.1
  have hTN : T ≤ Subgroup.normalizer (V₁ : Set G) := SecA.IsVi.le_normalizer hV₁
  have hTK : T ≤ Subgroup.normalizer (K : Set G) := hTN.trans (normalizer_le_normalizer_kOf L V₁ V₁)
  have hTL₁ : T ≤ Subgroup.normalizer (L₁ : Set G) := fun t ht =>
    mem_normalizer_lOf (h.normal ht) (hTN ht)
  have hTH : T ≤ H₁ := le_sup_right.trans hH₁.1
  have hsylH : QuasithinUnique.IsSylowTwoOf T H₁ :=
    isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow hTH
  have hR₁T : R₁ ≤ T := ROf_le_T h V₁
  have hR₁K : R₁ ≤ Subgroup.normalizer (K : Set G) := hR₁T.trans hTK
  have hlt : L₁ < K := by
    refine lt_of_le_of_ne (le_conjClosure _ _) fun heq => hH₁M ?_
    rw [← oTwoUpper_sup_eq_of_sylow' hsylH]
    refine sup_le (hOK.trans ?_) h.normal
    rw [← heq]
    exact ((perfectCore_le _).trans inf_le_left).trans Subgroup.le_normalizer
  have hfin : ∀ S : Subgroup G, R₁ ⊓ S ≤ pCoreOf 2 H₁ → E3.mQuot A (A ⊓ S) ≤ 1 →
      E3.mQuot A (A ⊓ pCoreOf 2 H₁) ≤ 1 := fun S hS hb =>
    le_trans (E3.mQuot_mono (le_inf inf_le_left
      ((le_inf (inf_le_left.trans hAR) inf_le_right).trans hS))) hb
  have hSK := inf_sectionCentralizer_le_pCoreOf h hH₁ hH₁N hOK
  have hcase2 : Case11_1_2Two L K → E3.mQuot A (A ⊓ pCoreOf 2 H₁) ≤ 1 := fun hK2 => by
    have hRK := commutator_ROf_kOf_le_of_case_two hSig h1110 h hV₁ hK2
    have hAsc : A ≤ sectionCentralizer K (pCoreOf 2 K) := fun a ha => by
      have haR := hAR ha
      refine ⟨hR₁K haR, CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K
        (hR₁K haR), fun k hk => ?_⟩
      have := Subgroup.commutator_le.mp hRK a haR k hk
      rwa [commutatorElement_def] at this
    refine hfin _ hSK ?_
    rw [inf_eq_left.mpr hAsc, E3.mQuot_self]
    exact Nat.zero_le _
  rcases (h1141 G T L I n V₁ X h hV₁ hX).2.1 _
      (kOf_cComp_centralizer hTI h1102 h1110 h1112 h1141 h1143 h hV₁) hlt with hK1 | hK2
  ·
    have hsylN : QuasithinUnique.IsSylowTwoOf (T ⊓ Subgroup.normalizer (V₁ : Set G))
        (Subgroup.normalizer (V₁ : Set G)) := by
      rw [inf_eq_left.mpr hTN]
      exact isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow hTN
    obtain ⟨K', hLK', hK', hNK', hcase'⟩ := h1111 G T L I n 1 V₁ V₁ h hV₁
      (Or.inl ⟨rfl, SecA.IsVi.ne_bot h hV₁ le_rfl, le_rfl, hsylN⟩)
    have hKK' : K = K' := kOf_eq_of_cComp hLK' hK' hNK' (lOf_ne_bot h1110 h hV₁)
    rw [← hKK'] at hcase'
    have hlist : List11_1_1Two (↥K ⧸ CFSG.pCore 2 ↥K) n ∨
        (n = 2 ∧ List11_1_1Three (↥K ⧸ CFSG.pCore 2 ↥K)) := by
      rcases hcase' with heq | h2 | h3
      · exact absurd heq.symm hlt.ne'
      · exact Or.inl h2
      · exact Or.inr h3
    have hL₁q := (h1110 G T L I n h).2.1 1 (Or.inl rfl) V₁ hV₁
    rcases hcase with hK2 | hp | ⟨p, hp, hle⟩
    · exact hcase2 hK2
    · exact hfin _ hSK (hM2 G K L₁ R₁ n hlist hK1 hp (le_conjClosure _ _)
        (perfectCore_perfect _) hL₁q (hT2.to_le hR₁T) hR₁K (hR₁T.trans hTL₁)
        (commutator_ROf_lOf_le h hV₁) A hAR hA)
    · have hTK₁ : T ≤ Subgroup.normalizer ((oTwoPrime K p ⊔ L₁ : Subgroup G) : Set G) :=
        le_normalizer_sup (hTK.trans (normalizer_le_normalizer_oTwoPrime K p)) hTL₁
      exact hfin _ (inf_sectionCentralizer_le_pCoreOf_of_le h hH₁ hH₁N hTK₁ hle)
        (hM2P G K L₁ R₁ n p hlist hK1 (conjClosure_perfect (perfectCore_perfect _))
          (le_conjClosure _ _) (perfectCore_perfect _) hL₁q (hT2.to_le hR₁T) hR₁K
          (hR₁T.trans hTL₁) (commutator_ROf_lOf_le h hV₁) hp A hAR hA)
  · exact hcase2 hK2

end CFSG.Quasithin.Vol2.Ch11.SecD
