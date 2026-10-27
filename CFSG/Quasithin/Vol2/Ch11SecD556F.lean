module

public import CFSG.Quasithin.Vol2.Ch11SecD551B
public import CFSG.Quasithin.Vol2.Ch11SecDFacts3

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem commutator_ROf_lOf_le (h : Hyp11 G T L I n) {V₁ : Subgroup G}
    (hV₁ : IsVi T L I n 1 V₁) : ⁅ROf T L V₁, LOf L V₁⁆ ≤ pCoreOf 2 (LOf L V₁) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L₁ := LOf L V₁ with hL₁def
  set R₁ := ROf T L V₁ with hR₁def
  have hR₁T : R₁ ≤ T := ROf_le_T h V₁
  have hR₁2 : IsPGroup 2 R₁ := h.fsu.sylow.1.to_le hR₁T
  have hTL₁ : T ≤ Subgroup.normalizer (L₁ : Set G) := fun t ht =>
    mem_normalizer_lOf (h.normal ht) (SecA.IsVi.le_normalizer hV₁ ht)
  have hXR : L₁ ⊔ T ≤ Subgroup.normalizer (R₁ : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L₁ ⊔ T)
  have hle : ⁅R₁, L₁⁆ ≤ R₁ ⊓ L₁ := Subgroup.commutator_le.mpr fun r hr l hl => by
    rw [commutatorElement_def]
    refine ⟨?_, L₁.mul_mem ((Subgroup.mem_normalizer_iff.mp (hTL₁ (hR₁T hr)) l).mp hl)
      (L₁.inv_mem hl)⟩
    have hl' : l * r⁻¹ * l⁻¹ ∈ R₁ :=
      (Subgroup.mem_normalizer_iff.mp (hXR (Subgroup.mem_sup_left hl)) _).mp (R₁.inv_mem hr)
    have e : r * l * r⁻¹ * l⁻¹ = r * (l * r⁻¹ * l⁻¹) := by group
    rw [e]
    exact R₁.mul_mem hr hl'
  refine hle.trans (CFSG.LieType.BorelTits.le_pCoreOf 2 inf_le_right ?_ (hR₁2.to_le inf_le_left))
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr fun l hl =>
    mem_normalizer_inf (hXR (Subgroup.mem_sup_left hl)) (Subgroup.le_normalizer hl)

theorem commutator_ROf_kOf_le_of_case_two (hSig : L2pSignalizerFact) (h1110 : Stmt11_1_0)
    (h : Hyp11 G T L I n) {V₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁)
    (hK2 : Case11_1_2Two L (KOf L V₁ V₁)) :
    ⁅ROf T L V₁, KOf L V₁ V₁⁆ ≤ pCoreOf 2 (KOf L V₁ V₁) := by
  obtain ⟨⟨p, hp, hp11, hpsl⟩, -⟩ := hK2
  have hR₁T : ROf T L V₁ ≤ T := ROf_le_T h V₁
  have hTN : T ≤ Subgroup.normalizer (V₁ : Set G) := SecA.IsVi.le_normalizer hV₁
  exact hSig G _ _ _ p n hp hp11 h.one_lt hpsl (le_conjClosure _ _) (perfectCore_perfect _)
    ((h1110 G T L I n h).2.1 1 (Or.inl rfl) V₁ hV₁) (h.fsu.sylow.1.to_le hR₁T)
    (hR₁T.trans (hTN.trans (normalizer_le_normalizer_kOf L V₁ V₁)))
    (hR₁T.trans fun t ht => mem_normalizer_lOf (h.normal ht) (hTN ht))
    (commutator_ROf_lOf_le h hV₁)

theorem inf_sectionCentralizer_le_pCoreOf (h : Hyp11 G T L I n) {V₁ H₁ : Subgroup G}
    (hH₁ : InH (LOf L V₁ ⊔ T) H₁)
    (hH₁N : H₁ ≤ Subgroup.normalizer (V₁ : Set G)) (hOK : oTwoUpper H₁ ≤ KOf L V₁ V₁) :
    ROf T L V₁ ⊓ sectionCentralizer (KOf L V₁ V₁) (pCoreOf 2 (KOf L V₁ V₁)) ≤
      pCoreOf 2 H₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := KOf L V₁ V₁ with hKdef
  set Q := pCoreOf 2 K with hQdef
  set R₁ := ROf T L V₁ with hR₁def
  set C := R₁ ⊓ sectionCentralizer K Q with hCdef
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
      (mem_normalizer_sectionCentralizer (hH₁N.trans hNK (hTH ht)) (hH₁Q (hTH ht)))
  have hTN : T ≤ Subgroup.normalizer ((C ⊔ D : Subgroup G) : Set G) :=
    le_normalizer_sup hTC (hTH.trans hDnorm)
  have hON : oTwoUpper H₁ ≤ Subgroup.normalizer ((C ⊔ D : Subgroup G) : Set G) := by
    intro g hg
    have hgK : g ∈ K := hOK hg
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

end CFSG.Quasithin.Vol2.Ch11.SecD
