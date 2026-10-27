module

public import CFSG.RankThree.PartTwo.Sec15.HypR
public import CFSG.RankThree.PartTwo.Sec13.Item13Inputs
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.RankThree.PartTwo.Sec14.Item145Bot
import CFSG.RankThree.PartTwo.Sec6.Item68
import CFSG.RankThree.PartTwo.Sec4.Census.Lift46

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem eq_of_mem_lA_of_mem {F L L'' : Subgroup G} {c : G} (hL : L ∈ thetaComponentsAt 3 c)
    (hL'' : L'' ∈ lA F c) {f : G} (hfF : f ∈ F) (hfL : f ∈ L)
    (hfc : f ∉ Subgroup.zpowers c) : L'' = L := by
  by_contra hne
  obtain ⟨hL''c, hFN, hsec, -⟩ := hL''
  apply hfc
  have hmem : f ∈ Late.sectionCentralizer F L''
      ((aschbacherSolvableCore 3 L'').map L''.subtype) := by
    refine ⟨hfF, fun x hx => ?_⟩
    have hcomm : ⁅f, x⁆ ∈ inSubgroup (aschbacherSolvableCore 3)
        (Subgroup.centralizer ({c} : Set G)) :=
      Sec6.commutator_le_theta_of_ne_mem_thetaComponentsAt hL hL''c (Ne.symm hne)
        (Subgroup.commutator_mem_commutator hfL hx)
    have hxL : f * x * f⁻¹ ∈ L'' := (Subgroup.mem_normalizer_iff.mp (hFN hfF) x).mp hx
    have hin : f * x * f⁻¹ * x⁻¹ ∈ L'' ⊓ inSubgroup (aschbacherSolvableCore 3)
        (Subgroup.centralizer ({c} : Set G)) := by
      refine Subgroup.mem_inf.mpr ⟨mul_mem hxL (inv_mem hx), ?_⟩
      rwa [commutatorElement_def] at hcomm
    rw [← Sec6.theta_eq_inf_of_mem_thetaComponentsAt hL''c] at hin
    exact hin
  rw [hsec] at hmem
  exact hmem

theorem exists_mem_inf_not_mem_zpowers_of_card {F L : Subgroup G} {c : G}
    (hFN : F ≤ Subgroup.normalizer (L : Set G)) (hcN : c ∈ Subgroup.normalizer (L : Set G))
    (hF27 : Nat.card F = 27) (hFL : F ≤ Subgroup.zpowers c ⊔ L) (hc3 : orderOf c = 3)
    (hcL : c ∉ L) : ∃ f ∈ F, f ∈ L ∧ f ∉ Subgroup.zpowers c := by
  have hcN' : Subgroup.zpowers c ≤ Subgroup.normalizer (L : Set G) :=
    Subgroup.zpowers_le.mpr hcN
  have h1 := Sec6.card_sup_mul_card_inf hFN
  have h2 := Sec6.card_sup_mul_card_inf hcN'
  have hdisj : Subgroup.zpowers c ⊓ L = ⊥ := by
    rw [inf_comm]
    exact Sec4.Census.inf_zpowers_eq_bot_of_not_mem Nat.prime_three hc3 hcL
  rw [hdisj, Subgroup.card_bot, mul_one, Nat.card_zpowers, hc3] at h2
  have hle : Nat.card (F ⊔ L : Subgroup G) ≤ Nat.card (Subgroup.zpowers c ⊔ L : Subgroup G) :=
    Subgroup.card_le_of_le (sup_le hFL le_sup_right)
  have hLpos : 0 < Nat.card L := Nat.card_pos
  have h9 : 9 ≤ Nat.card (F ⊓ L : Subgroup G) := by
    by_contra hlt
    push Not at hlt
    have : Nat.card (F ⊔ L : Subgroup G) * Nat.card (F ⊓ L : Subgroup G) <
        3 * Nat.card L * 9 := by
      calc Nat.card (F ⊔ L : Subgroup G) * Nat.card (F ⊓ L : Subgroup G)
          ≤ 3 * Nat.card L * Nat.card (F ⊓ L : Subgroup G) := by
            exact Nat.mul_le_mul_right _ (h2 ▸ hle)
        _ < 3 * Nat.card L * 9 := Nat.mul_lt_mul_of_pos_left hlt (by omega)
    rw [h1, hF27] at this
    omega
  by_contra hall
  push Not at hall
  have hsub : F ⊓ L ≤ ⊥ := by
    intro f hf
    have hfz := hall f hf.1 hf.2
    have : f ∈ Subgroup.zpowers c ⊓ L := ⟨hfz, hf.2⟩
    rwa [hdisj] at this
  have := Subgroup.card_le_of_le hsub
  rw [Subgroup.card_bot] at this
  omega

theorem sec15R_of_le {A F L : Subgroup G} {c : G} (h : Sec15R G A c L) (hset : Item13SetupAt)
    (hF : F ∈ partTwoF G) (hFL : F ≤ Subgroup.zpowers c ⊔ L)
    (hΩ : omegaA F = orbitIn (Subgroup.normalizer (F : Set G)) (Subgroup.zpowers c))
    (hcL : c ∉ L) : Sec15R G F c L := by
  have hFE : partTwoF G = partTwoE G :=
    (h.toTheoremFourHyp.partTwoF_eq_partTwoE h.partTwoS_eq).1
  have hFE' : F ∈ partTwoE G := hFE ▸ hF
  have hLc : L ∈ thetaComponentsAt 3 c := h.toSec13Data.mem_thetaComponentsAt
  have hLC : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hLc
  have hc3 : orderOf c = 3 := h.toSec13Data.orderOf_eq
  have hc3' : c ^ 3 = 1 := by rw [← hc3]; exact pow_orderOf_eq_one c
  have hcC : Subgroup.zpowers c ≤ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  have hFC : F ≤ Subgroup.centralizer ({c} : Set G) := hFL.trans (sup_le hcC hLC)
  have hcF : c ∈ F := mem_of_mem_partTwoF hF hc3' hFC
  have hcΩ : Subgroup.zpowers c ∈ omegaA F := by
    rw [hΩ]
    exact ⟨1, one_mem _, (Late.map_conj_one _).symm⟩
  have hAE : A ∈ partTwoE G := h.toSec13Data.mem_partTwoE
  have hstep : A ∈ partTwoE G ∧ F ∈ partTwoE G ∧ graphRel A F :=
    ⟨hAE, hFE', Subgroup.zpowers c, h.zpowers_mem_omegaA, Subgroup.zpowers_le.mpr hcF⟩
  have hreach : F ∈ reachE A := ⟨hFE', Relation.ReflTransGen.single hstep⟩
  have hFT : F ∉ partTwoT G := h.hypR.1 F hreach
  have hHT : HypT F := hypT_of_mem_reachE h.toTheoremFourHyp h.partTwoS_eq h.hypR hreach
  have hcN : c ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun l hl =>
      (Subgroup.mem_centralizer_singleton_iff.mp (hLC hl)))
  have hFN : F ≤ Subgroup.normalizer (L : Set G) :=
    hFL.trans (sup_le (Subgroup.zpowers_le.mpr hcN) Subgroup.le_normalizer)
  obtain ⟨f, hfF, hfL, hfc⟩ := exists_mem_inf_not_mem_zpowers_of_card hFN
    (hFN hcF) hFE'.2.1 hFL hc3 hcL
  have huniqF : ∀ L'' ∈ lA F c, L'' = L := fun L'' hL'' =>
    eq_of_mem_lA_of_mem hLc hL'' hfF hfL hfc
  obtain ⟨L'', hL''⟩ := hset G h.toPartTwoStanding h.partTwoS_eq F hF hFT c hcΩ
  have hLF : L ∈ lA F c := huniqF L'' hL'' ▸ hL''
  have hD : Sec13Data G F c L := ⟨h.toPartTwoStanding, h.partTwoS_eq, hF, hFT, hcΩ, hLF⟩
  obtain ⟨-, hchA⟩ := h.chosen136
  obtain ⟨htypes, huniq⟩ := hchA c h.zpowers_mem_omegaA L h.mem_lA
  have hch : Chosen136 F := by
    refine ⟨hF, fun c' hc' L' hL' => ?_⟩
    rw [hΩ] at hc'
    obtain ⟨x, hx, hxc⟩ := hc'
    have hzx : Subgroup.zpowers c' = Subgroup.zpowers (x * c * x⁻¹) := by
      rw [hxc, MonoidHom.map_zpowers]
      rfl
    have hL'x : L' ∈ lA F (x * c * x⁻¹) := lA_eq_of_zpowers_eq hzx ▸ hL'
    have hL'0 : L'.map (MulAut.conj x⁻¹).toMonoidHom ∈ lA F c := by
      exact (map_conj_mem_lA_iff (A := F) (L := L'.map (MulAut.conj x⁻¹).toMonoidHom) (c := c)
        hx).mp (by rwa [Late.map_conj_map_conj, mul_inv_cancel, Late.map_conj_one])
    have hL'eq : L' = L.map (MulAut.conj x).toMonoidHom := by
      have h0 := huniqF _ hL'0
      rw [← h0, Late.map_conj_map_conj, mul_inv_cancel, Late.map_conj_one]
    subst hL'eq
    refine ⟨?_, fun K hK h3 => ?_⟩
    ·
      set e := thetaQuotEquiv (MulAut.conj x) L
      rcases htypes with ⟨⟨φ⟩⟩ | h1 | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
      · exact Or.inl ⟨e.symm.trans φ⟩
      · exact Or.inr (Or.inl (isLThreePi_of_mulEquiv e.symm h1))
      · exact Or.inr (Or.inr (Or.inl ⟨e.symm.trans φ⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e.symm.trans φ⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨e.symm.trans φ⟩)))
    ·
      have hT : thetaComponentsAt 3 c' = thetaComponentsAt 3 (x * c * x⁻¹) := by
        have hC : Subgroup.centralizer ({c'} : Set G) =
            Subgroup.centralizer ({x * c * x⁻¹} : Set G) :=
          centralizer_singleton_eq_of_zpowers_eq hzx
        have key : ∀ C₁ C₂ : Subgroup G, C₁ = C₂ →
            (fun L : Subgroup ↥C₁ => L.map C₁.subtype) '' thetaComponents 3 ↥C₁ =
              (fun L : Subgroup ↥C₂ => L.map C₂.subtype) '' thetaComponents 3 ↥C₂ := by
          rintro _ _ rfl
          rfl
        exact key _ _ hC
      have hK' : K ∈ thetaComponentsAt 3 (x * c * x⁻¹) := hT ▸ hK
      have hK0 := map_mem_thetaComponentsAt (MulAut.conj x⁻¹) hK'
      have hcx : (MulAut.conj x⁻¹) (x * c * x⁻¹) = c := by
        rw [MulAut.conj_apply]
        group
      rw [hcx] at hK0
      have h3' : 3 ∣ Nat.card (K.map (MulAut.conj x⁻¹).toMonoidHom) := by
        rwa [Subgroup.card_map_of_injective (MulAut.conj x⁻¹).injective]
      have hK1 := huniq _ hK0 h3'
      rw [← hK1, Late.map_conj_map_conj, mul_inv_cancel, Late.map_conj_one]
  have hR : HypR F := by
    refine ⟨fun B hB => h.hypR.1 B ⟨hB.1, ?_⟩, hch⟩
    exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single hstep) hB.2
  exact ⟨⟨hD, Or.inr hHT, hch⟩, hR⟩

end CFSG.RankThree.PartTwo.Sec15
