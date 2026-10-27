module

public import CFSG.LocalAnalysis.StandardType.GGResILineInputs
public import CFSG.LocalAnalysis.StandardType.GGResLeaf
public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derA6
public import CFSG.LocalAnalysis.StandardType.GGHdRo7CoprimeSplit
public import CFSG.LocalAnalysis.StandardType.GGQTwoU5Bridges
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixSplit
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bA6
public import CFSG.LocalAnalysis.AGLEmbedding.AltAlpha
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight56Residual
public import CFSG.HardMathSupport.Solomon.Coordinator.I11_2VSylow
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.Alternating.Multipliers.Small
public import CFSG.Blueprint.LieModelAPI
public import CFSG.GroupTheory.CoprimeActionSupport.AbelianEquivalence
public import CFSG.GroupTheory.CoprimeActionSupport.Geometry
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264Alt
public import CFSG.LocalAnalysis.GLTheoremA.S4S.I145GW
public import CFSG.LocalAnalysis.GLTheoremA.S4S.KData
public import CFSG.LocalAnalysis.GLTheoremA.S6.InputsAlt72
public import CFSG.LocalAnalysis.RankThreeUC.Notation
public import CFSG.LocalAnalysis.RankThreeUC.Section3.CoprimeSpecialGroups.CommPowPow
public import CFSG.LocalAnalysis.RankThreeUC.Section5.ExtraspecialOrder
public import CFSG.LocalAnalysis.RankThreeUC.SourceSetting.AschbacherCommon
public import CFSG.LocalAnalysis.RankThreeUC.WeakModules
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846d
public import CFSG.LocalAnalysis.UniquenessCase.UCFront07
public import CFSG.LocalAnalysis.UniquenessCase.UCR638
public import CFSG.Milestones.CL_LIT_Gorenstein_Walter_L_balance
public import CFSG.RankThree.OddKernel.CentralCoverComponentModels

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem GGResHyp.not_B2der_of_lineJDatum_A2
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hD : GGResLineJDatum 3 Bs J .A2)
    (hJ : GGHasLabel (⟨.B2der, 0, 1⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J)) :
    False := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hJperf : commutator ↥J = ⊤ := hH.1.2.2.1.2.2.2.2.2.1.2.2.1
  haveI hJperfI : Group.IsPerfect ↥J := Group.IsPerfect.mk hJperf
  obtain ⟨e⟩ := ggB2der_label_iso_A6 hJ
  have hBN : Bs ≤ Subgroup.normalizer (J : Set G) := GGResHyp.Bs_le_normalizer_J hH
  have hinner : ∀ b ∈ Bs, ∃ j ∈ J, ∀ t ∈ J, b * t * b⁻¹ = j * t * j⁻¹ := by
    intro b hb
    have hb3 : b ^ 3 = 1 := hH.1.2.1.2.1.2 b hb
    refine CFSG.StandardType.QTwo.U5.inner_of_normalizer_pow_three J hJperf ?_ (hBN hb) hb3
    intro φ hφ
    obtain ⟨x, hx⟩ := CFSG.LocalAnalysis.GLTheoremA.alt6_aut_three_inner
      (MulAut.congr e φ) (by rw [← map_pow, hφ, map_one])
    refine ⟨e.symm x, ?_⟩
    apply (MulAut.congr e).injective
    rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj,
      MulEquiv.apply_symm_apply, hx]
  have hZcard : Nat.card (Subgroup.center ↥J) ∣ 6 := by
    have h := CFSG.AGLEmbedding.card_center_dvd_card_hopfMultiplier e
    rw [(CFSG.Alternating.Multipliers.hopfMultiplier_alternatingGroup_six).2] at h
    exact h
  have h360 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    have h := CFSG.Alternating.Multipliers.nat_card_alternatingGroup_fin 4
    simpa [Nat.factorial] using h
  have hJcard : Nat.card ↥J = 360 * Nat.card (Subgroup.center ↥J) := by
    have hq := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥J)
    have hquo : Nat.card (↥J ⧸ Subgroup.center ↥J) = 360 := by
      rw [Nat.card_congr e.toEquiv, h360]
    rw [hquo] at hq
    exact hq
  let E : Subgroup G := Bs ⊓ J
  have hEcard9 : 9 ≤ Nat.card ↥E := by
    have h := pow_rank_le_card_inf_of_lineJDatum_three hH.1.2.1 hBN hD
    rw [show (GGResLineJType.A2).rank = 2 from rfl] at h
    norm_num at h ⊢
    simpa [E] using h
  let κ : ↥J →* MulAut ↥J := MulAut.conj
  let A : Subgroup (MulAut ↥J) := (ggGamma J hBN).range
  let P : Subgroup ↥J := A.comap κ
  have hstruct := bstar_inf_le_conj_preimage_centralizes (p := 3) hH.1.2.1 hBN
  have hEP : E ≤ P.map J.subtype := by
    have h := hstruct.1
    simpa [E, P, A, κ] using h
  have hEcent : ∀ q ∈ P, ∀ e ∈ E, (q : G) * e * (q : G)⁻¹ = e := by
    intro q hq e he
    exact hstruct.2 q (by simpa [P, A, κ] using hq) e (by simpa [E] using he)
  have hAinn : A ≤ (MulAut.conj : ↥J →* MulAut ↥J).range := by
    rintro a ⟨b, rfl⟩
    obtain ⟨j, hjJ, hj⟩ := hinner b b.2
    refine ⟨⟨j, hjJ⟩, ?_⟩
    ext t
    change (j : G) * (t : G) * (j : G)⁻¹ = (b : G) * (t : G) * (b : G)⁻¹
    exact (hj (t : G) t.2).symm
  have hAea : IsElemAbelian 3 A := by
    have h := ggIsElemAbelian_range (le_refl Bs) hH.1.2.1.2.1 (ggGamma J hBN)
    simpa [A] using h
  have hA3 : IsPGroup 3 A := by
    intro a
    exact ⟨1, by
      apply Subtype.ext
      simpa using hAea.2 (a : MulAut ↥J) a.2⟩
  have hkerConj : (MulAut.conj : ↥J →* MulAut ↥J).ker = Subgroup.center ↥J := by
    ext z
    rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
    constructor
    · intro h t
      have hzt : z * t * z⁻¹ = t := by
        have := congrArg (fun f : MulAut ↥J => f t) h
        simpa [MulAut.conj_apply] using this
      have hcomm : z * t = t * z := by
        calc z * t = (z * t * z⁻¹) * z := by group
          _ = t * z := by rw [hzt]
      exact hcomm.symm
    · intro h
      ext t
      change (z : G) * (t : G) * (z : G)⁻¹ = (t : G)
      have htz : (t : G) * (z : G) = (z : G) * (t : G) := by
        simpa using congrArg (fun x : ↥J => (x : G)) (h t)
      calc (z : G) * (t : G) * (z : G)⁻¹ = ((t : G) * (z : G)) * (z : G)⁻¹ := by rw [htz]
        _ = (t : G) := by group
  have hInncard : Nat.card (MulAut.conj : ↥J →* MulAut ↥J).range = 360 := by
    have hcard := Subgroup.card_ker_mul_card_range (MulAut.conj : ↥J →* MulAut ↥J)
    rw [hkerConj, hJcard] at hcard
    have hZpos : 0 < Nat.card (Subgroup.center ↥J) := Nat.card_pos
    have hcard' : Nat.card (Subgroup.center ↥J) *
        Nat.card (MulAut.conj : ↥J →* MulAut ↥J).range =
        Nat.card (Subgroup.center ↥J) * 360 := by
      rw [hcard, mul_comm 360]
    exact Nat.mul_left_cancel hZpos hcard'
  have hA9 : Nat.card A = 9 := by
    have hAge : 9 ≤ Nat.card A := by
      have h := GGResHyp.sq_le_card_gamma_J hH
      simpa [A] using h
    have hAdvd : Nat.card A ∣ 360 := by
      have := Subgroup.card_dvd_of_le hAinn
      rwa [hInncard] at this
    obtain ⟨k, hk⟩ := hA3.exists_card_eq
    have hk2 : k ≤ 2 := by
      by_contra h
      push Not at h
      have h27 : 27 ∣ 3 ^ k := by
        have := pow_dvd_pow 3 (by omega : 3 ≤ k)
        norm_num at this ⊢
        exact this
      have : 27 ∣ 360 := by
        rw [← hk] at h27
        exact h27.trans hAdvd
      norm_num at this
    have hkge : 2 ≤ k := by
      by_contra h
      push Not at h
      rw [hk] at hAge
      interval_cases k <;> norm_num at hAge
    have hk_eq : k = 2 := le_antisymm hk2 hkge
    rw [hk, hk_eq]
    norm_num
  have hZP : Subgroup.center ↥J ≤ P := by
    intro z hz
    rw [show P = A.comap κ from rfl, Subgroup.mem_comap]
    show κ z ∈ A
    have hzker : z ∈ κ.ker := by
      rw [show κ.ker = Subgroup.center ↥J from hkerConj]
      exact hz
    rw [MonoidHom.mem_ker.mp hzker]
    exact Subgroup.one_mem A
  let f : ↥P →* MulAut ↥J := κ.comp P.subtype
  have hfker : f.ker = (Subgroup.center ↥J).subgroupOf P := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change MulAut.conj (x : ↥J) = 1 ↔ (x : ↥J) ∈ Subgroup.center ↥J
    rw [← hkerConj, MonoidHom.mem_ker]
  have hfrange : f.range = A := by
    ext a
    constructor
    · rintro ⟨x, rfl⟩
      exact x.2
    · intro ha
      have hmap : a ∈ Subgroup.map κ P := by
        rw [show P = A.comap κ from rfl,
          Subgroup.map_comap_eq_self (show A ≤ κ.range from hAinn)]
        exact ha
      obtain ⟨x, hx, hxa⟩ := hmap
      exact ⟨⟨x, hx⟩, hxa⟩
  have hPcard : Nat.card ↥P = Nat.card A * Nat.card (Subgroup.center ↥J) := by
    have hcard := Subgroup.card_ker_mul_card_range f
    rw [hfker, hfrange] at hcard
    have hz : Nat.card ↥((Subgroup.center ↥J).subgroupOf P) =
        Nat.card (Subgroup.center ↥J) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZP).toEquiv
    rw [hz] at hcard
    rw [← hcard, mul_comm]
  by_cases h3Z : 3 ∣ Nat.card (Subgroup.center ↥J)
  ·
    obtain ⟨j, hjdef⟩ := h3Z
    have hj2 : j ∣ 2 := by
      have hZcard' : 3 * j ∣ 6 := by rwa [hjdef] at hZcard
      obtain ⟨c, hc⟩ := hZcard'
      refine ⟨c, ?_⟩
      have h3 : 3 * (j * c) = 3 * 2 := by
        calc 3 * (j * c) = (3 * j) * c := by ring
          _ = 6 := hc.symm
          _ = 3 * 2 := by norm_num
      exact Nat.mul_left_cancel (by norm_num : 0 < 3) h3.symm
    have hj : j = 1 ∨ j = 2 := (Nat.dvd_prime Nat.prime_two).1 hj2
    have hPcard_j : Nat.card ↥P = 27 * j := by
      rw [hPcard, hA9, hjdef]
      ring
    have hPfac : (Nat.card ↥P).factorization 3 = 3 := by
      rcases hj with h | h
      · rw [hPcard_j, h, show (27 * 1 : ℕ) = 3 ^ 3 by norm_num,
          Nat.factorization_def _ Nat.prime_three, padicValNat.prime_pow 3]
      · rw [hPcard_j, h, show (27 * 2 : ℕ) = 3 ^ 3 * 2 by norm_num,
          Nat.factorization_def _ Nat.prime_three,
          padicValNat_base_pow_mul (p := 3) (n := 2) (by norm_num) (by norm_num)]
        rw [padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 2)]
    let E' : Subgroup ↥J := E.subgroupOf J
    have hE'P : E' ≤ P := by
      intro e he
      have heE : (e : G) ∈ E := he
      obtain ⟨q, hqP, hq⟩ := hEP heE
      have hqe : q = e := Subtype.ext hq
      rwa [← hqe]
    have hE3 : IsPGroup 3 ↥E := by
      intro x
      refine ⟨1, ?_⟩
      apply Subtype.ext
      have hx : ((x : ↥E) : G) ∈ Bs := (Subgroup.mem_inf.mp x.2).1
      simpa using hH.1.2.1.2.1.2 ((x : ↥E) : G) hx
    have hE'3 : IsPGroup 3 ↥E' :=
      IsPGroup.of_equiv hE3 (Subgroup.subgroupOfEquivOfLe (show E ≤ J from inf_le_right)).symm
    let E'' : Subgroup ↥P := E'.subgroupOf P
    have hE''3 : IsPGroup 3 ↥E'' :=
      IsPGroup.of_equiv hE'3 (Subgroup.subgroupOfEquivOfLe hE'P).symm
    obtain ⟨S, hE''S⟩ := IsPGroup.exists_le_sylow (p := 3) hE''3
    have hScard : Nat.card ↥(S : Subgroup ↥P) = 27 := by
      rw [Sylow.card_eq_multiplicity, hPfac]
      norm_num
    let Ssub : Subgroup ↥J := (S : Subgroup ↥P).map P.subtype
    have hSsubcard : Nat.card ↥Ssub = 27 := by
      rw [Subgroup.card_map_of_injective P.subtype_injective, hScard]
    have hSsubP : Ssub ≤ P := by
      rintro _ ⟨s, -, rfl⟩
      exact s.2
    have hE'Ssub : E' ≤ Ssub := by
      intro e he
      have he'' : (⟨e, hE'P he⟩ : ↥P) ∈ E'' := he
      exact ⟨⟨e, hE'P he⟩, hE''S he'', rfl⟩
    have hSsub3 : IsPGroup 3 ↥Ssub :=
      IsPGroup.of_equiv (Sylow.isPGroup' S)
        (Subgroup.equivMapOfInjective (S : Subgroup ↥P) P.subtype P.subtype_injective)
    obtain ⟨SJ, hSsubSJ⟩ := IsPGroup.exists_le_sylow (p := 3) hSsub3
    have hJfac : (Nat.card ↥J).factorization 3 = 3 := by
      rcases hj with h | h
      · have hjv : Nat.card ↥J = 3 ^ 3 * 40 := by rw [hJcard, hjdef, h]; norm_num
        rw [hjv, Nat.factorization_def _ Nat.prime_three,
          padicValNat_base_pow_mul (p := 3) (n := 40) (by norm_num) (by norm_num)]
        rw [padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 40)]
      · have hjv : Nat.card ↥J = 3 ^ 3 * 80 := by rw [hJcard, hjdef, h]; norm_num
        rw [hjv, Nat.factorization_def _ Nat.prime_three,
          padicValNat_base_pow_mul (p := 3) (n := 80) (by norm_num) (by norm_num)]
        rw [padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 80)]
    have hSJcard : Nat.card ↥(SJ : Subgroup ↥J) = 27 := by
      rw [Sylow.card_eq_multiplicity, hJfac]
      norm_num
    have hSJeq : Ssub = (SJ : Subgroup ↥J) :=
      Subgroup.eq_of_le_of_card_ge hSsubSJ (by rw [hSsubcard, hSJcard])
    have hSJP : (SJ : Subgroup ↥J) ≤ P := by
      rw [← hSJeq]
      exact hSsubP
    have hE'SJ : E' ≤ (SJ : Subgroup ↥J) := hE'Ssub.trans hSsubSJ
    obtain ⟨sx, hsxSJ, sy, hsySJ, hxy⟩ :=
      CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.sylow_three_noncomm_of_perfect_of_center
        hJperfI ⟨j, hjdef⟩ SJ
    have hna : ∃ r s : ↥(SJ : Subgroup ↥J), r * s ≠ s * r := by
      refine ⟨⟨sx, hsxSJ⟩, ⟨sy, hsySJ⟩, ?_⟩
      intro h
      exact hxy (congrArg Subtype.val h)
    have hZScard : Nat.card (Subgroup.center ↥(SJ : Subgroup ↥J)) = 3 :=
      CFSG.HardMathSupport.Solomon.Coordinator.i112v_card_center_eq_three hSJcard hna
    have hEZ : E ≤ ((Subgroup.center ↥(SJ : Subgroup ↥J)).map
        (SJ : Subgroup ↥J).subtype).map J.subtype := by
      intro e he
      have heJ : e ∈ J := (Subgroup.mem_inf.mp he).2
      have heE' : (⟨e, heJ⟩ : ↥J) ∈ E' := he
      have heSJ : (⟨e, heJ⟩ : ↥J) ∈ (SJ : Subgroup ↥J) := hE'SJ heE'
      refine ⟨⟨e, heJ⟩, ?_, rfl⟩
      refine ⟨⟨⟨e, heJ⟩, heSJ⟩, ?_, rfl⟩
      change (⟨⟨e, heJ⟩, heSJ⟩ : ↥(SJ : Subgroup ↥J)) ∈
        Subgroup.center ↥(SJ : Subgroup ↥J)
      rw [Subgroup.mem_center_iff]
      intro s
      apply Subtype.ext
      apply Subtype.ext
      have hsP : (s : ↥J) ∈ P := hSJP s.2
      have hcomm := hEcent (s : ↥J) hsP e he
      simp only [Subgroup.coe_mul, Subtype.coe_mk]
      change ((s : ↥J) : G) * (e : G) = (e : G) * ((s : ↥J) : G)
      calc ((s : ↥J) : G) * (e : G) =
          (((s : ↥J) : G) * e * (((s : ↥J) : G))⁻¹) * ((s : ↥J) : G) := by group
        _ = (e : G) * ((s : ↥J) : G) := by rw [hcomm]
    have hEZcard : Nat.card ↥E ≤ 3 := by
      calc Nat.card ↥E ≤ Nat.card ↥(((Subgroup.center ↥(SJ : Subgroup ↥J)).map
            (SJ : Subgroup ↥J).subtype).map J.subtype) := Subgroup.card_le_of_le hEZ
        _ = Nat.card ↥((Subgroup.center ↥(SJ : Subgroup ↥J)).map
              (SJ : Subgroup ↥J).subtype) :=
            Subgroup.card_map_of_injective J.subtype_injective
        _ = Nat.card (Subgroup.center ↥(SJ : Subgroup ↥J)) :=
            Subgroup.card_map_of_injective (SJ : Subgroup ↥J).subtype_injective
        _ = 3 := hZScard
    omega
  ·
    have hcop : Nat.Coprime 3 (Nat.card (Subgroup.center ↥J)) :=
      (Nat.prime_three.coprime_iff_not_dvd).mpr h3Z
    have hsplitpt : ∀ b ∈ Bs,
        ∃ q ∈ Bs ⊓ J, ∃ c ∈ Bs ⊓ Subgroup.centralizer (J : Set G), b = q * c :=
      ggBstar_split_of_inner_coprime Nat.prime_three hH.1.2.1 hcop hBN hinner
    have hsplit : Bs = (Bs ⊓ J) ⊔ (Bs ⊓ Subgroup.centralizer (J : Set G)) := by
      apply le_antisymm
      · intro b hb
        obtain ⟨q, hq, c, hc, rfl⟩ := hsplitpt b hb
        exact Subgroup.mul_mem_sup hq hc
      · exact sup_le inf_le_left inf_le_left
    have h27E : 27 ≤ Nat.card ↥E := by
      have h := card_inf_ge_twentyseven_of_lineJDatum_A2_of_split
        hH.1.2.1 hsplit hH.2.2.2.1 hD
      simpa [E] using h
    have hZ12 : Nat.card (Subgroup.center ↥J) = 1 ∨ Nat.card (Subgroup.center ↥J) = 2 := by
      have hm2 : Nat.card (Subgroup.center ↥J) ∣ 2 := by
        have h6 : Nat.card (Subgroup.center ↥J) ∣ 3 * 2 := by
          rw [mul_comm]
          exact hZcard
        exact (Nat.Coprime.symm hcop).dvd_of_dvd_mul_left h6
      rcases (Nat.dvd_prime Nat.prime_two).1 hm2 with h | h
      · exact Or.inl h
      · exact Or.inr h
    have hJval : Nat.card ↥J = 360 ∨ Nat.card ↥J = 720 := by
      rcases hZ12 with h | h
      · left; rw [hJcard, h]
      · right; rw [hJcard, h]
    have hE3 : IsPGroup 3 ↥E := by
      intro x
      refine ⟨1, ?_⟩
      apply Subtype.ext
      have hx : ((x : ↥E) : G) ∈ Bs := (Subgroup.mem_inf.mp x.2).1
      simpa using hH.1.2.1.2.1.2 ((x : ↥E) : G) hx
    obtain ⟨k, hk⟩ := hE3.exists_card_eq
    have hk2 : k ≤ 2 := by
      by_contra h
      push Not at h
      have h27 : 27 ∣ 3 ^ k := by
        have := pow_dvd_pow 3 (by omega : 3 ≤ k)
        norm_num at this ⊢
        exact this
      have : 27 ∣ Nat.card ↥J := by
        rw [← hk] at h27
        exact h27.trans (Subgroup.card_dvd_of_le (show E ≤ J from inf_le_right))
      rcases hJval with hjv | hjv <;> (rw [hjv] at this; norm_num at this)
    have hEle9 : Nat.card ↥E ≤ 9 := by
      calc Nat.card ↥E = 3 ^ k := hk
        _ ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
        _ = 9 := by norm_num
    omega

end CFSG.StandardType

end
