module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenTwentyFive72
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFactsNineteenR
public import CFSG.GroupTheory.InvertingLift
public import CFSG.Monster.B.Recog.GenericGoldschmidtArith
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenTwentyTwoP

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

variable {G : Type} [Group G] [Finite G]


theorem nineteen_glue_four (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp19 D V₀ V p L) (h1910 : Setting1910 D V₀ V p L) (h42 : S17.R17_42At D V₀ V)
    (htorus : K_19_glue4_torus) :
    ∃ A t B r, Ctx19_10 D V₀ V p L A t B r ∧ (3 ∈ piSet A → r = 3) := by
  classical
  let n : ℕ := S17.nOf L
  let I : Subgroup G := IOf D p L
  have hLcalC : L ∈ calC D.M := h.hL.1
  have hIleM : I ≤ D.M := IOf_le_M D p hLcalC.1.le
  have hInormM : (I.subgroupOf D.M).Normal := IOf_normal D p hLcalC
  have hMleNI : D.M ≤ normalizer (I : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hIleM).mp hInormM
  have hTM : D.T ≤ D.M := D.sylowM.le
  have hn3 : 3 ≤ n := three_le_nOf_of_setting1910 h1910
  have hshape : IsSp4 (Bar2 I) n ∨ IsL2Square (Bar2 I) n ∨ IsSzSquare (Bar2 I) n ∨
      S17.IsL2U3Product (Bar2 I) n := by
    rcases h1910 with ⟨-, h1 | h2 | h3⟩
    · exact Or.inl h1.1
    · obtain ⟨-, x, hxM, hXsup, hne, -, -⟩ :=
        S17.p42_alt2_of_ne h42 h.hp hLcalC h2.2.1
      rcases h2.2.2.2 with ⟨hL2, -⟩ | ⟨hSz, -⟩
      · refine Or.inr (Or.inl ?_)
        have hsq := isL2Square_bar2_conjClosure hLcalC hxM hXsup hne hL2
        have hIeq : I = conjClosure D.M L := h2.1
        rw [← hIeq] at hsq
        exact hsq
      · refine Or.inr (Or.inr (Or.inl ?_))
        have hsq := isSzSquare_bar2_conjClosure hLcalC hxM hXsup hne hSz
        have hIeq : I = conjClosure D.M L := h2.1
        rw [← hIeq] at hsq
        exact hsq
    · rcases h3.1 with hs | hs
      · exact Or.inr (Or.inr (Or.inr hs))
      · exact Or.inr (Or.inl hs)
  let Q : Subgroup G := D.T ⊓ I
  have hQleI : Q ≤ I := inf_le_right
  have hQsyl : CFSG.ABGLocalTools.IsSylowOf 2 Q I :=
    CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer D.sylowM hIleM hMleNI
  have hQmap : (Q.subgroupOf I).map I.subtype = Q :=
    Subgroup.map_subgroupOf_eq_of_le hQleI
  have hQHsyl : CFSG.ABGLocalTools.IsSylowOf 2 (Q.subgroupOf I) ⊤ := by
    have h1 : CFSG.ABGLocalTools.IsSylowOf 2 ((Q.subgroupOf I).map I.subtype)
        ((⊤ : Subgroup ↥I).map I.subtype) := by
      rw [hQmap, Subgroup.map_top, Subgroup.range_subtype]
      exact hQsyl
    exact (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff I).1 h1
  have hP_G_le_T : CFSG.Open.pCoreOf 2 I ≤ D.T :=
    CFSG.GH74.Uniqueness.le_of_isSylowOf_of_isPGroup_normal D.sylowM
      (CFSG.LieType.BorelTits.pCoreOf_le 2 I |>.trans hIleM)
      (hMleNI.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 I))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 I)
  let P' : Subgroup ↥I := CFSG.pCore 2 ↥I
  let π : ↥I →* Bar2 I := QuotientGroup.mk' P'
  have hπ_one : ∀ x : ↥I, π x = 1 ↔ x ∈ P' := by
    intro x
    change (QuotientGroup.mk' P') x = 1 ↔ x ∈ P'
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  let Ū : Subgroup (Bar2 I) := (Q.subgroupOf I).map π
  have hŪsyl : CFSG.ABGLocalTools.IsSylowOf 2 Ū ⊤ :=
    uc22p22r_isSylowOf_map_top (QuotientGroup.mk'_surjective P') hQHsyl
  obtain ⟨A₁, tbar, hA₁N, hA₁sq, hchar, htbar2, htbarinv⟩ :=
    htorus (Bar2 I) n hn3 hshape Ū hŪsyl
  let B : Subgroup (Bar2 I) := A₁ ⊔ Ū
  have hBle : B ≤ normalizer (Ū : Set (Bar2 I)) :=
    sup_le hA₁N Subgroup.le_normalizer
  have hBcoe : (B : Set (Bar2 I)) = (A₁ : Set (Bar2 I)) * (Ū : Set (Bar2 I)) :=
    Subgroup.coe_mul_of_left_le_normalizer_right A₁ Ū hA₁N
  have hkerP'leQH : P' ≤ Q.subgroupOf I := by
    intro z hz
    rw [Subgroup.mem_subgroupOf]
    refine ⟨?_, z.2⟩
    have hzG : (z : G) ∈ CFSG.Open.pCoreOf 2 I := Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
    exact hP_G_le_T hzG
  have hŪcomap : Ū.comap π = Q.subgroupOf I := by
    ext z
    rw [Subgroup.mem_comap]
    constructor
    · intro hz
      obtain ⟨q, hq, hqz⟩ := Subgroup.mem_map.mp hz
      have hzq : π (z * q⁻¹) = 1 := by
        rw [map_mul, map_inv, hqz, mul_inv_cancel]
      have hmem : z * q⁻¹ ∈ P' := (hπ_one _).mp hzq
      have h1 : z = (z * q⁻¹) * q := by group
      rw [h1]
      exact (Q.subgroupOf I).mul_mem (hkerP'leQH hmem) hq
    · intro hz
      exact Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
  have hNQiff : ∀ x : ↥I, x ∈ normalizer ((Q.subgroupOf I : Subgroup ↥I) : Set ↥I) ↔
      (x : G) ∈ normalizer (Q : Set G) := by
    intro x
    rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
    constructor
    · intro hx y
      by_cases hy : y ∈ I
      · simpa [Subgroup.mem_subgroupOf] using hx ⟨y, hy⟩
      · have hxy : (x : G) * y * (x : G)⁻¹ ∉ I := by
          intro hmem
          have h2 : (x : G)⁻¹ * ((x : G) * y * (x : G)⁻¹) * (x : G) ∈ I :=
            I.mul_mem (I.mul_mem (I.inv_mem x.2) hmem) x.2
          have e : (x : G)⁻¹ * ((x : G) * y * (x : G)⁻¹) * (x : G) = y := by group
          rw [e] at h2
          exact hy h2
        exact ⟨fun hyQ => absurd (hQleI hyQ) hy, fun hc => absurd (hQleI hc) hxy⟩
    · intro hx y
      simpa [Subgroup.mem_subgroupOf] using hx (y : G)
  let W' : Subgroup ↥I := A₁.comap π
  have hP'leW' : P' ≤ W' := by
    intro z hz
    rw [Subgroup.mem_comap]
    show π z ∈ A₁
    rw [(hπ_one z).mpr hz]
    exact A₁.one_mem
  let f : ↥W' →* Bar2 I := π.comp W'.subtype
  have hfker : f.ker = P'.subgroupOf W' := by
    ext z
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hz
      exact (hπ_one z).mp hz
    · intro hz
      exact (hπ_one z).mpr hz
  have hfrange : f.range = A₁ := by
    ext y
    constructor
    · rintro ⟨z, -, rfl⟩
      exact z.2
    · intro hy
      obtain ⟨z, hz⟩ := QuotientGroup.mk'_surjective P' y
      exact ⟨⟨z, by show π z ∈ A₁; rw [hz]; exact hy⟩, hz⟩
  have hkerindex : (P'.subgroupOf W').index = Nat.card ↥A₁ := by
    rw [← hfker, Subgroup.index_ker, hfrange]
  have hcardP'sub : Nat.card ↥(P'.subgroupOf W') = Nat.card ↥P' :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP'leW').toEquiv
  have hoddA₁ : Odd (Nat.card ↥A₁) := by
    rw [card_eq_of_isZModSq hA₁sq]
    exact (CFSG.Monster.B.Recog.GoldschmidtArith.odd_two_pow_sub_one (by omega)).mul
      (CFSG.Monster.B.Recog.GoldschmidtArith.odd_two_pow_sub_one (by omega))
  have hcop : Nat.Coprime (Nat.card ↥(P'.subgroupOf W')) (P'.subgroupOf W').index := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥I))
    rw [hcardP'sub, hkerindex, hk]
    exact Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hoddA₁)
  obtain ⟨C, hC⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  let A_H : Subgroup ↥I := C.map W'.subtype
  let A_G : Subgroup G := A_H.map I.subtype
  let g : ↥C →* ↥A₁ := (f.comp C.subtype).codRestrict A₁ (fun c => (c : ↥W').2)
  have hg_inj : Function.Injective g := by
    intro c₁ c₂ hcc
    have h1 : π ((c₁ : ↥W') : ↥I) = π ((c₂ : ↥W') : ↥I) := by
      have h1' : ((g c₁ : ↥A₁) : Bar2 I) = ((g c₂ : ↥A₁) : Bar2 I) :=
        congrArg Subtype.val hcc
      have e1 : ((g c₁ : ↥A₁) : Bar2 I) = π ((c₁ : ↥W') : ↥I) := rfl
      have e2 : ((g c₂ : ↥A₁) : Bar2 I) = π ((c₂ : ↥W') : ↥I) := rfl
      rw [e1, e2] at h1'
      exact h1'
    set d : ↥W' := ⟨((c₁ : ↥W') : ↥I)⁻¹ * ((c₂ : ↥W') : ↥I),
      W'.mul_mem (W'.inv_mem (c₁ : ↥W').2) (c₂ : ↥W').2⟩ with hd
    have hdval : (d : ↥I) = ((c₁ : ↥W') : ↥I)⁻¹ * ((c₂ : ↥W') : ↥I) := rfl
    have hdP : d ∈ P'.subgroupOf W' := by
      refine Subgroup.mem_subgroupOf.mpr ((hπ_one _).mp ?_)
      rw [hdval, map_mul, map_inv, h1, inv_mul_cancel]
    have hdC : d ∈ C := by
      rw [hd]
      exact C.mul_mem (C.inv_mem c₁.2) c₂.2
    have h5 : d ∈ P'.subgroupOf W' ⊓ C := ⟨hdP, hdC⟩
    rw [Subgroup.IsComplement'.disjoint hC |>.eq_bot] at h5
    have h6 : d = 1 := Subgroup.mem_bot.mp h5
    have h7 : ((c₁ : ↥W') : ↥I) = ((c₂ : ↥W') : ↥I) := by
      have hv : ((c₁ : ↥W') : ↥I)⁻¹ * ((c₂ : ↥W') : ↥I) = 1 := by
        rw [← hdval]; exact congrArg Subtype.val h6
      have := congrArg (fun z => ((c₁ : ↥W') : ↥I) * z) hv
      simpa using this.symm
    exact Subtype.ext (Subtype.ext h7)
  have hg_surj : Function.Surjective g := by
    intro a
    obtain ⟨z, hz⟩ := QuotientGroup.mk'_surjective P' (a : ↥A₁)
    have hzW' : z ∈ W' := by
      show π z ∈ A₁
      rw [hz]
      exact a.2
    have hmul : (P'.subgroupOf W' : Set ↥W') * (C : Set ↥W') = Set.univ :=
      (Subgroup.isComplement'_def.mp hC).mul_eq
    have hz'' : (⟨z, hzW'⟩ : ↥W') ∈ (P'.subgroupOf W' : Set ↥W') * (C : Set ↥W') := by
      rw [hmul]
      trivial
    obtain ⟨p, hp, c, hc, hpc⟩ := hz''
    refine ⟨⟨c, hc⟩, ?_⟩
    apply Subtype.ext
    have hpc' : (p : ↥I) * (c : ↥I) = z := by
      have hpc'' : ((p : ↥W') : ↥I) * ((c : ↥W') : ↥I) = z := by
        have := congrArg (fun t : ↥W' => (t : ↥I)) hpc
        simpa using this
      simpa using hpc''
    have hpp : π (p : ↥I) = 1 := by
      exact (hπ_one _).mpr (Subgroup.mem_subgroupOf.mp hp)
    show π ((c : ↥W') : ↥I) = (a : ↥A₁)
    calc π ((c : ↥W') : ↥I) = π (p : ↥I) * π ((c : ↥W') : ↥I) := by rw [hpp, one_mul]
      _ = π ((p : ↥I) * (c : ↥I)) := by rw [map_mul]
      _ = π z := by rw [hpc']
      _ = (a : ↥A₁) := hz
  let eCA : ↥C ≃* ↥A₁ := MulEquiv.ofBijective g ⟨hg_inj, hg_surj⟩
  let eAC : ↥A_H ≃* ↥C :=
    (Subgroup.equivMapOfInjective C W'.subtype W'.subtype_injective).symm
  let eGA : ↥A_G ≃* ↥A_H :=
    (Subgroup.equivMapOfInjective A_H I.subtype I.subtype_injective).symm
  let eAG : ↥A_G ≃* ↥A₁ := eGA.trans (eAC.trans eCA)
  have hcardAG : Nat.card ↥A_G = Nat.card ↥A₁ := Nat.card_congr eAG.toEquiv
  have hcardAH : Nat.card ↥A_H = Nat.card ↥A₁ :=
    Nat.card_congr (eAC.trans eCA).toEquiv
  have hoddAH : Odd (Nat.card ↥A_H) := by
    rw [hcardAH]
    exact hoddA₁
  have hAGsq : IsZModSq A_G n := by
    obtain ⟨e₁⟩ := hA₁sq
    exact ⟨eAG.trans e₁⟩
  have hLiftA : ∀ a₁ ∈ A₁, ∃ aH ∈ A_H, π aH = a₁ := by
    intro a₁ ha₁
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective P' a₁
    have hyW' : y ∈ W' := by
      show π y ∈ A₁
      rw [hy]
      exact ha₁
    have hmul : (P'.subgroupOf W' : Set ↥W') * (C : Set ↥W') = Set.univ :=
      (Subgroup.isComplement'_def.mp hC).mul_eq
    have hy'' : (⟨y, hyW'⟩ : ↥W') ∈ (P'.subgroupOf W' : Set ↥W') * (C : Set ↥W') := by
      rw [hmul]
      trivial
    obtain ⟨p, hp, c, hc, hpc⟩ := hy''
    refine ⟨((c : ↥W') : ↥I), Subgroup.mem_map.mpr ⟨(c : ↥W'), hc, rfl⟩, ?_⟩
    have hpc' : (p : ↥I) * (c : ↥I) = y := by
      have hpc'' : ((p : ↥W') : ↥I) * ((c : ↥W') : ↥I) = y := by
        have := congrArg (fun t : ↥W' => (t : ↥I)) hpc
        simpa using this
      simpa using hpc''
    have hpp : π (p : ↥I) = 1 := by
      exact (hπ_one _).mpr (Subgroup.mem_subgroupOf.mp hp)
    calc π ((c : ↥W') : ↥I) = π (p : ↥I) * π ((c : ↥W') : ↥I) := by rw [hpp, one_mul]
      _ = π ((p : ↥I) * (c : ↥I)) := by rw [map_mul]
      _ = π y := by rw [hpc']
      _ = a₁ := hy
  have hAHN : A_H ≤ normalizer ((Q.subgroupOf I : Subgroup ↥I) : Set ↥I) := by
    intro a ha
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp ha
    have hcA₁ : π ((c : ↥W') : ↥I) ∈ A₁ := (c : ↥W').2
    have hcN : π ((c : ↥W') : ↥I) ∈ normalizer (Ū : Set (Bar2 I)) := hA₁N hcA₁
    have h1 : ((c : ↥W') : ↥I) ∈ (normalizer (Ū : Set (Bar2 I))).comap π := hcN
    rwa [Subgroup.comap_normalizer_eq_of_surjective Ū (QuotientGroup.mk'_surjective P'),
      hŪcomap] at h1
  have hAQ : A_G ≤ normalizer (Q : Set G) := by
    intro a ha
    obtain ⟨aH, haH, rfl⟩ := Subgroup.mem_map.mp ha
    exact (hNQiff aH).mp (hAHN haH)
  let W_H : Subgroup ↥I := B.comap π
  let W_G : Subgroup G := W_H.map I.subtype
  have hWmem : ∀ x : G, x ∈ W_G ↔ x ∈ I ∧ x ∈ normalizer (Q : Set G) ∧
      x ^ (2 ^ n - 1) ∈ Q := by
    intro x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      have hB : π y ∈ B := hy
      have hyN : π y ∈ normalizer (Ū : Set (Bar2 I)) := hBle hB
      have hypow : (π y) ^ (2 ^ n - 1) ∈ Ū := (hchar (π y) hyN).mpr hB
      have hyN' : y ∈ normalizer ((Q.subgroupOf I : Subgroup ↥I) : Set ↥I) := by
        have h1 : y ∈ (normalizer (Ū : Set (Bar2 I))).comap π := hyN
        rwa [Subgroup.comap_normalizer_eq_of_surjective Ū (QuotientGroup.mk'_surjective P'),
          hŪcomap] at h1
      have hypow' : y ^ (2 ^ n - 1) ∈ Q.subgroupOf I := by
        rw [← hŪcomap]
        exact Subgroup.mem_comap.mpr (by rw [map_pow]; exact hypow)
      refine ⟨y.2, (hNQiff y).mp hyN', ?_⟩
      simpa using Subgroup.mem_subgroupOf.mp hypow'
    · rintro ⟨hxI, hxN, hxpow⟩
      refine Subgroup.mem_map.mpr ⟨⟨x, hxI⟩, ?_, rfl⟩
      have hxN' : (⟨x, hxI⟩ : ↥I) ∈ normalizer ((Q.subgroupOf I : Subgroup ↥I) : Set ↥I) :=
        (hNQiff _).mpr hxN
      have hxpow' : (⟨x, hxI⟩ : ↥I) ^ (2 ^ n - 1) ∈ Q.subgroupOf I := by
        exact Subgroup.mem_subgroupOf.mpr (by simpa using hxpow)
      have hxNbar : π ⟨x, hxI⟩ ∈ normalizer (Ū : Set (Bar2 I)) := by
        have h1 : (⟨x, hxI⟩ : ↥I) ∈ (normalizer (Ū : Set (Bar2 I))).comap π := by
          rwa [Subgroup.comap_normalizer_eq_of_surjective Ū (QuotientGroup.mk'_surjective P'),
            hŪcomap]
        exact h1
      have hxpowbar : (π ⟨x, hxI⟩) ^ (2 ^ n - 1) ∈ Ū := by
        have h1 : (⟨x, hxI⟩ : ↥I) ^ (2 ^ n - 1) ∈ Ū.comap π := by
          rwa [hŪcomap]
        exact Subgroup.mem_comap.mp h1
      exact (hchar _ hxNbar).mp hxpowbar
  have hAGleW : A_G ≤ W_G := by
    intro a ha
    obtain ⟨aH, haH, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp haH
    exact Subgroup.mem_map.mpr ⟨(c : ↥W'),
      Subgroup.mem_comap.mpr (Subgroup.mem_sup_left ((c : ↥W').2)), rfl⟩
  have hQleW : Q ≤ W_G := by
    rw [← hQmap]
    rintro _ ⟨q, hq, rfl⟩
    exact Subgroup.mem_map.mpr ⟨q,
      Subgroup.mem_comap.mpr (Subgroup.mem_sup_right (Subgroup.mem_map.mpr ⟨q, hq, rfl⟩)), rfl⟩
  have hWset : ∀ x : G, x ∈ W_G ↔ x ∈ (A_G : Set G) * (Q : Set G) := by
    intro x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      have hyB : π y ∈ B := Subgroup.mem_comap.mp hy
      have hyB' : π y ∈ (A₁ : Set (Bar2 I)) * (Ū : Set (Bar2 I)) := by
        rwa [← hBcoe]
      obtain ⟨a₁, ha₁, u, hu, hdecomp⟩ := hyB'
      obtain ⟨aH, haH, hpaH⟩ := hLiftA a₁ ha₁
      obtain ⟨qH, hqH, hpqH⟩ := Subgroup.mem_map.mp hu
      have hker : y * (aH * qH)⁻¹ ∈ P' := by
        have h1 : π (y * (aH * qH)⁻¹) = 1 := by
          rw [map_mul, map_inv, map_mul, hpaH, hpqH, ← hdecomp, mul_inv_cancel]
        exact (hπ_one _).mp h1
      have hP'GleQ : P'.map I.subtype ≤ Q := by
        rw [← hQmap]
        exact Subgroup.map_mono hkerP'leQH
      have hpG : (((y * (aH * qH)⁻¹ : ↥I)) : G) ∈ Q :=
        hP'GleQ (Subgroup.mem_map.mpr ⟨y * (aH * qH)⁻¹, hker, rfl⟩)
      have haG : (aH : G) ∈ A_G := Subgroup.mem_map.mpr ⟨aH, haH, rfl⟩
      have hqG : (qH : G) ∈ Q := by
        rw [← hQmap]
        exact Subgroup.mem_map.mpr ⟨qH, hqH, rfl⟩
      have hx_eq : (y : G) = (((y * (aH * qH)⁻¹ : ↥I)) : G) * (aH : G) * (qH : G) := by
        have h1 : y = (y * (aH * qH)⁻¹) * aH * qH := by group
        exact congrArg Subtype.val h1
      have hconj : (aH : G)⁻¹ * (((y * (aH * qH)⁻¹ : ↥I)) : G) * (aH : G) ∈ Q := by
        have h := (Subgroup.mem_normalizer_iff.mp (hAQ (A_G.inv_mem haG)) _).mp hpG
        simpa using h
      change (y : G) ∈ (A_G : Set G) * (Q : Set G)
      rw [hx_eq]
      refine ⟨(aH : G), haG,
        (aH : G)⁻¹ * (((y * (aH * qH)⁻¹ : ↥I)) : G) * (aH : G) * (qH : G),
        Q.mul_mem hconj hqG, ?_⟩
      group
    · rintro ⟨a, ha, q, hq, rfl⟩
      exact W_G.mul_mem (hAGleW ha) (hQleW hq)
  have hWGeq : W_G = A_G ⊔ Q := by
    apply le_antisymm
    · intro x hx
      have hx' : x ∈ (A_G : Set G) * (Q : Set G) := (hWset x).mp hx
      obtain ⟨a, ha, q, hq, rfl⟩ := hx'
      exact Subgroup.mul_mem_sup ha hq
    · exact sup_le hAGleW hQleW
  have hTQ : D.T ≤ normalizer (Q : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxT, hxI⟩
      refine ⟨D.T.mul_mem (D.T.mul_mem ht hxT) (D.T.inv_mem ht), ?_⟩
      exact (Subgroup.mem_normalizer_iff.mp (hMleNI (hTM ht)) x).mp hxI
    · rintro ⟨hxT, hxI⟩
      have hxT' : t⁻¹ * (t * x * t⁻¹) * t ∈ D.T :=
        D.T.mul_mem (D.T.mul_mem (D.T.inv_mem ht) hxT) ht
      have e1 : t⁻¹ * (t * x * t⁻¹) * t = x := by group
      have hxI' : t⁻¹ * (t * x * t⁻¹) * t ∈ I := by
        have h := (Subgroup.mem_normalizer_iff.mp (hMleNI (hTM (D.T.inv_mem ht)))
          (t * x * t⁻¹)).mp hxI
        simpa using h
      exact ⟨e1 ▸ hxT', e1 ▸ hxI'⟩
  have hWT : D.T ≤ normalizer (W_G : Set G) := by
    have hconj : ∀ u ∈ D.T, ∀ z ∈ W_G, u * z * u⁻¹ ∈ W_G := by
      intro u hu z hz
      obtain ⟨hzI, hzN, hzpow⟩ := (hWmem z).mp hz
      have huI : u * z * u⁻¹ ∈ I :=
        (Subgroup.mem_normalizer_iff.mp (hMleNI (hTM hu)) z).mp hzI
      have huN : u * z * u⁻¹ ∈ normalizer (Q : Set G) :=
        (normalizer (Q : Set G)).mul_mem ((normalizer (Q : Set G)).mul_mem (hTQ hu) hzN)
          ((normalizer (Q : Set G)).inv_mem (hTQ hu))
      have hupow : (u * z * u⁻¹) ^ (2 ^ n - 1) = u * z ^ (2 ^ n - 1) * u⁻¹ := by
        rw [conj_pow]
      have hupowQ : u * z ^ (2 ^ n - 1) * u⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp (hTQ hu) _).mp hzpow
      exact (hWmem (u * z * u⁻¹)).mpr ⟨huI, huN, hupow ▸ hupowQ⟩
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact hconj t ht x
    · intro hx
      have h1 := hconj t⁻¹ (D.T.inv_mem ht) (t * x * t⁻¹) hx
      have hx' : t⁻¹ * (t * x * t⁻¹) * t⁻¹⁻¹ = x := by group
      rwa [hx'] at h1
  have hPerm : Permutes A_G D.T :=
    TwelveNineteen.permutes_of_le_normalizer_sup inf_le_left
      (by rwa [hWGeq] at hWT) hAQ
  obtain ⟨t₀, ht₀⟩ := QuotientGroup.mk'_surjective P' tbar
  have hkerP' : π.ker = P' := QuotientGroup.ker_mk' P'
  have ht0g : IsPGroup 2 (Subgroup.zpowers tbar) := by
    obtain ⟨k, hk⟩ := htbar2
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  have hV : IsPGroup 2 ((Subgroup.zpowers tbar).comap π) :=
    ht0g.comap_of_ker_isPGroup π (by rw [hkerP']; exact CFSG.pCore_isPGroup)
  have ht₀2 : ∃ k : ℕ, orderOf t₀ = 2 ^ k := by
    obtain ⟨k, hk⟩ := hV.exists_orderOf_eq_pow
      ⟨t₀, Subgroup.mem_comap.mpr (by rw [ht₀]; exact Subgroup.mem_zpowers tbar)⟩
    exact ⟨k, (Subgroup.orderOf_coe _).trans hk⟩
  have hAHleW' : A_H ≤ W' := by
    intro a ha
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp ha
    exact (c : ↥W').2
  have hinvH : ∀ a ∈ A_H, t₀ * a * t₀⁻¹ * a ∈ P' := by
    intro a ha
    have hpa : π a ∈ A₁ := hAHleW' ha
    have h1 : π (t₀ * a * t₀⁻¹ * a) = 1 := by
      have e : π (t₀ * a * t₀⁻¹ * a) = π t₀ * π a * (π t₀)⁻¹ * π a := by
        rw [map_mul, map_mul, map_mul, map_inv]
      rw [e, ht₀, htbarinv (π a) hpa, inv_mul_cancel]
    exact (hπ_one _).mp h1
  obtain ⟨y, hyP', htorder, htinv⟩ :=
    CFSG.GroupTheory.exists_inverting_of_inverting_mod (G := ↥I) (P := P') (A := A_H)
      (t₀ := t₀) CFSG.pCore_isPGroup
      (Subgroup.le_normalizer_of_normal (H := P') (K := A_H)) hoddAH
      ((Subgroup.le_normalizer_of_normal (H := P') (K := ⊤)) (Subgroup.mem_top t₀))
      ht₀2 hinvH
  let t_H : ↥I := y * t₀
  let t_G : G := (t_H : G)
  have htA : t_G ∈ I := t_H.2
  have ht2 : ∃ k : ℕ, orderOf t_G = 2 ^ k := by
    obtain ⟨k, hk⟩ := htorder
    exact ⟨k, (Subgroup.orderOf_coe t_H).trans hk⟩
  have hinvG : ∀ a ∈ A_G, t_G * a * t_G⁻¹ = a⁻¹ := by
    intro a ha
    obtain ⟨aH, haH, rfl⟩ := Subgroup.mem_map.mp ha
    have h1 : ((y * t₀) * aH * (y * t₀)⁻¹ : ↥I) = aH⁻¹ := htinv aH haH
    have h2 : (((y * t₀) * aH * (y * t₀)⁻¹ : ↥I) : G) = ((aH⁻¹ : ↥I) : G) :=
      congrArg Subtype.val h1
    simpa [t_G, t_H, Subgroup.coe_mul, Subgroup.coe_inv] using h2
  obtain ⟨r, hrprime, hrdvd, hr5, hr3⟩ := CFSG.GroupTheory.exists_prime_choice hn3
  have hAGcard : Nat.card ↥A_G = (2 ^ n - 1) * (2 ^ n - 1) := card_eq_of_isZModSq hAGsq
  have hr : r ∈ piSet A_G := by
    refine ⟨hrprime, ?_⟩
    rw [hAGcard]
    exact hrdvd.mul_right _
  have hr3' : 3 ∈ piSet A_G → r = 3 := by
    intro h3mem
    obtain ⟨-, h3dvd⟩ := h3mem
    rw [hAGcard] at h3dvd
    have h3' : 3 ∣ 2 ^ n - 1 :=
      Nat.prime_three.dvd_of_dvd_pow (n := 2) (by rw [pow_two]; exact h3dvd)
    exact hr3 h3'
  refine ⟨A_G, t_G, A_G ⊔ Subgroup.zpowers t_G, r, ?_, hr3'⟩
  exact ⟨h, h1910, Subgroup.map_subtype_le A_H, hAGsq, hPerm, htA, ht2, hinvG, rfl, hr, hr5⟩

theorem r19_glue_4At_of_K (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp19 D V₀ V p L) (h1910 : Setting1910 D V₀ V p L) (h42 : S17.R17_42At D V₀ V)
    (htorus : K_19_glue4_torus) : R19_glue_4At D V₀ V p L h h1910 := by
  obtain ⟨A, t, B, r, hctx, -⟩ := nineteen_glue_four D h h1910 h42 htorus
  exact ⟨A, t, B, r, hctx⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
