module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22uc
public import CFSG.Quasithin.H13.NQCoreP134Setup
public import CFSG.RankThree.PartTwo.Sec15.Item157Proof
public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.GrpA
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputs
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Layer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.Yardstones.Mf4cdcdf2e013.Definitions

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne (IsSL3Four)
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 TheoremCAt)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (StronglyEmbeddedFive)

variable {G : Type} [Group G] [Finite G]

theorem isSL3Four_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsSL3Four X) : IsSL3Four Y := by
  obtain ⟨⟨hqs, hL3⟩, hcenter⟩ := h
  refine ⟨⟨CFSG.Open.IsQuasisimple.of_mulEquiv e.symm hqs, ?_⟩, ?_⟩
  · let ec : (X ⧸ Subgroup.center X) ≃* (Y ⧸ Subgroup.center Y) :=
      QuotientGroup.congr (Subgroup.center X) (Subgroup.center Y) e
        (Subgroup.map_center_eq e)
    exact CFSG.Blueprint.LieModel.of_mulEquiv ec hL3
  · rw [← Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact hcenter

noncomputable def equiv_barImage_of_isPGroup {M Q : Subgroup G} (hQM : Q ≤ M)
    (hQp : IsPGroup 3 Q) : ↥Q ≃* ↥(barImage M Q) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hO2p : IsPGroup 2 (pCoreOf 2 M) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥M)).map M.subtype
  have hdisj : Disjoint Q (pCoreOf 2 M) :=
    IsPGroup.disjoint_of_ne 3 2 (by norm_num) Q (pCoreOf 2 M) hQp hO2p
  let q : ↥M →* Bar2 M := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  let g : ↥Q →* Bar2 M := q.comp (Subgroup.inclusion hQM)
  have hg_inj : Function.Injective g := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxO : ((x : Q) : G) ∈ pCoreOf 2 M := by
      have hxq : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨(x : Q), hQM x.2⟩ = 1 := by
        have hx' : q (Subgroup.inclusion hQM x) = 1 := by simpa [g] using hx
        have hsub : (Subgroup.inclusion hQM x : ↥M) = ⟨(x : Q), hQM x.2⟩ := rfl
        simpa [q, hsub] using hx'
      have hx' : (⟨(x : Q), hQM x.2⟩ : ↥M) ∈ CFSG.pCore 2 ↥M :=
        (QuotientGroup.eq_one_iff _).1 hxq
      exact Subgroup.mem_map.mpr ⟨⟨(x : Q), hQM x.2⟩, hx', rfl⟩
    have hxbot : ((x : Q) : G) ∈ (⊥ : Subgroup G) := by
      rw [← hdisj.eq_bot]
      exact ⟨x.2, hxO⟩
    exact Subtype.ext (Subgroup.mem_bot.mp hxbot)
  have hg_range : g.range = barImage M Q := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact uc22p21c_mem_barImage.2 ⟨⟨(x : Q), hQM x.2⟩, x.2, rfl⟩
    · intro hy
      obtain ⟨m, hm, rfl⟩ := uc22p21c_mem_barImage.1 hy
      refine ⟨⟨(m : G), hm⟩, ?_⟩
      rfl
  let f : ↥Q →* ↥(barImage M Q) :=
    { toFun := fun x => ⟨g x, by rw [← hg_range]; exact ⟨x, rfl⟩⟩
      map_one' := by ext; exact map_one g
      map_mul' := by intro a b; ext; exact map_mul g a b }
  have hf_inj : Function.Injective f := by
    intro a b hab
    exact hg_inj (congrArg Subtype.val hab)
  have hf_surj : Function.Surjective f := by
    intro y
    have hy : (y : Bar2 M) ∈ g.range := by rw [hg_range]; exact y.2
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩
  exact MulEquiv.ofBijective f ⟨hf_inj, hf_surj⟩

theorem isSylowOf_barImage_of_isSylowOf {M L R : Subgroup G} (hLM : L ≤ M)
    (hR : CFSG.ABGLocalTools.IsSylowOf 3 R L)
    (e : Bar2 L ≃* ↥(barImage M L)) :
    CFSG.ABGLocalTools.IsSylowOf 3 (barImage M R) (barImage M L) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hRin : CFSG.Quasithin.IsSylowIn 3 R L := by
    refine ⟨hR.le, hR.isPGroup, ?_⟩
    exact (CFSG.ABGLocalTools.isSylowOf_iff.mp hR).2.2
  have hcardRbar : Nat.card (barImage M R) = Nat.card R := by
    have h := CFSG.Quasithin.H13.NQCore.card_bar_of_sylow
      (H := M) (X := L) (P := R) (p := 3) hLM (by norm_num : (3 : ℕ) ≠ 2) hRin
    simpa [barImage, CFSG.Quasithin.modO2Image] using h
  have hfac : (Nat.card L).factorization 3 = (Nat.card (barImage M L)).factorization 3 := by
    have hO : ¬ 3 ∣ Nat.card (CFSG.pCore 2 ↥L) := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥L))
      rw [hk]
      intro h3
      have h32 : (3 : ℕ) = 2 :=
        (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
          (Nat.prime_three.dvd_of_dvd_pow h3)
      norm_num at h32
    have h1 := CFSG.RankThree.PartTwo.Sec15.Proof157.factorization_three_card_quotient
      (Q := ↥L) (CFSG.pCore 2 ↥L) hO
    rwa [Nat.card_congr e.toEquiv] at h1
  refine CFSG.ABGLocalTools.isSylowOf_of_card (uc22p22u_barImage_mono hR.le) ?_
  rw [hcardRbar, hR.card_eq, hfac]

theorem exists_elemAbelian_nine_of_isExtraspecial_of_pow_three {A : Subgroup G}
    (hA : CFSG.IsExtraspecial 3 A) (hexp : ∀ x : A, x ^ 3 = 1) {x : G} (hx : x ∈ A) :
    ∃ E : Subgroup G, x ∈ E ∧ E ≤ A ∧ CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Z : Subgroup G := (Subgroup.center A).map A.subtype
  have hZcard : Nat.card Z = 3 := by
    rw [Subgroup.card_map_of_injective A.subtype_injective, hA.center_order_p]
  have hZel : CFSG.Open.IsElemAbelian 3 Z := by
    have hc : CFSG.Open.IsElemAbelian 3 (Subgroup.center A) := by
      refine ⟨inferInstance, ?_⟩
      intro z _
      change ((z : A) ^ 3) = 1
      exact hexp (z : A)
    exact hc.map A.subtype
  have hcenter_ne_top : Subgroup.center A ≠ ⊤ := by
    intro htop
    haveI : Subsingleton (A ⧸ Subgroup.center A) :=
      (QuotientGroup.subsingleton_iff).mpr htop
    exact not_subsingleton_iff_nontrivial.mpr hA.quotient_nontrivial inferInstance
  obtain ⟨y, hy⟩ : ∃ y : A, y ∉ Subgroup.center A := by
    by_contra h
    push Not at h
    exact hcenter_ne_top (le_antisymm le_top fun z _ => h z)
  let w : A := if x ∈ Z then y else ⟨x, hx⟩
  have hw_notin : w ∉ Subgroup.center A := by
    by_cases hxZ : x ∈ Z
    · have hw : w = y := by
        dsimp [w]
        rw [if_pos hxZ]
      rw [hw]; exact hy
    · have hw : w = ⟨x, hx⟩ := by
        dsimp [w]
        rw [if_neg hxZ]
      rw [hw]
      intro hmem
      exact hxZ (Subgroup.mem_map.mpr ⟨⟨x, hx⟩, hmem, rfl⟩)
  have hw1 : w ≠ 1 := by
    intro h1
    apply hw_notin
    rw [h1]
    exact Subgroup.one_mem _
  have hw3 : (w : G) ^ 3 = 1 := congrArg Subtype.val (hexp w)
  have hword : orderOf (w : G) = 3 :=
    orderOf_eq_prime hw3 (fun h => hw1 (Subtype.ext h))
  have hzp : CFSG.IsElementaryAbelian 3 (Subgroup.zpowers (w : G)) :=
    CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one hw3
  have hcent : Subgroup.zpowers (w : G) ≤ Subgroup.centralizer (Z : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hz
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hc w).symm
  have hcommZ : ∀ z ∈ Z, ∀ v ∈ Subgroup.zpowers (w : G), z * v = v * z := by
    intro z hz v hv
    exact Subgroup.mem_centralizer_iff.mp (hcent hv) z hz
  refine ⟨Z ⊔ Subgroup.zpowers (w : G), ?_, ?_, ?_, ?_⟩
  · by_cases hxZ : x ∈ Z
    · exact Subgroup.mem_sup_left hxZ
    · have hxw : x = (w : G) := by
        dsimp [w]
        rw [if_neg hxZ]
      rw [hxw]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  · exact sup_le (Subgroup.map_subtype_le _) (Subgroup.zpowers_le.mpr w.2)
  · have hZclass : CFSG.IsElementaryAbelian 3 ↥Z :=
      CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mp hZel
    have hclass : CFSG.IsElementaryAbelian 3 ↥(Z ⊔ Subgroup.zpowers (w : G)) := by
      haveI : CFSG.IsElementaryAbelian 3 ↥Z := hZclass
      haveI : CFSG.IsElementaryAbelian 3 ↥(Subgroup.zpowers (w : G)) := hzp
      exact CFSG.IsElementaryAbelian.sup_of_le_centralizer (E := Z)
        (C := Subgroup.zpowers (w : G)) hcent
    exact CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mpr hclass
  · have hinf : Z ⊓ Subgroup.zpowers (w : G) = ⊥ := by
      have hdvd : Nat.card ↥(Z ⊓ Subgroup.zpowers (w : G)) ∣ 3 := by
        have h := Subgroup.card_dvd_of_le (H := Z ⊓ Subgroup.zpowers (w : G))
          (K := Subgroup.zpowers (w : G)) inf_le_right
        rwa [Nat.card_zpowers, hword] at h
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
      · exact Subgroup.eq_bot_of_card_eq _ h1
      · exfalso
        have hle : Z ⊓ Subgroup.zpowers (w : G) = Subgroup.zpowers (w : G) :=
          Subgroup.eq_of_le_of_card_ge inf_le_right
            (by rw [h3, Nat.card_zpowers, hword])
        have hwmem : (w : G) ∈ Z ⊓ Subgroup.zpowers (w : G) := by
          rw [hle]
          exact Subgroup.mem_zpowers _
        obtain ⟨c, hc, hcw⟩ := Subgroup.mem_map.mp hwmem.1
        exact hw_notin (Subtype.ext hcw ▸ hc)
    have h := CFSG.GH74.GLS.Stage1.Thm3.Sec7.A.card_sup_mul_card_inf_of_commute hcommZ
    rw [hinf, Subgroup.card_bot, hZcard, Nat.card_zpowers, hword] at h
    change Nat.card ↥(Z ⊔ Subgroup.zpowers (w : G)) = 9
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
