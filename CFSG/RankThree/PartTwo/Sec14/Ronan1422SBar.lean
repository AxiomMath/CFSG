module

public import CFSG.RankThree.PartTwo.Sec14.Ronan1422SItem431
public import CFSG.RankThree.PartTwo.Sec14.Ronan148JNA6
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofHyp
public import CFSG.RankThree.PartTwo.Sec13.Ronan41F135ListDefs
import CFSG.RankThree.PartTwo.Sec4.T444.Coprime
public import CFSG.RankThree.PartTwo.Sec14.Ronan1422SChoose
public import CFSG.RankThree.PartTwo.Sec14.Ronan1422SK

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan1422S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projSp)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isE27_subgroupOf1422 {Γ : Type*} [Group Γ] {A C : Subgroup Γ} (hAC : A ≤ C)
    (hA : IsE27 A) : IsE27 (A.subgroupOf C) := by
  refine ⟨⟨⟨⟨fun x y => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩, ?_⟩
  · have h := congrArg Subtype.val
      (hA.1.1.is_comm.comm ⟨((x : ↥C) : Γ), x.2⟩ ⟨((y : ↥C) : Γ), y.2⟩)
    simpa using h
  · simpa using hA.1.2 _ hx
  · rw [← hA.2]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAC).toEquiv

noncomputable def quotientCenterEquiv1422 {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) :
    X ⧸ Subgroup.center X ≃* Y ⧸ Subgroup.center Y :=
  QuotientGroup.congr (Subgroup.center X) (Subgroup.center Y) e (by
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_center_iff]
    constructor
    · rintro ⟨x, hx, rfl⟩ g
      have h2 := congrArg e (hx (e.symm g))
      simpa using h2
    · intro hy
      refine ⟨e.symm y, fun g => ?_, by simp⟩
      have h2 := congrArg e.symm (hy (e g))
      simpa using h2)

theorem nonempty_mulEquiv_congr1422 {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {T : Type}
    {_ : Group T} : Nonempty (X ≃* T) ↔ Nonempty (Y ≃* T) :=
  ⟨fun ⟨φ⟩ => ⟨e.symm.trans φ⟩, fun ⟨φ⟩ => ⟨e.trans φ⟩⟩

theorem list42_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : Sec4.Census.List42 X) : Sec4.Census.List42 Y := by
  unfold Sec4.Census.List42 Sec4.IsChevTwoRankTwo Sec4.IsoGTwo at h ⊢
  simp only [nonempty_mulEquiv_congr1422 e] at h
  exact h

structure Cfg (A : Subgroup G) (c : G) (L R S J : Subgroup G) : Prop where
  pt : Pt A c L
  R_mem : R ∈ scriptQPiStar A (lB A) L (piOf 2)
  S_mem : S ∈ fam A c R (L ⊓ Subgroup.normalizer (R : Set G))
  J_mem : J ∈ thetaComponentsIn (Subgroup.normalizer (S : Set G))
  K_le : L ⊓ Subgroup.normalizer (R : Set G) ≤ J
  A_le : A ≤ Subgroup.normalizer (J : Set G)

namespace Cfg

variable {A L R S J : Subgroup G} {c : G}

theorem A_le_M (h : Cfg A c L R S J) : A ≤ Subgroup.normalizer (S : Set G) :=
  (fam_facts h.S_mem).2.1

theorem K_le_M (h : Cfg A c L R S J) :
    L ⊓ Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (S : Set G) :=
  (fam_facts h.S_mem).2.2.2

theorem J_le_M (h : Cfg A c L R S J) : J ≤ Subgroup.normalizer (S : Set G) :=
  le_of_mem_thetaComponentsIn h.J_mem

theorem isPGroup_S (h : Cfg A c L R S J) : IsPGroup 2 S := (fam_facts h.S_mem).1

theorem R_le_S (h : Cfg A c L R S J) : R ≤ S := (fam_facts h.S_mem).2.2.1

theorem sup_A_eq (h : Cfg A c L R S J) :
    Subgroup.normalizer (S : Set G) ⊔ A = Subgroup.normalizer (S : Set G) :=
  sup_of_le_left h.A_le_M

theorem A_le_NM (h : Cfg A c L R S J) :
    A ≤ Subgroup.normalizer ((Subgroup.normalizer (S : Set G) : Subgroup G) : Set G) :=
  h.A_le_M.trans Subgroup.le_normalizer

theorem ker_normal (h : Cfg A c L R S J) :
    (ker148 A (Subgroup.normalizer (S : Set G))).Normal :=
  ker148_normal h.A_le_NM

theorem S_le_pPrimeCoreOf (h : Cfg A c L R S J) :
    S ≤ pPrimeCoreOf 3 (Subgroup.normalizer (S : Set G)) := by
  set M := Subgroup.normalizer (S : Set G) with hM
  have hSM : S ≤ M := Subgroup.le_normalizer
  have hn : (S.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSM).mpr le_rfl
  have hcop : Nat.Coprime 3 (Nat.card (S.subgroupOf M)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSM).toEquiv]
    obtain ⟨k, hk⟩ := h.isPGroup_S.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right _ (by norm_num)
  have hle : S.subgroupOf M ≤ CFSG.pPrimeCore 3 ↥M := le_sSup ⟨hn, hcop⟩
  intro s hs
  exact ⟨⟨s, hSM hs⟩, hle (Subgroup.mem_subgroupOf.mpr hs), rfl⟩

end Cfg

section KP4

namespace Cfg

variable {A L R S J : Subgroup G} {c : G}

theorem R_ne_bot (h : Cfg A c L R S J) : R ≠ ⊥ := by
  intro hR
  have h16 := (h.pt.R_kp4 h.R_mem).2.1
  rw [hR, Subgroup.card_bot] at h16
  norm_num at h16

theorem S_ne_bot (h : Cfg A c L R S J) : S ≠ ⊥ :=
  fun hS => h.R_ne_bot (le_bot_iff.mp (hS ▸ h.R_le_S))

theorem isTwoLocal_M (h : Cfg A c L R S J) :
    CFSG.Open.IsTwoLocal (Subgroup.normalizer (S : Set G)) :=
  ⟨S, h.S_ne_bot, h.isPGroup_S, rfl⟩

theorem M_ne_top (h : Cfg A c L R S J) : Subgroup.normalizer (S : Set G) ≠ ⊤ := by
  intro htop
  have hSn : S.Normal := Subgroup.normalizer_eq_top_iff.mp htop
  have hsimple : IsSimpleGroup G := h.pt.std.isSimpleGroup
  rcases hSn.eq_bot_or_eq_top with h1 | h1
  · exact h.S_ne_bot h1
  · obtain ⟨a, b, hab⟩ := h.pt.std.nonabelian
    have hG2 : IsPGroup 2 G := by
      have h2 := h.isPGroup_S
      rw [h1] at h2
      exact h2.of_equiv Subgroup.topEquiv
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : Nontrivial G := hsimple.toNontrivial
    have hZ := hG2.center_nontrivial
    have hZtop : Subgroup.center G = ⊤ := by
      rcases (Subgroup.center G).normal_of_characteristic.eq_bot_or_eq_top with h0 | h0
      · exfalso
        obtain ⟨⟨z, hz⟩, ⟨w, hw⟩, hzw⟩ := hZ
        have hz1 : z = 1 := by rw [h0] at hz; exact hz
        have hw1 : w = 1 := by rw [h0] at hw; exact hw
        exact hzw (Subtype.ext (hz1.trans hw1.symm))
      · exact h0
    have ha : a ∈ Subgroup.center G := hZtop ▸ Subgroup.mem_top a
    exact hab ((Subgroup.mem_center_iff.mp ha b).symm)

theorem inf_pPrimeCoreOf_eq (h : Cfg A c L R S J) :
    (L ⊓ Subgroup.normalizer (R : Set G)) ⊓ pPrimeCoreOf 3 (Subgroup.normalizer (S : Set G)) =
      R := by
  set K := L ⊓ Subgroup.normalizer (R : Set G) with hK
  set O := pPrimeCoreOf 3 (Subgroup.normalizer (S : Set G)) with hO
  obtain ⟨hRL, -, -, -⟩ := h.pt.R_facts h.R_mem
  obtain ⟨-, f, hf, hker⟩ := h.pt.K_kp4 h.R_mem
  apply le_antisymm
  · intro x hx
    set N : Subgroup ↥K := O.subgroupOf K with hN
    have hNn : N.Normal := by
      refine ⟨fun n hn k => ?_⟩
      rw [hN, Subgroup.mem_subgroupOf] at hn ⊢
      have hkM : (k : G) ∈ Subgroup.normalizer (S : Set G) := h.K_le_M k.2
      have := (Subgroup.mem_normalizer_iff.mp
        (le_normalizer_pPrimeCoreOf 3 _ hkM) n).mp hn
      simpa using this
    have hsimple : IsSimpleGroup (alternatingGroup (Fin 6)) :=
      alternatingGroup.isSimpleGroup (by simp)
    have hN3 : Nat.Coprime 3 (Nat.card N) := by
      have h1 : Nat.card N ∣ Nat.card O := by
        rw [← Subgroup.card_map_of_injective K.subtype_injective, Subgroup.subgroupOf_map_subtype]
        exact Subgroup.card_dvd_of_le inf_le_left
      exact Nat.Coprime.coprime_dvd_right h1 (coprime_card_pPrimeCoreOf 3 _)
    rcases (hNn.map f hf).eq_bot_or_eq_top with h0 | h0
    · have hxN : (⟨x, hx.1⟩ : ↥K) ∈ N := Subgroup.mem_subgroupOf.mpr hx.2
      have : (⟨x, hx.1⟩ : ↥K) ∈ f.ker := by
        rw [MonoidHom.mem_ker]
        have := Subgroup.mem_map_of_mem f hxN
        rwa [h0, Subgroup.mem_bot] at this
      rw [hker, Subgroup.mem_subgroupOf] at this
      exact this
    · exfalso
      have h360 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
        rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
        norm_num [Nat.factorial]
      have hdvd : Nat.card (N.map f) ∣ Nat.card N := Subgroup.card_map_dvd N f
      rw [h0, Subgroup.card_top, h360] at hdvd
      have h3 : 3 ∣ Nat.card N := (by norm_num : 3 ∣ 360).trans hdvd
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hN3 h3
  · exact le_inf (R_le_K hRL) (h.R_le_S.trans h.S_le_pPrimeCoreOf)

theorem three_dvd_card_J (h : Cfg A c L R S J) : 3 ∣ Nat.card J := by
  obtain ⟨hK, -⟩ := h.pt.K_kp4 h.R_mem
  have h3 : 3 ∣ Nat.card (L ⊓ Subgroup.normalizer (R : Set G) : Subgroup G) := by
    rw [hK]; norm_num
  exact h3.trans (Subgroup.card_dvd_of_le h.K_le)

variable [(ker148 A (Subgroup.normalizer (S : Set G))).Normal]

theorem nonempty_K_equiv (h : Cfg A c L R S J) :
    Nonempty (↥(img148 A (Subgroup.normalizer (S : Set G))
      (L ⊓ Subgroup.normalizer (R : Set G))) ≃* alternatingGroup (Fin 6)) := by
  set M := Subgroup.normalizer (S : Set G) with hM
  set K := L ⊓ Subgroup.normalizer (R : Set G) with hK
  obtain ⟨-, f, hf, hker⟩ := h.pt.K_kp4 h.R_mem
  have hKMA : K ≤ M ⊔ A := h.K_le_M.trans le_sup_left
  let ψ : ↥K →* ↥(img148 A M K) :=
    ((QuotientGroup.mk' (ker148 A M)).comp (Subgroup.inclusion hKMA)).codRestrict
      (img148 A M K) (fun k => mem_img148_iff.mpr ⟨k, hKMA k.2, k.2, rfl⟩)
  have hψ : Function.Surjective ψ := by
    rintro ⟨x, hx⟩
    obtain ⟨g, hg, hgK, rfl⟩ := mem_img148_iff.mp hx
    exact ⟨⟨g, hgK⟩, rfl⟩
  have hψker : ψ.ker = f.ker := by
    rw [hker]
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hk
      have h1 : QuotientGroup.mk' (ker148 A M) ⟨(k : G), hKMA k.2⟩ = 1 :=
        congrArg Subtype.val hk
      rw [mk'_ker148_eq_one_iff] at h1
      have h2 : (k : G) ∈ K ⊓ pPrimeCoreOf 3 M := ⟨k.2, h1⟩
      rwa [h.inf_pPrimeCoreOf_eq] at h2
    · intro hk
      apply Subtype.ext
      change QuotientGroup.mk' (ker148 A M) ⟨(k : G), hKMA k.2⟩ = 1
      rw [mk'_ker148_eq_one_iff]
      exact h.S_le_pPrimeCoreOf (h.R_le_S hk)
  exact ⟨((QuotientGroup.quotientKerEquivOfSurjective ψ hψ).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hψker)).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)⟩

theorem pRank_le (h : Cfg A c L R S J)
    (X : Subgroup (↥(Subgroup.normalizer (S : Set G) ⊔ A) ⧸
      ker148 A (Subgroup.normalizer (S : Set G)))) :
    CFSG.Open.pRank 3 X ≤ 3 := by
  set M := Subgroup.normalizer (S : Set G) with hM
  have h1 : CFSG.Open.pRank 3 X ≤ CFSG.Open.pRank 3
      ((⊤ : Subgroup ↥(M ⊔ A)).map (QuotientGroup.mk' (ker148 A M))) := by
    rw [← MonoidHom.range_eq_map, QuotientGroup.range_mk']
    exact CFSG.RankThreeEvenClassification.Helpers.pRank_mono 3 Nat.prime_three le_top
  have h2 := Sec4.pRank_map_le_of_not_dvd Nat.prime_three (QuotientGroup.mk' (ker148 A M))
    (by rw [QuotientGroup.ker_mk']; exact Main148.not_three_dvd_card_ker148)
    (⊤ : Subgroup ↥(M ⊔ A))
  have h3 := CFSG.RankThreeEvenClassification.Helpers.pRank_le_map_of_injective 3
    Nat.prime_three (M ⊔ A).subtype (M ⊔ A).subtype_injective ⊤
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h3
  have h3' : CFSG.Open.pRank 3 (M ⊔ A) ≤ CFSG.Open.pRank 3 M :=
    CFSG.RankThreeEvenClassification.Helpers.pRank_mono 3 Nat.prime_three h.sup_A_eq.le
  have h4 := CFSG.RankThree.Classical.pRank_le_localRank (by norm_num : 1 < 3) h.isTwoLocal_M
  rw [h.pt.std.toTheoremFourHyp.localRank_three] at h4
  exact h1.trans (h2.trans (h3.trans (h3'.trans h4)))

theorem c_ne_one (h : Cfg A c L R S J) : c ≠ 1 := fun hc => h.pt.not_mem (hc ▸ L.one_mem)

theorem K_le_centralizer (h : Cfg A c L R S J) :
    img148 A (Subgroup.normalizer (S : Set G)) (L ⊓ Subgroup.normalizer (R : Set G)) ≤
        img148 A (Subgroup.normalizer (S : Set G)) J ⊓
          Subgroup.centralizer {alpha148 A (Subgroup.normalizer (S : Set G)) c h.pt.mem_A} ∧
      ((img148 A (Subgroup.normalizer (S : Set G))
        (L ⊓ Subgroup.normalizer (R : Set G))).subgroupOf
        (img148 A (Subgroup.normalizer (S : Set G)) J ⊓ Subgroup.centralizer
          {alpha148 A (Subgroup.normalizer (S : Set G)) c h.pt.mem_A})).IsSubnormal := by
  set M := Subgroup.normalizer (S : Set G) with hM
  set K := L ⊓ Subgroup.normalizer (R : Set G) with hK
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := h.pt.std.isE27.1.2
  have hJMA : J ≤ M ⊔ A := h.J_le_M.trans le_sup_left
  have hKc : K ≤ Subgroup.centralizer ({c} : Set G) := inf_le_left.trans h.pt.le_centralizer
  have hCJ := Main148.img148_inf_centralizer_alpha148 h.A_le_NM hJMA h.A_le h.pt.mem_A
    (hA3 c h.pt.mem_A)
  rw [hCJ]
  refine ⟨img148_mono (le_inf h.K_le hKc), Main148.isSubnormal_img148 (le_inf h.K_le hKc)
    (inf_le_left.trans hJMA) (Subgroup.Normal.isSubnormal ⟨fun k hk g => ?_⟩)⟩
  rw [Subgroup.mem_subgroupOf] at hk ⊢
  have hgN : ((g : G)) ∈ M ⊓ Subgroup.centralizer ({c} : Set G) :=
    ⟨h.J_le_M g.2.1, g.2.2⟩
  have := (Subgroup.mem_normalizer_iff.mp
    (h.pt.centralizer_inf_le_normalizer_K h.R_mem h.S_mem hgN) _).mp hk
  simpa [hK] using this

theorem type431 (h431 : Sec4.Ronan431.Item4_31List42) (hCL : F135Last.ComponentList42)
    (h : Cfg A c L R S J) :
    Nonempty (↥(img148 A (Subgroup.normalizer (S : Set G)) J) ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (↥(img148 A (Subgroup.normalizer (S : Set G)) J) ≃*
        Blueprint.NativeSporadic.J3) ∨
      Nonempty (↥(img148 A (Subgroup.normalizer (S : Set G)) J) ≃*
        projSp 3 (GaloisField 2 1)) ∨
      Nonempty (↥(img148 A (Subgroup.normalizer (S : Set G)) J) ≃* alternatingGroup (Fin 9)) ∨
      Nonempty (↥(img148 A (Subgroup.normalizer (S : Set G)) J) ≃*
        projSp 2 (GaloisField 2 3)) := by
  set M := Subgroup.normalizer (S : Set G) with hM
  set K := L ⊓ Subgroup.normalizer (R : Set G) with hK
  have hA : IsE27 A := h.pt.std.isE27
  have hJMA : J ≤ M ⊔ A := h.J_le_M.trans le_sup_left
  obtain ⟨hJq, hJθ⟩ := Main148.img148_isQuasisimple (A := A) (Y := M) h.J_mem h.three_dvd_card_J
  set C := img148 A M (J ⊔ A) with hCdef
  have hCeq : C = img148 A M J ⊔ img148 A M A := img148_sup hJMA le_sup_right
  have hAαJα : img148 A M A ≤
      Subgroup.normalizer (img148 A M J : Set (↥(M ⊔ A) ⧸ ker148 A M)) :=
    img148_le_normalizer h.A_le
  have hAα3 : ∀ a ∈ img148 A M A, a ^ 3 = 1 := (img148_isE27 hA).1.2
  have hCθ : aschbacherSolvableCore 3 ↥C = ⊥ := by
    rw [hCeq]
    exact Main148.aschbacherSolvableCore_sup_eq_bot hAαJα hAα3 hJθ
  have hAC : img148 A M A ≤ C := img148_mono le_sup_right
  have hLC : img148 A M J ≤ C := img148_mono le_sup_left
  have hLn : C ≤ Subgroup.normalizer (img148 A M J : Set (↥(M ⊔ A) ⧸ ker148 A M)) := by
    rw [hCeq]
    exact sup_le Subgroup.le_normalizer hAαJα
  have hCr : CFSG.Open.pRank 3 (⊤ : Subgroup ↥C) = 3 := by
    apply le_antisymm
    · have h1 := CFSG.RankThreeEvenClassification.Helpers.pRank_le_map_of_injective 3
        Nat.prime_three C.subtype C.subtype_injective ⊤
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h1
      exact h1.trans (h.pRank_le C)
    · have hE := isE27_subgroupOf1422 hAC (img148_isE27 hA)
      refine le_csSup (CFSG.RankThreeEvenClassification.Helpers.pRank_bddAbove 3
        Nat.prime_three ⊤) ⟨(img148 A M A).subgroupOf C, le_top, hE.1, ?_⟩
      rw [hE.2]
      norm_num
  obtain ⟨hKL, hKsub⟩ := h.K_le_centralizer
  obtain ⟨φ⟩ := h.nonempty_K_equiv
  have hsimple6 : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hKs : IsSimpleGroup ↥(img148 A M K) := MulEquiv.isSimpleGroup φ
  have hKnc : ∃ a b : ↥(img148 A M K), a * b ≠ b * a := by
    have : Nontrivial (alternatingGroup (Fin 6)) := hsimple6.toNontrivial
    obtain ⟨a, b, hab⟩ := Main148.exists_ne_comm_of_isPerfect isPerfect_alternatingGroup_six
    exact ⟨φ.symm a, φ.symm b, fun h1 => hab (by simpa using congrArg φ h1)⟩
  have hMtop : M ⊔ A ≠ ⊤ := by rw [h.sup_A_eq]; exact h.M_ne_top
  have hM4 : SectionFourHyp ↥(M ⊔ A) := h.pt.std.toTheoremFourHyp.sectionFourHyp hMtop
  have hJc : IsComponent (img148 A M J) :=
    Ronan148J.isComponent_img148_of_three_dvd h.A_le_NM h.J_mem h.three_dvd_card_J
  have hJL := hCL (M ⊔ A) hM4 (ker148 A M) (img148 A M J) hJc
  have hL42 := list42_of_mulEquiv
    (quotientCenterEquiv1422 (Subgroup.subgroupOfEquivOfLe hLC).symm) hJL
  exact item4_31_of_le h431 C hCr hCθ hAC hLC (img148_isE27 hA) (alpha148_mem_img148 h.pt.mem_A)
    (Main148.alpha148_ne_one h.pt.mem_A h.c_ne_one (hA.1.2 c h.pt.mem_A)) hJq hLn hL42 hKL hKs
    hKnc hKsub
    ⟨φ⟩

end Cfg

end KP4

end CFSG.RankThree.PartTwo.Sec14.Ronan1422S
