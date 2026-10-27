module

public import CFSG.RankThree.PartTwo.Sec4.Item423StepsProof424
public import CFSG.RankThree.PartTwo.Sec11.Item119Used

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.RankThree.PartOne.EmbeddingFixedResidual

section Core

variable {G : Type} [Group G] [Finite G]


theorem item119_of_kType_M (h424 : Sec4.Item4_24M) (h45 : Sec4.Item4_5) {A : Subgroup G} {c : G}
    {L : Subgroup G} {a : G} {R Y : Subgroup G} (h : Sec11Std G A c L a R Y) {d : G}
    (hdL : A ⊓ L = Subgroup.zpowers d) (hA : A = Subgroup.closure {c, a, d})
    (hCA : Late.sectionCentralizer A Y ((aschbacherSolvableCore 3 Y).map Y.subtype) =
      (Subgroup.zpowers a : Set G))
    (hWd : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G))
    (hKT : IsType424 (sec11K L a ⧸ aschbacherSolvableCore 3 (sec11K L a))) :
    (KFacts.InducesStdKind Y c .field ∧ Nonempty (Sec4.autIn Y A ≃* Equiv.Perm (Fin 3))) ∨
      (((∃ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.G2 q).Valid),
            Nonempty (sec11YA a Y A ≃* Multiplicative (ZMod 3) ×
              (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group)) ∨
          ∃ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid),
            Nonempty (sec11YA a Y A ≃* Multiplicative (ZMod 3) ×
              (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group)) ∧
        Nonempty (Sec4.autIn Y A ≃* DihedralGroup 6)) ∨
      ((Sec8.IsZ3LThreePi (sec11YA a Y A) ∨ Sec8.IsZ3PGLThreePi (sec11YA a Y A)) ∧
        Nonempty (Sec4.autIn Y A ≃* Equiv.Perm (Fin 3))) ∨
      ((Nonempty (sec11YA a Y A ≃* Multiplicative (ZMod 3) ×
            CFSG.Blueprint.NativeSporadic.M24) ∨
          Nonempty (sec11YA a Y A ≃* Multiplicative (ZMod 3) ×
            CFSG.Blueprint.NativeSporadic.He)) ∧
        Nonempty (sec11K L a ⧸ aschbacherSolvableCore 3 (sec11K L a) ≃*
          projSL 3 (GaloisField 2 1)) ∧
        Nonempty (Sec4.autIn Y A ≃* DihedralGroup 6)) := by
  have hG := h.toTheoremFourHyp
  have := hG.isSimpleGroup
  have hAe := h.mem_partTwoF.1
  have hexp : ∀ y ∈ A, y ^ 3 = 1 := hAe.2
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have hcA := h.mem_A
  have haA := h.a_mem
  have ha1 := h.a_ne_one
  have hdAL : d ∈ A ⊓ L := by
    rw [hdL]
    exact Subgroup.mem_zpowers d
  obtain ⟨hca, hacd, -⟩ := h.not_mem_facts hdL hA
  obtain ⟨-, -, -, -, hdK⟩ := basic_facts_of_conj h45 h hdL hA haA hacd
  set C := Subgroup.centralizer ({a} : Set G) with hC
  have hAC : A ≤ C := fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr (hcomm y hy a haA)
  have hcC : c ∈ C := hAC hcA
  have haC : a ∈ C := hAC haA
  obtain ⟨hYC, hY'⟩ := mem_thetaComponentsIn_iff.mp h.mem_thetaComponentsAt_Y
  have hC4 : SectionFourHyp C :=
    hG.sectionFourHyp (centralizer_ne_top_of_simple hG.nonabelian ha1)
  set A' := A.subgroupOf C with hA'def
  have hA'max : Maximal (fun B : Subgroup C => CFSG.Assembly.IsElemAbelian 3 B) A' :=
    maximal_subgroupOf_of_le h.mem_partTwoF.2.1 hAe hAC
  have h27 : Nat.card A' = 27 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAC).toEquiv, h.card_eq]
  have hEF : partTwoE C = partTwoF C :=
    partTwoE_eq_partTwoF_subgroup (h.partTwoE_eq h.card_eq) C
  set L' := Y.subgroupOf C with hL'def
  set a' : C := ⟨a, haC⟩ with ha'def
  have ha'3 : orderOf a' = 3 := by
    rw [ha'def, Subgroup.orderOf_mk]
    exact orderOf_eq_prime (hexp a haA) ha1
  have ha'Z : a' ∈ Subgroup.center C := mk_mem_center_centralizer a
  have hLmap : L'.map C.subtype = Y := by
    rw [hL'def, Subgroup.subgroupOf_map_subtype, inf_of_le_left hYC]
  have hθ : ∀ w : C, w ∈ (aschbacherSolvableCore 3 L').map L'.subtype ↔
      (w : G) ∈ inSubgroup (aschbacherSolvableCore 3) Y := by
    intro w
    have e1 := inSubgroup_theta_map_subtype_sub L'
    rw [hLmap] at e1
    rw [e1]
    constructor
    · intro hw
      exact ⟨w, hw, rfl⟩
    · rintro ⟨w', hw', hww'⟩
      have : w' = w := Subtype.ext hww'
      rw [← this]
      exact hw'
  have hsec : Late.sectionCentralizer A' L' ((aschbacherSolvableCore 3 L').map L'.subtype) =
      (Subgroup.zpowers a' : Set C) := by
    ext z
    have hz : z ∈ Late.sectionCentralizer A' L' ((aschbacherSolvableCore 3 L').map L'.subtype) ↔
        (z : G) ∈ Late.sectionCentralizer A Y ((aschbacherSolvableCore 3 Y).map Y.subtype) := by
      constructor
      · rintro ⟨hzA, hzL⟩
        refine ⟨Subgroup.mem_subgroupOf.mp hzA, fun y hy => ?_⟩
        have := (hθ _).mp (hzL ⟨y, hYC hy⟩ (Subgroup.mem_subgroupOf.mpr hy))
        simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
        exact this
      · rintro ⟨hzA, hzY⟩
        refine ⟨Subgroup.mem_subgroupOf.mpr hzA, fun y hy => (hθ _).mpr ?_⟩
        have := hzY (y : G) (Subgroup.mem_subgroupOf.mp hy)
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        exact this
    rw [hz, hCA, SetLike.mem_coe, SetLike.mem_coe]
    constructor
    · intro h1
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext (by simpa [ha'def] using hk)⟩
    · intro h1
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp h1
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simp [ha'def]⟩
  set c' : C := ⟨c, hcC⟩ with hc'def
  have hc'A : c' ∈ A' := Subgroup.mem_subgroupOf.mpr hcA
  have hc'a : c' ∉ Subgroup.zpowers a' := by
    intro hc'
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hc'
    apply hca
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    simpa [ha'def, hc'def] using congrArg Subtype.val hk
  set K := sec11K L a with hKdef
  have hKC : K ≤ C := (Subgroup.map_subtype_le _).trans inf_le_right
  have hK' := mem_thetaComponentsIn_sec11K h45 h hdL hA hcC
  have hKT' : IsType424 (K.subgroupOf C ⧸ aschbacherSolvableCore 3 (K.subgroupOf C)) := by
    set e := Subgroup.subgroupOfEquivOfLe hKC
    exact isType424_of_mulEquiv (QuotientGroup.congr _ _ e
      (CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv Nat.prime_three e)) hKT
  have hdC : Subgroup.zpowers d ≤ C := Subgroup.zpowers_le.mpr (hAC hdAL.1)
  have hAK : A' ⊓ K.subgroupOf C = (Subgroup.zpowers d).subgroupOf C := by
    ext x
    rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
      Subgroup.mem_subgroupOf, ← hdL]
    constructor
    · rintro ⟨hxA, hxK⟩
      exact ⟨hxA, sec11K_le L a hxK⟩
    · rintro ⟨hxA, hxL⟩
      have hxd : (x : G) ∈ Subgroup.zpowers d := by
        rw [← hdL]
        exact ⟨hxA, hxL⟩
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxd
      rw [← hk]
      exact ⟨A.zpow_mem hdAL.1 k, K.zpow_mem hdK k⟩
  have hNK : Subgroup.normalizer (A' : Set C) ≤
      Subgroup.normalizer ((A' ⊓ K.subgroupOf C : Subgroup C) : Set C) := by
    intro w hw
    have hw' : (w : G) ∈ Subgroup.normalizer (A : Set G) := by
      have := (Sec13.coe_mem_normalizer_map_iff C (L' := A')).mpr hw
      rwa [hA'def, Subgroup.subgroupOf_map_subtype, inf_of_le_left hAC] at this
    rw [hAK]
    refine (Sec13.coe_mem_normalizer_map_iff C).mp ?_
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hdC]
    exact hWd hw'
  have h4 := h424 C hC4 A' hA'max h27 hEF L' hY' a' ha'3 ha'Z hsec c' hc'A hc'a
    (K.subgroupOf C) hK' hKT' hNK
  have himg : Sec4.thetaImage (L' ⊔ A') = sec11YA a Y A := by
    rw [hL'def, hA'def, ← Subgroup.subgroupOf_sup hYC hAC]
    rfl
  obtain ⟨eAut⟩ := Sec13.nonempty_autIn_subgroupOf_equiv C hYC hAC
  rw [himg] at h4
  rcases h4 with ⟨h1, ⟨e1⟩⟩ | ⟨h2, ⟨e2⟩⟩ | ⟨h3, ⟨e3⟩⟩ | ⟨h4, ⟨eK⟩, ⟨e4⟩⟩
  · left
    have hk := Sec13.inducesStdKind_sub C L' h1
    rw [hLmap] at hk
    exact ⟨hk, ⟨eAut.symm.trans e1⟩⟩
  · exact Or.inr (Or.inl ⟨h2, ⟨eAut.symm.trans e2⟩⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h3, ⟨eAut.symm.trans e3⟩⟩))
  · set e := Subgroup.subgroupOfEquivOfLe hKC
    have eQ : K.subgroupOf C ⧸ aschbacherSolvableCore 3 (K.subgroupOf C) ≃*
        K ⧸ aschbacherSolvableCore 3 K := QuotientGroup.congr _ _ e
      (CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv Nat.prime_three e)
    exact Or.inr (Or.inr (Or.inr ⟨h4, ⟨eQ.symm.trans eK⟩, ⟨eAut.symm.trans e4⟩⟩))

theorem item119_of_M (h424 : Sec4.Item4_24M) (h45 : Sec4.Item4_5) (h112 : Item112)
    (h114 : Item114) (h117 : Item117) (h118 : Item118) (hKT : KType119) : Item119 := by
  intro G _ _ A c L a R Y h d hdL hA
  have hexp : ∀ y ∈ A, y ^ 3 = 1 := h.mem_partTwoF.1.2
  have hdAL : d ∈ A ⊓ L := by
    rw [hdL]
    exact Subgroup.mem_zpowers d
  obtain ⟨-, -, hd1⟩ := h.not_mem_facts hdL hA
  have hcdA : Subgroup.closure ({c, d} : Set G) ≤ A := by
    rw [Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact h.mem_A
    · exact hdAL.1
  have hWd : Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers d : Set G) :=
    (h117 G A c L a R Y h d hdL (Subgroup.zpowers d) (Subgroup.zpowers_le.mpr hdAL.1)
      (by rw [Nat.card_zpowers, orderOf_eq_prime (hexp d hdAL.1) hd1])).mpr rfl
  obtain ⟨g, hgcd, hgne⟩ := h112 G A c L a R Y h d hdL
  obtain ⟨w, hwW, hw⟩ := h114 G A c L a R Y h g (hgcd.trans hcdA)
  have hwH : w ∉ Subgroup.normalizer (Subgroup.zpowers c : Set G) := fun hwN =>
    hgne (hw.trans (Subgroup.mem_normalizer_iff_map_conj_eq.mp hwN))
  have hwc : w * c * w⁻¹ ∈ Subgroup.closure ({c, d} : Set G) := by
    have hmem : w * c * w⁻¹ ∈ (Subgroup.zpowers c).map (MulAut.conj w).toMonoidHom :=
      ⟨c, Subgroup.mem_zpowers c, rfl⟩
    rw [← hw] at hmem
    exact hgcd hmem
  obtain ⟨-, -, hCA⟩ := h118 G A c L a R Y h d w hdL hA hwW hwH hwc
  exact item119_of_kType_M h424 h45 h hdL hA hCA hWd (hKT G A c L a R Y h d hdL hA)

theorem item119_of_item118_M (h424 : Sec4.Item4_24M) (h45 : Sec4.Item4_5) (h112 : Item112)
    (h114 : Item114) (h117 : Item117) (h118 : Item118) : Item119 :=
  item119_of_M h424 h45 h112 h114 h117 h118 kType119

end Core

end CFSG.RankThree.PartTwo.Sec11
