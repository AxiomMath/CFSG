module

public import CFSG.RankThree.PartTwo.Sec12.Hering129KSub
public import CFSG.RankThree.PartTwo.Sec11.Item119Used
public import CFSG.RankThree.PartTwo.Sec11.Item1116Proof
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec12.Item128BarProofSetup
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)


section Transport

variable {G : Type} [Group G] [Finite G]

theorem mem_thetaComponentsIn_subgroupOf {Y X : Subgroup G} {b : G} (C : Subgroup G)
    (hYC : Y ≤ C) (hbC : b ∈ C)
    (hX : X ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({b} : Set G))) :
    X.subgroupOf C ∈ thetaComponentsIn (Y.subgroupOf C ⊓
      Subgroup.centralizer ({(⟨b, hbC⟩ : C)} : Set C)) := by
  obtain ⟨hXM, hX'⟩ := mem_thetaComponentsIn_iff.mp hX
  set b' : C := ⟨b, hbC⟩ with hb'
  set M := Y ⊓ Subgroup.centralizer ({b} : Set G) with hM
  set Z := Y.subgroupOf C ⊓ Subgroup.centralizer ({b'} : Set C) with hZdef
  have hXC : X ≤ C := hXM.trans (inf_le_left.trans hYC)
  have hXZ : X.subgroupOf C ≤ Z := by
    intro k hk
    rw [Subgroup.mem_subgroupOf] at hk
    have hkM := hXM hk
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mpr hkM.1, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp hkM.2
  set T := (X.subgroupOf C).subgroupOf Z with hT
  set e : T ≃* X := (Subgroup.subgroupOfEquivOfLe hXZ).trans (Subgroup.subgroupOfEquivOfLe hXC)
    with he
  refine mem_thetaComponentsIn_iff.mpr ⟨hXZ, ?_, ?_, ?_⟩
  · have hXp : Group.IsPerfect X := by
      have := hX'.1
      exact Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hXM).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hXM).surjective
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  · set ι : Z →* ↥M :=
      (C.subtype.comp Z.subtype).codRestrict M (fun z => by
        refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · exact Subgroup.mem_subgroupOf.mp z.2.1
        · have hz := Subgroup.mem_centralizer_singleton_iff.mp z.2.2
          exact Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hz)) with hι
    set MD := (X.subgroupOf M).comap ι with hMD
    have hMDsn : MD.IsSubnormal := hX'.2.1.comap ι
    have hTMD : (X.subgroupOf C).subgroupOf Z = MD := by
      ext t
      simp only [hMD, Subgroup.mem_subgroupOf, Subgroup.mem_comap]
      rfl
    rw [hTMD]
    exact hMDsn
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.congr _ _ e (CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv
        Nat.prime_three e)).symm
      (by
        have := hX'.2.2
        exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
          (QuotientGroup.congr _ _ (Subgroup.subgroupOfEquivOfLe hXM)
            (CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv Nat.prime_three
              (Subgroup.subgroupOfEquivOfLe hXM))) this)

theorem yshape_424 (h424 : Sec4.Item4_24Used) (hst : PartTwoStanding G) {A : Subgroup G}
    (hAF : A ∈ partTwoF G) (hFE : partTwoF G = partTwoE G) (h27 : Nat.card A = 27) {x b : G}
    (hxA : x ∈ A) (hx1 : x ≠ 1) (hbA : b ∈ A) (hbx : b ∉ Subgroup.zpowers x) {Y : Subgroup G}
    (hY : Y ∈ thetaComponentsAt 3 x)
    (hsec : Late.sectionCentralizer A Y ((aschbacherSolvableCore 3 Y).map Y.subtype) =
      (Subgroup.zpowers x : Set G))
    {X : Subgroup G} (hX : X ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({b} : Set G)))
    (hXT : (∃ n : ℕ, 1 ≤ n ∧
        Nonempty (X ⧸ aschbacherSolvableCore 3 X ≃* projSL 2 (GaloisField 2 n))) ∨
      (∃ (p n : ℕ) (_ : Fact p.Prime), 3 < p ∧ 1 ≤ n ∧
        Nonempty (X ⧸ aschbacherSolvableCore 3 X ≃* projSL 2 (GaloisField p n))))
    (hNX : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer ((A ⊓ X : Subgroup G) : Set G)) :
    KFacts.InducesStdKind Y b .field ∨
      ∃ (X' : Type) (_ : Group X'), Sec4.IsList424 X' ∧
        Nonempty (Sec11.sec11YA x Y A ≃* Multiplicative (ZMod 3) × X') := by
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hAF.1
  have hexp : ∀ y ∈ A, y ^ 3 = 1 := hAe.2
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  obtain ⟨hC4, hAC, hA'max, h27'⟩ := Proof128.centralizer_setup hst hAF h27 hxA hx1
  set C := Subgroup.centralizer ({x} : Set G) with hC
  have hbC : b ∈ C := hAC hbA
  have hxC : x ∈ C := hAC hxA
  obtain ⟨hYC, hY'⟩ := mem_thetaComponentsIn_iff.mp hY
  set A' := A.subgroupOf C with hA'def
  have hEF : partTwoE C = partTwoF C := Sec11.partTwoE_eq_partTwoF_subgroup hFE.symm C
  set L' := Y.subgroupOf C with hL'def
  set a' : C := ⟨x, hxC⟩ with ha'def
  have ha'3 : orderOf a' = 3 := by
    rw [ha'def, Subgroup.orderOf_mk]
    exact orderOf_eq_prime (hexp x hxA) hx1
  have ha'Z : a' ∈ Subgroup.center C := Sec11.mk_mem_center_centralizer x
  have hLmap : L'.map C.subtype = Y := by
    rw [hL'def, Subgroup.subgroupOf_map_subtype, inf_of_le_left hYC]
  have hθ : ∀ w : C, w ∈ (aschbacherSolvableCore 3 L').map L'.subtype ↔
      (w : G) ∈ inSubgroup (aschbacherSolvableCore 3) Y := by
    intro w
    have e1 := Sec11.inSubgroup_theta_map_subtype_sub L'
    rw [hLmap] at e1
    rw [e1]
    constructor
    · intro hw
      exact ⟨w, hw, rfl⟩
    · rintro ⟨w', hw', hww'⟩
      have : w' = w := Subtype.ext hww'
      rw [← this]
      exact hw'
  have hsec' : Late.sectionCentralizer A' L' ((aschbacherSolvableCore 3 L').map L'.subtype) =
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
    rw [hz, hsec, SetLike.mem_coe, SetLike.mem_coe]
    constructor
    · intro h1
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext (by simpa [ha'def] using hk)⟩
    · intro h1
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp h1
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simp [ha'def]⟩
  set b' : C := ⟨b, hbC⟩ with hb'def
  have hb'A : b' ∈ A' := Subgroup.mem_subgroupOf.mpr hbA
  have hb'a : b' ∉ Subgroup.zpowers a' := by
    intro hb'
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb'
    apply hbx
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    simpa [ha'def, hb'def] using congrArg Subtype.val hk
  obtain ⟨hXM, -⟩ := mem_thetaComponentsIn_iff.mp hX
  have hXC : X ≤ C := hXM.trans (inf_le_left.trans hYC)
  have hK' := mem_thetaComponentsIn_subgroupOf C hYC hbC hX
  set K' := X.subgroupOf C with hK'def
  have eK : K' ⧸ aschbacherSolvableCore 3 K' ≃* X ⧸ aschbacherSolvableCore 3 X :=
    QuotientGroup.congr _ _ (Subgroup.subgroupOfEquivOfLe hXC)
      (CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv Nat.prime_three
        (Subgroup.subgroupOfEquivOfLe hXC))
  have hKT' : (∃ n : ℕ, 1 ≤ n ∧
        Nonempty (K' ⧸ aschbacherSolvableCore 3 K' ≃* projSL 2 (GaloisField 2 n))) ∨
      (∃ (p n : ℕ) (_ : Fact p.Prime), 3 < p ∧ 1 ≤ n ∧
        Nonempty (K' ⧸ aschbacherSolvableCore 3 K' ≃* projSL 2 (GaloisField p n))) ∨
      ∃ n : ℕ, 1 ≤ n ∧ Sec8.IsoLThreeMinusPi (K' ⧸ aschbacherSolvableCore 3 K') 2 n := by
    rcases hXT with ⟨n, hn, ⟨f⟩⟩ | ⟨p, n, hp, hp3, hn, ⟨f⟩⟩
    · exact Or.inl ⟨n, hn, ⟨eK.trans f⟩⟩
    · exact Or.inr (Or.inl ⟨p, n, hp, hp3, hn, ⟨eK.trans f⟩⟩)
  have hAXC : A ⊓ X ≤ C := inf_le_right.trans hXC
  have hAK : A' ⊓ K' = (A ⊓ X).subgroupOf C := by
    ext z
    simp only [hA'def, hK'def, Subgroup.mem_inf, Subgroup.mem_subgroupOf]
  have hNK : Subgroup.normalizer (A' : Set C) ≤
      Subgroup.normalizer ((A' ⊓ K' : Subgroup C) : Set C) := by
    intro w hw
    have hw' : (w : G) ∈ Subgroup.normalizer (A : Set G) := by
      have := (Sec13.coe_mem_normalizer_map_iff C (L' := A')).mpr hw
      rwa [hA'def, Subgroup.subgroupOf_map_subtype, inf_of_le_left hAC] at this
    rw [hAK]
    refine (Sec13.coe_mem_normalizer_map_iff C).mp ?_
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hAXC]
    exact hNX hw'
  have h4 := h424 C hC4 A' hA'max h27' hEF L' hY' a' ha'3 ha'Z hsec' b' hb'A hb'a K' hK' hKT' hNK
  have himg : Sec4.thetaImage (L' ⊔ A') = Sec11.sec11YA x Y A := by
    rw [hL'def, hA'def, ← Subgroup.subgroupOf_sup hYC hAC]
    rfl
  rw [himg] at h4
  rcases h4.2 with h1 | ⟨X', _, hX', hXe⟩
  · left
    have hk := Sec13.inducesStdKind_sub C L' h1
    rw [hLmap] at hk
    exact hk
  · exact Or.inr ⟨X', inferInstance, hX', hXe⟩

theorem yshape_424_commutator {A : Subgroup G} {x : G} {Y : Subgroup G}
    (hY : Y ∈ thetaComponentsAt 3 x) (hAC : A ≤ Subgroup.centralizer ({x} : Set G))
    (hAN : A ≤ Subgroup.normalizer (Y : Set G)) (hA : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u)
    {X' : Type} [Group X'] (e : Sec11.sec11YA x Y A ≃* Multiplicative (ZMod 3) × X') :
    Nonempty (Y ⧸ aschbacherSolvableCore 3 Y ≃* _root_.commutator X') :=
  Sec11.Item1116Proof.nonempty_thetaQuot_equiv_commutator hY hAC hAN hA e

theorem resCent_mem_thetaComponentsIn {K Y : Subgroup G} {b x : G}
    (hK : K ∈ thetaComponentsAt 3 b) (hYx : Y ≤ Subgroup.centralizer ({x} : Set G))
    (hXY : resCent K x ≤ Y)
    (hXq : IsQuasisimple (↥(resCent K x) ⧸ aschbacherSolvableCore 3 ↥(resCent K x))) :
    resCent K x ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({b} : Set G)) := by
  have hKb : K ≤ Subgroup.centralizer ({b} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hK
  have hXK : resCent K x ≤ K := (resCent_le K x).trans inf_le_left
  have hXM : resCent K x ≤ Y ⊓ Subgroup.centralizer ({b} : Set G) :=
    le_inf hXY (hXK.trans hKb)
  haveI : Group.IsPerfect ↥(resCent K x) := isPerfect_resCent K x
  refine mem_thetaComponentsIn_iff.mpr ⟨hXM, ?_, ?_, ?_⟩
  · exact Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hXM).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hXM).symm.surjective
  · exact resCent_isSubnormal hK inf_le_right (inf_le_left.trans hYx) hXM
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.congr _ _ (Subgroup.subgroupOfEquivOfLe hXM)
        (CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv Nat.prime_three
          (Subgroup.subgroupOfEquivOfLe hXM))).symm hXq

end Transport

end CFSG.RankThree.PartTwo.Sec12
