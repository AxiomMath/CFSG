module

public import CFSG.RankThree.PartTwo.Sec21.Item2119End4ProofTools
public import CFSG.RankThree.PartTwo.Sec11.Item119Used
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec21.Item2119End4ProofKF
public import CFSG.RankThree.PartTwo.Sec4.Item423StepsProof424

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering2125

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.RankThree.PartTwo.Sec21.Item2119End4Proof

variable {G : Type} [Group G] [Finite G]

theorem item424M_at
    (h424 : Sec4.Item4_24M)
    {A : Subgroup G} (hAe : IsElemAbelian 3 A)
    (hAmax : ∀ B : Subgroup G, IsElemAbelian 3 B → A ≤ B → B = A) (h27 : Nat.card A = 27)
    (hEF : partTwoE G = partTwoF G) {e : G} (heA : e ∈ A) (he1 : e ≠ 1)
    (hC4 : SectionFourHyp (Subgroup.centralizer ({e} : Set G)))
    {Y : Subgroup G} (hY : Y ∈ thetaComponentsAt 3 e)
    (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    (hCA : A ⊓ Sec4.thetaQuotCentralizer Y = Subgroup.zpowers e)
    {c : G} (hcA : c ∈ A) (hce : c ∉ Subgroup.zpowers e) {L : Subgroup G}
    (hLc : L ∈ thetaComponentsAt 3 c) (hKY : Sec11.sec11K L e ≤ Y)
    (hKT : Sec11.IsType424 (lBar (Sec11.sec11K L e)))
    (hKq : IsQuasisimple (lBar (Sec11.sec11K L e)))
    (hNK : Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((A ⊓ Sec11.sec11K L e : Subgroup G) : Set G)) :
    (KFacts.InducesStdKind Y c .field ∧ Nonempty (Sec4.autIn Y A ≃* Equiv.Perm (Fin 3))) ∨
      (((∃ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.G2 q).Valid),
            Nonempty (Sec11.sec11YA e Y A ≃* Multiplicative (ZMod 3) ×
              (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group)) ∨
          ∃ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid),
            Nonempty (Sec11.sec11YA e Y A ≃* Multiplicative (ZMod 3) ×
              (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group)) ∧
        Nonempty (Sec4.autIn Y A ≃* DihedralGroup 6)) ∨
      ((Sec8.IsZ3LThreePi (Sec11.sec11YA e Y A) ∨ Sec8.IsZ3PGLThreePi (Sec11.sec11YA e Y A)) ∧
        Nonempty (Sec4.autIn Y A ≃* Equiv.Perm (Fin 3))) ∨
      ((Nonempty (Sec11.sec11YA e Y A ≃* Multiplicative (ZMod 3) ×
            CFSG.Blueprint.NativeSporadic.M24) ∨
          Nonempty (Sec11.sec11YA e Y A ≃* Multiplicative (ZMod 3) ×
            CFSG.Blueprint.NativeSporadic.He)) ∧
        Nonempty (lBar (Sec11.sec11K L e) ≃* projSL 3 (GaloisField 2 1)) ∧
        Nonempty (Sec4.autIn Y A ≃* DihedralGroup 6)) := by
  have hexp : ∀ y ∈ A, y ^ 3 = 1 := hAe.2
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  set C := Subgroup.centralizer ({e} : Set G) with hC
  have hAC : A ≤ C := fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr (hcomm y hy e heA)
  have hcC : c ∈ C := hAC hcA
  have heC : e ∈ C := hAC heA
  obtain ⟨hYC, hY'⟩ := mem_thetaComponentsIn_iff.mp hY
  set A' := A.subgroupOf C with hA'def
  have hA' : CFSG.Assembly.IsElemAbelian 3 A' := by
    refine ⟨⟨⟨fun y z => Subtype.ext (Subtype.ext ?_)⟩⟩, fun y hy => ?_⟩
    · exact hcomm _ (Subgroup.mem_subgroupOf.mp y.2) _ (Subgroup.mem_subgroupOf.mp z.2)
    · exact Subtype.ext (by simpa using hexp _ (Subgroup.mem_subgroupOf.mp hy))
  have h27' : Nat.card A' = 27 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAC).toEquiv, h27]
  have hEF' : partTwoE C = partTwoF C := Sec11.partTwoE_eq_partTwoF_subgroup hEF C
  set L' := Y.subgroupOf C with hL'def
  set e' : C := ⟨e, heC⟩ with he'def
  have he'3 : orderOf e' = 3 := by
    rw [he'def, Subgroup.orderOf_mk]
    exact orderOf_eq_prime (hexp e heA) he1
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
  have hCA' : Late.sectionCentralizer A Y ((aschbacherSolvableCore 3 Y).map Y.subtype) =
      (Subgroup.zpowers e : Set G) := by
    rw [Sec13.sectionCentralizer_eq_inf hAY, hCA]
  have hsec : Late.sectionCentralizer A' L' ((aschbacherSolvableCore 3 L').map L'.subtype) =
      (Subgroup.zpowers e' : Set C) := by
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
    rw [hz, hCA', SetLike.mem_coe, SetLike.mem_coe]
    constructor
    · intro h1
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext (by simpa [he'def] using hk)⟩
    · intro h1
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp h1
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simp [he'def]⟩
  set c' : C := ⟨c, hcC⟩ with hc'def
  have hc'A : c' ∈ A' := Subgroup.mem_subgroupOf.mpr hcA
  have hc'e : c' ∉ Subgroup.zpowers e' := by
    intro hc'
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hc'
    apply hce
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    simpa [he'def, hc'def] using congrArg Subtype.val hk
  set K := Sec11.sec11K L e with hKdef
  have hKC : K ≤ C := (Subgroup.map_subtype_le _).trans inf_le_right
  have hK' := mem_thetaComponentsIn_sec11K' hLc hKY hKq hcC
  have hKT' : Sec11.IsType424 (K.subgroupOf C ⧸ aschbacherSolvableCore 3 (K.subgroupOf C)) := by
    set eK := Subgroup.subgroupOfEquivOfLe hKC
    exact Sec11.isType424_of_mulEquiv (QuotientGroup.congr _ _ eK
      (CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv Nat.prime_three eK)) hKT
  have hAKC : A ⊓ K ≤ C := inf_le_left.trans hAC
  have hAK : A' ⊓ K.subgroupOf C = (A ⊓ K).subgroupOf C := by
    ext x
    rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
      Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  have hNK' : Subgroup.normalizer (A' : Set C) ≤
      Subgroup.normalizer ((A' ⊓ K.subgroupOf C : Subgroup C) : Set C) := by
    intro w hw
    have hw' : (w : G) ∈ Subgroup.normalizer (A : Set G) := by
      have := (Sec13.coe_mem_normalizer_map_iff C (L' := A')).mpr hw
      rwa [hA'def, Subgroup.subgroupOf_map_subtype, inf_of_le_left hAC] at this
    rw [hAK]
    refine (Sec13.coe_mem_normalizer_map_iff C).mp ?_
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hAKC]
    exact hNK hw'
  have h4 := h424 C hC4 A' (Sec11.maximal_subgroupOf_of_le hAmax hAe hAC) h27' hEF' L' hY' e'
    he'3 (Sec11.mk_mem_center_centralizer e) hsec c' hc'A hc'e (K.subgroupOf C) hK' hKT' hNK'
  have himg : Sec4.thetaImage (L' ⊔ A') = Sec11.sec11YA e Y A := by
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
  · set eK' := Subgroup.subgroupOfEquivOfLe hKC
    have eQ : K.subgroupOf C ⧸ aschbacherSolvableCore 3 (K.subgroupOf C) ≃*
        K ⧸ aschbacherSolvableCore 3 K := QuotientGroup.congr _ _ eK'
      (CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv Nat.prime_three eK')
    exact Or.inr (Or.inr (Or.inr ⟨h4, ⟨eQ.symm.trans eK⟩, ⟨eAut.symm.trans e4⟩⟩))

end CFSG.RankThree.PartTwo.Sec21.Hering2125
