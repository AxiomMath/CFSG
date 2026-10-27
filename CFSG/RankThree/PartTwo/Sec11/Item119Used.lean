module

public import CFSG.RankThree.PartTwo.Sec4.Item424ProofStatement
public import CFSG.RankThree.PartTwo.Sec11.Item119K
public import CFSG.RankThree.PartTwo.Sec11.Item1116KFact
public import CFSG.RankThree.PartTwo.Sec11.Item116P2Proof
public import CFSG.RankThree.PartTwo.Sec11.Item116TheoremOP2
public import CFSG.RankThree.PartTwo.Sec11.LaterSteps
public import CFSG.RankThree.PartTwo.Sec13.Item131Transport

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.RankThree.PartOne.EmbeddingFixedResidual

@[expose] def Item119Used : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G), Sec11Std G A c L a R Y → ∀ d : G, A ⊓ L = Subgroup.zpowers d →
      A = Subgroup.closure {c, a, d} →
        (Nonempty (Sec4.autIn Y A ≃* Equiv.Perm (Fin 3)) ∨
            Nonempty (Sec4.autIn Y A ≃* DihedralGroup 6)) ∧
          (KFacts.InducesStdKind Y c .field ∨
            ∃ (X : Type) (_ : Group X), IsList119 X ∧
              Nonempty (sec11YA a Y A ≃* Multiplicative (ZMod 3) × X))

theorem item119Used_of_item119 (h119 : Item119) : Item119Used := by
  intro G _ _ A c L a R Y h d hdL hA
  rcases h119 G A c L a R Y h d hdL hA with ⟨hf, hS⟩ | ⟨hG2, hD⟩ | ⟨hL3, hS⟩ | ⟨hMH, -, hD⟩
  · exact ⟨Or.inl hS, Or.inl hf⟩
  · refine ⟨Or.inr hD, Or.inr ?_⟩
    rcases hG2 with ⟨q, hq, ⟨e⟩⟩ | ⟨q, hq, ⟨e⟩⟩
    · exact ⟨_, inferInstance, Or.inl ⟨q, hq, ⟨MulEquiv.refl _⟩⟩, ⟨e⟩⟩
    · exact ⟨_, inferInstance, Or.inr (Or.inl ⟨q, hq, ⟨MulEquiv.refl _⟩⟩), ⟨e⟩⟩
  · refine ⟨Or.inl hS, Or.inr ?_⟩
    rcases hL3 with ⟨p, e', hp, he, ⟨hpe, ⟨e⟩⟩ | ⟨hpe, ⟨e⟩⟩⟩ |
      ⟨π, p, f, K', hK', hPF, hmod, ⟨e⟩⟩
    · exact ⟨_, inferInstance,
        Or.inr (Or.inr (Or.inl ⟨p, e', hp, he, Or.inl ⟨hpe, ⟨MulEquiv.refl _⟩⟩⟩)), ⟨e⟩⟩
    · exact ⟨_, inferInstance,
        Or.inr (Or.inr (Or.inl ⟨p, e', hp, he, Or.inr ⟨hpe, ⟨MulEquiv.refl _⟩⟩⟩)), ⟨e⟩⟩
    · exact ⟨_, inferInstance,
        Or.inr (Or.inr (Or.inr (Or.inl ⟨π, p, f, K', hK', hPF, hmod, ⟨MulEquiv.refl _⟩⟩))), ⟨e⟩⟩
  · refine ⟨Or.inr hD, Or.inr ?_⟩
    rcases hMH with hM | hH
    · exact ⟨CFSG.Blueprint.NativeSporadic.M24, inferInstance,
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨MulEquiv.refl _⟩)))), hM⟩
    · exact ⟨CFSG.Blueprint.NativeSporadic.He, inferInstance,
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨MulEquiv.refl _⟩)))), hH⟩

section Core

variable {G : Type} [Group G]

theorem maximal_subgroupOf_of_le {A C : Subgroup G}
    (hA : ∀ B : Subgroup G, CFSG.Assembly.IsElemAbelian 3 B → A ≤ B → B = A)
    (hAe : CFSG.Assembly.IsElemAbelian 3 A) (hAC : A ≤ C) :
    Maximal (fun B : Subgroup C => CFSG.Assembly.IsElemAbelian 3 B) (A.subgroupOf C) := by
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  refine ⟨⟨⟨⟨fun y z => Subtype.ext (Subtype.ext ?_)⟩⟩, fun y hy => ?_⟩, fun B hB hAB => ?_⟩
  · exact hcomm _ (Subgroup.mem_subgroupOf.mp y.2) _ (Subgroup.mem_subgroupOf.mp z.2)
  · exact Subtype.ext (by simpa using hAe.2 _ (Subgroup.mem_subgroupOf.mp hy))
  · have hAB' : A ≤ B.map C.subtype := fun x hx =>
      ⟨⟨x, hAC hx⟩, hAB (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
    have heq := hA _ (isElemAbelian_map_subtype hB) hAB'
    intro x hx
    rw [Subgroup.mem_subgroupOf, ← heq]
    exact ⟨x, hx, rfl⟩

theorem mk_mem_center_centralizer (a : G) :
    (⟨a, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ :
      Subgroup.centralizer ({a} : Set G)) ∈ Subgroup.center (Subgroup.centralizer ({a} : Set G)) :=
  Subgroup.mem_center_iff.mpr fun z =>
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp z.2)

variable [Finite G]

theorem P2Proof.autIn_cases_of_item4_24Used (h424 : Sec4.Item4_24Used) (h45 : Sec4.Item4_5)
    {A : Subgroup G} {c : G} {L : Subgroup G} {a : G} {R Y : Subgroup G}
    (h : Sec11Std G A c L a R Y) {d : G} (hdL : A ⊓ L = Subgroup.zpowers d)
    (hA : A = Subgroup.closure {c, a, d})
    (hCA : Late.sectionCentralizer A Y (inSubgroup (aschbacherSolvableCore 3) Y) =
      (Subgroup.zpowers a : Set G))
    (hWd : ∀ w ∈ Subgroup.normalizer (A : Set G), w * a * w⁻¹ = a →
      w * d * w⁻¹ ∈ Subgroup.zpowers d) :
    Nonempty (Sec4.autIn Y A ≃* Equiv.Perm (Fin 3)) ∨
      Nonempty (Sec4.autIn Y A ≃* DihedralGroup 6) := by
  have hKT := kType119 G A c L a R Y h d hdL hA
  have hCA' : Late.sectionCentralizer A Y ((aschbacherSolvableCore 3 Y).map Y.subtype) =
      (Subgroup.zpowers a : Set G) := hCA
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
  have hC4 : SectionFourHyp C := hG.sectionFourHyp
    (PartOne.EmbeddingFixedResidual.centralizer_ne_top_of_simple hG.nonabelian ha1)
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
    rw [hz, hCA', SetLike.mem_coe, SetLike.mem_coe]
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
    have hwa : (w : G) * a * (w : G)⁻¹ = a := by
      rw [Subgroup.mem_centralizer_singleton_iff.mp w.2, mul_inv_cancel_right]
    rw [hAK]
    refine (Sec13.coe_mem_normalizer_map_iff C).mp ?_
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hdC]
    exact TheoremO.mem_normalizer_zpowers_of_conj_mem (hWd _ hw' hwa)
  obtain ⟨hAut, -⟩ := h424 C hC4 A' hA'max h27 hEF L' hY' a' ha'3 ha'Z hsec c' hc'A hc'a
    (K.subgroupOf C) hK' hKT' hNK
  obtain ⟨eAut⟩ := Sec13.nonempty_autIn_subgroupOf_equiv C hYC hAC
  rcases hAut with ⟨⟨e1⟩⟩ | ⟨⟨e2⟩⟩
  · exact Or.inl ⟨eAut.symm.trans e1⟩
  · exact Or.inr ⟨eAut.symm.trans e2⟩

theorem P2Proof.false_of_sectionCentralizer_eq_zpowers_of_used (h424 : Sec4.Item4_24Used)
    (h45 : Sec4.Item4_5) {A : Subgroup G} {c : G} {L : Subgroup G} {a : G} {R Y : Subgroup G}
    (h : Sec11Std G A c L a R Y) {d : G} (hdL : A ⊓ L = Subgroup.zpowers d)
    (hdc : d ∉ Subgroup.zpowers c)
    (hCA : Late.sectionCentralizer A Y (inSubgroup (aschbacherSolvableCore 3) Y) =
      (Subgroup.zpowers a : Set G))
    (hfix : ∀ w ∈ Subgroup.normalizer (A : Set G), w * a * w⁻¹ = a →
      w * c * w⁻¹ ∈ Subgroup.zpowers c ∧ w * d * w⁻¹ ∈ Subgroup.zpowers d) : False := by
  have hA : A = Subgroup.closure {c, a, d} := by
    rw [← Item116Fusion.closure_cda_eq h hdL hdc, Set.pair_comm d a]
  have hsq : ∀ σ : Sec4.autIn Y A, σ * σ = 1 := fun σ =>
    Subtype.ext (P2Proof.mul_self_eq_one_of_mem_autIn hA h.mem_partTwoF.1.2
      (Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt_Y) hfix σ.2)
  rcases P2Proof.autIn_cases_of_item4_24Used h424 h45 h hdL hA hCA
      (fun w hw hwa => (hfix w hw hwa).2) with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact P2Proof.false_of_mulEquiv_of_mul_self e hsq
      (x := Equiv.swap 0 1 * Equiv.swap 1 2) (by decide)
  · exact P2Proof.false_of_mulEquiv_of_mul_self e hsq (x := DihedralGroup.r 1) (by decide)

theorem item116P2bCore_of_used (h424 : Sec4.Item4_24Used) (h45 : Sec4.Item4_5) :
    Item116P2bCore :=
  fun _ _ _ _ _ _ _ _ _ h _ hdL _ _ _ hdc _ _ _ _ _ _ _ _ _ hCA hfix =>
    P2Proof.false_of_sectionCentralizer_eq_zpowers_of_used h424 h45 h hdL hdc hCA hfix

end Core

end CFSG.RankThree.PartTwo.Sec11
