module

public import CFSG.RankThree.PartTwo.Sec4.Item47WStatement
public import CFSG.RankThree.PartTwo.Sec13.Item13SetupAt
import CFSG.RankThree.PartTwo.Sec13.Item131Transport
import CFSG.RankThree.PartTwo.Sec8.Outer
import CFSG.RankThree.PartTwo.Sec6.Item612Core
public import CFSG.RankThree.PartTwo.Sec8.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item82OneProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

section Iso

variable {X Y : Type} [Group X] [Group Y]

theorem isSLThreePiAt_of_mulEquiv (e : X ≃* Y) {q : ℕ} (h : IsSLThreePiAt Y q) :
    IsSLThreePiAt X q := by
  obtain ⟨K, _, _, ⟨hK, hq, ⟨f⟩⟩ | ⟨hK, hq, ⟨f⟩⟩⟩ := h
  · exact ⟨K, inferInstance, inferInstance, Or.inl ⟨hK, hq, ⟨e.trans f⟩⟩⟩
  · exact ⟨K, inferInstance, inferInstance, Or.inr ⟨hK, hq, ⟨e.trans f⟩⟩⟩

theorem isoLThreePi_of_mulEquiv (e : X ≃* Y) {p f : ℕ} [Fact p.Prime] (h : IsoLThreePi Y p f) :
    IsoLThreePi X p f := by
  rcases h with ⟨hq, ⟨g⟩⟩ | ⟨hq, ⟨g⟩⟩
  · exact Or.inl ⟨hq, ⟨e.trans g⟩⟩
  · exact Or.inr ⟨hq, ⟨e.trans g⟩⟩

theorem isoGTwoEven_of_mulEquiv (e : X ≃* Y) {m : ℕ} (h : IsoGTwoEven Y m) : IsoGTwoEven X m := by
  obtain ⟨K, _, _, hK, ⟨g⟩⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, ⟨e.trans g⟩⟩

theorem isoPGUThree_of_mulEquiv (e : X ≃* Y) {q : ℕ} (h : IsoPGUThree Y q) :
    IsoPGUThree X q := by
  obtain ⟨K, _, _, hK, ⟨g⟩⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, ⟨e.trans g⟩⟩

end Iso

section Sub

variable {G : Type} [Group G] [Finite G] (C : Subgroup G)

theorem barCentralizer_map_sub (X' L' : Subgroup C) :
    barCentralizer (X'.map C.subtype) (L'.map C.subtype) =
      (barCentralizer X' L').map (Sec13.thetaQuotEquivSub C L').toMonoidHom := by
  set e := Sec13.thetaQuotEquivSub C L' with he
  have hA := Sec13.map_autThetaQuot_sub C X' L'
  ext z
  rw [barCentralizer, FixedPoints.mem_subgroup]
  constructor
  · intro hz
    refine ⟨e.symm z, ?_, by simp⟩
    rw [SetLike.mem_coe, barCentralizer, FixedPoints.mem_subgroup]
    rintro ⟨σ, hσ⟩
    have hmem : MulAut.congr e σ ∈ autThetaQuot (X'.map C.subtype) (L'.map C.subtype) := by
      rw [← hA]
      exact ⟨σ, hσ, rfl⟩
    have h1 : e (σ (e.symm z)) = z := hz ⟨_, hmem⟩
    change σ (e.symm z) = e.symm z
    exact e.injective (by rw [h1, MulEquiv.apply_symm_apply])
  · rintro ⟨w, hw, rfl⟩ ⟨τ, hτ⟩
    rw [← hA] at hτ
    obtain ⟨σ, hσ, rfl⟩ := hτ
    rw [SetLike.mem_coe, barCentralizer, FixedPoints.mem_subgroup] at hw
    have h1 := hw ⟨σ, hσ⟩
    change σ w = w at h1
    change e (σ (e.symm (e w))) = e w
    rw [MulEquiv.symm_apply_apply, h1]

theorem nonempty_barCentralizer_sub (L' : Subgroup C) (h : C) :
    Nonempty (barCentralizer (Subgroup.zpowers h) L' ≃*
      barCentralizer (Subgroup.zpowers (h : G)) (L'.map C.subtype)) := by
  have hz : (Subgroup.zpowers h).map C.subtype = Subgroup.zpowers (h : G) :=
    MonoidHom.map_zpowers C.subtype h
  rw [← hz, barCentralizer_map_sub]
  exact ⟨Subgroup.equivMapOfInjective _ _ (Sec13.thetaQuotEquivSub C L').injective⟩

theorem inducesOuterTheta_sub_iff (L' : Subgroup C) (x : C) :
    InducesOuterTheta x L' ↔ InducesOuterTheta (x : G) (L'.map C.subtype) := by
  constructor
  · rintro ⟨hx, hnot⟩
    have hx' := (Sec13.coe_mem_normalizer_map_iff C).mpr hx
    refine ⟨hx', fun hin => hnot ?_⟩
    have h1 := Sec13.congr_thetaQuotMulAut_sub C L' hx hx'
    change IsInnerAut (thetaQuotMulAut _ (Subgroup.normalizerMonoidHom _ _)) at hin
    rw [← h1, isInnerAut_congr] at hin
    exact hin
  · rintro ⟨hx', hnot⟩
    have hx := (Sec13.coe_mem_normalizer_map_iff C).mp hx'
    refine ⟨hx, fun hin => hnot ?_⟩
    have h1 := Sec13.congr_thetaQuotMulAut_sub C L' hx hx'
    change IsInnerAut (thetaQuotMulAut _ (Subgroup.normalizerMonoidHom _ _))
    rw [← h1, isInnerAut_congr]
    exact hin


theorem alt47_map (L' : Subgroup C) (a' : C) (h : Alt47 L' a') :
    Alt47 (L'.map C.subtype) (a' : G) := by
  set ε := Sec13.thetaQuotEquivSub C L' with hε
  have hk : ∀ {x : C} {k : AutKind}, InducesStdKind L' x k →
      InducesStdKind (L'.map C.subtype) (x : G) k := fun hx => Sec13.inducesStdKind_sub C L' hx
  have hiso : ∀ {X : Type} [Group X], Nonempty (L' ⧸ aschbacherSolvableCore 3 L' ≃* X) →
      Nonempty ((L'.map C.subtype) ⧸ aschbacherSolvableCore 3 (L'.map C.subtype) ≃* X) :=
    fun ⟨f⟩ => ⟨ε.symm.trans f⟩
  have hbar : ∀ (P : ∀ (X : Type) [Group X], Prop)
      (_ : ∀ {X Y : Type} [Group X] [Group Y], (X ≃* Y) → P Y → P X) (x : C),
      P (barCentralizer (Subgroup.zpowers x) L') →
        P (barCentralizer (Subgroup.zpowers (x : G)) (L'.map C.subtype)) := by
    intro P hP x hx
    obtain ⟨f⟩ := nonempty_barCentralizer_sub C L' x
    exact hP f.symm hx
  rcases h with ⟨p, e, hp, hp2, he, hX, hka⟩ | ⟨p, e, hp, hp3, he1, he2, hX, hka⟩ |
    ⟨hX, hka⟩ | ⟨n, hn, hX, hka⟩ | ⟨n, hn, hX, hka, hC⟩
  · exact Or.inl ⟨p, e, hp, hp2, he, hiso hX, hk hka⟩
  · refine Or.inr (Or.inl ⟨p, e, hp, hp3, he1, he2, ?_, hk hka⟩)
    rcases hX with hX | hX
    · exact Or.inl (isSLThreePiAt_of_mulEquiv ε.symm hX)
    · exact Or.inr (isoLThreePi_of_mulEquiv ε.symm hX)
  · refine Or.inr (Or.inr (Or.inl ⟨?_, hk hka⟩))
    rcases hX with ⟨m, hm, hX⟩ | ⟨n, hn, hX⟩
    · refine Or.inl ⟨m, hm, ?_⟩
      rcases hX with hX | ⟨K, _, _, hK, hX⟩ | hX | ⟨K, _, _, hK, hX⟩
      · exact Or.inl (hiso hX)
      · exact Or.inr (Or.inl ⟨K, inferInstance, inferInstance, hK, hiso hX⟩)
      · exact Or.inr (Or.inr (Or.inl (hiso hX)))
      · exact Or.inr (Or.inr (Or.inr ⟨K, inferInstance, inferInstance, hK, hiso hX⟩))
    · refine Or.inr ⟨n, hn, ?_⟩
      rcases hX with hX | hX | hX | hX | hX
      · exact Or.inl (CFSG.SectionRank.suzukiModel_of_mulEquiv ε.symm hX)
      · exact Or.inr (Or.inl (hiso hX))
      · exact Or.inr (Or.inr (Or.inl (hiso hX)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl
          (CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv ε.symm hX))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr
          (CFSG.SectionRank.reeTitsModel_of_mulEquiv ε.symm hX))))
  · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn, ?_, hk hka⟩)))
    rcases hX with hX | hX
    · exact Or.inl (isSLThreePiAt_of_mulEquiv ε.symm hX)
    · exact Or.inr (isoLThreePi_of_mulEquiv ε.symm hX)
  · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨n, hn,
      CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv ε.symm hX, hk hka, ?_⟩)))
    rcases hC with hC | ⟨σ, x, hσx, hσ, hσC, hxL, hxo, hxσ, hC⟩
    · exact Or.inl (hbar (fun X _ => IsoGTwoEven X n)
        (fun f h => isoGTwoEven_of_mulEquiv f h) a' hC)
    · refine Or.inr ⟨σ, x, congrArg Subtype.val hσx, hk hσ,
        hbar (fun X _ => IsoGTwoEven X n) (fun f h => isoGTwoEven_of_mulEquiv f h) σ hσC,
        Subgroup.mem_map_of_mem _ hxL, by rw [Subgroup.orderOf_coe, hxo],
        congrArg Subtype.val hxσ, ?_⟩
      exact hbar (fun X _ => IsoPGUThree X (2 ^ n)) (fun f h => isoPGUThree_of_mulEquiv f h) a' hC

theorem alt47W_map (L' : Subgroup C) (a' : C) (h : Alt47W L' a') :
    Alt47W (L'.map C.subtype) (a' : G) := by
  set ε := Sec13.thetaQuotEquivSub C L' with hε
  rcases h with h1 | h2 | h3 | h4 | ⟨n, hn, hX⟩
  · exact (alt47_map C L' a' (Or.inl h1)).toW
  · exact (alt47_map C L' a' (Or.inr (Or.inl h2))).toW
  · exact (alt47_map C L' a' (Or.inr (Or.inr (Or.inl h3)))).toW
  · exact (alt47_map C L' a' (Or.inr (Or.inr (Or.inr (Or.inl h4))))).toW
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      ⟨n, hn, CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv ε.symm hX⟩)))

end Sub

section Hyp81


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}

theorem exists_sub_of_hyp81 (h : Hyp81 G A c L a) :
    ∃ (L' : Subgroup (Subgroup.centralizer ({c} : Set G)))
      (a' : Subgroup.centralizer ({c} : Set G)),
      SectionFourHyp (Subgroup.centralizer ({c} : Set G)) ∧
      3 ∣ Nat.card (Subgroup.center (Subgroup.centralizer ({c} : Set G))) ∧
      L' ∈ thetaComponents 3 (Subgroup.centralizer ({c} : Set G)) ∧ orderOf a' = 3 ∧
      InducesOuterTheta a' L' ∧ L'.map (Subgroup.centralizer ({c} : Set G)).subtype = L ∧
      (a' : G) = a := by
  set C := Subgroup.centralizer ({c} : Set G) with hC
  have hAe := h.mem_partTwoF.1
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hc3 : c ^ 3 = 1 := hAe.2 c h.mem_A
  have ha3 : a ^ 3 = 1 := hAe.2 a h.a_mem
  have hout := h.inducesOuterTheta
  obtain ⟨L', hL', rfl⟩ := h.mem_thetaComponentsAt
  have hC4 : SectionFourHyp C := h.toTheoremFourHyp.sectionFourHyp
    (Sec6.centralizer_ne_top_of_ne_one h.toTheoremFourHyp h.ne_one)
  set c' : C := ⟨c, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ with hc'
  have hc'Z : c' ∈ Subgroup.center C := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp g.2)
  have hc'o : orderOf c' = 3 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime hc3 h.ne_one
  have h3 : 3 ∣ Nat.card (Subgroup.center C) := by
    rw [← hc'o, show orderOf c' = orderOf (⟨c', hc'Z⟩ : Subgroup.center C) from
      (Subgroup.orderOf_mk c' hc'Z).symm]
    exact orderOf_dvd_natCard _
  set a' : C :=
    ⟨a, Subgroup.mem_centralizer_singleton_iff.mpr (hcomm c h.mem_A a h.a_mem).symm⟩
    with ha'
  have ha'o : orderOf a' = 3 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime ha3 h.a_ne_one
  exact ⟨L', a', hC4, h3, hL', ha'o, (inducesOuterTheta_sub_iff C L' a').mpr hout, rfl, rfl⟩

theorem alt47_of_hyp81 (h47 : Item4_7) (h : Hyp81 G A c L a) : Alt47 L a := by
  obtain ⟨L', a', hC4, h3, hL', ha'o, hout', rfl, rfl⟩ := exists_sub_of_hyp81 h
  exact alt47_map _ L' a' (h47 _ hC4 h3 L' hL' a' ha'o hout')

theorem alt47W_of_hyp81 (h47 : Item4_7W) (h : Hyp81 G A c L a) : Alt47W L a := by
  obtain ⟨L', a', hC4, h3, hL', ha'o, hout', rfl, rfl⟩ := exists_sub_of_hyp81 h
  exact alt47W_map _ L' a' (h47 _ hC4 h3 L' hL' a' ha'o hout')

end Hyp81

end CFSG.RankThree.PartTwo.Sec8.Item82OneProof
