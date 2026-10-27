module

public import CFSG.RankThree.PartTwo.Sec13.Item134Arg128FailPoint
import CFSG.RankThree.PartTwo.Sec13.Item134ONProof
import CFSG.RankThree.PartTwo.Sec13.Item13Models
import CFSG.RankThree.PartTwo.Sec13.Item13Theta
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec12.Item124Bar
import CFSG.RankThree.PartTwo.Sec4.LThreePiCaseI
import CFSG.RankThree.PartOne.S10.EmbeddingFixedResidual
import CFSG.RankThree.PartTwo.KFacts.KS14HJTwentySeven
import CFSG.RankThree.PartTwo.Sec6.Item612
import CFSG.GroupTheory.PerfectResidualNodes

public section

namespace CFSG.RankThree.PartTwo.Sec13.Item134Arg128Fail

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec13.Item134SylowBarProof
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Assembly.RankThreeEven (projImage)
open Matrix (ProjGenLinGroup)

variable {G : Type} [Group G] [Finite G] {A L K : Subgroup G} {c d : G}

theorem le_inSubgroup_perfectResidual {P X : Subgroup G} (hP : Group.IsPerfect P) (hPX : P ≤ X) :
    P ≤ inSubgroup perfectResidual X := by
  have hP' : Group.IsPerfect (P.subgroupOf X) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hPX).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hPX).symm.surjective
  have hle := (perfect_residual_transport (MonoidHom.id X)).2.2 (P.subgroupOf X) hP'
  intro p hp
  exact ⟨⟨p, hPX hp⟩, hle (Subgroup.mem_subgroupOf.mpr hp), rfl⟩

theorem inf_le_of_mem_B (h48 : Sec4.Item4_8) (H : Base A c L d K)
    (heq : A ⊓ Sec4.thetaQuotCentralizer K = Subgroup.zpowers c ⊔ Subgroup.zpowers d)
    {a : G} (haB : a ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers d) (ha1 : a ≠ 1)
    {J : Subgroup G} (hJ : Sec13Data G A a J) : A ⊓ L ≤ J := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have haA : a ∈ A := H.B_le haB
  have ha3 : a ^ 3 = 1 := H.data.isElemAbelian.2 a haA
  have haK : a ∈ Sec4.thetaQuotCentralizer K := by
    have : a ∈ A ⊓ Sec4.thetaQuotCentralizer K := heq ▸ haB
    exact this.2
  obtain ⟨haN, hatriv⟩ := Sec6.mem_thetaQuotCentralizer_iff.mp haK
  have htriv : ∀ w ∈ K, a * w * a⁻¹ * w⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) K := by
    intro w hw
    have h1 := Sec12.conj_mem_inSubgroup_theta (Subgroup.le_normalizer hw) (hatriv w hw)
    have e : w * (w⁻¹ * (a * w * a⁻¹)) * w⁻¹ = a * w * a⁻¹ * w⁻¹ := by group
    rwa [e] at h1
  have hda : d * a = a * d := H.data.commute H.mem_A haA
  obtain ⟨-, P', hP', hP'eq⟩ := PartOne.EmbeddingFixedResidual.fixed_residual_ambient
    Nat.prime_three hda ⟨1, by rw [pow_one]; exact orderOf_eq_prime ha3 ha1⟩ H.mem_K haN htriv
  have : IsSimpleGroup G := H.data.isSimpleGroup
  have hCtop : Subgroup.centralizer ({a} : Set G) ≠ ⊤ :=
    PartOne.EmbeddingFixedResidual.centralizer_ne_top_of_simple H.data.nonabelian ha1
  have hS4 : SectionFourHyp (Subgroup.centralizer ({a} : Set G)) :=
    H.data.toTheoremFourHyp.sectionFourHyp hCtop
  have hAC : A ≤ Subgroup.centralizer ({a} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (H.data.commute hx haA)
  set A' := A.subgroupOf (Subgroup.centralizer ({a} : Set G)) with hA'def
  have hA'e : CFSG.Assembly.IsElemAbelian 3 A' :=
    ⟨⟨⟨fun x y => Subtype.ext (Subtype.ext (H.data.commute (Subgroup.mem_subgroupOf.mp x.2)
      (Subgroup.mem_subgroupOf.mp y.2)))⟩⟩,
      fun x hx => Subtype.ext (H.data.isElemAbelian.2 _ (Subgroup.mem_subgroupOf.mp hx))⟩
  have h27' : Nat.card A' = 3 ^ 3 := by
    rw [hA'def, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAC).toEquiv, H.data.card_eq]
    norm_num
  have hd'A : (⟨d, PartOne.EmbeddingFixedResidual.commute_mem_centralizer hda⟩ :
      Subgroup.centralizer ({a} : Set G)) ∈ A' := Subgroup.mem_subgroupOf.mpr H.mem_A
  have hd'1 : (⟨d, PartOne.EmbeddingFixedResidual.commute_mem_centralizer hda⟩ :
      Subgroup.centralizer ({a} : Set G)) ≠ 1 := fun h => H.ne_one (congrArg Subtype.val h)
  obtain ⟨X, hX, hP'X⟩ := h48 (Subgroup.centralizer ({a} : Set G)) hS4 A' hA'e
    ⟨3, le_rfl, h27'⟩ _ hd'A hd'1 P' hP'
  set XG := X.map (Subgroup.centralizer ({a} : Set G)).subtype with hXG
  have hXa : XG ∈ thetaComponentsAt 3 a := ⟨X, hX, rfl⟩
  have hJ₀ : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ≤
      K ⊓ Subgroup.centralizer ({a} : Set G) := by
    refine le_inf H.residual_le fun x hx => ?_
    have hxL : x ∈ L ⊓ Subgroup.centralizer ({d} : Set G) := Subgroup.map_subtype_le _ hx
    have hxc : x * c = c * x := H.comm_L hxL.1
    have hxd : x * d = d * x := Subgroup.mem_centralizer_singleton_iff.mp hxL.2
    have hle : Subgroup.zpowers c ⊔ Subgroup.zpowers d ≤
        Subgroup.centralizer ({x} : Set G) := by
      refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_) <;>
        rw [Subgroup.mem_centralizer_singleton_iff]
      · exact hxc.symm
      · exact hxd.symm
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp (hle haB)).symm
  have hALX : A ⊓ L ≤ XG := by
    intro x hx
    have h1 := le_inSubgroup_perfectResidual
      (PartOne.EmbeddingFixedResidual.isPerfect_inSubgroup_perfectResidual _) hJ₀
      (inf_le_residual H hx)
    rw [← hP'eq] at h1
    obtain ⟨y, hy, rfl⟩ := h1
    exact ⟨y, hP'X hy, rfl⟩
  by_contra hcon
  have hXJ : XG ≠ J := fun h => hcon (h ▸ hALX)
  have hle : A ⊓ L ≤ Subgroup.zpowers a := by
    intro x hx
    have hmem : x ∈ Late.sectionCentralizer A J ((aschbacherSolvableCore 3 J).map J.subtype) := by
      refine ⟨hx.1, fun y hy => ?_⟩
      have h1 := Sec10.commutator_mem_theta_of_ne hXa hJ.mem_thetaComponentsAt hXJ (hALX hx) hy
      have h2 : x * y * x⁻¹ * y⁻¹ ∈ J :=
        J.mul_mem ((Subgroup.mem_normalizer_iff.mp (hJ.le_normalizer hx.1) y).mp hy) (J.inv_mem hy)
      have h3 : x * y * x⁻¹ * y⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) J := by
        rw [Sec6.theta_eq_inf_of_mem_thetaComponentsAt hJ.mem_thetaComponentsAt]
        exact ⟨h2, h1⟩
      exact h3
    rw [hJ.sectionCentralizer_eq] at hmem
    exact hmem
  have := Subgroup.card_le_of_le hle
  rw [H.card_inf, card_zpowers_of_pow_three ha3 ha1] at this
  omega

theorem false_of_pgl (h48 : Sec4.Item4_8) (H : Base A c L d K)
    (heq : A ⊓ Sec4.thetaQuotCentralizer K = Subgroup.zpowers c ⊔ Subgroup.zpowers d)
    {a : G} (haB : a ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers d) (ha1 : a ≠ 1)
    {J : Subgroup G} (hJ : Sec13Data G A a J) (haJ : a ∉ J)
    (hx : ∃ x ∈ A, Sec4.InducesTypeOn J x 3) : False := by
  have haA : a ∈ A := H.B_le haB
  have ha3 : a ^ 3 = 1 := H.data.isElemAbelian.2 a haA
  have hALJ := inf_le_of_mem_B h48 H heq haB ha1 hJ
  have hAeq : A = Subgroup.zpowers a ⊔ (A ⊓ L) := by
    have hle : Subgroup.zpowers a ⊔ (A ⊓ L) ≤ A :=
      sup_le (Subgroup.zpowers_le.mpr haA) inf_le_left
    have hcard := (isElemAbelian_zpowers_sup_of_card_nine ha3
      (fun h => haJ (hALJ h)) le_rfl H.card_inf
      (fun b hb => H.data.isElemAbelian.2 b hb.1) (fun b hb => H.data.commute haA hb.1)).2
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [H.data.card_eq, hcard])).symm
  obtain ⟨x, hxA, hxN, π, p, f, K', _, hK', hq', e, y', hy'H, hy'3, hact⟩ := hx
  have haC : a ∈ Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun b hb => H.data.commute hb.1 haA
  obtain ⟨k, y, hy, hxy⟩ := KFacts.KS14.exists_zpow_mul_of_mem_sup haC (by rw [← hAeq]; exact hxA)
  have hyJ : y ∈ J := hALJ hy
  have haNJ : a ∈ Subgroup.normalizer (J : Set G) := hJ.le_normalizer haA
  have hyN : y ∈ Subgroup.normalizer (J : Set G) := Subgroup.le_normalizer hyJ
  have hρa : Sec4.thetaQuotMulAut J (J.normalizerMonoidHom ⟨a, haNJ⟩) = 1 := by
    have hmem := Sec6.mem_thetaQuotCentralizer_of_mem_thetaComponentsAt hJ.mem_thetaComponentsAt
    obtain ⟨n, hn, hna⟩ := hmem
    have : n = ⟨a, haNJ⟩ := Subtype.ext hna
    rw [← this]
    exact MonoidHom.mem_ker.mp hn
  have hxe : (⟨x, hxN⟩ : Subgroup.normalizer (J : Set G)) = ⟨a, haNJ⟩ ^ k * ⟨y, hyN⟩ :=
    Subtype.ext (by simp [hxy])
  have hρx : ∀ z : J ⧸ aschbacherSolvableCore 3 J,
      Sec4.thetaQuotMulAut J (J.normalizerMonoidHom ⟨x, hxN⟩) z =
        (QuotientGroup.mk' (aschbacherSolvableCore 3 J) (⟨y, hyJ⟩ : J)) * z *
          (QuotientGroup.mk' (aschbacherSolvableCore 3 J) (⟨y, hyJ⟩ : J))⁻¹ := by
    intro z
    have h1 : Sec4.thetaQuotMulAut J (J.normalizerMonoidHom ⟨x, hxN⟩) =
        Sec4.thetaQuotMulAut J (J.normalizerMonoidHom ⟨y, hyN⟩) := by
      rw [hxe, map_mul, map_mul, map_zpow, map_zpow, hρa, one_zpow, one_mul]
    rw [h1]
    induction z using QuotientGroup.induction_on with
    | H z =>
      rw [Sec4.thetaQuotMulAut_mk]
      change ((QuotientGroup.mk' (aschbacherSolvableCore 3 J))
        (J.normalizerMonoidHom ⟨y, hyN⟩ z)) = _
      have : J.normalizerMonoidHom ⟨y, hyN⟩ z = ⟨y, hyJ⟩ * z * (⟨y, hyJ⟩ : J)⁻¹ :=
        Subtype.ext rfl
      rw [this]
      simp only [QuotientGroup.mk'_apply, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  have hq2 : 2 < p ^ f := by
    by_contra hq2
    have hp := hK'.prime
    have hf := hK'.one_le
    have h2 : p ^ f = 2 := by
      have : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) _)
      omega
    have hq := Sec6.isQuasisimple_of_mem_thetaComponentsAt hJ.mem_thetaComponentsAt
    cases π
    · have hsol := isSolvable_projImage_slPi_two hK' h2
      have : Group.IsSolvable (J ⧸ aschbacherSolvableCore 3 J) :=
        Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
      have : Group.IsPerfect (J ⧸ aschbacherSolvableCore 3 J) := hq.1
      have : IsSimpleGroup ((J ⧸ aschbacherSolvableCore 3 J) ⧸
          Subgroup.center (J ⧸ aschbacherSolvableCore 3 J)) := hq.2.1
      have : Nontrivial (J ⧸ aschbacherSolvableCore 3 J) :=
        (QuotientGroup.mk_surjective
          (s := Subgroup.center (J ⧸ aschbacherSolvableCore 3 J))).nontrivial
      exact Group.IsPerfect.not_isSolvable (J ⧸ aschbacherSolvableCore 3 J) inferInstance
    · change p ^ f % 3 = 1 at hq'
      omega
  set yb := QuotientGroup.mk' (aschbacherSolvableCore 3 J) (⟨y, hyJ⟩ : J) with hyb
  obtain ⟨s, hs, hse⟩ := Subgroup.mem_map.mp (e yb).2
  have hcomm : ∀ m ∈ Sec4.slPi π 3 (p ^ f) K',
      ProjGenLinGroup.mk (s⁻¹ * y') * ProjGenLinGroup.mk m =
        ProjGenLinGroup.mk m * ProjGenLinGroup.mk (s⁻¹ * y') := by
    intro m hm
    set z := e.symm ⟨ProjGenLinGroup.mk m, Subgroup.mem_map_of_mem _ hm⟩ with hz
    have hez : ((e z : projImage (Sec4.slPi π 3 (p ^ f) K')) : ProjGenLinGroup (Fin 3) K') =
        ProjGenLinGroup.mk m := by rw [hz, MulEquiv.apply_symm_apply]
    have h1 := hact z
    rw [hρx z, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      hez, ← hse] at h1
    rw [map_mul, map_inv]
    calc (ProjGenLinGroup.mk s)⁻¹ * ProjGenLinGroup.mk y' * ProjGenLinGroup.mk m =
        (ProjGenLinGroup.mk s)⁻¹ * (ProjGenLinGroup.mk y' * ProjGenLinGroup.mk m *
          (ProjGenLinGroup.mk y')⁻¹) * ProjGenLinGroup.mk y' := by group
      _ = (ProjGenLinGroup.mk s)⁻¹ * (ProjGenLinGroup.mk s * ProjGenLinGroup.mk m *
          (ProjGenLinGroup.mk s)⁻¹) * ProjGenLinGroup.mk y' := by rw [h1]
      _ = ProjGenLinGroup.mk m * ((ProjGenLinGroup.mk s)⁻¹ * ProjGenLinGroup.mk y') := by group
  have hsc := mem_statedScalars_of_commute_mk hK' hq' hq2 hcomm
  apply Sec4.not_inner_of_type3 hK' hq' hy'H hy'3
  refine ⟨s, hs, fun m _ => ?_⟩
  have h1 := Sec4.commute_of_mem_statedScalars hsc m
  calc y' * m * y'⁻¹ = s * ((s⁻¹ * y') * m) * (s⁻¹ * y')⁻¹ * s⁻¹ := by group
    _ = s * (m * (s⁻¹ * y')) * (s⁻¹ * y')⁻¹ * s⁻¹ := by rw [← h1]
    _ = s * m * s⁻¹ := by group

theorem false_of_mem_of_mem_B (h48 : Sec4.Item4_8) (H : Base A c L d K)
    (heq : A ⊓ Sec4.thetaQuotCentralizer K = Subgroup.zpowers c ⊔ Subgroup.zpowers d)
    {a : G} (haB : a ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers d) (had : a ∉ Subgroup.zpowers d)
    {J : Subgroup G} (hJ : Sec13Data G A a J) (haJ : a ∈ J)
    (h7 : Sec4.IsSLThreePiTwo (lBarA a J A) ∨
      Sec4.IsHeisCentral (lBarA a J A) (J ⧸ aschbacherSolvableCore 3 J)) : False := by
  have haA : a ∈ A := H.B_le haB
  have ha1 : a ≠ 1 := fun h => had (h ▸ one_mem _)
  have hALJ := inf_le_of_mem_B h48 H heq haB ha1 hJ
  have hdJ : d ∈ J := hALJ ⟨H.mem_A, H.d_mem_L⟩
  have hcJ : c ∈ J := by
    have hBJ : Subgroup.zpowers a ⊔ Subgroup.zpowers d ≤ J :=
      sup_le (Subgroup.zpowers_le.mpr haJ) (Subgroup.zpowers_le.mpr hdJ)
    rw [zpowers_sup_eq_of_mem H haA haB had] at hBJ
    exact hBJ (Subgroup.mem_sup_left (Subgroup.mem_zpowers c))
  have hAJ : A ≤ J := by
    rw [H.eq_sup]
    exact sup_le (Subgroup.zpowers_le.mpr hcJ) hALJ
  have hperf : Group.IsPerfect (lBarA a J A) := by
    have hsup : J ⊔ A = J := sup_eq_left.mpr hAJ
    have hJN : J ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G) :=
      hJ.le_centralizer.trans (centralizer_le_normalizer_zpowers a)
    have hJp : Group.IsPerfect J := Sec6.isPerfect_of_mem_thetaComponentsAt hJ.mem_thetaComponentsAt
    have : Group.IsPerfect (J.subgroupOf (Subgroup.normalizer (Subgroup.zpowers a : Set G))) :=
      Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hJN).symm.toMonoidHom)
        (MulEquiv.surjective _)
    unfold lBarA
    rw [hsup]
    exact Group.IsPerfect.map _
  rcases h7 with hSL | hHeis
  · exact ON134.not_isPerfect_of_isSLThreePiTwo hSL hperf
  · exact ON134.not_isPerfect_of_isHeisCentral hHeis hperf

end CFSG.RankThree.PartTwo.Sec13.Item134Arg128Fail
