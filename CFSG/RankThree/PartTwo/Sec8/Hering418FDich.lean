module

public import CFSG.RankThree.PartTwo.Sec19.SimsC198G2
public import CFSG.RankThree.PartTwo.Sec6.Item65UsedTools
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.RankThree.PartTwo.Sec8.Hering418ROuter
public import CFSG.RankThree.PartTwo.Sec8.Hering418RSix

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering418

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF418
open CFSG.Open (IsElemAbelian)

section Dichotomy


theorem kF418ModelOn_of_dichotomy {P : ∀ (X : Type) [Group X], Prop}
    (hD : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), L ∈ thetaComponents 3 G →
      P (L ⧸ aschbacherSolvableCore 3 L) →
      ∃ N : Subgroup (MulAut (L ⧸ aschbacherSolvableCore 3 L)), innBar L ≤ N ∧
        (∀ F : Subgroup (MulAut (L ⧸ aschbacherSolvableCore 3 L)), IsElemAbelian 3 F → F ≤ N →
          Nat.card F ≤ 9) ∧
        ∀ (x : G) (hx : x ∈ Subgroup.normalizer (L : Set G)), x ^ 3 = 1 →
          (rho L ⟨x, hx⟩ ∈ N ∧ ¬ (KFacts.InducesStdKind L x .field ∨
              KFacts.InducesStdKind L x .graphField)) ∨
            (rho L ⟨x, hx⟩ ∉ N ∧ (KFacts.InducesStdKind L x .field ∨
              KFacts.InducesStdKind L x .graphField)))
    (hB : KF418OuterOn P) : KF418ModelOn P := by
  intro G _ _ L hL hl a b ha3 hb3 hab hb1 habz haN hbN hbC haC K hK n hn htype hKa
  obtain ⟨N, hinn, hbound, hdich⟩ := hD G L hL hl
  have c := Cfg.of_model hK ha3 hb3 hab haN hbN hbC haC hKa
  have hKq := Sec6.isQuasisimple_of_mem_thetaComponentsIn hK
  rcases hdich b hbN hb3 with ⟨hbm, hbk⟩ | ⟨-, hbk⟩
  · refine ⟨?_, hbk⟩
    rcases hdich a haN ha3 with ⟨ham, -⟩ | ⟨-, hak⟩
    · exact (c.false_of_bound hn hKq htype hKa hinn ham hbm hbound).elim
    · exact hak
  · exact (hB G L hL hl a b ha3 hb3 hab hb1 habz haN hbN hbC haC K hK n hn htype hKa hbk).elim

end Dichotomy

section Quot

variable {G : Type} [Group G] [Finite G] {L K : Subgroup G} {a b : G}

theorem noThetaNormal_of_isQuasisimple {Q : Type*} [Group Q] [Finite Q] (hq : IsQuasisimple Q)
    (hZ : IsPGroup 3 (Subgroup.center Q)) : NoThetaNormal Q := by
  intro N hN hNs hN3
  rcases Sec6.subnormal_le_center_or_eq_top_of_isQuasisimple hq
      (Subgroup.Normal.isSubnormal hN) with hle | htop
  · have hNZ : IsPGroup 3 (N.subgroupOf (Subgroup.center Q)) := hZ.to_subgroup _
    have hcard : Nat.card (N.subgroupOf (Subgroup.center Q)) = 1 := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hNZ
      have hk0 : k = 0 := by
        by_contra hk0
        apply hN3
        have : Nat.card N = Nat.card (N.subgroupOf (Subgroup.center Q)) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv.symm
        rw [this, hk]
        exact dvd_pow_self 3 hk0
      rw [hk, hk0, pow_zero]
    have h1 : N.subgroupOf (Subgroup.center Q) = ⊥ := Subgroup.eq_bot_of_card_eq _ hcard
    rw [← Subgroup.map_subgroupOf_eq_of_le hle, h1, Subgroup.map_bot]
  · exfalso
    subst htop
    have hs : Group.IsSolvable Q :=
      Group.isSolvable_of_isSolvable_injective (f := (Subgroup.topEquiv (G := Q)).symm.toMonoidHom)
        (Subgroup.topEquiv (G := Q)).symm.injective
    obtain ⟨-, hsimple, x, y, hxy⟩ := hq
    haveI := hsimple
    exact hxy ((IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance) x y)

theorem imageModTheta_isSubnormal_barCentralizer (hbN : b ∈ Subgroup.normalizer (L : Set G))
    (hb3 : b ^ 3 = 1) (hK : K ∈ thetaComponentsIn (L ⊓ Subgroup.centralizer {b})) :
    ((Sec8.imageModTheta L K).subgroupOf
      (Sec8.barCentralizer (Subgroup.zpowers b) L)).IsSubnormal := by
  set M : Subgroup G := L ⊓ Subgroup.centralizer {b} with hM
  set q := QuotientGroup.mk' (aschbacherSolvableCore 3 L) with hq
  set g : ↥M →* L ⧸ aschbacherSolvableCore 3 L := q.comp (Subgroup.inclusion inf_le_left) with hg
  have hrange : g.range = Sec8.barCentralizer (Subgroup.zpowers b) L := by
    rw [← KFacts.imageModTheta_centralizer_eq hbN ⟨1, by rw [pow_one]; exact hb3⟩,
      Sec8.imageModTheta, hg, MonoidHom.range_comp, Subgroup.inclusion_range]
  obtain ⟨hKM, hKp⟩ := mem_thetaComponentsIn_iff.mp hK
  have hsub : (K.subgroupOf M).IsSubnormal := hKp.2.1
  have hmap : ((K.subgroupOf M).map g.rangeRestrict).IsSubnormal :=
    hsub.map g.rangeRestrict_surjective
  have himg : ((K.subgroupOf M).map g.rangeRestrict).map g.range.subtype =
      Sec8.imageModTheta L K := by
    rw [Subgroup.map_map, Sec8.imageModTheta]
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨Subgroup.inclusion inf_le_left x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hKM hx⟩, hx, rfl⟩
  have h2 : (Sec8.imageModTheta L K).subgroupOf g.range =
      (K.subgroupOf M).map g.rangeRestrict := by
    rw [← himg]
    exact Subgroup.comap_map_eq_self_of_injective g.range.subtype_injective _
  rw [← hrange, h2]
  exact hmap

theorem isPerfect_imageModTheta (hK : K ∈ thetaComponentsIn (L ⊓ Subgroup.centralizer {b})) :
    Group.IsPerfect ↥(Sec8.imageModTheta L K) := by
  obtain ⟨hKM, hKp⟩ := mem_thetaComponentsIn_iff.mp hK
  have hKL : K ≤ L := hKM.trans inf_le_left
  haveI hP := hKp.1
  haveI : Group.IsPerfect K :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hKM).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hKM).surjective
  haveI : Group.IsPerfect ↥(Item87Res2Proof.toQuot hKL).range :=
    Group.IsPerfect.ofSurjective (f := (Item87Res2Proof.toQuot hKL).rangeRestrict)
      (MonoidHom.rangeRestrict_surjective _)
  rw [← Item87Res2Proof.range_toQuot hKL]
  exact this

theorem imageModTheta_eq_barCentralizer_of_isQuasisimple
    (hbN : b ∈ Subgroup.normalizer (L : Set G)) (hb3 : b ^ 3 = 1)
    (hK : K ∈ thetaComponentsIn (L ⊓ Subgroup.centralizer {b}))
    (hq : IsQuasisimple ↥(Sec8.barCentralizer (Subgroup.zpowers b) L)) :
    Sec8.imageModTheta L K = Sec8.barCentralizer (Subgroup.zpowers b) L := by
  have hKq := Sec6.isQuasisimple_of_mem_thetaComponentsIn hK
  have hKM := le_of_mem_thetaComponentsIn hK
  exact Sec19.SimsC198.G2.eq_of_isPerfect_of_isSubnormal_of_isQuasisimple hq
    (imageModTheta_le_barCentralizer_of_le hbN hb3 (hKM.trans inf_le_left)
      (hKM.trans inf_le_right)) (isPerfect_imageModTheta hK)
    (imageModTheta_isSubnormal_barCentralizer hbN hb3 hK)
    (imageModTheta_ne_bot (hKM.trans inf_le_left) hKq)

theorem ker_toQuot_eq_of_noThetaNormal (hKL : K ≤ L)
    (hN : NoThetaNormal ↥(Item87Res2Proof.toQuot hKL).range) :
    (Item87Res2Proof.toQuot hKL).ker = aschbacherSolvableCore 3 K := by
  obtain ⟨hθs, -, hθ3, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := K) Nat.prime_three
  refine le_antisymm (Item87Res2Proof.ker_toQuot_le hKL) ?_
  set ρ := (Item87Res2Proof.toQuot hKL).rangeRestrict with hρ
  have hρs : Function.Surjective ρ := MonoidHom.rangeRestrict_surjective _
  set M := (aschbacherSolvableCore 3 K).map ρ with hM
  have hMn : M.Normal := by
    have : (aschbacherSolvableCore 3 K).Normal := inferInstance
    exact this.map ρ hρs
  have hMs : Group.IsSolvable M := by
    have := hθs
    exact Group.isSolvable_of_surjective (ρ.subgroupMap_surjective _)
  have hM3 : ¬ 3 ∣ Nat.card M := fun h3 => hθ3 (h3.trans (Subgroup.card_map_dvd _ _))
  have hM1 : M = ⊥ := hN M hMn hMs hM3
  intro k hk
  rw [MonoidHom.mem_ker]
  have : ρ k ∈ M := Subgroup.mem_map_of_mem ρ hk
  rw [hM1, Subgroup.mem_bot] at this
  exact congrArg Subtype.val this

theorem Cfg.exists_mulEquiv_barCentralizer_of_isQuasisimple (c : Cfg L K a b)
    (hK : K ∈ thetaComponentsIn (L ⊓ Subgroup.centralizer {b}))
    (hq : IsQuasisimple ↥(Sec8.barCentralizer (Subgroup.zpowers b) L))
    (hZ : IsPGroup 3 (Subgroup.center ↥(Sec8.barCentralizer (Subgroup.zpowers b) L))) :
    ∃ Ψ : (K ⧸ aschbacherSolvableCore 3 K) ≃*
        ↥(Sec8.barCentralizer (Subgroup.zpowers b) L),
      ∀ y : K ⧸ aschbacherSolvableCore 3 K,
        ((Ψ (Sec4.thetaQuotMulAut K (Sec4.compAction K ⟨a, c.haK⟩) y) :
          ↥(Sec8.barCentralizer (Subgroup.zpowers b) L)) : L ⧸ aschbacherSolvableCore 3 L) =
          c.alpha (Ψ y : L ⧸ aschbacherSolvableCore 3 L) := by
  have hCeq := imageModTheta_eq_barCentralizer_of_isQuasisimple c.hbL c.hb3 hK hq
  have hrange : (Item87Res2Proof.toQuot c.hKL).range =
      Sec8.barCentralizer (Subgroup.zpowers b) L :=
    (Item87Res2Proof.range_toQuot c.hKL).trans hCeq
  have hNT : NoThetaNormal ↥(Item87Res2Proof.toQuot c.hKL).range := by
    rw [hrange]
    exact noThetaNormal_of_isQuasisimple hq hZ
  have hker := ker_toQuot_eq_of_noThetaNormal c.hKL hNT
  let Ψ0 : (K ⧸ aschbacherSolvableCore 3 K) ≃* ↥(Item87Res2Proof.toQuot c.hKL).range :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivRange (Item87Res2Proof.toQuot c.hKL))
  refine ⟨Ψ0.trans (MulEquiv.subgroupCongr hrange), fun y => ?_⟩
  induction y using QuotientGroup.induction_on with
  | H k =>
    rw [Sec4.thetaQuotMulAut_mk]
    change Item87Res2Proof.toQuot c.hKL _ = _
    rfl
end Quot

end CFSG.RankThree.PartTwo.Sec8.Hering418
