module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefsB
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem s16c6_aux_mem_centralizer_of_comm {w h : G} (hcw : h * w = w * h) :
    h ∈ centralizer ({w} : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  exact hcw.symm

theorem s16c6_centralizes_v0 (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) {K : Subgroup G} (hKM : K ≤ D.M) (hK : ⁅K, K⁆ = K) :
    K ≤ centralizer (V₀ : Set G) := by
  classical
  have hpair := hS.setting.hyp16.hyp125.pairFacts
  have hsmall : Nat.card V₀ ≤ 4 := by
    have h2 : IsPGroup 2 ↥V₀ := CFSG.Open.IsElemAbelian.isPGroup hpair.elemAbelian₀
    rw [card_eq_two_pow_mSub h2]
    calc 2 ^ mSub V₀ ≤ 2 ^ 2 :=
          Nat.pow_le_pow_right (by norm_num) hS.setting.hyp16.small
      _ = 4 := by norm_num
  let φ : K →* MulAut ↥V₀ :=
    (Subgroup.normalizerMonoidHom V₀).comp
      (Subgroup.inclusion (hKM.trans hpair.le_normalizer₀))
  haveI : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr hK
  haveI : Group.IsPerfect ↥(φ.range) := Group.IsPerfect.range φ
  haveI hsol : Group.IsSolvable (MulAut ↥V₀) := by
    haveI : Group.IsSolvable (Equiv.Perm ↥V₀) := Equiv.Perm.isSolvable hsmall
    exact Group.isSolvable_of_isSolvable_injective (f := MulAut.toPerm (M := ↥V₀))
      (fun _ _ hab => MulEquiv.toEquiv_injective hab)
  have hbot : φ.range = ⊥ := by
    by_contra hne
    have hlt := Group.IsSolvable.commutator_lt_of_ne_bot (G := MulAut ↥V₀) hne
    rw [Subgroup.commutator_eq_self (H := φ.range)] at hlt
    exact lt_irrefl _ hlt
  have hker : φ.ker = (centralizer (V₀ : Set G)).subgroupOf K := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show (Subgroup.normalizerMonoidHom V₀)
        (Subgroup.inclusion (hKM.trans hpair.le_normalizer₀) x) = 1 ↔
      (x : G) ∈ centralizer (V₀ : Set G)
    rw [← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker V₀,
      Subgroup.mem_subgroupOf, Subgroup.coe_inclusion]
  have hKle : (⊤ : Subgroup ↥K) ≤ φ.ker :=
    (Subgroup.map_eq_bot_iff (⊤ : Subgroup ↥K) (f := φ)).1
      (by rw [← MonoidHom.range_eq_map]; exact hbot)
  intro k hk
  have hmem : (⟨k, hk⟩ : ↥K) ∈ φ.ker := hKle (Subgroup.mem_top _)
  rw [hker, Subgroup.mem_subgroupOf] at hmem
  simpa using hmem

theorem s16c6_le_centralizer_of_fix (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) {K H : Subgroup G} (hKM : K ≤ D.M) (hK : ⁅K, K⁆ = K)
    (hHK : H ≤ K) {w : G} (hw : w ∈ V) (hfix : ∀ h ∈ H, h * w * h⁻¹ * w⁻¹ ∈ V₀)
    (hH : ⁅H, H⁆ = H ∨ Odd (Nat.card H)) : H ≤ centralizer ({w} : Set G) := by
  classical
  have hpair := hS.setting.hyp16.hyp125.pairFacts
  haveI hcommV : IsMulCommutative ↥V₀ := hpair.elemAbelian₀.1
  have hcentK : K ≤ centralizer (V₀ : Set G) := s16c6_centralizes_v0 D hS hKM hK
  have hHcent : H ≤ centralizer (V₀ : Set G) := hHK.trans hcentK
  let θf : H → ↥V₀ := fun h => ⟨(h : G) * w * (h : G)⁻¹ * w⁻¹, hfix (h : G) h.2⟩
  let θ : H →* ↥V₀ :=
    { toFun := θf
      map_one' := by
        apply Subtype.ext
        show (1 : G) * w * (1 : G)⁻¹ * w⁻¹ = (1 : G)
        simp
      map_mul' := by
        intro a b
        have hθa : ((a : G) * w * (a : G)⁻¹ * w⁻¹) * w =
            (a : G) * w * (a : G)⁻¹ := by group
        have hθb : ((b : G) * w * (b : G)⁻¹ * w⁻¹) * w =
            (b : G) * w * (b : G)⁻¹ := by group
        have hcomm_ab : (a : G) * ((b : G) * w * (b : G)⁻¹ * w⁻¹) =
            ((b : G) * w * (b : G)⁻¹ * w⁻¹) * (a : G) :=
          ((Subgroup.mem_centralizer_iff.mp (hHcent a.2)) _
            (hfix (b : G) b.2)).symm
        have hcomm_θ : ((a : G) * w * (a : G)⁻¹ * w⁻¹) *
              ((b : G) * w * (b : G)⁻¹ * w⁻¹) =
            ((b : G) * w * (b : G)⁻¹ * w⁻¹) *
              ((a : G) * w * (a : G)⁻¹ * w⁻¹) :=
          CFSG.Open.IsElemAbelian.comm hpair.elemAbelian₀
            (hfix (a : G) a.2) (hfix (b : G) b.2)
        apply Subtype.ext
        show (a : G) * (b : G) * w * ((a : G) * (b : G))⁻¹ * w⁻¹ =
          ((a : G) * w * (a : G)⁻¹ * w⁻¹) *
            ((b : G) * w * (b : G)⁻¹ * w⁻¹)
        calc (a : G) * (b : G) * w * ((a : G) * (b : G))⁻¹ * w⁻¹
            = (a : G) * ((b : G) * w * (b : G)⁻¹) * (a : G)⁻¹ * w⁻¹ := by group
          _ = (a : G) * (((b : G) * w * (b : G)⁻¹ * w⁻¹) * w) *
                (a : G)⁻¹ * w⁻¹ := by
                conv_lhs => rw [← hθb]
          _ = (a : G) * ((b : G) * w * (b : G)⁻¹ * w⁻¹) * w *
                (a : G)⁻¹ * w⁻¹ := by group
          _ = (a : G) * ((b : G) * w * (b : G)⁻¹ * w⁻¹) * (a : G)⁻¹ *
                ((a : G) * w * (a : G)⁻¹) * w⁻¹ := by group
          _ = ((b : G) * w * (b : G)⁻¹ * w⁻¹) *
                (((a : G) * w * (a : G)⁻¹ * w⁻¹) * w) * w⁻¹ := by
                conv_lhs => rw [hcomm_ab, ← hθa]
                group
          _ = ((b : G) * w * (b : G)⁻¹ * w⁻¹) *
                ((a : G) * w * (a : G)⁻¹ * w⁻¹) := by group
          _ = ((a : G) * w * (a : G)⁻¹ * w⁻¹) *
                ((b : G) * w * (b : G)⁻¹ * w⁻¹) := hcomm_θ.symm }
  intro h hh
  have hθ : θ ⟨h, hh⟩ = 1 := by
    rcases hH with hHperf | hHodd
    · haveI : Group.IsPerfect ↥H := Subgroup.isPerfect_iff.mpr hHperf
      haveI : Group.IsPerfect ↥(θ.range) := Group.IsPerfect.range θ
      haveI : Subsingleton ↥(θ.range) := inferInstance
      have hbot : θ.range = ⊥ := by
        rw [Subgroup.eq_bot_iff_forall θ.range]
        intro x hx
        simpa using Subsingleton.elim (⟨x, hx⟩ : ↥(θ.range)) 1
      have hx : θ ⟨h, hh⟩ ∈ θ.range := MonoidHom.mem_range.mpr ⟨⟨h, hh⟩, rfl⟩
      rw [hbot] at hx
      exact Subgroup.mem_bot.mp hx
    · have hsq : (θ ⟨h, hh⟩) ^ 2 = 1 := by
        rw [sq]
        apply Subtype.ext
        simpa using hpair.elemAbelian₀.mul_self_eq_one (θ ⟨h, hh⟩).2
      have hdvd2 : orderOf (θ ⟨h, hh⟩) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hsq
      have hdvdH : orderOf (θ ⟨h, hh⟩) ∣ Nat.card H :=
        (orderOf_map_dvd θ ⟨h, hh⟩).trans (orderOf_dvd_natCard _)
      have horder : orderOf (θ ⟨h, hh⟩) = 1 := by
        by_contra hne
        have h2 : orderOf (θ ⟨h, hh⟩) = 2 := by
          have hle : orderOf (θ ⟨h, hh⟩) ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd2
          have hpos : 0 < orderOf (θ ⟨h, hh⟩) := orderOf_pos _
          omega
        exact hHodd.not_two_dvd_nat (h2 ▸ hdvdH)
      rwa [orderOf_eq_one_iff] at horder
  have hcw : (h : G) * w = w * (h : G) := by
    have hval : (θ ⟨h, hh⟩ : G) = (h : G) * w * (h : G)⁻¹ * w⁻¹ := rfl
    have h1 : (h : G) * w * (h : G)⁻¹ * w⁻¹ = 1 := by
      rw [← hval, hθ]
      rfl
    rw [← commutatorElement_eq_one_iff_mul_comm, commutatorElement_def]
    exact h1
  exact s16c6_aux_mem_centralizer_of_comm hcw

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
