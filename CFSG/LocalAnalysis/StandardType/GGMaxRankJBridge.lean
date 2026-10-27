module

public import CFSG.LocalAnalysis.StandardType.GGMaxRankJReflection
import CFSG.LocalAnalysis.StandardType.GGMaxRankJModel
import CFSG.LocalAnalysis.StandardType.GGMaxRankJWitness
import CFSG.LocalAnalysis.StandardType.GGMaxRankJCard
import CFSG.LocalAnalysis.StandardType.GGMaxRankJAutSplit
import CFSG.LocalAnalysis.StandardType.GGMaxRankJTransport
import CFSG.LocalAnalysis.StandardType.GGSpJoinBstarSplit
import CFSG.LocalAnalysis.StandardType.GGTPNDefs
import CFSG.GroupTheory.IsComponentOfMap
import CFSG.LocalAnalysis.GLTheoremA.CatB.CfgILift
import CFSG.LocalAnalysis.StandardType.GGF4NbrAutReflKGReduce

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma pjb_isComponentOf_subgroupOf {G : Type} [Group G] {L H K : Subgroup G}
    (hHL : H ≤ L) (h : CFSG.Open.IsComponentOf H K) :
    CFSG.Open.IsComponentOf (H.subgroupOf L) (K.subgroupOf L) :=
  ⟨Subgroup.comap_mono h.1, h.2.1.comap L.subtype,
    CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hHL) h.2.2⟩

private lemma pjb_isElemAbelian_subgroupOf {G : Type} [Group G] {p : ℕ} {H K : Subgroup G}
    (hHK : H ≤ K) (h : IsElemAbelian p H) : IsElemAbelian p (H.subgroupOf K) := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
  · apply Subtype.ext
    apply Subtype.ext
    exact h.comm x.2 y.2
  · intro x hx
    exact Subtype.ext (h.2 (x : G) hx)

private theorem pjb_ggMaxRankJReflection_side
    (hLab : GGLabelRigidInput) (hCore : GGMaxRankE8Core)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs X J : Subgroup G}
    (hBstar : GGBstar p B Bs) (hinn : GGInnerDiagOn Bs X) (hJX : J ≤ X)
    (hrow : GGResRowAt ggRowMaxRank p J X) (hD : GGResE8SeparatedDatum p Bs X)
    (hw : ∃ z ∈ Bs, z ∉ Subgroup.centralizer (X : Set G) ∧
      IsComponentOf J (X ⊓ Subgroup.centralizer ({z} : Set G))) :
    ∃ eJ : (CoxeterMatrix.A 8).Group ≃* ↥(ggAutomizer J Bs),
      ∀ i, GGIsReflection p
        ((eJ ((CoxeterMatrix.A 8).simple i) : ↥(ggAutomizer J Bs)) : MulAut ↥Bs) := by
  obtain ⟨labJ, labX, hΛJ, hΛX, hJlab, hXlab, hrowlab⟩ := hrow
  have hXeq : labX = ⟨.E8, 0, labJ.n⟩ := by
    rcases hrowlab with ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ <;> exact h
  have hrow_j : (labJ = ⟨.A, 8, labJ.n⟩ ∧ p = 3 ∧ 3 ∣ 2 ^ labJ.n - 1) ∨
      (labJ = ⟨.twA, 8, labJ.n⟩ ∧ p = 3 ∧ 3 ∣ 2 ^ labJ.n + 1) := by
    rcases hrowlab with ⟨h1, h2, h3, _⟩ | ⟨h1, h2, h3, _⟩
    · exact Or.inl ⟨h1, h2, h3⟩
    · exact Or.inr ⟨h1, h2, h3⟩
  have hp3 : p = 3 := by rcases hrow_j with ⟨_, h, _⟩ | ⟨_, h, _⟩ <;> exact h
  have hΛE8 : LargeEvenInLambda2 ⟨.E8, 0, labJ.n⟩ := hXeq ▸ hΛX
  have hXE8 : GGHasLabel ⟨.E8, 0, labJ.n⟩ (↥X ⧸ Subgroup.center ↥X) := hXeq ▸ hXlab
  obtain ⟨Kf, hKf_field, hKf_fin, hKf_char, hKf_card, θ, hZL, hnorm, hinnerL⟩ :=
    ggMaxRank_model hLab hΛE8 hinn hXE8
  letI : Field Kf := hKf_field
  letI : Finite Kf := hKf_fin
  letI : CharP Kf 2 := hKf_char
  have hsplit := ggBstar_split_of_inner hBstar hZL hnorm hinnerL
  have hcard_split := card_ggBstar_split hBstar hZL hnorm hinnerL
  have hcard_E8 := ggResE8Separated_card (Bs := Bs) (X := X) hD
  have hB0card : Nat.card ↥(Bs ⊓ X) = p ^ 8 := by
    have h := hcard_split.symm.trans hcard_E8
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  have hdisj : Bs ⊓ X ⊓ Subgroup.centralizer (X : Set G) = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    have hgX : g ∈ X := hg.1.2
    have hgC : g ∈ Subgroup.centralizer (X : Set G) := hg.2
    have hgZ : (⟨g, hgX⟩ : ↥X) ∈ Subgroup.center ↥X := by
      rw [Subgroup.mem_center_iff]
      intro l
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hgC (l : G) l.2)
    rw [hZL] at hgZ
    exact Subgroup.mem_bot.mpr (Subtype.ext_iff.mp (Subgroup.mem_bot.mp hgZ))
  obtain ⟨z, hzBs, hzC, hzcomp⟩ := hw
  obtain ⟨a, ha, c, hc, hzac⟩ := hsplit z hzBs
  have haX : a ∈ X := ha.2
  have hcCX : c ∈ Subgroup.centralizer (X : Set G) := hc.2
  have ha1 : a ≠ 1 := by
    intro h
    exact hzC (by rw [hzac, h, one_mul]; exact hcCX)
  have hKz : X ⊓ Subgroup.centralizer ({z} : Set G) =
      X ⊓ Subgroup.centralizer ({a} : Set G) := by
    apply le_antisymm
    · intro g hg
      rcases hg with ⟨hgX, hgC⟩
      refine ⟨hgX, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      have hzg : z * g = g * z := Subgroup.mem_centralizer_iff.mp hgC z (Set.mem_singleton z)
      have hgc : g * c = c * g := Subgroup.mem_centralizer_iff.mp hcCX g hgX
      have h1 : a * g * c = g * a * c := by
        calc a * g * c = a * (g * c) := by group
          _ = a * (c * g) := by rw [hgc]
          _ = a * c * g := by group
          _ = z * g := by rw [← hzac]
          _ = g * z := hzg
          _ = g * (a * c) := by rw [hzac]
          _ = g * a * c := by group
      exact mul_right_cancel h1
    · intro g hg
      rcases hg with ⟨hgX, hgC⟩
      refine ⟨hgX, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      have hag : a * g = g * a := Subgroup.mem_centralizer_iff.mp hgC a (Set.mem_singleton a)
      have hgc : g * c = c * g := Subgroup.mem_centralizer_iff.mp hcCX g hgX
      calc z * g = (a * c) * g := by rw [hzac]
        _ = a * (c * g) := by group
        _ = a * (g * c) := by rw [hgc]
        _ = (a * g) * c := by group
        _ = (g * a) * c := by rw [hag]
        _ = g * (a * c) := by group
        _ = g * z := by rw [hzac]
  let s : adjointGroup .E8 Kf := θ ⟨a, haX⟩
  let A_E : Subgroup (adjointGroup .E8 Kf) := ((Bs ⊓ X).subgroupOf X).map θ.toMonoidHom
  let J_E : Subgroup (adjointGroup .E8 Kf) := (J.subgroupOf X).map θ.toMonoidHom
  have hcomp_sub : CFSG.Open.IsComponentOf (J.subgroupOf X)
      ((X ⊓ Subgroup.centralizer ({z} : Set G)).subgroupOf X) :=
    pjb_isComponentOf_subgroupOf hJX (CFSG.Assembly.isComponentOf_iff_open.mp hzcomp)
  have hcomp_sub_a : CFSG.Open.IsComponentOf (J.subgroupOf X)
      ((X ⊓ Subgroup.centralizer ({a} : Set G)).subgroupOf X) := hKz ▸ hcomp_sub
  have hcomp_map : CFSG.Open.IsComponentOf ((J.subgroupOf X).map θ.toMonoidHom)
      (((X ⊓ Subgroup.centralizer ({a} : Set G)).subgroupOf X).map θ.toMonoidHom) :=
    CFSG.isComponentOf_map_mulEquiv θ hcomp_sub_a
  have hcentralizer_eq :
      (((X ⊓ Subgroup.centralizer ({a} : Set G)).subgroupOf X).map θ.toMonoidHom) =
        Subgroup.centralizer ({s} : Set (adjointGroup .E8 Kf)) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      rw [hw]
      have hx' : (x : G) ∈ X ⊓ Subgroup.centralizer ({a} : Set G) := hx
      have hxa : a * (x : G) = (x : G) * a :=
        Subgroup.mem_centralizer_iff.mp hx'.2 a (Set.mem_singleton a)
      have hcomm_X : (⟨a, haX⟩ : ↥X) * x = x * ⟨a, haX⟩ := Subtype.ext hxa
      calc s * θ x = θ ⟨a, haX⟩ * θ x := rfl
        _ = θ (⟨a, haX⟩ * x) := by rw [← map_mul]
        _ = θ (x * ⟨a, haX⟩) := by rw [hcomm_X]
        _ = θ x * θ ⟨a, haX⟩ := by rw [map_mul]
        _ = θ x * s := rfl
    · intro hy
      obtain ⟨x, rfl⟩ := θ.surjective y
      have hcomm : s * θ x = θ x * s :=
        Subgroup.mem_centralizer_iff.mp hy s (Set.mem_singleton s)
      have h1 : ⟨a, haX⟩ * x = x * ⟨a, haX⟩ :=
        θ.injective (by rw [map_mul, map_mul]; exact hcomm)
      have h2 : a * (x : G) = (x : G) * a := congrArg Subtype.val h1
      refine ⟨x, ?_, rfl⟩
      have hxX : (x : G) ∈ X := x.2
      have hxC : (x : G) ∈ Subgroup.centralizer ({a} : Set G) := by
        refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
        rw [Set.mem_singleton_iff] at hw
        rw [hw]
        exact h2
      exact Subgroup.mem_inf.mpr ⟨hxX, hxC⟩
  have hcomp_map' : CFSG.Open.IsComponentOf ((J.subgroupOf X).map θ.toMonoidHom)
      (Subgroup.centralizer ({s} : Set (adjointGroup .E8 Kf))) := by
    rw [hcentralizer_eq] at hcomp_map
    exact hcomp_map
  have hcomp_core : IsComponentOf J_E
      (Subgroup.centralizer ({s} : Set (adjointGroup .E8 Kf))) :=
    CFSG.Assembly.isComponentOf_iff_open.mpr hcomp_map'
  have hJE_lab : GGHasLabel labJ (↥J_E ⧸ Subgroup.center ↥J_E) :=
    ggHasLabel_quotCenter_of_mulEquiv
      ((Subgroup.subgroupOfEquivOfLe hJX).symm.trans
        (Subgroup.equivMapOfInjective (J.subgroupOf X) θ.toMonoidHom θ.injective)) hJlab
  have hclause : (GGHasLabel ⟨.A, 8, labJ.n⟩ (↥J_E ⧸ Subgroup.center ↥J_E) ∧
        3 ∣ 2 ^ labJ.n - 1) ∨
      (GGHasLabel ⟨.twA, 8, labJ.n⟩ (↥J_E ⧸ Subgroup.center ↥J_E) ∧
        3 ∣ 2 ^ labJ.n + 1) := by
    rcases hrow_j with ⟨hJeq, _, hdvd⟩ | ⟨hJeq, _, hdvd⟩
    · exact Or.inl ⟨by rw [← hJeq]; exact hJE_lab, hdvd⟩
    · exact Or.inr ⟨by rw [← hJeq]; exact hJE_lab, hdvd⟩
  have hA0 : IsElemAbelian p (Bs ⊓ X) := hBstar.2.1.mono inf_le_left
  have hA0sub : IsElemAbelian p ((Bs ⊓ X).subgroupOf X) :=
    pjb_isElemAbelian_subgroupOf inf_le_right hA0
  have hAe_elem_p : IsElemAbelian p A_E :=
    CFSG.LocalAnalysis.GLTheoremA.S8.CfgI.isElemAbelian_map_of_injective θ.injective hA0sub
  have hAe_elem : IsElemAbelian 3 A_E := by rw [← hp3]; exact hAe_elem_p
  have hAe_card : Nat.card A_E = 3 ^ 8 := by
    have h1 : Nat.card A_E = Nat.card ↥(Bs ⊓ X) := by
      show Nat.card ↥(((Bs ⊓ X).subgroupOf X).map θ.toMonoidHom) = Nat.card ↥(Bs ⊓ X)
      rw [Subgroup.card_map_of_injective θ.injective]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
    rw [h1, hB0card, hp3]
  have hs_mem : s ∈ A_E := by
    show θ ⟨a, haX⟩ ∈ ((Bs ⊓ X).subgroupOf X).map θ.toMonoidHom
    exact ⟨⟨a, haX⟩, ha, rfl⟩
  have hs_ne : s ≠ 1 := by
    intro h
    have h1 : (⟨a, haX⟩ : ↥X) = 1 := θ.injective (h.trans (map_one θ).symm)
    exact ha1 (by simpa using congrArg Subtype.val h1)
  obtain ⟨eJ_E, heJ_E⟩ :=
    hCore Kf labJ.n hKf_card A_E J_E s hAe_elem (by rw [hAe_card]) hs_mem hs_ne hcomp_core hclause
  obtain ⟨eA, e, he⟩ :=
    ggMaxRank_automizerTransport (X := X) (J := J) (A := Bs ⊓ X) hJX inf_le_right θ
  obtain ⟨e', he'⟩ :=
    ggMaxRank_automizerSplit (X := X) (J := J) (Bs := Bs) hJX hsplit hdisj
  refine ⟨(eJ_E.trans e.symm).trans e'.symm, ?_⟩
  intro i
  have hrefl_E : GGIsReflection p
      ((eJ_E ((CoxeterMatrix.A 8).simple i) : ↥(ggAutomizer J_E A_E)) : MulAut ↥A_E) := by
    rw [hp3]
    exact heJ_E i
  have hcongr : GGIsReflection p
      (MulAut.congr eA ((e.symm (eJ_E ((CoxeterMatrix.A 8).simple i)) :
        ↥(ggAutomizer J (Bs ⊓ X))) : MulAut ↥(Bs ⊓ X))) := by
    rw [← he (e.symm (eJ_E ((CoxeterMatrix.A 8).simple i)))]
    simpa only [MulEquiv.apply_symm_apply] using hrefl_E
  have hrefl_A : GGIsReflection p
      ((e.symm (eJ_E ((CoxeterMatrix.A 8).simple i)) : ↥(ggAutomizer J (Bs ⊓ X))) :
        MulAut ↥(Bs ⊓ X)) :=
    (F4AutRefl.ggIsReflection_congr_iff eA _).mp hcongr
  have hrefl_B : GGIsReflection p
      ((e'.symm (e.symm (eJ_E ((CoxeterMatrix.A 8).simple i))) : ↥(ggAutomizer J Bs)) :
        MulAut ↥Bs) :=
    (he' (e'.symm (e.symm (eJ_E ((CoxeterMatrix.A 8).simple i))))).mpr
      (by simpa using hrefl_A)
  simpa only [MulEquiv.trans_apply] using hrefl_B

theorem ggMaxRankJReflectionInputTyped_of_core
    (hLab : GGLabelRigidInput) (hCore : GGMaxRankE8Core) :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
      (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime],
      GGResRowAt ggRowMaxRank p J L → GGResE8SeparatedDatum p Bs L →
        ∃ eJ : (CoxeterMatrix.A 8).Group ≃* ↥(ggAutomizer J Bs),
          ∀ i, GGIsReflection p ((eJ ((CoxeterMatrix.A 8).simple i) : ↥(ggAutomizer J Bs)) : MulAut ↥Bs) := by
  intro G _ _ p B Bs x L D J y K hH _ hrL hDL
  have hJL : J ≤ L := (hH.1.2.2).1.2.2.2.2.2.1.1.trans inf_le_left
  exact pjb_ggMaxRankJReflection_side (X := L) (J := J) hLab hCore
    hH.1.2.1 hH.2.2.1.1 hJL hrL hDL (ggMaxRank_witness hH hLab hrL)

theorem ggMaxRankJReflection_side_of_core
    (hLab : GGLabelRigidInput) (hCore : GGMaxRankE8Core)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs X J : Subgroup G}
    (hBstar : GGBstar p B Bs) (hinn : GGInnerDiagOn Bs X) (hJX : J ≤ X)
    (hrow : GGResRowAt ggRowMaxRank p J X) (hD : GGResE8SeparatedDatum p Bs X)
    (hw : ∃ z ∈ Bs, z ∉ Subgroup.centralizer (X : Set G) ∧
      IsComponentOf J (X ⊓ Subgroup.centralizer ({z} : Set G))) :
    ∃ eJ : (CoxeterMatrix.A 8).Group ≃* ↥(ggAutomizer J Bs),
      ∀ i, GGIsReflection p
        ((eJ ((CoxeterMatrix.A 8).simple i) : ↥(ggAutomizer J Bs)) : MulAut ↥Bs) :=
  pjb_ggMaxRankJReflection_side (X := X) (J := J) hLab hCore hBstar hinn hJX hrow hD hw

end CFSG.StandardType

end
