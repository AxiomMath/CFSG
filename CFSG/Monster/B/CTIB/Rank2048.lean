module

public import CFSG.Monster.B.CTIB.UniqueComponent
public import CFSG.Monster.Existence.TwoB
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTIBasic
public import Certificates.Certificate3011
public import Certificates.Certificate3012
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3028
public import Certificates.Certificate3045
public import Certificates.Certificate3048
public import Certificates.Certificate3049
public import Certificates.Certificate3050
public import Certificates.Certificate3051
public import Certificates.Certificate3098
public import Certificates.Certificate3099
public import Certificates.Certificate3100
public import Certificates.Certificate3101
public import Certificates.Certificate3102
public import Certificates.Certificate3103
public import Certificates.Certificate3106
public import Certificates.Certificate3107
public import Certificates.Certificate3108
public import Certificates.Certificate3109
public import Certificates.Certificate3110
public import Certificates.Certificate3111
public import Certificates.Certificate3114
public import Certificates.Certificate3115
public import Certificates.Certificate3116
public import Certificates.Certificate3117
public import Certificates.Certificate3118
public import Certificates.Certificate3027
public import CFSG.Open.MonsterY443Defs
public import CFSG.Sporadic.Co1Base

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.CTIB

open MulOpposite CFSG.Blueprint CFSG.Monster.B
open CFSG.Sporadic.Co2Inv (co2_involution_input)

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)
local notation "βr" s => ((betaRow Dyadic.betaS s : MatBˣ) : MatB)

theorem isConj_xs_of_rank
    {s : Sbp} (hs : orderOf s = 2) (hr : ((βr s) - 1).rank = 2048) :
    IsConj s xs := by
  obtain ⟨i, ⟨hi, hc⟩, -⟩ := four_classes co2_involution_input hs
  have e := rank_beta_conj hc
  obtain ⟨h1, h0, h5, h3⟩ := rank_four
  have hi0 : i = 0 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> omega
  subst hi0
  exact rs0_eq ▸ hc

@[expose] noncomputable def conjCbar (c : Sbp) : Sbp ≃* Cbar :=
  (MulAut.conj c).trans (MulEquiv.inv' Cbar).symm

theorem conjCbar_apply (c g : Sbp) : conjCbar c g = (c * g * c⁻¹).unop⁻¹ := rfl

variable {c s : Sbp}

theorem conjCbar_self (hc : c * s * c⁻¹ = xs) : conjCbar c s = xbar⁻¹ :=
  (conjCbar_apply c s).trans (congrArg (fun y : Sbp => y.unop⁻¹) hc)

theorem centralizer_conjCbar (hc : c * s * c⁻¹ = xs) :
    Subgroup.centralizer {conjCbar c s} = Jbar :=
  (congrArg (fun y : Cbar => Subgroup.centralizer {y}) (conjCbar_self hc)).trans
    ((centralizer_inv xbar).trans centralizer_xbar)

@[expose] noncomputable def centJbar (hc : c * s * c⁻¹ = xs) :
    Subgroup.centralizer {s} ≃* Jbar :=
  (centralizerEquiv (conjCbar c) s).trans (MulEquiv.subgroupCongr (centralizer_conjCbar hc))

theorem centJbar_apply
    (hc : c * s * c⁻¹ = xs) (g : Subgroup.centralizer {s}) :
    ((centJbar hc g : Jbar) : Cbar) = conjCbar c g := rfl

theorem mem_centralizer_iff_of_conj
    (hc : c * s * c⁻¹ = xs) (g : Sbp) :
    g ∈ Subgroup.centralizer {s} ↔ c * g * c⁻¹ ∈ Jbar.op := by
  have key : g ∈ Subgroup.centralizer {s} ↔
      conjCbar c g ∈ Subgroup.centralizer {conjCbar c s} := by
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff,
      ← map_mul, ← map_mul, (conjCbar c).injective.eq_iff]
  exact key.trans ((SetLike.ext_iff.1 (centralizer_conjCbar hc) _).trans Jbar.inv_mem_iff)

@[expose] noncomputable def qCent (hc : c * s * c⁻¹ = xs) :
    Subgroup (Subgroup.centralizer {s}) :=
  (Ebar.subgroupOf Jbar).comap (centJbar hc).toMonoidHom

theorem mem_qCent_iff
    (hc : c * s * c⁻¹ = xs) (g : Subgroup.centralizer {s}) :
    g ∈ qCent hc ↔ conjCbar c g ∈ Ebar := Iff.rfl

theorem mem_qCent_iff_of_conj
    (hc : c * s * c⁻¹ = xs) (g : Subgroup.centralizer {s}) :
    g ∈ qCent hc ↔ c * (g : Sbp) * c⁻¹ ∈ Qs :=
  (mem_qCent_iff hc g).trans Ebar.inv_mem_iff

@[expose] noncomputable def qCentEquiv
    (hc : c * s * c⁻¹ = xs) : qCent hc ≃* Ebar :=
  ((MulEquiv.subgroupCongr (Subgroup.comap_equiv_eq_map_symm' (centJbar hc)
    (Ebar.subgroupOf Jbar))).trans
    ((Ebar.subgroupOf Jbar).equivMapOfInjective (centJbar hc).symm.toMonoidHom
      (centJbar hc).symm.injective).symm).trans
    (Subgroup.subgroupOfEquivOfLe Ebar_le_Jbar)

instance qCent_normal (hc : c * s * c⁻¹ = xs) : (qCent hc).Normal :=
  Subgroup.Normal.comap inferInstance _

theorem qCent_extraspecial (hc : c * s * c⁻¹ = xs) :
    IsExtraspecialPGroup 2 (qCent hc) ∧ Nat.card (qCent hc) = 2 ^ 23 :=
  ⟨CFSG.Monster.Existence.IsExtraspecialPGroup.of_mulEquiv (qCentEquiv hc).symm
      Ebar_extraspecial.1,
    (Nat.card_congr (qCentEquiv hc).toEquiv).trans Ebar_extraspecial.2⟩

theorem centralizer_qCent_le (hc : c * s * c⁻¹ = xs) :
    Subgroup.centralizer (qCent hc : Set (Subgroup.centralizer {s})) ≤ qCent hc := by
  intro g hg
  have hE : conjCbar c g ∈ Subgroup.centralizer (Ebar : Set Cbar) := by
    refine Subgroup.mem_centralizer_iff.2 fun e he => ?_
    have hq : (centJbar hc).symm ⟨e, Ebar_le_Jbar he⟩ ∈ qCent hc := by
      show (((centJbar hc) ((centJbar hc).symm ⟨e, Ebar_le_Jbar he⟩) : Jbar) : Cbar) ∈ Ebar
      exact (congrArg (fun y : Jbar => (y : Cbar) ∈ Ebar)
        ((centJbar hc).apply_symm_apply ⟨e, Ebar_le_Jbar he⟩)).mpr he
    have h := congrArg (fun y => ((centJbar hc y : Jbar) : Cbar))
      (Subgroup.mem_centralizer_iff.1 hg _ hq)
    simpa only [map_mul, MulEquiv.apply_symm_apply, Subgroup.coe_mul, centJbar_apply] using h
  have hz : conjCbar c g ∈ Subgroup.zpowers xbar :=
    (SetLike.ext_iff.1 centralizer_Ebar _).1 ⟨(centJbar hc g).2, hE⟩
  exact Subgroup.zpowers_le.2 xbar_mem_Ebar hz

theorem centralizer_eq_map_center {G : Type*} [Group G] {Q : Subgroup G}
    (h : Subgroup.centralizer (Q : Set G) ≤ Q) :
    Subgroup.centralizer (Q : Set G) = (Subgroup.center Q).map Q.subtype := by
  ext g
  constructor
  · intro hg
    refine ⟨⟨g, h hg⟩, Subgroup.mem_center_iff.2 fun q => Subtype.ext ?_, rfl⟩
    exact Subgroup.mem_centralizer_iff.1 hg q q.2
  · rintro ⟨q, hq, rfl⟩
    exact Subgroup.mem_centralizer_iff.2 fun y hy =>
      congrArg Subtype.val (Subgroup.mem_center_iff.1 hq ⟨y, hy⟩)

theorem native_rank_2048_centralizer_has_no_components :
    ∀ s : Sbp, orderOf s = 2 → ((βr s) - 1).rank = 2048 →
      ∃ c : Sbp, c * s * c⁻¹ = xs ∧
        (∀ g : Sbp, g ∈ Subgroup.centralizer {s} ↔ c * g * c⁻¹ ∈ Jbar.op) ∧
        (∃ m : ℕ, Odd m ∧ Nat.card (Subgroup.centralizer {s}) = 2 ^ 41 * m) ∧
        ∃ Q : Subgroup (Subgroup.centralizer {s}),
          (∀ g : Subgroup.centralizer {s}, g ∈ Q ↔ c * (g : Sbp) * c⁻¹ ∈ Qs) ∧
          Q.Normal ∧ IsExtraspecialPGroup 2 Q ∧ Nat.card Q = 2 ^ 23 ∧
          Subgroup.centralizer (Q : Set (Subgroup.centralizer {s})) =
            (Subgroup.center Q).map Q.subtype ∧
          (Subgroup.center Q).map Q.subtype =
            Subgroup.zpowers ⟨s, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩ ∧
          Nat.card (Subgroup.center Q) = 2 ∧
          ∀ K : Subgroup (Subgroup.centralizer {s}), ¬ CFSG.IsComponent K := by
  intro s hs hr
  have hconj := isConj_xs_of_rank hs hr
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  have hX := qCent_extraspecial hc
  have hCQ := centralizer_qCent_le hc
  have hZ := centralizer_eq_map_center hCQ
  have hz2 : Nat.card (Subgroup.center (qCent hc)) = 2 := hX.1.2.2.2
  let sC : Subgroup.centralizer {s} := ⟨s, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
  have hsC : sC ∈ Subgroup.centralizer (qCent hc : Set (Subgroup.centralizer {s})) :=
    Subgroup.mem_centralizer_iff.2 fun q _ =>
      Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 q.2)
  have hle : Subgroup.zpowers sC ≤ (Subgroup.center (qCent hc)).map (qCent hc).subtype :=
    Subgroup.zpowers_le.2 (hZ ▸ hsC)
  have hcard : Nat.card ((Subgroup.center (qCent hc)).map (qCent hc).subtype) =
      Nat.card (Subgroup.zpowers sC) := by
    rw [Subgroup.card_map_of_injective (qCent hc).subtype_injective, hz2, Nat.card_zpowers,
      ← Subgroup.orderOf_coe]
    exact hs.symm
  refine ⟨c, hc, mem_centralizer_iff_of_conj hc,
    ⟨161382375, by decide, (Nat.card_congr (centJbar hc).toEquiv).trans natCard_Jbar_eq⟩,
    qCent hc, mem_qCent_iff_of_conj hc, inferInstance, hX.1, hX.2, hZ,
    (Subgroup.eq_of_le_of_card_ge hle hcard.le).symm, hz2, fun K =>
      CFSG.ComponentClassification.OutcomeLocal.not_isComponent_of_selfCentralizing
        (p := 2) inferInstance hX.1.1 hCQ K⟩

end CFSG.Monster.B.CTIB
