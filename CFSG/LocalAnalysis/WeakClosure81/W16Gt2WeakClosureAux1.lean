module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenSixFive

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Cfg1620

variable {M V₀ V U S R H : Subgroup G} {g : G} {B : Subgroup G}

private theorem rk_intSub_eq_of_le {V S : Subgroup G} (hV : IsElemAbelian 2 V) (hS : S ≤ V) :
    rk ↥(intSub V hV S) = rk ↥S := by
  unfold rk
  change padicValNat 2 (Nat.card ↥(S.subgroupOf V)) = padicValNat 2 (Nat.card ↥S)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS).toEquiv]

theorem imgTil_rank_le {V₀ V S : Subgroup G} (hV : IsElemAbelian 2 V) (hS : S ≤ V) :
    rk ↥(imgTil V₀ V hV S) ≤ rk ↥S := by
  have h1 : rk ↥(imgTil V₀ V hV S) ≤ rk ↥(intSub V hV S) := by
    have h := rk_map_add_rk_inf_ker (mkTil V₀ V hV) (intSub V hV S)
    change rk ↥(Subgroup.map (mkTil V₀ V hV) (intSub V hV S)) +
        rk ↥(intSub V hV S ⊓ (mkTil V₀ V hV).ker) = rk ↥(intSub V hV S) at h
    have h2 : Subgroup.map (mkTil V₀ V hV) (intSub V hV S) = imgTil V₀ V hV S := rfl
    rw [h2] at h
    omega
  rw [rk_intSub_eq_of_le hV hS] at h1
  exact h1

theorem commV_zpowers_actTil_eq_imgTil_commutator {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    {x : G} (hx : x ∈ stabTil V₀ V) :
    commV (Subgroup.zpowers (actTil V₀ V hV ⟨x, hx⟩)) =
      imgTil V₀ V hV ⁅V, Subgroup.zpowers x⁆ := by
  have hbar : barSub V₀ V hV (Subgroup.zpowers x) =
      Subgroup.zpowers (actTil V₀ V hV ⟨x, hx⟩) := by
    unfold barSub
    have hsub : (Subgroup.zpowers x).subgroupOf (stabTil V₀ V) =
        Subgroup.zpowers ⟨x, hx⟩ := by
      ext y
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
      constructor
      · rintro ⟨n, hn⟩
        exact ⟨n, Subtype.ext hn⟩
      · rintro ⟨n, hn⟩
        exact ⟨n, congrArg Subtype.val hn⟩
    rw [hsub, MonoidHom.map_zpowers]
  have htop : imgTil V₀ V hV V = ⊤ := by
    rw [← imgTil_preTil V₀ V hV ⊤, preTil_top]
  have h := S18.imgTil_commutator_eq_commSub_of_le (V₀ := V₀) (V := V) (A := V)
    (X := Subgroup.zpowers x) hV le_rfl (Subgroup.zpowers_le.2 hx)
  rw [htop, hbar, ← commV_eq_commSub] at h
  exact h.symm

theorem rk_commV_actTil_le_of_commutator_le {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    {x : G} (hx : x ∈ stabTil V₀ V) {Y : Subgroup G}
    (hcomm : ⁅V, Subgroup.zpowers x⁆ ≤ Y) :
    rk ↥(commV (Subgroup.zpowers (actTil V₀ V hV ⟨x, hx⟩))) ≤ rk ↥Y := by
  rw [commV_zpowers_actTil_eq_imgTil_commutator hV hx]
  have hxN : Subgroup.zpowers x ≤ Subgroup.normalizer (V : Set G) :=
    (Subgroup.zpowers_le.2 (stabTil_le_normalizer V₀ V hx))
  have hcommV : ⁅V, Subgroup.zpowers x⁆ ≤ V :=
    (Subgroup.le_normalizer_iff_commutator_le_left).1 hxN
  exact (imgTil_rank_le hV hcommV).trans (rk_mono hcomm)

theorem mQuot_inf_centralizer_le_rk {A V X : Subgroup G} (hV : IsElemAbelian 2 V)
    (hAV : A ≤ V) (hXV : X ≤ V) {t : G} (hcomm : ∀ a ∈ A, ⁅a, t⁆ ∈ X) :
    E3.mQuot A (A ⊓ Subgroup.centralizer ({t} : Set G)) ≤ rk ↥X := by
  let f : ↥A →* G :=
    { toFun := fun a => (a : G) * t * (a : G)⁻¹ * t⁻¹
      map_one' := by simp
      map_mul' := by
        intro a b
        have haX : ⁅(a : G), t⁆ ∈ X := hcomm a a.2
        have hbX : ⁅(b : G), t⁆ ∈ X := hcomm b b.2
        have hcbv : (b : G) * t * (b : G)⁻¹ = ⁅(b : G), t⁆ * t := by
          rw [commutatorElement_def]
          group
        have hcav : (a : G) * t * (a : G)⁻¹ = ⁅(a : G), t⁆ * t := by
          rw [commutatorElement_def]
          group
        have hacb : (a : G) * ⁅(b : G), t⁆ = ⁅(b : G), t⁆ * (a : G) :=
          B2F.isElemAbelian_comm hV (hAV a.2) (hXV hbX)
        have hconjb : (a : G) * ⁅(b : G), t⁆ * (a : G)⁻¹ = ⁅(b : G), t⁆ := by
          rw [hacb]
          group
        have hcab : ⁅(a : G), t⁆ * ⁅(b : G), t⁆ = ⁅(b : G), t⁆ * ⁅(a : G), t⁆ :=
          B2F.isElemAbelian_comm hV (hXV haX) (hXV hbX)
        show ((a * b : ↥A) : G) * t * ((a * b : ↥A) : G)⁻¹ * t⁻¹ =
          ⁅(a : G), t⁆ * ⁅(b : G), t⁆
        rw [Subgroup.coe_mul]
        calc ((a : G) * (b : G)) * t * ((a : G) * (b : G))⁻¹ * t⁻¹
            = (a : G) * ((b : G) * t * (b : G)⁻¹) * (a : G)⁻¹ * t⁻¹ := by group
          _ = (a : G) * (⁅(b : G), t⁆ * t) * (a : G)⁻¹ * t⁻¹ := by rw [hcbv]
          _ = ((a : G) * ⁅(b : G), t⁆ * (a : G)⁻¹) *
              ((a : G) * t * (a : G)⁻¹) * t⁻¹ := by group
          _ = ⁅(b : G), t⁆ * ((a : G) * t * (a : G)⁻¹) * t⁻¹ := by rw [hconjb]
          _ = ⁅(b : G), t⁆ * (⁅(a : G), t⁆ * t) * t⁻¹ := by rw [hcav]
          _ = ⁅(b : G), t⁆ * ⁅(a : G), t⁆ := by group
          _ = ⁅(a : G), t⁆ * ⁅(b : G), t⁆ := hcab.symm }
  have hker : f.ker = (A ⊓ Subgroup.centralizer ({t} : Set G)).subgroupOf A := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro h
      refine ⟨x.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      have h2 : (x : G) * t * (x : G)⁻¹ = t := mul_inv_eq_one.1 h
      have h3 : (x : G) * t = t * (x : G) := (mul_inv_eq_iff_eq_mul).1 h2
      exact h3.symm
    · rintro ⟨-, hxC⟩
      have hcv : t * (x : G) = (x : G) * t :=
        (Subgroup.mem_centralizer_iff.1 hxC) t (Set.mem_singleton t)
      show (x : G) * t * (x : G)⁻¹ * t⁻¹ = 1
      rw [← hcv]
      group
  have hrk : rkIdx f.ker = rk ↥f.range := by
    unfold rkIdx rk
    rw [Subgroup.index_ker]
  calc E3.mQuot A (A ⊓ Subgroup.centralizer ({t} : Set G))
      = rkIdx ((A ⊓ Subgroup.centralizer ({t} : Set G)).subgroupOf A) := E3.mQuot_eq_rkIdx A _
    _ = rkIdx f.ker := by rw [hker]
    _ = rk ↥f.range := hrk
    _ ≤ rk ↥X := rk_mono (fun y hy => by
        rcases hy with ⟨a, rfl⟩
        exact hcomm a a.2)

end Cfg1620

end CFSG.LocalAnalysis.WeakClosure81
