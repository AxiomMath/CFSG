module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrDefs
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Defs
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Glauberman
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.Invariance
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic

public section

open CFSG.Open
open scoped commutatorElement Pointwise

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Thm35

variable {Γ : Type u} [Group Γ] {p : ℕ}

section FittingPre

variable {D D₂ : Subgroup Γ} [(D₂.subgroupOf D).Normal]

theorem fittingPre_le : fittingPre D D₂ ≤ D :=
  Subgroup.map_subtype_le _

theorem le_fittingPre (h : D₂ ≤ D) : D₂ ≤ fittingPre D D₂ := by
  intro x hx
  refine ⟨⟨x, h hx⟩, ?_, rfl⟩
  have : (QuotientGroup.mk' (D₂.subgroupOf D)) ⟨x, h hx⟩ = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hx)
  exact Subgroup.mem_comap.mpr (by rw [this]; exact one_mem _)

theorem le_fittingPre_of_nilpotent {Z : Subgroup Γ} (hZD : Z ≤ D)
    (hZ : D ≤ Subgroup.normalizer (Z : Set Γ)) (hnil : Group.IsNilpotent Z) :
    Z ≤ fittingPre D D₂ := by
  have hnorm : (Z.subgroupOf D).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hZD).mpr hZ
  have hnil' : Group.IsNilpotent (Z.subgroupOf D) :=
    Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hZD).symm
  have himg : Group.IsNilpotent ((Z.subgroupOf D).map (QuotientGroup.mk' (D₂.subgroupOf D))) :=
    Group.nilpotent_of_surjective
      ((QuotientGroup.mk' (D₂.subgroupOf D)).subgroupMap (Z.subgroupOf D))
      ((QuotientGroup.mk' (D₂.subgroupOf D)).subgroupMap_surjective _)
  have hle : (Z.subgroupOf D).map (QuotientGroup.mk' (D₂.subgroupOf D)) ≤
      CFSG.fittingSubgroup (↥D ⧸ D₂.subgroupOf D) :=
    le_sSup ⟨hnorm.map _ (QuotientGroup.mk'_surjective _), himg⟩
  intro x hx
  refine ⟨⟨x, hZD hx⟩, ?_, rfl⟩
  exact hle ⟨⟨x, hZD hx⟩, hx, rfl⟩

end FittingPre

section Glauberman

variable {A X : Subgroup Γ}

theorem admits_of_le_cenIn {Z : Subgroup Γ} (hZ : Z ≤ cenIn X (A : Set Γ)) : Admits A Z := by
  rw [Admits, Subgroup.le_normalizer_iff]
  intro a ha z hz
  have := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hZ hz)).2 a ha
  rw [this]
  group
  exact hz

theorem inf_cenIn_sup_le [Finite Γ] (h : NearAsolvAction p A X) {D₂ K₁ K₂ : Subgroup Γ}
    (h₁ : K₁ ≤ X) (h₂ : K₂ ≤ X) (hA₁ : Admits A K₁) (hA₂ : Admits A K₂)
    (hK : K₁ ≤ Subgroup.normalizer (K₂ : Set Γ))
    (hD₁ : K₁ ⊓ cenIn X (A : Set Γ) ≤ D₂) (hD₂ : K₂ ⊓ cenIn X (A : Set Γ) ≤ D₂) :
    (K₁ ⊔ K₂) ⊓ cenIn X (A : Set Γ) ≤ D₂ := by
  intro x hx
  obtain ⟨hxs, hxc⟩ := Subgroup.mem_inf.mp hx
  have hAp : IsPGroup p A :=
    CFSG.SignalizerFunctor.Helpers.elementary_abelian_isPGroup p A h.elemAbelian
  have hcop : Nat.Coprime p (Nat.card ↥K₁) :=
    h.nearPSolvable.1.coprime_dvd_right (Subgroup.card_dvd_of_le h₁)
  have hxs' : x ∈ (K₁ : Set Γ) * K₂ := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right K₁ K₂ hK]
    exact hxs
  obtain ⟨a, ha, b, hb, rfl⟩ := CFSG.SignalizerFunctorTheorem.McBride.exists_mul_of_mem_centralizer
    h.prime hAp hcop hA₁ hA₂ hxs' (Subgroup.mem_inf.mp hxc).2
  have ha' : a ∈ K₁ ⊓ cenIn X (A : Set Γ) :=
    Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp ha).1, Subgroup.mem_inf.mpr
      ⟨h₁ (Subgroup.mem_inf.mp ha).1, (Subgroup.mem_inf.mp ha).2⟩⟩
  have hb' : b ∈ K₂ ⊓ cenIn X (A : Set Γ) :=
    Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hb).1, Subgroup.mem_inf.mpr
      ⟨h₂ (Subgroup.mem_inf.mp hb).1, (Subgroup.mem_inf.mp hb).2⟩⟩
  exact mul_mem (hD₁ ha') (hD₂ hb')

end Glauberman

structure Hyp (p : ℕ) (A X D D₂ N L R : Subgroup Γ) [(D₂.subgroupOf D).Normal] : Prop where
  near : NearAsolvAction p A X
  cen : cenIn X (A : Set Γ) = D
  pair : (iPairsY A X D₂).Nonempty
  hN : N ≤ X
  hL : L ≤ X
  hR : R ≤ X
  nN : IsNormalIn N (R ⊔ D ⊔ A)
  nL : IsNormalIn L (R ⊔ D ⊔ A)
  nR : IsNormalIn R (R ⊔ D ⊔ A)
  chief : IsChiefFactorOf (R ⊔ D ⊔ A) L N
  LR : L ≤ R
  cent : A ⊔ R ≤ secCenIn (R ⊔ D ⊔ A) L N
  RD : R ⊓ D = fittingPre D D₂
  ND : D ⊓ N ≤ D₂
  prod : IsDirectProductMod N (fittingPre D D₂ ⊔ N) (D₂ ⊔ N) L

@[expose] def Concl (A D D₂ R : Subgroup Γ) [(D₂.subgroupOf D).Normal] : Prop :=
  ∃ B : Subgroup Γ, B ≤ R ∧ IsNormalIn B (R ⊔ D ⊔ A) ∧ B ⊓ D = D₂ ∧
    R = B ⊔ fittingPre D D₂

theorem R_le_H (R D A : Subgroup Γ) : R ≤ R ⊔ D ⊔ A := le_sup_left.trans le_sup_left

theorem D_le_H (R D A : Subgroup Γ) : D ≤ R ⊔ D ⊔ A := le_sup_right.trans le_sup_left

theorem A_le_H (R D A : Subgroup Γ) : A ≤ R ⊔ D ⊔ A := le_sup_right

namespace Hyp

variable {A X D D₂ N L R : Subgroup Γ} [(D₂.subgroupOf D).Normal] (H : Hyp p A X D D₂ N L R)

include H

theorem D_le_X : D ≤ X := H.cen ▸ inf_le_left

theorem D₂_le_D : D₂ ≤ D := by
  obtain ⟨⟨X₁, X₂⟩, hP⟩ := H.pair
  have h := hP.2
  rw [H.cen] at h
  rw [← h]
  exact inf_le_right

theorem D₂_le_Ds : D₂ ≤ fittingPre D D₂ := le_fittingPre H.D₂_le_D

theorem Ds_le_R : fittingPre D D₂ ≤ R := H.RD ▸ inf_le_left

theorem D₂_le_R : D₂ ≤ R := H.D₂_le_Ds.trans H.Ds_le_R

theorem D₂_le_X : D₂ ≤ X := H.D₂_le_D.trans H.D_le_X

theorem admits_A_D₂ : Admits A D₂ :=
  admits_of_le_cenIn (X := X) (by rw [H.cen]; exact H.D₂_le_D)

theorem H_le_N : R ⊔ D ⊔ A ≤ Subgroup.normalizer (N : Set Γ) := H.nN.2

theorem H_le_L : R ⊔ D ⊔ A ≤ Subgroup.normalizer (L : Set Γ) := H.nL.2

theorem H_le_R : R ⊔ D ⊔ A ≤ Subgroup.normalizer (R : Set Γ) := H.nR.2

theorem N_le_L : N ≤ L := H.chief.2.2.1.le

theorem admits_A_N : Admits A N := (A_le_H R D A).trans H.H_le_N

theorem cent_normalizes_N {g : Γ} (hg : g ∈ A ⊔ R) : g ∈ Subgroup.normalizer (N : Set Γ) :=
  (mem_sectionCentralizer_iff.mp (Subgroup.mem_inf.mp (H.cent hg)).2).1

theorem cent_normalizes_L {g : Γ} (hg : g ∈ A ⊔ R) : g ∈ Subgroup.normalizer (L : Set Γ) :=
  (mem_sectionCentralizer_iff.mp (Subgroup.mem_inf.mp (H.cent hg)).2).2.1

theorem cent_comm {g : Γ} (hg : g ∈ A ⊔ R) {y : Γ} (hy : y ∈ L) : ⁅g, y⁆ ∈ N :=
  (mem_sectionCentralizer_iff.mp (Subgroup.mem_inf.mp (H.cent hg)).2).2.2 y hy

theorem R_normalizes_N {g : Γ} (hg : g ∈ R) : g ∈ Subgroup.normalizer (N : Set Γ) :=
  H.cent_normalizes_N (Subgroup.mem_sup_right hg)

theorem R_comm {g : Γ} (hg : g ∈ R) {y : Γ} (hy : y ∈ L) : ⁅g, y⁆ ∈ N :=
  H.cent_comm (Subgroup.mem_sup_right hg) hy

theorem L_le_sup : L ≤ fittingPre D D₂ ⊔ N := by
  rw [← H.prod.2.2.1]
  exact le_sup_right

theorem sup_inf_L : (D₂ ⊔ N) ⊓ L = N := H.prod.2.2.2.1

theorem inf_sup_le [Finite Γ] {M : Subgroup Γ} (hMX : M ≤ X) (hXM : Admits X M) (hAM : Admits A M)
    (hMD : D ⊓ M ≤ D₂) : L ⊓ (D₂ ⊔ N ⊔ M) ≤ N := by
  have hDX := H.D_le_X
  have hD₂X := H.D₂_le_X
  have hAN := H.admits_A_N
  have hDN : D ≤ Subgroup.normalizer (N : Set Γ) := (D_le_H R D A).trans H.H_le_N
  have hD₂N : D₂ ≤ Subgroup.normalizer (N : Set Γ) := H.D₂_le_D.trans hDN
  have h1 : (D₂ ⊔ N) ⊓ cenIn X (A : Set Γ) ≤ D₂ :=
    inf_cenIn_sup_le H.near hD₂X H.hN H.admits_A_D₂ hAN hD₂N inf_le_left
      (by rw [H.cen, inf_comm]; exact H.ND)
  have h2 : (D₂ ⊔ N ⊔ M) ⊓ cenIn X (A : Set Γ) ≤ D₂ :=
    inf_cenIn_sup_le H.near (sup_le hD₂X H.hN) hMX (H.admits_A_D₂.sup hAN) hAM
      ((sup_le hD₂X H.hN).trans hXM) h1 (by rw [H.cen, inf_comm]; exact hMD)
  intro l hl
  obtain ⟨hlL, hlS⟩ := Subgroup.mem_inf.mp hl
  have hDsN : fittingPre D D₂ ≤ Subgroup.normalizer (N : Set Γ) := fittingPre_le.trans hDN
  have hl' : l ∈ (fittingPre D D₂ : Set Γ) * N := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hDsN]
    exact H.L_le_sup hlL
  obtain ⟨d, hd, n, hn, rfl⟩ := hl'
  have hnS : n ∈ D₂ ⊔ N ⊔ M := Subgroup.mem_sup_left (Subgroup.mem_sup_right hn)
  have hdS : d ∈ D₂ ⊔ N ⊔ M := by
    have := mul_mem hlS (inv_mem hnS)
    simpa using this
  have hdD : d ∈ cenIn X (A : Set Γ) := by
    rw [H.cen]
    exact fittingPre_le hd
  have hdD₂ : d ∈ D₂ := h2 (Subgroup.mem_inf.mpr ⟨hdS, hdD⟩)
  have hln : d * n ∈ (D₂ ⊔ N) ⊓ L :=
    Subgroup.mem_inf.mpr ⟨mul_mem (Subgroup.mem_sup_left hdD₂) (Subgroup.mem_sup_right hn), hlL⟩
  rwa [H.sup_inf_L] at hln

end Hyp

end CFSG.SignalizerFunctorTheorem.McBride.Near.Thm35
