module

public import Mathlib
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrThm32Quot
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LieType.Ree.SuzukiSimple
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.SignalizerFunctorTheorem.McBride.Near.AssocSup
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210j
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.theorem_4_18_b
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import Certificates.Certificate43

public section

open CFSG.Open
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
open scoped commutatorElement

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Thm32

variable {Γ : Type u} [Group Γ] {p : ℕ}

theorem isElemAbelian_of_le {A B : Subgroup Γ} (hA : IsElemAbelian p A) (hBA : B ≤ A) :
    IsElemAbelian p B := CFSG.Open.IsElemAbelian.mono hA hBA

structure BackSetting (p : ℕ) (A D X₁ X₂ B : Subgroup Γ) : Prop where
  prime : p.Prime
  elemAbelian : IsElemAbelian p A
  D_cen : D ≤ Subgroup.centralizer (A : Set Γ)
  coprime : Nat.Coprime p (Nat.card ↥(X₁ ⊔ D))
  chief : IsChiefFactorOf (X₁ ⊔ D ⊔ A) X₁ X₂
  B_le : B ≤ A

namespace BackSetting

variable {A D X₁ X₂ B : Subgroup Γ} (S : BackSetting p A D X₁ X₂ B)

include S

theorem X₂_le : X₂ ≤ X₁ := S.chief.2.2.1.le

theorem E_le_nor_X₂ : X₁ ⊔ D ⊔ A ≤ Subgroup.normalizer (X₂ : Set Γ) := S.chief.1.2

theorem E_le_nor_X₁ : X₁ ⊔ D ⊔ A ≤ Subgroup.normalizer (X₁ : Set Γ) := S.chief.2.1.2

theorem G_le_nrm : X₁ ⊔ D ≤ AChief.nrm X₂ := le_sup_left.trans S.E_le_nor_X₂

theorem A_le_nrm : A ≤ AChief.nrm X₂ := le_sup_right.trans S.E_le_nor_X₂

theorem X₁_le_nrm : X₁ ≤ AChief.nrm X₂ := le_sup_left.trans S.G_le_nrm

theorem D_le_nrm : D ≤ AChief.nrm X₂ := le_sup_right.trans S.G_le_nrm

theorem B_le_nrm : B ≤ AChief.nrm X₂ := S.B_le.trans S.A_le_nrm

theorem A_le_nor_X₁ : A ≤ Subgroup.normalizer (X₁ : Set Γ) :=
  le_sup_right.trans S.E_le_nor_X₁

theorem D_le_nor_X₁ : D ≤ Subgroup.normalizer (X₁ : Set Γ) :=
  (le_sup_right.trans le_sup_left).trans S.E_le_nor_X₁

theorem mul_comm_of_mem_A {a b : Γ} (ha : a ∈ A) (hb : b ∈ A) : a * b = b * a := by
  have := S.elemAbelian.1
  exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : A) ⟨b, hb⟩)

theorem A_le_cen_B : A ≤ Subgroup.centralizer (B : Set Γ) := fun _ ha =>
  Subgroup.mem_centralizer_iff.mpr fun _ hb => S.mul_comm_of_mem_A (S.B_le hb) ha

theorem D_le_cen_B : D ≤ Subgroup.centralizer (B : Set Γ) :=
  S.D_cen.trans (Subgroup.centralizer_le S.B_le)

theorem A_le_cen_D : A ≤ Subgroup.centralizer (D : Set Γ) := fun _ ha =>
  Subgroup.mem_centralizer_iff.mpr fun _ hd =>
    (Subgroup.mem_centralizer_iff.mp (S.D_cen hd) _ ha).symm

theorem A_le_nor_D : A ≤ Subgroup.normalizer (D : Set Γ) :=
  S.A_le_cen_D.trans (Subgroup.centralizer_le_normalizer _)

theorem A_le_nor_G : A ≤ Subgroup.normalizer ((X₁ ⊔ D : Subgroup Γ) : Set Γ) :=
  le_normalizer_sup S.A_le_nor_X₁ S.A_le_nor_D

theorem isElemAbelian_B : IsElemAbelian p B := isElemAbelian_of_le S.elemAbelian S.B_le

theorem coprime_X₁ : Nat.Coprime p (Nat.card ↥X₁) :=
  S.coprime.coprime_dvd_right (Subgroup.card_dvd_of_le le_sup_left)

theorem cenIn_sup_eq : cenIn (X₁ ⊔ D) (B : Set Γ) = cenIn X₁ (B : Set Γ) ⊔ D := by
  refine le_antisymm (fun g hg => ?_) (sup_le (inf_le_inf_right _ le_sup_left)
    (le_inf le_sup_right S.D_le_cen_B))
  obtain ⟨hgG, hgC⟩ := Subgroup.mem_inf.mp hg
  obtain ⟨x, hx, d, hd, rfl⟩ := (mem_sup_iff_mul S.D_le_nor_X₁).mp hgG
  have hxC : x ∈ Subgroup.centralizer (B : Set Γ) := by
    have : x = x * d * d⁻¹ := by group
    rw [this]
    exact mul_mem hgC (inv_mem (S.D_le_cen_B hd))
  exact Subgroup.mul_mem_sup (Subgroup.mem_inf.mpr ⟨hx, hxC⟩) hd

theorem cenIn_inf_X₂ : cenIn X₁ (B : Set Γ) ⊓ X₂ = cenIn X₂ (B : Set Γ) := by
  ext x
  simp only [cenIn, Subgroup.mem_inf]
  constructor
  · rintro ⟨⟨_, hxC⟩, hxX₂⟩
    exact ⟨hxX₂, hxC⟩
  · rintro ⟨hxX₂, hxC⟩
    exact ⟨⟨S.X₂_le hxX₂, hxC⟩, hxX₂⟩

theorem cenIn_X₂_le : cenIn X₂ (B : Set Γ) ≤ cenIn X₁ (B : Set Γ) :=
  inf_le_inf_right _ S.X₂_le

omit S in
theorem cenIn_X₁_le_cen : cenIn X₁ (B : Set Γ) ≤ Subgroup.centralizer (B : Set Γ) := inf_le_right

theorem E_cen_le_cen_B : cenIn X₁ (B : Set Γ) ⊔ D ⊔ A ≤ Subgroup.centralizer (B : Set Γ) :=
  sup_le (sup_le cenIn_X₁_le_cen S.D_le_cen_B) S.A_le_cen_B

omit S in
theorem E_cen_le_E : cenIn X₁ (B : Set Γ) ⊔ D ⊔ A ≤ X₁ ⊔ D ⊔ A :=
  sup_le_sup_right (sup_le_sup_right inf_le_left D) A

theorem E_cen_le_nor_X₂ : cenIn X₁ (B : Set Γ) ⊔ D ⊔ A ≤
    Subgroup.normalizer ((cenIn X₂ (B : Set Γ) : Subgroup Γ) : Set Γ) :=
  le_normalizer_inf (E_cen_le_E.trans S.E_le_nor_X₂)
    (S.E_cen_le_cen_B.trans Subgroup.le_normalizer)

theorem E_cen_le_nor_X₁ : cenIn X₁ (B : Set Γ) ⊔ D ⊔ A ≤
    Subgroup.normalizer ((cenIn X₁ (B : Set Γ) : Subgroup Γ) : Set Γ) :=
  le_normalizer_inf (E_cen_le_E.trans S.E_le_nor_X₁)
    (S.E_cen_le_cen_B.trans Subgroup.le_normalizer)

end BackSetting

section Quotient

variable {A D X₁ X₂ B : Subgroup Γ} (S : BackSetting p A D X₁ X₂ B)

local notation "q" => AChief.qimg X₂

namespace BackSetting

include S

theorem qimg_cenIn_X₁ : q (cenIn X₁ (B : Set Γ)) = cenIn (q X₁) (q B) :=
  AChief.qimg_inf_centralizer S.prime S.isElemAbelian_B (S.B_le.trans S.A_le_nor_X₁)
    S.B_le_nrm S.X₁_le_nrm S.coprime_X₁

theorem qimg_cenIn_G : q (cenIn X₁ (B : Set Γ) ⊔ D) = cenIn (q (X₁ ⊔ D)) (q B) := by
  rw [← S.cenIn_sup_eq]
  exact AChief.qimg_inf_centralizer S.prime S.isElemAbelian_B (S.B_le.trans S.A_le_nor_G)
    S.B_le_nrm S.G_le_nrm S.coprime

theorem isChiefFactorOf_cen (hns : ¬ Group.IsSolvable ↥(cenIn (q X₁) (q B)))
    (hch : IsChiefFactorOf (q A ⊔ cenIn (q (X₁ ⊔ D)) (q B)) (cenIn (q X₁) (q B)) ⊥) :
    IsChiefFactorOf (cenIn X₁ (B : Set Γ) ⊔ D ⊔ A) (cenIn X₁ (B : Set Γ))
      (cenIn X₂ (B : Set Γ)) := by
  have hZ₁N : cenIn X₁ (B : Set Γ) ≤ AChief.nrm X₂ := inf_le_left.trans S.X₁_le_nrm
  have hLem : ∀ L : Subgroup Γ, L ≤ cenIn X₁ (B : Set Γ) → L ≤ AChief.nrm X₂ := fun L hL =>
    hL.trans hZ₁N
  have hne : q (cenIn X₁ (B : Set Γ)) ≠ ⊥ := fun hb => hns (by
    rw [← S.qimg_cenIn_X₁, hb]
    infer_instance)
  have hlt : cenIn X₂ (B : Set Γ) < cenIn X₁ (B : Set Γ) :=
    lt_of_le_of_ne S.cenIn_X₂_le fun heq => hne (by
      rw [eq_bot_iff, ← SolQuot.qimg_self (R := X₂)]
      refine SolQuot.qimg_mono ?_
      calc cenIn X₁ (B : Set Γ) = cenIn X₂ (B : Set Γ) := heq.symm
        _ ≤ X₂ := inf_le_left)
  refine ⟨⟨S.cenIn_X₂_le.trans (le_sup_left.trans le_sup_left), S.E_cen_le_nor_X₂⟩,
    ⟨le_sup_left.trans le_sup_left, S.E_cen_le_nor_X₁⟩, hlt, ?_⟩
  intro L hL hZ₂L hLZ₁
  have hLN : L ≤ AChief.nrm X₂ := hLem L hLZ₁
  have hZ₁D : cenIn X₁ (B : Set Γ) ⊔ D ≤ AChief.nrm X₂ := sup_le hZ₁N S.D_le_nrm
  have hLZ₁' : q L ≤ cenIn (q X₁) (q B) := S.qimg_cenIn_X₁ ▸ SolQuot.qimg_mono hLZ₁
  have hLZD : q L ≤ cenIn (q (X₁ ⊔ D)) (q B) :=
    S.qimg_cenIn_G ▸ SolQuot.qimg_mono (hLZ₁.trans le_sup_left)
  have hnor : q A ⊔ cenIn (q (X₁ ⊔ D)) (q B) ≤
      Subgroup.normalizer ((q L : Subgroup _) : Set _) := by
    have h1 : q (cenIn X₁ (B : Set Γ) ⊔ D ⊔ A) ≤
        Subgroup.normalizer ((q L : Subgroup _) : Set _) := AChief.qimg_le_normalizer hL.2
    rw [SolQuot.qimg_sup hZ₁D S.A_le_nrm, S.qimg_cenIn_G, sup_comm] at h1
    exact h1
  rcases hch.2.2.2 (q L) ⟨hLZD.trans le_sup_right, hnor⟩ bot_le hLZ₁' with h0 | h0
  · left
    refine le_antisymm ?_ hZ₂L
    rw [← S.cenIn_inf_X₂]
    exact le_inf hLZ₁ ((SolQuot.qimg_eq_bot_iff hLN).mp h0)
  · right
    have hZL : q (cenIn X₁ (B : Set Γ)) ≤ q L := by rw [h0, S.qimg_cenIn_X₁]
    have h1 : cenIn X₁ (B : Set Γ) ≤ L ⊔ X₂ := (SolQuot.qimg_le_qimg_iff hZ₁N hLN).mp hZL
    have hLnor : L ≤ Subgroup.normalizer (X₂ : Set Γ) :=
      hLZ₁.trans (inf_le_left.trans (le_sup_left.trans (le_sup_left.trans S.E_le_nor_X₂)))
    exact le_antisymm hLZ₁
      (le_of_le_sup_of_inf_le hLZ₁ hLnor (S.cenIn_inf_X₂.le.trans hZ₂L) h1)

theorem secCenIn_cen [Finite Γ] (hD : Group.IsSolvable ↥D)
    (hns : ¬ Group.IsSolvable ↥(cenIn (q X₁) (q B)))
    (hch : IsChiefFactorOf (q A ⊔ cenIn (q (X₁ ⊔ D)) (q B)) (cenIn (q X₁) (q B)) ⊥)
    (hsol : sol (cenIn (q (X₁ ⊔ D)) (q B)) = ⊥) :
    secCenIn (cenIn X₁ (B : Set Γ) ⊔ D) (cenIn X₁ (B : Set Γ)) (cenIn X₂ (B : Set Γ)) =
      cenIn X₂ (B : Set Γ) := by
  have hZ₁N : cenIn X₁ (B : Set Γ) ≤ AChief.nrm X₂ := inf_le_left.trans S.X₁_le_nrm
  have hZ₁nor : cenIn X₁ (B : Set Γ) ≤
      Subgroup.normalizer ((cenIn X₂ (B : Set Γ) : Subgroup Γ) : Set Γ) :=
    le_sup_left.trans (le_sup_left.trans S.E_cen_le_nor_X₂)
  have hGn₁ : X₁ ⊔ D ≤ Subgroup.normalizer (X₁ : Set Γ) :=
    sup_le Subgroup.le_normalizer S.D_le_nor_X₁
  have hCnorZ : cenIn (q (X₁ ⊔ D)) (q B) ≤
      Subgroup.normalizer ((cenIn (q X₁) (q B) : Subgroup (AChief.QG X₂)) : Set (AChief.QG X₂)) :=
    le_normalizer_inf (inf_le_left.trans (AChief.qimg_le_normalizer hGn₁))
      (inf_le_right.trans Subgroup.le_normalizer)
  have hDC : q D ≤ cenIn (q (X₁ ⊔ D)) (q B) := by
    rw [← S.qimg_cenIn_G]
    exact SolQuot.qimg_mono le_sup_right
  have hsup : cenIn (q (X₁ ⊔ D)) (q B) ≤ cenIn (q X₁) (q B) ⊔ q D := by
    rw [← S.qimg_cenIn_G, SolQuot.qimg_sup hZ₁N S.D_le_nrm, S.qimg_cenIn_X₁]
  have hDs' : Group.IsSolvable ↥(q D) := by
    have := hD
    exact Group.isSolvable_of_surjective (SolQuot.qres_surjective S.D_le_nrm)
  have hcenter := inf_centralizer_self_eq_bot hch hns
  have hCbot := inf_centralizer_eq_bot hCnorZ hDC hsup hDs' hcenter hsol
  refine le_antisymm (fun g hg => ?_) (fun g hg => ?_)
  · obtain ⟨hgZD, hgsc⟩ := Subgroup.mem_inf.mp hg
    have hgcomm := (mem_sectionCentralizer_iff.mp hgsc).2.2
    have hgC : g ∈ cenIn (X₁ ⊔ D) (B : Set Γ) := by
      rw [S.cenIn_sup_eq]
      exact hgZD
    have hgN : g ∈ AChief.nrm X₂ := S.G_le_nrm (Subgroup.mem_inf.mp hgC).1
    obtain ⟨gb, rfl⟩ : ∃ gb : ↥(AChief.nrm X₂), (gb : Γ) = g := ⟨⟨g, hgN⟩, rfl⟩
    have hgbar : AChief.qmap X₂ gb ∈ cenIn (q (X₁ ⊔ D)) (q B) := by
      rw [← S.qimg_cenIn_G]
      exact (AChief.mem_qimg_iff X₂ _ _).mpr ⟨gb, hgZD, rfl⟩
    have hgcen : AChief.qmap X₂ gb ∈ Subgroup.centralizer
        ((cenIn (q X₁) (q B) : Subgroup (AChief.QG X₂)) : Set (AChief.QG X₂)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z' hz'
      rw [← S.qimg_cenIn_X₁] at hz'
      obtain ⟨z, hz, rfl⟩ := (AChief.mem_qimg_iff X₂ _ _).mp hz'
      have h1 : (gb * z * gb⁻¹ * z⁻¹ : ↥(AChief.nrm X₂)) ∈ X₂.subgroupOf (AChief.nrm X₂) := by
        rw [Subgroup.mem_subgroupOf]
        have h2 : ⁅(gb : Γ), (z : Γ)⁆ ∈ X₂ := (Subgroup.mem_inf.mp (hgcomm z hz)).1
        simpa [commutatorElement_def] using h2
      have h3 : AChief.qmap X₂ (gb * z * gb⁻¹ * z⁻¹) = 1 := (QuotientGroup.eq_one_iff _).mpr h1
      rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h3
      exact (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h3)).symm
    have hzero : AChief.qmap X₂ gb ∈ (⊥ : Subgroup (AChief.QG X₂)) := by
      rw [← hCbot]
      exact Subgroup.mem_inf.mpr ⟨hgbar, hgcen⟩
    have hgR : (gb : Γ) ∈ X₂ :=
      Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp (Subgroup.mem_bot.mp hzero))
    exact Subgroup.mem_inf.mpr ⟨hgR, (Subgroup.mem_inf.mp hgC).2⟩
  · refine Subgroup.mem_inf.mpr ⟨(S.cenIn_X₂_le.trans le_sup_left) hg, ?_⟩
    refine mem_sectionCentralizer_iff.mpr ⟨Subgroup.le_normalizer hg,
      Subgroup.le_normalizer (S.cenIn_X₂_le hg), fun y hy => ?_⟩
    have h1 := (Subgroup.mem_normalizer_iff.mp (hZ₁nor hy) g⁻¹).mp (inv_mem hg)
    have h2 := mul_mem hg h1
    simpa [commutatorElement_def, mul_assoc] using h2

end BackSetting

end Quotient

end CFSG.SignalizerFunctorTheorem.McBride.Near.Thm32
