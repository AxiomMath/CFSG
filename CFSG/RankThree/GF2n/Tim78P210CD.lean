module

public import CFSG.RankThree.GF2n.Tim78P210Main
public import CFSG.RankThree.GF2n.DecompSetupSz
public import CFSG.RankThree.GF2n.DecompSetupSplit
public import CFSG.CGT.Timmesfeld75.L2Basic
public import Certificates.Certificate100
public import Certificates.Certificate101
public import Certificates.Certificate102
public import Certificates.Certificate103
public import Certificates.Certificate104
public import Certificates.Certificate105
public import Certificates.Certificate106
public import Certificates.Certificate107
public import Certificates.Certificate108
public import Certificates.Certificate109
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate43
public import Certificates.Certificate82
public import Certificates.Certificate83
public import Certificates.Certificate84
public import Certificates.Certificate85
public import Certificates.Certificate86
public import Certificates.Certificate87
public import Certificates.Certificate88
public import Certificates.Certificate89
public import Certificates.Certificate90
public import Certificates.Certificate91
public import Certificates.Certificate92
public import Certificates.Certificate93
public import Certificates.Certificate94
public import Certificates.Certificate95
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG.CGT.Timmesfeld75 CFSG.Open Matrix CFSG.Timmesfeld CFSG.Timmesfeld.RankOne
open CFSG.Timmesfeld.ARS.NaturalModule
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

namespace QData

variable {B₀ B₁ : Subgroup G} (D : QData B₀ B₁ B₀ B₁)
include D

theorem commutator_mem_F₀ {y m : G} (hy : y ∈ B₀) (hm : m ∈ nrm B₀ B₁ ⊔ nrm B₁ B₀) :
    y * m * y⁻¹ * m⁻¹ ∈ nrm B₀ B₁ := by
  obtain ⟨l, hl, lb, hlb, rfl⟩ := D.exists_mul_of_mem_Q hm
  have hc := D.conj_F₁_mem hy hlb
  have hyl : y * l = l * y := D.setup.comm _ hy _ (mem_nrm.mp hl).1
  have hlc : l * (y * lb * y⁻¹ * lb⁻¹) = (y * lb * y⁻¹ * lb⁻¹) * l :=
    D.setup.comm _ (mem_nrm.mp hl).1 _ (mem_nrm.mp hc).1
  have e : y * (l * lb) * y⁻¹ * (l * lb)⁻¹ = y * lb * y⁻¹ * lb⁻¹ := by
    calc y * (l * lb) * y⁻¹ * (l * lb)⁻¹ = (y * l) * lb * y⁻¹ * lb⁻¹ * l⁻¹ := by group
      _ = l * (y * lb * y⁻¹ * lb⁻¹) * l⁻¹ := by rw [hyl]; group
      _ = y * lb * y⁻¹ * lb⁻¹ := by rw [hlc, mul_inv_cancel_right]
  rw [e]
  exact hc

theorem decompSetup :
    DecompSetup B₀ B₁ (nrm B₀ B₁) (nrm B₁ B₀) (nrm B₀ B₁ ⊔ nrm B₁ B₀) where
  comm_A := D.setup.comm
  comm_Ab := D.setup.comm₁
  L_le := inf_le_left
  Lb_le := inf_le_left
  ne := fun h => by
    obtain ⟨z, hz, hzF⟩ := D.neA₀
    exact hzF (by rw [h]; exact hz)
  Lb_ne := fun h => by
    obtain ⟨z, hz, hzF⟩ := D.neA₁
    exact hzF (by rw [h]; exact hz)
  L_le_M := le_sup_left
  Lb_le_M := le_sup_right
  sq_A := fun x hx => ((D.memA₀ x).mp hx).2
  sq_Ab := fun x hx => ((D.memA₁ x).mp hx).2
  comm_M := fun _ hx _ hy => D.comm_Q hx hy
  sq_M := fun _ hx => D.sq_Q hx
  exists_mul := fun _ hm => D.exists_mul_of_mem_Q hm
  A_le_normalizer := D.A₀_le_normalizer_Q
  Ab_le_normalizer := by
    have := D.symm.A₀_le_normalizer_Q
    rwa [sup_comm] at this
  comm_L := fun _ hy _ hm => D.commutator_mem_F₀ hy hm
  comm_Lb := fun _ hy _ hm => D.symm.commutator_mem_F₀ hy (by rwa [sup_comm])
  cent := fun _ ha haL _ hm hma => D.mem_F_of_commute ha haL hm hma
  cent_b := fun _ hb hbL _ hm hmb => D.symm.mem_F_of_commute hb hbL (by rwa [sup_comm]) hmb
  inf := D.setup.inf_eq_bot D.ne
  card := by
    obtain ⟨g, hg⟩ := D.setup.conj
    rw [hg, card_conjSubgroup]

end QData

namespace Setup210

variable {B₀ B₁ : Subgroup G} (S : Setup210 B₀ B₁)
include S

theorem invol_of_not_comm (hnc : ¬ ∀ a ∈ B₀, ∀ b ∈ B₁, a * b = b * a) :
    B₀ ≠ B₁ ∧ (∀ x ∈ nrm B₀ B₁, x * x = 1) ∧ (∀ x ∈ nrm B₁ B₀, x * x = 1) := by
  refine ⟨fun h => hnc (by subst h; exact S.comm), fun x hx => ?_, fun x hx => ?_⟩
  · by_contra hx2
    exact hnc (S.commutes_of_sq_ne_one hx hx2)
  · by_contra hx2
    exact hnc fun a ha b hb => (S.symm.commutes_of_sq_ne_one hx hx2 b hb a ha).symm

end Setup210

omit [Finite G] in
theorem comm_sup {B₀ B₁ : Subgroup G} (h0 : ∀ x ∈ B₀, ∀ y ∈ B₀, x * y = y * x)
    (h1 : ∀ x ∈ B₁, ∀ y ∈ B₁, x * y = y * x) (h01 : ∀ a ∈ B₀, ∀ b ∈ B₁, a * b = b * a) :
    ∀ x ∈ B₀ ⊔ B₁, ∀ y ∈ B₀ ⊔ B₁, x * y = y * x := by
  have hc0 : B₀ ⊔ B₁ ≤ Subgroup.centralizer (B₀ : Set G) := sup_le
    (fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => h0 y hy x hx)
    (fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => h01 y hy x hx)
  have hc1 : B₀ ⊔ B₁ ≤ Subgroup.centralizer (B₁ : Set G) := sup_le
    (fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => (h01 x hx y hy).symm)
    (fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => h1 y hy x hx)
  have hc : B₀ ⊔ B₁ ≤ Subgroup.centralizer ((B₀ ⊔ B₁ : Subgroup G) : Set G) := by
    refine sup_le (fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => ?_)
      (fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => ?_)
    · exact (Subgroup.mem_centralizer_iff.mp (hc0 hy) x hx).symm
    · exact (Subgroup.mem_centralizer_iff.mp (hc1 hy) x hx).symm
  intro x hx y hy
  exact (Subgroup.mem_centralizer_iff.mp (hc hy) x hx)

theorem tim78_2_10_d (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    {B₀ B₁ : Subgroup G} (S : Setup210 B₀ B₁) (hexp : ∀ x ∈ B₀, x ^ 4 = 1)
    [((PartTwo.omegaOneSub B₀ ⊔ PartTwo.omegaOneSub B₁).subgroupOf (B₀ ⊔ B₁)).Normal]
    {f : ℕ} (hf : 3 ≤ f)
    (e : ↥(B₀ ⊔ B₁) ⧸ (PartTwo.omegaOneSub B₀ ⊔ PartTwo.omegaOneSub B₁).subgroupOf (B₀ ⊔ B₁) ≃*
      PSL(2, GaloisField 2 f)) (X₁ : Subgroup ↥(B₀ ⊔ B₁)) :
    ¬ Subgroup.IsComplement'
      ((PartTwo.omegaOneSub B₀ ⊔ PartTwo.omegaOneSub B₁).subgroupOf (B₀ ⊔ B₁)) X₁ := by
  have hnc : ¬ ∀ a ∈ B₀, ∀ b ∈ B₁, a * b = b * a := by
    intro hc
    have hX := comm_sup S.comm S.comm₁ hc
    have hs : Function.Surjective fun x : ↥(B₀ ⊔ B₁) =>
        (e.trans pslMulEquivSL) (QuotientGroup.mk' _ x) :=
      (e.trans pslMulEquivSL).surjective.comp (QuotientGroup.mk'_surjective _)
    obtain ⟨x, hx⟩ := hs (upperElt (GaloisField 2 f) 1)
    obtain ⟨x', hx'⟩ := hs (lowerElt (GaloisField 2 f) 1)
    have hxx : x * x' = x' * x := Subtype.ext (hX x x.2 x' x'.2)
    have key : upperElt (GaloisField 2 f) 1 * lowerElt (GaloisField 2 f) 1 =
        lowerElt (GaloisField 2 f) 1 * upperElt (GaloisField 2 f) 1 := by
      rw [← hx, ← hx', ← map_mul, ← map_mul, ← map_mul, ← map_mul, hxx]
    have h00 := congrArg
      (fun g : SL(2, GaloisField 2 f) => (g : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) 0 0) key
    simp [Matrix.SpecialLinearGroup.coe_mul, coe_upperElt, coe_lowerElt, Matrix.mul_apply,
      Fin.sum_univ_two] at h00
  obtain ⟨hne, h0, h1⟩ := S.invol_of_not_comm hnc
  have D := S.qdata_full hCen hU hexp hne h0 h1
  have hF0 := S.nrm_eq_omega hCen hU hne h0 h1
  have hF1 := S.symm.nrm_eq_omega hCen hU (Ne.symm hne) h1 h0
  have hN := D.normal_Q
  have hNe : (nrm B₀ B₁ ⊔ nrm B₁ B₀).subgroupOf (B₀ ⊔ B₁) =
      (PartTwo.omegaOneSub B₀ ⊔ PartTwo.omegaOneSub B₁).subgroupOf (B₀ ⊔ B₁) := by
    rw [hF0, hF1]
  have hL : ∀ y ∈ B₀, y * y = 1 → y ∈ nrm B₀ B₁ := fun y hy hyy => by
    rw [hF0]
    exact S.mem_L₀.mpr ⟨hy, hyy⟩
  have h := D.decompSetup.not_isComplement' D.quotPair hf
    ((QuotientGroup.quotientMulEquivOfEq hNe).trans e) S.ti hL X₁
  rwa [hNe] at h

end CFSG.RankThree.GF2n.Tim78
