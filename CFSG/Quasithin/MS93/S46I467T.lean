module

public import CFSG.Quasithin.MS93.S46I467TC1
public import CFSG.Quasithin.MS93.S46I467
public import CFSG.LocalAnalysis.ComponentInitial.CommutingBlock
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldNaturalAction
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftSaturate
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalFamily
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinearStrong
public import CFSG.Quasithin.Background.SmithB42L2L32
public import CFSG.Quasithin.Background.SmithB42L2Nat
public import CFSG.Quasithin.Background.SmithB42SL3Aut

public section

namespace CFSG.Quasithin.MS93.S46.I467T

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S46.I467
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S46.I464 CFSG.Quasithin.MS93.S46.I466b
open scoped Matrix commutatorElement

section Main

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
  (h464 : ∀ δ ρ : Vtx (puAmalgam h.le), IsMVtx _ δ → (puAmalgam h.le).treeGraph.Adj δ ρ →
    Usup (puAmalgam h.le) δ ρ ≤ ZH _ ρ)
  (hsq : ∀ δ ρ : Vtx (puAmalgam h.le), IsMVtx _ δ → (puAmalgam h.le).treeGraph.Adj δ ρ →
    Nat.card ↥(Usup (puAmalgam h.le) δ ρ) = Fintype.card F ^ 2)
  (h466 : ∀ δ ρ : Vtx (puAmalgam h.le), IsMVtx _ δ → (puAmalgam h.le).treeGraph.Adj δ ρ →
    (Qv (puAmalgam h.le) δ).relIndex (Qv _ ρ) = Fintype.card F ^ 2)
  (h465 : ∀ x : Vtx (puAmalgam h.le), IsMVtx _ x →
    ⁅Vv (puAmalgam h.le) x, Qv _ x⁆ ≤ ZM _ x)
  (hV' : ∀ x : Vtx (puAmalgam h.le), IsMVtx _ x →
    ⁅Vv (puAmalgam h.le) x, Vv _ x⁆ ≤ ZM _ x)
  (hZq : ∀ x ρ : Vtx (puAmalgam h.le), IsMVtx _ x → (puAmalgam h.le).treeGraph.Adj x ρ →
    (ZH (puAmalgam h.le) ρ).relIndex (ZM _ x) = Fintype.card F)
include h

local notation "𝔛" => puAmalgam h.le
local notation "𝔘" => GoldAmalgam.Universal (puAmalgam h.le)

include hφ h464 hsq h466 h465 hV' hZq in
theorem bloc_le_centerOf_transv (hb4 : critDist (puAmalgam h.le) = 4)
    {α : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α) : Bloc h.le L α ≤ centerOf (Vv 𝔛 α) := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have h20 := h.hyp20
  have hb : 2 < critDist 𝔛 := by omega
  have hb0 : 0 < critDist 𝔛 := by omega
  by_contra hne
  obtain ⟨β, δ, hαβ, hβδ, hBQ⟩ := exists_not_bloc_le_qv h hα hne
  have hβH : ¬ IsMVtx 𝔛 β := (isMVtx_iff_of_adj _ hαβ).mp hα
  have hδ : IsMVtx 𝔛 δ := by
    have := isMVtx_iff_of_adj _ hβδ
    tauto
  have hδβ : (puAmalgam h.le).treeGraph.Adj δ β := hβδ.symm
  have hd : (puAmalgam h.le).treeGraph.dist α δ ≤ 2 := by
    have := dist_triangle 𝔛 α β δ
    rw [dist_eq_one_of_adj _ hαβ, dist_eq_one_of_adj _ hβδ] at this
    exact this
  have hBs : Bloc h.le L α ≤ stab 𝔛 α := (bloc_le_vv h α).trans
    ((vv_le_qv h hb hα).trans (qv_le_stab _ α))
  have : Finite ↥(Bloc h.le L α) := finite_of_le_stab h hα hBs
  have hBT : Bloc h.le L α ≤ Qv 𝔛 β :=
    (bloc_le_vv h α).trans ((vv_le_qv h hb hα).trans (qv_le_qv _ h20 hα hαβ))
  have hZαδ : ZM 𝔛 α ≤ Qv 𝔛 δ := zm_le_qv_of_dist_le_three hb4 hα (by omega)
  have hA2 : ∀ a ∈ Bloc h.le L α, a ^ 2 ∈ Qv 𝔛 δ := fun a ha =>
    hZαδ (sq_mem_zm_of_mem_vv h hfull (hV' α hα) (bloc_le_vv h α ha))
  have hVδs : Vv 𝔛 δ ≤ stab 𝔛 α := (vv_le_qv h hb hδ).trans ((qv_le_qv _ h20 hδ hδβ).trans
    (qv_le_stab_of_adj _ hαβ.symm))
  have hVB : ⁅Vv 𝔛 δ, Bloc h.le L α⁆ ≤ ZM 𝔛 α :=
    (Subgroup.commutator_mono hVδs le_rfl).trans (commutator_stab_bloc_le h h465 hfull hb hα)
  have hZs : ZM 𝔛 δ ≤ stab 𝔛 δ := (zm_le_qv_self _ hδ hb0).trans (qv_le_stab _ δ)
  have : Finite ↥(ZM 𝔛 δ) := finite_of_le_stab h hδ hZs
  have : Finite ↥(ZM 𝔛 α) := finite_of_le_stab h hα ((zm_le_qv_self _ hα hb0).trans
    (qv_le_stab _ α))
  have : Finite ↥(ZM 𝔛 α ⊔ ZM 𝔛 δ) := finite_of_le_stab h hδ
    (sup_le (hZαδ.trans (qv_le_stab _ δ)) hZs)
  have : Finite ↥(ZM 𝔛 α ⊓ ZM 𝔛 δ) := finite_of_le_stab h hδ (inf_le_right.trans hZs)
  have hsup : (ZM 𝔛 δ).relIndex (ZM 𝔛 α ⊔ ZM 𝔛 δ) = (ZM 𝔛 δ).relIndex (ZM 𝔛 α) := by
    have hc := card_sup_mul_card_inf_of_commute (H := ZM 𝔛 α) (K := ZM 𝔛 δ) fun a ha b hb =>
      Subgroup.mem_centralizer_iff.mp (zm_le_centralizer_qv _ h20 hδ hb) a (hZαδ ha)
    have h1 := Subgroup.relIndex_mul_card (H := ZM 𝔛 δ) (K := ZM 𝔛 α ⊔ ZM 𝔛 δ)
    have h2 := Subgroup.relIndex_mul_card (H := ZM 𝔛 δ) (K := ZM 𝔛 α)
    rw [inf_eq_left.mpr le_sup_right] at h1
    rw [inf_comm] at h2
    have hpos : 0 < Nat.card ↥(ZM 𝔛 δ) * Nat.card ↥(ZM 𝔛 α ⊓ ZM 𝔛 δ) :=
      Nat.mul_pos Nat.card_pos Nat.card_pos
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    calc (ZM 𝔛 δ).relIndex (ZM 𝔛 α ⊔ ZM 𝔛 δ) * (Nat.card ↥(ZM 𝔛 δ) *
          Nat.card ↥(ZM 𝔛 α ⊓ ZM 𝔛 δ))
        = Nat.card ↥(ZM 𝔛 α ⊔ ZM 𝔛 δ) * Nat.card ↥(ZM 𝔛 α ⊓ ZM 𝔛 δ) := by
          rw [← h1, mul_assoc]
      _ = Nat.card ↥(ZM 𝔛 α) * Nat.card ↥(ZM 𝔛 δ) := hc
      _ = _ := by rw [← h2]; ring
  have hsmall : (ZM 𝔛 δ).relIndex (⁅Vv 𝔛 δ, Bloc h.le L α⁆ ⊔ ZM 𝔛 δ) ≤ Fintype.card F := by
    calc (ZM 𝔛 δ).relIndex (⁅Vv 𝔛 δ, Bloc h.le L α⁆ ⊔ ZM 𝔛 δ)
        ≤ (ZM 𝔛 δ).relIndex (ZM 𝔛 α ⊔ ZM 𝔛 δ) :=
          Subgroup.relIndex_le_of_le_right (sup_le_sup_right hVB _) relIndex_ne_zero_of_finite
      _ = (ZM 𝔛 δ).relIndex (ZM 𝔛 α) := hsup
      _ ≤ (ZH 𝔛 β).relIndex (ZM 𝔛 α) :=
          Subgroup.relIndex_le_of_le_left (zh_le_zm _ hδβ) relIndex_ne_zero_of_finite
      _ = Fintype.card F := hZq α β hα hαβ
  have hC1 := isC1_of_transv h hφ hb hδ hδβ hBT hA2 hBQ (hV' δ hδ) (h465 δ hδ) hsmall
  have hBδ := bloc_le_vv_of_isC1 h hφ h464 hsq h466 h465 hb4 hδ hδβ hBT hBQ
    (hVB.trans (zm_le_vv_of_adj hαβ.symm hα)) hC1
  apply not_bloc_le_centerOf_of_isMVtx h hα hδ hne
  refine le_inf (bloc_le_vv h δ) ?_
  rw [Subgroup.le_centralizer_iff, vv_eq_iSup_vv hδ]
  refine iSup₂_le fun ρ hρ => ?_
  obtain ⟨k, hk, rfl⟩ := exists_mem_stab_smul_eq hδ hδβ hρ
  have hρH : ¬ IsMVtx 𝔛 (k • β) := by rwa [isMVtx_smul]
  have hBρ : Bloc h.le L δ ≤ Vv 𝔛 (k • β) := by
    rw [show Vv 𝔛 (k • β) = Vi 𝔛 (k • β) 2 from rfl, vi_smul]
    have e : (Bloc h.le L δ).map (MulAut.conj k).toMonoidHom = Bloc h.le L δ := by
      rw [← bloc_smul h k δ, (mem_stab _).mp hk]
    rw [← e]
    exact Subgroup.map_mono hBδ
  rw [Subgroup.le_centralizer_iff]
  exact hBρ.trans (vv_le_centralizer_vv h hb4 hρH)

end Main

end CFSG.Quasithin.MS93.S46.I467T

namespace CFSG.Quasithin.MS93.S46

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A

theorem i467_of_transv (h461 : I461) (h463 : I463) (h464 : I464) (h465 : I465)
    (h466a : I466a) : I467 := by
  intro G _ _ M T L F _ _ φ c α hα
  refine le_antisymm ?_ (h461 G M T L F φ c α hα)
  refine I467T.bloc_le_centerOf_transv c.pu c.via
    (fun δ ρ hδ hδρ => h464 G M T L F φ c δ ρ hδ hδρ)
    (fun δ ρ hδ hδρ => (h465 G M T L F φ c δ ρ hδ hδρ).1)
    (fun δ ρ hδ hδρ => h466a G M T L F φ c δ ρ hδ hδρ) (fun x hx => ?_)
    (fun x hx => (h463 G M T L F φ c x hx).2)
    (fun x ρ hx hxρ => (h465 G M T L F φ c x ρ hx hxρ).2.1) c.b4 hα
  obtain ⟨β, hβ⟩ := exists_adj _ x
  exact (h465 G M T L F φ c x β hx hβ).2.2

end CFSG.Quasithin.MS93.S46
