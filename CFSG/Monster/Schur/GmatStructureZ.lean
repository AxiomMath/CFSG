module

public import CFSG.Monster.Schur.GmatStructurePhi
public import CFSG.Monster.Schur.GmatStructureMain

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Schur

open CFSG.Monster CFSG.Monster.Generated CFSG.Monster.Visible CFSG.Monster.VisQuot
  CFSG.Monster.VisCert CFSG.Monster.Spin CFSG.Monster.SpinLattice CFSG.Monster.ScalarKernel
  CFSG.Monster.Griess CFSG.Monster.B Subgroup

@[expose] def QyMat : Subgroup (SpaceB ≃ₗ[ℚ] SpaceB) := conjSub tauB Qmat

@[expose] def CyMat : Subgroup (SpaceB ≃ₗ[ℚ] SpaceB) := conjSub tauB Hmat

@[expose] def CVMat : Subgroup (SpaceB ≃ₗ[ℚ] SpaceB) := Hmat ⊓ CyMat

@[expose] def RMat : Subgroup (SpaceB ≃ₗ[ℚ] SpaceB) := QyMat ⊓ Hmat

@[expose] def PMat : Subgroup (SpaceB ≃ₗ[ℚ] SpaceB) := Qmat ⊔ CVMat

@[expose] def ZMat : Subgroup (SpaceB ≃ₗ[ℚ] SpaceB) := Qmat ⊓ QyMat

theorem QyMat_le_Gmat : QyMat ≤ Gmat :=
  mem_conjSub_of_mem tauB_mem_Gmat (Qmat_le_Hmat.trans Hmat_le_Gmat)

theorem CyMat_le_Gmat : CyMat ≤ Gmat := mem_conjSub_of_mem tauB_mem_Gmat Hmat_le_Gmat

theorem QyMat_le_CyMat : QyMat ≤ CyMat := conjSub_mono tauB Qmat_le_Hmat

theorem CVMat_le_Hmat : CVMat ≤ Hmat := inf_le_left

theorem CVMat_le_Gmat : CVMat ≤ Gmat := CVMat_le_Hmat.trans Hmat_le_Gmat

theorem RMat_le_CVMat : RMat ≤ CVMat := fun _ hr => ⟨hr.2, QyMat_le_CyMat hr.1⟩

theorem RMat_le_QyMat : RMat ≤ QyMat := inf_le_left

theorem norm_Qmat : ∀ g ∈ Hmat, ∀ a ∈ Qmat, g * a * g⁻¹ ∈ Qmat := by
  intro g hg a ha
  have h := (inferInstance : (rhoQ.subgroupOf Gvis).Normal).conj_mem ⟨a, Qmat_le_Hmat ha⟩
    (Subgroup.mem_subgroupOf.2 ha) ⟨g, hg⟩
  exact Subgroup.mem_subgroupOf.1 h

theorem QyMat_normalized : ∀ g ∈ CyMat, ∀ a ∈ QyMat, g * a * g⁻¹ ∈ QyMat :=
  conjSub_normalizes norm_Qmat

theorem Hmat_comm_xmat {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ Hmat) : g * xmat = xmat * g := by
  have h : g ∈ Gmat ⊓ Subgroup.centralizer {xmat} := by
    rw [Gmat_inf_centralizer_xmat]
    exact hg
  exact Subgroup.mem_centralizer_singleton_iff.1 h.2

theorem CyMat_comm {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ CyMat) :
    g * xmatTau = xmatTau * g := by
  have h := Hmat_comm_xmat (mem_conjSub.1 hg)
  show g * (tauB * xmat * tauB⁻¹) = (tauB * xmat * tauB⁻¹) * g
  calc g * (tauB * xmat * tauB⁻¹) = tauB * ((tauB⁻¹ * g * tauB) * xmat) * tauB⁻¹ := by group
    _ = tauB * (xmat * (tauB⁻¹ * g * tauB)) * tauB⁻¹ := by rw [h]
    _ = (tauB * xmat * tauB⁻¹) * g := by group

theorem mem_CyMat_of_comm {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ Gmat)
    (h : g * xmatTau = xmatTau * g) : g ∈ CyMat := by
  have hτ : tauB⁻¹ * g * tauB ∈ Gmat :=
    Gmat.mul_mem (Gmat.mul_mem (Gmat.inv_mem tauB_mem_Gmat) hg) tauB_mem_Gmat
  have hc : (tauB⁻¹ * g * tauB) * xmat = xmat * (tauB⁻¹ * g * tauB) := by
    have h' : g * (tauB * xmat * tauB⁻¹) = (tauB * xmat * tauB⁻¹) * g := h
    calc (tauB⁻¹ * g * tauB) * xmat = tauB⁻¹ * (g * (tauB * xmat * tauB⁻¹)) * tauB := by group
      _ = tauB⁻¹ * ((tauB * xmat * tauB⁻¹) * g) * tauB := by rw [h']
      _ = xmat * (tauB⁻¹ * g * tauB) := by group
  have : tauB⁻¹ * g * tauB ∈ Gmat ⊓ Subgroup.centralizer {xmat} :=
    ⟨hτ, Subgroup.mem_centralizer_singleton_iff.2 hc⟩
  rw [Gmat_inf_centralizer_xmat] at this
  exact mem_conjSub.2 this

theorem imPhi_CV_eq_Nvis :
    imPhi CVMat = Nvis := by
  refine le_antisymm (fun ν hν => ?_) (fun ν hν => ?_)
  · obtain ⟨g, hg, hgC, rfl⟩ := mem_imPhi.1 hν
    exact PhiV_mem_Nvis_of_comm ⟨g, hg⟩ (CyMat_comm hgC.2)
  · obtain ⟨g, rfl⟩ := exists_PhiV_eq (Nvis_le_Hvis hν)
    obtain ⟨q, hq, hqg⟩ := exists_mul_comm_of_mem_Nvis g hν
    have hqH : q ∈ Gvis := Qmat_le_Hmat hq
    have hg' : q * (g : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Gvis := Gvis.mul_mem hqH g.2
    refine mem_imPhi.2 ⟨q * g, hg', ⟨hg', mem_CyMat_of_comm
      (Hmat_le_Gmat hg') hqg⟩, ?_⟩
    have h1 : PhiV ⟨q, hqH⟩ = 1 := PhiV_eq_one_iff.2 hq
    have : (⟨q * g, hg'⟩ : Gvis) = ⟨q, hqH⟩ * g := rfl
    rw [this, map_mul, h1, one_mul]

theorem imPhi_mono {S T : Subgroup (SpaceB ≃ₗ[ℚ] SpaceB)} (h : S ≤ T) : imPhi S ≤ imPhi T := by
  intro ν hν
  obtain ⟨g, hg, hgS, hgν⟩ := mem_imPhi.1 hν
  exact mem_imPhi.2 ⟨g, hg, h hgS, hgν⟩

theorem PMat_le_Hmat : PMat ≤ Hmat := sup_le Qmat_le_Hmat CVMat_le_Hmat

theorem PMat_le_Gmat : PMat ≤ Gmat := PMat_le_Hmat.trans Hmat_le_Gmat

theorem exists_mul_of_mem_PMat {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ PMat) :
    ∃ q ∈ Qmat, ∃ c ∈ CVMat, g = q * c :=
  exists_mul_of_mem_sup (A := Qmat) (B := CVMat) (fun b hb a ha => norm_Qmat b hb.1 a ha) hg

theorem imPhi_PMat_eq_Nvis :
    imPhi PMat = Nvis := by
  refine le_antisymm (fun ν hν => ?_) (imPhi_CV_eq_Nvis ▸ imPhi_mono le_sup_right)
  obtain ⟨g, hg, hgP, rfl⟩ := mem_imPhi.1 hν
  obtain ⟨q, hq, c, hc, rfl⟩ := exists_mul_of_mem_PMat hgP
  have hcH : c ∈ Gvis := CVMat_le_Hmat hc
  have hqH : q ∈ Gvis := Qmat_le_Hmat hq
  have : (⟨q * c, hg⟩ : Gvis) = ⟨q, hqH⟩ * ⟨c, hcH⟩ := rfl
  rw [this, map_mul, PhiV_eq_one_iff.2 hq, one_mul]
  exact imPhi_CV_eq_Nvis ▸ mem_imPhi.2 ⟨c, hcH, hc, rfl⟩

theorem natCard_Qmat : Nat.card Qmat = 2 ^ 25 := by
  rw [← CFSG.Monster.Existence.natCard_rhoQvis]
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe rhoQ_le_Gvis).toEquiv).symm

instance finite_Qmat : Finite Qmat := Nat.finite_of_card_ne_zero (by rw [natCard_Qmat]; norm_num)

theorem natCard_QyMat : Nat.card QyMat = 2 ^ 25 := by
  rw [QyMat, natCard_conjSub, natCard_Qmat]

instance finite_QyMat : Finite QyMat := Nat.finite_of_card_ne_zero (by rw [natCard_QyMat]; norm_num)

theorem isExtraspecialAmbient_QyMat : IsExtraspecialAmbient QyMat xmatTau :=
  isExtraspecialAmbient_Qmat.conj tauB

theorem xmatTau2_mem_Qmat : xmatTau2 ∈ Qmat := by
  obtain ⟨-, -, -, -, -, -, -, hV, -, -, -⟩ := B.triality_four_group_spin_identification
  exact hV (mem_Vmat.2 (Or.inr (Or.inr (Or.inr rfl))))

theorem xmat_mem_QyMat : xmat ∈ QyMat := by
  rw [QyMat, mem_conjSub]
  have h : tauB⁻¹ * xmat * tauB = xmatTau2 := by
    rw [xmatTau2_eq, xmat_eq_xB]
    calc tauB⁻¹ * xB * tauB = tauB⁻¹ * (tauB * zB * tauB⁻¹) * tauB := by rw [conj_tauB_zB]
      _ = zB := by group
  rw [h]
  exact xmatTau2_mem_Qmat

theorem xmatTau_mem_QyMat : xmatTau ∈ QyMat := isExtraspecialAmbient_QyMat.mem

theorem xmat_mem_ZMat : xmat ∈ ZMat := ⟨xmat_mem_Qmat, xmat_mem_QyMat⟩

theorem xmatTau_mem_ZMat :
    xmatTau ∈ ZMat := ⟨xmatTau_mem_Qmat, xmatTau_mem_QyMat⟩

theorem QyMat_inf_centralizer_eq : QyMat ⊓ Subgroup.centralizer {xmat} = RMat := by
  ext g
  constructor
  · rintro ⟨hgQ, hgc⟩
    refine ⟨hgQ, ?_⟩
    rw [← Gmat_inf_centralizer_xmat]
    exact ⟨QyMat_le_Gmat hgQ, hgc⟩
  · rintro ⟨hgQ, hgH⟩
    refine ⟨hgQ, ?_⟩
    rw [← Gmat_inf_centralizer_xmat] at hgH
    exact hgH.2

theorem two_mul_natCard_RMat : 2 * Nat.card RMat = Nat.card QyMat := by
  have hQy := isExtraspecialAmbient_QyMat
  have hne : ∃ b ∈ QyMat, b * xmat ≠ xmat * b := by
    by_contra hcon
    push Not at hcon
    exact (hQy.center xmat xmat_mem_QyMat (fun h hh => (hcon h hh).symm)).elim
      xmat_ne_one xmat_ne_xmatTau
  have := hQy.two_mul_card_inf_centralizer le_rfl xmat_mem_QyMat hne
  rwa [QyMat_inf_centralizer_eq] at this

end CFSG.Monster.Schur
