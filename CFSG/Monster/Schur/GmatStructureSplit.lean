module

public import CFSG.Monster.Schur.GmatStructureCard

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Schur

open CFSG.Monster CFSG.Monster.Generated CFSG.Monster.Visible CFSG.Monster.VisQuot
  CFSG.Monster.VisCert CFSG.Monster.Spin CFSG.Monster.SpinLattice CFSG.Monster.ScalarKernel
  CFSG.Monster.Griess CFSG.Monster.B Subgroup

theorem perfect_of_simple_of_card {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (h : 2 ∣ Nat.card G) (h2 : Nat.card G ≠ 2) : Group.IsPerfect G := by
  refine ⟨?_⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with hb | ht
  · exfalso
    have hcomm : IsMulCommutative G := (commutator_eq_bot_iff G).1 hb
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 2 h
    have hN : (zpowers g).Normal := ⟨fun x hx h => by
      have : h * x * h⁻¹ = x := by rw [mul_comm' h x, mul_inv_cancel_right]
      rw [this]
      exact hx⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (zpowers g) with h1 | h1
    · have : g = 1 := by
        have hg1 : g ∈ zpowers g := mem_zpowers g
        rw [h1] at hg1
        exact Subgroup.mem_bot.1 hg1
      rw [this, orderOf_one] at hg
      omega
    · apply h2
      rw [← Nat.card_zpowers, h1, Subgroup.card_top] at hg
      exact hg.symm ▸ rfl
  · exact ht

theorem perfect_AutPerm :
    Group.IsPerfect CFSG.Monster.Code.AutPerm := by
  have := CFSG.Monster.Code.AutPerm_isSimpleGroup
  have : Finite CFSG.Monster.Code.AutPerm :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Monster.Code.card_AutPerm]; norm_num)
  refine perfect_of_simple_of_card ?_ ?_ <;> rw [CFSG.Monster.Code.card_AutPerm] <;> norm_num

theorem W3_of
    (hE : Evis ⊓ Subgroup.centralizer (Nvis : Set GLV) = ⊥) :
    ∀ r ∈ QyMat ⊓ Hmat, (∀ g ∈ Hmat ⊓ CyMat, r⁻¹ * (g * r * g⁻¹) ∈ Qmat) → r ∈ Qmat := by
  intro r hr hcomm
  have hrH : r ∈ Gvis := hr.2
  have hrE : PhiV ⟨r, hrH⟩ ∈ Evis := imPhi_RMat_le_Evis (mem_imPhi.2 ⟨r, hrH, hr, rfl⟩)
  have hcent : PhiV ⟨r, hrH⟩ ∈ Subgroup.centralizer (Nvis : Set GLV) := by
    refine Subgroup.mem_centralizer_iff.2 fun ν hν => ?_
    rw [← imPhi_CV_eq_Nvis] at hν
    obtain ⟨g, hg, hgC, rfl⟩ := mem_imPhi.1 hν
    have h1 : r⁻¹ * (g * r * g⁻¹) ∈ Gvis :=
      Gvis.mul_mem (Gvis.inv_mem hrH) (Gvis.mul_mem (Gvis.mul_mem hg hrH) (Gvis.inv_mem hg))
    have h2 : PhiV ⟨r⁻¹ * (g * r * g⁻¹), h1⟩ = 1 := PhiV_eq_one_iff.2 (hcomm g hgC)
    have h3 : (⟨r⁻¹ * (g * r * g⁻¹), h1⟩ : Gvis) = ⟨r, hrH⟩⁻¹ * (⟨g, hg⟩ * ⟨r, hrH⟩ * ⟨g, hg⟩⁻¹) :=
      rfl
    rw [h3, map_mul, map_mul, map_mul, map_inv, map_inv, inv_mul_eq_one] at h2
    exact (eq_mul_inv_iff_mul_eq.1 h2).symm
  have hbot : PhiV ⟨r, hrH⟩ ∈ (⊥ : Subgroup GLV) := hE ▸ ⟨hrE, hcent⟩
  exact PhiV_eq_one_iff.1 (Subgroup.mem_bot.1 hbot)

theorem PMat_le_Gvis : PMat ≤ Gvis := PMat_le_Hmat

theorem PhiV_mem_Nvis_of_mem_PMat
    (g : PMat) :
    PhiV (Subgroup.inclusion PMat_le_Gvis g) ∈ Nvis :=
  imPhi_PMat_eq_Nvis ▸ mem_imPhi.2 ⟨g.1, PMat_le_Gvis g.2, g.2, rfl⟩

@[expose] def PhiP :
    PMat →* Nvis :=
  (PhiV.comp (Subgroup.inclusion PMat_le_Gvis)).codRestrict Nvis PhiV_mem_Nvis_of_mem_PMat

theorem coe_PhiP
    (g : PMat) : ((PhiP g : Nvis) : GLV) = PhiV (Subgroup.inclusion PMat_le_Gvis g) :=
  rfl

theorem PhiP_surjective :
    Function.Surjective PhiP := by
  intro ν
  have hν : (ν : GLV) ∈ imPhi PMat := by
    rw [imPhi_PMat_eq_Nvis]
    exact ν.2
  obtain ⟨g, hg, hgP, hgν⟩ := mem_imPhi.1 hν
  exact ⟨⟨g, hgP⟩, Subtype.ext hgν⟩

@[expose] def psiP :
    PMat →* CFSG.Monster.Code.AutPerm := NvisToAutPerm.comp PhiP

theorem psiP_surjective :
    Function.Surjective psiP :=
  NvisToAutPerm_surjective.comp PhiP_surjective

theorem ker_psiP :
    psiP.ker = (Qmat ⊔ RMat).subgroupOf PMat := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  have h1 : psiP g = 1 ↔ ((PhiP g : Nvis) : GLV) ∈ Evis := by
    rw [psiP, MonoidHom.comp_apply, ← MonoidHom.mem_ker, ker_NvisToAutPerm,
      Subgroup.mem_subgroupOf]
  rw [h1, coe_PhiP]
  have hgH : g.1 ∈ Gvis := PMat_le_Gvis g.2
  have e : Subgroup.inclusion PMat_le_Gvis g = ⟨g.1, hgH⟩ := rfl
  rw [e]
  constructor
  · intro hE
    rw [← imPhi_RMat_eq_Evis] at hE
    obtain ⟨r, hrH, hrR, hrg⟩ := mem_imPhi.1 hE
    have hq : r⁻¹ * g.1 ∈ Qmat := by
      have h2 : PhiV (⟨r, hrH⟩⁻¹ * ⟨g.1, hgH⟩) = 1 := by
        rw [map_mul, map_inv, hrg, inv_mul_cancel]
      exact PhiV_eq_one_iff.1 h2
    have : g.1 = r * (r⁻¹ * g.1) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hrR) (Subgroup.mem_sup_left hq)
  · intro hmem
    obtain ⟨q, hq, r, hr, hqr⟩ := exists_mul_of_mem_sup (A := Qmat) (B := RMat)
      (fun b hb a ha => norm_Qmat b hb.2 a ha) hmem
    have hqH : q ∈ Gvis := Qmat_le_Hmat hq
    have hrH : r ∈ Gvis := hr.2
    have : (⟨g.1, hgH⟩ : Gvis) = ⟨q, hqH⟩ * ⟨r, hrH⟩ := Subtype.ext hqr
    rw [this, map_mul, PhiV_eq_one_iff.2 hq, one_mul]
    exact imPhi_RMat_le_Evis (mem_imPhi.2 ⟨r, hrH, hr, rfl⟩)

end CFSG.Monster.Schur
