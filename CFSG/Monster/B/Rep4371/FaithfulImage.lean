
module

public import CFSG.Monster.B.Rep4371.FaithfulImageBase

public import CFSG.Monster.B.Rep4371.SmallFaithful
public import CFSG.Monster.B.Gen.PacketGeneration
public import Certificates.Certificate16021
public import CFSG.Monster.B.Gen.Max2AssemblyBase

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.VisQuot CFSG.Monster.B.Rep4371
open scoped Matrix

theorem Jbar_le_of_lifts
    {G : Subgroup Cbar}
    (hgen : ∀ i, ∃ g : Jbar, (g : Cbar) ∈ G ∧
      ((jbarToKv g : Kstab (phi0 (coordOf rStar))) : OLq) = (Co2.alpha i)⁻¹)
    (he : ∃ e : Ebar, (e : Cbar) ∈ G ∧ psiBar e ≠ 1) : Jbar ≤ G := by
  set I : Subgroup OLq :=
    ((G.subgroupOf Jbar).map jbarToKv).map (Kstab (phi0 (coordOf rStar))).subtype with hI
  have hK : Kstab (phi0 (coordOf rStar)) = Subgroup.closure (Set.range Co2.alpha) :=
    (congrArg Kstab phi0_coordOf_rStar).trans Kstab_v0_eq_closure_alpha
  have hKI : Subgroup.closure (Set.range Co2.alpha) ≤ I := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨g, hgG, hg⟩ := hgen i
    have hmem : (Co2.alpha i)⁻¹ ∈ I :=
      ⟨jbarToKv g, ⟨g, (Subgroup.mem_subgroupOf).2 hgG, rfl⟩, hg⟩
    simpa using I.inv_mem hmem
  refine Jbar_le_of_generates G (fun k => ?_) he
  have hk : (k : OLq) ∈ I := hKI (hK ▸ k.2)
  obtain ⟨k', ⟨g, hgG, rfl⟩, hk'⟩ := hk
  exact ⟨g, (Subgroup.mem_subgroupOf).1 hgG, Subtype.ext hk'⟩

theorem gramPauli_mul_self : gramPauli * gramPauli = 1 :=
  Certificates.certificate16021

theorem linearIndependent_ePauli' :
    LinearIndependent (ZMod 2) fun k => Multiplicative.toAdd (psiBar ⟨ePauli' k, ePauli'_mem_Ebar k⟩) :=
  linearIndependent_psi_of_gram ePauli' ePauli'_mem_Ebar gramPauli gramPauli gramPauli_mul_self
    ePauli'_rel

theorem Ebar_eq_closure_pauli :
    Ebar = Subgroup.closure (Set.range ePauli) := by
  set H := Subgroup.closure (Set.range ePauli)
  apply le_antisymm
  · intro e he
    set β := psiBasis ePauli' ePauli'_mem_Ebar linearIndependent_ePauli'
    set c : Fin 22 → ZMod 2 := fun k => β.repr (Multiplicative.toAdd (psiBar ⟨e, he⟩)) k
    set e' : Cbar := ((List.finRange 22).map fun k => ePauli' k ^ (c k).val).prod
    have he'H : e' ∈ H := Subgroup.list_prod_mem H fun x hx => by
      obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
      exact H.pow_mem (Subgroup.subset_closure ⟨_, rfl⟩) _
    have he'E : e' ∈ Ebar := Subgroup.list_prod_mem Ebar fun x hx => by
      obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
      exact Ebar.pow_mem (ePauli'_mem_Ebar k) _
    have hpsi : psiBar ⟨e', he'E⟩ = psiBar ⟨e, he⟩ := by
      rw [hom_eq_sum_of_eq_prod psiBar ePauli' ePauli'_mem_Ebar xbar_mem_Ebar
        ((psiBar_eq_one_iff _).2 (Or.inr rfl)) he'E c 0 (by rw [pow_zero, mul_one])]
      apply Multiplicative.toAdd.injective
      rw [toAdd_ofAdd]
      have hsum := β.sum_repr (Multiplicative.toAdd (psiBar ⟨e, he⟩))
      rw [← hsum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [psiBasis_apply]
    have hq : psiBar (⟨e', he'E⟩⁻¹ * ⟨e, he⟩) = 1 := by
      rw [map_mul, map_inv, hpsi, inv_mul_cancel]
    rcases (psiBar_eq_one_iff _).1 hq with h | h
    · have : e = e' := by
        have := congrArg Subtype.val h
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one] at this
        exact (inv_mul_eq_one.1 this).symm
      rw [this]
      exact he'H
    · have hx : e = e' * xbar := by
        have := congrArg Subtype.val h
        simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
        rw [← this, mul_inv_cancel_left]
      rw [hx]
      refine H.mul_mem he'H ?_
      rw [← ePauli_zero]
      exact Subgroup.subset_closure ⟨0, rfl⟩
  · rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ePauli_mem_Ebar i

theorem Jbar_eq_closure_47 :
    Jbar = Subgroup.closure (Set.range fun k : Fin 47 => packetElt ⟨k, by omega⟩) := by
  apply le_antisymm
  · refine Jbar_le_of_lifts (fun i => ⟨⟨kappa ⟨hElt i, hElt_mem_Cgen i⟩,
      kappa_mem_Jbar (hElt_mem_Jstar i)⟩, ?_,
      jbarToKv_kappa_hElt i (hElt_mem_Cgen i) (hElt_mem_Jstar i)⟩) ?_
    · refine Subgroup.subset_closure ⟨⟨23 + i, by omega⟩, ?_⟩
      exact packetElt_h i
    · refine ⟨⟨_, kappa_rho_mem_Ebar (qElt_mem_centralizer 1)⟩, ?_, psiBar_qElt_one_ne_one⟩
      refine Subgroup.subset_closure ⟨⟨1, by omega⟩, ?_⟩
      exact (packetElt_pauli 1).trans rfl
  · rw [Subgroup.closure_le]
    rintro _ ⟨k, rfl⟩
    exact packetElt_mem_Jbar k.2

theorem closure_packetElt :
    Subgroup.closure (Set.range packetElt) = ⊤ := by
  rw [eq_top_iff, ← closure_selGen, Subgroup.closure_le]
  rintro _ ⟨g, rfl⟩
  exact Subgroup.subset_closure ⟨_, rfl⟩

theorem rational_4371_packet_faithful_simple_image :
    Function.Injective chiMat ∧
    (∀ k : Fin 48, ((chiMat (packetElt k) : GL (Fin 4371) ℚ) :
      Matrix (Fin 4371) (Fin 4371) ℚ) = (packetN k)ᵀ) ∧
    chiMat.range = Subgroup.closure (Set.range fun k : Fin 48 => chiMat (packetElt k)) ∧
    Jbar.map chiMat = Subgroup.closure (Set.range fun k : Fin 47 => chiMat (packetElt ⟨k, by omega⟩)) ∧
    Ebar.map chiMat = Subgroup.closure (Set.range fun k : Fin 23 => chiMat (packetElt ⟨k, by omega⟩)) := by
  refine ⟨chiMat_injective, coe_chiMat_packetElt, ?_, ?_, ?_⟩
  · rw [MonoidHom.range_eq_map, ← closure_packetElt, MonoidHom.map_closure, ← Set.range_comp]
    rfl
  · rw [Jbar_eq_closure_47, MonoidHom.map_closure, ← Set.range_comp]
    rfl
  · rw [Ebar_eq_closure_pauli, MonoidHom.map_closure, ← Set.range_comp]
    refine congrArg (fun f : Fin 23 → GL (Fin 4371) ℚ => Subgroup.closure (Set.range f))
      (funext fun k => ?_)
    show chiMat (ePauli k) = chiMat (packetElt ⟨k, by omega⟩)
    rw [packetElt_pauli]

end CFSG.Monster.B
