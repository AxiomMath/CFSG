module

public import CFSG.LocalAnalysis.StandardType.FS81.RootD6ModelDefs
public import Certificates.Certificate13605
public import Certificates.Certificate13666
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs295e2
import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTBFull
import TauCeti.Algebra.Group.Subgroup.Map

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.Blueprint.Chevalley

theorem exists_conj_mem_of_elemAbelian_E7
    {E : Subgroup ↥(adjointGroup .E7 (ZMod 2))} (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 7) (t : ↥(adjointGroup .E7 (ZMod 2))) (ht : t ^ 3 = 1) :
    ∃ c : ↥(adjointGroup .E7 (ZMod 2)), c * t * c⁻¹ ∈ E := by
  have hK : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  obtain ⟨E', htE', hE'e, hcardE'⟩ :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs295e.exists_elemAbelian_E7_two hK t ht
  obtain ⟨c, hc⟩ := TableBExcTwoTB.exists_conj_frame_of_card_E7 hK hE (le_of_eq hcard.symm)
  obtain ⟨c', hc'⟩ := TableBExcTwoTB.exists_conj_frame_of_card_E7 hK hE'e (le_of_eq hcardE'.symm)
  refine ⟨c * c'⁻¹, ?_⟩
  have hEeq : E = E'.map (MulAut.conj (c * c'⁻¹)).toMonoidHom := by
    rw [hc, hc', Subgroup.map_conj_map_conj]
    rw [show (c * c'⁻¹) * c' = c by group]
  rw [hEeq]
  exact Subgroup.mem_map_of_mem _ htE'

private theorem elemAbelian_card_pullback {G : Type} [Group G] {Y E : Subgroup G}
    (ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥Y) (hEY : E ≤ Y) (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 7) :
    IsElemAbelian 3 ((E.subgroupOf Y).map ψ.symm.toMonoidHom) ∧
      Nat.card ((E.subgroupOf Y).map ψ.symm.toMonoidHom) = 3 ^ 7 := by
  refine ⟨(hE.subgroupOf Y).map ψ.symm.toMonoidHom, ?_⟩
  rw [Subgroup.card_map_of_injective ψ.symm.injective,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEY).toEquiv, hcard]

private theorem exists_conj_mem_of_pullback {G A : Type} [Group G] [Group A] {Y E : Subgroup G}
    (ψ : A ≃* ↥Y) {x : G} (hxY : x ∈ Y) {c : A}
    (hc : c * ψ.symm ⟨x, hxY⟩ * c⁻¹ ∈ (E.subgroupOf Y).map ψ.symm.toMonoidHom) :
    ∃ y ∈ Y, y * x * y⁻¹ ∈ E := by
  obtain ⟨a, ha, haeq⟩ := Subgroup.mem_map.mp hc
  have hmem : ψ (c * ψ.symm ⟨x, hxY⟩ * c⁻¹) ∈ E.subgroupOf Y := by
    rw [← haeq]
    simpa using ha
  have hconv : ψ (c * ψ.symm ⟨x, hxY⟩ * c⁻¹) = ψ c * (⟨x, hxY⟩ : ↥Y) * (ψ c)⁻¹ := by
    simp
  refine ⟨((ψ c : ↥Y) : G), (ψ c).2, ?_⟩
  have hmemG : ((ψ (c * ψ.symm ⟨x, hxY⟩ * c⁻¹) : ↥Y) : G) ∈ E := Subgroup.mem_subgroupOf.mp hmem
  rw [hconv] at hmemG
  simpa using hmemG

theorem e8TorusAt_D6_of_model
    (hM : IsEmSevenModel) :
    E8TorusAt Row.D6 := by
  intro G _ _ b₀ K E B Y h x hxY hx3
  obtain ⟨ψ⟩ := hM G Y h.isEm
  have hEcard : Nat.card E = 3 ^ 7 := by
    have h' := h.std.2.1.2.2.2.1
    rwa [show Row.D6.m = 7 from rfl] at h'
  obtain ⟨hE'ea, hE'card⟩ := elemAbelian_card_pullback ψ h.torus_le h.std.2.1.2.1.2.1 hEcard
  have hx3Y : (⟨x, hxY⟩ : ↥Y) ^ 3 = 1 := by
    have hx3' : x ^ 3 = 1 := by rw [← hx3]; exact pow_orderOf_eq_one x
    exact Subtype.ext (by simpa using hx3')
  have ht : (ψ.symm ⟨x, hxY⟩) ^ 3 = 1 := by
    rw [← map_pow, hx3Y, map_one]
  obtain ⟨c, hc⟩ := exists_conj_mem_of_elemAbelian_E7 hE'ea hE'card _ ht
  exact exists_conj_mem_of_pullback ψ hxY hc

end CFSG.StandardType.FrameRoute.FS81
