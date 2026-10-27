module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.Hss113Core
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.StepA
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S42

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F53Mod Equiv

namespace F53.Stellmacher

open CosetGeom

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem hss113_ordered (hA : F53Amalgam H M S) {e e' : Geo H M} (hbe : bAt e = bMin H M)
    (hZ' : Zv e' ≤ stab e) (hn : ¬ Zv e ≤ Qv e') (hn' : ¬ Zv e' ≤ Qv e)
    (hle : (Zv e ⊓ Qv e').relIndex (Zv e) ≤ (Zv e' ⊓ Qv e).relIndex (Zv e')) :
    (Zv e ⊓ Qv e').relIndex (Zv e) = (Zv e' ⊓ Qv e).relIndex (Zv e') ∧
      (vtype e = false →
        IsNatSec (stab e) (Zv e ⊓ Subgroup.centralizer (oTwoRes (stab e) : Set G)) (Zv e) ∨
          IsOrthSec (stab e) (Zv e ⊓ Subgroup.centralizer (oTwoRes (stab e) : Set G)) (Zv e)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, ψ, hn5, hsurj, hker⟩ := exists_quotHom hA e
  rcases hn5 with ⟨rfl, hv⟩ | ⟨rfl, hv⟩
  ·
    have hC : stab e ⊓ Subgroup.centralizer (Zv e : Set G) = pCoreOf 2 (stab e) :=
      centralizer_Zv_eq_Qv_of_bAt hA hbe
    obtain ⟨h1, h2⟩ := hss113_core (X := stab e) (Z := Zv e) (Y := Zv e') (Q' := Qv e') ψ hsurj hker
      (isElemAbelian_Zv hA e) (stab_le_normalizer_Zv hA e) hC hZ' (isElemAbelian_Zv hA e')
      (fun y hy q hq => ((Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA e' hy).2) q hq).symm)
      hn' hle
    exact ⟨le_antisymm hle h1, fun _ => h2⟩
  ·
    have hZ2 : IsPGroup 2 (Zv e') := (CFSG.LieType.BorelTits.pCoreOf_isPGroup (G := G) (r := 2) (stab e')).to_le (Zv_le_Qv hA e')
    have hcard : Nat.card (((Zv e').subgroupOf (stab e)).map ψ) = (Zv e' ⊓ Qv e).relIndex (Zv e') := by
      rw [card_map_subgroupOf_eq_relIndex ψ hker hZ', Subgroup.inf_relIndex_left]
    have ha'le : (Zv e' ⊓ Qv e).relIndex (Zv e') ≤ 2 := by
      rw [← hcard]
      exact perm3_card_le_two_of_isPGroup _ (isPGroup_map_subgroupOf ψ hZ2)
    have ha1 : (Zv e ⊓ Qv e').relIndex (Zv e) ≠ 1 := by
      rw [Ne, Subgroup.relIndex_eq_one]
      intro h; exact hn (h.trans inf_le_right)
    have ha0 : (Zv e ⊓ Qv e').relIndex (Zv e) ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
    refine ⟨by omega, fun h => ?_⟩
    simp [hv] at h

theorem hss113_data (hA : F53Amalgam H M S) {δ δ' : Geo H M} (hcp : IsCritPair₁ δ δ')
    (hcomm : ⁅Zv δ, Zv δ'⁆ ≠ ⊥) :
    bAt δ = bMin H M ∧ bAt δ' = bMin H M ∧ Zv δ' ≤ stab δ ∧ Zv δ ≤ stab δ' ∧
      ¬ Zv δ ≤ Qv δ' ∧ ¬ Zv δ' ≤ Qv δ := by
  obtain ⟨hbδ, hbδ'⟩ := crit_bAt_eq hA hcp hcomm
  refine ⟨hbδ, hbδ', Zv_le_stab_of_dist_le hA ?_, Zv_le_stab_of_dist_le hA ?_, hcp.1,
    not_le_Qv_of_comm_ne hA hcomm⟩
  · rw [CosetGeom.dist_comm, hcp.2, hbδ']
  · rw [hcp.2, hbδ]

theorem hss113aAt_of (hA : F53Amalgam H M S) : Hss113aAt H M := by
  intro δ δ' hcp hcomm
  obtain ⟨hbδ, hbδ', hZ', hZ, hn, hn'⟩ := hss113_data hA hcp hcomm
  rcases le_total ((Zv δ ⊓ Qv δ').relIndex (Zv δ)) ((Zv δ' ⊓ Qv δ).relIndex (Zv δ')) with h | h
  · exact (hss113_ordered hA hbδ hZ' hn hn' h).1
  · exact (hss113_ordered hA hbδ' hZ hn' hn h).1.symm

theorem hss113cAt_of (hA : F53Amalgam H M S) : Hss113cAt H M := by
  intro δ δ' hcp hcomm hv
  obtain ⟨hbδ, -, hZ', -, hn, hn'⟩ := hss113_data hA hcp hcomm
  exact (hss113_ordered hA hbδ hZ' hn hn' (hss113aAt_of hA δ δ' hcp hcomm).le).2 hv

end F53.Stellmacher

end CFSG.Quasithin
