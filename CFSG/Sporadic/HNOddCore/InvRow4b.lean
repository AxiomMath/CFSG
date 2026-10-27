
module

public import CFSG.Sporadic.HNOddCore.InvRow4bBase

public import CFSG.Sporadic.HNOddCore.InvRow4
public import CFSG.Sporadic.HNOddCore.DCheckInputs
public import CFSG.Sporadic.HNOddCore.NatCheckInputs
public meta import CFSG.Sporadic.HNOddCore.InvData
public meta import CFSG.Sporadic.HNSchreier.LocalCheck
public import CFSG.Sporadic.HNOddCore.SCheckInputs
public import CFSG.Sporadic.HNOddCore.XCheckInputs
public meta import CFSG.Sporadic.HNOddCore.CCheck
public meta import CFSG.Sporadic.HNOddCore.InvArrays
public meta import Certificates.Data.CFSGNative.ONSchreier.Tools
public import CFSG.Sporadic.HNSchreier.ChainCheckInputs
public import CFSG.Sporadic.HNSchreier.LevelInputs
public meta import CFSG.Sporadic.HNSchreier.OrbitCheck
public meta import Certificates.Data.CFSGNative.ONSchreier.Vectors
public import CFSG.Sporadic.HNSchreier.InvolCheckInputs
public meta import CFSG.Sporadic.HNSchreier.SeedsCheck
public import CFSG.Sporadic.HNSchreier.LocalCheckInputs
public meta import CFSG.Sporadic.HNSchreier.PrimCheck
public meta import CFSG.Sporadic.HNSchreier.LocalData
public meta import CFSG.Sporadic.HNSchreier.MaskCheck
public import CFSG.Sporadic.HNSchreier.OrbitCheckInputs
public import CFSG.Sporadic.HNSchreier.PrimCheckInputs
public meta import Certificates.Data.CFSGNative.Perm.Chain
public import CFSG.Sporadic.HNSchreier.VectorData

public noncomputable section

namespace CFSG.Sporadic.HNOddCore

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier
open CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore.Native Equiv

theorem fix_t4_set :
    {x : X | jR t4J • x = x} = Set.range hF4.pt := by
  ext x
  exact fix_t4 x

theorem orbit_S4 :
    MulAction.orbit S4 x0 = {x : X | jR t4J • x = x} := by
  have hc := orbit4_parts.1
  unfold orbitOK at hc
  have h := orbit_eq_of_cert hF4 hact4 hc
  dsimp only at h
  rw [PtList.range_eq_univ _ (orbit4_parts.2.trans data_parts.2.1.symm), Set.image_univ,
    ← fix_t4_set] at h
  have hx0 : x0 ∈ {x : X | jR t4J • x = x} := x0_fix_t4
  rw [← h] at hx0
  exact (MulAction.orbit_eq_iff.2 hx0).trans h

theorem card_K4 :
    Nat.card K4 = 4608 := by
  rw [card_closure_eq_nat (fun s : Fin InvData.c4Nat.size => c4G s) (fun s => c4G_mem_HJ s)]
  have hO : ∀ k < (natArrs InvData.c4Nat).size,
      PRep 12 (natArrs InvData.c4Nat)[k]! (thetaJ ⟨c4G k, c4G_mem_HJ k⟩ : Perm (Fin 12)) := by
    intro k hk
    have hk' : k < 9 := by simpa [natArrs, c4Nat_size] using hk
    have := nat_c4G hk'
    rwa [natArrs, getElem!_pos _ k (by simpa [natArrs] using hk), Array.getElem_map,
      ← getElem!_pos InvData.c4Nat k (by rw [c4Nat_size]; exact hk')]
  have h1 := arrGen_eq hO
  have h2 : Set.range (fun s : Fin InvData.c4Nat.size =>
      (thetaJ ⟨c4G s, c4G_mem_HJ s⟩ : Perm (Fin 12))) =
      Set.range (fun k : Fin (natArrs InvData.c4Nat).size =>
        (thetaJ ⟨c4G k, c4G_mem_HJ k⟩ : Perm (Fin 12))) := by
    rw [range_fin_eq (fun k => (thetaJ ⟨c4G k, c4G_mem_HJ k⟩ : Perm (Fin 12))),
      range_fin_eq (fun k => (thetaJ ⟨c4G k, c4G_mem_HJ k⟩ : Perm (Fin 12)))]
    congr 2
    simp [natArrs]
  rw [h2, ← h1]
  have hc := natChain_cert
  unfold natChainChecks at hc
  simp only [Bool.and_eq_true] at hc
  rw [card_arrGen_of_chainCheck (by norm_num) (List.nodup_finRange 12) hc.1.1.2]
  decide

theorem K4_le_S4 :
    K4 ≤ S4 := by
  rw [Subgroup.closure_le]
  rintro _ ⟨s, rfl⟩
  have hs : (s : ℕ) < 9 := by rw [← c4Nat_size]; exact s.2
  refine Subgroup.subset_closure ⟨⟨s, by rw [s4J_size]; omega⟩, ?_⟩
  show g4 s = c4G s
  exact ite_eq_left hs

theorem CH_t4_eq :
    (Subgroup.centralizer {t4J} ⊓ HJ : Subgroup JH) = K4 ∧
    S4 ⊓ HJ = K4 := by
  have h1 : K4 ≤ S4 ⊓ HJ := le_inf K4_le_S4 K4_le_HJ
  have h2 : S4 ⊓ HJ ≤ Subgroup.centralizer {t4J} ⊓ HJ := inf_le_inf_right _ S4_le
  have h3 : Nat.card (Subgroup.centralizer {t4J} ⊓ HJ : Subgroup JH) ≤ Nat.card K4 := by
    rw [card_K4]
    exact card_CH_t4_le
  have e1 : K4 = Subgroup.centralizer {t4J} ⊓ HJ :=
    Subgroup.eq_of_le_of_card_ge (h1.trans h2) h3
  refine ⟨e1.symm, le_antisymm ?_ h1⟩
  rw [e1]
  exact h2

theorem card_S4 :
    Nat.card S4 = 3686400 := by
  rw [card_eq_orbit_mul, orbit_S4, CH_t4_eq.2, card_K4]
  rw [show {x : X | jR t4J • x = x}.ncard = 800 by
    rw [← Nat.card_coe_set_eq]; exact card_fix_t4]

theorem CJ_t4_eq :
    S4 = Subgroup.centralizer {t4J} := by
  apply Subgroup.eq_of_le_of_card_ge S4_le
  rw [card_S4, card_eq_orbit_mul, CH_t4_eq.1, card_K4]
  have hsub : MulAction.orbit (Subgroup.centralizer {t4J}) x0 ⊆ {x : X | jR t4J • x = x} := by
    rintro _ ⟨g, rfl⟩
    exact fix_t4_smul ((Subgroup.mem_centralizer_singleton_iff (g := t4J) (k := (g : JH))).1
      g.2) x0_fix_t4
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [show {x : X | jR t4J • x = x}.ncard = 800 by
    rw [← Nat.card_coe_set_eq]; exact card_fix_t4] at hle
  have : (MulAction.orbit (Subgroup.centralizer {t4J}) x0).ncard * 4608 ≤ 800 * 4608 :=
    Nat.mul_le_mul_right _ hle
  omega

theorem card_CJ_t4 :
    Nat.card (Subgroup.centralizer {t4J}) = 3686400 := by
  rw [← CJ_t4_eq, card_S4]

theorem card_CR_t4 :
    Nat.card (Subgroup.centralizer {jR t4J}) = 7372800 := by
  rw [card_of_split mem_centralizer_t4_iff, card_CJ_t4]

end CFSG.Sporadic.HNOddCore
