module

public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutOddCore
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatFactsK
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatCode
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRows
public import Certificates.Data.Kernel.SporLatDcCode
public import Certificates.Data.Kernel.AutJ2Lat.Lat
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.Sporadic.J2
public import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.Quasithin.F112R.AJ2L

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm
  CFSG.ComponentClassification.J2Cover CFSG.KC.SLDc

theorem permU_mul_permA_mem : permU * permA ∈ R :=
  R.mul_mem permU_mem_R (P_le_R (Subgroup.subset_closure (Set.mem_insert _ _)))

@[expose] noncomputable def xR : R := ⟨permU * permA, permU_mul_permA_mem⟩

@[expose] noncomputable def yR : R :=
  ⟨permB, P_le_R (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))⟩


theorem sylowGen_mem {i : ℕ} (hi : i < 3) :
    CFSG.Monster.B.Co2.permOfArr 315 sylowStrong[i]! ∈ sylowS := by
  rw [sylowS, sylowChain, ofArrays_originalSubgroup]
  exact Subgroup.subset_closure ⟨i, hi, rfl⟩

@[expose] noncomputable def sgen (i : ℕ) (hi : i < 3) : R :=
  ⟨CFSG.Monster.B.Co2.permOfArr 315 sylowStrong[i]!, sylowS_le_R (sylowGen_mem hi)⟩

@[expose] noncomputable def rSg : List R :=
  [sgen 0 (by norm_num), sgen 1 (by norm_num), sgen 2 (by norm_num)]

theorem closure_rSg : Subgroup.closure {x | x ∈ rSg} = sylowS.subgroupOf R := by
  apply Subgroup.map_injective R.subtype_injective
  rw [MonoidHom.map_closure, Subgroup.map_subgroupOf_eq_of_le sylowS_le_R, sylowS, sylowChain,
    ofArrays_originalSubgroup]
  congr 1
  ext g
  simp only [Set.mem_image, Set.mem_setOf_eq, rSg, List.mem_cons, List.mem_nil_iff, or_false]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx with rfl | rfl | rfl
    · exact ⟨0, by norm_num, rfl⟩
    · exact ⟨1, by norm_num, rfl⟩
    · exact ⟨2, by norm_num, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    obtain rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    · exact ⟨_, Or.inl rfl, rfl⟩
    · exact ⟨_, Or.inr (Or.inl rfl), rfl⟩
    · exact ⟨_, Or.inr (Or.inr rfl), rfl⟩

theorem card_closure_rSg : Nat.card (Subgroup.closure {x | x ∈ rSg}) = 2 ^ 8 := by
  rw [closure_rSg, card_sylowS_subgroupOf]

@[expose] def rSets : List (List ℕ) :=
  [[82, 86], [82, 93], [86, 100], [93, 100], [67, 262], [164, 262], [67, 283], [164, 283]]

@[expose] def rDelta : List ℕ := rSets.map (encodeSet 315)

theorem rDelta_valid : CodeSetValid 315 rDelta := by
  have h : ∀ l ∈ rSets, PtValid 315 l := by decide
  refine ⟨by decide, fun c hc => ?_⟩
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hc
  exact ⟨l, h l hl, rfl⟩

@[expose] noncomputable def rLatD : LatData (List ℕ) where
  O := default
  F := default
  sTabs := genTabs 315 rSg
  mw := AutJ2Lat.RL.mw.toArray
  mt := AutJ2Lat.RL.mw.toArray.map fun ws =>
    ws.map (wordTabA #[(tab 315 xR).toArray, (tab 315 yR).toArray] 315)
  Om := #[omL (AutJ2Lat.RL.Om.getD 0 default), omL (AutJ2Lat.RL.Om.getD 1 default),
    omL (AutJ2Lat.RL.Om.getD 2 default), omL (AutJ2Lat.RL.Om.getD 3 default),
    omL (AutJ2Lat.RL.Om.getD 4 default)]
  atoms := #[]
  joins := []

end CFSG.Quasithin.F112R.AJ2L

namespace CFSG.Quasithin.F112R.AJ2L

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.KC.SLDc

@[expose] noncomputable def rOtD : Array (OmegaData (List (List ℕ))) :=
  #[omL (AutJ2Lat.RL.Ot.getD 0 default), omL (AutJ2Lat.RL.Ot.getD 1 default),
    omL (AutJ2Lat.RL.Ot.getD 2 default), omL (AutJ2Lat.RL.Ot.getD 3 default),
    omL (AutJ2Lat.RL.Ot.getD 4 default)]

@[expose] def mems : List Mem :=
  [⟨256, 256, 256⟩, ⟨2304, 64, 2304⟩, ⟨3840, 32, 3840⟩, ⟨768, 128, 768⟩, ⟨768, 128, 768⟩]

end CFSG.Quasithin.F112R.AJ2L

end
