module

public import CFSG.Quasithin.Recognition.Stroth.Str83G4CaseADefs

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Quasithin.F112R

variable {G : Type} [Group G] {L1 L2 S : Subgroup G}

private theorem iSup_nbrs_smul {H : f112Gamma L1 L2 S → Subgroup (f112Amalgam L1 L2 S).Ghat}
    (hH : ∀ (g : f112Acting L1 L2 S) (w : f112Gamma L1 L2 S),
      H (g • w) = conjSub (g : (f112Amalgam L1 L2 S).Ghat) (H w))
    (g : f112Acting L1 L2 S) (v : f112Gamma L1 L2 S) :
    (⨆ (w : f112Gamma L1 L2 S) (_ : w ∈ CosetGeom.nbrs (g • v)), H w) =
      conjSub (g : (f112Amalgam L1 L2 S).Ghat)
        (⨆ (w : f112Gamma L1 L2 S) (_ : w ∈ CosetGeom.nbrs v), H w) := by
  simp_rw [conjSub_iSup]
  refine le_antisymm (iSup₂_le fun w hw => ?_) (iSup₂_le fun w hw => ?_)
  · have hw' : g⁻¹ • w ∈ CosetGeom.nbrs v := by
      have := (CosetGeom.smul_adj g⁻¹).mpr hw
      simpa [CosetGeom.nbrs] using this
    have hHw : H w = conjSub (g : (f112Amalgam L1 L2 S).Ghat) (H (g⁻¹ • w)) := by
      have := hH g (g⁻¹ • w)
      simpa using this
    rw [hHw]
    exact le_iSup₂ (f := fun w (_ : w ∈ CosetGeom.nbrs v) =>
      conjSub (g : (f112Amalgam L1 L2 S).Ghat) (H w)) (g⁻¹ • w) hw'
  · have hgw : g • w ∈ CosetGeom.nbrs (g • v) := by
      simpa [CosetGeom.nbrs] using (CosetGeom.smul_adj g).mpr hw
    rw [← hH g w]
    exact le_iSup₂ (f := fun w (_ : w ∈ CosetGeom.nbrs (g • v)) => H w) (g • w) hgw

theorem caseA_Qy_smul (g : f112Acting L1 L2 S) (v : f112Gamma L1 L2 S) :
    CosetGeom.Qy (g • v) = conjSub (g : (f112Amalgam L1 L2 S).Ghat) (CosetGeom.Qy v) := by
  unfold CosetGeom.Qy
  rw [CosetGeom.stab_smul]
  exact CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2
    (MulAut.conj (g : (f112Amalgam L1 L2 S).Ghat)) (CosetGeom.stab v)

theorem caseA_Z_smul (g : f112Acting L1 L2 S) (v : f112Gamma L1 L2 S) :
    caseAZ (g • v) = conjSub (g : (f112Amalgam L1 L2 S).Ghat) (caseAZ v) := by
  unfold caseAZ
  rw [caseA_Qy_smul]
  exact (CFSG.Quasithin.omegaOneCenterOf_map_mulEquiv
    (MulAut.conj (g : (f112Amalgam L1 L2 S).Ghat)) (CosetGeom.Qy v)).symm

theorem caseA_X_smul (g : f112Acting L1 L2 S) (v : f112Gamma L1 L2 S) :
    caseAX (g • v) = conjSub (g : (f112Amalgam L1 L2 S).Ghat) (caseAX v) := by
  unfold caseAX
  exact iSup_nbrs_smul (fun g w => caseA_Z_smul g w) g v

theorem caseA_R_smul (g : f112Acting L1 L2 S) (v : f112Gamma L1 L2 S) :
    caseAR (g • v) = conjSub (g : (f112Amalgam L1 L2 S).Ghat) (caseAR v) := by
  unfold caseAR
  exact iSup_nbrs_smul (fun g w => caseA_X_smul g w) g v

theorem caseA_Z_le_Qy (v : f112Gamma L1 L2 S) : caseAZ v ≤ CosetGeom.Qy v := by
  unfold caseAZ
  exact CFSG.Quasithin.A4.omegaOneCenterOf_le (CosetGeom.Qy v)

theorem caseA_Qy_le_stab (v : f112Gamma L1 L2 S) : CosetGeom.Qy v ≤ CosetGeom.stab v := by
  unfold CosetGeom.Qy
  exact CFSG.LieType.BorelTits.pCoreOf_le 2 (CosetGeom.stab v)

private theorem mem_normalizer_of_mem_stab {v : f112Gamma L1 L2 S}
    {H : f112Gamma L1 L2 S → Subgroup (f112Amalgam L1 L2 S).Ghat}
    (hH : ∀ (g : f112Acting L1 L2 S) (w : f112Gamma L1 L2 S),
      H (g • w) = conjSub (g : (f112Amalgam L1 L2 S).Ghat) (H w))
    {x : (f112Amalgam L1 L2 S).Ghat} (hx : x ∈ CosetGeom.stab v) :
    x ∈ Subgroup.normalizer (H v : Set (f112Amalgam L1 L2 S).Ghat) := by
  obtain ⟨hxG, hxv⟩ := CosetGeom.mem_stab.mp hx
  have h := hH ⟨x, hxG⟩ v
  rw [hxv] at h
  exact CosetGeom.mem_normalizer_of_conjSub_eq h.symm

theorem caseA_stab_le_normalizer_Qy (v : f112Gamma L1 L2 S) :
    CosetGeom.stab v ≤ Subgroup.normalizer (CosetGeom.Qy v : Set (f112Amalgam L1 L2 S).Ghat) :=
  fun _ hx => mem_normalizer_of_mem_stab (fun g w => caseA_Qy_smul g w) hx

theorem caseA_stab_le_normalizer_Z (v : f112Gamma L1 L2 S) :
    CosetGeom.stab v ≤ Subgroup.normalizer (caseAZ v : Set (f112Amalgam L1 L2 S).Ghat) :=
  fun _ hx => mem_normalizer_of_mem_stab (fun g w => caseA_Z_smul g w) hx

theorem caseA_stab_le_normalizer_X (v : f112Gamma L1 L2 S) :
    CosetGeom.stab v ≤ Subgroup.normalizer (caseAX v : Set (f112Amalgam L1 L2 S).Ghat) :=
  fun _ hx => mem_normalizer_of_mem_stab (fun g w => caseA_X_smul g w) hx

theorem caseA_stab_le_normalizer_R (v : f112Gamma L1 L2 S) :
    CosetGeom.stab v ≤ Subgroup.normalizer (caseAR v : Set (f112Amalgam L1 L2 S).Ghat) :=
  fun _ hx => mem_normalizer_of_mem_stab (fun g w => caseA_R_smul g w) hx

end CFSG.Quasithin.Stroth

end
