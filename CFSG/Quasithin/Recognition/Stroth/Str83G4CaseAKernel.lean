module

public import CFSG.Quasithin.Recognition.Stroth.Str83G4CaseABase
public import CFSG.Quasithin.Recognition.Stroth.Str83G4CaseAEquiv
public import CFSG.Quasithin.Recognition.Stroth.Str83G4Frame
import CFSG.Quasithin.Recognition.Stroth.Str83TwoArc

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Quasithin.F112R CFSG.QuasithinUnique CFSG.GH74.Uniqueness.Bender

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G}

private theorem caseA_Qy_γ₀_le_ballStab_one {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) :
    CosetGeom.Qy (f112Gamma0 L1 L2 S) ≤ CosetGeom.ballStab 1 (f112Gamma0 L1 L2 S) := by
  obtain ⟨hF, hB, ha, hSz, hL2, -⟩ := hfr
  intro x hx
  have hxstab : x ∈ CosetGeom.stab (f112Gamma0 L1 L2 S) := caseA_Qy_le_stab _ hx
  obtain ⟨hAmem, hfix⟩ := CosetGeom.mem_stab.mp hxstab
  set hA : f112Acting L1 L2 S := ⟨x, hAmem⟩ with hAeq
  have hfixA : hA • f112Gamma0 L1 L2 S = f112Gamma0 L1 L2 S := hfix
  have hQ1 : (f112StabEquiv0 L1 L2 S ⟨hA, hfixA⟩ : G) ∈ Q1 L1 L2 S :=
    (caseA_mem_Qy_γ₀_iff ⟨hA, hfixA⟩).mp hx
  have hmK1 : f112StabEquiv0 L1 L2 S ⟨hA, hfixA⟩ ∈ f112K1 L1 L2 S :=
    (Subgroup.mem_map_iff_mem (f := (L1 ⊔ bigB L1 L2 S).subtype)
      (L1 ⊔ bigB L1 L2 S).subtype_injective).mp (pCoreOf_le_K1_map hF hQ1)
  have hfixN : ∀ w, (f112Amalgam L1 L2 S).graphHat.Adj (f112Gamma0 L1 L2 S) w → hA • w = w :=
    (f112_fixes_nbrs_iff_mem_K1 hF hA hfixA).mpr hmK1
  refine CosetGeom.mem_ballStab.mpr fun δ hδ => ?_
  rcases (CosetGeom.dist_le_one_iff rfl).mp hδ with rfl | hadj
  · exact hxstab
  · exact CosetGeom.mem_stab_of_smul_eq (hfixN δ hadj)

private theorem caseA_Qy_γ₁_le_ballStab_one {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) :
    CosetGeom.Qy (f112Gamma1 L1 L2 S) ≤ CosetGeom.ballStab 1 (f112Gamma1 L1 L2 S) := by
  obtain ⟨hF, hB, ha, hSz, hL2, -⟩ := hfr
  intro x hx
  have hxstab : x ∈ CosetGeom.stab (f112Gamma1 L1 L2 S) := caseA_Qy_le_stab _ hx
  obtain ⟨hAmem, hfix⟩ := CosetGeom.mem_stab.mp hxstab
  set hA : f112Acting L1 L2 S := ⟨x, hAmem⟩ with hAeq
  have hfixA : hA • f112Gamma1 L1 L2 S = f112Gamma1 L1 L2 S := hfix
  have hQ2 : (f112StabEquiv1 L1 L2 S ⟨hA, hfixA⟩ : G) ∈ Q2 L1 L2 S :=
    (caseA_mem_Qy_γ₁_iff ⟨hA, hfixA⟩).mp hx
  have hmK2 : f112StabEquiv1 L1 L2 S ⟨hA, hfixA⟩ ∈ f112K2 L1 L2 S :=
    (Subgroup.mem_map_iff_mem (f := (L2 ⊔ bigB L1 L2 S).subtype)
      (L2 ⊔ bigB L1 L2 S).subtype_injective).mp (pCoreOf_le_K2_map hF hQ2)
  have hfixN : ∀ w, (f112Amalgam L1 L2 S).graphHat.Adj (f112Gamma1 L1 L2 S) w → hA • w = w :=
    (f112_fixes_nbrs_iff_mem_K2 hF hA hfixA).mpr hmK2
  refine CosetGeom.mem_ballStab.mpr fun δ hδ => ?_
  rcases (CosetGeom.dist_le_one_iff rfl).mp hδ with rfl | hadj
  · exact hxstab
  · exact CosetGeom.mem_stab_of_smul_eq (hfixN δ hadj)

theorem caseA_Qy_le_ballStab_one {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) (v : f112Gamma L1 L2 S) :
    CosetGeom.Qy v ≤ CosetGeom.ballStab 1 v := by
  cases hv : CosetGeom.vtype v with
  | false =>
    obtain ⟨u, rfl⟩ := CosetGeom.exists_smul_eq_γ₀ hv
    rw [caseA_Qy_smul u (f112Gamma0 L1 L2 S),
      CosetGeom.ballStab_smul u 1 (f112Gamma0 L1 L2 S)]
    exact conjSub_mono _ (caseA_Qy_γ₀_le_ballStab_one hfr)
  | true =>
    obtain ⟨u, rfl⟩ := CosetGeom.exists_smul_eq_γ₁ hv
    rw [caseA_Qy_smul u (f112Gamma1 L1 L2 S),
      CosetGeom.ballStab_smul u 1 (f112Gamma1 L1 L2 S)]
    exact conjSub_mono _ (caseA_Qy_γ₁_le_ballStab_one hfr)

end CFSG.Quasithin.Stroth

end
