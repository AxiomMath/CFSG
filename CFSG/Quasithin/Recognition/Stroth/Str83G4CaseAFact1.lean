module

public import CFSG.Quasithin.Recognition.Stroth.Str83G4CaseAKernel

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Quasithin.F112R

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G}

private theorem caseA_Z_le_Z_base {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) :
    caseAZ (f112Gamma0 L1 L2 S) ≤ caseAZ (f112Gamma1 L1 L2 S) := by
  have hfr' := hfr
  obtain ⟨hF, hB, ha, hSz, hL2, hZI⟩ := hfr
  have hZ12 : Z1 L1 L2 S ≤ Z2 L1 L2 S := (str83_caseI_basics hF hB ha hSz hL2 hZI).2.1
  intro x hx
  have hxQ : x ∈ CosetGeom.Qy (f112Gamma0 L1 L2 S) := caseA_Z_le_Qy _ hx
  have hxK : x ∈ CosetGeom.ballStab 1 (f112Gamma0 L1 L2 S) :=
    caseA_Qy_le_ballStab_one hfr' _ hxQ
  have hdist : CosetGeom.dist (f112Gamma0 L1 L2 S) (f112Gamma1 L1 L2 S) ≤ 1 :=
    (CosetGeom.dist_eq_one_iff_adj.mpr CosetGeom.adj_γ₀_γ₁).le
  have hxst1 : x ∈ CosetGeom.stab (f112Gamma1 L1 L2 S) :=
    CosetGeom.ballStab_le_stab_of_dist_le hdist hxK
  obtain ⟨hxG0, hfix0⟩ := CosetGeom.mem_stab.mp (caseA_Qy_le_stab (f112Gamma0 L1 L2 S) hxQ)
  obtain ⟨hxG1, hfix1⟩ := CosetGeom.mem_stab.mp hxst1
  let h0 : MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma0 L1 L2 S) :=
    ⟨⟨x, hxG0⟩, hfix0⟩
  let h1 : MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma1 L1 L2 S) :=
    ⟨⟨x, hxG1⟩, hfix1⟩
  have hZ1 : (f112StabEquiv0 L1 L2 S h0 : G) ∈ Z1 L1 L2 S :=
    (caseA_mem_Z_γ₀_iff h0).mp hx
  have heq : (f112StabEquiv1 L1 L2 S h1 : G) = (f112StabEquiv0 L1 L2 S h0 : G) := by
    rw [coe_f112StabEquiv1, coe_f112StabEquiv0]
  exact (caseA_mem_Z_γ₁_iff h1).mpr (heq.symm ▸ hZ12 hZ1)

theorem caseA_Z_le_Z_of_adj {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) {α β : f112Gamma L1 L2 S}
    (hα : CosetGeom.vtype α = false) (hadj : (f112Amalgam L1 L2 S).graphHat.Adj α β) :
    caseAZ α ≤ caseAZ β := by
  obtain ⟨g, hg | hg⟩ := CosetGeom.exists_smul_edge hadj
  · rw [← hg.1, ← hg.2, caseA_Z_smul, caseA_Z_smul]
    exact conjSub_mono _ (caseA_Z_le_Z_base hfr)
  · exfalso
    have htrue : CosetGeom.vtype α = true := by
      rw [← hg.2, CosetGeom.vtype_smul, CosetGeom.vtype_γ₁]
    rw [hα] at htrue
    exact Bool.false_ne_true htrue

theorem caseA_Z_ne_bot {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) (v : f112Gamma L1 L2 S) : caseAZ v ≠ ⊥ := by
  have hfr' := hfr
  obtain ⟨hF, hB, ha, hSz, hL2, hZI⟩ := hfr
  have hZ1eq : Z1 L1 L2 S = omegaOneCenterOf S := (str83_caseI_basics hF hB ha hSz hL2 hZI).1
  have hZ1ne : Z1 L1 L2 S ≠ ⊥ := by
    rw [hZ1eq]
    exact omegaOneCenterOf_ne_bot_of_hyp111 hF.1
  have hbase0 : caseAZ (f112Gamma0 L1 L2 S) ≠ ⊥ := by
    intro hbot
    apply hZ1ne
    apply le_bot_iff.mp
    intro z hz
    have hzP1 : z ∈ P1 L1 L2 S :=
      (le_trans (omegaOneCenterOf_le (Q1 L1 L2 S))
        (CFSG.LieType.BorelTits.pCoreOf_le 2 (P1 L1 L2 S))) hz
    obtain ⟨h, hh⟩ := (f112StabEquiv0 L1 L2 S).surjective ⟨z, hzP1⟩
    have hzh : (f112StabEquiv0 L1 L2 S h : G) = z := by
      simpa using congrArg Subtype.val hh
    have hmem : ((h : f112Acting L1 L2 S) : (f112Amalgam L1 L2 S).Ghat) ∈
        caseAZ (f112Gamma0 L1 L2 S) := (caseA_mem_Z_γ₀_iff h).mpr (hzh.symm ▸ hz)
    rw [hbot] at hmem
    have h1 : (h : f112Acting L1 L2 S) = 1 :=
      Subtype.val_injective (Subgroup.mem_bot.mp hmem)
    rw [← hzh, coe_f112StabEquiv0, h1]
    simp
  have hbase1 : caseAZ (f112Gamma1 L1 L2 S) ≠ ⊥ := by
    intro h1
    exact hbase0 (le_bot_iff.mp ((caseA_Z_le_Z_base hfr').trans (le_of_eq h1)))
  cases hv : CosetGeom.vtype v with
  | false =>
    obtain ⟨g, hg⟩ := CosetGeom.exists_smul_eq_γ₀ hv
    rw [hg, caseA_Z_smul]
    intro h
    exact hbase0 ((conjSub_eq_bot_iff (G := (f112Amalgam L1 L2 S).Ghat) g).mp h)
  | true =>
    obtain ⟨g, hg⟩ := CosetGeom.exists_smul_eq_γ₁ hv
    rw [hg, caseA_Z_smul]
    intro h
    exact hbase1 ((conjSub_eq_bot_iff (G := (f112Amalgam L1 L2 S).Ghat) g).mp h)

end CFSG.Quasithin.Stroth

end
