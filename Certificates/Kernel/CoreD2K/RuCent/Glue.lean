module

public import Certificates.Kernel.CoreD2K.RuCent.Checks
public import Certificates.Kernel.CoreD2K.RuFive.Glue
public import CFSG.Certificates.Kernel.CoreD2K.Cent

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCoreD2K.RuCent

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.Open CFSG.KS.MaxD2 CFSG.KS.CoreD2K CFSG.KD.CoreD2K
  CFSG.Sporadic.RuSchreier Certificates.CoreD2Perm
open CertificateChecks.KernelCoreD2K.RuFive (GP GPI)

noncomputable def fE (k : Nat) : Bool :=
  bAnd(wordEqK 4060 12 (mask 12) (pidn 4060 12) GP GPI (nat_lit 2) (ruCentK.base.eW.getD k [])
    (RE.G k), canonK 4060 12 (mask 12) (Nat.mul 4060 12) (RE.G k))

noncomputable def fG (j : Nat) : Bool :=
  bAnd(wordEqK 4060 12 (mask 12) (pidn 4060 12) GP GPI (nat_lit 2) (ruCentK.base.gWs.getD j [])
    (GT j), permOK 4060 12 (mask 12) (Nat.mul 4060 12) (GT j) (GTI j))

theorem len_eW : ruCentK.base.eW.length = 7 := rfl
theorem len_gWs : ruCentK.base.gWs.length = 9 := rfl

theorem all_fE : ∀ k < ruCentK.base.eW.length, fE k = true := by
  rw [len_eW]
  intro k hk
  match k, hk with
  | 0, _ => exact (fE.eq_1 0).trans k_e0
  | 1, _ => exact (fE.eq_1 1).trans k_e1
  | 2, _ => exact (fE.eq_1 2).trans k_e2
  | 3, _ => exact (fE.eq_1 3).trans k_e3
  | 4, _ => exact (fE.eq_1 4).trans k_e4
  | 5, _ => exact (fE.eq_1 5).trans k_e5
  | 6, _ => exact (fE.eq_1 6).trans k_e6
  | _ + 7, h => omega

theorem all_fG : ∀ j < ruCentK.base.gWs.length, fG j = true := by
  rw [len_gWs]
  intro j hj
  match j, hj with
  | 0, _ => exact (fG.eq_1 0).trans k_g0
  | 1, _ => exact (fG.eq_1 1).trans k_g1
  | 2, _ => exact (fG.eq_1 2).trans k_g2
  | 3, _ => exact (fG.eq_1 3).trans k_g3
  | 4, _ => exact (fG.eq_1 4).trans k_g4
  | 5, _ => exact (fG.eq_1 5).trans k_g5
  | 6, _ => exact (fG.eq_1 6).trans k_g6
  | 7, _ => exact (fG.eq_1 7).trans k_g7
  | 8, _ => exact (fG.eq_1 8).trans k_g8
  | _ + 9, h => omega

theorem hyps : KHypsC 4060 12 ruCentK ruCentReps ruCentSteps GP GPI GT GTI RE.G RE.GI RE.T RE.PL
    RE.POS RE.SRT RE.SRI RE.cnt 125 125 where
  hn := RuFive.k_sz
  hgp := RuFive.k_gp
  hE := fun k hk => (fE.eq_1 k).symm.trans (all_fE k hk)
  hG := fun j hj => (fG.eq_1 j).symm.trans (all_fG j hj)
  hh := k_eh
  hsl := by
    rw [← Nat.eq_of_beq_eq_true k_ek]
    exact k_esl
  hlen := by rw [Nat.eq_of_beq_eq_true k_ecnt]
  hcnt := by
    rw [Nat.eq_of_beq_eq_true k_ecnt]
    rfl
  hnab := k_nab
  hcen := k_cen
  hlines := k_lines
  hkinds := k_kinds
  hreps := by
    intro i hi
    simp only [ruCentReps, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · exact k_rep0
    · exact k_rep3
    · exact k_rep5
  hsteps := List.all_eq_true.1 k_steps
  hchain := k_chain

theorem exists_cent_gens_ruP :
    ∃ E : Subgroup ↥ruP, Nat.card E = 5 ^ 3 ∧
      ∀ A : Subgroup ↥ruP, A ≤ E → IsElemAbelian 5 A → Nat.card A = 5 ^ 2 →
        ∃ Γ : Set ↥ruP, Subgroup.closure Γ = ⊤ ∧ ∀ g ∈ Γ, ∃ y ∈ A, y ≠ 1 ∧ g * y = y * g :=
  exists_cent_gens_of_kchecks hyps Nat.prime_five (by decide) (by decide) RuFive.tab0 RuFive.tab1

end CertificateChecks.KernelCoreD2K.RuCent

end
