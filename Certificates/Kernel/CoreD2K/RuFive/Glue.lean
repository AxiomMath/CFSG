module

public import Certificates.Kernel.CoreD2K.RuFive.Checks
public import Certificates.Kernel.CoreD2K.RuFive.Bind
public import Certificates.Kernel.Misc.RuInv.Proof
public import CFSG.Certificates.Kernel.CoreD2K.SoundOne
public import CFSG.Certificates.Kernel.CoreD2K.Parts
public import CFSG.LocalAnalysis.RankThreeTheoremC.CoreGenerationOne

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCoreD2K.RuFive

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MaxD2 CFSG.KS.CoreD2K CFSG.KD.CoreD2K
  CFSG.ComponentClassification.PSL3Four CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2
  Certificates.CoreD2Perm CFSG.Open

noncomputable def fE (k : Nat) : Bool :=
  bAnd(wordEqK 4060 12 (mask 12) (pidn 4060 12) GP GPI (nat_lit 2) (V.base.eW.getD k [])
    (RE.G k), canonK 4060 12 (mask 12) (Nat.mul 4060 12) (RE.G k))

noncomputable def fG (j : Nat) : Bool :=
  bAnd(wordEqK 4060 12 (mask 12) (pidn 4060 12) GP GPI (nat_lit 2) (V.base.gWs.getD j [])
    (GT j), permOK 4060 12 (mask 12) (Nat.mul 4060 12) (GT j) (GTI j))

noncomputable def fA (i : Nat) : Bool :=
  wordEqK 4060 12 (mask 12) (pidn 4060 12) GT GTI V.base.gWs.length (V.wAs.getD i [])
    (GP (nat_lit 0))

noncomputable def fB (i : Nat) : Bool :=
  wordEqK 4060 12 (mask 12) (pidn 4060 12) GT GTI V.base.gWs.length (V.wBs.getD i [])
    (GP (nat_lit 1))

theorem len_eW : V.base.eW.length = 7 := rfl
theorem len_gWs : V.base.gWs.length = 8 := rfl
theorem len_ys : V.ys.length = 6 := rfl
theorem len_ys' : V.ys.length = nat_lit 6 := rfl
theorem len_wAs : V.wAs.length = V.ys.length := rfl
theorem len_wBs : V.wBs.length = V.ys.length := rfl

theorem all_fE : ∀ k < V.base.eW.length, fE k = true := by
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

theorem all_fG : ∀ j < V.base.gWs.length, fG j = true := by
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
  | _ + 8, h => omega

theorem all_fAB : ∀ i < V.ys.length, fA i = true ∧ fB i = true := by
  rw [len_ys]
  intro i hi
  match i, hi with
  | 0, _ => exact ⟨(fA.eq_1 0).trans k_wa0, (fB.eq_1 0).trans k_wb0⟩
  | 1, _ => exact ⟨(fA.eq_1 1).trans k_wa1, (fB.eq_1 1).trans k_wb1⟩
  | 2, _ => exact ⟨(fA.eq_1 2).trans k_wa2, (fB.eq_1 2).trans k_wb2⟩
  | 3, _ => exact ⟨(fA.eq_1 3).trans k_wa3, (fB.eq_1 3).trans k_wb3⟩
  | 4, _ => exact ⟨(fA.eq_1 4).trans k_wa4, (fB.eq_1 4).trans k_wb4⟩
  | 5, _ => exact ⟨(fA.eq_1 5).trans k_wa5, (fB.eq_1 5).trans k_wb5⟩
  | _ + 6, h => omega

theorem k_gens : gensK 4060 12 V GP GPI RE.G GT GTI = true :=
  gensK_of k_gp (fun k hk => (fE.eq_1 k).symm.trans (all_fE k hk))
    (fun j hj => (fG.eq_1 j).symm.trans (all_fG j hj))

theorem k_words : wordsK 4060 12 V GP GT GTI = true :=
  wordsK_of len_wAs len_wBs
    (fun i hi => ⟨(fA.eq_1 i).symm.trans (all_fAB i hi).1,
      (fB.eq_1 i).symm.trans (all_fAB i hi).2⟩)
    (by rw [len_ys']; exact k_wok)

theorem hyps : KHyps 4060 12 V GP GPI GT GTI RE.G RE.GI RE.T RE.PL RE.POS RE.SRT RE.SRI RE.cnt
    125 125 where
  hn := k_sz
  hgens := k_gens
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
  hwords := k_words

theorem tab_gp {j : Nat} (hj : j < 2) {P : Nat} (hP : ruArr4060 j = unpack 4060 12 P)
    (hb : Nat.beq (GP j) P = true) :
    TabRep (unpack 4060 12 (GP j)) (permOfArr 4060 (ruArr4060 j)) := by
  have hperm : invEqK 4060 12 (mask 12) (4060 * 12) (GP j) (GPI j) = true :=
    PK.allN_iff.1 k_gp j hj
  rw [hP, ← Nat.eq_of_beq_eq_true hb]
  exact ⟨size_u _, (rep_permOfArr (invEqK_sound hperm).2).1⟩

theorem tab0 : TabRep (unpack 4060 12 (GP 0)) ruA0 :=
  tab_gp (by norm_num) CertificateChecks.KernelMisc.RuInv.hA0 gp0_eq

theorem tab1 : TabRep (unpack 4060 12 (GP 1)) ruA1 :=
  tab_gp (by norm_num) CertificateChecks.KernelMisc.RuInv.hA1 gp1_eq

theorem strict_facts_ruP :
    ∃ E : Subgroup (Equiv.Perm (Fin 4060)), Nat.card E = 5 ^ 3 ∧
      (∀ x ∈ E, x ^ 5 = 1) ∧ (∃ x ∈ E, ∃ y ∈ E, x * y ≠ y * x) ∧ E ≤ ruP ∧
      ∀ A : Subgroup (Equiv.Perm (Fin 4060)), A ≤ E → IsElemAbelian 5 A → Nat.card A = 5 ^ 2 →
        ∃ Γ : Set (Equiv.Perm (Fin 4060)), Γ ⊆ ruP ∧
          ({ruA0, ruA1} : Set (Equiv.Perm (Fin 4060))) ⊆ Subgroup.closure Γ ∧ ∀ g ∈ Γ,
            (∃ u v : Equiv.Perm (Fin 4060), u ∈ A ∧ v ∈ A ∧ u ^ 5 = 1 ∧ v ^ 5 = 1 ∧
              u * v = v * u ∧ u ≠ 1 ∧ (∀ j < 5, v ≠ u ^ j) ∧ ∃ α β γ δ : ℕ,
                g * u = (u ^ α * v ^ β) * g ∧ g * v = (u ^ γ * v ^ δ) * g) ∨
            (∃ y ∈ A, y ≠ 1 ∧ y ^ 5 = 1 ∧ ∃ α : ℕ, g * y = y ^ α * g) :=
  lines_facts_one hyps (by rw [len_ys']; exact k_strict) Nat.prime_five tab0 tab1

theorem coreGenerationOneOf_ruP_five :
    CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen.CoreGenerationOneOf ↥ruP 5 := by
  obtain ⟨E, hEc, hEexp, hEnab, hEG, hΓ⟩ := strict_facts_ruP
  exact CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen.coreGenerationOneOf_of_gens
    Nat.prime_five (S := {ruA0, ruA1}) rfl hEc hEexp hEnab hEG hΓ

end CertificateChecks.KernelCoreD2K.RuFive

end
