module

public import Certificates.Kernel.C12643.Cent
public import Certificates.Kernel.Misc.Perm.J2CentGJ
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Gen
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KS155.J2E4Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelC12643

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.J2Enum CertificateChecks.KernelJ2Cover
open CFSG.ComponentClassification.J2Cover CFSG.Certificates.Native CFSG.Monster.B.Co2.Native
open CFSG.RankThree.Native CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 CFSG.Monster.B.Fischer
open CFSG.AGLEmbeddingD2.Wilson.Coordinator.KS155
open CertificateChecks.KernelMisc.J2Cent (gen_eq_P card_centralizer_eq kL0)
open CFSG.Monster.B.Co2 (Rep)

theorem cent_eq {gs : Array (Array ℕ)} {c : ArrCert}
    {t : Array ℕ} {P N : ℕ} (hP : t = unpack 315 9 P)
    (hcard : ∀ ξ ∈ Raw.Orb.Gen 315 autStrong 2, Raw.Orb.PRep 315 9 P ξ →
      Nat.card {h : Equiv.Perm (Fin 315) // h ∈ Raw.Orb.Gen 315 autStrong 2 ∧ h * ξ = ξ * h} = N)
    (hen : enumOK 315 gs keyPts c = true) (hs : c.pts.size = N)
    (hok : ∀ k < gs.size, validA 315 gs[k]! = true ∧ inP gs[k]! = true)
    (hcm : ∀ k < gs.size, commA gs[k]! t = true) {g : GJ} (hg : Rep 315 t g.1) :
    Subgroup.centralizer ({g} : Set GJ) = subOf gs := by
  refine (Subgroup.eq_of_le_of_card_ge ?_ ?_).symm
  · refine subOf_le_of gs hok fun k hk => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (commute_of_commA (rep_gElt _ _ k hk) hg (hcm k hk)).eq
  · rw [card_centralizer_eq,
      hcard _ ((SetLike.ext_iff.1 gen_eq_P _).2 g.2) (Raw.Orb.prep_of_rep (by rw [← hP]; exact hg)),
      card_subOf (by decide) hen hok, hs]

theorem kL1 : rcnt (PA.LR 1) = 160 := Nat.eq_of_beq_eq_true (by quickRfl)

theorem kL2 : rcnt (PA.LR 2) = 12 := Nat.eq_of_beq_eq_true (by quickRfl)

theorem mem_cperm {a b c : ℕ} (ha : a < 315) (hb : b < 160) (hc : c < 12) :
    cperm a b c ∈ CFSG.ComponentClassification.J2Cover.P := by
  have h := (GrpPf.enum3 binds PA.head PA.hl (by norm_num) PA.hs).1
  rw [← gen_eq_P, cperm, jBase_eq]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (h 0 (by norm_num) a (by rw [kL0]; exact ha)).1
    (h 1 (by norm_num) b (by rw [kL1]; exact hb)).1) (h 2 (by norm_num) c (by rw [kL2]; exact hc)).1

theorem test_of {gs : Array (Array ℕ)} {ce : ArrCert}
    {t u : Array ℕ} {g x : GJ} (hen : enumOK 315 gs keyPts ce = true) (ht : Rep 315 t g.1)
    (hu : Rep 315 u x.1) (hC : Subgroup.centralizer ({x} : Set GJ) = subOf gs)
    (hc : commA t u = true) : inCert ce t = true :=
  inCert_of_mem hen ht (hC ▸ Subgroup.mem_centralizer_singleton_iff.2 (commute_of_commA ht hu hc).eq)

theorem bruteOK_of
    (h5a : enumOK 315 gC5a keyPts (c5a ()) = true) (s5a : (c5a ()).pts.size = 300)
    (h5c : enumOK 315 gC5c keyPts (c5c ()) = true) (s5c : (c5c ()).pts.size = 50)
    (h7 : enumOK 315 gC7 keyPts (c7 ()) = true) (s7 : (c7 ()).pts.size = 7)
    (hE : enumOK 315 gCE keyPts (cE ()) = true) (sE : (cE ()).pts.size = 240)
    (ok5a : ∀ k < gC5a.size, validA 315 gC5a[k]! = true ∧ inP gC5a[k]! = true)
    (ok5c : ∀ k < gC5c.size, validA 315 gC5c[k]! = true ∧ inP gC5c[k]! = true)
    (ok7 : ∀ k < gC7.size, validA 315 gC7[k]! = true ∧ inP gC7[k]! = true)
    (okE : ∀ k < gCE.size, validA 315 gCE[k]! = true ∧ inP gCE[k]! = true)
    (cm5a : ∀ k < gC5a.size, commA gC5a[k]! x5aA = true)
    (cm5c : ∀ k < gC5c.size, commA gC5c[k]! x5cA = true)
    (cm7 : ∀ k < gC7.size, commA gC7[k]! x7A = true)
    (cmE : ∀ k < gCE.size, commA gCE[k]! e1A = true)
    (v5a : validA 315 x5aA = true ∧ inP x5aA = true) (v5c : validA 315 x5cA = true ∧ inP x5cA = true)
    (v7 : validA 315 x7A = true ∧ inP x7A = true) (vE : validA 315 e1A = true ∧ inP e1A = true) :
    bruteOK (c5a ()) (c5c ()) (c7 ()) (cE ()) = true := by
  have C5a := cent_eq hx5a (fun _ h1 h2 => card_cent_x5a h1 h2) h5a s5a ok5a cm5a (rep_elA v5a)
  have C5c := cent_eq hx5c (fun _ h1 h2 => card_cent_x5c h1 h2) h5c s5c ok5c cm5c (rep_elA v5c)
  have C7 := cent_eq hx7 (fun _ h1 h2 => card_cent_x7 h1 h2) h7 s7 ok7 cm7 (rep_elA v7)
  have CE := cent_eq he1 (fun _ h1 h2 => card_cent_e1 h1 h2) hE sE okE cmE (rep_elA vE)
  unfold bruteOK
  rw [CFSG.Monster.B.Co2.allLt_iff]
  intro a ha
  rw [CFSG.Monster.B.Co2.allLt_iff]
  intro b hb
  rw [CFSG.Monster.B.Co2.allLt_iff]
  intro c hc
  have hg : Rep 315 (prod3 315 autLevels a b c) (⟨cperm a b c, mem_cperm ha hb hc⟩ : GJ).1 :=
    rep_prod3 ha hb hc
  unfold brutePr
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true']
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · cases h : commA (prod3 315 autLevels a b c) x5aA
    · exact Or.inl rfl
    · exact Or.inr (test_of h5a hg (rep_elA v5a) C5a h)
  · cases h : commA (prod3 315 autLevels a b c) x5cA
    · exact Or.inl rfl
    · exact Or.inr (test_of h5c hg (rep_elA v5c) C5c h)
  · cases h : commA (prod3 315 autLevels a b c) x7A
    · exact Or.inl rfl
    · exact Or.inr (test_of h7 hg (rep_elA v7) C7 h)
  · cases h : commA (prod3 315 autLevels a b c) e1A
    · exact Or.inl (by rw [Bool.and_eq_false_iff]; exact Or.inl rfl)
    · exact Or.inr (test_of hE hg (rep_elA vE) CE h)

end CertificateChecks.KernelC12643

end
