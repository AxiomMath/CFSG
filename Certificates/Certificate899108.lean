module

public import Certificates.Data.RudvalisFF81Sp6Over
public import CFSG.Quasithin.H13.L32NMatNGen
import Certificates.Kernel.Misc.Sp6Over.Facts

public section

namespace Certificates

open CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Over CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two
  CFSG.Quasithin.G2U CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII CFSG.Quasithin.H13.MatNCert in
open scoped Matrix in
theorem certificate899108 :
    (pairCheck (ovGamC, ovGamI) = true ∧ pairCheck (ovHC, ovHI) = true ∧
      pairCheck (ovCC, ovCI) = true ∧ relW.all (fun r => powCode (wordC r.1) r.2 == one6) = true ∧
      powCode ovGamC 7 = one6 ∧ ovGamC ≠ one6 ∧ powCode ovHC 6 = one6 ∧
      mul6 ovHC ovGamC = mul6 (powCode ovGamC 3) ovHC ∧
      mul6 ovCC (mul6 ovHC ovHC) = mul6 (mul6 ovHC ovHC) ovCC ∧
      wordC wZ0 = zCode 0 ∧ wordC wZ1 = zCode 1 ∧ wordC wT = tCode ∧
      wS.map wordC = sylowP.map Prod.fst ∧ powCode (wordC [0, 1, 2]) 5 = one6 ∧
      wordC [0, 1, 2] ≠ one6) ∧
    ((∀ c < 128, mvN n2c c = c → c ∈ fixL) ∧
      (∀ c < 128, mvN n2c (mvN n2c c) = (c ^^^ mvN n2c c) → c ∈ wL) ∧
      (∀ a ∈ fixL, ∀ u ∈ wL, ∀ b ∈ fixL, ∀ v ∈ wL, relsOK (CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Over.cand a u b v) = true →
        CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Over.cand a u b v = xSc ∨ CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Over.cand a u b v = xIc)) ∧
    (∀ x : List ℕ, x = xSc ∨ x = xIc →
      (∀ m, 0 < m → m < 64 → ∃ s ∈ genSubN 7 [nGc, nHc, x],
        decN 7 (kC m) = ((s : GL (Fin 7) (ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)) *
          decN 7 (kC 1) * ((s⁻¹ : GL (Fin 7) (ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2))) ∧
      ((List.range 128).filter fun v => mvN (bbarC x) v == v).length = 32 ∧
      (∀ g ∈ rGens x, mulN g (bbarC x) = mulN (bbarC x) g) ∧
      (∀ m ∈ [6, 8, 17, 33], mulN (kC m) (kC m) = oneN 7) ∧
      Nat.card (genSubN 7 (rGens x)) = 32) ∧
    (piC xIc = piC xSc ∧
      (∀ u ∈ uGens, mulN u u = oneN 6 ∧ mulN u pibbarC = mulN pibbarC u) ∧
      Nat.card (genSubN 6 uGens) = 32) ∧
    ((∀ g ∈ sbGens, (decN 6 g)ᵀ * decN 6 w0c * decN 6 g = decN 6 w0c) ∧
      (∀ g ∈ sbGens ++ grs, ∃ u : GL (Fin 6) (ZMod 2),
        (u : Matrix (Fin 6) (Fin 6) (ZMod 2)) = decN 6 g) ∧
      ∃ T : ℕ → List (Matrix (Fin 6) (Fin 6) (ZMod 2)), T 0 = [decN 6 w0c] ∧
        (∀ r < 5, (T (r + 1)).length = [315, 2880, 2880, 3780, 4032].getD r 0) ∧
        ((List.range 6).flatMap T).Nodup ∧
        ∀ r < 5, ∀ x ∈ T (r + 1), ∃ u : GL (Fin 6) (ZMod 2),
          (u : Matrix (Fin 6) (Fin 6) (ZMod 2)) = decN 6 (grs.getD r []) ∧
          ∃ s ∈ genSubN 6 sbGens,
            x = ((u * s : GL (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2))ᵀ * decN 6 w0c *
              ((u * s : GL (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2))) :=
  ⟨CFSG.KC.Sp6Over.ov_h6_facts, CFSG.KC.Sp6Over.ov_pin_facts,
    fun _ hx => CFSG.KC.Sp6Over.ov_k_facts hx, CFSG.KC.Sp6Over.ov_u_facts,
    CFSG.KC.Sp6Over.ov_form_facts⟩

end Certificates
