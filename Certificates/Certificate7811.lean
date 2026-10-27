module

public import CFSG.Milestones.ASVolI.F48.D43.EInputs
public import Certificates.Certificate7805
import CFSG.Certificates.Kernel.Misc.Coset.PG

public section

open CFSG CFSG.ASVolI CFSG.CosetTable CFSG.KC.MiscCoset

namespace Certificates

private theorem certificate7811_PG_eq {m m' : ℕ} (hm : m = m') {ws : List (List (Fin m × Bool))}
    {ws' : List (List (Fin m' × Bool))} (h : ws.map encW = ws'.map encW) :
    PG m ws = PG m' ws' := by
  subst hm
  have hinj : Function.Injective (encW : List (Fin m × Bool) → List (ℕ × Bool)) :=
    List.map_injective_iff.2 fun a b hab => by
      simp only [Prod.mk.injEq] at hab
      exact Prod.ext (Fin.ext hab.1) hab.2
  rw [List.map_injective_iff.2 hinj h]

private theorem certificate7811_rels :
    burnsideF48dE_WsP1'.map encW = (burnsideF48d_Ws1 ()).map encW := by
  decide +kernel

open CFSG CFSG.ASVolI CFSG.CosetTable in
theorem certificate7811 : Finite (PG _ burnsideF48dE_WsP1') ∧
    Nat.card (PG _ burnsideF48dE_WsP1') ≤ 28 * (52 * 531441) := by
  have h := Certificates.certificate7805.2
  rw [← certificate7811_PG_eq (by decide) certificate7811_rels] at h
  exact h

end Certificates
