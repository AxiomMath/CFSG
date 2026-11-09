module

public import Certificates.Data.Kernel.AEOrbitK

public section

namespace CertificateChecks.KernelAEOrbit

open Certificates.AEOrbit CFSG.KC.AEOrbitK

theorem c397301sign5 : (cands 5).all (fun σ => decide (Equiv.Perm.sign σ = 1)) = true := by
  decide +kernel

theorem c397301sign6 : (cands 6).all (fun σ => decide (Equiv.Perm.sign σ = 1)) = true := by
  decide +kernel

theorem c397301ct5 : ((cands 5).map tab == ct5) = true := by decide +kernel

theorem c397301ct6 : ((cands 6).map tab == ct6) = true := by decide +kernel

theorem c397301k5 : kchkM 5 ct5 4 = true := by decide +kernel

private theorem all_take_drop {α : Type} (l : List α) (f : α → Bool) (k : ℕ)
    (h1 : (l.take k).all f = true) (h2 : (l.drop k).all f = true) : l.all f = true := by
  rw [← List.take_append_drop k l, List.all_append, h1, h2]
  rfl

theorem c397301k6a : ((masks4 6).take 5).all (fun a => (masks4 6).all fun b => a == b ||
    (masks4 6).all fun c => decide (c ∈ (reachM (movesT ct6 a ++ movesT ct6 b) a 4).1)) =
    true := by
  decide +kernel

theorem c397301k6b : (((masks4 6).drop 5).take 5).all (fun a => (masks4 6).all fun b => a == b ||
    (masks4 6).all fun c => decide (c ∈ (reachM (movesT ct6 a ++ movesT ct6 b) a 4).1)) =
    true := by
  decide +kernel

theorem c397301k6c : (((masks4 6).drop 5).drop 5).all (fun a => (masks4 6).all fun b => a == b ||
    (masks4 6).all fun c => decide (c ∈ (reachM (movesT ct6 a ++ movesT ct6 b) a 4).1)) =
    true := by
  decide +kernel

theorem c397301k6 : kchkM 6 ct6 4 = true := by
  unfold kchkM
  exact all_take_drop _ _ 5 c397301k6a (all_take_drop _ _ 5 c397301k6b c397301k6c)

theorem c397301lt5 : (masks4 5).all (fun a => decide (a < 2 ^ 5)) = true := by decide +kernel

theorem c397301lt6 : (masks4 6).all (fun a => decide (a < 2 ^ 6)) = true := by decide +kernel

theorem c397301cov5 : ∀ α ∈ fours 5, ∃ a ∈ masks4 5, dec 5 a = α := by decide +kernel

theorem c397301cov6 : ∀ α ∈ fours 6, ∃ a ∈ masks4 6, dec 6 a = α := by decide +kernel

end CertificateChecks.KernelAEOrbit
