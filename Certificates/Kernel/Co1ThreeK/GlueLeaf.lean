
module

public import Certificates.Kernel.Co1ThreeK.GlueNodes
public import Certificates.Kernel.Co1B.C17591
public import CFSG.Certificates.Kernel.Co1Three.LeafSound
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1ThreeBase

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1ThreeK

open CFSG.KC.Co1Cl CFSG.KC.Co1F2 CFSG.KC.Co1BBound CFSG.KC.Co1Leaf
open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.SmallF2
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Proving
open CertificateChecks.KernelCo1B.Bound17591

section Leaf

theorem memK_XB_lt {x : ℕ} (h : memK XB x = true) : x < 2 ^ 24 :=
  Co1T.xL_lt x (mem_of_memK h)

theorem eq_one_of_leafK_GA {G : List ℕ} {piM w : ℕ} {S B : List ℕ} {T : List (List ℕ)}
    (h : leafK XB G piM w S B T = true) {fs : List ↥GA} (hG : ∀ g ∈ G, ∃ f ∈ fs, matK g = ιK f)
    {n : ↥GA} (hn : ∀ f ∈ fs, n * f = f * n) (hcop : Nat.Coprime (orderOf n) 3) : n = 1 := by
  refine ιK_injective ((eq_one_of_leafK (n := ιK n) (fun x hx => memK_XB_lt hx) h
    (fun g hg => ?_) (fun x hx => ?_) (m := orderOf n) ?_ hcop).trans (map_one ιK).symm)
  · obtain ⟨f, hf, hgf⟩ := hG g hg
    change ιK n * matK g = matK g * ιK n
    rw [hgf, ← map_mul, ← map_mul, hn f hf]
  · obtain ⟨y, hy, hxy⟩ := Co1T.xL_maps n x (mem_of_memK hx)
    exact ⟨y, memK_of_mem hy, hxy⟩
  · rw [← map_pow, pow_orderOf_eq_one, map_one]

theorem good_of_leafK {G : List ℕ} {piM w : ℕ} {S B : List ℕ} {T : List (List ℕ)}
    (h : leafK XB G piM w S B T = true) {fs : List ↥GA} (hG : ∀ g ∈ G, ∃ f ∈ fs, matK g = ιK f) :
    CFSG.Open.GLAPPrimeCoreOf 3 (Subgroup.centralizer {x | x ∈ fs}) = ⊥ := by
  have := Co1T.finite_GA
  exact gLAPPrimeCoreOf_eq_bot_of_isPGroup Nat.prime_three
    (Co1T.isPGroup_of_coprime_eq_one Nat.prime_three fun n hn hcop =>
      eq_one_of_leafK_GA h hG (fun f hf => (Subgroup.mem_centralizer_iff.1 hn f hf).symm) hcop)

end Leaf

end CertificateChecks.KernelCo1ThreeK

end
