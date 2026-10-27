module

public import Certificates.Kernel.CertF8.Om9558Data
public import Certificates.Data.ONanG28Om

set_option maxRecDepth 100000

public section

namespace CFSG.KC.CertF8.Om9558

open CFSG.KC.CertF8 CFSG.KC.CertF8.Om CFSG.KC.G28 CFSG.AGLEmbedding.KFactProofs.G28

@[expose] noncomputable def zK : Nat := powS6 (wordS6 tUW) 3

@[expose] def rootIdx : List Nat := [1, 32320, 65152, 97984]

theorem ch9558gens : ∀ j : Fin 4,
    gK j.val = wordS6 gW[j.val]! ∧ gK (j.val + 4) = wordS6 (gW[j.val]!).reverse := by
  decide +kernel

theorem ch9558hgens : ∀ t : Fin 8,
    hK t.val = symW omSchW[t.val]! ∧ hK (t.val + 8) = symWi omSchW[t.val]! := by
  decide +kernel

theorem ch9558root0 : keyK (F 0) = canonK zK := by
  decide +kernel

theorem ch9558roots : ∀ k : Fin 4, keyK (F rootIdx[k.val]!) =
    stepK (wordS6 omSeedW[k.val]!) (wordS6 (omSeedW[k.val]!).reverse) zK := by
  decide +kernel

theorem ch9558quad : Nat.xor (Nat.xor (mulS6 zK zK) zK) idP = 0 := by
  decide +kernel

theorem ch9558eps : ∀ j : Fin 4, mulS6 (mulS6 (gK j.val) zK) (gK (j.val + 4)) =
    if j.val % 2 = 1 then mulS6 zK zK else zK := by
  decide +kernel

theorem ch9558rev : ∀ j : Fin 4,
    mulS6 (gK j.val) (gK (j.val + 4)) = idP ∧ mulS6 (gK (j.val + 4)) (gK j.val) = idP := by
  decide +kernel

theorem ch9558seedrev : ∀ k : Fin 4,
    mulS6 (wordS6 omSeedW[k.val]!) (wordS6 (omSeedW[k.val]!).reverse) = idP ∧
      mulS6 (wordS6 (omSeedW[k.val]!).reverse) (wordS6 omSeedW[k.val]!) = idP := by
  decide +kernel

theorem ch9558letters : omSchW.length = 8 ∧ ∀ w ∈ omSchW, ∀ s ∈ w, s < 8 := by
  decide +kernel

theorem ch9558hroot : keyK (H 0) = keyK (F 3263) := by
  decide +kernel

theorem ch9558fix :
    allFrom 0 8 (fun t => Nat.beq (stepK (hK t) (hK (Nat.add t 8)) (keyK (F 1))) (keyK (F 1))) =
      true := by
  decide +kernel

theorem ch9558h0 : allFrom 0 512 (hAt H) = true := by
  decide +kernel

theorem ch9558h1 : allFrom 512 512 (hAt H) = true := by
  decide +kernel

theorem ch9558hs : allFrom 0 1024 (sortAt H HS 1024) = true := by
  decide +kernel

end CFSG.KC.CertF8.Om9558

end
