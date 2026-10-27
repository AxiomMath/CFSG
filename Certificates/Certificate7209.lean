
module

public import CFSG.Quasithin.Background.H12OneHatM22PfInputs
public import CFSG.Quasithin.H13.L32NMatNGen
import CFSG.Certificates.Kernel.H12Glue
import Certificates.Kernel.H12.H12C1
import Certificates.Kernel.H12.H12C2
import Certificates.Kernel.H12.H12C3
import Certificates.Kernel.H12.H12Ov4N

public section

namespace Certificates

open CertificateChecks.KernelH12 in
open CFSG.Quasithin.H13.MatNCert CFSG.Quasithin.H.Mathieu.H12Cert in
theorem certificate7209 :
    (∀ v ∈ List.range 4096, mvN z12 v ≠ v ∨ v = 0) ∧
    (orbL.head? = some (v0, []) ∧ orbL.length = 693 ∧ (orbL.map Prod.fst).Nodup ∧
      ∀ uw ∈ orbL, mvN (tW uw.2) v0 = uw.1) ∧
    (∀ uw ∈ orbL, ∀ g ∈ gG, ∃ uw' ∈ orbL, uw'.1 = mvN g uw.1 ∧
      ∃ s ∈ genSubN 12 s0G,
        mulN (tW uw'.2) (colsN (s : Matrix (Fin 12) (Fin 12) (ZMod 2))) = mulN g (tW uw.2)) ∧
    (Nat.card (genSubN 12 s0G) = 1920 ∧
      ∀ s ∈ genSubN 12 s0G, mvN (colsN (s : Matrix (Fin 12) (Fin 12) (ZMod 2))) v0 = v0) ∧
    (Nat.card (genSubN 12 tG) = 128 ∧
      (∀ g ∈ tG, ∃ s ∈ genSubN 12 s0G, colsN (s : Matrix (Fin 12) (Fin 12) (ZMod 2)) = g) ∧
      ∀ v ∈ List.range 4096, (tG.all fun g => mvN g v == v) = false ∨ v ∈ f0) ∧
    (∀ uw ∈ orbL, uw.1 ∈ f0 ∨ uw.1 ∈ UC ∨
      ∃ t₁ ∈ genSubN 12 tG, ∃ t₂ ∈ genSubN 12 tG,
        lineNe uw.1 (mvN (colsN (t₁ : Matrix (Fin 12) (Fin 12) (ZMod 2))) uw.1) = true ∧
        lineNe uw.1 (mvN (colsN (t₂ : Matrix (Fin 12) (Fin 12) (ZMod 2))) uw.1) = true ∧
        lineNe (mvN (colsN (t₁ : Matrix (Fin 12) (Fin 12) (ZMod 2))) uw.1)
          (mvN (colsN (t₂ : Matrix (Fin 12) (Fin 12) (ZMod 2))) uw.1) = true) ∧
    (∀ r ∈ rP, (∃ s ∈ genSubN 12 s0G, colsN (s : Matrix (Fin 12) (Fin 12) (ZMod 2)) = r.1) ∧
      mulN r.1 r.2 = one12) ∧
    (∀ s ∈ genSubN 12 s0G, ∃ r ∈ rP, ∃ t ∈ genSubN 12 tG,
      colsN (t : Matrix (Fin 12) (Fin 12) (ZMod 2)) =
        mulN r.2 (colsN (s : Matrix (Fin 12) (Fin 12) (ZMod 2)))) ∧
    (∀ u ∈ UC, ∃ w : List ℕ, mvN (tW w) v0 = u ∧ ∀ r ∈ rP,
      (∃ w' : List ℕ, evalW 12 rG w' = mulN (tW w) r.1) ∨
      ∃ c₁ c₂ c₃ : ℕ, (∀ c ∈ [c₁, c₂, c₃], c ≠ 0 ∧ lineNe v0 c = true ∧
          ∃ w' : List ℕ, mvN (evalW 12 (tG ++ [z12, mulN (tW w) r.1]) w') v0 = c) ∧
        lineNe c₁ c₂ = true ∧ lineNe c₁ c₃ = true ∧ lineNe c₂ c₃ = true) ∧
    Nat.card (genSubN 12 rG) = 1152 ∧ mvN y0 v0 ∉ f0 :=
  CFSG.KC.H12K.cert7209_of h12_zB_true h12_orbB_true h12_wB_true h12_tB2_true h12_cosS_true
    h12_cosR_true h12_schC_true h12_ov1C_true h12_ov4N_true

end Certificates
