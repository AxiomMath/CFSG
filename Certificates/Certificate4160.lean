
module

public import Certificates.Certificate4160Base

public import CFSG.Quasithin.Vol2.GoldschmidtF45RuLocal
public import CFSG.Quasithin.Vol2.GoldschmidtF45RuLayers
public import CFSG.Quasithin.Vol2.GoldschmidtF45RuModel
import Certificates.Kernel.TitsOct.Glue

public section

open CFSG.Quasithin CFSG.Quasithin.H13.F45Ru

public section

namespace Certificates

open CertificateChecks

open CFSG.Quasithin CFSG.Quasithin.H13.F45Ru in
local notation "TA" => CFSG.Sporadic.Schreier.Tits.titsA

theorem certificate4160 : IsGenPolygon octGraph 8 ∧ (∀ x : Vtx, ∃ lay, Layers octGraph 8 x lay) ∧
    
      (∃ (b₀ w₀ w₁ : Vtx) (Fg : Set ↥TA) (L : Finset ↥TA),
        LocalData ↥TA octGraph 8 (Sum.inl 0) b₀ w₀ w₁ Fg L 20480 1024 5) ∧
      (∃ (b₀ w₀ w₁ : Vtx) (Fg : Set ↥TA) (L : Finset ↥TA),
        LocalData ↥TA octGraph 8 (Sum.inr 0) b₀ w₀ w₁ Fg L 12288 2048 3) ∧
      ∀ v : Fin 2925, ∃ g : ↥TA, g • (Sum.inr 0 : Vtx) = Sum.inr v :=
  ⟨KernelTitsOct.facts.1, KernelTitsOct.facts.2.1, KernelTitsOct.facts.2.2⟩

end Certificates
