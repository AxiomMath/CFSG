module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP0

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open

@[expose] def D1h : Subgroup Ah := P1h ⊓ Yh ⊓ Subgroup.centralizer ({fhatA} : Set Ah)

@[expose] def D2h : Subgroup Ah := P2h ⊓ Yh ⊓ Subgroup.centralizer ({fhatA} : Set Ah)

@[expose] def IsCoxPair (s t : Ah) : Prop :=
  s ∈ D1h ∧ s ∉ Bh ∧ s ^ 2 = 1 ∧ t ∈ D2h ∧ t ∉ Bh ∧ t ^ 2 = 1 ∧ (s * t) ^ 4 = 1 ∧
    (s * t) ^ 2 ≠ 1

@[expose] def U42AutIotaOfCox : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M₁ M₂ : Subgroup G) (z : G) (c : AutCtx G M₁ M₂ z)
    (s : ↥P1h) (t : ↥P2h), IsCoxPair (s : Ah) (t : Ah) →
    (((c.iso.phi1 s : ↥M₁) : G) * ((c.iso.phi2 t : ↥M₂) : G)) ^ 4 = 1 →
    ∃ ι : Ah ≃* ↥(M₁ ⊔ M₂), (∀ x : P1h, (ι (x : Ah) : G) = (c.iso.phi1 x : G)) ∧
      ∀ x : P2h, (ι (x : Ah) : G) = (c.iso.phi2 x : G)

end CFSG.Quasithin.H13.F431.U42Aut
