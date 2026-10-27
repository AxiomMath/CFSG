module

public import CFSG.Quasithin.Vol2.Asc94.He42Base
public import CFSG.Quasithin.Vol2.Asc94.HeK4
public import CFSG.Sporadic.Schreier.J4SOrder
public import CFSG.Sporadic.Th.KernelPlanes
public import CFSG.Sporadic.Th.Local
public import CFSG.Sporadic.ThSchreier.AutCore

public section

namespace CFSG.Quasithin.A94.He42

open Matrix Subgroup CFSG.CGT.M24S CFSG.Open CFSG.Quasithin.A94.HeJ

namespace HeSetup

variable {G : Type} [Group G] [Finite G] {z : G}

@[expose] noncomputable def ofCtx (e : ↥(Cz z) ≃* L52.Hc) (hF6 : L52.F6Model) (S : Setting G z e)
    (h1 : normalizer (tr e L52.U1 : Set G) = Cz z) (h2 : normalizer (tr e L52.U2 : Set G) = Cz z)
    {a x : G} (ha : a ∈ tr e L52.A1 ⊓ tr e L52.A2) (ham : HeJ.mG e a = 1)
    (hxN : x ∈ normalizer ((tr e L52.A1 ⊔ tr e L52.A2 : Subgroup G) : Set G))
    (hxa : x ∈ centralizer ({a} : Set G)) (hx3 : orderOf x = 3) : HeSetup G where
  A := tr e L52.A1
  A' := tr e L52.A2
  u := HeJ.uG e
  w := HeJ.wG e
  m := HeJ.mG e
  N := normalizer ((tr e L52.A1 ⊔ tr e L52.A2 : Subgroup G) : Set G)
  T := tr e L52.Tm
  a := a
  x := x
  hD := HeJ.data40 e hF6 S h1 h2 ha ham
  hD' := HeJ.data40_symm e hF6 S h1 h2 ha ham
  hN := rfl
  hxN := hxN
  hxa := hxa
  hx3 := hx3
  h5 := by
    intro g hg5
    by_contra hcon
    push Not at hcon
    have hz := S.ord
    have hzZ : z ∈ tr e L52.A1 ⊓ tr e L52.A2 := (frame4 e hz hF6).z_mem_B
    have hgz : g ∈ Cz z := mem_centralizer_singleton_iff.2 (hcon z hzZ)
    have hdvd : orderOf (⟨g, hgz⟩ : ↥(Cz z)) ∣ Nat.card ↥(Cz z) := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hg5, (frame0 e hz).card_H] at hdvd
    omega

variable (e : ↥(Cz z) ≃* L52.Hc) (hF6 : L52.F6Model) (S : Setting G z e)
    (h1 : normalizer (tr e L52.U1 : Set G) = Cz z) (h2 : normalizer (tr e L52.U2 : Set G) = Cz z)
    {a x : G} (ha : a ∈ tr e L52.A1 ⊓ tr e L52.A2) (ham : HeJ.mG e a = 1)
    (hxN : x ∈ normalizer ((tr e L52.A1 ⊔ tr e L52.A2 : Subgroup G) : Set G))
    (hxa : x ∈ centralizer ({a} : Set G)) (hx3 : orderOf x = 3)

end HeSetup

end CFSG.Quasithin.A94.He42
