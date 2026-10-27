module

public import Certificates.Data.Kernel.PermCent.CV
public import Certificates.Data.OmegaB0

public section

namespace CFSG.Certificates.Kernel.PkCV.B0T

open CFSG.ComponentClassification.CatFactsSmall.PSp43 Certificates.OmegaB0

@[expose] noncomputable def phiC (B : List (CV 45)) : List (CV 45) :=
  (List.range 32).map fun n =>
    ((List.finRange 5).map fun j => if vecOfNat n j = 1 then B.getD (j : ℕ) 1 else 1).prod

@[expose] noncomputable def phi0C (Φ : List (CV 45)) (v : Fin 5 → ZMod 2) : CV 45 :=
  Φ.getD (vcode v) 1

@[expose] noncomputable def phC : List (CV 45) := phiC ((bl ()).map cOf)

@[expose] noncomputable def bElemsC (Φ : List (CV 45)) (allV : List (Fin 5 → ZMod 2)) :
    List (CV 45) :=
  (allV.filter fun v => decide (∑ i, v i = 0)).map (phi0C Φ)

@[expose] noncomputable def blC : List (CV 45) := bElemsC phC (allVecs ())

@[expose] noncomputable def closedC (Bl : List (CV 45)) : Bool :=
  decide (Bl.length = 16 ∧ Bl.Nodup) && decide ((1 : CV 45) ∈ Bl) &&
    Bl.all fun a => decide (a⁻¹ ∈ Bl) && decide (a * a = 1) &&
      Bl.all fun b => decide (a * b ∈ Bl) && decide (a * b = b * a)

@[expose] noncomputable def sylowC (T Bl : List (CV 45)) : Bool :=
  Bl.all (fun b => decide (b ∈ T)) &&
    T.all fun a => decide (a ∈ Bl) ||
      (let C := T.filter fun g => decide (g * a = a * g)
       decide (C.length ≤ 16) &&
        (decide (C.length < 16) || C.any fun x => C.any fun y => decide (x * y ≠ y * x)))

@[expose] noncomputable def centC (A0 Bl : List (CV 45)) : Bool :=
  A0.all fun a => !(Bl.all fun b => eq22C a b b a) || decide (a ∈ Bl)

@[expose] noncomputable def homC (Φ : List (CV 45)) (allV : List (Fin 5 → ZMod 2)) : Bool :=
  allV.all fun v => allV.all fun w =>
    decide (phi0C Φ (v + w) = phi0C Φ v * phi0C Φ w) &&
      (!(decide (∑ i, v i = 0) && decide (∑ i, w i = 0) && decide (phi0C Φ v = phi0C Φ w)) ||
        decide (v = w))

@[expose] noncomputable def normBC (Bl : List (CV 45)) (n : CV 45) : Bool :=
  Bl.all fun b => decide (n * b * n⁻¹ ∈ Bl) && decide (n⁻¹ * b * n ∈ Bl)

@[expose] noncomputable def actEqC (Φ : List (CV 45)) (allV : List (Fin 5 → ZMod 2)) (n : CV 45)
    (σ : Equiv.Perm (Fin 5)) : Bool :=
  allV.all fun v => decide (n * phi0C Φ v * n⁻¹ = phi0C Φ (v ∘ σ.symm))

@[expose] noncomputable def conjIdxC (bs : List (CV 45)) (n : CV 45) : List ℕ :=
  bs.map fun b => bs.findIdx fun c => decide (n * b * n⁻¹ = c)

@[expose] noncomputable def actC (L0 A0 bs : List (CV 45)) (Φ : List (CV 45)) (Bl : List (CV 45))
    (allV : List (Fin 5 → ZMod 2)) (S5 : List (Equiv.Perm (Fin 5))) : Bool :=
  let NP := L0.filter (normBC Bl)
  (NP.all fun n => let τ := conjIdxC bs n
    S5.any fun σ => matchIdx τ σ && decide (Equiv.Perm.sign σ = 1) && actEqC Φ allV n σ) &&
    ((A0.filter (normBC Bl)).all fun n => let τ := conjIdxC bs n
      S5.any fun σ => matchIdx τ σ && actEqC Φ allV n σ) &&
    S5.all fun σ => !decide (Equiv.Perm.sign σ = 1) ||
      NP.any fun n => matchIdx (conjIdxC bs n) σ && actEqC Φ allV n σ

@[expose] noncomputable def classC (L0 : List (CV 45)) (Φ : List (CV 45))
    (allV : List (Fin 5 → ZMod 2)) : Bool :=
  let a := cOf (Certificates.P43Twin.tA ())
  let b := cOf (Certificates.P43Twin.tB ())
  allV.all fun v =>
    (!(decide (∑ i, v i = 0) && decide ((Finset.univ.filter fun i : Fin 5 => v i ≠ 0).card = 4)) ||
      L0.any fun c => eq22C c a (phi0C Φ v) c) &&
    (!(decide (∑ i, v i = 0) && decide ((Finset.univ.filter fun i : Fin 5 => v i ≠ 0).card = 2)) ||
      L0.any fun c => eq22C c b (phi0C Φ v) c)

end CFSG.Certificates.Kernel.PkCV.B0T

end
