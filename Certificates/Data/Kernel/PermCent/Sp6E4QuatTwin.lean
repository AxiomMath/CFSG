module

public import Certificates.Data.Kernel.PermCent.Sp6E4Twin

public section

namespace CFSG.Certificates.Kernel.PkCV.Sp6E

open CFSG.EvenSmallLie.Sp6 CFSG.ClassicalInvolution.Q3.TL4.E4Sp6
  CFSG.ClassicalInvolution.Q3.TL4.E4Sp6Data CFSG.Certificates.Kernel.PkCV.Sp6B

variable {n : Nat} [Small n]

@[expose] noncomputable def q8C (r i j : CV n) : List (CV n) := [1, r, i, i * r, j, j * r, i * j, i * j * r]

@[expose] noncomputable def normsN (L : List (CV n)) (i j h : CV n) : Bool :=
  decide (h * i * h⁻¹ ∈ L) && decide (h * j * h⁻¹ ∈ L)

@[expose] noncomputable def closedLC (L : List (CV n)) (i j : CV n) : Bool :=
  decide ((1 : CV n) ∈ L) && L.all fun x =>
    decide (i * x ∈ L) && decide (j * x ∈ L) && decide (i⁻¹ * x ∈ L) && decide (j⁻¹ * x ∈ L)

@[expose] noncomputable def lettersC (gens : List (CV n)) : List (CV n) := gens ++ gens.map (·⁻¹)

@[expose] noncomputable def memberCheckC (gens L : List (CV n)) (i j : CV n) (ws : List (CV n))
    (σ : List (List ℕ)) : Bool :=
  decide (0 < ws.length) && decide (ws.getD 0 1 = 1) && (List.range ws.length).all fun k =>
    (List.range (lettersC gens).length).all fun l =>
      decide ((σ.getD k []).getD l 0 < ws.length) &&
        normsN L i j ((ws.getD ((σ.getD k []).getD l 0) 1)⁻¹ * (lettersC gens).getD l 1 *
          ws.getD k 1)

@[expose] noncomputable def treeStepC (L : List (CV n)) (i j u gp gk : CV n) (d : Bool) : Bool :=
  !normsN L i j (gp⁻¹ * gk) &&
    (if d then normsN L i j (gk⁻¹ * (gp * u * gp⁻¹) * gk)
      else normsN L i j (gp⁻¹ * (gk * u * gk⁻¹) * gp))

@[expose] noncomputable def treeCheckC (L U : List (CV n)) (i j : CV n) (ws : List (CV n))
    (tree : List (ℕ × Bool × ℕ)) : Bool :=
  U.all (fun u => decide (u ∈ L) && !decide (u ^ 2 = 1) && decide (u ^ 4 = 1)) &&
    (List.range ws.length).all fun k => k == 0 ||
      (decide ((tree.getD k (0, false, 0)).1 < k) &&
        decide ((tree.getD k (0, false, 0)).2.2 < U.length) &&
        treeStepC L i j (U.getD (tree.getD k (0, false, 0)).2.2 1)
          (ws.getD (tree.getD k (0, false, 0)).1 1) (ws.getD k 1) (tree.getD k (0, false, 0)).2.1)

@[expose] noncomputable def nbrCheckC (L : List (CV n)) (i j : CV n) (ws : List (CV n))
    (allowed : List ℕ) : Bool :=
  (List.range ws.length).all fun k => decide (k ∈ allowed) ||
    !(normsN L i j (ws.getD k 1 * i * (ws.getD k 1)⁻¹) &&
      normsN L i j (ws.getD k 1 * j * (ws.getD k 1)⁻¹))

@[expose] noncomputable def edgeCheckC (L : List (CV n)) (i j g : CV n) : Bool :=
  !normsN L i j g && normsN L i j (g * i * g⁻¹) && normsN L i j (g * j * g⁻¹)

@[expose] noncomputable def violatesC (T : List (CV n)) (i j c : CV n) : Bool :=
  T.any (fun x => !decide (c * x * c⁻¹ ∈ T)) &&
    [i, j].any fun x => [c * i * c⁻¹, c * j * c⁻¹].any fun y => !decide (x * y = y * x)

@[expose] noncomputable def sameSetC (A B : List (CV n)) : Bool :=
  A.all (fun x => decide (x ∈ B)) && B.all (fun x => decide (x ∈ A))

@[expose] noncomputable def identStepC (r ρ : CV n) (W L0 L1 : List (CV n)) (j : CV n) : Bool :=
  !(decide (j * j = r) && decide (j * ρ * j⁻¹ = ρ⁻¹)) ||
    (sameSetC (q8C r ρ j) L0 || sameSetC (q8C r ρ j) L1 || W.any (violatesC (q8C r ρ j) ρ j))

@[expose] noncomputable def identCheckC (r : CV n) (reps C W L0 L1 : List (CV n)) : Bool :=
  reps.all fun ρ => !decide (ρ * ρ = r) || C.all fun j => identStepC r ρ W L0 L1 j

@[expose] noncomputable def p124a : Bool :=
  decide (iC * iC = r2C) && closedLC L0C iC jC && edgeCheckC L0C iC jC (wsC.getD 11 1)

@[expose] noncomputable def p124i1 : Bool :=
  identCheckC (cOf sp6Rep1) (sp6FourReps1.map cOf) (elemsC sp6CentQ1) [] [] []

@[expose] noncomputable def p124i2 : Bool :=
  identCheckC r2C (sp6FourReps2.map cOf) E2 [cOf (sp6CentGens2.getD 0 1)] L0C L1C

@[expose] noncomputable def p124i3 : Bool :=
  identCheckC (cOf sp6Rep3) (sp6FourReps3.map cOf) (elemsC sp6CentQ3) [] [] []

@[expose] noncomputable def p124i4 : Bool :=
  identCheckC (cOf sp6Rep4) (sp6FourReps4.map cOf) (elemsC sp6CentQ4) [] [] []

@[expose] noncomputable def p124m : Bool := memberCheckC G L0C iC jC wsC memberSigma

@[expose] noncomputable def p124t : Bool := treeCheckC L0C (L0C.drop 2) iC jC wsC memberTree

@[expose] noncomputable def p124n : Bool := nbrCheckC L0C iC jC wsC [0, 11]

end CFSG.Certificates.Kernel.PkCV.Sp6E

end
