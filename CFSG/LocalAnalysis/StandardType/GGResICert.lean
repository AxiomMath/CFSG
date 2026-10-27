module

public import CFSG.LocalAnalysis.StandardType.GGResIWitness
public import CFSG.LocalAnalysis.StandardType.GGResIWStar
public import CFSG.LocalAnalysis.StandardType.GGResIICert
public import CFSG.LocalAnalysis.StandardType.GGResILinDefs
public import CFSG.LocalAnalysis.StandardType.GGResIStd

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open GGPoly

namespace GGPoly

variable {N : ℕ}

@[expose] def fH (T : Fin N → Vector GGPoly (N + 1)) (t : Fin N × List (Fin N)) :
    Vector GGPoly (N + 1) :=
  fword T t.2 (funit t.1.castSucc)

theorem evalV_fH {S : Type} [CommRing S] (u v : S) (T : Fin N → Vector GGPoly (N + 1))
    (t : Fin N × List (Fin N)) : evalV u v (fH T t) = ggFH (evalT u v T) t := by
  rw [fH, evalV_fword, evalV_funit, ggFH]

theorem eval_fH {S : Type} [CommRing S] (u v : S) (T : Fin N → Vector GGPoly (N + 1))
    (t : Fin N × List (Fin N)) (l : Fin (N + 1)) :
    eval u v ((fH T t).get l) = (ggFH (evalT u v T) t).get l := by
  rw [← evalV_fH, get_evalV]

end GGPoly

section Bad

variable {p : ℕ} [Fact p.Prime]

theorem ggTriBad_of_pair {a : Fin 3 → Fin 3 → ZMod p}
    (h : a 1 2 * a 2 1 ∉ ({0, 1, 2, 3, 4} : Set (ZMod p))) : GGTriBad p a := by
  refine ⟨Or.inl ⟨fun h0 => h (by simp [h0]), fun h4 => h (by simp [h4])⟩, ?_⟩
  rintro ⟨P01, P02, P12, τ, -, -, -, -, h0, h4, -, -, h12, -⟩
  apply h
  rw [← h12]
  interval_cases P12 <;> simp

theorem ggTriBad_of_tau {a : Fin 3 → Fin 3 → ZMod p}
    (h : a 0 1 * a 1 2 * a 2 0 ≠ a 0 2 * a 2 1 * a 1 0) : GGTriBad p a := by
  refine ⟨Or.inr (Or.inl h), ?_⟩
  rintro ⟨P01, P02, P12, τ, -, -, -, -, -, -, -, -, -, h1, h2, -⟩
  exact h (h1.symm.trans h2)

end Bad

inductive GGTreeI (n : ℕ) where
  | tv (t₁ t₂ : Fin (n + 1) × List (Fin (n + 1))) (l₀ z : Fin (n + 2)) (cs : List CertV)
      (n₁ n₂ nY : CertNV)
  | tvk (t₁ t₂ : Fin (n + 1) × List (Fin (n + 1))) (o₀ l : Fin (n + 1)) (cs : List CertV)
      (n₁ n₂ nC : CertNV)
  | tri (t : Fin (n + 1) × List (Fin (n + 1))) (j' : Fin (n + 1)) (cs : List CertNV)
  | triple (t : Fin (n + 1) × List (Fin (n + 1))) (j' : Fin (n + 1)) (nt : CertNV)
  | wstar (typ : GGWTypeI) (ts : List (Fin (n + 1) × List (Fin (n + 1)))) (dd : List GGPoly)
      (lam : List (List GGPoly)) (dz : GGPoly) (cpair : List (List CertV)) (cnz : List CertNV)
      (nz : CertNV) (clam : List (List CertV))
  | split (s₁ s₂ : GGPoly) (m₁ m₂ : ℕ) (cv : CertV) (l r : GGTreeI n)
  | empty (cv : CertV)
  | triOr (t : Fin (n + 1) × List (Fin (n + 1))) (j' : Fin (n + 1)) (c₀ c₁ c₂ c₃ c₄ : GGTreeI n)

section Check

variable {n : ℕ} (M : ℕ) (Ts : Fin (n + 1) → Vector GGPoly (n + 2)) (ib : Fin n)

@[expose] def checkTVI (E : List GGPoly) (t₁ t₂ : Fin (n + 1) × List (Fin (n + 1)))
    (l₀ z : Fin (n + 2)) (cs : List CertV) (n₁ n₂ nY : CertNV) : Bool :=
  (fun H₁ H₂ : Vector GGPoly (n + 2) =>
    (List.finRange (n + 1)).all (fun l =>
      checkV M E (sub (mul (H₂.get l₀) (H₁.get l.castSucc)) (mul (H₁.get l₀) (H₂.get l.castSucc)))
        (cs.getD l.val CertV.dflt)) &&
    checkNV M E (H₁.get l₀) n₁ && checkNV M E (H₂.get l₀) n₂ &&
    checkNV M E (sub (mul (H₁.get l₀) (frootAt Ts (fC Ts t₁) (funit z)))
      (mul (H₂.get l₀) (frootAt Ts (fC Ts t₂) (funit z)))) nY)
  (fH Ts t₁) (fH Ts t₂)

@[expose] def checkTVkI (E : List GGPoly) (t₁ t₂ : Fin (n + 1) × List (Fin (n + 1)))
    (o₀ l : Fin (n + 1)) (cs : List CertV) (n₁ n₂ nC : CertNV) : Bool :=
  (fun c₁ c₂ : Vector GGPoly (n + 1) =>
    (List.finRange (n + 1)).all (fun o =>
      checkV M E (sub (mul (fdualAt Ts c₂ o₀) (fdualAt Ts c₁ o))
        (mul (fdualAt Ts c₁ o₀) (fdualAt Ts c₂ o))) (cs.getD o.val CertV.dflt)) &&
    checkNV M E (fdualAt Ts c₂ o₀) n₁ && checkNV M E (fdualAt Ts c₁ o₀) n₂ &&
    checkNV M E (sub (mul (fdualAt Ts c₁ o₀) ((fH Ts t₁).get l.castSucc))
      (mul (fdualAt Ts c₂ o₀) ((fH Ts t₂).get l.castSucc))) nC)
  (fC Ts t₁) (fC Ts t₂)

@[expose] def triTau (t : Fin (n + 1) × List (Fin (n + 1))) (j' : Fin (n + 1)) : GGPoly :=
  sub (mul (mul ((Ts t.1).get j'.castSucc) ((fA Ts t).get j')) (fdualAt Ts (fC Ts t) t.1))
    (mul (mul ((fA Ts t).get t.1) (fdualAt Ts (fC Ts t) j')) ((Ts j').get t.1.castSucc))

@[expose] def checkTripleI (E : List GGPoly) (t : Fin (n + 1) × List (Fin (n + 1)))
    (j' : Fin (n + 1)) (nt : CertNV) : Bool :=
  inJ ib t.1 && inJ ib j' && checkNV M E (triTau Ts t j') nt

@[expose] def wstarGen (ts : Fin (n + 1) → Fin (n + 1) × List (Fin (n + 1))) : Bool :=
  (List.finRange (n + 1)).all fun k =>
    (List.finRange (n + 1)).any (fun m => decide (ts m = (k, []))) ||
    (List.finRange (n + 1)).any (fun i => decide ((ts i).1 = k) && (ts i).2.all fun l =>
      (List.finRange (n + 1)).any fun m => decide (ts m = (l, [])))

@[expose] def checkWStarI (E : List GGPoly) (typ : GGWTypeI)
    (ts : List (Fin (n + 1) × List (Fin (n + 1)))) (dd : List GGPoly) (lam : List (List GGPoly))
    (dz : GGPoly) (cpair : List (List CertV)) (cnz : List CertNV) (nz : CertNV)
    (clam : List (List CertV)) : Bool :=
  (fun (t : Fin (n + 1) → Fin (n + 1) × List (Fin (n + 1))) (d : Fin (n + 1) → GGPoly)
      (ll : Fin (n + 1) → Fin (n + 1) → GGPoly) =>
    ggWTypeOk typ (n + 1) && wstarGen t && checkNV M E dz nz &&
    (List.finRange (n + 1)).all (fun i => checkNV M E (d i) (cnz.getD i.val CertNV.dflt)) &&
    (List.finRange (n + 1)).all (fun i => (List.finRange (n + 1)).all fun j =>
      checkV M E (sub (mul (d i) (frootAt Ts (fC Ts (t j)) (fH Ts (t i))))
        (mul (d j) (const (ggWCartanI typ (n + 1) i j))))
        ((cpair.getD i.val []).getD j.val CertV.dflt)) &&
    (List.finRange (n + 1)).all (fun i => (List.finRange (n + 1)).all fun o =>
      checkV M E (sub ((List.finRange (n + 1)).foldr
          (fun l acc => add (mul ((fH Ts (t i)).get l.castSucc) (ll l o)) acc) [])
        (if i = o then dz else []))
        ((clam.getD i.val []).getD o.val CertV.dflt)))
  (fun i => ts.getD i.val (0, [])) (fun i => dd.getD i.val [])
  (fun o i => (lam.getD o.val []).getD i.val [])

@[expose] def checkTreeI : List GGPoly → GGTreeI n → Bool
  | E, .tv t₁ t₂ l₀ z cs n₁ n₂ nY => checkTVI M Ts E t₁ t₂ l₀ z cs n₁ n₂ nY
  | E, .tvk t₁ t₂ o₀ l cs n₁ n₂ nC => checkTVkI M Ts E t₁ t₂ o₀ l cs n₁ n₂ nC
  | E, .tri t j' cs => checkTRI M Ts ib E t j' cs
  | E, .triple t j' nt => checkTripleI M Ts ib E t j' nt
  | E, .wstar typ ts dd lam dz cpair cnz nz clam =>
    checkWStarI M Ts E typ ts dd lam dz cpair cnz nz clam
  | E, .split s₁ s₂ m₁ m₂ cv l r =>
    checkV M E (mul (pow s₁ m₁) (pow s₂ m₂)) cv && checkTreeI (E ++ [s₁]) l &&
      checkTreeI (E ++ [s₂]) r
  | E, .empty cv => checkV M E (const 1) cv
  | E, .triOr t j' c₀ c₁ c₂ c₃ c₄ =>
    inJ ib t.1 && inJ ib j' &&
      (fun P => checkTreeI (E ++ [sub P (const 0)]) c₀ && checkTreeI (E ++ [sub P (const 1)]) c₁ &&
        checkTreeI (E ++ [sub P (const 2)]) c₂ && checkTreeI (E ++ [sub P (const 3)]) c₃ &&
        checkTreeI (E ++ [sub P (const 4)]) c₄) (pairPoly Ts t j')

end Check

end CFSG.StandardType
