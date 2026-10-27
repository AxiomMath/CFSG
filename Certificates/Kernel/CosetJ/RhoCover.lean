module

public import CFSG.Certificates.Kernel.Misc.Coset.ActPermRep

public section

namespace CertificateChecks.KernelCosetJ.RhoCover

open CFSG.Certificates CFSG.Certificates.CosetEnumeration CFSG.KC.MiscCoset

theorem signedProd_reverse_inv {m : ℕ} {G : Type*} [Group G] (τ : Fin m → G)
    (u : List (Fin m × Bool)) :
    signedProd (fun g => (τ g)⁻¹) u.reverse = (signedProd τ u)⁻¹ := by
  induction u with
  | nil => simp
  | cons l u ih =>
    obtain ⟨g, b⟩ := l
    rw [List.reverse_cons, signedProd_append, ih]
    cases b <;> simp [signedProd_cons, mul_inv_rev]

theorem revCodes_reverse {m : ℕ} (ws : List (List (Fin m × Bool))) :
    (ws.map List.reverse).map Act.revCodes = codes ws := by
  simp only [List.map_map, codes]
  congr 1
  funext u
  simp [Act.revCodes, List.map_reverse]

theorem cover_trivial {m N : ℕ} {A B : ℕ → ℕ} (R : List (List (Fin m × Bool)))
    (w : Fin m → List (Fin m × Bool)) (extra : List (List (Fin m × Bool)))
    {Rc Wc : List (List ℕ)} (hR : codes R = Rc)
    (hW : codes ((List.finRange m).map fun i => (i, false) :: w i) ++ codes extra = Wc)
    (h : ∀ x < N, Act.coverPointOK A B m N Rc Wc x = true) :
    ∃ σ : Fin m → Equiv.Perm (Fin N), Act.Rep A m N σ ∧
      ∀ u ∈ CFSG.LieType.Multipliers.coverWords R w ++ extra,
        signedProd (fun g => (σ g)⁻¹) u = 1 := by
  have hp := Act.coverPointOK_sound R w extra hR hW h
  obtain ⟨σ, hσ⟩ := Act.exists_rep hp
  refine ⟨σ, hσ, fun u hu => ?_⟩
  have hw := Act.relsAt_sound hσ ((CFSG.LieType.Multipliers.coverWords R w ++ extra).map
    List.reverse) (revCodes_reverse _) (fun x hx => Act.relsAt_of_pointOK (hp x hx))
    u.reverse (List.mem_map_of_mem hu)
  have e := signedProd_reverse_inv (fun g => (σ g)⁻¹) u
  simp only [inv_inv] at e
  rw [e, inv_eq_one] at hw
  exact hw

theorem ne_one_of_distinct {m N : ℕ} {A : ℕ → ℕ} {σ : Fin m → Equiv.Perm (Fin N)}
    (hσ : Act.Rep A m N σ) (u : List (Fin m × Bool)) {rels : List (List ℕ)}
    (hrels : [[], u.map letterCode] = rels) {base ord : List ℕ}
    (h : Act.distinctOK A (Nat.add m m) N rels base ord = true) :
    signedProd (fun g => (σ g)⁻¹) u ≠ 1 := by
  have hr : ([[], u.reverse] : List (List (Fin m × Bool))).map Act.revCodes = rels := by
    rw [← hrels]
    simp [Act.revCodes, codes, List.map_reverse]
  have hd := Act.distinctOK_sound hσ [[], u.reverse] hr h 0 1 (by simp) (by simp)
  intro h1
  have e := signedProd_reverse_inv (fun g => (σ g)⁻¹) u
  simp only [inv_inv] at e
  rw [h1, inv_one] at e
  exact absurd (hd (by simp [e])) (by decide)

end CertificateChecks.KernelCosetJ.RhoCover

end
