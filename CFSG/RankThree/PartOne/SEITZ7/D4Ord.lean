module

public import CFSG.RankThree.PartOne.SEITZ7.D4Blk
public import CFSG.LieType.Steinberg.TwistedD4.Perfect

public section

namespace CFSG.RankThree.PartOne.SEITZ7

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
open scoped commutatorElement

variable {K : Type} [Field K] (σ : K →+* K)

@[expose] def dpos : List ℕ := [2, 0, 1, 3, 5, 7, 9, 12, 13, 15, 19, 22]

@[expose] noncomputable def ordD (e : ℕ → K) : adjointGroup d4 K :=
  xd 2 (e 2) * xd 0 (e 0) * xd 1 (e 1) * xd 3 (e 3) * xd 5 (e 5) * xd 7 (e 7) * xd 9 (e 9) *
    xd 12 (e 12) * xd 13 (e 13) * xd 15 (e 15) * xd 19 (e 19) * xd 22 (e 22)

@[expose] def htD4 : (Fin d4.rank → ℤ) →+ ℤ :=
  Pi.evalAddMonoidHom (fun _ => ℤ) (nd 0) + Pi.evalAddMonoidHom (fun _ => ℤ) (nd 1) +
    Pi.evalAddMonoidHom (fun _ => ℤ) (nd 2) + Pi.evalAddMonoidHom (fun _ => ℤ) (nd 3)

theorem dpos_lt {p : ℕ} (hp : p ∈ dpos) : p < 24 := by
  simp only [dpos, List.mem_cons, List.not_mem_nil, or_false] at hp
  omega

theorem dpos_pos_height : ∀ p ∈ dpos, 0 < htD4 (d4Root p) := by decide +kernel

theorem d4_roots_length : (Tag.rootCertificate d4).roots.length = 24 := by decide +kernel

theorem ordD_injective [CharP K 2] {e e' : ℕ → K} (h : ordD e = ordD e') :
    ∀ p ∈ dpos, e p = e' p := by
  set L : List (Fin d4.rank → ℤ) := dpos.map d4Root with hLdef
  have hroots : ∀ γ ∈ L, IsRoot d4 γ ∧ 0 < htD4 γ := by
    intro γ hγ
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hγ
    exact ⟨isRoot_d4Root (by rw [d4_roots_length]; exact dpos_lt hp), dpos_pos_height p hp⟩
  have hnd : L.Nodup := by decide +kernel
  have hsort : L.Pairwise fun γ δ => htD4 γ ≤ htD4 δ := by decide +kernel
  have hinj := prodInjective (F := rootOperatorFamily d4) (K := K) htD4 L hnd hroots hsort
  set pos : (Fin d4.rank → ℤ) → ℕ := fun v =>
    if v = d4Root 2 then 2 else if v = d4Root 0 then 0 else if v = d4Root 1 then 1 else
    if v = d4Root 3 then 3 else if v = d4Root 5 then 5 else if v = d4Root 7 then 7 else
    if v = d4Root 9 then 9 else if v = d4Root 12 then 12 else if v = d4Root 13 then 13 else
    if v = d4Root 15 then 15 else if v = d4Root 19 then 19 else 22 with hpos
  have hpos_root : ∀ p ∈ dpos, pos (d4Root p) = p := by decide +kernel
  have hprod : ∀ e : ℕ → K,
      (L.map fun v => xPar (rootOperatorFamily d4) v (e (pos v))).prod = ordD e := by
    intro e
    simp only [hLdef, List.map_map]
    rw [List.map_congr_left (g := fun p => xd p (e p)) (fun p hp => by
      simp only [Function.comp_apply, hpos_root p hp])]
    simp [dpos, ordD, mul_assoc]
  have key := hinj (fun v => xPar (rootOperatorFamily d4) v (e (pos v)))
    (fun v => xPar (rootOperatorFamily d4) v (e' (pos v)))
    (fun γ hγ => xPar_mem (hroots _ hγ).1 _) (fun γ hγ => xPar_mem (hroots _ hγ).1 _)
    (by rw [hprod e, hprod e']; exact h)
  intro p hp
  have hmem : d4Root p ∈ L := List.mem_map.2 ⟨p, hp, rfl⟩
  have := key (d4Root p) hmem
  simp only [hpos_root p hp] at this
  exact xPar_injective (F := rootOperatorFamily d4) (K := K) (hroots _ hmem).1 this

@[expose] def crd (c : ℕ → K) : ℕ → K := fun p =>
  if p = 0 then c 1 else if p = 1 then σ (c 1) else if p = 3 then σ (σ (c 1)) else
  if p = 2 then c 0 else if p = 5 then c 4 else if p = 7 then σ (c 4) else
  if p = 9 then σ (σ (c 4)) else if p = 12 then c 8 else if p = 15 then σ (c 8) else
  if p = 13 then σ (σ (c 8)) else if p = 19 then c 3 else if p = 22 then c 7 else 0

theorem ordT_eq_ordD [CharP K 2] (c : ℕ → K) : ordT σ c = ordD (crd σ c) := by
  unfold ordT xA xAB xAAB xB xN xH ordD
  simp only [crd]
  d4coll
  simp

theorem ordT_inj [CharP K 2] {c c' : ℕ → K} (h : ordT σ c = ordT σ c') :
    c 0 = c' 0 ∧ c 1 = c' 1 ∧ c 4 = c' 4 ∧ c 8 = c' 8 ∧ c 3 = c' 3 ∧ c 7 = c' 7 := by
  rw [ordT_eq_ordD, ordT_eq_ordD] at h
  have h' := ordD_injective h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [crd] using h' 2 (by simp [dpos])
  · simpa [crd] using h' 0 (by simp [dpos])
  · simpa [crd] using h' 5 (by simp [dpos])
  · simpa [crd] using h' 12 (by simp [dpos])
  · simpa [crd] using h' 19 (by simp [dpos])
  · simpa [crd] using h' 22 (by simp [dpos])

end CFSG.RankThree.PartOne.SEITZ7
