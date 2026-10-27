module

public import CFSG.RankThree.Native.PermEnumeration

public section

namespace CFSG.RankThree.PartOne

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native

variable {n : ℕ}

theorem card_closure_eq_card_mul_card_centralizer {gs : Array (Array ℕ)} {ps : List ℕ}
    (hps : ∀ p ∈ ps, p < n) (hgs : ∀ k < gs.size, validA n gs[k]! = true) {x : Array ℕ}
    {c : ArrCert}
    (hc : arrCertOK (fun k a => conjA n gs[k]! a) gs.size (validA n) (keyA n ps) x c = true) :
    {y : Equiv.Perm (Fin n) | ∃ g ∈ Subgroup.closure (permsA n gs),
        y = g * permOfArr n x * g⁻¹}.ncard = c.pts.size ∧
      Nat.card (Subgroup.closure (permsA n gs)) =
        c.pts.size * Nat.card ↥(Subgroup.closure (permsA n gs) ⊓
          Subgroup.centralizer ({permOfArr n x} : Set (Equiv.Perm (Fin n)))) := by
  classical
  set R := Subgroup.closure (permsA n gs) with hR
  set X := permOfArr n x with hX
  let gens' : ℕ → ConjAct (Equiv.Perm (Fin n)) := fun k =>
    ConjAct.toConjAct (permOfArr n gs[k]!)
  have hact : ∀ k < gs.size, ∀ a, validA n a = true →
      permOfArr n (conjA n gs[k]! a) = gens' k • permOfArr n a := by
    intro k hk a ha
    rw [ConjAct.smul_def]
    exact permOfArr_eq_of_rep (rep_conjA (hgs k hk) (rep_of_validA ha))
  have hkey : ∀ a b, validA n a = true → validA n b = true → permOfArr n a = permOfArr n b →
      keyA n ps a = keyA n ps b := fun a b ha hb h => keyA_eq hps ha hb h
  have horb := ncard_orbit_of_arrCertOK (G := ConjAct (Equiv.Perm (Fin n)))
    (X := Equiv.Perm (Fin n)) (dec := permOfArr n) (gens := gens') hc hact hkey
  set H : Subgroup (ConjAct (Equiv.Perm (Fin n))) :=
    Subgroup.closure (gens' '' {k | k < gs.size}) with hH
  have hHR : H = R.map (ConjAct.toConjAct : Equiv.Perm (Fin n) ≃* _).toMonoidHom := by
    rw [hH, hR, MonoidHom.map_closure]
    congr 1
    ext g
    simp only [Set.mem_image, permsA, Set.mem_ofPred_eq, gens']
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨permOfArr n gs[k]!, ⟨k, hk, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      exact ⟨k, hk, rfl⟩
  have hHmem : ∀ g : ConjAct (Equiv.Perm (Fin n)), g ∈ H ↔ ConjAct.ofConjAct g ∈ R := by
    intro g
    rw [hHR, Subgroup.mem_map_equiv]
    rfl
  have hcardH : Nat.card H = Nat.card R := by
    rw [hHR]
    exact (Nat.card_congr (R.equivMapOfInjective
      (ConjAct.toConjAct : Equiv.Perm (Fin n) ≃* _).toMonoidHom
      (ConjAct.toConjAct : Equiv.Perm (Fin n) ≃* _).injective).toEquiv).symm
  have hos : Nat.card (MulAction.orbit H X) * Nat.card (MulAction.stabilizer H X) =
      Nat.card H := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup H X)
  have hstab : ∀ g : ConjAct (Equiv.Perm (Fin n)), g • X = X ↔
      ConjAct.ofConjAct g ∈ Subgroup.centralizer ({X} : Set (Equiv.Perm (Fin n))) := by
    intro g
    rw [ConjAct.smul_def, Subgroup.mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]
  have hstabcard : Nat.card (MulAction.stabilizer H X) =
      Nat.card ↥(R ⊓ Subgroup.centralizer ({X} : Set (Equiv.Perm (Fin n)))) := by
    refine Nat.card_congr
      { toFun := fun s => ⟨ConjAct.ofConjAct (s.1 : ConjAct (Equiv.Perm (Fin n))),
          Subgroup.mem_inf.2 ⟨(hHmem _).1 s.1.2,
            (hstab _).1 (MulAction.mem_stabilizer_iff.1 s.2)⟩⟩
        invFun := fun r => ⟨⟨ConjAct.toConjAct (r : Equiv.Perm (Fin n)),
          (hHmem _).2 (Subgroup.mem_inf.1 r.2).1⟩, MulAction.mem_stabilizer_iff.2
            ((hstab _).2 (Subgroup.mem_inf.1 r.2).2)⟩
        left_inv := fun s => rfl
        right_inv := fun r => rfl }
  have hclass : {y : Equiv.Perm (Fin n) | ∃ g ∈ R, y = g * X * g⁻¹} =
      (MulAction.orbit H X : Set (Equiv.Perm (Fin n))) := by
    ext y
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨ConjAct.toConjAct g, (hHmem _).2 hg⟩, by simp [ConjAct.smul_def]⟩
    · rintro ⟨⟨h, hh⟩, rfl⟩
      exact ⟨ConjAct.ofConjAct h, (hHmem h).1 hh, by simp [ConjAct.smul_def]⟩
  refine ⟨by rw [hclass]; exact horb, ?_⟩
  rw [← hcardH, ← hos, hstabcard]
  congr 1

theorem ncard_class_mul_card_centralizer (R : Subgroup (Equiv.Perm (Fin n)))
    (X : Equiv.Perm (Fin n)) :
    {y : Equiv.Perm (Fin n) | ∃ g ∈ R, y = g * X * g⁻¹}.ncard *
      Nat.card ↥(R ⊓ Subgroup.centralizer ({X} : Set (Equiv.Perm (Fin n)))) = Nat.card R := by
  classical
  set H : Subgroup (ConjAct (Equiv.Perm (Fin n))) :=
    R.map (ConjAct.toConjAct : Equiv.Perm (Fin n) ≃* _).toMonoidHom with hH
  have hHmem : ∀ g : ConjAct (Equiv.Perm (Fin n)), g ∈ H ↔ ConjAct.ofConjAct g ∈ R := by
    intro g
    rw [hH, Subgroup.mem_map_equiv]
    rfl
  have hcardH : Nat.card H = Nat.card R :=
    (Nat.card_congr (R.equivMapOfInjective
      (ConjAct.toConjAct : Equiv.Perm (Fin n) ≃* _).toMonoidHom
      (ConjAct.toConjAct : Equiv.Perm (Fin n) ≃* _).injective).toEquiv).symm
  have hos : Nat.card (MulAction.orbit H X) * Nat.card (MulAction.stabilizer H X) =
      Nat.card H := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup H X)
  have hstab : ∀ g : ConjAct (Equiv.Perm (Fin n)), g • X = X ↔
      ConjAct.ofConjAct g ∈ Subgroup.centralizer ({X} : Set (Equiv.Perm (Fin n))) := by
    intro g
    rw [ConjAct.smul_def, Subgroup.mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]
  have hstabcard : Nat.card (MulAction.stabilizer H X) =
      Nat.card ↥(R ⊓ Subgroup.centralizer ({X} : Set (Equiv.Perm (Fin n)))) := by
    refine Nat.card_congr
      { toFun := fun s => ⟨ConjAct.ofConjAct (s.1 : ConjAct (Equiv.Perm (Fin n))),
          Subgroup.mem_inf.2 ⟨(hHmem _).1 s.1.2,
            (hstab _).1 (MulAction.mem_stabilizer_iff.1 s.2)⟩⟩
        invFun := fun r => ⟨⟨ConjAct.toConjAct (r : Equiv.Perm (Fin n)),
          (hHmem _).2 (Subgroup.mem_inf.1 r.2).1⟩, MulAction.mem_stabilizer_iff.2
            ((hstab _).2 (Subgroup.mem_inf.1 r.2).2)⟩
        left_inv := fun s => rfl
        right_inv := fun r => rfl }
  have hclass : {y : Equiv.Perm (Fin n) | ∃ g ∈ R, y = g * X * g⁻¹} =
      (MulAction.orbit H X : Set (Equiv.Perm (Fin n))) := by
    ext y
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨ConjAct.toConjAct g, (hHmem _).2 hg⟩, by simp [ConjAct.smul_def]⟩
    · rintro ⟨⟨h, hh⟩, rfl⟩
      exact ⟨ConjAct.ofConjAct h, (hHmem h).1 hh, by simp [ConjAct.smul_def]⟩
  rw [hclass, ← Nat.card_coe_set_eq, ← hstabcard, hos, hcardH]

end CFSG.RankThree.PartOne
