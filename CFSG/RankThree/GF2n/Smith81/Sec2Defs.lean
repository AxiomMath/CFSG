module

public import CFSG.RankThree.GF2n.Smith81.Sec1Fusion
public import CFSG.RankThree.GF2n.Stroth80.Sec34Symm

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def conjClassSet (z : G) : Set G := {g | IsConj z g}

@[expose] def CommOn (D : Set G) (a b : G) : Prop := a ∈ D ∧ b ∈ D ∧ Commute a b

@[expose] def IsZConjugate (Z X : Subgroup G) : Prop := ∃ g : G, X = conjSubgroup g Z

theorem conjClassSet_conj {z a : G} (ha : a ∈ conjClassSet z) (g : G) :
    g * a * g⁻¹ ∈ conjClassSet z :=
  IsConj.trans ha (isConj_iff.mpr ⟨g, rfl⟩)

theorem commOn_symm {D : Set G} {a b : G} (h : CommOn D a b) : CommOn D b a :=
  ⟨h.2.1, h.1, h.2.2.symm⟩

theorem IsZConjugate.self (Z : Subgroup G) : IsZConjugate Z Z := ⟨1, (conjSubgroup_one Z).symm⟩

theorem IsZConjugate.conj {Z X : Subgroup G} (h : IsZConjugate Z X) (g : G) :
    IsZConjugate Z (conjSubgroup g X) := by
  obtain ⟨h, rfl⟩ := h
  exact ⟨g * h, (conjSubgroup_mul g h Z).symm⟩

theorem exists_isZConjugate_mem {Z : Subgroup G} {z a : G} (hz : z ∈ Z) (ha : IsConj z a) :
    ∃ X, IsZConjugate Z X ∧ a ∈ X := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp ha
  refine ⟨conjSubgroup g Z, ⟨g, rfl⟩, ?_⟩
  rw [mem_conjSubgroup]
  simpa [mul_assoc] using hz

section Conjugates

variable [Finite G] {M Q Z : Subgroup G}

theorem IsZConjugate.eq_of_mem (H : StrothHyp M Q Z) {X Y : Subgroup G} (hX : IsZConjugate Z X)
    (hY : IsZConjugate Z Y) {a : G} (ha : a ≠ 1) (haX : a ∈ X) (haY : a ∈ Y) : X = Y := by
  obtain ⟨g, rfl⟩ := hX
  obtain ⟨g', rfl⟩ := hY
  exact conjSubgroup_eq_of_mem_ne_one H ha haX haY

theorem isPGroup_Q' (H : StrothHyp M Q Z) : IsPGroup 2 Q := by
  rw [H.hQ]
  exact (inSubgroup_pCore_two M).1

theorem IsZConjugate.QB_eq (H : StrothHyp M Q Z) {X : Subgroup G} (hX : IsZConjugate Z X) :
    ∃ g : G, X = conjSubgroup g Z ∧ QB X = conjSubgroup g Q ∧
      Subgroup.normalizer (X : Set G) = conjSubgroup g M := by
  obtain ⟨g, rfl⟩ := hX
  exact ⟨g, rfl, QB_conj_eq H g, normalizer_conj_eq H g⟩

theorem IsZConjugate.le_QB_self (H : StrothHyp M Q Z) {X : Subgroup G} (hX : IsZConjugate Z X) :
    X ≤ QB X := by
  obtain ⟨g, rfl, hQ, -⟩ := hX.QB_eq H
  rw [hQ]
  exact Subgroup.map_mono H.Z_normal.1

theorem IsZConjugate.le_QB_iff (H : StrothHyp M Q Z) {A X : Subgroup G} (hA : IsZConjugate Z A)
    (hX : IsZConjugate Z X) : X ≤ QB A ↔ A ≤ QB X := by
  by_cases h : X = A
  · subst h
    exact ⟨fun _ => hX.le_QB_self H, fun _ => hX.le_QB_self H⟩
  · exact H.le_QB_iff_le_QB hX hA h

theorem IsZConjugate.mem_normalizer_of_commute (H : StrothHyp M Q Z) {A : Subgroup G}
    (hA : IsZConjugate Z A) {a c : G} (ha1 : a ≠ 1) (haA : a ∈ A) (hc : Commute c a) :
    c ∈ Subgroup.normalizer (A : Set G) := by
  obtain ⟨g, rfl⟩ := hA
  exact Tim77.mem_normalizer_of_commute_of_isTI (isTI_conjSubgroup H.ti g) haA ha1 hc.eq

theorem IsZConjugate.conj_mem_QB (H : StrothHyp M Q Z) {X : Subgroup G} (hX : IsZConjugate Z X)
    {c q : G} (hc : c ∈ Subgroup.normalizer (X : Set G)) (hq : q ∈ QB X) :
    c * q * c⁻¹ ∈ QB X := by
  obtain ⟨g, -, hQ, hN⟩ := hX.QB_eq H
  rw [hN, mem_conjSubgroup] at hc
  rw [hQ, mem_conjSubgroup] at hq ⊢
  have h1 := conj_mem_Q H hc hq
  have e : g⁻¹ * (c * q * c⁻¹) * g = (g⁻¹ * c * g) * (g⁻¹ * q * g) * (g⁻¹ * c * g)⁻¹ := by group
  rw [e]
  exact h1

theorem IsZConjugate.isPGroup_QB (H : StrothHyp M Q Z) {X : Subgroup G} (hX : IsZConjugate Z X) :
    IsPGroup 2 (QB X) := by
  obtain ⟨g, -, hQ, -⟩ := hX.QB_eq H
  rw [hQ]
  have h := (isPGroup_Q' H).map (MulAut.conj g).toMonoidHom
  exact h

theorem IsZConjugate.comm_mem_QB (H : StrothHyp M Q Z) {X : Subgroup G} (hX : IsZConjugate Z X)
    {a b : G} (ha : a ∈ QB X) (hb : b ∈ QB X) : ⁅a, b⁆ ∈ X := by
  obtain ⟨g, hg, hQ, -⟩ := hX.QB_eq H
  rw [hQ] at ha hb
  rw [hg]
  exact H.toHyp79.comm_mem_conj g ha hb

theorem IsZConjugate.central_QB (H : StrothHyp M Q Z) {X : Subgroup G} (hX : IsZConjugate Z X)
    {u y : G} (hu : u ∈ X) (hy : y ∈ QB X) : u * y = y * u := by
  obtain ⟨g, hg, hQ, -⟩ := hX.QB_eq H
  rw [hQ] at hy
  rw [hg] at hu
  exact H.toHyp79.conj_central g hu hy

theorem IsZConjugate.le_QB_of_mem (H : StrothHyp M Q Z) {A X : Subgroup G}
    (hA : IsZConjugate Z A) (hX : IsZConjugate Z X) {x : G} (hx1 : x ≠ 1) (hxX : x ∈ X)
    (hxA : x ∈ QB A) : X ≤ QB A := by
  obtain ⟨g, -, hQ, -⟩ := hA.QB_eq H
  rw [hQ] at hxA ⊢
  set X' := conjSubgroup g⁻¹ X with hX'
  have hX'c : IsZConjugate Z X' := hX.conj g⁻¹
  have hx' : g⁻¹ * x * g ∈ X' := by
    rw [hX', mem_conjSubgroup]
    simpa [mul_assoc] using hxX
  have hx'Q : g⁻¹ * x * g ∈ Q := mem_conjSubgroup.mp hxA
  have hx'1 : g⁻¹ * x * g ≠ 1 := by
    intro h
    apply hx1
    have : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    rw [this, h]; group
  have hX'Q : X' ≤ Q := by
    by_cases hxZ : g⁻¹ * x * g ∈ Z
    · have := hX'c.eq_of_mem H (IsZConjugate.self Z) hx'1 hx' hxZ
      rw [this]
      exact H.Z_normal.1
    · obtain ⟨h, hh⟩ := hX'c
      have hmem : g⁻¹ * x * g ∈ conjSubgroup h Z := hh ▸ hx'
      rw [mem_conjSubgroup] at hmem
      obtain ⟨k, hkQ, hxk⟩ := stroth_2_6 H hx'Q hxZ
        ⟨h, h⁻¹ * (g⁻¹ * x * g) * h, hmem, by group⟩
      have := (IsZConjugate.eq_of_mem H ⟨h, hh⟩ ⟨k, rfl⟩ hx'1 hx' hxk)
      rw [this]
      exact hkQ
  have : X = conjSubgroup g X' := by
    rw [hX', ← conjSubgroup_mul]
    simp [conjSubgroup_one]
  rw [this]
  exact Subgroup.map_mono hX'Q

theorem mul_self_eq_one_of_isConj_Z (H : StrothHyp M Q Z) {z : G} (hz : z ∈ Z) {d : G}
    (hd : IsConj z d) : d * d = 1 := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp hd
  have hzz : z * z = 1 := by rw [← pow_two]; exact Z_sq H hz
  calc c * z * c⁻¹ * (c * z * c⁻¹) = c * (z * z) * c⁻¹ := by group
    _ = 1 := by rw [hzz]; group

theorem ne_one_of_isConj_Z {z : G} (hz1 : z ≠ 1) {d : G} (hd : IsConj z d) : d ≠ 1 := by
  intro h
  rw [h] at hd
  exact hz1 (isConj_one_left.mp hd)

theorem IsZConjugate.card_eq {X : Subgroup G} (hX : IsZConjugate Z X) :
    Nat.card X = Nat.card Z := by
  obtain ⟨g, rfl⟩ := hX
  exact card_conjSubgroup g Z

end Conjugates

end CFSG.RankThree.GF2n.Smith81
