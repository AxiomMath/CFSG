module

public import CFSG.Quasithin.Recognition.St84.Gen.NatSecDefs
import CFSG.RankThree.GF2n.Tim79Hom

public section

namespace CFSG.Quasithin.St84

open Matrix
open Multiplicative
open scoped commutatorElement MatrixGroups

private theorem toAdd_eq_zero_iff_ker {G : Type} [Group G] {E N : Subgroup G}
    {F : Type} [Field F] {β : ↥E →* Multiplicative (Fin 2 → F)}
    (hker : β.ker = N.subgroupOf E) (e : ↥E) :
    toAdd (β e) = 0 ↔ (e : G) ∈ N := by
  rw [toAdd_eq_zero, ← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]

private theorem toAdd_comm_eq_zero {G : Type} [Group G] {V Z : Subgroup G}
    {F : Type} [Field F] {β₂ : ↥V →* Multiplicative (Fin 2 → F)}
    (hβ₂ker : β₂.ker = Z.subgroupOf V) {a b : G}
    (hV : ⁅a, b⁆ ∈ V) (hZ : ⁅a, b⁆ ∈ Z) :
    toAdd (β₂ ⟨⁅a, b⁆, hV⟩) = 0 :=
  (toAdd_eq_zero_iff_ker hβ₂ker _).mpr hZ

private theorem toAdd_conj_eq {G : Type} [Group G] {E V Z : Subgroup G}
    {F : Type} [Field F] (hZV : Z ≤ V) (hcent : ⁅E, V⁆ ≤ Z)
    {β₂ : ↥V →* Multiplicative (Fin 2 → F)} (hβ₂ker : β₂.ker = Z.subgroupOf V)
    (a : ↥E) (z : ↥V) (hmem : (a : G) * (z : G) * (a : G)⁻¹ ∈ V) :
    toAdd (β₂ ⟨(a : G) * (z : G) * (a : G)⁻¹, hmem⟩) = toAdd (β₂ z) := by
  have hZ : ⁅(a : G), (z : G)⁆ ∈ Z :=
    hcent (Subgroup.commutator_mem_commutator a.2 z.2)
  have hker : (⟨⁅(a : G), (z : G)⁆, hZV hZ⟩ : ↥V) ∈ β₂.ker := by
    rw [hβ₂ker, Subgroup.mem_subgroupOf]
    exact hZ
  have heq : (⟨(a : G) * (z : G) * (a : G)⁻¹, hmem⟩ : ↥V) =
      (⟨⁅(a : G), (z : G)⁆, hZV hZ⟩ : ↥V) * z := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, commutatorElement_def]
    group
  rw [heq, map_mul, toAdd_mul, MonoidHom.mem_ker.mp hker, toAdd_one, zero_add]

private theorem toAdd_comm_mul_left {G : Type} [Group G] {E V Z : Subgroup G}
    {F : Type} [Field F] (hZV : Z ≤ V) (hcent : ⁅E, V⁆ ≤ Z)
    {β₂ : ↥V →* Multiplicative (Fin 2 → F)} (hβ₂ker : β₂.ker = Z.subgroupOf V)
    (a b c : ↥E) (h1 : ⁅((a * b : ↥E) : G), (c : G)⁆ ∈ V)
    (h2 : ⁅(b : G), (c : G)⁆ ∈ V) (h3 : ⁅(a : G), (c : G)⁆ ∈ V) :
    toAdd (β₂ ⟨⁅((a * b : ↥E) : G), (c : G)⁆, h1⟩) =
      toAdd (β₂ ⟨⁅(b : G), (c : G)⁆, h2⟩) +
        toAdd (β₂ ⟨⁅(a : G), (c : G)⁆, h3⟩) := by
  let y : ↥V := ⟨⁅(b : G), (c : G)⁆, h2⟩
  have hyZ : ⁅(a : G), (y : G)⁆ ∈ Z :=
    hcent (Subgroup.commutator_mem_commutator a.2 y.2)
  have hmem : (a : G) * (y : G) * (a : G)⁻¹ ∈ V := by
    rw [show (a : G) * (y : G) * (a : G)⁻¹ = ⁅(a : G), (y : G)⁆ * (y : G) by
      rw [commutatorElement_def]
      group]
    exact V.mul_mem (hZV hyZ) y.2
  have heq : (⟨⁅((a * b : ↥E) : G), (c : G)⁆, h1⟩ : ↥V) =
      (⟨(a : G) * (y : G) * (a : G)⁻¹, hmem⟩ : ↥V) *
        (⟨⁅(a : G), (c : G)⁆, h3⟩ : ↥V) := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, commutatorElement_def, y]
    group
  rw [heq, map_mul, toAdd_mul, toAdd_conj_eq hZV hcent hβ₂ker a y hmem]

private theorem toAdd_comm_mul_right {G : Type} [Group G] {E V Z : Subgroup G}
    {F : Type} [Field F] (hZV : Z ≤ V) (hcent : ⁅E, V⁆ ≤ Z)
    {β₂ : ↥V →* Multiplicative (Fin 2 → F)} (hβ₂ker : β₂.ker = Z.subgroupOf V)
    (a b c : ↥E) (h1 : ⁅(a : G), ((b * c : ↥E) : G)⁆ ∈ V)
    (h2 : ⁅(a : G), (b : G)⁆ ∈ V) (h3 : ⁅(a : G), (c : G)⁆ ∈ V) :
    toAdd (β₂ ⟨⁅(a : G), ((b * c : ↥E) : G)⁆, h1⟩) =
      toAdd (β₂ ⟨⁅(a : G), (b : G)⁆, h2⟩) +
        toAdd (β₂ ⟨⁅(a : G), (c : G)⁆, h3⟩) := by
  let y : ↥V := ⟨⁅(a : G), (c : G)⁆, h3⟩
  have hyZ : ⁅(b : G), (y : G)⁆ ∈ Z :=
    hcent (Subgroup.commutator_mem_commutator b.2 y.2)
  have hmem : (b : G) * (y : G) * (b : G)⁻¹ ∈ V := by
    rw [show (b : G) * (y : G) * (b : G)⁻¹ = ⁅(b : G), (y : G)⁆ * (y : G) by
      rw [commutatorElement_def]
      group]
    exact V.mul_mem (hZV hyZ) y.2
  have heq : (⟨⁅(a : G), ((b * c : ↥E) : G)⁆, h1⟩ : ↥V) =
      (⟨⁅(a : G), (b : G)⁆, h2⟩ : ↥V) *
        (⟨(b : G) * (y : G) * (b : G)⁻¹, hmem⟩ : ↥V) := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, commutatorElement_def, y]
    group
  rw [heq, map_mul, toAdd_mul, toAdd_conj_eq hZV hcent hβ₂ker b y hmem]

private noncomputable def commPair {G : Type} [Group G] {E V : Subgroup G}
    {F : Type} [Field F] (hcomm : ⁅E, E⁆ ≤ V)
    (β₁ : ↥E →* Multiplicative (Fin 2 → F)) (hβ₁ : Function.Surjective β₁)
    (β₂ : ↥V →* Multiplicative (Fin 2 → F)) (v w : Fin 2 → F) : Fin 2 → F :=
  let r₁ : ↥E := Function.surjInv hβ₁ (ofAdd v)
  let r₂ : ↥E := Function.surjInv hβ₁ (ofAdd w)
  toAdd (β₂ ⟨⁅(r₁ : G), (r₂ : G)⁆,
    hcomm (Subgroup.commutator_mem_commutator r₁.2 r₂.2)⟩)

private theorem toAdd_comm_conj_eq {G : Type} [Group G] {E V Z : Subgroup G}
    {F : Type} [Field F] (hcomm : ⁅E, E⁆ ≤ V) (hZV : Z ≤ V) (hcent : ⁅E, V⁆ ≤ Z)
    {β₂ : ↥V →* Multiplicative (Fin 2 → F)} (hβ₂ker : β₂.ker = Z.subgroupOf V)
    (x y cx cy : ↥E) (hcx : (cx : G) ∈ V) (hcy : (cy : G) ∈ V) :
    toAdd (β₂ ⟨⁅((cx * x : ↥E) : G), ((cy * y : ↥E) : G)⁆,
        hcomm (Subgroup.commutator_mem_commutator (E.mul_mem cx.2 x.2)
          (E.mul_mem cy.2 y.2))⟩) =
      toAdd (β₂ ⟨⁅(x : G), (y : G)⁆,
        hcomm (Subgroup.commutator_mem_commutator x.2 y.2)⟩) := by
  have hstep1 := toAdd_comm_mul_left hZV hcent hβ₂ker cx x (cy * y)
    (hcomm (Subgroup.commutator_mem_commutator (E.mul_mem cx.2 x.2)
      (E.mul_mem cy.2 y.2)))
    (hcomm (Subgroup.commutator_mem_commutator x.2 (E.mul_mem cy.2 y.2)))
    (hcomm (Subgroup.commutator_mem_commutator cx.2 (E.mul_mem cy.2 y.2)))
  have hstep2 := toAdd_comm_mul_right hZV hcent hβ₂ker x cy y
    (hcomm (Subgroup.commutator_mem_commutator x.2 (E.mul_mem cy.2 y.2)))
    (hcomm (Subgroup.commutator_mem_commutator x.2 cy.2))
    (hcomm (Subgroup.commutator_mem_commutator x.2 y.2))
  have hstep3 := toAdd_comm_mul_right hZV hcent hβ₂ker cx cy y
    (hcomm (Subgroup.commutator_mem_commutator cx.2 (E.mul_mem cy.2 y.2)))
    (hcomm (Subgroup.commutator_mem_commutator cx.2 cy.2))
    (hcomm (Subgroup.commutator_mem_commutator cx.2 y.2))
  have hZxy : ⁅(x : G), (cy : G)⁆ ∈ Z :=
    hcent (Subgroup.commutator_mem_commutator x.2 hcy)
  have hZcxcy : ⁅(cx : G), (cy : G)⁆ ∈ Z :=
    hcent (Subgroup.commutator_mem_commutator cx.2 hcy)
  have hZcxy : ⁅(cx : G), (y : G)⁆ ∈ Z := by
    have h := hcent (Subgroup.commutator_mem_commutator y.2 hcx)
    rw [← commutatorElement_inv]
    exact Z.inv_mem h
  calc
    toAdd (β₂ ⟨⁅((cx * x : ↥E) : G), ((cy * y : ↥E) : G)⁆,
          hcomm (Subgroup.commutator_mem_commutator (E.mul_mem cx.2 x.2)
            (E.mul_mem cy.2 y.2))⟩) =
        toAdd (β₂ ⟨⁅(x : G), ((cy * y : ↥E) : G)⁆,
          hcomm (Subgroup.commutator_mem_commutator x.2 (E.mul_mem cy.2 y.2))⟩) +
          toAdd (β₂ ⟨⁅(cx : G), ((cy * y : ↥E) : G)⁆,
            hcomm (Subgroup.commutator_mem_commutator cx.2 (E.mul_mem cy.2 y.2))⟩) :=
      hstep1
    _ = (toAdd (β₂ ⟨⁅(x : G), (cy : G)⁆,
            hcomm (Subgroup.commutator_mem_commutator x.2 cy.2)⟩) +
          toAdd (β₂ ⟨⁅(x : G), (y : G)⁆,
            hcomm (Subgroup.commutator_mem_commutator x.2 y.2)⟩)) +
        (toAdd (β₂ ⟨⁅(cx : G), (cy : G)⁆,
            hcomm (Subgroup.commutator_mem_commutator cx.2 cy.2)⟩) +
          toAdd (β₂ ⟨⁅(cx : G), (y : G)⁆,
            hcomm (Subgroup.commutator_mem_commutator cx.2 y.2)⟩)) := by
      rw [hstep2, hstep3]
    _ = toAdd (β₂ ⟨⁅(x : G), (y : G)⁆,
          hcomm (Subgroup.commutator_mem_commutator x.2 y.2)⟩) := by
      rw [toAdd_comm_eq_zero hβ₂ker
            (hcomm (Subgroup.commutator_mem_commutator x.2 cy.2)) hZxy,
        toAdd_comm_eq_zero hβ₂ker
            (hcomm (Subgroup.commutator_mem_commutator cx.2 cy.2)) hZcxcy,
        toAdd_comm_eq_zero hβ₂ker
            (hcomm (Subgroup.commutator_mem_commutator cx.2 y.2)) hZcxy]
      abel

private theorem commPair_eq_comm {G : Type} [Group G] {E V Z : Subgroup G}
    {F : Type} [Field F] (hcomm : ⁅E, E⁆ ≤ V) (hZV : Z ≤ V) (hcent : ⁅E, V⁆ ≤ Z)
    {β₁ : ↥E →* Multiplicative (Fin 2 → F)} (hβ₁ : Function.Surjective β₁)
    (hβ₁ker : β₁.ker = V.subgroupOf E)
    {β₂ : ↥V →* Multiplicative (Fin 2 → F)} (hβ₂ker : β₂.ker = Z.subgroupOf V)
    {x y : ↥E} :
    commPair hcomm β₁ hβ₁ β₂ (toAdd (β₁ x)) (toAdd (β₁ y)) =
      toAdd (β₂ ⟨⁅(x : G), (y : G)⁆,
        hcomm (Subgroup.commutator_mem_commutator x.2 y.2)⟩) := by
  classical
  let rx : ↥E := Function.surjInv hβ₁ (ofAdd (toAdd (β₁ x)))
  let ry : ↥E := Function.surjInv hβ₁ (ofAdd (toAdd (β₁ y)))
  have hrx : toAdd (β₁ rx) = toAdd (β₁ x) := by
    rw [show β₁ rx = ofAdd (toAdd (β₁ x)) from Function.surjInv_eq hβ₁ _, toAdd_ofAdd]
  have hry : toAdd (β₁ ry) = toAdd (β₁ y) := by
    rw [show β₁ ry = ofAdd (toAdd (β₁ y)) from Function.surjInv_eq hβ₁ _, toAdd_ofAdd]
  let cx : ↥E := rx * x⁻¹
  let cy : ↥E := ry * y⁻¹
  have hcx : (cx : G) ∈ V := by
    apply (toAdd_eq_zero_iff_ker hβ₁ker cx).mp
    change toAdd (β₁ (rx * x⁻¹)) = 0
    rw [map_mul, map_inv, toAdd_mul, toAdd_inv, hrx, add_neg_cancel]
  have hcy : (cy : G) ∈ V := by
    apply (toAdd_eq_zero_iff_ker hβ₁ker cy).mp
    change toAdd (β₁ (ry * y⁻¹)) = 0
    rw [map_mul, map_inv, toAdd_mul, toAdd_inv, hry, add_neg_cancel]
  have hx_eq : rx = cx * x := by
    apply Subtype.ext
    show (rx : G) = ((rx * x⁻¹ : ↥E) : G) * (x : G)
    simp [mul_assoc]
  have hy_eq : ry = cy * y := by
    apply Subtype.ext
    show (ry : G) = ((ry * y⁻¹ : ↥E) : G) * (y : G)
    simp [mul_assoc]
  have hconv : (⟨⁅(rx : G), (ry : G)⁆,
        hcomm (Subgroup.commutator_mem_commutator rx.2 ry.2)⟩ : ↥V) =
      ⟨⁅((cx * x : ↥E) : G), ((cy * y : ↥E) : G)⁆,
        hcomm (Subgroup.commutator_mem_commutator (E.mul_mem cx.2 x.2)
          (E.mul_mem cy.2 y.2))⟩ := by
    apply Subtype.ext
    show ⁅(rx : G), (ry : G)⁆ = ⁅((cx * x : ↥E) : G), ((cy * y : ↥E) : G)⁆
    rw [← hx_eq, ← hy_eq]
  calc
    commPair hcomm β₁ hβ₁ β₂ (toAdd (β₁ x)) (toAdd (β₁ y)) =
        toAdd (β₂ ⟨⁅(rx : G), (ry : G)⁆,
          hcomm (Subgroup.commutator_mem_commutator rx.2 ry.2)⟩) := rfl
    _ = toAdd (β₂ ⟨⁅((cx * x : ↥E) : G), ((cy * y : ↥E) : G)⁆,
          hcomm (Subgroup.commutator_mem_commutator (E.mul_mem cx.2 x.2)
            (E.mul_mem cy.2 y.2))⟩) := by rw [hconv]
    _ = toAdd (β₂ ⟨⁅(x : G), (y : G)⁆,
          hcomm (Subgroup.commutator_mem_commutator x.2 y.2)⟩) :=
      toAdd_comm_conj_eq hcomm hZV hcent hβ₂ker x y cx cy hcx hcy

private theorem commPair_add_left {G : Type} [Group G] {E V Z : Subgroup G}
    {F : Type} [Field F] (hcomm : ⁅E, E⁆ ≤ V) (hZV : Z ≤ V) (hcent : ⁅E, V⁆ ≤ Z)
    {β₁ : ↥E →* Multiplicative (Fin 2 → F)} (hβ₁ : Function.Surjective β₁)
    (hβ₁ker : β₁.ker = V.subgroupOf E)
    {β₂ : ↥V →* Multiplicative (Fin 2 → F)} (hβ₂ker : β₂.ker = Z.subgroupOf V)
    (v v' w : Fin 2 → F) :
    commPair hcomm β₁ hβ₁ β₂ (v + v') w =
      commPair hcomm β₁ hβ₁ β₂ v w + commPair hcomm β₁ hβ₁ β₂ v' w := by
  classical
  let r : ↥E := Function.surjInv hβ₁ (ofAdd (v + v'))
  let r₁ : ↥E := Function.surjInv hβ₁ (ofAdd v)
  let r₂ : ↥E := Function.surjInv hβ₁ (ofAdd v')
  let s : ↥E := Function.surjInv hβ₁ (ofAdd w)
  have hr : toAdd (β₁ r) = v + v' := by
    rw [show β₁ r = ofAdd (v + v') from Function.surjInv_eq hβ₁ _, toAdd_ofAdd]
  have hr₁ : toAdd (β₁ r₁) = v := by
    rw [show β₁ r₁ = ofAdd v from Function.surjInv_eq hβ₁ _, toAdd_ofAdd]
  have hr₂ : toAdd (β₁ r₂) = v' := by
    rw [show β₁ r₂ = ofAdd v' from Function.surjInv_eq hβ₁ _, toAdd_ofAdd]
  have hs : toAdd (β₁ s) = w := by
    rw [show β₁ s = ofAdd w from Function.surjInv_eq hβ₁ _, toAdd_ofAdd]
  have hprod : toAdd (β₁ (r₁ * r₂)) = v + v' := by
    rw [map_mul, toAdd_mul, hr₁, hr₂]
  have h1 : commPair hcomm β₁ hβ₁ β₂ (v + v') w =
      toAdd (β₂ ⟨⁅(r : G), (s : G)⁆,
        hcomm (Subgroup.commutator_mem_commutator r.2 s.2)⟩) := rfl
  have h2 : commPair hcomm β₁ hβ₁ β₂ v w =
      toAdd (β₂ ⟨⁅(r₁ : G), (s : G)⁆,
        hcomm (Subgroup.commutator_mem_commutator r₁.2 s.2)⟩) := rfl
  have h3 : commPair hcomm β₁ hβ₁ β₂ v' w =
      toAdd (β₂ ⟨⁅(r₂ : G), (s : G)⁆,
        hcomm (Subgroup.commutator_mem_commutator r₂.2 s.2)⟩) := rfl
  have hrr : toAdd (β₂ ⟨⁅(r : G), (s : G)⁆,
        hcomm (Subgroup.commutator_mem_commutator r.2 s.2)⟩) =
      toAdd (β₂ ⟨⁅((r₁ * r₂ : ↥E) : G), (s : G)⁆,
        hcomm (Subgroup.commutator_mem_commutator (E.mul_mem r₁.2 r₂.2) s.2)⟩) := by
    rw [← commPair_eq_comm hcomm hZV hcent hβ₁ hβ₁ker hβ₂ker (x := r) (y := s),
      ← commPair_eq_comm hcomm hZV hcent hβ₁ hβ₁ker hβ₂ker (x := r₁ * r₂) (y := s),
      hr, hprod, hs]
  calc
    commPair hcomm β₁ hβ₁ β₂ (v + v') w =
        toAdd (β₂ ⟨⁅(r : G), (s : G)⁆,
          hcomm (Subgroup.commutator_mem_commutator r.2 s.2)⟩) := h1
    _ = toAdd (β₂ ⟨⁅((r₁ * r₂ : ↥E) : G), (s : G)⁆,
          hcomm (Subgroup.commutator_mem_commutator (E.mul_mem r₁.2 r₂.2) s.2)⟩) := hrr
    _ = toAdd (β₂ ⟨⁅(r₂ : G), (s : G)⁆,
          hcomm (Subgroup.commutator_mem_commutator r₂.2 s.2)⟩) +
        toAdd (β₂ ⟨⁅(r₁ : G), (s : G)⁆,
          hcomm (Subgroup.commutator_mem_commutator r₁.2 s.2)⟩) :=
      toAdd_comm_mul_left hZV hcent hβ₂ker r₁ r₂ s
        (hcomm (Subgroup.commutator_mem_commutator (E.mul_mem r₁.2 r₂.2) s.2))
        (hcomm (Subgroup.commutator_mem_commutator r₂.2 s.2))
        (hcomm (Subgroup.commutator_mem_commutator r₁.2 s.2))
    _ = commPair hcomm β₁ hβ₁ β₂ v w + commPair hcomm β₁ hβ₁ β₂ v' w := by
      rw [← h2, ← h3, add_comm]

private theorem commPair_add_right {G : Type} [Group G] {E V Z : Subgroup G}
    {F : Type} [Field F] (hcomm : ⁅E, E⁆ ≤ V) (hZV : Z ≤ V) (hcent : ⁅E, V⁆ ≤ Z)
    {β₁ : ↥E →* Multiplicative (Fin 2 → F)} (hβ₁ : Function.Surjective β₁)
    (hβ₁ker : β₁.ker = V.subgroupOf E)
    {β₂ : ↥V →* Multiplicative (Fin 2 → F)} (hβ₂ker : β₂.ker = Z.subgroupOf V)
    (v w w' : Fin 2 → F) :
    commPair hcomm β₁ hβ₁ β₂ v (w + w') =
      commPair hcomm β₁ hβ₁ β₂ v w + commPair hcomm β₁ hβ₁ β₂ v w' := by
  classical
  let r : ↥E := Function.surjInv hβ₁ (ofAdd v)
  let s : ↥E := Function.surjInv hβ₁ (ofAdd (w + w'))
  let s₁ : ↥E := Function.surjInv hβ₁ (ofAdd w)
  let s₂ : ↥E := Function.surjInv hβ₁ (ofAdd w')
  have hr : toAdd (β₁ r) = v := by
    rw [show β₁ r = ofAdd v from Function.surjInv_eq hβ₁ _, toAdd_ofAdd]
  have hs : toAdd (β₁ s) = w + w' := by
    rw [show β₁ s = ofAdd (w + w') from Function.surjInv_eq hβ₁ _, toAdd_ofAdd]
  have hs₁ : toAdd (β₁ s₁) = w := by
    rw [show β₁ s₁ = ofAdd w from Function.surjInv_eq hβ₁ _, toAdd_ofAdd]
  have hs₂ : toAdd (β₁ s₂) = w' := by
    rw [show β₁ s₂ = ofAdd w' from Function.surjInv_eq hβ₁ _, toAdd_ofAdd]
  have hprod : toAdd (β₁ (s₁ * s₂)) = w + w' := by
    rw [map_mul, toAdd_mul, hs₁, hs₂]
  have h1 : commPair hcomm β₁ hβ₁ β₂ v (w + w') =
      toAdd (β₂ ⟨⁅(r : G), (s : G)⁆,
        hcomm (Subgroup.commutator_mem_commutator r.2 s.2)⟩) := rfl
  have h2 : commPair hcomm β₁ hβ₁ β₂ v w =
      toAdd (β₂ ⟨⁅(r : G), (s₁ : G)⁆,
        hcomm (Subgroup.commutator_mem_commutator r.2 s₁.2)⟩) := rfl
  have h3 : commPair hcomm β₁ hβ₁ β₂ v w' =
      toAdd (β₂ ⟨⁅(r : G), (s₂ : G)⁆,
        hcomm (Subgroup.commutator_mem_commutator r.2 s₂.2)⟩) := rfl
  have hrr : toAdd (β₂ ⟨⁅(r : G), (s : G)⁆,
        hcomm (Subgroup.commutator_mem_commutator r.2 s.2)⟩) =
      toAdd (β₂ ⟨⁅(r : G), ((s₁ * s₂ : ↥E) : G)⁆,
        hcomm (Subgroup.commutator_mem_commutator r.2 (E.mul_mem s₁.2 s₂.2))⟩) := by
    rw [← commPair_eq_comm hcomm hZV hcent hβ₁ hβ₁ker hβ₂ker (x := r) (y := s),
      ← commPair_eq_comm hcomm hZV hcent hβ₁ hβ₁ker hβ₂ker (x := r) (y := s₁ * s₂),
      hr, hprod, hs]
  calc
    commPair hcomm β₁ hβ₁ β₂ v (w + w') =
        toAdd (β₂ ⟨⁅(r : G), (s : G)⁆,
          hcomm (Subgroup.commutator_mem_commutator r.2 s.2)⟩) := h1
    _ = toAdd (β₂ ⟨⁅(r : G), ((s₁ * s₂ : ↥E) : G)⁆,
          hcomm (Subgroup.commutator_mem_commutator r.2 (E.mul_mem s₁.2 s₂.2))⟩) := hrr
    _ = toAdd (β₂ ⟨⁅(r : G), (s₁ : G)⁆,
          hcomm (Subgroup.commutator_mem_commutator r.2 s₁.2)⟩) +
        toAdd (β₂ ⟨⁅(r : G), (s₂ : G)⁆,
          hcomm (Subgroup.commutator_mem_commutator r.2 s₂.2)⟩) :=
      toAdd_comm_mul_right hZV hcent hβ₂ker r s₁ s₂
        (hcomm (Subgroup.commutator_mem_commutator r.2 (E.mul_mem s₁.2 s₂.2)))
        (hcomm (Subgroup.commutator_mem_commutator r.2 s₁.2))
        (hcomm (Subgroup.commutator_mem_commutator r.2 s₂.2))
    _ = commPair hcomm β₁ hβ₁ β₂ v w + commPair hcomm β₁ hβ₁ β₂ v w' := by
      rw [← h2, ← h3, add_comm]

private noncomputable def commPairHom {G : Type} [Group G] {E V Z : Subgroup G}
    {F : Type} [Field F] (hcomm : ⁅E, E⁆ ≤ V) (hZV : Z ≤ V) (hcent : ⁅E, V⁆ ≤ Z)
    {β₁ : ↥E →* Multiplicative (Fin 2 → F)} (hβ₁ : Function.Surjective β₁)
    (hβ₁ker : β₁.ker = V.subgroupOf E)
    {β₂ : ↥V →* Multiplicative (Fin 2 → F)} (hβ₂ker : β₂.ker = Z.subgroupOf V) :
    (Fin 2 → F) →+ (Fin 2 → F) →+ (Fin 2 → F) :=
  AddMonoidHom.mk' (fun v =>
    AddMonoidHom.mk' (fun w => commPair hcomm β₁ hβ₁ β₂ v w)
      (fun w w' => commPair_add_right hcomm hZV hcent hβ₁ hβ₁ker hβ₂ker v w w'))
    (fun v v' => AddMonoidHom.ext fun w =>
      commPair_add_left hcomm hZV hcent hβ₁ hβ₁ker hβ₂ker v v' w)

private theorem commPairHom_equivariant {G : Type} [Group G] {L E V Z : Subgroup G}
    {F : Type} [Field F] {α : ↥L →* SL(2, F)} (hα : Function.Surjective α)
    (hLE : L ≤ Subgroup.normalizer (E : Set G))
    (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hcomm : ⁅E, E⁆ ≤ V) (hZV : Z ≤ V) (hcent : ⁅E, V⁆ ≤ Z)
    {β₁ : ↥E →* Multiplicative (Fin 2 → F)} (hβ₁ : Function.Surjective β₁)
    (hβ₁ker : β₁.ker = V.subgroupOf E)
    (hβ₁act : ∀ (ℓ : ↥L) (u v : ↥E), (v : G) = ℓ * u * ℓ⁻¹ →
      toAdd (β₁ v) = (α ℓ : Matrix (Fin 2) (Fin 2) F) *ᵥ toAdd (β₁ u))
    {β₂ : ↥V →* Multiplicative (Fin 2 → F)} (hβ₂ker : β₂.ker = Z.subgroupOf V)
    (hβ₂act : ∀ (ℓ : ↥L) (u v : ↥V), (v : G) = ℓ * u * ℓ⁻¹ →
      toAdd (β₂ v) = (α ℓ : Matrix (Fin 2) (Fin 2) F) *ᵥ toAdd (β₂ u))
    (g : SL(2, F)) (v w : Fin 2 → F) :
    commPairHom hcomm hZV hcent hβ₁ hβ₁ker hβ₂ker (g.1 *ᵥ v) (g.1 *ᵥ w) =
      g.1 *ᵥ commPairHom hcomm hZV hcent hβ₁ hβ₁ker hβ₂ker v w := by
  classical
  obtain ⟨ℓ, rfl⟩ := hα g
  change commPair hcomm β₁ hβ₁ β₂
      ((α ℓ : Matrix (Fin 2) (Fin 2) F) *ᵥ v)
      ((α ℓ : Matrix (Fin 2) (Fin 2) F) *ᵥ w) =
    (α ℓ : Matrix (Fin 2) (Fin 2) F) *ᵥ commPair hcomm β₁ hβ₁ β₂ v w
  let rv : ↥E := Function.surjInv hβ₁ (ofAdd v)
  let rw' : ↥E := Function.surjInv hβ₁ (ofAdd w)
  have hrv : toAdd (β₁ rv) = v := by
    rw [show β₁ rv = ofAdd v from Function.surjInv_eq hβ₁ _, toAdd_ofAdd]
  have hrw : toAdd (β₁ rw') = w := by
    rw [show β₁ rw' = ofAdd w from Function.surjInv_eq hβ₁ _, toAdd_ofAdd]
  let e : ↥E := ⟨(ℓ : G) * (rv : G) * (ℓ : G)⁻¹,
    (Subgroup.mem_normalizer_iff.mp (hLE ℓ.2) _).mp rv.2⟩
  let e' : ↥E := ⟨(ℓ : G) * (rw' : G) * (ℓ : G)⁻¹,
    (Subgroup.mem_normalizer_iff.mp (hLE ℓ.2) _).mp rw'.2⟩
  have he : toAdd (β₁ e) = (α ℓ : Matrix (Fin 2) (Fin 2) F) *ᵥ v := by
    have h := hβ₁act ℓ rv e rfl
    rwa [hrv] at h
  have he' : toAdd (β₁ e') = (α ℓ : Matrix (Fin 2) (Fin 2) F) *ᵥ w := by
    have h := hβ₁act ℓ rw' e' rfl
    rwa [hrw] at h
  have hbase : commPair hcomm β₁ hβ₁ β₂
        ((α ℓ : Matrix (Fin 2) (Fin 2) F) *ᵥ v)
        ((α ℓ : Matrix (Fin 2) (Fin 2) F) *ᵥ w) =
      toAdd (β₂ ⟨⁅(e : G), (e' : G)⁆,
        hcomm (Subgroup.commutator_mem_commutator e.2 e'.2)⟩) := by
    rw [← he, ← he']
    exact commPair_eq_comm hcomm hZV hcent hβ₁ hβ₁ker hβ₂ker
  have hmemV : (ℓ : G) * ⁅(rv : G), (rw' : G)⁆ * (ℓ : G)⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.mp (hLV ℓ.2) _).mp
      (hcomm (Subgroup.commutator_mem_commutator rv.2 rw'.2))
  have hee' : (⟨⁅(e : G), (e' : G)⁆,
        hcomm (Subgroup.commutator_mem_commutator e.2 e'.2)⟩ : ↥V) =
      ⟨(ℓ : G) * ⁅(rv : G), (rw' : G)⁆ * (ℓ : G)⁻¹, hmemV⟩ := by
    apply Subtype.ext
    show ⁅(e : G), (e' : G)⁆ = (ℓ : G) * ⁅(rv : G), (rw' : G)⁆ * (ℓ : G)⁻¹
    rw [show (e : G) = (ℓ : G) * (rv : G) * (ℓ : G)⁻¹ from rfl,
      show (e' : G) = (ℓ : G) * (rw' : G) * (ℓ : G)⁻¹ from rfl]
    exact (conjugate_commutatorElement (rv : G) (rw' : G) (ℓ : G)).symm
  have hact := hβ₂act ℓ ⟨⁅(rv : G), (rw' : G)⁆,
      hcomm (Subgroup.commutator_mem_commutator rv.2 rw'.2)⟩
    ⟨(ℓ : G) * ⁅(rv : G), (rw' : G)⁆ * (ℓ : G)⁻¹, hmemV⟩ rfl
  rw [hbase, hee', hact]
  have hpair : toAdd (β₂ ⟨⁅(rv : G), (rw' : G)⁆,
        hcomm (Subgroup.commutator_mem_commutator rv.2 rw'.2)⟩) =
      commPair hcomm β₁ hβ₁ β₂ v w := by
    rw [← commPair_eq_comm hcomm hZV hcent hβ₁ hβ₁ker hβ₂ker (x := rv) (y := rw')]
    rw [hrv, hrw]
  rw [hpair]

theorem comm_le_of_isNatSecOf {G : Type} [Group G] {L E V Z : Subgroup G}
    {F : Type} [Field F] [Fintype F] [CharP F 2] (hF : 4 ≤ Fintype.card F)
    {α : ↥L →* SL(2, F)} (hα : Function.Surjective α) (hZV : Z ≤ V)
    (hLE : L ≤ Subgroup.normalizer (E : Set G))
    (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hEV : CFSG.Quasithin.F112R.St84.IsNatSecOf L E V α)
    (hVZ : CFSG.Quasithin.F112R.St84.IsNatSecOf L V Z α)
    (hcomm : ⁅E, E⁆ ≤ V) (hcent : ⁅E, V⁆ ≤ Z) : ⁅E, E⁆ ≤ Z := by
  classical
  obtain ⟨β₁, hβ₁surj, hβ₁ker, hβ₁act⟩ := hEV
  obtain ⟨β₂, _, hβ₂ker, hβ₂act⟩ := hVZ
  let f : (Fin 2 → F) →+ (Fin 2 → F) →+ (Fin 2 → F) :=
    commPairHom hcomm hZV hcent hβ₁surj hβ₁ker hβ₂ker
  have hf : f = 0 :=
    CFSG.RankThree.GF2n.Tim79.equivariant_biadditive_eq_zero
      (K := F) (by rw [Nat.card_eq_fintype_card]; exact hF) f
      (fun g v w =>
        commPairHom_equivariant hα hLE hLV hcomm hZV hcent hβ₁surj hβ₁ker hβ₁act
          hβ₂ker hβ₂act g v w)
  rw [Subgroup.commutator_le]
  intro x hx y hy
  let x' : ↥E := ⟨x, hx⟩
  let y' : ↥E := ⟨y, hy⟩
  have hpair := commPair_eq_comm hcomm hZV hcent hβ₁surj hβ₁ker hβ₂ker
    (x := x') (y := y')
  have hzero : commPair hcomm β₁ hβ₁surj β₂
      (toAdd (β₁ x')) (toAdd (β₁ y')) = 0 := by
    change f (toAdd (β₁ x')) (toAdd (β₁ y')) = 0
    rw [hf]
    rfl
  have hZ : ⁅(x' : G), (y' : G)⁆ ∈ Z := by
    have h1 : toAdd (β₂ ⟨⁅(x' : G), (y' : G)⁆,
        hcomm (Subgroup.commutator_mem_commutator x'.2 y'.2)⟩) = 0 := by
      rw [← hpair]
      exact hzero
    exact (toAdd_eq_zero_iff_ker hβ₂ker _).mp h1
  simpa [x', y'] using hZ

end CFSG.Quasithin.St84

end
