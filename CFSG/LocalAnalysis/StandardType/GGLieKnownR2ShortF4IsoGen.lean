module

public import CFSG.LieType.Ree.ExceptionalAutomorphismData
public import CFSG.LieType.Steinberg.Adjoint.Presentation
public import CFSG.LieType.Chevalley.G2ThreeAutomorphismNormalForm
public import CFSG.Blueprint.ChevalleyWeyl

public section

namespace CFSG.StandardType.LieKnownR2.Short

open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.Ree
  CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.Blueprint.Chevalley
open scoped commutatorElement

theorem finiteExceptionalAut_F4_weylElement
    (K : Type) [Field K] [Finite K] [CharP K ReeTag.F4.prime]
    (i : Fin Tag.F4.rank) :
    ReeTag.F4.finiteExceptionalAut K (CFSG.LieType.Chevalley.weylElement .F4 K i) =
      CFSG.LieType.Chevalley.weylElement .F4 K (ReeTag.F4.perm i) := by
  haveI : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  let φ : MulAut (adjointGroup Tag.F4 K) := ReeTag.F4.finiteExceptionalAut K
  let ρ : Fin Tag.F4.rank → Fin Tag.F4.rank := fun j => ReeTag.F4.perm j
  change φ (CFSG.LieType.Chevalley.weylElement Tag.F4 K i) =
    CFSG.LieType.Chevalley.weylElement Tag.F4 K (ρ i)
  have hweyl : ∀ j : Fin Tag.F4.rank,
      CFSG.LieType.Chevalley.weylElement Tag.F4 K j =
        xElement (τ := Tag.F4) (K := K) j 1 * yElement (τ := Tag.F4) (K := K) j (-1) *
          xElement (τ := Tag.F4) (K := K) j 1 := by
    intro j
    refine Subtype.ext ?_
    change weylElt Tag.F4 K j 1 =
      xUnit Tag.F4 K j 1 * yUnit Tag.F4 K j (-1) * xUnit Tag.F4 K j 1
    simpa using weylElt_eq_xUnit_mul (τ := Tag.F4) (R := K) j 1
  have hmap : ∀ a b : adjointGroup Tag.F4 K, φ (a * b) = φ a * φ b :=
    fun a b => map_mul _ a b
  have hxφ : ∀ (j : Fin Tag.F4.rank) (c : K),
      φ (xElement (τ := Tag.F4) (K := K) j c) =
        xElement (τ := Tag.F4) (K := K) (ρ j) (c ^ ReeTag.F4.exponent j) :=
    fun j c => ReeTag.finiteExceptionalAut_xElement (t := ReeTag.F4) j c
  have hyφ : ∀ (j : Fin Tag.F4.rank) (c : K),
      φ (yElement (τ := Tag.F4) (K := K) j c) =
        yElement (τ := Tag.F4) (K := K) (ρ j) (c ^ ReeTag.F4.exponent j) :=
    fun j c => ReeTag.finiteExceptionalAut_yElement (t := ReeTag.F4) j c
  rw [hweyl i, hweyl (ρ i)]
  rw [hmap, hmap, hxφ, hyφ]
  have hneg : (-1 : K) = 1 := CharTwo.neg_eq 1
  rw [hneg]
  simp

theorem finiteExceptionalAut_F4_map_rootGroup_single
    (K : Type) [Field K] [Finite K] [CharP K ReeTag.F4.prime]
    (i : Fin Tag.F4.rank) :
    ((f4Datum K).rootGroup (Pi.single i 1)).map (ReeTag.F4.finiteExceptionalAut K).toMonoidHom =
        (f4Datum K).rootGroup (Pi.single (ReeTag.F4.perm i) 1) ∧
      ((f4Datum K).rootGroup (-Pi.single i 1)).map
          (ReeTag.F4.finiteExceptionalAut K).toMonoidHom =
        (f4Datum K).rootGroup (-Pi.single (ReeTag.F4.perm i) 1) := by
  let φ : MulAut (adjointGroup Tag.F4 K) := ReeTag.F4.finiteExceptionalAut K
  let ρ : Fin Tag.F4.rank → Fin Tag.F4.rank := fun j => ReeTag.F4.perm j
  change ((f4Datum K).rootGroup (Pi.single i 1)).map φ.toMonoidHom =
      (f4Datum K).rootGroup (Pi.single (ρ i) 1) ∧
    ((f4Datum K).rootGroup (-Pi.single i 1)).map φ.toMonoidHom =
      (f4Datum K).rootGroup (-Pi.single (ρ i) 1)
  have hxP : ∀ (j : Fin Tag.F4.rank) (c : K),
      xPar (rootOperatorFamily Tag.F4) (Pi.single j 1) c =
        xElement (τ := Tag.F4) (K := K) j c := by
    intro j c
    rw [xPar_simple]
    exact Subtype.ext ((rootOperatorFamily Tag.F4).eltUnit_simple j c)
  have hyP : ∀ (j : Fin Tag.F4.rank) (c : K),
      xPar (rootOperatorFamily Tag.F4) (-Pi.single j 1) c =
        yElement (τ := Tag.F4) (K := K) j c := by
    intro j c
    rw [xPar_neg_simple]
    exact Subtype.ext ((rootOperatorFamily Tag.F4).eltUnit_neg_simple j c)
  have hxφ : ∀ (j : Fin Tag.F4.rank) (c : K),
      φ.toMonoidHom (xElement (τ := Tag.F4) (K := K) j c) =
        xElement (τ := Tag.F4) (K := K) (ρ j) (c ^ ReeTag.F4.exponent j) :=
    fun j c => ReeTag.finiteExceptionalAut_xElement (t := ReeTag.F4) j c
  have hyφ : ∀ (j : Fin Tag.F4.rank) (c : K),
      φ.toMonoidHom (yElement (τ := Tag.F4) (K := K) j c) =
        yElement (τ := Tag.F4) (K := K) (ρ j) (c ^ ReeTag.F4.exponent j) :=
    fun j c => ReeTag.finiteExceptionalAut_yElement (t := ReeTag.F4) j c
  constructor
  · ext g
    constructor
    · intro hg
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hg
      obtain ⟨c, rfl⟩ := (mem_rootGroup_iff (isRoot_single Tag.F4 i) x).1 hx
      rw [hxP i c, hxφ i c]
      exact (mem_rootGroup_iff (isRoot_single Tag.F4 (ρ i)) _).2
        ⟨c ^ ReeTag.F4.exponent i, by rw [hxP (ρ i) (c ^ ReeTag.F4.exponent i)]⟩
    · intro hg
      obtain ⟨d, hd⟩ := (mem_rootGroup_iff (isRoot_single Tag.F4 (ρ i)) g).1 hg
      obtain ⟨c, hc⟩ :=
        finiteExceptionalAut_pow_exponent_surjective (t := ReeTag.F4) i d
      have hc' : c ^ ReeTag.F4.exponent i = d := hc
      refine Subgroup.mem_map.2 ⟨xPar (rootOperatorFamily Tag.F4) (Pi.single i 1) c, ?_, ?_⟩
      · exact xPar_mem (isRoot_single Tag.F4 i) c
      · rw [hxP i c, hxφ i c, hc', ← hxP (ρ i) d, hd]
  · ext g
    constructor
    · intro hg
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hg
      obtain ⟨c, rfl⟩ := (mem_rootGroup_iff (isRoot_neg_single Tag.F4 i) x).1 hx
      rw [hyP i c, hyφ i c]
      exact (mem_rootGroup_iff (isRoot_neg_single Tag.F4 (ρ i)) _).2
        ⟨c ^ ReeTag.F4.exponent i, by rw [hyP (ρ i) (c ^ ReeTag.F4.exponent i)]⟩
    · intro hg
      obtain ⟨d, hd⟩ :=
        (mem_rootGroup_iff (isRoot_neg_single Tag.F4 (ρ i)) g).1 hg
      obtain ⟨c, hc⟩ :=
        finiteExceptionalAut_pow_exponent_surjective (t := ReeTag.F4) i d
      have hc' : c ^ ReeTag.F4.exponent i = d := hc
      refine Subgroup.mem_map.2 ⟨xPar (rootOperatorFamily Tag.F4) (-Pi.single i 1) c, ?_, ?_⟩
      · exact xPar_mem (isRoot_neg_single Tag.F4 i) c
      · rw [hyP i c, hyφ i c, hc', ← hyP (ρ i) d, hd]

end CFSG.StandardType.LieKnownR2.Short
