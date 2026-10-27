module

public import CFSG.OddTranspositions.PartFour.ThirteenListThreeFischerPoints
public import CFSG.OddTranspositions.PartFour.ThirteenListThreeFischerOrder
public import CFSG.Fischer.ConjugationEmbedding
public import CFSG.Sporadic.Fi22.LH.Root
public import Certificates.Certificate1164101
public import CFSG.Sporadic.Fi22.LH.Orbit

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Sporadic.Fi22 CFSG.Sporadic.Fi22.Native CFSG.Fischer Subgroup
open scoped Pointwise


theorem fi22_lhRoot_closure_card_le (i : Fin 2) :
    Nat.card (Subgroup.closure (Subtype.val '' lhRoot i)) ≤ 4585351680 := by
  let : MulAction J D := MulAction.compHom D (Pair.conjPerm pair_D)
  have horbit : MulAction.orbit J (lhRoot i) = lhOrbit i := by
    ext T
    simp only [MulAction.mem_orbit_iff, lhOrbit, Set.mem_setOf_eq]
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g, rfl⟩
    · rintro ⟨g, rfl⟩
      exact ⟨g, rfl⟩
  have hindex : (MulAction.stabilizer J (lhRoot i)).index = 14080 := by
    rw [MulAction.index_stabilizer, horbit, ncard_lhOrbit]
  have hcard := (MulAction.stabilizer J (lhRoot i)).card_mul_index
  rw [hindex, card_J] at hcard
  have hle : Subgroup.closure (Subtype.val '' lhRoot i) ≤ MulAction.stabilizer J (lhRoot i) := by
    intro g hg
    rw [MulAction.mem_stabilizer_iff]
    have h := conj_image_lhRoot_of_mem_closure i hg
    change (fun x : D => Pair.conjPerm pair_D g x) '' lhRoot i = lhRoot i
    apply Set.image_injective.2 Subtype.val_injective
    simpa only [Set.image_image, Function.comp_def, Pair.conjPerm_apply] using h
  have hbound := Subgroup.card_le_of_le hle
  omega

end CFSG.OddTranspositions.PartFour

namespace CFSG.OddTranspositions.FischerMarked

open CFSG.Fischer.Classification CFSG.Sporadic.Fi22 CFSG.Sporadic.Fi22.Native
open CFSG.F3.Native CFSG.Sporadic.Th.Native CFSG.OddTranspositions.PartFour CFSG.Fischer

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

attribute [local irreducible] lhData pointCodes pointIndices fi22Indices

abbrev fi22Pts : Array ℕ := (lhData ())[0]!


theorem fi22Marked_conj (i j : Fin 351) :
    ap (cTab orb (genTables orb (-2)) fi22Pts[i.val]!) fi22Pts[j.val]! =
      fi22Pts[(pointIndex (reflectPoint (point i) (point j))).val]! :=
  Certificates.certificate1164101 i j

theorem fi22Pts_inj {i j : Fin 351} (h : fi22Pts[i.val]! = fi22Pts[j.val]!) : i = j := by
  have hinc := (lhData_parts.2 0 (by decide)).2.2.1
  have hmono : ∀ a b, a < b → b < 351 → fi22Pts[a]! < fi22Pts[b]! := by
    intro a b hab hb
    induction b with
    | zero => omega
    | succ b ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hab with h' | h'
      · exact (ih h' (by omega)).trans (hinc b (by omega))
      · rw [h']
        exact hinc b (by omega)
  rcases lt_trichotomy i.val j.val with h' | h' | h'
  · exact absurd h (hmono _ _ h' j.2).ne
  · exact Fin.ext h'
  · exact absurd h (hmono _ _ h' i.2).ne'

abbrev fi22Set : Set J := Subtype.val '' lhRoot 0

private theorem lhData_zero_lt (i : Fin 351) : fi22Pts[i.val]! < 3510 :=
  lhData_lt (by decide) i.2

private theorem lhData_zero_size : fi22Pts.size = 351 :=
  (lhData_parts.2 0 (by decide)).1

theorem conjPt_lhData_mem (i : Fin 351) : conjPt (fi22Pts[i.val]!) ∈ fi22Set := by
  have hx : ⟨fi22Pts[i.val]!, lhData_zero_lt i⟩ ∈
      {k : Fin 3510 | k.val ∈ fi22Pts} := by
    change fi22Pts[i.val]! ∈ fi22Pts
    rw [getElem!_pos _ _ (by rw [lhData_zero_size]; exact i.2)]
    exact Array.getElem_mem _
  exact ⟨_, ⟨_, hx, rfl⟩, rfl⟩

@[expose] noncomputable def fi22Point (i : Fin 351) : fi22Set :=
  ⟨conjPt (fi22Pts[i.val]!), conjPt_lhData_mem i⟩

theorem fi22Point_bijective : Function.Bijective fi22Point := by
  constructor
  · intro i j hij
    have h := conjPt_inj (by rw [orb_size]; exact lhData_zero_lt i)
      (by rw [orb_size]; exact lhData_zero_lt j) (congrArg Subtype.val hij)
    exact fi22Pts_inj h
  · rintro ⟨x, hx⟩
    obtain ⟨d, ⟨k, hk, rfl⟩, rfl⟩ := hx
    obtain ⟨i, hi, he⟩ := Array.mem_iff_getElem.mp hk
    have hfi : i < 351 := by
      change i < fi22Pts.size at hi
      rwa [lhData_zero_size] at hi
    refine ⟨⟨i, hfi⟩, Subtype.ext ?_⟩
    change conjPt (fi22Pts[i]!) = conjPt k.val
    change fi22Pts[i] = k.val at he
    rw [getElem!_pos fi22Pts i hi, he]

@[expose] noncomputable def fi22PointEquiv : Fin 351 ≃ fi22Set :=
  Equiv.ofBijective fi22Point fi22Point_bijective

theorem fi22PointEquiv_apply (i : Fin 351) : fi22PointEquiv i = fi22Point i := rfl

theorem fi22Point_conj (i j : Fin 351) :
    (fi22Point (pointIndex (reflectPoint (point i) (point j))) : J) =
      fi22Point i * fi22Point j * fi22Point i := by
  change conjPt _ = conjPt _ * conjPt _ * conjPt _
  rw [conjPt_mul_conjPt (lhData_zero_lt i) (lhData_zero_lt j), tT_get (lhData_zero_lt i)]
  exact congrArg conjPt (fi22Marked_conj i j).symm

@[expose] noncomputable def fi22Bijection : fi22Set ≃ D3 (diagF3 7 1) :=
  fi22PointEquiv.symm.trans reflPointEquiv

theorem fi22Bijection_apply (i : Fin 351) : fi22Bijection (fi22Point i) = reflPoint i := by
  change reflPointEquiv (fi22PointEquiv.symm (fi22Point i)) = _
  rw [← fi22PointEquiv_apply, fi22PointEquiv.symm_apply_apply, reflPointEquiv_apply]

theorem fi22Set_mul_self {x : J} (hx : x ∈ fi22Set) : x * x = 1 := by
  obtain ⟨d, -, rfl⟩ := hx
  exact CFSG.Fischer.Pair.mul_self pair_D d.2

theorem fi22Set_conj_mem {x y : J} (hx : x ∈ fi22Set) (hy : y ∈ fi22Set) :
    x * y * x ∈ fi22Set := lhRoot_closed 0 hx hy

theorem fi22Bijection_conj (x y : fi22Set) :
    (fi22Bijection ⟨x * y * x, fi22Set_conj_mem x.2 y.2⟩ : R3 (diagF3 7 1)) =
      fi22Bijection x * fi22Bijection y * fi22Bijection x := by
  obtain ⟨i, rfl⟩ := fi22PointEquiv.surjective x
  obtain ⟨j, rfl⟩ := fi22PointEquiv.surjective y
  let k := pointIndex (reflectPoint (point i) (point j))
  have hk : (⟨fi22PointEquiv i * fi22PointEquiv j * fi22PointEquiv i,
      fi22Set_conj_mem (fi22PointEquiv i).2 (fi22PointEquiv j).2⟩ : fi22Set) =
      fi22PointEquiv k := Subtype.ext (fi22Point_conj i j).symm
  rw [hk, fi22PointEquiv_apply, fi22PointEquiv_apply, fi22PointEquiv_apply,
    fi22Bijection_apply, fi22Bijection_apply, fi22Bijection_apply]
  exact reflPoint_reflect i j

attribute [local irreducible] fi22Bijection fi22PointEquiv fi22Point reflPointEquiv reflPoint

theorem exists_fi22_refl_embedding :
    ∃ ι : R3 (diagF3 7 1) →* J, Function.Injective ι ∧
      ∀ i : Fin 351, ι (reflPoint i) = fi22Point i := by
  have hfin : Finite (Subgroup.closure fi22Set) := Subtype.finite
  obtain ⟨ι, hι, hιβ⟩ := @exists_embedding_of_conjugation_bijection J
    (R3 (diagF3 7 1)) _ _ fi22Set hfin
    (fun _ hx => fi22Set_mul_self hx) (fun _ hx _ hy => fi22Set_conj_mem hx hy)
    (D3 (diagF3 7 1))
    (pair_R3 (isF3Form_diagF3 (m := 7) (δ := 1) (by decide)) (by decide))
    (center_R3_eq_bot (isF3Form_diagF3 (m := 7) (δ := 1) (by decide)) (by decide))
    fi22Bijection fi22Bijection_conj
    ((fi22_lhRoot_closure_card_le (0 : Fin 2)).trans
      (natCard_R3_seven_ge (isF3Form_diagF3 (m := 7) (δ := 1) (by decide))))
  refine ⟨ι, hι, fun i => ?_⟩
  have h := hιβ (fi22Point i)
  rwa [fi22Bijection_apply] at h

end CFSG.OddTranspositions.FischerMarked
