module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Nine24XDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Nine24XThreeEltsCore
import CFSG.GroupTheory.ThreeTranspositions.QuotientLift

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup
open CFSG.GroupTheory.ThreeTranspositions (HasE9)

theorem kFactL2EvenThreeElts_holds : KFactL2EvenThreeElts := by
  classical
  intro Z _ _ X n hXn _ hL2 hrank z hz
  haveI : X.Normal := hXn
  let O : Subgroup ↥X := CFSG.pCore 2 ↥X
  let Ō : Subgroup Z := O.map X.subtype
  haveI hŌn : Ō.Normal :=
    ConjAct.normal_of_characteristic_of_normal (H := X) (K := O)
  have hŌle : Ō ≤ X := Subgroup.map_subtype_le O
  have hŌ2 : IsPGroup 2 Ō := (CFSG.pCore_isPGroup (p := 2) (G := ↥X)).map X.subtype
  have hŌnot3 : ¬ 3 ∣ Nat.card Ō := by
    obtain ⟨k, hk⟩ := hŌ2.exists_card_dvd_pow
    intro h3
    exact absurd (Nat.prime_three.dvd_of_dvd_pow (h3.trans hk)) (by norm_num)
  let mk : Z →* Z ⧸ Ō := QuotientGroup.mk' Ō
  let X' : Subgroup (Z ⧸ Ō) := X.map mk
  haveI hX'n : X'.Normal := hXn.map mk (QuotientGroup.mk'_surjective Ō)
  let φ : ↥X →* Z ⧸ Ō := mk.comp X.subtype
  let f : ↥X →* ↥X' := φ.codRestrict X' (fun x => Subgroup.mem_map_of_mem mk x.2)
  have hfsurj : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hfker : f.ker = O := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have h1 : φ x = 1 := congrArg Subtype.val hx
      have h2 : (x : Z) ∈ O.map X.subtype :=
        (QuotientGroup.eq_one_iff (N := Ō) (x : Z)).mp h1
      obtain ⟨o, ho, hox⟩ := Subgroup.mem_map.mp h2
      exact Subtype.ext hox ▸ ho
    · intro hx
      apply Subtype.ext
      change (QuotientGroup.mk' Ō) (x : Z) = (1 : Z ⧸ Ō)
      exact (QuotientGroup.eq_one_iff (N := Ō) (x : Z)).mpr
        (Subgroup.mem_map_of_mem X.subtype hx)
  have hX'L2 : IsL2 ↥X' (2 * n) :=
    CFSG.Blueprint.LieModel.of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hfker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective f hfsurj)) hL2
  have hE9Z : ¬ HasE9 Z := fun h => absurd h.two_le_pRank (by omega)
  have hE9Z' : ¬ HasE9 (Z ⧸ Ō) := fun h =>
    hE9Z (CFSG.GroupTheory.ThreeTranspositions.hasE9_of_hasE9_quotient Ō hŌnot3 h)
  have hz' : IsPGroup 3 (Subgroup.zpowers (mk z)) := by
    rw [← MonoidHom.map_zpowers (f := mk) (x := z)]
    exact hz.map mk
  have hmem : mk z ∈ X' :=
    mem_of_isPGroup_three_of_isL2_normal hX'n hX'L2 hE9Z' hz'
  obtain ⟨x, hxX, hxeq⟩ := Subgroup.mem_map.mp hmem
  have hmemO : x⁻¹ * z ∈ Ō := by
    apply (QuotientGroup.eq_one_iff (N := Ō) (x⁻¹ * z)).mp
    show mk (x⁻¹ * z) = 1
    rw [map_mul, map_inv, hxeq, inv_mul_cancel]
  have hz_eq : x * (x⁻¹ * z) = z := by group
  rw [← hz_eq]
  exact X.mul_mem hxX (hŌle hmemO)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
