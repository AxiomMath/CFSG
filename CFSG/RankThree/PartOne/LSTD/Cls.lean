module

public import CFSG.RankThree.PartOne.LSTD.ClsA
public import CFSG.RankThree.PartOne.LSTD.ClsB
public import CFSG.RankThree.PartOne.LSTD.PermW

public section

namespace CFSG.RankThree.PartOne.LSTD

open Matrix CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryCoord CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.CTP

variable {f : ℕ} {K : Type} [Field K]

section Conj

variable {P : Type} [Group P]

theorem isPerfect_conjBy (g : P) {X : Subgroup P} (hX : Group.IsPerfect ↥X) :
    Group.IsPerfect ↥(conjBy g X) := by
  have e := Subgroup.equivMapOfInjective X (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective

theorem conjBy_le_centralizer (g : P) {X : Subgroup P} {x : P}
    (hX : X ≤ Subgroup.centralizer ({x} : Set P)) :
    conjBy g X ≤ Subgroup.centralizer ({g * x * g⁻¹} : Set P) := by
  rintro _ ⟨y, hy, rfl⟩
  have hc := Subgroup.mem_centralizer_singleton_iff.mp (hX hy)
  rw [Subgroup.mem_centralizer_singleton_iff]
  show g * y * g⁻¹ * (g * x * g⁻¹) = g * x * g⁻¹ * (g * y * g⁻¹)
  calc g * y * g⁻¹ * (g * x * g⁻¹) = g * (y * x) * g⁻¹ := by group
    _ = g * (x * y) * g⁻¹ := by rw [hc]
    _ = g * x * g⁻¹ * (g * y * g⁻¹) := by group

theorem card_conjBy (g : P) (X : Subgroup P) : Nat.card ↥(conjBy g X) = Nat.card ↥X :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

end Conj

section Cls

variable (hU : UnitaryFieldData 2 f K) (h5 : 5 ∣ 2 ^ f + 1)

theorem Wmodel_conj_tSU (ρ : Equiv.Perm (Fin 5)) {v : Fin 5 → Kˣ} (hv : v ∈ torusVec 5 5 K) :
    Wmodel hU ρ.symm * projU K f (tSU hU h5 v hv) * (Wmodel hU ρ.symm)⁻¹ =
      projU K f (tSU hU h5 (v ∘ ρ) (torusVec_comp ρ hv)) := by
  rw [Wmodel_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, InvMemClass.coe_inv, coe_permSU, coe_tSU, coe_tSU,
    permGL_conj_diagU, Equiv.symm_symm]

include h5 in
theorem classify_b [Finite K] (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ 5)
    {x : StatedProj (unitarySU 2 f K 5)} (hxT : x ∈ torusBar K f) (hx1 : x ≠ 1)
    (X : Subgroup (StatedProj (unitarySU 2 f K 5))) (hX : Group.IsPerfect ↥X)
    (hXc : X ≤ Subgroup.centralizer ({x} : Set (StatedProj (unitarySU 2 f K 5))))
    (hXcard : Nat.card ↥X = Nat.card ↥(unitarySU 2 f K 3)) :
    ∃ τ : Equiv.Perm (Fin 5), Wmodel hU τ * x * (Wmodel hU τ)⁻¹ ∈ Jfun hU 3 4 ∧
      conjBy (Wmodel hU τ) X = Jfun hU 0 1 ⊔ Jfun hU 1 2 := by
  obtain ⟨ζ, hζ'⟩ := hζ
  obtain ⟨v, hv, rfl⟩ := (mem_torusBar_iff hU h5).mp hxT
  have hnc : ∃ i j, v i ≠ v j := by
    by_contra hcon
    push Not at hcon
    apply hx1
    have hconst : v = fun _ => v 0 := funext fun i => hcon i 0
    have hv' : (fun _ : Fin 5 => v 0) ∈ torusVec 5 5 K := hconst ▸ hv
    have hxs : tSU hU h5 v hv = tSU hU h5 (fun _ => v 0) hv' := Subtype.ext (congrArg diagU hconst)
    have : tSU hU h5 v hv ∈ scalarsU K f := by
      rw [hxs]
      exact const_mem_scalarsU hU h5 hv'
    rw [← ker_projU] at this
    exact this
  obtain ⟨ρ, hρ⟩ := exists_perm_cases_units hζ' v hv.1 hv.2 hnc
  have hw : v ∘ ρ ∈ torusVec 5 5 K := torusVec_comp ρ hv
  have hconj := Wmodel_conj_tSU hU h5 ρ hv
  set g := Wmodel hU ρ.symm with hg
  have hX' := isPerfect_conjBy g hX
  have hXc' := conjBy_le_centralizer g hXc
  rw [hconj] at hXc'
  have hXcard' : Nat.card ↥(conjBy g X) = Nat.card ↥(unitarySU 2 f K 3) := by
    rw [card_conjBy, hXcard]
  rcases hρ with hA | hB
  · obtain ⟨t, ht, h1, hxt⟩ := projU_tSU_eq_bB hU h5 hw hA
    refine ⟨ρ.symm, ?_, ?_⟩
    · rw [← hg, hconj, hxt]
      exact projU_bB_mem_Jfun hU h5 ht
    · rw [← hg, Kbar_eq_range hU (two_le_of_five_dvd h5)]
      rw [hxt] at hXc'
      exact eq_range_of_bB hU h5 ht h1 (conjBy g X) hX' hXc' hXcard'
  · exact (false_of_B5 hU h5 hw hB (conjBy g X) hX' hXc' hXcard').elim

end Cls

end CFSG.RankThree.PartOne.LSTD
