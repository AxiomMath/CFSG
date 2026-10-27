module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Stmt2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53

namespace S35.II

variable {G : Type} [Group G] [Finite G] {H M : Subgroup G}

omit [Finite G] in
theorem exists_notMem_both (R A B : Subgroup G) (hA : ¬ R ≤ A) (hB : ¬ R ≤ B) :
    ∃ r ∈ R, r ∉ A ∧ r ∉ B := by
  obtain ⟨x, hxR, hxA⟩ := IsConcreteLE.not_le_iff_exists.mp hA
  obtain ⟨y, hyR, hyB⟩ := IsConcreteLE.not_le_iff_exists.mp hB
  by_cases hxB : x ∈ B
  · by_cases hyA : y ∈ A
    · refine ⟨x * y, R.mul_mem hxR hyR, fun h => hxA ?_, fun h => hyB ?_⟩
      · simpa using A.mul_mem h (A.inv_mem hyA)
      · simpa using B.mul_mem (B.inv_mem hxB) h
    · exact ⟨y, hyR, hyA, hyB⟩
  · exact ⟨x, hxR, hxA, hxB⟩

omit [Finite G] in
theorem back_rev (hb5 : bMin H M = 5) {β α' la γ lb : Geo H M} (hp : S34.PD β α')
    (hla : la ∈ nbrs β) (hγla : γ ∈ nbrs la) (hB : Back H M β α' lb γ) :
    Back H M α' β la γ := by
  obtain ⟨hlb, hγlb, h1, h2⟩ := hB
  have hd := hp.dist_eq
  have e1 : dist α' lb = 1 := dist_eq_one_iff_adj.mpr hlb
  have e2 : dist lb γ = 1 := dist_eq_one_iff_adj.mpr hγlb
  have e3 : dist la γ = 1 := dist_eq_one_iff_adj.mpr hγla
  have e4 : dist β la = 1 := dist_eq_one_iff_adj.mpr hla
  have e3' : dist γ la = 1 := by rw [CosetGeom.dist_comm]; exact e3
  have e4' : dist la β = 1 := by rw [CosetGeom.dist_comm]; exact e4
  have t1 : dist α' γ ≤ dist α' lb + dist lb γ := CosetGeom.dist_triangle rfl α' lb γ
  have t2 : dist α' la ≤ dist α' γ + dist γ la := CosetGeom.dist_triangle rfl α' γ la
  have t3 : dist α' β ≤ dist α' la + dist la β := CosetGeom.dist_triangle rfl α' la β
  have e5 : dist α' β = dist β α' := CosetGeom.dist_comm _ _
  refine ⟨hla, hγla, ?_, ?_⟩ <;> omega

omit [Finite G] in
theorem thmBa (h3a : Claim3a H M) : ThmBa H M := by
  intro hb5 β la γ lb α' hL hL' hla hγla hB
  have hB' : Back H M α' β la γ := back_rev hb5 hL.1 hla hγla hB
  have h1 := (h3a β α' lb γ hL.1 hB).2
  have h2 := (h3a α' β la γ hL'.1 hB').2
  rw [Subgroup.commutator_comm] at h2
  exact exists_notMem_both _ _ _ h2 h1

end S35.II

end F53.Stellmacher

end CFSG.Quasithin
