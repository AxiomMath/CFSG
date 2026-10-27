module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Stmt
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35ChBase
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.At

open S35.Std

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G} {β α' m γ' : Geo H M}

omit [Finite G] in
theorem Back.facts (hp : S34.PD β α') (hb : Back H M β α' m γ') :
    vtype m = true ∧ vtype γ' = false ∧ γ' ≠ α' ∧ dist β m + 2 = bMin H M ∧
      dist β γ' + 3 = bMin H M := by
  obtain ⟨hm, hγ, d1, d2⟩ := hb
  have hd := hp.dist_eq
  have hm' : vtype m = true := vtype_nbr_S5 hp.vδ' hm
  refine ⟨hm', vtype_nbr_S3 hm' hγ, ?_, by omega, by omega⟩
  rintro rfl
  omega

theorem Back.Vn_le (hS : Sit H M S) (hp : S34.PD β α') (hb : Back H M β α' m γ') :
    Vn β ≤ stab α' ∧ Vn β ≤ stab m ∧ Vn β ≤ Qv m := by
  obtain ⟨-, -, -, h1, -⟩ := Back.facts hp hb
  have hQ : Vn β ≤ Qv m := Vn_le_Qv_dist hS (by omega)
  exact ⟨hQ.trans (Qv_le_stab hS (mem_nbrs_symm.mp hb.1)), hQ.trans (Ch.Qv_le_stab' m), hQ⟩

theorem Back.comm (hS : Sit H M S) (hp : S34.PD β α') (hb : Back H M β α' m γ') :
    ∀ a ∈ Vn β, ∀ b ∈ Vn γ', a * b = b * a := by
  obtain ⟨-, -, -, -, h1⟩ := Back.facts hp hb
  exact Vn_commute_dist hS (by omega)

theorem Back.Wb_le_stab (hS : Sit H M S) (hp : S34.PD β α') (hb : Back H M β α' m γ') :
    Wb β ≤ stab γ' := by
  obtain ⟨-, -, -, -, h1⟩ := Back.facts hp hb
  refine iSup₂_le fun ρ hρ => Vn_le_stab_dist hS ?_
  have h2 := dist_triangle rfl ρ β γ'
  omega

omit [Finite G] in
@[expose] def commSub (V : Subgroup G) (k : G) : Subgroup G where
  carrier := {w | w ∈ Subgroup.normalizer (V : Set G) ∧ ⁅w, k⁆ ∈ V}
  one_mem' := ⟨(Subgroup.normalizer (V : Set G)).one_mem, by simp⟩
  mul_mem' := fun {a b} ha hb => by
    refine ⟨(Subgroup.normalizer (V : Set G)).mul_mem ha.1 hb.1, ?_⟩
    have e : ⁅a * b, k⁆ = a * ⁅b, k⁆ * a⁻¹ * ⁅a, k⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact V.mul_mem (((Subgroup.mem_normalizer_iff.mp ha.1) _).mp hb.2) ha.2
  inv_mem' := fun {a} ha => by
    refine ⟨(Subgroup.normalizer (V : Set G)).inv_mem ha.1, ?_⟩
    have e : ⁅a⁻¹, k⁆ = a⁻¹ * ⁅a, k⁆⁻¹ * a := by
      simp only [commutatorElement_def]; group
    rw [e]
    have h1 : ⁅a, k⁆⁻¹ ∈ V := V.inv_mem ha.2
    have h2 := (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer (V : Set G)).inv_mem ha.1) _).mp h1
    simpa [mul_assoc] using h2

omit [Finite G] in
theorem mem_commSub {V : Subgroup G} {k w : G} :
    w ∈ commSub V k ↔ w ∈ Subgroup.normalizer (V : Set G) ∧ ⁅w, k⁆ ∈ V := Iff.rfl

end S35.At

end F53.Stellmacher

end CFSG.Quasithin
