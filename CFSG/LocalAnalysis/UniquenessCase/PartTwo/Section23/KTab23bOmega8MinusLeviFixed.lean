module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bOmega8Minus
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bSL3Natural

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.O8Levi

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open scoped Pointwise

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}

private theorem fixedPointSubgroup_sylow_eq_map_conj_H14
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (S : Sylow 2 ↥(T3H K b c)) (h : ↥(T3H K b c))
    (hS : (S : Subgroup ↥(T3H K b c)) =
      (t3UH K b c).map (MulAut.conj h).toMonoidHom) :
    letI : MulDistribMulAction ↥S (Multiplicative (T3V K)) :=
      MulDistribMulAction.compHom (Multiplicative (T3V K))
        ((T3H K b c).subtype.comp (S : Subgroup ↥(T3H K b c)).subtype)
    (CFSG.fixedPointSubgroup ↥S (Multiplicative (T3V K)) :
        Subgroup (Multiplicative (T3V K))) =
      (linFixV (tailUnipotent 3 (minusTailForm K b c))).map
        ((h : MulAut (Multiplicative (T3V K)))).toMonoidHom := by
  letI : MulDistribMulAction ↥S (Multiplicative (T3V K)) :=
    MulDistribMulAction.compHom (Multiplicative (T3V K))
      ((T3H K b c).subtype.comp (S : Subgroup ↥(T3H K b c)).subtype)
  change (CFSG.fixedPointSubgroup ↥S (Multiplicative (T3V K)) :
      Subgroup (Multiplicative (T3V K))) =
      (linFixV (tailUnipotent 3 (minusTailForm K b c))).map
        ((h : MulAut (Multiplicative (T3V K)))).toMonoidHom
  have hfixV : (CFSG.fixedPointSubgroup ↥S (Multiplicative (T3V K)) :
      Subgroup (Multiplicative (T3V K))) =
      CFSG.Quasithin.fixV ((S : Subgroup ↥(T3H K b c)).map (T3H K b c).subtype) := by
    ext v
    constructor
    · intro hv x hx
      obtain ⟨s, hs, hxs⟩ := Subgroup.mem_map.mp hx
      have h1 := hv ⟨s, hs⟩
      change (s : MulAut (Multiplicative (T3V K))) v = v at h1
      change (x : MulAut (Multiplicative (T3V K))) v = v
      rw [← hxs]
      exact h1
    · intro hv s
      have hmem : (s : MulAut (Multiplicative (T3V K))) ∈
          (S : Subgroup ↥(T3H K b c)).map (T3H K b c).subtype :=
        Subgroup.mem_map_of_mem _ s.2
      have h1 := hv (s : MulAut (Multiplicative (T3V K))) hmem
      change (s : MulAut (Multiplicative (T3V K))) v = v
      exact h1
  have hcomp : (T3H K b c).subtype.comp (MulAut.conj h).toMonoidHom =
      (MulAut.conj ((h : ↥(T3H K b c)) :
        MulAut (Multiplicative (T3V K)))).toMonoidHom.comp (T3H K b c).subtype := rfl
  have hSH : (S : Subgroup ↥(T3H K b c)).map (T3H K b c).subtype =
      ((t3UH K b c).map (T3H K b c).subtype).map
        (MulAut.conj ((h : ↥(T3H K b c)) :
          MulAut (Multiplicative (T3V K)))).toMonoidHom := by
    rw [hS, Subgroup.map_map, hcomp, ← Subgroup.map_map]
  rw [hfixV, hSH, fixV_map_conj, t3UH_map_subtype hirr, fixV_map_linMulAut8]

theorem exists_map_conj_eq_of_sylow (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (S : Sylow 2 ↥(T3H K b c)) :
    ∃ h : ↥(T3H K b c),
      (S : Subgroup ↥(T3H K b c)) = (t3UH K b c).map (MulAut.conj h).toMonoidHom := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite ↥(T3H K b c) :=
    Finite.of_injective (fun x : ↥(T3H K b c) => (t3e K b c).symm x)
      (t3e K b c).symm.injective
  haveI : Finite (Sylow 2 ↥(T3H K b c)) := Sylow.finite_of_finiteIndex (t3SH hirr)
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq ↥(T3H K b c) (t3SH hirr) S
  refine ⟨h, ?_⟩
  have h' := congrArg (fun T : Sylow 2 ↥(T3H K b c) =>
    (T : Subgroup ↥(T3H K b c))) hh
  rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def,
    MulDistribMulAction.toMonoidEnd_apply, t3SH_coe] at h'
  exact h'.symm

theorem stabilizer_fixedPointSubgroup_eq_t3PℓH (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (S : Sylow 2 ↥(T3H K b c)) (h : ↥(T3H K b c))
    (hS : (S : Subgroup ↥(T3H K b c)) = (t3UH K b c).map (MulAut.conj h).toMonoidHom) :
    letI : MulDistribMulAction ↥(T3H K b c) (Multiplicative (T3V K)) :=
      MulDistribMulAction.compHom (Multiplicative (T3V K)) (T3H K b c).subtype
    letI : MulAction ↥(T3H K b c) (Multiplicative (T3V K)) :=
      MulAction.compHom (Multiplicative (T3V K)) (T3H K b c).subtype
    letI : MulAction ↥(T3H K b c) (Set (Multiplicative (T3V K))) := Set.mulActionSet
    letI : MulDistribMulAction ↥S (Multiplicative (T3V K)) :=
      MulDistribMulAction.compHom (Multiplicative (T3V K))
        ((T3H K b c).subtype.comp (S : Subgroup ↥(T3H K b c)).subtype)
    MulAction.stabilizer ↥(T3H K b c)
      ((CFSG.fixedPointSubgroup ↥S (Multiplicative (T3V K)) : Subgroup (Multiplicative (T3V K))) :
        Set (Multiplicative (T3V K))) = t3PℓH K b c h := by
  classical
  letI : MulDistribMulAction ↥(T3H K b c) (Multiplicative (T3V K)) :=
    MulDistribMulAction.compHom (Multiplicative (T3V K)) (T3H K b c).subtype
  letI : MulAction ↥(T3H K b c) (Multiplicative (T3V K)) :=
    MulAction.compHom (Multiplicative (T3V K)) (T3H K b c).subtype
  letI : MulAction ↥(T3H K b c) (Set (Multiplicative (T3V K))) := Set.mulActionSet
  change MulAction.stabilizer ↥(T3H K b c)
      ((@CFSG.fixedPointSubgroup ↥S (Multiplicative (T3V K)) _ _
        (MulDistribMulAction.compHom (Multiplicative (T3V K))
          ((T3H K b c).subtype.comp (S : Subgroup ↥(T3H K b c)).subtype)) :
        Subgroup (Multiplicative (T3V K))) : Set (Multiplicative (T3V K))) = t3PℓH K b c h
  have hℓ := fixedPointSubgroup_sylow_eq_map_conj_H14 (K := K) (b := b) (c := c) hirr S h hS
  have hset : (h : ↥(T3H K b c)) •
        (linFixV (tailUnipotent 3 (minusTailForm K b c)) :
          Set (Multiplicative (T3V K))) =
      (((linFixV (tailUnipotent 3 (minusTailForm K b c))).map
        ((h : MulAut (Multiplicative (T3V K)))).toMonoidHom :
          Subgroup (Multiplicative (T3V K))) : Set (Multiplicative (T3V K))) := by
    ext x
    simp only [Set.mem_smul_set, Subgroup.mem_map, SetLike.mem_coe]
    exact ⟨fun ⟨y, hy, hxy⟩ => ⟨y, hy, by simpa [MulAction.compHom_smul_def] using hxy⟩,
      fun ⟨y, hy, hxy⟩ => ⟨y, hy, by simpa [MulAction.compHom_smul_def] using hxy⟩⟩
  have hbridge : MulAction.stabilizer ↥(T3H K b c)
      (linFixV (tailUnipotent 3 (minusTailForm K b c)) :
        Subgroup (Multiplicative (T3V K))) =
      MulAction.stabilizer ↥(T3H K b c)
        (↑(linFixV (tailUnipotent 3 (minusTailForm K b c))) :
          Set (Multiplicative (T3V K))) := by
    ext g
    rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
    exact ⟨fun hg => by rwa [← Subgroup.coe_pointwise_smul, SetLike.coe_set_eq],
      fun hg => by rwa [← Subgroup.coe_pointwise_smul, SetLike.coe_set_eq] at hg⟩
  rw [hℓ, ← hset, MulAction.stabilizer_smul_eq_stabilizer_map_conj (h : ↥(T3H K b c))
    (linFixV (tailUnipotent 3 (minusTailForm K b c)) : Set (Multiplicative (T3V K))),
    ← hbridge, (t3Pℓ0H_eq_stabilizer hirr).symm]

end CFSG.LocalAnalysis.UniquenessCase.UC22.O8Levi
