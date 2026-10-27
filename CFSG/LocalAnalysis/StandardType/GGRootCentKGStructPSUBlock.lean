module

public import CFSG.LocalAnalysis.StandardType.GGRootCentKGOTwoPSUCent
public import CFSG.LieType.Steinberg.CentralExt.SUOddFieldThreeLevi

public section

namespace CFSG.StandardType.KGPSU

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LieType.Universal.Unitary (SU)
open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree (iotaHom)

variable {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

@[expose] noncomputable def blockHom (h : UnitaryFieldData 2 f K) (k : ℕ) :
    SU (unitaryInvolution K 2 f) k →* AutPSU.PJ h (k + 2) :=
  (AutPSU.projU h).comp (iotaHom (σ := unitaryInvolution K 2 f) (m := k))

@[expose] noncomputable def suBlock (h : UnitaryFieldData 2 f K) (k : ℕ) :
    Subgroup (AutPSU.PJ h (k + 2)) :=
  (blockHom h k).range

@[expose] noncomputable def blockOnto (h : UnitaryFieldData 2 f K) (k : ℕ) :
    SU (unitaryInvolution K 2 f) k →* ↥(suBlock h k) :=
  (blockHom h k).rangeRestrict

theorem blockOnto_surjective (h : UnitaryFieldData 2 f K) (k : ℕ) :
    Function.Surjective (blockOnto h k) :=
  MonoidHom.rangeRestrict_surjective _

theorem suBlock_le_leviFull (h : UnitaryFieldData 2 f K) (k : ℕ) :
    suBlock h k ≤ leviFull h (k + 1) := by
  rintro _ ⟨B, rfl⟩
  have hm1 : 1 ≤ k + 1 := by omega
  have hB := RCSTSU.range_iotaHom_le_centralizer (σ := unitaryInvolution K 2 f) (k := k)
    ⟨B, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff] at hB
  rw [leviFull, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff, y0_of_le h hm1]
  refine ⟨?_, ?_⟩
  · change AutPSU.projU h (iotaHom B) * AutPSU.projU h _ =
      AutPSU.projU h _ * AutPSU.projU h (iotaHom B)
    rw [← map_mul, ← map_mul]
    exact congrArg (AutPSU.projU h) hB
  · change AutPSU.projU h (iotaHom B) * AutPSU.projU h _ =
      AutPSU.projU h _ * AutPSU.projU h (iotaHom B)
    rw [← map_mul, ← map_mul, iotaHom_commute_lroot]

theorem suBlock_le_normalizer_radical (h : UnitaryFieldData 2 f K) {k : ℕ} (hk : 2 ≤ k) :
    suBlock h k ≤ Subgroup.normalizer (radical h (k + 1) : Set (AutPSU.PJ h (k + 2))) :=
  (suBlock_le_leviFull h k).trans (leviFull_le_normalizer_radical h (by omega))

theorem radical_inf_suBlock (h : UnitaryFieldData 2 f K) {k : ℕ} (hk : 2 ≤ k) :
    radical h (k + 1) ⊓ suBlock h k = ⊥ :=
  ((disjoint_radical_leviFull h (by omega)).mono_right (suBlock_le_leviFull h k)).eq_bot

theorem radical_sup_suBlock_le_centralizer (h : UnitaryFieldData 2 f K) {k : ℕ} (hk : 2 ≤ k) :
    radical h (k + 1) ⊔ suBlock h k ≤
      Subgroup.centralizer {AutPSU.projU h (AutPSU.rootU (K := K) (f := f) (k + 1))} := by
  rw [centralizer_rootU_eq_sup h (by omega)]
  exact sup_le_sup_left (suBlock_le_leviFull h k) _

end CFSG.StandardType.KGPSU
