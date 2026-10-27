module

public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5LayerFrame
public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitSU
public import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompSUComp

public section

namespace CFSG.StandardType.Line63.H5

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.SectionRank.OddCover CFSG.StandardType.TableBUE CFSG.StandardType.TableBUD
  CFSG.Assembly CFSG.StandardType

variable {K : Type} [Field K] {n d : ℕ}

@[expose] def suToPGL (K : Type) [Field K] (n d : ℕ) :
    ↥(unitarySU 2 n K d) →* GL (Fin d) K ⧸ LargeEvenScalars (Fin d) K :=
  (QuotientGroup.mk' (LargeEvenScalars (Fin d) K)).comp (unitarySU 2 n K d).subtype

theorem ker_suToPGL_le_center :
    (suToPGL K n d).ker ≤ Subgroup.center ↥(unitarySU 2 n K d) := by
  intro z hz
  have hz' : (z : GL (Fin d) K) ∈ LargeEvenScalars (Fin d) K :=
    (QuotientGroup.eq_one_iff (z : GL (Fin d) K)).mp hz
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext (Subgroup.mem_center_iff.mp (TableB.scalars_le_center hz') g)

@[expose] def reducedToPGL (K : Type) [Field K] (n d : ℕ) :
    LargeEvenProj (unitarySU 2 n K d) →* GL (Fin d) K ⧸ LargeEvenScalars (Fin d) K :=
  QuotientGroup.lift _ (suToPGL K n d) fun z hz =>
    (QuotientGroup.eq_one_iff (z : GL (Fin d) K)).mpr (Subgroup.mem_subgroupOf.mp hz)

theorem reducedToPGL_injective : Function.Injective (reducedToPGL K n d) := by
  rw [injective_iff_map_eq_one]
  intro r hr
  obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective r
  have hr' : suToPGL K n d s = 1 := hr
  exact (QuotientGroup.eq_one_iff s).mpr
    (Subgroup.mem_subgroupOf.mpr ((QuotientGroup.eq_one_iff (s : GL (Fin d) K)).mp hr'))

theorem map_ggFix_eq {D : GL (Fin d) K}
    (hD : D ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K))) :
    (ggFix (TableB.projConj (unitarySU 2 n K d) ⟨D, hD⟩)).map (reducedToPGL K n d) =
      (suToPGL K n d).range ⊓
        Subgroup.centralizer ({(QuotientGroup.mk D : GL (Fin d) K ⧸ LargeEvenScalars (Fin d) K)} :
          Set (GL (Fin d) K ⧸ LargeEvenScalars (Fin d) K)) := by
  ext x
  constructor
  · rintro ⟨r, hr, rfl⟩
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective r
    obtain ⟨c, hc⟩ := exists_conj_eq_scalar_mul hD hr
    refine ⟨⟨s, rfl⟩, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    show QuotientGroup.mk D * QuotientGroup.mk (s : GL (Fin d) K) =
      QuotientGroup.mk (s : GL (Fin d) K) * QuotientGroup.mk D
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    have e : D * (s : GL (Fin d) K) =
        GeneralLinearGroup.scalar (Fin d) c * ((s : GL (Fin d) K) * D) := by
      calc D * (s : GL (Fin d) K) = (D * s * D⁻¹) * D := by group
        _ = GeneralLinearGroup.scalar (Fin d) c * ((s : GL (Fin d) K) * D) := by
            rw [hc, mul_assoc]
    have hsc : GeneralLinearGroup.scalar (Fin d) c ∈ LargeEvenScalars (Fin d) K := ⟨c, rfl⟩
    rw [e, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr hsc, one_mul]
  · rintro ⟨⟨s, rfl⟩, hx⟩
    refine ⟨LargeEvenProjMk (unitarySU 2 n K d) s, ?_, rfl⟩
    have h1 := Subgroup.mem_centralizer_iff.mp hx _ (Set.mem_singleton _)
    change QuotientGroup.mk D * QuotientGroup.mk (s : GL (Fin d) K) =
      QuotientGroup.mk (s : GL (Fin d) K) * QuotientGroup.mk D at h1
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at h1
    have hcen := TableB.scalars_le_center h1
    refine mem_ggFix.mpr ?_
    rw [projConj_mk_coe]
    refine QuotientGroup.eq.mpr (Subgroup.mem_subgroupOf.mpr ?_)
    have e : ((((unitarySU 2 n K d).normalizerMonoidHom ⟨D, hD⟩ s)⁻¹ * s :
        ↥(unitarySU 2 n K d)) : GL (Fin d) K) = (D * s)⁻¹ * (s * D) := by
      show (D * (s : GL (Fin d) K) * D⁻¹)⁻¹ * (s : GL (Fin d) K) = _
      calc (D * (s : GL (Fin d) K) * D⁻¹)⁻¹ * s = D * ((D * s)⁻¹ * (s * D)) * D⁻¹ := by group
        _ = (D * s)⁻¹ * (s * D) := by
            rw [Subgroup.mem_center_iff.mp hcen D, mul_inv_cancel_right]
    rw [e]
    exact h1

theorem not_isComponentOf_layer_ggFix_diag_two (hKd : UnitaryFieldData 2 1 K)
    {τ : Fin 6 → Kˣ} (hD : diagHom 6 τ ∈ Subgroup.normalizer
      (unitarySU 2 1 K 6 : Set (GL (Fin 6) K)))
    (hb : ∀ (i : Fin 6) (S : Finset (Fin 6)), (∀ j, j ∈ S ↔ τ j = τ i) → S.card ≤ 3) :
    ¬ IsComponentOf (LargeEvenLayer (ggFix (TableB.projConj (unitarySU 2 1 K 6)
      ⟨diagHom 6 τ, hD⟩))) (ggFix (TableB.projConj (unitarySU 2 1 K 6) ⟨diagHom 6 τ, hD⟩)) := by
  classical
  haveI : Finite K := hKd.finite
  intro hE
  set ē : GL (Fin 6) K ⧸ LargeEvenScalars (Fin 6) K := QuotientGroup.mk (diagHom 6 τ) with hē
  have hJ := isComponentOf_map_of_injective (reducedToPGL K 1 6) reducedToPGL_injective hE
  rw [map_ggFix_eq hD] at hJ
  have hδ : ∀ e ∈ ({ē} : Set (GL (Fin 6) K ⧸ LargeEvenScalars (Fin 6) K)),
      (e, diagHom (5 + 1) ((fun _ => τ) e)) ∈ SUTorus.suPairs (suToPGL K 1 6) := by
    intro e he
    rw [Set.mem_singleton_iff] at he
    subst he
    refine ⟨hD, fun u v huv => ?_⟩
    show QuotientGroup.mk (diagHom 6 τ) * QuotientGroup.mk (u : GL (Fin 6) K) *
      (QuotientGroup.mk (diagHom 6 τ))⁻¹ = QuotientGroup.mk (v : GL (Fin 6) K)
    rw [huv, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  obtain ⟨i, hi⟩ := SUTorus.exists_le_map_blockSU (m := 5) hKd Nat.prime_three (by norm_num)
    ker_suToPGL_le_center hδ hJ
  have hcls : (LinTorus.diagClass {ē} (fun _ => τ) i).card ≤ 3 :=
    hb i _ fun j => by simp [LinTorus.mem_diagClass]
  have hcls1 : 1 ≤ (LinTorus.diagClass {ē} (fun _ => τ) i).card :=
    Finset.card_pos.mpr ⟨i, LinTorus.self_mem_diagClass _ _ i⟩
  haveI hBs : Group.IsSolvable ↥((TableBUE.blockSU (K := K) (n := 1)
      (LinTorus.diagClass {ē} (fun _ => τ) i)).map (suToPGL K 1 6)) :=
    WitSU.isSolvable_map_blockSU_two_one hKd (suToPGL K 1 6) hcls1 hcls
  exact isQuasisimple_not_isSolvable hJ.2.2
    (solvable_of_solvable_injective (Subgroup.inclusion_injective hi))

end CFSG.StandardType.Line63.H5

end
