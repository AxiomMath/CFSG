module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndCharNormal
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndKeySetup
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndLines
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndWeakClosure
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15GNPair
import CFSG.CharacterTheory.Semidihedral.PrimeOrderCyclicConfinementLift

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

variable {G : Type} [Group G] [Finite G] {D : Data G}

namespace Ctx82E3.A10Frame

open CFSG.GH74.Uniqueness.SU.SU13.TA.L10

variable {c : Ctx82E3 D}

theorem le_M_of_L_le (F : A10Frame c) {H : Subgroup G} (hH : CFSG.Open.IsTwoLocal H)
    (hLH : c.L ≤ H) : H ≤ D.M := by
  classical
  have hLM : c.L ≤ D.M := c.hyp81.1
  have hAG : alternatingGroup (Fin 10) ≤ ((H ⊓ D.M).subgroupOf D.M).map F.phiA := by
    rw [← F.map_L_phiA]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono D.M (le_inf hLH hLM))
  have hpa : pa ∈ A10Perm.atilde := A10Perm.mem_atilde_iff.mpr ⟨1, 0, 0, by decide +kernel⟩
  have hpb : pb ∈ A10Perm.atilde := A10Perm.mem_atilde_iff.mpr ⟨0, 1, 0, by decide +kernel⟩
  have hpae : pa = toP 1 0 0 := by simp [toP]
  have hpbe : pb = toP 0 1 0 := by simp [toP]
  have hpsa : pa.support.card = 3 := by
    rw [hpae, A10Perm.support_toP]
    decide +kernel
  have hpsb : pb.support.card = 3 := by
    rw [hpbe, A10Perm.support_toP]
    decide +kernel
  have hpsne : pa.support ≠ pb.support := by
    rw [hpae, hpbe, A10Perm.support_toP, A10Perm.support_toP]
    decide +kernel
  obtain ⟨E, hE_le, hE5, hEnc⟩ :=
    A10Perm.exists_noncyclic_five hpa hpb hpsa hpsb hpsne
  have haltA : A10Perm.altOff pa.support ≤ ((H ⊓ D.M).subgroupOf D.M).map F.phiA :=
    le_trans inf_le_left hAG
  have haltB : A10Perm.altOff pb.support ≤ ((H ⊓ D.M).subgroupOf D.M).map F.phiA :=
    le_trans inf_le_left hAG
  have hE : E ≤ ((H ⊓ D.M).subgroupOf D.M).map F.phiA :=
    le_trans hE_le (sup_le haltA haltB)
  exact c.u2 5 (by rw [F.sig]; simp) H hH
    (F.two_le_pRank_inf_of_noncyclic_five hE5 hEnc hE)

theorem normalizer_le_of_maxInv
    (F : A10Frame c) {S : Subgroup G} (hSM : S ≤ D.M) (hS : IsPGroup 2 S)
    (hAS : F.A ≤ Subgroup.normalizer (S : Set G))
    (hmax : ∀ S' : Subgroup G, S' ≤ D.M → IsPGroup 2 S' →
      F.A ≤ Subgroup.normalizer (S' : Set G) → S ≤ S' → S' = S) :
    Subgroup.normalizer (S : Set G) ≤ D.M := by
  classical
  let X : Subgroup G := c.L ⊔ S
  have hSx2 : IsPGroup 2 (S.subgroupOf X) := hS.comap_subtype
  obtain ⟨C', hC'ne, hC'S, hC'char, hC'normal⟩ :=
    A10Gen.exists_char_normal_of_a10 (X := ↥X) (L := c.L.subgroupOf X)
      (T := S.subgroupOf X) (F.charTwo_join hSM hS hAS hmax)
      (normal_L_subgroupOf_join hSM) (F.phiJoin hSM) (F.ker_phiJoin hSM hS hAS)
      (F.range_phiJoin hSM hS hAS) (F.not_L_le_ker_phiJoin hSM)
      (F.pCoreOf_join_le hSM hS hAS hmax) hSx2 (F.exists_fixed_phiJoin hSM hS hAS)
  obtain ⟨hCS, hCchar⟩ :=
    CFSG.LocalAnalysis.RankThreeUC.S15.map_subtype_characteristic
      (M := X) (T := S) (T₁' := C') le_sup_right hC'S hC'char
  let C : Subgroup G := C'.map X.subtype
  have hCne : C ≠ ⊥ := by
    intro hbot
    exact hC'ne ((Subgroup.map_eq_bot_iff_of_injective C' X.subtype_injective).mp hbot)
  have hC2 : IsPGroup 2 C := hS.to_le hCS
  have hLnormC : c.L ≤ Subgroup.normalizer (C : Set G) := by
    intro x hx
    have hxX : x ∈ X := (show c.L ≤ X from le_sup_left) hx
    have hxnorm : (⟨x, hxX⟩ : ↥X) ∈ Subgroup.normalizer (C' : Set ↥X) := by
      rw [Subgroup.normalizer_eq_top_iff.mpr hC'normal]
      exact Subgroup.mem_top _
    exact (CFSG.Glauberman.mem_normalizer_map_subtype_iff C' ⟨x, hxX⟩).mp hxnorm
  have hM2 : CFSG.Open.IsTwoLocal (Subgroup.normalizer (C : Set G)) :=
    ⟨C, hCne, hC2, rfl⟩
  have hNM : Subgroup.normalizer (C : Set G) ≤ D.M :=
    le_M_of_L_le F hM2 hLnormC
  exact le_trans
    (CFSG.Semidihedral.PrimeOrderCyclicConfinementLift.normalizer_le_of_characteristic_subgroupOf
      hCS hCchar) hNM

theorem le_M_of_isPGroup_two
    (F : A10Frame c) (hF : A10Facts F)
    (hC : ∀ B ≤ F.A, Nat.card B = 3 →
      Subgroup.centralizer (B : Set G) ≤ (Subgroup.centralizer (B : Set G) ⊓ D.M) ⊔
        CFSG.Open.relPPrimeCore 3 (Subgroup.centralizer (B : Set G)))
    {T : Subgroup G} (hT : IsPGroup 2 T) (hAT : F.A ≤ Subgroup.normalizer (T : Set G)) :
    T ≤ D.M :=
  F.le_M_of_isPGroup_two_of_normalizer_le hF hC
    (fun S hSM hS hAS hmax => F.normalizer_le_of_maxInv hSM hS hAS hmax) hT hAT

end Ctx82E3.A10Frame

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
