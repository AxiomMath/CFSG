module

public import CFSG.LieType.BorelTits.HeldFlagSU
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniDefs
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.LieType.BorelTits.CompleteFlag

public section

namespace CFSG.StandardType.TablePThreeKG

open Matrix CFSG.AGLEmbedding

section

open CFSG.LieType.BorelTits

theorem heldFlagGU {K : Type} [Field K] [Finite K] [CharP K 2] {n q : ℕ} (hK : Nat.card K = q ^ 2)
    (G T : Subgroup (GL (Fin n) K)) (hG : ∀ g ∈ G, IsHermIsometry q (g : Matrix (Fin n) (Fin n) K))
    (hTG : T ≤ G) (hT : T ≠ ⊥) (hT2 : IsPGroup 2 T) :
    ∃ W : Submodule K (Fin n → K), W ≠ ⊥ ∧ IsTotallyIsotropicSU q W ∧
      ∀ y ∈ G, y ∈ Subgroup.normalizer (T : Set (GL (Fin n) K)) →
        ∀ w ∈ W, (y : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W := by
  obtain ⟨f, -, rfl⟩ := ToralCensus.exists_eq_two_pow_of_card_eq_sq hK
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK' : Nat.card K = (2 ^ f) ^ 2 := hK
  set R : Subgroup G := T.subgroupOf G with hR
  have hRne : R ≠ ⊥ := by
    intro hbot
    apply hT
    rw [Subgroup.eq_bot_iff_forall]
    intro t ht
    have htR : (⟨t, hTG ht⟩ : G) ∈ R := by
      rw [hR]
      exact Subgroup.mem_subgroupOf.mpr ht
    rw [hbot, Subgroup.mem_bot] at htR
    simpa using congrArg Subtype.val htR
  have hRp : IsPGroup 2 R := by
    rw [hR, ← Subgroup.comap_subtype T G]
    exact hT2.comap_subtype
  have hρ : IsIsometric (unitaryForm 2 f hK' n) (natRep G) := by
    intro g u v
    rw [natRep_apply, natRep_apply, unitaryForm_β hK']
    simp only [unitaryInvolution_apply]
    exact hG g g.2 u v
  have hinj : Function.Injective (natRep G) := natRep_injective G
  refine ⟨isoSeq (unitaryForm 2 f hK' n) (natRep G) R 1,
    isoSeq_one_ne_bot _ _ 2 hρ hinj R hRp hRne, ?_, ?_⟩
  · intro v hv w hw
    have hWiso := isoSeq_isTotallyIsotropic (unitaryForm 2 f hK' n) (natRep G) R 1
    have hperp : w ∈ (unitaryForm 2 f hK' n).perp
        (isoSeq (unitaryForm 2 f hK' n) (natRep G) R 1) := hWiso hw
    have hβ := (ReflForm.mem_perp _).mp hperp v hv
    rw [unitaryForm_β hK'] at hβ
    simp only [unitaryInvolution_apply] at hβ
    exact hβ
  · intro y hyG hy w hw
    have hyR : (⟨y, hyG⟩ : G) ∈ Subgroup.normalizer (R : Set G) := by
      rw [hR]
      have hy' : (⟨y, hyG⟩ : G) ∈
          (Subgroup.normalizer (T : Set (GL (Fin n) K))).subgroupOf G :=
        Subgroup.mem_subgroupOf.mpr hy
      rwa [Subgroup.subgroupOf_normalizer_eq hTG] at hy'
    have hmem := apply_mem_isoSeq (unitaryForm 2 f hK' n) (natRep G) hρ R 1 hyR hw
    rwa [natRep_apply] at hmem

end

end CFSG.StandardType.TablePThreeKG

end
