module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPGapF4Data
public import Certificates.Certificate43
import CFSG.LocalAnalysis.UniquenessCase.UC22P22d
import CFSG.GroupTheory.AlternatingFive.SylowTwo
public import CFSG.CGT.Timmesfeld75.Cfg214Gen
public import CFSG.LargeExtraspecial.S9TIXC
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPShape
public import CFSG.LocalAnalysis.WeakClosure81.SevenFour
public import CFSG.LocalAnalysis.WeakClosure81.SevenKGen
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup

private theorem wcgapif_card_sylowTwo_sl2 {F : Type} [Field F]
    [Finite F] (hF : Nat.card F = 4) :
    Nat.card (Sylow 2 (Matrix.SpecialLinearGroup (Fin 2) F)) = 5 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL2 : CFSG.LocalAnalysis.UniquenessCase.UC22.IsL2
      (Matrix.SpecialLinearGroup (Fin 2) F) 2 :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22d_isL2_of_statedSL (n := 2) (F := F)
      (by norm_num) (by rw [hF]; norm_num)
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F)
  obtain ⟨e⟩ : Nonempty (Matrix.SpecialLinearGroup (Fin 2) F ≃*
      alternatingGroup (Fin 5)) :=
    CFSG.LocalAnalysis.ComponentInitial.PSL2_four_alternating_five_model _ hL2
  have hinj : Function.Injective (Sylow.mapSurjective (p := 2) (f := e.toMonoidHom)
      e.surjective :
      Sylow 2 (Matrix.SpecialLinearGroup (Fin 2) F) → Sylow 2 (alternatingGroup (Fin 5))) := by
    intro P Q h
    apply Sylow.ext
    have h' : (P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)).map e.toMonoidHom =
        (Q : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)).map e.toMonoidHom :=
      congrArg (fun S : Sylow 2 (alternatingGroup (Fin 5)) =>
        (S : Subgroup (alternatingGroup (Fin 5)))) h
    exact Subgroup.map_injective (f := e.toMonoidHom) e.injective h'
  have hsurj : Function.Surjective (Sylow.mapSurjective (p := 2) (f := e.toMonoidHom)
      e.surjective :
      Sylow 2 (Matrix.SpecialLinearGroup (Fin 2) F) → Sylow 2 (alternatingGroup (Fin 5))) :=
    Sylow.mapSurjective_surjective (p := 2) (f := e.toMonoidHom) e.surjective
  calc Nat.card (Sylow 2 (Matrix.SpecialLinearGroup (Fin 2) F))
      = Nat.card (Sylow 2 (alternatingGroup (Fin 5))) :=
        Nat.card_congr (Equiv.ofBijective
          (Sylow.mapSurjective (p := 2) (f := e.toMonoidHom) e.surjective) ⟨hinj, hsurj⟩)
    _ = 5 := CFSG.GroupTheory.AlternatingFive.card_sylowTwo

theorem relIndex_normalizer_eq_five_of_surj_sl2 {M : Type}
    [Group M] [Finite M] {U K Q : Subgroup M} {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 4) (hU : IsPGroup 2 U) (hUK : U ≤ K) (hQU : Q ≤ U)
    (hUidx : ¬ 2 ∣ U.relIndex (⊤ : Subgroup M))
    (φ : ↥K →* Matrix.SpecialLinearGroup (Fin 2) F) (hφ : Function.Surjective φ)
    (hker : φ.ker = Q.subgroupOf K) :
    (K ⊓ ((⊤ : Subgroup M) ⊓ normalizer (U : Set M))).relIndex K = 5 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU'p : IsPGroup 2 (U.subgroupOf K) := hU.comap_subtype (K := K)
  have hU'idx : ¬ 2 ∣ (U.subgroupOf K).index := by
    have hmul := Subgroup.relIndex_mul_relIndex (H := U) (K := K) (L := ⊤) hUK le_top
    rw [Subgroup.relIndex_top_right] at hmul
    intro h
    refine hUidx ?_
    rw [← hmul]
    rw [show U.relIndex K = (U.subgroupOf K).index from rfl]
    exact dvd_mul_of_dvd_left h K.index
  have hkerU : φ.ker ≤ U.subgroupOf K := by
    rw [hker]
    exact Subgroup.subgroupOf_mono K hQU
  have hkerN : φ.ker ≤ Subgroup.normalizer
      ((U.subgroupOf K : Subgroup ↥K) : Set ↥K) :=
    hkerU.trans Subgroup.le_normalizer
  have hmapN : (Subgroup.normalizer
        ((U.subgroupOf K : Subgroup ↥K) : Set ↥K)).map φ =
      Subgroup.normalizer ((U.subgroupOf K).map φ) :=
    CFSG.ComponentClassification.CentralTwoBInclusion.normalizer_image φ hφ
      (U.subgroupOf K) hkerU
  let S : Sylow 2 ↥K := hU'p.toSylow hU'idx
  have hScoe : (S : Subgroup ↥K) = U.subgroupOf K := IsPGroup.toSylow_coe hU'p hU'idx
  let S' : Sylow 2 (Matrix.SpecialLinearGroup (Fin 2) F) :=
    S.mapSurjective (f := φ) hφ
  have hS'coe : (S' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) =
      (U.subgroupOf K).map φ := by
    rw [Sylow.coe_mapSurjective, hScoe]
  have hidx : (Subgroup.normalizer
      ((U.subgroupOf K : Subgroup ↥K) : Set ↥K)).index = 5 := by
    calc (Subgroup.normalizer
          ((U.subgroupOf K : Subgroup ↥K) : Set ↥K)).index
        = ((Subgroup.normalizer
            ((U.subgroupOf K : Subgroup ↥K) : Set ↥K)).map φ).index :=
          (Subgroup.index_map_eq (Subgroup.normalizer
            ((U.subgroupOf K : Subgroup ↥K) : Set ↥K)) hφ hkerN).symm
      _ = (Subgroup.normalizer ((U.subgroupOf K).map φ)).index := by rw [hmapN]
      _ = (Subgroup.normalizer
            (S' : Set (Matrix.SpecialLinearGroup (Fin 2) F))).index := by
          rw [← hS'coe]
          rfl
      _ = Nat.card (Sylow 2 (Matrix.SpecialLinearGroup (Fin 2) F)) :=
          (Sylow.card_eq_index_normalizer S').symm
      _ = 5 := wcgapif_card_sylowTwo_sl2 hF
  have hB : (K ⊓ normalizer (U : Set M)).subgroupOf K =
      Subgroup.normalizer ((U.subgroupOf K : Subgroup ↥K) : Set ↥K) := by
    rw [Subgroup.inf_subgroupOf_left, Subgroup.subgroupOf_normalizer_eq hUK]
  rw [top_inf_eq, Subgroup.relIndex, hB]
  exact hidx

end CFSG.LocalAnalysis.WeakClosure81

end
