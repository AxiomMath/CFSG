module

public import CFSG.RankThree.PartTwo.Sec8.Notation
public import CFSG.RankThree.PartTwo.Sec4.LThreePiDefs
import CFSG.ClassicalInvolution.ModelFacts.OddCover.ThreeQ
import CFSG.RankThree.PartTwo.Census.Classical.Bridges

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.Assembly.RankThreeEven (projImage projSL projSU)
open Matrix

theorem isCyclic_sylow_of_mulEquiv_projImage {X : Type*} [Group X] {ι : Type} [Fintype ι]
    [DecidableEq ι] {K : Type} [Field K] [Finite K] {H : Subgroup (GL ι K)}
    (e : X ≃* projImage H) {r : ℕ} [Fact r.Prime] (hH : ∀ S : Sylow r H, IsCyclic S)
    (Q : Sylow r X) : IsCyclic Q := by
  have hf : Function.Surjective (e.symm.toMonoidHom.comp (ProjGenLinGroup.mk.subgroupMap H)) :=
    e.symm.surjective.comp (MonoidHom.subgroupMap_surjective _ _)
  obtain ⟨S, rfl⟩ := Sylow.mapSurjective_surjective hf r Q
  have := hH S
  rw [Sylow.coe_mapSurjective]
  exact isCyclic_of_surjective _ (MonoidHom.subgroupMap_surjective _ _)

theorem isCyclic_sylow_three_of_mulEquiv_projSL {X : Type*} [Group X] {K : Type} [Field K]
    [Finite K] (hK : Nat.card K % 3 = 2) (e : X ≃* projSL 3 K) (Q : Sylow 3 X) : IsCyclic Q := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine isCyclic_sylow_of_mulEquiv_projImage e (fun S => ?_) Q
  exact SectionRank.OddCover.isCyclic_of_isPGroup_of_le_GL_three (by omega) (by omega)
    S.isPGroup'

theorem isCyclic_sylow_three_projSL {K : Type} [Field K] [Finite K] (hK : Nat.card K % 3 = 2)
    (Q : Sylow 3 (projSL 3 K)) : IsCyclic Q :=
  isCyclic_sylow_three_of_mulEquiv_projSL hK (MulEquiv.refl _) Q

theorem isCyclic_sylow_three_of_mulEquiv_projSU {X : Type*} [Group X] {p f : ℕ} [Fact p.Prime]
    (hf : f ≠ 0) (hq : p ^ f % 3 = 1) (e : X ≃* projSU 3 p f) (Q : Sylow 3 X) : IsCyclic Q := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 := by
    rw [GaloisField.card p (2 * f) (by omega), ← pow_mul, mul_comm]
  have hp3 : (3 : ℕ) ≠ p := by
    rintro rfl
    rw [Nat.pow_mod, Nat.mod_self, zero_pow hf] at hq
    simp at hq
  exact isCyclic_sylow_of_mulEquiv_projImage
    (e.trans (MulEquiv.subgroupCongr (Census.projImage_statedSU 3 p f).symm))
    (ClassicalInvolution.ModelFacts.OddCover.statedSU_three_isCyclic_sylow hK (by norm_num) hp3
      (by omega)) Q

theorem isCyclic_sylow_three_projSU {p f : ℕ} [Fact p.Prime] (hf : f ≠ 0) (hq : p ^ f % 3 = 1)
    (Q : Sylow 3 (projSU 3 p f)) : IsCyclic Q :=
  isCyclic_sylow_three_of_mulEquiv_projSU hf hq (MulEquiv.refl _) Q

theorem isCyclic_sylow_three_of_isoLThreeMinusPi_of_ne_zero {X : Type} [Group X] {p e : ℕ}
    [Fact p.Prime] (he : e ≠ 0) (h : Sec8.IsoLThreeMinusPi X p e) (Q : Sylow 3 X) :
    IsCyclic Q := by
  rcases h with ⟨hq, ⟨φ⟩⟩ | ⟨hq, ⟨φ⟩⟩
  · exact isCyclic_sylow_three_of_mulEquiv_projSU he hq φ Q
  · refine isCyclic_sylow_three_of_mulEquiv_projSL ?_ φ Q
    rwa [GaloisField.card p e he]

theorem isCyclic_sylow_three_of_isoLThreeMinusPi {X : Type} [Group X] {n : ℕ} (hn : 1 ≤ n)
    (h : Sec8.IsoLThreeMinusPi X 2 (3 * n)) (Q : Sylow 3 X) : IsCyclic Q :=
  isCyclic_sylow_three_of_isoLThreeMinusPi_of_ne_zero (by omega) h Q

theorem cycThree_pow_three {K : Type} [Field K] : (Sec4.cycThree : GL (Fin 3) K) ^ 3 = 1 := by
  ext i j
  rw [Units.val_pow_eq_pow_val, Sec4.coe_cycThree, Units.val_one]
  fin_cases i <;> fin_cases j <;> simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three]

theorem mk_cycThree_ne_one {K : Type} [Field K] :
    ProjGenLinGroup.mk (Sec4.cycThree : GL (Fin 3) K) ≠ 1 := by
  rw [Ne, ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar]
  rintro ⟨u, hu⟩
  have h := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) hu
  simp [Sec4.coe_cycThree] at h

theorem three_dvd_card_of_mulEquiv_projImage {X : Type*} [Group X] {K : Type} [Field K]
    {H : Subgroup (GL (Fin 3) K)} (e : X ≃* projImage H) (hH : Sec4.cycThree ∈ H) :
    3 ∣ Nat.card X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let x : projImage H := ⟨ProjGenLinGroup.mk Sec4.cycThree, Subgroup.mem_map_of_mem _ hH⟩
  have hx1 : x ≠ 1 := fun hx => mk_cycThree_ne_one (congrArg Subtype.val hx)
  have hx3 : x ^ 3 = 1 := Subtype.ext (by
    change ProjGenLinGroup.mk Sec4.cycThree ^ 3 = 1
    rw [← map_pow, cycThree_pow_three, map_one])
  have hx := orderOf_dvd_natCard x
  rw [orderOf_eq_prime hx3 hx1] at hx
  rwa [Nat.card_congr e.toEquiv]

theorem three_dvd_card_of_mulEquiv_projSL {X : Type*} [Group X] {K : Type} [Field K]
    (e : X ≃* projSL 3 K) : 3 ∣ Nat.card X := by
  refine three_dvd_card_of_mulEquiv_projImage e ?_
  rw [MonoidHom.mem_ker]
  ext
  rw [GeneralLinearGroup.val_det_apply, Sec4.coe_cycThree, det_fin_three]
  simp

theorem three_dvd_card_of_mulEquiv_projSU {X : Type*} [Group X] {p f : ℕ} [Fact p.Prime]
    (hf : f ≠ 0) (e : X ≃* projSU 3 p f) : 3 ∣ Nat.card X := by
  have hK : LocalAnalysis.ComponentInitial.UnitaryFieldData p f (GaloisField p (2 * f)) :=
    ⟨Fact.out, Nat.one_le_iff_ne_zero.mpr hf, GaloisField.card p (2 * f) (by omega)⟩
  exact three_dvd_card_of_mulEquiv_projImage
    (e.trans (MulEquiv.subgroupCongr (Census.projImage_statedSU 3 p f).symm))
    (Sec4.cycThree_mem_slPi (π := false) fun _ => hK)

theorem three_dvd_card_of_isoLThreeMinusPi_of_ne_zero {X : Type} [Group X] {p e : ℕ}
    [Fact p.Prime] (he : e ≠ 0) (h : Sec8.IsoLThreeMinusPi X p e) : 3 ∣ Nat.card X := by
  rcases h with ⟨-, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
  · exact three_dvd_card_of_mulEquiv_projSU he φ
  · exact three_dvd_card_of_mulEquiv_projSL φ

theorem three_dvd_card_of_isoLThreeMinusPi {X : Type} [Group X] {n : ℕ} (hn : 1 ≤ n)
    (h : Sec8.IsoLThreeMinusPi X 2 (3 * n)) : 3 ∣ Nat.card X :=
  three_dvd_card_of_isoLThreeMinusPi_of_ne_zero (by omega) h

end CFSG.RankThree.PartTwo.KFacts
