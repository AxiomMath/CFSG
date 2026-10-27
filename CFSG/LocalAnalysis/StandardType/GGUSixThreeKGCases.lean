module

public import CFSG.LocalAnalysis.StandardType.GGUSixThreeKGDefs
public import CFSG.LocalAnalysis.StandardType.GGUSixThreeKGFrameCase
public import CFSG.LocalAnalysis.StandardType.GGUSixThreeKGHeisCase
public import CFSG.LocalAnalysis.StandardType.GGUSixThreeKGFieldType
public import CFSG.LocalAnalysis.StandardType.GGUSixThreeKGFieldNorm
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitarySixThreeCases
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63Two

public section

namespace CFSG.StandardType.UnitSixThreeKG

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.SectionRank.OddCover CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.StandardType.TableBUE CFSG.StandardType.TableBUD CFSG.Assembly CFSG.StandardType

theorem perLineOn_of_cover {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hpq : 3 ∣ 2 ^ n + 1)
    (hperfSU : commutator (unitarySU 2 n K 6) = ⊤)
    {L' : Type} [Group L'] [Finite L'] {ψ : L' →* LargeEvenProj (unitarySU 2 n K 6)}
    (hcov' : ∀ ψ'' : L' →* LargeEvenProj (unitarySU 2 n K 6), Function.Surjective ψ'' →
      ψ''.ker = ψ.ker →
      ∃ φ : ↥(unitarySU 2 n K 6) →* L', ∀ s, ψ'' (φ s) = LargeEvenProjMk (unitarySU 2 n K 6) s)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hA : CFSG.Open.IsElemAbelian 3 A)
    (hAI : ∀ a ∈ A, ∃ x ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n K 6))
      (LargeEvenGUSet (Fin 6) K (2 ^ n)), ∀ l : L', x (ψ l) = ψ (a l))
    (hcard : 3 ^ 3 ≤ Nat.card A) : PerLineOn A := by
  classical
  have h : UnitaryFieldData 2 n K := TableBU.unitaryFieldData_of_card hK hn
  have hdq : ((6 : ℕ), 2 ^ n) ≠ (3, 2) := fun he => by
    have := congrArg Prod.fst he
    simp only at this
    omega
  have hp3 : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp3⟩
  have hAb : CFSG.Open.IsElemAbelian 3 (TypeA.inducedSub ψ A) :=
    TypeA.isElemAbelian_inducedSub hψ hA
  have hAbI : ∀ x ∈ TypeA.inducedSub ψ A, x ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (unitarySU 2 n K 6)) (LargeEvenGUSet (Fin 6) K (2 ^ n)) := by
    intro x hx
    obtain ⟨a, ha, hxa⟩ := TypeA.mem_inducedSub.mp hx
    obtain ⟨y, hy, hya⟩ := hAI a ha
    rw [TypeA.induced_unique ψ hψ hxa hya]
    exact hy
  have hcardAb : Nat.card (TypeA.inducedSub ψ A) = Nat.card A :=
    TypeA.card_inducedSub hψ hker hperf (fun a ha => by
      obtain ⟨y, -, hy⟩ := hAI a ha
      exact ⟨y, hy⟩)
  by_cases hfr : ∃ P ∈ primeFormUnitary h (idGram K 6), ∀ a ∈ TypeA.inducedSub ψ A,
      ∃ (M : GL (Fin 6) K) (hM : M ∈ LargeEvenGUSet (Fin 6) K (2 ^ n)),
        ((P⁻¹ * M * P : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).IsDiag ∧
          a = TableB.projConj (unitarySU 2 n K 6) ⟨M, gu_subset_normalizer h hM⟩
  · obtain ⟨P, hP, hfra⟩ := hfr
    refine perLineOn_of_frame h hperfSU hcov' hψ hker hperf hA hP (fun a ha => ?_)
    obtain ⟨x, -, hx⟩ := hAI a ha
    have hxAb : x ∈ TypeA.inducedSub ψ A := TypeA.mem_inducedSub.mpr ⟨a, ha, hx⟩
    obtain ⟨M, hM, hdiag, hxeq⟩ := hfra x hxAb
    exact ⟨M, hM, hdiag, fun l => by rw [← hxeq]; exact hx l⟩
  · have h81 : Nat.card A < 3 ^ 4 := by
      by_contra hge
      push Not at hge
      exact hfr (TableBUD.exists_unitary_frame h hK (by norm_num) hdq hp3 hpq hAb hAbI
        (by rw [hcardAb]; simpa using hge))
    haveI : Finite (MulAut L') := Finite.of_injective (fun φ : MulAut L' => (φ : L' → L'))
      DFunLike.coe_injective
    have hA3 : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hA.2 g.1 g.2)⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hA3
    have hk3 : k = 3 := by
      rw [hk] at hcard h81
      rcases Nat.lt_or_ge k 3 with hlt | hge
      · have := Nat.pow_le_pow_right (show 0 < 3 by norm_num) (show k ≤ 2 by omega)
        omega
      · rcases Nat.lt_or_ge k 4 with hlt4 | hge4
        · omega
        · have := Nat.pow_le_pow_right (show 0 < 3 by norm_num) hge4
          omega
    have hcard27 : Nat.card A = 27 := by rw [hk, hk3]; norm_num
    have hcardAb' : 3 ^ 3 ≤ Nat.card (TypeA.inducedSub ψ A) := by rw [hcardAb]; exact hcard
    rcases TableBU63.fieldType_or_heis h hK hpq hAb hAbI hcardAb' hfr with
      ⟨M, hMN, l, hMu, hM3, hl, hMA⟩ | ⟨x, y, z, hxN, hyN, hzN, ζ, hxu, hyu, hzu, hxA, hyA, hzA,
        hx3, hz3, hζ3, hζ1, hxy, hxz, hyz, hzs⟩
    · exact perLineOn_of_fieldType h hK hpq hperfSU hcov' hψ hker hperf hA hAI hcard27 hMN hMu
        hM3 hl hMA
    · have hζ : IsPrimitiveRoot ζ 3 := by
        have := IsPrimitiveRoot.orderOf ζ
        rwa [orderOf_eq_prime hζ3 hζ1] at this
      obtain ⟨s, hs⟩ : ∃ s : Kˣ, y ^ 3 = GeneralLinearGroup.scalar (Fin 6) s := by
        have h3 : (TableB.projConj (unitarySU 2 n K 6) ⟨y, hyN⟩) ^ 3 = 1 := hAb.2 _ hyA
        rw [← map_pow] at h3
        obtain ⟨k', hk'⟩ :=
          TableBUE.mem_scalars_of_projConj_eq_one h hK (by norm_num) hdq hp3 hpq h3
        exact ⟨k', hk'.symm⟩
      by_cases hcube : ∃ t : Kˣ, t ^ 3 = s
      · obtain ⟨t, ht⟩ := hcube
        have hc : ∀ g : GL (Fin 6) K, GeneralLinearGroup.scalar (Fin 6) t⁻¹ * g =
            g * GeneralLinearGroup.scalar (Fin 6) t⁻¹ := fun g => (commute_scalar t⁻¹ g).symm.eq
        have hy'3 : (GeneralLinearGroup.scalar (Fin 6) t⁻¹ * y) ^ 3 = 1 := by
          rw [TableBU63.scalar_mul_pow, hs, ← map_mul, ← ht, inv_pow, inv_mul_cancel, map_one]
        have hsU : GeneralLinearGroup.scalar (Fin 6) (t ^ 3) ∈
            primeFormUnitary h (idGram K 6) := by
          rw [ht, ← hs]
          exact pow_mem hyu 3
        have htU := scalar_mem_primeFormUnitary_of_cube h hpq hsU
        have hy'u : GeneralLinearGroup.scalar (Fin 6) t⁻¹ * y ∈
            primeFormUnitary h (idGram K 6) := by
          rw [map_inv]
          exact Subgroup.mul_mem _ (Subgroup.inv_mem _ htU) hyu
        have hsN : GeneralLinearGroup.scalar (Fin 6) t⁻¹ ∈
            Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)) :=
          TableB.scalar_mem_normalizer _ ⟨t⁻¹, rfl⟩
        have hy'N : GeneralLinearGroup.scalar (Fin 6) t⁻¹ * y ∈
            Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)) :=
          Subgroup.mul_mem _ hsN hyN
        have hy'A : TableB.projConj (unitarySU 2 n K 6)
            ⟨GeneralLinearGroup.scalar (Fin 6) t⁻¹ * y, hy'N⟩ ∈ TypeA.inducedSub ψ A := by
          have e : (⟨GeneralLinearGroup.scalar (Fin 6) t⁻¹ * y, hy'N⟩ : Subgroup.normalizer
              (unitarySU 2 n K 6 : Set (GL (Fin 6) K))) = ⟨_, hsN⟩ * ⟨y, hyN⟩ := rfl
          rw [e, map_mul, TableB.projConj_of_scalar _ ⟨t⁻¹, rfl⟩, one_mul]
          exact hyA
        have hxy' : x * (GeneralLinearGroup.scalar (Fin 6) t⁻¹ * y) =
            GeneralLinearGroup.scalar (Fin 6) ζ *
              ((GeneralLinearGroup.scalar (Fin 6) t⁻¹ * y) * x) := by
          calc x * (GeneralLinearGroup.scalar (Fin 6) t⁻¹ * y)
              = (x * GeneralLinearGroup.scalar (Fin 6) t⁻¹) * y := (mul_assoc _ _ _).symm
            _ = (GeneralLinearGroup.scalar (Fin 6) t⁻¹ * x) * y := by rw [← hc x]
            _ = GeneralLinearGroup.scalar (Fin 6) t⁻¹ * (x * y) := mul_assoc _ _ _
            _ = GeneralLinearGroup.scalar (Fin 6) t⁻¹ *
                (GeneralLinearGroup.scalar (Fin 6) ζ * (y * x)) := by rw [hxy]
            _ = GeneralLinearGroup.scalar (Fin 6) ζ *
                (GeneralLinearGroup.scalar (Fin 6) t⁻¹ * (y * x)) := by
                rw [← mul_assoc, hc (GeneralLinearGroup.scalar (Fin 6) ζ), mul_assoc]
            _ = GeneralLinearGroup.scalar (Fin 6) ζ *
                ((GeneralLinearGroup.scalar (Fin 6) t⁻¹ * y) * x) := by rw [mul_assoc]
        have hy'z : (GeneralLinearGroup.scalar (Fin 6) t⁻¹ * y) * z =
            z * (GeneralLinearGroup.scalar (Fin 6) t⁻¹ * y) := by
          calc (GeneralLinearGroup.scalar (Fin 6) t⁻¹ * y) * z
              = GeneralLinearGroup.scalar (Fin 6) t⁻¹ * (y * z) := mul_assoc _ _ _
            _ = GeneralLinearGroup.scalar (Fin 6) t⁻¹ * (z * y) := by rw [hyz]
            _ = (GeneralLinearGroup.scalar (Fin 6) t⁻¹ * z) * y := (mul_assoc _ _ _).symm
            _ = (z * GeneralLinearGroup.scalar (Fin 6) t⁻¹) * y := by rw [hc z]
            _ = z * (GeneralLinearGroup.scalar (Fin 6) t⁻¹ * y) := mul_assoc _ _ _
        exact perLineOn_of_heisTriple h hpq hψ hker hperf hA hAI hcard27 hxN hy'N hzN hxu hy'u hzu
          hx3 hy'3 hz3 hζ hxy' hxz hy'z hzs hxA hy'A hzA
      · exact perLineOn_of_fieldType h hK hpq hperfSU hcov' hψ hker hperf hA hAI hcard27 hyN hyu hs
          (fun t ht => hcube ⟨t, ht⟩) hyA

end CFSG.StandardType.UnitSixThreeKG

end
