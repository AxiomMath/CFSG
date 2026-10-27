module

public import CFSG.RankThree.PartTwo.Sec20.Item20Res5ProofSteps
import CFSG.RankThree.PartTwo.Sec20.Item20Res6ProofTools
import CFSG.RankThree.PartTwo.Sec18.Components
import CFSG.GroupTheory.PerfectResidualNodes

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late

@[expose] def Step204YKO3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) (T : Subgroup G)
    (i j : Fin 4) (P : Subgroup G), Setting204 G A M L N c T i j P →
      ∀ X ∈ scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G), X ≠ M →
        CFSG.Open.pRank 3 (yTwenty X c) ≤ 1 →
        yTwenty X c ≤ kTwenty M c ⊔ inSubgroup (CFSG.pPrimeCore 3) (yTwenty X c) →
          IsPGroup 2 (inSubgroup (CFSG.pPrimeCore 3) (yTwenty X c))

@[expose] def Step204YAlphaNe : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) (T : Subgroup G)
    (i j : Fin 4) (P : Subgroup G), Setting204 G A M L N c T i j P →
      ∀ X ∈ scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G), X ≠ M →
        CFSG.Open.pRank 3 (yTwenty X c) ≤ 1 →
          ¬ yTwenty X c ≤ kTwenty M c ⊔ oThreePrimeYR M X T c

namespace Res6

variable {G : Type} [Group G] [Finite G]

theorem le_sup_inSubgroup_pPrimeCore {K Y R : Subgroup G} (hKY : K ≤ Y)
    (hle : Y ≤ K ⊔ inSubgroup (CFSG.pPrimeCore 3) (Y ⊔ R)) :
    Y ≤ K ⊔ inSubgroup (CFSG.pPrimeCore 3) Y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set O' := inSubgroup (CFSG.pPrimeCore 3) (Y ⊔ R) with hO'
  have hYO' : Y ≤ Subgroup.normalizer (O' : Set G) :=
    le_sup_left.trans (le_normalizer_inSubgroup_pPrimeCore 3 (Y ⊔ R))
  have hKO' : K ≤ Subgroup.normalizer (O' : Set G) := hKY.trans hYO'
  have hmeet : Y ⊓ O' ≤ inSubgroup (CFSG.pPrimeCore 3) Y := by
    refine le_inSubgroup_pPrimeCore inf_le_left (fun y hy => ?_) ?_
    · exact Sec20.mem_normalizer_inf_of_mem (Subgroup.le_normalizer hy) (hYO' hy)
    · have hdvd : Nat.card (Y ⊓ O' : Subgroup G) ∣ Nat.card O' :=
        Subgroup.card_dvd_of_le inf_le_right
      exact Nat.Coprime.coprime_dvd_right hdvd (coprime_card_inSubgroup_pPrimeCore 3 _)
  intro y hy
  have hy' : y ∈ ((K ⊔ O' : Subgroup G) : Set G) := hle hy
  rw [Subgroup.coe_mul_of_left_le_normalizer_right K O' hKO'] at hy'
  obtain ⟨k, hk, o, ho, rfl⟩ := hy'
  have hoY : o ∈ Y := by
    have : k⁻¹ * (k * o) ∈ Y := Y.mul_mem (Y.inv_mem (hKY hk)) hy
    simpa using this
  exact Subgroup.mul_mem_sup hk (hmeet ⟨hoY, ho⟩)

end Res6

theorem step204YAlphaNe_of (h : Step204YKO3) : Step204YAlphaNe := by
  intro G _ _ A M L N c T i j P hset X hX hXM hm hle
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := kTwenty M c with hKdef
  set Y := yTwenty X c with hYdef
  set R := CFSG.Open.pCoreOf 2 (K ⊔ T) with hRdef
  set O3 := inSubgroup (CFSG.pPrimeCore 3) Y with hO3
  have hKM : K ≤ M := Res6.kTwenty_le_M hset
  have hTM : T ≤ M := hset.sylow.le
  have hKTX : K ⊔ T ≤ X := fun x hx => hX.2 hx
  have hKX : K ≤ X := le_sup_left.trans hKTX
  have hKY : K ≤ Y := Res6.kTwenty_le_yTwenty hset hKX
  have hMK : M ≤ Subgroup.normalizer (K : Set G) := le_normalizer_normalClosureIn M c
  have hXY : X ≤ Subgroup.normalizer (Y : Set G) := le_normalizer_normalClosureIn X c
  have hXO3 : X ≤ Subgroup.normalizer (O3 : Set G) :=
    hXY.trans (Res6.normalizer_le_normalizer_inSubgroup_pPrimeCore 3 Y)
  have hRKT : R ≤ K ⊔ T := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hle3 : Y ≤ K ⊔ O3 := Res6.le_sup_inSubgroup_pPrimeCore hKY hle
  have hO32 : IsPGroup 2 O3 := h G A M L N c T i j P hset X hX hXM hm hle3
  have hO3R : O3 ≤ R := by
    have hmax := mem_maxInvariantPiSubgroups_iff.mp hset.maxInvariant
    have hRO3 : R ≤ Subgroup.normalizer (O3 : Set G) := (hRKT.trans hKTX).trans hXO3
    have hZ2 : IsPGroup 2 (O3 ⊔ R : Subgroup G) := hO32.to_sup_of_normal_left' hR2 hRO3
    have hZmem : (O3 ⊔ R : Subgroup G) ∈ invariantPiSubgroups ⊤ (K ⊔ T) (piOf 2) := by
      refine (mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mpr ⟨le_top, hZ2, ?_⟩
      intro x hx
      exact Res6.mem_normalizer_sup (hXO3 (hKTX hx))
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ hx)
    have heq := hmax.2 _ hZmem le_sup_right
    exact le_sup_left.trans heq.le
  have hYK : Y ≤ Subgroup.normalizer (K : Set G) :=
    hle3.trans (sup_le Subgroup.le_normalizer (hO3R.trans ((hRKT.trans (sup_le hKM hTM)).trans
      hMK)))
  have hKC := hset.mem_oTwoComponentsIn
  have hO3Y : O3 ≤ Y := Res6.inSubgroup_pPrimeCore_le 3 Y
  have hsol : Group.IsSolvable O3 := by
    have : Group.IsNilpotent O3 := hO32.isNilpotent
    infer_instance
  have hKn : (K.subgroupOf Y).Normal := by
    refine ⟨fun x hx y => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have := (Subgroup.mem_normalizer_iff.mp (hYK y.2) x).mp hx
    simpa using this
  have hres : inSubgroup perfectResidual Y = K :=
    Sec18.inSubgroup_perfectResidual_eq_of_isSubnormal hKY hO3Y
      (Subgroup.le_normalizer.trans
        (Res6.normalizer_le_normalizer_inSubgroup_pPrimeCore 3 Y)) hsol hKn.isSubnormal
      (Sec18.commutator_eq_of_mem_oTwoComponentsIn hKC) (le_antisymm (sup_le hKY hO3Y) hle3)
  have hXK : X ≤ Subgroup.normalizer (K : Set G) := by
    have : (perfectResidual ↥Y).Characteristic :=
      (CFSG.perfect_residual_characterization (G := ↥Y)).2.1
    have h1 := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (perfectResidual ↥Y)
    rw [show (perfectResidual ↥Y).map Y.subtype = K from hres] at h1
    exact hXY.trans h1
  exact hXM (Res6.eq_of_le_normalizer hset.charTwoType hset.mem_scriptM.1 hX.1 hKC hMK hXK)

theorem step204FinalCover_of (h : Step204YAlphaNe) : Step204FinalCover := by
  intro G _ _ A M L N c T i j P hset X hX hXM hm k hk hcov
  apply h G A M L N c T i j P hset X hX hXM hm
  set K := kTwenty M c with hKdef
  set Y := yTwenty X c with hYdef
  set R := CFSG.Open.pCoreOf 2 (K ⊔ T) with hRdef
  set O' := oThreePrimeYR M X T c with hO'
  set J := K ⊔ O' with hJ
  have hMK : M ≤ Subgroup.normalizer (K : Set G) := le_normalizer_normalClosureIn M c
  have hNk : Subgroup.normalizer (Sec18.fourChar R k : Set G) ≤ M := by
    rcases hk with rfl | rfl
    · exact hset.normalizer_left
    · exact hset.normalizer_right
  have hYO' : Y ≤ Subgroup.normalizer (O' : Set G) :=
    le_sup_left.trans (Res6.le_normalizer_inSubgroup_pPrimeCore 3 (Y ⊔ R))
  have hYJ : Y ≤ Subgroup.normalizer (J : Set G) := by
    refine hcov.trans (sup_le ?_ ?_)
    · intro y hy
      exact Res6.mem_normalizer_sup (hMK (hNk hy.2)) (hYO' hy.1)
    · exact (le_sup_right : O' ≤ J).trans Subgroup.le_normalizer
  have hcJ : c ∈ J := Subgroup.mem_sup_left (self_mem_normalClosureIn M c)
  refine (Res6.yTwenty_le_normalClosureIn_self hset X).trans ?_
  rw [normalClosureIn, Subgroup.closure_le]
  rintro _ ⟨y, hy, rfl⟩
  exact (Subgroup.mem_normalizer_iff.mp (hYJ hy) c).mp hcJ

theorem step204FinalCover_of_kO3 (h : Step204YKO3) : Step204FinalCover :=
  step204FinalCover_of (step204YAlphaNe_of h)

end CFSG.RankThree.PartTwo.Sec20
