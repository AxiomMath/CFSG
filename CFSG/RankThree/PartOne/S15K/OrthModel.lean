module

public import CFSG.RankThree.PartOne.S12.Sec1511Model
public import CFSG.RankThree.PartOne.S11d.LieCentralizerPOmega
public import CFSG.RankThree.PartOne.S11d.OutOrthogonal
import CFSG.Timmesfeld.Orders.Classical

public section

namespace CFSG.RankThree.PartOne.S15K

open CFSG CFSG.Assembly.LowTwoRank CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal
open CFSG.Assembly.RankThreeEven (projImage projOmegaMinus)
open CFSG.LieType.Universal.Spin (quadMinus coe_quadMinus nondegenerate_polarBilin_quadMinus_of_finite
  quadMinus_apply)

noncomputable def projOmegaMinusEquivOrth (K : Type) [Field K] (b c : K) :
    projOmegaMinus 3 K b c ≃* ProjOrthDerived (quadMinus 4 K b c) :=
  (statedProjEquivRefl (projImage_statedOmegaMinus_eq_projOmegaMinus 4 K b c)).symm.trans
    (statedProjOrthEquiv (coe_quadMinus 4 K b c))

theorem polar_nondegenerate_quadMinus {K : Type} [Field K] [Finite K] {b c : K}
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (QuadraticMap.polarBilin (quadMinus 4 K b c)).Nondegenerate :=
  nondegenerate_polarBilin_quadMinus_of_finite 4 K hbc

theorem exists_three_totSing_quadMinus (K : Type) [Field K] (b c : K) :
    ∃ U : Submodule K (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → K), Module.finrank K U = 3 ∧
      ∀ u ∈ U, quadMinus 4 K b c u = 0 := by
  classical
  let e : Fin 3 → (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → K) := fun i => Pi.single (.inl i) 1
  have hli : LinearIndependent K e := by
    have h1 : LinearIndependent K (fun j : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 =>
        (Pi.single j 1 : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → K)) :=
      Pi.linearIndependent_single_one _ _
    exact h1.comp (fun i : Fin 3 => (Sum.inl i : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2))
      (fun i j h => by simpa using h)
  refine ⟨Submodule.span K (Set.range e), ?_, ?_⟩
  · rw [finrank_span_eq_card hli, Fintype.card_fin]
  · let S0 : Submodule K (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → K) :=
      { carrier := {v | ∀ j : Fin (4 - 1) ⊕ Fin 2, v (.inr j) = 0}
        add_mem' := fun {a b} ha hb j => by simp [ha j, hb j]
        zero_mem' := fun j => rfl
        smul_mem' := fun r a ha j => by simp [ha j] }
    have hle : Submodule.span K (Set.range e) ≤ S0 := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩ j
      simp [e]
    intro u hu
    have hu0 := hle hu
    rw [quadMinus_apply]
    have h1 : ∀ i, u (.inr (.inl i)) = 0 := fun i => hu0 (.inl i)
    have h2 : u (.inr (.inr 0)) = 0 := hu0 (.inr 0)
    have h3 : u (.inr (.inr 1)) = 0 := hu0 (.inr 1)
    simp [h1, h2, h3]

theorem mk_injective_orth {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type*} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [Nontrivial V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) :
    Function.Injective (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hgs := Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff g).mp hg)
  exact Subtype.ext (eq_one_of_mem_scalars_of_mem_orthDerived hQ g.2 hgs)

theorem statedClassicalModel_of_projOmegaMinus {X : Type} [Group X] {f : ℕ} (hf : 1 ≤ f)
    {b c : GaloisField 2 f} (hbc : ∀ s : GaloisField 2 f, s ^ 2 + b * s + c ≠ 0)
    (e : X ≃* projOmegaMinus 3 (GaloisField 2 f) b c) : StatedClassicalModel X .POmegaMinus 4 2 f :=
  ⟨⟨Nat.prime_two, hf, by norm_num⟩, GaloisField 2 f, inferInstance, inferInstance,
    GaloisField.card 2 f (by omega), b, c, hbc,
    ⟨e.trans (statedProjEquivRefl (projImage_statedOmegaMinus_eq_projOmegaMinus 4 _ b c)).symm⟩⟩

theorem outPNice_of_projOmegaMinus {X : Type} [Group X] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) {b c : GaloisField 2 f} (hbc : ∀ s : GaloisField 2 f, s ^ 2 + b * s + c ≠ 0)
    (e : X ≃* projOmegaMinus 3 (GaloisField 2 f) b c) : OutStructure.OutPNice p X :=
  OutStructure.outPNice_POmegaMinus hp hp2 (by norm_num) (statedClassicalModel_of_projOmegaMinus hf hbc e)

theorem dvd_card_of_projOmegaMinus {X : Type} [Group X] {p f : ℕ} (hf : 1 ≤ f)
    {b c : GaloisField 2 f} (hbc : ∀ s : GaloisField 2 f, s ^ 2 + b * s + c ≠ 0)
    (e : X ≃* projOmegaMinus 3 (GaloisField 2 f) b c)
    (hd : p ∣ 2 ^ f - 1 ∨ p ∣ 2 ^ f + 1) : p ∣ Nat.card X := by
  have hC := statedClassicalModel_of_projOmegaMinus hf hbc e
  have hcard : Nat.card X = CFSG.Open.ordTwistedD 4 (2 ^ f) :=
    (CFSG.Timmesfeld.card_statedClassicalModel_two hC).2.2.2.2 rfl
  have hodd : Odd ((2 ^ f) ^ 4 + 1) := by
    have h2 : Even ((2 ^ f) ^ 4) := (Nat.even_pow.mpr ⟨Nat.even_pow.mpr ⟨even_two, by omega⟩, by norm_num⟩)
    exact h2.add_one
  have hgcd : Nat.gcd 4 ((2 ^ f) ^ 4 + 1) = 1 := by
    have : Nat.Coprime (2 ^ 2) ((2 ^ f) ^ 4 + 1) :=
      Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hodd)
    simpa using this
  have hp1 : p ∣ (2 ^ f) ^ (2 * 1) - 1 := by
    have h2f : (2 ^ f) ^ 2 - 1 = (2 ^ f - 1) * (2 ^ f + 1) := by
      have : 1 ≤ 2 ^ f := Nat.one_le_two_pow
      zify [this, (Nat.one_le_pow 2 (2 ^ f) (by positivity) : 1 ≤ (2 ^ f) ^ 2)]
      ring
    rw [mul_one, h2f]
    rcases hd with h | h
    · exact h.mul_right _
    · exact h.mul_left _
  rw [hcard, CFSG.Open.ordTwistedD, hgcd, Nat.div_one]
  refine Dvd.dvd.mul_left ?_ _
  exact hp1.trans (Finset.dvd_prod_of_mem (fun j => (2 ^ f) ^ (2 * j) - 1)
    (show 1 ∈ Finset.Icc 1 (4 - 1) by simp))

end CFSG.RankThree.PartOne.S15K
