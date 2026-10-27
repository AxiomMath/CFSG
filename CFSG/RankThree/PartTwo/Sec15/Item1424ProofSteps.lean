module

public import CFSG.RankThree.PartTwo.Sec15.Item15Inputs
public import CFSG.RankThree.PartTwo.Sec14.Std
public import CFSG.RankThree.PartTwo.Sec6.Item612Basic

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (localRank)
open scoped commutatorElement

structure Ctx1424 (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y : Subgroup G)
    (n : ℕ) : Prop where
  std : Sec14Std G A c L
  mem_scriptY3 : Y ∈ scriptY3 A (lB A)
  le_normalizer : A ≤ Subgroup.normalizer (Y : Set G)
  four_le : 4 ≤ n
  iso : letI := kerAO2_normal le_normalizer
    ∃ T : Type, ∃ _ : Group T, Sec4.IsoLThreePi T 2 n ∧
      Nonempty (↥(A ⊔ Y) ⧸ kerAO2 A Y ≃* Multiplicative (ZMod 3) × T)
  eq_sup : Y = (Y ⊓ L) ⊔ CFSG.Open.pCoreOf 2 Y
  fitting_eq : generalizedFitting ↥Y = CFSG.pCore 2 ↥Y
  simple : IsSimpleGroup ↥L
  omegaA_eq : omegaA A = {Subgroup.zpowers c}

variable {G : Type} [Group G] [Finite G]

@[expose] def IsE1424 (A L Y : Subgroup G) (p : ℕ) (E : Subgroup G) : Prop :=
  p.Prime ∧ 3 < p ∧ CFSG.Assembly.IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧ E = ⁅E, A⁆ ∧
    E ∈ scriptQ A (lB A) ∧ E ≤ Y ⊓ L ∧ IsHyperplane A (A ⊓ Subgroup.centralizer (E : Set G))

@[expose] def Step1424E : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y : Subgroup G) (n : ℕ),
    Ctx1424 G A c L Y n → ∃ (p : ℕ) (E : Subgroup G), IsE1424 A L Y p E

@[expose] def Step1424Core : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y : Subgroup G) (n : ℕ),
    Ctx1424 G A c L Y n → CFSG.Open.pCoreOf 2 Y ⊓ L = ⊥

@[expose] def Step1424NotHJ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y : Subgroup G) (n : ℕ),
    Ctx1424 G A c L Y n →
      ¬ Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)

omit [Finite G] in
theorem le_normalClosureSub {X E : Subgroup G} (hEX : E ≤ X) : E ≤ normalClosureSub X E := by
  intro e he
  exact ⟨⟨e, hEX he⟩, Subgroup.subset_normalClosure (Subgroup.mem_subgroupOf.mpr he), rfl⟩

omit [Finite G] in
theorem normalClosureSub_le (X E : Subgroup G) : normalClosureSub X E ≤ X :=
  Subgroup.map_subtype_le _

omit [Finite G] in
theorem le_normalizer_normalClosureSub (X E : Subgroup G) :
    X ≤ Subgroup.normalizer (normalClosureSub X E : Set G) := by
  have h : (normalClosureSub X E).subgroupOf X =
      Subgroup.normalClosure ((E.subgroupOf X : Subgroup X) : Set X) := by
    rw [normalClosureSub, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective X.subtype_injective]
  have hn : ((normalClosureSub X E).subgroupOf X).Normal := h ▸ Subgroup.normalClosure_normal
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer (normalClosureSub_le X E)).mp hn

omit [Finite G] in
theorem normalizer_inf_le_normalizer_normalClosureSub (X E : Subgroup G) :
    Subgroup.normalizer (X : Set G) ⊓ Subgroup.normalizer (E : Set G) ≤
      Subgroup.normalizer (normalClosureSub X E : Set G) := by
  refine Sec6.le_normalizer_of_forall_conj_mem fun g hg n hn => ?_
  obtain ⟨hgX, hgE⟩ := Subgroup.mem_inf.mp hg
  have key : normalClosureSub X E ≤ (normalClosureSub X E).comap (MulAut.conj g).toMonoidHom := by
    rw [normalClosureSub, Subgroup.map_le_iff_le_comap, Subgroup.normalClosure,
      Subgroup.closure_le]
    intro y hy
    obtain ⟨s, hs, hsy⟩ := Group.mem_conjugatesOfSet_iff.mp hy
    obtain ⟨z, rfl⟩ := isConj_iff.mp hsy
    have hsE : (s : G) ∈ E := Subgroup.mem_subgroupOf.mp hs
    have hzX : g * (z : G) * g⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hgX _).mp z.2
    have hsE' : g * (s : G) * g⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hgE _).mp hsE
    have hsX : g * (s : G) * g⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hgX _).mp s.2
    refine ⟨⟨g * (z : G) * g⁻¹, hzX⟩ * ⟨g * (s : G) * g⁻¹, hsX⟩ * ⟨g * (z : G) * g⁻¹, hzX⟩⁻¹,
      ?_, ?_⟩
    · exact Subgroup.normalClosure_normal.conj_mem _
        (Subgroup.subset_normalClosure (Subgroup.mem_subgroupOf.mpr hsE')) _
    · simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply]
      group
  exact key hn

omit [Finite G] in
theorem commutator_le_normalClosureSub {X E U : Subgroup G} (hEX : E ≤ X) (hUX : U ≤ X) :
    ⁅U, E⁆ ≤ normalClosureSub X E := by
  rw [Subgroup.commutator_le]
  intro u hu e he
  have heN := le_normalClosureSub hEX he
  have h1 : u * e * u⁻¹ ∈ normalClosureSub X E :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_normalClosureSub X E (hUX hu)) e).mp heN
  rw [commutatorElement_def]
  exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ heN)

end CFSG.RankThree.PartTwo.Sec15
