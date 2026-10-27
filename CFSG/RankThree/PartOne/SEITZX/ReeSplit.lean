module

public import CFSG.RankThree.PartOne.CTP.SeitzFineG2
public import CFSG.RankThree.Chevalley.SteinbergCFLargeReeSplitSylow
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.AmbientGroup
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Classification
public import CFSG.LieType.Ree.LargeReeModelSchreier

public section

namespace CFSG.RankThree.PartOne.SEITZX

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag TauCeti CFSG.LocalAnalysis.ComponentInitial
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.RankThree.PartOne.CTP
  CFSG.RankThree.Chevalley
open CFSG.RankThree.PartOne.Census3 (IsoLie)

section Generic

variable {G : Type*} [Group G] [Finite G]

theorem not_dvd_card_of_isPGroup_two {S : Subgroup G} (hS : IsPGroup 2 S) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) : ¬ p ∣ Nat.card S := by
  obtain ⟨n, hn⟩ := hS.exists_card_eq
  rw [hn]
  intro h
  have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)
  omega

theorem le_iSup_centralizer_of_isPGroup_two {p : ℕ} [Fact p.Prime] (hp3 : 3 < p)
    (A S C : Subgroup G) (hAp : ∀ x : A, x ^ p = 1) (hA : Nat.card A = p ^ 2)
    (hS : IsPGroup 2 S) (hSC : S ≤ C) (hAN : A ≤ Subgroup.normalizer (S : Set G)) :
    S ≤ ⨆ x ∈ A, ⨆ (_ : x ≠ 1), C ⊓ Subgroup.centralizer ({x} : Set G) := by
  have h := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane p
    Fact.out A S hAp hA (not_dvd_card_of_isPGroup_two hS Fact.out hp3) hAN
  refine h.le.trans (iSup_le fun x => iSup_le fun hx => fun g hg => ?_)
  obtain ⟨hgS, hgx⟩ := Subgroup.mem_inf.1 hg
  exact Subgroup.mem_iSup_of_mem (x : G) (Subgroup.mem_iSup_of_mem x.2
    (Subgroup.mem_iSup_of_mem (fun h => hx (Subtype.ext h))
      (Subgroup.mem_inf.2 ⟨hSC hgS, hgx⟩)))

end Generic

section Ree

variable {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K F4.prime]

theorem reeGamma_le_iSup_centralizers (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} [Fact p.Prime]
    (hp3 : 3 < p) (hpq : p ∣ 2 ^ (2 * a + 1) - 1) (A : Subgroup (ModGL F4.tag K))
    (hAΓ : A ≤ F4.reeGamma K a) (hAp : ∀ x : A, x ^ p = 1) (hA : Nat.card A = p ^ 2) :
    F4.reeGamma K a ≤ ⨆ x ∈ A, ⨆ (_ : x ≠ 1),
      F4.reeGamma K a ⊓ Subgroup.centralizer ({x} : Set (ModGL F4.tag K)) := by
  have : Finite (ModGL F4.tag K) := finite_modGL
  have hApG : IsPGroup p A := IsPGroup.of_card (n := 2) hA
  obtain ⟨y, hyΓ, hyA⟩ :=
    (large_Ree_split_torus_contains_Sylow_prime_subgroups a K hK Fact.out hp3 hpq).2.2 A hAΓ hApG
  set A' : Subgroup (ModGL F4.tag K) := A.map (MulAut.conj y).toMonoidHom with hA'
  have hA'p : ∀ x : A', x ^ p = 1 := by
    rintro ⟨_, x, hx, rfl⟩
    refine Subtype.ext ?_
    change ((MulAut.conj y) x) ^ p = 1
    rw [← map_pow]
    have : x ^ p = 1 := congrArg Subtype.val (hAp ⟨x, hx⟩)
    rw [this, map_one]
  have hA'card : Nat.card A' = p ^ 2 := by
    rw [hA', Subgroup.card_map_of_injective (MulAut.conj y).injective]
    exact hA
  have hblock : ∀ j : Fin F4.fixedOrbitCount, F4.reeLocalBlock K a j ≤ ⨆ x ∈ A', ⨆ (_ : x ≠ 1),
      F4.reeGamma K a ⊓ Subgroup.centralizer ({x} : Set (ModGL F4.tag K)) := fun j =>
    sup_le
      (le_iSup_centralizer_of_isPGroup_two hp3 A' _ _ hA'p hA'card
        (isPGroup_reeFixedOrbitUnipotent j) inf_le_right
        (hyA.trans (reeFixedTorus_le_normalizer_reeFixedOrbitUnipotent j)))
      (le_iSup_centralizer_of_isPGroup_two hp3 A' _ _ hA'p hA'card
        (isPGroup_reeFixedOrbitNegUnipotent j) inf_le_right
        (hyA.trans (reeFixedTorus_le_normalizer_reeFixedOrbitNegUnipotent j)))
  have hkey : F4.reeGamma K a ≤ ⨆ x ∈ A', ⨆ (_ : x ≠ 1),
      F4.reeGamma K a ⊓ Subgroup.centralizer ({x} : Set (ModGL F4.tag K)) := by
    exact (large_Ree_simple_pair_generation a K hK).le.trans (sup_le (hblock _) (hblock _))
  exact le_iSup_inf_centralizer_of_map_conj hyΓ hkey

end Ree

section Models

theorem exists_reeGamma_model {m : ℕ} {K : Type} [Group K] (hiso : IsoLie K (.reeF4 m)) :
    ∃ (X : Type) (_ : Field X) (_ : Finite X) (_ : CharP X F4.prime),
      1 ≤ m ∧ Nat.card X = 2 ^ (2 * m + 1) ∧ Nonempty (K ≃* F4.reeGamma X m) := by
  obtain ⟨hv, ⟨e0⟩⟩ := hiso
  let e : K ≃* ValidLieTypeIndex.Group ⟨.reeF4 m, hv⟩ := e0
  have hfin : ∀ d : ReeF4LieIndex, Finite d.1.fixedField := fun _ => inferInstance
  have hchar : ∀ d : ReeF4LieIndex, CharP d.1.fixedField 2 := fun _ => inferInstance
  have := hfin (ReeF4LieIndex.of m hv)
  have := hchar (ReeF4LieIndex.of m hv)
  have hm1 : 1 ≤ m :=
    (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  have hhalf : (ReeF4LieIndex.of m hv).toSuzukiReeIndex.halfExponent = m :=
    SuzukiReeIndex.halfExponent_reeF4 m hv
  obtain ⟨e₁⟩ := CFSG.TauCetiBridge.ReeF4.nonempty_candidate_equiv_reeF4 (ReeF4LieIndex.of m hv)
  rw [hhalf] at e₁
  have hK := CFSG.TauCetiBridge.ReeF4.card_fixedField_reeF4 (ReeF4LieIndex.of m hv)
  rw [hhalf] at hK
  have hmodel : ReeTitsModel K .twistedF4 2 (2 * m + 1) :=
    ⟨⟨Nat.prime_two, by omega, ⟨rfl, rfl, ⟨m, rfl⟩, by omega⟩⟩, m, rfl,
      ⟨(ReeF4LieIndex.of m hv).1.fixedField, inferInstance, inferInstance, hK,
        ⟨(e.trans e₁).trans (CFSG.TauCetiBridge.ReeF4.nativeModelEquiv m).symm⟩⟩⟩
  obtain ⟨hFin, -, -, -, -, hmain⟩ := ReeTag.large_Ree_model_Schreier K 2 (2 * m + 1) hmodel
  obtain ⟨-, a, hfa, X, _, _, hXcard, ⟨e2⟩⟩ := hmodel
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar' : CharP X F4.prime := by
    have : Fintype X := Fintype.ofFinite X
    exact charP_of_card_eq_prime_pow (p := 2) (f := 2 * m + 1) (by
      rw [← Nat.card_eq_fintype_card, hXcard])
  have ham : a = m := by omega
  subst ham
  obtain ⟨E⟩ := hmain a X hfa hXcard ⟨e2⟩
  exact ⟨X, inferInstance, inferInstance, hchar', hm1, hXcard, ⟨E⟩⟩

theorem extSeitzAtInnerFor_reeF4_split (m : ℕ) :
    ExtSeitzAtInnerFor (.reeF4 m) fun p => p ∣ 2 ^ (2 * m + 1) - 1 := by
  intro K _ _ _ hnab hiso p hp hp5 hpd hpq E hE hcard hinner
  left
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨X, _, _, _, hm1, hX, ⟨e⟩⟩ := exists_reeGamma_model hiso
  have : IsSimpleGroup (F4.reeGamma X m) := MulEquiv.isSimpleGroup e.symm
  refine closure_fixUnion_eq_top_of_inner_equiv hnab e (p := p) ?_ E hcard hinner
  intro E₁ hE₁ hcard₁
  have := hE₁
  apply closure_centralizers_of_iSup_eq (F4.reeGamma X m) E₁
  have : IsElementaryAbelian p (E₁.map (F4.reeGamma X m).subtype) := IsElementaryAbelian.map _
  refine le_antisymm (iSup₂_le fun x _ => iSup_le fun _ => inf_le_left) ?_
  exact reeGamma_le_iSup_centralizers hX (by omega) hpq _ (Subgroup.map_subtype_le _)
    (fun x => Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := p) (x : ModGL F4.tag X) x.2))
    (by rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hcard₁])

end Models

end CFSG.RankThree.PartOne.SEITZX
