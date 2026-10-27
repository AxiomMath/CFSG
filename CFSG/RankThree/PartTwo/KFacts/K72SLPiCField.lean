module

public import CFSG.RankThree.PartTwo.KFacts.K72SLPiIdent
import CFSG.RankThree.PartTwo.KFacts.K72SLPiAut
import CFSG.RankThree.PartTwo.KFacts.K72L3Linear
import CFSG.RankThree.PartTwo.KFacts.AutKindsUnique

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.ComponentClassification.CatalogueBHigherLinearField
open CFSG.GH74.GLS.IVK (fixedField fixedField_apply fixedField_card_pow)
open Matrix

section Model

theorem exists_slPi_of_isSLThreePiAt_two_pow {X : Type} [Group X] {m : ℕ} (hm : 1 ≤ m)
    (hX : IsSLThreePiAt X (2 ^ m)) :
    ∃ (π : Bool) (K : Type) (_ : Field K), PiField π 2 m K ∧ ModThree π (2 ^ m) ∧
      Nonempty (X ≃* slPi π 3 (2 ^ m) K) := by
  obtain ⟨K, _, _, ⟨hK, hq, ⟨e⟩⟩ | ⟨hK, hq, ⟨e⟩⟩⟩ := hX
  · exact ⟨true, K, inferInstance, ⟨Nat.prime_two, hm, hK⟩, hq, ⟨e⟩⟩
  · exact ⟨false, K, inferInstance, ⟨Nat.prime_two, hm, hK⟩, hq, ⟨e⟩⟩

variable {π : Bool} {p f : ℕ} {K : Type} [Field K]

theorem exists_pow_three_eq_one_not_mem_center_slPi (hK : PiField π p f K)
    (hq : ModThree π (p ^ f)) :
    ∃ x : slPi π 3 (p ^ f) K, x ^ 3 = 1 ∧ x ∉ Subgroup.center (slPi π 3 (p ^ f) K) := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  obtain ⟨τ, hτ3, hτ1⟩ := exists_tau hK hq
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    norm_num at hτ3
  set ζ : Kˣ := Units.mk0 τ hτ0 with hζdef
  have hζ3 : ζ ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hτ3,
    Units.val_one])
  have hζ1 : ζ ≠ 1 := fun h => hτ1 (by rw [← Units.val_mk0 hτ0, ← hζdef, h, Units.val_one])
  have hζT := mem_rootsOfUnity_qSubPi_of_pow_three hq hζ3
  refine ⟨⟨torusHom (ζ, ζ ^ 2), torusHom_mem_slPi hK hζT (pow_mem hζT 2)⟩, ?_, ?_⟩
  · apply Subtype.ext
    change torusHom (ζ, ζ ^ 2) ^ 3 = 1
    rw [← map_pow, Prod.pow_mk, hζ3, ← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul, hζ3,
      one_pow]
    exact map_one torusHom
  · intro hc
    have h : (cycThree : GL (Fin 3) K) * torusHom (ζ, ζ ^ 2) = torusHom (ζ, ζ ^ 2) * cycThree :=
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨cycThree, cycThree_mem_slPi hπ⟩)
    have h' := congrArg Units.val h
    rw [Units.val_mul, Units.val_mul, coe_torusHom] at h'
    obtain ⟨h1, -⟩ := eq_of_diagonal_commute_cycThree h'
    have h2 : ζ * 1 = ζ * ζ := by
      rw [mul_one, ← sq]
      exact Units.ext h1
    exact hζ1 (mul_left_cancel h2).symm

theorem isQuasisimple_of_isSLThreePiAt_two_pow {X : Type} [Group X] {m : ℕ} (hm : 2 ≤ m)
    (hX : IsSLThreePiAt X (2 ^ m)) : IsQuasisimple X := by
  obtain ⟨K, _, _, ⟨-, -, ⟨e⟩⟩ | ⟨hK, -, ⟨e⟩⟩⟩ := hX
  · exact CFSG.LieType.Universal.Unitary.isQuasisimple_of_mulEquiv
      (e.trans (slPiTrueEquiv (2 ^ m) K)).symm
      (CFSG.LieType.Universal.SpecialLinear.isQuasisimple 2 K le_rfl)
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h4 : 4 ≤ 2 ^ m :=
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    have hnq : ((3 : ℕ), 2 ^ m) ≠ (3, 2) := fun h => by
      have h2 := congrArg Prod.snd h
      simp only at h2
      omega
    exact CFSG.LieType.Universal.Unitary.isQuasisimple_of_mulEquiv e.symm
      (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hK le_rfl hnq).1

theorem card_center_of_isSLThreePiAt_two_pow {X : Type} [Group X] {m : ℕ} (hm : 1 ≤ m)
    (hX : IsSLThreePiAt X (2 ^ m)) : Nat.card (Subgroup.center X) = 3 := by
  obtain ⟨π, K, _, hK, hq, ⟨e⟩⟩ := exists_slPi_of_isSLThreePiAt_two_pow hm hX
  rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
  exact card_center_slPi hK hq

theorem exists_pow_three_eq_one_not_mem_center_of_isSLThreePiAt_two_pow {X : Type} [Group X]
    {m : ℕ} (hm : 1 ≤ m) (hX : IsSLThreePiAt X (2 ^ m)) :
    ∃ x : X, x ^ 3 = 1 ∧ x ∉ Subgroup.center X := by
  obtain ⟨π, K, _, hK, hq, ⟨e⟩⟩ := exists_slPi_of_isSLThreePiAt_two_pow hm hX
  obtain ⟨s, hs3, hs⟩ := exists_pow_three_eq_one_not_mem_center_slPi hK hq
  refine ⟨e.symm s, by rw [← map_pow, hs3, map_one], fun h => hs ?_⟩
  simpa using mem_center_of_mulEquiv e h

end Model

section Linear

variable {K : Type} [Field K]

theorem mem_range_sl_map_subtype_iff (σ : K ≃+* K) (A : SpecialLinearGroup (Fin 3) K) :
    A ∈ (SpecialLinearGroup.map (fixedField σ).subtype).range ↔
      slFieldAut (Fin 3) K σ A = A := by
  constructor
  · rintro ⟨A₀, rfl⟩
    ext i j
    exact fixedField_apply σ _
  · intro hA
    exact exists_sl_map_subtype_eq hA

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_barCentralizer_mulEquiv_sl3 [Finite K] {a : G} (ha3 : a ^ 3 = 1)
    (ha : InducesKindSL 3 K L a .field) :
    ∃ σ : K ≃+* K, orderOf σ = 3 ∧
      Nonempty (Sec8.barCentralizer (Subgroup.zpowers a) L ≃*
        SpecialLinearGroup (Fin 3) (fixedField σ)) := by
  obtain ⟨e, hN, hk⟩ := ha
  set β := inducedAutHom L e ⟨a, hN⟩ with hβ
  have hβ3 : β ^ 3 = 1 := inducedAutHom_pow_eq_one L e hN ha3
  have hα3 : descendAut 3 K β ^ 3 = 1 := by rw [← map_pow, hβ3, map_one]
  have hD : descendAut 3 K β ∉ linearAutGroup 3 K :=
    (stdPinnedPSL_separated (n := 3) (K := K) le_rfl).not_mem_inndiag_of_hasKind hk
      (by decide) (by decide)
  obtain ⟨σ, hσ3, H, hαH⟩ := linear_order_three_field_descent le_rfl _ hα3 hD
  have hlift : β = slConjugation 3 K H * slFieldAut (Fin 3) K σ * (slConjugation 3 K H)⁻¹ :=
    eq_of_descendAut_eq (by rw [hαH, map_mul, map_mul, map_inv]; rfl)
  refine ⟨σ, hσ3, nonempty_barCentralizer_mulEquiv hN e
    ((slConjugation 3 K H : SpecialLinearGroup (Fin 3) K ≃*
      SpecialLinearGroup (Fin 3) K).toMonoidHom.comp
        (SpecialLinearGroup.map (fixedField σ).subtype))
    ((slConjugation 3 K H).injective.comp (sl_map_subtype_injective σ)) fun z => ?_⟩
  rw [← hβ, hlift]
  exact mem_range_conj_comp_iff _ _ _ (mem_range_sl_map_subtype_iff σ) z

theorem isSLThreePiAt_barCentralizer_of_field {n : ℕ} (hn : 1 ≤ n)
    (hL : Sec4.IsSLThreePiAt (L ⧸ aschbacherSolvableCore 3 L) (2 ^ (3 * n))) {a : G}
    (ha3 : a ^ 3 = 1) (ha : InducesStdKind L a .field ∨ InducesStdKind L a .graphField) :
    Sec4.IsSLThreePiAt (Sec8.barCentralizer (Subgroup.zpowers a) L) (2 ^ n) := by
  have hn3 : 3 ≤ 3 * n := by omega
  have hcube : (2 ^ n) ^ 3 = 2 ^ (3 * n) := by rw [← pow_mul, mul_comm]
  rcases hL with ⟨K₀, _, _, ⟨hK₀, hq₀, ⟨e₀⟩⟩ | ⟨hK₀, hq₀, ⟨e₀⟩⟩⟩
  ·
    have hIso : ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ (3 * n) ∧
        Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Assembly.LowTwoRank.StatedSL 3 K) :=
      ⟨K₀, inferInstance, inferInstance, hK₀, ⟨e₀⟩⟩
    have haF : InducesStdKind L a .field :=
      ha.resolve_right (not_inducesStdKind_graphField_of_isoSLThree hn3 hq₀ hIso ha3)
    obtain ⟨K, _, _, hK, hk⟩ := inducesKindSL_of_inducesStdKind hn3 hq₀ hIso haF
    obtain ⟨σ, hσ, ⟨eC⟩⟩ := exists_barCentralizer_mulEquiv_sl3 ha3 hk
    have hcard : Nat.card (fixedField σ) = 2 ^ n := by
      have h := fixedField_card_pow σ
      rw [hσ, hK, ← hcube] at h
      exact Nat.pow_left_injective (by norm_num) h
    have hmod : 2 ^ n % 3 = 1 := modThree_of_cube (π := true) (by rw [hcube]; exact hq₀)
    exact ⟨fixedField σ, inferInstance, inferInstance,
      Or.inl ⟨hcard, hmod, ⟨eC.trans (slPiTrueEquiv (2 ^ n) (fixedField σ)).symm⟩⟩⟩
  ·
    have hIso : Sec8.IsoSUThree (L ⧸ aschbacherSolvableCore 3 L) (2 ^ (3 * n)) :=
      ⟨K₀, inferInstance, inferInstance, hK₀, ⟨e₀⟩⟩
    have hm3 : 3 ∣ 2 ^ (3 * n) + 1 := by
      generalize 2 ^ (3 * n) = t at hq₀ ⊢
      omega
    have haF : InducesStdKind L a .field :=
      ha.resolve_right (not_inducesStdKind_graphField_of_isoSUThree hn3 hm3 hIso)
    have hmod : 2 ^ n % 3 = 2 := modThree_of_cube (π := false) (by rw [hcube]; exact hq₀)
    have hodd : Odd n := by
      by_contra h
      obtain ⟨k, rfl⟩ := Nat.not_odd_iff_even.mp h
      have h1 : 2 ^ (k + k) % 3 = 1 := by
        rw [← two_mul, pow_mul, Nat.pow_mod]
        norm_num
      omega
    obtain ⟨K, _, _, hK, ⟨eC⟩⟩ := isoSUThree_barCentralizer_of_inducesStdKind hodd hIso ha3 haF
    exact ⟨K, inferInstance, inferInstance, Or.inr ⟨hK, hmod, ⟨eC⟩⟩⟩

end Linear

theorem barCentralizer_facts_of_field {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ}
    (hn : 2 ≤ n) (hL : Sec4.IsSLThreePiAt (L ⧸ aschbacherSolvableCore 3 L) (2 ^ (3 * n)))
    {a : G} (haN : a ∈ Subgroup.normalizer (L : Set G)) (ha3 : a ^ 3 = 1)
    (ha : InducesStdKind L a .field ∨ InducesStdKind L a .graphField) :
    IsQuasisimple (Sec8.barCentralizer (Subgroup.zpowers a) L) ∧
      Nat.card (Subgroup.center (Sec8.barCentralizer (Subgroup.zpowers a) L)) = 3 ∧
      ∃ z ∈ Sec8.barCentralizer (Subgroup.zpowers a) L, z ^ 3 = 1 ∧
        z ∉ Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) := by
  have _ := haN
  have hC := isSLThreePiAt_barCentralizer_of_field (by omega) hL ha3 ha
  obtain ⟨x, hx3, hx⟩ :=
    exists_pow_three_eq_one_not_mem_center_of_isSLThreePiAt_two_pow (by omega) hC
  refine ⟨isQuasisimple_of_isSLThreePiAt_two_pow hn hC,
    card_center_of_isSLThreePiAt_two_pow (by omega) hC, x, x.2, ?_, fun hz => hx ?_⟩
  · rw [← SubgroupClass.coe_pow, hx3]
    rfl
  · rw [Subgroup.mem_center_iff] at hz ⊢
    intro g
    exact Subtype.ext (hz g)

end CFSG.RankThree.PartTwo.KFacts
