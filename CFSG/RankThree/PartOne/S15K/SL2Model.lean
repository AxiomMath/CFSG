module

public import CFSG.RankThree.PartOne.S15K.SL2Split
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Foundations.Basic
import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
import CFSG.RankThree.Classical.SteinbergBJUnitaryTwoBlock

public section

namespace CFSG.RankThree.PartOne.S15K

open CFSG.Assembly.LowTwoRank Matrix
open scoped commutatorElement

theorem center_sl2_eq_bot {F : Type*} [Field F] [CharP F 2] :
    Subgroup.center (SpecialLinearGroup (Fin 2) F) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Fintype.card_fin] at hr
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hr1 : r = 1 := by
    have h0 : (r - 1) ^ 2 = 0 := by linear_combination hr - (r - 1) * h2
    exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h0)
  subst hr1
  ext1
  rw [Matrix.SpecialLinearGroup.coe_one, ← hrA, map_one]

theorem nonempty_sl2_mulEquiv_statedProj {F : Type} [Field F] [CharP F 2] :
    Nonempty (SpecialLinearGroup (Fin 2) F ≃* StatedProj (StatedSL 2 F)) :=
  ⟨((QuotientGroup.quotientMulEquivOfEq center_sl2_eq_bot).trans
    QuotientGroup.quotientBot).symm.trans (projectiveSpecialLinearGroupEquivStatedProj 2 F)⟩

theorem exists_mulEquiv_sl2_of_model {K : Type} [Group K] {f : ℕ}
    (hK : StatedClassicalModel K .PSL 2 2 f) :
    2 ≤ f ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 2 ^ f ∧
      Nonempty (K ≃* SpecialLinearGroup (Fin 2) F) := by
  obtain ⟨⟨-, hf1, -, hne4, -⟩, F, hF, hFin, hcard, ⟨e⟩⟩ := hK
  have hf2 : 2 ≤ f := by
    by_contra h
    have : f = 1 := by omega
    subst this
    exact hne4 (by simp)
  have : CharP F 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two hf1 hcard
  obtain ⟨e'⟩ := nonempty_sl2_mulEquiv_statedProj (F := F)
  exact ⟨hf2, F, hF, hFin, this, hcard, ⟨e.trans e'.symm⟩⟩

theorem isQuasisimple_of_model {K : Type} [Group K] {f : ℕ} (hK : StatedClassicalModel K .PSL 2 2 f) :
    CFSG.IsQuasisimple K := by
  obtain ⟨hf2, F, hF, hFin, hchar, hcard, ⟨e⟩⟩ := exists_mulEquiv_sl2_of_model hK
  have h4 : ∃ s : Finset F, s.card = 4 := by
    have := Fintype.ofFinite F
    have hq : 4 ≤ 2 ^ f := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
    have hle : 4 ≤ (Finset.univ : Finset F).card := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hcard]
      exact hq
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq hle
    exact ⟨s, hs⟩
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm
    (CFSG.RankThree.Classical.isQuasisimple_SL2 h4)

theorem center_eq_bot_of_model {K : Type} [Group K] {f : ℕ} (hK : StatedClassicalModel K .PSL 2 2 f) :
    Subgroup.center K = ⊥ := by
  obtain ⟨-, F, hF, hFin, hchar, hcard, ⟨e⟩⟩ := exists_mulEquiv_sl2_of_model hK
  have h := Subgroup.map_center_eq e
  rw [center_sl2_eq_bot] at h
  rwa [Subgroup.map_eq_bot_iff_of_injective _ e.injective] at h

theorem exists_two_subgroup_of_mulEquiv {K K' : Type*} [Group K] [Group K'] (e : K ≃* K') {a : K}
    (h : ∃ S : Subgroup K', S ≠ ⊥ ∧ IsPGroup 2 S ∧ e a ∈ Subgroup.normalizer (S : Set K') ∧
      ⁅S, Subgroup.zpowers (e a)⁆ = S) :
    ∃ S : Subgroup K, S ≠ ⊥ ∧ IsPGroup 2 S ∧ a ∈ Subgroup.normalizer (S : Set K) ∧
      ⁅S, Subgroup.zpowers a⁆ = S := by
  obtain ⟨S', hS1, hS2, hSn, hSc⟩ := h
  have hmem : ∀ x : K, x ∈ S'.map e.symm.toMonoidHom ↔ e x ∈ S' := fun x => by
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm]
  refine ⟨S'.map e.symm.toMonoidHom, ?_, hS2.map _, ?_, ?_⟩
  · intro h
    apply hS1
    rw [Subgroup.map_eq_bot_iff_of_injective _ e.symm.injective] at h
    exact h
  · rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [hmem, hmem, map_mul, map_mul, map_inv]
    exact Subgroup.mem_normalizer_iff.1 hSn (e h)
  · have hmap : (S'.map e.symm.toMonoidHom).map e.toMonoidHom = S' := by
      rw [Subgroup.map_map]
      have : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id K' := by
        ext x; simp
      rw [this, Subgroup.map_id]
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [Subgroup.map_commutator, MonoidHom.map_zpowers, hmap]
    exact hSc

theorem exists_two_subgroup_of_model {K : Type} [Group K] {f : ℕ}
    (hK : StatedClassicalModel K .PSL 2 2 f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpf : p ∣ 2 ^ f - 1)
    {a : K} (ha1 : a ≠ 1) (hap : a ^ p = 1) :
    ∃ S : Subgroup K, S ≠ ⊥ ∧ IsPGroup 2 S ∧ a ∈ Subgroup.normalizer (S : Set K) ∧
      ⁅S, Subgroup.zpowers a⁆ = S := by
  obtain ⟨-, F, hF, hFin, hchar, hcard, ⟨e⟩⟩ := exists_mulEquiv_sl2_of_model hK
  have hpq : p ∣ Nat.card F - 1 := by rwa [hcard]
  have hg1 : e a ≠ 1 := fun h => ha1 (e.injective (h.trans (map_one e).symm))
  have hgp : e a ^ p = 1 := by rw [← map_pow, hap, map_one]
  exact exists_two_subgroup_of_mulEquiv e (exists_two_subgroup_of_pow_eq_one hp hp2 hpq hg1 hgp)

end CFSG.RankThree.PartOne.S15K
