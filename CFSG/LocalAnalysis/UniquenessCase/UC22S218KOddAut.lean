module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherAutomorphismData
import CFSG.LocalAnalysis.UniquenessCase.UC22S218KOddModel
import CFSG.LocalAnalysis.UniquenessCase.Lie.Shared
import CFSG.RankThree.PartOne.CTP.SpAut
import CFSG.GroupTheory.ElementaryAbelianTransport
import TauCeti.Algebra.Group.Coprime
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldAut)
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (spInner spInner_eq_conj
  exists_eq_spInner_mul_fieldAut)

theorem uc22s218k_fix_of_pow_eq_one {K : Type} [Field K] [Finite K] [CharP K 2]
    {E Q : Subgroup (StatedProj (StatedSp 2 K))} (hE : IsElemAbelian 3 E)
    (hfix : ∀ σ : K ≃+* K, ∀ x ∈ E, fieldAut 2 K σ x = x) (hQ : ¬ 3 ∣ Q.index)
    (hQC : Q ≤ centralizer (E : Set (StatedProj (StatedSp 2 K))))
    (hQE : ∀ x ∈ Q, x ^ 3 = 1 → x ∈ E) {α : MulAut (StatedProj (StatedSp 2 K))} {k : ℕ}
    (hα : α ^ 3 ^ k = 1) (hαE : ∀ x ∈ E, α x ∈ Q) : ∀ x ∈ E, α x = x := by
  obtain ⟨g, φ, rfl⟩ := exists_eq_spInner_mul_fieldAut
    (CFSG.RankThree.PartOne.CTP.mem_spSemilinearAutGroup_of_odd_pow (Odd.pow (by decide)) hα)
  have hact : ∀ x ∈ E, (spInner 2 K g * fieldAut 2 K φ) x = proj 2 K g * x * (proj 2 K g)⁻¹ := by
    intro x hx
    rw [MulAut.mul_apply, hfix φ x hx, spInner_eq_conj, MulAut.conj_apply]
  set h := proj 2 K g
  have hEE : ∀ x ∈ E, h * x * h⁻¹ ∈ E := fun x hx => by
    rw [← hact x hx]
    refine hQE _ (hαE x hx) ?_
    rw [← map_pow, hE.2 x hx, map_one]
  have hN : h ∈ normalizer (E : Set (StatedProj (StatedSp 2 K))) := by
    rw [mem_normalizer_iff_map_conj_eq]
    have hle : E.map (MulAut.conj h).toMonoidHom ≤ E := by
      rintro _ ⟨x, hx, rfl⟩
      exact hEE x hx
    exact eq_of_le_of_card_ge hle (by rw [card_map_of_injective (MulAut.conj h).injective])
  have hpow : ∀ j : ℕ, ∀ x ∈ E,
      ((spInner 2 K g * fieldAut 2 K φ) ^ j) x = h ^ j * x * (h ^ j)⁻¹ := by
    intro j
    induction j with
    | zero => intro x _; simp
    | succ j ih =>
      intro x hx
      rw [pow_succ, MulAut.mul_apply, hact x hx, ih _ (hEE x hx)]
      group
  have hC3 : h ^ 3 ^ k ∈ centralizer (E : Set (StatedProj (StatedSp 2 K))) := by
    rw [mem_centralizer_iff]
    intro x hx
    have h1 := hpow (3 ^ k) x hx
    rw [hα, MulAut.one_apply] at h1
    calc x * h ^ 3 ^ k = h ^ 3 ^ k * x * (h ^ 3 ^ k)⁻¹ * h ^ 3 ^ k := by rw [← h1]
      _ = h ^ 3 ^ k * x := by group
  set C := centralizer (E : Set (StatedProj (StatedSp 2 K)))
  set N := normalizer (E : Set (StatedProj (StatedSp 2 K)))
  have hidx : ¬ 3 ∣ (C.subgroupOf N).index := by
    intro h3
    have h3' : 3 ∣ C.relIndex N := h3
    exact hQ ((h3'.trans (Dvd.intro _ (relIndex_mul_index (centralizer_le_normalizer _)))).trans
      (index_dvd_of_le hQC))
  have hm : h ^ (C.subgroupOf N).index ∈ C := by
    have h1 := pow_index_mem (C.subgroupOf N) (⟨h, hN⟩ : N)
    rw [mem_subgroupOf] at h1
    simpa using h1
  have hhC : h ∈ C := Subgroup.mem_of_forall_prime_exists_pow_mem fun ℓ hℓ => by
    by_cases hℓ3 : ℓ = 3
    · subst hℓ3
      exact ⟨_, hidx, hm⟩
    · exact ⟨3 ^ k, fun h' => hℓ3 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1
        (hℓ.dvd_of_dvd_pow h')), hC3⟩
  intro x hx
  rw [hact x hx, ← mem_centralizer_iff.1 hhC x hx, mul_inv_cancel_right]

theorem uc22s218k_odd_sp4 {X : Type} [Group X] {n p : ℕ} (hX : IsSp4 X n) (hn : Odd n)
    (hpn : p ∣ 2 ^ n + 1) :
    ∃ E Q : Subgroup X, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 ∧ E ≤ Q ∧ IsPGroup 3 Q ∧
      ¬ 3 ∣ Q.index ∧ (∃ z ∈ centralizer (E : Set X), orderOf z = p) ∧
      ∀ α : MulAut X, ∀ k : ℕ, α ^ 3 ^ k = 1 → (∀ x ∈ E, α x ∈ Q) → ∀ x ∈ E, α x = x := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := CFSG.Blueprint.LieModel.statedClassicalModel hX (by decide)
  have : CharP K 2 := uc22pwlie_charP_two hK
  have h3 : 3 ∣ Nat.card K + 1 := by
    obtain ⟨m, rfl⟩ := hn
    have e4 : 2 ^ (2 * m + 1) = 2 * 4 ^ m := by
      rw [pow_succ, pow_mul, mul_comm]
      norm_num
    have h4 : 4 ^ m % 3 = 1 := by
      rw [Nat.pow_mod]
      norm_num
    rw [hK, e4]
    omega
  obtain ⟨E, Q, hEel, hEc, hEQ, hQp, hQi, hQC, hQE, ⟨z, hzC, hzo⟩, hfix⟩ :=
    uc22s218k_odd_model (K := K) (p := p) (by rw [hK]; exact hpn) h3
  refine ⟨E.map e.symm.toMonoidHom, Q.map e.symm.toMonoidHom, hEel.map _, ?_, map_mono hEQ,
    hQp.map _, ?_, ⟨e.symm z, ?_, by rw [MulEquiv.orderOf_eq, hzo]⟩, ?_⟩
  · rw [card_map_of_injective (f := e.symm.toMonoidHom) e.symm.injective, hEc]
  · rwa [index_map_of_bijective (f := e.symm.toMonoidHom) e.symm.bijective]
  · rw [mem_centralizer_iff]
    rintro _ ⟨x, hx, rfl⟩
    simpa only [MulEquiv.coe_toMonoidHom, map_mul] using
      congrArg e.symm (mem_centralizer_iff.1 hzC x hx)
  · intro α k hα hαE
    rintro _ ⟨y, hy, rfl⟩
    have hβ : (MulAut.congr e α) ^ 3 ^ k = 1 := by rw [← map_pow, hα, map_one]
    have hβE : ∀ x ∈ E, MulAut.congr e α x ∈ Q := fun x hx => by
      have h1 := hαE (e.symm x) (mem_map_of_mem _ hx)
      rw [mem_map_equiv, MulEquiv.symm_symm] at h1
      exact h1
    have h2 : e (α (e.symm y)) = y := uc22s218k_fix_of_pow_eq_one hEel hfix hQi hQC hQE hβ hβE y hy
    simpa using congrArg e.symm h2

end CFSG.LocalAnalysis.UniquenessCase.UC22
