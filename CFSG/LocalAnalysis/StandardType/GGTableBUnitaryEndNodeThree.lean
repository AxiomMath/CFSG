module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeInner
public import CFSG.LocalAnalysis.StandardType.GGPGLTorality
import CFSG.RankThree.PartOne.S15K.CentralCover

public section

namespace CFSG.StandardType

namespace TableBUE

open CFSG.Assembly Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {K : Type} [Field K] [Finite K] {n d p : ℕ} (h : UnitaryFieldData 2 n K)

omit [Finite K] in
theorem mem_scalars_of_eq_scalar {M : GL (Fin d) K} {c : K}
    (hc : (M : Matrix (Fin d) (Fin d) K) = Matrix.scalar (Fin d) c) :
    M ∈ LargeEvenScalars (Fin d) K := by
  rcases isEmpty_or_nonempty (Fin d) with hd | ⟨⟨i₀⟩⟩
  · refine ⟨1, Units.ext ?_⟩
    ext i
    exact isEmptyElim i
  · have hc0 : c ≠ 0 := by
      intro h0
      have h1 : ((M * M⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i₀ i₀ = 1 := by
        rw [mul_inv_cancel, Units.val_one, Matrix.one_apply_eq]
      rw [Units.val_mul, hc, h0, map_zero, Matrix.zero_mul] at h1
      exact zero_ne_one h1
    refine ⟨Units.mk0 c hc0, Units.ext ?_⟩
    rw [Matrix.GeneralLinearGroup.coe_scalar, hc, Units.val_mk0]

include h in
theorem mem_scalars_of_projConj_eq_one (hK : Nat.card K = (2 ^ n) ^ 2) (hd : 3 ≤ d)
    (hdq : (d, 2 ^ n) ≠ (3, 2)) (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1)
    {M : Subgroup.normalizer (LargeEvenSUGroup (Fin d) K (2 ^ n) : Set (GL (Fin d) K))}
    (hM : TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ n)) M = 1) :
    (M : GL (Fin d) K) ∈ LargeEvenScalars (Fin d) K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hperf : Group.IsPerfect (LargeEvenSUGroup (Fin d) K (2 ^ n)) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hK hd hdq
  have hker : (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n))).ker ≤
      Subgroup.center (LargeEvenSUGroup (Fin d) K (2 ^ n)) := ker_projMk_le_center
  refine mem_scalars_of_commute h hp hpq fun g hg => ?_
  have key := CFSG.RankThree.PartOne.S15K.eq_of_perfect_of_map_eq
    (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n))) hker hperf
    ((LargeEvenSUGroup (Fin d) K (2 ^ n)).normalizerMonoidHom M).toMonoidHom
    (MonoidHom.id (LargeEvenSUGroup (Fin d) K (2 ^ n))) (fun u => by
      have h1 := congrArg (fun ψ : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) =>
        ψ (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)) u)) hM
      exact h1) ⟨g, hg⟩
  have h2 := congrArg Subtype.val key
  change (M : GL (Fin d) K) * g * (M : GL (Fin d) K)⁻¹ = g at h2
  calc (M : GL (Fin d) K) * g = (M : GL (Fin d) K) * g * (M : GL (Fin d) K)⁻¹ * M := by group
    _ = g * M := by rw [h2]

include h in
theorem card_lt_unitary_three (hK : Nat.card K = (2 ^ n) ^ 2) (h2 : 2 < 2 ^ n) (hp : p.Prime)
    (hpq : p ∣ 2 ^ n + 1) {L' : Type} [Group L'] [Finite L']
    {ψ : L' →* LargeEvenProj (LargeEvenSUGroup (Fin 3) K (2 ^ n))} (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ φ ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSUGroup (Fin 3) K (2 ^ n))) (LargeEvenGUSet (Fin 3) K (2 ^ n)),
        ∀ l : L', φ (ψ l) = ψ (a l)) :
    Nat.card A < p ^ 3 := by
  classical
  have hdq : (3, 2 ^ n) ≠ (3, 2) := by
    intro he
    have := congrArg Prod.snd he
    simp only at this
    omega
  have hN := gu_subset_normalizer (d := 3) h
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one h.one_le hpq
  have hpK := dvd_card_sub_one hK hpq
  set ρ := TableB.projConj (LargeEvenSUGroup (Fin 3) K (2 ^ n)) with hρ
  set N₀ : Subgroup
      (Subgroup.normalizer (LargeEvenSUGroup (Fin 3) K (2 ^ n) : Set (GL (Fin 3) K))) :=
    (TypeA.inducedSub ψ A).comap ρ with hN₀
  set χ : Subgroup.normalizer (LargeEvenSUGroup (Fin 3) K (2 ^ n) : Set (GL (Fin 3) K)) →*
      MulAut (projectiveSL 3 K) :=
    (conjAut 3 K).comp
      (Subgroup.normalizer (LargeEvenSUGroup (Fin 3) K (2 ^ n) : Set (GL (Fin 3) K))).subtype
    with hχ
  set X := N₀.map χ with hX
  have hscal : ∀ M ∈ N₀, ρ M = 1 → χ M = 1 := by
    intro M _ hM
    obtain ⟨c, hc⟩ := mem_scalars_of_projConj_eq_one h hK le_rfl hdq hp hpq hM
    rw [hχ, MonoidHom.comp_apply, Subgroup.coe_subtype, ← hc, conjAut_scalar]
  have hab := TypeA.isElemAbelian_inducedSub hψ hA (ψ := ψ)
  have hXab : IsElemAbelian p X := by
    refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨_, M, hM, rfl⟩ ⟨_, M', hM', rfl⟩
      apply Subtype.ext
      show χ M * χ M' = χ M' * χ M
      have hc : ρ (M * M' * M⁻¹ * M'⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv,
          TableB.IsElemAbelian.comm hab hM hM', mul_inv_cancel_right, mul_inv_cancel]
      have h1 := hscal _ (N₀.mul_mem (N₀.mul_mem (N₀.mul_mem hM hM') (N₀.inv_mem hM))
        (N₀.inv_mem hM')) hc
      rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
      calc χ M * χ M' = χ M * χ M' * (χ M)⁻¹ * (χ M')⁻¹ * (χ M' * χ M) := by group
        _ = χ M' * χ M := by rw [h1, one_mul]
    · rintro _ ⟨M, hM, rfl⟩
      rw [← map_pow]
      exact hscal _ (N₀.pow_mem hM p) (by rw [map_pow]; exact hab.2 _ hM)
  have hXI : (X : Set (MulAut (projectiveSL 3 K))) ⊆ Set.range (conjAut 3 K) := by
    rintro _ ⟨M, -, rfl⟩
    exact ⟨M, rfl⟩
  have hlift : ∀ a : A,
      ∃ M : Subgroup.normalizer (LargeEvenSUGroup (Fin 3) K (2 ^ n) : Set (GL (Fin 3) K)),
      ∀ l : L', ρ M (ψ l) = ψ ((a : MulAut L') l) := by
    intro a
    obtain ⟨φ, hφI, hφ⟩ := hAI a a.2
    obtain ⟨M, hMgu, hMeq⟩ := TableB.exists_eq_projConj hN hφI
    exact ⟨⟨M, hN hMgu⟩, fun l => by rw [← hMeq]; exact hφ l⟩
  choose Mf hMf using hlift
  have hMN : ∀ a : A, Mf a ∈ N₀ := fun a =>
    TypeA.mem_inducedSub.mpr ⟨a, a.2, hMf a⟩
  let f : A → X := fun a => ⟨χ (Mf a), Mf a, hMN a, rfl⟩
  have hf : Function.Injective f := by
    intro a b hab'
    have h1 : χ ((Mf a)⁻¹ * Mf b) = 1 := by
      have := congrArg Subtype.val hab'
      simp only [f] at this
      rw [map_mul, map_inv, this, inv_mul_cancel]
    obtain ⟨c, hc⟩ := TypeA.exists_scalar_of_conjAut_eq_one h1
    have hz := mem_scalars_of_eq_scalar hc
    have h2 : ρ ((Mf a)⁻¹ * Mf b) = 1 := by
      have he : (Mf a)⁻¹ * Mf b = ⟨_, TableB.scalar_mem_normalizer _ hz⟩ := Subtype.ext rfl
      rw [he]
      exact TableB.projConj_of_scalar _ hz
    have h3 : ρ (Mf a) = ρ (Mf b) := by
      rw [map_mul, map_inv, inv_mul_eq_one] at h2
      exact h2
    apply Subtype.ext
    apply TypeA.mulAut_eq_of_forall ψ hker hperf
    intro l
    rw [← hMf a l, ← hMf b l, h3]
  have hle := Nat.card_le_card_of_injective f hf
  have hlt := TypeA.card_lt_of_torality hp hpK (by norm_num) le_rfl
    (TypeA.ggPGLTorality_holds hp hp2 hpK) hXab hXI
  omega

include h in
theorem ggEndNodeAdm_unitary_three (hK : Nat.card K = (2 ^ n) ^ 2) (h2 : 2 < 2 ^ n)
    (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (r : ℕ) :
    GGEndNodeAdm p r (LargeEvenProj (LargeEvenSUGroup (Fin 3) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 3) K (2 ^ n)))
        (LargeEvenGUSet (Fin 3) K (2 ^ n))) := by
  intro L' _ _ ψ hψ hker hperf A hA hAI _ h3 _
  exact absurd h3 (not_le.mpr (card_lt_unitary_three h hK h2 hp hpq hψ hker hperf hA hAI))

end TableBUE

end CFSG.StandardType
