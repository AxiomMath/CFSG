module

public import CFSG.RankThree.PartOne.KF.ClsSU3
public import CFSG.RankThree.PartOne.S11d.PSUGood

public section

namespace CFSG.RankThree.PartOne.TCU

open Matrix Subgroup CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LieType.BorelTits CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.Assembly.LowTwoRank (StatedSU)

variable {F : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 F K)

theorem unitaryForm_β_eq_idForm [Finite K] [CharP K 2] {n : ℕ} (u v : Fin n → K) :
    (unitaryForm 2 F h.card_eq_sq n).β u v = idForm h n u v := by
  rw [unitaryForm_β, idForm, gramForm_apply]
  simp only [idGram, Units.val_one, Matrix.one_mulVec, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [unitaryInvolution_apply, h.bar_apply]

theorem isIsometric_natRep_gramSU [Finite K] [CharP K 2] (n : ℕ) :
    IsIsometric (unitaryForm 2 F h.card_eq_sq n) (natRep (gramSU h (idGram K n))) := by
  intro g u v
  have hg : (g : GL (Fin n) K) ∈ StatedSU n (2 ^ F) K := by
    have e : unitarySU 2 F K n = gramSU h (idGram K n) := unitarySU_eq_gramSU h n
    exact (SetLike.ext_iff.mp e (g : GL (Fin n) K)).mpr g.2
  rw [natRep_apply, natRep_apply]
  exact statedSU_preserves h.card_eq_sq hg u v

theorem exists_two_subgroup_normalized {A : SUn h 3} {S : Subgroup (PSUn h 3)} (hS1 : S ≠ ⊥)
    (hS2 : IsPGroup 2 ↥S)
    (hA : (A : PSUn h 3) ∈ Subgroup.normalizer (S : Set (PSUn h 3))) :
    ∃ R : Subgroup (SUn h 3), R ≠ ⊥ ∧ IsPGroup 2 ↥R ∧
      A ∈ Subgroup.normalizer (R : Set (SUn h 3)) := by
  classical
  have hfin : Finite K := h.finite
  have hchar : CharP K 2 := h.charP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := piSU h 3 with hπ
  set N : Subgroup (SUn h 3) := S.comap π with hN
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hAN : ∀ n : SUn h 3, n ∈ N ↔ A * n * A⁻¹ ∈ N := by
    intro n
    have h1 := Subgroup.mem_normalizer_iff.mp hA (π n)
    change π n ∈ S ↔ π (A * n * A⁻¹) ∈ S
    rw [map_mul, map_mul, map_inv]
    exact h1
  have hnil : Group.IsNilpotent ↥N := by
    have : Group.IsNilpotent ↥S := hS2.isNilpotent
    refine Subgroup.isNilpotent_of_ker_le_center (π.subgroupComap S) ?_
    intro n hn
    rw [Subgroup.mem_center_iff]
    intro m
    have hn' : (n : SUn h 3) ∈ π.ker := by
      have h0 := congrArg Subtype.val (MonoidHom.mem_ker.mp hn)
      exact MonoidHom.mem_ker.mpr h0
    have := Subgroup.mem_center_iff.mp (piSU_ker_le_center h hn') (m : SUn h 3)
    exact Subtype.ext this
  have := hnil
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥N) := inferInstance
  have hPn : (P : Subgroup ↥N).Normal := inferInstance
  have hPc : (P : Subgroup ↥N).Characteristic := Sylow.characteristic_of_normal P hPn
  let cA : ↥N ≃* ↥N :=
    { toFun := fun n => ⟨A * n * A⁻¹, (hAN n).mp n.2⟩
      invFun := fun n => ⟨A⁻¹ * n * A, by
        have := (hAN (A⁻¹ * n * A)).mpr
        have e : A * (A⁻¹ * (n : SUn h 3) * A) * A⁻¹ = n := by group
        rw [e] at this
        exact this n.2⟩
      left_inv := fun n => Subtype.ext (by simp [mul_assoc])
      right_inv := fun n => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  have hcA : ∀ y : ↥N, cA y ∈ (P : Subgroup ↥N) ↔ y ∈ (P : Subgroup ↥N) := by
    intro y
    have := hPc.fixed cA
    have h2 : y ∈ (P : Subgroup ↥N).comap cA.toMonoidHom ↔ y ∈ (P : Subgroup ↥N) := by
      rw [this]
    exact h2
  refine ⟨(P : Subgroup ↥N).map N.subtype, ?_, ?_, ?_⟩
  ·
    intro hbot
    have hP1 : (P : Subgroup ↥N) = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective _ N.subtype_injective).mp hbot
    have hcardP : Nat.card ↥(P : Subgroup ↥N) = 2 ^ (Nat.card ↥N).factorization 2 :=
      P.card_eq_multiplicity
    rw [hP1, Subgroup.card_bot] at hcardP
    have hf0 : (Nat.card ↥N).factorization 2 = 0 := by
      have h2 : 2 ^ (Nat.card ↥N).factorization 2 = 2 ^ 0 := by rw [pow_zero]; exact hcardP.symm
      exact Nat.pow_right_injective (le_refl 2) h2
    have hS2dvd : 2 ∣ Nat.card ↥S := by
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hS2
      have hne : Nat.card ↥S ≠ 1 := fun h1 => hS1 (Subgroup.card_eq_one.mp h1)
      rcases Nat.eq_zero_or_pos k with hk0 | hk0
      · rw [hk0, pow_zero] at hk
        exact absurd hk hne
      · rw [hk]
        exact dvd_pow_self 2 hk0.ne'
    have hSN : Nat.card ↥S ∣ Nat.card ↥N := by
      refine Subgroup.card_dvd_of_surjective (f := π.subgroupComap S) ?_
      intro s
      obtain ⟨g, hg⟩ := hsurj (s : PSUn h 3)
      exact ⟨⟨g, by change π g ∈ S; rw [hg]; exact s.2⟩, Subtype.ext hg⟩
    have h2N : 2 ∣ Nat.card ↥N := hS2dvd.trans hSN
    have hN0 : Nat.card ↥N ≠ 0 := Nat.card_pos.ne'
    have : 0 < (Nat.card ↥N).factorization 2 :=
      (Nat.Prime.factorization_pos_of_dvd Nat.prime_two hN0 h2N)
    omega
  · exact P.isPGroup'.map N.subtype
  · rw [Subgroup.mem_normalizer_iff]
    intro r
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨cA x, (hcA x).mpr hx, rfl⟩
    · rintro ⟨x, hx, hxr⟩
      have hrN : r ∈ N := by
        rw [hAN r, ← hxr]
        exact x.2
      have hxP : cA ⟨r, hrN⟩ ∈ (P : Subgroup ↥N) := by
        have h3 : cA ⟨r, hrN⟩ = x := Subtype.ext hxr.symm
        rw [h3]
        exact hx
      exact ⟨⟨r, hrN⟩, (hcA _).mp hxP, rfl⟩

theorem exists_isotropic_eigenvector {A : SUn h 3} {S : Subgroup (PSUn h 3)} (hS1 : S ≠ ⊥)
    (hS2 : IsPGroup 2 ↥S) (hA : (A : PSUn h 3) ∈ Subgroup.normalizer (S : Set (PSUn h 3))) :
    ∃ (w : Fin 3 → K) (μ : K), w ≠ 0 ∧ idForm h 3 w w = 0 ∧
      linOf (A : GL (Fin 3) K) w = μ • w := by
  classical
  have hfin : Finite K := h.finite
  have hchar : CharP K 2 := h.charP
  obtain ⟨R, hR1, hR2, hAR⟩ := exists_two_subgroup_normalized h hS1 hS2 hA
  obtain ⟨W, hW0, hWiso, hWE⟩ := KFU.exists_invariant_isotropic
    (unitaryForm 2 F h.card_eq_sq 3) (natRep (gramSU h (idGram K 3)))
    (isIsometric_natRep_gramSU h 3) (natRep_injective _) hR2 hR1 (E := Subgroup.zpowers A)
    ((Subgroup.zpowers_le).mpr hAR)
  have hdim := (KFU.finrank_totallyIsotropic_fin_three _ hWiso hW0).1
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  have hle : Submodule.span K {w} ≤ W := (Submodule.span_singleton_le_iff_mem w W).mpr hwW
  have hspan : W = Submodule.span K {w} :=
    (Submodule.eq_of_le_of_finrank_eq hle ((finrank_span_singleton hw0).trans hdim.symm)).symm
  have hAw : natRep (gramSU h (idGram K 3)) A w ∈ W := hWE A (Subgroup.mem_zpowers A) w hwW
  rw [hspan, Submodule.mem_span_singleton] at hAw
  obtain ⟨μ, hμ⟩ := hAw
  refine ⟨w, μ, hw0, ?_, ?_⟩
  · have h1 : (unitaryForm 2 F h.card_eq_sq 3).β w w = 0 := hWiso hwW w hwW
    rw [← unitaryForm_β_eq_idForm h]
    exact h1
  · rw [natRep_apply] at hμ
    rw [linOf_apply]
    exact hμ.symm

end CFSG.RankThree.PartOne.TCU
