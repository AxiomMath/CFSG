module

public import CFSG.RankThree.PartTwo.KFacts.KS21SylowCore
public import CFSG.RankThree.PartTwo.KFacts.KS21FusionU58

public noncomputable section

namespace CFSG.RankThree.PartTwo.KFacts.KS21.U58

open CFSG.RankThree.PartTwo.KFacts.KS21.DFT CFSG.Assembly.RankThreeEven

theorem exists_zeta_data : ∃ ζ : Kˣ, orderOf ζ = 9 ∧ ζ ^ 9 = 1 ∧
    ((ζ ^ 3 : Kˣ) : K) ^ 2 + ↑(ζ ^ 3) + 1 = 0 := by
  obtain ⟨ζ, hζ⟩ := exists_zeta
  have hζ9 : ζ ^ 9 = 1 := by
    have := pow_orderOf_eq_one ζ
    rwa [hζ] at this
  have hω : orderOf (ζ ^ 3) = 3 := by
    rw [orderOf_pow_of_dvd (by norm_num) (by rw [hζ]; norm_num), hζ]
  have hω3 : (ζ ^ 3) ^ 3 = 1 := by
    have := pow_orderOf_eq_one (ζ ^ 3)
    rwa [hω] at this
  have hω1 : ζ ^ 3 ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hω
    norm_num at hω
  exact ⟨ζ, hζ, hζ9, sq_add_add_one_eq_zero hω3 hω1⟩

theorem emb5_tau9_mem {ζ : Kˣ} (hζ9 : ζ ^ 9 = 1) (v) : emb5 (tau9 hζ9 v) ∈ SUI := by
  obtain ⟨⟨u, d⟩, rfl⟩ := Multiplicative.ofAdd.surjective v
  rw [tau9_apply]
  refine emb5_mem (unitary_diagGL fun i => ?_) (pow_eight_mul_self ?_)
  · rw [← pow_mul, mul_comm _ 9, pow_mul, hζ9, one_pow]
  · rw [← pow_mul, mul_comm _ 9, pow_mul, hζ9, one_pow]

theorem emb5_permGL3_mem : emb5 ((permGL3, 1) : GL (Fin 3) K × Kˣ) ∈ SUI :=
  emb5_mem unitary_permGL3 (by simp)

theorem permGL3_one_pow_three : ((permGL3, 1) : GL (Fin 3) K × Kˣ) ^ 3 = 1 := by
  rw [Prod.pow_mk, permGL3_pow_three, one_pow]
  rfl

theorem maxEA_SUI : MaxEA SUI 4 := by
  obtain ⟨ζ, hζ, hζ9, -⟩ := exists_zeta_data
  exact maxEA_of_torus_sub (S := SUI) emb5 emb5_injective (tau9_injective hζ9 hζ)
    (emb5_tau9_mem hζ9) emb5_permGL3_mem permGL3_one_pow_three (permGL3_mul_tau9 hζ9) rot9_ne
    card_V9 card_SUI (by norm_num) rot9_norm card_fix9_lt card_V9_three

theorem maxEA_projSU : MaxEA (projSU 5 2 3) 4 := maxEA_SUI.of_mulEquiv equivSUI.symm

theorem sylowModel_SUI :
    SylowModel SUI (Multiplicative (ZMod 9) × Multiplicative (ZMod 9) ≀ᵣ
      Multiplicative (ZMod 3)) := by
  obtain ⟨ζ, hζ, hζ9, -⟩ := exists_zeta_data
  have hmem : ∀ x, emb5 (wreathHom9 (tau9 hζ9) (permGL3, 1) permGL3_one_pow_three
      (permGL3_mul_tau9 hζ9) x) ∈ SUI := by
    intro x
    rw [wreathHom9_apply, map_mul, map_pow]
    exact SUI.mul_mem (emb5_tau9_mem hζ9 _) (SUI.pow_mem emb5_permGL3_mem _)
  refine ⟨(emb5.comp (wreathHom9 (tau9 hζ9) (permGL3, 1) permGL3_one_pow_three
    (permGL3_mul_tau9 hζ9))).codRestrict SUI hmem, fun x y h => ?_, ?_⟩
  · have h' := congrArg Subtype.val h
    exact wreathHom9_injective (tau9_injective hζ9 hζ) permGL3_one_pow_three
      (permGL3_mul_tau9 hζ9) rot9_ne (emb5_injective h')
  · rw [factorization_three_eq card_SUI (by norm_num), Nat.card_prod,
      RegularWreathProduct.card]
    simp

theorem sylowModel_projSU :
    SylowModel (projSU 5 2 3) (Multiplicative (ZMod 9) × Multiplicative (ZMod 9) ≀ᵣ
      Multiplicative (ZMod 3)) :=
  sylowModel_SUI.of_mulEquiv equivSUI.symm

end CFSG.RankThree.PartTwo.KFacts.KS21.U58
