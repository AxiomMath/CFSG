module

public import CFSG.Quasithin.Vol2.Ch10SecAFactsOrthCoord
public import CFSG.Quasithin.Vol2.Ch10SecATorus
public import CFSG.Quasithin.Vol2.Ch10SecAFactsOrthEmb
public import CFSG.Quasithin.Vol2.Ch10SecAFactsTorus
public import CFSG.Quasithin.Vol2.Ch10SecALiftSyl

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.Quasithin CFSG.QuasithinUnique
open scoped Matrix

theorem frobPow_one {F : Type} [Field F] (a : ℕ) :
    frobPow a (1 : Matrix (Fin 2) (Fin 2) F) = 1 := by
  ext i j
  rw [frobPow_apply, Matrix.one_apply]
  split_ifs
  · exact one_pow _
  · exact zero_pow (by positivity)

theorem factOrthTorus_holds : FactOrthTorus := by
  intro V _ H n hO P hP A hAH hAN hAodd v hv hPv hAv
  obtain ⟨F, _, _, _, hF, eρ, β, hβinj, hβherm, hβeq⟩ := exists_orthCoord hO
  have := Fintype.ofFinite F
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0
      have h1 : 1 < Nat.card F := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
      rw [hF] at h1
      norm_num at h1
    · exact h0
  have hσ : ∀ x : F, (x ^ 2 ^ n) ^ 2 ^ n = x := fun x => by
    rw [← pow_mul, ← pow_add, ← two_mul, ← hF, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card x
  have hb0 := exists_add_frobPow_ne_zero hn hF
  set P' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F) :=
    (P.subgroupOf H).comap eρ.toMonoidHom with hP'def
  have hP'mem : ∀ x, x ∈ P' ↔ ((eρ x : ↥H) : MulAut V) ∈ P := fun x => Iff.rfl
  have hP'2 : IsPGroup 2 P' :=
    (hP.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hP.1).symm).comap_of_injective
      eρ.toMonoidHom eρ.injective
  have hP'idx : ¬ 2 ∣ P'.index := by
    rw [hP'def, Subgroup.index_comap_of_surjective _ eρ.surjective]
    exact hP.2.2
  obtain ⟨g, hgP, hPg⟩ := exists_conj_unip hF hP'2 hP'idx
  have : Finite ↥H := Finite.of_equiv _ eρ.toEquiv
  have : Finite ↥A := Finite.of_injective _ (Subgroup.inclusion_injective hAH)
  let ψ : ↥A →* Matrix.SpecialLinearGroup (Fin 2) F :=
    (MulAut.conj g).toMonoidHom.comp (eρ.symm.toMonoidHom.comp (Subgroup.inclusion hAH))
  have hψv : ∀ a : ↥A, ψ a = g * eρ.symm ⟨a, hAH a.2⟩ * g⁻¹ := fun a => rfl
  have hψinj : Function.Injective ψ :=
    ((MulAut.conj g).injective.comp eρ.symm.injective).comp (Subgroup.inclusion_injective hAH)
  have hlow : ∀ a : ↥A,
      ((ψ a : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    intro a
    have hp : ((eρ (g⁻¹ * unipSL 1 * g) : ↥H) : MulAut V) ∈ P := (hP'mem _).mp (hPg 1)
    have hap := (Subgroup.mem_normalizer_iff.mp (hAN a.2) _).mp hp
    have he : eρ (eρ.symm ⟨a, hAH a.2⟩ * (g⁻¹ * unipSL 1 * g) * (eρ.symm ⟨a, hAH a.2⟩)⁻¹) =
        ⟨a, hAH a.2⟩ * eρ (g⁻¹ * unipSL 1 * g) * (⟨a, hAH a.2⟩ : ↥H)⁻¹ := by
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    have hmem : eρ.symm ⟨a, hAH a.2⟩ * (g⁻¹ * unipSL 1 * g) * (eρ.symm ⟨a, hAH a.2⟩)⁻¹ ∈ P' := by
      rw [hP'mem, he, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      exact hap
    obtain ⟨b, hb⟩ := hgP _ hmem
    apply lower_left_eq_zero (b := b)
    rw [hψv, ← hb]
    group
  have hdet : ∀ a : ↥A, ((ψ a : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) 0 0 * ((ψ a : Matrix.SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
    intro a
    have h1 := Matrix.SpecialLinearGroup.det_coe (ψ a)
    rw [Matrix.det_fin_two, hlow a, mul_zero, sub_zero] at h1
    exact h1
  have hne : ∀ a : ↥A, ((ψ a : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := fun a h => by
    have h1 := hdet a
    rw [h, zero_mul] at h1
    exact zero_ne_one h1
  let χ : ↥A →* Fˣ :=
    { toFun := fun a => Units.mk0 _ (hne a)
      map_one' := Units.ext (by simp)
      map_mul' := fun a b => Units.ext (by
        simp only [Units.val_mk0, Units.val_mul, map_mul, Matrix.SpecialLinearGroup.coe_mul,
          Matrix.mul_apply, Fin.sum_univ_two, hlow b, mul_zero, add_zero]) }
  have hχv : ∀ a, (χ a : F) = ((ψ a : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) 0 0 := fun a => rfl
  have hχ : Function.Injective χ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h00 : ((ψ a : Matrix.SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
      rw [← hχv, ha, Units.val_one]
    have h11 : ((ψ a : Matrix.SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
      have h1 := hdet a
      rwa [h00, one_mul] at h1
    have hU : ψ a = unipSL (((ψ a : Matrix.SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) 0 1) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [coe_unipSL, h00, h11, hlow a]
    have hsq : ψ (a * a) = 1 := by rw [map_mul, hU, unipSL_mul_self]
    have ha2 : a * a = 1 := hψinj (by rw [hsq, map_one])
    have hdvd : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact ha2)
    have hodd : Odd (orderOf a) := Odd.of_dvd_nat hAodd (orderOf_dvd_natCard a)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact orderOf_eq_one_iff.mp h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  set X := Multiplicative.toAdd (β v) with hXdef
  have hX0 : X ≠ 0 := fun h0 => hv (hβinj (by rw [map_one]; exact toAdd_eq_zero.mp h0))
  set Y := (g : Matrix (Fin 2) (Fin 2) F) * X * (frobPow n (g : Matrix (Fin 2) (Fin 2) F))ᵀ
    with hYdef
  have hYherm : (frobPow n Y)ᵀ = Y := herm_conj hσ (hβherm v) _
  have hfixP : ∀ b : F, (unipSL b : Matrix (Fin 2) (Fin 2) F) * Y *
      (frobPow n (unipSL b : Matrix (Fin 2) (Fin 2) F))ᵀ = Y := by
    intro b
    have hp : ((eρ (g⁻¹ * unipSL b * g) : ↥H) : MulAut V) v = v :=
      hPv _ ((hP'mem _).mp (hPg b))
    have h1 := hβeq (g⁻¹ * unipSL b * g) v
    rw [hp] at h1
    have h2 : ((g⁻¹ * unipSL b * g : Matrix.SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) * X * (frobPow n ((g⁻¹ * unipSL b * g :
          Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F))ᵀ = X := by
      have h3 := congrArg Multiplicative.toAdd h1.symm
      simpa using h3
    rw [hYdef, twist_conj n _ ((g⁻¹ * unipSL b * g : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) _ X ?_, h2]
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, coe_mul_inv_SL, Matrix.one_mul]
  obtain ⟨hY01, hY10, hY11⟩ := fixed_of_unip hσ hb0 hYherm hfixP
  have hY00 : Y 0 0 ≠ 0 := by
    intro h00
    have hY : Y = 0 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h00, hY01, hY10, hY11]
    apply hX0
    have h1 : ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * Y *
        (frobPow n ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F))ᵀ = X := by
      rw [hYdef]
      calc ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
            ((g : Matrix (Fin 2) (Fin 2) F) * X * (frobPow n (g : Matrix (Fin 2) (Fin 2) F))ᵀ) *
            (frobPow n ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) :
              Matrix (Fin 2) (Fin 2) F))ᵀ =
          (((g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
            (g : Matrix (Fin 2) (Fin 2) F)) * X *
            (frobPow n (((g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) :
              Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F)))ᵀ := by
            rw [frobPow_mul, Matrix.transpose_mul]
            simp only [Matrix.mul_assoc]
        _ = X := by rw [coe_inv_mul_SL, frobPow_one, Matrix.transpose_one, Matrix.one_mul,
            Matrix.mul_one]
    rw [← h1, hY, Matrix.mul_zero, Matrix.zero_mul]
  have hpow : ∀ a : ↥A, χ a ^ (2 ^ n + 1) = 1 := by
    intro a
    have h1 := hβeq (eρ.symm ⟨a, hAH a.2⟩) v
    rw [MulEquiv.apply_symm_apply] at h1
    have h1' : β v = Multiplicative.ofAdd
        ((eρ.symm ⟨a, hAH a.2⟩ : Matrix.SpecialLinearGroup (Fin 2) F) * X *
          (frobPow n ((eρ.symm ⟨a, hAH a.2⟩ : Matrix.SpecialLinearGroup (Fin 2) F) :
            Matrix (Fin 2) (Fin 2) F))ᵀ) := by
      rw [← h1]
      exact congrArg β (hAv a a.2).symm
    have h2 : ((eρ.symm ⟨a, hAH a.2⟩ : Matrix.SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) * X * (frobPow n ((eρ.symm ⟨a, hAH a.2⟩ :
          Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F))ᵀ = X := by
      have h3 := congrArg Multiplicative.toAdd h1'.symm
      simpa using h3
    have h3 : ((ψ a : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * Y *
        (frobPow n ((ψ a : Matrix.SpecialLinearGroup (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F))ᵀ = Y := by
      rw [hYdef, twist_conj n _ ((eρ.symm ⟨a, hAH a.2⟩ : Matrix.SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) _ X ?_, h2]
      rw [hψv, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.mul_assoc, coe_inv_mul_SL, Matrix.mul_one]
    have h4 := congrFun (congrFun h3 0) 0
    rw [twist_apply_zero_zero _ _ hY01 hY10 hY11] at h4
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hχv, Units.val_one, pow_succ]
    have h5 : (((ψ a : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0 ^
        2 ^ n * ((ψ a : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0 -
          1) * Y 0 0 = 0 := by
      linear_combination h4
    exact sub_eq_zero.mp ((mul_eq_zero.mp h5).resolve_right hY00)
  exact exists_injective_zmod_of_units χ hχ (by positivity) hpow

end CFSG.Quasithin.Vol2.Ch10.SecA
