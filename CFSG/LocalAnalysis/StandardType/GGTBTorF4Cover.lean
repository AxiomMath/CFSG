module

public import CFSG.LocalAnalysis.StandardType.GGTBTorTransport
public import CFSG.LocalAnalysis.StandardType.GGTableBF4Basic
public import CFSG.LieType.Steinberg.CentralExt.F4Even
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerF4Toral

public noncomputable section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar

theorem f4_two_pow_ne_two_of_scalar_prime {p n : ℕ} (hp : p.Prime)
    (hdiv : p ∣ (2 ^ n - 1) * (2 ^ n + 1))
    (hex : ¬ (p = 3 ∧ p ∣ 2 ^ n + 1)) : 2 ^ n ≠ 2 := by
  intro hq
  have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
    (by simpa only [hq] using hdiv)
  apply hex
  exact ⟨hp3, by simp [hq, hp3]⟩

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem f4_card_four_le_of_ne_two (hK2 : Nat.card K ≠ 2) : 4 ≤ Nat.card K := by
  let : Fintype K := Fintype.ofFinite K
  have hEven : Nat.card K % 2 = 0 := by
    simpa only [Nat.card_eq_fintype_card] using
      FiniteField.even_card_of_char_two (ringChar.eq K 2)
  have hPos : 1 < Nat.card K := Finite.one_lt_card
  obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero hEven
  have hk0 : 0 < k := by omega
  have hk1 : k ≠ 1 := by
    intro h
    apply hK2
    omega
  omega

section Model


theorem exists_f4_model_of_tbGroup {p r : ℕ} {L : Type} [Group L] [Finite L]
    (hK2 : Nat.card K ≠ 2)
    (ψ : L →* TableBF4.RecipeGroup K) (A : Subgroup (MulAut L))
    (hTB : GGTorusTBGroup p r (TableBF4.RecipeGroup K)
      (TableBF4.RecipeID K) L ψ A) :
    ∃ e : L ≃* adjointGroup .F4 K,
      (∀ l, e l = TableBF4.recipeEquiv K (ψ l)) ∧
      ∃ E : Subgroup (adjointGroup .F4 K), IsElemAbelian p E ∧ Nat.card E = Nat.card A ∧
        (∀ g : adjointGroup .F4 K, (∀ x ∈ E, g * x = x * g) → g ^ p = 1 → g ∈ E) ∧
        A.map (MulAut.congr e).toMonoidHom =
          E.map (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)) := by
  have hK4 : 4 ≤ Nat.card K := f4_card_four_le_of_ne_two hK2
  obtain ⟨hψ, hker, hperf, hA, hAI, -, -, hSC⟩ := hTB
  have : Group.IsPerfect L := ⟨hperf⟩
  let π : L →* adjointGroup .F4 K := (TableBF4.recipeEquiv K).toMonoidHom.comp ψ
  have hπ : Function.Surjective π := (TableBF4.recipeEquiv K).surjective.comp hψ
  have hπker : π.ker ≤ Subgroup.center L := by
    simpa only [π, MonoidHom.ker_comp_of_injective ψ
      (TableBF4.recipeEquiv K).toMonoidHom (TableBF4.recipeEquiv K).injective]
      using hker
  let e : L ≃* adjointGroup .F4 K := MulEquiv.ofBijective π
    (CFSG.LieType.Steinberg.CentralExt.f4_even_bijective_of_perfect hK4 π hπ hπker)
  let B : Subgroup (MulAut (adjointGroup .F4 K)) := A.map (MulAut.congr e).toMonoidHom
  let j : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K) := MulAut.conj
  have hj : Function.Injective j := mulAut_conj_injective_adjointGroup (τ := .F4) (K := K)
  have hBinn : B ≤ j.range := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨φ, hφ, hφeq⟩ := hAI a ha
    obtain ⟨x, rfl⟩ := TableBF4.idImage_subset_inn K hφ
    refine ⟨TableBF4.recipeEquiv K x, ?_⟩
    apply MulEquiv.ext
    intro y
    obtain ⟨l, rfl⟩ := e.surjective y
    have heq : ∀ l, e l = TableBF4.recipeEquiv K (ψ l) := fun _ => rfl
    change MulAut.conj (TableBF4.recipeEquiv K x) (e l) = MulAut.congr e a (e l)
    rw [MulAut.conj_apply, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply]
    change (TableBF4.recipeEquiv K x) * e l *
      (TableBF4.recipeEquiv K x)⁻¹ = e (a l)
    rw [heq, heq]
    simp only [← map_inv, ← map_mul]
    exact congrArg (TableBF4.recipeEquiv K) (hφeq l)
  let E : Subgroup (adjointGroup .F4 K) := B.comap j
  have hEB : E.map j = B := Subgroup.map_comap_eq_self hBinn
  have hB : IsElemAbelian p B := TableB.isElemAbelian_map hA _
  have hE : IsElemAbelian p E := by
    refine ⟨⟨⟨fun x y => Subtype.ext (hj ?_)⟩⟩, fun x hx => hj ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact TableB.IsElemAbelian.comm hB x.2 y.2
    · rw [map_pow, map_one]
      exact hB.2 _ hx
  have hcard : Nat.card E = Nat.card A := by
    rw [← Subgroup.card_map_of_injective hj, hEB, Subgroup.card_map_of_injective
      (MulAut.congr e).injective]
  have hESC : ∀ g : adjointGroup .F4 K, (∀ x ∈ E, g * x = x * g) →
      g ^ p = 1 → g ∈ E := by
    intro g hg hgp
    have hnp : (e.symm g) ^ p = 1 := by rw [← map_pow, hgp, map_one]
    have hfix : ∀ a ∈ A, a (e.symm g) = e.symm g := by
      intro a ha
      obtain ⟨x, hx⟩ := hBinn (Subgroup.mem_map_of_mem _ ha)
      have hxE : x ∈ E := by
        change j x ∈ B
        exact hx ▸ Subgroup.mem_map_of_mem (MulAut.congr e).toMonoidHom ha
      apply e.injective
      have hax : MulAut.congr e a g = x * g * x⁻¹ := by
        exact (congrArg (fun f : MulAut (adjointGroup .F4 K) => f g) hx).symm
      have hconj : x * g * x⁻¹ = g := by rw [← hg x hxE, mul_inv_cancel_right]
      simpa [MulAut.congr_apply, MulEquiv.trans_apply] using hax.trans hconj
    have hmem := hSC (e.symm g) hfix hnp
    change j g ∈ B
    have h := Subgroup.mem_map_of_mem (MulAut.congr e).toMonoidHom hmem
    change MulAut.congr e (MulAut.conj (e.symm g)) ∈ B at h
    simpa only [congr_conj, MulEquiv.apply_symm_apply] using h
  exact ⟨e, fun _ => rfl, E, hE, hcard, hESC, hEB.symm⟩

end Model

omit [Finite K] [CharP K 2] in
theorem torData_of_f4_model {L : Type} [Group L] (e : L ≃* adjointGroup .F4 K)
    {A : Subgroup (MulAut L)} {E : Subgroup (adjointGroup .F4 K)}
    (hA : A.map (MulAut.congr e).toMonoidHom =
      E.map (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)))
    {m N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    (h : GGTorusTorData m N C M (adjointGroup .F4 K)
      (E.map (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)))) :
    GGTorusTorData m N C M L A := by
  have hback : (E.map (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K))).map
      (MulAut.congr e.symm).toMonoidHom = A := by
    rw [← hA, Subgroup.map_map]
    have hcomp : (MulAut.congr e.symm).toMonoidHom.comp (MulAut.congr e).toMonoidHom =
        MonoidHom.id (MulAut L) := by
      ext a x
      simp [MulAut.congr_apply, MulEquiv.trans_apply]
    rw [hcomp, Subgroup.map_id]
  exact h.transport_eq e.symm hback.symm

end CFSG.StandardType
