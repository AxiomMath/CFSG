module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerNinePGL
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerNineDim
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerNineClassicalLabel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag NbrInnerNine

theorem NbrInnerNine.card_lt_cube_of_pow_le {G : Type*} [Group G] {E : Subgroup G} {p e d : ℕ}
    (hp : p.Prime) (hE : IsElemAbelian p E) [Finite E] (h : Nat.card E ^ e ≤ p ^ d)
    (hd : d < 3 * e) : Nat.card E < p ^ 3 := by
  have := Fact.mk hp
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp (TableB.isPGroup_of_isElemAbelian hE)
  rw [hk, ← pow_mul] at h
  rw [hk]
  have hkd : k * e ≤ d := (Nat.pow_le_pow_iff_right hp.one_lt).mp h
  refine Nat.pow_lt_pow_right hp.one_lt ?_
  by_contra h3
  have : 3 * e ≤ k * e := by nlinarith
  omega

namespace TypeA

variable {K : Type} [Field K] [Finite K]

theorem card_lt_cube_pgl_of_ord [CharP K 2] {d p : ℕ} (hd3 : 3 ≤ d) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpe : ∀ j, 0 < j → 3 * j ≤ d → ¬ p ∣ Nat.card K ^ j - 1)
    {X : Subgroup (MulAut (projectiveSL d K))} (hX : IsElemAbelian p X)
    (hXI : (X : Set (MulAut (projectiveSL d K))) ⊆ Set.range (conjAut d K)) :
    Nat.card X < p ^ 3 := by
  have hpK : ¬ p ∣ Nat.card K - 1 := by
    have := hpe 1 one_pos (by omega)
    rwa [pow_one] at this
  obtain ⟨E, hE, hcard, -⟩ := exists_lift_of_not_dvd hp hpK (by omega) hX hXI
  have h := card_pow_le_of_gl (e := d / 3 + 1) hp
    (CFSG.RankThree.PartOne.LIT.natCast_ne_zero_of_charTwo hp hp2)
    (fun j hj hje => hpe j hj (by omega)) E (fun g hg h hh => TableB.IsElemAbelian.comm hE hg hh)
    (fun g hg => hE.2 g hg)
  rw [Fintype.card_fin] at h
  rw [← hcard]
  exact card_lt_cube_of_pow_le hp hE h (by omega)

end TypeA

theorem recipeLinear_card_lt_of_ord {d N p : ℕ} (hd3 : 3 ≤ d) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpe : ∀ j, 0 < j → 3 * j ≤ d → ¬ p ∣ (2 ^ N) ^ j - 1) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeLinear d (2 ^ N) Q) :
    LargeEvenRecipeLinear d (2 ^ N) fun R _ I F => Q R I F ∧ ∀ X : Subgroup (MulAut R),
      (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X → Nat.card X < p ^ 3 := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  refine ⟨K, inferInstance, inferInstance, hK, hQ, fun X hXI hX => ?_⟩
  have : CharP K 2 := charP_two_of_card hK
  exact StdSubRestThree.card_lt_of_congr (TypeA.recipeEquiv d K)
    (fun _ hφ => TypeA.congr_recipeEquiv_mem hφ)
    (fun _ hX'I hX' => TypeA.card_lt_cube_pgl_of_ord hd3 hp hp2 (by rw [hK]; exact hpe)
      hX' hX'I) hXI hX

theorem largeEvenLabelAll_card_lt_linear_of_ord {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {lab : LargeEvenLabel} (h : (lab.tag = .A ∧ 2 ≤ lab.rank) ∨ (lab.tag = .D ∧ lab.rank = 3))
    (hpe : ∀ j, 0 < j → 3 * j ≤ (if lab.tag = .D then 4 else lab.rank + 1) →
      ¬ p ∣ (2 ^ lab.n) ^ j - 1) :
    LargeEvenLabelAll lab fun R _ I _ => ∀ X : Subgroup (MulAut R),
      (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X → Nat.card X < p ^ 3 := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at h hpe
  intro Q hQ
  rcases h with ⟨rfl, hl⟩ | ⟨rfl, rfl⟩
  · simp only [reduceCtorEq, ↓reduceIte] at hpe
    exact recipeLinear_card_lt_of_ord (d := l + 1) (by omega) hp hp2 hpe hQ
  · simp only [↓reduceIte] at hpe
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    simp only [↓reduceIte] at hQ ⊢
    exact recipeLinear_card_lt_of_ord (d := 4) (by norm_num) hp hp2 hpe hQ

namespace TableBUE

open CFSG.ClassicalGroups.UnitaryFlag

variable {K : Type} [Field K] [Finite K] {n d p : ℕ}

theorem card_lt_unitary_of_ord (h : UnitaryFieldData 2 n K) (hK : Nat.card K = (2 ^ n) ^ 2)
    (hdq : (d, 2 ^ n) ≠ (3, 2)) (hd3 : 3 ≤ d) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpe : ∀ j, 0 < j → 3 * j ≤ d → ¬ p ∣ Nat.card K ^ j - 1) {L' : Type} [Group L'] [Finite L']
    {ψ : L' →* LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))} (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ φ ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n))) (LargeEvenGUSet (Fin d) K (2 ^ n)),
        ∀ l : L', φ (ψ l) = ψ (a l)) :
    Nat.card A < p ^ 3 := by
  classical
  have : CharP K 2 := h.charP
  obtain ⟨p', hp', hp'q⟩ := Nat.exists_prime_and_dvd (n := 2 ^ n + 1) (by
    have := Nat.one_le_two_pow (n := n)
    omega)
  have hN := gu_subset_normalizer (d := d) h
  set ρ := TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ n)) with hρ
  set N₀ : Subgroup
      (Subgroup.normalizer (LargeEvenSUGroup (Fin d) K (2 ^ n) : Set (GL (Fin d) K))) :=
    (TypeA.inducedSub ψ A).comap ρ with hN₀
  set χ : Subgroup.normalizer (LargeEvenSUGroup (Fin d) K (2 ^ n) : Set (GL (Fin d) K)) →*
      MulAut (projectiveSL d K) :=
    (conjAut d K).comp
      (Subgroup.normalizer (LargeEvenSUGroup (Fin d) K (2 ^ n) : Set (GL (Fin d) K))).subtype
    with hχ
  set X := N₀.map χ with hX
  have hscal : ∀ M ∈ N₀, ρ M = 1 → χ M = 1 := by
    intro M _ hM
    obtain ⟨c, hc⟩ := mem_scalars_of_projConj_eq_one h hK hd3 hdq hp' hp'q hM
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
  have hXI : (X : Set (MulAut (projectiveSL d K))) ⊆ Set.range (conjAut d K) := by
    rintro _ ⟨M, -, rfl⟩
    exact ⟨M, rfl⟩
  have hlift : ∀ a : A,
      ∃ M : Subgroup.normalizer (LargeEvenSUGroup (Fin d) K (2 ^ n) : Set (GL (Fin d) K)),
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
  have hlt := TypeA.card_lt_cube_pgl_of_ord hd3 hp hp2 hpe hXab hXI
  omega

end TableBUE

open scoped commutatorElement in
theorem recipeUnitary_card_lt_of_ord {d n p : ℕ} (hn : 1 ≤ n) (hdq : (d, 2 ^ n) ≠ (3, 2))
    (hd3 : 3 ≤ d) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpe : ∀ j, 0 < j → 3 * j ≤ d → ¬ p ∣ ((2 ^ n) ^ 2) ^ j - 1)
    {Q : LargeEvenRawCont} (h : LargeEvenRecipeUnitary d (2 ^ n) Q) :
    LargeEvenRecipeUnitary d (2 ^ n) fun R _ I F => Q R I F ∧ (IsSimpleGroup R →
      (∃ a b : R, a * b ≠ b * a) → ∀ X : Subgroup (MulAut R), (X : Set (MulAut R)) ⊆ I →
        IsElemAbelian p X → Nat.card X < p ^ 3) := by
  obtain ⟨K, i1, i2, hK, hq'⟩ := h
  refine ⟨K, i1, i2, hK, hq', fun hs hna X hXI hX => ?_⟩
  have : Finite (LargeEvenSUGroup (Fin d) K (2 ^ n)) := Subtype.finite
  have : Finite (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) :=
    Finite.of_surjective _ (QuotientGroup.mk'_surjective _)
  have hperf : commutator (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) = ⊤ := by
    have : (commutator (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))).Normal :=
      Subgroup.commutator_normal ⊤ ⊤
    rcases hs.eq_bot_or_eq_top_of_normal (commutator _) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hna
      apply hab
      have hc : ⁅a, b⁆ ∈ commutator (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot] at hc
      exact commutatorElement_eq_one_iff_mul_comm.mp hc
    · exact h
  refine TableBUE.card_lt_unitary_of_ord (TableBU.unitaryFieldData_of_card hK hn) hK hdq hd3
    hp hp2 (by rw [hK]; exact hpe) (ψ := MonoidHom.id _) Function.surjective_id ?_ hperf hX
    fun a ha => ⟨a, hXI ha, fun _ => rfl⟩
  intro x hx
  rw [MonoidHom.mem_ker, MonoidHom.id_apply] at hx
  rw [hx]
  exact Subgroup.one_mem _

theorem largeEvenLabelAll_card_lt_unitary_of_ord {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : (lab.tag = .twA ∧ 2 ≤ lab.rank) ∨ (lab.tag = .twD ∧ lab.rank = 3))
    (hpe : ∀ j, 0 < j → 3 * j ≤ (if lab.tag = .twD then 4 else lab.rank + 1) →
      ¬ p ∣ ((2 ^ lab.n) ^ 2) ^ j - 1) :
    LargeEvenLabelAll lab fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      ∀ X : Subgroup (MulAut R), (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X →
        Nat.card X < p ^ 3 := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at h hpe hlab
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  rcases h with ⟨rfl, hl⟩ | ⟨rfl, rfl⟩
  · simp only [reduceCtorEq, ↓reduceIte] at hpe
    have hdq : (l + 1, 2 ^ n) ≠ (3, 2) := by
      intro he
      have h1 := congrArg Prod.fst he
      have h2 := congrArg Prod.snd he
      simp only at h1 h2
      have hl2 : l = 2 := by omega
      have hn2 : 2 ≤ n := hlab.2.2 hl2
      have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
      omega
    exact recipeUnitary_card_lt_of_ord (d := l + 1) hn hdq (by omega) hp hp2 hpe hQ
  · simp only [↓reduceIte] at hpe
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    simp only [show ¬ ((3 : ℕ) = 2) from by norm_num, ↓reduceIte] at hQ ⊢
    exact recipeUnitary_card_lt_of_ord (d := 4) hn
      (fun he => by have := congrArg Prod.fst he; simp only at this; omega) (by norm_num)
      hp hp2 hpe hQ

theorem NbrInnerNine.center_eq_bot_of_simple {R : Type*} [Group R] (hs : IsSimpleGroup R)
    (hna : ∃ a b : R, a * b ≠ b * a) : Subgroup.center R = ⊥ := by
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center R) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hna
    have ha : a ∈ Subgroup.center R := h ▸ Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.mp ha b).symm

theorem NbrInnerNine.card_lt_cube_proj_of_ord {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] [Finite K] [CharP K 2] {H : Subgroup (GL ι K)}
    (hH : (LargeEvenScalars ι K).subgroupOf H = ⊥) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpe : ∀ j, 0 < j → 3 * j ≤ Fintype.card ι → ¬ p ∣ Nat.card K ^ j - 1)
    {A : Subgroup (LargeEvenProj H)} (hA : IsElemAbelian p A) : Nat.card A < p ^ 3 := by
  let e : LargeEvenProj H ≃* H :=
    (QuotientGroup.quotientMulEquivOfEq hH).trans QuotientGroup.quotientBot
  set A' : Subgroup (GL ι K) := (A.map e.toMonoidHom).map H.subtype with hA'def
  have hA' : IsElemAbelian p A' := TableB.isElemAbelian_map (TableB.isElemAbelian_map hA _) _
  have hcard : Nat.card A' = Nat.card A := by
    rw [hA'def, Subgroup.card_map_of_injective H.subtype_injective,
      Subgroup.card_map_of_injective e.injective]
  have h := card_pow_le_of_gl (e := Fintype.card ι / 3 + 1) hp
    (CFSG.RankThree.PartOne.LIT.natCast_ne_zero_of_charTwo hp hp2)
    (fun j hj hje => hpe j hj (by omega)) A' (fun g hg h hh => TableB.IsElemAbelian.comm hA' hg hh)
    (fun g hg => hA'.2 g hg)
  rw [← hcard]
  exact card_lt_cube_of_pow_le hp hA' h (by omega)

theorem NbrInnerNine.card_lt_cube_sp_of_ord {K : Type} [Field K] [Finite K] [CharP K 2]
    {m p : ℕ} [NeZero m] (hp : p.Prime) (hp2 : p ≠ 2)
    (hpe : ∀ j, 0 < j → 3 * j ≤ 2 * m → ¬ p ∣ Nat.card K ^ j - 1)
    {A : Subgroup (LargeEvenProj (LargeEvenSpGroup K m))} (hA : IsElemAbelian p A) :
    Nat.card A < p ^ 3 := by
  set A' : Subgroup (GL (Fin m ⊕ Fin m) K) :=
    (A.map (TableBSymp.spProjEquivSp (K := K) (m := m)).toMonoidHom).map
      (LargeEvenSpGroup K m).subtype with hA'def
  have hA' : IsElemAbelian p A' := TableB.isElemAbelian_map (TableB.isElemAbelian_map hA _) _
  have hcard : Nat.card A' = Nat.card A := by
    rw [hA'def, Subgroup.card_map_of_injective (LargeEvenSpGroup K m).subtype_injective,
      Subgroup.card_map_of_injective (TableBSymp.spProjEquivSp (K := K) (m := m)).injective]
  have h := card_pow_le_of_gl (e := 2 * m / 3 + 1) hp
    (CFSG.RankThree.PartOne.LIT.natCast_ne_zero_of_charTwo hp hp2)
    (fun j hj hje => hpe j hj (by omega)) A' (fun g hg h hh => TableB.IsElemAbelian.comm hA' hg hh)
    (fun g hg => hA'.2 g hg)
  rw [Fintype.card_sum, Fintype.card_fin] at h
  rw [← hcard]
  exact card_lt_cube_of_pow_le hp hA' h (by omega)

theorem recipeSymplectic_card_lt_of_ord {l n p : ℕ} (hl : 1 ≤ l) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpe : ∀ j, 0 < j → 3 * j ≤ 2 * l → ¬ p ∣ (2 ^ n) ^ j - 1) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeSymplectic l (2 ^ n) false Q) :
    LargeEvenRecipeSymplectic l (2 ^ n) false fun R _ I F => Q R I F ∧ ∀ X : Subgroup (MulAut R),
      (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X → Nat.card X < p ^ 3 := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have := charP_two_of_card hK
  have : NeZero l := ⟨by omega⟩
  refine ⟨K, inferInstance, inferInstance, hK, hQ, fun X hXI hX => ?_⟩
  have : Finite (LargeEvenSpGroup K l) := Subtype.finite
  have : Finite (LargeEvenProj (LargeEvenSpGroup K l)) :=
    Finite.of_equiv _ (TableBSymp.spProjEquivSp (K := K) (m := l)).symm.toEquiv
  exact TableBExcSmallRest.card_lt_of_subset_inn TableBSymp.center_spProj_eq_bot
    (fun A hA => card_lt_cube_sp_of_ord hp hp2 (by rw [hK]; exact hpe) hA)
    (fun φ hφ => TableBSymp.sp_I_subset_inn (hXI hφ)) hX

theorem largeEvenLabelAll_card_lt_symplectic_of_ord {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (ht : lab.tag = .B ∨ lab.tag = .C)
    (hpe : ∀ j, 0 < j → 3 * j ≤ 2 * lab.rank → ¬ p ∣ (2 ^ lab.n) ^ j - 1) :
    LargeEvenLabelAll lab fun R _ I _ => ∀ X : Subgroup (MulAut R),
      (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X → Nat.card X < p ^ 3 := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hpe hlab
  intro Q hQ
  rcases ht with rfl | rfl
  · have hl2 : 2 ≤ l := hlab.2.1
    exact recipeSymplectic_card_lt_of_ord (by omega) hp hp2 hpe hQ
  · have hl2 : 2 ≤ l := hlab.2.1
    exact recipeSymplectic_card_lt_of_ord (by omega) hp hp2 hpe hQ

theorem largeEvenLabelAll_card_lt_orthogonal_of_ord {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {lab : LargeEvenLabel} (ht : lab.tag = .D ∨ lab.tag = .twD) (hl : 4 ≤ lab.rank)
    (hpe : ∀ j, 0 < j → 3 * j ≤ 2 * lab.rank → ¬ p ∣ (2 ^ lab.n) ^ j - 1) :
    LargeEvenLabelAll lab fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      ∀ X : Subgroup (MulAut R), (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X →
        Nat.card X < p ^ 3 := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hl hpe
  intro Q hQ
  rcases ht with rfl | rfl
  · dsimp only [LargeEvenRawDatum] at hQ ⊢
    simp only [show l ≠ 3 by omega, ↓reduceIte] at hQ ⊢
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    have := charP_two_of_card hK
    refine ⟨K, inferInstance, inferInstance, hK, hQ', fun hs hna X hXI hX => ?_⟩
    have : Finite (LargeEvenOmega (LargeEvenQPlus K l)) := Subtype.finite
    have : Finite (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K l))) :=
      Finite.of_surjective _ (QuotientGroup.mk'_surjective _)
    exact TableBExcSmallRest.card_lt_of_subset_inn (center_eq_bot_of_simple hs hna)
      (fun A hA => card_lt_cube_proj_of_ord
        (TableBOrth.scalars_subgroupOf_omegaPlus_eq_bot (by omega)) hp hp2
        (by rw [Fintype.card_sum, Fintype.card_fin, hK]; intro j hj hj3; exact hpe j hj (by omega))
        hA) hXI hX
  · dsimp only [LargeEvenRawDatum] at hQ ⊢
    simp only [show l ≠ 2 by omega, show l ≠ 3 by omega, ↓reduceIte] at hQ ⊢
    obtain ⟨K, _, _, hK, b, c, hbc, hQ'⟩ := hQ
    have := charP_two_of_card hK
    refine ⟨K, inferInstance, inferInstance, hK, b, c, hbc, hQ', fun hs hna X hXI hX => ?_⟩
    have : Finite (LargeEvenOmega (LargeEvenQMinus (l - 1) b c)) := Subtype.finite
    have : Finite (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (l - 1) b c))) :=
      Finite.of_surjective _ (QuotientGroup.mk'_surjective _)
    exact TableBExcSmallRest.card_lt_of_subset_inn (center_eq_bot_of_simple hs hna)
      (fun A hA => card_lt_cube_proj_of_ord
        (TableBOrth.scalars_subgroupOf_omegaMinus_eq_bot b c) hp hp2
        (by
          rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, hK]
          intro j hj hj3
          exact hpe j hj (by omega))
        hA) hXI hX

theorem largeEvenLabelAll_card_lt_nineClassical {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab)
    (hcl : GGTableBNbrInnerNineClassicalLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => IsSimpleGroup R →
      (∃ a b : R, a * b ≠ b * a) → ∀ E : Subgroup (MulAut R),
        (E : Set (MulAut R)) ⊆ I → IsElemAbelian p E → Nat.card E < p ^ 3 := by
  rcases hcl with ⟨h, hpe⟩ | ⟨h, hpe⟩ | ⟨ht, hpe⟩ | ⟨ht, hl, hpe⟩
  · exact (largeEvenLabelAll_card_lt_linear_of_ord hp hp2 h hpe).mono
      fun _ _ _ _ hX _ _ => hX
  · exact largeEvenLabelAll_card_lt_unitary_of_ord hp hp2 hΛ h hpe
  · exact (largeEvenLabelAll_card_lt_symplectic_of_ord hp hp2 hΛ ht hpe).mono
      fun _ _ _ _ hX _ _ => hX
  · exact largeEvenLabelAll_card_lt_orthogonal_of_ord hp hp2 ht hl hpe

end CFSG.StandardType

end
