module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Defs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Basic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.TorusProd
import CFSG.LocalAnalysis.UniquenessCase.UC22S13d
import CFSG.Quasithin.H13.QRCAltFiveGL3PairTwoRank
import CFSG.GroupTheory.ProdFactors
import CFSG.Adapters.LieModelSimple
import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLift
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

private theorem taprod_eq_one_of_mul_self {G : Type*} [Group G] {m : ℕ} (hm : Odd m) {x : G}
    (hx : orderOf x ∣ m) (h : x * x = 1) : x = 1 :=
  orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes (Nat.coprime_two_left.2 hm)
    (orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h)) hx)

theorem not_forall_apply_apply_eq_inv_of_card_mod_four {A : Type*} [Group A]
    (hA : Nat.card A % 4 = 3) (μ : A → A) : ¬ ∀ a, μ (μ a) = a⁻¹ := by
  intro hμ
  have : Finite A := Nat.finite_of_card_ne_zero (by omega)
  classical
  let := Fintype.ofFinite A
  have hAodd : Odd (Nat.card A) := Nat.odd_iff.2 (by omega)
  have h4 : ∀ a, μ (μ (μ (μ a))) = a := fun a => by rw [hμ, hμ, inv_inv]
  let e : Equiv.Perm A := ⟨μ, fun a => μ (μ (μ a)), h4, h4⟩
  have he : e ^ 2 = Equiv.inv A := Equiv.ext fun a => by
    rw [sq, Equiv.Perm.mul_apply]
    exact hμ a
  have hι : Equiv.inv A ^ 2 = 1 := Equiv.ext fun a => by
    rw [sq, Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
    exact inv_inv a
  have hfix : Nat.card (Function.fixedPoints (Equiv.inv A)) = 1 := by
    have h1 : ∀ c : Function.fixedPoints (Equiv.inv A), (c : A) = 1 := fun c =>
      taprod_eq_one_of_mul_self hAodd (orderOf_dvd_natCard _)
        (inv_eq_iff_mul_eq_one.1 (show (c : A)⁻¹ = c from c.2))
    rw [Nat.card_eq_one_iff_unique]
    exact ⟨⟨fun a b => Subtype.ext (by rw [h1 a, h1 b])⟩, ⟨⟨1, inv_one⟩⟩⟩
  have hs := Equiv.Perm.sign_of_pow_two_eq_one hι
  simp only [Fintype.card_eq_nat_card] at hs
  rw [hfix, ← he, map_pow, Int.units_sq,
    Odd.neg_one_pow (n := (Nat.card A - 1) / 2) (Nat.odd_iff.2 (by omega))] at hs
  exact absurd hs (by decide)

section Factor

variable {X : Type} [Group X]

private theorem taprod_mem_iff {S S' : Subgroup X} {σ : MulAut X}
    (h : S.map σ.toMonoidHom = S') (x : X) : x ∈ S ↔ σ x ∈ S' := by
  rw [← h, mem_map_equiv, MulEquiv.symm_apply_apply]

private theorem taprod_pow_mem {U : Subgroup X} {σ : MulAut X} (h : ∀ x ∈ U, σ x ∈ U)
    (r : ℕ) : ∀ x ∈ U, (σ ^ r) x ∈ U := by
  induction r with
  | zero => exact fun x hx => by simpa using hx
  | succ r ih =>
    intro x hx
    rw [pow_succ, MulAut.mul_apply]
    exact ih _ (h x hx)

private theorem taprod_inner {n : ℕ} (hodd : Odd n)
    {S : Subgroup X} (hS : IsL2 S n ∨ IsSz S n) {σ : MulAut X} {k : ℕ} (hσ : σ ^ 2 ^ k = 1)
    (hσS : ∀ x, x ∈ S ↔ σ x ∈ S) :
    ∃ s ∈ S, ∀ r : ℕ, ∀ y ∈ S, (σ ^ r) y = s ^ r * y * (s ^ r)⁻¹ := by
  have hmem : σ ∈ CFSG.Quasithin.H13.QRC.autStab S :=
    CFSG.Quasithin.H13.QRC.mem_autStab.2 hσS
  have hpow : (⟨σ, hmem⟩ : CFSG.Quasithin.H13.QRC.autStab S) ^ 2 ^ k = 1 :=
    Subtype.ext (by simpa using hσ)
  obtain ⟨s, hs⟩ := uc22s13d_inner_of_two hS hodd
    (CFSG.Quasithin.H13.QRC.restrictHom S ⟨σ, hmem⟩) (by rw [← map_pow, hpow, map_one])
  refine ⟨s, s.2, fun r y hy => ?_⟩
  have h1 : MulAut.conj (s ^ r) =
      CFSG.Quasithin.H13.QRC.restrictHom S (⟨σ, hmem⟩ ^ r) := by
    rw [map_pow, map_pow, hs]
  have h2 := congrArg (fun f : MulAut S => ((f ⟨y, hy⟩ : S) : X)) h1
  simp only [MulAut.conj_apply, CFSG.Quasithin.H13.QRC.coe_restrictHom_apply, coe_mul, coe_inv,
    coe_pow] at h2
  exact h2.symm

private theorem taprod_fix {n : ℕ} (hodd : Odd n)
    {S U : Subgroup X} (hS : IsL2 S n ∨ IsSz S n) (hUS : U ≤ S)
    (hUc : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x)
    (hcent : ∀ a ∈ U, a ≠ 1 → centralizer ({a} : Set X) ⊓ S ≤ U) {σ : MulAut X} {k : ℕ}
    (hσ : σ ^ 2 ^ k = 1) (hσS : ∀ x, x ∈ S ↔ σ x ∈ S) {r : ℕ} {a : X} (ha : a ∈ U)
    (ha1 : a ≠ 1) (hfix : (σ ^ r) a = a) : ∀ x ∈ U, (σ ^ r) x = x := by
  obtain ⟨s, hsS, hs⟩ := taprod_inner hodd hS hσ hσS
  have hsr : s ^ r ∈ U := by
    refine hcent a ha ha1 ⟨mem_centralizer_singleton_iff.2 ?_, pow_mem hsS r⟩
    have h := hs r a (hUS ha)
    rw [hfix, eq_mul_inv_iff_mul_eq] at h
    exact h.symm
  intro x hx
  rw [hs r x (hUS hx), hUc _ hsr x hx, mul_inv_cancel_right]

private theorem taprod_inv {U : Subgroup X} (hUc : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x)
    {ρ : MulAut X} (hρU : ∀ x ∈ U, ρ x ∈ U) (hρ2 : ∀ x ∈ U, ρ (ρ x) = x)
    (hfree : ∀ a ∈ U, ρ a = a → a = 1) : ∀ x ∈ U, ρ x = x⁻¹ := fun x hx =>
  eq_inv_of_mul_eq_one_right (hfree _ (U.mul_mem hx (hρU x hx))
    (by rw [map_mul, hρ2 x hx, hUc _ (hρU x hx) x hx]))

theorem eq_or_eq_inv_of_mulAut_of_torus_factor {n : ℕ}
    (hodd : Odd n) {S U : Subgroup X} (hS : IsL2 S n ∨ IsSz S n) (hUS : U ≤ S)
    (hUc : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x) (hU4 : Nat.card U % 4 = 3)
    (hcent : ∀ a ∈ U, a ≠ 1 → centralizer ({a} : Set X) ⊓ S ≤ U) (σ : MulAut X)
    (hσ : ∃ k : ℕ, σ ^ 2 ^ k = 1) (hσS : S.map σ.toMonoidHom = S)
    (hσU : U.map σ.toMonoidHom = U) :
    (∀ x ∈ U, σ x = x) ∨ ∀ x ∈ U, σ x = x⁻¹ := by
  obtain ⟨k, hk⟩ := hσ
  have hpow := taprod_pow_mem fun x hx => (taprod_mem_iff hσU x).1 hx
  have hF : ∀ {r : ℕ} {a : X}, a ∈ U → a ≠ 1 → (σ ^ r) a = a → ∀ x ∈ U, (σ ^ r) x = x :=
    fun ha ha1 hfix => taprod_fix hodd hS hUS hUc hcent hk (taprod_mem_iff hσS) ha ha1 hfix
  have hsq : ∀ i : ℕ, ∀ x, (σ ^ 2 ^ (i + 1)) x = (σ ^ 2 ^ i) ((σ ^ 2 ^ i) x) := fun i x => by
    rw [pow_succ, pow_mul, sq, MulAut.mul_apply]
  suffices key : ∀ j : ℕ, (∀ x ∈ U, (σ ^ 2 ^ j) x = x) →
      (∀ x ∈ U, σ x = x) ∨ ∀ x ∈ U, σ x = x⁻¹ from
    key k fun x _ => by rw [hk, MulAut.one_apply]
  intro j
  induction j with
  | zero => exact fun h => Or.inl fun x hx => by simpa using h x hx
  | succ j ih =>
    intro h
    by_cases hρ : ∀ x ∈ U, (σ ^ 2 ^ j) x = x
    · exact ih hρ
    have hinv : ∀ x ∈ U, (σ ^ 2 ^ j) x = x⁻¹ :=
      taprod_inv hUc (hpow _) (fun x hx => (hsq j x).symm.trans (h x hx))
        fun a ha hfix => Classical.byContradiction fun ha1 => hρ (hF ha ha1 hfix)
    rcases j with _ | j
    · exact Or.inr fun x hx => by simpa using hinv x hx
    · exact (not_forall_apply_apply_eq_inv_of_card_mod_four hU4
        (fun x : U => ⟨(σ ^ 2 ^ j) x, hpow _ x x.2⟩)
        fun x => Subtype.ext ((hsq j x).symm.trans (hinv x x.2))).elim

end Factor

section Product

variable {X : Type} [Group X]

private theorem taprod_simple {Y : Type} [Group Y] {n : ℕ} (h : IsL2 Y n ∨ IsSz Y n) :
    IsSimpleGroup Y ∧ ∃ a b : Y, a * b ≠ b * a := by
  rcases h with h | h
  · exact ⟨CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (t := .PSL) (by decide) h,
      CFSG.ComponentClassification.HarrisLit.nonabelian_of_lieModel_psl2 h⟩
  · exact ⟨CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 h,
      CFSG.LocalAnalysis.EvenBN.GMSK.exists_mul_ne_of_lieModel_twistedB2 h⟩

private theorem taprod_internal {n : ℕ} (hX : IsL2Square X n ∨ IsSzSquare X n) :
    ∃ S₁ S₂ : Subgroup X, S₁.Normal ∧ S₂.Normal ∧ S₁ ⊓ S₂ = ⊥ ∧ S₁ ⊔ S₂ = ⊤ ∧
      ((IsL2 S₁ n ∧ IsL2 S₂ n) ∨ (IsSz S₁ n ∧ IsSz S₂ n)) := by
  rcases hX with ⟨A, B, _, _, ⟨e⟩, hA, hB⟩ | ⟨A, B, _, _, ⟨e⟩, hA, hB⟩
  · exact ⟨_, _, CFSG.GroupTheory.prodFirstFactor_normal e,
      CFSG.GroupTheory.prodSecondFactor_normal e,
      CFSG.GroupTheory.prodFirstFactor_inf_prodSecondFactor e,
      CFSG.GroupTheory.prodFirstFactor_sup_prodSecondFactor e,
      Or.inl ⟨CFSG.Blueprint.LieModel.of_mulEquiv
          (CFSG.GroupTheory.prodFirstFactorMulEquiv e).symm hA,
        CFSG.Blueprint.LieModel.of_mulEquiv (CFSG.GroupTheory.prodSecondFactorMulEquiv e).symm hB⟩⟩
  · exact ⟨_, _, CFSG.GroupTheory.prodFirstFactor_normal e,
      CFSG.GroupTheory.prodSecondFactor_normal e,
      CFSG.GroupTheory.prodFirstFactor_inf_prodSecondFactor e,
      CFSG.GroupTheory.prodFirstFactor_sup_prodSecondFactor e,
      Or.inr ⟨CFSG.Blueprint.LieModel.of_mulEquiv
          (CFSG.GroupTheory.prodFirstFactorMulEquiv e).symm hA,
        CFSG.Blueprint.LieModel.of_mulEquiv (CFSG.GroupTheory.prodSecondFactorMulEquiv e).symm hB⟩⟩

private theorem taprod_fix_or_swap [Finite X] {S₁ S₂ : Subgroup X} (h₁ : S₁.Normal)
    (h₂ : S₂.Normal) (hcomm : ∀ x ∈ S₁, ∀ y ∈ S₂, x * y = y * x) (hinf : S₁ ⊓ S₂ = ⊥)
    (hsup : S₁ ⊔ S₂ = ⊤) [IsSimpleGroup S₁] [IsSimpleGroup S₂]
    (hnab₁ : ∃ a b : S₁, a * b ≠ b * a) (hnab₂ : ∃ a b : S₂, a * b ≠ b * a) (σ : MulAut X) :
    (S₁.map σ.toMonoidHom = S₁ ∧ S₂.map σ.toMonoidHom = S₂) ∨
      (S₁.map σ.toMonoidHom = S₂ ∧ S₂.map σ.toMonoidHom = S₁) := by
  have hS1 : S₁ ≠ ⊥ := (nontrivial_iff_ne_bot S₁).1 inferInstance
  have hS2 : S₂ ≠ ⊥ := (nontrivial_iff_ne_bot S₂).1 inferInstance
  have himg : ∀ S : Subgroup X, S.Normal → S ≠ ⊥ →
      S₁ ≤ S.map σ.toMonoidHom ∨ S₂ ≤ S.map σ.toMonoidHom := fun S hS hS0 => by
    have := hS.map σ.toMonoidHom σ.surjective
    exact CFSG.Quasithin.H13.QRC.le_or_le_of_normal hcomm hsup hnab₁ hnab₂
      (by rwa [Ne, map_eq_bot_iff_of_injective S (f := σ.toMonoidHom) σ.injective])
  have hc : ∀ S : Subgroup X, Nat.card (S.map σ.toMonoidHom) = Nat.card S := fun S =>
    card_map_of_injective σ.injective
  have hbot : ∀ S : Subgroup X, S ≠ ⊥ →
      ¬ (S ≤ S₁.map σ.toMonoidHom ∧ S ≤ S₂.map σ.toMonoidHom) := fun S hS h => by
    have hle := le_inf h.1 h.2
    rw [← map_inf _ _ _ σ.injective, hinf, Subgroup.map_bot] at hle
    exact hS (le_bot_iff.1 hle)
  rcases himg S₁ h₁ hS1 with h1 | h1 <;> rcases himg S₂ h₂ hS2 with h2 | h2
  · exact absurd ⟨h1, h2⟩ (hbot S₁ hS1)
  · exact Or.inl ⟨(eq_of_le_of_card_ge h1 (hc S₁).le).symm,
      (eq_of_le_of_card_ge h2 (hc S₂).le).symm⟩
  · have h12 := (card_le_of_le h1).trans (hc S₁).le
    have h21 := (card_le_of_le h2).trans (hc S₂).le
    exact Or.inr ⟨(eq_of_le_of_card_ge h1 ((hc S₁).trans_le h21)).symm,
      (eq_of_le_of_card_ge h2 ((hc S₂).trans_le h12)).symm⟩
  · exact absurd ⟨h1, h2⟩ (hbot S₂ hS2)

private theorem taprod_mod_four {n : ℕ} (hn : 2 ≤ n) : (2 ^ n - 1) % 4 = 3 := by
  obtain ⟨c, hc⟩ : 4 ∣ 2 ^ n := by simpa using (pow_dvd_pow 2 hn : 2 ^ 2 ∣ 2 ^ n)
  have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  omega

private theorem taprod_comm {T : Subgroup X} {n : ℕ} (hT : IsZModSq T n) :
    ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := fun x hx y hy =>
  congrArg Subtype.val (@mul_comm' T _ (isMulCommutative_of_isZModSq hT) ⟨x, hx⟩ ⟨y, hy⟩)

private theorem taprod_fix_sup {A B : Subgroup X} {ρ : MulAut X} (hA : ∀ x ∈ A, ρ x = x)
    (hB : ∀ x ∈ B, ρ x = x) : ∀ x ∈ A ⊔ B, ρ x = x := by
  have h : A ⊔ B ≤ ρ.toMonoidHom.eqLocus (MonoidHom.id X) :=
    sup_le (fun x hx => hA x hx) fun x hx => hB x hx
  exact fun x hx => h hx

private theorem taprod_inv_sup {T A B : Subgroup X} (hTc : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x)
    (hAT : A ≤ T) (hBT : B ≤ T) {ρ : MulAut X} (hA : ∀ x ∈ A, ρ x = x⁻¹)
    (hB : ∀ x ∈ B, ρ x = x⁻¹) : ∀ x ∈ A ⊔ B, ρ x = x⁻¹ := by
  let W : Subgroup X :=
    { carrier := {x | x ∈ T ∧ ρ x = x⁻¹}
      mul_mem' := fun {a b} ⟨haT, ha⟩ ⟨hbT, hb⟩ => ⟨T.mul_mem haT hbT, by
        rw [map_mul, ha, hb, ← mul_inv_rev, hTc b hbT a haT]⟩
      one_mem' := ⟨T.one_mem, by rw [map_one, inv_one]⟩
      inv_mem' := fun {a} ⟨haT, ha⟩ => ⟨T.inv_mem haT, by rw [map_inv, ha]⟩ }
  have h : A ⊔ B ≤ W := sup_le (fun x hx => (show x ∈ T ∧ ρ x = x⁻¹ from ⟨hAT hx, hA x hx⟩))
    fun x hx => (show x ∈ T ∧ ρ x = x⁻¹ from ⟨hBT hx, hB x hx⟩)
  exact fun x hx => (show x ∈ T ∧ ρ x = x⁻¹ from h hx).2

private theorem taprod_mixed [Finite X] {n : ℕ} {T A B : Subgroup X} (hT : T = A ⊔ B)
    (hBT : B ≤ T) (hB : Nat.card B = 2 ^ n - 1) {σ : MulAut X} (hA : ∀ x ∈ A, σ x = x)
    (hBi : ∀ x ∈ B, σ x = x⁻¹) :
    (∀ x ∈ T, σ (σ x) = x) ∧
      ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ 2 ^ n - 1 → ∃ x ∈ T, orderOf x = ℓ ∧ σ x = x⁻¹ := by
  refine ⟨fun x hx => taprod_fix_sup (ρ := σ * σ) (fun y hy => ?_) (fun y hy => ?_) x (hT.le hx),
    fun ℓ hℓ hℓm => ?_⟩
  · rw [MulAut.mul_apply, hA y hy, hA y hy]
  · rw [MulAut.mul_apply, hBi y hy, map_inv, hBi y hy, inv_inv]
  · have := Fact.mk hℓ
    obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := B) ℓ (by rw [hB]; exact hℓm)
    exact ⟨b, hBT b.2, by rw [orderOf_coe, hb], hBi b b.2⟩

private theorem taprod_nonswap [Finite X] {n : ℕ} {T T₁ T₂ : Subgroup X}
    (hTc : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x) (hTodd : Odd (Nat.card T)) (hT : T = T₁ ⊔ T₂)
    (h₁T : T₁ ≤ T) (h₂T : T₂ ≤ T) (hc₁ : Nat.card T₁ = 2 ^ n - 1)
    (hc₂ : Nat.card T₂ = 2 ^ n - 1) {σ : MulAut X} {t₀ : X} (ht₀T : t₀ ∈ T) (ht₀1 : t₀ ≠ 1)
    (hσt₀ : σ t₀ = t₀) (h₁ : (∀ x ∈ T₁, σ x = x) ∨ ∀ x ∈ T₁, σ x = x⁻¹)
    (h₂ : (∀ x ∈ T₂, σ x = x) ∨ ∀ x ∈ T₂, σ x = x⁻¹) :
    (∀ x ∈ T, σ x = x) ∨ ((∀ x ∈ T, σ (σ x) = x) ∧
      ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ 2 ^ n - 1 → ∃ x ∈ T, orderOf x = ℓ ∧ σ x = x⁻¹) := by
  rcases h₁ with hf₁ | hi₁ <;> rcases h₂ with hf₂ | hi₂
  · exact Or.inl fun x hx => taprod_fix_sup hf₁ hf₂ x (hT.le hx)
  · exact Or.inr (taprod_mixed hT h₂T hc₂ hf₁ hi₂)
  · exact Or.inr (taprod_mixed (hT.trans (sup_comm _ _)) h₁T hc₁ hf₂ hi₁)
  · exfalso
    have h := taprod_inv_sup hTc h₁T h₂T hi₁ hi₂ t₀ (hT.le ht₀T)
    rw [hσt₀] at h
    exact ht₀1 (taprod_eq_one_of_mul_self hTodd (T.orderOf_dvd_natCard ht₀T)
      (inv_eq_iff_mul_eq_one.1 h.symm))

private theorem taprod_swap_elt [Finite X] {n : ℕ} {T S₁ S₂ : Subgroup X}
    (hTc : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x) (hinf : S₁ ⊓ S₂ = ⊥)
    (hc₁ : Nat.card (T ⊓ S₁ : Subgroup X) = 2 ^ n - 1) {σ : MulAut X}
    (hσ : ∀ x ∈ T ⊓ S₁, σ x ∈ T ⊓ S₂) (hfT : ∀ x ∈ T, σ (σ x) = x) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓm : ℓ ∣ 2 ^ n - 1) : ∃ x ∈ T, orderOf x = ℓ ∧ σ x = x⁻¹ := by
  have := Fact.mk hℓ
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := ↥(T ⊓ S₁)) ℓ (by rw [hc₁]; exact hℓm)
  have ha' : orderOf (a : X) = ℓ := by rw [orderOf_coe, ha]
  have hσa := hσ a a.2
  have hcomm : Commute (a : X) (σ a)⁻¹ := hTc _ a.2.1 _ (T.inv_mem hσa.1)
  have hapow : (a : X) ^ ℓ = 1 := ha' ▸ pow_orderOf_eq_one (a : X)
  refine ⟨a * (σ a)⁻¹, T.mul_mem a.2.1 (T.inv_mem hσa.1), orderOf_eq_prime ?_ ?_, ?_⟩
  · rw [hcomm.mul_pow, inv_pow, ← map_pow, hapow, map_one, inv_one, one_mul]
  · intro h1
    rw [mul_inv_eq_one] at h1
    have h0 : (a : X) ∈ S₁ ⊓ S₂ := ⟨a.2.2, by rw [h1]; exact hσa.2⟩
    rw [hinf, mem_bot] at h0
    rw [h0, orderOf_one] at ha'
    exact hℓ.one_lt.ne ha'
  · rw [map_mul, map_inv, hfT a a.2.1, mul_inv_rev, inv_inv]

private theorem taprod_swap [Finite X] {n : ℕ} {T S₁ S₂ : Subgroup X}
    (hTc : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x) (hTodd : Odd (Nat.card T)) (hinf : S₁ ⊓ S₂ = ⊥)
    (hT : T = T ⊓ S₁ ⊔ T ⊓ S₂) (hc₁ : Nat.card (T ⊓ S₁ : Subgroup X) = 2 ^ n - 1)
    {σ : MulAut X} (hσT : T.map σ.toMonoidHom = T) (hσ₁ : S₁.map σ.toMonoidHom = S₂)
    {t₀ : X} (ht₀T : t₀ ∈ T) (ht₀1 : t₀ ≠ 1) (hσt₀ : σ t₀ = t₀)
    (h : (∀ x ∈ T ⊓ S₁, σ (σ x) = x) ∨ ∀ x ∈ T ⊓ S₁, σ (σ x) = x⁻¹) :
    (∀ x ∈ T, σ x = x) ∨ ((∀ x ∈ T, σ (σ x) = x) ∧
      ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ 2 ^ n - 1 → ∃ x ∈ T, orderOf x = ℓ ∧ σ x = x⁻¹) := by
  have hT₁₂ : (T ⊓ S₁).map σ.toMonoidHom = T ⊓ S₂ := by
    rw [map_inf _ _ _ σ.injective, hσT, hσ₁]
  have hpre : ∀ y ∈ T ⊓ S₂, ∃ x ∈ T ⊓ S₁, σ x = y := fun y hy => by
    rw [← hT₁₂] at hy
    obtain ⟨x, hx, rfl⟩ := mem_map.1 hy
    exact ⟨x, hx, rfl⟩
  have hσ : ∀ x ∈ T ⊓ S₁, σ x ∈ T ⊓ S₂ := fun x hx => by
    rw [← hT₁₂]
    exact mem_map_of_mem σ.toMonoidHom hx
  rcases h with hf₁ | hi₁
  · have hf₂ : ∀ y ∈ T ⊓ S₂, σ (σ y) = y := fun y hy => by
      obtain ⟨x, hx, rfl⟩ := hpre y hy
      rw [hf₁ x hx]
    have hfT : ∀ x ∈ T, σ (σ x) = x := fun x hx =>
      taprod_fix_sup (ρ := σ * σ) hf₁ hf₂ x (hT.le hx)
    exact Or.inr ⟨hfT, fun ℓ hℓ hℓm => taprod_swap_elt hTc hinf hc₁ hσ hfT hℓ hℓm⟩
  · exfalso
    have hi₂ : ∀ y ∈ T ⊓ S₂, σ (σ y) = y⁻¹ := fun y hy => by
      obtain ⟨x, hx, rfl⟩ := hpre y hy
      rw [hi₁ x hx, map_inv]
    have h := taprod_inv_sup hTc inf_le_left inf_le_left (ρ := σ * σ) hi₁ hi₂ t₀ (hT.le ht₀T)
    rw [MulAut.mul_apply, hσt₀, hσt₀] at h
    exact ht₀1 (taprod_eq_one_of_mul_self hTodd (T.orderOf_dvd_natCard ht₀T)
      (inv_eq_iff_mul_eq_one.1 h.symm))

end Product

theorem k_19_28_torusAutomizer_internal_prod {X : Type}
    [Group X] [Finite X] {n : ℕ} (hn : 3 ≤ n) (hodd : Odd n) {T : Subgroup X}
    (hT : IsZModSq T n) (S₁ S₂ : Subgroup X) (h₁ : S₁.Normal) (h₂ : S₂.Normal)
    (hinf : S₁ ⊓ S₂ = ⊥) (hsup : S₁ ⊔ S₂ = ⊤)
    (hS : (IsL2 S₁ n ∧ IsL2 S₂ n) ∨ (IsSz S₁ n ∧ IsSz S₂ n)) (σ : MulAut X)
    (hσ : ∃ k : ℕ, orderOf σ = 2 ^ k) (hσT : T.map σ.toMonoidHom = T)
    (ht₀ : ∃ t₀ ∈ T, t₀ ≠ 1 ∧ σ t₀ = t₀) :
    (∀ x ∈ T, σ x = x) ∨ ((∀ x ∈ T, σ (σ x) = x) ∧
      ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ 2 ^ n - 1 → ∃ x ∈ T, orderOf x = ℓ ∧ σ x = x⁻¹) := by
  obtain ⟨t₀, ht₀T, ht₀1, hσt₀⟩ := ht₀
  obtain ⟨k, hk⟩ := hσ
  have hσk : σ ^ 2 ^ k = 1 := by rw [← hk]; exact pow_orderOf_eq_one σ
  obtain ⟨hS₁, hS₂⟩ : (IsL2 S₁ n ∨ IsSz S₁ n) ∧ (IsL2 S₂ n ∨ IsSz S₂ n) :=
    hS.elim (fun h => ⟨Or.inl h.1, Or.inl h.2⟩) fun h => ⟨Or.inr h.1, Or.inr h.2⟩
  obtain ⟨hc₁, hc₂, hTsup⟩ := torus_eq_sup_inf_of_prod (by omega) hT S₁ S₂ h₁ h₂ hinf hsup hS
  obtain ⟨hC₁, hC₂⟩ := inf_eq_centralizer_inf_of_prod (by omega) hT S₁ S₂ h₁ h₂ hinf hsup hS
  have hm4 := taprod_mod_four (n := n) (by omega)
  have hTc := taprod_comm hT
  have hTodd : Odd (Nat.card T) := by
    rw [card_eq_of_isZModSq hT]
    exact (Nat.odd_iff.2 (by omega)).mul (Nat.odd_iff.2 (by omega))
  have hdich : ∀ {S : Subgroup X}, (IsL2 S n ∨ IsSz S n) →
      Nat.card (T ⊓ S : Subgroup X) = 2 ^ n - 1 →
      (∀ a ∈ T ⊓ S, a ≠ 1 → T ⊓ S = centralizer ({a} : Set X) ⊓ S) →
      ∀ ρ : MulAut X, ρ ^ 2 ^ k = 1 → S.map ρ.toMonoidHom = S → T.map ρ.toMonoidHom = T →
      (∀ x ∈ T ⊓ S, ρ x = x) ∨ ∀ x ∈ T ⊓ S, ρ x = x⁻¹ := fun hS hc hC ρ hρ hρS hρT =>
    eq_or_eq_inv_of_mulAut_of_torus_factor hodd hS inf_le_right
      (fun x hx y hy => hTc x hx.1 y hy.1) (by rw [hc]; exact hm4)
      (fun a ha ha1 => (hC a ha ha1).ge) ρ ⟨k, hρ⟩ hρS
      (by rw [map_inf _ _ _ ρ.injective, hρT, hρS])
  obtain ⟨hs₁, hnab₁⟩ := taprod_simple hS₁
  obtain ⟨hs₂, hnab₂⟩ := taprod_simple hS₂
  have hcomm : ∀ x ∈ S₁, ∀ y ∈ S₂, x * y = y * x := fun x hx y hy =>
    commute_of_normal_of_disjoint S₁ S₂ h₁ h₂ (disjoint_iff.2 hinf) x y hx hy
  rcases taprod_fix_or_swap h₁ h₂ hcomm hinf hsup hnab₁ hnab₂ σ with ⟨hσ₁, hσ₂⟩ | ⟨hσ₁, hσ₂⟩
  · exact taprod_nonswap hTc hTodd hTsup inf_le_left inf_le_left hc₁ hc₂ ht₀T ht₀1 hσt₀
      (hdich hS₁ hc₁ hC₁ σ hσk hσ₁ hσT) (hdich hS₂ hc₂ hC₂ σ hσk hσ₂ hσT)
  · have hmap : ∀ H : Subgroup X,
        H.map (σ * σ).toMonoidHom = (H.map σ.toMonoidHom).map σ.toMonoidHom := fun H => by
      rw [map_map]
      rfl
    have hρk : (σ * σ) ^ 2 ^ k = 1 := by rw [← sq, ← pow_mul, pow_mul', hσk, one_pow]
    exact taprod_swap hTc hTodd hinf hTsup hc₁ hσT hσ₁ ht₀T ht₀1 hσt₀
      (hdich hS₁ hc₁ hC₁ (σ * σ) hρk (by rw [hmap, hσ₁, hσ₂]) (by rw [hmap, hσT, hσT]))

theorem k_19_28_torusAutomizer_prod
    {X : Type} [Group X] [Finite X] {n : ℕ} (hn : 3 ≤ n) (hodd : Odd n)
    (hX : IsL2Square X n ∨ IsSzSquare X n) {T : Subgroup X} (hT : IsZModSq T n)
    (σ : MulAut X) (hσ : ∃ k : ℕ, orderOf σ = 2 ^ k) (hσT : T.map σ.toMonoidHom = T)
    (ht₀ : ∃ t₀ ∈ T, t₀ ≠ 1 ∧ σ t₀ = t₀) :
    (∀ x ∈ T, σ x = x) ∨ ((∀ x ∈ T, σ (σ x) = x) ∧
      ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ 2 ^ n - 1 → ∃ x ∈ T, orderOf x = ℓ ∧ σ x = x⁻¹) := by
  obtain ⟨S₁, S₂, h₁, h₂, hinf, hsup, hS⟩ := taprod_internal hX
  exact k_19_28_torusAutomizer_internal_prod hn hodd hT S₁ S₂ h₁ h₂ hinf hsup hS σ hσ hσT ht₀

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
