module

public import CFSG.LieType.BorelTits.FormFlag
public import CFSG.RankThree.PartOne.KF.RankGL

public section

namespace CFSG.RankThree.PartOne.KFU

open CFSG.LieType.BorelTits Module

namespace FlagSplit

@[expose] def repAut {K : Type} [Field K] {G X : Type*} [Group G] [AddCommGroup X] [Module K X]
    (ρ : G →* Module.End K X) : G →* (X ≃ₗ[K] X) where
  toFun g :=
    { toFun := ρ g
      map_add' := map_add (ρ g)
      map_smul' := map_smul (ρ g)
      invFun := ρ g⁻¹
      left_inv := fun x => by
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
      right_inv := fun x => by
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] }
  map_one' := LinearEquiv.ext fun x => by simp
  map_mul' g h := LinearEquiv.ext fun x => by simp

@[expose] def quotRep {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    {G : Type*} [Monoid G] (ρ : G →* Module.End K V) (A B : Submodule K V)
    (hA : ∀ g : G, ∀ v ∈ A, ρ g v ∈ A) (hB : ∀ g : G, ∀ v ∈ B, ρ g v ∈ B) :
    G →* Module.End K (B ⧸ A.comap B.subtype) where
  toFun g := (A.comap B.subtype).mapQ (A.comap B.subtype) ((ρ g).restrict (hB g))
    fun v hv => hA g v hv
  map_one' := by
    apply Submodule.linearMap_qext
    ext v
    simp [LinearMap.restrict_apply]
  map_mul' g h := by
    apply Submodule.linearMap_qext
    ext v
    simp only [map_mul]
    rfl

abbrev perpQuot {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    (F : ReflForm K V) (W : Submodule K V) : Type :=
  ↥(F.perp W) ⧸ W.comap (F.perp W).subtype

theorem finrank_perpQuot {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (F : ReflForm K V) {W : Submodule K V} (hW : F.IsTotallyIsotropic W) :
    finrank K (perpQuot F W) = finrank K V - 2 * finrank K W := by
  have h1 := F.finrank_perp W
  have h2 : finrank K (perpQuot F W) + finrank K (W.comap (F.perp W).subtype) =
      finrank K (F.perp W) := Submodule.finrank_quotient_add_finrank _
  have h3 : finrank K (W.comap (F.perp W).subtype) = finrank K W :=
    (Submodule.comapSubtypeEquivOfLe hW).finrank_eq
  omega

theorem finite_linearEquiv {K : Type} [Field K] [Finite K] {X : Type*} [AddCommGroup X]
    [Module K X] [FiniteDimensional K X] : Finite (X ≃ₗ[K] X) := by
  have : Finite X := Module.finite_of_finite K
  exact Finite.of_injective (fun f : X ≃ₗ[K] X => (f : X → X)) DFunLike.coe_injective

theorem card_le_card_range_mul {G A B : Type*} [Group G] [Group A] [Group B] [Finite A]
    [Finite B] (f : G →* A) (g : G →* B) (h : ∀ x, f x = 1 → g x = 1 → x = 1) :
    Nat.card G ≤ Nat.card f.range * Nat.card g.range := by
  have hinj : Function.Injective
      (fun x : G => ((⟨f x, x, rfl⟩ : f.range), (⟨g x, x, rfl⟩ : g.range))) := by
    intro x y hxy
    simp only [Prod.mk.injEq] at hxy
    obtain ⟨h1, h2⟩ := hxy
    have h1' : f x = f y := congrArg Subtype.val h1
    have h2' : g x = g y := congrArg Subtype.val h2
    exact mul_inv_eq_one.mp (h (x * y⁻¹) (by rw [map_mul, map_inv, h1', mul_inv_cancel])
      (by rw [map_mul, map_inv, h2', mul_inv_cancel]))
  rw [← Nat.card_prod]
  exact Nat.card_le_card_of_injective _ hinj

theorem card_range_le_pow_div {K : Type} [Field K] [Finite K] {G : Type*} [Group G] {X : Type}
    [AddCommGroup X] [Module K X] [FiniteDimensional K X] (ψ : G →* (X ≃ₗ[K] X)) {p : ℕ}
    (hp : p.Prime) (hpK : (p : K) ≠ 0) {d : ℕ} (hd : 0 < d)
    (hdiv : ∀ i : ℕ, 0 < i → i < d → ¬ p ∣ Nat.card K ^ i - 1)
    (hcomm : ∀ g h : G, g * h = h * g) (hexp : ∀ g : G, g ^ p = 1) :
    Nat.card ψ.range ≤ p ^ (finrank K X / d) :=
  LIT.card_le_pow_div hp hpK hd hdiv ψ.range
    (by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      rw [← map_mul, ← map_mul, hcomm])
    (by
      rintro _ ⟨a, rfl⟩
      rw [← map_pow, hexp, map_one])

theorem eq_one_of_fixes_flag {K : Type} [Field K] [CharP K 2] {V : Type} [AddCommGroup V]
    [Module K V] {H : Type} [Group H] (F : ReflForm K V) (ρ : H →* Module.End K V)
    (hρ : IsIsometric F ρ) (hinj : Function.Injective ρ) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {g : H} (hgp : g ^ p = 1) {W : Submodule K V} (hW : ∀ w ∈ W, ρ g w = w)
    (hM : ∀ v ∈ F.perp W, ρ g v - v ∈ W) : g = 1 := by
  have h2 : ∀ x : V, x + x = 0 := fun x => by
    rw [← two_smul K x, show (2 : K) = 0 by simpa using CharP.cast_eq_zero K 2, zero_smul]
  have hperp : ∀ v : V, ρ g v - v ∈ F.perp W := by
    intro v w hw
    have h1 := hρ g w v
    rw [hW w hw] at h1
    rw [F.β_sub_right, h1, sub_self]
  have hsq : ∀ v : V, ∃ c ∈ W, ρ g (ρ g v) = v + c := by
    intro v
    refine ⟨ρ g (ρ g v - v) - (ρ g v - v), hM _ (hperp v), ?_⟩
    have e : v + (ρ g (ρ g v - v) - (ρ g v - v)) =
        ρ g (ρ g v) + (v + v) - (ρ g v + ρ g v) := by
      rw [map_sub]
      abel
    rw [e, h2 v, h2 (ρ g v), add_zero, sub_zero]
  have hfour : ∀ v : V, ρ g (ρ g (ρ g (ρ g v))) = v := by
    intro v
    obtain ⟨c, hcW, hc⟩ := hsq v
    have hcfix : ρ g c = c := hW c hcW
    rw [hc, map_add, map_add, hcfix, hcfix, hc, add_assoc, h2 c, add_zero]
  have hg4 : g ^ 4 = 1 := by
    apply hinj
    apply LinearMap.ext
    intro v
    have e : g ^ 4 = g * g * g * g := by simp [pow_succ]
    rw [e]
    simpa using hfour v
  have hcop : Nat.Coprime 4 p := by
    have h2p : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)
    simpa using Nat.Coprime.pow_left 2 h2p
  exact (pow_eq_one_iff_of_coprime hcop).mp ⟨hg4, hgp⟩

end FlagSplit

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {H : Type} [Group H]

theorem exists_invariant_isotropic [CharP K 2] (F : ReflForm K V) (ρ : H →* Module.End K V)
    (hρ : IsIsometric F ρ) (hinj : Function.Injective ρ) {R E : Subgroup H}
    (hR : IsPGroup 2 R) (hR1 : R ≠ ⊥) (hE : E ≤ Subgroup.normalizer (R : Set H)) :
    ∃ W : Submodule K V, W ≠ ⊥ ∧ F.IsTotallyIsotropic W ∧ ∀ g ∈ E, ∀ w ∈ W, ρ g w ∈ W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite V := Module.finite_of_finite K
  exact ⟨isoSeq F ρ R 1, isoSeq_one_ne_bot F ρ 2 hρ hinj R hR hR1,
    isoSeq_isTotallyIsotropic F ρ R 1, fun g hg w hw => apply_mem_isoSeq F ρ hρ R 1 (hE hg) hw⟩

theorem card_le_of_invariant_isotropic [CharP K 2] (F : ReflForm K V) (ρ : H →* Module.End K V)
    (hρ : IsIsometric F ρ) (hinj : Function.Injective ρ) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : (p : K) ≠ 0) {d : ℕ} (hd : 0 < d)
    (hdiv : ∀ i : ℕ, 0 < i → i < d → ¬ p ∣ Nat.card K ^ i - 1)
    (E : Subgroup H) (hcomm : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g) (hexp : ∀ g ∈ E, g ^ p = 1)
    (W : Submodule K V) (hW : F.IsTotallyIsotropic W) (hWE : ∀ g ∈ E, ∀ w ∈ W, ρ g w ∈ W) :
    Nat.card E ≤ p ^ (finrank K W / d) * p ^ ((finrank K V - 2 * finrank K W) / d) := by
  have hWinv : ∀ g ∈ E, ∀ w ∈ W, ρ g⁻¹ w ∈ W := fun g hg => hWE g⁻¹ (inv_mem hg)
  have hPinv : ∀ g ∈ E, ∀ v ∈ F.perp W, ρ g v ∈ F.perp W :=
    fun g hg v hv => hρ.apply_mem_perp_of_forall (hWinv g hg) hv
  let ρE : E →* Module.End K V := ρ.comp E.subtype
  have hW' : ∀ g : E, ∀ w ∈ W, ρE g w ∈ W := fun g w hw => hWE g g.2 w hw
  have hP' : ∀ g : E, ∀ v ∈ F.perp W, ρE g v ∈ F.perp W := fun g v hv => hPinv g g.2 v hv
  let ρW : E →* (W ≃ₗ[K] W) := LIT.restrictAction (FlagSplit.repAut ρE) W hW'
  let ρM : E →* (FlagSplit.perpQuot F W ≃ₗ[K] FlagSplit.perpQuot F W) :=
    FlagSplit.repAut (FlagSplit.quotRep ρE W (F.perp W) hW' hP')
  have hker : ∀ g : E, ρW g = 1 → ρM g = 1 → g = 1 := by
    intro g h1 h2
    refine Subtype.ext (FlagSplit.eq_one_of_fixes_flag F ρ hρ hinj hp hp2 (hexp g g.2)
      (W := W) ?_ ?_)
    · intro w hw
      exact congrArg Subtype.val (LinearEquiv.congr_fun h1 ⟨w, hw⟩)
    · intro v hv
      have h3 : (Submodule.Quotient.mk ⟨ρ g v, hPinv g g.2 v hv⟩ : FlagSplit.perpQuot F W) =
          Submodule.Quotient.mk ⟨v, hv⟩ :=
        LinearEquiv.congr_fun h2 (Submodule.Quotient.mk ⟨v, hv⟩)
      exact (Submodule.Quotient.eq (W.comap (F.perp W).subtype)).mp h3
  have hcommE : ∀ g h : E, g * h = h * g := fun g h => Subtype.ext (hcomm g g.2 h h.2)
  have hexpE : ∀ g : E, g ^ p = 1 := fun g => Subtype.ext (hexp g g.2)
  have : Finite (W ≃ₗ[K] W) := FlagSplit.finite_linearEquiv (K := K)
  have : Finite (FlagSplit.perpQuot F W ≃ₗ[K] FlagSplit.perpQuot F W) :=
    FlagSplit.finite_linearEquiv (K := K)
  calc Nat.card E ≤ Nat.card ρW.range * Nat.card ρM.range :=
        FlagSplit.card_le_card_range_mul ρW ρM hker
    _ ≤ p ^ (finrank K W / d) * p ^ (finrank K (FlagSplit.perpQuot F W) / d) :=
        Nat.mul_le_mul (FlagSplit.card_range_le_pow_div ρW hp hpK hd hdiv hcommE hexpE)
          (FlagSplit.card_range_le_pow_div ρM hp hpK hd hdiv hcommE hexpE)
    _ = p ^ (finrank K W / d) * p ^ ((finrank K V - 2 * finrank K W) / d) := by
        rw [FlagSplit.finrank_perpQuot F hW]

theorem card_le_of_normalizes [CharP K 2] (F : ReflForm K V) (ρ : H →* Module.End K V)
    (hρ : IsIsometric F ρ) (hinj : Function.Injective ρ) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : (p : K) ≠ 0) {d : ℕ} (hd : 0 < d)
    (hdiv : ∀ i : ℕ, 0 < i → i < d → ¬ p ∣ Nat.card K ^ i - 1)
    {R E : Subgroup H} (hR : IsPGroup 2 R) (hR1 : R ≠ ⊥)
    (hE : E ≤ Subgroup.normalizer (R : Set H)) (hcomm : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g)
    (hexp : ∀ g ∈ E, g ^ p = 1) :
    ∃ a : ℕ, 1 ≤ a ∧ 2 * a ≤ finrank K V ∧
      Nat.card E ≤ p ^ (a / d) * p ^ ((finrank K V - 2 * a) / d) := by
  obtain ⟨W, hW0, hWiso, hWE⟩ := exists_invariant_isotropic F ρ hρ hinj hR hR1 hE
  have h1 : 1 ≤ finrank K W := Submodule.one_le_finrank_iff.mpr hW0
  have h2 := F.finrank_perp W
  have h3 : finrank K W ≤ finrank K (F.perp W) := Submodule.finrank_mono hWiso
  exact ⟨finrank K W, h1, by omega,
    card_le_of_invariant_isotropic F ρ hρ hinj hp hp2 hpK hd hdiv E hcomm hexp W hWiso hWE⟩

end CFSG.RankThree.PartOne.KFU
