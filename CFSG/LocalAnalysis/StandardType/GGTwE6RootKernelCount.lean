module

public import CFSG.LocalAnalysis.StandardType.GGTwE6RootKillWeyl
public import CFSG.LocalAnalysis.StandardType.GGTwE6RootAsCoreDefs
public import CFSG.LieType.Chevalley.KernelComponentRoots

public section

namespace CFSG.StandardType.TwE6RootKill

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint

section Prime

theorem exists_intCast_ne_zero_of_isRoot {τ : Tag} {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    (p : ℕ) [Fact p.Prime] : ∃ k, ((β k : ℤ) : ZMod p) ≠ 0 := by
  induction hβ with
  | basis j => exact ⟨j, by simp⟩
  | @reflect i v _ ih =>
    obtain ⟨k, hk⟩ := ih
    by_contra hall
    push Not at hall
    have hoff : ∀ j, j ≠ i → ((v j : ℤ) : ZMod p) = 0 := fun j hj => by
      simpa [reflect, Pi.single_apply, hj] using hall j
    have hsum : ((∑ j, τ.cartan i j * v j : ℤ) : ZMod p) = 2 * ((v i : ℤ) : ZMod p) := by
      push_cast
      rw [Finset.sum_eq_single i (fun j _ hj => by rw [hoff j hj, mul_zero])
        (fun h => absurd (Finset.mem_univ i) h), Tag.cartan_self]
      push_cast
      ring
    have hii := hall i
    simp only [reflect, Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one,
      Int.cast_sub] at hii
    rw [hsum] at hii
    have hvi : ((v i : ℤ) : ZMod p) = 0 := by linear_combination -hii
    by_cases hki : k = i
    · exact hk (hki ▸ hvi)
    · exact hk (hoff k hki)

theorem card_hyperplane_le {p : ℕ} [Fact p.Prime] {n : ℕ} (u : Fin n → ℤ) {k : Fin n}
    (hk : ((u k : ℤ) : ZMod p) ≠ 0) :
    Nat.card {y : Fin n → ZMod p // ∑ j, y j * (u j : ZMod p) = 0} ≤ p ^ (n - 1) := by
  classical
  let L : (Fin n → ZMod p) →ₗ[ZMod p] ZMod p :=
    { toFun := fun y => ∑ j, y j * (u j : ZMod p)
      map_add' := fun y y' => by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun c y => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc] }
  have hL : ∀ y, L y = ∑ j, y j * (u j : ZMod p) := fun y => rfl
  have hsurj : Function.Surjective L := by
    intro c
    refine ⟨Pi.single k (c * ((u k : ℤ) : ZMod p)⁻¹), ?_⟩
    rw [hL, Finset.sum_eq_single k (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_mul])
      (fun h => absurd (Finset.mem_univ k) h), Pi.single_eq_same, mul_assoc,
      inv_mul_cancel₀ hk, mul_one]
  have hrank := LinearMap.finrank_range_add_finrank_ker L
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_self,
    Module.finrank_fin_fun] at hrank
  have hker : Nat.card (LinearMap.ker L) = p ^ (n - 1) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
    congr 1
    omega
  have hinj : Function.Injective (fun y : {y : Fin n → ZMod p // ∑ j, y j * (u j : ZMod p) = 0} =>
      (⟨y.1, LinearMap.mem_ker.2 ((hL y.1).trans y.2)⟩ : LinearMap.ker L)) := by
    intro y y' h
    apply Subtype.ext
    simpa using congrArg Subtype.val h
  exact (Nat.card_le_card_of_injective _ hinj).trans hker.le

end Prime

section Coroot

theorem zpow_pow_eq_one_rk {L : Type} [Field L] {p : ℕ} {ζ : Lˣ} (hζ : ζ ^ p = 1) (m : ℤ) :
    (ζ ^ m) ^ p = 1 := by
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζ, one_zpow]

theorem exists_zpow_val_eq_rk {L : Type} [Field L] {p : ℕ} [NeZero p] {ζ : Lˣ}
    (hζ : IsPrimitiveRoot ζ p) {a : Fin TwistTag.E6.tag.rank → Lˣ} (ha : ∀ k, a k ^ p = 1) :
    ∃ y : Fin TwistTag.E6.tag.rank → ZMod p, (fun k => ζ ^ ((y k).val : ℤ)) = a := by
  have hlog : ∀ k, ∃ e : ℕ, e < p ∧ ζ ^ e = a k := fun k =>
    hζ.eq_pow_of_mem_rootsOfUnity ((mem_rootsOfUnity p (a k)).2 (ha k))
  choose e he hea using hlog
  exact ⟨fun k => (e k : ZMod p), funext fun k => by
    rw [ZMod.val_cast_of_lt (he k), zpow_natCast, hea k]⟩

theorem symmetrizedCartan_twE6 : TwistTag.E6.tag.symmetrizedCartan = TwistTag.E6.tag.cartan := by
  rw [Tag.symmetrizedCartan, show TwistTag.E6.tag.symmetrizer = 1 from rfl, Matrix.one_mul]

theorem rootChar_corootTuple {L : Type} [Field L] (γ β : Fin TwistTag.E6.tag.rank → ℤ)
    (ζ : Lˣ) : rootChar (TwE6RootAs.corootTuple γ ζ) β = ζ ^ iform β γ := by
  rw [show TwE6RootAs.corootTuple γ ζ =
    fun k => ζ ^ (∑ l, TwistTag.E6.tag.cartan k l * γ l) from rfl, rootChar_zpow_wk]
  congr 1
  simp only [iform, symmetrizedCartan_twE6, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

theorem iform_single_single_twE6 (i j : Fin TwistTag.E6.tag.rank) :
    iform (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ) (Pi.single j 1) =
      TwistTag.E6.tag.cartan i j := by
  simp [iform, Pi.single_apply, symmetrizedCartan_twE6]

theorem exists_root_iform_eq_zero
    {β : Fin TwistTag.E6.tag.rank → ℤ} (hβ : IsRoot TwistTag.E6.tag β) :
    ∃ γ, IsRoot TwistTag.E6.tag γ ∧ iform γ β = 0 := by
  obtain ⟨w, j, rfl⟩ := isRoot_iff_exists_smul_single.1 hβ
  refine ⟨w • Pi.single (if (j : ℕ) = 0 ∨ (j : ℕ) = 2 then ⟨1, by decide⟩ else ⟨0, by decide⟩) 1,
    IsRoot.smul (IsRoot.basis _) w, ?_⟩
  rw [iform_smul, iform_single_single_twE6]
  clear hβ
  revert j
  decide

end Coroot

end CFSG.StandardType.TwE6RootKill

end
