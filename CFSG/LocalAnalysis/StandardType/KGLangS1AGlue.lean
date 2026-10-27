module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangKGInputs
import CFSG.LocalAnalysis.StandardType.KGLangTorAGeneric
import CFSG.LocalAnalysis.StandardType.GGD4OddCentVocab

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem kgLangS1A_setup_eq {R : Type} [Group R] {I : Set (MulAut R)} {K : Type} [Group K]
    [Finite K] (θ : K ⧸ Subgroup.center K ≃* R) (hK : commutator K = ⊤)
    {A B₀ : Subgroup (MulAut K)} {X : Subgroup (MulAut R)} {u₀ : MulAut R}
    (hmem : ∀ α ∈ A, kgInducedAut θ α ∈ I → α ∈ B₀)
    (hXcard : Nat.card X = Nat.card {α : MulAut K // α ∈ A ∧ kgInducedAut θ α ∈ I})
    (hXβ : ∀ β ∈ B₀, u₀⁻¹ * kgInducedAut θ β * u₀ ∈ X) :
    (∀ β ∈ B₀, β ∈ A ∧ kgInducedAut θ β ∈ I) ∧
      X = B₀.map ((MulAut.conj u₀⁻¹).toMonoidHom.comp (kgInducedAut θ)) := by
  classical
  haveI hfinK : Finite (MulAut K) :=
    Finite.of_injective (fun f : MulAut K => (f : K → K)) DFunLike.coe_injective
  haveI hfinR : Finite R := Finite.of_injective θ.symm θ.symm.injective
  haveI hfinMR : Finite (MulAut R) :=
    Finite.of_injective (fun f : MulAut R => (f : R → R)) DFunLike.coe_injective
  let φ : MulAut K →* MulAut R := (MulAut.conj u₀⁻¹).toMonoidHom.comp (kgInducedAut θ)
  have hinjθ : Function.Injective (kgInducedAut θ) := ggInducedAut_injective_of_perfect hK θ
  have hφβ : ∀ β : MulAut K, φ β = u₀⁻¹ * kgInducedAut θ β * u₀ := fun β => by
    change (MulAut.conj u₀⁻¹) (kgInducedAut θ β) = _
    rw [MulAut.conj_apply, inv_inv]
  have hXβ' : ∀ β ∈ B₀, φ β ∈ X := fun β hβ => by rw [hφβ]; exact hXβ β hβ
  have hinjφ : Function.Injective φ := (MulAut.conj u₀⁻¹).injective.comp hinjθ
  have hA₀sub : {α : MulAut K | α ∈ A ∧ kgInducedAut θ α ∈ I} ⊆ (B₀ : Set (MulAut K)) :=
    fun α hα => hmem α hα.1 hα.2
  have hle1 : Nat.card ↥B₀ ≤ Nat.card {α : MulAut K // α ∈ A ∧ kgInducedAut θ α ∈ I} := by
    rw [← hXcard]
    exact Nat.card_le_card_of_injective
      (fun β : ↥B₀ => (⟨φ (β : MulAut K), hXβ' (β : MulAut K) β.2⟩ : ↥X))
      (fun β γ h => Subtype.ext (hinjφ (congrArg Subtype.val h)))
  have hle2 : Nat.card {α : MulAut K // α ∈ A ∧ kgInducedAut θ α ∈ I} ≤ Nat.card ↥B₀ :=
    Nat.card_le_card_of_injective
      (fun a : {α : MulAut K // α ∈ A ∧ kgInducedAut θ α ∈ I} =>
        (⟨a.1, hA₀sub a.2⟩ : ↥B₀))
      (fun a b h => Subtype.ext (congrArg (fun x : ↥B₀ => (x : MulAut K)) h))
  have hcardeq : Nat.card ↥B₀ =
      Nat.card {α : MulAut K // α ∈ A ∧ kgInducedAut θ α ∈ I} := le_antisymm hle1 hle2
  have hcardeq' : (B₀ : Set (MulAut K)).ncard =
      {α : MulAut K | α ∈ A ∧ kgInducedAut θ α ∈ I}.ncard := by
    rw [← Nat.card_coe_set_eq (B₀ : Set (MulAut K)),
      ← Nat.card_coe_set_eq {α : MulAut K | α ∈ A ∧ kgInducedAut θ α ∈ I}]
    exact hcardeq
  have hseteq : {α : MulAut K | α ∈ A ∧ kgInducedAut θ α ∈ I} = (B₀ : Set (MulAut K)) :=
    Set.eq_of_subset_of_ncard_le hA₀sub (le_of_eq hcardeq') (Set.toFinite _)
  have hB₀AI : ∀ β ∈ B₀, β ∈ A ∧ kgInducedAut θ β ∈ I := fun β hβ =>
    (show β ∈ {α : MulAut K | α ∈ A ∧ kgInducedAut θ α ∈ I} from by rw [hseteq]; exact hβ)
  refine ⟨hB₀AI, ?_⟩
  symm
  apply Subgroup.eq_of_le_of_card_ge
  · rw [Subgroup.map_le_iff_le_comap]
    exact fun β hβ => hXβ' β hβ
  · rw [Subgroup.card_map_of_injective hinjφ, hcardeq, hXcard]

theorem kgLangS1A_concl_of_xi {K : Type} [Group K] {p : ℕ} (hp : p.Prime)
    {A B₀ : Subgroup (MulAut K)} (hA : IsElemAbelian p A) (hB₀A : B₀ ≤ A) {ξ α₀ : MulAut K}
    (hξ : ξ ∈ A) (hdec : ∀ α ∈ A, ∃ β ∈ B₀, ∃ j : ℕ, α = β * ξ ^ j) (hα₀ : α₀ ∈ A)
    (hα₀B₀ : α₀ ∉ B₀) {k e : K} (he : e ≠ 1) (hep : e ^ p = 1) (hAe : ∀ α ∈ A, α e = e)
    (hBk : ∀ β ∈ B₀, β k = k) (hke : k * (ξ k)⁻¹ = e) :
    ∃ e' : K, e' ≠ 1 ∧ e' ^ p = 1 ∧ (∀ α ∈ A, α e' = e') ∧ k * (α₀ k)⁻¹ = e' := by
  obtain ⟨β₀, hβ₀, j, hα₀dec⟩ := hdec α₀ hα₀
  have hjp : ¬ p ∣ j := by
    intro hpj
    have hξj : ξ ^ j = 1 := by
      obtain ⟨t, rfl⟩ := hpj
      rw [pow_mul, hA.2 ξ hξ, one_pow]
    apply hα₀B₀
    rw [hα₀dec, hξj, mul_one]
    exact hβ₀
  have hkξ : ξ k = e⁻¹ * k := by
    have h2 : k = e * ξ k := mul_inv_eq_iff_eq_mul.mp hke
    conv_rhs => rw [h2]
    group
  have hefix : ∀ m : ℕ, (ξ ^ m) e = e := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => rw [pow_succ, MulAut.mul_apply, hAe ξ hξ, ih]
  have hpowk : ∀ m : ℕ, (ξ ^ m) k = (e ^ m)⁻¹ * k := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, MulAut.mul_apply, hkξ, map_mul, map_inv, ih, hefix m, pow_succ, mul_inv_rev]
      group
  have hα₀k : α₀ k = (ξ ^ j) k := by
    rw [hα₀dec, MulAut.mul_apply, hpowk j]
    simp only [map_mul, map_inv, map_pow, hAe β₀ (hB₀A hβ₀), hBk β₀ hβ₀]
  refine ⟨e ^ j, ?_, ?_, ?_, ?_⟩
  · intro h
    haveI : Fact p.Prime := ⟨hp⟩
    have horder : orderOf e = p := orderOf_eq_prime hep he
    exact hjp (by rw [← horder, orderOf_dvd_iff_pow_eq_one]; exact h)
  · rw [← pow_mul, mul_comm, pow_mul, hep, one_pow]
  · intro α hα
    rw [map_pow, hAe α hα]
  · rw [hα₀k, hpowk j]
    group

end CFSG.StandardType
