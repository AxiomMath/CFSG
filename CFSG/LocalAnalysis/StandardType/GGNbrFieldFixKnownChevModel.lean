module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixDefs
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45FieldFixAut
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45FieldFixData
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45FieldFixMark
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangModel
public import CFSG.LieType.Simplicity.Exceptional
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylFieldVacOther

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] def ChevFixGroupOn (K : Type) [Field K] (τ : Tag) (S : (Fin τ.rank → ℤ) → Prop)
    (n p : ℕ) : Prop :=
  ∀ f ∈ RecipeFieldExcInn.markFieldImage S K (MarkChev.chevH τ.cartan S K false),
    orderOf f = p →
      ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ^ (n / p) ∧
        Nonempty (adjointGroup τ k ≃* ↥(ggFixSub f))

theorem ChevFixGroupOn.of_eq {K : Type} [Field K] {τ : Tag} {S S' : (Fin τ.rank → ℤ) → Prop}
    {n p : ℕ} (hS : S = S') (h : ChevFixGroupOn K τ S n p) : ChevFixGroupOn K τ S' n p :=
  hS ▸ h

section Model

theorem chev_isQuasisimple {τ : Tag} (hτ : τ = .F4 ∨ τ = .E7 ∨ τ = .E8) (k : Type) [Field k]
    [Finite k] : CFSG.IsQuasisimple ↥(adjointGroup τ k) := by
  rcases hτ with rfl | rfl | rfl
  · exact gff_isQuasisimple_adjoint (Or.inl rfl) k
  · exact CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e7 k
  · exact gff_isQuasisimple_adjoint (Or.inr rfl) k

theorem chev_fixed_data {τ : Tag} (hτ : τ = .F4 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K]
    [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) {σ : K ≃+* K} {p : ℕ} (hp : 0 < p)
    (hσ : orderOf σ = p) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k) (n' : ℕ), Nat.card k = 2 ^ n' ∧ n = p * n' ∧
      1 ≤ n' ∧ Nonempty (adjointGroup τ k ≃* ↥(ggAutFixedSubgroup (entrywiseAdjointAut τ σ))) := by
  haveI : Fintype K := Fintype.ofFinite K
  have hcharP : CharP K 2 :=
    charP_of_card_eq_prime_pow (p := 2) (f := n)
      (by rw [← Nat.card_eq_fintype_card]; exact hK)
  have hchar : ringChar K = 2 := ringChar.eq K 2
  obtain ⟨hdvd, hcard⟩ :=
    CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield (p := 2) (f := n)
      Nat.prime_two hn hK σ
  rw [hσ] at hdvd hcard
  obtain ⟨n', hn'⟩ := hdvd
  have hdiv : n / p = n' := by rw [hn']; exact Nat.mul_div_cancel_left n' hp
  rw [hdiv] at hcard
  have hn'1 : 1 ≤ n' := by
    rcases Nat.eq_zero_or_pos n' with h | h
    · rw [h, Nat.mul_zero] at hn'
      omega
    · exact h
  have hτ' : τ = .G2 ∨ τ = .F4 ∨ τ = .D4 ∨ τ = .E7 ∨ τ = .E8 := by
    rcases hτ with rfl | rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  have hfix : ggAutFixedSubgroup (entrywiseAdjointAut τ σ) =
      (fixedFieldImage τ σ).subgroupOf (adjointGroup τ K) := by
    rw [gff_ggAutFixedSubgroup_eq_entrywiseFixedGroup τ σ,
      entrywiseFixedGroup_eq_fixedFieldImage_of_ringChar_two hτ' hchar σ]
  have hJC : fixedFieldImage τ σ ≤ adjointGroup τ K :=
    fun x hx => (fixedFieldImage_le hx).1
  let e : adjointGroup τ ↥(fixSubfield σ) ≃*
      ↥(ggAutFixedSubgroup (entrywiseAdjointAut τ σ)) :=
    (fixedFieldImageEquiv (τ := τ) σ).trans
      ((Subgroup.subgroupOfEquivOfLe hJC).symm.trans (MulEquiv.subgroupCongr hfix.symm))
  exact ⟨↥(fixSubfield σ), inferInstance, inferInstance, n', hcard, hn', hn'1, ⟨e⟩⟩

theorem chevFixGroupOn_isRoot {τ : Tag} (hτ : τ = .F4 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K]
    [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) {p : ℕ} (hp : 0 < p) :
    ChevFixGroupOn K τ (IsRoot τ) n p := by
  suffices h : ∀ H : Subgroup (MarkChev.GLS (IsRoot τ) K), H = adjointGroup τ K →
      ∀ f ∈ RecipeFieldExcInn.markFieldImage (IsRoot τ) K H, orderOf f = p →
        ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ^ (n / p) ∧
          Nonempty (adjointGroup τ k ≃* ↥(ggFixSub f)) from
    h _ (chevH_false_eq_adjointGroup K τ)
  intro H hH f hf hford
  subst hH
  have hr : 0 < τ.rank := by rcases hτ with rfl | rfl | rfl <;> decide
  obtain ⟨σ, hσ⟩ := RecipeExcLang.autEquiv_eq_entrywise_of_mem_markField hf
  have hσp : orderOf σ = p := by
    rw [← CFSG.RankThree.Chevalley.SteinbergBT.orderOf_entrywiseAdjointAut hr σ, ← hσ,
      MulEquiv.orderOf_eq, hford]
  obtain ⟨k, _, _, n', hk, hnn', hn'1, ⟨E⟩⟩ := chev_fixed_data hτ hn hK hp hσp
  let m : LargeEvenCenterQuot (adjointGroup τ K) ≃* adjointGroup τ K :=
    centerQuotEquivOfBot center_adjointGroup_eq_bot
  have key : ∀ x, ((1 : MulAut (adjointGroup τ K)) * entrywiseAdjointAut τ σ * 1⁻¹) (m x) =
      m (f x) := by
    intro x
    rw [one_mul, inv_one, mul_one, ← hσ, RecipeExcLang.autEquiv, MulAut.congr_apply]
    simp only [m, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  obtain ⟨E'⟩ := gff_nonempty_equiv_fixed m f 1 (entrywiseAdjointAut τ σ) key E
  refine ⟨k, inferInstance, inferInstance, ?_, ?_⟩
  · rw [hk, hnn', Nat.mul_div_cancel_left n' hp]
  · exact ⟨E'.symm.trans (MulEquiv.subgroupCongr (Subgroup.ext fun _ => Iff.rfl))⟩

theorem chevFixGroup_recipe {τ : Tag} (hτ : τ = .F4 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K]
    [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) {p : ℕ} (hp : 0 < p)
    {f : MulAut (LargeEvenCenterQuot (LargeEvenChevH τ.cartan K false))}
    (hf : f ∈ LargeEvenChevFieldImage τ.cartan K (LargeEvenChevH τ.cartan K false))
    (hord : orderOf f = p) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ^ (n / p) ∧
      Nonempty (adjointGroup τ k ≃* ↥(ggFixSub f)) := by
  have h := (chevFixGroupOn_isRoot hτ hn hK hp).of_eq (largeEvenIsRoot_eq_isRoot τ).symm
  suffices key : ∀ H : Subgroup (LargeEvenChevGL τ.cartan K),
      H = MarkChev.chevH τ.cartan (LargeEvenIsRoot τ.cartan) K false →
      ∀ f ∈ LargeEvenChevFieldImage τ.cartan K H, orderOf f = p →
        ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ^ (n / p) ∧
          Nonempty (adjointGroup τ k ≃* ↥(ggFixSub f)) from
    key _ (largeEvenChevH_eq τ.cartan K false) f hf hord
  intro H hH
  subst hH
  exact h

end Model

end CFSG.StandardType

end
