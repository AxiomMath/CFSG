module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownChevGeom
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownChevModel
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownChevRecipe
public import CFSG.LieType.Steinberg.G2.Perfect
import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagCartan

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

private theorem chevG2_nonabelian {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : ∃ a b : A, a * b ≠ b * a) : ∃ a b : B, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := h
  exact ⟨e a, e b, fun h' => hab (e.injective (by rw [map_mul, map_mul, h']))⟩

theorem chevG2_idImage_subset_inn
    (K : Type) [Field K] :
    LargeEvenChevIDImage Tag.G2.cartan K (LargeEvenChevH Tag.G2.cartan K false) ⊆
      Set.range (MulAut.conj : LargeEvenCenterQuot (LargeEvenChevH Tag.G2.cartan K false) →*
        MulAut (LargeEvenCenterQuot (LargeEvenChevH Tag.G2.cartan K false))) :=
  TableBExc.idImage_subset_inn_of_top Tag.G2 K
    (TableB.torusSubgroup_eq_top_of_mul_eq_smul _ K TableB.cartanG2_inv fun s => ⟨s, pow_one s⟩)

theorem chevG2_fixed_data
    {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {σ : K ≃+* K} {p : ℕ} (hp : 0 < p) (hσ : orderOf σ = p) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k) (n' : ℕ), Nat.card k = 2 ^ n' ∧ n = p * n' ∧
      1 ≤ n' ∧
        Nonempty (adjointGroup .G2 k ≃* ↥(ggAutFixedSubgroup (entrywiseAdjointAut .G2 σ))) := by
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
  have hτ' : Tag.G2 = .G2 ∨ Tag.G2 = .F4 ∨ Tag.G2 = .D4 ∨ Tag.G2 = .E7 ∨ Tag.G2 = .E8 :=
    Or.inl rfl
  have hfix : ggAutFixedSubgroup (entrywiseAdjointAut .G2 σ) =
      (fixedFieldImage .G2 σ).subgroupOf (adjointGroup .G2 K) := by
    rw [gff_ggAutFixedSubgroup_eq_entrywiseFixedGroup .G2 σ,
      entrywiseFixedGroup_eq_fixedFieldImage_of_ringChar_two hτ' hchar σ]
  have hJC : fixedFieldImage .G2 σ ≤ adjointGroup .G2 K :=
    fun x hx => (fixedFieldImage_le hx).1
  let e : adjointGroup .G2 ↥(fixSubfield σ) ≃*
      ↥(ggAutFixedSubgroup (entrywiseAdjointAut .G2 σ)) :=
    (fixedFieldImageEquiv (τ := .G2) σ).trans
      ((Subgroup.subgroupOfEquivOfLe hJC).symm.trans (MulEquiv.subgroupCongr hfix.symm))
  exact ⟨↥(fixSubfield σ), inferInstance, inferInstance, n', hcard, hn', hn'1, ⟨e⟩⟩

theorem chevG2FixGroupOn_isRoot
    {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) {p : ℕ}
    (hp : 0 < p) : ChevFixGroupOn K .G2 (IsRoot .G2) n p := by
  suffices h : ∀ H : Subgroup (MarkChev.GLS (IsRoot .G2) K), H = adjointGroup .G2 K →
      ∀ f ∈ RecipeFieldExcInn.markFieldImage (IsRoot .G2) K H, orderOf f = p →
        ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ^ (n / p) ∧
          Nonempty (adjointGroup .G2 k ≃* ↥(ggFixSub f)) from
    h _ (chevH_false_eq_adjointGroup K .G2)
  intro H hH f hf hford
  subst hH
  have hr : 0 < Tag.G2.rank := by decide
  obtain ⟨σ, hσ⟩ := RecipeExcLang.autEquiv_eq_entrywise_of_mem_markField hf
  have hσp : orderOf σ = p := by
    rw [← CFSG.RankThree.Chevalley.SteinbergBT.orderOf_entrywiseAdjointAut hr σ, ← hσ,
      MulEquiv.orderOf_eq, hford]
  obtain ⟨k, _, _, n', hk, hnn', hn'1, ⟨E⟩⟩ := chevG2_fixed_data hn hK hp hσp
  let m : LargeEvenCenterQuot (adjointGroup .G2 K) ≃* adjointGroup .G2 K :=
    centerQuotEquivOfBot center_adjointGroup_eq_bot
  have key : ∀ x, ((1 : MulAut (adjointGroup .G2 K)) * entrywiseAdjointAut .G2 σ * 1⁻¹) (m x) =
      m (f x) := by
    intro x
    rw [one_mul, inv_one, mul_one, ← hσ, RecipeExcLang.autEquiv, MulAut.congr_apply]
    simp only [m, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  obtain ⟨E'⟩ := gff_nonempty_equiv_fixed m f 1 (entrywiseAdjointAut .G2 σ) key E
  refine ⟨k, inferInstance, inferInstance, ?_, ?_⟩
  · rw [hk, hnn', Nat.mul_div_cancel_left n' hp]
  · exact ⟨E'.symm.trans (MulEquiv.subgroupCongr (Subgroup.ext fun _ => Iff.rfl))⟩

theorem chevG2FixGroup_recipe
    {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) {p : ℕ}
    (hp : 0 < p) {f : MulAut (LargeEvenCenterQuot (LargeEvenChevH Tag.G2.cartan K false))}
    (hf : f ∈ LargeEvenChevFieldImage Tag.G2.cartan K (LargeEvenChevH Tag.G2.cartan K false))
    (hord : orderOf f = p) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ^ (n / p) ∧
      Nonempty (adjointGroup .G2 k ≃* ↥(ggFixSub f)) := by
  have h := (chevG2FixGroupOn_isRoot hn hK hp).of_eq (largeEvenIsRoot_eq_isRoot .G2).symm
  suffices key : ∀ H : Subgroup (LargeEvenChevGL Tag.G2.cartan K),
      H = MarkChev.chevH Tag.G2.cartan (LargeEvenIsRoot Tag.G2.cartan) K false →
      ∀ f ∈ LargeEvenChevFieldImage Tag.G2.cartan K H, orderOf f = p →
        ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ^ (n / p) ∧
          Nonempty (adjointGroup .G2 k ≃* ↥(ggFixSub f)) from
    key _ (largeEvenChevH_eq Tag.G2.cartan K false) f hf hord
  intro H hH
  subst hH
  exact h

theorem chevG2_fixStd
    {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) {p : ℕ}
    (hp : 0 < p) (hn2 : 2 ≤ n / p)
    {f : MulAut (LargeEvenCenterQuot (LargeEvenChevH Tag.G2.cartan K false))}
    (hf : f ∈ LargeEvenChevFieldImage Tag.G2.cartan K (LargeEvenChevH Tag.G2.cartan K false))
    (hord : orderOf f = p) :
    LargeEvenRecipeChevalley Tag.G2.cartan (2 ^ (n / p)) false fun R₀ _ I₀ _ =>
      IsSimpleGroup R₀ ∧ (∃ a b : R₀, a * b ≠ b * a) ∧
        ∃ θ₀ : ggFixDer f ≃* R₀,
          GGFixGeom (LargeEvenChevIDImage Tag.G2.cartan K (LargeEvenChevH Tag.G2.cartan K false))
            f I₀ θ₀ := by
  obtain ⟨k, hkF, hkFin, hk, hE⟩ := chevG2FixGroup_recipe hn hK hp hf hord
  obtain ⟨E⟩ := hE
  letI : Field k := hkF
  letI : Finite k := hkFin
  refine ⟨k, inferInstance, inferInstance, hk, ?_⟩
  have h3 : 3 ≤ Nat.card k := by
    rw [hk]
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (n / p) := Nat.pow_le_pow_right (by norm_num) hn2
  have hq := CFSG.LieType.Steinberg.Adjoint.isQuasisimple_g2_of_three_le_card k h3
  obtain ⟨eR⟩ := centerQuot_chevGroup_equiv k Tag.G2
  have hsimple : IsSimpleGroup (LargeEvenCenterQuot (LargeEvenChevH Tag.G2.cartan k false)) := by
    haveI : IsSimpleGroup (AdjointQuotient Tag.G2 k) := hq.2.1
    exact eR.isSimpleGroup
  have hnab : ∃ a b : LargeEvenCenterQuot (LargeEvenChevH Tag.G2.cartan k false), a * b ≠ b * a :=
    chevG2_nonabelian eR.symm hq.2.2
  haveI : IsSimpleGroup (LargeEvenCenterQuot (LargeEvenChevH Tag.G2.cartan k false)) := hsimple
  refine ⟨hsimple, hnab, ?_⟩
  let e : LargeEvenCenterQuot (LargeEvenChevH Tag.G2.cartan k false) ≃* ↥(ggFixSub f) :=
    (TableBExc.recipeEquiv Tag.G2 k).trans E
  exact ggFixGeom_of_inn
    (I := LargeEvenChevIDImage Tag.G2.cartan K (LargeEvenChevH Tag.G2.cartan K false))
    (I₀ := LargeEvenChevIDImage Tag.G2.cartan k (LargeEvenChevH Tag.G2.cartan k false))
    hnab (TableBExc.center_recipeGroup_eq_bot Tag.G2 K)
    (chevG2_idImage_subset_inn K) (by
      rintro _ ⟨x, rfl⟩
      exact conj_mem_chevIDImage (LargeEvenChevH Tag.G2.cartan k false) x) e

theorem ggFieldFixKnown_G2 :
    GGFieldFixKnown fun p lab => lab.tag = .G2 ∧ 2 ≤ lab.n / p := by
  intro p lab hp _ hlab hS
  intro Q hQ
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, -⟩ := hlab
  obtain ⟨ht, hn2⟩ := hS
  dsimp only at ht hn2
  subst ht
  exact recipeChevalley_and (fun K _ _ hK _ _ f hf hord =>
    chevG2_fixStd hn hK hp.pos hn2 hf hord) hQ

end CFSG.StandardType

end
