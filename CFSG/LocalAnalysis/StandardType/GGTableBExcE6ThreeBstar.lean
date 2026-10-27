module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeToral
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldE6
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Aut

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley InndiagE6 RecipeFieldE6

namespace TableBExc.E6Three

theorem ggBstarBound_of_toral {R : Type} [Group R] [Finite R] {I : Set (MulAut R)}
    (J : Subgroup (MulAut R)) (hJ : (J : Set (MulAut R)) = I)
    (hidx : ∀ Eh : Subgroup (MulAut R), IsElemAbelian 3 Eh →
      Nat.card Eh ≤ 3 * Nat.card (Eh ⊓ J : Subgroup (MulAut R)))
    (htor : ∀ X : Subgroup (MulAut R), IsElemAbelian 3 X → X ≤ J →
      Nat.card X ≤ 3 ^ 6 ∧ (3 ^ 6 ≤ Nat.card X →
        ∃ U : Subgroup R, U ≠ ⊥ ∧ IsPGroup 2 U ∧ ∀ φ ∈ X, ∀ u ∈ U, φ u ∈ U)) :
    GGBstarBound 3 5 R I := by
  intro Eb Eh hEbI hEb hr _ hEbh hEh hcard
  have := TableBSymp.finite_mulAut (R := R)
  have hEbJ : Eb ≤ J := fun φ hφ => by
    rw [← SetLike.mem_coe, hJ]
    exact hEbI hφ
  set X := Eh ⊓ J with hX
  have hXab : IsElemAbelian 3 X := TableB.isElemAbelian_mono hEh inf_le_left
  obtain ⟨hX6, hXU⟩ := htor X hXab inf_le_right
  have h1 := hidx Eh hEh
  have hX6' : 3 ^ 6 ≤ Nat.card X := by
    have : 3 ^ 2 * 3 ^ 5 ≤ 3 * Nat.card X :=
      (Nat.mul_le_mul_left _ hr).trans (hcard.trans h1)
    omega
  have hEb5 : Nat.card Eb ≤ 3 ^ 5 := by
    have : 3 ^ 2 * Nat.card Eb ≤ 3 * 3 ^ 6 :=
      hcard.trans (h1.trans (Nat.mul_le_mul_left _ hX6))
    omega
  obtain ⟨U, hU, hU2, hUX⟩ := hXU hX6'
  have hEbX : Eb ≤ X := le_inf hEbh hEbJ
  refine ⟨X, lt_of_le_of_ne hEbX fun h => ?_, inf_le_left, U, hU, hU2, hUX⟩
  have : Nat.card X ≤ 3 ^ 5 := by rw [← h]; exact hEb5
  omega

section Quot


theorem exists_quot_E6 (K : Type) [Field K] [Finite K] :
    ∃ Ψ : MulAut (RecipeGroup .E6 K) →*
        (K ≃+* K) × Multiplicative (ZMod (exactE TwistTag.E6.tag)),
      ∀ φ, Ψ φ = 1 ↔ φ ∈ RecipeID .E6 K := by
  have hQ := (e6QuotOn_isRoot K).of_eq (largeEvenIsRoot_eq_isRoot TwistTag.E6.tag).symm
  unfold E6QuotOn at hQ
  rw [← diagHom_eq_markDiagUnit] at hQ
  suffices key : ∀ H : Subgroup (LargeEvenChevGL TwistTag.E6.tag.cartan K),
      H = MarkChev.chevH TwistTag.E6.tag.cartan (LargeEvenIsRoot TwistTag.E6.tag.cartan) K false →
      ∃ Ψ : MulAut (LargeEvenCenterQuot H) →*
          (K ≃+* K) × Multiplicative (ZMod (exactE TwistTag.E6.tag)),
        ∀ φ, Ψ φ = 1 ↔ φ ∈ LargeEvenChevIDImage TwistTag.E6.tag.cartan K H from
    key _ (largeEvenChevH_eq _ K false)
  intro H hH
  subst hH
  obtain ⟨Ψ, hker, -⟩ := hQ
  exact ⟨Ψ, fun φ => by rw [hker, ← mem_chevID_iff_isInnDiagOn]⟩

theorem card_le_mul_card_inf_ID_E6_three (K : Type) [Field K] [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) {Eh : Subgroup (MulAut (RecipeGroup .E6 K))}
    (hEh : IsElemAbelian 3 Eh) :
    Nat.card Eh ≤ 3 * Nat.card (Eh ⊓ Subgroup.closure (LargeEvenInnSet (RecipeGroup .E6 K) ∪
      LargeEvenChevDiagImage Tag.E6.cartan K (LargeEvenChevH Tag.E6.cartan K false)) :
        Subgroup (MulAut (RecipeGroup .E6 K))) := by
  have := finite_recipeGroup .E6 K
  have := TableBSymp.finite_mulAut (R := RecipeGroup .E6 K)
  obtain ⟨Ψ, hker⟩ := exists_quot_E6 K
  have hcyc := isCyclic_ringAut K hf hK
  set J := Subgroup.closure (LargeEvenInnSet (RecipeGroup .E6 K) ∪
      LargeEvenChevDiagImage Tag.E6.cartan K (LargeEvenChevH Tag.E6.cartan K false)) with hJ
  set φ₁ : Eh →* (K ≃+* K) := (MonoidHom.fst _ _).comp (Ψ.comp Eh.subtype) with hφ₁
  have hsq : ∀ y : Multiplicative (ZMod (exactE TwistTag.E6.tag)), y ^ 2 = 1 := by
    have h0 : ∀ z : ZMod 2, z + z = 0 := by decide
    intro y
    rw [pow_two]
    exact congrArg Multiplicative.ofAdd (h0 (Multiplicative.toAdd y))
  have hkerJ : ∀ e : Eh, φ₁ e = 1 → (e : MulAut (RecipeGroup .E6 K)) ∈ J := by
    intro e he
    have hep : (e : MulAut (RecipeGroup .E6 K)) ^ 3 = 1 := hEh.2 _ e.2
    have h2 : (Ψ e).2 = 1 := by
      refine eq_one_of_sq_of_pow_odd (p := 3) (by decide) (hsq _) ?_
      rw [← Prod.pow_snd, ← map_pow, hep, map_one, Prod.snd_one]
    have hΨ : Ψ e = 1 := Prod.ext he h2
    exact (hker _).1 hΨ
  have h1 := TableB.card_range_mul_card_ker φ₁
  have hrange : Nat.card φ₁.range ≤ 3 := by
    have : Finite φ₁.range := Finite.of_surjective _ φ₁.rangeRestrict_surjective
    refine TableB.card_le_of_isCyclic (by norm_num) inferInstance ?_
    rintro _ ⟨e, rfl⟩
    rw [← map_pow, show e ^ 3 = 1 from Subtype.ext (hEh.2 e e.2), map_one]
  have hkerle : Nat.card φ₁.ker ≤ Nat.card (Eh ⊓ J : Subgroup (MulAut (RecipeGroup .E6 K))) := by
    refine Nat.card_le_card_of_injective
      (fun e => (⟨(e : Eh), (e : Eh).2, hkerJ e e.2⟩ : (Eh ⊓ J : Subgroup _))) fun x y hxy => ?_
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : (Eh ⊓ J : Subgroup (MulAut (RecipeGroup .E6 K))) =>
      (z : MulAut (RecipeGroup .E6 K))) hxy
  calc Nat.card Eh = Nat.card φ₁.range * Nat.card φ₁.ker := h1.symm
    _ ≤ 3 * Nat.card (Eh ⊓ J : Subgroup (MulAut (RecipeGroup .E6 K))) :=
      Nat.mul_le_mul hrange hkerle

end Quot

section Toral


@[expose] def E6ThreeToralOn (K : Type) [Field K] (S : (Fin Tag.E6.rank → ℤ) → Prop) : Prop :=
  ∀ X : Subgroup (MulAut (LargeEvenCenterQuot (MarkChev.chevH Tag.E6.cartan S K false))),
    IsElemAbelian 3 X →
    (∀ φ ∈ X, IsInnDiagOn (MarkChev.chevH Tag.E6.cartan S K false) (markDiagUnit S K) φ) →
    Nat.card X ≤ 3 ^ 6 ∧ (3 ^ 6 ≤ Nat.card X →
      ∃ U : Subgroup (LargeEvenCenterQuot (MarkChev.chevH Tag.E6.cartan S K false)),
        U ≠ ⊥ ∧ IsPGroup 2 U ∧ ∀ φ ∈ X, ∀ u ∈ U, φ u ∈ U)

theorem E6ThreeToralOn.of_eq {K : Type} [Field K] {S S' : (Fin Tag.E6.rank → ℤ) → Prop}
    (hS : S = S') (h : E6ThreeToralOn K S) : E6ThreeToralOn K S' :=
  hS ▸ h

theorem e6ThreeToralOn_isRoot (K : Type) [Field K] [Finite K] [CharP K 2]
    (h3 : 3 ∣ Nat.card K - 1) : E6ThreeToralOn K (IsRoot Tag.E6) := by
  unfold E6ThreeToralOn
  rw [markDiagUnit_isRoot]
  suffices key : ∀ H : Subgroup (MarkChev.GLS (IsRoot Tag.E6) K), H = adjointGroup Tag.E6 K →
      ∀ X : Subgroup (MulAut (LargeEvenCenterQuot H)), IsElemAbelian 3 X →
      (∀ φ ∈ X, IsInnDiagOn H (rootDiagUnit Tag.E6) φ) →
      Nat.card X ≤ 3 ^ 6 ∧ (3 ^ 6 ≤ Nat.card X →
        ∃ U : Subgroup (LargeEvenCenterQuot H), U ≠ ⊥ ∧ IsPGroup 2 U ∧
          ∀ φ ∈ X, ∀ u ∈ U, φ u ∈ U) from
    key _ (chevH_false_eq_adjointGroup K Tag.E6)
  intro H hH
  subst hH
  intro X hX hXI
  have hZ : Subgroup.center (adjointGroup Tag.E6 K) = ⊥ := center_adjointGroup_eq_bot
  have hmk : Function.Injective (LargeEvenCenterMk (adjointGroup Tag.E6 K)) := by
    rw [← MonoidHom.ker_eq_bot_iff, LargeEvenCenterMk, QuotientGroup.ker_mk', hZ]
  set e := centerQuotEquivOfBot hZ with he
  set X' := X.map (MulAut.congr e).toMonoidHom with hX'
  have hX'ab : IsElemAbelian 3 X' := TableB.isElemAbelian_map hX _
  have hX'I : X' ≤ (hatAut .E6 K).range := by
    rintro _ ⟨φ, hφ, rfl⟩
    obtain ⟨g, hg, a, -, -, hφc⟩ := hXI φ hφ
    refine ⟨⟨g * rootDiagUnit .E6 a, ⟨g, hg, a, rfl⟩⟩, MulEquiv.ext fun h => Subtype.ext ?_⟩
    have h1 := hφc.2 h (hφc.1 h h.2)
    rw [congr_centerQuotEquivOfBot_mk hZ φ h] at h1
    have h2 := congrArg Subtype.val (hmk h1)
    rw [coe_hatAut_apply]
    exact h2.symm
  have hcard : Nat.card X' = Nat.card X :=
    Subgroup.card_map_of_injective (MulAut.congr e).injective
  obtain ⟨h1, h2⟩ := card_le_and_normalizes_of_le_hatAut h3 hX'ab hX'I
  refine ⟨hcard ▸ h1, fun h6 => ?_⟩
  obtain ⟨U', hU', hU'2, hU'X⟩ := h2 (hcard ▸ h6)
  refine ⟨U'.map e.symm.toMonoidHom, fun h => hU' ?_, hU'2.map _, ?_⟩
  · rwa [Subgroup.map_eq_bot_iff_of_injective _ e.symm.injective] at h
  · rintro φ hφ _ ⟨u', hu', rfl⟩
    have hmem := hU'X (MulAut.congr e φ) ⟨φ, hφ, rfl⟩ u' hu'
    refine ⟨MulAut.congr e φ u', hmem, ?_⟩
    simp [MulAut.congr_apply]

theorem card_le_and_normalizes_E6_three (K : Type) [Field K] [Finite K] [CharP K 2]
    (h3 : 3 ∣ Nat.card K - 1) {X : Subgroup (MulAut (RecipeGroup .E6 K))}
    (hX : IsElemAbelian 3 X) (hXI : ∀ φ ∈ X, φ ∈ RecipeID .E6 K) :
    Nat.card X ≤ 3 ^ 6 ∧ (3 ^ 6 ≤ Nat.card X →
      ∃ U : Subgroup (RecipeGroup .E6 K), U ≠ ⊥ ∧ IsPGroup 2 U ∧ ∀ φ ∈ X, ∀ u ∈ U, φ u ∈ U) := by
  have h := (e6ThreeToralOn_isRoot K h3).of_eq (largeEvenIsRoot_eq_isRoot Tag.E6).symm
  unfold E6ThreeToralOn at h
  rw [← diagHom_eq_markDiagUnit] at h
  suffices key : ∀ H : Subgroup (LargeEvenChevGL Tag.E6.cartan K),
      H = MarkChev.chevH Tag.E6.cartan (LargeEvenIsRoot Tag.E6.cartan) K false →
      ∀ X : Subgroup (MulAut (LargeEvenCenterQuot H)), IsElemAbelian 3 X →
      (∀ φ ∈ X, φ ∈ LargeEvenChevIDImage Tag.E6.cartan K H) →
      Nat.card X ≤ 3 ^ 6 ∧ (3 ^ 6 ≤ Nat.card X →
        ∃ U : Subgroup (LargeEvenCenterQuot H), U ≠ ⊥ ∧ IsPGroup 2 U ∧
          ∀ φ ∈ X, ∀ u ∈ U, φ u ∈ U) from
    key _ (largeEvenChevH_eq _ K false) X hX hXI
  intro H hH
  subst hH
  intro X hX hXI
  exact h X hX fun φ hφ => mem_chevID_iff_isInnDiagOn.mp (hXI φ hφ)

theorem ggBstarBound_E6_three (K : Type) [Field K] [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (h3 : 3 ∣ Nat.card K - 1) :
    GGBstarBound 3 5 (RecipeGroup .E6 K) (RecipeID .E6 K) := by
  have := finite_recipeGroup .E6 K
  have : CharP K 2 := charP_two_of_card hK
  exact ggBstarBound_of_toral _ rfl (fun Eh hEh => card_le_mul_card_inf_ID_E6_three K hf hK hEh)
    fun X hX hXJ => card_le_and_normalizes_E6_three K h3 hX fun φ hφ => hXJ hφ

end Toral

end TableBExc.E6Three

end CFSG.StandardType
