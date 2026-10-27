module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Basic

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.CentralCover
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace TableBExc

theorem ggTorusLift_of_reflections_of_injOn {p d r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {R : Type}
    [Group R] (e : Multiplicative (Fin d → ZMod p) →* R)
    (c : Fin d → (Fin d → ZMod p) →ₗ[ZMod p] ZMod p) (hc : ∀ i, c i (Pi.single i 1) = 2)
    (n : Fin d → R)
    (hn : ∀ i v, n i * e (.ofAdd v) * (n i)⁻¹ = e (.ofAdd (v - c i v • Pi.single i 1)))
    {W : Subgroup (Multiplicative (Fin d → ZMod p))} (hW : Nat.card W = p ^ r)
    (hWe : ∀ w ∈ W, e w = 1 → w = 1)
    {U : Subgroup R} (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U)
    (hTU : ∀ v, ∀ u ∈ U, e v * u * (e v)⁻¹ ∈ U) : GGTorusLift p r R := by
  intro L' _ _ ψ hψ hker _
  have hodd : Odd p := hp.odd_of_ne_two hp2
  set τ := TableBF4.piTorus e with hτdef
  have hcomm : ∀ x ∈ τ.range.comap ψ, ∀ y ∈ τ.range.comap ψ, x * y = y * x := by
    rw [hτdef, TableBF4.range_piTorus]
    exact reflection_comap_comm hψ hker hp hp2 e c hc n hn
  have hinv : ∀ i : Fin d, ∃ w : R,
      w * TableBSymp.torusBasis τ i * w⁻¹ = (TableBSymp.torusBasis τ i)⁻¹ := by
    intro i
    refine ⟨n i, ?_⟩
    rw [hτdef, TableBF4.torusBasis_piTorus, hn, hc, ← map_inv, ← ofAdd_neg]
    congr 2
    rw [two_smul]
    abel
  obtain ⟨σ, hσ⟩ := TableBF4.exists_torus_section_of_comm hψ hker hodd τ hcomm hinv
  set σ' : Multiplicative (Fin d → ZMod p) →* L' :=
    σ.comp (MulEquiv.piMultiplicative fun _ : Fin d => ZMod p).toMonoidHom with hσ'
  have hψσ' : ∀ v, ψ (σ' v) = e v := by
    intro v
    have h1 : ψ (σ' v) = τ (MulEquiv.piMultiplicative (fun _ : Fin d => ZMod p) v) := by
      rw [← hσ]
      rfl
    rw [h1, hτdef, TableBF4.piTorus, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply]
  have hinj : Function.Injective (σ'.comp W.subtype) := by
    intro w w' h
    have h2 : σ' w = σ' w' := h
    have h1 : e ((w : Multiplicative (Fin d → ZMod p)) *
        (w' : Multiplicative (Fin d → ZMod p))⁻¹) = 1 := by
      rw [map_mul_inv, ← hψσ', ← hψσ', h2, mul_inv_cancel]
    exact Subtype.ext (mul_inv_eq_one.mp (hWe _ (W.mul_mem w.2 (W.inv_mem w'.2)) h1))
  have hrange : (σ'.comp W.subtype).range = W.map σ' := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  obtain ⟨T, hT, hT2, hET⟩ := TableBSymp.exists_twoSubgroup_lift (E := W.map σ') hψ hker hU hU2
    (by
      rintro _ ⟨w, -, rfl⟩ u hu
      rw [hψσ']
      exact hTU _ u hu)
  refine ⟨T, W.map σ', hT, hT2, hET, ?_, ?_, ?_⟩
  · refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨_, a, -, rfl⟩ ⟨_, b, -, rfl⟩
      apply Subtype.ext
      show σ' a * σ' b = σ' b * σ' a
      rw [← map_mul, ← map_mul, mul_comm]
    · rintro _ ⟨a, -, rfl⟩
      rw [← map_pow]
      have : a ^ p = 1 := by
        apply Multiplicative.toAdd.injective
        funext i
        rw [toAdd_pow, toAdd_one, Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul,
          Pi.zero_apply]
      rw [this, map_one]
  · rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hW]
  · rw [eq_bot_iff]
    rintro _ ⟨⟨w, hw, rfl⟩, hk⟩
    have hk' : ψ (σ' w) = 1 := hk
    rw [hψσ'] at hk'
    rw [Subgroup.mem_bot, hWe w hw hk', map_one]


section Torus

variable {τ : Tag} {K : Type} [Field K]

theorem cartan_sum_eq_zero_of_chevTorus_eq_one {p : ℕ} [NeZero p] {ζ : Kˣ} (hζo : orderOf ζ = p)
    (hζ : ζ ^ p = 1) {a : Multiplicative (Fin τ.rank → ZMod p)} (ha : chevTorus τ ζ hζ a = 1)
    (j : Fin τ.rank) : ∑ i, (τ.cartan i j : ZMod p) * Multiplicative.toAdd a i = 0 := by
  have ht : torusCoordHom τ K (chevTorusExp τ ζ hζ a) = 1 := by
    have := congrArg Subtype.val ha
    exact Subtype.ext this
  have h := torusCoordHom_apply_rootVec_single (R := K) (chevTorusExp τ ζ hζ a) j
  rw [ht, OneMemClass.coe_one, Units.val_one, Module.End.one_apply,
    rootVec_eq_single_of_isRoot (isRoot_single τ j)] at h
  have h' := congrArg (fun v : RootModule τ K =>
    v (Sum.inr ⟨Pi.single j 1, isRoot_single τ j⟩)) h
  simp only [Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one] at h'
  have h1 : ∏ i, chevTorusExp τ ζ hζ a i ^ τ.cartan i j = 1 := Units.ext (by
    rw [Units.val_one, ← h'])
  have h2 : zmodPowHom ζ hζ (.ofAdd (∑ i, (τ.cartan i j : ZMod p) * Multiplicative.toAdd a i))
      = 1 := by
    rw [← h1, ofAdd_sum, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [chevTorusExp_apply, ← map_zpow, ← ofAdd_zsmul, zsmul_eq_mul]
  have h3 := zmodPowHom_injective hζo hζ (h2.trans (map_one _).symm)
  exact Multiplicative.ofAdd.injective h3

end Torus

local instance tableBExcE6ThreeNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

@[expose] def e6ThreeEval : Multiplicative (Fin Tag.E6.rank → ZMod 3) →* Multiplicative (ZMod 3) :=
  AddMonoidHom.toMultiplicative (Pi.evalAddMonoidHom (fun _ => ZMod 3) 0)

@[expose] def e6ThreeW : Subgroup (Multiplicative (Fin Tag.E6.rank → ZMod 3)) :=
  e6ThreeEval.ker

theorem mem_e6ThreeW {a : Multiplicative (Fin Tag.E6.rank → ZMod 3)} :
    a ∈ e6ThreeW ↔ Multiplicative.toAdd a 0 = 0 :=
  MonoidHom.mem_ker

theorem card_e6ThreeW : Nat.card e6ThreeW = 3 ^ 5 := by
  have h1 := TableB.card_range_mul_card_ker e6ThreeEval
  have hsurj : e6ThreeEval.range = ⊤ := by
    rw [eq_top_iff]
    intro x _
    refine ⟨.ofAdd (Pi.single 0 (Multiplicative.toAdd x)), ?_⟩
    simp [e6ThreeEval]
  rw [hsurj, Subgroup.card_top, card_multiplicative_fin_zmod, Nat.card_eq_fintype_card,
    Fintype.card_multiplicative, ZMod.card] at h1
  change 3 * Nat.card e6ThreeW = 3 ^ 6 at h1
  omega

theorem e6_three_kernel : ∀ a : Fin Tag.E6.rank → ZMod 3, a 0 = 0 →
    (∀ j, ∑ i, ((Tag.E6.cartan i j : ℤ) : ZMod 3) * a i = 0) → a = 0 := by
  decide +kernel


section Lift

variable {K : Type} [Field K]

theorem ggTorusLift_adjoint_E6_three [Finite K] [CharP K 2] (h3 : 3 ∣ Nat.card K - 1) :
    GGTorusLift 3 5 (adjointGroup .E6 K) := by
  have := Fact.mk Nat.prime_three
  obtain ⟨ζ, hζo⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := K) h3
  have hζ : ζ ^ 3 = 1 := by
    rw [← hζo]
    exact pow_orderOf_eq_one ζ
  obtain ⟨U, hU, hU2, hTU⟩ := exists_rootGroup_normalized (τ := .E6) ⟨0, by decide⟩ ζ hζ
  refine ggTorusLift_of_reflections_of_injOn (d := Tag.E6.rank) Nat.prime_three (by norm_num)
    (chevTorus .E6 ζ hζ) (cartanFunctional .E6 3)
    (fun i => CFSG.RankThree.CentralCover.cartanFunctional_single i)
    (fun i => ⟨weylElt .E6 K i 1, weylElt_mem_adjointGroup i 1⟩)
    (fun i v => weylElt_conj_chevTorus ζ hζ i v) card_e6ThreeW (fun w hw h1 => ?_) hU hU2 hTU
  have h0 := e6_three_kernel (Multiplicative.toAdd w) (mem_e6ThreeW.mp hw)
    (cartan_sum_eq_zero_of_chevTorus_eq_one hζo hζ h1)
  exact Multiplicative.toAdd.injective (h0.trans toAdd_one.symm)


theorem ggTorusLift_E6_three [Finite K] [CharP K 2] (h3 : 3 ∣ Nat.card K - 1) :
    GGTorusLift 3 5 (RecipeGroup .E6 K) :=
  TableBF4.ggTorusLift_of_mulEquiv (recipeEquiv .E6 K) (ggTorusLift_adjoint_E6_three h3)

theorem recipeChevalleyE6_torusLift_three {n : ℕ} (h3 : 3 ∣ 2 ^ n - 1) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeChevalley (LargeEvenCartanE 6) (2 ^ n) false Q) :
    LargeEvenRecipeChevalley (LargeEvenCartanE 6) (2 ^ n) false fun R _ I F =>
      Q R I F ∧ GGTorusLift 3 5 R := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have : CharP K 2 := charP_two_of_card hK
  exact ⟨K, inferInstance, inferInstance, hK, hQ, ggTorusLift_E6_three (by rw [hK]; exact h3)⟩

end Lift

end TableBExc


theorem largeEvenLabelAll_torusLift_E6_three {lab : LargeEvenLabel} (htag : lab.tag = .E6)
    (h3 : 3 ∣ 2 ^ lab.n - 1) : LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift 3 5 R := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag
  subst htag
  intro Q hQ
  exact TableBExc.recipeChevalleyE6_torusLift_three h3 hQ

end CFSG.StandardType
