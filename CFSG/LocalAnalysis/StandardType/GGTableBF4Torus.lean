module

public import CFSG.LocalAnalysis.StandardType.GGTableBF4Basic
public import CFSG.RankThree.CentralCover.SteinbergBNF4SplitTorus

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.CentralCover

namespace TableBF4

section Section

variable {L' R : Type*} [Group L'] [Group R] {ψ : L' →* R}

theorem exists_torus_section_of_comm (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') {p k : ℕ} (hp : Odd p)
    (τ : (Fin k → Multiplicative (ZMod p)) →* R)
    (hcomm : ∀ x ∈ τ.range.comap ψ, ∀ y ∈ τ.range.comap ψ, x * y = y * x)
    (hinv : ∀ i : Fin k, ∃ w : R,
      w * TableBSymp.torusBasis τ i * w⁻¹ = (TableBSymp.torusBasis τ i)⁻¹) :
    ∃ σ : (Fin k → Multiplicative (ZMod p)) →* L', ψ.comp σ = τ := by
  classical
  have : NeZero p := ⟨by rintro rfl; exact Nat.not_odd_zero hp⟩
  set A := τ.range.comap ψ with hA
  have hkerA : ψ.ker ≤ A := fun z hz => by
    show ψ z ∈ τ.range
    rw [MonoidHom.mem_ker.mp hz]
    exact one_mem _
  have hlift : ∀ i, ∃ t ∈ A, ψ t = TableBSymp.torusBasis τ i ∧ t ^ p = 1 := by
    intro i
    obtain ⟨x, hx⟩ := hψ (TableBSymp.torusBasis τ i)
    obtain ⟨w, hw⟩ := hinv i
    have hxA : x ∈ A := by
      show ψ x ∈ τ.range
      rw [hx]
      exact ⟨_, rfl⟩
    exact TableBSymp.exists_lift_pow_eq_one hψ hker hp (TableBSymp.torusBasis_pow τ i) hw hcomm
      hkerA hx hxA
  choose t htA hψt htp using hlift
  set φ : ∀ i : Fin k, Multiplicative (ZMod p) →* L' := fun i => TableBSymp.zmodPowHom (htp i)
    with hφ
  have hc : Pairwise fun i j => ∀ a b, Commute (φ i a) (φ j b) := fun i j _ a b =>
    hcomm _ (TableBSymp.zmodPowHom_mem (htp i) (htA i) a) _
      (TableBSymp.zmodPowHom_mem (htp j) (htA j) b)
  refine ⟨MonoidHom.noncommPiCoprod φ hc, MonoidHom.pi_ext fun i a => ?_⟩
  rw [MonoidHom.comp_apply, MonoidHom.noncommPiCoprod_mulSingle, hφ,
    TableBSymp.zmodPowHom_apply, map_pow, hψt, TableBSymp.torusBasis_pow_val]

end Section

@[expose] def piTorus {p d : ℕ} {R : Type*} [Group R] (e : Multiplicative (Fin d → ZMod p) →* R) :
    (Fin d → Multiplicative (ZMod p)) →* R :=
  e.comp (MulEquiv.piMultiplicative fun _ : Fin d => ZMod p).symm.toMonoidHom

theorem piTorus_apply {p d : ℕ} {R : Type*} [Group R] (e : Multiplicative (Fin d → ZMod p) →* R)
    (f : Fin d → Multiplicative (ZMod p)) :
    piTorus e f = e (.ofAdd fun i => Multiplicative.toAdd (f i)) :=
  rfl

theorem range_piTorus {p d : ℕ} {R : Type*} [Group R] (e : Multiplicative (Fin d → ZMod p) →* R) :
    (piTorus e).range = e.range := by
  ext x
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨MulEquiv.piMultiplicative _ a, by
      rw [piTorus, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]⟩

theorem torusBasis_piTorus {p d : ℕ} {R : Type*} [Group R]
    (e : Multiplicative (Fin d → ZMod p) →* R) (i : Fin d) :
    TableBSymp.torusBasis (piTorus e) i = e (.ofAdd (Pi.single i 1)) := by
  rw [TableBSymp.torusBasis, piTorus_apply]
  congr 2

theorem ggTorusLift_of_reflections {p d : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {R : Type} [Group R]
    (e : Multiplicative (Fin d → ZMod p) →* R) (he : Function.Injective e)
    (c : Fin d → (Fin d → ZMod p) →ₗ[ZMod p] ZMod p) (hc : ∀ i, c i (Pi.single i 1) = 2)
    (n : Fin d → R)
    (hn : ∀ i v, n i * e (.ofAdd v) * (n i)⁻¹ = e (.ofAdd (v - c i v • Pi.single i 1)))
    {U : Subgroup R} (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U)
    (hTU : ∀ v, ∀ u ∈ U, e v * u * (e v)⁻¹ ∈ U) : GGTorusLift p d R := by
  intro L' _ _ ψ hψ hker _
  have hodd : Odd p := hp.odd_of_ne_two hp2
  set τ := piTorus e with hτdef
  have hτ : Function.Injective τ :=
    he.comp (MulEquiv.piMultiplicative fun _ : Fin d => ZMod p).symm.injective
  have hcomm : ∀ x ∈ τ.range.comap ψ, ∀ y ∈ τ.range.comap ψ, x * y = y * x := by
    rw [hτdef, range_piTorus]
    exact reflection_comap_comm hψ hker hp hp2 e c hc n hn
  have hinv : ∀ i : Fin d, ∃ w : R,
      w * TableBSymp.torusBasis τ i * w⁻¹ = (TableBSymp.torusBasis τ i)⁻¹ := by
    intro i
    refine ⟨n i, ?_⟩
    rw [hτdef, torusBasis_piTorus, hn, hc, ← map_inv, ← ofAdd_neg]
    congr 2
    rw [two_smul]
    abel
  obtain ⟨σ, hσ⟩ := exists_torus_section_of_comm hψ hker hodd τ hcomm hinv
  have hσi : Function.Injective σ := by
    intro a b hab
    apply hτ
    rw [← hσ, MonoidHom.comp_apply, MonoidHom.comp_apply, hab]
  obtain ⟨T, hT, hT2, hET⟩ := TableBSymp.exists_twoSubgroup_lift (E := σ.range) hψ hker hU hU2
    (by
      rintro _ ⟨f, rfl⟩ u hu
      have h1 : ψ (σ f) = e (.ofAdd fun i => Multiplicative.toAdd (f i)) := by
        rw [← MonoidHom.comp_apply, hσ, hτdef, piTorus_apply]
      rw [h1]
      exact hTU _ u hu)
  refine ⟨T, σ.range, hT, hT2, hET, ?_, ?_, ?_⟩
  · refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
      apply Subtype.ext
      show σ a * σ b = σ b * σ a
      rw [← map_mul, ← map_mul, mul_comm]
    · rintro _ ⟨a, rfl⟩
      rw [← map_pow]
      have : a ^ p = 1 := by
        funext i
        rw [Pi.pow_apply, Pi.one_apply, ← ofAdd_toAdd (a i), ← ofAdd_nsmul, nsmul_eq_mul,
          ZMod.natCast_self, zero_mul, ofAdd_zero]
      rw [this, map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hσi).toEquiv, Nat.card_fun,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod p) ≃ ZMod p), Nat.card_zmod,
      Nat.card_fin]
  · rw [eq_bot_iff]
    rintro _ ⟨⟨f, rfl⟩, hf⟩
    have hf' : ψ (σ f) = 1 := hf
    rw [← MonoidHom.comp_apply, hσ] at hf'
    rw [Subgroup.mem_bot, hτ (hf'.trans (map_one τ).symm), map_one]

section F4

variable {K : Type} [Field K]

theorem exists_rootGroup_normalized_F4 [CharP K 2] {p : ℕ} [NeZero p] (ζ : Kˣ) (hζ : ζ ^ p = 1) :
    ∃ U : Subgroup (adjointGroup .F4 K), U ≠ ⊥ ∧ IsPGroup 2 U ∧
      ∀ v, ∀ u ∈ U, chevTorus .F4 ζ hζ v * u * (chevTorus .F4 ζ hζ v)⁻¹ ∈ U := by
  classical
  set i₀ : Fin Tag.F4.rank := ⟨0, by decide⟩
  let xh : Multiplicative K →* adjointGroup .F4 K :=
    { toFun := fun c => ⟨xUnit .F4 K i₀ (Multiplicative.toAdd c), xUnit_mem_adjointGroup _ _⟩
      map_one' := Subtype.ext (xUnit_zero i₀)
      map_mul' := fun c c' => Subtype.ext (xUnit_add i₀ _ _) }
  have htwo : (2 : K) = 0 := CharTwo.two_eq_zero
  refine ⟨xh.range, fun h => ?_, ?_, ?_⟩
  · have h1 : xh (.ofAdd 1) ∈ xh.range := ⟨_, rfl⟩
    rw [h, Subgroup.mem_bot] at h1
    have h2 : xOp .F4 K i₀ 1 = xOp .F4 K i₀ 0 := by
      have h3 : xUnit .F4 K i₀ 1 = xUnit .F4 K i₀ 0 := by
        rw [xUnit_zero]
        exact congrArg Subtype.val h1
      exact congrArg Units.val h3
    exact one_ne_zero (xOp_injective i₀ h2)
  · rintro ⟨_, ⟨c, rfl⟩⟩
    refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    change (xUnit .F4 K i₀ (Multiplicative.toAdd c)) ^ 2 = 1
    rw [pow_two, ← xUnit_add, ← two_mul, htwo, zero_mul, xUnit_zero]
  · rintro a _ ⟨c, rfl⟩
    obtain ⟨c', hc'⟩ := listProd_torusElt_conj_xUnit i₀
      (List.ofFn fun i => torusElt .F4 K i (zmodPowHom ζ hζ (.ofAdd (Multiplicative.toAdd a i))))
      (fun g hg => by
        obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hg
        exact ⟨i, _, rfl⟩) (Multiplicative.toAdd c)
    refine ⟨.ofAdd c', Subtype.ext ?_⟩
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_chevTorus]
    exact hc'.symm

theorem ggTorusLift_adjointF4 [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1) : GGTorusLift p 4 (adjointGroup .F4 K) := by
  have := Fact.mk hp
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζo⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := K) hpq
  have hζ : ζ ^ p = 1 := by
    rw [← hζo]
    exact pow_orderOf_eq_one ζ
  have hdet : IsUnit ((Tag.F4.cartan.det : ℤ) : ZMod p) := by
    rw [det_cartan_F4, Int.cast_one]
    exact isUnit_one
  obtain ⟨U, hU, hU2, hTU⟩ := exists_rootGroup_normalized_F4 ζ hζ
  exact ggTorusLift_of_reflections (d := Tag.F4.rank) hp hp2 (chevTorus .F4 ζ hζ)
    (chevTorus_injective hζo hζ hdet) (cartanFunctional .F4 p)
    (fun i => CFSG.RankThree.CentralCover.cartanFunctional_single i)
    (fun i => ⟨weylElt .F4 K i 1, weylElt_mem_adjointGroup i 1⟩)
    (fun i v => weylElt_conj_chevTorus ζ hζ i v) hU hU2 hTU


theorem ggTorusLift_F4 [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1) : GGTorusLift p 4 (RecipeGroup K) :=
  ggTorusLift_of_mulEquiv (recipeEquiv K) (ggTorusLift_adjointF4 hp hp2 hpq)

end F4

end TableBF4

end CFSG.StandardType
