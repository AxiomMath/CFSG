module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAbelianNormalizer
public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.ShultStronglyClosedTI.CyclicSemiregular

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped IsMulCommutative

section Linear

variable {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]

theorem exists_pow_conj_eq_of_transitive [Finite V] [Nontrivial V]
    {T : Subgroup (LinearMap.GeneralLinearGroup (ZMod p) V)}
    (hcomm : ∀ g ∈ T, ∀ h ∈ T, g * h = h * g)
    (htrans : ∀ v w : V, v ≠ 0 → w ≠ 0 → ∃ t ∈ T, (t : Module.End (ZMod p) V) v = w)
    {g : LinearMap.GeneralLinearGroup (ZMod p) V} (hg : ∀ t ∈ T, g * t * g⁻¹ ∈ T)
    (hg' : ∀ t ∈ T, g⁻¹ * t * g⁻¹⁻¹ ∈ T) :
    ∃ j : ℕ, ∀ t ∈ T, g * t * g⁻¹ = t ^ (p ^ j) := by
  have : FiniteDimensional (ZMod p) V := Module.Finite.of_finite
  have hn : 1 ≤ Module.finrank (ZMod p) V := Module.finrank_pos
  have hirr : ∀ W : Submodule (ZMod p) V,
      (∀ t ∈ T, ∀ w ∈ W, (t : Module.End (ZMod p) V) w ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    by_cases hbot : W = ⊥
    · exact Or.inl hbot
    right
    obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    rw [Submodule.eq_top_iff']
    intro v
    by_cases hv : v = 0
    · rw [hv]
      exact W.zero_mem
    obtain ⟨t, ht, rfl⟩ := htrans w v hw0 hv
    exact hW t ht w hwW
  obtain ⟨hF, hcard, -⟩ := irreducible_abelian_operator_algebra_field hn rfl hcomm hirr
  let σ : RingAut (operatorAlgebra T) := operatorConjAut T hg hg'
  let : Field (operatorAlgebra T) := hF.toField
  obtain ⟨φ, hφ, -, hzp, hcardAut, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality (F := operatorAlgebra T)
      (Fact.out : p.Prime) hn hcard
  have : Finite (operatorAlgebra T ≃+* operatorAlgebra T) :=
    Nat.finite_of_card_ne_zero (by rw [hcardAut]; omega)
  have hσ : σ ∈ Submonoid.powers φ := by
    rw [mem_powers_iff_mem_zpowers, hzp]
    exact Subgroup.mem_top _
  obtain ⟨j, hj⟩ := hσ
  have hpow : ∀ (k : ℕ) (a : operatorAlgebra T), (φ ^ k) a = a ^ (p ^ k) := by
    intro k
    induction k with
    | zero => intro a; simp
    | succ k ih =>
      intro a
      rw [pow_succ, RingAut.mul_apply, hφ, ih, ← pow_mul, ← pow_succ']
  refine ⟨j, fun t ht => ?_⟩
  let a : operatorAlgebra T := ⟨t, Algebra.subset_adjoin ⟨t, ht, rfl⟩⟩
  have h1 : σ a = a ^ (p ^ j) := by rw [← hj, hpow]
  have h2 := congrArg (fun b : operatorAlgebra T => (b : Module.End (ZMod p) V)) h1
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val]
  exact h2

variable (p) (A : Type*) [CommGroup A] [Module (ZMod p) (Additive A)]

@[expose] def mulAutGL : MulAut A →* LinearMap.GeneralLinearGroup (ZMod p) (Additive A) where
  toFun σ := LinearMap.GeneralLinearGroup.ofLinearEquiv
    ((MulEquiv.toAdditive σ).toLinearEquiv (ZMod.map_smul (MulEquiv.toAdditive σ)))
  map_one' := Units.ext (LinearMap.ext fun _ => rfl)
  map_mul' _ _ := Units.ext (LinearMap.ext fun _ => rfl)

theorem mulAutGL_apply (σ : MulAut A) (v : Additive A) :
    (mulAutGL p A σ : Module.End (ZMod p) (Additive A)) v = Additive.ofMul (σ v.toMul) :=
  rfl

end Linear

section Group

variable {G : Type*} [Group G]

theorem conj_mem_of_forall_inv_conj_mem [Finite G] {H : Subgroup G} {y : G}
    (hy : ∀ v ∈ H, y⁻¹ * v * y ∈ H) {v : G} (hv : v ∈ H) : y * v * y⁻¹ ∈ H := by
  let f : H → H := fun w => ⟨y⁻¹ * w * y, hy w w.2⟩
  have hf : Function.Injective f := fun a b hab => Subtype.ext (by
    have h := congrArg Subtype.val hab
    simpa [f] using h)
  obtain ⟨w, hw⟩ := Finite.surjective_of_injective hf ⟨v, hv⟩
  have hw' : y⁻¹ * w * y = v := congrArg Subtype.val hw
  rw [← hw']
  simp [mul_assoc]

theorem mem_normalizer_of_forall_inv_conj_mem [Finite G] {H : Subgroup G} {y : G}
    (hy : ∀ v ∈ H, y⁻¹ * v * y ∈ H) : y ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => conj_mem_of_forall_inv_conj_mem hy hh, fun hh => ?_⟩
  simpa [mul_assoc] using hy _ hh

end Group

open CFSG.Open in
theorem exists_two_pow_conj_eq {G : Type*} [Group G] [Finite G] {Q X : Subgroup G} {e : ℕ}
    (hQ : IsElemAbelian 2 Q) (hQcard : Nat.card Q = 2 ^ e) (he : 1 ≤ e)
    (hXQ : ∀ x ∈ X, ∀ v ∈ Q, x⁻¹ * v * x ∈ Q) (hXcyclic : IsCyclic X)
    (hXregular : ∀ a ∈ (Q : Set G) \ {1}, ∀ b ∈ (Q : Set G) \ {1},
      ∃! x : X, (x : G)⁻¹ * a * x = b)
    {y : G} (hyQ : ∀ v ∈ Q, y⁻¹ * v * y ∈ Q) (hyX : ∀ x ∈ X, y⁻¹ * x * y ∈ X) :
    ∃ j : ℕ, ∀ x ∈ X, y⁻¹ * x * y = x ^ (2 ^ j) := by
  classical
  have : IsMulCommutative Q := hQ.1
  let : Module (ZMod 2) (Additive Q) := AddCommGroup.zmodModule (n := 2) fun v => by
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    exact Subtype.ext (hQ.2 _ v.toMul.2)
  have : Finite (Additive Q) := inferInstanceAs (Finite Q)
  have : Nontrivial Q := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [hQcard]
    exact Nat.one_lt_two_pow (by omega))
  obtain ⟨⟨v₀, hv₀Q⟩, hv₀1⟩ := exists_ne (1 : Q)
  replace hv₀1 : v₀ ≠ 1 := fun h => hv₀1 (Subtype.ext h)
  have : Nontrivial (Additive Q) := ⟨⟨Additive.ofMul ⟨v₀, hv₀Q⟩, 0, fun h =>
    hv₀1 (congrArg Subtype.val (congrArg Additive.toMul h))⟩⟩
  set N := Subgroup.normalizer (Q : Set G)
  have hXN : ∀ x ∈ X, x ∈ N := fun x hx => by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => by simpa using hXQ x⁻¹ (X.inv_mem hx) h hh, fun hh => ?_⟩
    simpa [mul_assoc] using hXQ x hx _ hh
  have hyN : y ∈ N := mem_normalizer_of_forall_inv_conj_mem hyQ
  let ρ : N →* LinearMap.GeneralLinearGroup (ZMod 2) (Additive Q) :=
    (mulAutGL 2 Q).comp Q.normalizerMonoidHom
  have hρ : ∀ (n : N) (v : Additive Q),
      ((((ρ n : LinearMap.GeneralLinearGroup (ZMod 2) (Additive Q)) :
        Module.End (ZMod 2) (Additive Q)) v).toMul : G) = (n : G) * (v.toMul : G) * (n : G)⁻¹ :=
    fun _ _ => rfl
  let T : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) (Additive Q)) :=
    (X.subgroupOf N).map ρ
  have hT : ∀ t ∈ T, ∃ (x : G) (hx : x ∈ X), ρ ⟨x, hXN x hx⟩ = t := by
    rintro t ⟨n, hn, rfl⟩
    exact ⟨n, hn, rfl⟩
  have hmemT : ∀ (x : G) (hx : x ∈ X), ρ ⟨x, hXN x hx⟩ ∈ T := fun x hx =>
    ⟨⟨x, hXN x hx⟩, hx, rfl⟩
  have hXcomm : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val ((inferInstance : IsMulCommutative X).is_comm.comm (⟨a, ha⟩ : X) ⟨b, hb⟩)
  have hcomm : ∀ g ∈ T, ∀ h ∈ T, g * h = h * g := by
    intro g hg h hh
    obtain ⟨a, ha, rfl⟩ := hT g hg
    obtain ⟨b, hb, rfl⟩ := hT h hh
    rw [← map_mul, ← map_mul]
    exact congrArg ρ (Subtype.ext (hXcomm a ha b hb))
  have hne : ∀ v : Additive Q, v ≠ 0 → (v.toMul : G) ∈ (Q : Set G) \ {1} := fun v hv =>
    ⟨v.toMul.2, fun h => hv (congrArg Additive.ofMul (Subtype.ext h))⟩
  have htrans : ∀ v w : Additive Q, v ≠ 0 → w ≠ 0 →
      ∃ t ∈ T, (t : Module.End (ZMod 2) (Additive Q)) v = w := by
    intro v w hv hw
    obtain ⟨x, hx, -⟩ := hXregular _ (hne v hv) _ (hne w hw)
    refine ⟨ρ ⟨(x : G)⁻¹, hXN _ (X.inv_mem x.2)⟩, hmemT _ (X.inv_mem x.2), ?_⟩
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [hρ]
    simpa using hx
  let g := ρ ⟨y⁻¹, N.inv_mem hyN⟩
  have hconj : ∀ (x : G) (hx : x ∈ X) (hx' : y⁻¹ * x * y ∈ X),
      g * ρ ⟨x, hXN x hx⟩ * g⁻¹ = ρ ⟨y⁻¹ * x * y, hXN _ hx'⟩ := by
    intro x hx hx'
    rw [← map_inv, ← map_mul, ← map_mul]
    exact congrArg ρ (Subtype.ext (by simp))
  have hconj' : ∀ (x : G) (hx : x ∈ X) (hx' : y * x * y⁻¹ ∈ X),
      g⁻¹ * ρ ⟨x, hXN x hx⟩ * g⁻¹⁻¹ = ρ ⟨y * x * y⁻¹, hXN _ hx'⟩ := by
    intro x hx hx'
    rw [inv_inv, ← map_inv, ← map_mul, ← map_mul]
    exact congrArg ρ (Subtype.ext (by simp))
  have hg : ∀ t ∈ T, g * t * g⁻¹ ∈ T := by
    intro t ht
    obtain ⟨x, hx, rfl⟩ := hT t ht
    rw [hconj x hx (hyX x hx)]
    exact hmemT _ (hyX x hx)
  have hg' : ∀ t ∈ T, g⁻¹ * t * g⁻¹⁻¹ ∈ T := by
    intro t ht
    obtain ⟨x, hx, rfl⟩ := hT t ht
    have hx' : y * x * y⁻¹ ∈ X := conj_mem_of_forall_inv_conj_mem hyX hx
    rw [hconj' x hx hx']
    exact hmemT _ hx'
  obtain ⟨j, hj⟩ := exists_pow_conj_eq_of_transitive hcomm htrans hg hg'
  refine ⟨j, fun x hx => ?_⟩
  have h1 := hj _ (hmemT x hx)
  rw [hconj x hx (hyX x hx), ← map_pow] at h1
  have h2 : (y⁻¹ * x * y) * v₀ * (y⁻¹ * x * y)⁻¹ = x ^ 2 ^ j * v₀ * (x ^ 2 ^ j)⁻¹ := by
    have h := congrArg (fun t : LinearMap.GeneralLinearGroup (ZMod 2) (Additive Q) =>
      (((t : Module.End (ZMod 2) (Additive Q)) (Additive.ofMul ⟨v₀, hv₀Q⟩)).toMul : G)) h1
    simpa only [hρ, toMul_ofMul, SubgroupClass.coe_pow] using h
  have hv₀ : v₀ ∈ (Q : Set G) \ {1} := ⟨hv₀Q, hv₀1⟩
  have hc : (y⁻¹ * x * y) * v₀ * (y⁻¹ * x * y)⁻¹ ∈ (Q : Set G) \ {1} := by
    refine ⟨?_, fun h => hv₀1 (conj_eq_one_iff.mp h)⟩
    simpa using hXQ _ (X.inv_mem (hyX x hx)) v₀ hv₀Q
  obtain ⟨z, -, hz⟩ := hXregular v₀ hv₀ _ hc
  have e1 := hz ⟨(y⁻¹ * x * y)⁻¹, X.inv_mem (hyX x hx)⟩ (by simp)
  have e2 := hz ⟨(x ^ 2 ^ j)⁻¹, X.inv_mem (X.pow_mem hx _)⟩ (by
    change ((x ^ 2 ^ j)⁻¹)⁻¹ * v₀ * (x ^ 2 ^ j)⁻¹ = _
    rw [inv_inv]
    exact h2.symm)
  exact inv_injective (congrArg Subtype.val (e1.trans e2.symm))

end CFSG.ShultStronglyClosedTI.CyclicSemiregular
