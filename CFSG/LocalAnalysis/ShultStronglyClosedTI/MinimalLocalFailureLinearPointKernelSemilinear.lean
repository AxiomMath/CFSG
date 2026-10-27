module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureFieldPrimeFrobenius

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.LinearChain

open CFSG.Open
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ShultStronglyClosedTI.CyclicSemiregular
open scoped IsMulCommutative

theorem semilinear_of_transitive_commutative {B V : Type} [Group B] [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V] {e : ℕ} (he : 1 ≤ e)
    (hdim : Module.finrank (ZMod 2) V = e)
    (ρ : B →* LinearMap.GeneralLinearGroup (ZMod 2) V) {X : Subgroup B} [hXn : X.Normal]
    (hXcomm : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a)
    (htrans : ∀ v w : V, v ≠ 0 → w ≠ 0 →
      ∃ x ∈ X, ((ρ x : LinearMap.GeneralLinearGroup (ZMod 2) V) : Module.End (ZMod 2) V) v = w)
    (hXinj : ∀ x ∈ X, ρ x = 1 → x = 1) (hXcard : Nat.card X = 2 ^ e - 1) :
    ∃ (k₀ : Type) (_ : Field k₀) (_ : Finite k₀), Nat.card k₀ = 2 ^ e ∧
      ∃ (ev : k₀ ≃+ V) (ι : B →* k₀ˣ ⋊[ringAutUnits k₀] RingAut k₀),
        ι.ker = ρ.ker ∧
        (∀ (b : B) (a : k₀),
          ((ρ b : LinearMap.GeneralLinearGroup (ZMod 2) V) : Module.End (ZMod 2) V) (ev a) =
            ev (((ι b).left : k₀) * (ι b).right a)) ∧
        X.map ι = (SemidirectProduct.inl : k₀ˣ →* _).range := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : FiniteDimensional (ZMod 2) V := Module.Finite.of_finite
  set T : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V) := X.map ρ with hTdef
  set U : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V) := ρ.range with hUdef
  have hTU : T ≤ U := Subgroup.map_le_range ρ _
  have hTn : (T.subgroupOf U).Normal := by
    constructor
    intro t ht u
    rw [Subgroup.mem_subgroupOf] at ht ⊢
    obtain ⟨x, hx, hxt⟩ := ht
    obtain ⟨b, hb⟩ := u.2
    refine ⟨b * x * b⁻¹, hXn.conj_mem x hx b, ?_⟩
    rw [map_mul, map_mul, map_inv, hb, hxt]
    rfl
  have hcomm : ∀ g ∈ T, ∀ h ∈ T, g * h = h * g := by
    rintro g ⟨a, ha, rfl⟩ h ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hXcomm a ha b hb]
  have hirr : ∀ W : Submodule (ZMod 2) V,
      (∀ g ∈ T, ∀ w ∈ W, (g : Module.End (ZMod 2) V) w ∈ W) → W = ⊥ ∨ W = ⊤ := by
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
    obtain ⟨x, hx, hxv⟩ := htrans w v hw0 hv
    rw [← hxv]
    exact hW _ ⟨x, hx, rfl⟩ w hwW
  obtain ⟨hF, hcardF, hev, -, hcompat, hkerσ, -, hι⟩ :=
    abelian_irreducible_normalizer_semilinear he hdim hTU hTn hcomm hirr
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  obtain ⟨s₀, hs₀⟩ := exists_ne (0 : V)
  obtain ⟨ι₀, hι₀inj, hι₀⟩ := hι s₀ hs₀
  have : Finite (operatorAlgebra T) := Nat.finite_of_card_ne_zero (by rw [hcardF]; positivity)
  let evHom : operatorAlgebra T →+ V :=
    { toFun := fun a => (a : Module.End (ZMod 2) V) s₀
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let ev : operatorAlgebra T ≃+ V := AddEquiv.ofBijective evHom (hev s₀ hs₀)
  have hev_apply : ∀ a : operatorAlgebra T, ev a = (a : Module.End (ZMod 2) V) s₀ := fun _ => rfl
  obtain ⟨ι, hιdef⟩ : ∃ ι, ι = ι₀.comp ρ.rangeRestrict := ⟨_, rfl⟩
  have hιx : ∀ x : B, ι x = ι₀ (ρ.rangeRestrict x) := fun x => by rw [hιdef]; rfl
  have hker : ι.ker = ρ.ker := by
    ext b
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hιx, map_eq_one_iff ι₀ hι₀inj]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hcompat' : ∀ (b : B) (a : operatorAlgebra T),
      ((ρ b : LinearMap.GeneralLinearGroup (ZMod 2) V) : Module.End (ZMod 2) V) (ev a) =
        ev (((ι b).left : operatorAlgebra T) * (ι b).right a) := by
    intro b a
    rw [hιx]
    generalize hu : ρ.rangeRestrict b = u
    have hub : ((u : LinearMap.GeneralLinearGroup (ZMod 2) V) : Module.End (ZMod 2) V) =
        ((ρ b : LinearMap.GeneralLinearGroup (ZMod 2) V) : Module.End (ZMod 2) V) := by
      rw [← hu]
      rfl
    have h2 := hcompat u a s₀
    rw [← (hι₀ u).2, hub] at h2
    rw [hev_apply, h2, hev_apply, (hι₀ u).1, hF.mul_comm (((ι₀ u).left : _) : operatorAlgebra T)]
    rfl
  have hle : X.map ι ≤ (SemidirectProduct.inl : _ →* _).range := by
    rintro _ ⟨x, hx, rfl⟩
    have hright : (ι x).right = 1 := by
      have h1 := (hι₀ (ρ.rangeRestrict x)).1
      rw [hιx, h1, hkerσ, MonoidHom.coe_rangeRestrict]
      exact Algebra.subset_adjoin ⟨ρ x, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨(ι x).left, SemidirectProduct.ext rfl (by rw [SemidirectProduct.right_inl, hright])⟩
  have hinj : Set.InjOn ι (X : Set B) := by
    intro x₁ hx₁ x₂ hx₂ h12
    have hk : x₁⁻¹ * x₂ ∈ ρ.ker := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, h12, inv_mul_cancel]
    have h1 := hXinj _ (X.mul_mem (X.inv_mem hx₁) hx₂) hk
    rw [inv_mul_eq_one] at h1
    exact h1
  have hcard1 : Nat.card (X.map ι) = Nat.card X := by
    have h1 : Nat.card (X.map ι) = Nat.card (ι '' (X : Set B)) := by
      rw [← Subgroup.coe_map]
      rfl
    rw [h1, Nat.card_image_of_injOn hinj]
    rfl
  let : Field (operatorAlgebra T) := hF.toField
  have hcard2 : Nat.card (SemidirectProduct.inl : (operatorAlgebra T)ˣ →*
      (operatorAlgebra T)ˣ ⋊[ringAutUnits (operatorAlgebra T)] RingAut (operatorAlgebra T)).range =
      2 ^ e - 1 := by
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective SemidirectProduct.inl_injective,
      Subgroup.card_top, Nat.card_units, hcardF]
  have : Finite (SemidirectProduct.inl : (operatorAlgebra T)ˣ →*
      (operatorAlgebra T)ˣ ⋊[ringAutUnits (operatorAlgebra T)] RingAut (operatorAlgebra T)).range :=
    Nat.finite_of_card_ne_zero (by
      rw [hcard2]
      have := Nat.one_lt_two_pow (n := e) (by omega)
      omega)
  have himage : X.map ι = (SemidirectProduct.inl : _ →* _).range :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcard1, hcard2, hXcard])
  exact ⟨operatorAlgebra T, hF.toField, inferInstance, hcardF, ev, ι, hker, hcompat', himage⟩

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem eq_one_of_regular_of_mem_centralizer {Q X : Subgroup G}
    (hXregular : ∀ a ∈ (Q : Set G) \ {1}, ∀ b ∈ (Q : Set G) \ {1},
      ∃! x : X, (x : G)⁻¹ * a * x = b)
    {v₀ : G} (hv₀ : v₀ ∈ (Q : Set G) \ {1}) {w : G} (hwX : w ∈ X)
    (hwC : w ∈ Subgroup.centralizer (Q : Set G)) : w = 1 := by
  obtain ⟨y, -, hyuniq⟩ := hXregular v₀ hv₀ v₀ hv₀
  have hw : w⁻¹ * v₀ * w = v₀ := by
    have hc := (Subgroup.mem_centralizer_iff.mp hwC) v₀ hv₀.1
    rw [mul_assoc, hc, inv_mul_cancel_left]
  have e1 := hyuniq ⟨w, hwX⟩ hw
  have e2 := hyuniq 1 (by simp)
  exact congrArg Subtype.val (e1.trans e2.symm)

theorem regular_cyclic_semilinear_embedding {Q X B : Subgroup G} {e : ℕ}
    (hQ : IsElemAbelian 2 Q) (hQcard : Nat.card Q = 2 ^ e) (he : 1 ≤ e)
    (hBQ : B ≤ Subgroup.normalizer (Q : Set G))
    (hXB : X ≤ B) (hXnormal : (X.subgroupOf B).Normal) (hXcyclic : IsCyclic X)
    (hXcard : Nat.card X = Nat.card Q - 1)
    (hXregular : ∀ a ∈ (Q : Set G) \ {1}, ∀ b ∈ (Q : Set G) \ {1},
      ∃! x : X, (x : G)⁻¹ * a * x = b) :
    ∃ (k₀ : Type) (_ : Field k₀) (_ : Finite k₀), Nat.card k₀ = Nat.card Q ∧
      ∃ (φ : Q ≃* Multiplicative k₀) (ι : B →* k₀ˣ ⋊[ringAutUnits k₀] RingAut k₀),
        ι.ker = (Subgroup.centralizer (Q : Set G)).subgroupOf B ∧
        (∀ (b : B) (x y : Q), (y : G) = (b : G) * x * (b : G)⁻¹ →
          (φ y).toAdd = ((ι b).left : k₀) * (ι b).right (φ x).toAdd) ∧
        (X.subgroupOf B).map ι = (SemidirectProduct.inl : k₀ˣ →* _).range := by
  classical
  have : IsMulCommutative Q := hQ.1
  let : Module (ZMod 2) (Additive Q) := AddCommGroup.zmodModule (n := 2) fun v => by
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    exact Subtype.ext (hQ.2 _ v.toMul.2)
  have : Finite (Additive Q) := inferInstanceAs (Finite Q)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ρ : B →* LinearMap.GeneralLinearGroup (ZMod 2) (Additive Q) :=
    ((mulAutGL 2 Q).comp Q.normalizerMonoidHom).comp (Subgroup.inclusion hBQ)
  have hρ : ∀ (b : B) (v : Additive Q),
      ((((ρ b : LinearMap.GeneralLinearGroup (ZMod 2) (Additive Q)) :
        Module.End (ZMod 2) (Additive Q)) v).toMul : G) = (b : G) * (v.toMul : G) * (b : G)⁻¹ :=
    fun _ _ => rfl
  have hρker : ∀ b : B, ρ b = 1 ↔ (b : G) ∈ Subgroup.centralizer (Q : Set G) := by
    intro b
    rw [Subgroup.mem_centralizer_iff]
    constructor
    · intro hb x hx
      have h1 := congrArg (fun g : LinearMap.GeneralLinearGroup (ZMod 2) (Additive Q) =>
        (((g : Module.End (ZMod 2) (Additive Q)) (Additive.ofMul ⟨x, hx⟩)).toMul : G)) hb
      simp only [hρ, toMul_ofMul, Units.val_one, Module.End.one_apply] at h1
      calc x * (b : G) = (b : G) * x * (b : G)⁻¹ * b := by rw [h1]
        _ = b * x := by group
    · intro hb
      apply Units.ext
      apply LinearMap.ext
      intro v
      apply Additive.toMul.injective
      apply Subtype.ext
      rw [hρ]
      change (b : G) * (v.toMul : G) * (b : G)⁻¹ = (v.toMul : G)
      rw [← hb _ v.toMul.2, mul_inv_cancel_right]
  have hne : ∀ v : Additive Q, v ≠ 0 → (v.toMul : G) ∈ (Q : Set G) \ {1} := fun v hv =>
    ⟨v.toMul.2, fun h => hv (congrArg Additive.ofMul (Subtype.ext h))⟩
  have hXcomm : ∀ a ∈ X.subgroupOf B, ∀ b ∈ X.subgroupOf B, a * b = b * a := by
    intro a ha b hb
    have h := (IsCyclic.commGroup (α := X)).mul_comm ⟨(a : G), ha⟩ ⟨(b : G), hb⟩
    apply Subtype.ext
    change (a : G) * b = b * a
    exact congrArg Subtype.val h
  have htrans : ∀ v w : Additive Q, v ≠ 0 → w ≠ 0 → ∃ x ∈ X.subgroupOf B,
      ((ρ x : LinearMap.GeneralLinearGroup (ZMod 2) (Additive Q)) :
        Module.End (ZMod 2) (Additive Q)) v = w := by
    intro v w hv hw
    obtain ⟨x, hx, -⟩ := hXregular _ (hne v hv) _ (hne w hw)
    have hxB : ((x : G))⁻¹ ∈ B := B.inv_mem (hXB x.2)
    refine ⟨⟨(x : G)⁻¹, hxB⟩, X.inv_mem x.2, ?_⟩
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [hρ]
    simpa using hx
  have : Nontrivial Q := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [hQcard]
    exact Nat.one_lt_two_pow (by omega))
  obtain ⟨⟨v₀, hv₀Q⟩, hv₀1⟩ := exists_ne (1 : Q)
  have hv₀ : v₀ ∈ (Q : Set G) \ {1} := ⟨hv₀Q, fun h => hv₀1 (Subtype.ext h)⟩
  have hXinj : ∀ x ∈ X.subgroupOf B, ρ x = 1 → x = 1 := fun x hx h1 =>
    Subtype.ext (eq_one_of_regular_of_mem_centralizer hXregular hv₀ hx ((hρker x).mp h1))
  have hXcard' : Nat.card (X.subgroupOf B) = 2 ^ e - 1 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXB).toEquiv, hXcard, hQcard]
  have hdim : Module.finrank (ZMod 2) (Additive Q) = e := by
    have h1 := FiniteField.pow_finrank_eq_natCard 2 (Additive Q)
    have h2 : Nat.card (Additive Q) = Nat.card Q := rfl
    rw [h2, hQcard] at h1
    exact Nat.pow_right_injective (le_refl 2) h1
  obtain ⟨k₀, _, _, hk₀, ev, ι, hker, hcompat, himage⟩ :=
    semilinear_of_transitive_commutative he hdim ρ hXcomm htrans hXinj hXcard'
  let φ : Q ≃* Multiplicative k₀ :=
    (MulEquiv.multiplicativeAdditive Q).symm.trans (AddEquiv.toMultiplicative ev.symm)
  have hφ : ∀ x : Q, ev (φ x).toAdd = Additive.ofMul x := fun x => by
    change ev (ev.symm (Additive.ofMul x)) = Additive.ofMul x
    exact ev.apply_symm_apply _
  refine ⟨k₀, inferInstance, inferInstance, hk₀.trans hQcard.symm, φ, ι, ?_, ?_, himage⟩
  · rw [hker]
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hρker b
  · intro b x y hy
    apply ev.injective
    rw [← hcompat, hφ, hφ]
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [hρ]
    exact hy

end CFSG.ShultStronglyClosedTI.LinearChain
