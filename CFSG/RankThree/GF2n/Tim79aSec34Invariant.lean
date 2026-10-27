module

public import CFSG.RankThree.GF2n.Tim79aCyclicDecomp

public section

namespace CFSG.RankThree.GF2n.Tim79a

theorem exists_invariant_subgroup_of_semiregular
    {G : Type} [Group G] [Finite G] (A : Subgroup G) (hA2 : ∀ x ∈ A, x * x = 1)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hA1 : A ≠ ⊥)
    (f : ℕ) (hf : 1 ≤ f) (h : G)
    (hhA : ∀ x ∈ A, h * x * h⁻¹ ∈ A)
    (hord : ∀ u ∈ A, h ^ (2 ^ f - 1) * u * (h ^ (2 ^ f - 1))⁻¹ = u)
    (hreg : ∀ i : ℕ, 0 < i → i < 2 ^ f - 1 → ∀ u ∈ A, h ^ i * u * (h ^ i)⁻¹ = u → u = 1) :
    ∃ A₁ : Subgroup G, A₁ ≤ A ∧ Nat.card ↥A₁ = 2 ^ f ∧
      ∀ i : ℕ, ∀ x ∈ A₁, h ^ i * x * (h ^ i)⁻¹ ∈ A₁ := by
  letI : CommGroup ↥A :=
    { (inferInstance : Group ↥A) with
      mul_comm := fun x y => Subtype.ext (hAab x x.2 y y.2) }
  have hsq : ∀ x : Additive ↥A, (2 : ℕ) • x = 0 := by
    intro x
    rw [two_nsmul]
    apply Additive.toMul.injective
    apply Subtype.ext
    exact hA2 ((Additive.toMul x : ↥A) : G) (Additive.toMul x).2
  letI : Module (ZMod 2) (Additive ↥A) := AddCommGroup.zmodModule hsq
  haveI : Finite (Additive ↥A) := Finite.of_equiv ↥A Additive.ofMul
  let cj : ↥A → ↥A := fun x => ⟨h * (x : G) * h⁻¹, hhA x x.2⟩
  have hcjinj : Function.Injective cj := by
    intro x y hxy
    apply Subtype.ext
    have h' : h * (x : G) * h⁻¹ = h * (y : G) * h⁻¹ := congrArg Subtype.val hxy
    exact mul_left_cancel (mul_right_cancel h')
  let cjH : ↥A →ₙ* ↥A :=
    { toFun := cj
      map_mul' := fun x y => Subtype.ext (by
        show h * ((x : G) * (y : G)) * h⁻¹ = h * (x : G) * h⁻¹ * (h * (y : G) * h⁻¹)
        group) }
  let cjM : ↥A ≃* ↥A :=
    MulEquiv.ofBijective cjH ⟨hcjinj, Finite.surjective_of_injective hcjinj⟩
  let cjA : Additive ↥A ≃+ Additive ↥A := MulEquiv.toAdditive cjM
  let hE : Additive ↥A ≃ₗ[ZMod 2] Additive ↥A :=
    cjA.toLinearEquiv (fun c x => ZMod.map_smul cjA c x)
  have hEstep : ∀ w : Additive ↥A,
      ((Additive.toMul (hE w) : ↥A) : G) = h * ((Additive.toMul w : ↥A) : G) * h⁻¹ :=
    fun w => rfl
  have hEpow : ∀ (n : ℕ) (v : Additive ↥A), (hE ^ (n + 1)) v = hE ((hE ^ n) v) :=
    fun n v => congrArg (fun g : Additive ↥A ≃ₗ[ZMod 2] Additive ↥A => g v) (pow_succ' hE n)
  have key : ∀ (i : ℕ) (v : Additive ↥A),
      ((Additive.toMul ((hE ^ i) v) : ↥A) : G) =
        h ^ i * ((Additive.toMul v : ↥A) : G) * (h ^ i)⁻¹ := by
    intro i
    induction i with
    | zero => intro v; simp
    | succ n ih =>
      intro v
      rw [hEpow, hEstep, ih v, pow_succ']
      group
  have hmem : ∀ i : ℕ, ∀ x ∈ A, h ^ i * x * (h ^ i)⁻¹ ∈ A := by
    intro i
    induction i with
    | zero => intro x hx; simpa using hx
    | succ n ih =>
      intro x hx
      have e : h ^ (n + 1) * x * (h ^ (n + 1))⁻¹ = h * (h ^ n * x * (h ^ n)⁻¹) * h⁻¹ := by
        rw [pow_succ']
        group
      rw [e]
      exact hhA _ (ih x hx)
  have hE1 : hE ^ (2 ^ f - 1) = 1 := by
    refine LinearEquiv.ext fun v => ?_
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [key]
    exact hord _ (Additive.toMul v).2
  obtain ⟨u, hu, hu1⟩ : ∃ u ∈ A, u ≠ 1 := by
    by_contra hcon
    apply hA1
    rw [eq_bot_iff]
    intro x hx
    refine Subgroup.mem_bot.mpr ?_
    by_contra hx1
    exact hcon ⟨x, hx, hx1⟩
  have h2f : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hpos : 0 < 2 ^ f - 1 := by
    generalize 2 ^ f = t at h2f ⊢
    omega
  have hordE : orderOf hE = 2 ^ f - 1 := by
    rw [orderOf_eq_iff hpos]
    refine ⟨hE1, fun m hmlt hm0 hEm => ?_⟩
    have hv : (hE ^ m) (Additive.ofMul (⟨u, hu⟩ : ↥A)) = Additive.ofMul (⟨u, hu⟩ : ↥A) :=
      congrArg (fun g : Additive ↥A ≃ₗ[ZMod 2] Additive ↥A => g (Additive.ofMul (⟨u, hu⟩ : ↥A)))
        hEm
    have h1 := key m (Additive.ofMul (⟨u, hu⟩ : ↥A))
    rw [hv] at h1
    exact hu1 (hreg m hm0 hmlt u hu h1.symm)
  have hfpfE : ∀ i : ℕ, 0 < i → i < 2 ^ f - 1 → ∀ x : Additive ↥A, (hE ^ i) x = x → x = 0 := by
    intro i hi0 hi1 v hv
    have h1 := key i v
    rw [hv] at h1
    have h2 := hreg i hi0 hi1 _ (Additive.toMul v).2 h1.symm
    apply Additive.toMul.injective
    apply Subtype.ext
    exact h2
  obtain ⟨ι, _, S, hinv, hcard, _, htop⟩ :=
    cyclicSemiregularDecomp_holds (Additive ↥A) f hf hE hordE hfpfE
  have hne : Nonempty ι := by
    by_contra hcon
    haveI : IsEmpty ι := not_nonempty_iff.mp hcon
    have hv : (Additive.ofMul (⟨u, hu⟩ : ↥A) : Additive ↥A) ∈ ⨆ j, S j := by
      rw [htop]
      exact Submodule.mem_top
    rw [iSup_of_empty, Submodule.mem_bot] at hv
    exact hu1 (congrArg (fun w : Additive ↥A => ((Additive.toMul w : ↥A) : G)) hv)
  obtain ⟨j⟩ := hne
  let B : Subgroup ↥A :=
    { carrier := {x | Additive.ofMul x ∈ S j}
      mul_mem' := fun {x y} hx hy => by
        have hx' : Additive.ofMul x ∈ S j := hx
        have hy' : Additive.ofMul y ∈ S j := hy
        show Additive.ofMul (x * y) ∈ S j
        exact (S j).add_mem hx' hy'
      one_mem' := by
        show Additive.ofMul (1 : ↥A) ∈ S j
        exact (S j).zero_mem
      inv_mem' := fun {x} hx => by
        have hx' : Additive.ofMul x ∈ S j := hx
        show Additive.ofMul (x⁻¹) ∈ S j
        exact (S j).neg_mem hx' }
  have hBcard : Nat.card ↥B = Nat.card ↥(S j) :=
    Nat.card_congr
      { toFun := fun x => ⟨Additive.ofMul (x : ↥A), x.2⟩
        invFun := fun z => ⟨Additive.toMul (z : Additive ↥A), z.2⟩
        left_inv := fun x => rfl
        right_inv := fun z => rfl }
  have hBequiv := Subgroup.equivMapOfInjective B A.subtype A.subtype_injective
  have hpowS : ∀ (i : ℕ) (v : Additive ↥A), v ∈ S j → (hE ^ i) v ∈ S j := by
    intro i
    induction i with
    | zero => intro v hv; simpa using hv
    | succ n ih =>
      intro v hv
      rw [hEpow]
      exact hinv j _ (ih v hv)
  refine ⟨B.map A.subtype, Subgroup.map_subtype_le B, ?_, ?_⟩
  · rw [← Nat.card_congr hBequiv.toEquiv, hBcard, hcard j]
  · intro i x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    have hyS : Additive.ofMul y ∈ S j := hy
    have hBm : (⟨h ^ i * (y : G) * (h ^ i)⁻¹, hmem i (y : G) y.2⟩ : ↥A) ∈ B := by
      show Additive.ofMul (⟨h ^ i * (y : G) * (h ^ i)⁻¹, hmem i (y : G) y.2⟩ : ↥A) ∈ S j
      have e1 : Additive.toMul ((hE ^ i) (Additive.ofMul y)) =
          (⟨h ^ i * (y : G) * (h ^ i)⁻¹, hmem i (y : G) y.2⟩ : ↥A) :=
        Subtype.ext (key i (Additive.ofMul y))
      have e2 : (Additive.ofMul (⟨h ^ i * (y : G) * (h ^ i)⁻¹, hmem i (y : G) y.2⟩ : ↥A) :
          Additive ↥A) = (hE ^ i) (Additive.ofMul y) := by
        apply Additive.toMul.injective
        exact e1.symm
      rw [e2]
      exact hpowS i _ hyS
    exact Subgroup.mem_map.mpr ⟨_, hBm, rfl⟩

end CFSG.RankThree.GF2n.Tim79a
