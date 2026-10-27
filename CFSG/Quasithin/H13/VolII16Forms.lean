module

public import CFSG.Quasithin.Background.JonesParshallSmallSL

public section

noncomputable section

namespace CFSG.Quasithin.H13.VolI

open CFSG.Quasithin CFSG.Quasithin.JonesParshall Matrix

theorem zmod2_add_self (u : ZMod 2) : u + u = 0 := by
  revert u
  decide

theorem zmod2_val_nsmul (y : ZMod 2) : (y.val : ℕ) • (1 : ZMod 2) = y := by
  revert y
  decide

theorem zmod2_cocycle (p t r : ZMod 2) : p + t = r + t + (p + r) := by
  revert p t r
  decide

theorem zmod2_swap (p q r t : ZMod 2) (h : p + q = r + t) : p + r = q + t := by
  revert p q r t
  decide

theorem zmod2_add_neg (u : ZMod 2) : u + -u = 0 := by
  revert u
  decide

theorem zmod2_neg_eq_zero (u : ZMod 2) (h : u = 0) : -u = 0 := by
  rw [h]
  decide

theorem zmod2_eq_one_of_ne_zero (u : ZMod 2) (h : u ≠ 0) : u = 1 := by
  revert u
  decide

theorem zmod2_one_add_one : (1 : ZMod 2) + 1 = 0 := by decide

theorem zmod2_neg {ι : Type*} (m : ι → ZMod 2) : -m = m :=
  funext fun i => ZMod.neg_eq_self_mod_two (m i)

theorem muF2_apply' {n : ℕ} (s : SpecialLinearGroup (Fin n) (ZMod 2)) (v : Fin n → ZMod 2) :
    muF2 n s v = (s : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v := by
  rw [← Matrix.smul_eq_mulVec, ← Matrix.SpecialLinearGroup.smul_def]
  rfl

section Forms

variable {G : Type*} [Group G] {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Type*}
  [AddCommGroup A]

@[expose] def formCocycle (ρA : G →* AddMonoid.End A) (s : ι → A) (a : A →+ ZMod 2) (g : G) :
    ι → ZMod 2 :=
  fun i => a (ρA g⁻¹ (s i)) + a (s i)

variable {ρA : G →* AddMonoid.End A} {π : A →+ (ι → ZMod 2)}
  {μ : G → Matrix ι ι (ZMod 2)}

theorem formCocycle_dot (hfix : ∀ g a, π a = 0 → ρA g a = a) {s : ι → A}
    (hs : ∀ i, π (s i) = Pi.single i 1) (a : A →+ ZMod 2) (g : G) (v : A) :
    a (ρA g⁻¹ v) + a v = formCocycle ρA s a g ⬝ᵥ π v := by
  classical
  let c : A →+ ZMod 2 := AddMonoidHom.mk' (fun v => a (ρA g⁻¹ v) + a v)
    (fun u v => by simp only [map_add]; abel)
  have hc : ∀ v, c v = a (ρA g⁻¹ v) + a v := fun _ => rfl
  have hc0 : ∀ v, π v = 0 → c v = 0 := fun v hv => by
    rw [hc, hfix g⁻¹ v hv, zmod2_add_self]
  set y := π v with hy
  let v' : A := ∑ i, (y i).val • s i
  have hv' : π v' = y := by
    simp only [v', map_sum, map_nsmul, hs]
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_ite, smul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true, zmod2_val_nsmul]
  have hdiff : π (v + v') = 0 := by
    rw [map_add, hv', ← hy]
    funext j
    exact zmod2_add_self (y j)
  have h1 := hc0 _ hdiff
  rw [map_add] at h1
  have h1' : c v = c v' := by
    have := zmod2_swap (c v) (c v') 0 0 (by rw [h1, zero_add])
    simpa using this
  rw [← hc, h1']
  simp only [v', map_sum, map_nsmul, dotProduct, formCocycle]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [nsmul_eq_mul, mul_comm, ← zmod2_val_nsmul (y i), nsmul_eq_mul, mul_one]
  simp [hc]

theorem formCocycle_mul (hfix : ∀ g a, π a = 0 → ρA g a = a)
    (hπρ : ∀ g a, π (ρA g a) = μ g *ᵥ π a) {s : ι → A}
    (hs : ∀ i, π (s i) = Pi.single i 1) (a : A →+ ZMod 2) (g h : G) :
    formCocycle ρA s a (g * h) = formCocycle ρA s a g + (μ g⁻¹)ᵀ *ᵥ formCocycle ρA s a h := by
  funext i
  have e1 : formCocycle ρA s a (g * h) i =
      formCocycle ρA s a g i + (a (ρA h⁻¹ (ρA g⁻¹ (s i))) + a (ρA g⁻¹ (s i))) := by
    simp only [formCocycle, _root_.mul_inv_rev, map_mul]
    exact zmod2_cocycle _ _ _
  have e2 : a (ρA h⁻¹ (ρA g⁻¹ (s i))) + a (ρA g⁻¹ (s i)) =
      ((μ g⁻¹)ᵀ *ᵥ formCocycle ρA s a h) i := by
    rw [formCocycle_dot hfix hs, hπρ, hs, dotProduct_mulVec, ← Matrix.mulVec_transpose,
      dotProduct_single, mul_one]
  rw [Pi.add_apply, e1, e2]

omit [Fintype ι] [DecidableEq ι] in
theorem formCocycle_add (s : ι → A) (a b : A →+ ZMod 2) :
    formCocycle ρA s (a + b) = formCocycle ρA s a + formCocycle ρA s b := by
  funext g i
  simp only [formCocycle, AddMonoidHom.add_apply, Pi.add_apply]
  abel

variable {G' : Type*} [Group G'] {ν : G' →* AddMonoid.End (ι → ZMod 2)} {θ : G ≃* G'}

@[expose] def transCocycle (θ : G ≃* G') (ρA : G →* AddMonoid.End A) (s : ι → A)
    (a : A →+ ZMod 2) : G' → (ι → ZMod 2) :=
  fun t => formCocycle ρA s a (θ.symm t)

omit [Fintype ι] [DecidableEq ι] in
theorem transCocycle_add (s : ι → A) (a b : A →+ ZMod 2) :
    transCocycle θ ρA s (a + b) = transCocycle θ ρA s a + transCocycle θ ρA s b := by
  funext t
  simp only [transCocycle, formCocycle_add, Pi.add_apply]

theorem transCocycle_mem_Z1A (hν : ∀ g x, ν (θ g) x = (μ g⁻¹)ᵀ *ᵥ x)
    (hfix : ∀ g a, π a = 0 → ρA g a = a) (hπρ : ∀ g a, π (ρA g a) = μ g *ᵥ π a)
    {s : ι → A} (hs : ∀ i, π (s i) = Pi.single i 1) (a : A →+ ZMod 2) :
    transCocycle θ ρA s a ∈ Z1A ν := by
  intro t u
  obtain ⟨g, rfl⟩ := θ.surjective t
  obtain ⟨h, rfl⟩ := θ.surjective u
  show formCocycle ρA s a (θ.symm (θ g * θ h)) = formCocycle ρA s a (θ.symm (θ g)) +
    ν (θ g) (formCocycle ρA s a (θ.symm (θ h)))
  rw [← map_mul, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply,
    formCocycle_mul hfix hπρ hs, hν]

theorem exists_invariant_of_mem_B1A (hν : ∀ g x, ν (θ g) x = (μ g⁻¹)ᵀ *ᵥ x)
    (hfix : ∀ g a, π a = 0 → ρA g a = a) (hπρ : ∀ g a, π (ρA g a) = μ g *ᵥ π a)
    {s : ι → A} (hs : ∀ i, π (s i) = Pi.single i 1) (a : A →+ ZMod 2)
    (hB : transCocycle θ ρA s a ∈ B1A ν) :
    ∃ a' : A →+ ZMod 2, (∀ g v, a' (ρA g v) = a' v) ∧ ∀ v, π v = 0 → a' v = a v := by
  obtain ⟨m, hm⟩ := hB
  have hx : ∀ g, formCocycle ρA s a g = (μ g⁻¹)ᵀ *ᵥ m + m := fun g => by
    have h1 := congrFun hm (θ g)
    change ν (θ g) m - m = _ at h1
    rw [hν] at h1
    have h2 : transCocycle θ ρA s a (θ g) = formCocycle ρA s a g := by
      show formCocycle ρA s a (θ.symm (θ g)) = _
      rw [MulEquiv.symm_apply_apply]
    rw [← h2, ← h1, sub_eq_add_neg]
    congr 1
    exact zmod2_neg m
  let φ : A →+ ZMod 2 :=
    { toFun := fun v => m ⬝ᵥ π v
      map_zero' := by simp
      map_add' := fun u v => by simp [dotProduct_add] }
  have hφ : ∀ v, φ v = m ⬝ᵥ π v := fun _ => rfl
  refine ⟨a + φ, fun g v => ?_, fun v hv => ?_⟩
  · have h1 : a (ρA g v) + a v = formCocycle ρA s a g⁻¹ ⬝ᵥ π v := by
      have := formCocycle_dot hfix hs a g⁻¹ v
      rwa [inv_inv] at this
    have h2 : φ (ρA g v) + φ v = ((μ g)ᵀ *ᵥ m + m) ⬝ᵥ π v := by
      rw [hφ, hφ, hπρ, dotProduct_mulVec, ← Matrix.mulVec_transpose, add_dotProduct]
    have h3 := hx g⁻¹
    rw [inv_inv] at h3
    have h4 : a (ρA g v) + a v = φ (ρA g v) + φ v := by rw [h1, h2, h3]
    simp only [AddMonoidHom.add_apply]
    exact zmod2_swap _ _ _ _ h4
  · simp [hφ, hv]

end Forms

section Covering

variable {G : Type*} [Group G] {ι : Type*} [Fintype ι] [DecidableEq ι] {W : Type*}
  [CommGroup W]

abbrev modTwoW (hW2 : ∀ w : W, w ^ 2 = 1) : Module (ZMod 2) (Additive W) :=
  AddCommGroup.zmodModule (fun a => by
    rw [two_nsmul]
    have h := hW2 (Additive.toMul a)
    rw [pow_two] at h
    exact congrArg Additive.ofMul h)

@[expose] def addAct (ρ : G →* MulAut W) : G →* AddMonoid.End (Additive W) where
  toFun g := ((ρ g : MulAut W).toMonoidHom).toAdditive
  map_one' := by rw [map_one]; rfl
  map_mul' a b := by rw [map_mul]; rfl

theorem addAct_ofMul (ρ : G →* MulAut W) (g : G) (w : W) :
    addAct ρ g (Additive.ofMul w) = Additive.ofMul (ρ g w) := rfl

@[expose] def addMap (β : W →* Multiplicative (ι → ZMod 2)) : Additive W →+ (ι → ZMod 2) :=
  (MonoidHom.toAdditive β).comp (AddMonoidHom.id _)

omit [Fintype ι] [DecidableEq ι] in
theorem addMap_ofMul (β : W →* Multiplicative (ι → ZMod 2)) (w : W) :
    addMap β (Additive.ofMul w) = Multiplicative.toAdd (β w) := rfl

variable {ρ : G →* MulAut W} {β : W →* Multiplicative (ι → ZMod 2)} {Z : Subgroup W}
  {μ : G → Matrix ι ι (ZMod 2)} {G' : Type*} [Group G']
  {ν : G' →* AddMonoid.End (ι → ZMod 2)} {θ : G ≃* G'}

theorem invariant_form_eq_zero
    (hgen : ∀ w : W, w ∈ Subgroup.closure {x | ∃ g v, x = ρ g v * v⁻¹})
    {a' : Additive W →+ ZMod 2} (ha' : ∀ g v, a' (addAct ρ g v) = a' v) (w : W) :
    a' (Additive.ofMul w) = 0 := by
  let S : Subgroup W :=
    { carrier := {v | a' (Additive.ofMul v) = 0}
      one_mem' := by
        show a' (Additive.ofMul 1) = 0
        rw [ofMul_one, map_zero]
      mul_mem' := fun {u v} hu hv => by
        show a' (Additive.ofMul (u * v)) = 0
        rw [ofMul_mul, map_add]
        rw [show a' (Additive.ofMul u) = 0 from hu, show a' (Additive.ofMul v) = 0 from hv,
          add_zero]
      inv_mem' := fun {u} hu => by
        show a' (Additive.ofMul u⁻¹) = 0
        rw [ofMul_inv, map_neg]
        exact zmod2_neg_eq_zero _ hu }
  have hS : Subgroup.closure {x | ∃ g v, x = ρ g v * v⁻¹} ≤ S := by
    rw [Subgroup.closure_le]
    rintro _ ⟨g, v, rfl⟩
    show a' (Additive.ofMul (ρ g v * v⁻¹)) = 0
    rw [ofMul_mul, ofMul_inv, map_add, map_neg, ← addAct_ofMul, ha']
    exact zmod2_add_neg _
  exact hS (hgen w)

omit [Fintype ι] in
theorem exists_lifts (hβs : Function.Surjective β) :
    ∃ s : ι → Additive W, ∀ i, addMap β (s i) = Pi.single i 1 := by
  classical
  have h : ∀ i : ι, ∃ s : Additive W, addMap β s = Pi.single i 1 := fun i => by
    obtain ⟨w, hw⟩ := hβs (Multiplicative.ofAdd (Pi.single i 1))
    exact ⟨Additive.ofMul w, by rw [addMap_ofMul, hw]; rfl⟩
  choose s hs using h
  exact ⟨s, hs⟩

theorem eq_bot_of_Z1A_eq_B1A (hν : ∀ g x, ν (θ g) x = (μ g⁻¹)ᵀ *ᵥ x) (hZB : Z1A ν = B1A ν)
    (hW2 : ∀ w : W, w ^ 2 = 1) (hβs : Function.Surjective β) (hβk : ∀ w, β w = 1 ↔ w ∈ Z)
    (hZfix : ∀ g, ∀ z ∈ Z, ρ g z = z)
    (hβe : ∀ g w, Multiplicative.toAdd (β (ρ g w)) = μ g *ᵥ Multiplicative.toAdd (β w))
    (hgen : ∀ w : W, w ∈ Subgroup.closure {x | ∃ g v, x = ρ g v * v⁻¹}) : Z = ⊥ := by
  let _ := modTwoW hW2
  have hfix : ∀ g a, addMap β a = 0 → addAct ρ g a = a := fun g a ha =>
    congrArg Additive.ofMul (hZfix g _ ((hβk _).1 (Multiplicative.toAdd.injective ha)))
  have hπρ : ∀ g a, addMap β (addAct ρ g a) = μ g *ᵥ addMap β a := fun g a =>
    hβe g (Additive.toMul a)
  obtain ⟨s, hs⟩ := exists_lifts (ι := ι) hβs
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  by_contra hz1
  have hz0 : Additive.ofMul z ≠ 0 := fun h => hz1 (Additive.ofMul.injective h)
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero (ZMod 2) hz0
  have hB : transCocycle θ (addAct ρ) s f.toAddMonoidHom ∈ B1A ν := by
    rw [← hZB]
    exact transCocycle_mem_Z1A hν hfix hπρ hs _
  obtain ⟨a', ha'inv, ha'eq⟩ := exists_invariant_of_mem_B1A hν hfix hπρ hs _ hB
  have h1 := invariant_form_eq_zero hgen ha'inv z
  rw [ha'eq _ (by rw [addMap_ofMul, (hβk z).2 hz]; rfl)] at h1
  exact hf h1

theorem card_le_two_of_card_Z1A [Finite W] [Finite G'] (hν : ∀ g x, ν (θ g) x = (μ g⁻¹)ᵀ *ᵥ x)
    (hZB : Nat.card (Z1A ν) = 2 * Nat.card (B1A ν)) (hW2 : ∀ w : W, w ^ 2 = 1)
    (hβs : Function.Surjective β) (hβk : ∀ w, β w = 1 ↔ w ∈ Z)
    (hZfix : ∀ g, ∀ z ∈ Z, ρ g z = z)
    (hβe : ∀ g w, Multiplicative.toAdd (β (ρ g w)) = μ g *ᵥ Multiplicative.toAdd (β w))
    (hgen : ∀ w : W, w ∈ Subgroup.closure {x | ∃ g v, x = ρ g v * v⁻¹}) :
    Nat.card Z ≤ 2 := by
  let _ := modTwoW hW2
  have hfix : ∀ g a, addMap β a = 0 → addAct ρ g a = a := fun g a ha =>
    congrArg Additive.ofMul (hZfix g _ ((hβk _).1 (Multiplicative.toAdd.injective ha)))
  have hπρ : ∀ g a, addMap β (addAct ρ g a) = μ g *ᵥ addMap β a := fun g a =>
    hβe g (Additive.toMul a)
  obtain ⟨s, hs⟩ := exists_lifts (ι := ι) hβs
  have hout : ∀ a : Additive W →+ ZMod 2, (∃ z ∈ Z, a (Additive.ofMul z) ≠ 0) →
      transCocycle θ (addAct ρ) s a ∉ B1A ν := by
    rintro a ⟨z, hz, haz⟩ hB
    obtain ⟨a', ha'inv, ha'eq⟩ := exists_invariant_of_mem_B1A hν hfix hπρ hs a hB
    have h1 := invariant_form_eq_zero hgen ha'inv z
    rw [ha'eq _ (by rw [addMap_ofMul, (hβk z).2 hz]; rfl)] at h1
    exact haz h1
  have hidx : ((B1A ν).addSubgroupOf (Z1A ν)).index = 2 := by
    have h1 := AddSubgroup.card_mul_index ((B1A ν).addSubgroupOf (Z1A ν))
    have hc : Nat.card ↥((B1A ν).addSubgroupOf (Z1A ν)) =
        Nat.card (B1A ν) :=
      Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe (B1A_le_Z1A _)).toEquiv
    rw [hc, hZB] at h1
    have hpos : 0 < Nat.card (B1A ν) := Nat.card_pos
    nlinarith
  obtain ⟨c, hc⟩ := AddSubgroup.index_eq_two_iff.1 hidx
  have hdiff : ∀ x y : ↥(Z1A ν), (x : _ → _) ∉ B1A ν →
      (y : _ → _) ∉ B1A ν → ((x + y : ↥(Z1A ν)) : _ → _) ∈ B1A ν := by
    intro x y hx hy
    have hx' : x + c ∈ (B1A ν).addSubgroupOf (Z1A ν) := by
      rcases hc x with ⟨h, -⟩ | ⟨h, -⟩
      · exact h
      · exact absurd (AddSubgroup.mem_addSubgroupOf.1 h) hx
    have hy' : y + c ∈ (B1A ν).addSubgroupOf (Z1A ν) := by
      rcases hc y with ⟨h, -⟩ | ⟨h, -⟩
      · exact h
      · exact absurd (AddSubgroup.mem_addSubgroupOf.1 h) hy
    have h2 := AddSubgroup.mem_addSubgroupOf.1 (sub_mem hx' hy')
    have h3 : x + c - (y + c) = x + y := by
      rw [add_sub_add_right_eq_sub, sub_eq_add_neg]
      congr 1
      exact Subtype.ext (funext fun g => zmod2_neg (ι := ι) _)
    rwa [h3] at h2
  by_contra hZ2
  push Not at hZ2
  have hne : Z ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hZ2
    omega
  obtain ⟨⟨z₁, hz₁⟩, hz₁1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  have hz₁1' : z₁ ≠ 1 := fun h => hz₁1 (Subtype.ext h)
  obtain ⟨z₂, hz₂, hz₂1, hz₂z₁⟩ : ∃ z₂ ∈ Z, z₂ ≠ 1 ∧ z₂ ≠ z₁ := by
    by_contra hc
    push Not at hc
    have hsub : (Z : Set W) ⊆ {1, z₁} := fun z hz => by
      by_cases h1 : z = 1
      · exact Or.inl h1
      · exact Or.inr (hc z hz h1)
    have hle : Nat.card ↥Z ≤ 2 := by
      rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
      calc (Z : Set W).ncard ≤ ({1, z₁} : Set W).ncard := Set.ncard_le_ncard hsub
        _ ≤ ({z₁} : Set W).ncard + 1 := Set.ncard_insert_le _ _
        _ = 2 := by rw [Set.ncard_singleton]
    omega
  obtain ⟨φ, ψ, hφ, hψ, hφψ⟩ : ∃ φ ψ : Additive W →+ ZMod 2,
      (∃ z ∈ Z, φ (Additive.ofMul z) ≠ 0) ∧ (∃ z ∈ Z, ψ (Additive.ofMul z) ≠ 0) ∧
        ∃ z ∈ Z, (φ + ψ) (Additive.ofMul z) ≠ 0 := by
    have hz₁0 : Additive.ofMul z₁ ≠ 0 := fun h => hz₁1' (Additive.ofMul.injective h)
    obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero (ZMod 2) hz₁0
    by_cases hf2 : f (Additive.ofMul z₂) = 0
    · have hz₂0 : Additive.ofMul z₂ ≠ 0 := fun h => hz₂1 (Additive.ofMul.injective h)
      obtain ⟨g, hg⟩ := Module.Projective.exists_dual_ne_zero (ZMod 2) hz₂0
      refine ⟨f.toAddMonoidHom, g.toAddMonoidHom, ⟨z₁, hz₁, hf⟩, ⟨z₂, hz₂, hg⟩, z₂, hz₂, ?_⟩
      show f (Additive.ofMul z₂) + g (Additive.ofMul z₂) ≠ 0
      rw [hf2, zero_add]
      exact hg
    · have h12 : z₁ * z₂ ≠ 1 := fun h => hz₂z₁ (by
        have h' : z₂ = z₁⁻¹ := eq_inv_of_mul_eq_one_right h
        rw [h', inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hW2 z₁)])
      have h120 : Additive.ofMul (z₁ * z₂) ≠ 0 := fun h => h12 (Additive.ofMul.injective h)
      obtain ⟨g, hg⟩ := Module.Projective.exists_dual_ne_zero (ZMod 2) h120
      have hfz : f (Additive.ofMul (z₁ * z₂)) = 0 := by
        rw [ofMul_mul, map_add, zmod2_eq_one_of_ne_zero _ hf, zmod2_eq_one_of_ne_zero _ hf2,
          zmod2_one_add_one]
      refine ⟨f.toAddMonoidHom, g.toAddMonoidHom, ⟨z₁, hz₁, hf⟩,
        ⟨z₁ * z₂, mul_mem hz₁ hz₂, hg⟩, z₁ * z₂, mul_mem hz₁ hz₂, ?_⟩
      show f (Additive.ofMul (z₁ * z₂)) + g (Additive.ofMul (z₁ * z₂)) ≠ 0
      rw [hfz, zero_add]
      exact hg
  let x : ↥(Z1A ν) := ⟨_, transCocycle_mem_Z1A hν hfix hπρ hs φ⟩
  let y : ↥(Z1A ν) := ⟨_, transCocycle_mem_Z1A hν hfix hπρ hs ψ⟩
  have hxy := hdiff x y (hout φ hφ) (hout ψ hψ)
  have hsum : ((x + y : ↥(Z1A ν)) : _ → _) = transCocycle θ (addAct ρ) s (φ + ψ) := by
    rw [transCocycle_add]
    rfl
  rw [hsum] at hxy
  exact hout (φ + ψ) hφψ hxy

end Covering

end CFSG.Quasithin.H13.VolI
