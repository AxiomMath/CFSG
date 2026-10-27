module

public import CFSG.Quasithin.Background.FFC4Coh
public import CFSG.Quasithin.Background.FFC5Ext

public section

namespace CFSG.Quasithin

namespace FFC

open Matrix CFSG.Quasithin.JonesParshall CFSG.Assembly.LowTwoRank

section Cohom3

theorem sl3F2_hom_eq_zero {M : Type*} [AddCommGroup M] {φ : SL3F2 → M}
    (h : ∀ g k, φ (g * k) = φ g + φ k) : ∀ g, φ g = 0 := by
  have hp : Group.IsPerfect SL3F2 :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (K := ZMod 2) (n := 3) (le_refl 3)
  let ψ : SL3F2 →* Multiplicative M :=
    { toFun := fun g => Multiplicative.ofAdd (φ g)
      map_one' := by
        have := h 1 1
        rw [mul_one] at this
        apply Multiplicative.toAdd.injective
        simpa using this
      map_mul' := fun g k => h g k }
  intro g
  have : g ∈ commutator SL3F2 := by rw [hp.commutator_eq_top]; trivial
  have h2 : g ∈ ψ.ker := Abelianization.commutator_subset_ker ψ this
  exact Multiplicative.toAdd.injective (MonoidHom.mem_ker.1 h2)

theorem cocycle3_invol : ∀ a : SL3F2, a * a = 1 → a ≠ 1 →
    ∀ v : Fin 3 → ZMod 2, cocycle3 a ≠ muF2 3 a v - v := by
  decide +kernel

theorem Z1A_three_cases
    {f : SL3F2 → Fin 3 → ZMod 2} (hf : f ∈ Z1A (muF2 3)) :
    f ∈ B1A (muF2 3) ∨ f - cocycle3 ∈ B1A (muF2 3) := by
  have hrel := rels_constraint (gens := gens3) (rels := rels3)
    (by rw [gens3_coe]; exact rels3_spec) hf
  rw [gens3_coe] at hrel
  rcases sol3 _ _ hrel with ⟨v, hv₀, hv₁⟩ | ⟨v, hv₀, hv₁⟩
  · left
    exact ⟨v, (eq_of_agree closure_gens3 hf (B1A_le_Z1A _ ⟨v, rfl⟩) hv₀ hv₁).symm⟩
  · right
    have hc : cocycle3 ∈ Z1A (muF2 3) := cocycle3_mem
    refine ⟨v, ?_⟩
    have := eq_of_agree closure_gens3 (sub_mem hf hc) (B1A_le_Z1A _ ⟨v, rfl⟩) (by
      rw [Pi.sub_apply, hv₀, add_sub_cancel_right]
      rfl) (by
      rw [Pi.sub_apply, hv₁, add_sub_cancel_right]
      rfl)
    exact this.symm

end Cohom3

section Quot

variable {M : Type*} [AddCommGroup M] {ι : Type*}

theorem mem_B1A_of_quot
    {μ : SL3F2 →* AddMonoid.End M} {q : ι → M →+ (Fin 3 → ZMod 2)}
    (hq : ∀ i (γ : SL3F2) m, q i (μ γ m) = muF2 3 γ (q i m))
    (hsurj : ∀ n : ι → (Fin 3 → ZMod 2), ∃ m, ∀ i, q i m = n i)
    (hker : ∀ m, (∀ i, q i m = 0) → ∀ γ, μ γ m = m)
    {a : SL3F2} (ha2 : a * a = 1) (ha1 : a ≠ 1) {f : SL3F2 → M} (hf : f ∈ Z1A μ) {m₀ : M}
    (h0 : f a = μ a m₀ - m₀) : f ∈ B1A μ := by
  have hfi : ∀ i, (fun γ => q i (f γ)) ∈ Z1A (muF2 3) := by
    intro i γ δ
    show q i (f (γ * δ)) = q i (f γ) + muF2 3 γ (q i (f δ))
    rw [hf γ δ, map_add, hq]
  have hB : ∀ i, ∃ n, ∀ γ, q i (f γ) = muF2 3 γ n - n := by
    intro i
    rcases Z1A_three_cases (hfi i) with ⟨n, hn⟩ | ⟨n, hn⟩
    · exact ⟨n, fun γ => (congrFun hn γ).symm⟩
    · exfalso
      have h1 : muF2 3 a n - n = q i (f a) - cocycle3 a := congrFun hn a
      have h2 : q i (f a) = muF2 3 a (q i m₀) - q i m₀ := by
        rw [h0, map_sub, hq]
        rfl
      apply cocycle3_invol a ha2 ha1 (q i m₀ - n)
      rw [h2] at h1
      have h3 : cocycle3 a = muF2 3 a (q i m₀) - q i m₀ - (muF2 3 a n - n) := by
        rw [h1]; abel
      rw [h3, map_sub]
      abel
  choose n hn using hB
  obtain ⟨m, hm⟩ := hsurj n
  have hf' : f - coboundaryA μ m ∈ Z1A μ := sub_mem hf (B1A_le_Z1A μ ⟨m, rfl⟩)
  have hfix : ∀ i γ, q i ((f - coboundaryA μ m) γ) = 0 := by
    intro i γ
    have h1 : q i ((f - coboundaryA μ m) γ) = q i (f γ) - (muF2 3 γ (q i m) - q i m) := by
      show q i (f γ - (μ γ m - m)) = _
      rw [map_sub, map_sub, hq]
      rfl
    rw [h1, hn i γ, hm i]
    exact sub_self _
  have hzero : ∀ γ, (f - coboundaryA μ m) γ = 0 := by
    apply sl3F2_hom_eq_zero
    intro γ δ
    rw [hf' γ δ, hker _ (hfix · δ) γ]
  refine ⟨m, ?_⟩
  funext γ
  exact (sub_eq_zero.1 (hzero γ)).symm

end Quot

section Pullback

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem pullback_mem_Z1A {L : Subgroup (MulAut V)} {W : Subgroup V} (hLW : ∀ g ∈ L, ∀ w ∈ W, g w ∈ W)
    {Γ : Type*} [Group Γ] (ρ : Γ →* ↥L) {M : Type*} [AddCommGroup M] (μ : Γ →* AddMonoid.End M)
    (θ : Additive ↥W ≃+ M) (hθ : ∀ γ w, θ (muW hLW (ρ γ) w) = μ γ (θ w))
    {f : ↥L → Additive ↥W} (hf : f ∈ Z1A (muW hLW)) : (fun γ => θ (f (ρ γ))) ∈ Z1A μ := by
  intro γ δ
  show θ (f (ρ (γ * δ))) = θ (f (ρ γ)) + μ γ (θ (f (ρ δ)))
  rw [map_mul, hf, map_add, hθ]

omit [Finite V] in
theorem mem_B1A_of_pullback {L : Subgroup (MulAut V)} {W : Subgroup V} (hLW : ∀ g ∈ L, ∀ w ∈ W, g w ∈ W)
    {Γ : Type*} [Group Γ] (ρ : Γ →* ↥L) (hρ : Function.Surjective ρ) {M : Type*} [AddCommGroup M]
    (μ : Γ →* AddMonoid.End M) (θ : Additive ↥W ≃+ M)
    (hθ : ∀ γ w, θ (muW hLW (ρ γ) w) = μ γ (θ w))
    {f : ↥L → Additive ↥W} (hB : (fun γ => θ (f (ρ γ))) ∈ B1A μ) : f ∈ B1A (muW hLW) := by
  obtain ⟨n, hn⟩ := hB
  refine ⟨θ.symm n, funext fun l => ?_⟩
  obtain ⟨γ, rfl⟩ := hρ l
  have h1 : μ γ n - n = θ (f (ρ γ)) := congrFun hn γ
  rw [coboundaryA_apply]
  apply θ.injective
  rw [map_sub, hθ, AddEquiv.apply_symm_apply, h1]

end Pullback

section NatQuot

variable {V : Type} [CommGroup V]

structure NatQuot3 (H : Subgroup (MulAut V)) (U Z : Subgroup V) where
  ρ : SL3F2 →* ↥H
  surj : Function.Surjective ρ
  inj : Function.Injective ρ
  θ : ↥U →* Multiplicative (Fin 3 → ZMod 2)
  θ_surj : Function.Surjective θ
  θ_ker : ∀ u : ↥U, θ u = 1 ↔ (u : V) ∈ Z
  inv : ∀ (g : SL3F2) (u : V), u ∈ U → ((ρ g : ↥H) : MulAut V) u ∈ U
  equiv : ∀ (g : SL3F2) (u : ↥U), θ ⟨((ρ g : ↥H) : MulAut V) (u : V), inv g u u.2⟩ =
    Multiplicative.ofAdd (g • Multiplicative.toAdd (θ u))

theorem exists_natQuot3 {H : Subgroup (MulAut V)} {U Z : Subgroup V} (h : BinaryNaturalSL H U Z 3 1) :
    Nonempty (NatQuot3 H U Z) := by
  obtain ⟨π, hπ⟩ := BinaryNaturalSL.exists_zmod h
  obtain ⟨f, hfs, hfk, hfe⟩ := exists_natMap hπ
  have hinj : Function.Injective π := injective_of_faithful_sec (FFModel.nat_faithful _) hπ
  exact ⟨{ ρ := π.comp (specialLinearGroupEquivStatedSL 3 (ZMod 2)).toMonoidHom
           surj := hπ.1.comp (specialLinearGroupEquivStatedSL 3 (ZMod 2)).surjective
           inj := hinj.comp (specialLinearGroupEquivStatedSL 3 (ZMod 2)).injective
           θ := f
           θ_surj := hfs
           θ_ker := hfk
           inv := fun g u hu => hπ.2.2.2.1 _ u hu
           equiv := fun g u => hfe _ u _ }⟩

theorem NatQuot3.hR
    {L A : Subgroup (MulAut V)} {W Z : Subgroup V} (D : NatQuot3 L W Z)
    (hZ : ∀ z ∈ Z, ∀ g ∈ L, g z = z) (hAL : A ≤ L) (hA : A ≠ ⊥) (hA2 : ∀ a ∈ A, a ^ 2 = 1)
    (hLW : ∀ g ∈ L, ∀ w ∈ W, g w ∈ W) :
    ∀ f ∈ Z1A (muW hLW), (∃ m : Additive ↥W, ∀ a : ↥L, (a : MulAut V) ∈ A →
      f a = muW hLW a m - m) → f ∈ B1A (muW hLW) := by
  intro f hf ⟨m₀, hm₀⟩
  obtain ⟨a₀, ha₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hA
  obtain ⟨a, haeq⟩ : ∃ a : ↥L, (a : MulAut V) = (a₀ : MulAut V) := ⟨⟨a₀, hAL a₀.2⟩, rfl⟩
  have haA : (a : MulAut V) ∈ A := by rw [haeq]; exact a₀.2
  have ha1 : a ≠ 1 := by
    intro h
    apply ha₀1
    apply Subtype.ext
    rw [← haeq, h]
    rfl
  have ha2 : a * a = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, haeq, ← sq]
    exact hA2 _ a₀.2
  obtain ⟨γ, hγ⟩ := D.surj a
  have hγ1 : γ ≠ 1 := fun h => ha1 (by rw [← hγ, h, map_one])
  have hγ2 : γ * γ = 1 := D.inj (by rw [map_mul, hγ, ha2, map_one])
  let μ : SL3F2 →* AddMonoid.End (Additive ↥W) := (muW hLW).comp D.ρ
  let qh : Additive ↥W →+ (Fin 3 → ZMod 2) :=
    { toFun := fun w => Multiplicative.toAdd (D.θ (Additive.toMul w))
      map_zero' := by simp
      map_add' := fun x y => by simp }
  have hq : ∀ (_ : Unit) (g : SL3F2) (m : Additive ↥W), qh (μ g m) = muF2 3 g (qh m) := by
    intro _ g m
    have h1 := D.equiv g (Additive.toMul m)
    show Multiplicative.toAdd (D.θ ⟨(D.ρ g : MulAut V) (Additive.toMul m : ↥W), _⟩) = _
    rw [h1, toAdd_ofAdd]
    rfl
  have hsurj : ∀ n : Unit → (Fin 3 → ZMod 2), ∃ m : Additive ↥W, ∀ _ : Unit, qh m = n () := by
    intro n
    obtain ⟨u, hu⟩ := D.θ_surj (Multiplicative.ofAdd (n ()))
    exact ⟨Additive.ofMul u, fun _ => by
      show Multiplicative.toAdd (D.θ u) = n ()
      rw [hu]; rfl⟩
  have hker : ∀ m : Additive ↥W, (∀ _ : Unit, qh m = 0) → ∀ g : SL3F2, μ g m = m := by
    intro m hm g
    have h1 : D.θ (Additive.toMul m) = 1 := by
      apply Multiplicative.toAdd.injective
      exact hm ()
    have h2 : ((Additive.toMul m : ↥W) : V) ∈ Z := (D.θ_ker _).1 h1
    apply Additive.toMul.injective
    apply Subtype.ext
    exact hZ _ h2 _ (D.ρ g).2
  have hf' := pullback_mem_Z1A hLW D.ρ μ (AddEquiv.refl _) (fun _ _ => rfl) hf
  have hres : (fun γ => (AddEquiv.refl _ : Additive ↥W ≃+ Additive ↥W) (f (D.ρ γ))) γ = μ γ m₀ - m₀ := by
    show f (D.ρ γ) = muW hLW (D.ρ γ) m₀ - m₀
    rw [hγ]
    exact hm₀ a haA
  have hB := mem_B1A_of_quot (μ := μ) (q := fun _ : Unit => qh) hq hsurj hker hγ2 hγ1 hf' hres
  exact mem_B1A_of_pullback hLW D.ρ D.surj μ (AddEquiv.refl _) (fun _ _ => rfl) hB

theorem natural_h1_vanish {K : Type} [Field K] [Finite K] {a : ℕ} (hK : Nat.card K = 2 ^ a)
    (ha : 1 < a) {L : Subgroup (MulAut V)} {W : Subgroup V} (hLW : ∀ g ∈ L, ∀ w ∈ W, g w ∈ W)
    (h : (FFModel.nat (StatedSL 3 K)).Realizes L W ⊥) :
    ∀ f ∈ Z1A (muW hLW), f ∈ B1A (muW hLW) := by
  obtain ⟨π, hπ⟩ := h
  obtain ⟨θ, hθs, hθk, hθe⟩ := exists_natMap hπ
  have hθi : Function.Injective θ := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have := (hθk u).1 hu
    exact Subtype.ext (Subgroup.mem_bot.1 this)
  let e : ↥W ≃* Multiplicative (Fin 3 → K) := MulEquiv.ofBijective θ ⟨hθi, hθs⟩
  let θ' : Additive ↥W ≃+ (Fin 3 → K) :=
    { toFun := fun w => Multiplicative.toAdd (θ (Additive.toMul w))
      invFun := fun v => Additive.ofMul (e.symm (Multiplicative.ofAdd v))
      left_inv := fun w => by
        show Additive.ofMul (e.symm (Multiplicative.ofAdd (Multiplicative.toAdd (θ (Additive.toMul w))))) = w
        exact congrArg Additive.ofMul (e.symm_apply_apply (Additive.toMul w))
      right_inv := fun v => by
        show Multiplicative.toAdd (θ (e.symm (Multiplicative.ofAdd v))) = v
        exact congrArg Multiplicative.toAdd (e.apply_symm_apply (Multiplicative.ofAdd v))
      map_add' := fun x y => by
        show Multiplicative.toAdd (θ (Additive.toMul x * Additive.toMul y)) = _
        rw [map_mul]
        rfl }
  have : Fintype K := Fintype.ofFinite K
  have hCharP : CharP K 2 := charP_two_of_card_pow hK
  have hF : Fintype.card K = 2 ^ a := by rw [← Nat.card_eq_fintype_card]; exact hK
  let ρ : SL3 K →* ↥L := π.comp (specialLinearGroupEquivStatedSL 3 K).toMonoidHom
  have hρ : Function.Surjective ρ := hπ.1.comp (specialLinearGroupEquivStatedSL 3 K).surjective
  intro f hf
  have hθ : ∀ γ w, θ' (muW hLW (ρ γ) w) = mu3 γ (θ' w) := by
    intro γ w
    have h1 := hθe (specialLinearGroupEquivStatedSL 3 K γ) (Additive.toMul w)
      (hLW _ (ρ γ).2 _ (Additive.toMul w).2)
    show Multiplicative.toAdd (θ (Additive.toMul (muW hLW (ρ γ) w))) =
      mu3 γ (Multiplicative.toAdd (θ (Additive.toMul w)))
    rw [muW_apply]
    exact congrArg Multiplicative.toAdd h1
  have hf' := pullback_mem_Z1A hLW ρ (mu3 (F := K)) θ' hθ hf
  exact mem_B1A_of_pullback hLW ρ hρ (mu3 (F := K)) θ' hθ (mem_B1A_mu3 hF ha hf')

@[expose] def cocyF {L : Subgroup (MulAut V)} {W : Subgroup V} (hc : ∀ g ∈ L, ∀ v : V, g v * v⁻¹ ∈ W)
    (v : V) : ↥L → Additive ↥W :=
  fun g => Additive.ofMul (⟨(g : MulAut V) v * v⁻¹, hc g g.2 v⟩ : ↥W)

theorem cocyF_mem_Z1A {L : Subgroup (MulAut V)} {W : Subgroup V} (hLW : ∀ g ∈ L, ∀ w ∈ W, g w ∈ W)
    (hc : ∀ g ∈ L, ∀ v : V, g v * v⁻¹ ∈ W) (v : V) : cocyF hc v ∈ Z1A (muW hLW) :=
  cocy_mem_Z1A hLW hc v

theorem cocyF_div {L : Subgroup (MulAut V)} {W : Subgroup V} (hc : ∀ g ∈ L, ∀ v : V, g v * v⁻¹ ∈ W)
    (v v' : V) : cocyF hc (v * v'⁻¹) = cocyF hc v - cocyF hc v' := by
  funext g
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [Pi.sub_apply, toMul_sub, Subgroup.coe_div, div_eq_mul_inv]
  show (g : MulAut V) (v * v'⁻¹) * (v * v'⁻¹)⁻¹ = ((g : MulAut V) v * v⁻¹) * ((g : MulAut V) v' * v'⁻¹)⁻¹
  rw [map_mul, map_inv, mul_inv, inv_inv]
  simp [mul_comm, mul_left_comm, mul_assoc]

theorem sup_fixV_natural3
    {L : Subgroup (MulAut V)} {W : Subgroup V} (hLW : ∀ g ∈ L, ∀ w ∈ W, g w ∈ W)
    (hc : ∀ g ∈ L, ∀ v : V, g v * v⁻¹ ∈ W) (D : NatQuot3 L W ⊥) (v v' : V) :
    v ∈ W ⊔ fixV L ∨ v' ∈ W ⊔ fixV L ∨ v * v'⁻¹ ∈ W ⊔ fixV L := by
  have hθi : Function.Injective D.θ := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.1 ((D.θ_ker u).1 hu))
  let e : ↥W ≃* Multiplicative (Fin 3 → ZMod 2) := MulEquiv.ofBijective D.θ ⟨hθi, D.θ_surj⟩
  let θ' : Additive ↥W ≃+ (Fin 3 → ZMod 2) :=
    { toFun := fun w => Multiplicative.toAdd (D.θ (Additive.toMul w))
      invFun := fun v => Additive.ofMul (e.symm (Multiplicative.ofAdd v))
      left_inv := fun w => by
        show Additive.ofMul (e.symm (Multiplicative.ofAdd (Multiplicative.toAdd (D.θ (Additive.toMul w))))) = w
        exact congrArg Additive.ofMul (e.symm_apply_apply (Additive.toMul w))
      right_inv := fun v => by
        show Multiplicative.toAdd (D.θ (e.symm (Multiplicative.ofAdd v))) = v
        exact congrArg Multiplicative.toAdd (e.apply_symm_apply (Multiplicative.ofAdd v))
      map_add' := fun x y => by
        show Multiplicative.toAdd (D.θ (Additive.toMul x * Additive.toMul y)) = _
        rw [map_mul]
        rfl }
  have hθ : ∀ γ w, θ' (muW hLW (D.ρ γ) w) = muF2 3 γ (θ' w) := by
    intro γ w
    have h1 := D.equiv γ (Additive.toMul w)
    show Multiplicative.toAdd (D.θ (Additive.toMul (muW hLW (D.ρ γ) w))) =
      muF2 3 γ (Multiplicative.toAdd (D.θ (Additive.toMul w)))
    rw [muW_apply]
    exact congrArg Multiplicative.toAdd h1
  let F : V → SL3F2 → Fin 3 → ZMod 2 := fun v γ => θ' (cocyF hc v (D.ρ γ))
  have hF : ∀ v, F v ∈ Z1A (muF2 3) := fun v =>
    pullback_mem_Z1A hLW D.ρ (muF2 3) θ' hθ (cocyF_mem_Z1A hLW hc v)
  have hFB : ∀ v, F v ∈ B1A (muF2 3) → v ∈ W ⊔ fixV L := fun v hv =>
    mem_sup_fixV_of_B1A hLW hc v (mem_B1A_of_pullback hLW D.ρ D.surj (muF2 3) θ' hθ hv)
  have hFdiv : F (v * v'⁻¹) = F v - F v' := by
    funext γ
    show θ' (cocyF hc (v * v'⁻¹) (D.ρ γ)) = θ' (cocyF hc v (D.ρ γ)) - θ' (cocyF hc v' (D.ρ γ))
    rw [cocyF_div, Pi.sub_apply, map_sub]
    rfl
  rcases Z1A_three_cases (hF v) with h1 | h1
  · exact Or.inl (hFB v h1)
  rcases Z1A_three_cases (hF v') with h2 | h2
  · exact Or.inr (Or.inl (hFB v' h2))
  refine Or.inr (Or.inr (hFB _ ?_))
  rw [hFdiv]
  have := sub_mem h1 h2
  rwa [sub_sub_sub_cancel_right] at this

end NatQuot

end FFC

end CFSG.Quasithin
