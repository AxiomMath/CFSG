module

public import CFSG.Open.StatedDefs
import CFSG.LocalAnalysis.RankThreeUC.AGL81S16Norm
import CFSG.LocalAnalysis.RankThreeUC.AGL81S16QAux
import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanResS26FieldAut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open Matrix CFSG.Open CFSG.LocalAnalysis.RankThreeUC

variable {F : Type} [Field F] [Finite F] {n : ℕ}

private def linSubgroup_T3J1 {H : Type} [Group H] (hH2 : ∀ h : H, h * h = 1)
    (ρ : H →* Equiv.Perm (Fin 4 → F)) : Subgroup H where
  carrier := {h | ∀ (c : F) (x : Fin 4 → F), ρ h (c • x) = c • ρ h x}
  mul_mem' := fun {a b} ha hb c x => by
    show ρ (a * b) (c • x) = c • ρ (a * b) x
    rw [map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hb, ha]
  one_mem' := fun c x => by
    show ρ 1 (c • x) = c • ρ 1 x
    rw [map_one, Equiv.Perm.one_apply, Equiv.Perm.one_apply]
  inv_mem' := fun {a} ha c x => by
    have hinv : ∀ y : Fin 4 → F, ρ a (ρ a⁻¹ y) = y := fun y => by
      rw [← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one, Equiv.Perm.one_apply]
    show ρ a⁻¹ (c • x) = c • ρ a⁻¹ x
    apply (ρ a).injective
    rw [hinv, ha c (ρ a⁻¹ x), hinv]

private theorem semilinear_sq_T3J1 (hF : Nat.card F = (2 ^ n) ^ 2)
    {H : Type} [Group H] (hH2 : ∀ h : H, h * h = 1)
    (ρ : H →* Equiv.Perm (Fin 4 → F))
    (hadd : ∀ (h : H) (x y : Fin 4 → F), ρ h (x + y) = ρ h x + ρ h y)
    (hN : ∀ h : H, ∀ g ∈ StatedSU 4 (2 ^ n) F, ∃ g' ∈ StatedSU 4 (2 ^ n) F, ∀ x : Fin 4 → F,
      ρ h⁻¹ (((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ x) =
        ((g' : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ ρ h⁻¹ x) :
    ∃ θ : H → F →+* F,
      (∀ (h : H) (c : F) (x : Fin 4 → F), ρ h (c • x) = θ h c • ρ h x) ∧
      ∀ (h : H) (c : F), θ h (θ h c) = c := by
  have hinv : ∀ (h : H) (y : Fin 4 → F), ρ h (ρ h⁻¹ y) = y := fun h y => by
    rw [← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one, Equiv.Perm.one_apply]
  let α : H → ((Fin 4 → F) ≃+ (Fin 4 → F)) := fun h => { toEquiv := ρ h, map_add' := hadd h }
  have hα : ∀ h x, α h x = ρ h x := fun h x => rfl
  have hsymm : ∀ (h : H) (y : Fin 4 → F), (α h).symm y = ρ h⁻¹ y := fun h y => by
    rw [AddEquiv.symm_apply_eq, hα]
    exact (hinv h y).symm
  have hθ : ∀ h : H, ∃ θ : F →+* F, ∀ (c : F) (x : Fin 4 → F), ρ h (c • x) = θ c • ρ h x :=
    fun h => exists_semilinear_statedSU hF (α h) (fun g hg => by
      obtain ⟨g', hg', hg'x⟩ := hN h g hg
      exact ⟨g', hg', fun x => by rw [hsymm, hsymm]; exact hg'x x⟩)
  choose θ hθ using hθ
  have hρ2 : ∀ (h : H) (x : Fin 4 → F), ρ h (ρ h x) = x := fun h x => by
    rw [← Equiv.Perm.mul_apply, ← map_mul, hH2 h, map_one, Equiv.Perm.one_apply]
  have hsq : ∀ (h : H) (c : F), θ h (θ h c) = c := by
    intro h c
    have h1 : c • (Pi.single 0 1 : Fin 4 → F) =
        θ h (θ h c) • (Pi.single 0 1 : Fin 4 → F) := by
      calc c • (Pi.single 0 1 : Fin 4 → F)
          = ρ h (ρ h (c • (Pi.single 0 1 : Fin 4 → F))) := (hρ2 h _).symm
        _ = ρ h (θ h c • ρ h (Pi.single 0 1)) := by rw [hθ h c]
        _ = θ h (θ h c) • ρ h (ρ h (Pi.single 0 1)) := by rw [hθ h (θ h c)]
        _ = θ h (θ h c) • (Pi.single 0 1 : Fin 4 → F) := by rw [hρ2 h]
    have h2 := congrFun h1 0
    simpa using h2.symm
  exact ⟨θ, hθ, hsq⟩

private theorem index_le_two_T3J1 {H : Type} [Group H] (H₀ : Subgroup H) (e : H → (F ≃+* F))
    (hinv2 : ∀ h, e h * e h = 1) (he : ∀ h k : H, e h = e k → h⁻¹ * k ∈ H₀) :
    H₀.index ≤ 2 := by
  classical
  have hcoin : ∀ h k : H, e h ≠ 1 → e k ≠ 1 → e h = e k := by
    intro h k hh hk
    obtain ⟨q, hq, hpow⟩ := CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes.fieldAut_invol_eq_pow
      (hinv2 h) hh
    obtain ⟨q', hq', hpow'⟩ := CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes.fieldAut_invol_eq_pow
      (hinv2 k) hk
    have hqq : q = q' := Nat.mul_self_inj.1 (hq.trans hq'.symm)
    subst hqq
    ext x
    rw [hpow, hpow']
  let g : H ⧸ H₀ → Bool := fun q => decide (e q.out = 1)
  have hg : Function.Injective g := by
    intro q₁ q₂ hq
    have key : e q₁.out = e q₂.out := by
      by_cases h1 : e q₁.out = 1
      · have h2 : e q₂.out = 1 := by
          by_contra h2
          simp [g, h1, h2] at hq
        rw [h1, h2]
      · have h2 : e q₂.out ≠ 1 := by
          intro h2
          simp [g, h1, h2] at hq
        exact hcoin _ _ h1 h2
    have h3 := he _ _ key
    have h4 : ((q₁.out : H) : H ⧸ H₀) = ((q₂.out : H) : H ⧸ H₀) := QuotientGroup.eq.mpr h3
    rwa [QuotientGroup.out_eq', QuotientGroup.out_eq'] at h4
  calc H₀.index = Nat.card (H ⧸ H₀) := rfl
    _ ≤ Nat.card Bool := Nat.card_le_card_of_injective _ hg
    _ = 2 := by simp

private theorem index_linSubgroup_T3J1 {H : Type} [Group H]
    (hH2 : ∀ h : H, h * h = 1) (ρ : H →* Equiv.Perm (Fin 4 → F))
    (θ : H → F →+* F)
    (hθ : ∀ (h : H) (c : F) (x : Fin 4 → F), ρ h (c • x) = θ h c • ρ h x)
    (hsq : ∀ (h : H) (c : F), θ h (θ h c) = c) :
    (linSubgroup_T3J1 hH2 ρ).index ≤ 2 := by
  classical
  let e : H → (F ≃+* F) := fun h => RingEquiv.ofBijective (θ h)
    ⟨(θ h).injective, Finite.injective_iff_surjective.mp (θ h).injective⟩
  have hinv : ∀ (h : H) (y : Fin 4 → F), ρ h (ρ h⁻¹ y) = y := fun h y => by
    rw [← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one, Equiv.Perm.one_apply]
  have he : ∀ h k : H, e h = e k → h⁻¹ * k ∈ linSubgroup_T3J1 hH2 ρ := by
    intro h k hk c x
    have hθeq : θ h = θ k := by
      ext c
      exact congrArg (fun r : F ≃+* F => r c) hk
    show ρ (h⁻¹ * k) (c • x) = c • ρ (h⁻¹ * k) x
    rw [map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    apply (ρ h).injective
    rw [hinv h (ρ k (c • x)), hθ h c (ρ h⁻¹ (ρ k x)), hinv h (ρ k x), hθ k c x, hθeq]
  exact index_le_two_T3J1 _ e (fun h => by ext c; exact hsq h c) he

private theorem linear_T3J1 (hF : Nat.card F = (2 ^ n) ^ 2) (hn : 1 ≤ n)
    {H : Type} [Group H] [Finite H] (hH2 : ∀ h : H, h * h = 1)
    (ρ : H →* Equiv.Perm (Fin 4 → F))
    (hadd : ∀ (h : H) (x y : Fin 4 → F), ρ h (x + y) = ρ h x + ρ h y)
    (hQ : ∀ K : Subgroup H, K.index ≤ 2 → ∀ x : Fin 4 → F, (∀ k ∈ K, ρ k x = x) →
      ∀ h : H, ρ h x = x)
    (θ : H → F →+* F)
    (hθ : ∀ (h : H) (c : F) (x : Fin 4 → F), ρ h (c • x) = θ h c • ρ h x)
    (hindex : (linSubgroup_T3J1 hH2 ρ).index ≤ 2) :
    ∀ (h : H) (c : F) (x : Fin 4 → F), ρ h (c • x) = c • ρ h x := by
  let H₀ : Subgroup H := linSubgroup_T3J1 hH2 ρ
  have hH₀2 : IsPGroup 2 ↥H₀ := fun a => ⟨1, by simpa [pow_two] using Subtype.ext (hH2 (a : H))⟩
  have hWeven : Even (Nat.card (Fin 4 → F)) := by
    rw [Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hF]
    exact Nat.even_pow.mpr ⟨Nat.even_pow.mpr ⟨Nat.even_pow.mpr ⟨even_two, by omega⟩,
      by norm_num⟩, by norm_num⟩
  let α : H → ((Fin 4 → F) ≃+ (Fin 4 → F)) := fun h => { toEquiv := ρ h, map_add' := hadd h }
  obtain ⟨w, hw0, hwfix⟩ := exists_ne_zero_fixed hH₀2 hWeven (ρ.comp H₀.subtype)
    (fun a => (α (a : H)).map_zero)
  have hfixall : ∀ (h : H) (c : F), ρ h (c • w) = c • w := by
    intro h c
    refine hQ H₀ hindex (c • w) (fun k hk => ?_) h
    have hkw : ρ k w = w := hwfix ⟨k, hk⟩
    rw [hk c w, hkw]
  intro h c x
  have hw1 : ρ h w = w := by simpa using hfixall h 1
  have h1 : θ h c = c := by
    have h2 := hfixall h c
    rw [hθ h c w, hw1] at h2
    exact smul_left_injective F hw0 h2
  rw [hθ h c x, h1]

private theorem mem_statedSU_T3J1 (hF : Nat.card F = (2 ^ n) ^ 2)
    {H : Type} [Group H] (hH2 : ∀ h : H, h * h = 1)
    (ρ : H →* Equiv.Perm (Fin 4 → F))
    (hadd : ∀ (h : H) (x y : Fin 4 → F), ρ h (x + y) = ρ h x + ρ h y)
    (hN : ∀ h : H, ∀ g ∈ StatedSU 4 (2 ^ n) F, ∃ g' ∈ StatedSU 4 (2 ^ n) F, ∀ x : Fin 4 → F,
      ρ h⁻¹ (((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ x) =
        ((g' : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ ρ h⁻¹ x)
    (hlin : ∀ (h : H) (c : F) (x : Fin 4 → F), ρ h (c • x) = c • ρ h x) :
    ∀ h : H, ∃ g ∈ StatedSU 4 (2 ^ n) F, ∀ x : Fin 4 → F,
      ρ h x = ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ x := by
  intro h
  let f : (Fin 4 → F) →ₗ[F] (Fin 4 → F) :=
    { toFun := ρ h
      map_add' := hadd h
      map_smul' := fun c x => hlin h c x }
  have hAx : ∀ x, (LinearMap.toMatrix' f) *ᵥ x = ρ h x := by
    intro x
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
    rfl
  have hρ2 : ∀ x, ρ h (ρ h x) = x := fun x => by
    rw [← Equiv.Perm.mul_apply, ← map_mul, hH2 h, map_one, Equiv.Perm.one_apply]
  have hAA : LinearMap.toMatrix' f * LinearMap.toMatrix' f = 1 := by
    ext i j
    have := congrFun (show (LinearMap.toMatrix' f * LinearMap.toMatrix' f) *ᵥ
        (Pi.single j 1 : Fin 4 → F) = Pi.single j 1 by
      rw [← mulVec_mulVec, hAx, hAx, hρ2]) i
    simpa [Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply] using this
  have hsy : ρ h⁻¹ = ρ h := by rw [inv_eq_of_mul_eq_one_right (hH2 h)]
  obtain ⟨g, hgS, hg⟩ := exists_mem_statedSU_of_normalizes hF (LinearMap.toMatrix' f) hAA
    (fun g hg => by
      obtain ⟨g', hg', hg'x⟩ := hN h g hg
      refine ⟨g', hg', fun x => ?_⟩
      rw [hAx, hAx, ← hsy]
      exact hg'x x)
  exact ⟨g, hgS, fun x => by rw [hg, hAx]⟩

theorem model_Q_two (hF : Nat.card F = (2 ^ n) ^ 2) (hn : 1 ≤ n) {H : Type} [Group H] [Finite H]
    (hH2 : ∀ h : H, h * h = 1) (ρ : H →* Equiv.Perm (Fin 4 → F))
    (hadd : ∀ (h : H) (x y : Fin 4 → F), ρ h (x + y) = ρ h x + ρ h y)
    (hN : ∀ h : H, ∀ g ∈ StatedSU 4 (2 ^ n) F, ∃ g' ∈ StatedSU 4 (2 ^ n) F, ∀ x : Fin 4 → F,
      ρ h⁻¹ (((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ x) =
        ((g' : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ ρ h⁻¹ x)
    (hQ : ∀ K : Subgroup H, K.index ≤ 2 → ∀ x : Fin 4 → F, (∀ k ∈ K, ρ k x = x) →
      ∀ h : H, ρ h x = x) :
    ∀ h : H, ∃ g ∈ StatedSU 4 (2 ^ n) F, ∀ x : Fin 4 → F,
      ρ h x = ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ x := by
  obtain ⟨θ, hθ, hsq⟩ := semilinear_sq_T3J1 hF hH2 ρ hadd hN
  have hindex : (linSubgroup_T3J1 hH2 ρ).index ≤ 2 :=
    index_linSubgroup_T3J1 hH2 ρ θ hθ hsq
  exact mem_statedSU_T3J1 hF hH2 ρ hadd hN (linear_T3J1 hF hn hH2 ρ hadd hQ θ hθ hindex)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
