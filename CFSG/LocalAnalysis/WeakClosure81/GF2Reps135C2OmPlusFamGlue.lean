module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Defs
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQNatPlus
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135Ctx
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinL28

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.LieType.Universal.Spin

theorem w135c2_exists_mulAut_of_mem {G : Type*} [Group G] {W : Type} [CommGroup W] [Finite W]
    {Y L : Subgroup (MulAut W)} (hctx : Is135Context Y L) {t : MulAut W} (htY : t ∈ Y)
    (e : G ≃* ↥L) :
    ∃ α : MulAut G, ∀ s : G, ((e (α s) : ↥L) : MulAut W) = t * (e s : MulAut W) * t⁻¹ := by
  classical
  have hLY : L ≤ Y := hctx.2.2.1
  have hnorm : t ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLY).mp (w135_normal_of_ctx hctx) htY
  refine ⟨MulAut.congr e.symm (L.normalizerMonoidHom ⟨t, hnorm⟩), fun s => ?_⟩
  have heq : e (MulAut.congr e.symm (L.normalizerMonoidHom ⟨t, hnorm⟩) s) =
      L.normalizerMonoidHom ⟨t, hnorm⟩ (e s) := by
    simp [MulAut.congr_apply]
  rw [heq, Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨t, hnorm⟩ (e s)]

theorem w135c2_mulAut_mul_self_of_conj {G : Type*} [Group G] {W : Type} [CommGroup W]
    {L : Subgroup (MulAut W)} (e : G ≃* ↥L) {t : MulAut W} (ht : t * t = 1) {α : MulAut G}
    (hα : ∀ s : G, ((e (α s) : ↥L) : MulAut W) = t * (e s : MulAut W) * t⁻¹) : α * α = 1 := by
  ext s
  apply e.injective
  apply Subtype.ext
  simp only [MulAut.mul_apply, MulAut.one_apply]
  rw [hα (α s), hα s]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  rw [htinv]
  calc t * (t * (e s : MulAut W) * t) * t
      = (t * t) * ((e s : MulAut W) * (t * t)) := by group
    _ = (e s : MulAut W) := by rw [ht]; group

theorem w135c2_mul_apply_eq_one_of_mul_self {G : Type*} [Group G]
    (hZ : Subgroup.center G = ⊥) {α β : MulAut G} (hα : α * α = 1) (hβ : ∀ g, β (β g) = g)
    {h : G} (hαβ : ∀ g, α g = h * β g * h⁻¹) : h * β h = 1 := by
  have hα1 : ∀ g, α (α g) = g := by
    intro g
    have h := congrArg (fun f : MulAut G => f g) hα
    simpa [MulAut.mul_apply] using h
  have hcomm : ∀ g, g * (h * β h) = (h * β h) * g := by
    intro g
    have h2 : α (α g) = (h * β h) * g * (h * β h)⁻¹ := by
      rw [hαβ (α g), hαβ g]
      simp only [map_mul, map_inv, hβ]
      group
    rw [hα1 g] at h2
    calc g * (h * β h) = ((h * β h) * g * (h * β h)⁻¹) * (h * β h) := by
          conv_lhs => rw [h2]
      _ = (h * β h) * g := by group
  have hz : h * β h ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    exact hcomm
  rw [hZ] at hz
  exact Subgroup.mem_bot.mp hz

theorem w135c2_exists_linearEquiv_of_conj {G : Type*} [Group G] {W : Type} [CommGroup W]
    {L : Subgroup (MulAut W)} {V : Type} [AddCommGroup V] [Module (ZMod 2) V] (e : G ≃* ↥L)
    {ρ : Representation (ZMod 2) G V} {θ : W ≃* Multiplicative V}
    (hθ : ∀ (s : G) (w : W),
      θ ((e s : MulAut W) w) = Multiplicative.ofAdd (ρ s (Multiplicative.toAdd (θ w))))
    {t : MulAut W} {α : MulAut G}
    (hα : ∀ s : G, ((e (α s) : ↥L) : MulAut W) = t * (e s : MulAut W) * t⁻¹) :
    ∃ T : V ≃ₗ[ZMod 2] V,
      (∀ w : W, θ (t w) = Multiplicative.ofAdd (T (Multiplicative.toAdd (θ w)))) ∧
        ∀ (s : G) (v : V), T (ρ s v) = ρ (α s) (T v) := by
  let φ : Additive W ≃+ V := MulEquiv.toAdditiveLeft θ
  let tA : Additive W ≃+ Additive W := MulEquiv.toAdditive t
  let TA : V ≃+ V := φ.symm.trans (tA.trans φ)
  let T : V ≃ₗ[ZMod 2] V := TA.toLinearEquiv (fun a x => ZMod.map_smul TA a x)
  have hφ : ∀ u : W, φ (Additive.ofMul u) = Multiplicative.toAdd (θ u) := fun u => rfl
  have hφ_symm : ∀ u : W, φ.symm (Multiplicative.toAdd (θ u)) = Additive.ofMul u := by
    intro u
    rw [← hφ u, AddEquiv.symm_apply_apply]
  have hT' : ∀ w : W, T (Multiplicative.toAdd (θ w)) = Multiplicative.toAdd (θ (t w)) := by
    intro w
    change φ (tA (φ.symm (Multiplicative.toAdd (θ w)))) = Multiplicative.toAdd (θ (t w))
    rw [hφ_symm w]
    rw [show tA (Additive.ofMul w) = Additive.ofMul (t w) from rfl]
    exact hφ (t w)
  have hρ_eq : ∀ (s : G) (w : W),
      ρ s (Multiplicative.toAdd (θ w)) = Multiplicative.toAdd (θ ((e s : MulAut W) w)) :=
    fun s w => (congrArg Multiplicative.toAdd (hθ s w)).symm
  refine ⟨T, ?_, ?_⟩
  · intro w
    simpa using (congrArg Multiplicative.ofAdd (hT' w)).symm
  · intro s v
    obtain ⟨u, rfl⟩ : ∃ u : W, v = Multiplicative.toAdd (θ u) :=
      ⟨θ.symm (Multiplicative.ofAdd v), by simp⟩
    rw [hρ_eq s u, hT' (((e s : ↥L) : MulAut W) u), hT' u, hρ_eq (α s) (t u)]
    have htu : t⁻¹ (t u) = u := by
      rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
    have hgoal : t (((e s : ↥L) : MulAut W) u) = ((e (α s) : ↥L) : MulAut W) (t u) := by
      rw [hα s, MulAut.mul_apply, MulAut.mul_apply, htu]
    exact congrArg (fun x : W => Multiplicative.toAdd (θ x)) hgoal

theorem w135c2_four_le_mQuot_of_finrank {W : Type} [CommGroup W] [Finite W] {V : Type}
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (θ : W ≃* Multiplicative V) {t : MulAut W}
    (T : V →ₗ[ZMod 2] V)
    (hT : ∀ w : W, θ (t w) = Multiplicative.ofAdd (T (Multiplicative.toAdd (θ w))))
    (h4 : 4 ≤ Module.finrank (ZMod 2) (LinearMap.range (T - 1))) :
    4 ≤ E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) := by
  have heq := finL28_two_pow_mQuot_eq_card_range θ t T hT
  have hcardR : Nat.card (LinearMap.range (T - 1)) =
      2 ^ Module.finrank (ZMod 2) (LinearMap.range (T - 1)) := by
    refine let : Module.Finite (ZMod 2) (LinearMap.range (T - 1)) :=
      Module.Finite.of_finite; ?_
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  rw [hcardR] at heq
  have hm := Nat.pow_right_injective (le_refl 2) heq
  rw [hm]
  exact h4

theorem w135c2_omPlus_chev2Natural_of_equiv {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 2) {n : ℕ} (hn : 3 ≤ n) {W : Type} [CommGroup W]
    {L : Subgroup (MulAut W)} {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (e : spinGroup (quadPlus n F) ≃* ↥L) {ρ : Representation (ZMod 2) (spinGroup (quadPlus n F)) V}
    {θ : W ≃* Multiplicative V}
    (hθ : ∀ (s : spinGroup (quadPlus n F)) (w : W),
      θ ((e s : MulAut W) w) = Multiplicative.ofAdd (ρ s (Multiplicative.toAdd (θ w))))
    (σ : MulAut (spinGroup (quadPlus n F))) (β : V ≃+ (Fin n ⊕ Fin n → F))
    (hβ : ∀ (g : spinGroup (quadPlus n F)) (v : V),
      β (ρ g v) = spinAction (quadPlus n F) (σ g) (β v)) :
    Chev2Natural W L := by
  classical
  let : Finite V := Finite.of_equiv (Fin n ⊕ Fin n → F) β.toEquiv.symm
  let : Finite (Multiplicative V) := Finite.of_equiv V Multiplicative.ofAdd
  let : Finite W := Finite.of_equiv (Multiplicative V) θ.toEquiv.symm
  let e' : spinGroup (quadPlus n F) ≃* ↥L := σ.symm.trans e
  let ρ' : Representation (ZMod 2) (spinGroup (quadPlus n F)) V := ρ.comp σ.symm.toMonoidHom
  have hθ' : ∀ (s : spinGroup (quadPlus n F)) (w : W),
      θ ((e' s : MulAut W) w) = Multiplicative.ofAdd (ρ' s (Multiplicative.toAdd (θ w))) := by
    intro s w
    simpa [e', ρ', MulEquiv.trans_apply] using hθ (σ.symm s) w
  open scoped Matrix in
  have hT : ∀ (s : spinGroup (quadPlus n F)) (v : V),
      β (ρ' s v) = spinMatrix (quadPlus n F) s *ᵥ β v := by
    intro s v
    have h := hβ (σ.symm s) v
    rw [MulEquiv.apply_symm_apply σ s] at h
    change β (ρ (σ.symm s) v) = spinMatrix (quadPlus n F) s *ᵥ β v
    rw [h, spinMatrix_mulVec]
  refine Or.inl ⟨2 * n, 1, Or.inr (Or.inr (Or.inl ?_))⟩
  exact w135c2_omPlus_natural_of_equiv (f := 1) hn (by simpa using hF) e' (ρ := ρ') hθ' β hT

end CFSG.LocalAnalysis.WeakClosure81
