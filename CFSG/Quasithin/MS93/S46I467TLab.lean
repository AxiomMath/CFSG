module

public import CFSG.Quasithin.MS93.S4AFMod
public import CFSG.Quasithin.Background.SmithB42SL3Base
public import CFSG.Quasithin.Background.SmithB42SL3Label
public import CFSG.Quasithin.Background.SmithB42SL3Trace

public section

namespace CFSG.Quasithin.MS93.S4A.F

open CFSG.Quasithin CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.S46
open CFSG.QuasithinUnique.Setup.X7a
open scoped Matrix MatrixGroups

section Comm

variable {X : Type} [CommGroup X] [Finite X]

theorem card_commV_mul_card_fixV_zpowers (g : MulAut X) :
    Nat.card (commV (Subgroup.zpowers g)) * Nat.card (fixV (Subgroup.zpowers g)) =
      Nat.card X := by
  rw [commV_zpowers_eq_map, ← MonoidHom.range_eq_map, ← ker_commHom, ← Subgroup.index_ker,
    mul_comm, Subgroup.card_mul_index]

omit [Finite X] in
theorem card_eq_of_binModel {W : Type} [AddCommGroup W] (θ : X ≃* Multiplicative W)
    {P : Subgroup X} {S : Set W} (h : ∀ v, v ∈ P ↔ Multiplicative.toAdd (θ v) ∈ S) :
    Nat.card P = Nat.card S :=
  Nat.card_congr
    { toFun := fun v => ⟨Multiplicative.toAdd (θ v), (h v).1 v.2⟩
      invFun := fun x => ⟨θ.symm (Multiplicative.ofAdd x), (h _).2 (by simp)⟩
      left_inv := fun v => Subtype.ext (by simp)
      right_inv := fun x => Subtype.ext (by simp) }

end Comm

section Label

variable {F : Type} [Field F] [Finite F] {n : ℕ} {X : Type} [CommGroup X] [Finite X]

theorem natCoord_or_large (hF : Nat.card F = 2 ^ n) (hX2 : ∀ x : X, x ^ 2 = 1)
    (ρ : SL3 F →* MulAut X)
    (hirr : ∀ W : Subgroup X, (∀ g : SL3 F, ∀ w ∈ W, ρ g w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hnt : ∃ g x, ρ g x ≠ x) {t : SL3 F} (ht1 : t ≠ 1) (ht2 : t * t = 1) :
    (∃ (σ : SL3 F ≃* ↥ρ.range) (θ : X ≃* Multiplicative (Fin 3 → F)), IsNatCoord σ θ) ∨
      Nat.card F ^ 2 ≤ Nat.card (commV (Subgroup.zpowers (ρ t))) := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have : CharP F 2 := FFC.charP_two_of_card_pow hF
  have hn : 1 ≤ n := R3c2.one_le_of_natCard_eq_two_pow hF
  have hFc : Fintype.card F = 2 ^ n := by rw [Fintype.card_eq_nat_card, hF]
  obtain ⟨W, iW, mW, fW, ⟨θ₀⟩⟩ :=
    CFSG.QuasithinUnique.Setup.Layer.Actor.exists_binModel_of_binary (V := X)
      fun x => by rw [← pow_two]; exact hX2 x
  have : Nontrivial W := by
    obtain ⟨g, x, hx⟩ := hnt
    by_contra hW
    rw [not_nontrivial_iff_subsingleton] at hW
    exact hx (θ₀.injective (Multiplicative.toAdd.injective (Subsingleton.elim _ _)))
  have hρW : ∀ g x, B42SL3.repOf θ₀ ρ.rangeRestrict g (Multiplicative.toAdd (θ₀ x)) =
      Multiplicative.toAdd (θ₀ (ρ g x)) := fun g x => B42SL3.repOf_toAdd θ₀ _ g x
  have hirrW : (B42SL3.repOf θ₀ ρ.rangeRestrict).IsIrreducible := by
    refine B42SL3.repOf_irreducible θ₀ ?_ ρ.rangeRestrict_surjective
    intro J hJ
    exact hirr J fun g w hw => hJ (ρ g) ⟨g, rfl⟩ w hw
  have hntW : ∃ g, B42SL3.repOf θ₀ ρ.rangeRestrict g ≠ 1 := by
    obtain ⟨g, x, hx⟩ := hnt
    refine ⟨g, fun h1 => hx ?_⟩
    have := hρW g x
    rw [h1, Module.End.one_apply] at this
    exact θ₀.injective (Multiplicative.toAdd.injective this.symm)
  have hcard : Nat.card (commV (Subgroup.zpowers (ρ t))) = 2 ^ Module.finrank (ZMod 2)
      (LinearMap.range (B42SL3.repOf θ₀ ρ.rangeRestrict (up3 0 0 1) - 1)) := by
    obtain ⟨g, hg⟩ := exists_conj_transvection t ht1 ht2
    have e1 : Nat.card (commV (Subgroup.zpowers (ρ (up3 0 0 1)))) =
        Nat.card (commV (Subgroup.zpowers (ρ t))) := by
      have := card_commV_zpowers_conj (ρ g)⁻¹ (ρ t)
      rw [inv_inv] at this
      rw [← hg, map_mul, map_mul, map_inv]
      exact this
    have e2 : Nat.card (commV (Subgroup.zpowers (ρ (up3 0 0 1)))) =
        Nat.card (LinearMap.range (B42SL3.repOf θ₀ ρ.rangeRestrict (up3 0 0 1) - 1) :
          Set W) := by
      refine card_eq_of_binModel θ₀ fun v => ?_
      rw [commV_zpowers_eq_map]
      constructor
      · rintro ⟨x, -, rfl⟩
        refine ⟨Multiplicative.toAdd (θ₀ x), ?_⟩
        rw [LinearMap.sub_apply, Module.End.one_apply, hρW, commHom_apply, map_mul, map_inv,
          toAdd_mul, toAdd_inv, sub_eq_add_neg]
      · rintro ⟨w, hw⟩
        refine ⟨θ₀.symm (Multiplicative.ofAdd w), Subgroup.mem_top _, θ₀.injective ?_⟩
        apply Multiplicative.toAdd.injective
        rw [commHom_apply, map_mul, map_inv, toAdd_mul, toAdd_inv, ← hw, LinearMap.sub_apply,
          Module.End.one_apply, ← hρW, MulEquiv.apply_symm_apply, toAdd_ofAdd, sub_eq_add_neg]
    have e3 : Nat.card (LinearMap.range (B42SL3.repOf θ₀ ρ.rangeRestrict (up3 0 0 1) - 1) :
        Set W) = 2 ^ Module.finrank (ZMod 2)
          (LinearMap.range (B42SL3.repOf θ₀ ρ.rangeRestrict (up3 0 0 1) - 1)) := by
      have : Module.Finite (ZMod 2)
          (LinearMap.range (B42SL3.repOf θ₀ ρ.rangeRestrict (up3 0 0 1) - 1)) :=
        Module.Finite.of_finite
      rw [show Nat.card (LinearMap.range (B42SL3.repOf θ₀ ρ.rangeRestrict (up3 0 0 1) - 1) :
          Set W) = Nat.card (LinearMap.range (B42SL3.repOf θ₀ ρ.rangeRestrict (up3 0 0 1) - 1))
        from rfl, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    rw [← e1, e2, e3]
  have : Module.Finite (ZMod 2) W := Module.Finite.of_finite
  obtain ⟨a, b, hne, hsum, W₀, ⟨e₀⟩⟩ := B42SL3.exists_label hFc hn
    (B42SL3.repOf θ₀ ρ.rangeRestrict) (Module.finBasis (ZMod 2) W) hirrW hntW
  have hdim : ∀ c : (Fin n → Bool) × (Fin n → Bool),
      3 ^ cntS c.1 c.2 * 8 ^ cntH c.1 c.2 ≤
        2 * (tensorRep (F := F) F c.1 c.2 (up3 0 0 1) - 1).rank + 1 :=
    fun c => dim_le_two_mul_rank_tensorRep c.1 c.2
  rcases B42SL3.label_cases hn a b hne _ hdim hsum with ⟨hS, hH⟩ | ⟨-, -, hR⟩ | hR
  ·
    left
    obtain ⟨ψ, hψ, E, hE⟩ := B42SL3.exists_natural_of_single hFc
      (B42SL3.repOf θ₀ ρ.rangeRestrict) (Module.finBasis (ZMod 2) W) hirrW hS hH W₀ e₀
    have hEX : ∀ h x, E (Multiplicative.toAdd (θ₀ (ρ h x))) =
        ((ψ h : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ E (Multiplicative.toAdd (θ₀ x)) := by
      intro h x
      rw [← hρW, hE]
    set σ₀ : SL3 F →* ↥ρ.range := ρ.rangeRestrict.comp ψ with hσ₀
    have hσinj : Function.Injective σ₀ := by
      intro g g' he
      have h1 : ρ (ψ g) = ρ (ψ g') := congrArg Subtype.val he
      have key : ∀ v : Fin 3 → F, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v =
          (g' : Matrix (Fin 3) (Fin 3) F) *ᵥ v := by
        intro v
        have hxv : E (Multiplicative.toAdd (θ₀ (θ₀.symm (Multiplicative.ofAdd (E.symm v))))) =
            v := by simp
        have h2 := hEX (ψ g) (θ₀.symm (Multiplicative.ofAdd (E.symm v)))
        have h3 := hEX (ψ g') (θ₀.symm (Multiplicative.ofAdd (E.symm v)))
        rw [hψ, hxv] at h2 h3
        rw [← h2, ← h3, h1]
      exact Subtype.ext (Matrix.ext_of_mulVec_single fun j => key _)
    have hσsurj : Function.Surjective σ₀ := by
      rintro ⟨_, h, rfl⟩
      exact ⟨ψ h, Subtype.ext (by simp [hσ₀, hψ])⟩
    refine ⟨MulEquiv.ofBijective σ₀ ⟨hσinj, hσsurj⟩,
      θ₀.trans (AddEquiv.toMultiplicative E), fun g v => ?_⟩
    apply Multiplicative.toAdd.injective
    show E (Multiplicative.toAdd (θ₀ (ρ (ψ g) v))) =
      Multiplicative.toAdd (Multiplicative.ofAdd ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ
        E (Multiplicative.toAdd (θ₀ v))))
    rw [hEX, hψ, toAdd_ofAdd]
  · right
    rw [hcard, hF, ← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  · right
    rw [hcard, hF, ← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem le_card_commV_zpowers (hF : Nat.card F = 2 ^ n) (hX2 : ∀ x : X, x ^ 2 = 1)
    (ρ : SL3 F →* MulAut X) (hnt : ∃ g x, ρ g x ≠ x) {t : SL3 F} (ht1 : t ≠ 1)
    (ht2 : t * t = 1) : Nat.card F ≤ Nat.card (commV (Subgroup.zpowers (ρ t))) := by
  have hYinv : ∀ g, ∀ x ∈ commV ρ.range, ρ g x ∈ commV ρ.range := fun g x hx => commV_inv ρ g hx
  obtain ⟨M₀, hM₀inv, -, hM₀Y, hirrS, hntS⟩ := exists_irr_sec ρ (R := ⊥)
    (fun g u hu => by rw [Subgroup.mem_bot] at hu ⊢; rw [hu, map_one]) bot_le
    (commV_range_ne_bot ρ hnt).symm
  set ρS := secRho ρ hYinv hM₀inv with hρS
  have ht2' : t ^ 2 = 1 := by rw [pow_two]; exact ht2
  have hS : Nat.card F ≤ Nat.card (commV (Subgroup.zpowers (ρS t))) := by
    rcases natCoord_or_large hF (sec_sq hX2) ρS hirrS hntS ht1 ht2 with ⟨σ, θ, hθ⟩ | hbig
    · refine le_card_commV_of_coord hθ ?_ ?_
      · rw [Subgroup.zpowers_le]
        exact ⟨t, rfl⟩
      · intro hbot
        apply ht1
        have h1 : ρS t = 1 := by
          have : ρS t ∈ Subgroup.zpowers (ρS t) := Subgroup.mem_zpowers _
          rwa [hbot, Subgroup.mem_bot] at this
        have h2 : t ∈ Subgroup.zpowers t ⊓ ρS.ker := ⟨Subgroup.mem_zpowers t, h1⟩
        rwa [inf_ker_eq_bot ρS hntS (zpowers_sq_eq_one ht2'), Subgroup.mem_bot] at h2
    · have hq : Nat.card F ≤ Nat.card F ^ 2 := Nat.le_self_pow (by norm_num) _
      exact hq.trans hbig
  have hsec := card_commV_sec_le ρ hYinv hM₀inv hM₀Y (Subgroup.zpowers t)
  rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers] at hsec
  exact hS.trans hsec

end Label

end CFSG.Quasithin.MS93.S4A.F
