module

public import CFSG.Quasithin.Vol2.Ch3Sec2Prop329Rows
public import CFSG.Quasithin.Background.FFC4Zmod

public section

namespace CFSG.Quasithin.H13.Prop329.Alt7

open CFSG.Quasithin CFSG.Quasithin.G6

theorem toAdd_allOnes_zpow (k : ℤ) (i : Fin 7) :
    Multiplicative.toAdd (G6.allOnes 7 ^ k) i = (k : ZMod 2) := by
  rw [toAdd_zpow]
  simp [G6.allOnes]

theorem altDn_ker_eq_bot : (FFModel.altDn 7).ker = ⊥ := by
  show Subgroup.zpowers (G6.allOnes 7) ⊓ G6.coreMod 7 = ⊥
  rw [eq_bot_iff]
  rintro x ⟨hx1, hx2⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx1
  have hx2 : G6.allOnes 7 ^ k ∈ G6.coreMod 7 := hx2
  rw [G6.mem_coreMod] at hx2
  simp only [toAdd_allOnes_zpow, Finset.sum_const, Finset.card_univ, Fintype.card_fin] at hx2
  have hk : (k : ZMod 2) = 0 := by
    have h7 : (7 : ZMod 2) = 1 := by decide
    rwa [nsmul_eq_mul, Nat.cast_ofNat, h7, one_mul] at hx2
  rw [Subgroup.mem_bot]
  apply Multiplicative.toAdd.injective
  funext i
  rw [toAdd_allOnes_zpow, hk]
  rfl

@[expose] def s01 : Equiv.Perm (Fin 7) := Equiv.swap 0 1

theorem s01_mul_self : s01 * s01 = 1 := Equiv.swap_mul_self 0 1

theorem s01_inv : s01⁻¹ = s01 := Equiv.swap_inv 0 1

@[expose] def sAut : ↥(G6.coreMod 7) ≃* ↥(G6.coreMod 7) where
  toFun x := ⟨G6.permAct 7 s01 x, G6.permAct_mem_coreMod s01 x.2⟩
  invFun x := ⟨G6.permAct 7 s01 x, G6.permAct_mem_coreMod s01 x.2⟩
  left_inv x := Subtype.ext (by
    change G6.permAct 7 s01 (G6.permAct 7 s01 x) = x
    rw [← MulAut.mul_apply, ← map_mul, s01_mul_self, map_one, MulAut.one_apply])
  right_inv x := Subtype.ext (by
    change G6.permAct 7 s01 (G6.permAct 7 s01 x) = x
    rw [← MulAut.mul_apply, ← map_mul, s01_mul_self, map_one, MulAut.one_apply])
  map_mul' x y := Subtype.ext (map_mul (G6.permAct 7 s01) (x : G6.PermMod 7) y)

theorem sAut_apply (x : ↥(G6.coreMod 7)) :
    ((sAut x : ↥(G6.coreMod 7)) : G6.PermMod 7) = G6.permAct 7 s01 x :=
  rfl

theorem s01_sub_apply : ∀ (y : Fin 7 → ZMod 2) (i : Fin 7),
    y (s01 i) + -y i = (y 0 + y 1) * ((Pi.single 0 1 + Pi.single 1 1 : Fin 7 → ZMod 2) i) := by
  decide +kernel

theorem permAct_s01_mul_inv (x : G6.PermMod 7) :
    G6.permAct 7 s01 x * x⁻¹ = 1 ∨
      G6.permAct 7 s01 x * x⁻¹ = Multiplicative.ofAdd (Pi.single 0 1 + Pi.single 1 1) := by
  have key : ∀ i : Fin 7, Multiplicative.toAdd (G6.permAct 7 s01 x * x⁻¹) i =
      (Multiplicative.toAdd x 0 + Multiplicative.toAdd x 1) *
        ((Pi.single 0 1 + Pi.single 1 1 : Fin 7 → ZMod 2) i) := by
    intro i
    rw [toAdd_mul, toAdd_inv, Pi.add_apply, Pi.neg_apply, G6.permAct_apply, s01_inv]
    exact s01_sub_apply _ i
  rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 by decide)
      (Multiplicative.toAdd x 0 + Multiplicative.toAdd x 1) with h | h
  · left
    apply Multiplicative.toAdd.injective
    funext i
    rw [key i, h, zero_mul]
    rfl
  · right
    apply Multiplicative.toAdd.injective
    funext i
    rw [key i, h, one_mul]
    rfl

variable {W : Type*} [CommGroup W] {Λ : Subgroup (MulAut W)}

theorem isFFModule_normalizer (h : AlternatingNatural Λ ⊤ ⊥ 7) :
    IsFFModule (Subgroup.normalizer (Λ : Set (MulAut W))) := by
  obtain ⟨π, hπ⟩ := h
  obtain ⟨f, hfs, hfk, hfe⟩ := FFC.RealizesVia.secMap altDn_ker_eq_bot hπ
  have hfi : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext ((Subgroup.mem_bot).1 ((hfk u).1 hu))
  let e : W ≃* ↥(G6.coreMod 7) :=
    Subgroup.topEquiv.symm.trans (MulEquiv.ofBijective f ⟨hfi, hfs⟩)
  have he : ∀ (σ : ↥(alternatingGroup (Fin 7))) (w : W),
      ((e (((π σ : ↥Λ) : MulAut W) w) : ↥(G6.coreMod 7)) : G6.PermMod 7) =
        G6.permAct 7 (σ : Equiv.Perm (Fin 7)) (e w) :=
    fun σ w => hfe σ ⟨w, Subgroup.mem_top w⟩ (Subgroup.mem_top _)
  let φ : MulAut W := e.trans (sAut.trans e.symm)
  have hφe : ∀ w : W, e (φ w) = sAut (e w) := fun w => by
    change e (e.symm (sAut (e w))) = sAut (e w)
    rw [MulEquiv.apply_symm_apply]
  have hφφ : φ * φ = 1 := by
    ext w
    apply e.injective
    rw [MulAut.mul_apply, hφe, hφe, MulAut.one_apply]
    apply Subtype.ext
    rw [sAut_apply, sAut_apply, ← MulAut.mul_apply, ← map_mul, s01_mul_self, map_one,
      MulAut.one_apply]
  have hφinv : φ⁻¹ = φ := inv_eq_of_mul_eq_one_right hφφ
  have hconj : ∀ σ : ↥(alternatingGroup (Fin 7)),
      φ * ((π σ : ↥Λ) : MulAut W) * φ⁻¹ =
        ((π ⟨s01 * (σ : Equiv.Perm (Fin 7)) * s01⁻¹,
          (alternatingGroup.normal (α := Fin 7)).conj_mem _ σ.2 s01⟩ : ↥Λ) : MulAut W) := by
    intro σ
    ext w
    apply e.injective
    apply Subtype.ext
    rw [hφinv, MulAut.mul_apply, MulAut.mul_apply, hφe, sAut_apply, he, hφe, sAut_apply, he]
    rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← map_mul, ← map_mul]
    show _ = G6.permAct 7 (s01 * (σ : Equiv.Perm (Fin 7)) * s01⁻¹) _
    rw [s01_inv]
  have hφN : φ ∈ Subgroup.normalizer (Λ : Set (MulAut W)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      obtain ⟨σ, hσ⟩ := hπ.1 ⟨x, hx⟩
      have hx' : x = ((π σ : ↥Λ) : MulAut W) := (congrArg Subtype.val hσ).symm
      rw [hx', hconj σ]
      exact (π _).2
    · intro hx
      obtain ⟨σ, hσ⟩ := hπ.1 ⟨_, hx⟩
      have hx' : φ * x * φ⁻¹ = ((π σ : ↥Λ) : MulAut W) := (congrArg Subtype.val hσ).symm
      have : x = φ * ((π σ : ↥Λ) : MulAut W) * φ⁻¹ := by
        rw [← hx', hφinv]
        calc x = (φ * φ) * x * (φ * φ) := by rw [hφφ, one_mul, mul_one]
          _ = φ * (φ * x * φ) * φ := by group
      rw [this, hconj σ]
      exact (π _).2
  have hφ1 : φ ≠ 1 := by
    intro h1
    set x₀ : G6.PermMod 7 := Multiplicative.ofAdd (Pi.single 0 1 + Pi.single 2 1) with hx₀
    have hx₀m : x₀ ∈ G6.coreMod 7 := by
      rw [G6.mem_coreMod]
      decide
    have h2 := congrArg (fun ψ : MulAut W => e (ψ (e.symm ⟨x₀, hx₀m⟩))) h1
    simp only [hφe, MulAut.one_apply, MulEquiv.apply_symm_apply] at h2
    have h3 := congrFun (congrArg Multiplicative.toAdd (congrArg Subtype.val h2)) 1
    rw [sAut_apply, G6.permAct_apply, s01_inv] at h3
    have h4 : (Pi.single 0 1 + Pi.single 2 1 : Fin 7 → ZMod 2) (s01 1) =
        (Pi.single 0 1 + Pi.single 2 1 : Fin 7 → ZMod 2) 1 := h3
    revert h4
    decide
  refine ⟨Subgroup.zpowers φ, (Subgroup.zpowers_le).2 hφN, ?_, ?_, ?_⟩
  · rw [Ne, Subgroup.zpowers_eq_bot]
    exact hφ1
  · refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      rw [← zpow_add, ← zpow_add, add_comm]
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, sq, hφφ, one_zpow]
  ·
    have hfix : ∀ w : W, w ∈ fixV (Subgroup.zpowers φ) ↔ φ w = w := by
      intro w
      constructor
      · intro hw
        exact hw φ (Subgroup.mem_zpowers φ)
      · intro hw a ha
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
        have hpow : ∀ n : ℕ, (φ ^ n) w = w := by
          intro n
          induction n with
          | zero => rfl
          | succ n ih => rw [pow_succ, MulAut.mul_apply, hw, ih]
        rcases Int.eq_nat_or_neg i with ⟨n, rfl | rfl⟩
        · rw [zpow_natCast, hpow]
        · rw [zpow_neg, zpow_natCast]
          calc ((φ ^ n)⁻¹ : MulAut W) w = (φ ^ n).symm ((φ ^ n) w) := by rw [hpow]; rfl
            _ = w := (φ ^ n).symm_apply_apply w
    let ψ : W →* W :=
      { toFun := fun w => φ w * w⁻¹
        map_one' := by simp
        map_mul' := fun a b => by
          rw [map_mul, mul_inv, mul_mul_mul_comm] }
    have hker : ψ.ker = fixV (Subgroup.zpowers φ) := by
      ext w
      rw [MonoidHom.mem_ker, hfix]
      exact mul_inv_eq_one
    have hrange : Nat.card ψ.range ≤ 2 := by
      classical
      set w₀ : W := e.symm ⟨Multiplicative.ofAdd (Pi.single 0 1 + Pi.single 1 1), by
        rw [G6.mem_coreMod]; decide⟩ with hw₀
      have hsub : (ψ.range : Set W) ⊆ ({1, w₀} : Finset W) := by
        rintro _ ⟨w, rfl⟩
        change φ w * w⁻¹ ∈ (({1, w₀} : Finset W) : Set W)
        rw [Finset.coe_insert, Finset.coe_singleton]
        have hmap : e (φ w * w⁻¹) = ⟨G6.permAct 7 s01 (e w) * (e w : G6.PermMod 7)⁻¹,
            (G6.coreMod 7).mul_mem (G6.permAct_mem_coreMod s01 (e w).2)
              ((G6.coreMod 7).inv_mem (e w).2)⟩ := by
          apply Subtype.ext
          rw [map_mul, map_inv, hφe]
          rfl
        rcases permAct_s01_mul_inv (e w : G6.PermMod 7) with h0 | h0
        · left
          apply e.injective
          rw [hmap, map_one]
          exact Subtype.ext h0
        · right
          rw [Set.mem_singleton_iff, hw₀]
          apply e.injective
          rw [hmap, MulEquiv.apply_symm_apply]
          exact Subtype.ext h0
      calc Nat.card ψ.range = Nat.card (ψ.range : Set W) := rfl
        _ ≤ Nat.card ((({1, w₀} : Finset W) : Set W)) := Nat.card_mono (Set.toFinite _) hsub
        _ = (({1, w₀} : Finset W)).card := (Nat.card_coe_set_eq _).trans (Set.ncard_coe_finset _)
        _ ≤ 2 := Finset.card_le_two
    have hcardA : Nat.card (Subgroup.zpowers φ) = 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (by rw [sq, hφφ]) hφ1
    have h1 := ψ.ker.card_mul_index
    rw [Subgroup.index_ker, hker] at h1
    rw [hcardA, ← h1, mul_comm]
    exact Nat.mul_le_mul_right _ hrange

end CFSG.Quasithin.H13.Prop329.Alt7

namespace CFSG.Quasithin.H13

theorem row329Alt7_holds : Row329Alt7 := fun _ _ _ _ h => Prop329.Alt7.isFFModule_normalizer h

end CFSG.Quasithin.H13
