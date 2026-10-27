module

public import CFSG.Quasithin.Background.SmithB45LnL4Codim
public import CFSG.Quasithin.Background.SmithB45G2Base
public import CFSG.Quasithin.Background.SmithB45Families
public import CFSG.Milestones.CL_LIT_SQTK_simple_list
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Geometry
public import Certificates.Certificate8026Base

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin

open Matrix CFSG.Assembly.LowTwoRank CFSG.Quasithin.B42Ln CFSG.Quasithin.SmithCurtis
open CFSG.Quasithin.JonesParshall

namespace B45Ln

local notation "𝕄₄" => Matrix (Fin 4) (Fin 4) (ZMod 2)

section CodeSub

variable (l : List (Fin 64)) (h0 : (0 : Fin 64) ∈ l)
  (hmul : ∀ c ∈ l, ∀ d ∈ l, code4 (up4 c * up4 d) ∈ l) (hsq : ∀ c ∈ l, up4 c * up4 c = 1)

@[expose] def codeSub : Subgroup G4 where
  carrier := {g | ∃ c ∈ l, g = uOf c}
  one_mem' := by
    refine ⟨0, h0, ?_⟩
    have h : uOf 0 = 1 := Subtype.ext up4_zero
    exact h.symm
  mul_mem' := by
    rintro _ _ ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩
    exact ⟨_, hmul c hc d hd, (uOf_code_mul c d).symm⟩
  inv_mem' := by
    rintro _ ⟨c, hc, rfl⟩
    exact ⟨c, hc, inv_eq_of_mul_eq_one_right (Subtype.ext (hsq c hc))⟩

theorem le_card_codeSub (hnd : l.Nodup) : l.length ≤ Nat.card (codeSub l h0 hmul hsq) := by
  classical
  let F : l.toFinset → codeSub l h0 hmul hsq := fun c =>
    ⟨uOf c, c, List.mem_toFinset.1 c.2, rfl⟩
  have hF : Function.Injective F := by
    intro c d hcd
    have h1 : uOf c = uOf d := congrArg Subtype.val hcd
    have h2 : up4 c = up4 d := congrArg Subtype.val h1
    have h3 : (c : Fin 64) = d := by rw [← code4_up4 c, ← code4_up4 d, h2]
    exact Subtype.ext h3
  have h := Nat.card_le_card_of_injective F hF
  rwa [Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup hnd] at h

theorem card_fix_codeSub {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ' : Representation (ZMod 2) G4 W) :
    Nat.card {x : W // ∀ u ∈ codeSub l h0 hmul hsq, ρ' u x = x} =
      Nat.card {x : W // ∀ c ∈ l, ρ' (uOf c) x = x} := by
  refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ⟨fun h c hc => h _ ⟨c, hc, rfl⟩, ?_⟩)
  rintro h _ ⟨c, hc, rfl⟩
  exact h c hc

end CodeSub

variable {V : Type} [CommGroup V] [Finite V] {G L : Subgroup (MulAut V)}
  [Module (ZMod 2) (Additive V)]

theorem qhatOf_le_one_of_sub (hV : ∀ v : V, v ^ 2 = 1) (hHyp : B4Hyp G L)
    (e : ↥L ≃* ↥(StatedSL 4 (ZMod 2))) {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ' : Representation (ZMod 2) G4 W) (κ : G4 ≃* G4) (β : Additive V ≃ₗ[ZMod 2] W)
    (hβ : ∀ g w, β (repOf4 (phiOf4 e) g w) = ρ' (κ g) (β w)) (Y : Subgroup G4)
    (hYc : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a) (hY2 : ∀ a ∈ Y, a * a = 1) (hY1 : Y ≠ ⊥)
    (hcard : Nat.card W ≤ Nat.card Y * Nat.card {x : W // ∀ u ∈ Y, ρ' u x = x}) :
    qhatOf G ≤ ((1 : ℚ) : WithTop ℚ) := by
  obtain ⟨-, hLF, -, -⟩ := hHyp
  have hLG : L ≤ G := hLF ▸ quasithinGenFitting_le G
  let ι : G4 →* MulAut V := (fL4 e).comp κ.symm.toMonoidHom
  have hιinj : Function.Injective ι := fun a b hab => κ.symm.injective (fL4_injective e hab)
  obtain ⟨E, hE⟩ : ∃ E, E = Y.map ι := ⟨_, rfl⟩
  have hEL : E ≤ L := by
    rw [hE]
    rintro _ ⟨g, -, rfl⟩
    exact fL4_mem e _
  have hEe : IsElemAbelian2 E := by
    rw [hE]
    refine ⟨?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, hYc a ha b hb]
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow, pow_two, hY2 a ha, map_one]
  have hEcard : Nat.card E = Nat.card Y := by
    rw [hE]
    exact Subgroup.card_map_of_injective hιinj
  have hEne : E ≠ ⊥ := by
    rw [hE, Ne, Subgroup.map_eq_bot_iff_of_injective Y hιinj]
    exact hY1
  have hEA2 : IsA2 G E := ⟨hEL.trans hLG, hEne, hEe⟩
  have hact : ∀ (u : G4) (v : V),
      β (Additive.ofMul (ι u v)) = ρ' u (β (Additive.ofMul v)) := fun u v => by
    have h1 := hβ (κ.symm u) (Additive.ofMul v)
    rw [MulEquiv.apply_symm_apply, repOf4_apply, ← fL4_apply] at h1
    exact h1
  have hfix : Nat.card (fixV E) = Nat.card {x : W // ∀ u ∈ Y, ρ' u x = x} := by
    refine Nat.card_congr
      { toFun := fun v => ⟨β (Additive.ofMul (v : V)), fun u hu => ?_⟩
        invFun := fun x => ⟨Additive.toMul (β.symm x.1), ?_⟩
        left_inv := fun v => Subtype.ext ?_
        right_inv := fun x => Subtype.ext ?_ }
    · rw [← hact, v.2 (ι u) (hE ▸ ⟨u, hu, rfl⟩)]
    · intro y hy
      rw [hE] at hy
      obtain ⟨u, hu, rfl⟩ := hy
      apply Additive.ofMul.injective
      apply β.injective
      rw [hact, ofMul_toMul, LinearEquiv.apply_symm_apply]
      exact x.2 u hu
    · change Additive.toMul (β.symm (β (Additive.ofMul (v : V)))) = v
      rw [LinearEquiv.symm_apply_apply, toMul_ofMul]
    · change β (Additive.ofMul (Additive.toMul (β.symm x.1))) = x.1
      rw [ofMul_toMul, LinearEquiv.apply_symm_apply]
  have hVW : Nat.card V = Nat.card W :=
    Nat.card_congr ((Additive.ofMul : V ≃ Additive V).trans β.toEquiv)
  have hr : rAV E ≤ 1 := by
    refine (rAV_le_one_iff hV hEA2).2 ?_
    rw [hVW, hEcard, hfix]
    exact hcard
  exact qhatOf_le_one_of_rAV_le_one hV hEA2 hr

theorem qhatOf_le_one_of_codes (hV : ∀ v : V, v ^ 2 = 1) (hHyp : B4Hyp G L)
    (e : ↥L ≃* ↥(StatedSL 4 (ZMod 2))) {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ' : Representation (ZMod 2) G4 W) (κ : G4 ≃* G4) (β : Additive V ≃ₗ[ZMod 2] W)
    (hβ : ∀ g w, β (repOf4 (phiOf4 e) g w) = ρ' (κ g) (β w)) (l : List (Fin 64))
    (h0 : (0 : Fin 64) ∈ l) (hmul : ∀ c ∈ l, ∀ d ∈ l, code4 (up4 c * up4 d) ∈ l)
    (hsq : ∀ c ∈ l, up4 c * up4 c = 1) (hcomm : ∀ c ∈ l, ∀ d ∈ l, up4 c * up4 d = up4 d * up4 c)
    (hnd : l.Nodup) (h2 : 2 ≤ l.length)
    (hcard : Nat.card W ≤ l.length * Nat.card {x : W // ∀ c ∈ l, ρ' (uOf c) x = x}) :
    qhatOf G ≤ ((1 : ℚ) : WithTop ℚ) := by
  have hY := le_card_codeSub l h0 hmul hsq hnd
  refine qhatOf_le_one_of_sub hV hHyp e ρ' κ β hβ (codeSub l h0 hmul hsq) ?_ ?_ ?_ ?_
  · rintro _ ⟨c, hc, rfl⟩ _ ⟨d, hd, rfl⟩
    exact Subtype.ext (hcomm c hc d hd)
  · rintro _ ⟨c, hc, rfl⟩
    exact Subtype.ext (hsq c hc)
  · intro h1
    have h3 : Nat.card (codeSub l h0 hmul hsq) = 1 := by rw [h1, Subgroup.card_bot]
    omega
  · rw [card_fix_codeSub]
    exact hcard.trans (Nat.mul_le_mul_right _ hY)

theorem card_fix_nat :
    Nat.card {x : Fin 4 → ZMod 2 // ∀ c ∈ ([0, 1] : List (Fin 64)), up4 c *ᵥ x = x} = 8 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

theorem card_fix_wedge :
    Nat.card {x : Fin 6 → ZMod 2 // ∀ c ∈ te0L, wedgeMat4 (up4 c) *ᵥ x = x} = 8 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

theorem qhatOf_le_one_nat (hV : ∀ v : V, v ^ 2 = 1) (hHyp : B4Hyp G L)
    (e : ↥L ≃* ↥(StatedSL 4 (ZMod 2))) (κ : G4 ≃* G4) (β : Additive V ≃ₗ[ZMod 2] (Fin 4 → ZMod 2))
    (hβ : ∀ g w, β (repOf4 (phiOf4 e) g w) = natRep4 (κ g) (β w)) :
    qhatOf G ≤ ((1 : ℚ) : WithTop ℚ) := by
  refine qhatOf_le_one_of_codes hV hHyp e natRep4 κ β hβ [0, 1] (by decide) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide) ?_
  have h := card_fix_nat
  rw [Nat.card_eq_fintype_card (α := Fin 4 → ZMod 2), Fintype.card_fun, ZMod.card]
  change 2 ^ 4 ≤ 2 * Nat.card {x : Fin 4 → ZMod 2 // ∀ c ∈ ([0, 1] : List (Fin 64)),
    up4 c *ᵥ x = x}
  rw [h]
  norm_num

theorem qhatOf_le_one_wedge (hV : ∀ v : V, v ^ 2 = 1) (hHyp : B4Hyp G L)
    (e : ↥L ≃* ↥(StatedSL 4 (ZMod 2))) (β : Additive V ≃ₗ[ZMod 2] (Fin 6 → ZMod 2))
    (hβ : ∀ g w, β (repOf4 (phiOf4 e) g w) = wedgeRep4' g (β w)) :
    qhatOf G ≤ ((1 : ℚ) : WithTop ℚ) := by
  refine qhatOf_le_one_of_codes hV hHyp e wedgeRep4' (MulEquiv.refl G4) β hβ te0L (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide) ?_
  have h := card_fix_wedge
  rw [Nat.card_eq_fintype_card (α := Fin 6 → ZMod 2), Fintype.card_fun, ZMod.card]
  change 2 ^ 6 ≤ 8 * Nat.card {x : Fin 6 → ZMod 2 // ∀ c ∈ te0L, wedgeMat4 (up4 c) *ᵥ x = x}
  rw [h]
  norm_num

theorem type_cases {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    {ρ : Representation (ZMod 2) G4 W} (hρ : IsSimpleRep ρ) :
    L4Model ρ ∨ 24 ≤ Module.finrank (ZMod 2) W ∨
      (∃ β : W ≃ₗ[ZMod 2] (Fin 20 → ZMod 2), ∀ g w, β (ρ g w) = rep20 g (β w)) ∨
      (∃ β : W ≃ₗ[ZMod 2] (Fin 20 → ZMod 2), ∀ g w, β (ρ g w) = rep20d g (β w)) ∨
      (∃ β : W ≃ₗ[ZMod 2] (Fin 14 → ZMod 2), ∀ g w, β (ρ g w) = rep14 g (β w)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, μ, ht⟩ := exists_isType4 hρ
  have hμ : μ = ![μ 0, μ 1, μ 2] := by
    funext s
    fin_cases s <;> rfl
  rw [hμ] at ht
  rcases zmod2_eq (μ 0) with h0 | h0 <;> rcases zmod2_eq (μ 1) with h1 | h1 <;>
    rcases zmod2_eq (μ 2) with h2 | h2 <;> rw [h0, h1, h2] at ht
  · exact Or.inl (l4Model_of_type hρ ht (by decide))
  · exact Or.inl (l4Model_of_type hρ ht (by decide))
  · exact Or.inl (l4Model_of_type hρ ht (by decide))
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      (datum4.iso_of_isCurtisType hρ rep20d_simple_type.1 ht rep20d_simple_type.2))))
  · exact Or.inl (l4Model_of_type hρ ht (by decide))
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      (datum4.iso_of_isCurtisType hρ rep14_simple_type.1 ht rep14_simple_type.2))))
  · exact Or.inr (Or.inr (Or.inl
      (datum4.iso_of_isCurtisType hρ rep20_simple_type.1 ht rep20_simple_type.2)))
  · exact Or.inr (Or.inl (twentyfour_le_finrank hρ ht (by decide)))

end B45Ln

open B45Ln in
theorem asB45L42_holds : AsB45L42 := by
  intro V _ _ hV G L hHyp hP hq
  classical
  obtain ⟨A, hA, -, hcard⟩ := exists_cubic_of_qhatOf_le_two hV hq
  obtain ⟨hZ, hmodel, -⟩ := hP
  obtain ⟨e⟩ := exists_statedSL_of_model hZ hmodel
  let : Module (ZMod 2) (Additive V) := zmod2Mod hV
  have : Finite (Additive V) := inferInstanceAs (Finite V)
  have : Nontrivial V := nontrivial_of_equiv4 e
  have hρ : IsSimpleRep (repOf4 (phiOf4 e)) :=
    isSimpleRep_repOf4 (phiOf4 e) (irr_of_isIrrSec hHyp.2.2.2)
  have h2F : (fixV A).index ≤ Nat.card A ^ 2 := by
    rw [← (fixV A).index_mul_card] at hcard
    exact Nat.le_of_mul_le_mul_right hcard Nat.card_pos
  have hmod : L4Model (repOf4 (phiOf4 e)) → qhatOf G ≤ ((1 : ℚ) : WithTop ℚ) := by
    rintro (htriv | ⟨κ, β, hβ⟩ | ⟨β, hβ⟩)
    · exact (not_trivial4 e htriv).elim
    · exact qhatOf_le_one_nat hV hHyp e κ β hβ
    · exact qhatOf_le_one_wedge hV hHyp e β hβ
  rcases card_le_or_l4Model hHyp hZ e hA h2F with hV18 | hm
  · have hcard20 : ∀ β : Additive V ≃ₗ[ZMod 2] (Fin 20 → ZMod 2), False := fun β => by
      have h1 : Nat.card V = 2 ^ 20 := by
        rw [show Nat.card V = Nat.card (Additive V) from rfl, Nat.card_congr β.toEquiv,
          Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card]
        rfl
      omega
    rcases type_cases hρ with hm | h24 | ⟨β, -⟩ | ⟨β, -⟩ | ⟨β, hβ⟩
    · exact hmod hm
    · exfalso
      have h1 : 2 ^ 24 ≤ Nat.card V := by
        rw [card_eq_two_pow_finrank]
        exact Nat.pow_le_pow_right (by norm_num) h24
      omega
    · exact (hcard20 β).elim
    · exact (hcard20 β).elim
    · exact (false_of_rep14 hHyp hZ e hβ hA h2F).elim
  · exact hmod hm

end CFSG.Quasithin
