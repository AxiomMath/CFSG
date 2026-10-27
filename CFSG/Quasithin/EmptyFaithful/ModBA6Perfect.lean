module

public import CFSG.Quasithin.H13.VolIAltCoverSix
public import CFSG.Quasithin.EmptyFaithful.ModA6Core
public import CFSG.Quasithin.EmptyFaithful.ModBA7Core
public import CFSG.Quasithin.EmptyFaithful.ModBA6Sub

public section

namespace CFSG.Quasithin

namespace ModB

open Equiv Equiv.Perm Subgroup CFSG.Quasithin CFSG.Quasithin.G6

private theorem card_modEq_fixed_prime6 {p : ℕ} [hp : Fact p.Prime] {α : Type*} [Finite α] (f : α → α)
    (hf : f^[p] = id) : Nat.card α ≡ Nat.card {a // f a = a} [MOD p] := by
  classical
  have : Fintype α := Fintype.ofFinite α
  let g : Function.End α := f
  have h5 : g ^ p ^ 1 = (1 : Function.End α) := by
    rw [pow_one]
    funext a
    exact congrFun hf a
  have h := Equiv.Perm.card_fixedPoints_modEq (α := α) (f := g) (p := p) (n := 1) h5
  have e : Nat.card {a // f a = a} = Nat.card ↑(Function.fixedPoints g) :=
    Nat.card_congr (Equiv.refl _)
  rw [e, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact h

section Orbit

variable {X : Type*} [MulAction A6 X]

private theorem card_orbit_dvd6 (x₀ : X) : Nat.card (MulAction.orbit A6 x₀) ∣ 360 := by
  rw [← card_A6, Nat.card_congr (MulAction.orbitEquivQuotientStabilizer A6 x₀)]
  exact Subgroup.index_dvd_card _

private theorem six_le_card_of_nontrivial {Y : Type*} [MulAction A6 Y] [Finite Y]
    (h : ∃ (y : Y) (σ : A6), σ • y ≠ y) : 6 ≤ Nat.card Y := by
  by_contra hlt
  push Not at hlt
  have hn : (MulAction.toPermHom A6 Y).ker.Normal := MonoidHom.normal_ker _
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (MulAction.toPermHom A6 Y).ker with hb | ht
  · have hinj := (MonoidHom.ker_eq_bot_iff _).mp hb
    have h1 := Nat.card_le_card_of_injective _ hinj
    rw [card_A6, Nat.card_perm] at h1
    have h2 : (Nat.card Y).factorial ≤ (5 : ℕ).factorial := Nat.factorial_le (by omega)
    have h3 : (5 : ℕ).factorial = 120 := by decide
    omega
  · obtain ⟨y, σ, hy⟩ := h
    apply hy
    have hσ : σ ∈ (MulAction.toPermHom A6 Y).ker := by rw [ht]; trivial
    rw [MonoidHom.mem_ker] at hσ
    have := congrArg (fun f : Perm Y => f y) hσ
    simpa using this

end Orbit

section Counting

variable {Ω : Type*} [MulAction A6 Ω]

private theorem card_modEq_set6 [Finite Ω] {p : ℕ} [Fact p.Prime] (S : Set Ω) {g : A6} (hg : g ^ p = 1)
    (hS : ∀ s ∈ S, g • s ∈ S) :
    S.ncard ≡ (S ∩ MulAction.fixedBy Ω g).ncard [MOD p] := by
  let f : S → S := fun a => ⟨g • a.1, hS a.1 a.2⟩
  have key : ∀ (n : ℕ) (a : S), (f^[n] a).1 = g ^ n • a.1 := by
    intro n
    induction n with
    | zero => intro a; simp
    | succ n ih =>
      intro a
      rw [Function.iterate_succ_apply, ih, pow_succ, mul_smul]
  have hf : f^[p] = id := by
    funext a
    apply Subtype.ext
    rw [key, hg, one_smul]
    rfl
  have h := card_modEq_fixed_prime6 f hf
  have e : Nat.card {a : S // f a = a} = (S ∩ MulAction.fixedBy Ω g).ncard := by
    rw [← Nat.card_coe_set_eq]
    refine Nat.card_congr
      { toFun := fun a => ⟨a.1.1, a.1.2, by
          have := congrArg Subtype.val a.2
          simpa [f] using this⟩
        invFun := fun a => ⟨⟨a.1, a.2.1⟩, Subtype.ext (by simpa [f] using a.2.2)⟩
        left_inv := fun a => rfl
        right_inv := fun a => rfl }
  rw [e, Nat.card_coe_set_eq] at h
  exact h

end Counting

section Chars

variable {W : Type} [CommGroup W]

private def charSmul6 (ρ : A6 →* MulAut W) (σ : A6) (χ : W →* ℂˣ) : W →* ℂˣ :=
  χ.comp (ρ σ)⁻¹.toMonoidHom

private theorem charSmul6_apply (ρ : A6 →* MulAut W) (σ : A6) (χ : W →* ℂˣ) (w : W) :
    charSmul6 ρ σ χ w = χ ((ρ σ)⁻¹ w) := rfl

@[instance_reducible] private def charAct6 (ρ : A6 →* MulAut W) : MulDistribMulAction A6 (W →* ℂˣ) where
  smul := charSmul6 ρ
  one_smul χ := by
    refine MonoidHom.ext fun w => ?_
    show χ ((ρ 1)⁻¹ w) = χ w
    simp
  mul_smul σ τ χ := by
    refine MonoidHom.ext fun w => ?_
    show χ ((ρ (σ * τ))⁻¹ w) = χ ((ρ τ)⁻¹ ((ρ σ)⁻¹ w))
    simp [mul_inv_rev]
  smul_mul σ χ₁ χ₂ := by
    refine MonoidHom.ext fun w => ?_
    show (χ₁ * χ₂) ((ρ σ)⁻¹ w) = χ₁ ((ρ σ)⁻¹ w) * χ₂ ((ρ σ)⁻¹ w)
    simp
  smul_one σ := by
    refine MonoidHom.ext fun w => ?_
    show (1 : W →* ℂˣ) ((ρ σ)⁻¹ w) = 1
    simp

private theorem char_mul_self6 (hW2 : ∀ w : W, w ^ 2 = 1) (χ : W →* ℂˣ) (w : W) : χ w * χ w = 1 := by
  rw [← map_mul, ← sq, hW2, map_one]

private theorem char_eq_one_or_neg (hW2 : ∀ w : W, w ^ 2 = 1) (χ : W →* ℂˣ) (w : W) :
    χ w = 1 ∨ χ w = -1 := by
  have h := char_mul_self6 hW2 χ w
  have h' : ((χ w : ℂˣ) : ℂ) * ((χ w : ℂˣ) : ℂ) = 1 := by
    have := congrArg (fun u : ℂˣ => (u : ℂ)) h
    simpa using this
  rcases mul_self_eq_one_iff.mp h' with h1 | h1
  · left; exact Units.ext h1
  · right; exact Units.ext (by simpa using h1)

private def Kgrp6 (Z : Subgroup W) : Subgroup (W →* ℂˣ) := (MonoidHom.domRestrictHom Z ℂˣ).ker

private theorem mem_Kgrp6 {Z : Subgroup W} {μ : W →* ℂˣ} : μ ∈ Kgrp6 Z ↔ ∀ z ∈ Z, μ z = 1 := by
  simp only [Kgrp6, MonoidHom.mem_ker]
  constructor
  · intro h z hz
    have := DFunLike.congr_fun h ⟨z, hz⟩
    simpa using this
  · intro h
    refine MonoidHom.ext fun z => ?_
    simpa using h z z.2

private theorem card_Kgrp6 [Finite W] (hW2 : ∀ w : W, w ^ 2 = 1) [Nontrivial W] (Z : Subgroup W) :
    Nat.card (Kgrp6 Z) = Z.index := by
  have hexp : Monoid.exponent W = 2 :=
    (Monoid.exponent_eq_prime_iff Nat.prime_two).mpr fun g hg => orderOf_eq_prime (hW2 g) hg
  have : HasEnoughRootsOfUnity ℂ (Monoid.exponent W) := by rw [hexp]; infer_instance
  have h := CommGroup.card_domRestrictHom_ker (G := W) (M := ℂ) Z
  rw [Subgroup.index_eq_card]
  exact h

private theorem card_chars [Finite W] (hW2 : ∀ w : W, w ^ 2 = 1) [Nontrivial W] :
    Nat.card (W →* ℂˣ) = Nat.card W := by
  have h := card_Kgrp6 hW2 (⊥ : Subgroup W)
  have hk : Kgrp6 (⊥ : Subgroup W) = ⊤ := by
    refine eq_top_iff.mpr fun μ _ => ?_
    rw [mem_Kgrp6]
    intro z hz
    rw [Subgroup.mem_bot] at hz
    rw [hz, map_one]
  rw [hk, Subgroup.card_top, Subgroup.index_bot] at h
  exact h

private theorem exists_char_ne_one [Finite W] (hW2 : ∀ w : W, w ^ 2 = 1) {w : W} (hw : w ≠ 1) :
    ∃ χ : W →* ℂˣ, χ w ≠ 1 := by
  have : Nontrivial W := ⟨⟨w, 1, hw⟩⟩
  by_contra hcon
  push Not at hcon
  have hZ : Kgrp6 (Subgroup.zpowers w) = ⊤ := by
    refine eq_top_iff.mpr fun μ _ => ?_
    rw [mem_Kgrp6]
    intro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [map_zpow, hcon μ, one_zpow]
  have h1 := card_Kgrp6 hW2 (Subgroup.zpowers w)
  rw [hZ, Subgroup.card_top] at h1
  have h2 := card_chars hW2 (W := W)
  have h3 : (Subgroup.zpowers w).index = Nat.card W := by rw [← h1, h2]
  have h4 := Subgroup.card_mul_index (Subgroup.zpowers w)
  rw [h3] at h4
  have hpos : 0 < Nat.card W := Nat.card_pos
  have h5 : Nat.card (Subgroup.zpowers w) = 1 := by
    have := Nat.eq_of_mul_eq_mul_right hpos (h4.trans (one_mul _).symm)
    exact this
  have : w ∈ Subgroup.zpowers w := Subgroup.mem_zpowers w
  rw [Nat.card_eq_one_iff_unique] at h5
  obtain ⟨hsub, -⟩ := h5
  have := hsub.elim ⟨w, this⟩ ⟨1, Subgroup.one_mem _⟩
  exact hw (congrArg Subtype.val this)

private def fixSub6 (ρ : A6 →* MulAut W) (g : A6) : Subgroup (W →* ℂˣ) where
  carrier := {μ | charSmul6 ρ g μ = μ}
  one_mem' := by
    refine MonoidHom.ext fun w => ?_
    simp [charSmul6_apply]
  mul_mem' := fun {a b} ha hb => by
    refine MonoidHom.ext fun w => ?_
    have h1 := DFunLike.congr_fun ha w
    have h2 := DFunLike.congr_fun hb w
    simp only [charSmul6_apply] at h1 h2
    show (a * b) ((ρ g)⁻¹ w) = (a * b) w
    rw [MonoidHom.mul_apply, MonoidHom.mul_apply, h1, h2]
  inv_mem' := fun {a} ha => by
    refine MonoidHom.ext fun w => ?_
    have h1 := DFunLike.congr_fun ha w
    simp only [charSmul6_apply] at h1
    show (a⁻¹) ((ρ g)⁻¹ w) = (a⁻¹) w
    rw [MonoidHom.inv_apply, MonoidHom.inv_apply, h1]

private theorem mem_fixSub6 {ρ : A6 →* MulAut W} {g : A6} {μ : W →* ℂˣ} :
    μ ∈ fixSub6 ρ g ↔ charSmul6 ρ g μ = μ := Iff.rfl

private theorem char_eq_one_of_fixed6 {ρ : A6 →* MulAut W} (hcomm : commV ρ.range = ⊤) {χ : W →* ℂˣ}
    (hfix : ∀ σ : A6, charSmul6 ρ σ χ = χ) (w : W) : χ w = 1 := by
  have hker : commV ρ.range ≤ χ.ker := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨x, ⟨σ, rfl⟩, v, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv]
    have h := DFunLike.congr_fun (hfix σ⁻¹) v
    have e : ((ρ σ⁻¹)⁻¹ : MulAut W) = ρ σ := by rw [map_inv, inv_inv]
    rw [charSmul6_apply, e] at h
    rw [h, mul_inv_cancel]
  have := hker (by rw [hcomm]; trivial : w ∈ commV ρ.range)
  exact this

end Chars

section Orbits

variable {W : Type} [CommGroup W] [Finite W]

private theorem rho_x5_eq_one_of_fix (hW2 : ∀ w : W, w ^ 2 = 1) {ρ : A6 →* MulAut W}
    (h : ∀ χ : W →* ℂˣ, charSmul6 ρ x5 χ = χ) : ρ x5 = 1 := by
  ext w
  by_contra hne
  have hne' : (ρ x5)⁻¹ w * w⁻¹ ≠ 1 := by
    intro h1
    apply hne
    have h2 : (ρ x5)⁻¹ w = w := by
      rwa [mul_inv_eq_one] at h1
    have h3 : (ρ x5) w = w := by
      have := congrArg (ρ x5) h2
      simpa using this.symm
    simpa using h3
  obtain ⟨χ, hχ⟩ := exists_char_ne_one hW2 hne'
  apply hχ
  have := DFunLike.congr_fun (h χ) w
  rw [charSmul6_apply] at this
  rw [map_mul, map_inv, this, mul_inv_cancel]

omit [Finite W] in
private theorem rho_injective6 {ρ : A6 →* MulAut W} (hnt : ¬ ∀ σ, ρ σ = 1) : Function.Injective ρ := by
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ρ.ker with h | h
  · exact h
  · exfalso
    apply hnt
    intro σ
    have : σ ∈ ρ.ker := h ▸ Subgroup.mem_top σ
    exact this

private theorem exists_orbit_six_aux (hW2 : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W = 2 ^ 6)
    {ρ : A6 →* MulAut W} (hcomm : commV ρ.range = ⊤)
    [inst : MulAction A6 (W →* ℂˣ)] (hsmul : ∀ σ χ, σ • χ = charSmul6 ρ σ χ) :
    ∃ Fx : Subgroup (W →* ℂˣ), Nat.card Fx = 4 ∧
      (MulAction.fixedBy (W →* ℂˣ) x5 = (Fx : Set (W →* ℂˣ))) := by
  classical
  have hnt : Nontrivial W := by
    refine Finite.one_lt_card_iff_nontrivial.mp ?_
    rw [hcard]; norm_num
  have hch : Nat.card (W →* ℂˣ) = 2 ^ 6 := by rw [card_chars hW2, hcard]
  set Fx := fixSub6 ρ x5 with hFx
  have hfixedBy : MulAction.fixedBy (W →* ℂˣ) x5 = (Fx : Set (W →* ℂˣ)) := by
    ext χ
    simp only [MulAction.mem_fixedBy, hsmul, SetLike.mem_coe, hFx, mem_fixSub6]
  refine ⟨Fx, ?_, hfixedBy⟩
  have hmod : Nat.card (W →* ℂˣ) ≡ Nat.card Fx [MOD 5] := by
    have h5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have := card_modEq_set6 (Ω := W →* ℂˣ) (p := 5) Set.univ x5_pow (fun s _ => trivial)
    rw [Set.univ_inter, Set.ncard_univ, hfixedBy, ← Nat.card_coe_set_eq] at this
    exact this
  have hdvd : Nat.card Fx ∣ 2 ^ 6 := by
    rw [← hch]
    exact Subgroup.card_subgroup_dvd_card _
  obtain ⟨j, hj6, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  rw [hch, hj] at hmod
  have hj' : j = 2 ∨ j = 6 := by
    interval_cases j <;> simp_all [Nat.ModEq]
  rcases hj' with rfl | rfl
  · simpa using hj
  · exfalso
    have htop : Fx = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [hj, hch]
    have hall : ∀ χ : W →* ℂˣ, charSmul6 ρ x5 χ = χ := fun χ => by
      have : χ ∈ Fx := by rw [htop]; trivial
      exact this
    have hx1 := rho_x5_eq_one_of_fix hW2 hall
    by_cases htriv : ∀ σ, ρ σ = 1
    · have hle : commV ρ.range ≤ ⊥ := by
        refine (Subgroup.closure_le _).mpr ?_
        rintro _ ⟨x, ⟨σ, rfl⟩, v, rfl⟩
        rw [htriv σ]
        simp
      rw [hcomm] at hle
      have : Subsingleton W := ⟨fun a b => by
        have ha : a ∈ (⊥ : Subgroup W) := hle (Subgroup.mem_top a)
        have hb : b ∈ (⊥ : Subgroup W) := hle (Subgroup.mem_top b)
        rw [Subgroup.mem_bot] at ha hb
        rw [ha, hb]⟩
      have := Nat.card_of_subsingleton (1 : W) (α := W)
      rw [hcard] at this
      omega
    · have hinj := rho_injective6 htriv
      apply x5_ne
      apply hinj
      rw [hx1, map_one]

private theorem exists_orbit_six (hW2 : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W = 2 ^ 6)
    {ρ : A6 →* MulAut W} (hcomm : commV ρ.range = ⊤)
    [inst : MulAction A6 (W →* ℂˣ)] (hsmul : ∀ σ χ, σ • χ = charSmul6 ρ σ χ) :
    ∃ χ : W →* ℂˣ, χ ≠ 1 ∧ Nat.card (MulAction.orbit A6 χ) = 6 := by
  classical
  have h5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨Fx, hFx4, hfixedBy⟩ := exists_orbit_six_aux hW2 hcard hcomm hsmul
  have hnt : Nontrivial W := by
    refine Finite.one_lt_card_iff_nontrivial.mp ?_
    rw [hcard]; norm_num
  have hch : Nat.card (W →* ℂˣ) = 2 ^ 6 := by rw [card_chars hW2, hcard]
  have hno : ∀ χ : W →* ℂˣ, (∀ σ : A6, σ • χ = χ) → χ = 1 := by
    intro χ hfix
    refine MonoidHom.ext fun w => ?_
    have := char_eq_one_of_fixed6 hcomm (fun σ => by rw [← hsmul]; exact hfix σ) w
    simpa using this
  have hsmul_one : ∀ (σ : A6) (c : W →* ℂˣ), σ • c = 1 → c = 1 := by
    intro σ c h
    refine MonoidHom.ext fun w => ?_
    have h1 := DFunLike.congr_fun h (ρ σ w)
    rw [hsmul, charSmul6_apply] at h1
    simpa using h1
  set C : Set (W →* ℂˣ) := (Fx : Set (W →* ℂˣ)) \ {1} with hC
  have hC3 : C.ncard = 3 := by
    rw [hC, Set.ncard_sdiff_singleton_of_mem Fx.one_mem, ← Nat.card_coe_set_eq]
    show Nat.card Fx - 1 = 3
    rw [hFx4]
  have hfixC : ∀ c : W →* ℂˣ, c ≠ 1 → (MulAction.orbit A6 c ∩ MulAction.fixedBy (W →* ℂˣ) x5) =
      (MulAction.orbit A6 c ∩ C) := by
    intro c hc
    ext χ
    simp only [Set.mem_inter_iff, hfixedBy, SetLike.mem_coe, hC, Set.mem_sdiff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨ho, hf⟩
      refine ⟨ho, hf, ?_⟩
      rintro rfl
      obtain ⟨σ, hσ⟩ := ho
      exact hc (hsmul_one σ c hσ)
    · rintro ⟨ho, hf, -⟩
      exact ⟨ho, hf⟩
  have key : ∀ c ∈ C, Nat.card (MulAction.orbit A6 c) = 6 ∨
      (Nat.card (MulAction.orbit A6 c) = 36 ∧ (MulAction.orbit A6 c ∩ C).ncard = 1) := by
    intro c hcC
    have hc1 : c ≠ 1 := fun h => hcC.2 h
    have hx5c : x5 • c = c := by
      have : c ∈ MulAction.fixedBy (W →* ℂˣ) x5 := by rw [hfixedBy]; exact hcC.1
      exact this
    have hm360 : Nat.card (MulAction.orbit A6 c) ∣ 360 := card_orbit_dvd6 c
    have hm6 : 6 ≤ Nat.card (MulAction.orbit A6 c) := by
      apply six_le_card_of_nontrivial
      obtain ⟨σ, hσ⟩ : ∃ σ : A6, σ • c ≠ c := by
        by_contra hcon
        push Not at hcon
        exact hc1 (hno c hcon)
      exact ⟨⟨c, MulAction.mem_orbit_self c⟩, σ, fun h => hσ (congrArg Subtype.val h)⟩
    have h1not : (1 : W →* ℂˣ) ∉ MulAction.orbit A6 c := by
      rintro ⟨σ, hσ⟩
      exact hc1 (hsmul_one σ c hσ)
    have hm63 : Nat.card (MulAction.orbit A6 c) ≤ 63 := by
      have h1 := Set.ncard_insert_of_notMem h1not (Set.toFinite _)
      have h2 := Set.ncard_le_ncard (Set.subset_univ (insert (1 : W →* ℂˣ) (MulAction.orbit A6 c)))
        (Set.toFinite _)
      rw [h1, Set.ncard_univ, hch, ← Nat.card_coe_set_eq] at h2
      omega
    have hmodf := card_modEq_set6 (Ω := W →* ℂˣ) (p := 5) (MulAction.orbit A6 c) x5_pow
      (fun s hs => by
        obtain ⟨σ, rfl⟩ := hs
        exact ⟨x5 * σ, mul_smul _ _ _⟩)
    rw [hfixC c hc1, ← Nat.card_coe_set_eq] at hmodf
    have hf1 : 1 ≤ (MulAction.orbit A6 c ∩ C).ncard := by
      have : (MulAction.orbit A6 c ∩ C).Nonempty := ⟨c, MulAction.mem_orbit_self c, hcC⟩
      exact (Set.ncard_pos (Set.toFinite _)).mpr this
    have hf3 : (MulAction.orbit A6 c ∩ C).ncard ≤ 3 := by
      rw [← hC3]
      exact Set.ncard_le_ncard Set.inter_subset_right (Set.toFinite _)
    have hstab : Nat.card (MulAction.stabilizer A6 c) * Nat.card (MulAction.orbit A6 c) = 360 := by
      have := Subgroup.card_mul_index (MulAction.stabilizer A6 c)
      rw [MulAction.index_stabilizer, card_A6, ← Nat.card_coe_set_eq] at this
      exact this
    have hxstab : x5 ∈ MulAction.stabilizer A6 c := hx5c
    generalize hm : Nat.card (MulAction.orbit A6 c) = m at *
    generalize hf : (MulAction.orbit A6 c ∩ C).ncard = f at *
    have hmod5 : m % 5 = f % 5 := hmodf
    have hcases : m = 6 ∨ m = 8 ∨ m = 12 ∨ m = 18 ∨ m = 36 := by
      have h123 : m % 5 = 1 ∨ m % 5 = 2 ∨ m % 5 = 3 := by omega
      interval_cases m <;> omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exfalso
      exact no_sub_20_45 _ hxstab (Or.inr (by omega))
    · exfalso
      exact no_sub_30 _ hxstab (by omega)
    · exfalso
      exact no_sub_20_45 _ hxstab (Or.inl (by omega))
    · exact Or.inr ⟨rfl, by omega⟩
  obtain ⟨c₀, c₁, hc₀, hc₁, hne⟩ :=
    (Set.one_lt_ncard_iff (Set.toFinite C)).mp (by rw [hC3]; norm_num)
  rcases key c₀ hc₀ with h6 | ⟨h36, hf⟩
  · exact ⟨c₀, hc₀.2, h6⟩
  · rcases key c₁ hc₁ with h6' | ⟨h36', -⟩
    · exact ⟨c₁, hc₁.2, h6'⟩
    · exfalso
      have hc₁not : c₁ ∉ MulAction.orbit A6 c₀ := by
        intro hmem
        obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp hf
        have h0 : c₀ ∈ MulAction.orbit A6 c₀ ∩ C := ⟨MulAction.mem_orbit_self c₀, hc₀⟩
        have h1 : c₁ ∈ MulAction.orbit A6 c₀ ∩ C := ⟨hmem, hc₁⟩
        rw [ha] at h0 h1
        exact hne ((Set.mem_singleton_iff.mp h0).trans (Set.mem_singleton_iff.mp h1).symm)
      have hdisj : Disjoint (MulAction.orbit A6 c₀) (MulAction.orbit A6 c₁) := by
        rw [Set.disjoint_left]
        intro x hx0 hx1
        apply hc₁not
        have h0 : MulAction.orbit A6 c₀ = MulAction.orbit A6 x := (MulAction.orbit_eq_iff.mpr hx0).symm
        have h1 : MulAction.orbit A6 c₁ = MulAction.orbit A6 x := (MulAction.orbit_eq_iff.mpr hx1).symm
        rw [h0, ← h1]
        exact MulAction.mem_orbit_self c₁
      have h1not : (1 : W →* ℂˣ) ∉ MulAction.orbit A6 c₀ ∪ MulAction.orbit A6 c₁ := by
        rintro (⟨σ, hσ⟩ | ⟨σ, hσ⟩)
        · exact hc₀.2 (hsmul_one σ c₀ hσ)
        · exact hc₁.2 (hsmul_one σ c₁ hσ)
      have h1 := Set.ncard_insert_of_notMem h1not (Set.toFinite _)
      have h2 := Set.ncard_le_ncard
        (Set.subset_univ (insert (1 : W →* ℂˣ) (MulAction.orbit A6 c₀ ∪ MulAction.orbit A6 c₁)))
        (Set.toFinite _)
      rw [h1, Set.ncard_univ, hch, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _),
        ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, h36, h36'] at h2
      omega

private theorem neg_one_ne_one' : (-1 : ℂˣ) ≠ 1 := by
  intro h
  have := congrArg (fun u : ℂˣ => (u : ℂ)) h
  norm_num at this

private def sumHom6 : PermMod 6 →* Multiplicative (ZMod 2) where
  toFun x := Multiplicative.ofAdd (∑ i, Multiplicative.toAdd x i)
  map_one' := by simp
  map_mul' x y := by simp [Finset.sum_add_distrib]

private theorem no_orbit_six (hW2 : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W = 2 ^ 6)
    {ρ : A6 →* MulAut W} (hcomm : commV ρ.range = ⊤)
    [inst : MulAction A6 (W →* ℂˣ)] (hsmul : ∀ σ χ, σ • χ = charSmul6 ρ σ χ)
    {c : W →* ℂˣ} (hc1 : c ≠ 1) (h6 : Nat.card (MulAction.orbit A6 c) = 6) : False := by
  classical
  have hno : ∀ χ : W →* ℂˣ, (∀ σ : A6, σ • χ = χ) → χ = 1 := by
    intro χ hfix
    refine MonoidHom.ext fun w => ?_
    have := char_eq_one_of_fixed6 hcomm (fun σ => by rw [← hsmul]; exact hfix σ) w
    simpa using this
  let e : MulAction.orbit A6 c ≃ Fin 6 := (Finite.equivFin _).trans (finCongr h6)
  let π : A6 →* Perm (Fin 6) :=
    (Equiv.permCongrHom e).toMonoidHom.comp (MulAction.toPermHom A6 (MulAction.orbit A6 c))
  have hπ : ∀ (g : A6) (i : Fin 6), e.symm (π g i) = g • e.symm i := by
    intro g i
    show e.symm (e ((MulAction.toPerm g) (e.symm i))) = _
    rw [e.symm_apply_apply, MulAction.toPerm_apply]
  let cc : Fin 6 → (W →* ℂˣ) := fun i => ((e.symm i : MulAction.orbit A6 c) : W →* ℂˣ)
  have hcc : ∀ (g : A6) (i : Fin 6), cc (π g i) = g • cc i := fun g i => by
    show ((e.symm (π g i) : MulAction.orbit A6 c) : W →* ℂˣ) = g • ((e.symm i : MulAction.orbit A6 c) : W →* ℂˣ)
    rw [hπ]
    rfl
  have hccinj : Function.Injective cc := fun i j hij =>
    e.symm.injective (Subtype.ext hij)
  have hfaith : Function.Injective π := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with h | h
    · exact h
    · exfalso
      apply hc1
      apply hno
      intro g
      have hg : π g = 1 := by
        have : g ∈ π.ker := h ▸ Subgroup.mem_top g
        exact this
      have h1 := hcc g (e ⟨c, MulAction.mem_orbit_self c⟩)
      rw [hg, Equiv.Perm.coe_one, id_eq] at h1
      have h2 : cc (e ⟨c, MulAction.mem_orbit_self c⟩) = c := by
        show ((e.symm (e ⟨c, MulAction.mem_orbit_self c⟩) : MulAction.orbit A6 c) : W →* ℂˣ) = c
        rw [e.symm_apply_apply]
      rw [h2] at h1
      exact h1.symm
  have halt : ∀ g : A6, π g ∈ alternatingGroup (Fin 6) := by
    have hs : (Equiv.Perm.sign.comp π).ker = ⊤ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Equiv.Perm.sign.comp π).ker with h | h
      · exfalso
        have hinj : Function.Injective (Equiv.Perm.sign.comp π) := (MonoidHom.ker_eq_bot_iff _).mp h
        have := Nat.card_le_card_of_injective _ hinj
        rw [card_A6, Nat.card_eq_fintype_card (α := ℤˣ), Fintype.card_units_int] at this
        omega
      · exact h
    intro g
    have : g ∈ (Equiv.Perm.sign.comp π).ker := hs ▸ Subgroup.mem_top g
    exact Equiv.Perm.mem_alternatingGroup.mpr this
  have hsurj : ∀ σ ∈ alternatingGroup (Fin 6), ∃ g : A6, π g = σ := by
    have hle : π.range ≤ alternatingGroup (Fin 6) := by
      rintro _ ⟨g, rfl⟩
      exact halt g
    have hcardr : Nat.card π.range = 360 := by
      rw [← card_A6]
      exact (Nat.card_congr (MonoidHom.ofInjective hfaith).toEquiv).symm
    have hcardalt : Nat.card (alternatingGroup (Fin 6)) = 360 := card_A6
    have heq : π.range = alternatingGroup (Fin 6) :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hcardalt, hcardr])
    intro σ hσ
    have : σ ∈ π.range := by rw [heq]; exact hσ
    exact this
  have hcc_val : ∀ (i : Fin 6) (w : W), cc i w = 1 ∨ cc i w = -1 := fun i w =>
    char_eq_one_or_neg hW2 (cc i) w
  let Φ₀ : W →* PermMod 6 :=
    { toFun := fun w => Multiplicative.ofAdd (fun i => if cc i w = 1 then (0 : ZMod 2) else 1)
      map_one' := by
        apply Multiplicative.toAdd.injective
        funext i
        simp
      map_mul' := fun a b => by
        apply Multiplicative.toAdd.injective
        funext i
        have h11 : (1 : ZMod 2) + 1 = 0 := by decide
        rcases hcc_val i a with ha | ha <;> rcases hcc_val i b with hb | hb <;>
          simp [ha, hb, h11] }
  have hΦ : ∀ (w : W) (i : Fin 6),
      Multiplicative.toAdd (Φ₀ w) i = if cc i w = 1 then (0 : ZMod 2) else 1 := fun w i => rfl
  have hmem : ∀ (g : A6) (w : W) (i : Fin 6), cc ((π g)⁻¹ i) w = cc i (ρ g w) := by
    intro g w i
    have h1 : (π g)⁻¹ i = π g⁻¹ i := by rw [map_inv]
    rw [h1, hcc, hsmul, charSmul6_apply]
    have : ((ρ g⁻¹)⁻¹ : MulAut W) = ρ g := by rw [map_inv, inv_inv]
    rw [this]
  have hequiv : ∀ (g : A6) (w : W), Φ₀ (ρ g w) = permAct 6 (π g) (Φ₀ w) := by
    intro g w
    apply Multiplicative.toAdd.injective
    funext i
    rw [permAct_apply, hΦ, hΦ, hmem]
  have hcore : ∀ w : W, Φ₀ w ∈ coreMod 6 := by
    let ψ : W →* Multiplicative (ZMod 2) := sumHom6.comp Φ₀
    have hψ : ∀ (g : A6) (w : W), ψ (ρ g w) = ψ w := by
      intro g w
      show Multiplicative.ofAdd (∑ i, Multiplicative.toAdd (Φ₀ (ρ g w)) i) =
        Multiplicative.ofAdd (∑ i, Multiplicative.toAdd (Φ₀ w) i)
      rw [hequiv]
      congr 1
      simp only [permAct_apply]
      exact Equiv.sum_comp (π g)⁻¹ (fun i => Multiplicative.toAdd (Φ₀ w) i)
    have hle : commV ρ.range ≤ ψ.ker := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨x, ⟨g, rfl⟩, v, rfl⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv]
      rw [hψ g v]
      exact mul_inv_cancel (ψ v)
    rw [hcomm] at hle
    intro w
    have hw : w ∈ ψ.ker := hle (Subgroup.mem_top w)
    rw [MonoidHom.mem_ker] at hw
    exact mem_coreMod.mpr (ofAdd_eq_one.mp hw)
  let Φ' : W →* ↥(coreMod 6) := Φ₀.codRestrict _ hcore
  have hsurj' : Function.Surjective Φ' := by
    have hinv : ∀ σ ∈ alternatingGroup (Fin 6), ∀ x ∈ Φ₀.range, permAct 6 σ x ∈ Φ₀.range := by
      rintro σ hσ _ ⟨w, rfl⟩
      obtain ⟨g, hg⟩ := hsurj σ hσ
      exact ⟨ρ g w, by rw [hequiv g w, hg]⟩
    obtain ⟨w, hw⟩ : ∃ w, ¬ (cc 0 w = 1 ↔ cc 1 w = 1) := by
      have hne : cc 0 ≠ cc 1 := fun h => absurd (hccinj h) (by decide)
      by_contra hcon
      push Not at hcon
      apply hne
      refine MonoidHom.ext fun w => ?_
      rcases hcc_val 0 w with h0 | h0 <;> rcases hcc_val 1 w with h1 | h1
      · rw [h0, h1]
      · exact absurd ((hcon w).mp h0) (by rw [h1]; exact neg_one_ne_one')
      · exact absurd ((hcon w).mpr h1) (by rw [h0]; exact neg_one_ne_one')
      · rw [h0, h1]
    have hw1 : Φ₀ w ≠ 1 := fun h => by
      have h0 := congrArg (fun x : PermMod 6 => Multiplicative.toAdd x 0) h
      have h1 := congrArg (fun x : PermMod 6 => Multiplicative.toAdd x 1) h
      simp only [hΦ, toAdd_one, Pi.zero_apply] at h0 h1
      apply hw
      constructor
      · intro _; by_contra hn; simp [hn] at h1
      · intro _; by_contra hn; simp [hn] at h0
    have hwo : Φ₀ w ≠ allOnes 6 := fun h => by
      have h0 := congrArg (fun x : PermMod 6 => Multiplicative.toAdd x 0) h
      have h1 := congrArg (fun x : PermMod 6 => Multiplicative.toAdd x 1) h
      simp only [hΦ, allOnes, toAdd_ofAdd] at h0 h1
      apply hw
      constructor
      · intro hh; simp [hh] at h0
      · intro hh; simp [hh] at h1
    have hle := ModA6.core_le_of_invariant Φ₀.range hinv ⟨w, rfl⟩ (hcore w) hw1 hwo
    intro cm
    obtain ⟨v, hv⟩ := hle cm.2
    exact ⟨v, Subtype.ext hv⟩
  let π' : A6 ≃* ↥(alternatingGroup (Fin 6)) :=
    MulEquiv.ofBijective (π.codRestrict _ halt)
      ⟨fun a b h => hfaith (congrArg Subtype.val h), fun σ => by
        obtain ⟨g, hg⟩ := hsurj σ σ.2
        exact ⟨g, Subtype.ext hg⟩⟩
  have hπ' : ∀ g : A6, ((π' g : ↥(alternatingGroup (Fin 6))) : Perm (Fin 6)) = π g := fun g => rfl
  let ρ' : ↥(alternatingGroup (Fin 6)) →* MulAut W := ρ.comp π'.symm.toMonoidHom
  have hρ'π : ∀ g : A6, ρ' (π' g) = ρ g := fun g => by
    show ρ (π'.symm (π' g)) = ρ g
    rw [π'.symm_apply_apply]
  have hΦ'eq : ∀ (τ : ↥(alternatingGroup (Fin 6))) (w : W),
      Φ' (ρ' τ w) = coreAct 6 (τ : Perm (Fin 6)) (Φ' w) := by
    intro τ w
    obtain ⟨g, rfl⟩ := π'.surjective τ
    apply Subtype.ext
    rw [hρ'π, hπ']
    exact hequiv g w
  have hmk : ∀ (τ : Perm (Fin 6)) (a b : ↥(coreMod 6)),
      (QuotientGroup.mk a : H13.VolI.DnQuot 6) = QuotientGroup.mk b →
        (QuotientGroup.mk (coreAct 6 τ a) : H13.VolI.DnQuot 6) =
          QuotientGroup.mk (coreAct 6 τ b) := by
    intro τ a b h
    rw [H13.VolI.mk_eq_mk_iff_six] at h ⊢
    have hall : permAct 6 τ (allOnes 6) = allOnes 6 := rfl
    rcases h with h | h
    · left
      show permAct 6 τ (b : PermMod 6) = permAct 6 τ (a : PermMod 6)
      rw [h]
    · right
      show permAct 6 τ (b : PermMod 6) = permAct 6 τ (a : PermMod 6) * allOnes 6
      rw [h, map_mul, hall]
  let β : W →* H13.VolI.DnQuot 6 := (QuotientGroup.mk' _).comp Φ'
  have hβ : ∀ w : W, β w = QuotientGroup.mk (Φ' w) := fun w => rfl
  have hZinv : ∀ (g : A6) (z : W), z ∈ β.ker → ρ g z ∈ β.ker := by
    intro g z hz
    rw [MonoidHom.mem_ker, hβ] at hz ⊢
    have h1 := hΦ'eq (π' g) z
    rw [hρ'π, hπ'] at h1
    have := hmk (π g) (Φ' z) 1 (by rw [hz]; rfl)
    rw [h1]
    simpa using this
  have hβsurj : Function.Surjective β := by
    intro q
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨w, hw⟩ := hsurj' m
    exact ⟨w, by rw [hβ, hw]⟩
  have hZcard : Nat.card β.ker = 4 := by
    have h := Subgroup.card_ker_mul_card_of_surjective hβsurj
    rw [H13.VolI.card_dnQuot_six, hcard] at h
    omega
  let actZ : MulAction A6 ↥β.ker :=
    { smul := fun g z => ⟨ρ g z, hZinv g z z.2⟩
      one_smul := fun z => Subtype.ext (by show ρ 1 (z : W) = z; simp)
      mul_smul := fun g h z => Subtype.ext (by show ρ (g * h) (z : W) = ρ g (ρ h (z : W)); simp) }
  have hZtriv : ∀ (g : A6) (z : W), z ∈ β.ker → ρ g z = z := by
    intro g z hz
    have h4 : ¬ 6 ≤ Nat.card ↥β.ker := by rw [hZcard]; norm_num
    have hnone : ¬ ∃ (y : ↥β.ker) (σ : A6), σ • y ≠ y := fun h =>
      h4 (@six_le_card_of_nontrivial ↥β.ker actZ _ h)
    push Not at hnone
    exact congrArg Subtype.val (hnone ⟨z, hz⟩ g)
  let C : H13.VolI.Cover6 W :=
    { H := ρ.range
      Z := β.ker
      ρ := ρ'
      β := β
      hV2 := hW2
      hZ := fun z hz x hx => by
        obtain ⟨g, rfl⟩ := hx
        exact hZtriv g z hz
      hcomm := hcomm
      hρ := fun τ => ⟨π'.symm τ, rfl⟩
      hρs := fun h hh => by
        obtain ⟨g, rfl⟩ := hh
        exact ⟨π' g, hρ'π g⟩
      hβs := hβsurj
      hβk := fun v => (MonoidHom.mem_ker).symm
      hβe := fun τ v m hv => by
        rw [hβ] at hv ⊢
        have := hmk (τ : Perm (Fin 6)) (Φ' v) m hv
        rw [hΦ'eq τ v]
        exact this }
  have hle := C.card_le
  rw [hcard] at hle
  omega

end Orbits

theorem noPerfectSixA6_holds : NoPerfectSixA6 := by
  intro W _ _ hW2 hcard ρ hcomm
  let _inst : MulAction A6 (W →* ℂˣ) := (charAct6 ρ).toMulAction
  have hsmul : ∀ (σ : A6) (χ : W →* ℂˣ), σ • χ = charSmul6 ρ σ χ := fun _ _ => rfl
  obtain ⟨c, hc1, h6⟩ := exists_orbit_six hW2 hcard hcomm hsmul
  exact no_orbit_six hW2 hcard hcomm hsmul hc1 h6

end ModB

theorem input14610PermFixedA7_holds : Input14610PermFixedA7 :=
  input14610PermFixedA7_of_noPerfectSixA6 ModB.noPerfectSixA6_holds

end CFSG.Quasithin
