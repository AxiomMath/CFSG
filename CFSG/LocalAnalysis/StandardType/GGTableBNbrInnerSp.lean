module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerElt
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInner
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplectic

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB TableBSymp

namespace NbrSp

section Coord

variable {p m : ℕ}

theorem mul_inv_update_eq (f : Fin m → Multiplicative (ZMod p)) (i : Fin m) :
    f * (Function.update f i (f i)⁻¹)⁻¹ = Pi.mulSingle i (f i ^ 2) := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp [sq]
  · simp [Function.update_of_ne hj, Pi.mulSingle_eq_of_ne hj]

theorem exists_pow_eq_of_sq_ne_one (hp : p.Prime) (hp2 : p ≠ 2) {a : Multiplicative (ZMod p)}
    (ha : a ≠ 1) (b : Multiplicative (ZMod p)) : ∃ n : ℕ, (a ^ 2) ^ n = b := by
  have := Fact.mk hp
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
  have ha' : Multiplicative.toAdd a ≠ 0 := by
    intro h
    apply ha
    rw [← ofAdd_toAdd a, h, ofAdd_zero]
  set c : ZMod p := Multiplicative.toAdd b / (2 * Multiplicative.toAdd a) with hc
  refine ⟨c.val, ?_⟩
  rw [← ofAdd_toAdd a, ← ofAdd_nsmul, ← ofAdd_nsmul, ← ofAdd_toAdd b]
  congr 1
  rw [nsmul_eq_mul, nsmul_eq_mul, ZMod.natCast_zmod_val, hc]
  push_cast
  exact div_mul_cancel₀ _ (mul_ne_zero h2 ha')

theorem eq_bot_or_eq_top_of_signed (hp : p.Prime) (hp2 : p ≠ 2)
    (F : Subgroup (Fin m → Multiplicative (ZMod p)))
    (hinv : ∀ i, ∀ f ∈ F, Function.update f i (f i)⁻¹ ∈ F)
    (hperm : ∀ σ : Equiv.Perm (Fin m), ∀ f ∈ F, f ∘ ⇑σ⁻¹ ∈ F) : F = ⊥ ∨ F = ⊤ := by
  classical
  by_cases hF : F = ⊥
  · exact Or.inl hF
  right
  obtain ⟨⟨f, hfF⟩, hf1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hF
  have hf1' : f ≠ 1 := fun h => hf1 (Subtype.ext h)
  obtain ⟨i, hi⟩ : ∃ i, f i ≠ 1 := by
    by_contra h
    push Not at h
    exact hf1' (funext h)
  have hδi : Pi.mulSingle i (f i ^ 2) ∈ F := by
    rw [← mul_inv_update_eq]
    exact F.mul_mem hfF (F.inv_mem (hinv i f hfF))
  have hδ : ∀ j (b : Multiplicative (ZMod p)), Pi.mulSingle j b ∈ F := by
    intro j b
    obtain ⟨n, hn⟩ := exists_pow_eq_of_sq_ne_one hp hp2 hi b
    have hb : Pi.mulSingle i b ∈ F := by
      rw [← hn, Pi.mulSingle_pow]
      exact F.pow_mem hδi n
    have h := hperm (Equiv.swap i j) _ hb
    have e : (Pi.mulSingle i b : Fin m → Multiplicative (ZMod p)) ∘ ⇑(Equiv.swap i j)⁻¹ =
        Pi.mulSingle j b := by
      funext k
      simp only [Function.comp_apply, Equiv.swap_inv]
      by_cases hk : k = j
      · subst hk
        simp
      · rw [Pi.mulSingle_eq_of_ne hk]
        by_cases hki : k = i
        · subst hki
          rw [Equiv.swap_apply_left, Pi.mulSingle_eq_of_ne (Ne.symm hk)]
        · rw [Equiv.swap_apply_of_ne_of_ne hki hk, Pi.mulSingle_eq_of_ne hki]
    rwa [e] at h
  rw [eq_top_iff]
  intro g _
  rw [← Finset.univ_prod_mulSingle g]
  exact Subgroup.prod_mem _ fun j _ => hδ j (g j)

end Coord

section Sp

variable {K : Type} [Field K] {m p : ℕ} {ζ : Kˣ}

@[expose] def pairPerm (σ : Equiv.Perm (Fin m)) : Equiv.Perm (Fin m ⊕ Fin m) :=
  Equiv.sumCongr σ σ

theorem largeEvenSpForm_pairPerm (σ : Equiv.Perm (Fin m)) (x y : Fin m ⊕ Fin m) :
    LargeEvenSpForm K m (pairPerm σ x) (pairPerm σ y) = LargeEvenSpForm K m x y := by
  rw [largeEvenSpForm_apply, largeEvenSpForm_apply]
  rcases x with a | a <;> rcases y with b | b <;> simp [pairPerm]

@[expose] noncomputable def spPermSp (σ : Equiv.Perm (Fin m)) : LargeEvenSpGroup K m :=
  ⟨TauCeti.permutationGL (pairPerm σ), permutationGL_mem_sp _ (largeEvenSpForm_pairPerm σ)⟩

theorem permutationGL_conj_diagGL {ι : Type*} [Fintype ι] [DecidableEq ι] (π : Equiv.Perm ι)
    (d : ι → Kˣ) :
    TauCeti.permutationGL (k := K) π * TauCeti.diagGL d * (TauCeti.permutationGL (k := K) π)⁻¹ =
      TauCeti.diagGL (d ∘ ⇑π⁻¹) := by
  rw [TauCeti.mul_diagGL_of_coe_eq_permMatrix (TauCeti.permutationGL (k := K) π) π⁻¹
    (TauCeti.permutationGL_coe _), mul_inv_cancel_right]

theorem pairedUnits_comp_pairPerm (u : Fin m → Kˣ) (σ : Equiv.Perm (Fin m)) :
    pairedUnits u ∘ ⇑(pairPerm σ)⁻¹ = pairedUnits (u ∘ ⇑σ⁻¹) := by
  funext x
  rcases x with a | a <;> rfl

theorem spPermSp_conj_spTorusSp (hζ : ζ ^ p = 1) (σ : Equiv.Perm (Fin m))
    (f : Fin m → Multiplicative (ZMod p)) :
    spPermSp σ * spTorusSp hζ f * (spPermSp σ)⁻¹ = spTorusSp hζ (f ∘ ⇑σ⁻¹) := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, spTorusSp_coe, spTorusSp_coe,
    spTorusGL_apply, spTorusGL_apply]
  change TauCeti.permutationGL (pairPerm σ) * _ * (TauCeti.permutationGL (pairPerm σ))⁻¹ = _
  rw [permutationGL_conj_diagGL, pairedUnits_comp_pairPerm]
  rfl

theorem spSwapSp_conj_spTorusSp [CharP K 2] (hζ : ζ ^ p = 1) (i : Fin m)
    (f : Fin m → Multiplicative (ZMod p)) :
    spSwapSp i * spTorusSp hζ f * (spSwapSp i)⁻¹ =
      spTorusSp hζ (Function.update f i (f i)⁻¹) := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, spSwapSp_coe, spTorusSp_coe,
    spTorusSp_coe, spTorusGL_apply, spTorusGL_apply, permutationGL_pairSwap_conj,
    pairedUnits_comp_pairSwap]
  congr 2
  funext j
  by_cases hj : j = i
  · subst hj
    simp
  · simp [Function.update_of_ne hj]

theorem update_mulSingle_inv (i j : Fin m) (a : Multiplicative (ZMod p)) :
    Function.update (Pi.mulSingle j a : Fin m → Multiplicative (ZMod p)) i
        ((Pi.mulSingle j a : Fin m → Multiplicative (ZMod p)) i)⁻¹ =
      if j = i then (Pi.mulSingle j a : Fin m → Multiplicative (ZMod p))⁻¹
      else (Pi.mulSingle j a : Fin m → Multiplicative (ZMod p)) := by
  funext k
  by_cases hji : j = i
  · subst hji
    by_cases hk : k = j
    · subst hk
      simp
    · simp [Function.update_of_ne hk, Pi.mulSingle_eq_of_ne hk]
  · simp only [hji, ↓reduceIte]
    rw [Pi.mulSingle_eq_of_ne (Ne.symm hji), inv_one]
    by_cases hk : k = i
    · subst hk
      rw [Function.update_self, Pi.mulSingle_eq_of_ne (Ne.symm hji)]
    · rw [Function.update_of_ne hk]

end Sp

section Elt

variable {K : Type} [Field K] {m p : ℕ}

theorem ggTorusIrredElt_sp [Finite K] [CharP K 2] (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1) : GGTorusIrredElt p m (LargeEvenSpGroup K m) := by
  classical
  intro E hE hr _
  obtain ⟨ζ, hζo⟩ := @exists_orderOf_eq_of_dvd K _ _ p ⟨hp⟩ hpq
  have hζ : ζ ^ p = 1 := by
    rw [← hζo]
    exact pow_orderOf_eq_one ζ
  set E₁ : Subgroup (GL (Fin m ⊕ Fin m) K) := E.map (LargeEvenSpGroup K m).subtype with hE₁
  have hE₁e : IsElemAbelian p E₁ := isElemAbelian_map hE _
  have hcard₁ : Nat.card E₁ = Nat.card E := (Nat.card_congr
    (E.equivMapOfInjective _ (LargeEvenSpGroup K m).subtype_injective).toEquiv).symm
  obtain ⟨P, hP, hconj⟩ := exists_conj_eq_range_spTorusGL (hpF := ⟨hp⟩) hp2
    (natCast_ne_zero_of_charTwo hp hp2) hζo hζ (Subgroup.map_subtype_le _) hE₁e (hcard₁ ▸ hr)
  set Pg : LargeEvenSpGroup K m := ⟨P, hP⟩ with hPg
  have hcoe : ∀ x : LargeEvenSpGroup K m,
      ((Pg⁻¹ * x * Pg : LargeEvenSpGroup K m) : GL (Fin m ⊕ Fin m) K) = P⁻¹ * x * P :=
    fun x => rfl
  have hmemE : ∀ x : LargeEvenSpGroup K m, x ∈ E ↔ ∃ f, spTorusSp hζ f = Pg⁻¹ * x * Pg := by
    intro x
    constructor
    · intro hx
      have h1 : P⁻¹ * (x : GL (Fin m ⊕ Fin m) K) * P ∈ E₁.map (MulAut.conj P⁻¹).toMonoidHom :=
        ⟨x, ⟨x, hx, rfl⟩, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩
      rw [hconj] at h1
      obtain ⟨f, hf⟩ := h1
      exact ⟨f, Subtype.ext (by rw [spTorusSp_coe, hf, hcoe])⟩
    · rintro ⟨f, hf⟩
      have h1 : spTorusGL hζ f ∈ E₁.map (MulAut.conj P⁻¹).toMonoidHom := by
        rw [hconj]
        exact ⟨f, rfl⟩
      obtain ⟨_, ⟨y, hy, rfl⟩, hyx⟩ := h1
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, Subgroup.coe_subtype]
        at hyx
      have h2 : P⁻¹ * (y : GL (Fin m ⊕ Fin m) K) * P = P⁻¹ * x * P := by
        rw [hyx, ← hcoe, ← hf, spTorusSp_coe]
      have h3 : y = x := Subtype.ext (by simpa using h2)
      exact h3 ▸ hy
  set τ : (Fin m → Multiplicative (ZMod p)) →* LargeEvenSpGroup K m :=
    (MulAut.conj Pg).toMonoidHom.comp (spTorusSp hζ) with hτ
  have hτapp : ∀ f, τ f = Pg * spTorusSp hζ f * Pg⁻¹ := fun f => rfl
  have hτE : τ.range = E := by
    ext x
    rw [MonoidHom.mem_range, hmemE]
    constructor
    · rintro ⟨f, rfl⟩
      exact ⟨f, by rw [hτapp]; group⟩
    · rintro ⟨f, hf⟩
      exact ⟨f, by rw [hτapp, hf]; group⟩
  have hτmem : ∀ x ∈ E, ∃ f, τ f = x := fun x hx => by
    rw [← hτE] at hx
    exact hx
  have hconjW : ∀ (w : LargeEvenSpGroup K m) (f g : Fin m → Multiplicative (ZMod p)),
      w * spTorusSp hζ f * w⁻¹ = spTorusSp hζ g →
      (Pg * w * Pg⁻¹) * τ f * (Pg * w * Pg⁻¹)⁻¹ = τ g := by
    intro w f g h
    rw [hτapp, hτapp, ← h]
    group
  have hswap : ∀ i (f : Fin m → Multiplicative (ZMod p)),
      (Pg * spSwapSp i * Pg⁻¹) * τ f * (Pg * spSwapSp i * Pg⁻¹)⁻¹ =
        τ (Function.update f i (f i)⁻¹) :=
    fun i f => hconjW _ f _ (spSwapSp_conj_spTorusSp hζ i f)
  have hperm : ∀ (σ : Equiv.Perm (Fin m)) (f : Fin m → Multiplicative (ZMod p)),
      (Pg * spPermSp σ * Pg⁻¹) * τ f * (Pg * spPermSp σ * Pg⁻¹)⁻¹ = τ (f ∘ ⇑σ⁻¹) :=
    fun σ f => hconjW _ f _ (spPermSp_conj_spTorusSp hζ σ f)
  refine ⟨m, τ, (fun w => Pg * w * Pg⁻¹) '' (Set.range spSwapSp ∪ Set.range spPermSp), hτE,
    fun i j => ⟨Pg * spSwapSp i * Pg⁻¹, ?_, fun hji => ?_⟩, ?_, ?_⟩
  · rw [torusBasis, hswap, update_mulSingle_inv]
    simp
  · rw [torusBasis, hswap, update_mulSingle_inv]
    simp [hji]
  · rintro _ ⟨w₀, hw₀, rfl⟩ e he
    obtain ⟨f, rfl⟩ := hτmem e he
    rw [← hτE]
    rcases hw₀ with ⟨i, rfl⟩ | ⟨σ, rfl⟩
    · exact ⟨_, (hswap i f).symm⟩
    · exact ⟨_, (hperm σ f).symm⟩
  · intro E' hE'E hE'inv
    have hinvF : ∀ i, ∀ f ∈ E'.comap τ, Function.update f i (f i)⁻¹ ∈ E'.comap τ := by
      intro i f hf
      rw [Subgroup.mem_comap, ← hswap]
      exact hE'inv _ ⟨spSwapSp i, Or.inl ⟨i, rfl⟩, rfl⟩ _ hf
    have hpermF : ∀ σ : Equiv.Perm (Fin m), ∀ f ∈ E'.comap τ, f ∘ ⇑σ⁻¹ ∈ E'.comap τ := by
      intro σ f hf
      rw [Subgroup.mem_comap, ← hperm]
      exact hE'inv _ ⟨spPermSp σ, Or.inr ⟨σ, rfl⟩, rfl⟩ _ hf
    rcases eq_bot_or_eq_top_of_signed hp hp2 _ hinvF hpermF with hbot | htop
    · left
      rw [eq_bot_iff]
      intro e he
      obtain ⟨f, rfl⟩ := hτmem e (hE'E he)
      have hf : f ∈ E'.comap τ := he
      rw [hbot, Subgroup.mem_bot] at hf
      rw [hf, map_one]
      exact Subgroup.one_mem _
    · right
      refine le_antisymm hE'E fun e he => ?_
      obtain ⟨f, rfl⟩ := hτmem e he
      have hf : f ∈ E'.comap τ := htop ▸ Subgroup.mem_top f
      exact hf

end Elt

section Label

variable {K : Type} [Field K]

theorem ggTorusNbr_symplectic [Finite K] [CharP K 2] {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1) (hm : 1 ≤ m) :
    GGTorusNbr p m (LargeEvenProj (LargeEvenSpGroup K m))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m)) (LargeEvenGSpSet K m)) := by
  have : NeZero m := ⟨by omega⟩
  exact ggTorusNbr_of_irredElt hp hp2 sp_I_subset_inn center_spProj_eq_bot
    (ggTorusIrredElt_of_mulEquiv spProjEquivSp (ggTorusIrredElt_sp hp hp2 hpq))

theorem recipeSymplectic_torusNbr {l n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpn : p ∣ 2 ^ n - 1)
    (hl : 1 ≤ l) {Q : LargeEvenRawCont} (h : LargeEvenRecipeSymplectic l (2 ^ n) false Q) :
    LargeEvenRecipeSymplectic l (2 ^ n) false fun R _ I F =>
      Q R I F ∧ ∃ r, GGTorusLift p r R ∧ GGTorusNbr p r R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have := charP_two_of_card hK
  have hpq : p ∣ Nat.card K - 1 := by rw [hK]; exact hpn
  exact ⟨K, inferInstance, inferInstance, hK, hQ, l, ggTorusLift_symplectic hp hp2 hpq hl,
    ggTorusNbr_symplectic hp hp2 hpq hl⟩

theorem largeEvenLabelAll_torusNbr_symplectic {lab : LargeEvenLabel}
    (htag : lab.tag = .B ∨ lab.tag = .C) (hlab : LargeEvenInLambda2 lab) {p : ℕ} (hp : p.Prime)
    (hpn : p ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusNbr p r R I := by
  obtain ⟨t, l, n⟩ := lab
  have hn : 1 ≤ n := hlab.1
  have hp2 := ne_two_of_dvd_two_pow_sub_one hn hpn
  intro Q hQ
  rcases htag with h | h <;> dsimp only at h <;> subst h <;>
    exact recipeSymplectic_torusNbr hp hp2 hpn (le_trans (by norm_num) hlab.2.1) hQ

end Label

end NbrSp

open NbrSp

theorem ggTableBNbrInnerInputOn_symplectic :
    GGTableBNbrInnerInputOn fun p lab => (lab.tag = .B ∨ lab.tag = .C) ∧ p ∣ 2 ^ lab.n - 1 :=
  ggTableBNbrInnerInputOn_of_labels fun _ _ hp hlab h =>
    largeEvenLabelAll_torusNbr_symplectic h.1 hlab hp h.2

theorem ggTableBNbrInnerInput_of_rest_symplectic
    (h : GGTableBNbrInnerInputOn fun p lab => GGCorFourTwoRestLabel p lab ∧
      ¬ ((lab.tag = .B ∨ lab.tag = .C) ∧ p ∣ 2 ^ lab.n - 1)) :
    GGTableBNbrInnerInput :=
  ((ggTableBNbrInnerInputOn_typeA.or ggTableBNbrInnerInputOn_symplectic).or h).of_cover
    fun p lab _ _ => by
      by_cases h1 : GGTypeALabel p lab
      · exact Or.inl (Or.inl h1)
      · by_cases h2 : (lab.tag = .B ∨ lab.tag = .C) ∧ p ∣ 2 ^ lab.n - 1
        · exact Or.inl (Or.inr h2)
        · exact Or.inr ⟨h1, h2⟩

end CFSG.StandardType

end
