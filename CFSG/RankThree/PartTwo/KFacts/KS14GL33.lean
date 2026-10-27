module

public import CFSG.RankThree.PartTwo.KFacts.KS18GL33
public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS14

open CFSG

section GL33

variable {V : Type} [Group V]

@[expose] def transvectionGroup (F : Subgroup V) : Subgroup (MulAut V) where
  carrier := {τ | (∀ f ∈ F, τ f = f) ∧ ∀ v, τ v * v⁻¹ ∈ F}
  one_mem' := ⟨fun _ _ => rfl, fun v => by simp⟩
  mul_mem' := by
    rintro τ₁ τ₂ ⟨h₁f, h₁v⟩ ⟨h₂f, h₂v⟩
    refine ⟨fun f hf => ?_, fun v => ?_⟩
    · rw [MulAut.mul_apply, h₂f f hf, h₁f f hf]
    · have : (τ₁ * τ₂) v * v⁻¹ = (τ₁ (τ₂ v) * (τ₂ v)⁻¹) * (τ₂ v * v⁻¹) := by
        rw [MulAut.mul_apply]
        group
      rw [this]
      exact mul_mem (h₁v _) (h₂v v)
  inv_mem' := by
    rintro τ ⟨hf, hv⟩
    refine ⟨fun f hf' => ?_, fun v => ?_⟩
    · calc τ⁻¹ f = τ⁻¹ (τ f) := by rw [hf f hf']
        _ = f := by rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
    · have h := hv (τ⁻¹ v)
      have hτ : τ (τ⁻¹ v) = v := by rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
      rw [hτ] at h
      have h' := inv_mem h
      rwa [mul_inv_rev, inv_inv] at h'

theorem transvectionGroup_isPGroup {F : Subgroup V} (hpow : ∀ f ∈ F, f ^ 3 = 1) :
    IsPGroup 3 (transvectionGroup F) := by
  rintro ⟨τ, hf, hv⟩
  refine ⟨1, Subtype.ext ?_⟩
  rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
  ext v
  obtain ⟨c, hcF, h1⟩ : ∃ c ∈ F, τ v = c * v := ⟨τ v * v⁻¹, hv v, by group⟩
  have h2 : τ (τ v) = c * c * v := by rw [h1, map_mul, hf c hcF, h1, mul_assoc]
  have h3 : τ (τ (τ v)) = c * c * c * v := by
    rw [h2, map_mul, map_mul, hf c hcF, h1]
    group
  have hc3 : c * c * c = 1 := by
    have := hpow c hcF
    rwa [pow_succ, pow_two] at this
  change (τ ^ 3) v = v
  rw [pow_succ, pow_two, MulAut.mul_apply, MulAut.mul_apply, h3, hc3, one_mul]

theorem conj_mem_transvectionGroup {F : Subgroup V} {σ τ : MulAut V}
    (hσ : F.map σ.toMonoidHom = F) (hτ : τ ∈ transvectionGroup F) :
    σ * τ * σ⁻¹ ∈ transvectionGroup F := by
  obtain ⟨hf, hv⟩ := hτ
  have hσF : ∀ f ∈ F, σ f ∈ F := fun f hf => hσ ▸ ⟨f, hf, rfl⟩
  have hσF' : ∀ f ∈ F, σ⁻¹ f ∈ F := by
    intro f hf
    rw [← hσ] at hf
    obtain ⟨g, hg, rfl⟩ := hf
    change σ⁻¹ (σ g) ∈ F
    rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
    exact hg
  have hσσ : ∀ w, σ (σ⁻¹ w) = w := fun w => by
    rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
  refine ⟨fun f hfF => ?_, fun v => ?_⟩
  · rw [MulAut.mul_apply, MulAut.mul_apply, hf _ (hσF' f hfF), hσσ]
  · have : (σ * τ * σ⁻¹) v * v⁻¹ = σ (τ (σ⁻¹ v) * (σ⁻¹ v)⁻¹) := by
      rw [MulAut.mul_apply, MulAut.mul_apply, map_mul, map_inv, hσσ]
    rw [this]
    exact hσF _ (hv _)

theorem le_normalizer_transvectionGroup {F : Subgroup V} {X : Subgroup (MulAut V)}
    (hX : ∀ σ ∈ X, F.map σ.toMonoidHom = F) :
    X ≤ Subgroup.normalizer (transvectionGroup F : Set (MulAut V)) := by
  intro σ hσ
  rw [Subgroup.mem_normalizer_iff]
  intro τ
  refine ⟨conj_mem_transvectionGroup (hX σ hσ), fun h => ?_⟩
  have := conj_mem_transvectionGroup (hX σ⁻¹ (inv_mem hσ)) h
  rwa [inv_inv, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul, mul_assoc, inv_mul_cancel,
    mul_one] at this

theorem exists_transvection [Finite V] (hcomm : ∀ a b : V, a * b = b * a)
    {F : Subgroup V} (hpowF : ∀ f ∈ F, f ^ 3 = 1) (hidx : F.index = 3) (hF1 : F ≠ ⊥) :
    ∃ σ : MulAut V, σ ∈ transvectionGroup F ∧ ∀ v : V, v ∉ F → σ v ≠ v := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hFn : F.Normal := ⟨fun n hn g => by rwa [hcomm g n, mul_inv_cancel_right]⟩
  have hQ : Nat.card (V ⧸ F) = 3 := by rw [← Subgroup.index, hidx]
  have hZ : Nat.card (Multiplicative (ZMod 3)) = 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  let κ : V →* Multiplicative (ZMod 3) :=
    (mulEquivOfPrimeCardEq hQ hZ).toMonoidHom.comp (QuotientGroup.mk' F)
  have hκ : ∀ v, κ v = 1 ↔ v ∈ F := by
    intro v
    simp only [κ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  obtain ⟨⟨f₀, hf₀F⟩, hf₀1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hF1
  have hf₀1 : f₀ ≠ 1 := fun h => hf₀1' (Subtype.ext h)
  have hord : orderOf f₀ = 3 := orderOf_eq_prime (hpowF f₀ hf₀F) hf₀1
  have hpm : ∀ m : ℕ, f₀ ^ (m % 3) = f₀ ^ m := fun m => by
    rw [← hord, pow_mod_orderOf]
  let ex : V → ℕ := fun v => (Multiplicative.toAdd (κ v)).val
  have hex_mul : ∀ a b, f₀ ^ ex (a * b) = f₀ ^ ex a * f₀ ^ ex b := by
    intro a b
    simp only [ex, map_mul, toAdd_mul, ZMod.val_add]
    rw [hpm, pow_add]
  have hex_F : ∀ f ∈ F, ex f = 0 := by
    intro f hf
    simp only [ex, (hκ f).mpr hf, toAdd_one, ZMod.val_zero]
  let σ₀ : V →* V :=
    { toFun := fun v => v * f₀ ^ ex v
      map_one' := by simp [ex]
      map_mul' := fun a b => by
        rw [hex_mul, mul_assoc, mul_assoc, ← mul_assoc (f₀ ^ ex a), hcomm (f₀ ^ ex a) b,
          mul_assoc] }
  have hσ₀ : ∀ v, σ₀ v = v * f₀ ^ ex v := fun _ => rfl
  have hfpow : ∀ v, f₀ ^ ex v ∈ F := fun v => pow_mem hf₀F _
  have hinj : Function.Injective σ₀ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro v hv
    rw [MonoidHom.mem_ker, hσ₀] at hv
    have hvF : v ∈ F := by
      have : v = (f₀ ^ ex v)⁻¹ := eq_inv_of_mul_eq_one_left hv
      rw [this]
      exact inv_mem (hfpow v)
    rw [hex_F v hvF, pow_zero, mul_one] at hv
    rw [hv]
    exact one_mem _
  let σ : MulAut V := MulEquiv.ofBijective σ₀ ⟨hinj, Finite.surjective_of_injective hinj⟩
  have hσ : ∀ v, σ v = v * f₀ ^ ex v := fun _ => rfl
  refine ⟨σ, ⟨fun f hf => ?_, fun v => ?_⟩, fun v hv => ?_⟩
  · rw [hσ, hex_F f hf, pow_zero, mul_one]
  · rw [hσ, hcomm v, mul_assoc, mul_inv_cancel, mul_one]
    exact hfpow v
  · rw [hσ]
    intro h
    have h1 : f₀ ^ ex v = 1 := by
      have := congrArg (v⁻¹ * ·) h
      simpa using this
    have hne : ex v ≠ 0 := by
      intro h0
      apply hv
      rw [← hκ]
      have : Multiplicative.toAdd (κ v) = 0 := (ZMod.val_eq_zero _).mp h0
      exact this
    have hlt : ex v < 3 := ZMod.val_lt _
    have hdvd := orderOf_dvd_of_pow_eq_one h1
    rw [hord] at hdvd
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdvd
    omega

theorem card_SL_two_three : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) = 24 := by
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (n := 2) (by norm_num),
    Nat.card_zmod, show Finset.Icc 2 2 = ({2} : Finset ℕ) by decide, Finset.prod_singleton]
  norm_num

theorem ks18GL33 : KS18GL33 := by
  intro V _ _ hV h27 F hF9 X hXF hext
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcomm : ∀ a b : V, a * b = b * a := fun a b =>
    congrArg Subtype.val (hV.1.is_comm.comm ⟨a, Subgroup.mem_top a⟩ ⟨b, Subgroup.mem_top b⟩)
  have hpow : ∀ v : V, v ^ 3 = 1 := fun v => hV.2 v (Subgroup.mem_top v)
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 3) hcomm hpow
    (n := 3) (by rw [h27]; norm_num)
  have hAut : Nat.card (MulAut V) = 11232 := by
    rw [CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL e, CFSG.SectionRank.Ccomm.card_GL_zmod,
      Fin.prod_univ_three]
    norm_num
  have hX : Nat.card X = 216 := by
    obtain ⟨K, hK, ⟨eK⟩, ⟨eQ⟩⟩ := hext
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup K, Nat.card_congr eQ.toEquiv,
      Nat.card_congr eK.toEquiv, card_SL_two_three, Nat.card_prod, Nat.card_eq_fintype_card,
      Fintype.card_multiplicative, ZMod.card]
  obtain ⟨S⟩ : Nonempty (Sylow 3 X) := inferInstance
  have hS27 : Nat.card (S : Subgroup X) = 27 := by
    rw [Sylow.card_eq_multiplicity, hX]
    have : Nat.factorization 216 3 = 3 := by
      rw [show (216 : ℕ) = 3 ^ 3 * 8 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
        Nat.Prime.factorization_pow Nat.prime_three, Finsupp.add_apply, Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]
    rw [this]
    norm_num
  set S' := (S : Subgroup X).map X.subtype with hS'def
  have hS'27 : Nat.card S' = 27 := by
    rw [hS'def, Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hS27]
  have hS'3 : IsPGroup 3 S' := (S.isPGroup').map _
  have hS'X : S' ≤ X := Subgroup.map_subtype_le _
  set T := transvectionGroup F with hTdef
  have hT3 : IsPGroup 3 T := transvectionGroup_isPGroup fun f _ => hpow f
  have hnorm : S' ≤ Subgroup.normalizer (T : Set (MulAut V)) :=
    hS'X.trans (le_normalizer_transvectionGroup hXF)
  have hsup : IsPGroup 3 ↥(T ⊔ S') := hT3.to_sup_of_normal_left' hS'3 hnorm
  obtain ⟨k, hk⟩ := hsup.exists_card_eq
  have hdvd : 3 ^ k ∣ 11232 := hk ▸ hAut ▸ Subgroup.card_subgroup_dvd_card _
  have hk3 : k ≤ 3 := by
    by_contra h
    have : 3 ^ 4 ∣ 11232 := (pow_dvd_pow 3 (by omega)).trans hdvd
    norm_num at this
  have hle : Nat.card ↥(T ⊔ S') ≤ Nat.card S' := by
    rw [hk, hS'27]
    calc 3 ^ k ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) hk3
      _ = 27 := by norm_num
  have heq : S' = T ⊔ S' := Subgroup.eq_of_le_of_card_ge le_sup_right hle
  have hTX : T ≤ X := le_sup_left.trans (heq ▸ hS'X)
  have hidx : F.index = 3 := by
    have h := F.card_mul_index
    rw [hF9, h27] at h
    omega
  have hF1 : F ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hF9
    norm_num at hF9
  obtain ⟨σ, hσT, hσ⟩ := exists_transvection hcomm (fun f _ => hpow f) hidx hF1
  exact ⟨σ, hTX hσT, hσT.1, hσT.2, hσ⟩

end GL33

end CFSG.RankThree.PartTwo.KFacts.KS14
