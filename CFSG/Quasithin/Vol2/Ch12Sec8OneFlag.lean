module

public import CFSG.Quasithin.Vol2.Ch12Sec8OneExist
public import CFSG.Quasithin.Vol2.Ch12Sec8OneFlagLin
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint Subgroup
open scoped IsMulCommutative

theorem relIndex_map_dvd {G H : Type*} [Group G] [Group H] (f : G →* H) {A B : Subgroup G}
    (hAB : A ≤ B) : (A.map f).relIndex (B.map f) ∣ A.relIndex B := by
  have key : (A.subgroupOf B).map (f.subgroupMap B) = (A.map f).subgroupOf (B.map f) := by
    ext ⟨y, hy⟩
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨⟨b, hb⟩, hbA, hbe⟩
      refine ⟨b, hbA, ?_⟩
      have := congrArg Subtype.val hbe
      exact this
    · rintro ⟨a, haA, rfl⟩
      exact ⟨⟨a, hAB haA⟩, haA, rfl⟩
  rw [Subgroup.relIndex, Subgroup.relIndex, ← key]
  exact Subgroup.index_map_dvd _ (f.subgroupMap_surjective B)

section Lin

variable {V : Type*} [CommGroup V] [Module (ZMod 2) (Additive V)]

@[expose] noncomputable def linOfMulAut (f : MulAut V) : Additive V ≃ₗ[ZMod 2] Additive V :=
  { AddMonoidHom.toZModLinearMap 2 (MonoidHom.toAdditive f.toMonoidHom) with
    invFun := fun x => Additive.ofMul (f.symm x.toMul)
    left_inv := fun x => by simp [MonoidHom.toAdditive]
    right_inv := fun x => by simp [MonoidHom.toAdditive] }

theorem linOfMulAut_apply (f : MulAut V) (x : Additive V) :
    linOfMulAut f x = Additive.ofMul (f x.toMul) := rfl

@[expose] noncomputable def linHom : MulAut V →* (Additive V ≃ₗ[ZMod 2] Additive V) where
  toFun := linOfMulAut
  map_one' := by
    ext x
    rfl
  map_mul' f g := by
    ext x
    rfl

theorem linHom_injective : Function.Injective (linHom (V := V)) := by
  intro f g h
  ext x
  have := LinearEquiv.congr_fun h (Additive.ofMul x)
  exact congrArg Additive.toMul this

end Lin

section Elem

variable {G : Type} [Group G]

theorem autOn_mono {X Y V : Subgroup G} (h : X ≤ Y) : autOn X V ≤ autOn Y V :=
  CFSG.Quasithin.AutOn.autOn_mono h

theorem isPGroup_autOn {T V : Subgroup G} (hT : IsPGroup 2 T) : IsPGroup 2 (autOn T V) :=
  CFSG.Quasithin.AutOn.isPGroup_autOn hT

variable {V : Subgroup G} [IsMulCommutative ↥V]

@[expose, instance_reducible] noncomputable def zmodModuleOf (h2 : ∀ v ∈ V, v ^ 2 = 1) :
    Module (ZMod 2) (Additive ↥V) :=
  AddCommGroup.zmodModule fun x => by
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    exact Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact h2 _ (x.toMul).2)

@[expose] def subOf [Module (ZMod 2) (Additive ↥V)] (W : Subgroup G) :
    Submodule (ZMod 2) (Additive ↥V) :=
  AddSubgroup.toZModSubmodule 2 (Subgroup.toAddSubgroup (W.subgroupOf V))

theorem mem_subOf [Module (ZMod 2) (Additive ↥V)] {W : Subgroup G} {x : Additive ↥V} :
    x ∈ subOf (V := V) W ↔ ((x.toMul : ↥V) : G) ∈ W := by
  simp [subOf, Subgroup.mem_subgroupOf]

theorem le_of_subOf_le [Module (ZMod 2) (Additive ↥V)] {W W' : Subgroup G} (hWV : W ≤ V)
    (h : subOf (V := V) W ≤ subOf (V := V) W') : W ≤ W' := by
  intro x hx
  have h1 : Additive.ofMul (⟨x, hWV hx⟩ : ↥V) ∈ subOf (V := V) W := mem_subOf.2 hx
  exact mem_subOf.1 (h h1)

theorem tinv_comparable [Finite G] {T : Subgroup G} {n : ℕ} (h2 : ∀ v ∈ V, v ^ 2 = 1)
    (hVn : Nat.card V = 2 ^ n) (hT : IsPGroup 2 T) (hS : Nat.card (autOn T V) = 2 ^ Flag.tri n)
    {W W' : Subgroup G} (hWV : W ≤ V) (hW'V : W' ≤ V)
    (hTW : T ≤ Subgroup.normalizer (W : Set G)) (hTW' : T ≤ Subgroup.normalizer (W' : Set G)) :
    W ≤ W' ∨ W' ≤ W := by
  let _ := zmodModuleOf h2
  set S : Subgroup (Additive ↥V ≃ₗ[ZMod 2] Additive ↥V) :=
    (autOn T V).map (linHom (V := ↥V)) with hSdef
  have hSp : IsPGroup 2 S := by
    rw [hSdef]
    exact (isPGroup_autOn hT).map (linHom (V := ↥V))
  have hScard : Nat.card S = 2 ^ Flag.tri n := by
    rw [hSdef, Subgroup.card_map_of_injective linHom_injective, hS]
  have hrank : Module.finrank (ZMod 2) (Additive ↥V) = n := by
    have : Module.Finite (ZMod 2) (Additive ↥V) := Module.Finite.of_finite
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive ↥V)
    rw [Nat.card_zmod] at h1
    have h3 : Nat.card (Additive ↥V) = 2 ^ n := hVn
    exact Nat.pow_right_injective le_rfl (h1.symm.trans h3)
  have hinv : ∀ X : Subgroup G, T ≤ Subgroup.normalizer (X : Set G) →
      ∀ s ∈ S, ∀ x ∈ subOf (V := V) X, (s : Additive ↥V ≃ₗ[ZMod 2] Additive ↥V) x ∈
        subOf (V := V) X := by
    intro X hTX s hs x hx
    obtain ⟨a, ha, rfl⟩ := hs
    obtain ⟨⟨t, htN⟩, ht, rfl⟩ := ha
    rw [mem_subOf] at hx ⊢
    have htX := hTX (Subgroup.mem_subgroupOf.1 ht)
    exact (Subgroup.mem_normalizer_iff.1 htX _).1 hx
  rcases (Flag.flag_main n hrank S hSp).2 hScard (subOf W) (subOf W') (hinv W hTW)
      (hinv W' hTW') with h | h
  · exact Or.inl (le_of_subOf_le hWV h)
  · exact Or.inr (le_of_subOf_le hW'V h)

end Elem

theorem card_eq_of_binaryNaturalSL {V : Type*} [CommGroup V] {H : Subgroup (MulAut V)} {n : ℕ}
    (h : BinaryNaturalSL H ⊤ ⊥ n 1) (hn : 1 ≤ n) :
    Nat.card H = 2 ^ (n * (n - 1) / 2) * ∏ j ∈ Finset.Icc 2 n, (2 ^ j - 1) := by
  obtain ⟨K, _, _, hK, π, hπs, -, -, -, -, -, -, β, hβs, -, hint⟩ := h
  have hK2 : Nat.card K = 2 := by simpa using hK
  have hπi : Function.Injective π := by
    rw [injective_iff_map_eq_one]
    intro γ hγ
    have hfix : ∀ m : (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL n K)).Amb,
        (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL n K)).act γ m = m := by
      intro m
      obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk ⟨m, Subgroup.mem_top m⟩)
      have h1 := hint γ u ⟨m, Subgroup.mem_top m⟩ (Subgroup.mem_top _) (Subgroup.mem_top _) hu
      have h2 : (⟨((π γ : ↥H) : MulAut V) (u : V), Subgroup.mem_top _⟩ :
          ↥(⊤ : Subgroup V)) = u := by
        apply Subtype.ext
        rw [hγ]
        rfl
      rw [h2, hu] at h1
      have h3 := Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 h1)
      have h4 : m⁻¹ * (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL n K)).act γ m = 1 := h3
      rw [inv_mul_eq_one] at h4
      exact h4.symm
    have hact : ∀ x : Fin n → K,
        (((show ↥(CFSG.Assembly.LowTwoRank.StatedSL n K) from γ) : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K).mulVec x = x := by
      intro x
      have h := hfix (show (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL n K)).Amb from
        Multiplicative.ofAdd x)
      exact Multiplicative.ofAdd.injective h
    have hγ1 : (show ↥(CFSG.Assembly.LowTwoRank.StatedSL n K) from γ) = 1 := by
      apply Subtype.ext
      apply Units.ext
      apply Matrix.ext_of_mulVec_single
      intro i
      rw [hact, Subgroup.coe_one, Units.val_one, Matrix.one_mulVec]
    exact hγ1
  have hcard : Nat.card H = Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL n K) :=
    (Nat.card_congr (Equiv.ofBijective π ⟨hπi, hπs⟩)).symm
  rw [hcard,
    ← Nat.card_congr (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n K).toEquiv,
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq hn, hK2]

section Hyp

variable {G : Type} [Group G]

theorem card_autOn_le [Finite G] {T V : Subgroup G} [IsMulCommutative ↥V] {n : ℕ}
    (h2 : ∀ v ∈ V, v ^ 2 = 1) (hVn : Nat.card V = 2 ^ n) (hT : IsPGroup 2 T) :
    Nat.card (autOn T V) ≤ 2 ^ Flag.tri n := by
  let _ := zmodModuleOf h2
  have hrank : Module.finrank (ZMod 2) (Additive ↥V) = n := by
    have : Module.Finite (ZMod 2) (Additive ↥V) := Module.Finite.of_finite
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive ↥V)
    rw [Nat.card_zmod] at h1
    have h3 : Nat.card (Additive ↥V) = 2 ^ n := hVn
    exact Nat.pow_right_injective le_rfl (h1.symm.trans h3)
  have h := (Flag.flag_main n hrank ((autOn T V).map (linHom (V := ↥V)))
    ((isPGroup_autOn hT).map (linHom (V := ↥V)))).1
  rwa [Subgroup.card_map_of_injective linHom_injective] at h

theorem tri_eq (n : ℕ) : Flag.tri n = n * (n - 1) / 2 := by
  have h := Finset.sum_range_id_mul_two n
  rw [Flag.tri]
  omega

theorem card_autOn_sylow (h1222 : Stmt12_2_2) [Finite G] {T L V : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) : Nat.card (autOn T V) = 2 ^ Flag.tri n := by
  obtain ⟨hcard, hsq, -⟩ := h.card_sq
  obtain ⟨hc, hnat⟩ := h.natural
  obtain ⟨-, hTV⟩ := h.hyp.le_and_normalizes h1222
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := h.hyp.irrPlus.2.2.1
  have hn : 1 ≤ n := by rcases h.n_mem with rfl | rfl | rfl <;> omega
  have hle := card_autOn_le hsq hcard h.hyp.sylow.1 (T := T)
  have hL : 2 ^ Flag.tri n ∣ Nat.card (autOn L V) := by
    rw [card_eq_of_binaryNaturalSL hnat hn, tri_eq]
    exact dvd_mul_right _ _
  have hLT : 2 ^ Flag.tri n ∣ Nat.card (autOn (L ⊔ T) V) :=
    hL.trans (Subgroup.card_dvd_of_le (autOn_mono le_sup_left))
  have hodd : ¬ 2 ∣ (autOn T V).relIndex (autOn (L ⊔ T) V) := by
    intro h2
    apply h.hyp.sylow.2
    have hAB : T.subgroupOf (Subgroup.normalizer (V : Set G)) ≤
        (L ⊔ T).subgroupOf (Subgroup.normalizer (V : Set G)) := fun x hx =>
      Subgroup.mem_subgroupOf.2 ((le_sup_right : T ≤ L ⊔ T) (Subgroup.mem_subgroupOf.1 hx))
    have e1 := relIndex_map_dvd (conjAct V) hAB
    rw [Subgroup.relIndex_subgroupOf (sup_le hLV hTV)] at e1
    exact h2.trans (e1.trans (Subgroup.relIndex_dvd_index_of_le le_sup_right))
  have hmul := Subgroup.relIndex_mul_card (autOn T V) (autOn (L ⊔ T) V)
  rw [inf_eq_left.2 (autOn_mono le_sup_right)] at hmul
  have hcop : Nat.Coprime (2 ^ Flag.tri n) ((autOn T V).relIndex (autOn (L ⊔ T) V)) :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd)
  have hdvd : 2 ^ Flag.tri n ∣ Nat.card (autOn T V) := by
    rw [← hmul] at hLT
    exact hcop.dvd_of_dvd_mul_left hLT
  exact le_antisymm hle (Nat.le_of_dvd Nat.card_pos hdvd)

theorem tinv_comparable_of_hyp1281One (h1222 : Stmt12_2_2) [Finite G] {T L V : Subgroup G}
    {n : ℕ} (h : Hyp1281One G T L V n) {W W' : Subgroup G} (hWV : W ≤ V) (hW'V : W' ≤ V)
    (hTW : T ≤ Subgroup.normalizer (W : Set G)) (hTW' : T ≤ Subgroup.normalizer (W' : Set G)) :
    W ≤ W' ∨ W' ≤ W := by
  obtain ⟨hcard, hsq, -⟩ := h.card_sq
  obtain ⟨hc, -⟩ := h.natural
  exact tinv_comparable hsq hcard h.hyp.sylow.1 (card_autOn_sylow h1222 h) hWV hW'V hTW hTW'

theorem unique1282 (h1222 : Stmt12_2_2) :
    ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (n : ℕ), Hyp1281One G T L V n →
      ∀ (i : ℕ) (W W' : Subgroup G), IsTSub T V W i → IsTSub T V W' i → W = W' := by
  intro G _ _ T L V n h i W W' hW hW'
  rcases tinv_comparable_of_hyp1281One h1222 h hW.1 hW'.1 hW.2.2 hW'.2.2 with hle | hle
  · exact Subgroup.eq_of_le_of_card_ge hle (by rw [hW.2.1, hW'.2.1])
  · exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hW.2.1, hW'.2.1])).symm

end Hyp

section Exist

variable {G : Type} [Group G]

theorem zmod_two_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c
  decide

theorem card_mulAut_le [Finite G] {V : Subgroup G} [IsMulCommutative ↥V] {n : ℕ}
    (h2 : ∀ v ∈ V, v ^ 2 = 1) (hVn : Nat.card V = 2 ^ n) (hn : 1 ≤ n) :
    Nat.card (MulAut ↥V) ≤ 2 ^ (n * (n - 1) / 2) * ∏ j ∈ Finset.Icc 2 n, (2 ^ j - 1) := by
  let _ := zmodModuleOf h2
  have : Module.Finite (ZMod 2) (Additive ↥V) := Module.Finite.of_finite
  have hrank : Module.finrank (ZMod 2) (Additive ↥V) = n := by
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive ↥V)
    rw [Nat.card_zmod] at h1
    have h3 : Nat.card (Additive ↥V) = 2 ^ n := hVn
    exact Nat.pow_right_injective le_rfl (h1.symm.trans h3)
  let b := Module.finBasisOfFinrankEq (ZMod 2) (Additive ↥V) hrank
  let e : (Additive ↥V ≃ₗ[ZMod 2] Additive ↥V) ≃* GL (Fin n) (ZMod 2) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Additive ↥V)).symm.trans
      (Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toMulEquiv)
  have : Finite (Additive ↥V ≃ₗ[ZMod 2] Additive ↥V) :=
    Finite.of_injective
      (fun f : Additive ↥V ≃ₗ[ZMod 2] Additive ↥V => (f : Additive ↥V → Additive ↥V))
      DFunLike.coe_injective
  have h1 : Nat.card (MulAut ↥V) ≤ Nat.card (Additive ↥V ≃ₗ[ZMod 2] Additive ↥V) :=
    Nat.card_le_card_of_injective _ linHom_injective
  have h3 : Nat.card (GL (Fin n) (ZMod 2)) =
      Nat.card (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) := by
    refine (Nat.card_congr (Equiv.ofBijective
      (fun x : Matrix.SpecialLinearGroup (Fin n) (ZMod 2) => Matrix.SpecialLinearGroup.toGL x)
      ⟨Matrix.SpecialLinearGroup.toGL_injective, fun g => ?_⟩)).symm
    have hdet : (g : Matrix (Fin n) (Fin n) (ZMod 2)).det = 1 :=
      Flag.zmod_two_eq_one ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero
    exact ⟨⟨g, hdet⟩, Units.ext rfl⟩
  have h4 := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (K := ZMod 2) hn
  rw [Nat.card_zmod] at h4
  calc Nat.card (MulAut ↥V) ≤ Nat.card (Additive ↥V ≃ₗ[ZMod 2] Additive ↥V) := h1
    _ = Nat.card (GL (Fin n) (ZMod 2)) := Nat.card_congr e.toEquiv
    _ = _ := h3.trans h4

theorem autOn_eq_top_of_hyp1281One [Finite G] {T L V : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) : autOn L V = ⊤ := by
  obtain ⟨hcard, hsq, -⟩ := h.card_sq
  obtain ⟨hc, hnat⟩ := h.natural
  have hn : 1 ≤ n := by rcases h.n_mem with rfl | rfl | rfl <;> omega
  apply Subgroup.eq_top_of_card_eq
  refine le_antisymm (Nat.card_le_card_of_injective _ Subtype.val_injective) ?_
  rw [card_eq_of_binaryNaturalSL hnat hn]
  exact card_mulAut_le hsq hcard hn

theorem exist1282g (h1222 : Stmt12_2_2) : Exist1282g := by
  intro G _ _ T L V n h V₁ hV₁
  obtain ⟨hcard, hsq, hab⟩ := h.card_sq
  obtain ⟨hc, -⟩ := h.natural
  obtain ⟨-, hTV⟩ := h.hyp.le_and_normalizes h1222
  have hn2 : 2 ≤ n := by rcases h.n_mem with rfl | rfl | rfl <;> omega
  obtain ⟨V₂, hV₂, hV₁₂⟩ := exists_tsub_two_of_one h.hyp.sylow.1 hsq hab hTV hcard hn2 hV₁
  obtain ⟨v₁, hv₁, hv₁1⟩ : ∃ v ∈ V₁, v ≠ 1 := by
    by_contra hne
    push Not at hne
    have hbot : V₁ = ⊥ := (Subgroup.eq_bot_iff_forall _).2 hne
    have h1 := hV₁.2.1
    rw [hbot, Subgroup.card_bot] at h1
    norm_num at h1
  obtain ⟨v₂, hv₂, hv₂1⟩ : ∃ v ∈ V₂, v ∉ V₁ := by
    by_contra hne
    push Not at hne
    have h1 := Subgroup.card_le_of_le (show V₂ ≤ V₁ from hne)
    rw [hV₂.2.1, hV₁.2.1] at h1
    norm_num at h1
  have hv₁V := hV₁.1 hv₁
  have hv₂V := hV₂.1 hv₂
  let _ := zmodModuleOf hsq
  set a₁ : Additive ↥V := Additive.ofMul ⟨v₁, hv₁V⟩ with ha₁
  set a₂ : Additive ↥V := Additive.ofMul ⟨v₂, hv₂V⟩ with ha₂
  have ha : a₁ ∉ (ZMod 2) ∙ a₂ := by
    intro hmem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
    rcases zmod_two_cases c with rfl | rfl
    · rw [zero_smul] at hc
      apply hv₁1
      have := congrArg (fun x : Additive ↥V => ((Additive.toMul x : ↥V) : G)) hc
      simpa [ha₁] using this.symm
    · rw [one_smul] at hc
      apply hv₂1
      have := congrArg (fun x : Additive ↥V => ((Additive.toMul x : ↥V) : G)) hc
      simp only [ha₁, ha₂, toMul_ofMul] at this
      rw [this]
      exact hv₁
  obtain ⟨f, hf1, hf2⟩ := Submodule.exists_le_ker_of_notMem ha
  have hfa₂ : f a₂ = 0 := LinearMap.mem_ker.1 (hf2 (Submodule.mem_span_singleton_self a₂))
  have hfa₁ : f a₁ = 1 := Flag.zmod_two_eq_one hf1
  let τ0 : Additive ↥V →ₗ[ZMod 2] Additive ↥V := LinearMap.id + f.smulRight a₂
  have hτ0 : ∀ x, τ0 x = x + f x • a₂ := fun x => rfl
  have hinv : Function.Involutive τ0 := by
    intro x
    rw [hτ0, hτ0, map_add, map_smul, hfa₂, smul_zero, add_zero, add_assoc, ← add_smul,
      CharTwo.add_self_eq_zero, zero_smul, add_zero]
  let α : MulAut ↥V :=
    { toFun := fun x => Additive.toMul (τ0 (Additive.ofMul x))
      invFun := fun x => Additive.toMul (τ0 (Additive.ofMul x))
      left_inv := fun x => by
        simp only [ofMul_toMul]
        rw [hinv]
        rfl
      right_inv := fun x => by
        simp only [ofMul_toMul]
        rw [hinv]
        rfl
      map_mul' := fun x y => by simp only [ofMul_mul, map_add, toMul_add] }
  have hα : ∀ x : ↥V, ((α x : ↥V) : G) = (x : G) ∨ ((α x : ↥V) : G) = (x : G) * v₂ := by
    intro x
    have e : α x = x * Additive.toMul (f (Additive.ofMul x) • a₂) := by
      show Additive.toMul (τ0 (Additive.ofMul x)) = _
      rw [hτ0, toMul_add, toMul_ofMul]
    rcases zmod_two_cases (f (Additive.ofMul x)) with h0 | h1
    · left
      rw [e, h0, zero_smul, toMul_zero, mul_one]
    · right
      rw [e, h1, one_smul, Subgroup.coe_mul, ha₂, toMul_ofMul]
  have hα₁ : ((α ⟨v₁, hv₁V⟩ : ↥V) : G) = v₁ * v₂ := by
    show ((Additive.toMul (τ0 a₁) : ↥V) : G) = _
    rw [hτ0, hfa₁, one_smul, toMul_add, Subgroup.coe_mul, ha₁, ha₂, toMul_ofMul, toMul_ofMul]
  have hαL : α ∈ autOn L V := by
    rw [autOn_eq_top_of_hyp1281One h]
    exact Subgroup.mem_top _
  obtain ⟨⟨g, hgN⟩, hgL, hgα⟩ := hαL
  have hconj : ∀ x (hx : x ∈ V), g * x * g⁻¹ = ((α ⟨x, hx⟩ : ↥V) : G) := by
    intro x hx
    rw [← hgα]
    rfl
  refine ⟨g, Subgroup.mem_inf.2 ⟨Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.1 hgL),
    Subgroup.mem_iInf.2 fun Y => Subgroup.mem_iInf.2 fun hY => ?_⟩, fun hgV₁ => ?_⟩
  · obtain ⟨i, hi, hYi⟩ := hY
    have hV₂Y : V₂ ≤ Y := by
      rcases tinv_comparable_of_hyp1281One h1222 h hV₂.1 hYi.1 hV₂.2.2 hYi.2.2 with hle | hle
      · exact hle
      · have heq : Y = V₂ := Subgroup.eq_of_le_of_card_ge hle (by
          rw [hV₂.2.1, hYi.2.1]
          exact Nat.pow_le_pow_right (by norm_num) hi)
        rw [heq]
    have hv₂Y : v₂ ∈ Y := hV₂Y hv₂
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have hyV := hYi.1 hy
      rw [hconj y hyV]
      rcases hα ⟨y, hyV⟩ with e | e
      · rw [e]
        exact hy
      · rw [e]
        exact Y.mul_mem hy hv₂Y
    · intro hy
      have hyV : y ∈ V := (Subgroup.mem_normalizer_iff.1 hgN y).2 (hYi.1 hy)
      rw [hconj y hyV] at hy
      rcases hα ⟨y, hyV⟩ with e | e
      · rw [e] at hy
        exact hy
      · rw [e] at hy
        have := Y.mul_mem hy (Y.inv_mem hv₂Y)
        rwa [mul_inv_cancel_right] at this
  · have h1 : g * v₁ * g⁻¹ ∈ V₁ := (Subgroup.mem_normalizer_iff.1 hgV₁ v₁).1 hv₁
    rw [hconj v₁ hv₁V, hα₁] at h1
    apply hv₂1
    have := V₁.mul_mem (V₁.inv_mem hv₁) h1
    rwa [inv_mul_cancel_left] at this

end Exist

end CFSG.Quasithin.H13
