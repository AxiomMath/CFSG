module

public import CFSG.Quasithin.H13.L32NKGG22Wit
public import CFSG.Quasithin.H13.L32NLem14331a
public import Certificates.Certificate7129

public section

namespace CFSG.Quasithin.H13.KGCert

open scoped commutatorElement

@[expose] def KGG22ConjModel : Prop :=
  ∀ x ∈ g22Elems, mulC x x = oneC → x ≠ oneC →
    ∃ y ∈ g22Elems, mulC y x = mulC t0C y ∨ mulC y x = mulC t1C y

theorem kgG22ConjModel : KGG22ConjModel := by
  intro x hx h2 h1
  have hcheck := Certificates.certificate7129
  simp only [g22ConjCheck, List.all_eq_true, List.any_eq_true, Bool.or_eq_true,
    beq_iff_eq] at hcheck
  exact hcheck x (List.mem_filter.mpr ⟨hx, by simp [h2, h1]⟩)

@[expose] def wH : List Bool := [false, false, true]

@[expose] def wHi : List Bool := [false, false, true, false, false, true, false, false, true]

@[expose] def wK1 : List Bool := [false]

@[expose] def wK1i : List Bool := [true, true, true, true, false, true, true, true, true]

@[expose] def wK2 : List Bool := [false, true, false, false, true, true]

@[expose] def wK2i : List Bool := [true, true, false, true, false, false, true, true, true, true]

@[expose] def wK3 : List Bool := [false, false, false, true, true, false]

@[expose] def wK3i : List Bool :=
  [true, true, false, true, false, false, false, true, true, false, true, true, false, true]

@[expose] def wX1 : List Bool := wT0 ++ wK1 ++ wT0 ++ wK1i

@[expose] def wX2 : List Bool := wK2 ++ wT0 ++ wK2i ++ (wK3 ++ wT0 ++ wK3i)

@[expose] def wX3 : List Bool := wT0 ++ (wK2 ++ wT0 ++ wK2i)

theorem g22_word_checks :
    evalWord (wT1 ++ (wH ++ wT1 ++ wHi)) = evalWord wT0 ∧
      evalWord (wH ++ wHi) = oneC ∧ evalWord (wK1 ++ wK1i) = oneC ∧
      evalWord (wK2 ++ wK2i) = oneC ∧ evalWord (wK3 ++ wK3i) = oneC ∧
      evalWord (powW wX1 3) = oneC ∧ evalWord wX1 ≠ oneC ∧
      evalWord (powW wX2 3) = oneC ∧ evalWord wX2 ≠ oneC ∧
      evalWord (wX1 ++ wX2) = evalWord (wX2 ++ wX1) ∧
      evalWord wX2 ≠ evalWord wX1 ∧ evalWord wX2 ≠ evalWord (powW wX1 2) ∧
      evalWord (powW wX3 3) = oneC ∧
      evalWord (wX3 ++ wX1 ++ powW wX3 2) = evalWord wX2 ∧
      evalWord (wX3 ++ wX2 ++ powW wX3 2) = evalWord (powW wX1 2 ++ powW wX2 2) ∧
      ∀ i < 3, ∀ j < 3, evalWord wX3 ≠ evalWord (powW wX2 i ++ powW wX1 j) := by
  decide +kernel

theorem mem_of_pGroup_le {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime] {N S : Subgroup X}
    (hN : N.Normal) (hSN : S ≤ N) (hSp : IsPGroup p S) (hSi : ¬ p ∣ S.index) {x : X} {k : ℕ}
    (hx : x ^ (p ^ k) = 1) : x ∈ N := by
  set P := hSp.toSylow hSi with hP
  have hxp : IsPGroup p (Subgroup.zpowers x) := by
    rintro ⟨y, hy⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    refine ⟨k, Subtype.ext ?_⟩
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]
  obtain ⟨Q, hQ⟩ := hxp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X P Q
  have hxQ : x ∈ (Q : Subgroup X) := hQ (Subgroup.mem_zpowers x)
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxQ
  have e1 : (MulAut.conj g)⁻¹ • x = g⁻¹ * x * g := by
    rw [MulAut.smul_def, ← map_inv, MulAut.conj_apply, inv_inv]
  rw [e1, hP, IsPGroup.toSylow_coe] at hxQ
  have hy : g⁻¹ * x * g ∈ N := hSN hxQ
  have e : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
  rw [e]
  exact hN.conj_mem _ hy g

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

@[expose] def KGG22Closure : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V), (∀ v, B v v = 0) → (∀ v, (∀ w, B v w = 0) → v = 0) →
    Module.finrank (ZMod 2) V = 6 →
    ∀ Γ : Subgroup (V ≃ₗ[ZMod 2] V), (∀ γ ∈ Γ, ∀ v w, B (γ v) (γ w) = B v w) →
    Nat.card Γ = 12096 →
    ∀ t ∈ Γ, t * t = 1 → t ≠ 1 → ∀ N : Subgroup (V ≃ₗ[ZMod 2] V), N ≤ Γ →
      Γ ≤ Subgroup.normalizer (N : Set (V ≃ₗ[ZMod 2] V)) → t ∈ N →
      (∀ γ ∈ Γ, γ ^ 3 = 1 → γ ∈ N) ∧
      ∃ s₁ ∈ N, ∃ s₂ ∈ N, orderOf s₁ = 3 ∧ orderOf s₂ = 3 ∧ s₁ * s₂ = s₂ * s₁ ∧
        s₂ ∉ Subgroup.zpowers s₁

theorem kgG22Closure_of (hM : KGG22ConjModel)
    (hO : KGSp6Order12096) : KGG22Closure := by
  intro V _ _ _ B hBalt hBnd hdim Γ hΓB hcard t ht ht2 ht1 N hNΓ hΓN htN
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (V ≃ₗ[ZMod 2] V) :=
    Finite.of_injective (fun e => (e : V → V)) fun _ _ h => LinearEquiv.ext (congrFun h)
  obtain ⟨b, hb⟩ := hO V B hBalt hBnd hdim Γ hΓB hcard
  set m : (V ≃ₗ[ZMod 2] V) → Matrix (Fin 6) (Fin 6) (ZMod 2) :=
    fun γ => LinearMap.toMatrix b b (γ : V →ₗ[ZMod 2] V) with hm
  have hmul : ∀ γ δ : V ≃ₗ[ZMod 2] V, m (γ * δ) = m γ * m δ := fun γ δ => by
    simp only [hm, LinearEquiv.coe_toLinearMap_mul, LinearMap.toMatrix_mul]
  have hone : m 1 = 1 := by
    simp only [hm, LinearEquiv.coe_toLinearMap_one, LinearMap.toMatrix_id]
  have hinj : ∀ γ δ : V ≃ₗ[ZMod 2] V, m γ = m δ → γ = δ := fun γ δ h =>
    LinearEquiv.toLinearMap_injective ((LinearMap.toMatrix b b).injective h)
  obtain ⟨γA, hγA, hmA⟩ := (hb (decodeC gAc)).mp (Submonoid.subset_closure (Or.inl rfl))
  obtain ⟨γB, hγB, hmB⟩ := (hb (decodeC gBc)).mp (Submonoid.subset_closure (Or.inr rfl))
  set W := wordEval γA γB with hW
  have hmW : ∀ w, m (W w) = decodeC (evalWord w) := by
    intro w
    induction w with
    | nil => rw [hW, wordEval, List.foldr_nil, hone, evalWord, List.foldr_nil, decodeC_oneC]
    | cons g w ih =>
      have e1 : W (g :: w) = (if g then γA else γB) * W w := rfl
      rw [e1, hmul, ih, evalWord_cons, decodeC_mulC _ _ (length_evalWord w)]
      cases g
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact congrArg (· * _) hmB
      · simp only [↓reduceIte]
        exact congrArg (· * _) hmA
  have heq : ∀ w w', evalWord w = evalWord w' → W w = W w' := fun w w' h =>
    hinj _ _ (by rw [hmW, hmW, h])
  have hne : ∀ w w', evalWord w ≠ evalWord w' → W w ≠ W w' := fun w w' h h' =>
    h (decodeC_injOn (validC_evalWord w) (validC_evalWord w') (by rw [← hmW, ← hmW, h']))
  have hone' : ∀ w, evalWord w = oneC → W w = 1 := fun w h => heq w [] h
  have hne1 : ∀ w, evalWord w ≠ oneC → W w ≠ 1 := fun w h => hne w [] h
  have hpow : ∀ w n, W (powW w n) = W w ^ n := wordEval_powW γA γB
  have happ : ∀ w₁ w₂, W (w₁ ++ w₂) = W w₁ * W w₂ := wordEval_append γA γB
  have hmem : ∀ w, W w ∈ Γ := wordEval_mem hγA hγB
  have hinv : ∀ w w', evalWord (w ++ w') = oneC → (W w)⁻¹ = W w' := fun w w' h =>
    inv_eq_of_mul_eq_one_right (by rw [← happ]; exact hone' _ h)
  obtain ⟨c1, cH, cK1, cK2, cK3, cx1, cx1', cx2, cx2', c12, c21, c22, cx3, c31, c32, c3E⟩ :=
    g22_word_checks
  have hconjN : ∀ {s : V ≃ₗ[ZMod 2] V}, s ∈ N → ∀ κ ∈ Γ, κ * s * κ⁻¹ ∈ N := fun hs κ hκ =>
    (Subgroup.mem_normalizer_iff.mp (hΓN hκ) _).mp hs
  have hmt : m t ∈ g22Mats := (hb (m t)).mpr ⟨t, ht, rfl⟩
  obtain ⟨x, hx, hxt⟩ := (mem_g22Mats_iff (m t)).mp hmt
  have hxV := validC_of_mem hx
  have hx2 : mulC x x = oneC := decodeC_injOn (validC_mulC hxV hxV) validC_oneC (by
    rw [decodeC_mulC _ _ hxV.1, hxt, ← hmul, ht2, hone, decodeC_oneC])
  have hx1 : x ≠ oneC := fun h => ht1 (hinj _ _ (by rw [hone, ← hxt, h, decodeC_oneC]))
  obtain ⟨y, hy, hyx⟩ := hM x hx hx2 hx1
  have hyV := validC_of_mem hy
  obtain ⟨γ, hγ, hmγ'⟩ := (hb (decodeC y)).mp ((mem_g22Mats_iff _).mpr ⟨y, hy, rfl⟩)
  have hmγ : m γ = decodeC y := hmγ'
  have hconj_t : ∀ w, mulC y x = mulC (evalWord w) y → γ * t * γ⁻¹ = W w := by
    intro w h
    have h1 : γ * t = W w * γ := hinj _ _ (by
      rw [hmul, hmul, hmγ, ← hxt, hmW, ← decodeC_mulC _ _ hxV.1, ← decodeC_mulC _ _ hyV.1, h])
    rw [h1, mul_inv_cancel_right]
  have ht0N : W wT0 ∈ N := by
    rcases hyx with h | h
    · rw [← hconj_t wT0 h]
      exact hconjN htN γ hγ
    · have ht1N : W wT1 ∈ N := by
        rw [← hconj_t wT1 h]
        exact hconjN htN γ hγ
      rw [← heq _ _ c1, happ, happ, happ, ← hinv _ _ cH]
      exact N.mul_mem ht1N (hconjN ht1N _ (hmem wH))
  have hconj0 : ∀ k k', evalWord (k ++ k') = oneC → W (k ++ wT0 ++ k') ∈ N := by
    intro k k' hk
    rw [happ, happ, ← hinv _ _ hk]
    exact hconjN ht0N _ (hmem k)
  have hx1N : W wX1 ∈ N := by
    rw [wX1, show wT0 ++ wK1 ++ wT0 ++ wK1i = wT0 ++ (wK1 ++ wT0 ++ wK1i) by simp, happ]
    exact N.mul_mem ht0N (hconj0 _ _ cK1)
  have hx2N : W wX2 ∈ N := by
    rw [wX2, happ]
    exact N.mul_mem (hconj0 _ _ cK2) (hconj0 _ _ cK3)
  have hx3N : W wX3 ∈ N := by
    rw [wX3, happ]
    exact N.mul_mem ht0N (hconj0 _ _ cK2)
  set X₁ := W wX1
  set X₂ := W wX2
  set X₃ := W wX3
  have hX1 : X₁ ^ 3 = 1 := by rw [← hpow]; exact hone' _ cx1
  have hX1' : X₁ ≠ 1 := hne1 _ cx1'
  have hX2 : X₂ ^ 3 = 1 := by rw [← hpow]; exact hone' _ cx2
  have hX2' : X₂ ≠ 1 := hne1 _ cx2'
  have hX3 : X₃ ^ 3 = 1 := by rw [← hpow]; exact hone' _ cx3
  have ho1 : orderOf X₁ = 3 := orderOf_eq_prime hX1 hX1'
  have ho2 : orderOf X₂ = 3 := orderOf_eq_prime hX2 hX2'
  have h12 : X₁ * X₂ = X₂ * X₁ := by rw [← happ, ← happ]; exact heq _ _ c12
  have h21 : X₂ ∉ Subgroup.zpowers X₁ := by
    refine L14331.not_mem_zpowers_of_three ho1 hX2' (hne _ _ c21) ?_
    rw [← hpow]
    exact hne _ _ c22
  set E := Subgroup.zpowers X₁ ⊔ Subgroup.zpowers X₂ with hE
  have hE9 : Nat.card E = 9 := L14331.card_e9 ho1 ho2 h12 h21
  have hX3inv : X₃⁻¹ = X₃ ^ 2 := by
    rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, hX3]
  have hc1 : X₃ * X₁ * X₃⁻¹ = X₂ := by
    rw [hX3inv, ← hpow, ← happ, ← happ]
    exact heq _ _ c31
  have hc2 : X₃ * X₂ * X₃⁻¹ = X₁ ^ 2 * X₂ ^ 2 := by
    rw [hX3inv, ← hpow, ← happ, ← happ, ← hpow, ← hpow, ← happ]
    exact heq _ _ c32
  have hX3E : X₃ ∈ Subgroup.normalizer (E : Set (V ≃ₗ[ZMod 2] V)) := by
    refine L14328.mem_normalizer_of_maps fun w hw => ?_
    obtain ⟨i, j, rfl⟩ := L14331.exists_zpow_of_mem_sup h12 hw
    have e1 : X₃ * (X₂ ^ i * X₁ ^ j) * X₃⁻¹ = (X₃ * X₂ * X₃⁻¹) ^ i * (X₃ * X₁ * X₃⁻¹) ^ j := by
      rw [← MulAut.conj_apply, map_mul, map_zpow, map_zpow, MulAut.conj_apply, MulAut.conj_apply]
    rw [e1, hc1, hc2]
    refine E.mul_mem (E.zpow_mem (E.mul_mem (E.pow_mem ?_ 2) (E.pow_mem ?_ 2)) i)
      (E.zpow_mem ?_ j)
    · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers X₁)
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers X₂)
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers X₂)
  have hX3notE : X₃ ∉ E := by
    intro h
    obtain ⟨i, j, hij⟩ := L14331.exists_zpow_of_mem_sup h12 h
    have e2 : X₂ ^ i = X₂ ^ (i % 3).toNat := by
      rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg i (by norm_num)),
        ← zpow_mod_orderOf, ho2]
      rfl
    have e1 : X₁ ^ j = X₁ ^ (j % 3).toNat := by
      rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg j (by norm_num)),
        ← zpow_mod_orderOf, ho1]
      rfl
    rw [e2, e1] at hij
    have hi3 : (i % 3).toNat < 3 := by omega
    have hj3 : (j % 3).toNat < 3 := by omega
    apply hne _ _ (c3E _ hi3 _ hj3)
    rw [happ, hpow, hpow]
    exact hij
  have hS : Nat.card ↥(Subgroup.zpowers X₃ ⊔ E) = 27 := by
    have h := L32NSet14.card_sup_mul_card_inf ((Subgroup.zpowers_le).mpr hX3E)
    have hinf : Subgroup.zpowers X₃ ⊓ E = ⊥ := by
      have hdvd : Nat.card ↥(Subgroup.zpowers X₃ ⊓ E) ∣ 3 := by
        have := Subgroup.card_dvd_of_le (inf_le_left : Subgroup.zpowers X₃ ⊓ E ≤ _)
        rwa [Nat.card_zpowers, orderOf_eq_prime hX3 (fun h1 => hX3notE (h1 ▸ E.one_mem))] at this
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
      · exact Subgroup.eq_bot_of_card_eq _ h1
      · exfalso
        have heq' : Subgroup.zpowers X₃ ⊓ E = Subgroup.zpowers X₃ :=
          Subgroup.eq_of_le_of_card_ge inf_le_left (by
            rw [h3, Nat.card_zpowers, orderOf_eq_prime hX3 (fun h1 => hX3notE (h1 ▸ E.one_mem))])
        exact hX3notE ((heq' ▸ inf_le_right : Subgroup.zpowers X₃ ≤ E) (Subgroup.mem_zpowers X₃))
    rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers,
      orderOf_eq_prime hX3 (fun h1 => hX3notE (h1 ▸ E.one_mem)), hE9] at h
    exact h
  have hSN : Subgroup.zpowers X₃ ⊔ E ≤ N :=
    sup_le ((Subgroup.zpowers_le).mpr hx3N) (sup_le ((Subgroup.zpowers_le).mpr hx1N)
      ((Subgroup.zpowers_le).mpr hx2N))
  have hSΓ : Subgroup.zpowers X₃ ⊔ E ≤ Γ := hSN.trans hNΓ
  have hNn : (N.subgroupOf Γ).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hΓN
  have hS' : Nat.card ↥((Subgroup.zpowers X₃ ⊔ E).subgroupOf Γ) = 27 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSΓ).toEquiv, hS]
  have hSp : IsPGroup 3 ↥((Subgroup.zpowers X₃ ⊔ E).subgroupOf Γ) :=
    IsPGroup.of_card (n := 3) (by rw [hS']; norm_num)
  have hSi : ¬ 3 ∣ ((Subgroup.zpowers X₃ ⊔ E).subgroupOf Γ).index := by
    have h := Subgroup.card_mul_index ((Subgroup.zpowers X₃ ⊔ E).subgroupOf Γ)
    rw [hS', hcard] at h
    have : ((Subgroup.zpowers X₃ ⊔ E).subgroupOf Γ).index = 448 := by omega
    rw [this]
    norm_num
  refine ⟨fun δ hδ h3 => ?_, X₁, hx1N, X₂, hx2N, ho1, ho2, h12, h21⟩
  have := mem_of_pGroup_le hNn
    (fun x hx => Subgroup.mem_subgroupOf.mpr (hSN (Subgroup.mem_subgroupOf.mp hx))) hSp hSi (k := 1)
    (x := ⟨δ, hδ⟩) (by rw [pow_one]; exact Subtype.ext h3)
  exact Subgroup.mem_subgroupOf.mp this

theorem kgG22Closure
    (hO : KGSp6Order12096) : KGG22Closure :=
  kgG22Closure_of kgG22ConjModel hO

end CFSG.Quasithin.H13.KGCert
