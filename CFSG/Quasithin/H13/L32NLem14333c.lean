module

public import CFSG.Quasithin.H13.L32NLem14333b

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint L14332 CFSG.LieType.BorelTits
open scoped commutatorElement

namespace L14333

variable {G : Type} [Group G]

theorem pow_eq_pow_mod_four {s : G} (hs : s ^ 4 = 1) (n : ℕ) : s ^ n = s ^ (n % 4) := by
  conv_lhs => rw [← Nat.div_add_mod n 4, pow_add, pow_mul, hs, one_pow, one_mul]

theorem pow_eq_pow_mod_two {s : G} (hs : s ^ 2 = 1) (n : ℕ) : s ^ n = s ^ (n % 2) := by
  conv_lhs => rw [← Nat.div_add_mod n 2, pow_add, pow_mul, hs, one_pow, one_mul]

theorem isZ4Cube_of [Finite G] {P : Subgroup G} (hPab : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x)
    {s₁ s₂ s₃ : G} (h₁ : s₁ ∈ P) (h₂ : s₂ ∈ P) (h₃ : s₃ ∈ P) (h₁4 : s₁ ^ 4 = 1)
    (h₂4 : s₂ ^ 4 = 1) (h₃4 : s₃ ^ 4 = 1)
    (hind : ∀ i j k : ℕ, i < 4 → j < 4 → k < 4 → s₁ ^ i * s₂ ^ j * s₃ ^ k = 1 →
      i = 0 ∧ j = 0 ∧ k = 0)
    (hcard : Nat.card P = 64) : HSType.IsZ4Cube ↥P := by
  have hcomm : ∀ (i j : ℕ) (u w : G), u ∈ P → w ∈ P → u ^ i * w ^ j = w ^ j * u ^ i :=
    fun i j u w hu hw => hPab _ (P.pow_mem hu i) _ (P.pow_mem hw j)
  let e : (ZMod 4) → G → G := fun m s => s ^ m.val
  have he_add : ∀ (m m' : ZMod 4) (s : G), s ^ 4 = 1 → e (m + m') s = e m s * e m' s := by
    intro m m' s hs
    show s ^ (m + m').val = s ^ m.val * s ^ m'.val
    rw [ZMod.val_add, ← pow_eq_pow_mod_four hs, pow_add]
  have hmem : ∀ (m : ZMod 4) (s : G), s ∈ P → e m s ∈ P := fun m s hs => P.pow_mem hs _
  let f : Multiplicative (ZMod 4) × Multiplicative (ZMod 4) × Multiplicative (ZMod 4) →* ↥P :=
    { toFun := fun m => ⟨e (Multiplicative.toAdd m.1) s₁ * e (Multiplicative.toAdd m.2.1) s₂ *
        e (Multiplicative.toAdd m.2.2) s₃, P.mul_mem (P.mul_mem (hmem _ _ h₁) (hmem _ _ h₂))
          (hmem _ _ h₃)⟩
      map_one' := by
        apply Subtype.ext
        simp [e]
      map_mul' := by
        rintro ⟨m₁, m₂, m₃⟩ ⟨n₁, n₂, n₃⟩
        apply Subtype.ext
        simp only [Prod.mk_mul_mk, toAdd_mul, Subgroup.coe_mul]
        rw [he_add _ _ _ h₁4, he_add _ _ _ h₂4, he_add _ _ _ h₃4]
        have c1 := hcomm (Multiplicative.toAdd n₁).val (Multiplicative.toAdd m₂).val s₁ s₂ h₁ h₂
        have c2 := hcomm (Multiplicative.toAdd n₁).val (Multiplicative.toAdd m₃).val s₁ s₃ h₁ h₃
        have c3 := hcomm (Multiplicative.toAdd n₂).val (Multiplicative.toAdd m₃).val s₂ s₃ h₂ h₃
        simp only [e]
        calc s₁ ^ (Multiplicative.toAdd m₁).val * s₁ ^ (Multiplicative.toAdd n₁).val *
              (s₂ ^ (Multiplicative.toAdd m₂).val * s₂ ^ (Multiplicative.toAdd n₂).val) *
              (s₃ ^ (Multiplicative.toAdd m₃).val * s₃ ^ (Multiplicative.toAdd n₃).val)
            = s₁ ^ (Multiplicative.toAdd m₁).val *
              (s₁ ^ (Multiplicative.toAdd n₁).val * s₂ ^ (Multiplicative.toAdd m₂).val) *
              s₂ ^ (Multiplicative.toAdd n₂).val *
              (s₃ ^ (Multiplicative.toAdd m₃).val * s₃ ^ (Multiplicative.toAdd n₃).val) := by
              group
          _ = s₁ ^ (Multiplicative.toAdd m₁).val *
              (s₂ ^ (Multiplicative.toAdd m₂).val * s₁ ^ (Multiplicative.toAdd n₁).val) *
              s₂ ^ (Multiplicative.toAdd n₂).val *
              (s₃ ^ (Multiplicative.toAdd m₃).val * s₃ ^ (Multiplicative.toAdd n₃).val) := by
              rw [c1]
          _ = s₁ ^ (Multiplicative.toAdd m₁).val * s₂ ^ (Multiplicative.toAdd m₂).val *
              (s₁ ^ (Multiplicative.toAdd n₁).val * s₂ ^ (Multiplicative.toAdd n₂).val *
                s₃ ^ (Multiplicative.toAdd m₃).val) * s₃ ^ (Multiplicative.toAdd n₃).val := by
              group
          _ = s₁ ^ (Multiplicative.toAdd m₁).val * s₂ ^ (Multiplicative.toAdd m₂).val *
              (s₃ ^ (Multiplicative.toAdd m₃).val * (s₁ ^ (Multiplicative.toAdd n₁).val *
                s₂ ^ (Multiplicative.toAdd n₂).val)) * s₃ ^ (Multiplicative.toAdd n₃).val := by
              rw [hPab _ (P.mul_mem (P.pow_mem h₁ _) (P.pow_mem h₂ _)) _ (P.pow_mem h₃ _)]
          _ = s₁ ^ (Multiplicative.toAdd m₁).val * s₂ ^ (Multiplicative.toAdd m₂).val *
              s₃ ^ (Multiplicative.toAdd m₃).val * (s₁ ^ (Multiplicative.toAdd n₁).val *
                s₂ ^ (Multiplicative.toAdd n₂).val * s₃ ^ (Multiplicative.toAdd n₃).val) := by
              group }
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro ⟨m₁, m₂, m₃⟩ hm
    have h := congrArg Subtype.val hm
    simp only [f, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_one, e] at h
    obtain ⟨hi, hj, hk⟩ := hind _ _ _ (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _) h
    have e1 : Multiplicative.toAdd m₁ = 0 := (ZMod.val_eq_zero _).mp hi
    have e2 : Multiplicative.toAdd m₂ = 0 := (ZMod.val_eq_zero _).mp hj
    have e3 : Multiplicative.toAdd m₃ = 0 := (ZMod.val_eq_zero _).mp hk
    simp only [Prod.mk_eq_one]
    exact ⟨congrArg Multiplicative.ofAdd e1, congrArg Multiplicative.ofAdd e2,
      congrArg Multiplicative.ofAdd e3⟩
  have hbij : Function.Bijective f := by
    refine hinj.bijective_of_nat_card_le ?_
    rw [hcard, Nat.card_prod, Nat.card_prod]
    simp [Nat.card_eq_fintype_card, ZMod.card]
  exact ⟨(MulEquiv.ofBijective f hbij).symm⟩

theorem mem_of_mul_self_eq_one [Finite G] {P V : Subgroup G}
    (hPab : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) (hVP : V ≤ P) (hV2 : ∀ v ∈ V, v * v = 1)
    (hsqV : ∀ p ∈ P, p * p ∈ V) (hsq : ∀ v ∈ V, ∃ p ∈ P, p * p = v)
    (hcard : Nat.card P = Nat.card V * Nat.card V) {u : G} (hu : u ∈ P) (hu1 : u * u = 1) :
    u ∈ V := by
  let φ : ↥P →* ↥V :=
    { toFun := fun p => ⟨(p : G) * p, hsqV p p.2⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun p q => by
        apply Subtype.ext
        show (p : G) * q * (p * q) = p * p * (q * q)
        rw [mul_assoc, ← mul_assoc (q : G), hPab _ q.2 _ p.2]
        group }
  have hsurj : Function.Surjective φ := by
    rintro ⟨v, hv⟩
    obtain ⟨p, hp, rfl⟩ := hsq v hv
    exact ⟨⟨p, hp⟩, rfl⟩
  have hle : V.subgroupOf P ≤ φ.ker := fun p hp => by
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    exact hV2 _ (Subgroup.mem_subgroupOf.mp hp)
  have hker : V.subgroupOf P = φ.ker := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    have h1 := Subgroup.card_ker_mul_card_range φ
    rw [MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top, hcard] at h1
    have h2 : Nat.card ↥(V.subgroupOf P) = Nat.card V :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVP).toEquiv
    rw [h2]
    have hV0 : 0 < Nat.card V := Nat.card_pos
    exact (Nat.eq_of_mul_eq_mul_right hV0 h1).le
  have hmem : (⟨u, hu⟩ : ↥P) ∈ φ.ker := by
    rw [MonoidHom.mem_ker]
    exact Subtype.ext hu1
  rw [← hker] at hmem
  exact Subgroup.mem_subgroupOf.mp hmem

theorem isXSectionIso₂_of_sq [Finite G] {X P V : Subgroup G}
    (hPab : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) (hVP : V ≤ P) (hV2 : ∀ v ∈ V, v * v = 1)
    (hsqV : ∀ p ∈ P, p * p ∈ V) (hsq : ∀ v ∈ V, ∃ p ∈ P, p * p = v)
    (hcard : Nat.card P = Nat.card V * Nat.card V) : IsXSectionIso₂ X P V V ⊥ := by
  have hN : (V.subgroupOf P).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have : (g : G) * n * (g : G)⁻¹ = n := by
      rw [hPab _ g.2 _ n.2]; group
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [this]
    exact hn⟩
  have hbot : (⊥ : Subgroup G).subgroupOf V = ⊥ := Subgroup.bot_subgroupOf V
  have hN' : ((⊥ : Subgroup G).subgroupOf V).Normal := by rw [hbot]; infer_instance
  let φ : ↥P →* ↥V :=
    { toFun := fun p => ⟨(p : G) * p, hsqV p p.2⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun p q => by
        apply Subtype.ext
        show (p : G) * q * (p * q) = p * p * (q * q)
        rw [mul_assoc, ← mul_assoc (q : G), hPab _ q.2 _ p.2]
        group }
  have hsurj : Function.Surjective φ := by
    rintro ⟨v, hv⟩
    obtain ⟨p, hp, rfl⟩ := hsq v hv
    exact ⟨⟨p, hp⟩, rfl⟩
  have hker : V.subgroupOf P = φ.ker := by
    ext p
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    constructor
    · intro hp
      exact Subtype.ext (hV2 _ hp)
    · intro hp
      exact mem_of_mul_self_eq_one hPab hVP hV2 hsqV hsq hcard p.2 (congrArg Subtype.val hp)
  let e : ↥P ⧸ V.subgroupOf P ≃* ↥V ⧸ (⊥ : Subgroup G).subgroupOf V :=
    ((QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hsurj)).trans
      ((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot).symm
  have he : ∀ j : ↥P, e (j : ↥P ⧸ V.subgroupOf P) = ((φ j : ↥V) : ↥V ⧸ _) := by
    intro j
    show ((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot).symm
      (QuotientGroup.quotientKerEquivOfSurjective φ hsurj
        (QuotientGroup.quotientMulEquivOfEq hker (j : ↥P ⧸ V.subgroupOf P))) = _
    rw [MulEquiv.symm_apply_eq]
    rfl
  refine ⟨hN, hN', e, fun x _ j k hj hk hjk => ?_⟩
  rw [he] at hjk ⊢
  have hjk' : φ j = k := by
    rw [QuotientGroup.eq, hbot, Subgroup.mem_bot] at hjk
    exact (inv_mul_eq_one.mp hjk)
  have hval : (j : G) * j = k := congrArg Subtype.val hjk'
  congr 1
  apply Subtype.ext
  show x * (j : G) * x⁻¹ * (x * j * x⁻¹) = x * k * x⁻¹
  rw [← hval]
  group

variable [Finite G]

namespace Ctx

variable {T L V V₂ K : Subgroup G} {g a z b d x : G} {D : HatModelU (fsuU T V)}
  (c : Ctx G T L V V₂ K g a z b d x D)
include c

theorem sq_mem_V_of_X : ∀ y ∈ conjClosure (centerOf (fsuU T V)) L, y * y ∈ V := by
  refine sq_mem_of_closure rfl c.X_comm ?_
  rintro _ ⟨l, hl, w, hw, rfl⟩
  have hw2 : w * w ∈ fsuV1 T V := c.ctx.sq w (Subgroup.mem_inf.mp hw).1
  have e : l * w * l⁻¹ * (l * w * l⁻¹) = l * (w * w) * l⁻¹ := by group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp (c.L_le_normV hl) _).mp (Subgroup.mem_inf.mp hw2).1

theorem indep {i j k : ℕ} (hi : i < 2) (hj : j < 2) (hk : k < 2)
    (h : z ^ i * a ^ j * b ^ k = 1) : i = 0 ∧ j = 0 ∧ k = 0 := by
  have hzV₂ : z ∈ V₂ := c.ctx.plane.2 c.z_mem
  have haV₂ := c.ctx.aV₂
  interval_cases i <;> interval_cases j <;> interval_cases k <;> simp at h ⊢
  · exact c.b_nmem (h ▸ one_mem _)
  · exact c.ctx.a1 (h ▸ one_mem _)
  · apply c.b_nmem
    have : b = a⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this]
    exact inv_mem haV₂
  · exact c.z_ne h
  · apply c.b_nmem
    have : b = z⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this]
    exact inv_mem hzV₂
  · apply c.ctx.a1
    have : a = z⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this]
    exact inv_mem c.z_mem
  · apply c.b_nmem
    have : b = (z * a)⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this]
    exact inv_mem (mul_mem hzV₂ haV₂)

theorem isZ4Cube (hyp : AlmostSpecialL3Hyp 1 V (fsuV1 T V) L T (l32nH T V)) :
    HSType.IsZ4Cube ↥(pCoreOf 2 L) := by
  obtain ⟨hP, hcard⟩ := c.pCoreOf_eq hyp
  have hVe : V = conjClosure (fsuV1 T V) L := hyp.V_eq
  rw [hP] at hcard ⊢
  set X := conjClosure (centerOf (fsuU T V)) L
  obtain ⟨s₁, hs₁, hs₁z⟩ := c.exists_sq hVe z c.z_mem_V
  obtain ⟨s₂, hs₂, hs₂a⟩ := c.exists_sq hVe a c.a_mem_V
  obtain ⟨s₃, hs₃, hs₃b⟩ := c.exists_sq hVe b c.b_mem
  have h4 : ∀ (s v : G), s * s = v → v ∈ V → s ^ 4 = 1 := by
    intro s v hsv hv
    calc s ^ 4 = (s * s) * (s * s) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := by rw [hsv]; exact c.mul_self_V hv
  have hsq2 : ∀ (s v : G), s * s = v → ∀ n : ℕ, s ^ (2 * n) = v ^ n := by
    intro s v hsv n
    rw [pow_mul, pow_two, hsv]
  have hv2 : ∀ v ∈ V, v ^ 2 = 1 := fun v hv => by rw [pow_two]; exact c.mul_self_V hv
  refine isZ4Cube_of c.X_comm hs₁ hs₂ hs₃ (h4 _ _ hs₁z c.z_mem_V) (h4 _ _ hs₂a c.a_mem_V)
    (h4 _ _ hs₃b c.b_mem) (fun i j k hi hj hk h => ?_) hcard
  have hcomm : ∀ (i j : ℕ) (u w : G), u ∈ X → w ∈ X → u ^ i * w ^ j = w ^ j * u ^ i :=
    fun i j u w hu hw => c.X_comm _ (X.pow_mem hu i) _ (X.pow_mem hw j)
  have hsq : (s₁ ^ i * s₂ ^ j * s₃ ^ k) * (s₁ ^ i * s₂ ^ j * s₃ ^ k) =
      z ^ i * a ^ j * b ^ k := by
    have e1 : (s₁ ^ i * s₂ ^ j * s₃ ^ k) * (s₁ ^ i * s₂ ^ j * s₃ ^ k) =
        (s₁ ^ i * s₁ ^ i) * (s₂ ^ j * s₂ ^ j) * (s₃ ^ k * s₃ ^ k) := by
      have c1 := hcomm i j s₁ s₂ hs₁ hs₂
      have c2 := hcomm i k s₁ s₃ hs₁ hs₃
      have c3 := hcomm j k s₂ s₃ hs₂ hs₃
      calc (s₁ ^ i * s₂ ^ j * s₃ ^ k) * (s₁ ^ i * s₂ ^ j * s₃ ^ k)
          = s₁ ^ i * s₂ ^ j * (s₃ ^ k * s₁ ^ i) * s₂ ^ j * s₃ ^ k := by group
        _ = s₁ ^ i * s₂ ^ j * (s₁ ^ i * s₃ ^ k) * s₂ ^ j * s₃ ^ k := by rw [c2]
        _ = s₁ ^ i * (s₂ ^ j * s₁ ^ i) * (s₃ ^ k * s₂ ^ j) * s₃ ^ k := by group
        _ = s₁ ^ i * (s₁ ^ i * s₂ ^ j) * (s₂ ^ j * s₃ ^ k) * s₃ ^ k := by rw [c1, c3]
        _ = (s₁ ^ i * s₁ ^ i) * (s₂ ^ j * s₂ ^ j) * (s₃ ^ k * s₃ ^ k) := by group
    rw [e1, ← pow_add, ← pow_add, ← pow_add, ← two_mul, ← two_mul, ← two_mul, hsq2 _ _ hs₁z,
      hsq2 _ _ hs₂a, hsq2 _ _ hs₃b]
  have h1 : z ^ (i % 2) * a ^ (j % 2) * b ^ (k % 2) = 1 := by
    rw [← pow_eq_pow_mod_two (hv2 z c.z_mem_V), ← pow_eq_pow_mod_two (hv2 a c.a_mem_V),
      ← pow_eq_pow_mod_two (hv2 b c.b_mem), ← hsq, h, one_mul]
  obtain ⟨ei, ej, ek⟩ := c.indep (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
    (Nat.mod_lt _ (by norm_num)) h1
  obtain ⟨i', rfl⟩ : ∃ i', i = 2 * i' := ⟨i / 2, by omega⟩
  obtain ⟨j', rfl⟩ : ∃ j', j = 2 * j' := ⟨j / 2, by omega⟩
  obtain ⟨k', rfl⟩ : ∃ k', k = 2 * k' := ⟨k / 2, by omega⟩
  rw [hsq2 _ _ hs₁z, hsq2 _ _ hs₂a, hsq2 _ _ hs₃b] at h
  obtain ⟨e1, e2, e3⟩ := c.indep (by omega) (by omega) (by omega) h
  omega

theorem isXSectionIso₂ (hyp : AlmostSpecialL3Hyp 1 V (fsuV1 T V) L T (l32nH T V)) :
    IsXSectionIso₂ L (pCoreOf 2 L) V V ⊥ := by
  obtain ⟨hP, hcard⟩ := c.pCoreOf_eq hyp
  have hVe : V = conjClosure (fsuV1 T V) L := hyp.V_eq
  rw [hP] at hcard ⊢
  exact isXSectionIso₂_of_sq c.X_comm (c.V_le_X hVe) (fun v hv => c.mul_self_V hv)
    c.sq_mem_V_of_X (c.exists_sq hVe) (by rw [hcard, c.card_V])

end Ctx

end L14333

end CFSG.Quasithin.H13
