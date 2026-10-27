module

public import CFSG.Quasithin.Vol2.Ch12Sec4G2OffTwo

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin Orbit
open scoped Pointwise

@[expose] def OffenderClaim {M : Type} [CommGroup M] (Ĝ : Subgroup (MulAut M)) : Prop :=
  ∀ B : Subgroup (MulAut M), B ≤ Ĝ → B ≠ ⊥ → IsElemAbelian2 B →
    Nat.card M ≤ Nat.card B * Nat.card (fixV B) → commV B = fixV B

theorem claim_transport {M M' : Type} [CommGroup M] [CommGroup M'] (e : M ≃* M')
    {Ĝ : Subgroup (MulAut M)} {Ĝ' : Subgroup (MulAut M')}
    (hG : ∀ x ∈ Ĝ, MulAut.congr e x ∈ Ĝ') (h' : OffenderClaim Ĝ') : OffenderClaim Ĝ := by
  intro B hB hne hea hff
  have hinj : Function.Injective (MulAut.congr e).toMonoidHom := (MulAut.congr e).injective
  have hle : B.map (MulAut.congr e).toMonoidHom ≤ Ĝ' := by
    rintro _ ⟨b, hb, rfl⟩
    exact hG b (hB hb)
  have hne' : B.map (MulAut.congr e).toMonoidHom ≠ ⊥ := fun h =>
    hne ((Subgroup.map_eq_bot_iff_of_injective _ hinj).1 h)
  have hff' : Nat.card M' ≤ Nat.card (B.map (MulAut.congr e).toMonoidHom) *
      Nat.card (fixV (B.map (MulAut.congr e).toMonoidHom)) := by
    rw [Subgroup.card_map_of_injective hinj, fixV_map_congr,
      Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective, ← Nat.card_congr e.toEquiv]
    exact hff
  have h := h' _ hle hne' (isElemAbelian2_map_congr e hea) hff'
  rw [commV_map_congr, fixV_map_congr] at h
  exact Subgroup.map_injective (f := e.toMonoidHom) e.injective h

theorem congr_eq_conj {M : Type} [CommGroup M] (x a : MulAut M) :
    MulAut.congr x a = x * a * x⁻¹ := by
  ext m
  rfl

section Two

theorem claim_of_sylow {M : Type} [CommGroup M] (ρ : ↥(quasithinG2 (ZMod 2)) →* MulAut M)
    (hρ : Function.Injective ρ)
    (hS : ∀ B : Subgroup ↥(quasithinG2 (ZMod 2)), B ≤ sSubG → B ≠ ⊥ →
      (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) → (∀ b ∈ B, b ^ 2 = 1) →
      Nat.card M ≤ Nat.card B * Nat.card (fixV (B.map ρ)) → commV (B.map ρ) = fixV (B.map ρ)) :
    OffenderClaim ρ.range := by
  intro Bh hle hne hea hff
  set B₀ := Bh.comap ρ with hB₀def
  have hB₀ : B₀.map ρ = Bh := Subgroup.map_comap_eq_self hle
  have hc : ∀ a ∈ B₀, ∀ b ∈ B₀, a * b = b * a := fun a ha b hb =>
    hρ (by rw [map_mul, map_mul]; exact hea.1 _ ha _ hb)
  have h2 : ∀ b ∈ B₀, b ^ 2 = 1 := fun b hb => hρ (by rw [map_pow, map_one]; exact hea.2 _ hb)
  have hp : IsPGroup 2 ↥B₀ := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (h2 g.1 g.2)⟩
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥(quasithinG2 (ZMod 2)) P sylowSub
  set c := (MulAut.conj g).toMonoidHom with hcdef
  have hcinj : Function.Injective c := (MulAut.conj g).injective
  set B₁ := B₀.map c with hB₁def
  have hB₁S : B₁ ≤ sSubG := by
    rintro _ ⟨b, hb, rfl⟩
    have h1 : MulAut.conj g • b ∈ MulAut.conj g • (P : Subgroup ↥(quasithinG2 (ZMod 2))) :=
      Subgroup.smul_mem_pointwise_smul _ _ _ (hP hb)
    rw [← Sylow.coe_subgroup_smul, hg] at h1
    exact h1
  have hB₁ne : B₁ ≠ ⊥ := by
    intro h
    apply hne
    rw [← hB₀, (Subgroup.map_eq_bot_iff_of_injective _ hcinj).1 h, Subgroup.map_bot]
  have hB₁c : ∀ a ∈ B₁, ∀ b ∈ B₁, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hc a ha b hb]
  have hB₁2 : ∀ b ∈ B₁, b ^ 2 = 1 := by
    rintro _ ⟨b, hb, rfl⟩
    rw [← map_pow, h2 b hb, map_one]
  have hmap : B₁.map ρ = Bh.map (MulAut.congr (ρ g)).toMonoidHom := by
    rw [← hB₀, Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext b m
    change ρ (g * b * g⁻¹) m = MulAut.congr (ρ g) (ρ b) m
    rw [congr_eq_conj, map_mul, map_mul, map_inv]
  have hcardB : Nat.card B₁ = Nat.card Bh := by
    rw [hB₁def, Subgroup.card_map_of_injective hcinj, ← hB₀, Subgroup.card_map_of_injective hρ]
  have hfix : Nat.card (fixV (B₁.map ρ)) = Nat.card (fixV Bh) := by
    rw [hmap, fixV_map_congr,
      Subgroup.card_map_of_injective (f := (ρ g).toMonoidHom) (ρ g).injective]
  have h := hS B₁ hB₁S hB₁ne hB₁c hB₁2 (by rw [hcardB, hfix]; exact hff)
  rw [hmap, commV_map_congr, fixV_map_congr] at h
  exact Subgroup.map_injective (f := (ρ g).toMonoidHom) (ρ g).injective h

theorem offenderClaim_two_O : OffenderClaim (g2OAct (ZMod 2)).range :=
  claim_of_sylow _ g2OAct_injective fun B hB hne hc h2 hff =>
    offender_sylow_O hB hne hc h2 (by rw [← card_eq_idx hB, ← card_ModO]; exact hff)

theorem offenderClaim_two_Q : OffenderClaim (g2QAct (ZMod 2)).range :=
  claim_of_sylow _ g2QAct_injective fun B hB hne hc h2 hff =>
    offender_sylow_Q hB hne hc h2 (by rw [← card_eq_idx hB, ← card_ModQ]; exact hff)

end Two

section Field

variable {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)

@[expose] noncomputable def twoEquiv : ZMod 2 ≃+* K :=
  RingEquiv.ofBijective (castTwo hK) (castTwo_bijective hK)

@[expose] noncomputable def zornEquivK : quasithinZorn (ZMod 2) ≃+ quasithinZorn K where
  toFun := zornMap (twoEquiv hK).toRingHom
  invFun := zornMap (twoEquiv hK).symm.toRingHom
  left_inv x := by
    apply zorn_ext <;> (try intro i) <;> simp [zornMap]
  right_inv x := by
    apply zorn_ext <;> (try intro i) <;> simp [zornMap]
  map_add' x y := by
    apply zorn_ext <;> (try intro i) <;> simp [zornMap]

omit [Finite K] [CharP K 2] in
theorem zornEquivK_apply (x : quasithinZorn (ZMod 2)) :
    zornEquivK hK x = zornMap (twoEquiv hK).toRingHom x := rfl

omit [Finite K] [CharP K 2] in
theorem zornEquivK_mul (x y : quasithinZorn (ZMod 2)) :
    zornEquivK hK (quasithinZornMul x y) =
      quasithinZornMul (zornEquivK hK x) (zornEquivK hK y) := by
  simp only [zornEquivK_apply]
  apply zorn_ext <;> (try intro i) <;> (try fin_cases i) <;>
    simp [zornMap, quasithinZornMul, quasithinCross, Fin.sum_univ_three]

omit [Finite K] [CharP K 2] in
theorem zornEquivK_symm_mul (x y : quasithinZorn K) :
    (zornEquivK hK).symm (quasithinZornMul x y) =
      quasithinZornMul ((zornEquivK hK).symm x) ((zornEquivK hK).symm y) := by
  apply (zornEquivK hK).injective
  rw [zornEquivK_mul, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
    AddEquiv.apply_symm_apply]

@[expose] noncomputable def conjF2 (g : quasithinZorn K ≃ₗ[K] quasithinZorn K) :
    quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] quasithinZorn (ZMod 2) where
  toFun x := (zornEquivK hK).symm (g (zornEquivK hK x))
  invFun x := (zornEquivK hK).symm (g.symm (zornEquivK hK x))
  map_add' x y := by simp
  map_smul' t x := by
    have ht : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide
    rcases ht t with rfl | rfl
    · simp
    · simp
  left_inv x := by simp
  right_inv x := by simp

omit [Finite K] [CharP K 2] in
theorem conjF2_apply (g : quasithinZorn K ≃ₗ[K] quasithinZorn K) (x : quasithinZorn (ZMod 2)) :
    conjF2 hK g x = (zornEquivK hK).symm (g (zornEquivK hK x)) := rfl

omit [Finite K] [CharP K 2] in
theorem conjF2_mem {g : quasithinZorn K ≃ₗ[K] quasithinZorn K} (hg : g ∈ quasithinG2 K) :
    conjF2 hK g ∈ quasithinG2 (ZMod 2) := by
  have hz := mem_quasithinG2_isZornAuto hg
  refine mem_quasithinG2 fun x y => ?_
  rw [conjF2_apply, conjF2_apply, conjF2_apply, zornEquivK_mul, hz, zornEquivK_symm_mul]

omit [Finite K] [CharP K 2] in
theorem map_zornO0_K :
    (zornO0 (ZMod 2)).map (zornEquivK hK).toMultiplicative.toMonoidHom = zornO0 K := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change (zornMap (twoEquiv hK).toRingHom (Multiplicative.toAdd x)).1 +
      (zornMap (twoEquiv hK).toRingHom (Multiplicative.toAdd x)).2.2.2 = 0
    simp only [zornMap]
    rw [← map_add]
    have hx' : (Multiplicative.toAdd x).1 + (Multiplicative.toAdd x).2.2.2 = 0 := hx
    rw [hx', map_zero]
  · intro hy
    refine ⟨Multiplicative.ofAdd ((zornEquivK hK).symm (Multiplicative.toAdd y)), ?_, ?_⟩
    · change ((zornEquivK hK).symm (Multiplicative.toAdd y)).1 +
        ((zornEquivK hK).symm (Multiplicative.toAdd y)).2.2.2 = 0
      have hy' : (Multiplicative.toAdd y).1 + (Multiplicative.toAdd y).2.2.2 = 0 := hy
      change (zornMap (twoEquiv hK).symm.toRingHom (Multiplicative.toAdd y)).1 +
        (zornMap (twoEquiv hK).symm.toRingHom (Multiplicative.toAdd y)).2.2.2 = 0
      simp only [zornMap]
      rw [← map_add, hy', map_zero]
    · change Multiplicative.ofAdd (zornEquivK hK ((zornEquivK hK).symm
        (Multiplicative.toAdd y))) = y
      rw [AddEquiv.apply_symm_apply, ofAdd_toAdd]

omit [Finite K] [CharP K 2] in
theorem map_zornR_K :
    (zornR (ZMod 2)).map (zornEquivK hK).toMultiplicative.toMonoidHom = zornR K := by
  ext y
  constructor
  · rintro ⟨x, ⟨t, ht⟩, rfl⟩
    refine ⟨twoEquiv hK t, ?_⟩
    change zornMap (twoEquiv hK).toRingHom (Multiplicative.toAdd x) = _
    rw [ht]
    apply zorn_ext <;> (try intro i) <;> simp [zornMap]
  · rintro ⟨t, ht⟩
    refine ⟨Multiplicative.ofAdd ((twoEquiv hK).symm t, 0, 0, (twoEquiv hK).symm t),
      ⟨(twoEquiv hK).symm t, rfl⟩, ?_⟩
    change Multiplicative.ofAdd (zornMap (twoEquiv hK).toRingHom _) = y
    apply Multiplicative.toAdd.injective
    rw [toAdd_ofAdd, ht]
    apply zorn_ext <;> (try intro i) <;> simp [zornMap]

@[expose] noncomputable def secEquivK : ↥(zornO0 (ZMod 2)) ≃* ↥(zornO0 K) :=
  ((zornEquivK hK).toMultiplicative.subgroupMap (zornO0 (ZMod 2))).trans
    (MulEquiv.subgroupCongr (map_zornO0_K hK))

@[expose] noncomputable def modOEquivK :
    (zornO0Model (quasithinG2 (ZMod 2))).Mod ≃* (zornO0Model (quasithinG2 K)).Mod :=
  QuotientGroup.congr _ _ (secEquivK hK) (by
    change ((⊥ : Subgroup (Multiplicative (quasithinZorn (ZMod 2)))).subgroupOf
        (zornO0 (ZMod 2))).map _ =
      (⊥ : Subgroup (Multiplicative (quasithinZorn K))).subgroupOf (zornO0 K)
    rw [Subgroup.bot_subgroupOf, Subgroup.bot_subgroupOf]
    exact Subgroup.map_bot _)

@[expose] noncomputable def modQEquivK :
    (FFModel.zornQ (quasithinG2 (ZMod 2))).Mod ≃* (FFModel.zornQ (quasithinG2 K)).Mod :=
  QuotientGroup.congr _ _ (secEquivK hK) (by
    ext m
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨x, hx, rfl⟩
      change ((secEquivK hK x : ↥(zornO0 K)) : Multiplicative (quasithinZorn K)) ∈ zornR K
      rw [← map_zornR_K hK]
      exact ⟨_, hx, rfl⟩
    · intro hm
      have hm' : (m.1 : Multiplicative (quasithinZorn K)) ∈
          (zornR (ZMod 2)).map (zornEquivK hK).toMultiplicative.toMonoidHom := by
        rw [map_zornR_K hK]
        exact hm
      obtain ⟨x, hx, hxm⟩ := hm'
      have hx0 : x ∈ zornO0 (ZMod 2) := zornR_le_zornO0 hx
      exact ⟨⟨x, hx0⟩, hx, Subtype.ext hxm⟩)

omit [Finite K] in
theorem modOEquivK_act (g : ↥(quasithinG2 K)) (v : (zornO0Model (quasithinG2 (ZMod 2))).Mod) :
    modOEquivK hK (g2OAct (ZMod 2) ⟨conjF2 hK g.1, conjF2_mem hK g.2⟩ v) =
      g2OAct K g (modOEquivK hK v) := by
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective v
  change (QuotientGroup.mk _ : (zornO0Model (quasithinG2 K)).Mod) = QuotientGroup.mk _
  congr 1
  apply Subtype.ext
  change Multiplicative.ofAdd (zornEquivK hK ((zornEquivK hK).symm (g.1 (zornEquivK hK
      (Multiplicative.toAdd m.1))))) =
    Multiplicative.ofAdd (g.1 (zornEquivK hK
      (Multiplicative.toAdd m.1)))
  rw [AddEquiv.apply_symm_apply]

omit [Finite K] in
theorem modQEquivK_act (g : ↥(quasithinG2 K)) (v : (FFModel.zornQ (quasithinG2 (ZMod 2))).Mod) :
    modQEquivK hK (g2QAct (ZMod 2) ⟨conjF2 hK g.1, conjF2_mem hK g.2⟩ v) =
      g2QAct K g (modQEquivK hK v) := by
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective v
  change (QuotientGroup.mk _ : (FFModel.zornQ (quasithinG2 K)).Mod) = QuotientGroup.mk _
  congr 1
  apply Subtype.ext
  change Multiplicative.ofAdd (zornEquivK hK ((zornEquivK hK).symm (g.1 (zornEquivK hK
      (Multiplicative.toAdd m.1))))) =
    Multiplicative.ofAdd (g.1 (zornEquivK hK
      (Multiplicative.toAdd m.1)))
  rw [AddEquiv.apply_symm_apply]

omit [Finite K] in
theorem congr_modOEquivK_symm (g : ↥(quasithinG2 K)) :
    MulAut.congr (modOEquivK hK).symm (g2OAct K g) =
      g2OAct (ZMod 2) ⟨conjF2 hK g.1, conjF2_mem hK g.2⟩ := by
  ext v
  obtain ⟨u, rfl⟩ := (modOEquivK hK).symm.surjective v
  apply (modOEquivK hK).injective
  rw [congr_apply_eq, MulEquiv.apply_symm_apply, modOEquivK_act, MulEquiv.apply_symm_apply]

omit [Finite K] in
theorem congr_modQEquivK_symm (g : ↥(quasithinG2 K)) :
    MulAut.congr (modQEquivK hK).symm (g2QAct K g) =
      g2QAct (ZMod 2) ⟨conjF2 hK g.1, conjF2_mem hK g.2⟩ := by
  ext v
  obtain ⟨u, rfl⟩ := (modQEquivK hK).symm.surjective v
  apply (modQEquivK hK).injective
  rw [congr_apply_eq, MulEquiv.apply_symm_apply, modQEquivK_act, MulEquiv.apply_symm_apply]

end Field

theorem g2OffenderZorn : G2OffenderZorn := by
  intro K _ _ _ hK
  constructor
  · intro B hB hne hea hff
    refine claim_transport (modQEquivK hK).symm (Ĝ' := (g2QAct (ZMod 2)).range)
      (fun x hx => ?_) offenderClaim_two_Q B hB hne hea hff
    obtain ⟨g, rfl⟩ := hx
    exact ⟨_, (congr_modQEquivK_symm hK g).symm⟩
  · intro B hB hne hea hff
    refine claim_transport (modOEquivK hK).symm (Ĝ' := (g2OAct (ZMod 2)).range)
      (fun x hx => ?_) offenderClaim_two_O B hB hne hea hff
    obtain ⟨g, rfl⟩ := hx
    exact ⟨_, (congr_modOEquivK_symm hK g).symm⟩

end CFSG.Quasithin.H13
