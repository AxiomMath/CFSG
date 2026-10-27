
module

public import CFSG.Quasithin.Vol2.KGFactC31RuImg
public import CFSG.Quasithin.Vol2.KGFactC31Std

public section

namespace CFSG.Quasithin.KGC31.Ru

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Sporadic.RuSchreier
  CFSG.Quasithin.KGC31

variable {A : Type} [Group A]

structure RuHyp (M₀ R M V : Subgroup A) : Prop where
  per : ⁅M₀, M₀⁆ = M₀
  pgrp : IsPGroup 2 ↥R
  RM : R ≤ M
  MN : M ≤ Subgroup.normalizer (M₀ : Set A)
  M₀R : M₀ ≤ Subgroup.normalizer (R : Set A)
  syl : IsSylowTwoOf R (CFSG.Quasithin.centralizerSection M M₀ (pCoreOf 2 M₀))
  VM₀ : V ≤ M₀
  Vne : V ≠ ⊥
  elem : IsElemAbelian 2 V
  comm : ⁅V, M₀⁆ = V
  Vc : V ≤ CFSG.Quasithin.centerOf (pCoreOf 2 (M₀ ⊔ R))
  NR : Subgroup.normalizer (R : Set A) ≤ M

namespace RuHyp

variable {M₀ R M V : Subgroup A} (h : RuHyp M₀ R M V)
include h

theorem facts [Finite A] : V ≤ pCoreOf 2 M₀ ∧ pCoreOf 2 M₀ ≤ R ∧
    R ≤ Subgroup.centralizer (V : Set A) ∧
      Subgroup.normalizer (R : Set A) ≤ Subgroup.normalizer (M₀ : Set A) :=
  orb_facts h.pgrp h.RM h.MN h.M₀R h.syl h.VM₀ h.elem h.comm h.Vc h.NR

theorem M₀V : M₀ ≤ Subgroup.normalizer (V : Set A) := le_normalizer_of_comm h.comm

theorem R_eq [Finite A] (hC : IsPGroup 2 ↥(Subgroup.centralizer (V : Set A))) :
    R = Subgroup.centralizer (V : Set A) :=
  eq_centralizer_of_isPGroup h.MN h.M₀V h.syl h.NR h.facts.2.2.1 hC

theorem V_comm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb => by
  have := h.elem.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
  simpa using congrArg Subtype.val this

theorem V_sq : ∀ a ∈ V, a * a = 1 := fun a ha => by
  have := h.elem.2 a ha
  rwa [sq] at this

end RuHyp

variable (e : G₀ ≃* A)

@[expose] def pb (X : Subgroup A) : Subgroup (Equiv.Perm (Fin 4060)) :=
  (X.comap e.toMonoidHom).map ruP.subtype

theorem pb_le (X : Subgroup A) : pb e X ≤ ruP := map_img_le e X

theorem img_pb (X : Subgroup A) : img e (pb e X) = X := (eq_img e X).symm

theorem mem_pb {X : Subgroup A} {g : Equiv.Perm (Fin 4060)} :
    g ∈ pb e X ↔ ∃ hg : g ∈ ruP, e ⟨g, hg⟩ ∈ X := by
  constructor
  · rintro ⟨g', hg', rfl⟩
    exact ⟨g'.2, hg'⟩
  · rintro ⟨hg, hX⟩
    exact ⟨⟨g, hg⟩, hX, rfl⟩

theorem apply_mem_iff_mem_pb {X : Subgroup A} {g : G₀} :
    e g ∈ X ↔ (g : Equiv.Perm (Fin 4060)) ∈ pb e X := by
  rw [mem_pb]
  exact ⟨fun h => ⟨g.2, h⟩, fun ⟨_, h⟩ => h⟩

theorem pb_img {Y : Subgroup (Equiv.Perm (Fin 4060))} (hY : Y ≤ ruP) : pb e (img e Y) = Y := by
  ext g
  rw [mem_pb]
  constructor
  · rintro ⟨hg, h⟩
    exact (apply_mem_img e).mp h
  · intro hg
    exact ⟨hY hg, (apply_mem_img e).mpr hg⟩

theorem pb_mono {X Y : Subgroup A} (h : X ≤ Y) : pb e X ≤ pb e Y :=
  Subgroup.map_mono (Subgroup.comap_mono h)

theorem le_iff_img_le {X : Subgroup A} {Y : Subgroup (Equiv.Perm (Fin 4060))} (hY : Y ≤ ruP) :
    img e Y ≤ X ↔ Y ≤ pb e X := by
  conv_lhs => rw [← img_pb e X]
  exact img_le_img_iff e hY

theorem img_le_iff_le_pb {X : Subgroup A} {Y : Subgroup (Equiv.Perm (Fin 4060))} :
    X ≤ img e Y ↔ pb e X ≤ Y := by
  constructor
  · intro h g hg
    obtain ⟨hgP, hX⟩ := (mem_pb e).mp hg
    exact (apply_mem_img e).mp (h hX)
  · intro h a ha
    rw [mem_img]
    exact h ((apply_mem_iff_mem_pb e).mp (by simpa using ha))

theorem pb_eq_iff {X : Subgroup A} {Y : Subgroup (Equiv.Perm (Fin 4060))} (hY : Y ≤ ruP) :
    X = img e Y ↔ pb e X = Y := by
  constructor
  · rintro rfl
    exact pb_img e hY
  · rintro rfl
    exact (img_pb e X).symm

theorem pb_centralizer (X : Subgroup A) :
    pb e (Subgroup.centralizer (X : Set A)) =
      ruP ⊓ Subgroup.centralizer (pb e X : Set (Equiv.Perm (Fin 4060))) := by
  conv_lhs => rw [← img_pb e X]
  rw [centralizer_img e (pb_le e X), pb_img e inf_le_left]

theorem pb_normalizer (X : Subgroup A) :
    pb e (Subgroup.normalizer (X : Set A)) =
      ruP ⊓ Subgroup.normalizer (pb e X : Set (Equiv.Perm (Fin 4060))) := by
  conv_lhs => rw [← img_pb e X]
  rw [normalizer_img e (pb_le e X), pb_img e inf_le_left]

theorem pb_inf (X Y : Subgroup A) : pb e (X ⊓ Y) = pb e X ⊓ pb e Y := by
  ext g
  simp only [Subgroup.mem_inf, mem_pb]
  constructor
  · rintro ⟨hg, h1, h2⟩
    exact ⟨⟨hg, h1⟩, ⟨hg, h2⟩⟩
  · rintro ⟨⟨hg, h1⟩, ⟨hg', h2⟩⟩
    exact ⟨hg, h1, h2⟩

theorem card_pb (X : Subgroup A) : Nat.card (pb e X) = Nat.card X := by
  conv_rhs => rw [← img_pb e X]
  rw [card_img e (pb_le e X)]

theorem pb_commutator (X Y : Subgroup A) : pb e ⁅X, Y⁆ = ⁅pb e X, pb e Y⁆ := by
  have hφ : ∀ Z : Subgroup A, pb e Z = (Z.map e.symm.toMonoidHom).map ruP.subtype := by
    intro Z
    rw [pb, Subgroup.comap_equiv_eq_map_symm']
  rw [hφ, hφ, hφ, Subgroup.map_commutator, Subgroup.map_commutator]

theorem pb_perfect {X : Subgroup A} (h : ⁅X, X⁆ = X) : ⁅pb e X, pb e X⁆ = pb e X := by
  rw [← pb_commutator, h]

theorem pb_ne_bot {X : Subgroup A} (h : X ≠ ⊥) : pb e X ≠ ⊥ := by
  intro h'
  apply h
  rw [← img_pb e X, h', img, Subgroup.bot_subgroupOf, Subgroup.map_bot]

theorem isPGroup_pb {X : Subgroup A} (h : IsPGroup 2 ↥X) : IsPGroup 2 ↥(pb e X) := by
  have hm := h.map e.symm.toMonoidHom
  have hm2 := hm.map ruP.subtype
  rw [Subgroup.map_map] at hm2
  rw [pb, Subgroup.comap_equiv_eq_map_symm', Subgroup.map_map]
  exact hm2

theorem isPGroup_of_pb {X : Subgroup A} (h : IsPGroup 2 ↥(pb e X)) : IsPGroup 2 ↥X := by
  rw [← img_pb e X, img]
  exact (h.of_equiv (Subgroup.subgroupOfEquivOfLe (pb_le e X)).symm).map e.toMonoidHom

theorem conj_mem_pb {X Y : Subgroup A} (hXY : X ≤ Subgroup.normalizer (Y : Set A))
    {x y : Equiv.Perm (Fin 4060)} (hx : x ∈ pb e X) (hy : y ∈ pb e Y) : x * y * x⁻¹ ∈ pb e Y := by
  obtain ⟨hxP, hxX⟩ := (mem_pb e).mp hx
  obtain ⟨hyP, hyY⟩ := (mem_pb e).mp hy
  rw [mem_pb]
  refine ⟨ruP.mul_mem (ruP.mul_mem hxP hyP) (ruP.inv_mem hxP), ?_⟩
  have := (Subgroup.mem_normalizer_iff.mp (hXY hxX) _).mp hyY
  rw [← map_inv, ← map_mul, ← map_mul] at this
  exact this

theorem pb_le_normalizer {X Y : Subgroup A} (hXY : X ≤ Subgroup.normalizer (Y : Set A)) :
    pb e X ≤ Subgroup.normalizer (pb e Y : Set (Equiv.Perm (Fin 4060))) :=
  fun _ hx => mem_normalizer_of_conj_le fun _ hy => conj_mem_pb e hXY hx hy

section Orbit

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem card_quot_le_of_conj_mem (H : Subgroup G) (x : G) {T : Set G} (hT : T.Finite)
    (h : ∀ g ∈ H, g * x * g⁻¹ ∈ T) :
    Nat.card (↥H ⧸ (H ⊓ Subgroup.centralizer {x}).subgroupOf H) ≤ T.ncard := by
  set C := (H ⊓ Subgroup.centralizer {x}).subgroupOf H
  let f : ↥H ⧸ C → T := Quotient.lift (fun g : ↥H => (⟨(g : G) * x * (g : G)⁻¹, h g g.2⟩ : T))
    (fun a b hab => by
      have hab' := QuotientGroup.leftRel_apply.mp hab
      rw [Subgroup.mem_subgroupOf] at hab'
      have hc := Subgroup.mem_centralizer_singleton_iff.mp hab'.2
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hc ⊢
      calc (a : G) * x * (a : G)⁻¹ = a * ((a : G)⁻¹ * b * x) * (b : G)⁻¹ := by rw [hc]; group
        _ = b * x * (b : G)⁻¹ := by group)
  have hf : Function.Injective f := by
    intro q₁ q₂ hq
    induction q₁ using QuotientGroup.induction_on with
    | H a =>
      induction q₂ using QuotientGroup.induction_on with
      | H b =>
        have h1 := congrArg Subtype.val hq
        change (a : G) * x * (a : G)⁻¹ = b * x * (b : G)⁻¹ at h1
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        refine ⟨H.mul_mem (H.inv_mem a.2) b.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        calc (a : G)⁻¹ * b * x = (a : G)⁻¹ * (b * x * (b : G)⁻¹) * b := by group
          _ = (a : G)⁻¹ * (a * x * (a : G)⁻¹) * b := by rw [h1]
          _ = x * ((a : G)⁻¹ * b) := by group
  have : Finite T := hT.to_subtype
  calc Nat.card (↥H ⧸ C) ≤ Nat.card T := Nat.card_le_card_of_injective f hf
    _ = T.ncard := (Nat.card_coe_set_eq T)

omit [Finite G] in
theorem card_le_of_conj_mem (H : Subgroup G) (x : G) {T : Set G} (hT : T.Finite)
    (h : ∀ g ∈ H, g * x * g⁻¹ ∈ T) :
    Nat.card H ≤ T.ncard * Nat.card ↥(H ⊓ Subgroup.centralizer {x}) := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((H ⊓ Subgroup.centralizer {x}).subgroupOf H)
  rw [card_subgroupOf_of_le inf_le_left] at h1
  rw [h1]
  exact Nat.mul_le_mul_right _ (card_quot_le_of_conj_mem H x hT h)

theorem dvd_card_of_conj_eq (H : Subgroup G) (x : G) {T : Set G}
    (hT : T = {y | ∃ g ∈ H, g * x * g⁻¹ = y}) : T.ncard ∣ Nat.card H := by
  set C := (H ⊓ Subgroup.centralizer {x}).subgroupOf H
  have hTf : T.Finite := Set.toFinite T
  let f : ↥H ⧸ C → T := Quotient.lift (fun g : ↥H => (⟨(g : G) * x * (g : G)⁻¹,
      hT ▸ ⟨g, g.2, rfl⟩⟩ : T))
    (fun a b hab => by
      have hab' := QuotientGroup.leftRel_apply.mp hab
      rw [Subgroup.mem_subgroupOf] at hab'
      have hc := Subgroup.mem_centralizer_singleton_iff.mp hab'.2
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hc ⊢
      calc (a : G) * x * (a : G)⁻¹ = a * ((a : G)⁻¹ * b * x) * (b : G)⁻¹ := by rw [hc]; group
        _ = b * x * (b : G)⁻¹ := by group)
  have hf : Function.Bijective f := by
    refine ⟨fun q₁ q₂ hq => ?_, fun t => ?_⟩
    · induction q₁ using QuotientGroup.induction_on with
      | H a =>
        induction q₂ using QuotientGroup.induction_on with
        | H b =>
          have h1 := congrArg Subtype.val hq
          change (a : G) * x * (a : G)⁻¹ = b * x * (b : G)⁻¹ at h1
          rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
          refine ⟨H.mul_mem (H.inv_mem a.2) b.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          calc (a : G)⁻¹ * b * x = (a : G)⁻¹ * (b * x * (b : G)⁻¹) * b := by group
            _ = (a : G)⁻¹ * (a * x * (a : G)⁻¹) * b := by rw [h1]
            _ = x * ((a : G)⁻¹ * b) := by group
    · obtain ⟨t, ht⟩ := t
      have ht' := ht
      rw [hT] at ht'
      obtain ⟨g, hg, rfl⟩ := ht'
      exact ⟨QuotientGroup.mk ⟨g, hg⟩, rfl⟩
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup C
  have h2 : Nat.card (↥H ⧸ C) = T.ncard := by
    rw [Nat.card_congr (Equiv.ofBijective f hf), Nat.card_coe_set_eq]
  rw [h1, h2]
  exact Dvd.intro _ rfl

end Orbit

theorem conj_mem_normalizer_of_map {G : Type*} [Group G] {H K : Subgroup G} {k : G}
    (h : H.map (MulAut.conj k).toMonoidHom = K) {x : G}
    (hx : x ∈ Subgroup.normalizer (K : Set G)) :
    k⁻¹ * x * k ∈ Subgroup.normalizer (H : Set G) := by
  have hiff : ∀ u, u ∈ H ↔ k * u * k⁻¹ ∈ K := by
    intro u
    rw [← h]
    constructor
    · intro hu
      exact ⟨u, hu, rfl⟩
    · rintro ⟨u', hu', he⟩
      have : u' = u := by
        have he' : k * u' * k⁻¹ = k * u * k⁻¹ := he
        simpa using he'
      rwa [← this]
  rw [Subgroup.mem_normalizer_iff]
  intro u
  rw [hiff, hiff, (Subgroup.mem_normalizer_iff.mp hx (k * u * k⁻¹))]
  constructor <;> intro hm <;> convert hm using 1 <;> group

theorem exists_conj_std {M₀ : Subgroup A} {N₀ : Subgroup (Equiv.Perm (Fin 4060))}
    (hN₀ : N₀ ≤ ruP) {x : Equiv.Perm (Fin 4060)} (hxN : x ∈ N₀) {p : ℕ} [Fact p.Prime]
    (hx : orderOf x = p) (hp2 : ¬ p ^ 2 ∣ Nat.card N₀) {y : G₀}
    (hyN : (y : Equiv.Perm (Fin 4060)) ∈ N₀) (hy : ∃ k : ℕ, y ^ p ^ k = 1) (hy1 : y ≠ 1)
    (hyM : e y ∈ M₀) :
    ∃ n : G₀, (n : Equiv.Perm (Fin 4060)) ∈ N₀ ∧ conjE e n⁻¹ ⟨x, hN₀ hxN⟩ ∈ M₀ := by
  have hy' : ∃ k : ℕ, (y : Equiv.Perm (Fin 4060)) ^ p ^ k = 1 := by
    obtain ⟨k, hk⟩ := hy
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hy1' : (y : Equiv.Perm (Fin 4060)) ≠ 1 := fun h => hy1 (Subtype.ext h)
  obtain ⟨n, hn, -, hxz⟩ := exists_conj_zpowers hxN hx hp2 hyN hy' hy1'
  refine ⟨⟨n, hN₀ hn⟩, hn, ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxz
  rw [conjE_apply]
  have e1 : (⟨n, hN₀ hn⟩ : G₀)⁻¹ * ⟨x, hN₀ hxN⟩ * (⟨n, hN₀ hn⟩ : G₀)⁻¹⁻¹ = y ^ k := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv, Subgroup.coe_zpow]
    rw [← hk, conj_zpow]
    group
  rw [e1, map_zpow]
  exact M₀.zpow_mem hyM k

end CFSG.Quasithin.KGC31.Ru

end
