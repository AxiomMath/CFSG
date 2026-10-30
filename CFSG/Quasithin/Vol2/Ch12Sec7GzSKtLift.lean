module

public import CFSG.Quasithin.Vol2.Ch12Sec7GzDefs

public section

namespace CFSG.Quasithin.H13.I1277

open CFSG.Open CFSG.Quasithin S127 S127.I77

@[expose] def KtSInv : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsPSL 3 2 2 S →
    ∀ a b : S, a ^ 2 = 1 → a ≠ 1 → b ^ 2 = 1 → b ≠ 1 → ∃ g : S, g * a * g⁻¹ = b

@[expose] def KtS16 : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsPSL 3 2 2 S →
    ∀ A : Subgroup S, IsElemAbelian 2 A → Nat.card ↥A = 16 →
      ∃ B : Subgroup S, IsElemAbelian 2 B ∧ Nat.card ↥B = 16 ∧ Nat.card ↥(B ⊓ A) = 4 ∧
        B ≤ Subgroup.normalizer (A : Set S) ∧
        ∃ k : Fin 5 → S, k 0 = 1 ∧ (∀ i, k i ∈ Subgroup.normalizer (B : Set S)) ∧
          ∀ i j, i ≠ j → ∀ x ∈ B, (∃ a ∈ A, x = k i * a * (k i)⁻¹) →
            (∃ a ∈ A, x = k j * a * (k j)⁻¹) → x = 1

section Lift

variable {G : Type} [Group G] [Finite G]

@[expose] def ktLiftG (K : Subgroup G) (B : Subgroup (↥K ⧸ Subgroup.center ↥K)) : Subgroup G :=
  (B.comap (QuotientGroup.mk' (Subgroup.center ↥K))).map K.subtype

@[expose] def ktQuotSub (K V : Subgroup G) : Subgroup (↥K ⧸ Subgroup.center ↥K) :=
  (V.subgroupOf K).map (QuotientGroup.mk' (Subgroup.center ↥K))

theorem ktLiftG_le (K : Subgroup G) (B : Subgroup (↥K ⧸ Subgroup.center ↥K)) :
    ktLiftG K B ≤ K :=
  Subgroup.map_subtype_le _

theorem mem_ktLiftG {K : Subgroup G} {B : Subgroup (↥K ⧸ Subgroup.center ↥K)} {x : G}
    (hx : x ∈ K) :
    x ∈ ktLiftG K B ↔ QuotientGroup.mk' (Subgroup.center ↥K) ⟨x, hx⟩ ∈ B := by
  unfold ktLiftG
  constructor
  · intro h
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp h
    have hy' : y = ⟨x, hx⟩ := Subtype.ext hyx
    subst hy'
    exact Subgroup.mem_comap.mp hy
  · intro h
    exact Subgroup.mem_map.mpr ⟨⟨x, hx⟩, Subgroup.mem_comap.mpr h, rfl⟩

theorem ktLiftG_inf (K : Subgroup G) (B C : Subgroup (↥K ⧸ Subgroup.center ↥K)) :
    ktLiftG K (B ⊓ C) = ktLiftG K B ⊓ ktLiftG K C := by
  unfold ktLiftG
  rw [Subgroup.comap_inf, Subgroup.map_inf_eq _ _ _ K.subtype_injective]

theorem card_ktComap (K : Subgroup G) (B : Subgroup (↥K ⧸ Subgroup.center ↥K)) :
    Nat.card ↥(B.comap (QuotientGroup.mk' (Subgroup.center ↥K))) =
      Nat.card ↥B * Nat.card ↥(Subgroup.center ↥K) := by
  have hsurj : Function.Surjective (QuotientGroup.mk' (Subgroup.center ↥K)) :=
    QuotientGroup.mk'_surjective _
  have h1 : (B.comap (QuotientGroup.mk' (Subgroup.center ↥K))).index = B.index :=
    Subgroup.index_comap_of_surjective (H := B) hsurj
  have h2 := Subgroup.index_mul_card (H := B.comap (QuotientGroup.mk' (Subgroup.center ↥K)))
  have h3 := Subgroup.index_mul_card (H := B)
  have h4 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥K)
  have hpos : 0 < B.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := B))
  apply Nat.eq_of_mul_eq_mul_left hpos
  calc B.index * Nat.card ↥(B.comap (QuotientGroup.mk' (Subgroup.center ↥K)))
      = (B.comap (QuotientGroup.mk' (Subgroup.center ↥K))).index *
          Nat.card ↥(B.comap (QuotientGroup.mk' (Subgroup.center ↥K))) := by rw [h1]
    _ = Nat.card ↥K := h2
    _ = Nat.card (↥K ⧸ Subgroup.center ↥K) * Nat.card ↥(Subgroup.center ↥K) := h4
    _ = (B.index * Nat.card ↥B) * Nat.card ↥(Subgroup.center ↥K) := by rw [h3]
    _ = B.index * (Nat.card ↥B * Nat.card ↥(Subgroup.center ↥K)) := by ring

theorem card_ktLiftG (K : Subgroup G) (B : Subgroup (↥K ⧸ Subgroup.center ↥K)) :
    Nat.card ↥(ktLiftG K B) = Nat.card ↥B * Nat.card ↥(Subgroup.center ↥K) := by
  unfold ktLiftG
  rw [Subgroup.card_map_of_injective K.subtype_injective, card_ktComap]

theorem ktQuotSub_comap {K V : Subgroup G} (hZV : (Subgroup.center ↥K).map K.subtype ≤ V) :
    (ktQuotSub K V).comap (QuotientGroup.mk' (Subgroup.center ↥K)) = V.subgroupOf K := by
  unfold ktQuotSub
  rw [QuotientGroup.comap_map_mk', sup_eq_right]
  intro y hy
  rw [Subgroup.mem_subgroupOf]
  exact hZV (Subgroup.mem_map.mpr ⟨y, hy, rfl⟩)

theorem mem_ktQuotSub {K V : Subgroup G} (hZV : (Subgroup.center ↥K).map K.subtype ≤ V)
    {x : G} (hx : x ∈ K) :
    QuotientGroup.mk' (Subgroup.center ↥K) ⟨x, hx⟩ ∈ ktQuotSub K V ↔ x ∈ V := by
  have h := (Subgroup.mem_comap (f := QuotientGroup.mk' (Subgroup.center ↥K))
    (K := ktQuotSub K V) (x := ⟨x, hx⟩)).symm
  rw [ktQuotSub_comap hZV] at h
  exact h.trans Subgroup.mem_subgroupOf

theorem card_ktQuotSub {K V : Subgroup G} (hVK : V ≤ K)
    (hZV : (Subgroup.center ↥K).map K.subtype ≤ V) :
    Nat.card ↥(ktQuotSub K V) * Nat.card ↥(Subgroup.center ↥K) = Nat.card ↥V := by
  have h := card_ktComap K (ktQuotSub K V)
  rw [ktQuotSub_comap hZV] at h
  rw [← h]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVK).toEquiv

theorem isElemAbelian_two_of_sq {H : Type} [Group H] (E : Subgroup H)
    (h : ∀ x ∈ E, x ^ 2 = 1) : IsElemAbelian 2 E := by
  have hinv : ∀ x ∈ E, x⁻¹ = x := fun x hx =>
    inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact h x hx)
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, h⟩
  have hab : ((a : H) * (b : H))⁻¹ = (a : H) * (b : H) :=
    inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact h _ (E.mul_mem a.2 b.2))
  rw [mul_inv_rev, hinv _ a.2, hinv _ b.2] at hab
  exact hab.symm

theorem isElemAbelian_ktQuotSub {K V : Subgroup G} (hVab : IsElemAbelian 2 V) :
    IsElemAbelian 2 (ktQuotSub K V) := by
  apply isElemAbelian_two_of_sq
  intro x hx
  unfold ktQuotSub at hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  have hyV : (y : G) ∈ V := Subgroup.mem_subgroupOf.mp hy
  have hy2 : y ^ 2 = 1 := Subtype.ext (hVab.2 _ hyV)
  rw [← map_pow, hy2, map_one]

theorem sq_eq_one_of_ktLift {K V : Subgroup G} (hVK : V ≤ K) (hVab : IsElemAbelian 2 V)
    (hZV : (Subgroup.center ↥K).map K.subtype ≤ V)
    (hvex : ∃ v ∈ V, v ∉ (Subgroup.center ↥K).map K.subtype)
    (hI : ∀ a b : ↥K ⧸ Subgroup.center ↥K, a ^ 2 = 1 → a ≠ 1 → b ^ 2 = 1 → b ≠ 1 →
      ∃ g : ↥K ⧸ Subgroup.center ↥K, g * a * g⁻¹ = b)
    {x : G} (hx : x ∈ K)
    (hsq : (QuotientGroup.mk' (Subgroup.center ↥K) ⟨x, hx⟩ : ↥K ⧸ Subgroup.center ↥K) ^ 2 = 1) :
    x ^ 2 = 1 := by
  by_cases h1 : (QuotientGroup.mk' (Subgroup.center ↥K) ⟨x, hx⟩ : ↥K ⧸ Subgroup.center ↥K) = 1
  · have hxc : (⟨x, hx⟩ : ↥K) ∈ Subgroup.center ↥K :=
      (QuotientGroup.eq_one_iff (⟨x, hx⟩ : ↥K)).mp h1
    exact hVab.2 x (hZV (Subgroup.mem_map.mpr ⟨⟨x, hx⟩, hxc, rfl⟩))
  · obtain ⟨v, hvV, hvZ⟩ := hvex
    have hvK : v ∈ K := hVK hvV
    have hvv : (⟨v, hvK⟩ : ↥K) ^ 2 = 1 := Subtype.ext (hVab.2 v hvV)
    have ha2 : (QuotientGroup.mk' (Subgroup.center ↥K) ⟨v, hvK⟩ :
        ↥K ⧸ Subgroup.center ↥K) ^ 2 = 1 := by
      rw [← map_pow, hvv, map_one]
    have ha1 : (QuotientGroup.mk' (Subgroup.center ↥K) ⟨v, hvK⟩ :
        ↥K ⧸ Subgroup.center ↥K) ≠ 1 := by
      intro h
      exact hvZ (Subgroup.mem_map.mpr ⟨⟨v, hvK⟩, (QuotientGroup.eq_one_iff (⟨v, hvK⟩ : ↥K)).mp h,
        rfl⟩)
    obtain ⟨g, hg⟩ := hI _ _ ha2 ha1 hsq h1
    obtain ⟨w, hw⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥K) g
    obtain ⟨u, hudef⟩ : ∃ u : ↥K, u = w * ⟨v, hvK⟩ * w⁻¹ := ⟨_, rfl⟩
    have hu2 : u ^ 2 = 1 := by
      rw [hudef, conj_pow, hvv, mul_one, mul_inv_cancel]
    have hπu : QuotientGroup.mk' (Subgroup.center ↥K) u =
        QuotientGroup.mk' (Subgroup.center ↥K) ⟨x, hx⟩ := by
      rw [hudef, map_mul, map_mul, map_inv, hw]
      exact hg
    obtain ⟨y, hydef⟩ : ∃ y : ↥K, y = u⁻¹ * ⟨x, hx⟩ := ⟨_, rfl⟩
    have hyc : y ∈ Subgroup.center ↥K := by
      apply (QuotientGroup.eq_one_iff y).mp
      show QuotientGroup.mk' (Subgroup.center ↥K) y = 1
      rw [hydef, map_mul, map_inv, hπu, inv_mul_cancel]
    have hyV : (y : G) ∈ V := hZV (Subgroup.mem_map.mpr ⟨y, hyc, rfl⟩)
    have hy2 : (y : G) ^ 2 = 1 := hVab.2 _ hyV
    have hu' : (u : G) ^ 2 = 1 := congrArg Subtype.val hu2
    have hcomm : u * y = y * u := Subgroup.mem_center_iff.mp hyc u
    have hcommG : (u : G) * (y : G) = (y : G) * (u : G) := congrArg Subtype.val hcomm
    have hxy : (u : G) * (y : G) = x := by
      have : u * y = (⟨x, hx⟩ : ↥K) := by rw [hydef, mul_inv_cancel_left]
      exact congrArg Subtype.val this
    have hyy : (y : G) * (y : G) = 1 := by rw [← pow_two]; exact hy2
    have huu : (u : G) * (u : G) = 1 := by rw [← pow_two]; exact hu'
    rw [← hxy, pow_two]
    calc (u : G) * (y : G) * ((u : G) * (y : G)) = (u : G) * (y : G) * ((y : G) * (u : G)) := by
          rw [← hcommG]
      _ = (u : G) * ((y : G) * (y : G)) * (u : G) := by simp only [mul_assoc]
      _ = (u : G) * (u : G) := by rw [hyy, mul_one]
      _ = 1 := huu

theorem ktLiftG_conj {K : Subgroup G} {B : Subgroup (↥K ⧸ Subgroup.center ↥K)} {gK : ↥K}
    (hg : QuotientGroup.mk' (Subgroup.center ↥K) gK ∈
      Subgroup.normalizer (B : Set (↥K ⧸ Subgroup.center ↥K)))
    {h : G} (hh : h ∈ ktLiftG K B) : (gK : G) * h * (gK : G)⁻¹ ∈ ktLiftG K B := by
  have hhK : h ∈ K := ktLiftG_le K B hh
  have hcK : (gK : G) * h * (gK : G)⁻¹ ∈ K := K.mul_mem (K.mul_mem gK.2 hhK) (K.inv_mem gK.2)
  rw [mem_ktLiftG hcK]
  have hel : (⟨(gK : G) * h * (gK : G)⁻¹, hcK⟩ : ↥K) = gK * ⟨h, hhK⟩ * gK⁻¹ := rfl
  rw [hel, map_mul, map_mul, map_inv]
  exact (Subgroup.mem_normalizer_iff.mp hg _).mp ((mem_ktLiftG hhK).mp hh)

theorem normalizer_ktLiftG {K : Subgroup G} {B : Subgroup (↥K ⧸ Subgroup.center ↥K)} {gK : ↥K}
    (hg : QuotientGroup.mk' (Subgroup.center ↥K) gK ∈
      Subgroup.normalizer (B : Set (↥K ⧸ Subgroup.center ↥K))) :
    (gK : G) ∈ Subgroup.normalizer ((ktLiftG K B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact ktLiftG_conj hg
  · intro hh
    have hg' : QuotientGroup.mk' (Subgroup.center ↥K) gK⁻¹ ∈
        Subgroup.normalizer (B : Set (↥K ⧸ Subgroup.center ↥K)) := by
      rw [map_inv]
      exact Subgroup.inv_mem _ hg
    have h3 := ktLiftG_conj hg' hh
    have h4 : ((gK⁻¹ : ↥K) : G) * ((gK : G) * h * (gK : G)⁻¹) * ((gK⁻¹ : ↥K) : G)⁻¹ = h := by
      simp only [Subgroup.coe_inv]
      group
    rwa [h4] at h3

theorem ktLine_of_quot {K V : Subgroup G} (hVK : V ≤ K) (hVab : IsElemAbelian 2 V)
    (hV64 : Nat.card ↥V = 64) (hZV : (Subgroup.center ↥K).map K.subtype ≤ V)
    (hZ4 : Nat.card ↥(Subgroup.center ↥K) = 4)
    (hcen : ∀ k ∈ K, ∀ z ∈ (Subgroup.center ↥K).map K.subtype, k * z = z * k)
    (hI : ∀ a b : ↥K ⧸ Subgroup.center ↥K, a ^ 2 = 1 → a ≠ 1 → b ^ 2 = 1 → b ≠ 1 →
      ∃ g : ↥K ⧸ Subgroup.center ↥K, g * a * g⁻¹ = b)
    (hE : ∀ A : Subgroup (↥K ⧸ Subgroup.center ↥K), IsElemAbelian 2 A → Nat.card ↥A = 16 →
      ∃ B : Subgroup (↥K ⧸ Subgroup.center ↥K), IsElemAbelian 2 B ∧ Nat.card ↥B = 16 ∧
        Nat.card ↥(B ⊓ A) = 4 ∧ B ≤ Subgroup.normalizer (A : Set (↥K ⧸ Subgroup.center ↥K)) ∧
        ∃ k : Fin 5 → ↥K ⧸ Subgroup.center ↥K, k 0 = 1 ∧
          (∀ i, k i ∈ Subgroup.normalizer (B : Set (↥K ⧸ Subgroup.center ↥K))) ∧
          ∀ i j, i ≠ j → ∀ x ∈ B, (∃ a ∈ A, x = k i * a * (k i)⁻¹) →
            (∃ a ∈ A, x = k j * a * (k j)⁻¹) → x = 1) :
    ∃ U : Subgroup G, U ≤ K ∧ IsElemAbelian 2 U ∧ Nat.card ↥U = 64 ∧ U ≠ V ∧
      Nat.card ↥(U ⊓ V) = 16 ∧ U ≤ Subgroup.normalizer (V : Set G) ∧
      ∃ k : Fin 5 → G, k 0 = 1 ∧ (∀ i, k i ∈ K ⊓ Subgroup.normalizer (U : Set G)) ∧
        ∀ i j, i ≠ j → V.map (MulAut.conj (k i)).toMonoidHom ⊓
          V.map (MulAut.conj (k j)).toMonoidHom ⊓ U = (Subgroup.center ↥K).map K.subtype := by
  classical
  obtain ⟨Vb, hVb⟩ : ∃ Vb : Subgroup (↥K ⧸ Subgroup.center ↥K), Vb = ktQuotSub K V := ⟨_, rfl⟩
  have hVb_ab : IsElemAbelian 2 Vb := by
    rw [hVb]
    exact isElemAbelian_ktQuotSub hVab
  have hVb_card : Nat.card ↥Vb = 16 := by
    have h := card_ktQuotSub hVK hZV
    rw [← hVb, hZ4, hV64] at h
    omega
  obtain ⟨Ub, hUb_ab, hUb_card, hUb_inf, hUb_norm, kb, hkb0, hkbN, hkbint⟩ :=
    hE Vb hVb_ab hVb_card
  obtain ⟨U, hU⟩ : ∃ U : Subgroup G, U = ktLiftG K Ub := ⟨_, rfl⟩
  have hUK : U ≤ K := by
    rw [hU]
    exact ktLiftG_le K Ub
  have hmemU : ∀ {x : G} (hx : x ∈ K),
      x ∈ U ↔ QuotientGroup.mk' (Subgroup.center ↥K) ⟨x, hx⟩ ∈ Ub := by
    intro x hx
    rw [hU]
    exact mem_ktLiftG hx
  have hmemV : ∀ {x : G} (hx : x ∈ K),
      x ∈ V ↔ QuotientGroup.mk' (Subgroup.center ↥K) ⟨x, hx⟩ ∈ Vb := by
    intro x hx
    rw [hVb]
    exact (mem_ktQuotSub hZV hx).symm
  have hliftV : ktLiftG K Vb = V := by
    rw [hVb]
    unfold ktLiftG
    rw [ktQuotSub_comap hZV, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hVK]
  have hUV : U ⊓ V = ktLiftG K (Ub ⊓ Vb) := by
    rw [hU, ktLiftG_inf, hliftV]
  have hUV_card : Nat.card ↥(U ⊓ V) = 16 := by
    rw [hUV, card_ktLiftG, hUb_inf, hZ4] <;> norm_num
  have hU_card : Nat.card ↥U = 64 := by
    rw [hU, card_ktLiftG, hUb_card, hZ4] <;> norm_num
  have hvex : ∃ v ∈ V, v ∉ (Subgroup.center ↥K).map K.subtype := by
    by_contra hcon
    push Not at hcon
    have h1 := Subgroup.card_le_of_le (show V ≤ (Subgroup.center ↥K).map K.subtype from
      fun v hv => hcon v hv)
    rw [Subgroup.card_map_of_injective K.subtype_injective, hZ4, hV64] at h1
    norm_num at h1
  have hU_ab : IsElemAbelian 2 U := by
    apply isElemAbelian_two_of_sq
    intro x hx
    have hxK : x ∈ K := hUK hx
    exact sq_eq_one_of_ktLift hVK hVab hZV hvex hI hxK (hUb_ab.2 _ ((hmemU hxK).mp hx))
  have hU_ne : U ≠ V := by
    intro h
    have h1 := hUV_card
    rw [h, inf_idem, hV64] at h1
    norm_num at h1
  have fwd : ∀ u ∈ U, ∀ v ∈ V, u * v * u⁻¹ ∈ V := by
    intro u hu v hv
    have huK : u ∈ K := hUK hu
    have hvK : v ∈ K := hVK hv
    have hconjK : u * v * u⁻¹ ∈ K := K.mul_mem (K.mul_mem huK hvK) (K.inv_mem huK)
    have hel : (⟨u * v * u⁻¹, hconjK⟩ : ↥K) = ⟨u, huK⟩ * ⟨v, hvK⟩ * ⟨u, huK⟩⁻¹ := rfl
    have hpu : QuotientGroup.mk' (Subgroup.center ↥K) ⟨u, huK⟩ ∈ Ub := (hmemU huK).mp hu
    have hpv : QuotientGroup.mk' (Subgroup.center ↥K) ⟨v, hvK⟩ ∈ Vb := (hmemV hvK).mp hv
    rw [hmemV hconjK, hel, map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hUb_norm hpu) _).mp hpv
  have hU_norm : U ≤ Subgroup.normalizer (V : Set G) := by
    intro u hu
    rw [Subgroup.mem_normalizer_iff]
    intro v
    constructor
    · exact fwd u hu v
    · intro hv
      have h1 := fwd u⁻¹ (U.inv_mem hu) _ hv
      have h2 : u⁻¹ * (u * v * u⁻¹) * u⁻¹⁻¹ = v := by group
      rw [h2] at h1
      exact h1
  have hsurj : Function.Surjective (QuotientGroup.mk' (Subgroup.center ↥K)) :=
    QuotientGroup.mk'_surjective _
  obtain ⟨kl, hkl, hkl1⟩ : ∃ kl : (↥K ⧸ Subgroup.center ↥K) → ↥K,
      (∀ s, QuotientGroup.mk' (Subgroup.center ↥K) (kl s) = s) ∧ kl 1 = 1 := by
    refine ⟨fun s => if s = 1 then 1 else Classical.choose (hsurj s), fun s => ?_, by simp⟩
    by_cases h : s = 1
    · subst h
      simp
    · simp only [if_neg h]
      exact Classical.choose_spec (hsurj s)
  obtain ⟨kG, hkG⟩ : ∃ kG : Fin 5 → G, ∀ i, kG i = ((kl (kb i) : ↥K) : G) :=
    ⟨_, fun i => rfl⟩
  have hkGK : ∀ i, kG i ∈ K := fun i => by
    rw [hkG]
    exact (kl (kb i)).2
  have hkGπ : ∀ i, QuotientGroup.mk' (Subgroup.center ↥K) ⟨kG i, hkGK i⟩ = kb i := by
    intro i
    have : (⟨kG i, hkGK i⟩ : ↥K) = kl (kb i) := Subtype.ext (hkG i)
    rw [this, hkl]
  have hkG0 : kG 0 = 1 := by
    rw [hkG, hkb0, hkl1] <;> simp
  have hkGN : ∀ i, kG i ∈ Subgroup.normalizer (U : Set G) := by
    intro i
    have hgi : QuotientGroup.mk' (Subgroup.center ↥K) (kl (kb i)) ∈
        Subgroup.normalizer (Ub : Set (↥K ⧸ Subgroup.center ↥K)) := by
      rw [hkl]
      exact hkbN i
    have h1 := normalizer_ktLiftG hgi
    rw [hU, hkG]
    exact h1
  have hkGmem : ∀ i, kG i ∈ K ⊓ Subgroup.normalizer (U : Set G) :=
    fun i => Subgroup.mem_inf.mpr ⟨hkGK i, hkGN i⟩
  have hint : ∀ i j, i ≠ j → V.map (MulAut.conj (kG i)).toMonoidHom ⊓
      V.map (MulAut.conj (kG j)).toMonoidHom ⊓ U = (Subgroup.center ↥K).map K.subtype := by
    intro i j hij
    ext x
    constructor
    · intro hx
      obtain ⟨hxAB, hxU⟩ := Subgroup.mem_inf.mp hx
      obtain ⟨hxA, hxB⟩ := Subgroup.mem_inf.mp hxAB
      obtain ⟨v, hvV, hvx⟩ := Subgroup.mem_map.mp hxA
      obtain ⟨v', hv'V, hv'x⟩ := Subgroup.mem_map.mp hxB
      have hxK : x ∈ K := hUK hxU
      have hvK : v ∈ K := hVK hvV
      have hv'K : v' ∈ K := hVK hv'V
      have hvx' : kG i * v * (kG i)⁻¹ = x := hvx
      have hv'x' : kG j * v' * (kG j)⁻¹ = x := hv'x
      have e1 : QuotientGroup.mk' (Subgroup.center ↥K) ⟨x, hxK⟩ =
          kb i * QuotientGroup.mk' (Subgroup.center ↥K) ⟨v, hvK⟩ * (kb i)⁻¹ := by
        have : (⟨x, hxK⟩ : ↥K) = ⟨kG i, hkGK i⟩ * ⟨v, hvK⟩ * ⟨kG i, hkGK i⟩⁻¹ :=
          Subtype.ext hvx'.symm
        rw [this, map_mul, map_mul, map_inv, hkGπ i]
      have e2 : QuotientGroup.mk' (Subgroup.center ↥K) ⟨x, hxK⟩ =
          kb j * QuotientGroup.mk' (Subgroup.center ↥K) ⟨v', hv'K⟩ * (kb j)⁻¹ := by
        have : (⟨x, hxK⟩ : ↥K) = ⟨kG j, hkGK j⟩ * ⟨v', hv'K⟩ * ⟨kG j, hkGK j⟩⁻¹ :=
          Subtype.ext hv'x'.symm
        rw [this, map_mul, map_mul, map_inv, hkGπ j]
      have hxUb : QuotientGroup.mk' (Subgroup.center ↥K) ⟨x, hxK⟩ ∈ Ub :=
        (hmemU hxK).mp hxU
      have h1 := hkbint i j hij _ hxUb
        ⟨_, (hmemV hvK).mp hvV, e1⟩ ⟨_, (hmemV hv'K).mp hv'V, e2⟩
      have hc : (⟨x, hxK⟩ : ↥K) ∈ Subgroup.center ↥K :=
        (QuotientGroup.eq_one_iff (⟨x, hxK⟩ : ↥K)).mp h1
      exact Subgroup.mem_map.mpr ⟨⟨x, hxK⟩, hc, rfl⟩
    · intro hx
      obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp hx
      have hxK : x ∈ K := by
        rw [← hzx]
        exact z.2
      have hxV : x ∈ V := hZV hx
      have hcx_i : kG i * x * (kG i)⁻¹ = x := by
        rw [hcen (kG i) (hkGK i) x hx, mul_inv_cancel_right]
      have hcx_j : kG j * x * (kG j)⁻¹ = x := by
        rw [hcen (kG j) (hkGK j) x hx, mul_inv_cancel_right]
      have hxZ : QuotientGroup.mk' (Subgroup.center ↥K) ⟨x, hxK⟩ = 1 := by
        have : (⟨x, hxK⟩ : ↥K) = z := Subtype.ext hzx.symm
        rw [this]
        exact (QuotientGroup.eq_one_iff z).mpr hz
      refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
      · exact Subgroup.mem_map.mpr ⟨x, hxV, hcx_i⟩
      · exact Subgroup.mem_map.mpr ⟨x, hxV, hcx_j⟩
      · exact (hmemU hxK).mpr (by rw [hxZ]; exact Ub.one_mem)
  exact ⟨U, hUK, hU_ab, hU_card, hU_ne, hUV_card, hU_norm, kG, hkG0, hkGmem, hint⟩

end Lift

theorem ktLine1277_of (h71 : Setup1271) (hI : KtSInv) (hE : KtS16) : KtLine1277 := by
  intro G _ _ T L V t s
  have hVab : IsElemAbelian 2 V := (h71 G T L V s.d.hyp).1
  have hV64 : Nat.card ↥V = 64 := s.d.card_V.trans (by norm_num)
  have hVK : V ≤ Kt L t := s.d.v_le_lt.trans (CFSG.Quasithin.H13.S127.I77.lt_le_Kt L t)
  have hZV : (Subgroup.center ↥(Kt L t)).map (Kt L t).subtype ≤ V := by
    rw [s.center]
    exact s.d.vt_le
  have hZ4 : Nat.card ↥(Subgroup.center ↥(Kt L t)) = 4 := s.card_center
  have hcen : ∀ k ∈ Kt L t, ∀ z ∈ (Subgroup.center ↥(Kt L t)).map (Kt L t).subtype,
      k * z = z * k := by
    intro k hk z hz
    rw [s.center] at hz
    exact ((Subgroup.mem_centralizer_iff.mp (s.le_centralizer_vt hk)) z hz).symm
  obtain ⟨U, hUK, hUab, hUcard, hUV, hUVcard, hUN, k, hk0, hkN, hkint⟩ :=
    ktLine_of_quot hVK hVab hV64 hZV hZ4 hcen
      (fun a b ha1 ha2 hb1 hb2 => hI _ s.psl a b ha1 ha2 hb1 hb2)
      (fun A hA hc => hE _ s.psl A hA hc)
  exact ⟨U, hUK, hUab, hUcard, hUV, hUVcard, hUN, k, hk0, hkN,
    fun i j hij => (hkint i j hij).trans s.center⟩

end CFSG.Quasithin.H13.I1277
