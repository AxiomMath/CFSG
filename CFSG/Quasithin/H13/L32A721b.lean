module

public import CFSG.Quasithin.H13.L32A721a
public import CFSG.Quasithin.H13.L32AS4d

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

section Counting

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem comm_mem_of_sup_eq {X Y F : Subgroup G} (h : IsElemSection X Y) {g : G}
    (hgX : g ∈ Subgroup.normalizer (X : Set G)) (hgY : g ∈ Subgroup.normalizer (Y : Set G))
    (hFX : F ≤ X) (hX : F ⊔ Y = X) (hF : ∀ f ∈ F, g * f * g⁻¹ * f⁻¹ ∈ Y) :
    ∀ x ∈ X, g * x * g⁻¹ * x⁻¹ ∈ Y := by
  have hAX : Subgroup.zpowers g ≤ Subgroup.normalizer (X : Set G) :=
    (Subgroup.zpowers_le).mpr hgX
  have hAY : Subgroup.zpowers g ≤ Subgroup.normalizer (Y : Set G) :=
    (Subgroup.zpowers_le).mpr hgY
  set a : ↥(Subgroup.zpowers g) := ⟨g, Subgroup.mem_zpowers g⟩ with ha
  have hS : F ⊔ Y ≤ SecW.pre h (fixSub (SecW.act h (Subgroup.zpowers g) hAX hAY a)) := by
    refine sup_le (fun f hf => ?_) (SecW.le_pre h _)
    exact (SecW.mem_pre h).mpr ⟨hFX hf, (SecW.act_mk_eq_mk_iff h a ⟨f, hFX hf⟩).mpr (hF f hf)⟩
  intro x hx
  obtain ⟨hx', hmk⟩ := (SecW.mem_pre h).mp (hS (by rw [hX]; exact hx))
  exact (SecW.act_mk_eq_mk_iff h a ⟨x, hx'⟩).mp hmk

omit [Finite G] in
theorem comm_eq_one_of_fix_of_isPGroup {Z : Subgroup G} (hZ2 : IsPGroup 2 ↥Z) {x z : G}
    (hxZ : x ∈ Subgroup.normalizer (Z : Set G)) (hz : z ∈ Z) (hx3 : x ^ 3 * z = z * x ^ 3)
    (hfix : x * (x * z * x⁻¹ * z⁻¹) * x⁻¹ = x * z * x⁻¹ * z⁻¹) : x * z * x⁻¹ * z⁻¹ = 1 := by
  set r := x * z * x⁻¹ * z⁻¹ with hr
  have hrZ : r ∈ Z := mul_mem ((Subgroup.mem_normalizer_iff.mp hxZ z).mp hz) (inv_mem hz)
  have e1 : (x * (x * r * x⁻¹) * x⁻¹) * (x * r * x⁻¹) * r =
      x ^ 3 * z * (x ^ 3)⁻¹ * z⁻¹ := by
    rw [hr, pow_three]
    group
  rw [hfix, hfix, hx3] at e1
  have h3 : r ^ 3 = 1 := by
    rw [pow_three', e1]
    group
  obtain ⟨n, hn⟩ := hZ2 ⟨r, hrZ⟩
  have hrn : r ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have hcop : Nat.Coprime 3 (2 ^ n) := Nat.Coprime.pow_right _ (by norm_num)
  have := pow_gcd_eq_one.mpr ⟨h3, hrn⟩
  rwa [hcop.gcd_eq_one, pow_one] at this

theorem card_le_of_forall_mem {Γ : Type} [Group Γ] [Finite Γ] (S : Subgroup Γ) (F : Finset Γ)
    (h : ∀ b ∈ S, b ∈ F) : Nat.card S ≤ F.card := by
  have := Nat.card_le_card_of_injective (fun b : ↥S => (⟨b, h b b.2⟩ : ↥(F : Set Γ)))
    (fun a b e => Subtype.ext (by simpa using congrArg Subtype.val e))
  rwa [Nat.card_coe_set_eq, Set.ncard_coe_finset] at this

theorem card_inf_centralizer_mul_four_le {V : Subgroup G} (hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    (hV2 : ∀ v ∈ V, v * v = 1) {x a : G} (hxV : x ∈ Subgroup.normalizer (V : Set G))
    (haV : a ∈ Subgroup.normalizer (V : Set G)) (hfpf : ∀ v ∈ V, x * v * x⁻¹ = v → v = 1)
    (hcomm : ∀ v ∈ V, x * (a * v * a⁻¹) * x⁻¹ = a * (x * v * x⁻¹) * a⁻¹)
    (hnt : ∃ v ∈ V, a * v * a⁻¹ ≠ v) :
    Nat.card ↥(V ⊓ Subgroup.centralizer ({a} : Set G)) * 4 ≤ Nat.card V := by
  classical
  set δ := commHom hVc haV with hδ
  have hker : Nat.card ↥(V ⊓ Subgroup.centralizer ({a} : Set G)) ≤ Nat.card δ.ker := by
    rw [← Subgroup.card_map_of_injective V.subtype_injective]
    refine Subgroup.card_le_of_le fun g hg => ?_
    have hgV := (Subgroup.mem_inf.mp hg).1
    have hga : a * g = g * a :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hg).2 a rfl
    refine ⟨⟨g, hgV⟩, MonoidHom.mem_ker.mpr ?_, rfl⟩
    apply Subtype.ext
    rw [hδ, coe_commHom, hga]
    simp
  obtain ⟨v, hv, hva⟩ := hnt
  have hxv : x * v * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hxV v).mp hv
  set r : G := a * v * a⁻¹ * v⁻¹ with hr
  set r' : G := a * (x * v * x⁻¹) * a⁻¹ * (x * v * x⁻¹)⁻¹ with hr'
  have hrV : r ∈ V := (δ ⟨v, hv⟩).2
  have hr1 : r ≠ 1 := fun h1 => hva (by rw [← mul_inv_eq_one]; exact h1)
  have hrr' : r' = x * r * x⁻¹ := by
    rw [hr', hr, ← hcomm v hv]
    group
  have hr'1 : r' ≠ 1 := fun h1 => hr1 (by rw [hrr', conj_eq_one_iff] at h1; exact h1)
  have hrne : r ≠ r' := fun h1 => hr1 (hfpf r hrV (by rw [← hrr', h1]))
  have hr2 : r * r = 1 := hV2 r hrV
  have hmem : ∀ g ∈ ({1, r, r', r * r'} : Finset G), g ∈ δ.range.map V.subtype := by
    intro g hg
    simp only [Finset.mem_insert, Finset.mem_singleton] at hg
    have h1 : r ∈ δ.range.map V.subtype := ⟨δ ⟨v, hv⟩, ⟨_, rfl⟩, rfl⟩
    have h2 : r' ∈ δ.range.map V.subtype := ⟨δ ⟨_, hxv⟩, ⟨_, rfl⟩, rfl⟩
    rcases hg with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact h1
    · exact h2
    · exact mul_mem h1 h2
  have hcard4 : ({1, r, r', r * r'} : Finset G).card = 4 := by
    have n1 : (1 : G) ≠ r * r' := fun h => hrne (by
      calc r = r * (r * r') := by rw [← h, mul_one]
        _ = r' := by rw [← mul_assoc, hr2, one_mul])
    have n2 : r ≠ r * r' := fun h => hr'1 (by
      calc r' = r⁻¹ * (r * r') := by group
        _ = 1 := by rw [← h, inv_mul_cancel])
    have n3 : r' ≠ r * r' := fun h => hr1 (by
      calc r = r * r' * r'⁻¹ := by group
        _ = 1 := by rw [← h, mul_inv_cancel])
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair n3]
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hrne, n2⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hr1 h.symm, fun h => hr'1 h.symm, n1⟩
  have hrange : 4 ≤ Nat.card δ.range := by
    rw [← Subgroup.card_map_of_injective V.subtype_injective, ← hcard4]
    have := Nat.card_le_card_of_injective
      (fun g : ↥(({1, r, r', r * r'} : Finset G) : Set G) =>
        (⟨g, hmem g g.2⟩ : ↥(δ.range.map V.subtype)))
      (fun a b e => Subtype.ext (by simpa using congrArg Subtype.val e))
    rwa [Nat.card_coe_set_eq, Set.ncard_coe_finset] at this
  have e := Subgroup.card_ker_mul_card_range δ
  calc Nat.card ↥(V ⊓ Subgroup.centralizer ({a} : Set G)) * 4 ≤
      Nat.card δ.ker * Nat.card δ.range := Nat.mul_le_mul hker hrange
    _ = Nat.card V := e

theorem card_inf_centralizer_mul_self_le {V : Subgroup G} {x a : G}
    (hxV : x ∈ Subgroup.normalizer (V : Set G)) (hx3 : x ^ 3 = 1)
    (hfpf : ∀ v ∈ V, x * v * x⁻¹ = v → v = 1)
    (hinv : ∀ v ∈ V, a * (x * v * x⁻¹) * a⁻¹ = x⁻¹ * (a * v * a⁻¹) * x) :
    Nat.card ↥(V ⊓ Subgroup.centralizer ({a} : Set G)) *
      Nat.card ↥(V ⊓ Subgroup.centralizer ({a} : Set G)) ≤ Nat.card V := by
  set C := V ⊓ Subgroup.centralizer ({a} : Set G) with hC
  have hcen : ∀ c ∈ C, a * c * a⁻¹ = c := fun c hc => by
    rw [Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2 a rfl]
    group
  have hconj : ∀ d ∈ V, x * d * x⁻¹ ∈ V := fun d hd =>
    (Subgroup.mem_normalizer_iff.mp hxV d).mp hd
  have hmeet : ∀ w ∈ C, x * w * x⁻¹ ∈ C → w = 1 := by
    intro w hw hxw
    have hwV := (Subgroup.mem_inf.mp hw).1
    have h1 := hinv w hwV
    rw [hcen _ hxw, hcen w hw] at h1
    have h2 : x ^ 3 * w * (x ^ 3)⁻¹ = x * w * x⁻¹ := by
      calc x ^ 3 * w * (x ^ 3)⁻¹ = x * (x * (x * w * x⁻¹) * x⁻¹) * x⁻¹ := by
            rw [pow_three]; group
        _ = x * (x * (x⁻¹ * w * x) * x⁻¹) * x⁻¹ := by rw [h1]
        _ = x * w * x⁻¹ := by group
    rw [hx3] at h2
    exact hfpf w hwV (by rw [← h2]; group)
  have hf : Function.Injective fun p : ↥C × ↥C =>
      (⟨(p.1 : G) * (x * (p.2 : G) * x⁻¹), mul_mem (Subgroup.mem_inf.mp p.1.2).1
        (hconj _ (Subgroup.mem_inf.mp p.2.2).1)⟩ : ↥V) := by
    rintro ⟨c₁, d₁⟩ ⟨c₂, d₂⟩ he
    have he' : (c₁ : G) * (x * (d₁ : G) * x⁻¹) = (c₂ : G) * (x * (d₂ : G) * x⁻¹) :=
      congrArg Subtype.val he
    have hw : (d₁ : G) * (d₂ : G)⁻¹ ∈ C := mul_mem d₁.2 (inv_mem d₂.2)
    have hxw : x * ((d₁ : G) * (d₂ : G)⁻¹) * x⁻¹ ∈ C := by
      have e : x * ((d₁ : G) * (d₂ : G)⁻¹) * x⁻¹ = (c₁ : G)⁻¹ * (c₂ : G) := by
        calc x * ((d₁ : G) * (d₂ : G)⁻¹) * x⁻¹ =
            (c₁ : G)⁻¹ * ((c₁ : G) * (x * (d₁ : G) * x⁻¹)) * (x * (d₂ : G) * x⁻¹)⁻¹ := by
              group
          _ = (c₁ : G)⁻¹ * (c₂ : G) := by rw [he']; group
      rw [e]
      exact mul_mem (inv_mem c₁.2) c₂.2
    have hd : (d₁ : G) = d₂ := by
      have := hmeet _ hw hxw
      rw [mul_inv_eq_one] at this
      exact this
    have hc : (c₁ : G) = c₂ := by
      rw [hd] at he'
      exact mul_right_cancel he'
    rw [Prod.mk.injEq]
    exact ⟨Subtype.ext hc, Subtype.ext hd⟩
  have := Nat.card_le_card_of_injective _ hf
  rwa [Nat.card_prod] at this

end Counting

namespace Ctx7153

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G} (E : Ctx7153 G T L V H)
include E

omit [Finite G] E in
theorem mk_eq_one_iff_hz (g : ↥(hz T V)) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥(hz T V)) g = 1 ↔ (g : G) ∈ pCoreOf 2 (hz T V) := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact C2Six.mem_pCore_two_iff

omit [Finite G] E in
theorem mk_conj_eq_iff {a x : G} (ha : a ∈ hz T V) (hx : x ∈ hz T V) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥(hz T V)) ⟨a, ha⟩ *
        QuotientGroup.mk' (CFSG.pCore 2 ↥(hz T V)) ⟨x, hx⟩ *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥(hz T V)) ⟨a, ha⟩)⁻¹ =
      QuotientGroup.mk' (CFSG.pCore 2 ↥(hz T V)) ⟨x, hx⟩ ↔
    a * x * a⁻¹ * x⁻¹ ∈ pCoreOf 2 (hz T V) := by
  have hm : a * x * a⁻¹ * x⁻¹ ∈ hz T V :=
    mul_mem (mul_mem (mul_mem ha hx) (inv_mem ha)) (inv_mem hx)
  have e : (⟨a * x * a⁻¹ * x⁻¹, hm⟩ : ↥(hz T V)) = ⟨a, ha⟩ * ⟨x, hx⟩ * ⟨a, ha⟩⁻¹ * ⟨x, hx⟩⁻¹ :=
    rfl
  rw [← mul_inv_eq_one, ← mk_eq_one_iff_hz ⟨_, hm⟩, e, map_mul, map_mul, map_mul, map_inv,
    map_inv]

omit [Finite G] E in
theorem mk_conj_eq_inv_iff {a x : G} (ha : a ∈ hz T V) (hx : x ∈ hz T V) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥(hz T V)) ⟨a, ha⟩ *
        QuotientGroup.mk' (CFSG.pCore 2 ↥(hz T V)) ⟨x, hx⟩ *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥(hz T V)) ⟨a, ha⟩)⁻¹ =
      (QuotientGroup.mk' (CFSG.pCore 2 ↥(hz T V)) ⟨x, hx⟩)⁻¹ ↔
    a * x * a⁻¹ * x ∈ pCoreOf 2 (hz T V) := by
  have hm : a * x * a⁻¹ * x ∈ hz T V := mul_mem (mul_mem (mul_mem ha hx) (inv_mem ha)) hx
  have e : (⟨a * x * a⁻¹ * x, hm⟩ : ↥(hz T V)) = ⟨a, ha⟩ * ⟨x, hx⟩ * ⟨a, ha⟩⁻¹ * ⟨x, hx⟩ := rfl
  rw [← mul_eq_one_iff_eq_inv, ← mk_eq_one_iff_hz ⟨_, hm⟩, e, map_mul, map_mul, map_mul, map_inv]

theorem conj_xdot_cases {x : G} (hxL : x ∈ l1 T L V) (hxH : x ∈ hz T V) (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) (b : ↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V)) :
    b * QuotientGroup.mk' (CFSG.pCore 2 ↥(hz T V)) ⟨x, hxH⟩ * b⁻¹ =
        QuotientGroup.mk' (CFSG.pCore 2 ↥(hz T V)) ⟨x, hxH⟩ ∨
      b * QuotientGroup.mk' (CFSG.pCore 2 ↥(hz T V)) ⟨x, hxH⟩ * b⁻¹ =
        (QuotientGroup.mk' (CFSG.pCore 2 ↥(hz T V)) ⟨x, hxH⟩)⁻¹ := by
  have hzp := E.zpowers_eq_l1dot hxL hxH hx3 hx1
  set y := QuotientGroup.mk' (CFSG.pCore 2 ↥(hz T V)) (⟨x, hxH⟩ : ↥(hz T V)) with hy
  have h3 : y ^ 3 = 1 := by
    rw [hy, ← map_pow]
    have e : (⟨x, hxH⟩ : ↥(hz T V)) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
    rw [e, map_one]
  have h1 : y ≠ 1 := by
    intro h1
    have := E.card_l1dot
    rw [← hzp, h1, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at this
    omega
  have hN := E.l1dot_normal
  have hmem : b * y * b⁻¹ ∈ Subgroup.zpowers y := by
    rw [hzp]
    exact hN.conj_mem y (hzp ▸ Subgroup.mem_zpowers y) b
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hmem)
  rw [← Nat.div_add_mod n 3, pow_add, pow_mul, h3, one_pow, one_mul] at hn
  obtain h | h | h : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  · rw [h, pow_zero] at hn
    exact absurd (conj_eq_one_iff.mp hn.symm) h1
  · left
    rw [h, pow_one] at hn
    exact hn.symm
  · right
    rw [h] at hn
    rw [← hn]
    exact eq_inv_of_mul_eq_one_left (by rw [sq, ← pow_three', h3])

theorem conj_cases_three {x : G} (hxL : x ∈ l1 T L V) (hxH : x ∈ hz T V) (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) {a : G} (ha : a ∈ hz T V) :
    a * x * a⁻¹ * x⁻¹ ∈ pCoreOf 2 (hz T V) ∨ a * x * a⁻¹ * x ∈ pCoreOf 2 (hz T V) := by
  rcases E.conj_xdot_cases hxL hxH hx3 hx1 (QuotientGroup.mk' _ ⟨a, ha⟩) with h | h
  · exact Or.inl ((mk_conj_eq_iff ha hxH).mp h)
  · exact Or.inr ((mk_conj_eq_inv_iff ha hxH).mp h)

theorem relIndex_le {x : G} (hxL : x ∈ l1 T L V) (hxH : x ∈ hz T V) (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) {A : Subgroup G} (hAT : A ≤ T) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hA2 : ∀ a ∈ A, a * a = 1) :
    (A ⊓ pCoreOf 2 (hz T V)).relIndex A ≤ 4 ∧
      ((∀ a ∈ A, a * x * a⁻¹ * x⁻¹ ∈ pCoreOf 2 (hz T V)) →
        (A ⊓ pCoreOf 2 (hz T V)).relIndex A ≤ 2) := by
  classical
  have hzp := E.zpowers_eq_l1dot hxL hxH hx3 hx1
  have hAH : A ≤ hz T V := hAT.trans E.t_le_hz
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥(hz T V)) with hπ
  set φ : ↥A →* ↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V) := π.comp (Subgroup.inclusion hAH) with hφ
  have hker : φ.ker = (A ⊓ pCoreOf 2 (hz T V)).subgroupOf A := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf, hφ, MonoidHom.comp_apply,
      mk_eq_one_iff_hz]
    exact ⟨fun h => ⟨a.2, h⟩, fun h => h.2⟩
  have hidx : (A ⊓ pCoreOf 2 (hz T V)).relIndex A = Nat.card φ.range := by
    rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
  set y' := π ⟨x, hxH⟩ with hy'
  obtain ⟨-, y, -, -, -, -, huniq, -⟩ := E.exists_y
  have hrange : ∀ b ∈ φ.range, b ∈ modO2Image (hz T V) T ∧ b * b = 1 := by
    rintro _ ⟨a, rfl⟩
    refine ⟨mem_modO2Image_iff.mpr ⟨⟨a, hAH a.2⟩, hAT a.2, rfl⟩, ?_⟩
    rw [← map_mul]
    have : a * a = 1 := Subtype.ext (hA2 a a.2)
    rw [this, map_one]
  have hcen : ∀ b ∈ φ.range, b * y' * b⁻¹ = y' → b = 1 ∨ b = y ^ 2 := by
    intro b hb hby
    by_cases hb1 : b = 1
    · exact Or.inl hb1
    right
    refine huniq b (hrange b hb).1 ?_ (by rw [sq]; exact (hrange b hb).2) hb1
    rw [← hzp, Subgroup.mem_centralizer_iff]
    intro l hl
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hl
    have hc : Commute y' b := by
      have e : b * y' = y' * b := by
        calc b * y' = b * y' * b⁻¹ * b := by group
          _ = y' * b := by rw [hby]
      exact e.symm
    exact (hc.zpow_left k).eq
  have hcomm : ∀ b ∈ φ.range, ∀ b' ∈ φ.range, b * b' = b' * b := by
    rintro _ ⟨a, rfl⟩ _ ⟨a', rfl⟩
    rw [← map_mul, ← map_mul]
    have : a * a' = a' * a := Subtype.ext (hAc a a.2 a' a'.2)
    rw [this]
  have htwo : (∀ b ∈ φ.range, b * y' * b⁻¹ = y') → Nat.card φ.range ≤ 2 := by
    intro hall
    refine (card_le_of_forall_mem φ.range {1, y ^ 2} fun b hb => ?_).trans Finset.card_le_two
    rcases hcen b hb (hall b hb) with rfl | rfl <;> simp
  refine ⟨?_, fun hall => ?_⟩
  · rw [hidx]
    by_cases hex : ∃ b₀ ∈ φ.range, b₀ * y' * b₀⁻¹ ≠ y'
    · obtain ⟨b₀, hb₀, hb₀y⟩ := hex
      have hb₀i : b₀ * y' * b₀⁻¹ = y'⁻¹ :=
        (E.conj_xdot_cases hxL hxH hx3 hx1 b₀).resolve_left hb₀y
      refine (card_le_of_forall_mem φ.range {1, y ^ 2, b₀, b₀ * y ^ 2}
        fun b hb => ?_).trans Finset.card_le_four
      by_cases hby : b * y' * b⁻¹ = y'
      · rcases hcen b hb hby with rfl | rfl <;> simp
      · have hbi : b * y' * b⁻¹ = y'⁻¹ :=
          (E.conj_xdot_cases hxL hxH hx3 hx1 b).resolve_left hby
        have hb0b : (b₀ * b) * y' * (b₀ * b)⁻¹ = y' := by
          calc (b₀ * b) * y' * (b₀ * b)⁻¹ = b₀ * (b * y' * b⁻¹) * b₀⁻¹ := by group
            _ = (b₀ * y' * b₀⁻¹)⁻¹ := by rw [hbi]; group
            _ = y' := by rw [hb₀i, inv_inv]
        have hb₀2 : b₀⁻¹ = b₀ := inv_eq_of_mul_eq_one_right (hrange b₀ hb₀).2
        rcases hcen _ (mul_mem hb₀ hb) hb0b with h | h
        · have : b = b₀ := by
            calc b = b₀⁻¹ * (b₀ * b) := by group
              _ = b₀ := by rw [h, mul_one, hb₀2]
          rw [this]
          simp
        · have : b = b₀ * y ^ 2 := by
            calc b = b₀⁻¹ * (b₀ * b) := by group
              _ = b₀ * y ^ 2 := by rw [h, hb₀2]
          rw [this]
          simp
    · push Not at hex
      exact (htwo hex).trans (by norm_num)
  · rw [hidx]
    refine htwo ?_
    rintro _ ⟨a, rfl⟩
    have h1 := (mk_conj_eq_iff (hAH a.2) hxH).mpr (hall a a.2)
    exact h1

variable (hF : HypF98 T V L (fsuV1 T V) V (hz T V))
include hF

omit hF in
theorem qh_le_r1 : pCoreOf 2 (hz T V) ≤ pCoreOf 2 (l1 T L V ⊔ T) ∧
    pCoreOf 2 (l1 T L V ⊔ T) ≤ T := by
  obtain ⟨hL1K, -⟩ := lemma14_7_15_one E.h331 E.hThm E.h1222 E.h1332 E.h1334 E.S E.three
  have hQT : pCoreOf 2 (hz T V) ≤ T :=
    EscapingLocal.pCoreOf_le_of_isSylowTwoOf (isSylowTwoOf_of_le E.S.hyp E.t_le_hz)
  have hLTH : l1 T L V ⊔ T ≤ hz T V := sup_le (hL1K.trans E.k_le_hz) E.t_le_hz
  refine ⟨le_pCoreOf_of_le_normalizer 2 (hQT.trans le_sup_right)
    (hLTH.trans (le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _), ?_⟩
  exact EscapingLocal.pCoreOf_le_of_isSylowTwoOf (isSylowTwoOf_of_le E.S.hyp le_sup_right)

omit hF in
theorem le_centralizer_of_isMaxElemAbelian {x : G} (hxL : x ∈ l1 T L V) (hxH : x ∈ hz T V)
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) {V' : Subgroup G} (hV' : IsElemAbelian 2 V')
    (hV'R : V' ≤ pCoreOf 2 (l1 T L V ⊔ T)) (hcard : 32 < Nat.card V')
    (hV'n : hz T V ≤ Subgroup.normalizer (V' : Set G))
    (hQC : pCoreOf 2 (hz T V) ≤ Subgroup.centralizer (V' : Set G))
    (hfpf : ∀ v ∈ V', x * v * x⁻¹ = v → v = 1) {A : Subgroup G}
    (hA : IsMaxElemAbelian (pCoreOf 2 (l1 T L V ⊔ T)) A) :
    A ≤ Subgroup.centralizer (V' : Set G) := by
  by_contra hAC
  obtain ⟨-, hR1T⟩ := E.qh_le_r1
  have hAT : A ≤ T := hA.1.trans hR1T
  have hAH : A ≤ hz T V := hAT.trans E.t_le_hz
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    F7.isElemAbelian_comm hA.2.1 ha hb
  have hA2 : ∀ a ∈ A, a * a = 1 := fun a ha => by
    rw [← sq]
    exact F7.isElemAbelian_pow_eq_one hA.2.1 ha
  have hVc : ∀ a ∈ V', ∀ b ∈ V', a * b = b * a := fun a ha b hb => F7.isElemAbelian_comm hV' ha hb
  have hV2 : ∀ v ∈ V', v * v = 1 := fun v hv => by
    rw [← sq]
    exact F7.isElemAbelian_pow_eq_one hV' hv
  have hxV := hV'n hxH
  have hB := card_le_relIndex_mul_card hV' hV'R hA
  have hidx : (A ⊓ Subgroup.centralizer (V' : Set G)).relIndex A ≤
      (A ⊓ pCoreOf 2 (hz T V)).relIndex A :=
    Subgroup.relIndex_le_of_le_left (inf_le_inf_left A hQC) (by
      rw [Subgroup.relIndex]
      exact Subgroup.index_ne_zero_of_finite)
  obtain ⟨hrel4, hrel2⟩ := E.relIndex_le hxL hxH hx3 hx1 hAT hAc hA2
  have hq : ∀ q ∈ pCoreOf 2 (hz T V), ∀ v ∈ V', q * v * q⁻¹ = v := fun q hq v hv => by
    rw [← Subgroup.mem_centralizer_iff.mp (hQC hq) v hv]
    group
  have hCA : ∀ a ∈ A, Nat.card ↥(V' ⊓ Subgroup.centralizer (A : Set G)) ≤
      Nat.card ↥(V' ⊓ Subgroup.centralizer ({a} : Set G)) := fun a ha =>
    Subgroup.card_le_of_le (inf_le_inf_left V' (Subgroup.centralizer_le (by simpa using ha)))
  have hpos : 0 < Nat.card ↥(V' ⊓ Subgroup.centralizer (A : Set G)) := Nat.card_pos
  by_cases hall : ∀ a ∈ A, a * x * a⁻¹ * x⁻¹ ∈ pCoreOf 2 (hz T V)
  ·
    obtain ⟨a, haA, haC⟩ := IsConcreteLE.not_le_iff_exists.mp hAC
    have hnt : ∃ v ∈ V', a * v * a⁻¹ ≠ v := by
      by_contra hno
      push Not at hno
      refine haC (Subgroup.mem_centralizer_iff.mpr fun v hv => ?_)
      calc v * a = a * v * a⁻¹ * a := by rw [hno v hv]
        _ = a * v := by group
    have hcomm : ∀ v ∈ V', x * (a * v * a⁻¹) * x⁻¹ = a * (x * v * x⁻¹) * a⁻¹ := by
      intro v hv
      have hq0 := hall a haA
      have hav : a * v * a⁻¹ ∈ V' := (Subgroup.mem_normalizer_iff.mp (hV'n (hAH haA)) v).mp hv
      have hxav : x * (a * v * a⁻¹) * x⁻¹ ∈ V' :=
        (Subgroup.mem_normalizer_iff.mp hxV _).mp hav
      have h1 := hq _ hq0 _ hxav
      calc x * (a * v * a⁻¹) * x⁻¹ =
          (a * x * a⁻¹ * x⁻¹) * (x * (a * v * a⁻¹) * x⁻¹) * (a * x * a⁻¹ * x⁻¹)⁻¹ := h1.symm
        _ = a * (x * v * x⁻¹) * a⁻¹ := by group
    have h4 := card_inf_centralizer_mul_four_le hVc hV2 hxV (hV'n (hAH haA)) hfpf hcomm hnt
    have h2 := hrel2 hall
    have h5 := hCA a haA
    have h6 : (A ⊓ Subgroup.centralizer (V' : Set G)).relIndex A *
        Nat.card ↥(V' ⊓ Subgroup.centralizer (A : Set G)) ≤
          2 * Nat.card ↥(V' ⊓ Subgroup.centralizer (A : Set G)) :=
      Nat.mul_le_mul_right _ (hidx.trans h2)
    omega
  ·
    push Not at hall
    obtain ⟨a₀, ha₀, ha₀x⟩ := hall
    have hq0 := (E.conj_cases_three hxL hxH hx3 hx1 (hAH ha₀)).resolve_left ha₀x
    have hinv : ∀ v ∈ V', a₀ * (x * v * x⁻¹) * a₀⁻¹ = x⁻¹ * (a₀ * v * a₀⁻¹) * x := by
      intro v hv
      have hav : a₀ * v * a₀⁻¹ ∈ V' :=
        (Subgroup.mem_normalizer_iff.mp (hV'n (hAH ha₀)) v).mp hv
      have hxav : x⁻¹ * (a₀ * v * a₀⁻¹) * x ∈ V' := by
        have := (Subgroup.mem_normalizer_iff.mp (inv_mem hxV) _).mp hav
        simpa using this
      have h1 := hq _ hq0 _ hxav
      calc a₀ * (x * v * x⁻¹) * a₀⁻¹ =
          (a₀ * x * a₀⁻¹ * x) * (x⁻¹ * (a₀ * v * a₀⁻¹) * x) * (a₀ * x * a₀⁻¹ * x)⁻¹ := by
            group
        _ = x⁻¹ * (a₀ * v * a₀⁻¹) * x := h1
    have h4 := card_inf_centralizer_mul_self_le hxV hx3 hfpf hinv
    have h5 := hCA a₀ ha₀
    have h6 : (A ⊓ Subgroup.centralizer (V' : Set G)).relIndex A *
        Nat.card ↥(V' ⊓ Subgroup.centralizer (A : Set G)) ≤
          4 * Nat.card ↥(V' ⊓ Subgroup.centralizer ({a₀} : Set G)) :=
      Nat.mul_le_mul (hidx.trans hrel4) h5
    have h7 : Nat.card ↥(V' ⊓ Subgroup.centralizer ({a₀} : Set G)) ≤ 4 := by nlinarith
    omega

omit hF in
theorem hz_le_normalizer_baum {x : G} (hxL : x ∈ l1 T L V) (hxH : x ∈ hz T V)
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) {V' : Subgroup G} (hV' : IsElemAbelian 2 V')
    (hV'R : V' ≤ pCoreOf 2 (l1 T L V ⊔ T)) (hcard : 32 < Nat.card V')
    (hV'n : hz T V ≤ Subgroup.normalizer (V' : Set G))
    (hQC : pCoreOf 2 (hz T V) ≤ Subgroup.centralizer (V' : Set G))
    (hCQ : hz T V ⊓ Subgroup.centralizer (V' : Set G) ≤ pCoreOf 2 (hz T V))
    (hfpf : ∀ v ∈ V', x * v * x⁻¹ = v → v = 1) :
    hz T V ≤ Subgroup.normalizer (baum (pCoreOf 2 (l1 T L V ⊔ T)) : Set G) := by
  obtain ⟨hQR, hR1T⟩ := E.qh_le_r1
  have hJ : thompsonJ (pCoreOf 2 (l1 T L V ⊔ T)) ≤
      pCoreOf 2 (l1 T L V ⊔ T) ⊓ Subgroup.centralizer (V' : Set G) :=
    iSup₂_le fun A hA => le_inf hA.1
      (E.le_centralizer_of_isMaxElemAbelian hxL hxH hx3 hx1 hV' hV'R hcard hV'n hQC hfpf hA)
  have hRC : pCoreOf 2 (l1 T L V ⊔ T) ⊓ Subgroup.centralizer (V' : Set G) =
      pCoreOf 2 (hz T V) :=
    le_antisymm (fun g hg => hCQ (Subgroup.mem_inf.mpr
      ⟨E.t_le_hz (hR1T (Subgroup.mem_inf.mp hg).1), (Subgroup.mem_inf.mp hg).2⟩))
      (le_inf hQR hQC)
  rw [baum_eq_baum_centralizer hV' hV'R hJ, hRC]
  exact (le_normalizer_pCoreOf 2 _).trans (normalizer_le_normalizer_baum _)

end Ctx7153

end CFSG.Quasithin.H13.L32A
