module

public import CFSG.Quasithin.Vol2.Ch10SecC9Irr
public import CFSG.Quasithin.Vol2.Ch10SecC9S4b

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] {L W W' Y V : Subgroup G}

theorem exists_mul_of_mem_sup (hc : ∀ a ∈ W, ∀ b ∈ W', a * b = b * a) {y : G}
    (hy : y ∈ W ⊔ W') : ∃ w ∈ W, ∃ w' ∈ W', w * w' = y := by
  have hC : W' ≤ Subgroup.centralizer (W : Set G) := fun b hb =>
    Subgroup.mem_centralizer_iff.mpr fun a ha => hc a ha b hb
  have hN : W' ≤ Subgroup.normalizer (W : Set G) :=
    hC.trans (Subgroup.centralizer_le_normalizer _)
  have hy' : y ∈ (↑(W ⊔ W') : Set G) := hy
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hN] at hy'
  obtain ⟨w, hw, w', hw', h⟩ := hy'
  exact ⟨w, hw, w', hw', h⟩

theorem eq_of_mul_mem (hYW' : Y ⊓ W' = ⊥) {w a b : G} (ha : a ∈ W') (hb : b ∈ W')
    (h1 : w * a ∈ Y) (h2 : w * b ∈ Y) : a = b := by
  have hmem : (w * a)⁻¹ * (w * b) ∈ Y ⊓ W' := by
    refine ⟨Y.mul_mem (Y.inv_mem h1) h2, ?_⟩
    rw [mul_inv_rev, mul_assoc, inv_mul_cancel_left]
    exact W'.mul_mem (W'.inv_mem ha) hb
  rw [hYW', Subgroup.mem_bot, mul_inv_rev, mul_assoc, inv_mul_cancel_left,
    inv_mul_eq_one] at hmem
  exact hmem

@[expose] noncomputable def botEquiv (W : Subgroup G) :
    ↥W ⧸ (⊥ : Subgroup G).subgroupOf W ≃* ↥W :=
  (QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf W)).trans QuotientGroup.quotientBot

theorem botEquiv_mk (W : Subgroup G) (w : ↥W) :
    botEquiv W (w : ↥W ⧸ (⊥ : Subgroup G).subgroupOf W) = w := rfl

theorem isXSectionIso_of_diag (hc : ∀ a ∈ W, ∀ b ∈ W', a * b = b * a) (hYW : Y ⊓ W = ⊥)
    (hYW' : Y ⊓ W' = ⊥) (hp : ∀ w ∈ W, ∃ w' ∈ W', w * w' ∈ Y)
    (hp' : ∀ w' ∈ W', ∃ w ∈ W, w * w' ∈ Y) (hLY : L ≤ Subgroup.normalizer (Y : Set G)) :
    IsXSectionIso L ⊥ W W' := by
  choose f hfW hfY using hp
  let φ : ↥W →* ↥W' :=
    { toFun := fun w => ⟨f w w.2, hfW w w.2⟩
      map_one' := Subtype.ext (eq_of_mul_mem hYW' (hfW 1 W.one_mem) W'.one_mem
        (hfY 1 W.one_mem) (by simp))
      map_mul' := fun a b => by
        apply Subtype.ext
        refine eq_of_mul_mem hYW' (hfW _ (W.mul_mem a.2 b.2))
          (W'.mul_mem (hfW a a.2) (hfW b b.2)) (hfY _ _) ?_
        have e : (a : G) * b * (f a a.2 * f b b.2) = (a * f a a.2) * (b * f b b.2) := by
          simp only [mul_assoc]
          rw [← mul_assoc (b : G), hc b b.2 _ (hfW a a.2), mul_assoc]
        simp only [Subgroup.coe_mul]
        rw [e]
        exact Y.mul_mem (hfY a a.2) (hfY b b.2) }
  have hφ : ∀ w : ↥W, ((φ w : ↥W') : G) = f w w.2 := fun _ => rfl
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro w hw
    have h1 : (w : G) ∈ Y ⊓ W := by
      refine ⟨?_, w.2⟩
      have := hfY w w.2
      rwa [← hφ, hw, Subgroup.coe_one, mul_one] at this
    rw [hYW, Subgroup.mem_bot] at h1
    exact Subtype.ext h1
  have hsurj : Function.Surjective φ := by
    rintro ⟨w', hw'⟩
    obtain ⟨w, hw, hY⟩ := hp' w' hw'
    exact ⟨⟨w, hw⟩, Subtype.ext (eq_of_mul_mem hYW' (hfW w hw) hw' (hfY w hw) hY)⟩
  have hbij : Function.Bijective φ := ⟨hinj, hsurj⟩
  let e : ↥W ⧸ (⊥ : Subgroup G).subgroupOf W ≃* ↥W' ⧸ (⊥ : Subgroup G).subgroupOf W' :=
    (botEquiv W).trans ((MulEquiv.ofBijective φ hbij).trans (botEquiv W').symm)
  refine ⟨by rw [Subgroup.bot_subgroupOf]; infer_instance,
    by rw [Subgroup.bot_subgroupOf]; infer_instance, e, ?_⟩
  have key : ∀ a : ↥W, e (a : ↥W ⧸ (⊥ : Subgroup G).subgroupOf W) =
      ((φ a : ↥W') : ↥W' ⧸ (⊥ : Subgroup G).subgroupOf W') := by
    intro a
    show (botEquiv W').symm ((MulEquiv.ofBijective φ hbij) (botEquiv W _)) = _
    rw [botEquiv_mk, MulEquiv.ofBijective_apply, MulEquiv.symm_apply_eq, botEquiv_mk]
  intro x hx j k hj hk hjk
  rw [key] at hjk
  have hjk' : φ j = k := by
    have := congrArg (botEquiv W') hjk
    rwa [botEquiv_mk, botEquiv_mk] at this
  rw [key]
  congr 1
  apply Subtype.ext
  rw [hφ]
  refine eq_of_mul_mem hYW' (hfW _ hj) hk (hfY _ hj) ?_
  have hY' := (Subgroup.mem_normalizer_iff.mp (hLY hx) _).mp (hfY j j.2)
  have e2 : x * (j : G) * x⁻¹ * (x * k * x⁻¹) = x * (j * f j j.2) * x⁻¹ := by
    rw [← hjk', hφ]; group
  rw [e2]
  exact hY'

theorem exists_mul_mem_of_irrG (hc : ∀ a ∈ W, ∀ b ∈ W', a * b = b * a) (hYs : Y ≤ W ⊔ W')
    (hYW' : Y ⊓ W' = ⊥) (hY : Y ≠ ⊥) (hirr : IrrG L W)
    (hLY : L ≤ Subgroup.normalizer (Y : Set G)) (hLW : L ≤ Subgroup.normalizer (W : Set G))
    (hLW' : L ≤ Subgroup.normalizer (W' : Set G)) : ∀ w ∈ W, ∃ w' ∈ W', w * w' ∈ Y := by
  let P : Subgroup G :=
    { carrier := {w | w ∈ W ∧ ∃ w' ∈ W', w * w' ∈ Y}
      one_mem' := ⟨W.one_mem, 1, W'.one_mem, by rw [mul_one]; exact Y.one_mem⟩
      mul_mem' := by
        rintro a b ⟨ha, a', ha', haY⟩ ⟨hb, b', hb', hbY⟩
        refine ⟨W.mul_mem ha hb, a' * b', W'.mul_mem ha' hb', ?_⟩
        have e : a * b * (a' * b') = (a * a') * (b * b') := by
          simp only [mul_assoc]
          rw [← mul_assoc b, hc b hb a' ha', mul_assoc]
        rw [e]
        exact Y.mul_mem haY hbY
      inv_mem' := by
        rintro a ⟨ha, a', ha', haY⟩
        refine ⟨W.inv_mem ha, a'⁻¹, W'.inv_mem ha', ?_⟩
        have e : a⁻¹ * a'⁻¹ = (a * a')⁻¹ := by
          rw [mul_inv_rev, ← hc _ (W.inv_mem ha) _ (W'.inv_mem ha')]
        rw [e]
        exact Y.inv_mem haY }
  have hconj : ∀ x ∈ L, ∀ w ∈ P, x * w * x⁻¹ ∈ P := by
    rintro x hx w ⟨hw, w', hw', hwY⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hLW hx) w).mp hw, x * w' * x⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hLW' hx) w').mp hw', ?_⟩
    have e : x * w * x⁻¹ * (x * w' * x⁻¹) = x * (w * w') * x⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hLY hx) _).mp hwY
  have hPN : L ≤ Subgroup.normalizer (P : Set G) := fun x hx => by
    rw [Subgroup.mem_normalizer_iff]
    intro w
    refine ⟨hconj x hx w, fun h => ?_⟩
    have := hconj x⁻¹ (L.inv_mem hx) _ h
    rwa [inv_inv, show x⁻¹ * (x * w * x⁻¹) * x = w by group] at this
  have hP : P ≠ ⊥ := by
    obtain ⟨⟨y, hy⟩, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hY
    obtain ⟨w, hw, w', hw', rfl⟩ := exists_mul_of_mem_sup hc (hYs hy)
    intro hPb
    have hwP : w ∈ P := ⟨hw, w', hw', hy⟩
    rw [hPb, Subgroup.mem_bot] at hwP
    subst hwP
    have : w' ∈ Y ⊓ W' := ⟨by simpa using hy, hw'⟩
    rw [hYW', Subgroup.mem_bot] at this
    exact hy1 (Subtype.ext (by simp [this]))
  rcases hirr.2 P (fun _ h => h.1) hPN with h | h
  · exact absurd h hP
  · intro w hw
    have : w ∈ P := h ▸ hw
    exact this.2

theorem eq_bot_of_disjoint (hc : ∀ a ∈ W, ∀ b ∈ W', a * b = b * a) (hirr : IrrG L W)
    (hirr' : IrrG L W') (hLW : L ≤ Subgroup.normalizer (W : Set G))
    (hLW' : L ≤ Subgroup.normalizer (W' : Set G)) (hni : ¬ IsXSectionIso L ⊥ W W') {D : Subgroup G}
    (hDs : D ≤ W ⊔ W') (hLD : L ≤ Subgroup.normalizer (D : Set G)) (hDW : D ⊓ W = ⊥)
    (hDW' : D ⊓ W' = ⊥) : D = ⊥ := by
  by_contra hD
  refine hni (isXSectionIso_of_diag hc hDW hDW'
    (exists_mul_mem_of_irrG hc hDs hDW' hD hirr hLD hLW hLW') (fun w' hw' => ?_) hLD)
  obtain ⟨w, hw, h⟩ := exists_mul_mem_of_irrG (W := W') (W' := W)
    (fun a ha b hb => (hc b hb a ha).symm) (sup_comm W W' ▸ hDs) hDW hD hirr' hLD hLW' hLW w' hw'
  exact ⟨w, hw, by rwa [hc w hw w' hw']⟩

theorem mem_normalizer_of_noDiag [Finite G] {r : G} (hinf : W ⊓ W' = ⊥) (hirr' : IrrG L W')
    (hLW' : L ≤ Subgroup.normalizer (W' : Set G))
    (hnd : ∀ D : Subgroup G, D ≤ W ⊔ W' → L ≤ Subgroup.normalizer (D : Set G) → D ⊓ W = ⊥ →
      D ⊓ W' = ⊥ → D = ⊥)
    (hrV : r ∈ Subgroup.normalizer ((W ⊔ W' : Subgroup G) : Set G))
    (hrL : r ∈ Subgroup.normalizer (L : Set G)) (hrW : r ∈ Subgroup.normalizer (W : Set G)) :
    r ∈ Subgroup.normalizer (W' : Set G) := by
  let D := W'.map (MulAut.conj r).toMonoidHom
  have hmem : ∀ x, x ∈ D ↔ r⁻¹ * x * r ∈ W' := fun x => by
    rw [Subgroup.mem_map_equiv]; simp [MulAut.conj_symm_apply]
  have hrD : ∀ g ∈ W', r * g * r⁻¹ ∈ D := fun g hg => (hmem _).mpr (by group; exact hg)
  have hDs : D ≤ W ⊔ W' := fun x hx => by
    have h1 : r⁻¹ * x * r ∈ W ⊔ W' := (le_sup_right : W' ≤ W ⊔ W') ((hmem x).mp hx)
    have := (Subgroup.mem_normalizer_iff.mp hrV (r⁻¹ * x * r)).mp h1
    rwa [show r * (r⁻¹ * x * r) * r⁻¹ = x by group] at this
  have hLD : L ≤ Subgroup.normalizer (D : Set G) := fun l hl => by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [hmem, hmem]
    have hl' : r⁻¹ * l * r ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hrL) l).mp hl
      rwa [inv_inv] at this
    have e : r⁻¹ * (l * x * l⁻¹) * r = (r⁻¹ * l * r) * (r⁻¹ * x * r) * (r⁻¹ * l * r)⁻¹ := by
      group
    rw [e]
    exact Subgroup.mem_normalizer_iff.mp (hLW' hl') _
  have hDW : D ⊓ W = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxD, hxW⟩
    have h1 : r⁻¹ * x * r ∈ W := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hrW) x).mp hxW
      rwa [inv_inv] at this
    have h2 : r⁻¹ * x * r ∈ W ⊓ W' := ⟨h1, (hmem x).mp hxD⟩
    rw [hinf, Subgroup.mem_bot] at h2
    rw [Subgroup.mem_bot]
    calc x = r * (r⁻¹ * x * r) * r⁻¹ := by group
      _ = 1 := by rw [h2]; group
  rcases hirr'.2 (D ⊓ W') inf_le_right
      (fun l hl => mem_normalizer_inf' (hLD hl) (hLW' hl)) with h | h
  · have := hnd D hDs hLD hDW h
    exact absurd (by
      have h0 : D = ⊥ := this
      rw [eq_bot_iff] at h0
      obtain ⟨⟨g, hg⟩, hg1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hirr'.1
      have := h0 (hrD g hg)
      rw [Subgroup.mem_bot] at this
      exact hg1 (Subtype.ext (by
        calc g = r⁻¹ * (r * g * r⁻¹) * r := by group
          _ = 1 := by rw [this]; group)) : False) id
  · have hW'D : W' ≤ D := h ▸ inf_le_left
    have hcard : Nat.card D = Nat.card W' :=
      Subgroup.card_map_of_injective (MulAut.conj r).injective
    have hDW'eq : D = W' := (Subgroup.eq_of_le_of_card_ge hW'D hcard.le).symm
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · intro hg
      rw [← hDW'eq]
      exact hrD g hg
    · intro hg
      rw [← hDW'eq, hmem] at hg
      rwa [show r⁻¹ * (r * g * r⁻¹) * r = g by group] at hg

end CFSG.Quasithin.Vol2.Ch10.SecC
