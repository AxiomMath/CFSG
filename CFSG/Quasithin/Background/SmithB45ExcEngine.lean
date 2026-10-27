module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeGen
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyOffenderAssembly

public section

namespace CFSG.Quasithin.B45Exc

open CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.Setup.Family

section Basic

variable {W : Type} [CommGroup W] [Finite W]

theorem weight2_lt_of_lt_index (E : Subgroup (MulAut W))
    (h : Nat.card E ^ 2 < (fixV E).index) : Nat.card E ^ 2 * Nat.card (fixV E) < Nat.card W := by
  have hmul := Subgroup.card_mul_index (fixV E)
  have hpos : 0 < Nat.card (fixV E) := Nat.card_pos
  rw [← hmul]
  nlinarith

theorem index_le_sq_of_offender2 (E : Subgroup (MulAut W))
    (h : Nat.card W ≤ Nat.card E ^ 2 * Nat.card (fixV E)) : (fixV E).index ≤ Nat.card E ^ 2 := by
  by_contra hcon
  push Not at hcon
  have := weight2_lt_of_lt_index E hcon
  omega

theorem index_zpowers_le_index (E : Subgroup (MulAut W)) {b : MulAut W} (hb : b ∈ E) :
    (fixV (Subgroup.zpowers b)).index ≤ (fixV E).index := by
  apply Subgroup.index_antitone
  apply fixV_anti
  rw [Subgroup.zpowers_le]
  exact hb

theorem weight2_lt_of_rank {E : Subgroup (MulAut W)} (hEne : E ≠ ⊥) {r ρ : ℕ} (hρ : 2 * r < ρ)
    (hcard : Nat.card E ≤ 2 ^ r)
    (hrank : ∀ b ∈ E, b ≠ 1 → 2 ^ ρ ≤ (fixV (Subgroup.zpowers b)).index) :
    Nat.card E ^ 2 * Nat.card (fixV E) < Nat.card W := by
  obtain ⟨⟨b, hbE⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hEne
  have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
  refine weight2_lt_of_lt_index E ?_
  calc Nat.card E ^ 2 ≤ (2 ^ r) ^ 2 := Nat.pow_le_pow_left hcard 2
    _ = 2 ^ (2 * r) := by rw [← pow_mul, mul_comm]
    _ < 2 ^ ρ := Nat.pow_lt_pow_right (by norm_num) hρ
    _ ≤ (fixV (Subgroup.zpowers b)).index := hrank b hbE hb1'
    _ ≤ (fixV E).index := index_zpowers_le_index E hbE

theorem exists_two_ne_one {G : Type*} [Group G] {E : Subgroup G} [Finite E]
    (h : ¬ Nat.card E ≤ 2) : ∃ t ∈ E, ∃ u ∈ E, t ≠ 1 ∧ u ≠ 1 ∧ t ≠ u := by
  by_contra hcon
  push Not at hcon
  apply h
  by_cases hne : ∃ t ∈ E, t ≠ 1
  · obtain ⟨t, htE, ht1⟩ := hne
    have hsub : (E : Set G) ⊆ {1, t} := by
      intro u hu
      by_cases hu1 : u = 1
      · exact Or.inl hu1
      · exact Or.inr (hcon t htE u hu ht1 hu1).symm
    calc Nat.card E = Set.ncard (E : Set G) := (Nat.card_coe_set_eq _).symm
      _ ≤ Set.ncard ({1, t} : Set G) := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ Set.ncard ({t} : Set G) + 1 := Set.ncard_insert_le _ _
      _ = 2 := by rw [Set.ncard_singleton]
  · push Not at hne
    have : E = ⊥ := (Subgroup.eq_bot_iff_forall E).2 hne
    rw [this, Subgroup.card_bot]
    norm_num

end Basic

@[expose] def SporadicExclusion2F (s : TauCeti.SporadicName) : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w * w = 1) →
    ∀ L E : Subgroup (MulAut W), CFSG.IsQuasisimple ↥L → IsIrrOn L →
      Nonempty (CQ L ≃* CFSG.Blueprint.NativeSporadic.Carrier s) →
      E ≤ Subgroup.normalizer (L : Set (MulAut W)) → E ≠ ⊥ → IsElemAbelian2 E →
      Nat.card E ^ 2 * Nat.card (fixV E) < Nat.card W

section Inner

variable {W : Type} [CommGroup W] [Finite W]

theorem exclusion2F_of_autInner (hW : ∀ w : W, w * w = 1) {L E : Subgroup (MulAut W)}
    (hperf : Group.IsPerfect ↥L) (hirr : IsIrrOn L)
    (hE : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hEne : E ≠ ⊥) (hEel : IsElemAbelian2 E)
    {S : Type} [Group S] (e : CQ L ≃* S)
    (hAut : ∀ φ : S ≃* S, ∃ s : S, ∀ x, φ x = s * x * s⁻¹) {r ρ : ℕ} (hρ : 2 * r < ρ)
    (hr : ∀ B : Subgroup S, (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) →
      Nat.card B ≤ 2 ^ r)
    (hrank : ∀ b : MulAut W, b ∈ L → b ≠ 1 → b * b = 1 →
      2 ^ ρ ≤ (fixV (Subgroup.zpowers b)).index) :
    Nat.card E ^ 2 * Nat.card (fixV E) < Nat.card W := by
  have hEL : E ≤ L := le_of_autInner hW hperf hirr hE hEel e hAut
  have hcard := card_le_two_pow_of_le hW hirr hEL hEel e hr
  refine weight2_lt_of_rank hEne hρ hcard fun b hb hb1 => hrank b (hEL hb) hb1 ?_
  have := hEel.2 b hb
  rwa [sq] at this

end Inner

section ThreeConj

variable {W : Type} [CommGroup W] [Finite W]

theorem weight2_lt_of_three_conj (hW : ∀ w : W, w * w = 1) {L E : Subgroup (MulAut W)}
    (hperf : Group.IsPerfect ↥L) (hirr : IsIrrOn L)
    (hE : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hEne : E ≠ ⊥) (hEel : IsElemAbelian2 E)
    {S : Type} [Group S] [Nontrivial S] (e : CQ L ≃* S) {r k ρ : ℕ} (hρ : 2 * r * k < ρ)
    (hCover : ∀ (E : Type) [Group E] [Finite E] [Group.IsPerfect E] (π : E →* S),
      Function.Surjective π → π.ker ≤ Subgroup.center E → Odd (Nat.card π.ker) → π.ker = ⊥)
    (hRank : ∀ B : Subgroup (MulAut S), (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
      (∀ x ∈ B, x * x = 1) → Nat.card B ≤ 2 ^ r)
    (hGen : ∀ ψ : MulAut S, ψ * ψ = 1 → ψ ≠ 1 → ∃ cs : List (MulAut S), cs.length = k ∧
      (∀ c ∈ cs, c ∈ (MulAut.conj : S →* MulAut S).range) ∧
      ∀ s : S, MulAut.conj s ∈ Subgroup.closure (conjSet cs {ψ}))
    (hDim : ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v * v = 1) →
      ∀ σ : S →* MulAut V, Function.Injective σ → 2 ^ ρ ≤ Nat.card V) :
    Nat.card E ^ 2 * Nat.card (fixV E) < Nat.card W := by
  have hZodd : Odd (Nat.card (Subgroup.center ↥L)) := by
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    have h2 : 2 ∣ Nat.card (Subgroup.center ↥L) := even_iff_two_dvd.1 hev
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have hcommZ : ∀ l ∈ L, l * ((x : ↥L) : MulAut W) = ((x : ↥L) : MulAut W) * l := by
      intro l hl
      have := Subgroup.mem_center_iff.1 x.2 ⟨l, hl⟩
      exact congrArg Subtype.val this
    have hxW : orderOf ((x : ↥L) : MulAut W) = 2 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]
    have hodd2 := odd_orderOf_of_commutes hW hirr hcommZ
    rw [hxW] at hodd2
    exact absurd hodd2 (by decide)
  have hker : (redHom L e).ker = Subgroup.center ↥L := by
    ext x
    exact redHom_eq_one_iff L e x
  have hker1 : (redHom L e).ker = ⊥ :=
    hCover ↥L (redHom L e) (redHom_surjective L e) (by rw [hker]) (by rw [hker]; exact hZodd)
  have hcent : Subgroup.center ↥L = ⊥ := by rw [← hker]; exact hker1
  have hinj : Function.Injective (redHom L e) := (MonoidHom.ker_eq_bot_iff _).1 hker1
  let eqv : ↥L ≃* S := MulEquiv.ofBijective (redHom L e) ⟨hinj, redHom_surjective L e⟩
  let σ : S →* MulAut W := L.subtype.comp eqv.symm.toMonoidHom
  have hσinj : Function.Injective σ := by
    intro x y hxy
    exact eqv.symm.injective (Subtype.ext hxy)
  have hdim : 2 ^ ρ ≤ Nat.card W := hDim W hW σ hσinj
  have hL : L ≠ ⊥ := by
    intro h
    obtain ⟨s, hs⟩ := exists_ne (1 : S)
    obtain ⟨l, rfl⟩ := redHom_surjective L e s
    apply hs
    have hall : ∀ x ∈ L, x = 1 := fun x hx => by
      rw [h] at hx
      exact Subgroup.mem_bot.1 hx
    have : l = 1 := Subtype.ext (hall l l.2)
    rw [this, map_one]
  have hact : Function.Injective (actS hE e) :=
    actS_injective_of_center hW hperf hirr hE hEel e hcent
  let ε : ↥E →* MulAut S := (actS hE e).comp (Subgroup.inclusion (le_sup_right : E ≤ L ⊔ E))
  have hεinj : Function.Injective ε := hact.comp (Subgroup.inclusion_injective _)
  have hEcard : Nat.card E ≤ 2 ^ r := by
    have hB : Nat.card ε.range = Nat.card E :=
      (Nat.card_congr (MonoidHom.ofInjective hεinj).toEquiv).symm
    rw [← hB]
    refine hRank ε.range ?_ ?_
    · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hEel.1 a a.2 b b.2)
    · rintro _ ⟨a, rfl⟩
      rw [← map_mul]
      have : a * a = 1 := Subtype.ext (by simpa [sq] using hEel.2 a a.2)
      rw [this, map_one]
  obtain ⟨⟨b, hbE⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hEne
  set b' : ↥(L ⊔ E) := ⟨b, Subgroup.mem_sup_right hbE⟩ with hb'
  have hb'1 : b' ≠ 1 := fun h => hb1 (Subtype.ext (by
    have := congrArg Subtype.val h
    simpa [hb'] using this))
  have hψ1 : actS hE e b' ≠ 1 := fun h => hb'1 (hact (h.trans (map_one _).symm))
  have hψ2 : actS hE e b' * actS hE e b' = 1 := by
    rw [← map_mul]
    have : b' * b' = 1 := Subtype.ext (by simpa [sq] using hEel.2 b hbE)
    rw [this, map_one]
  obtain ⟨cs, hcslen, hcsin, hcsgen⟩ := hGen _ hψ2 hψ1
  have hcsr : ∀ c ∈ cs, c ∈ (actS hE e).range := by
    intro c hc
    obtain ⟨s, rfl⟩ := hcsin c hc
    exact conj_mem_range_actS hE e s
  have hgen : ∀ s : S, MulAut.conj s ∈ Subgroup.closure {y : MulAut S | ∃ c ∈ cs,
      ∃ b : ↥(L ⊔ E), (b : MulAut W) ∈ E ∧ y = c * actS hE e b * c⁻¹} := by
    intro s
    refine Subgroup.closure_mono ?_ (hcsgen s)
    rintro _ ⟨c, hc, t, ht, rfl⟩
    have : t = actS hE e b' := by simpa using ht
    subst this
    exact ⟨c, hc, b', hbE, rfl⟩
  have hbound := card_le_index_pow_of_inn_le hW hperf hirr hL hE hEel e cs hcsr hgen
  rw [hcslen] at hbound
  refine weight2_lt_of_lt_index E ?_
  by_contra hcon
  push Not at hcon
  have h1 : (fixV E).index ^ k ≤ 2 ^ (2 * r * k) :=
    calc (fixV E).index ^ k ≤ ((2 ^ r) ^ 2) ^ k :=
          Nat.pow_le_pow_left (hcon.trans (Nat.pow_le_pow_left hEcard 2)) k
      _ = 2 ^ (2 * r * k) := by rw [← pow_mul, ← pow_mul]; ring_nf
  have h2 : 2 ^ (2 * r * k) < 2 ^ ρ := Nat.pow_lt_pow_right (by norm_num) hρ
  omega

end ThreeConj

section OrderFour

variable {W : Type} [CommGroup W]

@[expose] def dispHom (g : MulAut W) : W →* W where
  toFun v := g v * v⁻¹
  map_one' := by simp
  map_mul' a b := by
    rw [map_mul, mul_inv]
    exact mul_mul_mul_comm _ _ _ _

theorem dispHom_apply (g : MulAut W) (v : W) : dispHom g v = g v * v⁻¹ := rfl

theorem dispHom_eq_one_iff (g : MulAut W) (v : W) : dispHom g v = 1 ↔ g v = v := by
  rw [dispHom_apply, mul_inv_eq_one]

theorem mem_fixV_zpowers_iff_dispHom {g : MulAut W} {v : W} :
    v ∈ fixV (Subgroup.zpowers g) ↔ dispHom g v = 1 := by
  rw [mem_fixV_zpowers, dispHom_eq_one_iff]

theorem dispHom_dispHom (hW : ∀ w : W, w * w = 1) (g : MulAut W) (v : W) :
    dispHom g (dispHom g v) = dispHom (g ^ 2) v := by
  have hinv : ∀ x : W, x⁻¹ = x := fun x => inv_eq_of_mul_eq_one_right (hW x)
  simp only [dispHom_apply, map_mul, hinv, pow_two, MulAut.mul_apply]
  have h1 : g v * g v = 1 := hW _
  calc g (g v) * g v * (g v * v) = g (g v) * (g v * g v) * v := by
        simp only [mul_assoc]
    _ = g (g v) * v := by rw [h1, mul_one]

theorem dispHom_four (hW : ∀ w : W, w * w = 1) {g : MulAut W} (h4 : g ^ 4 = 1) (v : W) :
    dispHom g (dispHom g (dispHom g (dispHom g v))) = 1 := by
  rw [dispHom_dispHom hW, dispHom_dispHom hW, dispHom_dispHom hW]
  rw [← pow_mul, show 2 * 2 = 4 by norm_num, h4, dispHom_apply]
  simp

theorem fixV_lt_fixV_sq (hW : ∀ w : W, w * w = 1) {w : MulAut W} (h4 : w ^ 4 = 1)
    (h2 : w ^ 2 ≠ 1) :
    fixV (Subgroup.zpowers w) < fixV (Subgroup.zpowers (w ^ 2)) := by
  have hle : fixV (Subgroup.zpowers w) ≤ fixV (Subgroup.zpowers (w ^ 2)) := by
    apply fixV_anti
    rw [Subgroup.zpowers_le]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers w) 2
  refine lt_of_le_of_ne hle fun heq => h2 ?_
  have hk : ∀ v : W, dispHom w (dispHom w v) = 1 → dispHom w v = 1 := by
    intro v hv
    have hv2 : v ∈ fixV (Subgroup.zpowers (w ^ 2)) := by
      rw [mem_fixV_zpowers_iff_dispHom, ← dispHom_dispHom hW]
      exact hv
    rw [← heq, mem_fixV_zpowers_iff_dispHom] at hv2
    exact hv2
  have hall : ∀ v : W, w v = v := by
    intro v
    rw [← dispHom_eq_one_iff]
    exact hk v (hk _ (hk _ (dispHom_four hW h4 v)))
  have hw1 : w = 1 := MulEquiv.ext hall
  rw [hw1, one_pow]

theorem index_fixV_lt_of_sq [Finite W] (hW : ∀ w : W, w * w = 1) {w : MulAut W}
    (h4 : w ^ 4 = 1) (h2 : w ^ 2 ≠ 1) :
    (fixV (Subgroup.zpowers (w ^ 2))).index < (fixV (Subgroup.zpowers w)).index := by
  have hlt := fixV_lt_fixV_sq hW h4 h2
  have h1 := Subgroup.card_mul_index (fixV (Subgroup.zpowers w))
  have h2' := Subgroup.card_mul_index (fixV (Subgroup.zpowers (w ^ 2)))
  have hc : Nat.card (fixV (Subgroup.zpowers w)) < Nat.card (fixV (Subgroup.zpowers (w ^ 2))) :=
    Subgroup.card_lt_of_lt hlt
  have hpos : 0 < (fixV (Subgroup.zpowers (w ^ 2))).index :=
    Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  by_contra hcon
  push Not at hcon
  have : Nat.card (fixV (Subgroup.zpowers (w ^ 2))) * (fixV (Subgroup.zpowers (w ^ 2))).index >
      Nat.card (fixV (Subgroup.zpowers w)) * (fixV (Subgroup.zpowers w)).index :=
    Nat.mul_lt_mul_of_lt_of_le hc hcon hpos
  omega

theorem mem_fixV_zpowers_conj {g x : MulAut W} {v : W} :
    v ∈ fixV (Subgroup.zpowers (g * x * g⁻¹)) ↔ g⁻¹ v ∈ fixV (Subgroup.zpowers x) := by
  rw [mem_fixV_zpowers, mem_fixV_zpowers]
  constructor
  · intro h
    have h1 : g (x (g⁻¹ v)) = v := h
    have h2 := congrArg (fun u => g⁻¹ u) h1
    simpa only [MulAut.inv_apply_self] using h2
  · intro h
    show g (x (g⁻¹ v)) = v
    rw [h, MulAut.apply_inv_self]

theorem fixV_le_fixV_conj {t e g : MulAut W} (hte : fixV (Subgroup.zpowers t) ≤
    fixV (Subgroup.zpowers e)) (hg : g * t = t * g) :
    fixV (Subgroup.zpowers t) ≤ fixV (Subgroup.zpowers (g * e * g⁻¹)) := by
  intro v hv
  rw [mem_fixV_zpowers_conj]
  apply hte
  rw [mem_fixV_zpowers] at hv ⊢
  have hgt : g⁻¹ * t = t * g⁻¹ := by
    calc g⁻¹ * t = g⁻¹ * (t * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * t) * g⁻¹ := by rw [hg]
      _ = t * g⁻¹ := by group
  calc t (g⁻¹ v) = (t * g⁻¹) v := rfl
    _ = (g⁻¹ * t) v := by rw [hgt]
    _ = g⁻¹ (t v) := rfl
    _ = g⁻¹ v := by rw [hv]

theorem fixV_le_fixV_mul {t x y : MulAut W} (hx : fixV (Subgroup.zpowers t) ≤
    fixV (Subgroup.zpowers x)) (hy : fixV (Subgroup.zpowers t) ≤ fixV (Subgroup.zpowers y)) :
    fixV (Subgroup.zpowers t) ≤ fixV (Subgroup.zpowers (x * y)) := by
  intro v hv
  rw [mem_fixV_zpowers] at ⊢
  have h1 := (mem_fixV_zpowers).1 (hx hv)
  have h2 := (mem_fixV_zpowers).1 (hy hv)
  show x (y v) = v
  rw [h2, h1]

theorem fixV_zpowers_le_pow (x : MulAut W) (n : ℕ) :
    fixV (Subgroup.zpowers x) ≤ fixV (Subgroup.zpowers (x ^ n)) := by
  apply fixV_anti
  rw [Subgroup.zpowers_le]
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers x) n

theorem fixV_le_fixV_zpowers {E : Subgroup (MulAut W)} {e : MulAut W} (he : e ∈ E) :
    fixV E ≤ fixV (Subgroup.zpowers e) := by
  apply fixV_anti
  rw [Subgroup.zpowers_le]
  exact he

theorem false_of_order_four [Finite W] (hW : ∀ w : W, w * w = 1) {t w : MulAut W}
    (htw : fixV (Subgroup.zpowers t) ≤ fixV (Subgroup.zpowers w)) (h4 : w ^ 4 = 1)
    (h2 : w ^ 2 ≠ 1)
    (hsq : (fixV (Subgroup.zpowers t)).index ≤ (fixV (Subgroup.zpowers (w ^ 2))).index) :
    False := by
  have h1 : (fixV (Subgroup.zpowers w)).index ≤ (fixV (Subgroup.zpowers t)).index :=
    Subgroup.index_antitone htw
  have h3 := index_fixV_lt_of_sq hW h4 h2
  omega

theorem fixV_eq_of_index_le [Finite W] {E : Subgroup (MulAut W)} {t : MulAut W} (ht : t ∈ E)
    (h : (fixV E).index ≤ (fixV (Subgroup.zpowers t)).index) :
    fixV E = fixV (Subgroup.zpowers t) := by
  have hle := fixV_le_fixV_zpowers (W := W) ht
  have hidx : (fixV (Subgroup.zpowers t)).index = (fixV E).index :=
    le_antisymm (Subgroup.index_antitone hle) h
  have hcard : Nat.card (fixV E) = Nat.card (fixV (Subgroup.zpowers t)) := by
    have h1 := Subgroup.card_mul_index (fixV E)
    have h2 := Subgroup.card_mul_index (fixV (Subgroup.zpowers t))
    rw [hidx] at h2
    have hpos : 0 < (fixV E).index := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
    exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)
  exact Subgroup.eq_of_le_of_card_ge hle hcard.symm.le

end OrderFour

section Lift

variable {W : Type} [CommGroup W] [Finite W]

theorem odd_orderOf_center (hW : ∀ w : W, w * w = 1) {L : Subgroup (MulAut W)} (hirr : IsIrrOn L)
    {z : ↥L} (hz : z ∈ Subgroup.center ↥L) : Odd (orderOf (z : MulAut W)) := by
  refine odd_orderOf_of_commutes hW hirr fun l hl => ?_
  exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨l, hl⟩)

theorem comm_of_redHom_comm (hW : ∀ w : W, w * w = 1) {L : Subgroup (MulAut W)} (hirr : IsIrrOn L)
    {S : Type} [Group S] (e : CQ L ≃* S) {s g : ↥L} (hs : s * s = 1)
    (hc : redHom L e g * redHom L e s = redHom L e s * redHom L e g) : g * s = s * g := by
  set z : ↥L := g * s * g⁻¹ * s with hz
  have hzc : z ∈ Subgroup.center ↥L := by
    rw [← redHom_eq_one_iff L e]
    have hs' : redHom L e s * redHom L e s = 1 := by rw [← map_mul, hs, map_one]
    rw [hz, map_mul, map_mul, map_mul, map_inv]
    calc redHom L e g * redHom L e s * (redHom L e g)⁻¹ * redHom L e s
        = redHom L e s * redHom L e g * (redHom L e g)⁻¹ * redHom L e s := by rw [hc]
      _ = 1 := by rw [mul_inv_cancel_right, hs']
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have hzs : g * s * g⁻¹ = z * s := by rw [hz, mul_assoc _ s s, hs, mul_one]
  have hz2 : z * z = 1 := by
    have h1 : (g * s * g⁻¹) * (g * s * g⁻¹) = 1 := by
      calc (g * s * g⁻¹) * (g * s * g⁻¹) = g * (s * s) * g⁻¹ := by group
        _ = 1 := by rw [hs, mul_one, mul_inv_cancel]
    rw [hzs] at h1
    have hcomm : z * s = s * z := (Subgroup.mem_center_iff.1 hzc s).symm
    calc z * z = z * z * (s * s) := by rw [hs, mul_one]
      _ = (z * s) * (z * s) := by
          calc z * z * (s * s) = z * (z * s) * s := by group
            _ = z * (s * z) * s := by rw [hcomm]
            _ = (z * s) * (z * s) := by group
      _ = 1 := h1
  have hodd := odd_orderOf_center hW hirr hzc
  have hz1 : z = 1 := by
    have hdvd : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hz2)
    have hodd' : Odd (orderOf z) := by rwa [Subgroup.orderOf_coe] at hodd
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact orderOf_eq_one_iff.1 h
    · rw [h] at hodd'
      exact absurd hodd' (by decide)
  rw [hz1, one_mul] at hzs
  calc g * s = g * s * g⁻¹ * g := by group
    _ = s * g := by rw [hzs]

theorem exists_pow_four_of_redHom (hW : ∀ w : W, w * w = 1) {L : Subgroup (MulAut W)}
    (hirr : IsIrrOn L) {S : Type} [Group S] (e : CQ L ≃* S) {w : ↥L}
    (h4 : redHom L e w ^ 4 = 1) (h2 : redHom L e w ^ 2 ≠ 1) :
    ∃ m : ℕ, ((w : MulAut W) ^ m) ^ 4 = 1 ∧ ((w : MulAut W) ^ m) ^ 2 ≠ 1 := by
  have hzc : w ^ 4 ∈ Subgroup.center ↥L := by
    rw [← redHom_eq_one_iff L e, map_pow]
    exact h4
  have hodd := odd_orderOf_center hW hirr hzc
  set m := orderOf ((w ^ 4 : ↥L) : MulAut W) with hm
  refine ⟨m, ?_, ?_⟩
  · rw [← pow_mul, mul_comm, pow_mul]
    have : ((w : MulAut W) ^ 4) = ((w ^ 4 : ↥L) : MulAut W) := by simp
    rw [this, hm, pow_orderOf_eq_one]
  · intro hcon
    obtain ⟨j, hj⟩ := hodd
    have h1 : (w : MulAut W) ^ (2 * m) = 1 := by rw [mul_comm, pow_mul]; exact hcon
    have h2' : w ^ (2 * m) = 1 := Subtype.ext (by simpa using h1)
    have h3 : redHom L e w ^ (2 * m) = 1 := by rw [← map_pow, h2', map_one]
    have h4' : (redHom L e w ^ 2) ^ 2 = 1 := by rw [← pow_mul]; exact h4
    have h5 : (redHom L e w ^ 2) ^ m = redHom L e w ^ 2 := by
      rw [hj, pow_succ, pow_mul, h4', one_pow, one_mul]
    apply h2
    rw [← h5, ← pow_mul]
    exact h3

theorem exists_pow_order_four_of {G : Type*} [Group G] {x : G}
    (h : orderOf x = 4 ∨ orderOf x = 8) : ∃ n : ℕ, (x ^ n) ^ 4 = 1 ∧ (x ^ n) ^ 2 ≠ 1 := by
  rcases h with h4 | h8
  · refine ⟨1, ?_, ?_⟩
    · rw [pow_one, ← h4, pow_orderOf_eq_one]
    · rw [pow_one]
      exact pow_ne_one_of_lt_orderOf (by norm_num) (by omega)
  · refine ⟨2, ?_, ?_⟩
    · rw [← pow_mul, show 2 * 4 = 8 by norm_num, ← h8, pow_orderOf_eq_one]
    · rw [← pow_mul]
      exact pow_ne_one_of_lt_orderOf (by norm_num) (by omega)

theorem false_of_o4_witness (hW : ∀ w : W, w * w = 1) {L : Subgroup (MulAut W)}
    (hirr : IsIrrOn L) {S : Type} [Group S] (e : CQ L ≃* S) {E : Subgroup (MulAut W)}
    (hEL : E ≤ L) {t u : MulAut W} (ht : t ∈ E) (hu : u ∈ E) (ht2 : t * t = 1)
    (hfix : fixV E = fixV (Subgroup.zpowers t)) {gb : S}
    (hgb : gb * redHom L e ⟨t, hEL ht⟩ = redHom L e ⟨t, hEL ht⟩ * gb) (n : ℕ)
    (h4 : ((redHom L e ⟨u, hEL hu⟩ * (gb * redHom L e ⟨u, hEL hu⟩ * gb⁻¹)) ^ n) ^ 4 = 1)
    (h2 : ((redHom L e ⟨u, hEL hu⟩ * (gb * redHom L e ⟨u, hEL hu⟩ * gb⁻¹)) ^ n) ^ 2 ≠ 1)
    (hinv : ∀ b ∈ L, b ≠ 1 → b * b = 1 →
      (fixV (Subgroup.zpowers t)).index ≤ (fixV (Subgroup.zpowers b)).index) : False := by
  obtain ⟨g, rfl⟩ := redHom_surjective L e gb
  have hgt : g * ⟨t, hEL ht⟩ = ⟨t, hEL ht⟩ * g :=
    comm_of_redHom_comm hW hirr e (Subtype.ext ht2) hgb
  have hgt' : (g : MulAut W) * t = t * (g : MulAut W) := congrArg Subtype.val hgt
  set u' : ↥L := ⟨u, hEL hu⟩ with hu'
  set x : ↥L := u' * (g * u' * g⁻¹) with hx
  have hxmap : redHom L e (x ^ n) =
      (redHom L e u' * (redHom L e g * redHom L e u' * (redHom L e g)⁻¹)) ^ n := by
    simp [hx, map_mul, map_inv, map_pow]
  rw [← hxmap] at h4 h2
  obtain ⟨m, hm4, hm2⟩ := exists_pow_four_of_redHom hW hirr e h4 h2
  have htu : fixV (Subgroup.zpowers t) ≤ fixV (Subgroup.zpowers u) := by
    rw [← hfix]
    exact fixV_le_fixV_zpowers hu
  have htx : fixV (Subgroup.zpowers t) ≤ fixV (Subgroup.zpowers (x : MulAut W)) := by
    have h1 := fixV_le_fixV_conj (g := (g : MulAut W)) htu hgt'
    have h2 := fixV_le_fixV_mul htu h1
    simpa [hx] using h2
  have htw : fixV (Subgroup.zpowers t) ≤
      fixV (Subgroup.zpowers (((x ^ n : ↥L) : MulAut W) ^ m)) := by
    refine htx.trans ?_
    have h1 := fixV_zpowers_le_pow (x : MulAut W) (n * m)
    simpa [pow_mul] using h1
  refine false_of_order_four hW htw hm4 hm2 ?_
  refine hinv _ ?_ hm2 ?_
  · exact L.pow_mem (L.pow_mem (x ^ n).2 m) 2
  · rw [← pow_mul, ← pow_add]
    have : (((x ^ n : ↥L) : MulAut W) ^ m) ^ 4 = 1 := hm4
    rw [← pow_mul] at this
    rw [show m * 2 + m * 2 = m * 4 by ring]
    exact this

end Lift

section Assembly

variable {G : Type*} [Group G] [Finite G] {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  [Module.Finite (ZMod 2) E]

open Module

theorem no_offender2_of_ranks (ρ : G →* (E ≃ₗ[ZMod 2] E)) (L B : Subgroup G) (hB1 : B ≠ ⊥)
    (F : Submodule (ZMod 2) E) (hF : ∀ a ∈ B, ∀ x ∈ F, ρ a x = x)
    (hin : ∀ t ∈ B, t ∈ L → t ≠ 1 → 7 ≤ finrank (ZMod 2) (LinearMap.range (sub1 (ρ t))))
    (hcard : ∀ T : Subgroup G, T ≤ B → T ≤ L → Nat.card T ≤ 4)
    (hout : ∀ a ∈ B, a ∉ L → 3 ≤ finrank (ZMod 2) (LinearMap.range (sub1 (ρ a))))
    (hidx : ∀ a ∈ B, ∀ a' ∈ B, a ∉ L → a' ∉ L → a * a' ∈ L)
    (hoff : finrank (ZMod 2) E - finrank (ZMod 2) F ≤ 2 * Nat.log 2 (Nat.card B)) : False := by
  classical
  obtain ⟨t, htB, ht1⟩ : ∃ t ∈ B, t ≠ 1 := by
    obtain ⟨t, ht⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hB1
    exact ⟨t, t.2, fun h => ht (Subtype.ext h)⟩
  have hlog : ∀ n : ℕ, Nat.card B ≤ n → Nat.log 2 (Nat.card B) ≤ Nat.log 2 n :=
    fun n hn => Nat.log_mono_right hn
  by_cases hBL : ∀ a ∈ B, a ∈ L
  ·
    have hc : Nat.card B ≤ 4 := hcard B le_rfl hBL
    have h1 := hlog 4 hc
    have h2 : Nat.log 2 4 = 2 := by decide
    have h3 := finrank_range_sub1_le_of_offender ρ hF htB (n := 4) (by omega)
    have h4 := hin t htB (hBL t htB) ht1
    omega
  · push Not at hBL
    obtain ⟨a₀, ha₀B, ha₀L⟩ := hBL
    set T : Subgroup G := B ⊓ L with hT
    have hTB : T ≤ B := inf_le_left
    have hTL : T ≤ L := inf_le_right
    have hT4 : Nat.card T ≤ 4 := hcard T hTB hTL
    have hBT : Nat.card B ≤ 2 * Nat.card T := by
      let f : B → T ⊕ T := fun x =>
        if hx : (x : G) ∈ L then Sum.inl ⟨x, x.2, hx⟩
        else Sum.inr ⟨a₀ * x, B.mul_mem ha₀B x.2, hidx a₀ ha₀B x x.2 ha₀L hx⟩
      have hf : Function.Injective f := by
        intro x y hxy
        by_cases hx : (x : G) ∈ L <;> by_cases hy : (y : G) ∈ L
        · simp only [f, hx, hy, dite_true, Sum.inl.injEq] at hxy
          exact Subtype.ext (congrArg (fun z : T => (z : G)) hxy)
        · simp [f, hx, hy] at hxy
        · simp [f, hx, hy] at hxy
        · simp only [f, hx, hy, dite_false, Sum.inr.injEq] at hxy
          exact Subtype.ext (mul_left_cancel (congrArg (fun z : T => (z : G)) hxy))
      have := Nat.card_le_card_of_injective f hf
      rwa [Nat.card_sum, ← two_mul] at this
    by_cases hTbot : ∀ x ∈ T, x = 1
    ·
      have hT1 : Nat.card T ≤ 1 := by
        have : T = ⊥ := (Subgroup.eq_bot_iff_forall T).2 hTbot
        rw [this, Subgroup.card_bot]
      have hc : Nat.card B ≤ 2 := by omega
      have h1 := hlog 2 hc
      have h2 : Nat.log 2 2 = 1 := by decide
      have h3 := finrank_range_sub1_le_of_offender ρ hF ha₀B (n := 2) (by omega)
      have h4 := hout a₀ ha₀B ha₀L
      omega
    · push Not at hTbot
      obtain ⟨u, huT, hu1⟩ := hTbot
      have hc : Nat.card B ≤ 8 := by omega
      have h1 := hlog 8 hc
      have h2 : Nat.log 2 8 = 3 := by decide
      have h3 := finrank_range_sub1_le_of_offender ρ hF (hTB huT) (n := 6) (by omega)
      have h4 := hin u (hTB huT) (hTL huT) hu1
      omega

end Assembly

end CFSG.Quasithin.B45Exc
