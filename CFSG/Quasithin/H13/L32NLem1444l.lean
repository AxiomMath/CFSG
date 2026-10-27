module

public import CFSG.Quasithin.H13.L32NLem1444k

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.LieType.BorelTits

namespace L1444

variable {G : Type} [Group G] [Finite G]

namespace Setup5

variable {T L V V₂ : Subgroup G} {g : G} {D : HatModelU (fsuU T V)} {Q₁ Q₂ : Subgroup G}
  (S : Setup5 G T L V V₂ g D Q₁ Q₂)
include S

theorem act_eq_of_basis {z a b x y : G} (hz : z ∈ fsuV1 T V) (hz1 : z ≠ 1) (ha : a ∈ V₂)
    (haV : a ∉ fsuV1 T V) (hb : b ∈ V) (hbV : b ∉ V₂) (hxz : x * z * x⁻¹ = y * z * y⁻¹)
    (hxa : x * a * x⁻¹ = y * a * y⁻¹) (hxb : x * b * x⁻¹ = y * b * y⁻¹) :
    ∀ v ∈ V, x * v * x⁻¹ = y * v * y⁻¹ := by
  have hc : ∀ w : G, x * w * x⁻¹ = y * w * y⁻¹ → Commute (y⁻¹ * x) w := by
    intro w hw
    show y⁻¹ * x * w = w * (y⁻¹ * x)
    calc y⁻¹ * x * w = y⁻¹ * (x * w * x⁻¹) * x := by group
      _ = y⁻¹ * (y * w * y⁻¹) * x := by rw [hw]
      _ = w * (y⁻¹ * x) := by group
  intro v hv
  have h := (S.comm_V_of_basis hz hz1 ha haV hb hbV (hc z hxz) (hc a hxa) (hc b hxb) v hv).eq
  calc x * v * x⁻¹ = y * (y⁻¹ * x * v) * x⁻¹ := by group
    _ = y * (v * (y⁻¹ * x)) * x⁻¹ := by rw [h]
    _ = y * v * y⁻¹ := by group

section Split

variable {X : Subgroup G} (hXL : X ≤ L) (hXV : X ⊓ V = ⊥) (hXsup : X ⊔ V = L)
include hXL hXV

omit hXV in
theorem X_le_normV : X ≤ Subgroup.normalizer (V : Set G) := hXL.trans S.L_le_normV

theorem eq_one_of_act {x : G} (hx : x ∈ X) (hxV : ∀ v ∈ V, x * v * x⁻¹ = v) : x = 1 := by
  have hxV' : x ∈ V := by
    rw [← S.centL]
    refine ⟨hXL hx, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
    calc v * x = x * v * x⁻¹ * x := by rw [hxV v hv]
      _ = x * v := by group
  have : x ∈ X ⊓ V := ⟨hx, hxV'⟩
  rwa [hXV, Subgroup.mem_bot] at this

theorem eq_of_act {x y : G} (hx : x ∈ X) (hy : y ∈ X)
    (hxy : ∀ v ∈ V, x * v * x⁻¹ = y * v * y⁻¹) : x = y := by
  have h := S.eq_one_of_act hXL hXV (X.mul_mem (X.inv_mem hy) hx) fun v hv => by
    calc y⁻¹ * x * v * (y⁻¹ * x)⁻¹ = y⁻¹ * (x * v * x⁻¹) * y := by group
      _ = y⁻¹ * (y * v * y⁻¹) * y := by rw [hxy v hv]
      _ = v := by group
  calc x = y * (y⁻¹ * x) := by group
    _ = y := by rw [h, mul_one]

omit hXV in
include hXsup in
theorem exists_X_act {l : G} (hl : l ∈ L) :
    ∃ x ∈ X, ∃ v ∈ V, l = x * v ∧ ∀ w ∈ V, x * w * x⁻¹ = l * w * l⁻¹ := by
  have hl' : l ∈ ((X ⊔ V : Subgroup G) : Set G) := by rw [hXsup]; exact hl
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ (S.X_le_normV hXL)] at hl'
  obtain ⟨x, hx, v, hv, rfl⟩ := hl'
  refine ⟨x, hx, v, hv, rfl, fun w hw => ?_⟩
  have hvw : v * w = w * v := S.comm_V hv hw
  calc x * w * x⁻¹ = x * (v * w * v⁻¹) * x⁻¹ := by rw [hvw]; group
    _ = x * v * w * (x * v)⁻¹ := by group

omit hXV in
include hXsup in
theorem exists_X_mem {Y : Subgroup G} (hVY : V ≤ Y) (hYL : Y ≤ L) {y : G} (hy : y ∈ Y)
    (hyV : y ∉ V) : ∃ x ∈ X ⊓ Y, x ≠ 1 ∧ ∃ v ∈ V, y = x * v := by
  obtain ⟨x, hx, v, hv, rfl, -⟩ := S.exists_X_act hXL hXsup (hYL hy)
  refine ⟨x, ⟨hx, ?_⟩, ?_, v, hv, rfl⟩
  · have := Y.mul_mem hy (Y.inv_mem (hVY hv))
    simpa using this
  · rintro rfl
    exact hyV (by simpa using hv)

omit hXL hXV in
theorem za_mem {z : G} (hz : z ∈ fsuV1 T V) (hz1 : z ≠ 1) :
    g⁻¹ * z * g ∈ V₂ ∧ g⁻¹ * z * g ∉ fsuV1 T V := by
  have hzV₂ : z ∈ V₂ := S.plane.2 hz
  refine ⟨?_, fun h => ?_⟩
  · have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem S.g_normV₂) z).mp
      hzV₂
    simpa using this
  · apply S.gH
    have hne : g⁻¹ * z * g ≠ 1 := fun h1 => hz1 (by
      calc z = g * (g⁻¹ * z * g) * g⁻¹ := by group
        _ = 1 := by rw [h1]; group)
    have heq : g⁻¹ * z * g = z := S.eq_of_mem_V1 h hne hz hz1
    rw [show l32nH T V = Subgroup.normalizer (fsuV1 T V : Set G) from rfl,
      normalizer_eq_centralizer_of_card_two S.card2 hz hz1,
      Subgroup.mem_centralizer_singleton_iff]
    calc g * z = g * (g⁻¹ * z * g) := by rw [heq]
      _ = z * g := by group

include hXsup in
theorem exists_tz {z b : G} (hz : z ∈ fsuV1 T V) (hz1 : z ≠ 1) (hb : b ∈ V) (hbV : b ∉ V₂) :
    ∃ t ∈ X, t ∈ l32nW T V V₂ ∧ t ≠ 1 ∧ (∀ v ∈ V₂, t * v * t⁻¹ = v) ∧ t * b * t⁻¹ = b * z := by
  obtain ⟨_, S'⟩ := S.set14
  obtain ⟨w, hw, hwV⟩ : ∃ w ∈ l32nW T V V₂, w ∉ V := by
    by_contra h
    push Not at h
    have := Subgroup.card_le_of_le (show l32nW T V V₂ ≤ V from h)
    rw [S.card_W, S.card8] at this
    omega
  obtain ⟨t, ⟨htX, htW⟩, ht1, -⟩ := S.exists_X_mem hXL hXsup S.V_le_W
    ((inf_le_left : l32nW T V V₂ ≤ fsuU T V).trans S.U_le_L) hw hwV
  have htV₂ : ∀ v ∈ V₂, t * v * t⁻¹ = v := fun v hv => by
    rw [(Subgroup.mem_centralizer_iff.mp htW.2 v hv).symm]
    group
  refine ⟨t, htX, htW, ht1, htV₂, ?_⟩
  have hc := S.comm_mem_V1 htW.1 hb
  rcases S'.eq_of_mem_V1 hz hz1 hc with h | h
  · exfalso
    apply ht1
    obtain ⟨a, -, -, -, -, -, -, -, -⟩ := S'.exists_basis
    refine S.eq_one_of_act hXL hXV htX fun v hv => ?_
    have htb : t * b * t⁻¹ = b := by
      calc t * b * t⁻¹ = (t * b * t⁻¹ * b⁻¹) * b := by group
        _ = b := by rw [h, one_mul]
    rcases S'.mem_V hb hbV hv with h1 | h1
    · exact htV₂ v h1
    · have e : v = b⁻¹ * (b * v) := by group
      rw [e]
      calc t * (b⁻¹ * (b * v)) * t⁻¹ = (t * b * t⁻¹)⁻¹ * (t * (b * v) * t⁻¹) := by group
        _ = b⁻¹ * (b * v) := by rw [htb, htV₂ _ h1]
  · calc t * b * t⁻¹ = (t * b * t⁻¹ * b⁻¹) * b := by group
      _ = z * b := by rw [h]
      _ = b * z := S.comm_V (S.plane.1.1 (S.plane.2 hz)) hb

omit hXL hXV in
theorem mem_W_of_comm {z a x : G} (hz : z ∈ fsuV1 T V) (hz1 : z ≠ 1) (ha : a ∈ V₂)
    (haV : a ∉ fsuV1 T V) (hxU : x ∈ fsuU T V) (hxz : x * z * x⁻¹ = z) (hxa : x * a * x⁻¹ = a) :
    x ∈ l32nW T V V₂ := by
  obtain ⟨_, S'⟩ := S.set14
  have hc : ∀ v : G, x * v * x⁻¹ = v → v * x = x * v := fun v hv => by
    calc v * x = x * v * x⁻¹ * x := by rw [hv]
      _ = x * v := by group
  refine ⟨hxU, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
  rcases S'.mem_V2 ha haV hv with h | h
  · rcases S'.eq_of_mem_V1 hz hz1 h with rfl | rfl
    · group
    · exact hc v hxz
  · rcases S'.eq_of_mem_V1 hz hz1 h with h' | h'
    · have e : v = a⁻¹ := by
        calc v = a⁻¹ * (a * v) := by group
          _ = a⁻¹ := by rw [h', mul_one]
      rw [e]
      apply hc
      rw [show x * a⁻¹ * x⁻¹ = (x * a * x⁻¹)⁻¹ by group, hxa]
    · have e : v = a⁻¹ * z := by
        calc v = a⁻¹ * (a * v) := by group
          _ = a⁻¹ * z := by rw [h']
      rw [e]
      apply hc
      rw [show x * (a⁻¹ * z) * x⁻¹ = (x * a * x⁻¹)⁻¹ * (x * z * x⁻¹) by group, hxa, hxz]

include hXsup in
theorem exists_ta {z b : G} (hz : z ∈ fsuV1 T V) (hz1 : z ≠ 1) (hb : b ∈ V) (hbV : b ∉ V₂) :
    ∃ t ∈ X, t ∈ CFSG.conjugate (l32nW T V V₂) g ∧ t ≠ 1 ∧ (∀ v ∈ V₂, t * v * t⁻¹ = v) ∧
      t * b * t⁻¹ = b * (g⁻¹ * z * g) := by
  obtain ⟨_, S'⟩ := S.set14
  obtain ⟨w, hw, hwV⟩ : ∃ w ∈ CFSG.conjugate (l32nW T V V₂) g, w ∉ V := by
    by_contra h
    push Not at h
    have := Subgroup.card_le_of_le (show CFSG.conjugate (l32nW T V V₂) g ≤ V from h)
    rw [S.card_Wg16, S.card8] at this
    omega
  obtain ⟨t, ⟨htX, htW⟩, ht1, -⟩ := S.exists_X_mem hXL hXsup S.V_le_Wg S.Wg_le_L hw hwV
  have htV₂ : ∀ v ∈ V₂, t * v * t⁻¹ = v := fun v hv => by
    rw [← (Subgroup.mem_centralizer_iff.mp (Wg_le_cent S.g_normV₂ htW) v hv)]
    group
  refine ⟨t, htX, htW, ht1, htV₂, ?_⟩
  obtain ⟨w', hw', hw'e⟩ := htW
  have ht : t = g⁻¹ * w' * g := by
    rw [← hw'e]
    simp
  have hgb : g * b * g⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp S.g_normV b).mp hb
  have hc := S.comm_mem_V1 hw'.1 hgb
  have hcomp : t * b * t⁻¹ = g⁻¹ * (w' * (g * b * g⁻¹) * w'⁻¹ * (g * b * g⁻¹)⁻¹) * g * b := by
    rw [ht]
    group
  have haV : g⁻¹ * z * g ∈ V := S.plane.1.1 (S.za_mem hz hz1).1
  rcases S'.eq_of_mem_V1 hz hz1 hc with h | h
  · exfalso
    apply ht1
    obtain ⟨a, -, -, -, -, -, -, -, -⟩ := S'.exists_basis
    have htb : t * b * t⁻¹ = b := by rw [hcomp, h]; group
    refine S.eq_one_of_act hXL hXV htX fun v hv => ?_
    rcases S'.mem_V hb hbV hv with h1 | h1
    · exact htV₂ v h1
    · have e : v = b⁻¹ * (b * v) := by group
      rw [e]
      calc t * (b⁻¹ * (b * v)) * t⁻¹ = (t * b * t⁻¹)⁻¹ * (t * (b * v) * t⁻¹) := by group
        _ = b⁻¹ * (b * v) := by rw [htb, htV₂ _ h1]
  · rw [hcomp, h]
    calc g⁻¹ * z * g * b = (g⁻¹ * z * g) * b := rfl
      _ = b * (g⁻¹ * z * g) := S.comm_V haV hb

omit hXV in
include hXsup in
theorem exists_nr {z a b : G} (hz : z ∈ fsuV1 T V) (hz1 : z ≠ 1) (ha : a ∈ V₂)
    (haV : a ∉ fsuV1 T V) (hb : b ∈ V) (hbV : b ∉ V₂) :
    ∃ r ∈ X, r * z * r⁻¹ = a ∧ r * a * r⁻¹ = z * a ∧ r * b * r⁻¹ = b := by
  obtain ⟨_, S'⟩ := S.set14
  have hzV₂ : z ∈ V₂ := S.plane.2 hz
  have hzV : z ∈ V := S.plane.1.1 hzV₂
  have haV' : a ∈ V := S.plane.1.1 ha
  have ha1 : a ≠ 1 := fun h => haV (h ▸ (fsuV1 T V).one_mem)
  have hzb : z ≠ b := fun h => hbV (h ▸ hzV₂)
  have hab : a ≠ b := fun h => hbV (h ▸ ha)
  have hza : z ≠ a := fun h => haV (h ▸ hz)
  have habz : a ≠ b * z := fun h => hbV (by
    have e : b = a * z⁻¹ := by rw [h]; group
    rw [e]
    exact V₂.mul_mem ha (V₂.inv_mem hzV₂))
  obtain ⟨l, hl, -, hlb, hlz, hla⟩ := S'.exists_rot hb hzV haV' hz1 ha1 hzb hab hza habz
  obtain ⟨x, hx, v, hv, -, hxv⟩ := S.exists_X_act hXL hXsup hl
  exact ⟨x, hx, by rw [hxv z hzV, hlz], by rw [hxv a haV', hla], by rw [hxv b hb, hlb]⟩

include hXsup in
theorem exists_uza {z a b : G} (hz : z ∈ fsuV1 T V) (hz1 : z ≠ 1) (ha : a ∈ V₂)
    (haV : a ∉ fsuV1 T V) (hb : b ∈ V) (hbV : b ∉ V₂) :
    ∃ u ∈ X, u ∈ fsuU T V ∧ u ∉ l32nW T V V₂ ∧ u * z * u⁻¹ = z ∧ u * a * u⁻¹ = z * a ∧
      u * b * u⁻¹ = b := by
  obtain ⟨_, S'⟩ := S.set14
  have hzV₂ : z ∈ V₂ := S.plane.2 hz
  have hzV : z ∈ V := S.plane.1.1 hzV₂
  have haV' : a ∈ V := S.plane.1.1 ha
  obtain ⟨u₀, hu₀, hu₀W⟩ : ∃ u ∈ fsuU T V, u ∉ l32nW T V V₂ := by
    by_contra h
    push Not at h
    have := Subgroup.card_le_of_le (show fsuU T V ≤ l32nW T V V₂ from h)
    rw [S.card32, S.card_W] at this
    omega
  obtain ⟨x, hx, v, hv, hu₀e, -⟩ := S.exists_X_act hXL hXsup (S.U_le_L hu₀)
  have hxU : x ∈ fsuU T V := by
    have e : x = u₀ * v⁻¹ := by rw [hu₀e]; group
    rw [e]
    exact (fsuU T V).mul_mem hu₀ ((fsuU T V).inv_mem (V_le_U hv))
  have hxW : x ∉ l32nW T V V₂ := fun h => hu₀W (by
    rw [hu₀e]
    exact (l32nW T V V₂).mul_mem h (S.V_le_W hv))
  have hxz : x * z * x⁻¹ = z := S.comm_V1 (S.U_le_H hxU) hz
  have hxa : x * a * x⁻¹ = z * a := by
    rcases S'.eq_of_mem_V1 hz hz1 (S.comm_mem_V1 hxU haV') with h | h
    · exact absurd (S.mem_W_of_comm hz hz1 ha haV hxU hxz (by
        calc x * a * x⁻¹ = (x * a * x⁻¹ * a⁻¹) * a := by group
          _ = a := by rw [h, one_mul])) hxW
    · calc x * a * x⁻¹ = (x * a * x⁻¹ * a⁻¹) * a := by group
        _ = z * a := by rw [h]
  rcases S'.eq_of_mem_V1 hz hz1 (S.comm_mem_V1 hxU hb) with h | h
  · refine ⟨x, hx, hxU, hxW, hxz, hxa, ?_⟩
    calc x * b * x⁻¹ = (x * b * x⁻¹ * b⁻¹) * b := by group
      _ = b := by rw [h, one_mul]
  ·
    obtain ⟨t, htX, htW, -, htV₂, htb⟩ := S.exists_tz hXL hXV hXsup hz hz1 hb hbV
    have hxb : x * b * x⁻¹ = z * b := by
      calc x * b * x⁻¹ = (x * b * x⁻¹ * b⁻¹) * b := by group
        _ = z * b := by rw [h]
    refine ⟨x * t, X.mul_mem hx htX, (fsuU T V).mul_mem hxU htW.1, fun hW => hxW ?_, ?_, ?_, ?_⟩
    · have e : x = (x * t) * t⁻¹ := by group
      rw [e]
      exact (l32nW T V V₂).mul_mem hW ((l32nW T V V₂).inv_mem htW)
    · rw [show x * t * z * (x * t)⁻¹ = x * (t * z * t⁻¹) * x⁻¹ by group, htV₂ z hzV₂, hxz]
    · rw [show x * t * a * (x * t)⁻¹ = x * (t * a * t⁻¹) * x⁻¹ by group, htV₂ a ha, hxa]
    · rw [show x * t * b * (x * t)⁻¹ = x * (t * b * t⁻¹) * x⁻¹ by group, htb,
        show x * (b * z) * x⁻¹ = (x * b * x⁻¹) * (x * z * x⁻¹) by group, hxb, hxz,
        mul_assoc, S.comm_V hb hzV, ← mul_assoc, S'.mul_self_V hzV, one_mul]

end Split

end Setup5

structure SplitModel (T V V₂ : Subgroup G) (g : G) where
  z : G
  a : G
  b : G
  tz : G
  ta : G
  r : G
  u : G
  hz : z ∈ fsuV1 T V
  hz1 : z ≠ 1
  ha : a ∈ V₂
  haV : a ∉ fsuV1 T V
  hb : b ∈ V
  hbV : b ∉ V₂
  htz : tz ∈ l32nW T V V₂
  htzV : tz ∉ V
  hta : ta ∈ CFSG.conjugate (l32nW T V V₂) g
  htaU : ta ∉ fsuU T V
  huU : u ∈ fsuU T V
  huW : u ∉ l32nW T V V₂
  tz_sq : tz * tz = 1
  ta_sq : ta * ta = 1
  tz_ta : tz * ta = ta * tz
  tz_V₂ : ∀ v ∈ V₂, tz * v * tz⁻¹ = v
  ta_V₂ : ∀ v ∈ V₂, ta * v * ta⁻¹ = v
  r_z : r * z * r⁻¹ = a
  r_a : r * a * r⁻¹ = z * a
  r_tz : r * tz * r⁻¹ = ta
  r_ta : r * ta * r⁻¹ = tz * ta
  b_tz : b * tz * b⁻¹ = z * tz
  b_ta : b * ta * b⁻¹ = a * ta
  u_z : u * z * u⁻¹ = z
  u_a : u * a * u⁻¹ = z * a
  u_tz : u * tz * u⁻¹ = tz
  u_ta : u * ta * u⁻¹ = tz * ta

namespace Setup5

variable {T L V V₂ : Subgroup G} {g : G} {D : HatModelU (fsuU T V)} {Q₁ Q₂ : Subgroup G}
  (S : Setup5 G T L V V₂ g D Q₁ Q₂)
include S

omit [Finite G] S in
theorem conj_conj (x y v : G) : (x * y) * v * (x * y)⁻¹ = x * (y * v * y⁻¹) * x⁻¹ := by group

omit [Finite G] S in
theorem conj_mul' (x u v : G) : x * (u * v) * x⁻¹ = (x * u * x⁻¹) * (x * v * x⁻¹) := by group

theorem exists_splitModel {X : Subgroup G} (hXL : X ≤ L) (hXV : X ⊓ V = ⊥) (hXsup : X ⊔ V = L) :
    Nonempty (SplitModel T V V₂ g) := by
  obtain ⟨_, S'⟩ := S.set14
  obtain ⟨z, -, b, hz, hz1, -, -, hb, hbV⟩ := S'.exists_basis
  obtain ⟨ha, haV⟩ := S.za_mem hz hz1
  generalize hadef : g⁻¹ * z * g = a at ha haV
  have hzV₂ : z ∈ V₂ := S.plane.2 hz
  have hzV : z ∈ V := S.plane.1.1 hzV₂
  have haV' : a ∈ V := S.plane.1.1 ha
  obtain ⟨tz, htzX, htzW, htz1, htzV₂, htzb⟩ := S.exists_tz hXL hXV hXsup hz hz1 hb hbV
  obtain ⟨ta, htaX, htaW, hta1, htaV₂, htab⟩ := S.exists_ta hXL hXV hXsup hz hz1 hb hbV
  rw [hadef] at htab
  obtain ⟨r, hrX, hrz, hra, hrb⟩ := S.exists_nr hXL hXsup hz hz1 ha haV hb hbV
  obtain ⟨u, huX, huU, huW, huz, hua, hub⟩ := S.exists_uza hXL hXV hXsup hz hz1 ha haV hb hbV
  have hX : ∀ {x y : G}, x ∈ X → y ∈ X → x * z * x⁻¹ = y * z * y⁻¹ →
      x * a * x⁻¹ = y * a * y⁻¹ → x * b * x⁻¹ = y * b * y⁻¹ → x = y := fun hx hy h1 h2 h3 =>
    S.eq_of_act hXL hXV hx hy (S.act_eq_of_basis hz hz1 ha haV hb hbV h1 h2 h3)
  have hza : z * a = a * z := S.comm_V hzV haV'
  have hzz : z * z = 1 := S'.mul_self_V hzV
  have haa : a * a = 1 := S'.mul_self_V haV'
  have hbz : b * z = z * b := S.comm_V hb hzV
  have hba : b * a = a * b := S.comm_V hb haV'
  have hzaV₂ : z * a ∈ V₂ := V₂.mul_mem hzV₂ ha
  have htzz := htzV₂ z hzV₂
  have htza := htzV₂ a ha
  have htaz := htaV₂ z hzV₂
  have htaa := htaV₂ a ha
  have htz2 : tz * tz = 1 := by
    have h := hX (X.mul_mem htzX htzX) X.one_mem (by rw [conj_conj, htzz, htzz]; group)
      (by rw [conj_conj, htza, htza]; group)
      (by rw [conj_conj, htzb, conj_mul', htzb, htzz, mul_assoc, hzz, mul_one]; group)
    exact h
  have hta2 : ta * ta = 1 := by
    have h := hX (X.mul_mem htaX htaX) X.one_mem (by rw [conj_conj, htaz, htaz]; group)
      (by rw [conj_conj, htaa, htaa]; group)
      (by rw [conj_conj, htab, conj_mul', htab, htaa, mul_assoc, haa, mul_one]; group)
    exact h
  have htzta : tz * ta = ta * tz := hX (X.mul_mem htzX htaX) (X.mul_mem htaX htzX)
    (by simp only [conj_conj, htaz, htzz])
    (by simp only [conj_conj, htaa, htza])
    (by
      simp only [conj_conj, conj_mul', htab, htzb, htza, htaz]
      rw [mul_assoc, mul_assoc, hza])
  have htzV : tz ∉ V := fun h => htz1 (by
    have : tz ∈ X ⊓ V := ⟨htzX, h⟩
    rwa [hXV, Subgroup.mem_bot] at this)
  have htaU : ta ∉ fsuU T V := fun h => hta1 (by
    have hV : ta ∈ V := by rw [← S.inf_Wg]; exact ⟨h, htaW⟩
    have : ta ∈ X ⊓ V := ⟨htaX, hV⟩
    rwa [hXV, Subgroup.mem_bot] at this)
  have hb2 : b⁻¹ = b := (eq_inv_of_mul_eq_one_left (S'.mul_self_V hb)).symm
  have hbtz : b * tz * b⁻¹ = z * tz := by
    calc b * tz * b⁻¹ = b * (tz * b * tz⁻¹) * tz := by rw [hb2]; group
      _ = z * tz := by rw [htzb, ← mul_assoc, S'.mul_self_V hb, one_mul]
  have hbta : b * ta * b⁻¹ = a * ta := by
    calc b * ta * b⁻¹ = b * (ta * b * ta⁻¹) * ta := by rw [hb2]; group
      _ = a * ta := by rw [htab, ← mul_assoc, S'.mul_self_V hb, one_mul]
  have hrtz : r * tz * r⁻¹ = ta := by
    have h : r * tz = ta * r := hX (X.mul_mem hrX htzX) (X.mul_mem htaX hrX)
      (by simp only [conj_conj, htzz, hrz, htaa])
      (by simp only [conj_conj, conj_mul', htza, hra, htaz, htaa])
      (by simp only [conj_conj, conj_mul', htzb, hrb, hrz, htab])
    rw [h]
    group
  have hrta : r * ta * r⁻¹ = tz * ta := by
    have h : r * ta = (tz * ta) * r := hX (X.mul_mem hrX htaX)
      (X.mul_mem (X.mul_mem htzX htaX) hrX)
      (by simp only [conj_conj, htaz, hrz, htaa, htza])
      (by simp only [conj_conj, conj_mul', htaa, hra, htaz, htzz, htza])
      (by simp only [conj_conj, conj_mul', htab, hrb, hra, htzb, htza]; group)
    rw [h]
    group
  have hutz : u * tz * u⁻¹ = tz := by
    have h : u * tz = tz * u := hX (X.mul_mem huX htzX) (X.mul_mem htzX huX)
      (by simp only [conj_conj, htzz, huz])
      (by simp only [conj_conj, conj_mul', htza, hua, htzz])
      (by simp only [conj_conj, conj_mul', htzb, hub, huz])
    rw [h]
    group
  have huta : u * ta * u⁻¹ = tz * ta := by
    have h : u * ta = (tz * ta) * u := hX (X.mul_mem huX htaX)
      (X.mul_mem (X.mul_mem htzX htaX) huX)
      (by simp only [conj_conj, htaz, huz, htzz])
      (by simp only [conj_conj, conj_mul', htaa, hua, htaz, htzz, htza])
      (by simp only [conj_conj, conj_mul', htab, hub, hua, htzb, htza]; group)
    rw [h]
    group
  exact ⟨⟨z, a, b, tz, ta, r, u, hz, hz1, ha, haV, hb, hbV, htzW, htzV, htaW, htaU, huU, huW,
    htz2, hta2, htzta, htzV₂, htaV₂, hrz, hra, hrtz, hrta, hbtz, hbta, huz, hua, hutz, huta⟩⟩

end Setup5

end L1444

end CFSG.Quasithin.H13
