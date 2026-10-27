module

public import CFSG.Quasithin.Recognition.HSTypeCtx

public section

namespace CFSG.Quasithin.HSType

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.A4 CFSG.Quasithin

@[expose] def zetaS : Equiv.Perm (Fin 6) := Equiv.swap 0 1 * Equiv.swap 2 3 * Equiv.swap 4 5

theorem zetaS_comm : ∀ σ : Equiv.Perm (Fin 6), σ ∈ stabS → σ * zetaS = zetaS * σ := by
  decide +kernel

theorem zetaS_facts : zetaS ∈ fixS ∧ zetaS * zetaS = 1 ∧ zetaS ≠ 1 ∧ zetaS ^ 3 = zetaS := by
  decide

theorem eq_zero_of_actS6_lam0 : ∀ σ : Equiv.Perm (Fin 6), σ ∈ lam0 → σ ^ 3 = 1 →
    σ = 1 ∨ ∀ u : SpV, actS6 σ u = u → u = 0 := by
  decide +kernel

theorem inV2m_orbit_of_lam0 : ∀ σ : Equiv.Perm (Fin 6), σ ∈ lam0 → σ ^ 3 = 1 →
    σ = 1 ∨ ∀ u v : SpV, InV2m u → InV2m v →
      u = 0 ∨ v = 0 ∨ v = u ∨ v = actS6 σ u ∨ v = actS6 σ (actS6 σ u) := by
  decide +kernel

namespace HSSetting

variable {G : Type} [Group G] {z : G} {V V₂ : Subgroup G}

theorem normalizer_V2_le_M [Finite G] (h : HSSetting z V) (hV₂ : V₂ ≤ V) (hc : Nat.card V₂ = 4)
    (hz : z ∈ V₂) : Subgroup.normalizer (V₂ : Set G) ≤ hsM V := by
  classical
  intro g hg
  have hV : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy => h.comm_of_mem_V hx hy
  have hV2 : ∀ x ∈ V, x * x = 1 := fun x hx => h.mul_self_of_mem_V hx
  have hidx := h.mul_mem_V2 hV₂ hc
  obtain ⟨x₀, hx₀V, hx₀⟩ := h.exists_mem_V_not_mem_V2 hc
  have hgV : ∀ v ∈ V₂, g * v * g⁻¹ ∈ V₂ := fun v hv =>
    (Subgroup.mem_normalizer_iff.mp hg v).mp hv
  have hmem2 : ∀ v : ↥V, (v : G) ∉ V₂ → (v : G) * x₀ ∈ V₂ := fun v hv =>
    hidx _ v.2 _ hx₀V hv hx₀
  let f : ↥V → ↥V := fun v =>
    if hv : (v : G) ∈ V₂ then ⟨g * v * g⁻¹, hV₂ (hgV _ hv)⟩
    else ⟨g * (v * x₀) * g⁻¹ * x₀, V.mul_mem (hV₂ (hgV _ (hmem2 v hv))) hx₀V⟩
  have hf1 : ∀ v : ↥V, (v : G) ∈ V₂ → (f v : G) = g * v * g⁻¹ := fun v hv => by
    simp only [f, hv, ↓reduceDIte]
  have hf2 : ∀ v : ↥V, (v : G) ∉ V₂ → (f v : G) = g * (v * x₀) * g⁻¹ * x₀ := fun v hv => by
    simp only [f, hv, ↓reduceDIte]
  have hnotmem : ∀ v : ↥V, (v : G) ∉ V₂ → (f v : G) ∉ V₂ := by
    intro v hv hfv
    rw [hf2 v hv] at hfv
    apply hx₀
    have := V₂.mul_mem (V₂.inv_mem (hgV _ (hmem2 v hv))) hfv
    rwa [← mul_assoc, inv_mul_cancel, one_mul] at this
  have hxx : x₀ * x₀ = 1 := hV2 _ hx₀V
  have hmul : ∀ a b : ↥V, f (a * b) = f a * f b := by
    intro a b
    apply Subtype.ext
    have hbx : (b : G) * x₀ = x₀ * b := hV _ b.2 _ hx₀V
    by_cases ha : (a : G) ∈ V₂ <;> by_cases hb : (b : G) ∈ V₂
    · rw [hf1 (a * b) (V₂.mul_mem ha hb), Subgroup.coe_mul, Subgroup.coe_mul, hf1 a ha, hf1 b hb]
      group
    · have hab : ((a * b : ↥V) : G) ∉ V₂ := fun h' => hb (by
        have := V₂.mul_mem (V₂.inv_mem ha) h'
        rwa [Subgroup.coe_mul, ← mul_assoc, inv_mul_cancel, one_mul] at this)
      rw [hf2 _ hab, Subgroup.coe_mul, Subgroup.coe_mul, hf1 a ha, hf2 b hb]
      group
    · have hab : ((a * b : ↥V) : G) ∉ V₂ := fun h' => ha (by
        have := V₂.mul_mem h' (V₂.inv_mem hb)
        rwa [Subgroup.coe_mul, mul_assoc, mul_inv_cancel, mul_one] at this)
      have hgbV : g * b * g⁻¹ ∈ V := hV₂ (hgV _ hb)
      rw [hf2 _ hab, Subgroup.coe_mul, Subgroup.coe_mul, hf2 a ha, hf1 b hb]
      calc g * (a * b * x₀) * g⁻¹ * x₀ = g * (a * (b * x₀)) * g⁻¹ * x₀ := by group
        _ = g * (a * (x₀ * b)) * g⁻¹ * x₀ := by rw [hbx]
        _ = g * (a * x₀) * g⁻¹ * ((g * b * g⁻¹) * x₀) := by group
        _ = g * (a * x₀) * g⁻¹ * (x₀ * (g * b * g⁻¹)) := by rw [hV _ hgbV _ hx₀V]
        _ = g * (a * x₀) * g⁻¹ * x₀ * (g * b * g⁻¹) := by group
    · have hab : ((a * b : ↥V) : G) ∈ V₂ := hidx a a.2 b b.2 ha hb
      have hB'V : g * (b * x₀) * g⁻¹ ∈ V := hV₂ (hgV _ (hmem2 b hb))
      rw [hf1 _ hab, Subgroup.coe_mul, Subgroup.coe_mul, hf2 a ha, hf2 b hb]
      calc g * (a * b) * g⁻¹ = g * (a * x₀ * (b * x₀)) * g⁻¹ := by
            rw [show (a : G) * x₀ * (b * x₀) = a * (x₀ * b) * x₀ by group, ← hbx,
              show (a : G) * (b * x₀) * x₀ = a * b * (x₀ * x₀) by group, hxx, mul_one]
        _ = g * (a * x₀) * g⁻¹ * (g * (b * x₀) * g⁻¹) * (x₀ * x₀) := by
            rw [hxx, mul_one]; group
        _ = g * (a * x₀) * g⁻¹ * (x₀ * (g * (b * x₀) * g⁻¹)) * x₀ := by
            rw [← hV _ hB'V _ hx₀V]; group
        _ = g * (a * x₀) * g⁻¹ * x₀ * (g * (b * x₀) * g⁻¹ * x₀) := by group
  have hinj : Function.Injective f := by
    intro a b hab
    have e := congrArg Subtype.val hab
    by_cases ha : (a : G) ∈ V₂ <;> by_cases hb : (b : G) ∈ V₂
    · rw [hf1 a ha, hf1 b hb] at e
      exact Subtype.ext (mul_left_cancel (mul_right_cancel e))
    · exfalso
      apply hnotmem b hb
      rw [← e, hf1 a ha]
      exact hgV _ ha
    · exfalso
      apply hnotmem a ha
      rw [e, hf1 b hb]
      exact hgV _ hb
    · rw [hf2 a ha, hf2 b hb] at e
      exact Subtype.ext (mul_right_cancel (mul_left_cancel (mul_right_cancel
        (mul_right_cancel e))))
  set α : MulAut ↥V := MulEquiv.ofBijective (MonoidHom.mk' f hmul)
    ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩ with hα
  have htop : α ∈ autOn (hsM V) V := by
    rw [h.autOn_M_eq_top]
    exact Subgroup.mem_top _
  obtain ⟨m, hm⟩ := (mem_autOn_iff (le_refl _)).mp htop
  have hmw : ∀ w ∈ V₂, (m : G) * w * (m : G)⁻¹ = g * w * g⁻¹ := by
    intro w hw
    have e := congrArg (fun φ : MulAut ↥V => ((φ ⟨w, hV₂ hw⟩ : ↥V) : G)) hm
    rw [actionOn_apply_coe] at e
    rw [e]
    exact hf1 ⟨w, hV₂ hw⟩ hw
  set mm : G := (m : G) with hmm
  have hR : g⁻¹ * mm ∈ Subgroup.centralizer (V₂ : Set G) := by
    refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
    calc w * (g⁻¹ * mm) = g⁻¹ * (g * w * g⁻¹) * mm := by group
      _ = g⁻¹ * (mm * w * mm⁻¹) * mm := by rw [hmw w hw]
      _ = g⁻¹ * mm * w := by group
  rw [h.centralizer_V2_eq hV₂ hc hz] at hR
  have := (hsM V).mul_mem m.2 ((hsM V).inv_mem hR.1)
  rwa [← hmm, mul_inv_rev, inv_inv, mul_inv_cancel_left] at this

theorem centralizes_V_of_comm [Finite G] (h : HSSetting z V) (hV₂ : V₂ ≤ V)
    (hc : Nat.card V₂ = 4) {a y : G} (haM : a ∈ hsM V) (hyM : y ∈ hsM V)
    (haC : a ∈ Subgroup.centralizer (V₂ : Set G)) (hyN : y ∈ Subgroup.normalizer (V₂ : Set G))
    (hay : a * y = y * a) (hfix : ∀ w ∈ V₂, w * y = y * w → w = 1) :
    a ∈ Subgroup.centralizer (V : Set G) := by
  have hV : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy => h.comm_of_mem_V hx hy
  have hV2 : ∀ x ∈ V, x * x = 1 := fun x hx => h.mul_self_of_mem_V hx
  have hidx := h.mul_mem_V2 hV₂ hc
  have hconj : ∀ b ∈ hsM V, ∀ v ∈ V, b * v * b⁻¹ ∈ V := fun b hb v hv =>
    (Subgroup.mem_normalizer_iff.mp hb v).mp hv
  have haw : ∀ w ∈ V₂, a * w * a⁻¹ = w := fun w hw => by
    rw [← Subgroup.mem_centralizer_iff.mp haC w hw, mul_inv_cancel_right]
  refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
  by_cases hv₂ : v ∈ V₂
  · exact Subgroup.mem_centralizer_iff.mp haC v hv₂
  have hvv : v * v = 1 := hV2 v hv
  set w := a * v * a⁻¹ with hw
  have hwV : w ∈ V := hconj a haM v hv
  have hwV₂ : w ∉ V₂ := fun hw₂ => hv₂ (by
    have e := haw w hw₂
    have : v = w := by
      calc v = a⁻¹ * w * a := by rw [hw]; group
        _ = a⁻¹ * (a * w * a⁻¹) * a := by rw [e]
        _ = w := by group
    rw [this]
    exact hw₂)
  have hl : v * w ∈ V₂ := hidx v hv w hwV hv₂ hwV₂
  set v' := y * v * y⁻¹ with hv'
  have hv'V : v' ∈ V := hconj y hyM v hv
  have hv'V₂ : v' ∉ V₂ := fun h' => hv₂ (by
    have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hyN) v').mp h'
    rwa [hv', inv_inv, show y⁻¹ * (y * v * y⁻¹) * y = v by group] at this)
  have hμ : v * v' ∈ V₂ := hidx v hv v' hv'V hv₂ hv'V₂
  have hμV : v * v' ∈ V := hV₂ hμ
  have hav' : a * v' * a⁻¹ = w * (v * v') := by
    have e : v' = v * (v * v') := by rw [← mul_assoc, hvv, one_mul]
    calc a * v' * a⁻¹ = a * (v * (v * v')) * a⁻¹ := by rw [← e]
      _ = (a * v * a⁻¹) * (a * (v * v') * a⁻¹) := by group
      _ = w * (v * v') := by rw [haw _ hμ]
  have hyl : y * (v * w) * y⁻¹ = v * w := by
    have hyw : y * w * y⁻¹ = a * v' * a⁻¹ := by
      have hya : y⁻¹ * a⁻¹ = a⁻¹ * y⁻¹ := by rw [← mul_inv_rev, ← mul_inv_rev, hay]
      calc y * w * y⁻¹ = (y * a) * v * (a⁻¹ * y⁻¹) := by rw [hw]; group
        _ = (a * y) * v * (y⁻¹ * a⁻¹) := by rw [hay, hya]
        _ = a * v' * a⁻¹ := by rw [hv']; group
    have hμμ : (v * v') * (v * v') = 1 := hV2 _ hμV
    have hwμ : w * (v * v') = (v * v') * w := hV _ hwV _ hμV
    calc y * (v * w) * y⁻¹ = (y * v * y⁻¹) * (y * w * y⁻¹) := by group
      _ = v' * (w * (v * v')) := by rw [hyw, hav']
      _ = v' * ((v * v') * w) := by rw [hwμ]
      _ = v * (v * v') * ((v * v') * w) := by rw [← mul_assoc v v, hvv, one_mul]
      _ = v * ((v * v') * (v * v')) * w := by group
      _ = v * w := by rw [hμμ, mul_one]
  have hl1 : v * w = 1 := hfix _ hl (by
    calc v * w * y = y * (v * w) * y⁻¹ * y := by rw [hyl]
      _ = y * (v * w) := by group)
  have hwv : w = v := by
    calc w = v * (v * w) := by rw [← mul_assoc, hvv, one_mul]
      _ = v := by rw [hl1, mul_one]
  calc v * a = (a * v * a⁻¹) * a := by rw [← hw, hwv]
    _ = a * v := by group

end HSSetting

namespace HSCtx

variable {G : Type} [Group G] [Finite G] (C : HSCtx G)

theorem not_graph {c : G} (hcN : c ∈ Subgroup.normalizer (C.M.V2 : Set G)) (hcNN : c ∉ C.M.NN)
    (hcc : c * c = 1) {y : G} (hyRX : y ∈ C.M.RX) (hy3 : orderOf y = 3) (hcy : c * y = y * c) :
    False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hyN, hσlam⟩ := C.M.mem_pre.mp hyRX
  set σ := C.M.π ⟨y, hyN⟩ with hσ
  have hσst : σ ∈ stabS := hσlam.2
  have hy33 : y ^ 3 = 1 := by rw [← hy3]; exact pow_orderOf_eq_one y
  have hσ3 : σ ^ 3 = 1 := by
    rw [hσ, ← map_pow, show (⟨y, hyN⟩ : ↥(HSSetting.hsNB C.z C.s)) ^ 3 = 1 from
      Subtype.ext (by rw [Subgroup.coe_pow]; exact hy33), map_one]
  have hσ1 : σ ≠ 1 := by
    intro h1
    have hyB : y ∈ hsB C.z C.s := (C.M.ker ⟨y, hyN⟩).mp h1
    have hyy := C.M.mul_self_of_mem_hsB hyB
    have : y = 1 := by
      calc y = y ^ 3 * (y * y)⁻¹ := by group
        _ = 1 := by rw [hy33, hyy]; group
    rw [this, orderOf_one] at hy3
    exact absurd hy3 (by norm_num)
  have hF1 := (eq_zero_of_actS6_lam0 σ hσlam hσ3).resolve_left hσ1
  have hF4 := (inV2m_orbit_of_lam0 σ hσlam hσ3).resolve_left hσ1
  have hfixB : ∀ b ∈ hsB C.z C.s, b * y = y * b → b = 1 := by
    intro b hb hby
    obtain ⟨u, rfl⟩ := C.M.surj b hb
    have h1 := C.M.act' hyN u
    have h2 : y * C.M.Φ u * y⁻¹ = C.M.Φ u := by rw [← hby, mul_inv_cancel_right]
    rw [h2] at h1
    rw [hF1 u (C.M.inj h1).symm, C.M.Φ_zero]
  have hfixV₂ : ∀ w ∈ C.M.V2, w * y = y * w → w = 1 := fun w hw =>
    hfixB w (C.M.V2_le_hsB hw)
  have hyV₂ : y ∈ Subgroup.normalizer (C.M.V2 : Set G) :=
    C.M.NN_le_normalizer (C.M.pre_mono inf_le_right hyRX)
  have horb : ∀ u ∈ C.M.V2, u ≠ 1 → ∀ v ∈ C.M.V2,
      v = 1 ∨ v = u ∨ v = y * u * y⁻¹ ∨ v = y * (y * u * y⁻¹) * y⁻¹ := by
    intro u hu hu1 v hv
    obtain ⟨u', hu', rfl⟩ := hu
    obtain ⟨v', hv', rfl⟩ := hv
    have hu'0 : u' ≠ 0 := fun h0 => hu1 (by rw [h0, C.M.Φ_zero])
    have e1 : y * C.M.Φ u' * y⁻¹ = C.M.Φ (actS6 σ u') := C.M.act' hyN u'
    have e2 : y * (y * C.M.Φ u' * y⁻¹) * y⁻¹ = C.M.Φ (actS6 σ (actS6 σ u')) := by
      rw [e1, C.M.act' hyN]
    rcases hF4 u' v' hu' hv' with h0 | h0 | h0 | h0 | h0
    · exact absurd h0 hu'0
    · left; rw [h0, C.M.Φ_zero]
    · right; left; rw [h0]
    · right; right; left; rw [h0, e1]
    · right; right; right; rw [h0, e2]
  have hcyu : ∀ x, c * x * c⁻¹ = x → c * (y * x * y⁻¹) * c⁻¹ = y * x * y⁻¹ := by
    intro x hx
    have hyc' : y⁻¹ * c⁻¹ = c⁻¹ * y⁻¹ := by rw [← mul_inv_rev, ← mul_inv_rev, hcy]
    calc c * (y * x * y⁻¹) * c⁻¹ = (c * y) * x * (y⁻¹ * c⁻¹) := by group
      _ = (y * c) * x * (c⁻¹ * y⁻¹) := by rw [hcy, hyc']
      _ = y * (c * x * c⁻¹) * y⁻¹ := by group
      _ = y * x * y⁻¹ := by rw [hx]
  have hzz : C.z * C.z = 1 := C.h.z_mul_z
  have hV₂comm : ∀ a ∈ C.M.V2, ∀ b ∈ C.M.V2, a * b = b * a := by
    rintro _ ⟨a', -, rfl⟩ _ ⟨b', -, rfl⟩
    rw [← C.M.add, add_comm, C.M.add]
  have hcz : c * C.z * c⁻¹ = C.z := by
    by_contra hne
    have hwV : c * C.z * c⁻¹ ∈ C.M.V2 :=
      (Subgroup.mem_normalizer_iff.mp hcN C.z).mp C.M.z_mem_V2
    have huV : C.z * (c * C.z * c⁻¹) ∈ C.M.V2 := C.M.V2.mul_mem C.M.z_mem_V2 hwV
    have hu1 : C.z * (c * C.z * c⁻¹) ≠ 1 := fun h1 => hne (by
      calc c * C.z * c⁻¹ = C.z * (C.z * (c * C.z * c⁻¹)) := by
            rw [← mul_assoc, hzz, one_mul]
        _ = C.z := by rw [h1, mul_one])
    have hcu : c * (C.z * (c * C.z * c⁻¹)) * c⁻¹ = C.z * (c * C.z * c⁻¹) := by
      have hcw : c * (c * C.z * c⁻¹) * c⁻¹ = C.z := by
        calc c * (c * C.z * c⁻¹) * c⁻¹ = (c * c) * C.z * (c * c)⁻¹ := by group
          _ = C.z := by rw [hcc]; group
      calc c * (C.z * (c * C.z * c⁻¹)) * c⁻¹ =
          (c * C.z * c⁻¹) * (c * (c * C.z * c⁻¹) * c⁻¹) := by group
        _ = (c * C.z * c⁻¹) * C.z := by rw [hcw]
        _ = C.z * (c * C.z * c⁻¹) := hV₂comm _ hwV _ C.M.z_mem_V2
    rcases horb _ huV hu1 C.z C.M.z_mem_V2 with h0 | h0 | h0 | h0
    · exact C.h.z_ne_one h0
    · apply hne
      conv_lhs => rw [h0]
      rw [hcu, ← h0]
    · apply hne
      conv_lhs => rw [h0]
      rw [hcyu _ hcu, ← h0]
    · apply hne
      conv_lhs => rw [h0]
      rw [hcyu _ (hcyu _ hcu), ← h0]
  have hcV₂ : c ∈ Subgroup.centralizer (C.M.V2 : Set G) := by
    refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
    have hcv : c * v * c⁻¹ = v := by
      rcases horb C.z C.M.z_mem_V2 C.h.z_ne_one v hv with h0 | h0 | h0 | h0
      · rw [h0]; group
      · rw [h0]; exact hcz
      · rw [h0]; exact hcyu _ hcz
      · rw [h0]; exact hcyu _ (hcyu _ hcz)
    calc v * c = c * v * c⁻¹ * c := by rw [hcv]
      _ = c * v := by group
  obtain ⟨V', h', hV'⟩ := C.M.exists_setting_V2 C.h
  have hNV' := h'.normalizer_V2_le_M hV' C.M.card_V2 C.M.z_mem_V2
  have hyM : y ∈ hsM V' := hNV' hyV₂
  have hinV : ∀ a : G, a ∈ Subgroup.normalizer (C.M.V2 : Set G) →
      a ∈ Subgroup.centralizer (C.M.V2 : Set G) → a * y = y * a → a * a = 1 → a ∈ V' := by
    intro a haN haC hay haa
    have haM : a ∈ hsM V' := hNV' haN
    have haV' := h'.centralizes_V_of_comm hV' C.M.card_V2 haM hyM haC hyV₂ hay hfixV₂
    have haP : a ∈ hsP V' := by
      rw [← h'.centralizer_V_eq]
      exact ⟨haM, haV'⟩
    exact h'.mem_V_of_mem_P haP haa
  have hcV' : c ∈ V' := hinV c hcN hcV₂ hcy hcc
  obtain ⟨hζfix, hζζ, hζ1, hζ3⟩ := zetaS_facts
  have hζσ : Commute zetaS σ := (zetaS_comm σ hσst).symm
  obtain ⟨v, hvy, σ', hσ', hπv⟩ := C.M.exists_normalizing_lift C.h C.hsmemH C.hsnotK C.hss
    C.hg₀ ⟨y, hyN⟩ hy3 zetaS (by
      rw [show zetaS * C.M.π ⟨y, hyN⟩ * zetaS⁻¹ = C.M.π ⟨y, hyN⟩ by
        rw [← hσ, hζσ.eq, mul_inv_cancel_right]]
      exact Subgroup.mem_zpowers _)
  rw [← hσ] at hσ'
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hσ'
  have hσ'c : Commute σ' σ := by rw [← hk]; exact Commute.zpow_left (Commute.refl σ) k
  have hζσ' : Commute σ' zetaS := by rw [← hk]; exact (hζσ.symm.zpow_left k)
  have hσ'3 : σ' ^ 3 = 1 := by
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hσ3, one_zpow]
  have hvy' : (v : G) * y * (v : G)⁻¹ = y := by
    rcases eq_of_mem_zpowers_three hy3 hvy with h1 | h1 | h1
    · exfalso
      have : y = 1 := by
        calc y = (v : G)⁻¹ * ((v : G) * y * (v : G)⁻¹) * v := by group
          _ = 1 := by rw [h1]; group
      rw [this, orderOf_one] at hy3
      exact absurd hy3 (by norm_num)
    · exact h1
    · exfalso
      have e : v * ⟨y, hyN⟩ * v⁻¹ = (⟨y, hyN⟩ : ↥(HSSetting.hsNB C.z C.s))⁻¹ := Subtype.ext (by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv]
        exact h1)
      have e' := congrArg C.M.π e
      rw [map_mul, map_mul, map_inv, map_inv, hπv, ← hσ] at e'
      have hs : σ' * zetaS * σ * (σ' * zetaS)⁻¹ = σ := by
        calc σ' * zetaS * σ * (σ' * zetaS)⁻¹ = σ' * (zetaS * σ * zetaS⁻¹) * σ'⁻¹ := by group
          _ = σ' * σ * σ'⁻¹ := by rw [hζσ.eq, mul_inv_cancel_right]
          _ = σ := by rw [hσ'c.eq, mul_inv_cancel_right]
      rw [hs] at e'
      apply hσ1
      calc σ = σ ^ 3 * (σ * σ)⁻¹ := by group
        _ = 1 := by rw [hσ3, show σ * σ = 1 by
              calc σ * σ = σ * σ⁻¹ := by rw [← e']
                _ = 1 := mul_inv_cancel σ]; group
  have hvyc : (v : G) * y = y * v := by
    calc (v : G) * y = (v : G) * y * (v : G)⁻¹ * v := by group
      _ = y * v := by rw [hvy']
  have hπf : C.M.π (v ^ 3) = zetaS := by
    rw [map_pow, hπv, hζσ'.mul_pow, hσ'3, one_mul, hζ3]
  set f : G := ((v ^ 3 : ↥(HSSetting.hsNB C.z C.s)) : G) with hf
  have hfy : f * y = y * f := by
    rw [hf, Subgroup.coe_pow]
    exact (Commute.pow_left (show Commute (v : G) y from hvyc) 3).eq
  have hff : f * f = 1 := by
    have hB : ((v ^ 3 * v ^ 3 : ↥(HSSetting.hsNB C.z C.s)) : G) ∈ hsB C.z C.s :=
      (C.M.ker _).mp (by rw [map_mul, hπf, hζζ])
    refine hfixB _ hB ?_
    calc f * f * y = f * (f * y) := by group
      _ = y * (f * f) := by rw [hfy, ← mul_assoc, hfy, mul_assoc]
  have hf1 : f ≠ 1 := by
    intro h1
    have : v ^ 3 = 1 := Subtype.ext h1
    rw [this, map_one] at hπf
    exact hζ1 hπf.symm
  have hfpre : f ∈ C.M.pre fixS := C.M.mem_pre.mpr ⟨(v ^ 3).2, by
    rw [show (⟨f, (v ^ 3).2⟩ : ↥(HSSetting.hsNB C.z C.s)) = v ^ 3 from rfl, hπf]
    exact hζfix⟩
  have hfNN : f ∈ C.M.NN := C.M.pre_mono fixS_le_stabS hfpre
  have hfV₂ : f ∈ Subgroup.centralizer (C.M.V2 : Set G) := C.M.centralizes_of_mem_pre_fixS hfpre
  have hfV' : f ∈ V' := hinV f (C.M.NN_le_normalizer hfNN) hfV₂ hfy hff
  have hcV₂' : c ∉ C.M.V2 := fun hc => hcNN (C.M.hsB_le_pre stabS (C.M.V2_le_hsB hc))
  have hfV₂' : f ∉ C.M.V2 := fun hf' => hf1 (hfixV₂ f hf' hfy)
  have hcf : c * f ∈ C.M.V2 := h'.mul_mem_V2 hV' C.M.card_V2 c hcV' f hfV' hcV₂' hfV₂'
  have hcfy : c * f * y = y * (c * f) := by
    rw [mul_assoc, hfy, ← mul_assoc, hcy, mul_assoc]
  have hcf1 := hfixV₂ _ hcf hcfy
  apply hcNN
  have : c = f := by
    calc c = c * f * f := by rw [mul_assoc, hff, mul_one]
      _ = f := by rw [hcf1, one_mul]
  rw [this]
  exact hfNN

end HSCtx

end CFSG.Quasithin.HSType
