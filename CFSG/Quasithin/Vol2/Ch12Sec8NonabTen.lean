module

public import CFSG.Quasithin.Vol2.Ch12Sec8NonabNine

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {T M L : Subgroup G}

omit [Finite G] in
theorem centerOf_rconj (X : Subgroup G) (g : G) :
    centerOf (rconj X g) = rconj (centerOf X) g := by
  ext y
  constructor
  · rintro ⟨hy, hc⟩
    have hy' : g * y * g⁻¹ ∈ X := mem_rconj.mp hy
    refine mem_rconj.mpr ⟨hy', Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
    have hz' : g⁻¹ * z * g ∈ rconj X g := by
      rw [mem_rconj]
      have e : g * (g⁻¹ * z * g) * g⁻¹ = z := by group
      rw [e]
      exact hz
    have := Subgroup.mem_centralizer_iff.mp hc _ hz'
    calc z * (g * y * g⁻¹) = g * ((g⁻¹ * z * g) * y) * g⁻¹ := by group
      _ = g * (y * (g⁻¹ * z * g)) * g⁻¹ := by rw [this]
      _ = g * y * g⁻¹ * z := by group
  · intro hy
    obtain ⟨hy1, hy2⟩ := mem_rconj.mp hy
    refine ⟨mem_rconj.mpr hy1, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
    have hz' : g * z * g⁻¹ ∈ X := mem_rconj.mp hz
    have := Subgroup.mem_centralizer_iff.mp hy2 _ hz'
    calc z * y = g⁻¹ * ((g * z * g⁻¹) * (g * y * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * y * g⁻¹) * (g * z * g⁻¹)) * g := by rw [this]
      _ = y * z := by group

omit [Finite G] in
theorem exists_eq_mul_of_mem_sup_of_forall_commute {A B : Subgroup G}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  have hA : A ≤ Subgroup.normalizer (B : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro b
    constructor
    · intro hb
      have e : a * b * a⁻¹ = b := by
        calc a * b * a⁻¹ = (b * a) * a⁻¹ := by rw [hAB a ha b hb]
          _ = b := by group
      rw [e]
      exact hb
    · intro hb
      have h2 : a * (a * b * a⁻¹) = (a * b * a⁻¹) * a := hAB a ha _ hb
      have h3 : (a * b * a⁻¹) * a = a * b := by group
      rw [h3] at h2
      have h4 : a * b * a⁻¹ = b := mul_left_cancel h2
      rw [h4] at hb
      exact hb
  have hmem : x ∈ ((A : Set G) * (B : Set G)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right A B hA]
    exact hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hmem
  exact ⟨a, ha, b, hb, rfl⟩

omit [Finite G] in
theorem rconj_le_rconj {X Y : Subgroup G} (hXY : X ≤ Y) (g : G) : rconj X g ≤ rconj Y g :=
  fun _ hy => mem_rconj.mpr (hXY (mem_rconj.mp hy))

omit [Finite G] in
theorem rconj_sup_eq (X Y : Subgroup G) (g : G) : rconj (X ⊔ Y) g = rconj X g ⊔ rconj Y g :=
  Subgroup.map_sup _ _ _

omit [Finite G] in
theorem rconj_rconj_inv_eq (X : Subgroup G) (g : G) : rconj (rconj X g) g⁻¹ = X := by
  ext y
  rw [mem_rconj, mem_rconj]
  have e : g * (g⁻¹ * y * g⁻¹⁻¹) * g⁻¹ = y := by group
  rw [e]

omit [Finite G] in
theorem GoodElt128.inv {g : G} (hg : GoodElt128 T L g) : GoodElt128 T L g⁻¹ :=
  ⟨Subgroup.inv_mem _ hg.mem, fun hn => hg.not_mem (by simpa using Subgroup.inv_mem _ hn)⟩

omit [Finite G] in
theorem exists_pow_sq_eq_one_ne_one {T : Subgroup G} (hT : IsPGroup 2 T) {z : G} (hzT : z ∈ T)
    (hz : z ≠ 1) : ∃ k : ℕ, (z ^ k) ^ 2 = 1 ∧ z ^ k ≠ 1 := by
  obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp hT) ⟨z, hzT⟩
  have hm' : orderOf z = 2 ^ m := by
    have := Subgroup.orderOf_mk z hzT
    rw [this] at hm
    exact hm
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := by
    refine Nat.exists_eq_succ_of_ne_zero ?_
    rintro rfl
    exact hz (orderOf_eq_one_iff.mp (by rw [hm']; rfl))
  have h2 : orderOf (z ^ 2 ^ k) = 2 := by
    rw [orderOf_pow_of_dvd (pow_ne_zero k two_ne_zero)
      (by rw [hm']; exact pow_dvd_pow 2 (Nat.le_succ k)), hm', pow_succ,
      Nat.mul_div_cancel_left _ (pow_pos two_pos k)]
  refine ⟨2 ^ k, ?_, fun he => ?_⟩
  · have := pow_orderOf_eq_one (z ^ 2 ^ k)
    rwa [h2] at this
  · rw [he, orderOf_one] at h2
    exact absurd h2 (by norm_num)

namespace Hyp1281Two

omit [Finite G] in
theorem rconj_centerOf_le_rconj_wOfU (T M : Subgroup G) (g : G) :
    rconj (centerOf (uOfL22 T M)) g ≤ rconj (wOfU T M) g :=
  rconj_le_rconj (centerOf_uOfL22_le_wOfU T M) g

theorem centerOf_wOfU_eq (h : Hyp1281Two G T M L) (hU : ¬ IsMulCommutative ↥(uOfL22 T M)) :
    centerOf (wOfU T M) = VZ T M ⊔ centerOf (uOfL22 T M) := by
  set U := uOfL22 T M with hUdef
  set W := wOfU T M with hWdef
  set Zu := centerOf U with hZudef
  have hA := h.almostSpecialHyp_g1
  have hVW : VZ T M ≤ W := h.VZ_le_wOfU
  have hZuW : Zu ≤ W := centerOf_uOfL22_le_wOfU T M
  apply le_antisymm
  · intro z hz
    have hzW : z ∈ W := hz.1
    have hzC : z ∈ Subgroup.centralizer (W : Set G) := hz.2
    have hzcomm : ∀ w ∈ W, w * z = z * w := fun w hw => Subgroup.mem_centralizer_iff.mp hzC w hw
    obtain ⟨u₀, hu₀U, hu₀W⟩ : ∃ u₀ ∈ U, u₀ ∉ W := by
      by_contra hall
      push Not at hall
      exact h.not_le_centralizer_VZ_of_nonabelian hU fun u hu => (hall u hu).2
    have hcentU : ∀ y ∈ U, (∀ w ∈ W, w * y = y * w) → u₀ * y = y * u₀ → y ∈ Zu := by
      intro y hyU hyW hyu
      refine ⟨hyU, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
      rcases h.mem_wOfU_or_inv_mul_mem hu₀U hu hu₀W with hu' | hu'
      · exact hyW u hu'
      · have h2 := hyW _ hu'
        calc u * y = u₀ * ((u₀⁻¹ * u) * y) := by group
          _ = u₀ * (y * (u₀⁻¹ * u)) := by rw [h2]
          _ = (u₀ * y) * (u₀⁻¹ * u) := by group
          _ = (y * u₀) * (u₀⁻¹ * u) := by rw [hyu]
          _ = y * u := by group
    by_cases hc0 : u₀ * z = z * u₀
    · exact Subgroup.mem_sup_right (hcentU z (wOfU_le_uOfL22 T M hzW) hzcomm hc0)
    ·
      obtain ⟨ζ₀, hζ₀Z, hζ₀1, hζ₀all⟩ := h.exists_zgen
      obtain ⟨a, haV, haZ⟩ := h.exists_mem_VZ_not_mem
      have hzU : z ∈ U := wOfU_le_uOfL22 T M hzW
      have haU : a ∈ U := VZ_le_uOfL22 T M haV
      have hζZ : u₀ * z * u₀⁻¹ * z⁻¹ ∈ quasithinOmegaOneCenter T :=
        h.commutator_mem_omegaOneCenter hu₀U hzU
      have hζ1 : u₀ * z * u₀⁻¹ * z⁻¹ ≠ 1 := by
        intro he
        apply hc0
        calc u₀ * z = (u₀ * z * u₀⁻¹ * z⁻¹) * z * u₀ := by group
          _ = z * u₀ := by rw [he]; group
      have haZ' : u₀ * a * u₀⁻¹ * a⁻¹ ∈ quasithinOmegaOneCenter T :=
        h.commutator_mem_omegaOneCenter hu₀U haU
      have ha1 : u₀ * a * u₀⁻¹ * a⁻¹ ≠ 1 := by
        intro he
        apply hu₀W
        refine ⟨hu₀U, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
        obtain ⟨z₁, hz₁Z, hz₁1, hz₁all⟩ := h.exists_zgen
        have hcases := h.VZ_cases hz₁Z hz₁1 haV haZ
        have hu₀z₁ : u₀ * z₁ = z₁ * u₀ := by
          have := Subgroup.mem_centralizer_iff.mp (h.uOfL22_le_g1 hu₀U) z₁ hz₁Z
          exact this.symm
        have hu₀a : u₀ * a = a * u₀ := by
          calc u₀ * a = (u₀ * a * u₀⁻¹ * a⁻¹) * a * u₀ := by group
            _ = a * u₀ := by rw [he]; group
        rcases hcases v hv with rfl | rfl | rfl | rfl
        · simp
        · exact hu₀z₁.symm
        · exact hu₀a.symm
        · calc z₁ * a * u₀ = z₁ * (a * u₀) := by group
            _ = z₁ * (u₀ * a) := by rw [hu₀a]
            _ = (z₁ * u₀) * a := by group
            _ = (u₀ * z₁) * a := by rw [hu₀z₁]
            _ = u₀ * (z₁ * a) := by group
      have hζeq : u₀ * z * u₀⁻¹ * z⁻¹ = u₀ * a * u₀⁻¹ * a⁻¹ := by
        rcases hζ₀all _ hζZ with h1 | h1
        · exact absurd h1 hζ1
        · rcases hζ₀all _ haZ' with h2 | h2
          · exact absurd h2 ha1
          · rw [h1, h2]
      set ζ := u₀ * a * u₀⁻¹ * a⁻¹ with hζdef
      have hζcentral : ∀ y ∈ U, y * ζ = ζ * y := fun y hy =>
        (Subgroup.mem_centralizer_iff.mp (h.omegaOneCenter_le_centerOf_uOfL22 haZ').2 y hy)
      have hu1 : u₀ * z * u₀⁻¹ = ζ * z := by
        calc u₀ * z * u₀⁻¹ = (u₀ * z * u₀⁻¹ * z⁻¹) * z := by group
          _ = ζ * z := by rw [hζeq]
      have hu2 : u₀ * a * u₀⁻¹ = ζ * a := by
        calc u₀ * a * u₀⁻¹ = (u₀ * a * u₀⁻¹ * a⁻¹) * a := by group
          _ = ζ * a := by rw [hζdef]
      have hz'u : u₀ * (z * a⁻¹) * u₀⁻¹ = z * a⁻¹ := by
        have hc := hζcentral (z * a⁻¹) (U.mul_mem hzU (U.inv_mem haU))
        calc u₀ * (z * a⁻¹) * u₀⁻¹ = (u₀ * z * u₀⁻¹) * (u₀ * a * u₀⁻¹)⁻¹ := by group
          _ = (ζ * z) * (ζ * a)⁻¹ := by rw [hu1, hu2]
          _ = (ζ * (z * a⁻¹)) * ζ⁻¹ := by group
          _ = ((z * a⁻¹) * ζ) * ζ⁻¹ := by rw [← hc]
          _ = z * a⁻¹ := by group
      have hz'W : ∀ w ∈ W, w * (z * a⁻¹) = (z * a⁻¹) * w := by
        intro w hw
        have hwa : a * w = w * a := Subgroup.mem_centralizer_iff.mp hw.2 a haV
        have hwai : w * a⁻¹ = a⁻¹ * w := by
          calc w * a⁻¹ = a⁻¹ * (a * w) * a⁻¹ := by group
            _ = a⁻¹ * (w * a) * a⁻¹ := by rw [hwa]
            _ = a⁻¹ * w := by group
        calc w * (z * a⁻¹) = (w * z) * a⁻¹ := by group
          _ = (z * w) * a⁻¹ := by rw [hzcomm w hw]
          _ = z * (w * a⁻¹) := by group
          _ = z * (a⁻¹ * w) := by rw [hwai]
          _ = (z * a⁻¹) * w := by group
      have hz'u' : u₀ * (z * a⁻¹) = (z * a⁻¹) * u₀ := by
        calc u₀ * (z * a⁻¹) = (u₀ * (z * a⁻¹) * u₀⁻¹) * u₀ := by group
          _ = (z * a⁻¹) * u₀ := by rw [hz'u]
      have hz'Zu : z * a⁻¹ ∈ Zu :=
        hcentU _ (U.mul_mem hzU (U.inv_mem haU)) hz'W hz'u'
      have e : z = (z * a⁻¹) * a := by group
      rw [e]
      have := Subgroup.mul_mem_sup hz'Zu haV
      rwa [sup_comm] at this
  · exact sup_le (fun v hv => ⟨hVW hv, Subgroup.mem_centralizer_iff.mpr fun w hw =>
      (Subgroup.mem_centralizer_iff.mp (hw.2) v hv).symm⟩) (fun x hx => ⟨hZuW hx,
      Subgroup.mem_centralizer_iff.mpr fun w hw => (Subgroup.mem_centralizer_iff.mp hx.2 w
        (wOfU_le_uOfL22 T M hw))⟩)


section

variable (h : Hyp1281Two G T M L) (hU : ¬ IsMulCommutative ↥(uOfL22 T M)) {g : G}
  (hg : GoodElt128 T L g)

include h hU hg

theorem omegaOneCenter_inf_rconj_centerOf :
    quasithinOmegaOneCenter T ⊓ rconj (centerOf (uOfL22 T M)) g = ⊥ := by
  have h9 := h.lemma_12_8_9_seven hU hg.inv
  rw [eq_bot_iff]
  rintro y ⟨hyZ, hyZg⟩
  have h1 : g * y * g⁻¹ ∈ rconj (quasithinOmegaOneCenter T) g⁻¹ ⊓ centerOf (uOfL22 T M) := by
    refine ⟨mem_rconj.mpr ?_, mem_rconj.mp hyZg⟩
    have e : g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y := by group
    rw [e]
    exact hyZ
  rw [h9] at h1
  have h2 : g * y * g⁻¹ = 1 := Subgroup.mem_bot.mp h1
  have hy : y = 1 := by
    calc y = g⁻¹ * (g * y * g⁻¹) * g := by group
      _ = 1 := by rw [h2]; group
  rw [hy]
  exact Subgroup.one_mem _

theorem rconj_wOfU_le_normalizer_centerOf :
    rconj (wOfU T M) g ≤ Subgroup.normalizer (centerOf (uOfL22 T M) : Set G) :=
  fun _ hx => normalizer_le_normalizer_centerOf _
    (h.T_le_normalizer_uOfL22 (h.rconj_wOfU_le_T hU hg hx))

theorem pCoreOf_sup_le_normalizer_rconj_centerOf :
    pCoreOf 2 (L ⊔ uOfL22 T M) ≤
      Subgroup.normalizer (rconj (centerOf (uOfL22 T M)) g : Set G) :=
  le_normalizer_rconj_of (mem_normalizer_pCoreOf_sup g hg _)
    (fun _ hs => normalizer_le_normalizer_centerOf _
      (h.pCoreOf_sup_uOfL22_le_normalizer_U hU hg hs))

theorem centerOf_rconj_wOfU_eq :
    centerOf (rconj (wOfU T M) g) = VZ T M ⊔ rconj (centerOf (uOfL22 T M)) g := by
  rw [centerOf_rconj, h.centerOf_wOfU_eq hU, rconj_sup_eq,
    rconj_eq_of_mem_normalizer (h.LT_le_normalizer_VZ (Subgroup.mem_sup_left hg.mem))]

theorem exists_mul_of_mem_VZ {v : G} (hv : v ∈ VZ T M) :
    ∃ a ∈ quasithinOmegaOneCenter T, ∃ b ∈ rconj (quasithinOmegaOneCenter T) g, a * b = v := by
  obtain ⟨z, hzZ, hz1, -⟩ := h.exists_zgen
  have hgN : rconj (VZ T M) g = VZ T M :=
    rconj_eq_of_mem_normalizer (h.LT_le_normalizer_VZ (Subgroup.mem_sup_left hg.mem))
  have hzV : z ∈ VZ T M := omegaOneCenter_le_VZ T M hzZ
  have ha₀Zg : g⁻¹ * z * g ∈ rconj (quasithinOmegaOneCenter T) g := inv_mul_mul_mem_rconj hzZ
  have ha₀V : g⁻¹ * z * g ∈ VZ T M := by
    have : g⁻¹ * z * g ∈ rconj (VZ T M) g := inv_mul_mul_mem_rconj hzV
    rwa [hgN] at this
  have ha₀Z : g⁻¹ * z * g ∉ quasithinOmegaOneCenter T := by
    intro hmem
    have hTI := (h.l2Setting128 hU).V₁_inf_rconj hg.mem hg.not_mem
    have : g⁻¹ * z * g ∈ quasithinOmegaOneCenter T ⊓ rconj (quasithinOmegaOneCenter T) g :=
      ⟨hmem, ha₀Zg⟩
    rw [hTI] at this
    have h1 : g⁻¹ * z * g = 1 := Subgroup.mem_bot.mp this
    apply hz1
    calc z = g * (g⁻¹ * z * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  rcases h.VZ_cases hzZ hz1 ha₀V ha₀Z v hv with h1 | h1 | h1 | h1
  · exact ⟨1, Subgroup.one_mem _, 1, Subgroup.one_mem _, by rw [h1, mul_one]⟩
  · exact ⟨z, hzZ, 1, Subgroup.one_mem _, by rw [h1, mul_one]⟩
  · exact ⟨1, Subgroup.one_mem _, g⁻¹ * z * g, ha₀Zg, by rw [h1, one_mul]⟩
  · exact ⟨z, hzZ, g⁻¹ * z * g, ha₀Zg, h1.symm⟩

theorem lemma_12_8_10_one :
    centerOf (uOfL22 T M) ⊓ rconj (uOfL22 T M) g =
      (centerOf (uOfL22 T M) ⊓ rconj (centerOf (uOfL22 T M)) g) ⊔
        quasithinOmegaOneCenter T := by
  have hZZu : quasithinOmegaOneCenter T ≤ centerOf (uOfL22 T M) :=
    h.omegaOneCenter_le_centerOf_uOfL22
  have hVU := h.VZ_le_inf_rconj hU hg
  have hZgU : rconj (centerOf (uOfL22 T M)) g ≤ rconj (uOfL22 T M) g := by
    rw [← centerOf_rconj]
    exact inf_le_left
  apply le_antisymm
  · intro a ha
    obtain ⟨haZu, haUg⟩ := Subgroup.mem_inf.mp ha
    have haU : a ∈ uOfL22 T M := haZu.1
    have haX : a ∈ rconj (wOfU T M) g := by
      have : a ∈ uOfL22 T M ⊓ rconj (uOfL22 T M) g := ⟨haU, haUg⟩
      rw [← h.wOfU_inf_rconj_eq hU hg] at this
      exact this.2
    have hcentX : ∀ x ∈ rconj (wOfU T M) g, x * a = a * x := by
      intro x hx
      have hxN : x ∈ Subgroup.normalizer (centerOf (uOfL22 T M) : Set G) :=
        h.rconj_wOfU_le_normalizer_centerOf hU hg hx
      have hxUg : x ∈ rconj (uOfL22 T M) g := rconj_le_rconj (wOfU_le_uOfL22 T M) g hx
      have h1 : a * x * a⁻¹ * x⁻¹ ∈ centerOf (uOfL22 T M) := by
        have e : a * x * a⁻¹ * x⁻¹ = a * (x * a⁻¹ * x⁻¹) := by group
        rw [e]
        exact (centerOf (uOfL22 T M)).mul_mem haZu
          ((Subgroup.mem_normalizer_iff.mp hxN _).mp ((centerOf (uOfL22 T M)).inv_mem haZu))
      have h2 : a * x * a⁻¹ * x⁻¹ ∈ rconj (quasithinOmegaOneCenter T) g := by
        rw [mem_rconj]
        have ha' : g * a * g⁻¹ ∈ uOfL22 T M := mem_rconj.mp haUg
        have hx' : g * x * g⁻¹ ∈ uOfL22 T M := mem_rconj.mp hxUg
        have := h.commutator_mem_omegaOneCenter ha' hx'
        have e : g * (a * x * a⁻¹ * x⁻¹) * g⁻¹ =
            (g * a * g⁻¹) * (g * x * g⁻¹) * (g * a * g⁻¹)⁻¹ * (g * x * g⁻¹)⁻¹ := by group
        rw [e]
        exact this
      have h3 := h.lemma_12_8_9_seven hU hg
      have h4 : a * x * a⁻¹ * x⁻¹ ∈
          rconj (quasithinOmegaOneCenter T) g ⊓ centerOf (uOfL22 T M) := ⟨h2, h1⟩
      rw [h3] at h4
      have h5 : a * x * a⁻¹ * x⁻¹ = 1 := Subgroup.mem_bot.mp h4
      have h6 : a * x = x * a := by
        calc a * x = (a * x * a⁻¹ * x⁻¹) * x * a := by group
          _ = x * a := by rw [h5]; group
      exact h6.symm
    have haCX : a ∈ centerOf (rconj (wOfU T M) g) :=
      ⟨haX, Subgroup.mem_centralizer_iff.mpr hcentX⟩
    rw [h.centerOf_rconj_wOfU_eq hU hg] at haCX
    have hVc : ∀ v ∈ VZ T M, ∀ z ∈ rconj (centerOf (uOfL22 T M)) g, v * z = z * v := by
      intro v hv z hz
      have hvC : v ∈ centerOf (rconj (wOfU T M) g) := by
        rw [h.centerOf_rconj_wOfU_eq hU hg]
        exact Subgroup.mem_sup_left hv
      have hzX : z ∈ rconj (wOfU T M) g := rconj_centerOf_le_rconj_wOfU T M g hz
      exact (Subgroup.mem_centralizer_iff.mp hvC.2 z hzX).symm
    obtain ⟨v, hv, z, hz, rfl⟩ := exists_eq_mul_of_mem_sup_of_forall_commute hVc haCX
    obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := h.exists_mul_of_mem_VZ hU hg hv
    have hv₂Zg : v₂ ∈ rconj (centerOf (uOfL22 T M)) g := rconj_le_rconj hZZu g hv₂
    have hcZg : v₂ * z ∈ rconj (centerOf (uOfL22 T M)) g := Subgroup.mul_mem _ hv₂Zg hz
    have hv₁Zu : v₁ ∈ centerOf (uOfL22 T M) := hZZu hv₁
    have hcZu : v₂ * z ∈ centerOf (uOfL22 T M) := by
      have e : v₂ * z = v₁⁻¹ * (v₁ * v₂ * z) := by group
      rw [e]
      exact (centerOf (uOfL22 T M)).mul_mem ((centerOf (uOfL22 T M)).inv_mem hv₁Zu) haZu
    have hcomm : (v₂ * z) * v₁ = v₁ * (v₂ * z) :=
      Subgroup.mem_centralizer_iff.mp hv₁Zu.2 _ hcZu.1
    have e : v₁ * v₂ * z = (v₂ * z) * v₁ := by rw [hcomm]; group
    rw [e]
    exact Subgroup.mul_mem_sup ⟨hcZu, hcZg⟩ hv₁
  · refine sup_le (fun c hc => ⟨hc.1, hZgU hc.2⟩) fun c hc => ?_
    exact ⟨hZZu hc, (hVU (omegaOneCenter_le_VZ T M hc)).2⟩


theorem lemma_12_8_10_one_symm :
    rconj (centerOf (uOfL22 T M)) g ⊓ uOfL22 T M =
      (centerOf (uOfL22 T M) ⊓ rconj (centerOf (uOfL22 T M)) g) ⊔
        rconj (quasithinOmegaOneCenter T) g := by
  have hZZu : quasithinOmegaOneCenter T ≤ centerOf (uOfL22 T M) :=
    h.omegaOneCenter_le_centerOf_uOfL22
  have hV1gV : rconj (quasithinOmegaOneCenter T) g ≤ VZ T M :=
    (h.l2Setting128 hU).V₁_le_rconj_V hg.mem
  have hV1gZg : rconj (quasithinOmegaOneCenter T) g ≤ rconj (centerOf (uOfL22 T M)) g :=
    rconj_le_rconj hZZu g
  apply le_antisymm
  · intro a ha
    obtain ⟨haZg, haU⟩ := Subgroup.mem_inf.mp ha
    have haX : a ∈ rconj (wOfU T M) g := rconj_centerOf_le_rconj_wOfU T M g haZg
    have haW : a ∈ wOfU T M := by
      rw [h.wOfU_eq_inf_pCoreOf hU hg]
      exact ⟨haU, h.rconj_wOfU_le_pCoreOf hU hg haX⟩
    have hcentW : ∀ w ∈ wOfU T M, w * a = a * w := by
      intro w hw
      have hwN : w ∈ Subgroup.normalizer (rconj (centerOf (uOfL22 T M)) g : Set G) :=
        h.pCoreOf_sup_le_normalizer_rconj_centerOf hU hg (h.wOfU_le_pCoreOf hU hg hw)
      have hwU : w ∈ uOfL22 T M := wOfU_le_uOfL22 T M hw
      have h1 : a * w * a⁻¹ * w⁻¹ ∈ rconj (centerOf (uOfL22 T M)) g := by
        have e : a * w * a⁻¹ * w⁻¹ = a * (w * a⁻¹ * w⁻¹) := by group
        rw [e]
        exact (rconj (centerOf (uOfL22 T M)) g).mul_mem haZg
          ((Subgroup.mem_normalizer_iff.mp hwN _).mp
            ((rconj (centerOf (uOfL22 T M)) g).inv_mem haZg))
      have h2 : a * w * a⁻¹ * w⁻¹ ∈ quasithinOmegaOneCenter T :=
        h.commutator_mem_omegaOneCenter haU hwU
      have h3 : a * w * a⁻¹ * w⁻¹ ∈
          quasithinOmegaOneCenter T ⊓ rconj (centerOf (uOfL22 T M)) g := ⟨h2, h1⟩
      rw [h.omegaOneCenter_inf_rconj_centerOf hU hg] at h3
      have h4 : a * w * a⁻¹ * w⁻¹ = 1 := Subgroup.mem_bot.mp h3
      have h5 : a * w = w * a := by
        calc a * w = (a * w * a⁻¹ * w⁻¹) * w * a := by group
          _ = w * a := by rw [h4]; group
      exact h5.symm
    have haCW : a ∈ centerOf (wOfU T M) := ⟨haW, Subgroup.mem_centralizer_iff.mpr hcentW⟩
    rw [h.centerOf_wOfU_eq hU] at haCW
    have hVcW : ∀ v ∈ VZ T M, v ∈ centerOf (wOfU T M) := by
      intro v hv
      rw [h.centerOf_wOfU_eq hU]
      exact Subgroup.mem_sup_left hv
    have hVc : ∀ v ∈ VZ T M, ∀ z ∈ centerOf (uOfL22 T M), v * z = z * v := by
      intro v hv z hz
      exact (Subgroup.mem_centralizer_iff.mp (hVcW v hv).2 z
        (centerOf_uOfL22_le_wOfU T M hz)).symm
    obtain ⟨v, hv, z, hz, rfl⟩ := exists_eq_mul_of_mem_sup_of_forall_commute hVc haCW
    obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := h.exists_mul_of_mem_VZ hU hg hv
    have hv₁V : v₁ ∈ VZ T M := omegaOneCenter_le_VZ T M hv₁
    have hv₂V : v₂ ∈ VZ T M := hV1gV hv₂
    have hv₂Zg : v₂ ∈ rconj (centerOf (uOfL22 T M)) g := hV1gZg hv₂
    have hcZu : v₁ * z ∈ centerOf (uOfL22 T M) :=
      (centerOf (uOfL22 T M)).mul_mem (hZZu hv₁) hz
    have h12 : v₁ * v₂ = v₂ * v₁ :=
      Subgroup.mem_centralizer_iff.mp (hVcW v₂ hv₂V).2 v₁ (h.VZ_le_wOfU hv₁V)
    have hcZg : v₁ * z ∈ rconj (centerOf (uOfL22 T M)) g := by
      have e : v₁ * z = v₂⁻¹ * (v₁ * v₂ * z) := by rw [h12]; group
      rw [e]
      exact (rconj (centerOf (uOfL22 T M)) g).mul_mem
        ((rconj (centerOf (uOfL22 T M)) g).inv_mem hv₂Zg) haZg
    have hv₂C : v₂ ∈ centerOf (rconj (uOfL22 T M) g) := by
      rw [centerOf_rconj]; exact hv₂Zg
    have hcUg : v₁ * z ∈ rconj (uOfL22 T M) g := by
      have : v₁ * z ∈ centerOf (rconj (uOfL22 T M) g) := by rw [centerOf_rconj]; exact hcZg
      exact this.1
    have hcomm : (v₁ * z) * v₂ = v₂ * (v₁ * z) := Subgroup.mem_centralizer_iff.mp hv₂C.2 _ hcUg
    have e : v₁ * v₂ * z = (v₁ * z) * v₂ := by
      calc v₁ * v₂ * z = v₂ * v₁ * z := by rw [h12]
        _ = v₂ * (v₁ * z) := by group
        _ = (v₁ * z) * v₂ := hcomm.symm
    rw [e]
    exact Subgroup.mul_mem_sup ⟨hcZu, hcZg⟩ hv₂
  · refine sup_le (fun c hc => ⟨hc.2, hc.1.1⟩) fun c hc => ?_
    exact ⟨hV1gZg hc, VZ_le_uOfL22 T M (hV1gV hc)⟩

theorem lemma_12_8_10_two :
    centerOf (uOfL22 T M) ⊓ rconj (centerOf (uOfL22 T M)) g = centerOf (L ⊔ uOfL22 T M) := by
  apply le_antisymm
  · rintro y ⟨hyZu, hyZg⟩
    have hyU : y ∈ uOfL22 T M := hyZu.1
    have hyUg' : y ∈ centerOf (rconj (uOfL22 T M) g) := by
      rw [centerOf_rconj]; exact hyZg
    have hI : L ⊔ uOfL22 T M = uOfL22 T M ⊔ rconj (uOfL22 T M) g :=
      (h.sup_rconj_uOfL22_eq hU hg).symm
    have hyI : y ∈ L ⊔ uOfL22 T M := Subgroup.mem_sup_right hyU
    refine ⟨hyI, Subgroup.mem_centralizer_iff.mpr fun i hi => ?_⟩
    have hK : L ⊔ uOfL22 T M ≤ Subgroup.centralizer ({y} : Set G) := by
      rw [hI]
      refine sup_le (fun u hu => ?_) (fun u hu => ?_)
      · rw [Subgroup.mem_centralizer_iff]
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        rw [hz]
        exact (Subgroup.mem_centralizer_iff.mp hyZu.2 u hu).symm
      · rw [Subgroup.mem_centralizer_iff]
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        rw [hz]
        exact (Subgroup.mem_centralizer_iff.mp hyUg'.2 u hu).symm
    exact (Subgroup.mem_centralizer_iff.mp (hK hi) y (Set.mem_singleton y)).symm
  · intro z hz
    obtain ⟨hzI, hzC⟩ := hz
    have hzcomm : ∀ i ∈ L ⊔ uOfL22 T M, i * z = z * i := fun i hi =>
      Subgroup.mem_centralizer_iff.mp hzC i hi
    have hzS : z ∈ pCoreOf 2 (L ⊔ uOfL22 T M) := by
      rw [h.pCoreOf_sup_uOfL22_eq hU hg]
      refine ⟨hzI, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
      exact hzcomm v (Subgroup.mem_sup_right (VZ_le_uOfL22 T M hv))
    obtain ⟨u₀, hu₀U, hu₀W⟩ : ∃ u₀ ∈ uOfL22 T M, u₀ ∉ wOfU T M := by
      by_contra hall
      push Not at hall
      exact h.not_le_centralizer_VZ_of_nonabelian hU fun u hu => (hall u hu).2
    have hzE : z ∈ wOfU T M ⊓ rconj (wOfU T M) g := by
      refine (h.module_relations hU hg hu₀U hu₀W).2.2.2 z hzS ?_
      have hgz : g * z * g⁻¹ = z := by
        have := hzcomm g (hg.mem_sup _)
        calc g * z * g⁻¹ = (g * z) * g⁻¹ := rfl
          _ = (z * g) * g⁻¹ := by rw [this]
          _ = z := by group
      rw [hgz, inv_mul_cancel]
      exact Subgroup.one_mem _
    rw [h.wOfU_inf_rconj_eq hU hg] at hzE
    obtain ⟨hzU, hzUg⟩ := hzE
    refine ⟨⟨hzU, Subgroup.mem_centralizer_iff.mpr fun u hu =>
      hzcomm u (Subgroup.mem_sup_right hu)⟩, ?_⟩
    rw [← centerOf_rconj]
    refine ⟨hzUg, Subgroup.mem_centralizer_iff.mpr fun u hu => hzcomm u ?_⟩
    rw [← h.sup_rconj_uOfL22_eq hU hg]
    exact Subgroup.mem_sup_right hu

theorem omegaOneCenter_inf_centerOf_ne_bot (hN : centerOf (L ⊔ uOfL22 T M) ≠ ⊥) :
    quasithinOmegaOneCenter T ⊓ centerOf (L ⊔ uOfL22 T M) ≠ ⊥ := by
  have hNS : centerOf (L ⊔ uOfL22 T M) ≤ pCoreOf 2 (L ⊔ uOfL22 T M) := by
    intro z hz
    rw [h.pCoreOf_sup_uOfL22_eq hU hg]
    refine ⟨hz.1, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
    exact Subgroup.mem_centralizer_iff.mp hz.2 v (Subgroup.mem_sup_right (VZ_le_uOfL22 T M hv))
  have hNT : centerOf (L ⊔ uOfL22 T M) ≤ T := hNS.trans (h.pCoreOf_sup_uOfL22_le_T hU hg)
  have hTnorm : T ≤ Subgroup.normalizer (centerOf (L ⊔ uOfL22 T M) : Set G) := fun t ht =>
    normalizer_le_normalizer_centerOf _
      (h.LT_le_normalizer_sup_uOfL22 (Subgroup.mem_sup_right ht))
  obtain ⟨z, hzN, hz1, hzT⟩ := exists_ne_one_mem_centralizer h.sylow.1 hNT hTnorm hN
  obtain ⟨k, hk2, hk1⟩ := exists_pow_sq_eq_one_ne_one h.sylow.1 (hNT hzN) hz1
  intro hbot
  apply hk1
  have hyN : z ^ k ∈ centerOf (L ⊔ uOfL22 T M) := Subgroup.pow_mem _ hzN k
  have hyZ : z ^ k ∈ quasithinOmegaOneCenter T := by
    refine Subgroup.subset_closure ⟨⟨hNT hyN, Subgroup.mem_centralizer_iff.mpr fun t ht => ?_⟩, hk2⟩
    exact Commute.pow_right (hzT t ht) k
  have : z ^ k ∈ quasithinOmegaOneCenter T ⊓ centerOf (L ⊔ uOfL22 T M) := ⟨hyZ, hyN⟩
  rw [hbot] at this
  exact Subgroup.mem_bot.mp this

theorem lemma_12_8_10_three
    (hlt : quasithinOmegaOneCenter T < centerOf (uOfL22 T M) ⊓ rconj (uOfL22 T M) g) :
    quasithinOmegaOneCenter T ⊓ centerOf (L ⊔ uOfL22 T M) ≠ ⊥ := by
  refine h.omegaOneCenter_inf_centerOf_ne_bot hU hg ?_
  intro h0
  have h1 := h.lemma_12_8_10_one hU hg
  rw [h.lemma_12_8_10_two hU hg, h0, bot_sup_eq] at h1
  exact hlt.ne h1.symm

theorem commutator_wOfU_rconj_centerOf_le :
    ⁅wOfU T M, rconj (centerOf (uOfL22 T M)) g⁆ ≤
      rconj (centerOf (uOfL22 T M)) g ⊓ uOfL22 T M := by
  rw [Subgroup.commutator_le]
  intro w hw z hz
  have hwN : w ∈ Subgroup.normalizer (rconj (centerOf (uOfL22 T M)) g : Set G) :=
    h.pCoreOf_sup_le_normalizer_rconj_centerOf hU hg (h.wOfU_le_pCoreOf hU hg hw)
  have hzX : z ∈ rconj (wOfU T M) g := rconj_centerOf_le_rconj_wOfU T M g hz
  have hzN : z ∈ Subgroup.normalizer (uOfL22 T M : Set G) :=
    h.T_le_normalizer_uOfL22 (h.rconj_wOfU_le_T hU hg hzX)
  have hwU : w ∈ uOfL22 T M := wOfU_le_uOfL22 T M hw
  refine ⟨?_, ?_⟩
  · have e : ⁅w, z⁆ = (w * z * w⁻¹) * z⁻¹ := by rw [commutatorElement_def]
    rw [e]
    exact (rconj (centerOf (uOfL22 T M)) g).mul_mem
      ((Subgroup.mem_normalizer_iff.mp hwN z).mp hz)
      ((rconj (centerOf (uOfL22 T M)) g).inv_mem hz)
  · have e : ⁅w, z⁆ = w * (z * w⁻¹ * z⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact (uOfL22 T M).mul_mem hwU
      ((Subgroup.mem_normalizer_iff.mp hzN _).mp ((uOfL22 T M).inv_mem hwU))

theorem lemma_12_8_10_four :
    ⁅wOfU T M, rconj (centerOf (uOfL22 T M)) g⁆ ≤ centerOf (uOfL22 T M) ⊔ VZ T M := by
  refine (h.commutator_wOfU_rconj_centerOf_le hU hg).trans ?_
  rw [h.lemma_12_8_10_one_symm hU hg]
  exact sup_le_sup inf_le_left ((h.l2Setting128 hU).V₁_le_rconj_V hg.mem)

theorem lemma_12_8_10_five (hle : rconj (centerOf (uOfL22 T M)) g ≤ uOfL22 T M) :
    centerOf (uOfL22 T M) = centerOf (L ⊔ uOfL22 T M) ⊔ quasithinOmegaOneCenter T ∧
      Disjoint (centerOf (L ⊔ uOfL22 T M)) (quasithinOmegaOneCenter T) ∧
      L ≤ Subgroup.centralizer (centerOf (L ⊔ uOfL22 T M) : Set G) := by
  have h1 := h.lemma_12_8_10_one_symm hU hg
  rw [inf_eq_left.mpr hle, h.lemma_12_8_10_two hU hg] at h1
  have hZI : rconj (centerOf (L ⊔ uOfL22 T M)) g⁻¹ = centerOf (L ⊔ uOfL22 T M) := by
    rw [← centerOf_rconj, rconj_eq_of_mem_normalizer]
    exact Subgroup.inv_mem _ (Subgroup.le_normalizer (hg.mem_sup _))
  refine ⟨?_, ?_, ?_⟩
  · have h2 := congrArg (fun K => rconj K g⁻¹) h1
    simp only [rconj_rconj_inv_eq, rconj_sup_eq, hZI] at h2
    exact h2
  · rw [disjoint_iff, eq_bot_iff]
    intro x hx
    have hxZg : x ∈ rconj (centerOf (uOfL22 T M)) g := by
      have := h.lemma_12_8_10_two hU hg
      have hxI : x ∈ centerOf (uOfL22 T M) ⊓ rconj (centerOf (uOfL22 T M)) g := by
        rw [this]; exact hx.1
      exact hxI.2
    have : x ∈ quasithinOmegaOneCenter T ⊓ rconj (centerOf (uOfL22 T M)) g := ⟨hx.2, hxZg⟩
    rw [h.omegaOneCenter_inf_rconj_centerOf hU hg] at this
    exact this
  · intro l hl
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (Subgroup.mem_centralizer_iff.mp hz.2 l (Subgroup.mem_sup_left hl)).symm

theorem lemma_12_8_10_six :
    centralizerMod (centerOf (uOfL22 T M)) (rconj (centerOf (uOfL22 T M)) g) (uOfL22 T M) =
        centralizerMod (quasithinOmegaOneCenter T) (rconj (centerOf (uOfL22 T M)) g)
          (uOfL22 T M) ∧
      centralizerMod (quasithinOmegaOneCenter T) (rconj (centerOf (uOfL22 T M)) g)
          (uOfL22 T M) =
        rconj (centerOf (uOfL22 T M)) g ⊓
          pCoreOf 2 (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ∧
      rconj (centerOf (uOfL22 T M)) g ⊓
          pCoreOf 2 (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) =
        rconj (centerOf (uOfL22 T M)) g ⊓ uOfL22 T M ∧
      rconj (centerOf (uOfL22 T M)) g ⊓ uOfL22 T M =
        (centerOf (uOfL22 T M) ⊓ rconj (centerOf (uOfL22 T M)) g) ⊔
          rconj (quasithinOmegaOneCenter T) g ∧
      (centerOf (uOfL22 T M) ⊓ rconj (centerOf (uOfL22 T M)) g) ⊔
          rconj (quasithinOmegaOneCenter T) g =
        centerOf (L ⊔ uOfL22 T M) ⊔ rconj (quasithinOmegaOneCenter T) g ∧
      centerOf (L ⊔ uOfL22 T M) ⊔ rconj (quasithinOmegaOneCenter T) g ≤ uOfL22 T M := by
  have hZZu : quasithinOmegaOneCenter T ≤ centerOf (uOfL22 T M) :=
    h.omegaOneCenter_le_centerOf_uOfL22
  have hZgX : rconj (centerOf (uOfL22 T M)) g ≤ rconj (wOfU T M) g :=
    rconj_centerOf_le_rconj_wOfU T M g
  have hXT : ∀ y ∈ rconj (centerOf (uOfL22 T M)) g, y ∈ T := fun y hy =>
    h.rconj_wOfU_le_T hU hg (hZgX hy)
  have hTN : ∀ y ∈ T, y ∈ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) := by
    intro y hy
    rw [h.normalizer_Z_eq_centralizer]
    exact h.almostSpecialHyp_g1.T_le_H hy
  have h95 := h.lemma_12_8_9_five hU hg
  have hA0 : centralizerMod (centerOf (uOfL22 T M)) (rconj (centerOf (uOfL22 T M)) g)
      (uOfL22 T M) = rconj (centerOf (uOfL22 T M)) g ⊓ uOfL22 T M := by
    apply le_antisymm
    · intro y hy
      refine ⟨centralizerMod_le_left _ _ _ hy, ?_⟩
      have : y ∈ centralizerMod (centerOf (uOfL22 T M)) (rconj (wOfU T M) g) (uOfL22 T M) :=
        centralizerMod_mono_left _ hZgX hy
      rw [h95.1] at this
      exact wOfU_le_uOfL22 T M this.1
    · rintro y ⟨hyZg, hyU⟩
      refine ⟨hyZg, h.rconj_wOfU_le_normalizer_centerOf hU hg (hZgX hyZg), fun u hu => ?_⟩
      exact hZZu (h.commutator_mem_omegaOneCenter hyU hu)
  have hA1 : centralizerMod (quasithinOmegaOneCenter T) (rconj (centerOf (uOfL22 T M)) g)
      (uOfL22 T M) = rconj (centerOf (uOfL22 T M)) g ⊓ uOfL22 T M := by
    apply le_antisymm
    · intro y hy
      refine ⟨centralizerMod_le_left _ _ _ hy, ?_⟩
      have : y ∈ centralizerMod (quasithinOmegaOneCenter T) (rconj (wOfU T M) g)
          (uOfL22 T M) := centralizerMod_mono_left _ hZgX hy
      rw [h95.2] at this
      exact wOfU_le_uOfL22 T M this.1
    · rintro y ⟨hyZg, hyU⟩
      exact ⟨hyZg, hTN y (hXT y hyZg), fun u hu => h.commutator_mem_omegaOneCenter hyU hu⟩
  have hA2 : rconj (centerOf (uOfL22 T M)) g ⊓
      pCoreOf 2 (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) =
        rconj (centerOf (uOfL22 T M)) g ⊓ uOfL22 T M := by
    have h4 := h.lemma_12_8_4_four h.isHz_centralizer
    change centralizerMod (quasithinOmegaOneCenter T)
      (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) (uOfL22 T M) = _ at h4
    rw [← h4]
    apply le_antisymm
    · rintro y ⟨hyZg, hy⟩
      have : y ∈ centralizerMod (quasithinOmegaOneCenter T) (rconj (centerOf (uOfL22 T M)) g)
          (uOfL22 T M) := ⟨hyZg, hy.2.1, hy.2.2⟩
      rw [hA1] at this
      exact this
    · rintro y ⟨hyZg, hyU⟩
      refine ⟨hyZg, ?_, hTN y (hXT y hyZg), fun u hu => h.commutator_mem_omegaOneCenter hyU hu⟩
      exact h.almostSpecialHyp_g1.T_le_H (hXT y hyZg)
  refine ⟨hA0.trans hA1.symm, hA1.trans hA2.symm, hA2, h.lemma_12_8_10_one_symm hU hg, ?_, ?_⟩
  · rw [h.lemma_12_8_10_two hU hg]
  · refine sup_le ?_ ?_
    · rw [← h.lemma_12_8_10_two hU hg]
      exact fun c hc => hc.1.1
    · exact ((h.l2Setting128 hU).V₁_le_rconj_V hg.mem).trans (VZ_le_uOfL22 T M)

end

end Hyp1281Two

end CFSG.Quasithin
