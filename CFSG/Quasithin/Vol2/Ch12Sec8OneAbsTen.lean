module

public import CFSG.Quasithin.Vol2.Ch12Sec8NonabTen
public import CFSG.Quasithin.Vol2.Ch12Sec8OneAbsMod

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace L128A

variable {G : Type} [Group G] [Finite G] {V V₁ L T : Subgroup G}

omit [Finite G] in
theorem Good.inv {g : G} (hg : Good V₁ L g) : Good V₁ L g⁻¹ :=
  ⟨Subgroup.inv_mem _ hg.mem, fun hn => hg.not_mem (by simpa using Subgroup.inv_mem _ hn)⟩

namespace Setting

theorem LT_le_normalizer_sup_uA (S : Setting V V₁ L T) :
    L ⊔ T ≤ Subgroup.normalizer ((L ⊔ uA V V₁ : Subgroup G) : Set G) := by
  refine sup_le ((le_sup_left : L ≤ L ⊔ uA V V₁).trans Subgroup.le_normalizer) ?_
  intro t ht
  exact Subgroup.inf_normalizer_le_normalizer_sup L (uA V V₁)
    ⟨S.base.T_le_normL ht, S.T_le_normalizer_uA ht⟩

omit [Finite G] in
theorem rconj_centerOf_le_rconj_wA (V V₁ : Subgroup G) (g : G) :
    rconj (centerOf (uA V V₁)) g ≤ rconj (wA V V₁) g :=
  rconj_le_rconj (centerOf_uA_le_wA V V₁) g

theorem centerOf_wA_eq (S : Setting V V₁ L T) :
    centerOf (wA V V₁) = V ⊔ centerOf (uA V V₁) := by
  set U := uA V V₁ with hUdef
  set W := wA V V₁ with hWdef
  set Zu := centerOf U with hZudef
  have hA := S.base
  have hVW : V ≤ W := S.le_wA
  have hZuW : Zu ≤ W := centerOf_uA_le_wA V V₁
  apply le_antisymm
  · intro z hz
    have hzW : z ∈ W := hz.1
    have hzC : z ∈ Subgroup.centralizer (W : Set G) := hz.2
    have hzcomm : ∀ w ∈ W, w * z = z * w := fun w hw => Subgroup.mem_centralizer_iff.mp hzC w hw
    obtain ⟨u₀, hu₀U, hu₀W⟩ : ∃ u₀ ∈ U, u₀ ∉ W := by
      by_contra hall
      push Not at hall
      exact S.not_le_centralizer_V fun u hu => (hall u hu).2
    have hcentU : ∀ y ∈ U, (∀ w ∈ W, w * y = y * w) → u₀ * y = y * u₀ → y ∈ Zu := by
      intro y hyU hyW hyu
      refine ⟨hyU, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
      rcases S.mem_wA_or_inv_mul_mem hu₀U hu hu₀W with hu' | hu'
      · exact hyW u hu'
      · have h2 := hyW _ hu'
        calc u * y = u₀ * ((u₀⁻¹ * u) * y) := by group
          _ = u₀ * (y * (u₀⁻¹ * u)) := by rw [h2]
          _ = (u₀ * y) * (u₀⁻¹ * u) := by group
          _ = (y * u₀) * (u₀⁻¹ * u) := by rw [hyu]
          _ = y * u := by group
    by_cases hc0 : u₀ * z = z * u₀
    · exact Subgroup.mem_sup_right (hcentU z (wA_le_uA V V₁ hzW) hzcomm hc0)
    ·
      obtain ⟨ζ₀, hζ₀Z, hζ₀1, hζ₀all⟩ := S.exists_gen
      obtain ⟨a, haV, haZ⟩ := S.exists_mem_not_mem
      have hzU : z ∈ U := wA_le_uA V V₁ hzW
      have haU : a ∈ U := le_uA V V₁ haV
      have hζZ : u₀ * z * u₀⁻¹ * z⁻¹ ∈ V₁ :=
        S.commutator_mem hu₀U hzU
      have hζ1 : u₀ * z * u₀⁻¹ * z⁻¹ ≠ 1 := by
        intro he
        apply hc0
        calc u₀ * z = (u₀ * z * u₀⁻¹ * z⁻¹) * z * u₀ := by group
          _ = z * u₀ := by rw [he]; group
      have haZ' : u₀ * a * u₀⁻¹ * a⁻¹ ∈ V₁ :=
        S.commutator_mem hu₀U haU
      have ha1 : u₀ * a * u₀⁻¹ * a⁻¹ ≠ 1 := by
        intro he
        apply hu₀W
        refine ⟨hu₀U, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
        obtain ⟨z₁, hz₁Z, hz₁1, hz₁all⟩ := S.exists_gen
        have hcases := S.V_cases hz₁Z hz₁1 haV haZ
        have hu₀z₁ : u₀ * z₁ = z₁ * u₀ := by
          have := Subgroup.mem_centralizer_iff.mp (S.uA_le_centralizer hu₀U) z₁ hz₁Z
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
        (Subgroup.mem_centralizer_iff.mp (S.V₁_le_centerOf haZ').2 y hy)
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
        (wA_le_uA V V₁ hw))⟩)


section

variable (S : Setting V V₁ L T) {g : G}
  (hg : Good V₁ L g)

include S hg

omit [Finite G] in
theorem V₁_inf_rconj_centerOf :
    V₁ ⊓ rconj (centerOf (uA V V₁)) g = ⊥ := by
  have h9 := S.nine_seven hg.inv
  rw [eq_bot_iff]
  rintro y ⟨hyZ, hyZg⟩
  have h1 : g * y * g⁻¹ ∈ rconj (V₁) g⁻¹ ⊓ centerOf (uA V V₁) := by
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

theorem rconj_wA_le_normalizer_centerOf :
    rconj (wA V V₁) g ≤ Subgroup.normalizer (centerOf (uA V V₁) : Set G) :=
  fun _ hx => normalizer_le_normalizer_centerOf _
    (S.T_le_normalizer_uA (S.rconj_wA_le_T hg hx))

theorem pCoreOf_sup_le_normalizer_rconj_centerOf :
    pCoreOf 2 (L ⊔ uA V V₁) ≤
      Subgroup.normalizer (rconj (centerOf (uA V V₁)) g : Set G) :=
  le_normalizer_rconj_of (hg.mem_normalizer_pCoreOf _)
    (fun _ hs => normalizer_le_normalizer_centerOf _
      (S.pCoreOf_sup_le_normalizer_uA hg hs))

theorem centerOf_rconj_wA_eq :
    centerOf (rconj (wA V V₁) g) = V ⊔ rconj (centerOf (uA V V₁)) g := by
  rw [centerOf_rconj, S.centerOf_wA_eq, rconj_sup_eq,
    rconj_eq_of_mem_normalizer (S.LT_le_normalizer_V (Subgroup.mem_sup_left hg.mem))]

theorem exists_mul_of_mem_V {v : G} (hv : v ∈ V) :
    ∃ a ∈ V₁, ∃ b ∈ rconj (V₁) g, a * b = v := by
  obtain ⟨z, hzZ, hz1, -⟩ := S.exists_gen
  have hgN : rconj (V) g = V :=
    rconj_eq_of_mem_normalizer (S.LT_le_normalizer_V (Subgroup.mem_sup_left hg.mem))
  have hzV : z ∈ V := S.V₁_le hzZ
  have ha₀Zg : g⁻¹ * z * g ∈ rconj (V₁) g := inv_mul_mul_mem_rconj hzZ
  have ha₀V : g⁻¹ * z * g ∈ V := by
    have : g⁻¹ * z * g ∈ rconj (V) g := inv_mul_mul_mem_rconj hzV
    rwa [hgN] at this
  have ha₀Z : g⁻¹ * z * g ∉ V₁ := by
    intro hmem
    have hTI := (S.l2Setting).V₁_inf_rconj hg.mem hg.not_mem
    have : g⁻¹ * z * g ∈ V₁ ⊓ rconj (V₁) g :=
      ⟨hmem, ha₀Zg⟩
    rw [hTI] at this
    have h1 : g⁻¹ * z * g = 1 := Subgroup.mem_bot.mp this
    apply hz1
    calc z = g * (g⁻¹ * z * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  rcases S.V_cases hzZ hz1 ha₀V ha₀Z v hv with h1 | h1 | h1 | h1
  · exact ⟨1, Subgroup.one_mem _, 1, Subgroup.one_mem _, by rw [h1, mul_one]⟩
  · exact ⟨z, hzZ, 1, Subgroup.one_mem _, by rw [h1, mul_one]⟩
  · exact ⟨1, Subgroup.one_mem _, g⁻¹ * z * g, ha₀Zg, by rw [h1, one_mul]⟩
  · exact ⟨z, hzZ, g⁻¹ * z * g, ha₀Zg, h1.symm⟩

theorem ten_one :
    centerOf (uA V V₁) ⊓ rconj (uA V V₁) g =
      (centerOf (uA V V₁) ⊓ rconj (centerOf (uA V V₁)) g) ⊔
        V₁ := by
  have hZZu : V₁ ≤ centerOf (uA V V₁) :=
    S.V₁_le_centerOf
  have hVU := S.le_inf_rconj hg
  have hZgU : rconj (centerOf (uA V V₁)) g ≤ rconj (uA V V₁) g := by
    rw [← centerOf_rconj]
    exact inf_le_left
  apply le_antisymm
  · intro a ha
    obtain ⟨haZu, haUg⟩ := Subgroup.mem_inf.mp ha
    have haU : a ∈ uA V V₁ := haZu.1
    have haX : a ∈ rconj (wA V V₁) g := by
      have : a ∈ uA V V₁ ⊓ rconj (uA V V₁) g := ⟨haU, haUg⟩
      rw [← S.wA_inf_rconj_eq hg] at this
      exact this.2
    have hcentX : ∀ x ∈ rconj (wA V V₁) g, x * a = a * x := by
      intro x hx
      have hxN : x ∈ Subgroup.normalizer (centerOf (uA V V₁) : Set G) :=
        S.rconj_wA_le_normalizer_centerOf hg hx
      have hxUg : x ∈ rconj (uA V V₁) g := rconj_le_rconj (wA_le_uA V V₁) g hx
      have h1 : a * x * a⁻¹ * x⁻¹ ∈ centerOf (uA V V₁) := by
        have e : a * x * a⁻¹ * x⁻¹ = a * (x * a⁻¹ * x⁻¹) := by group
        rw [e]
        exact (centerOf (uA V V₁)).mul_mem haZu
          ((Subgroup.mem_normalizer_iff.mp hxN _).mp ((centerOf (uA V V₁)).inv_mem haZu))
      have h2 : a * x * a⁻¹ * x⁻¹ ∈ rconj (V₁) g := by
        rw [mem_rconj]
        have ha' : g * a * g⁻¹ ∈ uA V V₁ := mem_rconj.mp haUg
        have hx' : g * x * g⁻¹ ∈ uA V V₁ := mem_rconj.mp hxUg
        have := S.commutator_mem ha' hx'
        have e : g * (a * x * a⁻¹ * x⁻¹) * g⁻¹ =
            (g * a * g⁻¹) * (g * x * g⁻¹) * (g * a * g⁻¹)⁻¹ * (g * x * g⁻¹)⁻¹ := by group
        rw [e]
        exact this
      have h3 := S.nine_seven hg
      have h4 : a * x * a⁻¹ * x⁻¹ ∈
          rconj (V₁) g ⊓ centerOf (uA V V₁) := ⟨h2, h1⟩
      rw [h3] at h4
      have h5 : a * x * a⁻¹ * x⁻¹ = 1 := Subgroup.mem_bot.mp h4
      have h6 : a * x = x * a := by
        calc a * x = (a * x * a⁻¹ * x⁻¹) * x * a := by group
          _ = x * a := by rw [h5]; group
      exact h6.symm
    have haCX : a ∈ centerOf (rconj (wA V V₁) g) :=
      ⟨haX, Subgroup.mem_centralizer_iff.mpr hcentX⟩
    rw [S.centerOf_rconj_wA_eq hg] at haCX
    have hVc : ∀ v ∈ V, ∀ z ∈ rconj (centerOf (uA V V₁)) g, v * z = z * v := by
      intro v hv z hz
      have hvC : v ∈ centerOf (rconj (wA V V₁) g) := by
        rw [S.centerOf_rconj_wA_eq hg]
        exact Subgroup.mem_sup_left hv
      have hzX : z ∈ rconj (wA V V₁) g := rconj_centerOf_le_rconj_wA V V₁ g hz
      exact (Subgroup.mem_centralizer_iff.mp hvC.2 z hzX).symm
    obtain ⟨v, hv, z, hz, rfl⟩ := exists_eq_mul_of_mem_sup_of_forall_commute hVc haCX
    obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := S.exists_mul_of_mem_V hg hv
    have hv₂Zg : v₂ ∈ rconj (centerOf (uA V V₁)) g := rconj_le_rconj hZZu g hv₂
    have hcZg : v₂ * z ∈ rconj (centerOf (uA V V₁)) g := Subgroup.mul_mem _ hv₂Zg hz
    have hv₁Zu : v₁ ∈ centerOf (uA V V₁) := hZZu hv₁
    have hcZu : v₂ * z ∈ centerOf (uA V V₁) := by
      have e : v₂ * z = v₁⁻¹ * (v₁ * v₂ * z) := by group
      rw [e]
      exact (centerOf (uA V V₁)).mul_mem ((centerOf (uA V V₁)).inv_mem hv₁Zu) haZu
    have hcomm : (v₂ * z) * v₁ = v₁ * (v₂ * z) :=
      Subgroup.mem_centralizer_iff.mp hv₁Zu.2 _ hcZu.1
    have e : v₁ * v₂ * z = (v₂ * z) * v₁ := by rw [hcomm]; group
    rw [e]
    exact Subgroup.mul_mem_sup ⟨hcZu, hcZg⟩ hv₁
  · refine sup_le (fun c hc => ⟨hc.1, hZgU hc.2⟩) fun c hc => ?_
    exact ⟨hZZu hc, (hVU (S.V₁_le hc)).2⟩


theorem ten_one_symm :
    rconj (centerOf (uA V V₁)) g ⊓ uA V V₁ =
      (centerOf (uA V V₁) ⊓ rconj (centerOf (uA V V₁)) g) ⊔
        rconj (V₁) g := by
  have hZZu : V₁ ≤ centerOf (uA V V₁) :=
    S.V₁_le_centerOf
  have hV1gV : rconj (V₁) g ≤ V :=
    (S.l2Setting).V₁_le_rconj_V hg.mem
  have hV1gZg : rconj (V₁) g ≤ rconj (centerOf (uA V V₁)) g :=
    rconj_le_rconj hZZu g
  apply le_antisymm
  · intro a ha
    obtain ⟨haZg, haU⟩ := Subgroup.mem_inf.mp ha
    have haX : a ∈ rconj (wA V V₁) g := rconj_centerOf_le_rconj_wA V V₁ g haZg
    have haW : a ∈ wA V V₁ := by
      rw [S.wA_eq_inf_pCoreOf hg]
      exact ⟨haU, S.rconj_wA_le_pCoreOf hg haX⟩
    have hcentW : ∀ w ∈ wA V V₁, w * a = a * w := by
      intro w hw
      have hwN : w ∈ Subgroup.normalizer (rconj (centerOf (uA V V₁)) g : Set G) :=
        S.pCoreOf_sup_le_normalizer_rconj_centerOf hg (S.wA_le_pCoreOf hg hw)
      have hwU : w ∈ uA V V₁ := wA_le_uA V V₁ hw
      have h1 : a * w * a⁻¹ * w⁻¹ ∈ rconj (centerOf (uA V V₁)) g := by
        have e : a * w * a⁻¹ * w⁻¹ = a * (w * a⁻¹ * w⁻¹) := by group
        rw [e]
        exact (rconj (centerOf (uA V V₁)) g).mul_mem haZg
          ((Subgroup.mem_normalizer_iff.mp hwN _).mp
            ((rconj (centerOf (uA V V₁)) g).inv_mem haZg))
      have h2 : a * w * a⁻¹ * w⁻¹ ∈ V₁ :=
        S.commutator_mem haU hwU
      have h3 : a * w * a⁻¹ * w⁻¹ ∈
          V₁ ⊓ rconj (centerOf (uA V V₁)) g := ⟨h2, h1⟩
      rw [S.V₁_inf_rconj_centerOf hg] at h3
      have h4 : a * w * a⁻¹ * w⁻¹ = 1 := Subgroup.mem_bot.mp h3
      have h5 : a * w = w * a := by
        calc a * w = (a * w * a⁻¹ * w⁻¹) * w * a := by group
          _ = w * a := by rw [h4]; group
      exact h5.symm
    have haCW : a ∈ centerOf (wA V V₁) := ⟨haW, Subgroup.mem_centralizer_iff.mpr hcentW⟩
    rw [S.centerOf_wA_eq] at haCW
    have hVcW : ∀ v ∈ V, v ∈ centerOf (wA V V₁) := by
      intro v hv
      rw [S.centerOf_wA_eq]
      exact Subgroup.mem_sup_left hv
    have hVc : ∀ v ∈ V, ∀ z ∈ centerOf (uA V V₁), v * z = z * v := by
      intro v hv z hz
      exact (Subgroup.mem_centralizer_iff.mp (hVcW v hv).2 z
        (centerOf_uA_le_wA V V₁ hz)).symm
    obtain ⟨v, hv, z, hz, rfl⟩ := exists_eq_mul_of_mem_sup_of_forall_commute hVc haCW
    obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := S.exists_mul_of_mem_V hg hv
    have hv₁V : v₁ ∈ V := S.V₁_le hv₁
    have hv₂V : v₂ ∈ V := hV1gV hv₂
    have hv₂Zg : v₂ ∈ rconj (centerOf (uA V V₁)) g := hV1gZg hv₂
    have hcZu : v₁ * z ∈ centerOf (uA V V₁) :=
      (centerOf (uA V V₁)).mul_mem (hZZu hv₁) hz
    have h12 : v₁ * v₂ = v₂ * v₁ :=
      Subgroup.mem_centralizer_iff.mp (hVcW v₂ hv₂V).2 v₁ (S.le_wA hv₁V)
    have hcZg : v₁ * z ∈ rconj (centerOf (uA V V₁)) g := by
      have e : v₁ * z = v₂⁻¹ * (v₁ * v₂ * z) := by rw [h12]; group
      rw [e]
      exact (rconj (centerOf (uA V V₁)) g).mul_mem
        ((rconj (centerOf (uA V V₁)) g).inv_mem hv₂Zg) haZg
    have hv₂C : v₂ ∈ centerOf (rconj (uA V V₁) g) := by
      rw [centerOf_rconj]; exact hv₂Zg
    have hcUg : v₁ * z ∈ rconj (uA V V₁) g := by
      have : v₁ * z ∈ centerOf (rconj (uA V V₁) g) := by rw [centerOf_rconj]; exact hcZg
      exact this.1
    have hcomm : (v₁ * z) * v₂ = v₂ * (v₁ * z) := Subgroup.mem_centralizer_iff.mp hv₂C.2 _ hcUg
    have e : v₁ * v₂ * z = (v₁ * z) * v₂ := by
      calc v₁ * v₂ * z = v₂ * v₁ * z := by rw [h12]
        _ = v₂ * (v₁ * z) := by group
        _ = (v₁ * z) * v₂ := hcomm.symm
    rw [e]
    exact Subgroup.mul_mem_sup ⟨hcZu, hcZg⟩ hv₂
  · refine sup_le (fun c hc => ⟨hc.2, hc.1.1⟩) fun c hc => ?_
    exact ⟨hV1gZg hc, le_uA V V₁ (hV1gV hc)⟩

theorem ten_two :
    centerOf (uA V V₁) ⊓ rconj (centerOf (uA V V₁)) g = centerOf (L ⊔ uA V V₁) := by
  apply le_antisymm
  · rintro y ⟨hyZu, hyZg⟩
    have hyU : y ∈ uA V V₁ := hyZu.1
    have hyUg' : y ∈ centerOf (rconj (uA V V₁) g) := by
      rw [centerOf_rconj]; exact hyZg
    have hI : L ⊔ uA V V₁ = uA V V₁ ⊔ rconj (uA V V₁) g :=
      (S.sup_rconj_uA_eq hg).symm
    have hyI : y ∈ L ⊔ uA V V₁ := Subgroup.mem_sup_right hyU
    refine ⟨hyI, Subgroup.mem_centralizer_iff.mpr fun i hi => ?_⟩
    have hK : L ⊔ uA V V₁ ≤ Subgroup.centralizer ({y} : Set G) := by
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
    have hzcomm : ∀ i ∈ L ⊔ uA V V₁, i * z = z * i := fun i hi =>
      Subgroup.mem_centralizer_iff.mp hzC i hi
    have hzS : z ∈ pCoreOf 2 (L ⊔ uA V V₁) := by
      rw [S.pCoreOf_sup_eq hg]
      refine ⟨hzI, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
      exact hzcomm v (Subgroup.mem_sup_right (le_uA V V₁ hv))
    obtain ⟨u₀, hu₀U, hu₀W⟩ : ∃ u₀ ∈ uA V V₁, u₀ ∉ wA V V₁ := by
      by_contra hall
      push Not at hall
      exact S.not_le_centralizer_V fun u hu => (hall u hu).2
    have hzE : z ∈ wA V V₁ ⊓ rconj (wA V V₁) g := by
      refine (S.module_relations hg hu₀U hu₀W).2.2.2 z hzS ?_
      have hgz : g * z * g⁻¹ = z := by
        have := hzcomm g (hg.mem_sup _)
        calc g * z * g⁻¹ = (g * z) * g⁻¹ := rfl
          _ = (z * g) * g⁻¹ := by rw [this]
          _ = z := by group
      rw [hgz, inv_mul_cancel]
      exact Subgroup.one_mem _
    rw [S.wA_inf_rconj_eq hg] at hzE
    obtain ⟨hzU, hzUg⟩ := hzE
    refine ⟨⟨hzU, Subgroup.mem_centralizer_iff.mpr fun u hu =>
      hzcomm u (Subgroup.mem_sup_right hu)⟩, ?_⟩
    rw [← centerOf_rconj]
    refine ⟨hzUg, Subgroup.mem_centralizer_iff.mpr fun u hu => hzcomm u ?_⟩
    rw [← S.sup_rconj_uA_eq hg]
    exact Subgroup.mem_sup_right hu

theorem omegaOneCenter_inf_centerOf_ne_bot (hN : centerOf (L ⊔ uA V V₁) ≠ ⊥) :
    quasithinOmegaOneCenter T ⊓ centerOf (L ⊔ uA V V₁) ≠ ⊥ := by
  have hNS : centerOf (L ⊔ uA V V₁) ≤ pCoreOf 2 (L ⊔ uA V V₁) := by
    intro z hz
    rw [S.pCoreOf_sup_eq hg]
    refine ⟨hz.1, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
    exact Subgroup.mem_centralizer_iff.mp hz.2 v (Subgroup.mem_sup_right (le_uA V V₁ hv))
  have hNT : centerOf (L ⊔ uA V V₁) ≤ T := hNS.trans (S.pCoreOf_sup_le_T hg)
  have hTnorm : T ≤ Subgroup.normalizer (centerOf (L ⊔ uA V V₁) : Set G) := fun t ht =>
    normalizer_le_normalizer_centerOf _
      (S.LT_le_normalizer_sup_uA (Subgroup.mem_sup_right ht))
  obtain ⟨z, hzN, hz1, hzT⟩ := exists_ne_one_mem_centralizer S.base.isPGroup_T hNT hTnorm hN
  obtain ⟨k, hk2, hk1⟩ := exists_pow_sq_eq_one_ne_one S.base.isPGroup_T (hNT hzN) hz1
  intro hbot
  apply hk1
  have hyN : z ^ k ∈ centerOf (L ⊔ uA V V₁) := Subgroup.pow_mem _ hzN k
  have hyZ : z ^ k ∈ quasithinOmegaOneCenter T := by
    refine Subgroup.subset_closure ⟨⟨hNT hyN, Subgroup.mem_centralizer_iff.mpr fun t ht => ?_⟩, hk2⟩
    exact Commute.pow_right (hzT t ht) k
  have : z ^ k ∈ quasithinOmegaOneCenter T ⊓ centerOf (L ⊔ uA V V₁) := ⟨hyZ, hyN⟩
  rw [hbot] at this
  exact Subgroup.mem_bot.mp this

theorem ten_three
    (hlt : V₁ < centerOf (uA V V₁) ⊓ rconj (uA V V₁) g) :
    quasithinOmegaOneCenter T ⊓ centerOf (L ⊔ uA V V₁) ≠ ⊥ := by
  refine S.omegaOneCenter_inf_centerOf_ne_bot hg ?_
  intro h0
  have h1 := S.ten_one hg
  rw [S.ten_two hg, h0, bot_sup_eq] at h1
  exact hlt.ne h1.symm

theorem commutator_wA_rconj_centerOf_le :
    ⁅wA V V₁, rconj (centerOf (uA V V₁)) g⁆ ≤
      rconj (centerOf (uA V V₁)) g ⊓ uA V V₁ := by
  rw [Subgroup.commutator_le]
  intro w hw z hz
  have hwN : w ∈ Subgroup.normalizer (rconj (centerOf (uA V V₁)) g : Set G) :=
    S.pCoreOf_sup_le_normalizer_rconj_centerOf hg (S.wA_le_pCoreOf hg hw)
  have hzX : z ∈ rconj (wA V V₁) g := rconj_centerOf_le_rconj_wA V V₁ g hz
  have hzN : z ∈ Subgroup.normalizer (uA V V₁ : Set G) :=
    S.T_le_normalizer_uA (S.rconj_wA_le_T hg hzX)
  have hwU : w ∈ uA V V₁ := wA_le_uA V V₁ hw
  refine ⟨?_, ?_⟩
  · have e : ⁅w, z⁆ = (w * z * w⁻¹) * z⁻¹ := by rw [commutatorElement_def]
    rw [e]
    exact (rconj (centerOf (uA V V₁)) g).mul_mem
      ((Subgroup.mem_normalizer_iff.mp hwN z).mp hz)
      ((rconj (centerOf (uA V V₁)) g).inv_mem hz)
  · have e : ⁅w, z⁆ = w * (z * w⁻¹ * z⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact (uA V V₁).mul_mem hwU
      ((Subgroup.mem_normalizer_iff.mp hzN _).mp ((uA V V₁).inv_mem hwU))

theorem ten_four :
    ⁅wA V V₁, rconj (centerOf (uA V V₁)) g⁆ ≤ centerOf (uA V V₁) ⊔ V := by
  refine (S.commutator_wA_rconj_centerOf_le hg).trans ?_
  rw [S.ten_one_symm hg]
  exact sup_le_sup inf_le_left ((S.l2Setting).V₁_le_rconj_V hg.mem)

theorem ten_five (hle : rconj (centerOf (uA V V₁)) g ≤ uA V V₁) :
    centerOf (uA V V₁) = centerOf (L ⊔ uA V V₁) ⊔ V₁ ∧
      Disjoint (centerOf (L ⊔ uA V V₁)) (V₁) ∧
      L ≤ Subgroup.centralizer (centerOf (L ⊔ uA V V₁) : Set G) := by
  have h1 := S.ten_one_symm hg
  rw [inf_eq_left.mpr hle, S.ten_two hg] at h1
  have hZI : rconj (centerOf (L ⊔ uA V V₁)) g⁻¹ = centerOf (L ⊔ uA V V₁) := by
    rw [← centerOf_rconj, rconj_eq_of_mem_normalizer]
    exact Subgroup.inv_mem _ (Subgroup.le_normalizer (hg.mem_sup _))
  refine ⟨?_, ?_, ?_⟩
  · have h2 := congrArg (fun K => rconj K g⁻¹) h1
    simp only [rconj_rconj_inv_eq, rconj_sup_eq, hZI] at h2
    exact h2
  · rw [disjoint_iff, eq_bot_iff]
    intro x hx
    have hxZg : x ∈ rconj (centerOf (uA V V₁)) g := by
      have := S.ten_two hg
      have hxI : x ∈ centerOf (uA V V₁) ⊓ rconj (centerOf (uA V V₁)) g := by
        rw [this]; exact hx.1
      exact hxI.2
    have : x ∈ V₁ ⊓ rconj (centerOf (uA V V₁)) g := ⟨hx.2, hxZg⟩
    rw [S.V₁_inf_rconj_centerOf hg] at this
    exact this
  · intro l hl
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (Subgroup.mem_centralizer_iff.mp hz.2 l (Subgroup.mem_sup_left hl)).symm

theorem ten_six
    (h84 : centralizerMod V₁ (Subgroup.normalizer (V₁ : Set G)) (uA V V₁) =
      pCoreOf 2 (Subgroup.normalizer (V₁ : Set G))) :
    centralizerMod (centerOf (uA V V₁)) (rconj (centerOf (uA V V₁)) g) (uA V V₁) =
        centralizerMod (V₁) (rconj (centerOf (uA V V₁)) g)
          (uA V V₁) ∧
      centralizerMod (V₁) (rconj (centerOf (uA V V₁)) g)
          (uA V V₁) =
        rconj (centerOf (uA V V₁)) g ⊓
          pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) ∧
      rconj (centerOf (uA V V₁)) g ⊓
          pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) =
        rconj (centerOf (uA V V₁)) g ⊓ uA V V₁ ∧
      rconj (centerOf (uA V V₁)) g ⊓ uA V V₁ =
        (centerOf (uA V V₁) ⊓ rconj (centerOf (uA V V₁)) g) ⊔
          rconj (V₁) g ∧
      (centerOf (uA V V₁) ⊓ rconj (centerOf (uA V V₁)) g) ⊔
          rconj (V₁) g =
        centerOf (L ⊔ uA V V₁) ⊔ rconj (V₁) g ∧
      centerOf (L ⊔ uA V V₁) ⊔ rconj (V₁) g ≤ uA V V₁ := by
  have hZZu : V₁ ≤ centerOf (uA V V₁) :=
    S.V₁_le_centerOf
  have hZgX : rconj (centerOf (uA V V₁)) g ≤ rconj (wA V V₁) g :=
    rconj_centerOf_le_rconj_wA V V₁ g
  have hXT : ∀ y ∈ rconj (centerOf (uA V V₁)) g, y ∈ T := fun y hy =>
    S.rconj_wA_le_T hg (hZgX hy)
  have hTN : ∀ y ∈ T, y ∈ Subgroup.normalizer (V₁ : Set G) := fun y hy =>
    S.base.T_le_normV₁ hy
  have h95 := S.nine_five hg
  have hA0 : centralizerMod (centerOf (uA V V₁)) (rconj (centerOf (uA V V₁)) g)
      (uA V V₁) = rconj (centerOf (uA V V₁)) g ⊓ uA V V₁ := by
    apply le_antisymm
    · intro y hy
      refine ⟨centralizerMod_le_left _ _ _ hy, ?_⟩
      have : y ∈ centralizerMod (centerOf (uA V V₁)) (rconj (wA V V₁) g) (uA V V₁) :=
        centralizerMod_mono_left _ hZgX hy
      rw [h95.1] at this
      exact wA_le_uA V V₁ this.1
    · rintro y ⟨hyZg, hyU⟩
      refine ⟨hyZg, S.rconj_wA_le_normalizer_centerOf hg (hZgX hyZg), fun u hu => ?_⟩
      exact hZZu (S.commutator_mem hyU hu)
  have hA1 : centralizerMod (V₁) (rconj (centerOf (uA V V₁)) g)
      (uA V V₁) = rconj (centerOf (uA V V₁)) g ⊓ uA V V₁ := by
    apply le_antisymm
    · intro y hy
      refine ⟨centralizerMod_le_left _ _ _ hy, ?_⟩
      have : y ∈ centralizerMod (V₁) (rconj (wA V V₁) g)
          (uA V V₁) := centralizerMod_mono_left _ hZgX hy
      rw [h95.2] at this
      exact wA_le_uA V V₁ this.1
    · rintro y ⟨hyZg, hyU⟩
      exact ⟨hyZg, hTN y (hXT y hyZg), fun u hu => S.commutator_mem hyU hu⟩
  have hA2 : rconj (centerOf (uA V V₁)) g ⊓
      pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) =
        rconj (centerOf (uA V V₁)) g ⊓ uA V V₁ := by
    rw [← h84]
    apply le_antisymm
    · rintro y ⟨hyZg, hy⟩
      have : y ∈ centralizerMod (V₁) (rconj (centerOf (uA V V₁)) g)
          (uA V V₁) := ⟨hyZg, hy.2.1, hy.2.2⟩
      rw [hA1] at this
      exact this
    · rintro y ⟨hyZg, hyU⟩
      refine ⟨hyZg, ?_, hTN y (hXT y hyZg), fun u hu => S.commutator_mem hyU hu⟩
      exact S.base.T_le_H (hXT y hyZg)
  refine ⟨hA0.trans hA1.symm, hA1.trans hA2.symm, hA2, S.ten_one_symm hg, ?_, ?_⟩
  · rw [S.ten_two hg]
  · refine sup_le ?_ ?_
    · rw [← S.ten_two hg]
      exact fun c hc => hc.1.1
    · exact ((S.l2Setting).V₁_le_rconj_V hg.mem).trans (le_uA V V₁)

end


end Setting

end L128A

end CFSG.Quasithin.H13
