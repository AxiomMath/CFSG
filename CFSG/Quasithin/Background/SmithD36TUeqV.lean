module

public import CFSG.Quasithin.Background.SmithD36TFaith

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W}

section Irr

omit [Finite W] in
theorem le_stabSub_of_inv_d36t {L : Subgroup (MulAut W)} {J : Subgroup W}
    (h : ∀ l ∈ L, ∀ w ∈ J, l w ∈ J) : L ≤ stabSub J := by
  intro l hl u
  refine ⟨fun hu => ?_, fun hu => h l hl u hu⟩
  have := h l⁻¹ (L.inv_mem hl) _ hu
  simpa using this

theorem d36t_fixV_Mp (n : D36Norm M Mp T L V t) : V ⊓ fixV Mp = V ⊓ fixV L := by
  apply le_antisymm
  · exact fun v hv => ⟨hv.1, fun l hl => hv.2 l (d36t_L_le_Mp n hl)⟩
  · intro v hv
    refine ⟨hv.1, ?_⟩
    rw [n.Mp_eq, fixV_sup_eq_inf_fixV]
    exact ⟨hv.2, fun g hg => n.triv v hv.1 g hg⟩

theorem d36t_irr_V (n : D36Norm M Mp T L V t) :
    ∀ J : Subgroup W, (∀ l ∈ L, ∀ w ∈ J, l w ∈ J) → V ⊓ fixV L ≤ J → J ≤ V →
      J = V ⊓ fixV L ∨ J = V := by
  intro J hJ hlo hhi
  obtain ⟨-, -, -, hirr⟩ := mem_irrPlus_top_iff.mp n.std.hyp.irr
  have hMpJ : Mp ≤ stabSub J := by
    rw [n.Mp_eq]
    refine sup_le (le_stabSub_of_inv_d36t hJ) (le_stabSub_of_inv_d36t fun g hg w hw => ?_)
    rw [n.triv w (hhi hw) g hg]
    exact hw
  have := hirr J (fun g hg w hw => ((hMpJ hg) w).mpr hw) (by rw [d36t_fixV_Mp n]; exact hlo) hhi
  rwa [d36t_fixV_Mp n] at this

omit [Finite W] in
theorem d36t_irr_map {L : Subgroup (MulAut W)} {V : Subgroup W} {s : MulAut W}
    (hsN : s ∈ Subgroup.normalizer (L : Set (MulAut W)))
    (hirr : ∀ J : Subgroup W, (∀ l ∈ L, ∀ w ∈ J, l w ∈ J) → V ⊓ fixV L ≤ J → J ≤ V →
      J = V ⊓ fixV L ∨ J = V) :
    ∀ J : Subgroup W, (∀ l ∈ L, ∀ w ∈ J, l w ∈ J) → V.map s.toMonoidHom ⊓ fixV L ≤ J →
      J ≤ V.map s.toMonoidHom → J = V.map s.toMonoidHom ⊓ fixV L ∨ J = V.map s.toMonoidHom := by
  intro J hJ hlo hhi
  have hfix : ∀ v ∈ fixV L, s v ∈ fixV L := by
    intro v hv l hl
    have h1 : s⁻¹ * l * s ∈ L := (Subgroup.mem_normalizer_iff''.mp hsN l).mp hl
    have h2 := hv _ h1
    calc l (s v) = s ((s⁻¹ * l * s) v) := by simp [MulAut.mul_apply]
      _ = s v := by rw [h2]
  have hfix' : ∀ v, s v ∈ fixV L → v ∈ fixV L := by
    intro v hv l hl
    have h1 : s * l * s⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hsN l).mp hl
    have h2 := hv _ h1
    have : s (l v) = s v := by simpa [MulAut.mul_apply] using h2
    exact s.injective this
  let J' : Subgroup W := J.comap s.toMonoidHom
  have hJ' : ∀ l ∈ L, ∀ w ∈ J', l w ∈ J' := by
    intro l hl w hw
    have h1 : s * l * s⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hsN l).mp hl
    have h2 := hJ _ h1 _ (show s w ∈ J from hw)
    show s (l w) ∈ J
    simpa [MulAut.mul_apply] using h2
  have hlo' : V ⊓ fixV L ≤ J' := fun v hv => hlo ⟨⟨v, hv.1, rfl⟩, hfix v hv.2⟩
  have hhi' : J' ≤ V := by
    intro w hw
    obtain ⟨v, hv, hvw⟩ := hhi (show s w ∈ J from hw)
    have : v = w := s.injective hvw
    exact this ▸ hv
  rcases hirr J' hJ' hlo' hhi' with h | h
  · left
    refine le_antisymm (fun w hw => ⟨hhi hw, ?_⟩) hlo
    obtain ⟨v, hv, rfl⟩ := hhi hw
    have hvJ : v ∈ J' := show s v ∈ J from hw
    rw [h] at hvJ
    exact hfix v hvJ.2
  · right
    refine le_antisymm hhi ?_
    rintro _ ⟨v, hv, rfl⟩
    have hvJ : v ∈ J' := h ▸ hv
    exact hvJ

theorem d36t_Vs_le_U (hL38 : D3L38) (n : D36Norm M Mp T L V t) {s : MulAut W} (hs : s ∈ T)
    (hsN : s ∈ Subgroup.normalizer (L : Set (MulAut W))) :
    V.map s.toMonoidHom ≤ commSub (orbSup T V) L := by
  rw [d36_U_eq hL38 n]
  exact map_le_orbSup ⟨hs, hsN⟩

theorem d36t_irr_J (hL38 : D3L38) (n : D36Norm M Mp T L V t) {s : MulAut W} (hs : s ∈ T)
    (hsN : s ∈ Subgroup.normalizer (L : Set (MulAut W))) :
    ∀ J : Subgroup W, (∀ l ∈ L, ∀ w ∈ J, l w ∈ J) → commSub (orbSup T V) L ⊓ fixV L ≤ J →
      J ≤ V.map s.toMonoidHom ⊔ (commSub (orbSup T V) L ⊓ fixV L) →
      J = commSub (orbSup T V) L ⊓ fixV L ∨
        J = V.map s.toMonoidHom ⊔ (commSub (orbSup T V) L ⊓ fixV L) := by
  intro J hJ hlo hhi
  have hVsU := d36t_Vs_le_U hL38 n hs hsN
  have hinvVs := d36t_L_inv_Vs n hsN
  have hirr := d36t_irr_map hsN (d36t_irr_V n)
  have hJV : ∀ l ∈ L, ∀ w ∈ J ⊓ V.map s.toMonoidHom, l w ∈ J ⊓ V.map s.toMonoidHom :=
    fun l hl w hw => ⟨hJ l hl w hw.1, hinvVs l hl w hw.2⟩
  have hlo' : V.map s.toMonoidHom ⊓ fixV L ≤ J ⊓ V.map s.toMonoidHom :=
    fun w hw => ⟨hlo ⟨hVsU hw.1, hw.2⟩, hw.1⟩
  rcases hirr _ hJV hlo' inf_le_right with h | h
  · left
    refine le_antisymm (fun j hj => ?_) hlo
    obtain ⟨w, hw, z, hz, rfl⟩ := Subgroup.mem_sup.mp (hhi hj)
    have hwJ : w ∈ J := by
      have := J.mul_mem hj (J.inv_mem (hlo hz))
      rwa [mul_inv_cancel_right] at this
    have hw' : w ∈ V.map s.toMonoidHom ⊓ fixV L := h ▸ ⟨hwJ, hw⟩
    exact (commSub (orbSup T V) L ⊓ fixV L).mul_mem ⟨hVsU hw, hw'.2⟩ hz
  · right
    refine le_antisymm hhi (sup_le (fun w hw => ?_) hlo)
    have : w ∈ J ⊓ V.map s.toMonoidHom := by rw [h]; exact hw
    exact this.1

theorem d36t_exists_three (n : D36Norm M Mp T L V t) {s : MulAut W}
    (hsN : s ∈ Subgroup.normalizer (L : Set (MulAut W))) :
    ∃ w₁ ∈ V.map s.toMonoidHom, ∃ w₂ ∈ V.map s.toMonoidHom,
      w₁ ∉ fixV L ∧ w₂ ∉ fixV L ∧ w₁ * w₂ ∉ fixV L := by
  have hinv := d36t_L_inv_Vs n hsN
  have hperf : Group.IsPerfect ↥L := n.std.hyp.quasi.1
  obtain ⟨w₁, hw₁, hw₁f⟩ : ∃ w₁ ∈ V.map s.toMonoidHom, w₁ ∉ fixV L := by
    by_contra h
    push Not at h
    exact d36t_Vs_not_le_fixV n hsN h
  by_contra hcon
  push Not at hcon
  have hall : ∀ w ∈ V.map s.toMonoidHom, w ∉ fixV L → w₁ * w ∈ fixV L :=
    fun w hw hwf => hcon w₁ hw₁ w hw hw₁f hwf
  have hout : ∀ l ∈ L, ∀ w, l w ∈ fixV L → w ∈ fixV L := by
    intro l hl w hw k hk
    have h1 := hw (k * l⁻¹) (L.mul_mem hk (L.inv_mem hl))
    have h2 := hw l⁻¹ (L.inv_mem hl)
    simp only [MulAut.mul_apply, MulAut.inv_apply_self] at h1 h2
    rw [h1, ← h2]
  have hcomm : ∀ l ∈ L, ∀ w ∈ V.map s.toMonoidHom, l w * w⁻¹ ∈ fixV L := by
    intro l hl w hw
    by_cases hwf : w ∈ fixV L
    · rw [hwf l hl, mul_inv_cancel]
      exact (fixV L).one_mem
    · have hlw : l w ∉ fixV L := fun h => hwf (hout l hl w h)
      have h1 := hall w hw hwf
      have h2 := hall (l w) (hinv l hl w hw) hlw
      have e : l w * w⁻¹ = (w₁ * l w) * (w₁ * w)⁻¹ := by
        rw [mul_comm w₁ (l w), mul_comm w₁ w]
        group
      rw [e]
      exact (fixV L).mul_mem h2 ((fixV L).inv_mem h1)
  apply hw₁f
  intro l hl
  exact fix_of_comm_le_fixV hperf hcomm l hl w₁ hw₁

end Irr

section Main

omit [Finite W] in
theorem comm_mul_d36t (x : MulAut W) (u v : W) :
    x (u * v) * (u * v)⁻¹ = (x u * u⁻¹) * (x v * v⁻¹) := by
  rw [map_mul, mul_inv_rev, mul_comm v⁻¹ u⁻¹]
  exact mul_mul_mul_comm _ _ _ _

theorem d36t_stab_J (hL38 : D3L38) (n : D36Norm M Mp T L V t) {x : MulAut W}
    (hxU : x ∈ stabSub (commSub (orbSup T V) L))
    (hxN : x ∈ Subgroup.normalizer (L : Set (MulAut W)))
    (hF5 : ∀ u ∈ commSub (orbSup T V) L, ∀ u' ∈ commSub (orbSup T V) L,
      x u * u⁻¹ ∈ fixV L ∨ x u' * u'⁻¹ ∈ fixV L ∨ x (u * u') * (u * u')⁻¹ ∈ fixV L)
    {s : MulAut W} (hs : s ∈ T) (hsN : s ∈ Subgroup.normalizer (L : Set (MulAut W))) :
    x ∈ stabSub (V.map s.toMonoidHom ⊔ (commSub (orbSup T V) L ⊓ fixV L)) := by
  set Z₀ := commSub (orbSup T V) L ⊓ fixV L with hZ₀
  set J := V.map s.toMonoidHom ⊔ Z₀ with hJ
  have hVsU := d36t_Vs_le_U hL38 n hs hsN
  have hinvVs := d36t_L_inv_Vs n hsN
  have hfixx : ∀ y ∈ Subgroup.normalizer (L : Set (MulAut W)), ∀ v ∈ fixV L, y v ∈ fixV L := by
    intro y hy v hv l hl
    have h1 : y⁻¹ * l * y ∈ L := (Subgroup.mem_normalizer_iff''.mp hy l).mp hl
    have h2 := hv _ h1
    calc l (y v) = y ((y⁻¹ * l * y) v) := by simp [MulAut.mul_apply]
      _ = y v := by rw [h2]
  have hxZ : ∀ z ∈ Z₀, x z ∈ Z₀ := fun z hz => ⟨(hxU z).mpr hz.1, hfixx x hxN z hz.2⟩
  have hxZ' : ∀ z ∈ Z₀, x⁻¹ z ∈ Z₀ := fun z hz =>
    ⟨((stabSub _).inv_mem hxU z).mpr hz.1, hfixx x⁻¹ (inv_mem hxN) z hz.2⟩
  have hJinv : ∀ l ∈ L, ∀ w ∈ J, l w ∈ J := by
    intro l hl w hw
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hw
    rw [map_mul, hb.2 l hl]
    exact Subgroup.mul_mem_sup (hinvVs l hl a ha) hb
  have hxJinv : ∀ l ∈ L, ∀ w ∈ J.map x.toMonoidHom, l w ∈ J.map x.toMonoidHom := by
    rintro l hl _ ⟨w, hw, rfl⟩
    have h1 : x⁻¹ * l * x ∈ L := (Subgroup.mem_normalizer_iff''.mp hxN l).mp hl
    refine ⟨(x⁻¹ * l * x) w, hJinv _ h1 w hw, ?_⟩
    simp [MulAut.mul_apply]
  have hZJ : Z₀ ≤ J := le_sup_right
  have hZxJ : Z₀ ≤ J.map x.toMonoidHom := fun z hz => ⟨x⁻¹ z, hZJ (hxZ' z hz), by simp⟩
  rcases d36t_irr_J hL38 n hs hsN (J ⊓ J.map x.toMonoidHom)
      (fun l hl w hw => ⟨hJinv l hl w hw.1, hxJinv l hl w hw.2⟩) (le_inf hZJ hZxJ) inf_le_left
    with h | h
  · exfalso
    have key : ∀ w ∈ V.map s.toMonoidHom, x w * w⁻¹ ∈ fixV L → w ∈ fixV L := by
      intro w hw hxw
      have hwU := hVsU hw
      have hd : x w * w⁻¹ ∈ Z₀ := ⟨(commSub (orbSup T V) L).mul_mem ((hxU w).mpr hwU)
        ((commSub (orbSup T V) L).inv_mem hwU), hxw⟩
      have hx1 : x⁻¹ w * w⁻¹ ∈ Z₀ := by
        have e : x⁻¹ w * w⁻¹ = x⁻¹ ((x w * w⁻¹)⁻¹) := by simp
        rw [e]
        exact hxZ' _ (Z₀.inv_mem hd)
      have hwx : w ∈ J.map x.toMonoidHom := by
        refine ⟨x⁻¹ w, ?_, by simp⟩
        have e : x⁻¹ w = w * (x⁻¹ w * w⁻¹) := by
          rw [mul_comm (x⁻¹ w) w⁻¹, mul_inv_cancel_left]
        rw [e]
        exact Subgroup.mul_mem_sup hw hx1
      have hmem : w ∈ J ⊓ J.map x.toMonoidHom := ⟨Subgroup.mem_sup_left hw, hwx⟩
      rw [h] at hmem
      exact hmem.2
    obtain ⟨w₁, hw₁, w₂, hw₂, h1, h2, h3⟩ := d36t_exists_three n hsN
    rcases hF5 w₁ (hVsU hw₁) w₂ (hVsU hw₂) with h' | h' | h'
    · exact h1 (key w₁ hw₁ h')
    · exact h2 (key w₂ hw₂ h')
    · exact h3 (key _ ((V.map s.toMonoidHom).mul_mem hw₁ hw₂) h')
  ·
    have hle : J ≤ J.map x.toMonoidHom := by
      intro w hw
      have : w ∈ J ⊓ J.map x.toMonoidHom := h ▸ hw
      exact this.2
    have heq : J.map x.toMonoidHom = J := by
      refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
      rw [Subgroup.card_map_of_injective x.injective]
    exact mem_stabSub_iff_map_eq.mpr heq

theorem d36t_commSub_V (hL38 : D3L38) (n : D36Norm M Mp T L V t) : commSub V L = V := by
  obtain ⟨hinv, hcomm, -, -⟩ := mem_irrPlus_top_iff.mp n.std.hyp.irr
  refine le_antisymm (commSub_le_of_invariant fun l hl w hw => hinv l (d36t_L_le_Mp n hl) w hw) ?_
  conv_lhs => rw [← hcomm]
  rw [commSub, Subgroup.closure_le]
  rintro _ ⟨m, hm, v, hv, rfl⟩
  have hLtN : conjAutSub t L ≤ Subgroup.normalizer (L : Set (MulAut W)) :=
    (d36t_Lt_le_centralizer hL38 n).trans (Subgroup.centralizer_le_normalizer _)
  have hm' : m ∈ ((L ⊔ conjAutSub t L : Subgroup (MulAut W)) : Set (MulAut W)) := by
    rw [← n.Mp_eq]
    exact hm
  rw [Subgroup.coe_mul_of_right_le_normalizer_left L (conjAutSub t L) hLtN] at hm'
  obtain ⟨l, hl, l', hl', rfl⟩ := hm'
  show l (l' v) * v⁻¹ ∈ commSub V L
  rw [n.triv v hv l' hl']
  exact Subgroup.subset_closure ⟨l, hl, v, hv, rfl⟩

theorem d36t_commSub_Vs (hL38 : D3L38) (n : D36Norm M Mp T L V t) {s : MulAut W}
    (hsN : s ∈ Subgroup.normalizer (L : Set (MulAut W))) :
    commSub (V.map s.toMonoidHom) L = V.map s.toMonoidHom := by
  have h := commSub_conjBy s V L
  have hs : conjBy s L = L := Subgroup.mem_normalizer_iff_map_conj_eq.mp hsN
  rw [hs, d36t_commSub_V hL38 n] at h
  exact h

theorem d36t_Vs_le (hL38 : D3L38) (n : D36Norm M Mp T L V t) {x : MulAut W}
    (hxU : x ∈ stabSub (commSub (orbSup T V) L))
    (hxN : x ∈ Subgroup.normalizer (L : Set (MulAut W)))
    (hF5 : ∀ u ∈ commSub (orbSup T V) L, ∀ u' ∈ commSub (orbSup T V) L,
      x u * u⁻¹ ∈ fixV L ∨ x u' * u'⁻¹ ∈ fixV L ∨ x (u * u') * (u * u')⁻¹ ∈ fixV L)
    (hF6 : ∀ s ∈ T, s ∈ Subgroup.normalizer (L : Set (MulAut W)) →
      ¬ ∀ w ∈ V.map s.toMonoidHom, x w * w⁻¹ ∈ fixV L)
    {s : MulAut W} (hs : s ∈ T) (hsN : s ∈ Subgroup.normalizer (L : Set (MulAut W))) :
    V.map s.toMonoidHom ≤ V ⊔ (commSub (orbSup T V) L ⊓ fixV L) := by
  set Z₀ := commSub (orbSup T V) L ⊓ fixV L with hZ₀
  have hV1 : V.map (1 : MulAut W).toMonoidHom = V := by
    ext v
    simp
  have h1T : (1 : MulAut W) ∈ T := T.one_mem
  have h1N : (1 : MulAut W) ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
    Subgroup.one_mem _
  have hstab1 := d36t_stab_J hL38 n hxU hxN hF5 h1T h1N
  have hstabs := d36t_stab_J hL38 n hxU hxN hF5 hs hsN
  rw [hV1] at hstab1
  have hirr1 := d36t_irr_J hL38 n h1T h1N
  rw [hV1, ← hZ₀] at hirr1
  have hirrs := d36t_irr_J hL38 n hs hsN
  rw [← hZ₀] at hirrs
  have hVsU := d36t_Vs_le_U hL38 n hs hsN
  have hVU := d36_V_le_U hL38 n
  have hinvJ : ∀ (Y : Subgroup W), (∀ l ∈ L, ∀ w ∈ Y, l w ∈ Y) →
      ∀ l ∈ L, ∀ w ∈ Y ⊔ Z₀, l w ∈ Y ⊔ Z₀ := by
    intro Y hY l hl w hw
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hw
    rw [map_mul, hb.2 l hl]
    exact Subgroup.mul_mem_sup (hY l hl a ha) hb
  have hinvV : ∀ l ∈ L, ∀ w ∈ V, l w ∈ V := fun l hl w hw => d36t_inv_V n (d36t_L_le_Mp n hl) hw
  have hinvVs := d36t_L_inv_Vs n hsN
  by_contra hcon
  have hcap : (V.map s.toMonoidHom ⊔ Z₀) ⊓ (V ⊔ Z₀) = Z₀ := by
    rcases hirrs ((V.map s.toMonoidHom ⊔ Z₀) ⊓ (V ⊔ Z₀))
        (fun l hl w hw => ⟨hinvJ _ hinvVs l hl w hw.1, hinvJ _ hinvV l hl w hw.2⟩)
        (le_inf le_sup_right le_sup_right) inf_le_left with h | h
    · exact h
    · exfalso
      have hle : V.map s.toMonoidHom ⊔ Z₀ ≤ V ⊔ Z₀ := by
        rw [← h]
        exact inf_le_right
      rcases hirr1 _ (hinvJ _ hinvVs) le_sup_right hle with h' | h'
      · apply d36t_Vs_not_le_fixV n hsN
        intro w hw
        have : w ∈ Z₀ := h' ▸ Subgroup.mem_sup_left hw
        exact this.2
      · exact hcon (h' ▸ le_sup_left)
  obtain ⟨v, hv, hvx⟩ : ∃ v ∈ V, x v * v⁻¹ ∉ fixV L := by
    by_contra h
    push Not at h
    exact hF6 1 h1T h1N (by rw [hV1]; exact h)
  obtain ⟨w, hw, hwx⟩ : ∃ w ∈ V.map s.toMonoidHom, x w * w⁻¹ ∉ fixV L := by
    by_contra h
    push Not at h
    exact hF6 s hs hsN h
  have hδv : x v * v⁻¹ ∈ V ⊔ Z₀ := by
    have hv' : v ∈ V ⊔ Z₀ := Subgroup.mem_sup_left hv
    exact (V ⊔ Z₀).mul_mem ((hstab1 v).mpr hv') ((V ⊔ Z₀).inv_mem hv')
  have hδw : x w * w⁻¹ ∈ V.map s.toMonoidHom ⊔ Z₀ := by
    have hw' : w ∈ V.map s.toMonoidHom ⊔ Z₀ := Subgroup.mem_sup_left hw
    exact (V.map s.toMonoidHom ⊔ Z₀).mul_mem ((hstabs w).mpr hw')
      ((V.map s.toMonoidHom ⊔ Z₀).inv_mem hw')
  rcases hF5 v (hVU hv) w (hVsU hw) with h | h | h
  · exact hvx h
  · exact hwx h
  · rw [comm_mul_d36t] at h
    have hvwU : x (v * w) * (v * w)⁻¹ ∈ commSub (orbSup T V) L := by
      have hu := (commSub (orbSup T V) L).mul_mem (hVU hv) (hVsU hw)
      exact (commSub (orbSup T V) L).mul_mem ((hxU _).mpr hu)
        ((commSub (orbSup T V) L).inv_mem hu)
    rw [comm_mul_d36t] at hvwU
    have hZ : (x v * v⁻¹) * (x w * w⁻¹) ∈ Z₀ := ⟨hvwU, h⟩
    have hδv' : x v * v⁻¹ ∈ V.map s.toMonoidHom ⊔ Z₀ := by
      have e : x v * v⁻¹ = ((x v * v⁻¹) * (x w * w⁻¹)) * (x w * w⁻¹)⁻¹ := by group
      rw [e]
      exact (V.map s.toMonoidHom ⊔ Z₀).mul_mem (Subgroup.mem_sup_right hZ)
        ((V.map s.toMonoidHom ⊔ Z₀).inv_mem hδw)
    have : x v * v⁻¹ ∈ Z₀ := hcap ▸ ⟨hδv', hδv⟩
    exact hvx this.2

theorem d36t_U_eq_V (hL38 : D3L38) (n : D36Norm M Mp T L V t) {x : MulAut W}
    (hxU : x ∈ stabSub (commSub (orbSup T V) L))
    (hxN : x ∈ Subgroup.normalizer (L : Set (MulAut W)))
    (hF5 : ∀ u ∈ commSub (orbSup T V) L, ∀ u' ∈ commSub (orbSup T V) L,
      x u * u⁻¹ ∈ fixV L ∨ x u' * u'⁻¹ ∈ fixV L ∨ x (u * u') * (u * u')⁻¹ ∈ fixV L)
    (hF6 : ∀ s ∈ T, s ∈ Subgroup.normalizer (L : Set (MulAut W)) →
      ¬ ∀ w ∈ V.map s.toMonoidHom, x w * w⁻¹ ∈ fixV L) :
    commSub (orbSup T V) L = V := by
  refine le_antisymm ?_ (d36_V_le_U hL38 n)
  rw [d36_U_eq hL38 n]
  refine orbSup_le fun s hs => ?_
  have hle := d36t_Vs_le hL38 n hxU hxN hF5 hF6 hs.1 hs.2
  rw [← d36t_commSub_Vs hL38 n hs.2]
  refine (commSub_mono hle le_rfl).trans ?_
  rw [commSub, Subgroup.closure_le]
  rintro _ ⟨l, hl, w, hw, rfl⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hw
  have e : l (a * b) * (a * b)⁻¹ = l a * a⁻¹ := by
    rw [map_mul, hb.2 l hl]
    group
  rw [e]
  exact V.mul_mem (d36t_inv_V n (d36t_L_le_Mp n hl) ha) (V.inv_mem ha)

end Main

end CFSG.Quasithin
