module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43Even17F
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43Even17G
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43Even17A
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43Even17C

public section

namespace CFSG.Quasithin.F53.Stellmacher.S43.Even

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod CosetGeom
open CFSG.LieType.BorelTits
open E17 E17.Sit43'

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem claim17 (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) {α : Geo H M}
    (hs : Sit43 α) (he : Even (bMin H M)) (hb : 4 ≤ bMin H M)
    (h14 : ∀ {γ : Geo H M}, Sit43 γ → Claim14 γ) (h15 : ∀ {γ : Geo H M}, Sit43 γ → Claim15 γ)
    (h16 : 6 ≤ bMin H M → Claim17 α) : Claim17 α := by
  by_cases h6 : 6 ≤ bMin H M
  · exact h16 h6
  have hb4 : bMin H M = 4 := by
    obtain ⟨k, hk⟩ := he
    omega
  by_contra hno
  have hno' : ∀ y ∈ stab α, y ∉ Qv α → ¬ IsTransvec 1 y (Zv α) (Wn α) :=
    fun y hy hyQ hT => hno ⟨y, hy, hyQ, hT⟩
  obtain ⟨α', hc⟩ := hs.exists_crit_partner hA
  have hα'v := hs.vtype_crit hA he hc
  obtain ⟨β, α₂, α₃, hβ, h2, h3, h', d2, d3, dβ, d2'⟩ :=
    exists_geodesic hA (by rw [hc.2, hb4])
  obtain ⟨x, hx, hxQ, hxT, hxH⟩ := exists_x hA h26 hs he hb4 (h15 hs) hc hβ h' d3 dβ
  have hxα : x ∈ stab α := hs.Zv_le_stab_crit' hA he hc hx
  have hxQβ : x ∈ Qst β := Zv_le_Qst hA hs hb4 h2 hα'v (by rw [CosetGeom.dist_comm]; exact dβ)
    (by rw [CosetGeom.dist_comm]; exact d2') hx
  have hx2 : x * x = 1 := by
    have := (isElemAbelian_Zv hA α').2 x hx
    rwa [pow_two] at this
  obtain ⟨δ, hδ, hYY, hxM, hTD⟩ := exists_delta hA h26 hs hβ hxα hxQβ hxT
  have hV2 := Vn_le_Qv₂ hA h26 hs hb4 hβ h2 d2 hδ hYY
  have h2v : vtype α₂ = false := hs.vtype_of_dist_two hA (by rw [CosetGeom.dist_comm]; exact d2)
  have hK2 := relIndex_Vn_le_two hA h2v h3 h' hV2
  have htwo := two_classes hA h26 hs hδ (by omega) hxH hK2
  obtain ⟨E, F, hE, hF, hZE, hEF, hFW, hR, hD4, -, hcase⟩ :=
    step5 hA h26 hs hb4 hδ hxα hxM htwo
  rcases hcase with ⟨horth, rfl⟩ | ⟨hnat, hFW2, -⟩
  ·
    exact hno' x hxα hxQ (case1_transvec hA h26 hs hb4 (h14 hs) hc h3 h' d2 d3 hδ hxα hx2 hxT
      hxM hxH htwo hE hZE hEF.le hR hD4 horth)
  ·
    have hw := exists_three hA h26 hs hβ h2 (by rw [CosetGeom.dist_comm]; exact d2') hx hxα hxQβ
      hxT
    exact case2_false hA h26 hs hb4 hβ h2 d2 hδ hTD hV2 hw hE hF hZE hFW hR hD4 hnat hFW2

end CFSG.Quasithin.F53.Stellmacher.S43.Even
