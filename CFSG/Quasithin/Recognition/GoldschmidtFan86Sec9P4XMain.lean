module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9Ex
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4XGood
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4XTrans
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4XBeta
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4XCol
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4XComm
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4XStar

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P4X

theorem secCfgExists_of_shape (F : FanTree Γ G) (L : ZLab Γ G) (h7 : Fan7 F L) (h65 : Fan65 F)
    (h81 : Fan81 F L) (h84a : Fan84a F L)
    (hN1 : ∀ (A : V) (D' : D10Set L A) (δ'' : V), D'.IsYPair δ'' → FixedPair D') :
    SecCfgExists F L := by
  intro α β hα hαβ
  have h71a : Fan71a F L := h7.1
  have h71c : Fan71c F L := h7.2.2.1
  have hdeg : ∀ u v, Γ.Adj u v → ∃ w, Γ.Adj u w ∧ w ≠ v := fun u v _ => F.exists_adj_ne u v
  obtain ⟨b, hαb, hbβ⟩ := F.exists_adj_ne α β
  obtain ⟨P0, hP00, hP01⟩ := exists_arc_start hdeg hαb 3
  obtain ⟨Q20, hQ200, hQ201⟩ := exists_arc_start hdeg hαβ 3
  have hne0 : P0.vert 1 ≠ Q20.vert 1 := by rw [hP01, hQ201]; exact hbβ
  obtain ⟨D₀, hD00, hD02⟩ := exists_d10Set_arcs h71a h71c hα P0 Q20 hP00 hQ200 hne0
  obtain ⟨w₀, hw₀⟩ := exists_w1star F L h7 h65 h84a α D₀
  obtain ⟨η', hY, hη⟩ := exists_good_partner F h7 hN1 D₀ hw₀.1
  have hξ : D₀.beta 0 ≠ β := by
    show (D₀.P 0).vert 1 ≠ β
    rw [hD00 1 (by norm_num), hP01]
    exact hbβ
  obtain ⟨ht2, htα, htβ, htA⟩ := t_facts h71c h81 hα hαβ hY hξ
  have hβ3 : valence Γ β = 3 := valence_adj_three F hα hαβ
  obtain ⟨A, hβA, hAα⟩ := F.exists_adj_ne β α
  obtain ⟨x, hxβ, hx3, htx, hxα⟩ :=
    exists_xbeta_of_t F hβ3 hαβ hβA hAα ht2 htα htβ (htA A hβA hAα)
  obtain ⟨Q2, hQ20, hQ21, hQ22, hQ23, hQ24⟩ := exists_arc_through F hαβ (D₀.adj_start_beta 0)
    (D₀.adj_beta_alpha 0) (D₀.alpha_ne_start 0).symm hξ hxβ hxα
  have hneQ : P0.vert 1 ≠ Q2.vert 1 := by rw [hP01, hQ21]; exact hbβ
  obtain ⟨D, hD0, hD2⟩ := exists_d10Set_arcs h71a h71c hα P0 Q2 hP00 hQ20 hneQ
  have hDP : ∀ m, m ≤ 4 → (D.P 0).vert m = (D₀.P 0).vert m := fun m hm => by
    rw [hD0 m hm, hD00 m hm]
  have hβ2 : D.beta 2 = β := by
    show (D.P 2).vert 1 = β
    rw [hD2 1 (by norm_num), hQ21]
  have hYD : D.IsYPair η' := by
    have e1 : D.alpha 0 = D₀.alpha 0 := hDP 2 (by norm_num)
    have e2 : D.beta 0 = D₀.beta 0 := hDP 1 (by norm_num)
    have e3 : D.delta 0 = D₀.delta 0 := hDP 4 (by norm_num)
    show IsZ2Pair Γ G α (D.alpha 0) (D.beta 0) (D.delta 0) η' 2
    rw [e1, e2, e3]
    exact hY
  have hy0 : D.y η' 0 = L.z (D₀.delta 0) * L.z η' := by
    have e3 : D.delta 0 = D₀.delta 0 := hDP 4 (by norm_num)
    show (D.x ^ ((0 : Fin 5) : ℕ))⁻¹ * (L.z (D.delta 0) * L.z η') * D.x ^ ((0 : Fin 5) : ℕ) = _
    rw [e3]
    simp
  have hinv : (D.y η' 0)⁻¹ * x * D.y η' 0 = x⁻¹ := by
    have htinv : (L.z (D₀.delta 0) * L.z η')⁻¹ = L.z (D₀.delta 0) * L.z η' :=
      inv_eq_of_mul_eq_one_right ht2
    rw [hy0, htinv]
    exact htx
  have hc : ∀ m, m ≤ 2 → (D.P 2).vert (m + 2) = x • (D.P 0).vert m := by
    intro m hm
    rw [hD2 (m + 2) (by omega), hD0 m (by omega)]
    have h1 : P0.vert 1 = D₀.beta 0 := (hD00 1 (by norm_num)).symm
    have h2 : P0.vert 2 = D₀.alpha 0 := (hD00 2 (by norm_num)).symm
    interval_cases m
    · rw [hP00]; exact hQ22
    · rw [h1]; exact hQ23
    · rw [h2]; exact hQ24
  have hbeta : IsBetaSet D x η' :=
    isBetaSet_of_collar D (by rw [hβ2]; exact hxβ) hx3 hYD hinv hc
  obtain ⟨g, hg0, hg2⟩ := exists_stab_pair h71a h71c h65 hα P0 Q20 P0 Q2 hP00 hQ200 hP00 hQ20
    hne0 hneQ
  have hgα : g • α = α := by
    have := hg0 0 (by norm_num)
    rwa [hP00] at this
  have hcompat : Compat D₀ D g :=
    ⟨fun m hm => by rw [hD00 m hm, hD0 m hm]; exact hg0 m hm,
      fun m hm => by rw [hD02 m hm, hD2 m hm]; exact hg2 m hm⟩
  obtain ⟨c, hcgen⟩ : ∃ c : G, D.calpha = Subgroup.zpowers c := by
    have := (h84a α D).1
    obtain ⟨⟨c, hc⟩, hgen⟩ := IsCyclic.exists_generator (α := ↥D.calpha)
    refine ⟨c, le_antisymm (fun y hy => ?_) ((Subgroup.zpowers_le).2 hc)⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hgen ⟨y, hy⟩)
    exact Subgroup.mem_zpowers_iff.2 ⟨k, by simpa using congrArg Subtype.val hk⟩
  exact ⟨⟨α, D, x, η', g * w₀ * g⁻¹, c, hbeta, isW1_conj F hgα hcompat hw₀.1,
    commutes_of_compat F h71c hcompat hDP hw₀.1 hY hη, hcgen⟩, rfl, hβ2,
    isW1Star_conj F hgα hcompat hw₀⟩

end P4X

end CFSG.Quasithin.Fan86
