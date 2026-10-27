module

public import CFSG.RankThree.GF2n.Stroth80.Sec108CR
public import CFSG.RankThree.GF2n.Stroth80.Sec85Normal

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {hc : Ctx M Q Z B} {t : G} {Y : Subgroup G}

private theorem mem_conj_LB_of_mem_Q (hc : Ctx M Q Z B) {m w : G} (hm : m ∈ M) (hw : w ∈ Q) :
    w ∈ conjSubgroup m (LB M Q B) := by
  rw [mem_conjSubgroup]
  have h := conj_mem_Q hc.hyp (M.inv_mem hm) hw
  rw [inv_inv] at h
  exact Subgroup.mem_sup_left h

private theorem mem_normalizer_of_conj_mem {H : Subgroup G} {g : G}
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  have hle : conjSubgroup g H ≤ H := by
    intro x hx
    rw [mem_conjSubgroup] at hx
    have h1 := h _ hx
    rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at h1
  exact conjSubgroup_eq_self_iff.mp
    (Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSubgroup]))

private theorem conj_inv_mem {H : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (H : Set G))
    {x : G} (hx : x ∈ H) : g⁻¹ * x * g ∈ H := by
  have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) x).mp hx
  rwa [inv_inv] at h

theorem Sec108Data.mem_conj_LB_iff (D : Sec108Data hc t Y) {m : G} (hm : m ∈ M) :
    t ∈ conjSubgroup m (LB M Q B) ↔ conjSubgroup m B ≤ Vt M (LB M Q B) B Z t := by
  refine ⟨fun htm => ?_, fun hle => ?_⟩
  · unfold Vt
    exact le_sup_of_le_right (le_iSup₂_of_le m hm (le_iSup_of_le htm le_rfl))
  rw [D.good.Vt_eq D.sit] at hle
  obtain ⟨w, hw, a, ha, ha1, haP⟩ := hc.exists_conj_mem_of_le_sup hm inf_le_left hle
  have hwm : w * m ∈ M := M.mul_mem (hc.hyp.Q_normal.1 hw) hm
  have hB : ∃ g : G, conjSubgroup (w * m) B = conjSubgroup g Z := by
    obtain ⟨g, hg⟩ := hc.conj
    exact ⟨w * m * g, by rw [hg, ← CFSG.RankThree.GF2n.conjSubgroup_mul]⟩
  have hYle : Y ≤ QB (conjSubgroup (w * m) B) :=
    hc.hyp.le_QB_of_mem_QB D.sit.conj hB ha ha1 haP.2
  have htL : t ∈ LB M Q (conjSubgroup (w * m) B) := by
    unfold LB
    exact Subgroup.mem_sup_right ⟨hYle D.sit.mem, D.sit.memM⟩
  rwa [hc.LB_conj hwm, CFSG.RankThree.GF2n.conjSubgroup_mul, conjSubgroup_eq_self_iff.mpr
    (Subgroup.le_normalizer (mem_conj_LB_of_mem_Q hc hm hw))] at htL

theorem Sec108Data.conj_Rt_of_conj_Vt (D : Sec108Data hc t Y) {g : G} (hg : g ∈ M)
    (hV : conjSubgroup g (Vt M (LB M Q B) B Z t) = Vt M (LB M Q B) B Z t) :
    conjSubgroup g (Rt M (LB M Q B) t) = Rt M (LB M Q B) t := by
  have hV' : conjSubgroup g⁻¹ (Vt M (LB M Q B) B Z t) = Vt M (LB M Q B) B Z t := by
    conv_lhs => rw [← hV]
    rw [← CFSG.RankThree.GF2n.conjSubgroup_mul, inv_mul_cancel,
      CFSG.RankThree.GF2n.conjSubgroup_one]
  have key : ∀ m, m ∈ M →
      (g * t * g⁻¹ ∈ conjSubgroup m (LB M Q B) ↔ t ∈ conjSubgroup m (LB M Q B)) := by
    intro m hm
    have hgm : g⁻¹ * m ∈ M := M.mul_mem (M.inv_mem hg) hm
    have e1 : g * t * g⁻¹ ∈ conjSubgroup m (LB M Q B) ↔
        t ∈ conjSubgroup (g⁻¹ * m) (LB M Q B) := by
      rw [mem_conjSubgroup, mem_conjSubgroup,
        show (g⁻¹ * m)⁻¹ * t * (g⁻¹ * m) = m⁻¹ * (g * t * g⁻¹) * m by group]
    rw [e1, D.mem_conj_LB_iff hgm, D.mem_conj_LB_iff hm, CFSG.RankThree.GF2n.conjSubgroup_mul]
    constructor
    · intro h
      calc conjSubgroup m B = conjSubgroup g (conjSubgroup g⁻¹ (conjSubgroup m B)) := by
            rw [← CFSG.RankThree.GF2n.conjSubgroup_mul g g⁻¹, mul_inv_cancel,
              CFSG.RankThree.GF2n.conjSubgroup_one]
        _ ≤ conjSubgroup g (Vt M (LB M Q B) B Z t) := Subgroup.map_mono h
        _ = Vt M (LB M Q B) B Z t := hV
    · intro h
      calc conjSubgroup g⁻¹ (conjSubgroup m B) ≤ conjSubgroup g⁻¹ (Vt M (LB M Q B) B Z t) :=
            Subgroup.map_mono h
        _ = Vt M (LB M Q B) B Z t := hV'
  rw [conjSubgroup_Rt_eq hg t]
  exact iSup_congr fun m => iSup_congr fun hm => iSup_congr_Prop (key m hm) fun _ => rfl

theorem Sec108Data.Rt_le_normalizer_root (D : Sec108Data hc t Y) :
    Rt M (LB M Q B) t ≤ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G) := by
  intro r hr
  have hrM : r ∈ M := hc.Rt_le_M t hr
  refine mem_normalizer_of_conj_mem fun x hx => ?_
  have hsub : Y ⊔ Q ≤ (Y ⊔ Q).comap (MulAut.conj r).toMonoidHom := by
    refine sup_le (fun y hy => ?_) (fun w hw => ?_)
    · show r * y * r⁻¹ ∈ Y ⊔ Q
      rw [show r * y * r⁻¹ = ⁅r, y⁆ * y by rw [commutatorElement_def]; group]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (D.comm_Rt_root_mem r hr y hy))
        (Subgroup.mem_sup_left hy)
    · exact Subgroup.mem_sup_right (conj_mem_Q hc.hyp hrM hw)
  exact hsub hx

theorem Sec108Data.mem_normalizer_root_of_conj_Rt (D : Sec108Data hc t Y) {g : G} (hg : g ∈ M)
    (hR : conjSubgroup g (Rt M (LB M Q B) t) = Rt M (LB M Q B) t) :
    g ∈ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G) := by
  have hRi : ∀ r ∈ Rt M (LB M Q B) t, g⁻¹ * r * g ∈ Rt M (LB M Q B) t := fun r hr =>
    conj_inv_mem (conjSubgroup_eq_self_iff.mp hR) hr
  refine mem_normalizer_of_conj_mem fun x hx => ?_
  have hsub : Y ⊔ Q ≤ (Y ⊔ Q).comap (MulAut.conj g).toMonoidHom := by
    refine sup_le (fun y hy => ?_) (fun w hw => ?_)
    · show g * y * g⁻¹ ∈ Y ⊔ Q
      have hyM : y ∈ M := ((smith_1_12 D.sit).1 hy).1
      have hxM : g * y * g⁻¹ ∈ M := M.mul_mem (M.mul_mem hg hyM) (M.inv_mem hg)
      have hy1 : y ^ Nat.card Y = 1 :=
        orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard Y hy)
      obtain ⟨n, -, hn, -⟩ := hc.hyp.cp
      have hYc : Nat.card Y = 2 ^ n := by
        obtain ⟨g', hg'⟩ := D.sit.conj
        rw [hg', card_conjSubgroup, hn]
      have h2 : (g * y * g⁻¹) ^ 2 ^ n ∈ Q := by
        rw [conj_pow, ← hYc, hy1, mul_one, mul_inv_cancel]
        exact Q.one_mem
      have hcomm : ∀ r ∈ Rt M (LB M Q B) t, ⁅g * y * g⁻¹, r⁆ ∈ Q := by
        intro r hr
        have h1 := conj_mem_Q hc.hyp hg (Q.inv_mem (D.comm_Rt_root_mem _ (hRi r hr) y hy))
        rwa [show g * ⁅g⁻¹ * r * g, y⁆⁻¹ * g⁻¹ = ⁅g * y * g⁻¹, r⁆ by
          simp only [commutatorElement_def]; group] at h1
      obtain ⟨y', hy', hq⟩ := D.exists_root_of_twoElt hxM h2 hcomm
      rw [show g * y * g⁻¹ = (g * y * g⁻¹ * y'⁻¹) * y' by group]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hq) (Subgroup.mem_sup_left hy')
    · exact Subgroup.mem_sup_right (conj_mem_Q hc.hyp hg hw)
  exact hsub hx

theorem Sec108Data.exists_root_mul (D : Sec108Data hc t Y) {x : G} (hx : x ∈ Y ⊔ Q) :
    ∃ y ∈ Y, ∃ w ∈ Q, y * w = x := by
  have hYN : Y ≤ Subgroup.normalizer ((Q : Subgroup G) : Set G) := fun y hy =>
    hc.hyp.Q_normal.2 ((smith_1_12 D.sit).1 hy).1
  have hmem : x ∈ ((Y ⊔ Q : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right Y Q hYN] at hmem
  obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hmem
  exact ⟨a, ha, b, hb, hab⟩

theorem Sec108Data.conj_Vt_of_mem_normalizer_root (D : Sec108Data hc t Y) {g : G} (hg : g ∈ M)
    (hgY : g ∈ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G)) :
    conjSubgroup g (Vt M (LB M Q B) B Z t) = Vt M (LB M Q B) B Z t := by
  obtain ⟨y, hy, w, hw, hyw⟩ := D.exists_root_mul
    ((Subgroup.mem_normalizer_iff.mp hgY t).mp (Subgroup.mem_sup_left D.sit.mem))
  have hy1 : y ≠ 1 := by
    rintro rfl
    rw [one_mul] at hyw
    rw [hyw] at hw
    apply D.sit.notQ
    have h := conj_mem_Q hc.hyp (M.inv_mem hg) hw
    rwa [show g⁻¹ * (g * t * g⁻¹) * g⁻¹⁻¹ = t by group] at h
  rw [conjSubgroup_Vt_eq hg (hc.conj_Z_eq hg) t, ← hyw, Vt_mul_of_mem_Q hc hw,
    D.good.1.Vt_eq_of_mem_root D.h34 D.hspread D.hyp D.sit hy hy1]

theorem Sec108Data.mem_normalizer_CN_of_conj_Vt (D : Sec108Data hc t Y) {g : G} (hg : g ∈ M)
    (hV : conjSubgroup g (Vt M (LB M Q B) B Z t) = Vt M (LB M Q B) B Z t) :
    g ∈ Subgroup.normalizer ((hc.CN t : Subgroup G) : Set G) :=
  mem_normalizer_of_conj_mem fun _ hx =>
    mem_CN_conj_of_normalizes hc hg (D.conj_Rt_of_conj_Vt hg hV) hV hx

theorem Sec108Data.mem_normalizer_root_iff_Vt (D : Sec108Data hc t Y) {g : G} (hg : g ∈ M) :
    g ∈ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G) ↔
      g ∈ Subgroup.normalizer ((Vt M (LB M Q B) B Z t : Subgroup G) : Set G) := by
  rw [← conjSubgroup_eq_self_iff (T := Vt M (LB M Q B) B Z t)]
  exact ⟨D.conj_Vt_of_mem_normalizer_root hg,
    fun hV => D.mem_normalizer_root_of_conj_Rt hg (D.conj_Rt_of_conj_Vt hg hV)⟩

theorem Sec108Data.mem_normalizer_root_iff_Rt (D : Sec108Data hc t Y) {g : G} (hg : g ∈ M) :
    g ∈ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G) ↔
      g ∈ Subgroup.normalizer ((Rt M (LB M Q B) t : Subgroup G) : Set G) := by
  rw [← conjSubgroup_eq_self_iff (T := Rt M (LB M Q B) t)]
  exact ⟨fun hgY => D.conj_Rt_of_conj_Vt hg (D.conj_Vt_of_mem_normalizer_root hg hgY),
    D.mem_normalizer_root_of_conj_Rt hg⟩

theorem Sec108Data.mem_normalizer_root_of_conj (D : Sec108Data hc t Y) {g : G} (hg : g ∈ M)
    {y y' : G} (hy : y ∈ Y) (hy' : y' ∈ Y) (hy1 : y ≠ 1) (h : y⁻¹ * (g * y' * g⁻¹) ∈ Q) :
    g ∈ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G) := by
  have hy'1 : y' ≠ 1 := by
    rintro rfl
    rw [mul_one, mul_inv_cancel, mul_one] at h
    have hmem : y⁻¹ ∈ Y ⊓ Q := ⟨Y.inv_mem hy, h⟩
    rw [(smith_1_12 D.sit).2, Subgroup.mem_bot, inv_eq_one] at hmem
    exact hy1 hmem
  have hV : conjSubgroup g (Vt M (LB M Q B) B Z t) = Vt M (LB M Q B) B Z t :=
    calc conjSubgroup g (Vt M (LB M Q B) B Z t) = conjSubgroup g (Vt M (LB M Q B) B Z y') := by
          rw [D.good.1.Vt_eq_of_mem_root D.h34 D.hspread D.hyp D.sit hy' hy'1]
      _ = Vt M (LB M Q B) B Z (g * y' * g⁻¹) := conjSubgroup_Vt_eq hg (hc.conj_Z_eq hg) y'
      _ = Vt M (LB M Q B) B Z (y * (y⁻¹ * (g * y' * g⁻¹))) := by rw [mul_inv_cancel_left]
      _ = Vt M (LB M Q B) B Z y := Vt_mul_of_mem_Q hc h
      _ = Vt M (LB M Q B) B Z t := D.good.1.Vt_eq_of_mem_root D.h34 D.hspread D.hyp D.sit hy hy1
  exact D.mem_normalizer_root_of_conj_Rt hg (D.conj_Rt_of_conj_Vt hg hV)

end CFSG.RankThree.GF2n.Stroth80
