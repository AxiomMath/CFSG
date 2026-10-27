module

public import CFSG.RankThree.GF2n.Stroth80.Sec9Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec39Rt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec9_Q_le_CN (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) : Q ≤ hc.CN t :=
  fun x hx => Ctx.mem_CN.mpr ⟨hc.Q_le_Rt ht hx,
    fun v hv => hc.hyp.toHyp79.comm_mem_V hx (hc.Vt_le_Q t hv)⟩

theorem sec9_CN_le_Rt (hc : Ctx M Q Z B) (t : G) : hc.CN t ≤ Rt M (LB M Q B) t :=
  fun _ hx => (Ctx.mem_CN.mp hx).1

theorem CN_le_Sec9R0 (hc : Ctx M Q Z B) (t x : G) : hc.CN t ≤ Sec9R0 hc t x := le_sup_left

theorem Q_le_Sec9R0 (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) (x : G) :
    Q ≤ Sec9R0 hc t x :=
  (sec9_Q_le_CN hc ht).trans (CN_le_Sec9R0 hc t x)

theorem Sec9R0_le_Rt (hc : Ctx M Q Z B) {t x : G} (hx : x ∈ Rt M (LB M Q B) t) :
    Sec9R0 hc t x ≤ Rt M (LB M Q B) t := by
  refine sup_le (sec9_CN_le_Rt hc t) (iSup₂_le fun ρ hρ => ?_)
  rw [Subgroup.zpowers_le]
  exact (Rt M (LB M Q B) t).mul_mem ((Rt M (LB M Q B) t).mul_mem hρ hx)
    ((Rt M (LB M Q B) t).inv_mem hρ)

theorem mem_Sec9R0 (hc : Ctx M Q Z B) (t : G) {x : G} (hx : x ∈ Rt M (LB M Q B) t) :
    x ∈ Sec9R0 hc t x := by
  refine Subgroup.mem_sup_right ?_
  refine (Subgroup.mem_iSup_of_mem 1 (Subgroup.mem_iSup_of_mem (Subgroup.one_mem _) ?_))
  have e : (1 : G) * x * (1 : G)⁻¹ = x := by group
  rw [e]
  exact Subgroup.mem_zpowers x

theorem sec9_conj_mem_Wt (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) {ρ : G}
    (hρ : ρ ∈ Rt M (LB M Q B) t) {w : G}
    (hw : w ∈ Wt Q (Vt M (LB M Q B) B Z t)) :
    ρ * w * ρ⁻¹ ∈ Wt Q (Vt M (LB M Q B) B Z t) := by
  have hρM : ρ ∈ M := hc.Rt_le_M t hρ
  refine ⟨(Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hρM) w).mp hw.1,
    Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
  have hv' : ρ⁻¹ * v * ρ ∈ Vt M (LB M Q B) B Z t := by
    have := (Subgroup.mem_normalizer_iff.mp
      (hc.Rt_normalizes_Vt ht ((Rt M (LB M Q B) t).inv_mem hρ)) v).mp hv
    simpa using this
  have hc' := Subgroup.mem_centralizer_iff.mp hw.2 _ hv'
  calc v * (ρ * w * ρ⁻¹) = ρ * ((ρ⁻¹ * v * ρ) * w) * ρ⁻¹ := by group
    _ = ρ * (w * (ρ⁻¹ * v * ρ)) * ρ⁻¹ := by rw [hc']
    _ = ρ * w * ρ⁻¹ * v := by group

theorem Sec9R0_comm_mem (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B)
    (hN : ∀ s ∈ hc.CN t, ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅s, w⁆ ∈ Vt M (LB M Q B) B Z t)
    {x : G} (hxR : x ∈ Rt M (LB M Q B) t)
    (hx : ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅x, w⁆ ∈ Vt M (LB M Q B) B Z t) :
    ∀ a ∈ Sec9R0 hc t x, ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t),
      ⁅a, w⁆ ∈ Vt M (LB M Q B) B Z t := by
  set V := Vt M (LB M Q B) B Z t with hV
  set W := Wt Q V with hW
  have hnV : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ v ∈ V, ρ * v * ρ⁻¹ ∈ V := fun ρ hρ v hv =>
    (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht hρ) v).mp hv
  let C : Subgroup G :=
    { carrier := {a | a ∈ Rt M (LB M Q B) t ∧ ∀ w ∈ W, ⁅a, w⁆ ∈ V}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨(Rt M (LB M Q B) t).mul_mem ha hb, fun w hw => ?_⟩
        have e : ⁅a * b, w⁆ = a * ⁅b, w⁆ * a⁻¹ * ⁅a, w⁆ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact V.mul_mem (hnV a ha _ (hb' w hw)) (ha' w hw)
      one_mem' := ⟨(Rt M (LB M Q B) t).one_mem, fun w _ => by
        simp [commutatorElement_def]⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨(Rt M (LB M Q B) t).inv_mem ha, fun w hw => ?_⟩
        have e : ⁅a⁻¹, w⁆ = a⁻¹ * ⁅a, w⁆⁻¹ * a := by
          simp only [commutatorElement_def]; group
        rw [e]
        have := hnV a⁻¹ ((Rt M (LB M Q B) t).inv_mem ha) _ (V.inv_mem (ha' w hw))
        simpa using this }
  have hCN : hc.CN t ≤ C := fun s hs => ⟨(Ctx.mem_CN.mp hs).1, hN s hs⟩
  have hconj : ∀ ρ ∈ Rt M (LB M Q B) t, ρ * x * ρ⁻¹ ∈ C := by
    intro ρ hρ
    refine ⟨(Rt M (LB M Q B) t).mul_mem ((Rt M (LB M Q B) t).mul_mem hρ hxR)
      ((Rt M (LB M Q B) t).inv_mem hρ), fun w hw => ?_⟩
    have hw' : ρ⁻¹ * w * ρ ∈ W := by
      have := sec9_conj_mem_Wt hc ht ((Rt M (LB M Q B) t).inv_mem hρ) hw
      simpa using this
    have e : ⁅ρ * x * ρ⁻¹, w⁆ = ρ * ⁅x, ρ⁻¹ * w * ρ⁆ * ρ⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact hnV ρ hρ _ (hx _ hw')
  have hle : Sec9R0 hc t x ≤ C := by
    refine sup_le hCN (iSup₂_le fun ρ hρ => ?_)
    rw [Subgroup.zpowers_le]
    exact hconj ρ hρ
  exact fun a ha w hw => (hle ha).2 w hw

theorem stroth92_of_steps (hA : Sec9AExistsStatement) (h91b : Stroth91bStatement)
    (hNon : Step92NontrivStatement) (hQuot : Step92QuotStatement)
    (hSplit : Step92SplitStatement) : Stroth92Statement := by
  intro G _ _ M Q Z B hc n t hs V W hV hW x hxL hxN hxW
  subst hV hW
  have ht := hs.mem
  obtain ⟨r, hr⟩ := hA G M Q Z B hc n t hs
  have hNW := (h91b G M Q Z B hc n t hs r hr _ _ rfl rfl).2
  have hxR : x ∈ Rt M (LB M Q B) t := (le_Rt (M := M) (LB M Q B) ht) hxL
  have hcomm := Sec9R0_comm_mem hc ht hNW hxR hxW
  have hlt : Sec9R0 hc t x < Rt M (LB M Q B) t := by
    refine lt_of_le_of_ne (Sec9R0_le_Rt hc hxR) fun h => ?_
    obtain ⟨ρ, hρ, w, hw, hn⟩ := hNon G M Q Z B hc n t hs _ _ rfl rfl
    exact hn (hcomm ρ (h ▸ hρ) w hw)
  have hquot := hQuot G M Q Z B hc n t hs x hxL hxN hlt
  exact ⟨hSplit G M Q Z B hc n t hs _ _ rfl rfl x hxL hxN hxW hlt hquot, hcomm⟩

end CFSG.RankThree.GF2n.Stroth80
