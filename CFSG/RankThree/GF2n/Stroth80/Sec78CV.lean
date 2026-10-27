module

public import CFSG.RankThree.GF2n.Stroth80.Sec78QB
public import CFSG.RankThree.GF2n.Stroth80.Sec78CommW
public import CFSG.RankThree.GF2n.Stroth80.Sec78Z1
public import CFSG.RankThree.GF2n.Stroth80.Sec78FixedMod

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec7ctr_Vt_le_Wt (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (h5 : Sec5Hyp hc n t) : Vt M (LB M Q B) B Z t ≤ Wt Q (Vt M (LB M Q B) B Z t) := by
  have h35 := (stroth_3_5 h34 hc h5.width h5.n_gt h5.noA2 h5.gen).2.1
  have hel := hc.Vt_isElemAbelian h35 h5.mem h5.notQ
  intro v hv
  refine ⟨hc.Vt_le_Q t hv, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
  exact congrArg Subtype.val (hel.1.is_comm.comm ⟨w, hw⟩ ⟨v, hv⟩)

theorem sec7CV_of_inputs (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (hA7 : Sec7AExistsStatement) (h52b : Stroth52bStatement) : Sec7CVStatement := by
  intro G _ _ M Q Z B hc n t hs x hxQ
  have hs5 := hs.toSec5
  have ht : t ∈ LB M Q B := hs5.mem
  have htM : t ∈ M := hc.LB_le_M ht
  refine ⟨fun hxV y hy => (Ctx.mem_CN.mp (Subgroup.mem_inf.mp hy).2).2 x hxV, fun hx => ?_⟩
  by_contra hxV
  have hQM : Q ≤ M := hc.hyp.Q_normal.1
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hWQ : Wt Q (Vt M (LB M Q B) B Z t) ≤ Q := inf_le_left
  have hZQ : Z ≤ Q := hc.Z_le_Q
  have hRM : Rt M (LB M Q B) t ≤ M := hc.Rt_le_M t
  have hZnorm : ∀ g ∈ M, ∀ z ∈ Z, g * z * g⁻¹ ∈ Z := fun g hg z hz =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hg) z).mp hz
  obtain ⟨Z0, hZ0⟩ := hc.exists_centre ht
  have htZ0 : t ∈ Z0 := IsCentrePre.mem_of_mem_LB (hc := hc) ht hZ0
  have htN : t ∈ hc.CN t := sec7ctr_Z0_le_CN hc hs hZ0 htZ0
  have hxt : ⁅t, x⁆ ∈ Z := hx t (Subgroup.mem_inf.mpr ⟨ht, htN⟩)
  obtain ⟨-, hWQ1⟩ := stroth310Chi_of_34 h34 G M Q Z B hc n t hs5 (Or.inr hs.omegaNat)
  have hxW : x ∈ Wt Q (Vt M (LB M Q B) B Z t) := by
    rw [hWQ1, hc.mem_Q1_iff htM]
    exact ⟨hxQ, hxt⟩
  let D : Subgroup G :=
    { carrier := {w | w ∈ Wt Q (Vt M (LB M Q B) B Z t) ∧
        ∀ y ∈ LB M Q B ⊓ hc.CN t, ⁅y, w⁆ ∈ Z}
      mul_mem' := by
        rintro a b ⟨haW, ha⟩ ⟨hbW, hb⟩
        refine ⟨(Wt Q (Vt M (LB M Q B) B Z t)).mul_mem haW hbW, fun y hy => ?_⟩
        have e : ⁅y, a * b⁆ = ⁅y, a⁆ * (a * ⁅y, b⁆ * a⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact Z.mul_mem (ha y hy) (hZnorm a (hQM (hWQ haW)) _ (hb y hy))
      one_mem' := ⟨(Wt Q (Vt M (LB M Q B) B Z t)).one_mem, fun y _ => by
        simpa [commutatorElement_def] using Z.one_mem⟩
      inv_mem' := by
        rintro a ⟨haW, ha⟩
        refine ⟨(Wt Q (Vt M (LB M Q B) B Z t)).inv_mem haW, fun y hy => ?_⟩
        have e : ⁅y, a⁻¹⁆ = (a⁻¹ * ⁅y, a⁆ * a)⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]
        have h1 := hZnorm a⁻¹ (M.inv_mem (hQM (hWQ haW))) _ (ha y hy)
        rw [inv_inv] at h1
        exact Z.inv_mem h1 }
  have hDmem : ∀ w, w ∈ D ↔ w ∈ Wt Q (Vt M (LB M Q B) B Z t) ∧
      ∀ y ∈ LB M Q B ⊓ hc.CN t, ⁅y, w⁆ ∈ Z := fun w => Iff.rfl
  have hxD : x ∈ D := (hDmem x).mpr ⟨hxW, hx⟩
  have hVW : Vt M (LB M Q B) B Z t ≤ Wt Q (Vt M (LB M Q B) B Z t) := sec7ctr_Vt_le_Wt h34 hc hs5
  have hVD : Vt M (LB M Q B) B Z t ≤ D := fun v hv =>
    (hDmem v).mpr ⟨hVW hv, fun y hy => (Ctx.mem_CN.mp (Subgroup.mem_inf.mp hy).2).2 v hv⟩
  have hDQ : D ≤ Q := fun d hd => hWQ ((hDmem d).mp hd).1
  have hVlt : Vt M (LB M Q B) B Z t < D := by
    refine lt_of_le_of_ne hVD fun h => hxV ?_
    rw [h]
    exact hxD
  obtain ⟨jj, kk, hZ2, -⟩ := hc.hyp.cp
  have hQ2 : IsPGroup 2 ↥Q := by
    refine IsPGroup.of_card (n := jj * (2 * n + 1)) ?_
    have hw := hs5.width
    unfold Width at hw
    rw [hw, hZ2, ← pow_mul]
  have hD2 : IsPGroup 2 ↥D := hQ2.of_injective (Subgroup.inclusion hDQ)
    (Subgroup.inclusion_injective hDQ)
  have hL2 : IsPGroup 2 ↥(LB M Q B) :=
    Ctx.isPGroup_LB h34 hc hs5.width hs5.n_gt hs5.noA2 hs5.gen
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht
  have hTD : ∀ r ∈ LB M Q B, ∀ d ∈ D, r * d * r⁻¹ ∈ D := by
    intro r hr d hd
    have hrR : r ∈ Rt M (LB M Q B) t := hLR hr
    have hrM : r ∈ M := hRM hrR
    refine (hDmem _).mpr ⟨sec7ctr_Wt_conj_mem hc ht hrR ((hDmem d).mp hd).1, fun y hy => ?_⟩
    have hy' : r⁻¹ * y * r ∈ LB M Q B ⊓ hc.CN t := by
      refine Subgroup.mem_inf.mpr ⟨(LB M Q B).mul_mem ((LB M Q B).mul_mem
        ((LB M Q B).inv_mem hr) (Subgroup.mem_inf.mp hy).1) hr, ?_⟩
      have := hc.CN_conj_mem ht ((Rt M (LB M Q B) t).inv_mem hrR) (Subgroup.mem_inf.mp hy).2
      simpa using this
    have e : ⁅y, r * d * r⁻¹⁆ = r * ⁅r⁻¹ * y * r, d⁆ * r⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hrM) _).mp (((hDmem d).mp hd).2 _ hy')
  have hTV : ∀ r ∈ LB M Q B, ∀ v ∈ Vt M (LB M Q B) B Z t,
      r * v * r⁻¹ ∈ Vt M (LB M Q B) B Z t := fun r hr v hv =>
    (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht (hLR hr)) v).mp hv
  have hcommD : ∀ a ∈ D, ∀ b ∈ D, ⁅a, b⁆ ∈ Vt M (LB M Q B) B Z t := fun a ha b hb =>
    hZV (hc.hyp.toHyp79.comm_mem_V (hDQ ha) (hDQ hb))
  have hsqD : ∀ a ∈ D, a ^ 2 ∈ Vt M (LB M Q B) B Z t := fun a ha =>
    hZV (hc.hyp.toHyp79.sq_mem_V (hDQ ha))
  obtain ⟨d, hdD, hdV, hfix⟩ := sec7ctr_exists_fixed_mod hL2 hD2 hVlt hcommD hsqD hTD hTV
  obtain ⟨r, hr⟩ := hA7 G M Q Z B hc n t hs
  have hopp := h52b G M Q Z B hc n t hs5 hs.omegaNat r hr.mem hr.plane (conjSubgroup r B)
    (LB M Q B) (LB M Q (conjSubgroup r B)) (Vt M (LB M Q B) B Z t)
    (Wt Q (Vt M (LB M Q B) B Z t)) rfl rfl rfl rfl rfl
  obtain ⟨-, -, -, -, -, -, -, -, hA1, -⟩ := hopp
  have hdW : d ∈ Wt Q (Vt M (LB M Q B) B Z t) := ((hDmem d).mp hdD).1
  have hdA : d ∈ (QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔ Vt M (LB M Q B) B Z t :=
    (hA1 d hdW).mpr hfix
  have hnorm : QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t) ≤
      Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) := fun a ha =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp ha).2).2
  obtain ⟨a, haQB, v, hv, hadv⟩ := exists_mul_of_mem_sup_of_le_normalizer hnorm hdA
  have haV : a ∉ Vt M (LB M Q B) B Z t := fun haV =>
    hdV (hadv ▸ (Vt M (LB M Q B) B Z t).mul_mem haV hv)
  have haQQ : a ∈ Q ⊓ QB B := Subgroup.mem_inf.mpr
    ⟨hWQ (Subgroup.mem_inf.mp haQB).2, (Subgroup.mem_inf.mp haQB).1⟩
  have hcommA : ∀ l ∈ (QB B ⊓ M) ⊓ hc.CN t, ⁅l, a⁆ ∈ Z := by
    intro l hl
    have hlL : l ∈ LB M Q B := Subgroup.mem_sup_right (Subgroup.mem_inf.mp hl).1
    have hlLN : l ∈ LB M Q B ⊓ hc.CN t := Subgroup.mem_inf.mpr ⟨hlL, (Subgroup.mem_inf.mp hl).2⟩
    have hld : ⁅l, d⁆ ∈ Z := ((hDmem d).mp hdD).2 l hlLN
    have hlv : ⁅l, v⁻¹⁆ ∈ Z := (Ctx.mem_CN.mp (Subgroup.mem_inf.mp hl).2).2 _
      ((Vt M (LB M Q B) B Z t).inv_mem hv)
    have e : ⁅l, a⁆ = ⁅l, d⁆ * (d * ⁅l, v⁻¹⁆ * d⁻¹) := by
      have : a = d * v⁻¹ := by rw [← hadv]; group
      rw [this]
      simp only [commutatorElement_def]; group
    rw [e]
    exact Z.mul_mem hld (hZnorm d (hQM (hDQ hdD)) _ hlv)
  exact haV (sec7ctr_QB h34 hRoot hc hs a haQQ hcommA)

end CFSG.RankThree.GF2n.Stroth80
