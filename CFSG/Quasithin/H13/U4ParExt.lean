module

public import CFSG.Quasithin.H13.U4ParModule

public section

namespace CFSG.Quasithin.H13.U4Par

open Matrix CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

theorem conj_mem_centerOf {Y : Type} [Group Y] {X : Subgroup Y} {x z : Y}
    (hx : x ∈ Subgroup.normalizer (X : Set Y)) (hz : z ∈ centerOf X) :
    x * z * x⁻¹ ∈ centerOf X := by
  rw [centerOf, Subgroup.mem_inf] at hz ⊢
  obtain ⟨hzX, hzC⟩ := hz
  refine ⟨(Subgroup.mem_normalizer_iff.mp hx z).mp hzX, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have hw' : x⁻¹ * w * x ∈ X := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx) w).mp hw
    simpa using this
  have hc := Subgroup.mem_centralizer_iff.mp hzC _ hw'
  calc w * (x * z * x⁻¹) = x * ((x⁻¹ * w * x) * z) * x⁻¹ := by group
    _ = x * (z * (x⁻¹ * w * x)) * x⁻¹ := by rw [hc]
    _ = x * z * x⁻¹ * w := by group

variable {m : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 m K}

@[expose] noncomputable def xc (g : hypSU h 2 0) : K := ((g : GL Ix K) : Matrix Ix Ix K) ie2 if1

@[expose] noncomputable def yc (g : hypSU h 2 0) : K := ((g : GL Ix K) : Matrix Ix Ix K) if2 if1

theorem xc_of {g : hypSU h 2 0} {x y c : K}
    (hG : ((g : GL Ix K) : Matrix Ix Ix K) = sMat h x y c) : xc g = x := by
  rw [xc, hG, sMat_ie2_if1]

theorem yc_of {g : hypSU h 2 0} {x y c : K}
    (hG : ((g : GL Ix K) : Matrix Ix Ix K) = sMat h x y c) : yc g = y := by
  rw [yc, hG, sMat_if2_if1]

theorem coe_eq_sMat_xc_yc {g : hypSU h 2 0} (hg : g ∈ radQ h) :
    ((g : GL Ix K) : Matrix Ix Ix K) =
      sMat h (xc g) (yc g) (((g : GL Ix K) : Matrix Ix Ix K) ie1 if1) :=
  coe_eq_sMat_coord hg

theorem coe_mul_of {g g' : hypSU h 2 0} {x y c x' y' c' : K}
    (hG : ((g : GL Ix K) : Matrix Ix Ix K) = sMat h x y c)
    (hG' : ((g' : GL Ix K) : Matrix Ix Ix K) = sMat h x' y' c') :
    (((g * g' : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) =
      sMat h (x + x') (y + y') (c + c' + (h.bar y * x' + h.bar x * y')) := by
  rw [coe_mul_hypSU, hG, hG', sMat_mul]

theorem xc_mul {g g' : hypSU h 2 0} (hg : g ∈ radQ h) (hg' : g' ∈ radQ h) :
    xc (g * g') = xc g + xc g' := by
  obtain ⟨x, y, c, -, hG⟩ := hg
  obtain ⟨x', y', c', -, hG'⟩ := hg'
  rw [xc_of hG, xc_of hG', xc_of (coe_mul_of hG hG')]

theorem yc_mul {g g' : hypSU h 2 0} (hg : g ∈ radQ h) (hg' : g' ∈ radQ h) :
    yc (g * g') = yc g + yc g' := by
  obtain ⟨x, y, c, -, hG⟩ := hg
  obtain ⟨x', y', c', -, hG'⟩ := hg'
  rw [yc_of hG, yc_of hG', yc_of (coe_mul_of hG hG')]

theorem xc_inv {g : hypSU h 2 0} (hg : g ∈ radQ h) : xc g⁻¹ = xc g := by
  obtain ⟨x, y, c, hc, hG⟩ := hg
  rw [xc_of hG, xc_of (coe_inv_of_sMat hc hG)]

theorem yc_inv {g : hypSU h 2 0} (hg : g ∈ radQ h) : yc g⁻¹ = yc g := by
  obtain ⟨x, y, c, hc, hG⟩ := hg
  rw [yc_of hG, yc_of (coe_inv_of_sMat hc hG)]

theorem xc_yc_of_mem_zRad {z : hypSU h 2 0} (hz : z ∈ zRad h) : xc z = 0 ∧ yc z = 0 := by
  obtain ⟨c, -, hG⟩ := hz
  exact ⟨xc_of hG, yc_of hG⟩

theorem mem_zRad_of_xc_yc {g : hypSU h 2 0} (hg : g ∈ radQ h) (hx : xc g = 0) (hy : yc g = 0) :
    g ∈ zRad h := by
  obtain ⟨x, y, c, hc, hG⟩ := hg
  rw [xc_of hG] at hx
  rw [yc_of hG] at hy
  subst hx hy
  exact ⟨c, (sAdm_zero_zero_iff h).mp hc, hG⟩

theorem levHom_conj_mem_radQ {w : hypSU h 2 0} (hw : w ∈ radQ h)
    (A : Matrix.SpecialLinearGroup (Fin 2) h.fixedField) :
    levHom h A * w * (levHom h A)⁻¹ ∈ radQ h :=
  (Subgroup.mem_normalizer_iff.mp (parP_le_normalizer_radQ h (levHom_le_parP h ⟨A, rfl⟩)) w).mp hw

theorem xc_conj {w : hypSU h 2 0} (hw : w ∈ radQ h)
    (A : Matrix.SpecialLinearGroup (Fin 2) h.fixedField) :
    xc (levHom h A * w * (levHom h A)⁻¹) = slMat h A 0 0 * xc w + slMat h A 0 1 * yc w := by
  obtain ⟨x, y, c, -, hG⟩ := hw
  rw [xc_of (coe_conj_levHom h hG A), xc_of hG, yc_of hG]

theorem yc_conj {w : hypSU h 2 0} (hw : w ∈ radQ h)
    (A : Matrix.SpecialLinearGroup (Fin 2) h.fixedField) :
    yc (levHom h A * w * (levHom h A)⁻¹) = slMat h A 1 0 * xc w + slMat h A 1 1 * yc w := by
  obtain ⟨x, y, c, -, hG⟩ := hw
  rw [yc_of (coe_conj_levHom h hG A), xc_of hG, yc_of hG]

variable (h) in
@[expose] noncomputable def sxElt (x : K) : hypSU h 2 0 := sElt h (sAdm_x_zero h x)

variable (h) in
@[expose] noncomputable def syElt (y : K) : hypSU h 2 0 := sElt h (sAdm_zero_y h y)

theorem coe_sxElt (x : K) : (((sxElt h x : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) =
    sMat h x 0 0 := rfl

theorem coe_syElt (y : K) : (((syElt h y : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) =
    sMat h 0 y 0 := rfl

theorem coe_sxElt_inv (x : K) :
    ((((sxElt h x)⁻¹ : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) = sMat h x 0 (h.bar 0) :=
  coe_sElt_inv h _

theorem coe_syElt_inv (y : K) :
    ((((syElt h y)⁻¹ : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) = sMat h 0 y (h.bar 0) :=
  coe_sElt_inv h _

theorem sxElt_mem (x : K) : sxElt h x ∈ radQ h := sElt_mem_radQ h _

theorem syElt_mem (y : K) : syElt h y ∈ radQ h := sElt_mem_radQ h _

theorem slMat_slUt_one : slMat h (slUt h 1) 0 0 = 1 ∧ slMat h (slUt h 1) 0 1 = 1 ∧
    slMat h (slUt h 1) 1 0 = 0 ∧ slMat h (slUt h 1) 1 1 = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [slMat, slUt]

theorem slMat_slLt (t : h.fixedField) : slMat h (slLt h t) 0 0 = 1 ∧
    slMat h (slLt h t) 0 1 = 0 ∧ slMat h (slLt h t) 1 0 = t ∧ slMat h (slLt h t) 1 1 = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [slMat, slLt]

theorem slMat_slW : slMat h (slW h) 0 0 = 0 ∧ slMat h (slW h) 0 1 = 1 ∧
    slMat h (slW h) 1 0 = 1 ∧ slMat h (slW h) 1 1 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [slMat, slW]

section Alpha

variable (α : hypSU h 2 0 ≃* hypSU h 2 0)

theorem xc_yc_alpha_congr (hQ : ∀ s ∈ radQ h, α s ∈ radQ h)
    (hZ : ∀ z ∈ zRad h, α z ∈ zRad h) {s s' : hypSU h 2 0} (hs : s ∈ radQ h)
    (hs' : s' ∈ radQ h) (hx : xc s = xc s') (hy : yc s = yc s') :
    xc (α s) = xc (α s') ∧ yc (α s) = yc (α s') := by
  have := h.charP
  have hsi := (radQ h).inv_mem hs
  have hdQ : s⁻¹ * s' ∈ radQ h := (radQ h).mul_mem hsi hs'
  have hdZ : s⁻¹ * s' ∈ zRad h := mem_zRad_of_xc_yc hdQ
    (by rw [xc_mul hsi hs', xc_inv hs, hx, CharTwo.add_self_eq_zero])
    (by rw [yc_mul hsi hs', yc_inv hs, hy, CharTwo.add_self_eq_zero])
  have hαd := xc_yc_of_mem_zRad (hZ _ hdZ)
  have e : α s' = α s * α (s⁻¹ * s') := by
    rw [← map_mul]
    congr 1
    group
  rw [e, xc_mul (hQ s hs) (hQ _ hdQ), yc_mul (hQ s hs) (hQ _ hdQ), hαd.1, hαd.2, add_zero,
    add_zero]
  exact ⟨rfl, rfl⟩

theorem xc_yc_alpha_conj (hQ : ∀ s ∈ radQ h, α s ∈ radQ h)
    (hL : ∀ A, α (levHom h A) * (levHom h A)⁻¹ ∈ radQ h) {s : hypSU h 2 0} (hs : s ∈ radQ h)
    (A : Matrix.SpecialLinearGroup (Fin 2) h.fixedField) :
    xc (α (levHom h A * s * (levHom h A)⁻¹)) =
        slMat h A 0 0 * xc (α s) + slMat h A 0 1 * yc (α s) ∧
      yc (α (levHom h A * s * (levHom h A)⁻¹)) =
        slMat h A 1 0 * xc (α s) + slMat h A 1 1 * yc (α s) := by
  have := h.charP
  have hc2 : ∀ a b : K, a + b + a = b := fun a b => by
    rw [add_comm a b, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  obtain ⟨q, hq⟩ : ∃ q, q = α (levHom h A) * (levHom h A)⁻¹ := ⟨_, rfl⟩
  have hqQ : q ∈ radQ h := by
    rw [hq]
    exact hL A
  have hqi := (radQ h).inv_mem hqQ
  have hw := levHom_conj_mem_radQ (hQ s hs) A
  have he : α (levHom h A * s * (levHom h A)⁻¹) =
      q * (levHom h A * α s * (levHom h A)⁻¹) * q⁻¹ := by
    have hαL : α (levHom h A) = q * levHom h A := by
      rw [hq]
      group
    rw [map_mul, map_mul, map_inv, hαL]
    group
  rw [he, xc_mul ((radQ h).mul_mem hqQ hw) hqi, xc_mul hqQ hw, xc_inv hqQ, xc_conj (hQ s hs),
    yc_mul ((radQ h).mul_mem hqQ hw) hqi, yc_mul hqQ hw, yc_inv hqQ, yc_conj (hQ s hs)]
  exact ⟨hc2 _ _, hc2 _ _⟩

theorem ext_center_model (hQ : ∀ s ∈ radQ h, α s ∈ radQ h)
    (hZ : ∀ z ∈ zRad h, α z ∈ zRad h)
    (hL : ∀ A, α (levHom h A) * (levHom h A)⁻¹ ∈ radQ h) (hα2 : ∀ g, α (α g) = g) :
    ∀ z ∈ zRad h, α z = z := by
  have := h.charP
  obtain ⟨u00, u01, u10, u11⟩ := slMat_slUt_one (h := h)
  have hU : ∀ x : K, levHom h (slUt h 1) * sxElt h x * (levHom h (slUt h 1))⁻¹ = sxElt h x := by
    intro x
    apply hypSU_ext
    rw [coe_conj_levHom h (coe_sxElt x), coe_sxElt x, u00, u01, u10, u11]
    congr 1 <;> ring
  have hy0 : ∀ x : K, yc (α (sxElt h x)) = 0 := by
    intro x
    have h1 := (xc_yc_alpha_conj α hQ hL (sxElt_mem x) (slUt h 1)).1
    rw [hU x, u00, u01] at h1
    linear_combination -h1
  obtain ⟨w00, w01, w10, w11⟩ := slMat_slW (h := h)
  have hW : ∀ y : K, levHom h (slW h) * sxElt h y * (levHom h (slW h))⁻¹ = syElt h y := by
    intro y
    apply hypSU_ext
    rw [coe_conj_levHom h (coe_sxElt y), coe_syElt y, w00, w01, w10, w11]
    congr 1 <;> ring
  have hsy : ∀ y : K, xc (α (syElt h y)) = 0 ∧ yc (α (syElt h y)) = xc (α (sxElt h y)) := by
    intro y
    have h1 := xc_yc_alpha_conj α hQ hL (sxElt_mem y) (slW h)
    rw [hW y, w00, w01, w10, w11, hy0 y] at h1
    exact ⟨by linear_combination h1.1, by linear_combination h1.2⟩
  have hlin : ∀ a x : K, h.bar a = a →
      xc (α (sxElt h (a * x))) = a * xc (α (sxElt h x)) := by
    intro a x ha
    obtain ⟨t, rfl⟩ : ∃ t : h.fixedField, (t : K) = a :=
      ⟨⟨a, (h.mem_fixedField).mpr ha⟩, rfl⟩
    obtain ⟨l00, l01, l10, l11⟩ := slMat_slLt (h := h) t
    have hconjQ := levHom_conj_mem_radQ (sxElt_mem x) (slLt h t)
    have hprodQ := (radQ h).mul_mem (sxElt_mem x) (syElt_mem ((t : K) * x))
    have hx1 : xc (levHom h (slLt h t) * sxElt h x * (levHom h (slLt h t))⁻¹) =
        xc (sxElt h x * syElt h ((t : K) * x)) := by
      rw [xc_conj (sxElt_mem x), xc_mul (sxElt_mem x) (syElt_mem _), xc_of (coe_sxElt x),
        yc_of (coe_sxElt x), xc_of (coe_syElt _), l00, l01]
      ring
    have hy1 : yc (levHom h (slLt h t) * sxElt h x * (levHom h (slLt h t))⁻¹) =
        yc (sxElt h x * syElt h ((t : K) * x)) := by
      rw [yc_conj (sxElt_mem x), yc_mul (sxElt_mem x) (syElt_mem _), xc_of (coe_sxElt x),
        yc_of (coe_sxElt x), yc_of (coe_syElt _), l10, l11]
      ring
    have hc := (xc_yc_alpha_congr α hQ hZ hconjQ hprodQ hx1 hy1).2
    have h1 := (xc_yc_alpha_conj α hQ hL (sxElt_mem x) (slLt h t)).2
    rw [l10, l11, hy0 x] at h1
    rw [h1, map_mul, yc_mul (hQ _ (sxElt_mem x)) (hQ _ (syElt_mem _)), hy0 x, (hsy _).2] at hc
    linear_combination -hc
  have hcomm : ∀ y : K, (((α (sxElt h 1 * syElt h y * (sxElt h 1)⁻¹ * (syElt h y)⁻¹) :
      hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) =
        sMat h 0 0 (h.trace (h.bar (xc (α (sxElt h 1))) * xc (α (sxElt h y)))) := by
    intro y
    have ha := hQ _ (sxElt_mem (h := h) 1)
    have hb := hQ _ (syElt_mem (h := h) y)
    obtain ⟨ca, hca⟩ : ∃ ca, ca =
        (((α (sxElt h 1) : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) ie1 if1 := ⟨_, rfl⟩
    obtain ⟨cb, hcb⟩ : ∃ cb, cb =
        (((α (syElt h y) : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) ie1 if1 := ⟨_, rfl⟩
    have hGa := coe_eq_sMat_xc_yc ha
    rw [hy0 1, ← hca] at hGa
    have hGb := coe_eq_sMat_xc_yc hb
    rw [(hsy y).1, (hsy y).2, ← hcb] at hGb
    have hadma := sAdm_of_mem_radQ ha hGa
    have hadmb := sAdm_of_mem_radQ hb hGb
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, coe_mul_hypSU, coe_mul_hypSU,
      coe_mul_hypSU, coe_inv_of_sMat hadma hGa, coe_inv_of_sMat hadmb hGb, hGa, hGb,
      commutator_sMat h hadma hadmb, map_zero, zero_mul, zero_add]
  obtain ⟨y₀, hy₀⟩ := h.traceLin_surjective 1
  have hy₀' : h.trace y₀ = 1 := congrArg Subtype.val hy₀
  obtain ⟨δ, hδ⟩ : ∃ δ : K, δ = h.trace (h.bar (xc (α (sxElt h 1))) * xc (α (sxElt h y₀))) :=
    ⟨_, rfl⟩
  have hmain : ∀ z : hypSU h 2 0, ∀ a : K, h.bar a = a →
      ((z : GL Ix K) : Matrix Ix Ix K) = sMat h 0 0 a →
        (((α z : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) = sMat h 0 0 (a * δ) := by
    intro z a ha hGz
    have hz' : z = sxElt h 1 * syElt h (a * y₀) * (sxElt h 1)⁻¹ * (syElt h (a * y₀))⁻¹ := by
      apply hypSU_ext
      rw [hGz, coe_mul_hypSU, coe_mul_hypSU, coe_mul_hypSU, coe_sxElt_inv, coe_syElt_inv,
        coe_sxElt, coe_syElt, commutator_sMat h (sAdm_x_zero h 1) (sAdm_zero_y h (a * y₀))]
      congr 1
      rw [map_zero, zero_mul, zero_add, map_one, one_mul]
      unfold UnitaryFieldData.trace at hy₀' ⊢
      rw [map_mul, ha]
      linear_combination (-a) * hy₀'
    rw [hz', hcomm (a * y₀), hlin a y₀ ha, hδ]
    congr 1
    unfold UnitaryFieldData.trace
    simp only [map_mul, ha, h.bar_bar]
    ring
  obtain ⟨z₁, hz₁⟩ : ∃ z, z = sElt h ((sAdm_zero_zero_iff h).mpr (map_one h.bar)) :=
    ⟨_, rfl⟩
  have hGz₁ : ((z₁ : GL Ix K) : Matrix Ix Ix K) = sMat h 0 0 1 := by
    rw [hz₁, coe_sElt]
  have hz₁Z : z₁ ∈ zRad h := ⟨1, map_one _, hGz₁⟩
  have e1 := hmain z₁ 1 (map_one _) hGz₁
  obtain ⟨c₁, hc₁, hGc₁⟩ := hZ z₁ hz₁Z
  have hcδ : c₁ = 1 * δ := (sMat_injective h (hGc₁.symm.trans e1)).2.2
  have e2 := hmain (α z₁) c₁ hc₁ hGc₁
  rw [hα2, hGz₁] at e2
  have hδ2 : 1 = c₁ * δ := (sMat_injective h e2).2.2
  rw [hcδ, one_mul] at hδ2
  have hδ1 : δ = 1 := by
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have h4 : (δ + 1) ^ 2 = 0 := by linear_combination -hδ2 + (δ + 1) * h2
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h4
    rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at this
    exact this
  intro z hz
  obtain ⟨a, ha, hGz⟩ := hz
  apply hypSU_ext
  rw [hmain z a ha hGz, hδ1, mul_one, hGz]

end Alpha

theorem factU4ExtCenter_holds : FactU4ExtCenter := by
  intro Y _ m T M₁ M hm hY hpair hsp t ht ht2 _ htk
  obtain ⟨hfin, K, _, h, ψ, hψ, hidx, -, -, hcore, hO⟩ := recog_of hm (Or.inr hY) hpair hsp
  have hnorm : ψ.range.Normal := normal_of_index_le_two hidx
  have hZQ : centerOf (pCoreOf 2 (perfectCore M)) = (zRad h).map ψ := by
    rw [hO, centerOf_map_of_inj hψ, centerOf_radQ]
  have htM : t ∈ Subgroup.normalizer (perfectCore M : Set Y) :=
    normalizer_le_normalizer_perfectCore M (Subgroup.le_normalizer ht)
  have htQ : t ∈ Subgroup.normalizer (pCoreOf 2 (perfectCore M) : Set Y) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ htM
  obtain ⟨α, hαdef⟩ : ∃ α : hypSU h 2 0 ≃* hypSU h 2 0, α = (MonoidHom.ofInjective hψ).trans
      ((MulAut.conjNormal t).trans (MonoidHom.ofInjective hψ).symm) := ⟨_, rfl⟩
  have hα : ∀ g, ψ (α g) = t * ψ g * t⁻¹ := fun g => by
    rw [hαdef]
    simp only [MulEquiv.trans_apply, MonoidHom.apply_ofInjective_symm,
      MulAut.conjNormal_apply, MonoidHom.ofInjective_apply]
  have htt : t * t = 1 := by rw [← sq]; exact ht2
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hQ : ∀ s ∈ radQ h, α s ∈ radQ h := by
    intro s hs
    rw [← Subgroup.mem_map_iff_mem hψ, hα, ← hO]
    refine (Subgroup.mem_normalizer_iff.mp htQ (ψ s)).mp ?_
    rw [hO]
    exact Subgroup.mem_map_of_mem ψ hs
  have hZ : ∀ z ∈ zRad h, α z ∈ zRad h := by
    intro z hz
    rw [← Subgroup.mem_map_iff_mem hψ, hα, ← hZQ]
    refine conj_mem_centerOf htQ ?_
    rw [hZQ]
    exact Subgroup.mem_map_of_mem ψ hz
  have hL : ∀ A, α (levHom h A) * (levHom h A)⁻¹ ∈ radQ h := by
    intro A
    have hk : ψ (levHom h A) ∈ perfectCore M := by
      rw [hcore]
      exact Subgroup.mem_map_of_mem ψ (levHom_range_le_perfectCore h hm ⟨A, rfl⟩)
    have h1 := htk _ hk
    rw [hO] at h1
    rw [← Subgroup.mem_map_iff_mem hψ, map_mul, map_inv, hα]
    exact h1
  have hα2 : ∀ g, α (α g) = g := by
    intro g
    apply hψ
    rw [hα, hα, hti]
    calc t * (t * ψ g * t) * t = (t * t) * ψ g * (t * t) := by group
      _ = ψ g := by rw [htt, one_mul, mul_one]
  have key := ext_center_model α hQ hZ hL hα2
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  rw [hZQ] at hz
  obtain ⟨z₀, hz₀, rfl⟩ := hz
  have h1 := hα z₀
  rw [key z₀ hz₀] at h1
  calc ψ z₀ * t = t * ψ z₀ * t⁻¹ * t := by rw [← h1]
    _ = t * ψ z₀ := by group

end CFSG.Quasithin.H13.U4Par
