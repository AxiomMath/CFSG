module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4OvGenP
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4OvOrb
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4OvGenE

public section

namespace CFSG.Quasithin.J4Ov

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2 Matrix
open CFSG.Quasithin.J4Loc

theorem kz0_fixed : ∀ i < 4, actT (kTab i) 1131 = 1131 ∧ actT (kInvTab i) 1131 = 1131 := by
  decide +kernel

theorem P0_conj_z0 (hM : MatFacts) :
    ∀ g ∈ P0, g * z0 * g⁻¹ = z0 := by
  have hKE : maskSub z0L ≤ Eg uJ 11 := maskSub_le_Eg z0L
  have hz0K : z0 ∈ maskSub z0L := (mem_z0Sub hM).2 (Or.inr rfl)
  have hk : ∀ i < 4, ∀ c < 2048, eta uJ 11 c ∈ maskSub z0L →
      eta uJ 11 (actT (kTab i) c) ∈ maskSub z0L ∧ eta uJ 11 (actT (kInvTab i) c) ∈ maskSub z0L := by
    intro i hi c hc hmem
    rcases (mem_z0Sub hM).1 hmem with h | h
    · have hc0 : c = 0 := by
        have : eta uJ 11 c = eta uJ 11 0 := by rw [h, eta_zero]
        exact eta_inj' hM hc (by norm_num) this
      subst hc0
      rw [actT_zero, actT_zero, eta_zero]
      exact ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩
    · have hc1 : c = 1131 := eta_inj' hM hc (by norm_num) h
      subst hc1
      rw [(kz0_fixed i hi).1, (kz0_fixed i hi).2]
      exact ⟨hz0K, hz0K⟩
  intro g hg
  have h1 := (normalized_of_gens hM hKE hk g hg z0 hz0K).1
  rcases (mem_z0Sub hM).1 h1 with h | h
  · exfalso
    apply z0_ne_one hM
    have e : z0 = g⁻¹ * (g * z0 * g⁻¹) * g := by group
    rw [e, h]
    group
  · exact h


@[expose] def conjPre {G : Type*} [Group G] (Y : Subgroup G) (h : G) : Subgroup G where
  carrier := {x | h * x * h⁻¹ ∈ Y}
  mul_mem' := by
    intro a b ha hb
    show h * (a * b) * h⁻¹ ∈ Y
    have e : h * (a * b) * h⁻¹ = (h * a * h⁻¹) * (h * b * h⁻¹) := by group
    rw [e]
    exact Y.mul_mem ha hb
  one_mem' := by
    show h * 1 * h⁻¹ ∈ Y
    simp
  inv_mem' := by
    intro a ha
    show h * a⁻¹ * h⁻¹ ∈ Y
    have e : h * a⁻¹ * h⁻¹ = (h * a * h⁻¹)⁻¹ := by group
    rw [e]
    exact Y.inv_mem ha

theorem mem_conjPre {G : Type*} [Group G] {Y : Subgroup G} {h x : G} :
    x ∈ conjPre Y h ↔ h * x * h⁻¹ ∈ Y := Iff.rfl

section Key


theorem conj_z0_mem [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat] (hF : J4Facts) {Y : Subgroup J} (hP : P0 ≤ Y) (hY : Y ≠ ⊤) :
    ∀ y ∈ Y, y⁻¹ * z0 * y ∈ Eg uJ 11 := by
  have hM := hF.mat
  intro y hy
  have hE : Eg uJ 11 ≤ Y := Eg_le_P0.trans hP
  obtain ⟨ℓ, hℓ, h, hh, h', hh', rfl⟩ := exists_rep hF y
  have hzE : z0 ∈ Eg uJ 11 := eta_mem_Eg 11 le_rfl 1131
  by_cases hℓ0 : ℓ = 0
  · subst hℓ0
    have e : (h * (pathElt (repPaths.getD 0 []))⁻¹ * h')⁻¹ * z0 *
        (h * (pathElt (repPaths.getD 0 []))⁻¹ * h') = (h * h')⁻¹ * z0 * (h * h')⁻¹⁻¹ := by
      simp [repPaths, pathElt]
    rw [e]
    exact Hj_normalizes_Eg hM _ (Hj.inv_mem (Hj.mul_mem hh hh')) z0 hzE
  by_cases hℓ4 : ℓ ≤ 4
  · exfalso
    apply hY
    let D : Subgroup J := conjPre Y h
    have hDE : Eg uJ 11 ≤ D := fun x hx => mem_conjPre.2 (hE (Hj_normalizes_Eg hM h hh x hx))
    have hDc : ∀ e ∈ Eg uJ 11, uEl ℓ * e * (uEl ℓ)⁻¹ ∈ D := by
      intro e he
      have e1 : h * (uEl ℓ * e * (uEl ℓ)⁻¹) * h⁻¹ =
          (h * uEl ℓ * h') * (h'⁻¹ * e * h') * (h * uEl ℓ * h')⁻¹ := by group
      rw [mem_conjPre, e1]
      have h2 : h'⁻¹ * e * h' ∈ Eg uJ 11 := by
        have := Hj_normalizes_Eg hM h'⁻¹ (Hj.inv_mem hh') e he
        rwa [inv_inv] at this
      exact Y.mul_mem (Y.mul_mem hy (hE h2)) (Y.inv_mem hy)
    have hDtop := genE hF (by omega) hℓ4 hDE hDc
    rw [eq_top_iff]
    intro z _
    have hz : h⁻¹ * z * h ∈ D := hDtop ▸ Subgroup.mem_top _
    have e2 : h * (h⁻¹ * z * h) * h⁻¹ = z := by group
    have := mem_conjPre.1 hz
    rwa [e2] at this
  · have h56 : ℓ = 5 ∨ ℓ = 6 := by omega
    obtain ⟨i, hi, q, hq, hqe⟩ := orbit_cover hF h56 hh
    set r := repData.getD i ⟨0, "", true, 0⟩ with hr
    have hy1 : (q * (h * (pathElt (repPaths.getD ℓ []))⁻¹ * h')) • w₀ = (zEl r)⁻¹ • w₀ := by
      rw [mul_smul, mul_assoc, mul_smul, mul_smul, smul_root_of_mem_Hj hM hh', ← hqe]
      rfl
    have hk : zEl r * (q * (h * (pathElt (repPaths.getD ℓ []))⁻¹ * h')) ∈ Hj := by
      apply mem_Hj_of_smul_root hF
      rw [mul_smul, hy1, smul_inv_smul]
    set k := zEl r * (q * (h * (pathElt (repPaths.getD ℓ []))⁻¹ * h')) with hkdef
    have hyq : q * (h * (pathElt (repPaths.getD ℓ []))⁻¹ * h') = (zEl r)⁻¹ * k := by
      rw [hkdef]; group
    by_cases hexc : r.exc = true
    · have hz := exc_cert hF hi hexc
      have hqz := P0_conj_z0 hM q hq
      have e : (h * (pathElt (repPaths.getD ℓ []))⁻¹ * h')⁻¹ * z0 *
          (h * (pathElt (repPaths.getD ℓ []))⁻¹ * h') =
          k⁻¹ * (zEl r * z0 * (zEl r)⁻¹) * k⁻¹⁻¹ := by
        have e0 : h * (pathElt (repPaths.getD ℓ []))⁻¹ * h' = q⁻¹ * ((zEl r)⁻¹ * k) := by
          rw [← hyq]; group
        rw [e0]
        have e1 : (q⁻¹ * ((zEl r)⁻¹ * k))⁻¹ * z0 * (q⁻¹ * ((zEl r)⁻¹ * k)) =
            k⁻¹ * zEl r * (q * z0 * q⁻¹) * (zEl r)⁻¹ * k := by group
        rw [e1, hqz]
        group
      rw [e]
      exact Hj_normalizes_Eg hM _ (Hj.inv_mem hk) _ hz
    · exfalso
      have hexc' : r.exc = false := by simpa using hexc
      apply hY
      refine genP hF hi hexc' hP (fun x hx => ?_)
      have hy' : q * (h * (pathElt (repPaths.getD ℓ []))⁻¹ * h') ∈ Y :=
        Y.mul_mem (hP hq) hy
      rw [hyq] at hy'
      have e : (zEl r)⁻¹ * x * zEl r = ((zEl r)⁻¹ * k) * (k⁻¹ * x * k) * ((zEl r)⁻¹ * k)⁻¹ := by
        group
      rw [e]
      have h2 : k⁻¹ * x * k ∈ Eg uJ 11 := by
        have := Hj_normalizes_Eg hM k⁻¹ (Hj.inv_mem hk) x hx
        rwa [inv_inv] at this
      exact Y.mul_mem (Y.mul_mem hy' (hE h2)) (Y.inv_mem hy')



theorem j4OvergroupLocal_holds [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat] : CFSG.Quasithin.J4Fam.J4OvergroupLocal := by
  have hF : J4Facts := j4Facts
  have hM := hF.mat
  refine CFSG.Quasithin.J4Fam.j4OvergroupLocal_of_normalizes fun Y hP hY _ => ?_
  have hNE : Subgroup.closure {x | ∃ y ∈ Y, x = y * z0 * y⁻¹} ≤ Eg uJ 11 := by
    rw [Subgroup.closure_le]
    rintro x ⟨y, hy, rfl⟩
    have := conj_z0_mem hF hP hY y⁻¹ (Y.inv_mem hy)
    rwa [inv_inv] at this
  refine ⟨Subgroup.closure {x | ∃ y ∈ Y, x = y * z0 * y⁻¹}, isPGroup_of_le_Eg hF hNE, ?_, ?_⟩
  · intro hbot
    have hz : z0 ∈ Subgroup.closure {x | ∃ y ∈ Y, x = y * z0 * y⁻¹} :=
      Subgroup.subset_closure ⟨1, Y.one_mem, by simp⟩
    rw [hbot, Subgroup.mem_bot] at hz
    exact z0_ne_one hM hz
  · intro y hy x hx
    induction hx using Subgroup.closure_induction with
    | mem a ha =>
      obtain ⟨y', hy', rfl⟩ := ha
      apply Subgroup.subset_closure
      exact ⟨y * y', Y.mul_mem hy hy', by group⟩
    | one => simp only [mul_one, mul_inv_cancel]; exact Subgroup.one_mem _
    | mul a b _ _ ha hb =>
      have e : y * (a * b) * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ ha hb
    | inv a _ ha =>
      have e : y * a⁻¹ * y⁻¹ = (y * a * y⁻¹)⁻¹ := by group
      rw [e]
      exact Subgroup.inv_mem _ ha

end Key

end CFSG.Quasithin.J4Ov
