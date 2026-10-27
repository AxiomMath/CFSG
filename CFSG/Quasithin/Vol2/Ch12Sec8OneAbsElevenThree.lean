module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch12Sec8OneAbsEleven
public import CFSG.Quasithin.Vol2.Ch12Sec8OneAbsHat

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace L128A

namespace Setting

variable {G : Type} [Group G] [Finite G] {V V₁ L T : Subgroup G}

section

variable (S : Setting V V₁ L T)

include S

theorem exists_mem_wA_commutator_eq (D : HatModelU (uA V V₁)) (E' : Subgroup G) (ψ' : G → G)
    (hE'U : E' ≤ uA V V₁) (hVE' : V ≤ E')
    (hψ'V : ∀ y ∈ E', ψ' y ∈ V₁)
    (hψ'm : ∀ y ∈ E', ∀ y' ∈ E', ψ' (y * y') = ψ' y * ψ' y')
    (hψ'1 : ∀ v ∈ V, ψ' v = 1)
    (hψ'Z : ∀ y ∈ E', y ∈ centerOf (uA V V₁) → ψ' y = 1) :
    ∃ w ∈ wA V V₁, ∀ y ∈ E', ⁅w, y⁆ = ψ' y := by
  classical
  obtain ⟨z, hzZ, hz1, hall⟩ := S.exists_gen
  have hzz : z * z = 1 := by
    simpa [sq] using S.base.sq_eq_one_of_mem_V (S.V₁_le hzZ)
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have hψ'one : ψ' 1 = 1 := by
    have := hψ'm 1 E'.one_mem 1 E'.one_mem
    simpa using this
  have hψ'inv : ∀ y ∈ E', ψ' y⁻¹ = (ψ' y)⁻¹ := by
    intro y hy
    have h1 := hψ'm y hy y⁻¹ (E'.inv_mem hy)
    rw [mul_inv_cancel, hψ'one] at h1
    exact (eq_inv_of_mul_eq_one_right h1.symm)
  let N : Subgroup G :=
    { carrier := {y | y ∈ E' ∧ ψ' y = 1}
      mul_mem' := fun {a b} ha hb =>
        ⟨E'.mul_mem ha.1 hb.1, by rw [hψ'm a ha.1 b hb.1, ha.2, hb.2, one_mul]⟩
      one_mem' := ⟨E'.one_mem, hψ'one⟩
      inv_mem' := fun {a} ha => ⟨E'.inv_mem ha.1, by rw [hψ'inv a ha.1, ha.2, inv_one]⟩ }
  by_cases hN : ∀ y ∈ E', ψ' y = 1
  · exact ⟨1, (wA V V₁).one_mem, fun y hy => by rw [hN y hy]; group⟩
  push Not at hN
  obtain ⟨y₀, hy₀E, hy₀1⟩ := hN
  have hy₀U : y₀ ∈ uA V V₁ := hE'U hy₀E
  have hπy₀ : D.π y₀ ∉ D.hat N := by
    intro hmem
    obtain ⟨n, hnN, hnU, hn⟩ := (HatU.mem_hat D).mp hmem
    have h1 := (D.π_eq_iff n hnU y₀ hy₀U).mp hn
    have h2 : ψ' (n⁻¹ * y₀) = 1 := hψ'Z _ (E'.mul_mem (E'.inv_mem hnN.1) hy₀E) h1
    have h3 := hψ'm n hnN.1 (n⁻¹ * y₀) (E'.mul_mem (E'.inv_mem hnN.1) hy₀E)
    rw [mul_inv_cancel_left, h2, hnN.2, mul_one] at h3
    exact hy₀1 h3
  have hB : D.B.Nondegenerate :=
    ⟨fun v hv => HatU.B_nondegenerate D v hv, fun w hw =>
      HatU.B_nondegenerate D w (fun v => by rw [HatU.B_symm D]; exact hw v)⟩
  have hB₀ : D.B.IsRefl := fun v w hvw => by rw [HatU.B_symm D]; exact hvw
  have hnot : D.π y₀ ∉ D.B.orthogonal (D.B.orthogonal (D.hat N)) := by
    rw [LinearMap.BilinForm.orthogonal_orthogonal hB hB₀]
    exact hπy₀
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at hnot
  push Not at hnot
  obtain ⟨w₀, hw₀N, hw₀⟩ := hnot
  obtain ⟨w, hwU, rfl⟩ := D.π_surj w₀
  have hπN : ∀ n ∈ N, D.B (D.π w) (D.π n) = 0 := by
    intro n hn
    have := (LinearMap.BilinForm.mem_orthogonal_iff.mp hw₀N) (D.π n)
      (HatU.π_mem_hat D hn (hE'U hn.1))
    rw [HatU.B_symm D]
    exact this
  have hwW : w ∈ wA V V₁ := by
    refine ⟨hwU, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩
    have haN : a ∈ N := ⟨hVE' ha, hψ'1 a ha⟩
    have h1 := (D.B_spec w hwU a (le_uA V V₁ ha)).mp (hπN a haN)
    have h2 : w * a = a * w := by
      calc w * a = (w * a * w⁻¹ * a⁻¹) * a * w := by group
        _ = a * w := by rw [h1]; group
    exact h2.symm
  refine ⟨w, hwW, fun y hy => ?_⟩
  have hyU : y ∈ uA V V₁ := hE'U hy
  have hcomm : ⁅w, y⁆ ∈ V₁ := S.commutator_mem hwU hyU
  have hBy : D.B (D.π w) (D.π y) = 0 ↔ ⁅w, y⁆ = 1 := by
    rw [D.B_spec w hwU y hyU, commutatorElement_def]
  by_cases hyN : ψ' y = 1
  · have : D.B (D.π w) (D.π y) = 0 := hπN y ⟨hy, hyN⟩
    rw [hyN]
    exact hBy.mp this
  · have hy1 : ψ' y = z := (hall _ (hψ'V y hy)).resolve_left hyN
    have hy01 : ψ' y₀ = z := (hall _ (hψ'V y₀ hy₀E)).resolve_left hy₀1
    have hn : y₀⁻¹ * y ∈ N := by
      refine ⟨E'.mul_mem (E'.inv_mem hy₀E) hy, ?_⟩
      rw [hψ'm _ (E'.inv_mem hy₀E) _ hy, hψ'inv y₀ hy₀E, hy1, hy01, hzi, hzz]
    have hπy : D.π y = D.π y₀ + D.π (y₀⁻¹ * y) := by
      rw [← D.π_mul y₀ hy₀U (y₀⁻¹ * y) (hE'U hn.1), mul_inv_cancel_left]
    have hne : ¬ D.B (D.π w) (D.π y) = 0 := by
      rw [hπy, map_add, hπN _ hn, add_zero]
      exact hw₀
    have hcomm1 : ⁅w, y⁆ ≠ 1 := fun he => hne (hBy.mpr he)
    rw [hy1]
    exact (hall _ hcomm).resolve_left hcomm1

end

section

variable (S : Setting V V₁ L T) {g : G}
  (hg : Good V₁ L g)

include S hg

omit hg in
theorem commutator_rconj_wA_inf_le :
    ∀ x ∈ rconj (wA V V₁) g, ∀ e ∈ wA V V₁ ⊓ rconj (wA V V₁) g,
      x * e * x⁻¹ * e⁻¹ ∈ rconj (V₁) g := by
  intro x hx e he
  have hxUg : x ∈ rconj (uA V V₁) g := rconj_le_rconj (wA_le_uA V V₁) g hx
  have heUg : e ∈ rconj (uA V V₁) g := rconj_le_rconj (wA_le_uA V V₁) g he.2
  rw [mem_rconj]
  have h1 := S.commutator_mem (mem_rconj.mp hxUg) (mem_rconj.mp heUg)
  have e1 : g * (x * e * x⁻¹ * e⁻¹) * g⁻¹ =
      (g * x * g⁻¹) * (g * e * g⁻¹) * (g * x * g⁻¹)⁻¹ * (g * e * g⁻¹)⁻¹ := by group
  rw [e1]
  exact h1

theorem eleven_three (D : HatModelU (uA V V₁)) (ψ : G → G)
    (hψV : ∀ e ∈ wA V V₁ ⊓ rconj (wA V V₁) g, ψ e ∈ rconj (V₁) g)
    (hψm : ∀ e ∈ wA V V₁ ⊓ rconj (wA V V₁) g, ∀ e' ∈ wA V V₁ ⊓ rconj (wA V V₁) g,
      ψ (e * e') = ψ e * ψ e')
    (hψ1 : ∀ v ∈ V, ψ v = 1)
    (hψZ : ∀ e ∈ wA V V₁ ⊓ rconj (wA V V₁) g, e ∈ centerOf (uA V V₁) → ψ e = 1) :
    ∃ x ∈ rconj (wA V V₁) g, ∀ e ∈ wA V V₁ ⊓ rconj (wA V V₁) g,
      x * e * x⁻¹ * e⁻¹ = ψ e := by
  have hE : wA V V₁ ⊓ rconj (wA V V₁) g = uA V V₁ ⊓ rconj (uA V V₁) g :=
    S.wA_inf_rconj_eq hg
  have hVE : V ≤ wA V V₁ ⊓ rconj (wA V V₁) g := S.thirteen_one hg
  have hgN : g ∈ Subgroup.normalizer (V : Set G) :=
    ((le_sup_left : L ≤ L ⊔ T).trans S.LT_le_normalizer_V) hg.mem
  have hgV : ∀ v ∈ V, g⁻¹ * v * g ∈ V := fun v hv => by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgN) v).mp hv
    simpa using this
  have hbackE : ∀ y ∈ rconj (wA V V₁ ⊓ rconj (wA V V₁) g) g⁻¹,
      g⁻¹ * y * g ∈ wA V V₁ ⊓ rconj (wA V V₁) g := fun y hy => by
    have := mem_rconj.mp hy
    simpa using this
  have hfwdE : ∀ e ∈ wA V V₁ ⊓ rconj (wA V V₁) g,
      g * e * g⁻¹ ∈ rconj (wA V V₁ ⊓ rconj (wA V V₁) g) g⁻¹ := fun e he => by
    rw [mem_rconj]
    have e1 : g⁻¹ * (g * e * g⁻¹) * g⁻¹⁻¹ = e := by group
    rw [e1]
    exact he
  have hE'W : ∀ y ∈ rconj (wA V V₁ ⊓ rconj (wA V V₁) g) g⁻¹, y ∈ wA V V₁ := fun y hy => by
    have h2 := mem_rconj.mp (hbackE y hy).2
    have e1 : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
    rwa [e1] at h2
  obtain ⟨w, hwW, hw⟩ := S.exists_mem_wA_commutator_eq D
    (rconj (wA V V₁ ⊓ rconj (wA V V₁) g) g⁻¹) (fun y => g * ψ (g⁻¹ * y * g) * g⁻¹)
    (fun y hy => wA_le_uA V V₁ (hE'W y hy))
    (fun v hv => by
      rw [mem_rconj, inv_inv]
      exact hVE (hgV v hv))
    (fun y hy => mem_rconj.mp (hψV _ (hbackE y hy)))
    (fun y hy y' hy' => by
      have e1 : g⁻¹ * (y * y') * g = (g⁻¹ * y * g) * (g⁻¹ * y' * g) := by group
      show g * ψ (g⁻¹ * (y * y') * g) * g⁻¹ =
        (g * ψ (g⁻¹ * y * g) * g⁻¹) * (g * ψ (g⁻¹ * y' * g) * g⁻¹)
      rw [e1, hψm _ (hbackE y hy) _ (hbackE y' hy')]
      group)
    (fun v hv => by
      show g * ψ (g⁻¹ * v * g) * g⁻¹ = 1
      rw [hψ1 _ (hgV v hv)]
      group)
    (fun y hy hyZ => by
      show g * ψ (g⁻¹ * y * g) * g⁻¹ = 1
      have heE := hbackE y hy
      have heZ : g⁻¹ * y * g ∈ rconj (centerOf (uA V V₁)) g := by
        rw [mem_rconj]
        have e1 : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
        rw [e1]
        exact hyZ
      have heU : g⁻¹ * y * g ∈ uA V V₁ := by
        rw [hE] at heE
        exact heE.1
      have h3 : g⁻¹ * y * g ∈ rconj (centerOf (uA V V₁)) g ⊓ uA V V₁ := ⟨heZ, heU⟩
      rw [S.ten_one_symm hg] at h3
      have hV₁gV : rconj V₁ g ≤ V := S.l2Setting.V₁_le_rconj_V hg.mem
      obtain ⟨c, hc, v, hv, hcv⟩ := exists_eq_mul_of_mem_sup_of_forall_commute
        (A := centerOf (uA V V₁) ⊓ rconj (centerOf (uA V V₁)) g) (B := rconj V₁ g)
        (fun c hc v hv => (Subgroup.mem_centralizer_iff.mp hc.1.2 v
          (le_uA V V₁ (hV₁gV hv))).symm) h3
      have hcE : c ∈ wA V V₁ ⊓ rconj (wA V V₁) g :=
        ⟨centerOf_uA_le_wA V V₁ hc.1, rconj_centerOf_le_rconj_wA V V₁ g hc.2⟩
      have hvE : v ∈ wA V V₁ ⊓ rconj (wA V V₁) g := hVE (hV₁gV hv)
      rw [← hcv, hψm c hcE v hvE, hψZ c hcE hc.1, hψ1 v (hV₁gV hv)]
      group)
  refine ⟨g⁻¹ * w * g, inv_mul_mul_mem_rconj hwW, fun e he => ?_⟩
  have h1 := hw (g * e * g⁻¹) (hfwdE e he)
  have e1 : g⁻¹ * (g * e * g⁻¹) * g = e := by group
  simp only [e1] at h1
  calc g⁻¹ * w * g * e * (g⁻¹ * w * g)⁻¹ * e⁻¹ = g⁻¹ * ⁅w, g * e * g⁻¹⁆ * g := by
        simp only [commutatorElement_def]
        group
    _ = g⁻¹ * (g * ψ e * g⁻¹) * g := by rw [h1]
    _ = ψ e := by group

end

end Setting

end L128A

end CFSG.Quasithin.H13
