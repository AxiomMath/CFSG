module

public import CFSG.Quasithin.Vol2.Ch12Sec8NonabHat
public import CFSG.Quasithin.Vol2.Ch12Sec8NonabThirteen

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {T M L : Subgroup G}

namespace Hyp1281Two

section

variable (h : Hyp1281Two G T M L) (hU : ¬ IsMulCommutative ↥(uOfL22 T M))

include h hU

omit hU in
theorem exists_mem_wOfU_commutator_eq (E' : Subgroup G) (ψ' : G → G)
    (hE'U : E' ≤ uOfL22 T M) (hVE' : VZ T M ≤ E')
    (hψ'V : ∀ y ∈ E', ψ' y ∈ quasithinOmegaOneCenter T)
    (hψ'm : ∀ y ∈ E', ∀ y' ∈ E', ψ' (y * y') = ψ' y * ψ' y')
    (hψ'1 : ∀ v ∈ VZ T M, ψ' v = 1)
    (hψ'Z : ∀ y ∈ E', y ∈ centerOf (uOfL22 T M) → ψ' y = 1) :
    ∃ w ∈ wOfU T M, ∀ y ∈ E', ⁅w, y⁆ = ψ' y := by
  classical
  obtain ⟨D⟩ := h.exists_hatModel
  obtain ⟨z, hzZ, hz1, hall⟩ := h.exists_zgen
  have hzz : z * z = 1 := by
    simpa [sq] using h.almostSpecialHyp_g1.sq_eq_one_of_mem_V (omegaOneCenter_le_VZ T M hzZ)
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
  · exact ⟨1, (wOfU T M).one_mem, fun y hy => by rw [hN y hy]; group⟩
  push Not at hN
  obtain ⟨y₀, hy₀E, hy₀1⟩ := hN
  have hy₀U : y₀ ∈ uOfL22 T M := hE'U hy₀E
  have hπy₀ : D.π y₀ ∉ D.hat N := by
    intro hmem
    obtain ⟨n, hnN, hnU, hn⟩ := D.mem_hat.mp hmem
    have h1 := (D.π_eq_iff n hnU y₀ hy₀U).mp hn
    have h2 : ψ' (n⁻¹ * y₀) = 1 := hψ'Z _ (E'.mul_mem (E'.inv_mem hnN.1) hy₀E) h1
    have h3 := hψ'm n hnN.1 (n⁻¹ * y₀) (E'.mul_mem (E'.inv_mem hnN.1) hy₀E)
    rw [mul_inv_cancel_left, h2, hnN.2, mul_one] at h3
    exact hy₀1 h3
  have hB : D.B.Nondegenerate :=
    ⟨fun v hv => D.B_nondegenerate v hv, fun w hw =>
      D.B_nondegenerate w (fun v => by rw [D.B_symm]; exact hw v)⟩
  have hB₀ : D.B.IsRefl := fun v w hvw => by rw [D.B_symm]; exact hvw
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
      (D.π_mem_hat hn (hE'U hn.1))
    rw [D.B_symm]
    exact this
  have hwW : w ∈ wOfU T M := by
    refine ⟨hwU, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩
    have haN : a ∈ N := ⟨hVE' ha, hψ'1 a ha⟩
    have h1 := (D.B_spec w hwU a (VZ_le_uOfL22 T M ha)).mp (hπN a haN)
    have h2 : w * a = a * w := by
      calc w * a = (w * a * w⁻¹ * a⁻¹) * a * w := by group
        _ = a * w := by rw [h1]; group
    exact h2.symm
  refine ⟨w, hwW, fun y hy => ?_⟩
  have hyU : y ∈ uOfL22 T M := hE'U hy
  have hcomm : ⁅w, y⁆ ∈ quasithinOmegaOneCenter T := h.commutator_mem_omegaOneCenter hwU hyU
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

variable (h : Hyp1281Two G T M L) (hU : ¬ IsMulCommutative ↥(uOfL22 T M)) {g : G}
  (hg : GoodElt128 T L g)

include h hU hg

omit hU hg in
theorem commutator_rconj_wOfU_inf_le :
    ∀ x ∈ rconj (wOfU T M) g, ∀ e ∈ wOfU T M ⊓ rconj (wOfU T M) g,
      x * e * x⁻¹ * e⁻¹ ∈ rconj (quasithinOmegaOneCenter T) g := by
  intro x hx e he
  have hxUg : x ∈ rconj (uOfL22 T M) g := rconj_le_rconj (wOfU_le_uOfL22 T M) g hx
  have heUg : e ∈ rconj (uOfL22 T M) g := rconj_le_rconj (wOfU_le_uOfL22 T M) g he.2
  rw [mem_rconj]
  have h1 := h.commutator_mem_omegaOneCenter (mem_rconj.mp hxUg) (mem_rconj.mp heUg)
  have e1 : g * (x * e * x⁻¹ * e⁻¹) * g⁻¹ =
      (g * x * g⁻¹) * (g * e * g⁻¹) * (g * x * g⁻¹)⁻¹ * (g * e * g⁻¹)⁻¹ := by group
  rw [e1]
  exact h1

theorem lemma_12_8_11_three (ψ : G → G)
    (hψV : ∀ e ∈ wOfU T M ⊓ rconj (wOfU T M) g, ψ e ∈ rconj (quasithinOmegaOneCenter T) g)
    (hψm : ∀ e ∈ wOfU T M ⊓ rconj (wOfU T M) g, ∀ e' ∈ wOfU T M ⊓ rconj (wOfU T M) g,
      ψ (e * e') = ψ e * ψ e')
    (hψ1 : ∀ v ∈ VZ T M, ψ v = 1) :
    ∃ x ∈ rconj (wOfU T M) g, ∀ e ∈ wOfU T M ⊓ rconj (wOfU T M) g,
      x * e * x⁻¹ * e⁻¹ = ψ e := by
  have hE : wOfU T M ⊓ rconj (wOfU T M) g = uOfL22 T M ⊓ rconj (uOfL22 T M) g :=
    h.wOfU_inf_rconj_eq hU hg
  have hVE : VZ T M ≤ wOfU T M ⊓ rconj (wOfU T M) g := h.lemma_12_8_13_one hU hg
  have hgN : g ∈ Subgroup.normalizer (VZ T M : Set G) :=
    ((le_sup_left : L ≤ L ⊔ T).trans h.LT_le_normalizer_VZ) hg.mem
  have hgV : ∀ v ∈ VZ T M, g⁻¹ * v * g ∈ VZ T M := fun v hv => by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgN) v).mp hv
    simpa using this
  have hbackE : ∀ y ∈ rconj (wOfU T M ⊓ rconj (wOfU T M) g) g⁻¹,
      g⁻¹ * y * g ∈ wOfU T M ⊓ rconj (wOfU T M) g := fun y hy => by
    have := mem_rconj.mp hy
    simpa using this
  have hfwdE : ∀ e ∈ wOfU T M ⊓ rconj (wOfU T M) g,
      g * e * g⁻¹ ∈ rconj (wOfU T M ⊓ rconj (wOfU T M) g) g⁻¹ := fun e he => by
    rw [mem_rconj]
    have e1 : g⁻¹ * (g * e * g⁻¹) * g⁻¹⁻¹ = e := by group
    rw [e1]
    exact he
  have hE'W : ∀ y ∈ rconj (wOfU T M ⊓ rconj (wOfU T M) g) g⁻¹, y ∈ wOfU T M := fun y hy => by
    have h2 := mem_rconj.mp (hbackE y hy).2
    have e1 : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
    rwa [e1] at h2
  obtain ⟨w, hwW, hw⟩ := h.exists_mem_wOfU_commutator_eq
    (rconj (wOfU T M ⊓ rconj (wOfU T M) g) g⁻¹) (fun y => g * ψ (g⁻¹ * y * g) * g⁻¹)
    (fun y hy => wOfU_le_uOfL22 T M (hE'W y hy))
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
      have heZ : g⁻¹ * y * g ∈ rconj (centerOf (uOfL22 T M)) g := by
        rw [mem_rconj]
        have e1 : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
        rw [e1]
        exact hyZ
      have heU : g⁻¹ * y * g ∈ uOfL22 T M := by
        rw [hE] at heE
        exact heE.1
      have h3 : g⁻¹ * y * g ∈ rconj (centerOf (uOfL22 T M)) g ⊓ uOfL22 T M := ⟨heZ, heU⟩
      rw [h.lemma_12_8_10_one_symm hU hg, h.centerOf_inf_rconj_centerOf_eq_bot hU hg,
        bot_sup_eq] at h3
      rw [hψ1 _ ((h.l2Setting128 hU).V₁_le_rconj_V hg.mem h3)]
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

end Hyp1281Two

end CFSG.Quasithin
