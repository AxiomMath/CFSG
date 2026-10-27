module

public import CFSG.RankThree.GF2n.Stroth80.Sec93Vanish

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace HS93

theorem conj_mem_Z0 {hc : Ctx M Q Z B} {t : G} {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {ρ y : G} (hρ : ρ ∈ Rt M (LB M Q B) t)
    (hy : y ∈ Z0) : ρ * y * ρ⁻¹ ∈ Z0 := by
  obtain ⟨hyR, hyc⟩ := (hZ0 y).mp hy
  refine (hZ0 _).mpr ⟨(Rt M (LB M Q B) t).mul_mem ((Rt M (LB M Q B) t).mul_mem hρ hyR)
    ((Rt M (LB M Q B) t).inv_mem hρ), fun r' hr' => ?_⟩
  have hρM : ρ ∈ M := hc.Rt_le_M t hρ
  have hr'' : ρ⁻¹ * r' * ρ ∈ Rt M (LB M Q B) t := by
    have := (Rt M (LB M Q B) t).mul_mem ((Rt M (LB M Q B) t).mul_mem
      ((Rt M (LB M Q B) t).inv_mem hρ) hr') hρ
    exact this
  have e : ⁅ρ * y * ρ⁻¹, r'⁆ = ρ * ⁅y, ρ⁻¹ * r' * ρ⁆ * ρ⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [e]
  exact norm_Q hc hρM (hyc _ hr'')

theorem notSing_inf_conj (h1 : Step93OneStatement) (hCentre : Step95CentreStatement)
    {hc : Ctx M Q Z B} {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {r : G} (hr : Sec7A hc t r)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hsc : StronglyClosedMod M Z0 (LB M Q B)) {s z : G} (hT : Sec9T1 M Q Z0 s z) :
    ∀ u ∈ Vt M (LB M Q B) B Z t ⊓ conjSubgroup z (Vt M (LB M Q B) B Z t),
      HS9.IsSingV M Q Z B t u → u ∈ Z := by
  classical
  intro u hu hsing
  by_contra huZ
  obtain ⟨huV, huVz⟩ := hu
  obtain ⟨ρ, hρ, b, hb, hub⟩ := hsing
  obtain ⟨hZ0N, -, -⟩ := hCentre G M Q Z B hc n t hs Z0 hZ0
  have ht : t ∈ LB M Q B := hs.mem
  have hρM : ρ ∈ M := hc.Rt_le_M t hρ
  have hzM : z ∈ M := hT.z_mem
  obtain ⟨K, fK, finK, chK, γ, M₀, h⟩ := stroth_globalModelData hc.hyp
  set V := Vt M (LB M Q B) B Z t with hV
  have hZV : Z ≤ V := sec39_Z_le_Vt
  have hVQ : V ≤ Q := hc.Vt_le_Q t
  have hZQ : Z ≤ Q := hc.Z_le_Q
  set m := z⁻¹ * ρ with hm
  have hmM : m ∈ M := M.mul_mem (M.inv_mem hzM) hρM
  have hc'' : Ctx M Q Z (conjSubgroup m B) := hc.conj_of_mem hmM
  obtain ⟨e, he0, -, hline, -, -⟩ := hc''.dictB h
  have hu'V : z⁻¹ * u * z ∈ V := mem_conjSubgroup.mp huVz
  have hu'Q : z⁻¹ * u * z ∈ Q := hVQ hu'V
  have hbB : m * b * m⁻¹ ∈ conjSubgroup m B := conj_mem' m hb
  have hbQ : m * b * m⁻¹ ∈ Q := hc''.le hbB
  have hζ : u * (ρ * b * ρ⁻¹)⁻¹ ∈ Z := hub
  have hu'eq : z⁻¹ * u * z = (z⁻¹ * (u * (ρ * b * ρ⁻¹)⁻¹) * z) * (m * b * m⁻¹) := by
    simp only [hm]; group
  have hζ' : z⁻¹ * (u * (ρ * b * ρ⁻¹)⁻¹) * z ∈ Z := by
    have := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 (M.inv_mem hzM)) _).mp hζ
    simpa [mul_assoc] using this
  have hπu' : M₀.π (z⁻¹ * u * z) = M₀.π (m * b * m⁻¹) := by
    rw [hu'eq, M₀.π_mul _ (hZQ hζ') _ hbQ, (M₀.π_ker _ (hZQ hζ')).mpr hζ', zero_add]
  have hπu'ne : M₀.π (z⁻¹ * u * z) ≠ 0 := by
    intro h0
    have hz1 : z⁻¹ * u * z ∈ Z := (M₀.π_ker _ hu'Q).mp h0
    apply huZ
    have h2 := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hzM) _).mp hz1
    simpa [mul_assoc] using h2
  have hmem : M₀.π (z⁻¹ * u * z) ∈ M₀.img (conjSubgroup m B) := by
    rw [hπu']; exact M₀.pi_mem_img hbB hbQ
  obtain ⟨s₀, hs₀⟩ := (hline _).mp hmem
  have hs₀ne : s₀ ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hs₀
    exact hπu'ne hs₀
  have himg : ∀ v ∈ M₀.img (conjSubgroup m B), v ∈ M₀.img V := by
    intro v hv
    obtain ⟨c, hcv⟩ := (hline v).mp hv
    have : v = (c * s₀⁻¹) • M₀.π (z⁻¹ * u * z) := by
      rw [hs₀, smul_smul, mul_assoc, inv_mul_cancel₀ hs₀ne, mul_one, hcv]
    rw [this]
    exact hc.smul_mem_img_Vt h t _ (M₀.pi_mem_img hu'V hu'Q)
  have hB''V : conjSubgroup m B ⊔ Z ≤ V := by
    refine sup_le (fun y hy => ?_) hZV
    have hyQ : y ∈ Q := hc''.le hy
    exact (M₀.mem_img_iff hZV hyQ).mp (himg _ (M₀.pi_mem_img hy hyQ))
  obtain ⟨ρ₂, hρ₂, hρ₂eq⟩ := h1 G M Q Z B hc n t hs r hr Z0 hZ0 hsc m hmM hB''V
  have hρ₂M : ρ₂ ∈ M := hc.Rt_le_M t hρ₂
  have hLeq := hc.conj_LB_eq_of_conj_BZ hmM hρ₂M hρ₂eq
  have hsL : s ∈ conjSubgroup ρ₂ (LB M Q B) := by
    rw [mem_conjSubgroup]
    have hq : ⁅ρ₂⁻¹, s⁆ ∈ Q := by
      have h3 := ((hZ0 s).mp hT.s_mem).2 ρ₂⁻¹ ((Rt M (LB M Q B) t).inv_mem hρ₂)
      rw [← commutatorElement_inv]
      exact Q.inv_mem h3
    have e : ρ₂⁻¹ * s * ρ₂ = ⁅ρ₂⁻¹, s⁆ * s := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (LB M Q B).mul_mem (sec39_Q_le_LB hq) (hZ0N hT.s_mem).1
  have hsm : s ∈ conjSubgroup m (LB M Q B) := by rw [hLeq]; exact hsL
  have hg : (ρ⁻¹ * z) * s * (ρ⁻¹ * z)⁻¹ ∈ LB M Q B := by
    have := mem_conjSubgroup.mp hsm
    simpa [hm, mul_assoc] using this
  have hgM : ρ⁻¹ * z ∈ M := M.mul_mem (M.inv_mem hρM) hzM
  have hgZ0 := hsc s hT.s_mem (ρ⁻¹ * z) hgM hg
  apply hT.not_mem
  have hxeq : z * s * z⁻¹ = ρ * ((ρ⁻¹ * z) * s * (ρ⁻¹ * z)⁻¹) * ρ⁻¹ := by group
  rw [hxeq]
  exact conj_mem_Z0 (hc := hc) hZ0 hρ hgZ0

end HS93

end CFSG.RankThree.GF2n.Stroth80
