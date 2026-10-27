module

public import CFSG.RankThree.GF2n.Stroth80.Sec5Vt
public import CFSG.RankThree.GF2n.Stroth80.Sec5Model
public import CFSG.RankThree.GF2n.Stroth80.Sec34Model
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.GF2n.Stroth80.Sec7Basic

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

omit [Finite G] in
theorem quadModel_B_iso {K : Type} [Field K] {γ : G → K} (M₀ : Tim79.QuadModel Q Z K γ)
    (T : M₀.E ≃ₗ[K] M₀.E) (hT : ∀ e, M₀.Qf (T e) = M₀.Qf e) (e f : M₀.E) :
    M₀.B (T e) (T f) = M₀.B e f := by
  have h1 := M₀.Qf_add (T e) (T f)
  have h2 := M₀.Qf_add e f
  rw [← map_add, hT, hT, hT] at h1
  linear_combination h2 - h1

omit [Finite G] in
theorem mem_of_pi_mem_img {K : Type} [Field K] {γ : G → K} (M₀ : Tim79.QuadModel Q Z K γ)
    {S : Subgroup G} (hZS : Z ≤ S) {w : G} (hwQ : w ∈ Q) (h : M₀.π w ∈ M₀.img S) : w ∈ S := by
  obtain ⟨w', hw'S, hw'Q, hw'⟩ := h
  have h1 : M₀.π (w' * (w'⁻¹ * w)) = M₀.π w' + M₀.π (w'⁻¹ * w) :=
    M₀.π_mul _ hw'Q _ (Q.mul_mem (Q.inv_mem hw'Q) hwQ)
  have h2 : w' * (w'⁻¹ * w) = w := by group
  rw [h2, hw'] at h1
  have h3 : M₀.π (w'⁻¹ * w) = 0 := by
    have := h1
    simpa using this
  have hz : w'⁻¹ * w ∈ Z := (M₀.π_ker _ (Q.mul_mem (Q.inv_mem hw'Q) hwQ)).mp h3
  have e : w = w' * (w'⁻¹ * w) := h2.symm
  rw [e]
  exact S.mul_mem hw'S (hZS hz)

theorem commZ0_mem_Q_of_centralizes_Vt (hc : Ctx M Q Z B) {t : G} {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hW : ∀ z ∈ Z0, ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅z, w⁆ ∈ Z)
    (hZV : ∀ u ∈ Z0, u ∉ Q → Ut Q Z u = Vt M (LB M Q B) B Z t)
    {x : G} (hxH : x ∈ H0 M Z) (hxV : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅x, v⁆ ∈ Z) :
    ∀ z ∈ Z0, ⁅z, x⁆ ∈ Q := by
  classical
  obtain ⟨K, fK, finK, chK, γ, M₀, h⟩ := stroth_globalModelData hc.hyp
  obtain ⟨φ, hφπ, hφker, hφQ⟩ := exists_actionHom_H0 hc.hyp h
  set V := Vt M (LB M Q B) B Z t with hV
  have hVQ : V ≤ Q := hc.Vt_le_Q t
  have hZQ : Z ≤ Q := hc.Z_le_Q
  have hQM : Q ≤ M := hc.hyp.Q_normal.1
  have hQn : ∀ m ∈ M, ∀ y ∈ Q, m * y * m⁻¹ ∈ Q := fun m hm y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hm) y).mp hy
  have hZ0H : Z0 ≤ H0 M Z := hZ0.le.trans (hc.Rt_le_H0 t)
  have hB : ∀ (m : ↥(H0 M Z)) (e f : M₀.E), M₀.B (φ m e) (φ m f) = M₀.B e f :=
    fun m => quadModel_B_iso M₀ (φ m) (hφQ m)
  intro z hz
  by_cases hzQ : z ∈ Q
  · have hxM : x ∈ M := hxH.1
    have := Q.mul_mem hzQ (Q.inv_mem (hQn x hxM z hzQ))
    have e : ⁅z, x⁆ = z * (x * z * x⁻¹)⁻¹ := by simp only [commutatorElement_def]; group
    rw [e]
    exact this
  · set xH : ↥(H0 M Z) := ⟨x, hxH⟩ with hxHdef
    set zH : ↥(H0 M Z) := ⟨z, hZ0H hz⟩ with hzHdef
    have hxM : x ∈ M := hxH.1
    have hzM : z ∈ M := (hZ0H hz).1
    have hUz := hZV z hz hzQ
    have ha : ∀ e, φ zH e - e ∈ M₀.img V := by
      intro e
      obtain ⟨y, hyQ, rfl⟩ := M₀.π_surj e
      have h1 : z * y * z⁻¹ ∈ Q := hQn z hzM y hyQ
      have hc1 : ⁅z, y⁆ ∈ Q := by
        have := Q.mul_mem h1 (Q.inv_mem hyQ)
        simpa [commutatorElement_def, mul_assoc] using this
      have hcV : ⁅z, y⁆ ∈ V := by
        have h2 : ⁅y, z⁆ ∈ Ut Q Z z := comm_mem_Ut hyQ
        rw [hUz] at h2
        have := V.inv_mem h2
        rwa [commutatorElement_inv] at this
      have e1 : z * y * z⁻¹ = ⁅z, y⁆ * y := by simp only [commutatorElement_def]; group
      have e2 : M₀.π (z * y * z⁻¹) = M₀.π ⁅z, y⁆ + M₀.π y := by
        rw [e1]; exact M₀.π_mul _ hc1 _ hyQ
      rw [← hφπ zH y hyQ, e2, add_sub_cancel_right]
      exact M₀.pi_mem_img hcV hc1
    have hb : ∀ e ∈ M₀.img (Wt Q V), φ zH e = e := by
      rintro _ ⟨w, hwW, hwQ, rfl⟩
      have hzw := hW z hz w hwW
      have h1 : z * w * z⁻¹ = ⁅z, w⁆ * w := by simp only [commutatorElement_def]; group
      have hzwQ : ⁅z, w⁆ ∈ Q := hZQ hzw
      have h2 : M₀.π (z * w * z⁻¹) = M₀.π ⁅z, w⁆ + M₀.π w := by
        rw [h1]; exact M₀.π_mul _ hzwQ _ hwQ
      have h3 : M₀.π ⁅z, w⁆ = 0 := (M₀.π_ker _ hzwQ).mpr hzw
      rw [← hφπ zH w hwQ, h2, h3, zero_add]
    have hc' : ∀ e ∈ M₀.img V, φ xH e = e := by
      rintro _ ⟨v, hvV, hvQ, rfl⟩
      have hxv := hxV v hvV
      have h1 : x * v * x⁻¹ = ⁅x, v⁆ * v := by simp only [commutatorElement_def]; group
      have hxvQ : ⁅x, v⁆ ∈ Q := hZQ hxv
      have h2 : M₀.π (x * v * x⁻¹) = M₀.π ⁅x, v⁆ + M₀.π v := by
        rw [h1]; exact M₀.π_mul _ hxvQ _ hvQ
      have h3 : M₀.π ⁅x, v⁆ = 0 := (M₀.π_ker _ hxvQ).mpr hxv
      rw [← hφπ xH v hvQ, h2, h3, zero_add]
    have hd : ∀ e, e - φ xH e ∈ M₀.img (Wt Q V) := by
      intro e
      rw [mem_img_Wt_iff M₀ h.reg hVQ]
      intro v hv
      have hfix := hc' v hv
      have h1 : M₀.B (φ xH e) v = M₀.B e v := by
        have := hB xH e v
        rwa [hfix] at this
      rw [map_sub, LinearMap.sub_apply, h1, sub_self]
    have hcomm : ∀ e, φ zH (φ xH e) = φ xH (φ zH e) := by
      intro e
      have h1 : φ zH (e - φ xH e) = e - φ xH e := hb _ (hd e)
      have h2 : φ xH (φ zH e - e) = φ zH e - e := hc' _ (ha e)
      rw [map_sub] at h1 h2
      have h3 : φ zH e - φ zH (φ xH e) = e - φ xH e := h1
      have h4 : φ xH (φ zH e) - φ xH e = φ zH e - e := h2
      calc φ zH (φ xH e) = φ zH e - (φ zH e - φ zH (φ xH e)) := by abel
        _ = φ zH e - (e - φ xH e) := by rw [h3]
        _ = (φ zH e - e) + φ xH e := by abel
        _ = (φ xH (φ zH e) - φ xH e) + φ xH e := by rw [h4]
        _ = φ xH (φ zH e) := by abel
    have hker : φ (xH * zH * xH⁻¹ * zH⁻¹) = 1 := by
      have : φ xH * φ zH = φ zH * φ xH := by
        refine LinearEquiv.ext fun e => ?_
        exact (hcomm e).symm
      simp only [map_mul, map_inv]
      rw [this]
      group
    have hmem := (hφker _).mp hker
    have hmem' : ⁅x, z⁆ ∈ Q := by
      simpa [commutatorElement_def, hxHdef, hzHdef] using hmem
    have := Q.inv_mem hmem'
    rwa [commutatorElement_inv] at this

theorem Ut_le_Wt_of_fixes (hc : Ctx M Q Z B) {V₁ : Subgroup G} (hV₁Q : V₁ ≤ Q) {x : G}
    (hxH : x ∈ H0 M Z) (hx : ∀ v ∈ V₁, ⁅x, v⁆ ∈ Z) : Ut Q Z x ≤ Wt Q V₁ := by
  classical
  obtain ⟨K, fK, finK, chK, γ, M₀, h⟩ := stroth_globalModelData hc.hyp
  obtain ⟨φ, hφπ, hφker, hφQ⟩ := exists_actionHom_H0 hc.hyp h
  have hZQ : Z ≤ Q := hc.Z_le_Q
  have hxM : x ∈ M := hxH.1
  have hQn : ∀ m ∈ M, ∀ y ∈ Q, m * y * m⁻¹ ∈ Q := fun m hm y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hm) y).mp hy
  set xH : ↥(H0 M Z) := ⟨x, hxH⟩ with hxHdef
  intro w hw
  have hwQ : w ∈ Q := hc.Ut_le_Q hxM hw
  have hmem : M₀.π w ∈ LinearMap.range ((φ xH : M₀.E →ₗ[K] M₀.E) - 1) :=
    (mem_img_comm_zpowers_sup_iff M₀ h.reg (φ xH) (hQn x hxM) (by
      have := hQn x⁻¹ (M.inv_mem hxM)
      simpa using this) (fun y hy => hφπ xH y hy) (M₀.π w)).mp ⟨w, hw, hwQ, rfl⟩
  obtain ⟨e', he'⟩ := hmem
  have hZW : Z ≤ Wt Q V₁ := fun z hz =>
    ⟨hZQ hz, Subgroup.mem_centralizer_iff.mpr fun v hv =>
      (hc.hyp.toHyp79.V_central hz (hV₁Q hv)).symm⟩
  refine mem_of_pi_mem_img M₀ hZW hwQ ((mem_img_Wt_iff M₀ h.reg hV₁Q).mpr ?_)
  rintro _ ⟨v, hv, hvQ, rfl⟩
  have hfix : φ xH (M₀.π v) = M₀.π v := by
    have hxv := hx v hv
    have hxvQ : ⁅x, v⁆ ∈ Q := hZQ hxv
    have h1 : x * v * x⁻¹ = ⁅x, v⁆ * v := by simp only [commutatorElement_def]; group
    have h2 : M₀.π (x * v * x⁻¹) = M₀.π ⁅x, v⁆ + M₀.π v := by
      rw [h1]; exact M₀.π_mul _ hxvQ _ hvQ
    have h3 : M₀.π ⁅x, v⁆ = 0 := (M₀.π_ker _ hxvQ).mpr hxv
    rw [← hφπ xH v hvQ, h2, h3, zero_add]
  rw [← he']
  have hiso := quadModel_B_iso M₀ (φ xH) (hφQ xH) e' (M₀.π v)
  rw [hfix] at hiso
  show M₀.B ((φ xH) e' - e') (M₀.π v) = 0
  rw [map_sub, LinearMap.sub_apply, hiso, sub_self]

end CFSG.RankThree.GF2n.Stroth80
