module

public import CFSG.Quasithin.Vol2.Ch6Sec2Lem5D

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G}

namespace Hyp6Sec2

variable (h : Hyp6Sec2 G T M L V)
include h

theorem isCentralType_of_isLine625 {F : Subgroup G} (hFV : F ≤ V) (hF4 : Nat.card F = 4)
    {v : Fin 2 → h.data.K} (hL : h.IsLine625 F v) : IsCentralType L V F 1 :=
  (h.isCentralType_iff_ch625 hFV hF4).mpr (h.exists_conj_ZS_of_isLine625 hFV hL)

theorem isPlane625_of_not_central {F : Subgroup G} (hFV : F ≤ V) (hF4 : Nat.card F = 4)
    (hF : ¬ IsCentralType L V F 1) : ∃ x y, h.IsPlane625 F x y := by
  rcases h.four_cases_ch625 hFV hF4 with ⟨v, hv⟩ | hP
  · exact absurd (h.isCentralType_of_isLine625 hFV hF4 hv) hF
  · exact hP

theorem not_central_of_isPlane625 {F : Subgroup G} (hFV : F ≤ V) (hF4 : Nat.card F = 4)
    {x y : Fin 2 → h.data.K} (hP : h.IsPlane625 F x y) : ¬ IsCentralType L V F 1 := by
  intro hc
  obtain ⟨l, hl, rfl⟩ := (h.isCentralType_iff_ch625 hFV hF4).mp hc
  obtain ⟨v, hv⟩ := h.exists_isLine625_conj_ZS hl
  exact h.not_isLine625_of_isPlane625 hP hv

theorem conj_fix_of_mem_centralizer {F : Subgroup G} {t : G}
    (htN : t ∈ Subgroup.normalizer (V : Set G)) (htF : t ∈ Subgroup.centralizer (F : Set G))
    {w : Fin 2 → h.data.K} (hw : h.vec625 w ∈ F) : h.data.conj ⟨t, htN⟩ w = w := by
  apply h.vec625_injective
  rw [← h.conj_vec625]
  have := Subgroup.mem_centralizer_iff.mp htF _ hw
  calc t * h.vec625 w * t⁻¹ = h.vec625 w * t * t⁻¹ := by rw [← this]
    _ = h.vec625 w := by group

theorem not_isFieldType_of_isLine625 {F : Subgroup G} (hFV : F ≤ V) (hF4 : Nat.card F = 4)
    {v : Fin 2 → h.data.K} (hL : h.IsLine625 F v) : ¬ IsFieldType M L V F 1 := by
  have hK := h.card_K_ch625
  intro hf
  obtain ⟨t, htM, htF, htN, hlin⟩ := (h.isFieldType_iff_ch625 hFV hF4).mp hf
  have hfrob := (h.semilinear_cases_ch625 ⟨t, htN⟩ (h.normal htM.1)).resolve_left hlin
  obtain ⟨ω, hω⟩ : ∃ ω : h.data.K, ω ^ 2 ≠ ω := by
    by_contra hcon
    push Not at hcon
    have hsub : ∀ c : h.data.K, c = 0 ∨ c = 1 := fun c => by
      rcases sq_add_self_ch625 hK c with h0 | h0
      · exact eq_zero_or_one_ch625 hK h0
      · exfalso
        rw [hcon c, add_self_ch625 hK] at h0
        exact zero_ne_one h0
    have := Fintype.ofFinite h.data.K
    have hcard : Fintype.card h.data.K ≤ 2 := by
      classical
      calc Fintype.card h.data.K = (Finset.univ : Finset h.data.K).card := rfl
        _ ≤ ({0, 1} : Finset h.data.K).card := Finset.card_le_card fun c _ => by
            rcases hsub c with rfl | rfl <;> simp
        _ ≤ 2 := Finset.card_le_two
    rw [← Nat.card_eq_fintype_card, hK] at hcard
    omega
  have h1 := h.conj_fix_of_mem_centralizer htN htF ((hL.2 (ω • v)).mpr ⟨ω, rfl⟩)
  rw [hfrob, h.conj_fix_of_mem_centralizer htN htF ((hL.2 v).mpr ⟨1, (one_smul _ v).symm⟩)]
    at h1
  apply hω
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hL.1
  have := congrFun h1 i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this hi
  exact mul_right_cancel₀ hi this

theorem eq_conjSubgroup_of_isPlane625 {F F' : Subgroup G} (hFV : F ≤ V) (hF'V : F' ≤ V)
    {x y x' y' : Fin 2 → h.data.K} (hP : h.IsPlane625 F x y) (hP' : h.IsPlane625 F' x' y')
    (m : Subgroup.normalizer (V : Set G)) (hx : h.data.conj m x' = x)
    (hy : h.data.conj m y' = y) : F' = conjSubgroup F m := by
  have hP'' := h.isPlane625_conjSubgroup hP m hx hy hP'.1
  have hmV : conjSubgroup V m = V := conjSubgroup_eq_iff_mem_normalizer.mpr m.2
  have hFmV : conjSubgroup F m ≤ V := by
    have := conjSubgroup_mono_left (m : G) hFV
    rwa [hmV] at this
  exact h.eq_of_vec625_iff hF'V hFmV fun w => (hP'.2 w).trans (hP''.2 w).symm

theorem det625_eq_inv_of_fix {t : Subgroup.normalizer (V : Set G)}
    (htL : (t : G) ∈ Subgroup.normalizer (L : Set G)) (hlin : ¬ h.IsLin625 t)
    {x y : Fin 2 → h.data.K} (hxy : det2 x y ≠ 0) (hx : h.data.conj t x = x)
    (hy : h.data.conj t y = y) : h.det625 t = (det2 x y)⁻¹ := by
  have hfrob := (h.semilinear_cases_ch625 t htL).resolve_left hlin
  have h1 := h.det2_conj_frob_ch625 hfrob x y
  rw [hx, hy] at h1
  have h2 : det2 x y * h.det625 t = 1 := by
    have e : det2 x y ^ 2 * h.det625 t = det2 x y * (det2 x y * h.det625 t) := by ring
    rw [e] at h1
    exact mul_left_cancel₀ hxy (h1.symm.trans (mul_one _).symm)
  exact eq_inv_of_mul_eq_one_right h2

theorem not_isLin625_mul {l t : Subgroup.normalizer (V : Set G)} (hl : h.IsLin625 l)
    (ht : ¬ h.IsLin625 t) : ¬ h.IsLin625 (l * t) := by
  intro hlt
  apply ht
  intro c w
  have e : l⁻¹ * (l * t) = t := by group
  calc h.data.conj t (c • w) = h.data.conj (l⁻¹ * (l * t)) (c • w) := by rw [e]
    _ = h.data.conj l⁻¹ (h.data.conj (l * t) (c • w)) := h.data.conj_mul _ _ _
    _ = c • h.data.conj l⁻¹ (h.data.conj (l * t) w) := by rw [hlt, h.isLin625_inv hl]
    _ = c • h.data.conj (l⁻¹ * (l * t)) w := by rw [h.data.conj_mul l⁻¹ (l * t)]
    _ = c • h.data.conj t w := by rw [e]

theorem isFieldType_of_isPlane625 {F : Subgroup G} (hFV : F ≤ V) (hF4 : Nat.card F = 4)
    {x y : Fin 2 → h.data.K} (hP : h.IsPlane625 F x y) {t₀ : G} (ht₀M : t₀ ∈ ch6MV M V)
    (ht₀ : ¬ h.IsLin625 ⟨t₀, ht₀M.2⟩) {l : Subgroup.normalizer (V : Set G)}
    (hlM : (l : G) ∈ ch6MV M V) (hllin : h.IsLin625 l)
    (hlx : h.data.conj l (h.data.conj ⟨t₀, ht₀M.2⟩ x) = x)
    (hly : h.data.conj l (h.data.conj ⟨t₀, ht₀M.2⟩ y) = y) : IsFieldType M L V F 1 := by
  set m : Subgroup.normalizer (V : Set G) := l * ⟨t₀, ht₀M.2⟩ with hm
  have hmM : (m : G) ∈ ch6MV M V := (ch6MV M V).mul_mem hlM ht₀M
  have hmx : h.data.conj m x = x := by rw [hm, h.data.conj_mul, hlx]
  have hmy : h.data.conj m y = y := by rw [hm, h.data.conj_mul, hly]
  refine (h.isFieldType_iff_ch625 hFV hF4).mpr ⟨m, hmM, ?_, m.2, h.not_isLin625_mul hllin ht₀⟩
  refine Subgroup.mem_centralizer_iff.mpr fun f hf => ?_
  obtain ⟨w, rfl⟩ := h.exists_vec625_eq (hFV hf)
  have hw : h.data.conj m w = w := by
    rcases (hP.2 w).mp hf with rfl | rfl | rfl | rfl
    · exact map_zero _
    · exact hmx
    · exact hmy
    · rw [map_add, hmx, hmy]
  have h1 := h.conj_vec625 m w
  rw [hw] at h1
  calc h.vec625 w * m = ((m : G) * h.vec625 w * (m : G)⁻¹) * m := by rw [h1]
    _ = m * h.vec625 w := by group

theorem exists_conj_of_central {F F' : Subgroup G} (hFV : F ≤ V) (hF4 : Nat.card F = 4)
    (hF'V : F' ≤ V) (hF'4 : Nat.card F' = 4) (hF : IsCentralType L V F 1)
    (hF' : IsCentralType L V F' 1) : ∃ m ∈ ch6MV M V, F' = conjSubgroup F m := by
  obtain ⟨l, hl, rfl⟩ := (h.isCentralType_iff_ch625 hFV hF4).mp hF
  obtain ⟨l', hl', rfl⟩ := (h.isCentralType_iff_ch625 hF'V hF'4).mp hF'
  refine ⟨l⁻¹ * l', h.L_le_MV_ch625 (L.mul_mem (L.inv_mem hl) hl'), ?_⟩
  rw [conjSubgroup_conjSubgroup, mul_inv_cancel_left]

theorem fieldType_data {F : Subgroup G} (hFV : F ≤ V) (hF4 : Nat.card F = 4)
    (hF : IsFieldType M L V F 1) : ∃ x y, h.IsPlane625 F x y ∧ ∃ t ∈ ch6MV M V,
      ∃ htN : t ∈ Subgroup.normalizer (V : Set G), ¬ h.IsLin625 ⟨t, htN⟩ ∧
        h.det625 ⟨t, htN⟩ = (det2 x y)⁻¹ := by
  obtain ⟨t, htM, htF, htN, hlin⟩ := (h.isFieldType_iff_ch625 hFV hF4).mp hF
  have hnc : ¬ IsCentralType L V F 1 := by
    intro hc
    obtain ⟨l, hl, rfl⟩ := (h.isCentralType_iff_ch625 hFV hF4).mp hc
    obtain ⟨v, hv⟩ := h.exists_isLine625_conj_ZS hl
    exact h.not_isFieldType_of_isLine625 hFV hF4 hv hF
  obtain ⟨x, y, hP⟩ := h.isPlane625_of_not_central hFV hF4 hnc
  refine ⟨x, y, hP, t, htM, htN, hlin, h.det625_eq_inv_of_fix (h.normal htM.1) hlin hP.1
    (h.conj_fix_of_mem_centralizer htN htF ((hP.2 x).mpr (Or.inr (Or.inl rfl))))
    (h.conj_fix_of_mem_centralizer htN htF ((hP.2 y).mpr (Or.inr (Or.inr (Or.inl rfl)))))⟩

theorem isFieldType_of_isPlane625_six (h331 : Stmt3_3_1) (h615 : Stmt6_1_5)
    (hidx : (autOn L V).relIndex (autOn (ch6MV M V) V) = 6) {F : Subgroup G} (hFV : F ≤ V)
    (hF4 : Nat.card F = 4) {x y : Fin 2 → h.data.K} (hP : h.IsPlane625 F x y) :
    IsFieldType M L V F 1 := by
  obtain ⟨t₀, ht₀T, ht₀⟩ := h.exists_not_lin_T h331 h615
  have ht₀M : t₀ ∈ ch6MV M V := h.T_le_MV_ch625 ht₀T
  have hfrob := (h.semilinear_cases_ch625 ⟨t₀, ht₀M.2⟩ (h.normal ht₀M.1)).resolve_left ht₀
  have hdet0 : det2 (h.data.conj ⟨t₀, ht₀M.2⟩ x) (h.data.conj ⟨t₀, ht₀M.2⟩ y) ≠ 0 := by
    rw [h.det2_conj_frob_ch625 hfrob]
    exact mul_ne_zero (pow_ne_zero 2 hP.1) (h.det625_ne_zero _ (h.normal ht₀M.1))
  obtain ⟨m, hmM, hmN, hmlin, hmx, hmy⟩ := h.exists_MV_basis_six h331 h615 hidx hdet0 hP.1
  exact h.isFieldType_of_isPlane625 hFV hF4 hP ht₀M ht₀ (l := ⟨m, hmN⟩) hmM hmlin hmx hmy

theorem isLin625_mul_inv_of_not_lin {m m' : G} (hm : m ∈ ch6MV M V) (hm' : m' ∈ ch6MV M V)
    (hlin : ¬ h.IsLin625 ⟨m, hm.2⟩) (hlin' : ¬ h.IsLin625 ⟨m', hm'.2⟩) :
    h.IsLin625 (⟨m', hm'.2⟩ * (⟨m, hm.2⟩ : Subgroup.normalizer (V : Set G))⁻¹) := by
  have hK := h.card_K_ch625
  set mm : Subgroup.normalizer (V : Set G) := ⟨m, hm.2⟩ with hmm
  have hf := (h.semilinear_cases_ch625 mm (h.normal hm.1)).resolve_left hlin
  have hf' := (h.semilinear_cases_ch625 ⟨m', hm'.2⟩ (h.normal hm'.1)).resolve_left hlin'
  have hfinv : ∀ (c : h.data.K) w, h.data.conj mm⁻¹ (c • w) = c ^ 2 • h.data.conj mm⁻¹ w := by
    intro c w
    apply (h.data.conj mm).injective
    rw [h.conj_conj_inv_ch625, hf, h.conj_conj_inv_ch625, sq_sq_ch625 hK]
  intro c w
  rw [h.data.conj_mul, h.data.conj_mul, hfinv, hf', sq_sq_ch625 hK]

theorem exists_conj_of_fieldType {F F' : Subgroup G} (hFV : F ≤ V) (hF4 : Nat.card F = 4)
    (hF'V : F' ≤ V) (hF'4 : Nat.card F' = 4) (hF : IsFieldType M L V F 1)
    (hF' : IsFieldType M L V F' 1) : ∃ m ∈ ch6MV M V, F' = conjSubgroup F m := by
  obtain ⟨x, y, hP, t, htM, htN, hlin, hdet⟩ := h.fieldType_data hFV hF4 hF
  obtain ⟨x', y', hP', t', ht'M, ht'N, hlin', hdet'⟩ := h.fieldType_data hF'V hF'4 hF'
  by_cases heq : det2 x y = det2 x' y'
  · obtain ⟨l, hlL, hlx, hly⟩ := h.exists_L_basis_ch625 hP'.1 heq
    exact ⟨l, h.L_le_MV_ch625 hlL, h.eq_conjSubgroup_of_isPlane625 hFV hF'V hP hP' l hlx hly⟩
  · set n : Subgroup.normalizer (V : Set G) :=
      ⟨t', ht'N⟩ * (⟨t, htN⟩ : Subgroup.normalizer (V : Set G))⁻¹ with hn
    have hnM : (n : G) ∈ ch6MV M V := (ch6MV M V).mul_mem ht'M ((ch6MV M V).inv_mem htM)
    have hnlin : h.IsLin625 ⟨(n : G), hnM.2⟩ := h.isLin625_mul_inv_of_not_lin htM ht'M hlin hlin'
    have hdetn : h.det625 ⟨(n : G), hnM.2⟩ ≠ 1 := by
      intro h1
      apply heq
      have e : (⟨t', ht'N⟩ : Subgroup.normalizer (V : Set G)) = n * ⟨t, htN⟩ := by
        rw [hn]; group
      have h2 := h.det625_mul_of_lin hnlin ⟨t, htN⟩
      have e' : (⟨(n : G), hnM.2⟩ : Subgroup.normalizer (V : Set G)) = n := rfl
      rw [e', ← e, h1, mul_one, hdet, hdet'] at h2
      exact (inv_injective h2).symm
    obtain ⟨s, hsM, μ, hμ0, hμ1, hs⟩ := h.exists_scalar_of_det_ne_one hnM hnlin hdetn
    obtain ⟨m, hmM, hmN, -, hmx, hmy⟩ := h.exists_MV_basis_of_scalar hsM hμ0 hμ1 hs hP'.1 hP.1
    exact ⟨m, hmM, h.eq_conjSubgroup_of_isPlane625 hFV hF'V hP hP' ⟨m, hmN⟩ hmx hmy⟩

end Hyp6Sec2

end CFSG.Quasithin.H13
