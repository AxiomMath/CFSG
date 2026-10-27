module

public import CFSG.LocalAnalysis.StandardType.ZS.OrthExtCaseA
import CFSG.LocalAnalysis.StandardType.ZS.ReflQuotient

public section

namespace CFSG.StandardType.ZS

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]
  {G H B : Subgroup (U ≃ₗ[ZMod p] U)} {h : U ≃ₗ[ZMod p] U}

private theorem reflect_mem_of_isOrthOn_full_aux {Q : QuadraticForm (ZMod p) U}
    {X : Subgroup (U ≃ₗ[ZMod p] U)} {u : U}
    (hfull : X = Subgroup.closure {t | IsRefl p t ∧ IsIsom p Q t ∧
      HardMathSupport.Kantor79.movedSpace t ≤ HardMathSupport.Kantor79.commutatorSpace X})
    (hrefl : IsRefl p (CFSG.ClassicalGroups.Orthogonal.reflect Q u))
    (hIsom : IsIsom p Q (CFSG.ClassicalGroups.Orthogonal.reflect Q u))
    (hVle : HardMathSupport.Kantor79.movedSpace
      (CFSG.ClassicalGroups.Orthogonal.reflect Q u) ≤
      HardMathSupport.Kantor79.commutatorSpace X) :
    CFSG.ClassicalGroups.Orthogonal.reflect Q u ∈ X := by
  rw [hfull]
  exact Subgroup.subset_closure ⟨hrefl, hIsom, hVle⟩

private theorem exists_class_root_aux (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {X : Subgroup (U ≃ₗ[ZMod p] U)} {r : U ≃ₗ[ZMod p] U} (hr : r ∈ X)
    (hrr : IsRefl p r) {a : U} (hQa : Q a ≠ 0) (hra : r a = -a)
    {c : ZMod p} (hc : c ≠ 0)
    (hclass : X = Subgroup.closure {t | t ∈ ClassRefl p Q c ∧
      HardMathSupport.Kantor79.movedSpace t ≤ HardMathSupport.Kantor79.commutatorSpace X}) :
    ∃ lam : ZMod p, lam ≠ 0 ∧ c = lam ^ 2 * Q a := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hr' : r ∈ Subgroup.closure {t | t ∈ ClassRefl p Q c ∧
      HardMathSupport.Kantor79.movedSpace t ≤
        HardMathSupport.Kantor79.commutatorSpace X} := by
    rw [← hclass]
    exact hr
  have hrcl : r ∈ Subgroup.closure (ClassRefl p Q c) :=
    Subgroup.closure_mono (fun t ht => ht.1) hr'
  have hrmem : r ∈ ClassRefl p Q c :=
    mem_classRefl_of_isRefl_mem_closure hp hQ hc hrcl hrr
  obtain ⟨a', hQa', hra'eq⟩ := (mem_classRefl_iff hp hQ hc r).mp hrmem
  have hQa'ne : Q a' ≠ 0 := by rw [hQa']; exact hc
  have ha'0 : a' ≠ 0 := by rintro rfl; exact hQa'ne (map_zero Q)
  have ha0 : a ≠ 0 := by rintro rfl; exact hQa (map_zero Q)
  have hra' : r a' = -a' := by
    rw [hra'eq, CFSG.ClassicalGroups.Orthogonal.reflect_apply hQa'ne,
      CFSG.ClassicalGroups.Orthogonal.polar_self_eq_two_mul,
      mul_div_cancel_right₀ (2 : ZMod p) hQa'ne, two_smul]
    abel
  have hVr : HardMathSupport.Kantor79.movedSpace r = ZMod p ∙ a :=
    IsRefl.movedSpace_eq_span hp hrr hra ha0
  have hVr' : HardMathSupport.Kantor79.movedSpace r = ZMod p ∙ a' :=
    IsRefl.movedSpace_eq_span hp hrr hra' ha'0
  have ha'_mem : a' ∈ ZMod p ∙ a := by
    rw [← hVr]
    exact HardMathSupport.Kantor79.mem_movedSpace_of_apply_eq_neg h2 hra'
  obtain ⟨lam, hlam⟩ := Submodule.mem_span_singleton.mp ha'_mem
  have hlam0 : lam ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hlam
    exact hQa'ne (by rw [← hlam]; exact map_zero Q)
  refine ⟨lam, hlam0, ?_⟩
  rw [← hQa', ← hlam, CFSG.ClassicalGroups.Orthogonal.map_smul_eq_sq]

private theorem mem_classRefl_of_class_aux (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {X : Subgroup (U ≃ₗ[ZMod p] U)} {r : U ≃ₗ[ZMod p] U} (hr : r ∈ X)
    (hrr : IsRefl p r) {a : U} (hQa : Q a ≠ 0) (hra : r a = -a) {u : U}
    {γ : ZMod p} (hγ : γ ≠ 0) (hQu : Q u = γ ^ 2 * Q a)
    {c : ZMod p} (hc : c ≠ 0)
    (hclass : X = Subgroup.closure {t | t ∈ ClassRefl p Q c ∧
      HardMathSupport.Kantor79.movedSpace t ≤ HardMathSupport.Kantor79.commutatorSpace X})
    (hru_self : CFSG.ClassicalGroups.Orthogonal.reflect Q u u = -u) :
    CFSG.ClassicalGroups.Orthogonal.reflect Q u ∈ ClassRefl p Q c := by
  obtain ⟨lam, hlam0, hc_lam⟩ := exists_class_root_aux hp hQ hr hrr hQa hra hc hclass
  let kap : ZMod p := lam / γ
  have hkapQ : Q (kap • u) = c := by
    rw [CFSG.ClassicalGroups.Orthogonal.map_smul_eq_sq, hQu, hc_lam]
    have hγlam : (lam / γ) * γ = lam := div_mul_cancel₀ lam hγ
    calc (lam / γ) ^ 2 * (γ ^ 2 * Q a) = ((lam / γ) * γ) ^ 2 * Q a := by ring
      _ = lam ^ 2 * Q a := by rw [hγlam]
  have hru_k : CFSG.ClassicalGroups.Orthogonal.reflect Q u (kap • u) = -(kap • u) := by
    rw [map_smul, hru_self, smul_neg]
  have hkap0 : kap ≠ 0 := div_ne_zero hlam0 hγ
  exact (mem_classRefl_iff hp hQ hc (CFSG.ClassicalGroups.Orthogonal.reflect Q u)).mpr
    ⟨kap • u, hkapQ,
      (CFSG.LieType.Universal.Spin.reflect_smul_of_ne_zero hkap0 u).symm⟩

private theorem reflect_mem_of_isOrthOn_class_aux (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {X : Subgroup (U ≃ₗ[ZMod p] U)} {r : U ≃ₗ[ZMod p] U} (hr : r ∈ X)
    (hrr : IsRefl p r) {a : U} (hQa : Q a ≠ 0) (hra : r a = -a) {u : U}
    {γ : ZMod p} (hγ : γ ≠ 0) (hQu : Q u = γ ^ 2 * Q a)
    {c : ZMod p} (hc : c ≠ 0)
    (hclass : X = Subgroup.closure {t | t ∈ ClassRefl p Q c ∧
      HardMathSupport.Kantor79.movedSpace t ≤ HardMathSupport.Kantor79.commutatorSpace X})
    (hru_self : CFSG.ClassicalGroups.Orthogonal.reflect Q u u = -u)
    (hVle : HardMathSupport.Kantor79.movedSpace
      (CFSG.ClassicalGroups.Orthogonal.reflect Q u) ≤
      HardMathSupport.Kantor79.commutatorSpace X) :
    CFSG.ClassicalGroups.Orthogonal.reflect Q u ∈ X := by
  have hmem := mem_classRefl_of_class_aux hp hQ hr hrr hQa hra hγ hQu hc hclass hru_self
  rw [hclass]
  exact Subgroup.subset_closure ⟨hmem, hVle⟩

theorem reflect_mem_of_isOrthOn (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {X : Subgroup (U ≃ₗ[ZMod p] U)} (hoX : IsOrthOn p Q X) {r : U ≃ₗ[ZMod p] U} (hr : r ∈ X)
    (hrr : IsRefl p r) {a : U} (hQa : Q a ≠ 0) (hra : r a = -a) {u : U}
    (hu : u ∈ HardMathSupport.Kantor79.commutatorSpace X) {γ : ZMod p} (hγ : γ ≠ 0)
    (hQu : Q u = γ ^ 2 * Q a) : CFSG.ClassicalGroups.Orthogonal.reflect Q u ∈ X := by
  have hQune : Q u ≠ 0 := by
    rw [hQu]
    exact mul_ne_zero (pow_ne_zero 2 hγ) hQa
  have hIsom : IsIsom p Q (CFSG.ClassicalGroups.Orthogonal.reflect Q u) :=
    isIsom_reflect Q u
  have hrefl : IsRefl p (CFSG.ClassicalGroups.Orthogonal.reflect Q u) :=
    isRefl_reflect hp hQune
  have hru_self : CFSG.ClassicalGroups.Orthogonal.reflect Q u u = -u :=
    reflect_apply_self hQune
  have hu0 : u ≠ 0 := by
    intro h
    rw [h] at hQune
    exact hQune (map_zero Q)
  have hspan : HardMathSupport.Kantor79.movedSpace
      (CFSG.ClassicalGroups.Orthogonal.reflect Q u) = ZMod p ∙ u :=
    IsRefl.movedSpace_eq_span hp hrefl hru_self hu0
  have hVle : HardMathSupport.Kantor79.movedSpace
      (CFSG.ClassicalGroups.Orthogonal.reflect Q u) ≤
      HardMathSupport.Kantor79.commutatorSpace X := by
    rw [hspan, Submodule.span_singleton_le_iff_mem]
    exact hu
  rcases hoX with hfull | ⟨c, hc, hclass⟩
  · exact reflect_mem_of_isOrthOn_full_aux hfull hrefl hIsom hVle
  · exact reflect_mem_of_isOrthOn_class_aux hp hQ hr hrr hQa hra hγ hQu hc hclass hru_self hVle

theorem commute_of_isRefl_of_apply_eq (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) {Q : QuadraticForm (ZMod p) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hoH : IsOrthOn p Q H)
    {r t : U ≃ₗ[ZMod p] U} (hr : r ∈ H) (hrr : IsRefl p r) (ht : t ∈ G) {u : U} (hu : u ≠ 0)
    (hru : r u = -u) (htu : t u = u) : r * t = t * r := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hrG : r ∈ G := hD.setting.le hr
  have hxG : t * r * t⁻¹ ∈ G := G.mul_mem (G.mul_mem ht hrG) (G.inv_mem ht)
  have hxrefl : IsRefl p (t * r * t⁻¹) := IsRefl.conj hrr t
  have hVr : HardMathSupport.Kantor79.movedSpace r = ZMod p ∙ u :=
    IsRefl.movedSpace_eq_span hp hrr hru hu
  have huVH : u ∈ HardMathSupport.Kantor79.commutatorSpace H :=
    HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hr
      (HardMathSupport.Kantor79.mem_movedSpace_of_apply_eq_neg h2 hru)
  have htu_inv : t⁻¹ u = u := by
    have h := LinearEquiv.symm_apply_apply t u
    rwa [htu] at h
  have hxV : HardMathSupport.Kantor79.movedSpace (t * r * t⁻¹) =
      (HardMathSupport.Kantor79.movedSpace r).map (t : U →ₗ[ZMod p] U) :=
    movedSpace_conj t r
  have hxVle : HardMathSupport.Kantor79.movedSpace (t * r * t⁻¹) ≤
      HardMathSupport.Kantor79.commutatorSpace H := by
    rw [hxV, hVr, Submodule.map_span, Set.image_singleton]
    have htu' : (t : U →ₗ[ZMod p] U) u = u := htu
    rw [htu', Submodule.span_singleton_le_iff_mem]
    exact huVH
  have hxH : t * r * t⁻¹ ∈ H := hD.mem_of_le (t * r * t⁻¹) hxG hxrefl hxVle
  have hx_u : (t * r * t⁻¹) u = -u := by
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, htu_inv, hru, map_neg, htu]
  have hxr : t * r * t⁻¹ = r :=
    DimThree.eq_of_isRefl_isIsom_of_apply_eq_neg hp hQ hxrefl (hoH.isIsom hxH) hrr
      (hoH.isIsom hr) hu hx_u hru
  have h1 : (t * r * t⁻¹) * t = t * r := by group
  rw [hxr] at h1
  exact h1

private theorem exists_s_sq_ne_neg_m (hp2 : p ≠ 2) (hp3 : p ≠ 3) {m : ZMod p} :
    ∃ s : ZMod p, s ^ 2 ≠ -m ∧ s ≠ 0 := by
  have h3 : (3 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 3 hp3
  by_cases h1 : (1 : ZMod p) ^ 2 = -m
  · refine ⟨2, ?_, ZMod.prime_ne_zero p 2 hp2⟩
    intro h2sq
    apply h3
    have h4eq : (4 : ZMod p) = 1 := by
      calc (4 : ZMod p) = 2 ^ 2 := by ring
        _ = -m := h2sq
        _ = 1 ^ 2 := h1.symm
        _ = 1 := by ring
    calc (3 : ZMod p) = 4 - 1 := by ring
      _ = 1 - 1 := by rw [h4eq]
      _ = 0 := by ring
  · exact ⟨1, h1, one_ne_zero⟩

private theorem exists_alpha_sq_add_mul_add_eq_sq (hp5 : 5 ≤ p) (b c : ZMod p) :
    ∃ α γ : ZMod p, γ ≠ 0 ∧ α * α + b * α + c = γ * γ := by
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp2
  have h4 : (4 : ZMod p) ≠ 0 := by
    have h42 : (4 : ZMod p) = 2 * 2 := by norm_num
    rw [h42]
    exact mul_ne_zero h2 h2
  set m : ZMod p := c - b ^ 2 / 4 with hm
  obtain ⟨s, hs_sq_ne, hs0⟩ := exists_s_sq_ne_neg_m hp2 hp3
  set γ : ZMod p := (s + m / s) / 2 with hγdef
  set x : ZMod p := (m / s - s) / 2 with hxdef
  have hγ_ne : γ ≠ 0 := by
    rw [hγdef]
    apply div_ne_zero
    · intro h
      apply hs_sq_ne
      have hsm : s * (s + m / s) = s ^ 2 + m := by
        rw [mul_add, mul_comm s (m / s), div_mul_cancel₀ m hs0]
        ring
      rw [h, mul_zero] at hsm
      have hzero : s ^ 2 + m = 0 := hsm.symm
      have hsneg : s ^ 2 = -m := by
        rw [← sub_eq_zero, sub_neg_eq_add]
        exact hzero
      exact hsneg
    · exact h2
  have hγx : γ ^ 2 - x ^ 2 = m := by
    rw [hγdef, hxdef]
    field_simp [hs0, h2, h4]
    ring
  refine ⟨x - b / 2, γ, hγ_ne, ?_⟩
  have hαeq : (x - b / 2) * (x - b / 2) + b * (x - b / 2) + c = x ^ 2 + m := by
    rw [hm]
    field_simp [h2, h4]
    ring
  have hsq : x ^ 2 + m = γ ^ 2 := by
    rw [← hγx]
    ring
  rw [hαeq, hsq, pow_two]

private theorem polar_eq_zero_aux_root (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) {Q : QuadraticForm (ZMod p) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hoH : IsOrthOn p Q H)
    {t : U ≃ₗ[ZMod p] U} (ht : t ∈ B) {w : U} (htw : t w = -w) :
    ∃ a : U, Q a ≠ 0 ∧ h a = -a ∧ t a = a ∧ h w = w ∧
      QuadraticMap.polar Q a w = 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have h3 : 3 ≤ Module.finrank (ZMod p) U := le_trans (by norm_num) hD.setting.four_le
  obtain ⟨a, hQa, hha⟩ :=
    DimThree.exists_root_of_isRefl_isIsom hp hQ hD.isRefl (hoH.isIsom hD.mem)
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hQa (map_zero Q)
  have haVH : a ∈ HardMathSupport.Kantor79.commutatorSpace H :=
    HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hD.mem
      (HardMathSupport.Kantor79.mem_movedSpace_of_apply_eq_neg h2 hha)
  obtain ⟨hVB, hCB⟩ := commutatorSpace_eq_ker_of_isCentralizingSplit hp h3 hD.split hD.isRefl
  have haCB : a ∈ centralizerSpace B := by
    rw [hCB]
    exact HardMathSupport.Kantor79.mem_movedSpace_of_apply_eq_neg h2 hha
  have hta : t a = a := mem_centralizerSpace.mp haCB t ht
  have hwVB : w ∈ HardMathSupport.Kantor79.commutatorSpace B :=
    HardMathSupport.Kantor79.movedSpace_le_commutatorSpace ht
      (HardMathSupport.Kantor79.mem_movedSpace_of_apply_eq_neg h2 htw)
  have hhw : h w = w := by
    have hwker : w ∈ LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1) := by
      rw [← hVB]
      exact hwVB
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hwker
    exact hwker
  have hβaw : QuadraticMap.polar Q a w = 0 :=
    IsIsom.polar_eq_zero_of_apply_eq_neg_of_apply_eq hp (hoH.isIsom hD.mem) hha hhw
  exact ⟨a, hQa, hha, hta, hhw, hβaw⟩

private theorem polar_eq_zero_aux_u (hp5 : 5 ≤ p) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) {Q : QuadraticForm (ZMod p) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hoH : IsOrthOn p Q H)
    {t : U ≃ₗ[ZMod p] U} {v : U}
    (hv : v ∈ HardMathSupport.Kantor79.commutatorSpace H) (htv : t v = v)
    {a : U} (hQa : Q a ≠ 0) (hha : h a = -a) (hta : t a = a) :
    ∃ u : U, ∃ α γ : ZMod p, u ∈ HardMathSupport.Kantor79.commutatorSpace H ∧
      Q u = γ ^ 2 * Q a ∧ CFSG.ClassicalGroups.Orthogonal.reflect Q u ∈ H ∧
      IsRefl p (CFSG.ClassicalGroups.Orthogonal.reflect Q u) ∧
      CFSG.ClassicalGroups.Orthogonal.reflect Q u u = -u ∧ u ≠ 0 ∧ t u = u ∧
      γ ≠ 0 ∧ u = α • a + v := by
  have hp : p ≠ 2 := by omega
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  obtain ⟨α, γ, hγ, hα⟩ := exists_alpha_sq_add_mul_add_eq_sq hp5
    (QuadraticMap.polar Q a v / Q a) (Q v / Q a)
  let u : U := α • a + v
  have haVH : a ∈ HardMathSupport.Kantor79.commutatorSpace H :=
    HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hD.mem
      (HardMathSupport.Kantor79.mem_movedSpace_of_apply_eq_neg h2 hha)
  have huVH : u ∈ HardMathSupport.Kantor79.commutatorSpace H := by
    change α • a + v ∈ HardMathSupport.Kantor79.commutatorSpace H
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ haVH) hv
  have hQu : Q u = γ ^ 2 * Q a := by
    change Q (α • a + v) = γ ^ 2 * Q a
    have hα' := hα
    field_simp [hQa] at hα'
    rw [QuadraticMap.map_add Q, CFSG.ClassicalGroups.Orthogonal.map_smul_eq_sq,
      CFSG.ClassicalGroups.Orthogonal.polar_smul_left_eq]
    linear_combination hα'
  have hruH : CFSG.ClassicalGroups.Orthogonal.reflect Q u ∈ H :=
    reflect_mem_of_isOrthOn hp hQ hoH hD.mem hD.isRefl hQa hha huVH hγ hQu
  have hQune : Q u ≠ 0 := by
    rw [hQu]
    exact mul_ne_zero (pow_ne_zero 2 hγ) hQa
  have hru_refl : IsRefl p (CFSG.ClassicalGroups.Orthogonal.reflect Q u) :=
    isRefl_reflect hp hQune
  have hru_u : CFSG.ClassicalGroups.Orthogonal.reflect Q u u = -u :=
    reflect_apply_self hQune
  have hu0 : u ≠ 0 := by
    intro h
    rw [h] at hQune
    exact hQune (map_zero Q)
  have htu : t u = u := by
    change t (α • a + v) = α • a + v
    rw [map_add, map_smul, hta, htv]
  exact ⟨u, α, γ, huVH, hQu, hruH, hru_refl, hru_u, hu0, htu, hγ, rfl⟩

private theorem polar_eq_zero_aux_final (hp : p ≠ 2) {Q : QuadraticForm (ZMod p) U}
    {t : U ≃ₗ[ZMod p] U} {w v u a : U} {α : ZMod p}
    (htw : t w = -w) (htu : t u = u)
    (hcomm : CFSG.ClassicalGroups.Orthogonal.reflect Q u * t =
      t * CFSG.ClassicalGroups.Orthogonal.reflect Q u)
    (hQune : Q u ≠ 0) (hu0 : u ≠ 0)
    (hβaw : QuadraticMap.polar Q a w = 0)
    (hαβ : QuadraticMap.polar Q v w = QuadraticMap.polar Q u w -
      α * QuadraticMap.polar Q a w) :
    QuadraticMap.polar Q v w = 0 := by
  set κ : ZMod p := QuadraticMap.polar Q u w / Q u with hκdef
  have hκu : κ • u = -(κ • u) := by
    have hw_eq : CFSG.ClassicalGroups.Orthogonal.reflect Q u (t w) =
        t (CFSG.ClassicalGroups.Orthogonal.reflect Q u w) := by
      rw [← LinearEquiv.mul_apply, hcomm, LinearEquiv.mul_apply]
    rw [htw, map_neg, CFSG.ClassicalGroups.Orthogonal.reflect_apply hQune] at hw_eq
    rw [map_sub, map_smul, htw, htu] at hw_eq
    have h : κ • u - w = -w - κ • u := by
      rw [← neg_sub]
      exact hw_eq
    have h1 : κ • u - w + w = (-w - κ • u) + w := congrArg (· + w) h
    rw [sub_add_cancel] at h1
    have h2 : (-w - κ • u) + w = -(κ • u) := by
      rw [sub_eq_add_neg, add_comm (-w) (-(κ • u)), add_assoc, neg_add_cancel, add_zero]
    rw [h2] at h1
    exact h1
  have h2κ : (2 : ZMod p) • (κ • u) = 0 := by
    rw [two_smul]
    nth_rewrite 1 [hκu]
    rw [neg_add_cancel]
  have hκ0 : κ = 0 := by
    have h1 : κ • u = 0 := (smul_eq_zero.mp h2κ).resolve_left
      (ZMod.prime_ne_zero p 2 hp)
    exact (smul_eq_zero.mp h1).resolve_right hu0
  have hβuw : QuadraticMap.polar Q u w = 0 := by
    have h : κ * Q u = QuadraticMap.polar Q u w := by
      rw [hκdef]
      exact div_mul_cancel₀ _ hQune
    rw [hκ0, zero_mul] at h
    exact h.symm
  rw [hαβ, hβuw, hβaw]
  ring

theorem polar_eq_zero_of_apply_eq_neg_of_apply_eq (hp5 : 5 ≤ p) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) {Q : QuadraticForm (ZMod p) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hoH : IsOrthOn p Q H)
    {t : U ≃ₗ[ZMod p] U} (ht : t ∈ B) {w : U} (htw : t w = -w) {v : U}
    (hv : v ∈ HardMathSupport.Kantor79.commutatorSpace H) (htv : t v = v) :
    QuadraticMap.polar Q v w = 0 := by
  have hp : p ≠ 2 := by omega
  obtain ⟨a, hQa, hha, hta, hhw, hβaw⟩ := polar_eq_zero_aux_root hp hD hQ hoH ht htw
  obtain ⟨u, α, γ, huVH, hQu, hruH, hru_refl, hru_u, hu0, htu, hγ, huv⟩ :=
    polar_eq_zero_aux_u hp5 hD hQ hoH hv htv hQa hha hta
  have hQune : Q u ≠ 0 := by
    rw [hQu]
    exact mul_ne_zero (pow_ne_zero 2 hγ) hQa
  have hcomm := commute_of_isRefl_of_apply_eq hp hD hQ hoH hruH hru_refl
    (hD.split.1 ht) hu0 hru_u htu
  have hαβ : QuadraticMap.polar Q v w = QuadraticMap.polar Q u w -
      α * QuadraticMap.polar Q a w := by
    rw [huv]
    rw [QuadraticMap.polar_add_left, CFSG.ClassicalGroups.Orthogonal.polar_smul_left_eq]
    abel
  exact polar_eq_zero_aux_final hp htw htu hcomm hQune hu0 hβaw hαβ

end CFSG.StandardType.ZS

end
