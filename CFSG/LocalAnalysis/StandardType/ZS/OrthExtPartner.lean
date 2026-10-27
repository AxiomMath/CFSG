module

public import CFSG.LocalAnalysis.StandardType.ZS.OrthExtSeven

public section

namespace CFSG.StandardType.ZS

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]
  {G H B : Subgroup (U ≃ₗ[ZMod p] U)} {h : U ≃ₗ[ZMod p] U}

private theorem exists_root_reflect_of_isIsom (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {g : U ≃ₗ[ZMod p] U} (hg' : IsRefl p g) (hgi : IsIsom p Q g) :
    ∃ e : U, Q e ≠ 0 ∧ g e = -e ∧ g = ClassicalGroups.Orthogonal.reflect Q e := by
  obtain ⟨e, heQ, hge⟩ := DimThree.exists_root_of_isRefl_isIsom hp hQ hg' hgi
  have hcl : ClassicalGroups.Orthogonal.reflect Q e ∈ ClassRefl p Q (Q e) :=
    (mem_classRefl_iff hp hQ heQ _).mpr ⟨e, rfl, rfl⟩
  have hre : ClassicalGroups.Orthogonal.reflect Q e e = -e :=
    reflect_apply_self heQ
  have he0 : e ≠ 0 := fun h => heQ (by rw [h, map_zero])
  exact ⟨e, heQ, hge, DimThree.eq_of_isRefl_isIsom_of_apply_eq_neg hp hQ hg' hgi
    hcl.1 hcl.2.1 he0 hge hre⟩

private theorem commutatorSpace_eq_ker_polar [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) (h4 : Module.finrank (ZMod p) U = 4)
    {Q : QuadraticForm (ZMod p) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hoH : IsOrthOn p Q H) {f : U}
    (hf : f ∈ centralizerSpace H) (hspan : centralizerSpace H = Submodule.span (ZMod p) {f}) :
    HardMathSupport.Kantor79.commutatorSpace H =
      LinearMap.ker (QuadraticMap.polarBilin Q f) := by
  have hsplitH : SplitSupport H 3 := by simpa [h4] using hD.setting.sub.2.1
  ext v
  rw [mem_commutatorSpace_iff_forall_polar_eq_zero hQ (fun g hg => hoH.isIsom hg) hsplitH.1,
    LinearMap.mem_ker, QuadraticMap.polarBilin_apply_apply]
  constructor
  · intro h; exact h f hf
  · intro h u hu
    rw [hspan] at hu
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
    rw [ClassicalGroups.Orthogonal.polar_smul_left_eq, h, mul_zero]

private theorem commutatorSpace_reflStab_eq_inf (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) (h4 : Module.finrank (ZMod p) U = 4)
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hoH : IsOrthOn p Q H) :
    HardMathSupport.Kantor79.commutatorSpace (reflStab p H h) =
      HardMathSupport.Kantor79.commutatorSpace H ⊓
        HardMathSupport.Kantor79.commutatorSpace B := by
  have h3 : 3 ≤ Module.finrank (ZMod p) U := by omega
  rw [commutatorSpace_reflStab hp hQ hD.setting.sub.2.1 (by omega)
    (by intro h3p; have h5 := hD.setting.five_le_of_eq_three h3p; omega) hoH hD.mem hD.isRefl,
    ← (commutatorSpace_eq_ker_of_isCentralizingSplit hp h3 hD.split hD.isRefl).1]

private theorem commutatorSpace_eq_ker_polar_of_reflection (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) {Q : QuadraticForm (ZMod p) U} {e : U}
    (heq : h = ClassicalGroups.Orthogonal.reflect Q e) (heQ : Q e ≠ 0) :
    HardMathSupport.Kantor79.commutatorSpace B =
      LinearMap.ker (QuadraticMap.polarBilin Q e) := by
  have h3 : 3 ≤ Module.finrank (ZMod p) U := by have := hD.setting.four_le; omega
  rw [(commutatorSpace_eq_ker_of_isCentralizingSplit hp h3 hD.split hD.isRefl).1, heq,
    ker_reflect_sub_one_eq_ker_polar heQ]

private theorem finrank_commutatorSpace_reflStab_eq_two (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] (hD : LemmaTwoSevenData p G H B h)
    (h4 : Module.finrank (ZMod p) U = 4) {Q : QuadraticForm (ZMod p) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hoH : IsOrthOn p Q H) {e : U}
    (heQ : Q e ≠ 0) (heVH : e ∈ HardMathSupport.Kantor79.commutatorSpace H)
    (hVB : HardMathSupport.Kantor79.commutatorSpace B =
      LinearMap.ker (QuadraticMap.polarBilin Q e)) :
    Module.finrank (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace (reflStab p H h)) = 2 := by
  have hsplitH : SplitSupport H 3 := by simpa [h4] using hD.setting.sub.2.1
  have hE : HardMathSupport.Kantor79.commutatorSpace (reflStab p H h) =
      HardMathSupport.Kantor79.commutatorSpace H ⊓ LinearMap.ker (QuadraticMap.polarBilin Q e) := by
    rw [commutatorSpace_reflStab_eq_inf hp hD h4 hQ hoH, hVB]
  rw [hE]
  have h := ClassicalGroups.Orthogonal.finrank_inf_ker_polarBilin_add_one
    (ZMod.prime_ne_zero p 2 hp) heVH heQ
  rw [hsplitH.2.1] at h
  omega

private theorem reflection_maps_reflStab (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) (h4 : Module.finrank (ZMod p) U = 4)
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hoH : IsOrthOn p Q H) (hB : ∀ g ∈ B, IsIsom p Q g) {f : U}
    (hf : f ∈ centralizerSpace H)
    (hspan : centralizerSpace H = Submodule.span (ZMod p) {f})
    (hroots : ∀ (r : U ≃ₗ[ZMod p] U), r ∈ B → IsRefl p r → ∀ a : U, Q a ≠ 0 →
      r a = -a → a ∈ HardMathSupport.Kantor79.commutatorSpace (reflStab p H h) ∨
        a ∈ Submodule.span (ZMod p) {f})
    {t : U ≃ₗ[ZMod p] U} (htB : t ∈ B) (htR : IsRefl p t) :
    ∀ x ∈ HardMathSupport.Kantor79.commutatorSpace (reflStab p H h), t x ∈
      HardMathSupport.Kantor79.commutatorSpace (reflStab p H h) ∧ t⁻¹ x ∈
      HardMathSupport.Kantor79.commutatorSpace (reflStab p H h) := by
  have hVH : HardMathSupport.Kantor79.commutatorSpace H =
      LinearMap.ker (QuadraticMap.polarBilin Q f) :=
    commutatorSpace_eq_ker_polar hD h4 hQ hoH hf hspan
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htR.1
  rintro x hx
  obtain ⟨a, haQ, hta, hteq⟩ := exists_root_reflect_of_isIsom hp hQ htR (hB t htB)
  have hmem : t x ∈ HardMathSupport.Kantor79.commutatorSpace (reflStab p H h) := by
    rcases hroots t htB htR a haQ hta with haE | haF
    · rw [hteq, ClassicalGroups.Orthogonal.reflect_apply haQ]
      exact Submodule.sub_mem _ hx (Submodule.smul_mem _ _ haE)
    · have hxH : x ∈ HardMathSupport.Kantor79.commutatorSpace H :=
        (commutatorSpace_reflStab_eq_inf hp hD h4 hQ hoH ▸ hx).1
      have hfa : QuadraticMap.polar Q f x = 0 := by
        rw [hVH, LinearMap.mem_ker, QuadraticMap.polarBilin_apply_apply] at hxH
        exact hxH
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp haF
      have hβ : QuadraticMap.polar Q (c • f) x = 0 := by
        rw [ClassicalGroups.Orthogonal.polar_smul_left_eq, hfa, mul_zero]
      rw [hteq, ClassicalGroups.Orthogonal.reflect_apply_of_polar_eq_zero hβ]
      exact hx
  exact ⟨hmem, by rw [hti]; exact hmem⟩

private theorem invariant_reflStab_of_roots (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) (h4 : Module.finrank (ZMod p) U = 4)
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hoH : IsOrthOn p Q H) (hB : ∀ g ∈ B, IsIsom p Q g) {f : U}
    (hf : f ∈ centralizerSpace H)
    (hspan : centralizerSpace H = Submodule.span (ZMod p) {f})
    (hroots : ∀ (r : U ≃ₗ[ZMod p] U), r ∈ B → IsRefl p r → ∀ a : U, Q a ≠ 0 →
      r a = -a → a ∈ HardMathSupport.Kantor79.commutatorSpace (reflStab p H h) ∨
        a ∈ Submodule.span (ZMod p) {f}) :
    ∀ r ∈ B, ∀ x ∈ HardMathSupport.Kantor79.commutatorSpace (reflStab p H h),
      r x ∈ HardMathSupport.Kantor79.commutatorSpace (reflStab p H h) := by
  intro r hr x hx
  have hgen : B = Subgroup.closure {t : U ≃ₗ[ZMod p] U | t ∈ B ∧ IsRefl p t} := hD.split.2.1
  rw [hgen] at hr
  exact forall_mem_closure_mapsTo_of_forall (S := {t : U ≃ₗ[ZMod p] U | t ∈ B ∧ IsRefl p t})
    (fun t ht x hx =>
      (reflection_maps_reflStab hp hD h4 hQ hoH hB hf hspan hroots ht.1 ht.2 x hx).1)
    r hr x hx

private theorem exists_smul_sub_mem_reflStab (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) (h4 : Module.finrank (ZMod p) U = 4)
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hoH : IsOrthOn p Q H) {f : U} (hf : f ∈ centralizerSpace H) (hf0 : f ≠ 0)
    (hspan : centralizerSpace H = Submodule.span (ZMod p) {f})
    (hVB : HardMathSupport.Kantor79.commutatorSpace B = LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1))
    {x : U} (hx : x ∈ HardMathSupport.Kantor79.commutatorSpace B) :
    ∃ μ : ZMod p, x - μ • f ∈
      HardMathSupport.Kantor79.commutatorSpace (reflStab p H h) := by
  have hsplitH : SplitSupport H 3 := by simpa [h4] using hD.setting.sub.2.1
  have hVH : HardMathSupport.Kantor79.commutatorSpace H =
      LinearMap.ker (QuadraticMap.polarBilin Q f) :=
    commutatorSpace_eq_ker_polar hD h4 hQ hoH hf hspan
  have hfVH : f ∉ HardMathSupport.Kantor79.commutatorSpace H := by
    intro hmem
    have hbot : f ∈ (⊥ : Submodule (ZMod p) U) := by
      rw [← hsplitH.1.inf_eq_bot]; exact ⟨hmem, hf⟩
    exact hf0 (by simpa using hbot)
  have hQf : Q f ≠ 0 := by
    intro h0
    exact hfVH (by
      rw [hVH, LinearMap.mem_ker, QuadraticMap.polarBilin_apply_apply,
        ClassicalGroups.Orthogonal.polar_self_eq_zero h0])
  have hβff : QuadraticMap.polar Q f f ≠ 0 := by
    rw [ClassicalGroups.Orthogonal.polar_self_eq_two_mul]
    exact mul_ne_zero (ZMod.prime_ne_zero p 2 hp) hQf
  refine ⟨QuadraticMap.polar Q f x / QuadraticMap.polar Q f f, ?_⟩
  rw [commutatorSpace_reflStab_eq_inf hp hD h4 hQ hoH]
  refine ⟨?_, ?_⟩
  · rw [hVH]
    exact LinearMap.mem_ker.mpr (by
      rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_sub_right,
        ClassicalGroups.Orthogonal.polar_smul_right_eq, div_mul_cancel₀ _ hβff, sub_self])
  · rw [hVB]
    have hxfix : (h : U →ₗ[ZMod p] U) x = x := by
      have hx' : ((h : U →ₗ[ZMod p] U) - 1) x = 0 := by
        rw [← LinearMap.mem_ker, ← hVB]; exact hx
      simpa using sub_eq_zero.mp hx'
    have hffix : (h : U →ₗ[ZMod p] U) f = f := (mem_centralizerSpace.mp hf) h hD.mem
    show (h : U →ₗ[ZMod p] U) (x - _ • f) - (x - _ • f) = 0
    rw [map_sub, map_smul, hxfix, hffix]
    abel

private theorem exists_root_mixed (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) (h4 : Module.finrank (ZMod p) U = 4)
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hoH : IsOrthOn p Q H) (hB : ∀ g ∈ B, IsIsom p Q g) {f : U}
    (hf : f ∈ centralizerSpace H) (hf0 : f ≠ 0)
    (hspan : centralizerSpace H = Submodule.span (ZMod p) {f})
    (hVB : HardMathSupport.Kantor79.commutatorSpace B = LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1))
    (hEfin : Module.finrank (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace (reflStab p H h)) = 2)
    (hVBfin : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace B) = 3) :
    ∃ (a w : U) (α : ZMod p) (r : U ≃ₗ[ZMod p] U),
      Q a ≠ 0 ∧ α ≠ 0 ∧ w ∈ HardMathSupport.Kantor79.commutatorSpace (reflStab p H h) ∧
        w ≠ 0 ∧ a = α • f + w ∧ r ∈ B ∧ r = ClassicalGroups.Orthogonal.reflect Q a := by
  by_contra hcon
  push Not at hcon
  have hroots : ∀ (r : U ≃ₗ[ZMod p] U), r ∈ B → IsRefl p r → ∀ a : U, Q a ≠ 0 →
      r a = -a → a ∈ HardMathSupport.Kantor79.commutatorSpace (reflStab p H h) ∨
        a ∈ Submodule.span (ZMod p) {f} := by
    intro r hr hrR a haQ hra
    have hreq : r = ClassicalGroups.Orthogonal.reflect Q a :=
      eq_reflect_of_isRefl_isIsom hp hQ hrR (hB r hr) haQ hra
    have haB : a ∈ HardMathSupport.Kantor79.commutatorSpace B := by
      have hmem : r a - a ∈ HardMathSupport.Kantor79.commutatorSpace B :=
        Submodule.subset_span ⟨r, hr, a, rfl⟩
      have haeq : a = (-2 : ZMod p)⁻¹ • (r a - a) := by
        rw [hra, show -a - a = (-2 : ZMod p) • a by rw [neg_smul, two_smul]; abel]
        rw [smul_smul, show (-2 : ZMod p)⁻¹ * -2 = 1 from
          inv_mul_cancel₀ (neg_ne_zero.mpr (ZMod.prime_ne_zero p 2 hp)), one_smul]
      rw [haeq]
      exact Submodule.smul_mem _ _ hmem
    obtain ⟨α, hwE⟩ := exists_smul_sub_mem_reflStab hp hD h4 hQ hoH hf hf0 hspan hVB haB
    by_cases hα : α = 0
    · left; simpa [hα] using hwE
    · by_cases hw0 : a - α • f = 0
      · right
        have haeq : a = α • f := by rw [← sub_eq_zero]; exact hw0
        rw [haeq]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton f))
      · exfalso; exact hcon a (a - α • f) α r haQ hα hwE hw0 (by abel) hr hreq
  have hinv := invariant_reflStab_of_roots hp hD h4 hQ hoH hB hf hspan hroots
  have hsplitB : SplitSupport B 3 := by simpa [h4] using hD.split.2.2.1
  have hle : HardMathSupport.Kantor79.commutatorSpace (reflStab p H h) ≤
      HardMathSupport.Kantor79.commutatorSpace B := by
    rw [commutatorSpace_reflStab_eq_inf hp hD h4 hQ hoH]; exact inf_le_right
  rcases hsplitB.2.2 _ bot_le hle hinv with hbot | htop
  · rw [hbot, finrank_bot] at hEfin; omega
  · rw [htop] at hEfin; omega

private theorem reflect_apply_mixed_root {Q : QuadraticForm (ZMod p) U} {f w a : U}
    {α : ZMod p} {r : U ≃ₗ[ZMod p] U} (c : ZMod p)
    (hcdef : c = QuadraticMap.polar Q a f / Q a) (haQ : Q a ≠ 0) (hα : α ≠ 0)
    (hβff : QuadraticMap.polar Q f f ≠ 0)
    (hβwf : QuadraticMap.polar Q w f = 0) (ha : a = α • f + w)
    (hr : r = ClassicalGroups.Orthogonal.reflect Q a) :
    c ≠ 0 ∧ r f = (1 - c * α) • f + (-c) • w ∧
      QuadraticMap.polar Q (r f) f = (1 - c * α) * QuadraticMap.polar Q f f := by
  have hβaf : QuadraticMap.polar Q a f = α * QuadraticMap.polar Q f f := by
    rw [ha, QuadraticMap.polar_add_left, ClassicalGroups.Orthogonal.polar_smul_left_eq,
      hβwf, add_zero]
  have hc : c ≠ 0 := by
    rw [hcdef, hβaf]
    exact div_ne_zero (mul_ne_zero hα hβff) haQ
  have hrf : r f = (1 - c * α) • f + (-c) • w := by
    rw [hr, ClassicalGroups.Orthogonal.reflect_apply haQ, ha, hcdef, smul_add, smul_smul,
      sub_smul, one_smul, neg_smul]
    rw [ha]
    module
  refine ⟨hc, hrf, ?_⟩
  rw [hrf, QuadraticMap.polar_add_left, ClassicalGroups.Orthogonal.polar_smul_left_eq,
    ClassicalGroups.Orthogonal.polar_smul_left_eq, hβwf, mul_zero, add_zero]

private theorem isSingular_of_forall_polar_sq_eq (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) (h4 : Module.finrank (ZMod p) U = 4)
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hoH : IsOrthOn p Q H) (hB : ∀ g ∈ B, IsIsom p Q g) {f : U}
    (hf : f ∈ centralizerSpace H)
    (hspan : centralizerSpace H = Submodule.span (ZMod p) {f})
    (hβff : QuadraticMap.polar Q f f ≠ 0)
    (hall : ∀ b ∈ B, QuadraticMap.polarBilin Q (b f) f ^ 2 =
      QuadraticMap.polarBilin Q f f ^ 2)
    {a w : U} {α : ZMod p} {r : U ≃ₗ[ZMod p] U} (haQ : Q a ≠ 0) (hα : α ≠ 0)
    (hwE : w ∈ HardMathSupport.Kantor79.commutatorSpace (reflStab p H h))
    (ha : a = α • f + w) (hrB : r ∈ B) (hr : r = ClassicalGroups.Orthogonal.reflect Q a) :
    Q w = 0 := by
  have hVH : HardMathSupport.Kantor79.commutatorSpace H =
      LinearMap.ker (QuadraticMap.polarBilin Q f) :=
    commutatorSpace_eq_ker_polar hD h4 hQ hoH hf hspan
  have hwH : w ∈ HardMathSupport.Kantor79.commutatorSpace H :=
    (commutatorSpace_reflStab_eq_inf hp hD h4 hQ hoH ▸ hwE).1
  have hβfw : QuadraticMap.polar Q f w = 0 := by
    rw [hVH, LinearMap.mem_ker, QuadraticMap.polarBilin_apply_apply] at hwH
    exact hwH
  have hβwf : QuadraticMap.polar Q w f = 0 := by
    rw [QuadraticMap.polar_comm]; exact hβfw
  set c : ZMod p := QuadraticMap.polar Q a f / Q a with hcdef
  obtain ⟨hc, hrf, hβrf⟩ := reflect_apply_mixed_root c hcdef haQ hα hβff hβwf ha hr
  have hsq : (1 - c * α) ^ 2 = 1 := by
    have h := hall r hrB
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply, hβrf] at h
    have h' : (1 - c * α) ^ 2 * QuadraticMap.polar Q f f ^ 2 =
        QuadraticMap.polar Q f f ^ 2 := by
      calc (1 - c * α) ^ 2 * QuadraticMap.polar Q f f ^ 2 =
          ((1 - c * α) * QuadraticMap.polar Q f f) ^ 2 := by ring
        _ = QuadraticMap.polar Q f f ^ 2 := h
    exact mul_right_cancel₀ (pow_ne_zero 2 hβff) (by simpa using h')
  have hQrf : Q (r f) = (1 - c * α) ^ 2 * Q f + c ^ 2 * Q w := by
    rw [hrf, QuadraticMap.map_add Q, ClassicalGroups.Orthogonal.map_smul_eq_sq,
      ClassicalGroups.Orthogonal.map_smul_eq_sq, ClassicalGroups.Orthogonal.polar_smul_left_eq,
      ClassicalGroups.Orthogonal.polar_smul_right_eq, hβfw, mul_zero, mul_zero, add_zero]
    ring
  have hQr : Q (r f) = Q f := hB r hrB f
  have hcw : c ^ 2 * Q w = 0 := by
    have h' : (1 - c * α) ^ 2 * Q f + c ^ 2 * Q w = Q f := by rw [← hQrf]; exact hQr
    rw [hsq, one_mul] at h'
    have h'' : Q f + c ^ 2 * Q w = Q f + 0 := by rw [add_zero]; exact h'
    exact add_left_cancel h''
  exact (mul_eq_zero.mp hcw).resolve_left (pow_ne_zero 2 hc)

private theorem exists_hyperbolic_partner {Q : QuadraticForm (ZMod p) U}
    {W : Submodule (ZMod p) U} (hW : ClassicalGroups.Orthogonal.PolarNondegOn Q W) {w : U}
    (hw : w ∈ W) (hw0 : w ≠ 0) (hQw : Q w = 0) :
    ∃ w' : U, w' ∈ W ∧ Q w' = 0 ∧ QuadraticMap.polar Q w w' = 1 := by
  obtain ⟨w₀, hw₀, hβ₀⟩ := hW.exists_polar_ne_zero hw hw0
  have hβ : QuadraticMap.polar Q w ((QuadraticMap.polar Q w w₀)⁻¹ • w₀) = 1 := by
    rw [ClassicalGroups.Orthogonal.polar_smul_right_eq]
    exact inv_mul_cancel₀ hβ₀
  let P := ClassicalGroups.Orthogonal.HypPair.ofPolarEqOne hQw hβ
  refine ⟨P.f, ?_, P.Q_f, P.polar_ef⟩
  have hP : P.f = (QuadraticMap.polar Q w w₀)⁻¹ • w₀ -
      Q ((QuadraticMap.polar Q w w₀)⁻¹ • w₀) • w := rfl
  rw [hP]
  exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hw₀) (Submodule.smul_mem _ _ hw)

private theorem eq_span_of_hyperbolic_pair [Module.Finite (ZMod p) U]
    {Q : QuadraticForm (ZMod p) U}
    {W : Submodule (ZMod p) U} {w w' : U} (hW : Module.finrank (ZMod p) W = 2)
    (hw : w ∈ W) (hw' : w' ∈ W) (hw0 : w ≠ 0) (hQw : Q w = 0) (hQw' : Q w' = 0)
    (hβ : QuadraticMap.polar Q w w' = 1) :
    W = Submodule.span (ZMod p) ({w, w'} : Set U) := by
  have hli : LinearIndependent (ZMod p) ![w, w'] := by
    refine (LinearIndependent.pair_iff' hw0).mpr fun a ha => ?_
    have h0 : QuadraticMap.polar Q w w' = 0 := by
      rw [← ha, ClassicalGroups.Orthogonal.polar_smul_right_eq,
        ClassicalGroups.Orthogonal.polar_self_eq_zero hQw, mul_zero]
    rw [hβ] at h0
    exact one_ne_zero h0
  have hfr : Module.finrank (ZMod p) (Submodule.span (ZMod p) (Set.range ![w, w'])) = 2 := by
    rw [finrank_span_eq_card hli]; simp
  have hrange : Set.range ![w, w'] = ({w, w'} : Set U) := by
    ext x; simp [or_comm]
  rw [hrange] at hfr
  symm
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rw [Submodule.span_le]; rintro x (rfl | rfl) <;> assumption
  · rw [hfr, hW]

private theorem exists_sigma_of_mem_span_hyperbolic {Q : QuadraticForm (ZMod p) U} {w w' x : U}
    (hx : x ∈ Submodule.span (ZMod p) ({w, w'} : Set U)) (hQx : Q x ≠ 0) (hQw : Q w = 0)
    (hQw' : Q w' = 0) (hβ : QuadraticMap.polar Q w w' = 1) :
    ∃ σ : ZMod p, σ ≠ 0 ∧ (ClassicalGroups.Orthogonal.reflect Q x) w = σ • w' ∧
      (ClassicalGroups.Orthogonal.reflect Q x) w' = σ⁻¹ • w := by
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hx
  have hQx_eq : Q x = a * b := by
    rw [← hab, QuadraticMap.map_add Q, ClassicalGroups.Orthogonal.map_smul_eq_sq,
      ClassicalGroups.Orthogonal.map_smul_eq_sq, hQw, hQw',
      ClassicalGroups.Orthogonal.polar_smul_left_eq,
      ClassicalGroups.Orthogonal.polar_smul_right_eq, hβ]
    ring
  have ha : a ≠ 0 := fun h => hQx (by rw [hQx_eq, h, zero_mul])
  have hb : b ≠ 0 := fun h => hQx (by rw [hQx_eq, h, mul_zero])
  rw [← hab] at hQx_eq
  refine ⟨-b / a, div_ne_zero (neg_ne_zero.mpr hb) ha, ?_, ?_⟩
  · have hc : b / (a * b) = 1 / a := by field_simp
    rw [ClassicalGroups.Orthogonal.reflect_apply hQx, ← hab,
      QuadraticMap.polar_add_left, ClassicalGroups.Orthogonal.polar_smul_left_eq,
      ClassicalGroups.Orthogonal.polar_smul_left_eq,
      QuadraticMap.polar_comm (x := w') (y := w), hβ,
      ClassicalGroups.Orthogonal.polar_self_eq_zero hQw, hQx_eq,
      show a * 0 + b * 1 = b by ring, hc]
    rw [smul_add, smul_smul, smul_smul, show (1 / a) * a = 1 by field_simp, one_smul,
      show (1 / a) * b = b / a by field_simp]
    rw [show w - (w + (b / a) • w') = -((b / a) • w') by abel, ← neg_smul]
    congr 1
    ring
  · have hc : a / (a * b) = 1 / b := by field_simp
    have hσ : (-b / a)⁻¹ = -a / b := by field_simp
    rw [ClassicalGroups.Orthogonal.reflect_apply hQx, ← hab,
      QuadraticMap.polar_add_left, ClassicalGroups.Orthogonal.polar_smul_left_eq,
      ClassicalGroups.Orthogonal.polar_smul_left_eq,
      ClassicalGroups.Orthogonal.polar_self_eq_zero hQw', hβ, hQx_eq,
      show a * 1 + b * 0 = a by ring, hc, hσ]
    rw [smul_add, smul_smul, smul_smul, show (1 / b) * b = 1 by field_simp, one_smul,
      show (1 / b) * a = a / b by field_simp]
    rw [show w' - ((a / b) • w + w') = -((a / b) • w) by abel, ← neg_smul]
    congr 1
    ring

private theorem exists_sigma_of_mem_reflStab (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) (h4 : Module.finrank (ZMod p) U = 4)
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hoH : IsOrthOn p Q H) {w w' : U}
    (hEeq : HardMathSupport.Kantor79.commutatorSpace (reflStab p H h) =
      Submodule.span (ZMod p) ({w, w'} : Set U))
    (hβ : QuadraticMap.polar Q w w' = 1) (hQw : Q w = 0) (hQw' : Q w' = 0)
    {t : U ≃ₗ[ZMod p] U} (ht : t ∈ reflStab p H h) (htR : IsRefl p t) :
    ∃ σ : ZMod p, σ ≠ 0 ∧ t w = σ • w' ∧ t w' = σ⁻¹ • w := by
  have h3 : 3 ≤ Module.finrank (ZMod p) U := by omega
  have htH : t ∈ H := reflSubgroupIn_le H _ ht
  obtain ⟨x, hxQ, htx, hteq⟩ := exists_root_reflect_of_isIsom hp hQ htR (hoH.isIsom htH)
  have hxeq : x = (-2 : ZMod p)⁻¹ • (t x - x) := by
    rw [htx, show -x - x = (-2 : ZMod p) • x by rw [neg_smul, two_smul]; abel]
    rw [smul_smul, show (-2 : ZMod p)⁻¹ * -2 = 1 from
      inv_mul_cancel₀ (neg_ne_zero.mpr (ZMod.prime_ne_zero p 2 hp)), one_smul]
  have hxmov : x ∈ HardMathSupport.Kantor79.movedSpace t := by
    rw [hxeq]
    exact Submodule.smul_mem _ _ (LinearMap.mem_range_self ((t : U →ₗ[ZMod p] U) - 1) x)
  have hxE : x ∈ HardMathSupport.Kantor79.commutatorSpace (reflStab p H h) := by
    rw [commutatorSpace_reflStab_eq_inf hp hD h4 hQ hoH]
    refine ⟨?_, ?_⟩
    · exact HardMathSupport.Kantor79.movedSpace_le_commutatorSpace htH hxmov
    · rw [(commutatorSpace_eq_ker_of_isCentralizingSplit hp h3 hD.split hD.isRefl).1]
      exact commutatorSpace_reflSubgroupIn_le H _
        (HardMathSupport.Kantor79.movedSpace_le_commutatorSpace ht hxmov)
  obtain ⟨σ, hσ0, hσw, hσw'⟩ := exists_sigma_of_mem_span_hyperbolic (Q := Q)
    (by rw [← hEeq]; exact hxE) hxQ hQw hQw' hβ
  refine ⟨σ, hσ0, ?_, ?_⟩
  · rw [hteq]; exact hσw
  · rw [hteq]; exact hσw'

private theorem exists_refl_mem_reflStab (H : Subgroup (U ≃ₗ[ZMod p] U)) (h : U ≃ₗ[ZMod p] U)
    (hne : reflStab p H h ≠ ⊥) :
    ∃ t ∈ reflStab p H h, IsRefl p t := by
  by_contra hcon
  push Not at hcon
  have hempty : {g : U ≃ₗ[ZMod p] U |
      g ∈ H ∧ IsRefl p g ∧ ∀ v, g v - v ∈ LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)} = ∅ := by
    ext x
    refine ⟨fun hx => False.elim (hcon x (Subgroup.subset_closure hx) hx.2.1), ?_⟩
    simp
  rw [reflStab, reflSubgroupIn, hempty, Subgroup.closure_empty] at hne
  exact hne rfl

private theorem exists_sigma_of_reflStab_ne_bot (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) (h4 : Module.finrank (ZMod p) U = 4)
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hoH : IsOrthOn p Q H) {w w' : U}
    (hEeq : HardMathSupport.Kantor79.commutatorSpace (reflStab p H h) =
      Submodule.span (ZMod p) ({w, w'} : Set U))
    (hβ : QuadraticMap.polar Q w w' = 1) (hQw : Q w = 0) (hQw' : Q w' = 0)
    (hne : reflStab p H h ≠ ⊥) :
    ∃ (t : U ≃ₗ[ZMod p] U) (σ : ZMod p), t ∈ reflStab p H h ∧ IsRefl p t ∧ σ ≠ 0 ∧
      t w = σ • w' ∧ t w' = σ⁻¹ • w := by
  obtain ⟨t, ht, htR⟩ := exists_refl_mem_reflStab H h hne
  obtain ⟨σ, hσ0, hσw, hσw'⟩ :=
    exists_sigma_of_mem_reflStab hp hD h4 hQ hoH hEeq hβ hQw hQw' ht htR
  exact ⟨t, σ, ht, htR, hσ0, hσw, hσw'⟩

private theorem exists_refl_not_invariant_span [Module.Finite (ZMod p) U]
    (hirr₁ : IrredOnSection (reflStab p H h) ⊥
      (HardMathSupport.Kantor79.commutatorSpace (reflStab p H h)))
    {Q : QuadraticForm (ZMod p) U} {w w' : U} {σ₁ : ZMod p}
    (hEeq : HardMathSupport.Kantor79.commutatorSpace (reflStab p H h) =
      Submodule.span (ZMod p) ({w, w'} : Set U))
    (hEfin : Module.finrank (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace (reflStab p H h)) = 2)
    (hβ : QuadraticMap.polar Q w w' = 1) (hQw' : Q w' = 0) :
    ∃ t₂ ∈ reflStab p H h, IsRefl p t₂ ∧
      ¬ ∀ x ∈ Submodule.span (ZMod p) {w + σ₁ • w'}, t₂ x ∈
        Submodule.span (ZMod p) {w + σ₁ • w'} := by
  let L := Submodule.span (ZMod p) {w + σ₁ • w'}
  have hLE : L ≤ HardMathSupport.Kantor79.commutatorSpace (reflStab p H h) := by
    rw [hEeq]
    refine Submodule.span_le.mpr ?_
    rintro x rfl
    exact Submodule.add_mem _ (Submodule.subset_span (Set.mem_insert _ _))
      (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert_of_mem _ rfl)))
  have hx0 : w + σ₁ • w' ≠ 0 := by
    intro hzero
    have hw : w = -σ₁ • w' := by
      rw [add_eq_zero_iff_eq_neg] at hzero; rw [hzero, neg_smul]
    have h0 : QuadraticMap.polar Q w w' = 0 := by
      rw [hw, ClassicalGroups.Orthogonal.polar_smul_left_eq,
        ClassicalGroups.Orthogonal.polar_self_eq_zero hQw', mul_zero]
    rw [hβ] at h0
    exact one_ne_zero h0
  have hLbot : L ≠ ⊥ := fun hbot => hx0 (Submodule.span_singleton_eq_bot.mp hbot)
  have hLne : L ≠ HardMathSupport.Kantor79.commutatorSpace (reflStab p H h) := by
    intro hEq
    have h1 : Module.finrank (ZMod p) L = 1 := finrank_span_singleton hx0
    rw [hEq, hEfin] at h1; omega
  by_contra hcon
  push Not at hcon
  have hinv : ∀ g ∈ reflStab p H h, ∀ x ∈ L, g x ∈ L := by
    intro g hg
    have hgen : reflStab p H h =
        Subgroup.closure {t : U ≃ₗ[ZMod p] U | t ∈ reflStab p H h ∧ IsRefl p t} :=
      reflGen_reflSubgroupIn H _
    rw [hgen] at hg
    exact forall_mem_closure_mapsTo_of_forall
      (S := {t : U ≃ₗ[ZMod p] U | t ∈ reflStab p H h ∧ IsRefl p t})
      (fun t ht => hcon t ht.1 ht.2) g hg
  rcases hirr₁ L bot_le hLE hinv with hbot | htop
  · exact hLbot hbot
  · exact hLne htop

private theorem exists_t_scaling (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) (h4 : Module.finrank (ZMod p) U = 4)
    (hirr₁ : IrredOnSection (reflStab p H h) ⊥
      (HardMathSupport.Kantor79.commutatorSpace (reflStab p H h)))
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hoH : IsOrthOn p Q H) {w w' : U}
    (hEeq : HardMathSupport.Kantor79.commutatorSpace (reflStab p H h) =
      Submodule.span (ZMod p) ({w, w'} : Set U))
    (hEfin : Module.finrank (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace (reflStab p H h)) = 2)
    (hβ : QuadraticMap.polar Q w w' = 1) (hQw : Q w = 0) (hQw' : Q w' = 0)
    (hne : reflStab p H h ≠ ⊥) {f : U} (hf : f ∈ centralizerSpace H) :
    ∃ (t : U ≃ₗ[ZMod p] U) (s : ZMod p), t ∈ reflStab p H h ∧ s ≠ 1 ∧
      t f = f ∧ t w = s • w := by
  obtain ⟨t₁, σ₁, ht1, ht1R, hσ1_0, hσ1w, hσ1w'⟩ :=
    exists_sigma_of_reflStab_ne_bot hp hD h4 hQ hoH hEeq hβ hQw hQw' hne
  obtain ⟨t₂, ht2, ht2R, hnotinv⟩ :=
    exists_refl_not_invariant_span hirr₁ hEeq hEfin hβ hQw'
  obtain ⟨σ₂, hσ2_0, hσ2w, hσ2w'⟩ :=
    exists_sigma_of_mem_reflStab hp hD h4 hQ hoH hEeq hβ hQw hQw' ht2 ht2R
  have hσ2_ne_σ1 : σ₂ ≠ σ₁ := by
    intro heq
    apply hnotinv
    intro x hx
    rw [Submodule.mem_span_singleton] at hx ⊢
    obtain ⟨c, rfl⟩ := hx
    refine ⟨c, ?_⟩
    rw [map_smul, map_add, map_smul, hσ2w, heq, hσ2w', heq, smul_smul, mul_inv_cancel₀ hσ1_0,
      one_smul, add_comm]
  refine ⟨t₁ * t₂, σ₂ * σ₁⁻¹, Subgroup.mul_mem _ ht1 ht2, ?_, ?_, ?_⟩
  · intro h
    apply hσ2_ne_σ1
    have := congrArg (fun x => x * σ₁) h
    simpa [mul_assoc, inv_mul_cancel₀ hσ1_0] using this
  · rw [LinearEquiv.mul_apply]
    have h1 : t₁ ∈ H := reflSubgroupIn_le H _ ht1
    have h2 : t₂ ∈ H := reflSubgroupIn_le H _ ht2
    rw [(mem_centralizerSpace.mp hf) t₂ h2, (mem_centralizerSpace.mp hf) t₁ h1]
  · rw [LinearEquiv.mul_apply, hσ2w, map_smul, hσ1w', smul_smul]

private theorem exists_unipotent_of_t_polar [Module.Finite (ZMod p) U]
    {Q : QuadraticForm (ZMod p) U} (hoH : IsOrthOn p Q H)
    {f : U} (hf : f ∈ centralizerSpace H)
    {w : U} (hwE : w ∈ HardMathSupport.Kantor79.commutatorSpace (reflStab p H h)) (hQw : Q w = 0)
    {a : U} {α : ZMod p} {r : U ≃ₗ[ZMod p] U} (haQ : Q a ≠ 0) (hα : α ≠ 0)
    (ha : a = α • f + w) (hr : r = ClassicalGroups.Orthogonal.reflect Q a) :
    r f = -f - (2 / α) • w ∧ r w = w := by
  have hβfw : QuadraticMap.polar Q f w = 0 := by
    have hwVH : w ∈ HardMathSupport.Kantor79.commutatorSpace H :=
      HardMathSupport.Kantor79.commutatorSpace_mono (reflSubgroupIn_le H _) hwE
    exact polar_eq_zero_of_mem_centralizerSpace (fun x hx => hoH.isIsom hx) hf hwVH
  have hβww : QuadraticMap.polar Q w w = 0 :=
    ClassicalGroups.Orthogonal.polar_self_eq_zero hQw
  have hβaw : QuadraticMap.polar Q a w = 0 := by
    rw [ha, QuadraticMap.polar_add_left, ClassicalGroups.Orthogonal.polar_smul_left_eq,
      hβfw, hβww, mul_zero, add_zero]
  have hβaf : QuadraticMap.polar Q a f = 2 * α * Q f := by
    rw [ha, QuadraticMap.polar_add_left, ClassicalGroups.Orthogonal.polar_smul_left_eq,
      ClassicalGroups.Orthogonal.polar_self_eq_two_mul, QuadraticMap.polar_comm, hβfw,
      add_zero]
    ring
  have hQa : Q a = α ^ 2 * Q f := by
    rw [ha, QuadraticMap.map_add Q, ClassicalGroups.Orthogonal.map_smul_eq_sq,
      ClassicalGroups.Orthogonal.polar_smul_left_eq, hβfw, mul_zero, add_zero, hQw]
    ring
  have hQf : Q f ≠ 0 := by
    intro h
    apply haQ
    rw [hQa, h, mul_zero]
  have hraf : r f = -f - (2 / α) • w := by
    rw [hr, ClassicalGroups.Orthogonal.reflect_apply haQ, hβaf, hQa, ha]
    field_simp [hQf, hα]
    rw [smul_add, smul_smul, div_mul_cancel₀ _ hα]
    module
  have hraw : r w = w := by
    rw [hr, ClassicalGroups.Orthogonal.reflect_apply haQ, hβaw, zero_div, zero_smul, sub_zero]
  exact ⟨hraf, hraw⟩

private theorem Q_ne_zero_of_span (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) (h4 : Module.finrank (ZMod p) U = 4)
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hoH : IsOrthOn p Q H) {f : U} (hf : f ∈ centralizerSpace H) (hf0 : f ≠ 0)
    (hspan : centralizerSpace H = Submodule.span (ZMod p) {f}) :
    Q f ≠ 0 ∧ QuadraticMap.polar Q f f ≠ 0 := by
  have hsplitH : SplitSupport H 3 := by simpa [h4] using hD.setting.sub.2.1
  have hVH : HardMathSupport.Kantor79.commutatorSpace H =
      LinearMap.ker (QuadraticMap.polarBilin Q f) :=
    commutatorSpace_eq_ker_polar hD h4 hQ hoH hf hspan
  have hfVH : f ∉ HardMathSupport.Kantor79.commutatorSpace H := by
    intro hmem
    have hbot : f ∈ (⊥ : Submodule (ZMod p) U) := by
      rw [← hsplitH.1.inf_eq_bot]
      exact ⟨hmem, hf⟩
    exact hf0 (by simpa using hbot)
  have hQf : Q f ≠ 0 := by
    intro h0
    exact hfVH (by
      rw [hVH, LinearMap.mem_ker, QuadraticMap.polarBilin_apply_apply,
        ClassicalGroups.Orthogonal.polar_self_eq_zero h0])
  refine ⟨hQf, ?_⟩
  rw [ClassicalGroups.Orthogonal.polar_self_eq_two_mul]
  exact mul_ne_zero (ZMod.prime_ne_zero p 2 hp) hQf

private theorem unipotent_formula {g : U ≃ₗ[ZMod p] U} {f w : U} (hgw : g w = w)
    (hgf : g f - f ∈ Submodule.span (ZMod p) ({w} : Set U))
    (hspan : ∀ x : U, g x - x ∈ Submodule.span (ZMod p) ({f, w} : Set U)) (k : ℕ) :
    ∀ x : U, (g ^ k) x = x + (k : ZMod p) • (g x - x) +
      ((Nat.choose k 2 : ℕ) : ZMod p) • (g (g x - x) - (g x - x)) := by
  let N : U →ₗ[ZMod p] U := (g : U →ₗ[ZMod p] U) - 1
  have hNw : N w = 0 := by
    change g w - w = 0
    rw [hgw, sub_self]
  have hNf : N f ∈ Submodule.span (ZMod p) ({w} : Set U) := by
    simpa only [N, LinearMap.sub_apply, Module.End.one_apply, LinearEquiv.coe_coe] using hgf
  have hNmem : ∀ x : U, N x ∈ Submodule.span (ZMod p) ({f, w} : Set U) := by
    intro x
    simpa only [N, LinearMap.sub_apply, Module.End.one_apply, LinearEquiv.coe_coe] using hspan x
  have hNzerow : ∀ y ∈ Submodule.span (ZMod p) ({w} : Set U), N y = 0 := by
    intro y hy
    rw [Submodule.mem_span_singleton] at hy
    obtain ⟨c, rfl⟩ := hy
    rw [map_smul, hNw, smul_zero]
  have hN2 : ∀ x : U, N (N x) ∈ Submodule.span (ZMod p) ({w} : Set U) := by
    intro x
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp (hNmem x)
    rw [← hab, map_add, map_smul, map_smul, hNw, smul_zero, add_zero]
    exact Submodule.smul_mem _ a hNf
  have hN3 : ∀ x : U, N (N (N x)) = 0 := fun x => hNzerow _ (hN2 x)
  have hgN : ∀ x : U, g x = x + N x := by
    intro x
    change g x = x + (g x - x)
    abel
  have hformula : ∀ j : ℕ, ∀ x : U,
      (g ^ j) x = x + (j : ZMod p) • N x +
        ((Nat.choose j 2 : ℕ) : ZMod p) • N (N x) := by
    intro j
    induction j with
    | zero => intro x; simp
    | succ j ih =>
        intro x
        rw [pow_succ', LinearEquiv.mul_apply, ih x, hgN]
        rw [map_add, map_add, map_smul, map_smul, hN3 x, smul_zero, add_zero]
        have hj : ((j + 1 : ℕ) : ZMod p) = (j : ZMod p) + 1 := by push_cast; ring
        have hc : ((Nat.choose (j + 1) 2 : ℕ) : ZMod p) =
            ((Nat.choose j 2 : ℕ) : ZMod p) + (j : ZMod p) := by
          rw [Nat.choose_succ_succ' j 1, Nat.choose_one_right]
          push_cast
          ring
        rw [hj, hc]
        module
  intro x
  simpa only [N, LinearMap.sub_apply, Module.End.one_apply, LinearEquiv.coe_coe] using hformula k x

private theorem pow_eq_one_of_unipotent {g : U ≃ₗ[ZMod p] U} {f w : U} (hp : p ≠ 2)
    (hgw : g w = w)
    (hgf : g f - f ∈ Submodule.span (ZMod p) ({w} : Set U))
    (hspan : ∀ x : U, g x - x ∈ Submodule.span (ZMod p) ({f, w} : Set U)) :
    g ^ p = 1 := by
  have hp0 : (p : ZMod p) = 0 := ZMod.natCast_self p
  have hpchoose : ((Nat.choose p 2 : ℕ) : ZMod p) = 0 := by
    have h2p : 2 < p := lt_of_le_of_ne (Fact.out : p.Prime).two_le hp.symm
    exact (CharP.cast_eq_zero_iff (ZMod p) p (Nat.choose p 2)).mpr
      (Nat.Prime.dvd_choose_self (Fact.out : p.Prime) (by norm_num) h2p)
  ext x
  rw [unipotent_formula hgw hgf hspan p x, hp0, hpchoose]
  simp

private theorem exists_mixed_root_of_forall_polar_sq_eq (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] (hD : LemmaTwoSevenData p G H B h)
    (h4 : Module.finrank (ZMod p) U = 4)
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hoH : IsOrthOn p Q H) (hB : ∀ g ∈ B, IsIsom p Q g) {f : U}
    (hf : f ∈ centralizerSpace H) (hf0 : f ≠ 0)
    (hall : ∀ b ∈ B, QuadraticMap.polarBilin Q (b f) f ^ 2 =
      QuadraticMap.polarBilin Q f f ^ 2) :
    ∃ (a w : U) (α : ZMod p) (r : U ≃ₗ[ZMod p] U),
      Q a ≠ 0 ∧ α ≠ 0 ∧ r ∈ B ∧ r = ClassicalGroups.Orthogonal.reflect Q a ∧
        a = α • f + w ∧ w ≠ 0 ∧
          w ∈ HardMathSupport.Kantor79.commutatorSpace (reflStab p H h) ∧ Q w = 0 := by
  have h3 : 3 ≤ Module.finrank (ZMod p) U := by have := hD.setting.four_le; omega
  have hsplitH : SplitSupport H 3 := by simpa [h4] using hD.setting.sub.2.1
  have hspan : centralizerSpace H = Submodule.span (ZMod p) {f} := by
    refine eq_span_singleton_of_mem_of_finrank_eq_one ?_ hf hf0
    have h := hsplitH.finrank_centralizerSpace
    omega
  obtain ⟨hQf, hβff⟩ := Q_ne_zero_of_span hp hD h4 hQ hoH hf hf0 hspan
  have hVB : HardMathSupport.Kantor79.commutatorSpace B =
      LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1) :=
    (commutatorSpace_eq_ker_of_isCentralizingSplit hp h3 hD.split hD.isRefl).1
  obtain ⟨e, heQ, hee, hheq⟩ := exists_root_reflect_of_isIsom hp hQ hD.isRefl
    (hoH.isIsom hD.mem)
  have heVH : e ∈ HardMathSupport.Kantor79.commutatorSpace H :=
    HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hD.mem
      (HardMathSupport.Kantor79.mem_movedSpace_of_apply_eq_neg
        (ZMod.prime_ne_zero p 2 hp) hee)
  have hVBker : HardMathSupport.Kantor79.commutatorSpace B =
      LinearMap.ker (QuadraticMap.polarBilin Q e) :=
    commutatorSpace_eq_ker_polar_of_reflection hp hD hheq heQ
  have hEfin : Module.finrank (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace (reflStab p H h)) = 2 :=
    finrank_commutatorSpace_reflStab_eq_two hp hD h4 hQ hoH heQ heVH hVBker
  have hVBfin : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace B) = 3 := by
    have h := hD.split.2.2.1.2.1
    rw [h4] at h
    exact h
  obtain ⟨a, w, α, r, haQ, hα, hwE, hw0, ha, hrB, hr⟩ :=
    exists_root_mixed hp hD h4 hQ hoH hB hf hf0 hspan hVB hEfin hVBfin
  have hQw : Q w = 0 :=
    isSingular_of_forall_polar_sq_eq hp hD h4 hQ hoH hB hf hspan hβff hall haQ hα hwE ha
      hrB hr
  exact ⟨a, w, α, r, haQ, hα, hrB, hr, ha, hw0, hwE, hQw⟩

private theorem exists_rotation_of_hyperbolic (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) (h4 : Module.finrank (ZMod p) U = 4)
    (hirr₁ : IrredOnSection (reflStab p H h) ⊥
      (HardMathSupport.Kantor79.commutatorSpace (reflStab p H h)))
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hoH : IsOrthOn p Q H) {w : U}
    (hwE : w ∈ HardMathSupport.Kantor79.commutatorSpace (reflStab p H h)) (hw0 : w ≠ 0)
    (hQw : Q w = 0) {f : U} (hf : f ∈ centralizerSpace H) :
    ∃ (w' : U) (t : U ≃ₗ[ZMod p] U) (s : ZMod p), Q w' = 0 ∧
      QuadraticMap.polar Q w w' = 1 ∧ t ∈ reflStab p H h ∧ s ≠ 1 ∧ t f = f ∧ t w = s • w := by
  obtain ⟨e, heQ, hee, hheq⟩ := exists_root_reflect_of_isIsom hp hQ hD.isRefl
    (hoH.isIsom hD.mem)
  have heVH : e ∈ HardMathSupport.Kantor79.commutatorSpace H :=
    HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hD.mem
      (HardMathSupport.Kantor79.mem_movedSpace_of_apply_eq_neg
        (ZMod.prime_ne_zero p 2 hp) hee)
  have hVBker : HardMathSupport.Kantor79.commutatorSpace B =
      LinearMap.ker (QuadraticMap.polarBilin Q e) :=
    commutatorSpace_eq_ker_polar_of_reflection hp hD hheq heQ
  have hEeq : HardMathSupport.Kantor79.commutatorSpace (reflStab p H h) =
      HardMathSupport.Kantor79.commutatorSpace H ⊓
        HardMathSupport.Kantor79.commutatorSpace B :=
    commutatorSpace_reflStab_eq_inf hp hD h4 hQ hoH
  have hEfin : Module.finrank (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace (reflStab p H h)) = 2 :=
    finrank_commutatorSpace_reflStab_eq_two hp hD h4 hQ hoH heQ heVH hVBker
  have hEnd : ClassicalGroups.Orthogonal.PolarNondegOn Q
      (HardMathSupport.Kantor79.commutatorSpace (reflStab p H h)) := by
    rw [hEeq, hVBker, ← ker_reflect_sub_one_eq_ker_polar heQ, ← hheq]
    exact polarNondegOn_commutatorSpace_reflStab hp hQ hoH hD.setting.sub.2.1
      heVH heQ hheq
  obtain ⟨w', hw'E, hQw', hβ⟩ := exists_hyperbolic_partner hEnd hwE hw0 hQw
  have hEspan : HardMathSupport.Kantor79.commutatorSpace (reflStab p H h) =
      Submodule.span (ZMod p) ({w, w'} : Set U) :=
    eq_span_of_hyperbolic_pair hEfin hwE hw'E hw0 hQw hQw' hβ
  have hne : reflStab p H h ≠ ⊥ := by
    intro hbot
    have h0 : HardMathSupport.Kantor79.commutatorSpace (reflStab p H h) = ⊥ := by
      rw [hbot]
      ext y
      simp [HardMathSupport.Kantor79.commutatorSpace]
    rw [h0, finrank_bot] at hEfin
    omega
  obtain ⟨t, s, ht, hs1, htf, htw⟩ :=
    exists_t_scaling hp hD h4 hirr₁ hQ hoH hEspan hEfin hβ hQw hQw' hne hf
  exact ⟨w', t, s, hQw', hβ, ht, hs1, htf, htw⟩

private theorem exists_conj_unipotent [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h)
    {Q : QuadraticForm (ZMod p) U} (hoH : IsOrthOn p Q H) {f a w : U} {α s : ZMod p}
    {r t : U ≃ₗ[ZMod p] U}
    (hrB : r ∈ B) (ht : t ∈ reflStab p H h) (haQ : Q a ≠ 0) (hα : α ≠ 0)
    (ha : a = α • f + w) (hr : r = ClassicalGroups.Orthogonal.reflect Q a)
    (hwE : w ∈ HardMathSupport.Kantor79.commutatorSpace (reflStab p H h)) (hw0 : w ≠ 0)
    (hQw : Q w = 0) (htf : t f = f) (htw : t w = s • w) (hf : f ∈ centralizerSpace H) :
    ∃ u : U ≃ₗ[ZMod p] U, u ∈ B ∧ u = t * r * t⁻¹ ∧
      u f = -f - (2 * s / α) • w ∧ u w = w ∧
        r f = -f - (2 / α) • w ∧ r w = w := by
  obtain ⟨hrf, hrw⟩ :=
    exists_unipotent_of_t_polar hoH hf hwE hQw haQ hα ha hr
  have hs0 : s ≠ 0 := by
    intro hs
    rw [hs, zero_smul] at htw
    exact hw0 (t.injective (by rw [htw, map_zero]))
  have htB : t ∈ B := hD.split.2.2.2.2 ht
  have htinvf : t⁻¹ f = f := by
    simpa using (congrArg (fun x => t⁻¹ x) htf).symm
  have htinvw : t⁻¹ w = s⁻¹ • w := by
    have h : w = s • t⁻¹ w := by
      simpa using congrArg (fun x => t⁻¹ x) htw
    calc t⁻¹ w = s⁻¹ • (s • t⁻¹ w) := by rw [smul_smul, inv_mul_cancel₀ hs0, one_smul]
      _ = s⁻¹ • w := by rw [← h]
  refine ⟨t * r * t⁻¹, ?_, rfl, ?_, ?_, hrf, hrw⟩
  · exact B.mul_mem (B.mul_mem htB hrB) (B.inv_mem htB)
  · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, htinvf, hrf, map_sub, map_neg, map_smul,
      htf, htw, smul_smul]
    module
  · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, htinvw, map_smul, hrw, map_smul, htw,
      smul_smul, inv_mul_cancel₀ hs0, one_smul]

private theorem exists_g_of_conj_unipotent (hp : p ≠ 2) {f w : U}
    {α s : ZMod p} {r u : U ≃ₗ[ZMod p] U} (hrB : r ∈ B) (huB : u ∈ B) (hα : α ≠ 0)
    (huf : u f = -f - (2 * s / α) • w) (huw : u w = w)
    (hrf : r f = -f - (2 / α) • w) (hrw : r w = w) (hw0 : w ≠ 0) (hs1 : s ≠ 1) :
    ∃ g : U ≃ₗ[ZMod p] U, g ∈ B ∧ g = r * u ∧ g w = w ∧
      g f = f + (2 * (1 - s) / α) • w ∧ g f ≠ f := by
  refine ⟨r * u, B.mul_mem hrB huB, rfl, ?_, ?_, ?_⟩
  · rw [LinearEquiv.mul_apply, huw, hrw]
  · rw [LinearEquiv.mul_apply, huf, map_sub, map_neg, map_smul, hrf, hrw]
    module
  · intro h
    have hcoef : (2 * (1 - s) / α) ≠ 0 := by
      refine div_ne_zero (mul_ne_zero (ZMod.prime_ne_zero p 2 hp) ?_) hα
      exact sub_ne_zero.mpr hs1.symm
    have hcw : (2 * (1 - s) / α) • w ≠ 0 := smul_ne_zero hcoef hw0
    apply hcw
    have h0 := congrArg (fun z => z - f) h
    rw [show (r * u) f = f + (2 * (1 - s) / α) • w from by
      rw [LinearEquiv.mul_apply, huf, map_sub, map_neg, map_smul, hrf, hrw]
      module] at h0
    simpa using h0

private theorem mul_conj_reflect_sub_mem_span {Q : QuadraticForm (ZMod p) U} {f a w : U}
    {α s : ZMod p} {r t u : U ≃ₗ[ZMod p] U} (hr : r = ClassicalGroups.Orthogonal.reflect Q a)
    (haQ : Q a ≠ 0) (ha : a = α • f + w) (htf : t f = f) (htw : t w = s • w)
    (hu : u = t * r * t⁻¹) (x : U) :
    (r * u) x - x ∈ Submodule.span (ZMod p) ({f, w} : Set U) := by
  have ha_span : a ∈ Submodule.span (ZMod p) ({f, w} : Set U) := by
    rw [ha]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert f {w})))
      (Submodule.subset_span (Set.mem_insert_of_mem f rfl))
  have hta : t a = α • f + s • w := by
    rw [ha, map_add, map_smul, htf, htw]
  have hta_span : t a ∈ Submodule.span (ZMod p) ({f, w} : Set U) := by
    rw [hta]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert f {w})))
      (Submodule.smul_mem _ s (Submodule.subset_span (Set.mem_insert_of_mem f rfl)))
  have hr_mem : ∀ y : U, r y - y ∈ Submodule.span (ZMod p) ({a} : Set U) := by
    intro y
    rw [hr, ClassicalGroups.Orthogonal.reflect_apply haQ]
    have hsub : y - (QuadraticMap.polar Q a y / Q a) • a - y =
        -((QuadraticMap.polar Q a y / Q a) • a) := by abel
    rw [hsub]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span rfl))
  have hu_mem : ∀ y : U, u y - y ∈ Submodule.span (ZMod p) ({t a} : Set U) := by
    intro y
    have hy : u y - y = t (r (t⁻¹ y) - t⁻¹ y) := by
      rw [hu, LinearEquiv.mul_apply, LinearEquiv.mul_apply, map_sub]
      rw [show t (t⁻¹ y) = y by
        rw [← LinearEquiv.mul_apply, mul_inv_cancel]
        rfl]
    rw [hy]
    have hmap : (Submodule.span (ZMod p) ({a} : Set U)).map (t : U →ₗ[ZMod p] U) =
        Submodule.span (ZMod p) ({t a} : Set U) := by
      rw [Submodule.map_span]; simp
    rw [← hmap]
    exact Submodule.mem_map_of_mem (hr_mem (t⁻¹ y))
  have h1 : u x - x ∈ Submodule.span (ZMod p) ({f, w} : Set U) := by
    refine Submodule.span_le.mpr ?_ (hu_mem x)
    rintro y rfl
    exact hta_span
  have h2 : r (u x) - u x ∈ Submodule.span (ZMod p) ({f, w} : Set U) := by
    refine Submodule.span_le.mpr ?_ (hr_mem (u x))
    rintro y rfl
    exact ha_span
  have hsum : (r * u) x - x = (r (u x) - u x) + (u x - x) := by
    rw [LinearEquiv.mul_apply]
    abel
  rw [hsum]
  exact Submodule.add_mem _ h2 h1

private theorem exists_pow_p_mem_of_mixed (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h)
    {Q : QuadraticForm (ZMod p) U} (hoH : IsOrthOn p Q H) {f a w : U} {α s : ZMod p}
    {r t : U ≃ₗ[ZMod p] U}
    (hrB : r ∈ B) (ht : t ∈ reflStab p H h) (haQ : Q a ≠ 0) (hα : α ≠ 0)
    (ha : a = α • f + w) (hr : r = ClassicalGroups.Orthogonal.reflect Q a)
    (hwE : w ∈ HardMathSupport.Kantor79.commutatorSpace (reflStab p H h)) (hw0 : w ≠ 0)
    (hQw : Q w = 0) (htf : t f = f) (htw : t w = s • w) (hs1 : s ≠ 1)
    (hf : f ∈ centralizerSpace H) :
    ∃ g ∈ B, g ^ p = 1 ∧ g f ≠ f := by
  obtain ⟨u, huB, hu, huf, huw, hrf, hrw⟩ :=
    exists_conj_unipotent hD hoH hrB ht haQ hα ha hr hwE hw0 hQw htf htw hf
  obtain ⟨g, hgB, hg, hgw, hgf, hgfne⟩ :=
    exists_g_of_conj_unipotent hp hrB huB hα huf huw hrf hrw hw0 hs1
  have hgf_sub : g f - f ∈ Submodule.span (ZMod p) ({w} : Set U) := by
    rw [hgf, add_sub_cancel_left]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton w))
  have hspan : ∀ x : U, g x - x ∈ Submodule.span (ZMod p) ({f, w} : Set U) := by
    intro x
    have := mul_conj_reflect_sub_mem_span (Q := Q) hr haQ ha htf htw hu x
    simpa [hg] using this
  exact ⟨g, hgB, pow_eq_one_of_unipotent hp hgw hgf_sub hspan, hgfne⟩

private theorem exists_pow_p_mem_of_forall_polar_sq_eq (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] (hD : LemmaTwoSevenData p G H B h)
    (h4 : Module.finrank (ZMod p) U = 4)
    (hirr₁ : IrredOnSection (reflStab p H h) ⊥
      (HardMathSupport.Kantor79.commutatorSpace (reflStab p H h)))
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hoH : IsOrthOn p Q H) (hB : ∀ g ∈ B, IsIsom p Q g) {f : U}
    (hf : f ∈ centralizerSpace H) (hf0 : f ≠ 0)
    (hall : ∀ b ∈ B, QuadraticMap.polarBilin Q (b f) f ^ 2 =
      QuadraticMap.polarBilin Q f f ^ 2) :
    ∃ g ∈ B, g ^ p = 1 ∧ g f ≠ f := by
  obtain ⟨a, w, α, r, haQ, hα, hrB, hr, ha, hw0, hwE, hQw⟩ :=
    exists_mixed_root_of_forall_polar_sq_eq hp hD h4 hQ hoH hB hf hf0 hall
  obtain ⟨w', t, s, -, hβ, ht, hs1, htf, htw⟩ :=
    exists_rotation_of_hyperbolic hp hD h4 hirr₁ hQ hoH hwE hw0 hQw hf
  exact exists_pow_p_mem_of_mixed hp hD hoH hrB ht haQ hα ha hr hwE hw0 hQw htf htw hs1 hf

theorem exists_mem_polar_sq_ne (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) (h4 : Module.finrank (ZMod p) U = 4)
    (hirr₁ : IrredOnSection (reflStab p H h) ⊥
      (HardMathSupport.Kantor79.commutatorSpace (reflStab p H h)))
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hoH : IsOrthOn p Q H) (hB : ∀ g ∈ B, IsIsom p Q g) (hcop : ∀ g ∈ B, g ^ p = 1 → g = 1)
    {f : U} (hf : f ∈ centralizerSpace H) (hf0 : f ≠ 0) :
    ∃ b ∈ B, QuadraticMap.polarBilin Q (b f) f ^ 2 ≠ QuadraticMap.polarBilin Q f f ^ 2 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨g, hgB, hgp, hgfne⟩ :=
    exists_pow_p_mem_of_forall_polar_sq_eq hp hD h4 hirr₁ hQ hoH hB hf hf0 hcon
  exact hgfne (by rw [hcop g hgB hgp]; rfl)

theorem exists_isOrthOvergroup_of_mem_map_ne (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h)
    (hcomp : ∃ Q₁ Q₂ : QuadraticForm (ZMod p) U, (QuadraticMap.polarBilin Q₁).Nondegenerate ∧
      IsOrthOn p Q₁ H ∧ (QuadraticMap.polarBilin Q₂).Nondegenerate ∧ (∀ g ∈ B, IsIsom p Q₂ g) ∧
      ∃ c : ZMod p, c ≠ 0 ∧
        ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace (reflStab p H h), Q₂ v = c * Q₁ v)
    {x : U ≃ₗ[ZMod p] U} (hx : x ∈ B)
    (hxV : centralizerSpace (reflStab p H h) ⊓ HardMathSupport.Kantor79.commutatorSpace B ≤
      (HardMathSupport.Kantor79.commutatorSpace (reflStab p H h)).map (x : U →ₗ[ZMod p] U)) :
    ∃ K, IsOrthOvergroup p G H K := by
  obtain ⟨Q, hQ, hoH, hBQ⟩ := exists_isOrthOn_of_lemmaTwoSevenData hp hD hcomp
  have h3 : 3 ≤ Module.finrank (ZMod p) U := by have := hD.setting.four_le; omega
  have hVB : HardMathSupport.Kantor79.commutatorSpace B =
      LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1) :=
    (commutatorSpace_eq_ker_of_isCentralizingSplit hp h3 hD.split hD.isRefl).1
  have hfix : centralizerSpace H ≤ HardMathSupport.Kantor79.commutatorSpace B := by
    intro v hv
    rw [hVB, LinearMap.mem_ker]
    have hv' : h v = v := mem_centralizerSpace.mp hv h hD.mem
    simpa using sub_eq_zero.mpr hv'
  have hVHH : centralizerSpace H ≤ centralizerSpace (reflStab p H h) :=
    centralizerSpace_le_of_le (reflSubgroupIn_le H _)
  have hEE : HardMathSupport.Kantor79.commutatorSpace (reflStab p H h) ≤
      HardMathSupport.Kantor79.commutatorSpace H :=
    HardMathSupport.Kantor79.commutatorSpace_mono (reflSubgroupIn_le H _)
  exact exists_isOrthOvergroup_of_isIsom hp hD.setting hQ hoH (hD.split.1 hx) (hBQ x hx)
    ((le_inf hVHH hfix).trans (hxV.trans (Submodule.map_mono hEE)))

end CFSG.StandardType.ZS

end
