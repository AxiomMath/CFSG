module

public import CFSG.ClassicalGroups.Orthogonal.TwoHyperplanes.Basic
public import CFSG.LocalAnalysis.StandardType.ZS.OrthExtWitt
public import CFSG.RankThree.Classical.OddQuadraticFrame

public section

namespace CFSG.StandardType.ZS

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def reflStab (p : ℕ) {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    (H : Subgroup (U ≃ₗ[ZMod p] U)) (h : U ≃ₗ[ZMod p] U) : Subgroup (U ≃ₗ[ZMod p] U) :=
  reflSubgroupIn p H (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1))

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]
  {Q : QuadraticForm (ZMod p) U} {X : Subgroup (U ≃ₗ[ZMod p] U)}

theorem polar_eq_zero_of_mem_centralizerSpace (hX : ∀ g ∈ X, IsIsom p Q g) {u v : U}
    (hu : u ∈ centralizerSpace X) (hv : v ∈ HardMathSupport.Kantor79.commutatorSpace X) :
    QuadraticMap.polar Q u v = 0 := by
  have hmem : HardMathSupport.Kantor79.commutatorSpace X ≤
      LinearMap.ker (QuadraticMap.polarBilin Q u) := by
    rw [HardMathSupport.Kantor79.commutatorSpace, Submodule.span_le]
    rintro w ⟨x, hx, z, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, QuadraticMap.polarBilin_apply_apply,
      QuadraticMap.polar_sub_right]
    have hfix : x u = u := (mem_centralizerSpace.mp hu) x hx
    have hpol := (hX x hx).polar_apply u z
    rw [hfix] at hpol
    rw [hpol, sub_self]
  exact LinearMap.mem_ker.mp (hmem hv)

theorem mem_commutatorSpace_iff_forall_polar_eq_zero [Module.Finite (ZMod p) U]
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hX : ∀ g ∈ X, IsIsom p Q g)
    (hc : IsCompl (HardMathSupport.Kantor79.commutatorSpace X) (centralizerSpace X)) {v : U} :
    v ∈ HardMathSupport.Kantor79.commutatorSpace X ↔
      ∀ u ∈ centralizerSpace X, QuadraticMap.polar Q u v = 0 := by
  constructor
  · intro hv u hu
    exact polar_eq_zero_of_mem_centralizerSpace hX hu hv
  · intro hv
    obtain ⟨v₁, hv₁, v₂, hv₂, hsum⟩ :=
      Submodule.mem_sup.mp (hc.sup_eq_top ▸ (Submodule.mem_top : v ∈ (⊤ : Submodule (ZMod p) U)))
    have hv₂ : v₂ = 0 := by
      apply hQ.1 v₂
      intro z
      rw [QuadraticMap.polarBilin_apply_apply]
      obtain ⟨w, hw, u, hu, rfl⟩ :=
        Submodule.mem_sup.mp (hc.sup_eq_top ▸ (Submodule.mem_top : z ∈ (⊤ : Submodule (ZMod p) U)))
      rw [QuadraticMap.polar_add_right]
      have h1 : QuadraticMap.polar Q v₂ w = 0 :=
        polar_eq_zero_of_mem_centralizerSpace hX hv₂ hw
      have h2 : QuadraticMap.polar Q v₂ u = 0 := by
        rw [QuadraticMap.polar_comm]
        have h := hv u hu
        rw [← hsum, QuadraticMap.polar_add_right,
          polar_eq_zero_of_mem_centralizerSpace hX hu hv₁, zero_add] at h
        exact h
      rw [h1, h2, add_zero]
    rw [← hsum, hv₂, add_zero]
    exact hv₁

theorem polarNondegOn_commutatorSpace (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hX : ∀ g ∈ X, IsIsom p Q g)
    (hc : IsCompl (HardMathSupport.Kantor79.commutatorSpace X) (centralizerSpace X)) :
    ClassicalGroups.Orthogonal.PolarNondegOn Q (HardMathSupport.Kantor79.commutatorSpace X) := by
  intro x hx hxorth
  apply hQ.1 x
  intro z
  rw [QuadraticMap.polarBilin_apply_apply]
  obtain ⟨w, hw, u, hu, rfl⟩ :=
    Submodule.mem_sup.mp (hc.sup_eq_top ▸ (Submodule.mem_top : z ∈ (⊤ : Submodule (ZMod p) U)))
  rw [QuadraticMap.polar_add_right]
  have h1 : QuadraticMap.polar Q x w = 0 := hxorth w hw
  have h2 : QuadraticMap.polar Q x u = 0 := by
    rw [QuadraticMap.polar_comm]
    exact polar_eq_zero_of_mem_centralizerSpace hX hu hx
  rw [h1, h2, add_zero]

theorem polarNondegOn_commutatorSpace_reflStab (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {H : Subgroup (U ≃ₗ[ZMod p] U)} (hQH : IsOrthOn p Q H) {m : ℕ} (hs : SplitSupport H m)
    {e : U} (heV : e ∈ HardMathSupport.Kantor79.commutatorSpace H) (hQe : Q e ≠ 0)
    {h : U ≃ₗ[ZMod p] U} (hh_eq : h = CFSG.ClassicalGroups.Orthogonal.reflect Q e) :
    ClassicalGroups.Orthogonal.PolarNondegOn Q
      (HardMathSupport.Kantor79.commutatorSpace H ⊓
        LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)) := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hS : ClassicalGroups.Orthogonal.PolarNondegOn Q
      (HardMathSupport.Kantor79.commutatorSpace H) :=
    polarNondegOn_commutatorSpace hQ (fun g hg => hQH.isIsom hg) hs.1
  have hker : LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1) =
      LinearMap.ker (QuadraticMap.polarBilin Q e) := by
    rw [hh_eq]
    ext x
    change CFSG.ClassicalGroups.Orthogonal.reflect Q e x - x = 0 ↔
      (QuadraticMap.polarBilin Q e) x = 0
    constructor
    · intro hx
      have hfix : CFSG.ClassicalGroups.Orthogonal.reflect Q e x = x := sub_eq_zero.mp hx
      rw [CFSG.ClassicalGroups.Orthogonal.reflect_apply hQe] at hfix
      have hsmul : (QuadraticMap.polar Q e x / Q e) • e = 0 := sub_eq_self.mp hfix
      have hdiv : QuadraticMap.polar Q e x / Q e = 0 :=
        (smul_eq_zero.mp hsmul).resolve_right (fun h0 => hQe (by rw [h0]; exact map_zero Q))
      rw [QuadraticMap.polarBilin_apply_apply]
      exact (div_eq_zero_iff.mp hdiv).resolve_right hQe
    · intro hx
      rw [QuadraticMap.polarBilin_apply_apply] at hx
      rw [CFSG.ClassicalGroups.Orthogonal.reflect_apply_of_polar_eq_zero hx]
      exact sub_self x
  rw [hker]
  exact ClassicalGroups.Orthogonal.PolarNondegOn.inf_ker h2 hS heV hQe

theorem reflect_mem_reflStab (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {Q : QuadraticForm (ZMod p) U} {H : Subgroup (U ≃ₗ[ZMod p] U)} {h : U ≃ₗ[ZMod p] U}
    {w : U} (hw : w ∈ LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1))
    (hQw : Q w ≠ 0) (hwH : ClassicalGroups.Orthogonal.reflect Q w ∈ H) :
    ClassicalGroups.Orthogonal.reflect Q w ∈ reflStab p H h := by
  refine mem_reflSubgroupIn_of_movedSpace_le hwH (isRefl_reflect hp hQw) ?_
  rw [movedSpace_reflect_eq_span hp hQw]
  exact Submodule.span_le.mpr (fun x hx => by
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact hw)

private theorem mem_commutatorSpace_reflStab_of_mem (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (_hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {h : U ≃ₗ[ZMod p] U} {a : U}
    (haW : a ∈ LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1))
    (haX : ClassicalGroups.Orthogonal.reflect Q a ∈ X) (haQ : Q a ≠ 0) :
    a ∈ HardMathSupport.Kantor79.commutatorSpace (reflStab p X h) := by
  have hgen : ClassicalGroups.Orthogonal.reflect Q a ∈ reflStab p X h := by
    refine Subgroup.subset_closure ⟨haX, isRefl_reflect hp haQ, fun v => ?_⟩
    have hv : ClassicalGroups.Orthogonal.reflect Q a v - v =
        -((QuadraticMap.polar Q a v / Q a) • a) := by
      rw [ClassicalGroups.Orthogonal.reflect_apply haQ]
      abel
    rw [hv]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ haW)
  have hmove : ClassicalGroups.Orthogonal.reflect Q a a - a ∈
      HardMathSupport.Kantor79.commutatorSpace (reflStab p X h) :=
    Submodule.subset_span ⟨_, hgen, a, rfl⟩
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hval : ClassicalGroups.Orthogonal.reflect Q a a - a = (-2 : ZMod p) • a := by
    rw [reflect_apply_self haQ, neg_smul, two_smul]
    abel
  have haeq : a = (-2 : ZMod p)⁻¹ •
      (ClassicalGroups.Orthogonal.reflect Q a a - a) := by
    rw [hval, smul_smul, inv_mul_cancel₀ (neg_ne_zero.mpr h2), one_smul]
  rw [haeq]
  exact Submodule.smul_mem _ _ hmove

private theorem exists_class_root_of_ne_three (hp : p ≠ 2) (hp3 : p ≠ 3)
    {W : Type*} [AddCommGroup W] [Module (ZMod p) W] {B : QuadraticForm (ZMod p) W}
    {v w : W} {c μ : ZMod p} (hv : B v = c) (hw : B w = μ)
    (hvw : QuadraticMap.polar B v w = 0)
    (hc : c ≠ 0) (hμ : μ ≠ 0) (hμc : μ ≠ c) :
    ∃ (α β : ZMod p), β ≠ 0 ∧ B (α • v + β • w) = c := by
  set ν : ZMod p := μ / c with hνdef
  have hμν : μ = ν * c := by
    rw [hνdef]
    exact (div_mul_cancel₀ μ hc).symm
  have hν0 : ν ≠ 0 := by rw [hνdef]; exact div_ne_zero hμ hc
  have hν1 : ν ≠ 1 := by
    intro h
    apply hμc
    rw [hμν, h, one_mul]
  have hchoose : ∃ t : ZMod p, (t = 1 ∨ t = 2) ∧ ν * t * t + 1 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h1 : ν * 1 * 1 + 1 = 0 := hcon 1 (Or.inl rfl)
    have h2 : ν * 2 * 2 + 1 = 0 := hcon 2 (Or.inr rfl)
    have h3 : (3 : ZMod p) * ν = 0 := by linear_combination h2 - h1
    have h3zero : (3 : ZMod p) = 0 := (mul_eq_zero.mp h3).resolve_right hν0
    apply hp3
    have hdiv : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp h3zero
    exact (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) (by norm_num)).mp hdiv
  obtain ⟨t, ht, hden⟩ := hchoose
  set s : ZMod p := 2 / (ν * t * t + 1) with hs
  have ht0 : t ≠ 0 := by
    rcases ht with rfl | rfl
    · exact one_ne_zero
    · exact ZMod.prime_ne_zero p 2 hp
  have hs0 : s ≠ 0 := by
    rw [hs]
    exact div_ne_zero (ZMod.prime_ne_zero p 2 hp) hden
  refine ⟨s - 1, t * s, mul_ne_zero ht0 hs0, ?_⟩
  have hsden : s * (ν * t * t + 1) = 2 := by
    rw [hs]
    exact div_mul_cancel₀ 2 hden
  have hkey : (s - 1) * (s - 1) + ν * (t * s) * (t * s) = 1 := by
    have h : (s - 1) * (s - 1) + ν * (t * s) * (t * s) =
        s * (s * (ν * t * t + 1)) - 2 * s + 1 := by ring
    rw [h, hsden]
    ring
  have hB : B ((s - 1) • v + (t * s) • w) =
      c * ((s - 1) * (s - 1) + ν * (t * s) * (t * s)) := by
    rw [QuadraticMap.map_add B, QuadraticMap.map_smul, QuadraticMap.map_smul,
      QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, hvw, hv, hw, hμν]
    simp only [smul_eq_mul, mul_zero, add_zero]
    ring
  rw [hB, hkey, mul_one]

private theorem exists_class_root_of_eq_three (hp3 : p = 3)
    {W : Type*} [AddCommGroup W] [Module (ZMod p) W] {B : QuadraticForm (ZMod p) W}
    {v₀ v₁ w : W} {c μ : ZMod p} (hv₀ : B v₀ = c) (hv₁ : B v₁ = c) (hw : B w = μ)
    (h01 : QuadraticMap.polar B v₀ v₁ = 0) (h0w : QuadraticMap.polar B v₀ w = 0)
    (h1w : QuadraticMap.polar B v₁ w = 0)
    (hc : c ≠ 0) (hμ : μ ≠ 0) (hμc : μ ≠ c) :
    ∃ (α β : ZMod p), B (α • v₀ + β • v₁ + w) = c := by
  subst hp3
  have hν0 : μ / c ≠ 0 := div_ne_zero hμ hc
  have hν1 : μ / c ≠ 1 := by
    intro h
    apply hμc
    calc μ = (μ / c) * c := (div_mul_cancel₀ μ hc).symm
      _ = 1 * c := by rw [h]
      _ = c := one_mul c
  have hν : μ / c = -1 := by
    have hx0 : (μ / c).val ≠ 0 := (ZMod.val_ne_zero (μ / c)).mpr hν0
    have hx1 : (μ / c).val ≠ 1 := by
      intro h
      exact hν1 ((ZMod.val_eq_one (by norm_num : 1 < 3) (μ / c)).mp h)
    have hlt : (μ / c).val < 3 := ZMod.val_lt (μ / c)
    have hval : (μ / c).val = 2 := by omega
    have hcast : (((μ / c).val : ℕ) : ZMod 3) = μ / c := ZMod.natCast_rightInverse _
    rw [← hcast, hval, eq_neg_iff_add_eq_zero]
    have h3 : ((2 : ℕ) : ZMod 3) + 1 = ((3 : ℕ) : ZMod 3) := by norm_num
    rw [h3, ZMod.natCast_self]
  have hμeq : μ = -c := by
    calc μ = (μ / c) * c := (div_mul_cancel₀ μ hc).symm
      _ = -1 * c := by rw [hν]
      _ = -c := by ring
  refine ⟨1, 1, ?_⟩
  rw [one_smul, one_smul]
  have hB : B (v₀ + v₁ + w) = B v₀ + B v₁ + B w := by
    rw [QuadraticMap.map_add B, QuadraticMap.map_add B, QuadraticMap.polar_add_left,
      h01, h0w, h1w]
    abel
  rw [hB, hv₀, hv₁, hw, hμeq]
  ring

private theorem last_basis_mem_eq_three (hp3 : p = 3) {Q : QuadraticForm (ZMod p) U}
    {c : ZMod p} (hc : c ≠ 0) {E : Submodule (ZMod p) U} {d : ℕ} (hd3 : 3 ≤ d)
    {v : Module.Basis (Fin d) (ZMod p) E}
    (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (v i : U) (v j : U) = 0)
    (hveq : ∀ i : Fin d, (i : ℕ) + 1 < d → Q (v i : U) = c)
    (hlast : Q (v ⟨d - 1, by omega⟩ : U) ≠ 0)
    (hw : Q (v ⟨d - 1, by omega⟩ : U) ≠ c) {Vh : Submodule (ZMod p) U}
    (hmem : ∀ a : E, Q (a : U) = c → (a : U) ∈ Vh) :
    (v ⟨d - 1, by omega⟩ : U) ∈ Vh := by
  set w : E := v ⟨d - 1, by omega⟩ with hwdef
  have hne0 : (⟨0, by omega⟩ : Fin d) ≠ ⟨d - 1, by omega⟩ := by
    intro h
    have := congrArg (fun i : Fin d => (i : ℕ)) h
    simp only at this
    omega
  have hne1 : (⟨1, by omega⟩ : Fin d) ≠ ⟨d - 1, by omega⟩ := by
    intro h
    have := congrArg (fun i : Fin d => (i : ℕ)) h
    simp only at this
    omega
  let v₀ : E := v ⟨0, by omega⟩
  let v₁ : E := v ⟨1, by omega⟩
  have h0 : Q (v₀ : U) = c := hveq ⟨0, by omega⟩ (by simp only; omega)
  have h1 : Q (v₁ : U) = c := hveq ⟨1, by omega⟩ (by simp only; omega)
  have h01 : QuadraticMap.polar Q (v₀ : U) (v₁ : U) = 0 :=
    horth ⟨0, by omega⟩ ⟨1, by omega⟩ (by
      intro h
      have := congrArg (fun i : Fin d => (i : ℕ)) h
      simp only at this
      omega)
  have h0w : QuadraticMap.polar Q (v₀ : U) (w : U) = 0 := by
    rw [hwdef]
    exact horth ⟨0, by omega⟩ ⟨d - 1, by omega⟩ hne0
  have h1w : QuadraticMap.polar Q (v₁ : U) (w : U) = 0 := by
    rw [hwdef]
    exact horth ⟨1, by omega⟩ ⟨d - 1, by omega⟩ hne1
  obtain ⟨α, β, hB⟩ := exists_class_root_of_eq_three (B := Q) (v₀ := (v₀ : U))
    (v₁ := (v₁ : U)) (w := (w : U)) (c := c) (μ := Q (w : U)) hp3 h0 h1 rfl h01 h0w h1w
    hc hlast hw
  let u : E := α • v₀ + β • v₁ + w
  have hu : Q (u : U) = c := hB
  have hwx : (w : U) = (u : U) - α • (v₀ : U) - β • (v₁ : U) := by
    have hcoe : (u : U) = α • (v₀ : U) + β • (v₁ : U) + (w : U) := rfl
    rw [hcoe]
    abel
  rw [hwx]
  exact Vh.sub_mem (Vh.sub_mem (hmem u hu) (Vh.smul_mem α (hmem v₀ h0)))
    (Vh.smul_mem β (hmem v₁ h1))

private theorem last_basis_mem_ne_three (hp : p ≠ 2) (hp3 : p ≠ 3)
    {Q : QuadraticForm (ZMod p) U} {c : ZMod p} (hc : c ≠ 0) {E : Submodule (ZMod p) U}
    {d : ℕ} (hd2 : 2 ≤ d) {v : Module.Basis (Fin d) (ZMod p) E}
    (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (v i : U) (v j : U) = 0)
    (hveq : ∀ i : Fin d, (i : ℕ) + 1 < d → Q (v i : U) = c)
    (hlast : Q (v ⟨d - 1, by omega⟩ : U) ≠ 0)
    (hw : Q (v ⟨d - 1, by omega⟩ : U) ≠ c) {Vh : Submodule (ZMod p) U}
    (hmem : ∀ a : E, Q (a : U) = c → (a : U) ∈ Vh) :
    (v ⟨d - 1, by omega⟩ : U) ∈ Vh := by
  set w : E := v ⟨d - 1, by omega⟩ with hwdef
  have hne0 : (⟨0, by omega⟩ : Fin d) ≠ ⟨d - 1, by omega⟩ := by
    intro h
    have := congrArg (fun i : Fin d => (i : ℕ)) h
    simp only at this
    omega
  let v₀ : E := v ⟨0, by omega⟩
  have h0 : Q (v₀ : U) = c := hveq ⟨0, by omega⟩ (by simp only; omega)
  have h0w : QuadraticMap.polar Q (v₀ : U) (w : U) = 0 := by
    rw [hwdef]
    exact horth ⟨0, by omega⟩ ⟨d - 1, by omega⟩ hne0
  obtain ⟨α, β, hβ, hB⟩ := exists_class_root_of_ne_three (B := Q) (v := (v₀ : U))
    (w := (w : U)) (c := c) (μ := Q (w : U)) hp hp3 h0 rfl h0w hc hlast hw
  let u : E := α • v₀ + β • w
  have hu : Q (u : U) = c := hB
  have hwx : (w : U) = β⁻¹ • ((u : U) - α • (v₀ : U)) := by
    have hmul : β • (w : U) = (u : U) - α • (v₀ : U) := by
      have hcoe : (u : U) = α • (v₀ : U) + β • (w : U) := rfl
      rw [hcoe]
      abel
    calc (w : U) = β⁻¹ • (β • (w : U)) := by
          rw [smul_smul, inv_mul_cancel₀ hβ, one_smul]
      _ = β⁻¹ • ((u : U) - α • (v₀ : U)) := by rw [hmul]
  rw [hwx]
  exact Vh.smul_mem β⁻¹ (Vh.sub_mem (hmem u hu) (Vh.smul_mem α (hmem v₀ h0)))

private theorem last_basis_mem (hp : p ≠ 2) {Q : QuadraticForm (ZMod p) U} {c : ZMod p}
    (hc : c ≠ 0) {E : Submodule (ZMod p) U} {d : ℕ} (hd2 : 2 ≤ d)
    {v : Module.Basis (Fin d) (ZMod p) E}
    (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (v i : U) (v j : U) = 0)
    (hveq : ∀ i : Fin d, (i : ℕ) + 1 < d → Q (v i : U) = c)
    (hlast : Q (v ⟨d - 1, by omega⟩ : U) ≠ 0)
    (hp3d : p = 3 → 3 ≤ d) {Vh : Submodule (ZMod p) U}
    (hmem : ∀ a : E, Q (a : U) = c → (a : U) ∈ Vh) :
    (v ⟨d - 1, by omega⟩ : U) ∈ Vh := by
  by_cases hw : Q (v ⟨d - 1, by omega⟩ : U) = c
  · exact hmem (v ⟨d - 1, by omega⟩) hw
  · by_cases hp3 : p = 3
    · exact last_basis_mem_eq_three hp3 hc (hp3d hp3) horth hveq hlast hw hmem
    · exact last_basis_mem_ne_three hp hp3 hc hd2 horth hveq hlast hw hmem

private theorem commutatorSpace_inf_ker_setup (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {m : ℕ} (hs : SplitSupport X m)
    (hm : 3 ≤ m) (hXiso : ∀ g ∈ X, IsIsom p Q g) {h : U ≃ₗ[ZMod p] U} {e : U}
    (hQe : Q e ≠ 0) (heV : e ∈ HardMathSupport.Kantor79.commutatorSpace X)
    (hWker0 : LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1) =
      LinearMap.ker (QuadraticMap.polarBilin Q e)) :
    ∃ d : ℕ,
      Module.finrank (ZMod p) ↥(HardMathSupport.Kantor79.commutatorSpace X ⊓
        LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)) = d ∧
      d = m - 1 ∧ 2 ≤ d ∧ ClassicalGroups.Orthogonal.PolarNondegOn Q
        (HardMathSupport.Kantor79.commutatorSpace X ⊓
          LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)) ∧
      (2 : ZMod p) ≠ 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hVnd : ClassicalGroups.Orthogonal.PolarNondegOn Q
      (HardMathSupport.Kantor79.commutatorSpace X) :=
    polarNondegOn_commutatorSpace hQ hXiso hs.1
  have hEnd : ClassicalGroups.Orthogonal.PolarNondegOn Q
      (HardMathSupport.Kantor79.commutatorSpace X ⊓
        LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)) := by
    rw [hWker0]
    exact ClassicalGroups.Orthogonal.PolarNondegOn.inf_ker h2 hVnd heV hQe
  refine ⟨m - 1, ?_, rfl, ?_, hEnd, h2⟩
  · rw [hWker0]
    have h := ClassicalGroups.Orthogonal.finrank_inf_ker_polarBilin_add_one h2 heV hQe
    rw [hs.2.1] at h
    omega
  · omega

private theorem full_mem_reflStab (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hfull : X = Subgroup.closure {t | IsRefl p t ∧ IsIsom p Q t ∧
      HardMathSupport.Kantor79.movedSpace t ≤ HardMathSupport.Kantor79.commutatorSpace X})
    {h : U ≃ₗ[ZMod p] U} {a : U}
    (haV : a ∈ HardMathSupport.Kantor79.commutatorSpace X)
    (haW : a ∈ LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)) (ha : Q a ≠ 0) :
    a ∈ HardMathSupport.Kantor79.commutatorSpace (reflStab p X h) := by
  refine mem_commutatorSpace_reflStab_of_mem hp hQ haW ?_ ha
  rw [hfull]
  exact Subgroup.subset_closure ⟨isRefl_reflect hp ha, isIsom_reflect Q a,
    (movedSpace_reflect_le_span Q a).trans
      ((Submodule.span_singleton_le_iff_mem a
        (HardMathSupport.Kantor79.commutatorSpace X)).mpr haV)⟩

private theorem le_of_basis_mem {V W Vh : Submodule (ZMod p) U} {d : ℕ}
    {v : Module.Basis (Fin d) (ZMod p) ↥(V ⊓ W)}
    (hmemAll : ∀ i, (v i : U) ∈ Vh) : V ⊓ W ≤ Vh := by
  intro x hx
  have hcoe : ((∑ i, v.repr ⟨x, hx⟩ i • v i : ↥(V ⊓ W)) : U) =
      ∑ i, v.repr ⟨x, hx⟩ i • (v i : U) := by
    rw [Submodule.coe_sum]
    exact Finset.sum_congr rfl fun i _ => Submodule.coe_smul _ _
  have hsum : x = ∑ i, v.repr ⟨x, hx⟩ i • (v i : U) := by
    calc x = ((⟨x, hx⟩ : ↥(V ⊓ W)) : U) := rfl
      _ = ((∑ i, v.repr ⟨x, hx⟩ i • v i : ↥(V ⊓ W)) : U) := by rw [v.sum_repr]
      _ = ∑ i, v.repr ⟨x, hx⟩ i • (v i : U) := hcoe
  rw [hsum]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hmemAll i)

private theorem commutatorSpace_reflStab_ge_full (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {m : ℕ} (hs : SplitSupport X m)
    (hm : 3 ≤ m) (hXiso : ∀ g ∈ X, IsIsom p Q g)
    (hfull : X = Subgroup.closure {t | IsRefl p t ∧ IsIsom p Q t ∧
      HardMathSupport.Kantor79.movedSpace t ≤ HardMathSupport.Kantor79.commutatorSpace X})
    {h : U ≃ₗ[ZMod p] U} {e : U} (hQe : Q e ≠ 0)
    (heV : e ∈ HardMathSupport.Kantor79.commutatorSpace X)
    (hWker0 : LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1) =
      LinearMap.ker (QuadraticMap.polarBilin Q e)) :
    HardMathSupport.Kantor79.commutatorSpace X ⊓ LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1) ≤
      HardMathSupport.Kantor79.commutatorSpace (reflStab p X h) := by
  obtain ⟨d, hfin, hdm, hd2, hEnd, -⟩ :=
    commutatorSpace_inf_ker_setup hp hQ hs hm hXiso hQe heV hWker0
  set V := HardMathSupport.Kantor79.commutatorSpace X with hVdef
  set W := LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1) with hWdef
  have hOdd : Odd (Nat.card (ZMod p)) := by
    rw [Nat.card_zmod]
    exact (Fact.out : p.Prime).odd_of_ne_two hp
  obtain ⟨v, -, hveq, hvlast⟩ :=
    CFSG.RankThree.Classical.exists_orthogonal_basis_quad_eq (K := ZMod p) (V := ↥(V ⊓ W))
      hOdd hfin hd2 (Q.restrict (V ⊓ W))
      (ClassicalGroups.Orthogonal.nondegenerate_polarBilin_restrict hEnd) (a := 1) one_ne_zero
  have hveq' : ∀ i : Fin d, (i : ℕ) + 1 < d → Q (v i : U) = 1 := by
    intro i hi
    rw [← ClassicalGroups.Orthogonal.restrict_apply']
    exact hveq i hi
  have hvlast' : Q (v ⟨d - 1, by omega⟩ : U) ≠ 0 := by
    rw [← ClassicalGroups.Orthogonal.restrict_apply']
    exact hvlast
  have hmemVh : ∀ a : ↥(V ⊓ W), Q (a : U) ≠ 0 →
      (a : U) ∈ HardMathSupport.Kantor79.commutatorSpace (reflStab p X h) :=
    fun a ha => full_mem_reflStab hp hQ hfull a.2.1 a.2.2 ha
  have hQne : ∀ i, Q (v i : U) ≠ 0 := by
    intro i
    by_cases hi : (i : ℕ) + 1 < d
    · rw [hveq' i hi]; exact one_ne_zero
    · have hii : i = ⟨d - 1, by omega⟩ := by
        apply Fin.ext
        simp only
        omega
      rw [hii]
      exact hvlast'
  exact le_of_basis_mem fun i => hmemVh (v i) (hQne i)

private theorem class_mem_reflStab (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {c : ZMod p} (hc : c ≠ 0)
    (hclass : X = Subgroup.closure {t | t ∈ ClassRefl p Q c ∧
      HardMathSupport.Kantor79.movedSpace t ≤ HardMathSupport.Kantor79.commutatorSpace X})
    {h : U ≃ₗ[ZMod p] U} {a : U}
    (haV : a ∈ HardMathSupport.Kantor79.commutatorSpace X)
    (haW : a ∈ LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)) (ha : Q a = c) :
    a ∈ HardMathSupport.Kantor79.commutatorSpace (reflStab p X h) := by
  refine mem_commutatorSpace_reflStab_of_mem hp hQ haW ?_ ?_
  · rw [hclass]
    refine Subgroup.subset_closure
      ⟨(mem_classRefl_iff hp hQ hc (ClassicalGroups.Orthogonal.reflect Q a)).mpr
        ⟨a, ha, rfl⟩, ?_⟩
    exact (movedSpace_reflect_le_span Q a).trans
      ((Submodule.span_singleton_le_iff_mem a
        (HardMathSupport.Kantor79.commutatorSpace X)).mpr haV)
  · rw [ha]; exact hc

private theorem class_basis_mem_all (hp : p ≠ 2) {Q : QuadraticForm (ZMod p) U} {c : ZMod p}
    (hc : c ≠ 0) {V W Vh : Submodule (ZMod p) U} {d : ℕ} (hd2 : 2 ≤ d)
    {v : Module.Basis (Fin d) (ZMod p) ↥(V ⊓ W)}
    (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (v i : U) (v j : U) = 0)
    (hveq : ∀ i : Fin d, (i : ℕ) + 1 < d → Q (v i : U) = c)
    (hlast : Q (v ⟨d - 1, by omega⟩ : U) ≠ 0) (hp3d : p = 3 → 3 ≤ d)
    (hmemVh : ∀ a : ↥(V ⊓ W), Q (a : U) = c → (a : U) ∈ Vh) :
    ∀ i, (v i : U) ∈ Vh := by
  intro i
  by_cases hi : (i : ℕ) + 1 < d
  · exact hmemVh (v i) (hveq i hi)
  · have hii : i = ⟨d - 1, by omega⟩ := by
      apply Fin.ext
      simp only
      omega
    rw [hii]
    exact last_basis_mem hp hc hd2 horth hveq hlast hp3d hmemVh

private theorem commutatorSpace_reflStab_ge_class (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {m : ℕ} (hs : SplitSupport X m)
    (hm : 3 ≤ m) (hm3 : p = 3 → 4 ≤ m) (hXiso : ∀ g ∈ X, IsIsom p Q g)
    {c : ZMod p} (hc : c ≠ 0)
    (hclass : X = Subgroup.closure {t | t ∈ ClassRefl p Q c ∧
      HardMathSupport.Kantor79.movedSpace t ≤ HardMathSupport.Kantor79.commutatorSpace X})
    {h : U ≃ₗ[ZMod p] U} {e : U} (hQe : Q e ≠ 0)
    (heV : e ∈ HardMathSupport.Kantor79.commutatorSpace X)
    (hWker0 : LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1) =
      LinearMap.ker (QuadraticMap.polarBilin Q e)) :
    HardMathSupport.Kantor79.commutatorSpace X ⊓ LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1) ≤
      HardMathSupport.Kantor79.commutatorSpace (reflStab p X h) := by
  obtain ⟨d, hfin, hdm, hd2, hEnd, -⟩ :=
    commutatorSpace_inf_ker_setup hp hQ hs hm hXiso hQe heV hWker0
  set V := HardMathSupport.Kantor79.commutatorSpace X with hVdef
  set W := LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1) with hWdef
  have hOdd : Odd (Nat.card (ZMod p)) := by
    rw [Nat.card_zmod]
    exact (Fact.out : p.Prime).odd_of_ne_two hp
  obtain ⟨v, hvorth, hveq, hvlast⟩ :=
    CFSG.RankThree.Classical.exists_orthogonal_basis_quad_eq (K := ZMod p) (V := ↥(V ⊓ W))
      hOdd hfin hd2 (Q.restrict (V ⊓ W))
      (ClassicalGroups.Orthogonal.nondegenerate_polarBilin_restrict hEnd) (a := c) hc
  have hveq' : ∀ i : Fin d, (i : ℕ) + 1 < d → Q (v i : U) = c := by
    intro i hi
    rw [← ClassicalGroups.Orthogonal.restrict_apply']
    exact hveq i hi
  have horth' : ∀ i j, i ≠ j → QuadraticMap.polar Q (v i : U) (v j : U) = 0 := by
    intro i j hij
    rw [← ClassicalGroups.Orthogonal.polar_restrict]
    exact hvorth i j hij
  have hvlast' : Q (v ⟨d - 1, by omega⟩ : U) ≠ 0 := by
    rw [← ClassicalGroups.Orthogonal.restrict_apply']
    exact hvlast
  have hmemVh : ∀ a : ↥(V ⊓ W), Q (a : U) = c →
      (a : U) ∈ HardMathSupport.Kantor79.commutatorSpace (reflStab p X h) :=
    fun a ha => class_mem_reflStab hp hQ hc hclass a.2.1 a.2.2 ha
  have hp3d : p = 3 → 3 ≤ d := by
    intro hp3
    have := hm3 hp3
    omega
  exact le_of_basis_mem (class_basis_mem_all hp hc hd2 horth' hveq' hvlast' hp3d hmemVh)

theorem commutatorSpace_reflStab (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {m : ℕ} (hs : SplitSupport X m)
    (hm : 3 ≤ m) (hm3 : p = 3 → 4 ≤ m) (ho : IsOrthOn p Q X) {h : U ≃ₗ[ZMod p] U} (hh : h ∈ X)
    (hh' : IsRefl p h) :
    HardMathSupport.Kantor79.commutatorSpace (reflStab p X h) =
      HardMathSupport.Kantor79.commutatorSpace X ⊓ LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1) := by
  have hXiso : ∀ g ∈ X, IsIsom p Q g := fun g hg => ho.isIsom hg
  refine le_antisymm ?_ ?_
  · refine le_inf ?_ ?_
    · exact HardMathSupport.Kantor79.commutatorSpace_mono (reflSubgroupIn_le X _)
    · exact commutatorSpace_reflSubgroupIn_le X _
  · obtain ⟨e, hQe, hee⟩ :=
      DimThree.exists_root_of_isRefl_isIsom hp hQ hh' (hXiso h hh)
    have he0 : e ≠ 0 := fun h0 => hQe (by rw [h0]; exact map_zero Q)
    have hh_eq : h = ClassicalGroups.Orthogonal.reflect Q e :=
      DimThree.eq_of_isRefl_isIsom_of_apply_eq_neg hp hQ hh' (hXiso h hh)
        (isRefl_reflect hp hQe) (isIsom_reflect Q e) he0 hee
        (reflect_apply_self hQe)
    have hWker : LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1) =
        LinearMap.ker (QuadraticMap.polarBilin Q e) := by
      rw [hh_eq]
      exact ker_reflect_sub_one_eq_ker_polar hQe
    have heV : e ∈ HardMathSupport.Kantor79.commutatorSpace X :=
      HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hh
        (HardMathSupport.Kantor79.mem_movedSpace_of_apply_eq_neg (ZMod.prime_ne_zero p 2 hp) hee)
    rcases ho with hfull | ⟨c, hc, hclass⟩
    · exact commutatorSpace_reflStab_ge_full hp hQ hs hm hXiso hfull hQe heV hWker
    · exact commutatorSpace_reflStab_ge_class hp hQ hs hm hm3 hXiso hc hclass hQe heV hWker

end CFSG.StandardType.ZS

end
