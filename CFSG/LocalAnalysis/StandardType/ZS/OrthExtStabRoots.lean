module

public import CFSG.LocalAnalysis.StandardType.ZS.OrthExtRoots
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CRankInv

public section

namespace CFSG.ClassicalGroups.Orthogonal

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

private theorem map_add_eq_two_mul {a z : V} (hz : Q z = Q a)
    (haz : QuadraticMap.polar Q a z = 0) : Q (a + z) = 2 * Q a := by
  rw [QuadraticMap.map_add Q, hz, haz, add_zero, two_mul]

private theorem reflect_add_apply_left (h2 : (2 : K) ≠ 0) {a z : V} (ha : Q a ≠ 0)
    (hz : Q z = Q a) (haz : QuadraticMap.polar Q a z = 0) : reflect Q (a + z) a = -z := by
  have hQaz : Q (a + z) = 2 * Q a := map_add_eq_two_mul hz haz
  have h2a : (2 : K) * Q a ≠ 0 := mul_ne_zero h2 ha
  have hQaz0 : Q (a + z) ≠ 0 := by rw [hQaz]; exact h2a
  have hp : QuadraticMap.polar Q (a + z) a = 2 * Q a := by
    rw [QuadraticMap.polar_add_left Q, QuadraticMap.polar_self, two_smul, ← two_mul,
      QuadraticMap.polar_comm Q z a, haz, add_zero]
  rw [reflect_apply hQaz0, hp, hQaz, div_self h2a, one_smul]
  abel

private theorem reflect_add_apply_right (h2 : (2 : K) ≠ 0) {a z : V} (ha : Q a ≠ 0)
    (hz : Q z = Q a) (haz : QuadraticMap.polar Q a z = 0) : reflect Q (a + z) z = -a := by
  have hQaz : Q (a + z) = 2 * Q a := map_add_eq_two_mul hz haz
  have h2a : (2 : K) * Q a ≠ 0 := mul_ne_zero h2 ha
  have hQaz0 : Q (a + z) ≠ 0 := by rw [hQaz]; exact h2a
  have hp : QuadraticMap.polar Q (a + z) z = 2 * Q a := by
    rw [QuadraticMap.polar_add_left Q, haz, QuadraticMap.polar_self, hz, two_smul, ← two_mul,
      zero_add]
  rw [reflect_apply hQaz0, hp, hQaz, div_self h2a, one_smul]
  abel

private theorem commute_reflect_add_sub (h2 : (2 : K) ≠ 0) {a z : V} (ha : Q a ≠ 0)
    (hz : Q z = Q a) (haz : QuadraticMap.polar Q a z = 0) :
    reflect Q (a + z) * reflect Q (z - a) = reflect Q (z - a) * reflect Q (a + z) := by
  have hrz_a : reflect Q (a + z) a = -z := reflect_add_apply_left h2 ha hz haz
  have hrz_z : reflect Q (a + z) z = -a := reflect_add_apply_right h2 ha hz haz
  have hfix : reflect Q (a + z) (z - a) = z - a := by
    rw [map_sub, hrz_a, hrz_z]
    abel
  have hconj : reflect Q (a + z) * reflect Q (z - a) * reflect Q (a + z) =
      reflect Q (z - a) := by
    have h := reflect_conj (Q := Q) (reflect_mem_orthogonalGroup Q (a + z)) (z - a)
    rwa [reflect_inv, hfix] at h
  have h := congrArg (fun t => t * reflect Q (a + z)) hconj
  rwa [mul_assoc (reflect Q (a + z) * reflect Q (z - a)), reflect_mul_self, mul_one] at h

private theorem sq_reflect_mul_reflect_add {a z : V} (ha : Q a ≠ 0)
    (haz : QuadraticMap.polar Q a z = 0) :
    (reflect Q a * reflect Q (a + z)) * (reflect Q a * reflect Q (a + z))
      = reflect Q (z - a) * reflect Q (a + z) := by
  have hra_a : reflect Q a a = -a := CFSG.StandardType.ZS.reflect_apply_self ha
  have hra_z : reflect Q a z = z := reflect_apply_of_polar_eq_zero haz
  have hra_add : reflect Q a (a + z) = z - a := by
    rw [map_add, hra_a, hra_z]
    abel
  have hconj : reflect Q a * reflect Q (a + z) * reflect Q a = reflect Q (z - a) := by
    have h := reflect_conj (Q := Q) (reflect_mem_orthogonalGroup Q a) (a + z)
    rwa [reflect_inv, hra_add] at h
  calc (reflect Q a * reflect Q (a + z)) * (reflect Q a * reflect Q (a + z))
      = (reflect Q a * reflect Q (a + z)) * reflect Q a * reflect Q (a + z) :=
        (mul_assoc _ _ _).symm
    _ = reflect Q (z - a) * reflect Q (a + z) := by rw [hconj]

private theorem pow_four_reflect_mul_reflect_add (h2 : (2 : K) ≠ 0) {a z : V} (ha : Q a ≠ 0)
    (hz : Q z = Q a) (haz : QuadraticMap.polar Q a z = 0) :
    (reflect Q a * reflect Q (a + z)) ^ 4 = 1 := by
  have hsq := sq_reflect_mul_reflect_add ha haz
  have hcomm := commute_reflect_add_sub h2 ha hz haz
  have h4 : (reflect Q (z - a) * reflect Q (a + z)) *
      (reflect Q (z - a) * reflect Q (a + z)) = 1 := by
    calc (reflect Q (z - a) * reflect Q (a + z)) *
          (reflect Q (z - a) * reflect Q (a + z))
        = reflect Q (z - a) * (reflect Q (a + z) *
            (reflect Q (z - a) * reflect Q (a + z))) := by rw [mul_assoc]
      _ = reflect Q (z - a) * ((reflect Q (a + z) * reflect Q (z - a)) *
            reflect Q (a + z)) := by rw [mul_assoc]
      _ = reflect Q (z - a) * ((reflect Q (z - a) * reflect Q (a + z)) *
            reflect Q (a + z)) := by rw [hcomm]
      _ = reflect Q (z - a) * (reflect Q (z - a) *
            (reflect Q (a + z) * reflect Q (a + z))) := by rw [mul_assoc]
      _ = (reflect Q (z - a) * reflect Q (z - a)) *
            (reflect Q (a + z) * reflect Q (a + z)) := by rw [mul_assoc]
      _ = 1 := by rw [reflect_mul_self, reflect_mul_self, mul_one]
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_two, pow_two, hsq]
  exact h4

private theorem pow_two_ne_one_reflect_mul_reflect_add (h2 : (2 : K) ≠ 0) {a z : V}
    (ha : Q a ≠ 0) (hz : Q z = Q a) (haz : QuadraticMap.polar Q a z = 0) :
    (reflect Q a * reflect Q (a + z)) ^ 2 ≠ 1 := by
  have hra_a : reflect Q a a = -a := CFSG.StandardType.ZS.reflect_apply_self ha
  have hra_z : reflect Q a z = z := reflect_apply_of_polar_eq_zero haz
  have hrz_a : reflect Q (a + z) a = -z := reflect_add_apply_left h2 ha hz haz
  have hrz_z : reflect Q (a + z) z = -a := reflect_add_apply_right h2 ha hz haz
  have hga : (reflect Q a * reflect Q (a + z)) a = -z := by
    rw [LinearEquiv.mul_apply, hrz_a, map_neg, hra_z]
  have hgz : (reflect Q a * reflect Q (a + z)) z = a := by
    rw [LinearEquiv.mul_apply, hrz_z, map_neg, hra_a, neg_neg]
  have hg2a : (reflect Q a * reflect Q (a + z)) ((reflect Q a * reflect Q (a + z)) a) = -a := by
    rw [hga, map_neg, hgz]
  intro h1
  have hzero : a = 0 := by
    refine CFSG.StandardType.ZS.eq_zero_of_eq_neg h2 ?_
    rw [← hg2a, ← LinearEquiv.mul_apply, ← pow_two, h1]
    rfl
  exact ha (by rw [hzero]; exact map_zero Q)

theorem orderOf_reflect_mul_reflect_add (h2 : (2 : K) ≠ 0) {a z : V} (ha : Q a ≠ 0)
    (hz : Q z = Q a) (haz : QuadraticMap.polar Q a z = 0) :
    orderOf (reflect Q a * reflect Q (a + z)) = 4 :=
  orderOf_eq_prime_pow (p := 2) (n := 1) (hp := ⟨Nat.prime_two⟩)
    (by simpa using pow_two_ne_one_reflect_mul_reflect_add h2 ha hz haz)
    (by simpa using pow_four_reflect_mul_reflect_add h2 ha hz haz)
end CFSG.ClassicalGroups.Orthogonal

namespace CFSG.StandardType.ZS

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]
  {Q : QuadraticForm (ZMod p) U} {X : Subgroup (U ≃ₗ[ZMod p] U)} {h : U ≃ₗ[ZMod p] U}

private theorem map_sub_eq_two_mul {a b : U} (hb : Q b = Q a)
    (hab : QuadraticMap.polar Q a b = 0) : Q (a - b) = 2 * Q a := by
  rw [sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg, hb,
    QuadraticMap.polar_neg_right, hab]
  ring

private theorem reflect_sub_apply_left (h2 : (2 : ZMod p) ≠ 0) {a b : U} (ha : Q a ≠ 0)
    (hb : Q b = Q a) (hab : QuadraticMap.polar Q a b = 0) :
    ClassicalGroups.Orthogonal.reflect Q (a - b) a = b := by
  have hQ : Q (a - b) = 2 * Q a := map_sub_eq_two_mul hb hab
  have h2a : (2 : ZMod p) * Q a ≠ 0 := mul_ne_zero h2 ha
  have hQ0 : Q (a - b) ≠ 0 := by rw [hQ]; exact h2a
  have hp : QuadraticMap.polar Q (a - b) a = 2 * Q a := by
    rw [QuadraticMap.polar_sub_left, ClassicalGroups.Orthogonal.polar_self_eq_two_mul,
      QuadraticMap.polar_comm Q b a, hab, sub_zero]
  rw [ClassicalGroups.Orthogonal.reflect_apply hQ0, hp, hQ, div_self h2a, one_smul]
  abel

private theorem reflect_sub_apply_right (h2 : (2 : ZMod p) ≠ 0) {a b : U} (ha : Q a ≠ 0)
    (hb : Q b = Q a) (hab : QuadraticMap.polar Q a b = 0) :
    ClassicalGroups.Orthogonal.reflect Q (a - b) b = a := by
  have hQ : Q (a - b) = 2 * Q a := map_sub_eq_two_mul hb hab
  have h2a : (2 : ZMod p) * Q a ≠ 0 := mul_ne_zero h2 ha
  have hQ0 : Q (a - b) ≠ 0 := by rw [hQ]; exact h2a
  have hp : QuadraticMap.polar Q (a - b) b = -(2 * Q a) := by
    rw [QuadraticMap.polar_sub_left, hab, ClassicalGroups.Orthogonal.polar_self_eq_two_mul, hb,
      zero_sub]
  have hc : -(2 * Q a) / (2 * Q a) = -1 := by rw [neg_div, div_self h2a]
  rw [ClassicalGroups.Orthogonal.reflect_apply hQ0, hp, hQ, hc, neg_one_smul, sub_neg_eq_add]
  abel

private theorem reflect_sub_apply_of_polar_eq_zero {a b u : U}
    (h1 : QuadraticMap.polar Q a u = 0) (h2 : QuadraticMap.polar Q b u = 0) :
    ClassicalGroups.Orthogonal.reflect Q (a - b) u = u :=
  ClassicalGroups.Orthogonal.reflect_apply_of_polar_eq_zero (by
    rw [QuadraticMap.polar_sub_left, h1, h2, sub_self])

private theorem exists_root_of_mem_closure (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {c : ZMod p} (hc : c ≠ 0)
    {t : U ≃ₗ[ZMod p] U} (ht : t ∈ Subgroup.closure (ClassRefl p Q c)) (hrt : IsRefl p t) :
    ∃ a, Q a = c ∧ t = ClassicalGroups.Orthogonal.reflect Q a :=
  (mem_classRefl_iff hp hQ hc t).mp (mem_classRefl_of_isRefl_mem_closure hp hQ hc ht hrt)

private theorem polar_root_eq_zero_of_mem_reflStab (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {h : U ≃ₗ[ZMod p] U} (hh' : IsRefl p h)
    (hhi : IsIsom p Q h) {t : U ≃ₗ[ZMod p] U} (ht : t ∈ reflStab p X h)
    {a b : U} (hb : Q b ≠ 0) (hhb : h b = -b) (hta : t a = -a) :
    QuadraticMap.polar Q b a = 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hb0 : b ≠ 0 := fun h0 => hb (by rw [h0]; exact map_zero Q)
  have hheq : h = ClassicalGroups.Orthogonal.reflect Q b :=
    DimThree.eq_of_isRefl_isIsom_of_apply_eq_neg hp hQ hh' hhi (isRefl_reflect hp hb)
      (isIsom_reflect Q b) hb0 hhb (reflect_apply_self hb)
  have ha : a ∈ HardMathSupport.Kantor79.movedSpace t :=
    HardMathSupport.Kantor79.mem_movedSpace_of_apply_eq_neg h2 hta
  have hle : HardMathSupport.Kantor79.movedSpace t ≤
      LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1) :=
    (HardMathSupport.Kantor79.movedSpace_le_commutatorSpace ht).trans
      (commutatorSpace_reflSubgroupIn_le X _)
  rw [hheq, ker_reflect_sub_one_eq_ker_polar hb] at hle
  have hmem := hle ha
  rwa [LinearMap.mem_ker, QuadraticMap.polarBilin_apply_apply] at hmem

private theorem exists_roots_of_commute (hp5 : p = 5) [Module.Finite (ZMod p) U]
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {c : ZMod p} (hc : c ≠ 0)
    (hX : X = Subgroup.closure {t | t ∈ ClassRefl p Q c ∧
      HardMathSupport.Kantor79.movedSpace t ≤ HardMathSupport.Kantor79.commutatorSpace X})
    (hh : h ∈ X) (hh' : IsRefl p h) {x y : U ≃ₗ[ZMod p] U} (hx : x ∈ reflStab p X h)
    (hy : y ∈ reflStab p X h) (hx' : IsRefl p x) (hy' : IsRefl p y) :
    ∃ e₀ e₁ e₂ : U, Q e₀ = c ∧ Q e₁ = c ∧ Q e₂ = c ∧
      h = ClassicalGroups.Orthogonal.reflect Q e₀ ∧
      x = ClassicalGroups.Orthogonal.reflect Q e₁ ∧
      y = ClassicalGroups.Orthogonal.reflect Q e₂ ∧
      e₀ ∈ HardMathSupport.Kantor79.commutatorSpace X ∧
      e₁ ∈ HardMathSupport.Kantor79.commutatorSpace X ∧
      e₂ ∈ HardMathSupport.Kantor79.commutatorSpace X := by
  have hp2 : p ≠ 2 := by rw [hp5]; decide
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp2
  have ho : IsOrthOn p Q X := Or.inr ⟨c, hc, hX⟩
  have hXiso : ∀ g ∈ X, IsIsom p Q g := fun g hg => ho.isIsom hg
  have hle : X ≤ Subgroup.closure (ClassRefl p Q c) := by
    rw [hX]
    exact Subgroup.closure_mono (fun t ht => ht.1)
  have hxX : x ∈ X := reflSubgroupIn_le X _ hx
  have hyX : y ∈ X := reflSubgroupIn_le X _ hy
  obtain ⟨e₀, hQe₀, he₀⟩ := exists_root_of_mem_closure hp2 hQ hc (hle hh) hh'
  obtain ⟨e₁, hQe₁, he₁⟩ := exists_root_of_mem_closure hp2 hQ hc (hle hxX) hx'
  obtain ⟨e₂, hQe₂, he₂⟩ := exists_root_of_mem_closure hp2 hQ hc (hle hyX) hy'
  have hQe₀0 : Q e₀ ≠ 0 := by rw [hQe₀]; exact hc
  have hQe₁0 : Q e₁ ≠ 0 := by rw [hQe₁]; exact hc
  have hQe₂0 : Q e₂ ≠ 0 := by rw [hQe₂]; exact hc
  have hneg₀ : h e₀ = -e₀ := by rw [he₀]; exact reflect_apply_self hQe₀0
  have hneg₁ : x e₁ = -e₁ := by rw [he₁]; exact reflect_apply_self hQe₁0
  have hneg₂ : y e₂ = -e₂ := by rw [he₂]; exact reflect_apply_self hQe₂0
  have he₀V : e₀ ∈ HardMathSupport.Kantor79.commutatorSpace X :=
    HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hh
      (HardMathSupport.Kantor79.mem_movedSpace_of_apply_eq_neg h2 hneg₀)
  have hxVle : HardMathSupport.Kantor79.movedSpace x ≤
      HardMathSupport.Kantor79.commutatorSpace X :=
    (HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hx).trans
      (HardMathSupport.Kantor79.commutatorSpace_mono (reflSubgroupIn_le X _))
  have hyVle : HardMathSupport.Kantor79.movedSpace y ≤
      HardMathSupport.Kantor79.commutatorSpace X :=
    (HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hy).trans
      (HardMathSupport.Kantor79.commutatorSpace_mono (reflSubgroupIn_le X _))
  exact ⟨e₀, e₁, e₂, hQe₀, hQe₁, hQe₂, he₀, he₁, he₂, he₀V,
    hxVle (HardMathSupport.Kantor79.mem_movedSpace_of_apply_eq_neg h2 hneg₁),
    hyVle (HardMathSupport.Kantor79.mem_movedSpace_of_apply_eq_neg h2 hneg₂)⟩

private theorem roots_pairwise_orthogonal (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {h x y : U ≃ₗ[ZMod p] U}
    (hh' : IsRefl p h) (hhi : IsIsom p Q h) (hx' : IsRefl p x) (hy' : IsRefl p y)
    (hxi : IsIsom p Q x) (hyi : IsIsom p Q y) (hx : x ∈ reflStab p X h)
    (hy : y ∈ reflStab p X h) (hxy : x * y = y * x) (hne : x ≠ y) {e₀ e₁ e₂ : U}
    (hQe₀ : Q e₀ ≠ 0) (hQe₁ : Q e₁ ≠ 0) (hQe₂ : Q e₂ ≠ 0)
    (hhe₀ : h = ClassicalGroups.Orthogonal.reflect Q e₀)
    (hxe₁ : x = ClassicalGroups.Orthogonal.reflect Q e₁)
    (hye₂ : y = ClassicalGroups.Orthogonal.reflect Q e₂) :
    QuadraticMap.polar Q e₀ e₁ = 0 ∧ QuadraticMap.polar Q e₀ e₂ = 0 ∧
      QuadraticMap.polar Q e₁ e₂ = 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hneg₀ : h e₀ = -e₀ := by rw [hhe₀]; exact reflect_apply_self hQe₀
  have hneg₁ : x e₁ = -e₁ := by rw [hxe₁]; exact reflect_apply_self hQe₁
  have hneg₂ : y e₂ = -e₂ := by rw [hye₂]; exact reflect_apply_self hQe₂
  have h01 := polar_root_eq_zero_of_mem_reflStab hp hQ hh' hhi hx hQe₀ hneg₀ hneg₁
  have h02 := polar_root_eq_zero_of_mem_reflStab hp hQ hh' hhi hy hQe₀ hneg₀ hneg₂
  have he₁0 : e₁ ≠ 0 := fun h0 => hQe₁ (by rw [h0]; exact map_zero Q)
  have hneV : HardMathSupport.Kantor79.movedSpace x ≠
      HardMathSupport.Kantor79.movedSpace y := by
    intro heq
    apply hne
    refine DimThree.eq_of_isRefl_isIsom_of_apply_eq_neg hp hQ hx' hxi hy' hyi he₁0 hneg₁ ?_
    exact HardMathSupport.Kantor79.apply_eq_neg_of_mem_movedSpace hy'.1
      (heq ▸ HardMathSupport.Kantor79.mem_movedSpace_of_apply_eq_neg h2 hneg₁)
  have hxe₂ : x e₂ = e₂ :=
    IsRefl.apply_eq_self_of_commute hx' hy' hxy hneV e₂
      (HardMathSupport.Kantor79.mem_movedSpace_of_apply_eq_neg h2 hneg₂)
  have h12 : QuadraticMap.polar Q e₁ e₂ = 0 := by
    have hmem : e₂ ∈ LinearMap.ker ((x : U →ₗ[ZMod p] U) - 1) := by
      rw [LinearMap.mem_ker]
      change x e₂ - e₂ = 0
      rw [hxe₂, sub_self]
    rw [hxe₁, ker_reflect_sub_one_eq_ker_polar hQe₁] at hmem
    rwa [LinearMap.mem_ker, QuadraticMap.polarBilin_apply_apply] at hmem
  exact ⟨h01, h02, h12⟩

private theorem linearIndependent_roots (h2 : (2 : ZMod p) ≠ 0) {c : ZMod p} (hc : c ≠ 0)
    {e₀ e₁ e₂ : U} (hQe₀ : Q e₀ = c) (hQe₁ : Q e₁ = c) (hQe₂ : Q e₂ = c)
    (h01 : QuadraticMap.polar Q e₀ e₁ = 0) (h02 : QuadraticMap.polar Q e₀ e₂ = 0)
    (h12 : QuadraticMap.polar Q e₁ e₂ = 0) :
    LinearIndependent (ZMod p) ![e₀, e₁, e₂] := by
  have h10 : QuadraticMap.polar Q e₁ e₀ = 0 := by
    rw [QuadraticMap.polar_comm]; exact h01
  have h20 : QuadraticMap.polar Q e₂ e₀ = 0 := by
    rw [QuadraticMap.polar_comm]; exact h02
  have h21 : QuadraticMap.polar Q e₂ e₁ = 0 := by
    rw [QuadraticMap.polar_comm]; exact h12
  refine LinearMap.BilinForm.linearIndependent_of_iIsOrtho (B := QuadraticMap.polarBilin Q)
    (fun i j hij => ?_) (fun i => ?_)
  · fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · show QuadraticMap.polarBilin Q e₀ e₁ = 0
      rwa [QuadraticMap.polarBilin_apply_apply]
    · show QuadraticMap.polarBilin Q e₀ e₂ = 0
      rwa [QuadraticMap.polarBilin_apply_apply]
    · show QuadraticMap.polarBilin Q e₁ e₀ = 0
      rwa [QuadraticMap.polarBilin_apply_apply]
    · exact absurd rfl hij
    · show QuadraticMap.polarBilin Q e₁ e₂ = 0
      rwa [QuadraticMap.polarBilin_apply_apply]
    · show QuadraticMap.polarBilin Q e₂ e₀ = 0
      rwa [QuadraticMap.polarBilin_apply_apply]
    · show QuadraticMap.polarBilin Q e₂ e₁ = 0
      rwa [QuadraticMap.polarBilin_apply_apply]
    · exact absurd rfl hij
  · fin_cases i
    · show QuadraticMap.polarBilin Q e₀ e₀ ≠ 0
      rw [QuadraticMap.polarBilin_apply_apply,
        ClassicalGroups.Orthogonal.polar_self_eq_two_mul, hQe₀]
      exact mul_ne_zero h2 hc
    · show QuadraticMap.polarBilin Q e₁ e₁ ≠ 0
      rw [QuadraticMap.polarBilin_apply_apply,
        ClassicalGroups.Orthogonal.polar_self_eq_two_mul, hQe₁]
      exact mul_ne_zero h2 hc
    · show QuadraticMap.polarBilin Q e₂ e₂ ≠ 0
      rw [QuadraticMap.polarBilin_apply_apply,
        ClassicalGroups.Orthogonal.polar_self_eq_two_mul, hQe₂]
      exact mul_ne_zero h2 hc

private theorem reflect_sub_mul_mem (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hs : SplitSupport X 3) {c : ZMod p}
    (hc : c ≠ 0) (hX : X = Subgroup.closure {t | t ∈ ClassRefl p Q c ∧
      HardMathSupport.Kantor79.movedSpace t ≤ HardMathSupport.Kantor79.commutatorSpace X})
    {e₀ e₁ e₂ : U} (hQe₀ : Q e₀ = c) (hQe₁ : Q e₁ = c) (hQe₂ : Q e₂ = c)
    (h01 : QuadraticMap.polar Q e₀ e₁ = 0) (h12 : QuadraticMap.polar Q e₁ e₂ = 0)
    (he₀V : e₀ ∈ HardMathSupport.Kantor79.commutatorSpace X)
    (he₁V : e₁ ∈ HardMathSupport.Kantor79.commutatorSpace X)
    (he₂V : e₂ ∈ HardMathSupport.Kantor79.commutatorSpace X) (h3 : (3 : ZMod p) ≠ 0) :
    ClassicalGroups.Orthogonal.reflect Q (e₀ - e₁) *
      ClassicalGroups.Orthogonal.reflect Q (e₁ - e₂) ∈ X := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hQd : Q (e₀ - e₁) = Q (e₁ - e₂) := by
    rw [map_sub_eq_two_mul (hQe₁.trans hQe₀.symm) h01,
      map_sub_eq_two_mul (hQe₂.trans hQe₁.symm) h12, hQe₀, hQe₁]
  have hVX : ClassicalGroups.Orthogonal.PolarNondegOn Q
      (HardMathSupport.Kantor79.commutatorSpace X) :=
    polarNondegOn_commutatorSpace hQ
      (fun g hg => IsOrthOn.isIsom (Or.inr ⟨c, hc, hX⟩ : IsOrthOn p Q X) hg) hs.1
  have hmem := ClassicalGroups.Orthogonal.reflect_mul_reflect_mem_closure_of_map_eq h2 h3 hVX
    (Submodule.sub_mem _ he₀V he₁V) (Submodule.sub_mem _ he₁V he₂V) hQd hc
  refine (Subgroup.closure_le _).mpr (fun t ht => ?_) hmem
  obtain ⟨v, ⟨hvV, hvQ⟩, rfl⟩ := ht
  rw [hX]
  refine Subgroup.subset_closure (show ClassicalGroups.Orthogonal.reflect Q v ∈
    ClassRefl p Q c ∧ HardMathSupport.Kantor79.movedSpace
      (ClassicalGroups.Orthogonal.reflect Q v) ≤
      HardMathSupport.Kantor79.commutatorSpace X from
    ⟨(mem_classRefl_iff hp hQ hc _).mpr ⟨v, hvQ, rfl⟩,
      (movedSpace_reflect_le_span Q v).trans
        (Submodule.span_le.mpr (by rintro w rfl; exact hvV))⟩)

private theorem exists_swap_of_roots (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hs : SplitSupport X 3) {c : ZMod p}
    (hc : c ≠ 0) (hX : X = Subgroup.closure {t | t ∈ ClassRefl p Q c ∧
      HardMathSupport.Kantor79.movedSpace t ≤ HardMathSupport.Kantor79.commutatorSpace X})
    {e₀ e₁ e₂ : U} (hQe₀ : Q e₀ = c) (hQe₁ : Q e₁ = c) (hQe₂ : Q e₂ = c)
    (h01 : QuadraticMap.polar Q e₀ e₁ = 0) (h02 : QuadraticMap.polar Q e₀ e₂ = 0)
    (h12 : QuadraticMap.polar Q e₁ e₂ = 0)
    (he₀V : e₀ ∈ HardMathSupport.Kantor79.commutatorSpace X)
    (he₁V : e₁ ∈ HardMathSupport.Kantor79.commutatorSpace X)
    (he₂V : e₂ ∈ HardMathSupport.Kantor79.commutatorSpace X) (h3 : (3 : ZMod p) ≠ 0) :
    ∃ s : U ≃ₗ[ZMod p] U, s ∈ X ∧ s e₀ = e₁ ∧ s e₁ = e₂ ∧ s e₂ = e₀ := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hQe₀0 : Q e₀ ≠ 0 := by rw [hQe₀]; exact hc
  have hQe₁0 : Q e₁ ≠ 0 := by rw [hQe₁]; exact hc
  have hQe₂0 : Q e₂ ≠ 0 := by rw [hQe₂]; exact hc
  have h10 : QuadraticMap.polar Q e₁ e₀ = 0 := by
    rw [QuadraticMap.polar_comm]; exact h01
  have h20 : QuadraticMap.polar Q e₂ e₀ = 0 := by
    rw [QuadraticMap.polar_comm]; exact h02
  refine ⟨ClassicalGroups.Orthogonal.reflect Q (e₀ - e₁) *
    ClassicalGroups.Orthogonal.reflect Q (e₁ - e₂),
    reflect_sub_mul_mem hp hQ hs hc hX hQe₀ hQe₁ hQe₂ h01 h12 he₀V he₁V he₂V h3, ?_, ?_, ?_⟩
  · rw [LinearEquiv.mul_apply, reflect_sub_apply_of_polar_eq_zero h10 h20,
      reflect_sub_apply_left h2 hQe₀0 (hQe₁.trans hQe₀.symm) h01]
  · rw [LinearEquiv.mul_apply, reflect_sub_apply_left h2 hQe₁0 (hQe₂.trans hQe₁.symm) h12,
      reflect_sub_apply_of_polar_eq_zero h02 h12]
  · rw [LinearEquiv.mul_apply, reflect_sub_apply_right h2 hQe₁0 (hQe₂.trans hQe₁.symm) h12,
      reflect_sub_apply_right h2 hQe₀0 (hQe₁.trans hQe₀.symm) h01]

private theorem isCyclicRootTriple_of_data {e₀ e₁ e₂ : U} {h x y : U ≃ₗ[ZMod p] U}
    (hh : h ∈ X) (hxX : x ∈ X) (hyX : y ∈ X) (hh' : IsRefl p h) (hx' : IsRefl p x)
    (hy' : IsRefl p y) (hneg₀ : h e₀ = -e₀) (hneg₁ : x e₁ = -e₁) (hneg₂ : y e₂ = -e₂)
    (hhe₀ : h = ClassicalGroups.Orthogonal.reflect Q e₀)
    (hxe₁ : x = ClassicalGroups.Orthogonal.reflect Q e₁)
    (hye₂ : y = ClassicalGroups.Orthogonal.reflect Q e₂)
    (h01 : QuadraticMap.polar Q e₀ e₁ = 0) (h02 : QuadraticMap.polar Q e₀ e₂ = 0)
    (h12 : QuadraticMap.polar Q e₁ e₂ = 0)
    (hli : LinearIndependent (ZMod p) ![e₀, e₁, e₂]) {s : U ≃ₗ[ZMod p] U} (hsX : s ∈ X)
    (hs₀ : s e₀ = e₁) (hs₁ : s e₁ = e₂) (hs₂ : s e₂ = e₀) :
    IsCyclicRootTriple p X ![h, x, y] ![e₀, e₁, e₂] s := by
  refine ⟨?_, ?_, hli, hsX, ?_⟩
  · intro i
    fin_cases i
    · exact ⟨hh, hh', hneg₀⟩
    · exact ⟨hxX, hx', hneg₁⟩
    · exact ⟨hyX, hy', hneg₂⟩
  · intro i j
    fin_cases i <;> fin_cases j
    · rfl
    · show h * x = x * h
      rw [hhe₀, hxe₁]
      exact (CFSG.LocalAnalysis.GLTheoremA.S172C.Rank.commute_reflect_of_polar_eq_zero h01).eq
    · show h * y = y * h
      rw [hhe₀, hye₂]
      exact (CFSG.LocalAnalysis.GLTheoremA.S172C.Rank.commute_reflect_of_polar_eq_zero h02).eq
    · show x * h = h * x
      rw [hhe₀, hxe₁]
      exact (CFSG.LocalAnalysis.GLTheoremA.S172C.Rank.commute_reflect_of_polar_eq_zero
        (by rw [QuadraticMap.polar_comm]; exact h01)).eq
    · rfl
    · show x * y = y * x
      rw [hxe₁, hye₂]
      exact (CFSG.LocalAnalysis.GLTheoremA.S172C.Rank.commute_reflect_of_polar_eq_zero h12).eq
    · show y * h = h * y
      rw [hhe₀, hye₂]
      exact (CFSG.LocalAnalysis.GLTheoremA.S172C.Rank.commute_reflect_of_polar_eq_zero
        (by rw [QuadraticMap.polar_comm]; exact h02)).eq
    · show y * x = x * y
      rw [hxe₁, hye₂]
      exact (CFSG.LocalAnalysis.GLTheoremA.S172C.Rank.commute_reflect_of_polar_eq_zero
        (by rw [QuadraticMap.polar_comm]; exact h12)).eq
    · rfl
  · intro i
    fin_cases i
    · exact hs₀
    · exact hs₁
    · exact hs₂

theorem exists_isCyclicRootTriple_of_commute (hp5 : p = 5) [Module.Finite (ZMod p) U]
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hs : SplitSupport X 3) {c : ZMod p}
    (hc : c ≠ 0) (hX : X = Subgroup.closure {t | t ∈ ClassRefl p Q c ∧
      HardMathSupport.Kantor79.movedSpace t ≤ HardMathSupport.Kantor79.commutatorSpace X})
    (hh : h ∈ X) (hh' : IsRefl p h) {x y : U ≃ₗ[ZMod p] U} (hx : x ∈ reflStab p X h)
    (hy : y ∈ reflStab p X h) (hx' : IsRefl p x) (hy' : IsRefl p y) (hxy : x * y = y * x)
    (hne : x ≠ y) :
    ∃ (r : Fin 3 → U ≃ₗ[ZMod p] U) (e : Fin 3 → U) (s : U ≃ₗ[ZMod p] U),
      r 0 = h ∧ IsCyclicRootTriple p X r e s := by
  have hp2 : p ≠ 2 := by rw [hp5]; decide
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp2
  have hp3 : p ≠ 3 := by rw [hp5]; decide
  have h3 : (3 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 3 hp3
  have ho : IsOrthOn p Q X := Or.inr ⟨c, hc, hX⟩
  have hXiso : ∀ g ∈ X, IsIsom p Q g := fun g hg => ho.isIsom hg
  have hxX : x ∈ X := reflSubgroupIn_le X _ hx
  have hyX : y ∈ X := reflSubgroupIn_le X _ hy
  obtain ⟨e₀, e₁, e₂, hQe₀, hQe₁, hQe₂, he₀, he₁, he₂, he₀V, he₁V, he₂V⟩ :=
    exists_roots_of_commute hp5 hQ hc hX hh hh' hx hy hx' hy'
  have hQe₀0 : Q e₀ ≠ 0 := by rw [hQe₀]; exact hc
  have hQe₁0 : Q e₁ ≠ 0 := by rw [hQe₁]; exact hc
  have hQe₂0 : Q e₂ ≠ 0 := by rw [hQe₂]; exact hc
  have hneg₀ : h e₀ = -e₀ := by rw [he₀]; exact reflect_apply_self hQe₀0
  have hneg₁ : x e₁ = -e₁ := by rw [he₁]; exact reflect_apply_self hQe₁0
  have hneg₂ : y e₂ = -e₂ := by rw [he₂]; exact reflect_apply_self hQe₂0
  obtain ⟨h01, h02, h12⟩ := roots_pairwise_orthogonal hp2 hQ hh' (hXiso h hh) hx' hy'
    (hXiso x hxX) (hXiso y hyX) hx hy hxy hne hQe₀0 hQe₁0 hQe₂0 he₀ he₁ he₂
  obtain ⟨s, hsX, hs₀, hs₁, hs₂⟩ := exists_swap_of_roots hp2 hQ hs hc hX hQe₀ hQe₁ hQe₂
    h01 h02 h12 he₀V he₁V he₂V h3
  exact ⟨![h, x, y], ![e₀, e₁, e₂], s, by simp,
    isCyclicRootTriple_of_data hh hxX hyX hh' hx' hy' hneg₀ hneg₁ hneg₂ he₀ he₁ he₂
      h01 h02 h12 (linearIndependent_roots h2 hc hQe₀ hQe₁ hQe₂ h01 h02 h12) hsX hs₀ hs₁ hs₂⟩

private theorem exists_orthogonal_pair_of_polarNondegOn [Module.Finite (ZMod p) U]
    (h2 : (2 : ZMod p) ≠ 0)
    {S : Submodule (ZMod p) U} (hS : ClassicalGroups.Orthogonal.PolarNondegOn Q S)
    (hS3 : 3 ≤ Module.finrank (ZMod p) S) :
    ∃ a z : U, a ∈ S ∧ z ∈ S ∧ Q a ≠ 0 ∧ Q z = Q a ∧
      QuadraticMap.polar Q a z = 0 := by
  have hSne : S ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hS3
    omega
  obtain ⟨a, haS, hQa⟩ := hS.exists_map_ne_zero hSne
  have hndF : ClassicalGroups.Orthogonal.PolarNondegOn Q
      (S ⊓ LinearMap.ker (QuadraticMap.polarBilin Q a)) := hS.inf_ker h2 haS hQa
  have hfinF : Module.finrank (ZMod p) ↥(S ⊓ LinearMap.ker
      (QuadraticMap.polarBilin Q a)) + 1 = Module.finrank (ZMod p) S :=
    ClassicalGroups.Orthogonal.finrank_inf_ker_polarBilin_add_one h2 haS hQa
  have hF2 : 2 ≤ Module.finrank (ZMod p) ↥(S ⊓ LinearMap.ker
      (QuadraticMap.polarBilin Q a)) := by omega
  obtain ⟨z, hzF, hQz⟩ := hndF.exists_map_eq h2 hF2 (Q a)
  refine ⟨a, z, haS, hzF.1, hQa, hQz, ?_⟩
  rw [← QuadraticMap.polarBilin_apply_apply]
  exact LinearMap.mem_ker.mp hzF.2

private theorem reflect_mem_of_closure (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {Q : QuadraticForm (ZMod p) U} {X : Subgroup (U ≃ₗ[ZMod p] U)}
    (hX : X = Subgroup.closure {t | IsRefl p t ∧ IsIsom p Q t ∧
      HardMathSupport.Kantor79.movedSpace t ≤ HardMathSupport.Kantor79.commutatorSpace X})
    {b : U} (hbV : b ∈ HardMathSupport.Kantor79.commutatorSpace X) (hQb : Q b ≠ 0) :
    ClassicalGroups.Orthogonal.reflect Q b ∈ X := by
  rw [hX]
  exact Subgroup.subset_closure ⟨isRefl_reflect hp hQb, isIsom_reflect Q b,
    (movedSpace_reflect_le_span Q b).trans
      (Submodule.span_le.mpr (by rintro v rfl; exact hbV))⟩

theorem exists_three_lt_orderOf_reflStab (hp3 : p = 3) [Module.Finite (ZMod p) U]
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {m : ℕ} (hs : SplitSupport X m)
    (hm : 4 ≤ m)
    (hX : X = Subgroup.closure {t | IsRefl p t ∧ IsIsom p Q t ∧
      HardMathSupport.Kantor79.movedSpace t ≤ HardMathSupport.Kantor79.commutatorSpace X})
    (hh : h ∈ X) (hh' : IsRefl p h) :
    ∃ x ∈ reflStab p X h, ∃ y ∈ reflStab p X h, IsRefl p x ∧ IsRefl p y ∧
      3 < orderOf (x * y) := by
  have hp2 : p ≠ 2 := by rw [hp3]; decide
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp2
  have hXiso : ∀ g ∈ X, IsIsom p Q g := fun g hg => IsOrthOn.isIsom (Or.inl hX) hg
  obtain ⟨e, hQe, hee⟩ := DimThree.exists_root_of_isRefl_isIsom hp2 hQ hh' (hXiso h hh)
  have he0 : e ≠ 0 := fun h0 => hQe (by rw [h0]; exact map_zero Q)
  have heV : e ∈ HardMathSupport.Kantor79.commutatorSpace X :=
    HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hh
      (HardMathSupport.Kantor79.mem_movedSpace_of_apply_eq_neg h2 hee)
  have he' : e ∉ LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1) := by
    intro hmem
    rw [LinearMap.mem_ker] at hmem
    change h e - e = 0 at hmem
    rw [hee] at hmem
    exact he0 (CFSG.StandardType.ZS.eq_zero_of_eq_neg h2 (sub_eq_zero.mp hmem).symm)
  have hfinE : Module.finrank (ZMod p) ↥(HardMathSupport.Kantor79.commutatorSpace X ⊓
      LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)) + 1 = m := by
    have h := IsRefl.finrank_inf_ker_sub_one_add_one (p := p) hp2 hh'
      (A := HardMathSupport.Kantor79.commutatorSpace X) heV he'
    rwa [hs.2.1] at h
  have hker : LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1) =
      LinearMap.ker (QuadraticMap.polarBilin Q e) := by
    rw [DimThree.eq_of_isRefl_isIsom_of_apply_eq_neg hp2 hQ hh' (hXiso h hh)
      (isRefl_reflect hp2 hQe) (isIsom_reflect Q e) he0 hee (reflect_apply_self hQe)]
    exact ker_reflect_sub_one_eq_ker_polar hQe
  have hndE : ClassicalGroups.Orthogonal.PolarNondegOn Q
      (HardMathSupport.Kantor79.commutatorSpace X ⊓
        LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)) := by
    rw [hker]
    exact (polarNondegOn_commutatorSpace hQ hXiso hs.1).inf_ker h2 heV hQe
  obtain ⟨a, z, haE, hzE, hQa, hQz, haz⟩ :=
    exists_orthogonal_pair_of_polarNondegOn h2 hndE (by omega)
  have hQaz : Q (a + z) ≠ 0 := by
    rw [QuadraticMap.map_add Q, hQz, haz, add_zero, ← two_mul]; exact mul_ne_zero h2 hQa
  have hxX := reflect_mem_reflStab hp2 haE.2 hQa (reflect_mem_of_closure hp2 hX haE.1 hQa)
  have hyX := reflect_mem_reflStab hp2 (add_mem haE.2 hzE.2) hQaz
    (reflect_mem_of_closure hp2 hX (add_mem haE.1 hzE.1) hQaz)
  have hord : orderOf (ClassicalGroups.Orthogonal.reflect Q a *
      ClassicalGroups.Orthogonal.reflect Q (a + z)) = 4 :=
    ClassicalGroups.Orthogonal.orderOf_reflect_mul_reflect_add h2 hQa hQz haz
  exact ⟨ClassicalGroups.Orthogonal.reflect Q a, hxX,
    ClassicalGroups.Orthogonal.reflect Q (a + z), hyX, isRefl_reflect hp2 hQa,
    isRefl_reflect hp2 hQaz, by rw [hord]; norm_num⟩

end CFSG.StandardType.ZS

end
