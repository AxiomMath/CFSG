module

public import CFSG.RankThree.PartOne.S11d.FixedFactorExt
public import CFSG.RankThree.PartOne.S11d.OddHerm
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeLinear

public section

namespace CFSG.RankThree.PartOne

open CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.OddIso

section Fix

variable {F : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 F K}
  {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {B : V →ₛₗ[h.bar] V →ₗ[K] K} {A : Module.End K V} {p : ℕ} [CharP K 2]

omit [FiniteDimensional K V] [CharP K 2] in
theorem fix_perp (hAB : ∀ v w, B (A v) (A w) = B v w) {v : V}
    (hv : v ∈ LinearMap.ker (A - 1)) {w : V} (hw : w ∈ LinearMap.range (A - 1)) : B v w = 0 := by
  obtain ⟨u, rfl⟩ := hw
  exact B_fix_range B hAB (sub_eq_zero.mp (LinearMap.mem_ker.mp hv)) u

omit [FiniteDimensional K V] [CharP K 2] in
theorem range_perp (hAB : ∀ v w, B (A v) (A w) = B v w) {v : V}
    (hv : v ∈ LinearMap.ker (A - 1)) {w : V} (hw : w ∈ LinearMap.range (A - 1)) : B w v = 0 := by
  obtain ⟨u, rfl⟩ := hw
  exact B_range_fix B hAB (sub_eq_zero.mp (LinearMap.mem_ker.mp hv)) u

omit [FiniteDimensional K V] [CharP K 2] in
theorem hermitian_of_isSymm (hB : B.IsSymm) (x y : V) : B y x = h.bar (B x y) :=
  (hB.eq x y).symm

omit [FiniteDimensional K V] in
theorem fixSpace_sep (hBl : B.SeparatingLeft) (hAB : ∀ v w, B (A v) (A w) = B v w)
    (hp : Odd p) (hA : A ^ p = 1) :
    (B.domRestrict₁₂ (LinearMap.ker (A - 1)) (LinearMap.ker (A - 1))).SeparatingLeft := by
  intro x hx
  apply Subtype.ext
  exact fix_sepH (fun v hv => hBl v hv) hAB hp hA x.1 x.2 fun v' hv' => hx ⟨v', hv'⟩

omit [FiniteDimensional K V] [CharP K 2] in
theorem fixSpace_isSymm (hB : B.IsSymm) :
    (B.domRestrict₁₂ (LinearMap.ker (A - 1)) (LinearMap.ker (A - 1))).IsSymm :=
  hB.domRestrict _

theorem mem_Dfix_iff' (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    (hAB : ∀ v w, B (A v) (A w) = B v w) (hp : Odd p) (hA : A ^ p = 1)
    (γ : LinearMap.GeneralLinearGroup K V) :
    γ ∈ Dfix B (isCompl_ker_range hp hA) ↔ γ ∈ sesqSpecialUnitaryGroup B ∧
      ∀ w ∈ LinearMap.range (A - 1), (γ : V →ₗ[K] V) w = w :=
  mem_Dfix_iff _ (hermitian_of_isSymm hB) (fun _ hv _ hw => fix_perp hAB hv hw)
    (fun _ hw _ hv => range_perp hAB hv hw) (range_sepH (fun v hv => hBl v hv) hAB hp hA) γ

theorem two_mem_Dfix (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    (hAB : ∀ v w, B (A v) (A w) = B v w) (hp : Odd p) (hA : A ^ p = 1)
    (hcyc : IsCyclicOn A (LinearMap.range (A - 1))) {g : LinearMap.GeneralLinearGroup K V}
    (hg : g ∈ sesqSpecialUnitaryGroup B) (hcomm : (g : V →ₗ[K] V) * A = A * (g : V →ₗ[K] V))
    {k : ℕ} (hgk : (g : V →ₗ[K] V) ^ (2 ^ k) = 1) : g ∈ Dfix B (isCompl_ker_range hp hA) :=
  (mem_Dfix_iff' hB hBl hAB hp hA g).mpr ⟨hg, eq_id_on_range_of_two_pow hp hA hcyc hcomm hgk⟩

theorem conj_mem_Dfix (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    (hAB : ∀ v w, B (A v) (A w) = B v w) (hp : Odd p) (hA : A ^ p = 1)
    {g : LinearMap.GeneralLinearGroup K V} (hg : g ∈ sesqUnitaryGroup B)
    (hcomm : (g : V →ₗ[K] V) * A = A * (g : V →ₗ[K] V))
    {δ : LinearMap.GeneralLinearGroup K V} (hδ : δ ∈ Dfix B (isCompl_ker_range hp hA)) :
    g * δ * g⁻¹ ∈ Dfix B (isCompl_ker_range hp hA) := by
  obtain ⟨hδS, hδfix⟩ := (mem_Dfix_iff' hB hBl hAB hp hA δ).mp hδ
  obtain ⟨hδU, hδdet⟩ := mem_sesqSpecialUnitaryGroup.mp hδS
  have hcomm' : (g⁻¹ : LinearMap.GeneralLinearGroup K V) * A =
      A * (g⁻¹ : LinearMap.GeneralLinearGroup K V) :=
    (Commute.units_inv_left (show Commute (g : V →ₗ[K] V) A from hcomm)).eq
  refine (mem_Dfix_iff' hB hBl hAB hp hA _).mpr ⟨mem_sesqSpecialUnitaryGroup.mpr ⟨?_, ?_⟩, ?_⟩
  · exact mul_mem (mul_mem hg hδU) (inv_mem hg)
  · have h1 : (((g * δ * g⁻¹ : LinearMap.GeneralLinearGroup K V)) : V →ₗ[K] V) =
        (g : V →ₗ[K] V) * (δ : V →ₗ[K] V) * ((g⁻¹ : LinearMap.GeneralLinearGroup K V) :
          V →ₗ[K] V) := by simp
    have h2 : LinearMap.det (g : V →ₗ[K] V) *
        LinearMap.det ((g⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) = 1 := by
      rw [← LinearMap.det_comp, ← Module.End.mul_eq_comp, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, map_one]
    rw [h1, map_mul, map_mul, hδdet]
    linear_combination h2
  · intro w hw
    have hgw : ((g⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) w ∈
        LinearMap.range (A - 1) := range_map_mem hcomm' hw
    have h3 := hδfix _ hgw
    change (g : V →ₗ[K] V) ((δ : V →ₗ[K] V) (((g⁻¹ : LinearMap.GeneralLinearGroup K V) :
      V →ₗ[K] V) w)) = w
    rw [h3]
    exact apply_inv_apply' g w

theorem scalar_of_commute_Dfix (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    (hAB : ∀ v w, B (A v) (A w) = B v w) (hp : Odd p) (hA : A ^ p = 1)
    (hm : 2 ≤ Module.finrank K (LinearMap.ker (A - 1))) (hq : 2 ≤ 2 ^ F)
    {g : LinearMap.GeneralLinearGroup K V} (hcomm : (g : V →ₗ[K] V) * A = A * (g : V →ₗ[K] V))
    (hDc : ∀ δ ∈ Dfix B (isCompl_ker_range hp hA), Commute g δ) :
    ∃ c : K, ∀ v ∈ LinearMap.ker (A - 1), (g : V →ₗ[K] V) v = c • v := by
  have hgV : ∀ v ∈ LinearMap.ker (A - 1), (g : V →ₗ[K] V) v ∈ LinearMap.ker (A - 1) := by
    intro v hv
    rw [LinearMap.mem_ker] at hv ⊢
    have := congrArg (fun f : V →ₗ[K] V => f v) hcomm
    simp only [Module.End.mul_apply] at this
    have hv' : A v = v := sub_eq_zero.mp hv
    rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero, ← this, hv']
  obtain ⟨c, hc⟩ := KCUnitary.exists_smul_of_commute_special_unitary h
    (fixSpace_isSymm hB) (fixSpace_sep hBl hAB hp hA) hm hq ((g : V →ₗ[K] V).restrict hgV)
    (fun δ hδ => by
      have hmem : extGL (isCompl_ker_range hp hA) δ ∈ Dfix B (isCompl_ker_range hp hA) :=
        ⟨δ, hδ, rfl⟩
      have hc1 := hDc _ hmem
      refine LinearMap.ext fun x => Subtype.ext ?_
      have h1 := congrArg (fun f : V →ₗ[K] V => f (x : V)) (Units.ext_iff.mp hc1.eq)
      simp only [Units.val_mul, Module.End.mul_apply] at h1
      rw [extGL_apply_left (isCompl_ker_range hp hA) δ x.2,
        extGL_apply_left (isCompl_ker_range hp hA) δ (hgV (x : V) x.2)] at h1
      exact h1)
  exact ⟨c, fun v hv => by simpa using congrArg Subtype.val (hc ⟨v, hv⟩)⟩

omit [FiniteDimensional K V] in
theorem commute_of_scalar (hp : Odd p) (hA : A ^ p = 1)
    (hcyc : IsCyclicOn A (LinearMap.range (A - 1))) {g g' : LinearMap.GeneralLinearGroup K V}
    (hg : (g : V →ₗ[K] V) * A = A * (g : V →ₗ[K] V))
    (hg' : (g' : V →ₗ[K] V) * A = A * (g' : V →ₗ[K] V))
    (hscal : ∃ c : K, ∀ v ∈ LinearMap.ker (A - 1), (g : V →ₗ[K] V) v = c • v) :
    g * g' = g' * g := by
  obtain ⟨c, hc⟩ := hscal
  have hg'V : ∀ v ∈ LinearMap.ker (A - 1), (g' : V →ₗ[K] V) v ∈ LinearMap.ker (A - 1) := by
    intro v hv
    rw [LinearMap.mem_ker] at hv ⊢
    have := congrArg (fun f : V →ₗ[K] V => f v) hg'
    simp only [Module.End.mul_apply] at this
    have hv' : A v = v := sub_eq_zero.mp hv
    rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero, ← this, hv']
  refine Units.ext (LinearMap.ext fun v => ?_)
  obtain ⟨v₁, hv₁, w, hw, rfl⟩ := exists_fix_add_range hp hA v
  simp only [Units.val_mul, Module.End.mul_apply, map_add]
  rw [hc _ (hg'V _ hv₁), hc _ hv₁, map_smul]
  congr 1
  exact commute_on_range hcyc hg hg' w hw

end Fix

end CFSG.RankThree.PartOne
