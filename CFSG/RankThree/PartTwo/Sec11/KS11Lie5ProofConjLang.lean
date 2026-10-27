module

public import CFSG.LieType.AlgebraicGroups.ConnectedToralLangFrobenius
public import CFSG.LieType.AlgebraicGroups.E6GraphCentralizerLangCurves

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups

variable {τ : Tag} {L : Type} [Field L] (p : ℕ) [Fact p.Prime] [CharP L p]

theorem frobTwistGL_conj (e : ℕ) (Q k g : ModGL τ L) :
    k⁻¹ * frobTwistGL τ L p e Q (k * g * k⁻¹) * k =
      frobTwistGL τ L p e (k⁻¹ * Q * entrywiseFrobGL τ L p e k) g := by
  rw [frobTwistGL_apply, frobTwistGL_apply, map_mul, map_mul, map_inv]
  group

variable [IsAlgClosed L]

theorem exists_fixed_conj_of_lang
    {e : ℕ} (he : 1 ≤ e) (Q : ModGL τ L)
    (hQG : ∀ g ∈ adjointGroup τ L, frobTwistGL τ L p e Q g ∈ adjointGroup τ L)
    {d : ModGL τ L}
    (hirr : IsPointIrreducible L (transportPoints (modGLPoint τ L) (graphCentralizer τ L d)))
    {k : ModGL τ L} (hk : k ∈ adjointGroup τ L) {A s x : ModGL τ L} (hA : A = k * d * k⁻¹)
    (hFA : frobTwistGL τ L p e Q A = A) (hFs : frobTwistGL τ L p e Q s = s)
    (hx : x ∈ adjointGroup τ L) (hxs : x * s * x⁻¹ = A) :
    ∃ y ∈ adjointGroup τ L, frobTwistGL τ L p e Q y = y ∧ y * s * y⁻¹ = A := by
  set F := frobTwistGL τ L p e Q with hFdef
  set Q' := k⁻¹ * Q * entrywiseFrobGL τ L p e k with hQ'
  set F' := frobTwistGL τ L p e Q' with hF'def
  have hF' : ∀ g, F' g = k⁻¹ * F (k * g * k⁻¹) * k := fun g =>
    (frobTwistGL_conj p e Q k g).symm
  have hFZ : ∀ g ∈ graphCentralizer τ L d, F' g ∈ graphCentralizer τ L d := by
    intro g hg
    obtain ⟨hgG, hgc⟩ := Subgroup.mem_inf.1 hg
    rw [Subgroup.mem_centralizer_singleton_iff] at hgc
    have hkg : k * g * k⁻¹ ∈ adjointGroup τ L := mul_mem (mul_mem hk hgG) (inv_mem hk)
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [hF']
      exact mul_mem (mul_mem (inv_mem hk) (hQG _ hkg)) hk
    · rw [Subgroup.mem_centralizer_singleton_iff, hF']
      have hcA : k * g * k⁻¹ * A = A * (k * g * k⁻¹) := by
        rw [hA]
        calc k * g * k⁻¹ * (k * d * k⁻¹) = k * (g * d) * k⁻¹ := by group
          _ = k * (d * g) * k⁻¹ := by rw [hgc]
          _ = k * d * k⁻¹ * (k * g * k⁻¹) := by group
      have hFcA : F (k * g * k⁻¹) * A = A * F (k * g * k⁻¹) := by
        have h := congrArg F hcA
        rwa [map_mul F (k * g * k⁻¹) A, map_mul F A (k * g * k⁻¹), hFA] at h
      have hd : d = k⁻¹ * A * k := by rw [hA]; group
      rw [hd]
      calc k⁻¹ * F (k * g * k⁻¹) * k * (k⁻¹ * A * k) = k⁻¹ * (F (k * g * k⁻¹) * A) * k := by
            group
        _ = k⁻¹ * (A * F (k * g * k⁻¹)) * k := by rw [hFcA]
        _ = k⁻¹ * A * k * (k⁻¹ * F (k * g * k⁻¹) * k) := by group
  obtain ⟨hZ, -, -, -⟩ := graphCentralizer_realization d hirr
  obtain ⟨-, -, -, hlang⟩ := exists_frobTwist_restriction p hZ he Q' hFZ
  have hFx : F x * s * (F x)⁻¹ = A := by
    have h := congrArg F hxs
    rwa [map_mul, map_mul, map_inv, hFs, hFA] at h
  have hcA : x * (F x)⁻¹ * A = A * (x * (F x)⁻¹) := by
    calc x * (F x)⁻¹ * A = x * ((F x)⁻¹ * A * F x) * (F x)⁻¹ := by group
      _ = x * s * x⁻¹ * (x * (F x)⁻¹) := by rw [← hFx]; group
      _ = A * (x * (F x)⁻¹) := by rw [hxs]
  have hFxG : F x ∈ adjointGroup τ L := hQG x hx
  have hc'Z : k⁻¹ * (x * (F x)⁻¹) * k ∈ graphCentralizer τ L d := by
    refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem (inv_mem hk) (mul_mem hx (inv_mem hFxG))) hk, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hd : d = k⁻¹ * A * k := by rw [hA]; group
    rw [hd]
    calc k⁻¹ * (x * (F x)⁻¹) * k * (k⁻¹ * A * k) = k⁻¹ * (x * (F x)⁻¹ * A) * k := by group
      _ = k⁻¹ * (A * (x * (F x)⁻¹)) * k := by rw [hcA]
      _ = k⁻¹ * A * k * (k⁻¹ * (x * (F x)⁻¹) * k) := by group
  obtain ⟨z', hz'Z, hz'c⟩ := hlang _ hc'Z
  obtain ⟨hz'G, hz'd⟩ := Subgroup.mem_inf.1 hz'Z
  rw [Subgroup.mem_centralizer_singleton_iff] at hz'd
  set z := k * z' * k⁻¹ with hz
  have hzA : z * A = A * z := by
    rw [hz, hA]
    calc k * z' * k⁻¹ * (k * d * k⁻¹) = k * (z' * d) * k⁻¹ := by group
      _ = k * (d * z') * k⁻¹ := by rw [hz'd]
      _ = k * d * k⁻¹ * (k * z' * k⁻¹) := by group
  have hFz : F z = z * (x * (F x)⁻¹) := by
    have h1 : F' z' = z' * (k⁻¹ * (x * (F x)⁻¹) * k) := by
      rw [← hz'c, hF'def]
      group
    rw [hF'] at h1
    have h2 : F z = k * (k⁻¹ * F (k * z' * k⁻¹) * k) * k⁻¹ := by rw [hz]; group
    rw [h2, h1, hz]
    group
  refine ⟨z * x, mul_mem (mul_mem (mul_mem hk hz'G) (inv_mem hk)) hx, ?_, ?_⟩
  · rw [map_mul, hFz]
    group
  · calc z * x * s * (z * x)⁻¹ = z * (x * s * x⁻¹) * z⁻¹ := by group
      _ = A := by rw [hxs, hzA]; group

end CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof
