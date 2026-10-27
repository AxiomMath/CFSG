module

public import CFSG.LieType.Steinberg.Isogeny.E6
public import CFSG.LieType.Chevalley.CoordinateFieldBaseChange
public import CFSG.LieType.Chevalley.PinnedBridge
public import Certificates.Certificate123

public noncomputable section

namespace CFSG.StandardType.E6Dep.ZL

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Adjoint


section EntrywiseBaseChange

variable {k E : Type} [Field k] [Field E]

private def zlEndFun (ι : k →+* E) (d : ℕ) (f : Module.End k (Fin d →₀ k)) :
    Module.End E (Fin d →₀ E) :=
  Finsupp.linearCombination E fun a : Fin d =>
    Finsupp.mapRange ι ι.map_zero (f (Finsupp.single a 1))

private theorem zlEndFun_single (ι : k →+* E) (d : ℕ) (f : Module.End k (Fin d →₀ k))
    (a : Fin d) :
    zlEndFun ι d f (Finsupp.single a 1) =
      Finsupp.mapRange ι ι.map_zero (f (Finsupp.single a 1)) := by
  simp [zlEndFun]

private theorem zlMapRange_add (ι : k →+* E) {d : ℕ} (v w : Fin d →₀ k) :
    Finsupp.mapRange ι ι.map_zero (v + w) =
      Finsupp.mapRange ι ι.map_zero v + Finsupp.mapRange ι ι.map_zero w := by
  ext a
  simp

private theorem zlMapRange_smul (ι : k →+* E) {d : ℕ} (c : k) (v : Fin d →₀ k) :
    Finsupp.mapRange ι ι.map_zero (c • v) = ι c • Finsupp.mapRange ι ι.map_zero v := by
  ext a
  simp

private theorem zlEndFun_mapRange (ι : k →+* E) (d : ℕ) (f : Module.End k (Fin d →₀ k))
    (v : Fin d →₀ k) :
    zlEndFun ι d f (Finsupp.mapRange ι ι.map_zero v) =
      Finsupp.mapRange ι ι.map_zero (f v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, zlMapRange_add, hv, hw]
  | single a c =>
    rw [Finsupp.mapRange_single, ← Finsupp.smul_single_one a (ι c), map_smul,
      zlEndFun_single, ← Finsupp.smul_single_one a c, map_smul, zlMapRange_smul]

private def zlEnd (ι : k →+* E) (d : ℕ) :
    Module.End k (Fin d →₀ k) →+* Module.End E (Fin d →₀ E) where
  toFun := zlEndFun ι d
  map_one' := by
    refine CFSG.LieType.Steinberg.Minuscule.ext_single fun a => ?_
    simp [zlEndFun_single]
  map_mul' f g := by
    refine CFSG.LieType.Steinberg.Minuscule.ext_single fun a => ?_
    simp only [Module.End.mul_apply, zlEndFun_single, zlEndFun_mapRange]
  map_zero' := by
    refine CFSG.LieType.Steinberg.Minuscule.ext_single fun a => ?_
    simp [zlEndFun_single]
  map_add' f g := by
    refine CFSG.LieType.Steinberg.Minuscule.ext_single fun a => ?_
    simp only [LinearMap.add_apply, zlEndFun_single, zlMapRange_add]

private theorem zlEnd_apply (ι : k →+* E) (d : ℕ) (f : Module.End k (Fin d →₀ k)) :
    zlEnd ι d f = zlEndFun ι d f :=
  rfl

private theorem zlEnd_injective (ι : k →+* E) (d : ℕ) : Function.Injective (zlEnd ι d) := by
  intro f g h
  refine CFSG.LieType.Steinberg.Minuscule.ext_single fun a => ?_
  have h' : zlEndFun ι d f (Finsupp.single a 1) = zlEndFun ι d g (Finsupp.single a 1) := by
    rw [← zlEnd_apply, ← zlEnd_apply, h]
  rw [zlEndFun_single, zlEndFun_single] at h'
  exact Finsupp.mapRange_injective ι ι.map_zero ι.injective h'

private theorem zlEnd_smul (ι : k →+* E) (d : ℕ) (c : k) (f : Module.End k (Fin d →₀ k)) :
    zlEnd ι d (c • f) = ι c • zlEnd ι d f := by
  refine CFSG.LieType.Steinberg.Minuscule.ext_single fun a => ?_
  simp only [zlEnd_apply, LinearMap.smul_apply, zlEndFun_single, zlMapRange_smul]

private theorem zlEnd_rootOp {τ : Tag} (D : MinData τ) (ι : k →+* E) (γ : Fin τ.rank → ℤ) :
    zlEnd ι D.d (D.rootOp k γ) = D.rootOp E γ := by
  have hdig : ∀ (d c : ℕ), Finsupp.mapRange ι ι.map_zero (digVec k d c) = digVec E d c := by
    intro d c
    unfold digVec
    split_ifs with h
    · simp only [zlMapRange_smul, Finsupp.mapRange_single, map_one, map_pow, map_neg]
    · exact Finsupp.mapRange_zero
  have htoEnd : ∀ M : ℕ, zlEndFun ι D.d (toEnd k D.d M) = toEnd E D.d M := by
    intro M
    refine CFSG.LieType.Steinberg.Minuscule.ext_single fun a => ?_
    rw [zlEndFun_single, toEnd_single, toEnd_single, hdig]
  unfold MinData.rootOp
  split_ifs with h
  · exact htoEnd _
  · exact map_zero _

private theorem zl_units_map_xu {τ : Tag} {D : MinData τ} (ι : k →+* E) (hV : D.Valid)
    (γ : Fin τ.rank → ℤ) (c : k) :
    Units.map (zlEnd ι D.d).toMonoidHom (hV.xu k γ c) = hV.xu E γ (ι c) := by
  refine Units.ext ?_
  change zlEnd ι D.d (hV.xu k γ c : Module.End k (Fin D.d →₀ k)) =
    (hV.xu E γ (ι c) : Module.End E (Fin D.d →₀ E))
  rw [hV.xu_val, hV.xu_val, map_add, map_one, zlEnd_smul, zlEnd_rootOp]

private theorem zl_minGroup_le_comap {τ : Tag} {D : MinData τ} (ι : k →+* E) (hV : D.Valid) :
    hV.minGroup k ≤ (hV.minGroup E).comap (Units.map (zlEnd ι D.d).toMonoidHom) := by
  rw [MinData.Valid.minGroup, Subgroup.closure_le]
  rintro _ ⟨γ, hγ, c, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_comap, zl_units_map_xu]
  exact hV.xu_mem E γ (ι c)

def scBase (ι : k →+* E) : ↥(e6Data_valid.minGroup k) →* ↥(e6Data_valid.minGroup E) :=
  MonoidHom.codRestrict
    ((Units.map (zlEnd ι e6Data.d).toMonoidHom).comp (e6Data_valid.minGroup k).subtype)
    (e6Data_valid.minGroup E)
    fun g => Subgroup.mem_comap.1 (zl_minGroup_le_comap ι e6Data_valid g.2)

theorem scBase_injective (ι : k →+* E) : Function.Injective (scBase ι) := by
  intro g h hgh
  refine Subtype.ext (Units.map_injective (zlEnd_injective ι e6Data.d) ?_)
  exact congrArg Subtype.val hgh

theorem scBase_xm (ι : k →+* E) (γ : Fin (Tag.rank .E6) → ℤ) (c : k) :
    scBase ι (e6Data_valid.xm k γ c) = e6Data_valid.xm E γ (ι c) :=
  Subtype.ext (zl_units_map_xu ι e6Data_valid γ c)

private theorem zl_minGroup_hom_eq_of_gens {τ : Tag} {D : MinData τ} (hV : D.Valid) {H : Type*}
    [Group H] (ψ₁ ψ₂ : ↥(hV.minGroup k) →* H)
    (hgen : ∀ γ : Fin τ.rank → ℤ, IsRoot τ γ → ∀ c : k, ψ₁ (hV.xm k γ c) = ψ₂ (hV.xm k γ c)) :
    ψ₁ = ψ₂ := by
  have key : ∀ x : (Module.End k (Fin D.d →₀ k))ˣ,
      x ∈ Subgroup.closure {g | ∃ γ, IsRoot τ γ ∧ ∃ c, g = hV.xu k γ c} →
        ∀ h : x ∈ hV.minGroup k, ψ₁ ⟨x, h⟩ = ψ₂ ⟨x, h⟩ := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨γ, hγ, c, rfl⟩ := hx
      intro h
      exact hgen γ hγ c
    | one =>
      intro h
      exact (map_one ψ₁).trans (map_one ψ₂).symm
    | mul x y hx hy ihx ihy =>
      intro h
      have e : (⟨x * y, h⟩ : ↥(hV.minGroup k)) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
      rw [e, map_mul, map_mul]
      exact congrArg₂ (· * ·) (ihx hx) (ihy hy)
    | inv x hx ih =>
      intro h
      have e : (⟨x⁻¹, h⟩ : ↥(hV.minGroup k)) = (⟨x, hx⟩ : ↥(hV.minGroup k))⁻¹ := rfl
      rw [e, map_inv, map_inv, ih hx]
  refine MonoidHom.ext fun g => ?_
  obtain ⟨x, hx⟩ := g
  exact key x hx hx

private theorem zl_baseChangeGL_eltUnit {τ : Tag} (F : RootOperatorFamily τ) (ι : k →+* E)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (c : k) :
    baseChangeGL (τ := τ) ι (F.eltUnit k ⟨α, hα⟩ c) = F.eltUnit E ⟨α, hα⟩ (ι c) := by
  have hk : F.eltUnit k ⟨α, hα⟩ c =
      pinnedX τ k α (((F.pinnedFamilySign α : ℤ) : k) * c) := by
    rw [F.pinnedX_eq_eltUnit k hα, ← mul_assoc, F.pinnedFamilySign_mul_self k α, one_mul]
  rw [hk, baseChangeGL_pinnedX, F.pinnedX_eq_eltUnit E hα, map_mul, map_intCast, ← mul_assoc,
    F.pinnedFamilySign_mul_self E α, one_mul]

private theorem zl_yPar_coe_eltUnit {γ : Fin (Tag.rank .E6) → ℤ} (hγ : IsRoot .E6 γ) (c : k) :
    ((yPar (rootOperatorFamily .E6) e6AdjData_valid γ c : ↥(adjointGroup .E6 k)) :
        ModGL .E6 k) =
      (rootOperatorFamily .E6).eltUnit k ⟨γ, hγ⟩
        ((relSignOr (rootOperatorFamily .E6) e6AdjData_valid γ : k) * c) := by
  rw [yPar, xPar_of_isRoot hγ]
  rfl

private theorem zl_e6Isogeny_xm_coe_eltUnit [Finite k] {γ : Fin (Tag.rank .E6) → ℤ}
    (hγ : IsRoot .E6 γ) (c : k) :
    ((e6Isogeny k (e6Data_valid.xm k γ c) : ↥(adjointGroup .E6 k)) : ModGL .E6 k) =
      (rootOperatorFamily .E6).eltUnit k ⟨γ, hγ⟩
        ((relSignOr (rootOperatorFamily .E6) e6AdjData_valid γ : k) * c) := by
  rw [e6Isogeny_xm k hγ c]
  exact zl_yPar_coe_eltUnit hγ c

private theorem zl_e6_gen_compat [Finite k] [Finite E] (ι : k →+* E)
    {γ : Fin (Tag.rank .E6) → ℤ} (hγ : IsRoot .E6 γ) (c : k) :
    ((e6Isogeny E (scBase ι (e6Data_valid.xm k γ c)) : ↥(adjointGroup .E6 E)) : ModGL .E6 E) =
      baseChangeGL (τ := Tag.E6) ι
        ((e6Isogeny k (e6Data_valid.xm k γ c) : ↥(adjointGroup .E6 k)) : ModGL .E6 k) := by
  rw [scBase_xm, zl_e6Isogeny_xm_coe_eltUnit hγ (ι c), zl_e6Isogeny_xm_coe_eltUnit hγ c,
    zl_baseChangeGL_eltUnit, map_mul, map_intCast]

theorem scBase_isogeny [Finite k] [Finite E] (ι : k →+* E) (u : ↥(e6Data_valid.minGroup k)) :
    ((e6Isogeny E (scBase ι u) : ↥(adjointGroup Tag.E6 E)) : ModGL Tag.E6 E) =
      baseChangeGL ι ((e6Isogeny k u : ↥(adjointGroup Tag.E6 k)) : ModGL Tag.E6 k) := by
  let ψ₁ : ↥(e6Data_valid.minGroup k) →* ModGL Tag.E6 E :=
    (adjointGroup Tag.E6 E).subtype.comp ((e6Isogeny E).comp (scBase ι))
  let ψ₂ : ↥(e6Data_valid.minGroup k) →* ModGL Tag.E6 E :=
    (baseChangeGL (τ := Tag.E6) ι).comp ((adjointGroup Tag.E6 k).subtype.comp (e6Isogeny k))
  have hψ : ψ₁ = ψ₂ :=
    zl_minGroup_hom_eq_of_gens e6Data_valid ψ₁ ψ₂ fun γ hγ c => zl_e6_gen_compat ι hγ c
  exact congrArg (fun ψ => ψ u) hψ

end EntrywiseBaseChange

end CFSG.StandardType.E6Dep.ZL

end
