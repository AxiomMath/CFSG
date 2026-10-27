module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TwE6Conj
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneCompDefs
public import CFSG.LieType.Steinberg.TwistedE6.Clause0
public import CFSG.LieType.Steinberg.TwistedE6.Unipotent
public import CFSG.LieType.Steinberg.TwistedE6.Roots
public import CFSG.LieType.Steinberg.Exceptional.Fields
public import CFSG.LieType.Steinberg.CentralExt.Unipotent

public section

namespace CFSG.StandardType.LieKnownR2.Short

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Steinberg.Minuscule
  CFSG.Blueprint.Chevalley
open scoped commutatorElement

@[expose] def twE6Last : Fin (Tag.rank .F4) := ⟨3, by decide⟩

@[expose] noncomputable def twE6Rad
    {k : Type} [Field k] (θ : k →+* k) : Subgroup (fixedGroup k θ) :=
  ggSub (twistedDatum k θ) {γ | γ ∈ (twistedDatum k θ).roots ∧ 1 ≤ γ twE6Last}

@[expose] noncomputable def twE6Cen
    {k : Type} [Field k] (θ : k →+* k) : Subgroup (fixedGroup k θ) :=
  ggSub (twistedDatum k θ) {γ | γ ∈ (twistedDatum k θ).roots ∧ 2 ≤ γ twE6Last}

private theorem teRad_f4_level_le_two :
    ∀ v ∈ rootFinset Tag.F4, v twE6Last ≤ 2 := by decide +kernel

private theorem teRad_f4_level_ge_neg_two :
    ∀ v ∈ rootFinset Tag.F4, -2 ≤ v twE6Last := by decide +kernel

private theorem teRad_alpha_level : twE6Alpha twE6Last = 2 := by decide +kernel

private theorem teRad_level_smul_add {ι : Type} (i : ι) (a b : ℕ)
    (γ δ : ι → ℤ) :
    (a • γ + b • δ) i = (a : ℤ) * γ i + (b : ℤ) * δ i := by
  simp only [Pi.add_apply, Pi.smul_apply]
  rw [nsmul_eq_mul, nsmul_eq_mul]

private theorem teRad_level_neg {ι : Type} (i : ι) (γ : ι → ℤ) :
    (-γ) i = -γ i := rfl

private theorem teRad_level_smul {ι : Type} (i : ι) (n : ℕ) (γ : ι → ℤ) :
    (n • γ) i = (n : ℤ) * γ i := by
  rw [Pi.smul_apply, nsmul_eq_mul]

private abbrev teRad_last
    {k : Type} [Field k] (θ : k →+* k) : Fin (twistedDatum k θ).rank := twE6Last

private theorem teRad_level_le_two
    {k : Type} [Field k] (θ : k →+* k) {γ : Fin (twistedDatum k θ).rank → ℤ}
    (hγ : γ ∈ (twistedDatum k θ).roots) : γ (teRad_last θ) ≤ 2 := by
  have hγ' : IsRoot .F4 γ := isRoot_of_mem_twistedDatum_roots θ hγ
  have hmem : γ ∈ rootFinset Tag.F4 := mem_rootFinset.2 hγ'
  simpa [teRad_last] using teRad_f4_level_le_two γ hmem

private theorem teRad_level_ge_neg_two
    {k : Type} [Field k] (θ : k →+* k) {γ : Fin (twistedDatum k θ).rank → ℤ}
    (hγ : γ ∈ (twistedDatum k θ).roots) : -2 ≤ γ (teRad_last θ) := by
  have hγ' : IsRoot .F4 γ := isRoot_of_mem_twistedDatum_roots θ hγ
  have hmem : γ ∈ rootFinset Tag.F4 := mem_rootFinset.2 hγ'
  simpa [teRad_last] using teRad_f4_level_ge_neg_two γ hmem

private theorem teRad_two_smul_notMem
    {k : Type} [Field k] (θ : k →+* k) {γ : Fin (twistedDatum k θ).rank → ℤ}
    (hγ : γ ∈ (twistedDatum k θ).roots) : 2 • γ ∉ (twistedDatum k θ).roots :=
  two_smul_notMem_roots (twistedDatum k θ).isFiniteType
    (show (twistedDatum k θ).divisible = ∅ from rfl) hγ

private theorem teRad_eq_of_level_pos_of_not_linIndep
    {k : Type} [Field k] (θ : k →+* k) {δ γ : Fin (twistedDatum k θ).rank → ℤ}
    (hδ : δ ∈ (twistedDatum k θ).roots) (hγ : γ ∈ (twistedDatum k θ).roots)
    (hδl : 1 ≤ δ (teRad_last θ)) (hγl : 1 ≤ γ (teRad_last θ))
    (h : ¬ LinIndepPair δ γ) : δ = γ := by
  rcases OfCartan.proportional (twistedDatum k θ).isFiniteType hδ hγ h with
    h' | h' | h' | h' | h' | h'
  · exact h'
  · have hlev : δ (teRad_last θ) = -(γ (teRad_last θ)) := by
      rw [h', teRad_level_neg]
    omega
  · exact absurd (h' ▸ hδ) (teRad_two_smul_notMem θ hγ)
  · have hlev : δ (teRad_last θ) = -2 * (γ (teRad_last θ)) := by
      rw [h', teRad_level_neg, teRad_level_smul]
      ring
    omega
  · exact absurd (h' ▸ hγ) (teRad_two_smul_notMem θ hδ)
  · have hlev : γ (teRad_last θ) = -2 * (δ (teRad_last θ)) := by
      rw [h', teRad_level_neg, teRad_level_smul]
      ring
    omega

private theorem teRad_commute_of_level_sum
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)
    {δ γ : Fin (twistedDatum k θ).rank → ℤ}
    (hδ : δ ∈ (twistedDatum k θ).roots) (hγ : γ ∈ (twistedDatum k θ).roots)
    (hsum : 3 ≤ δ (teRad_last θ) + γ (teRad_last θ)) :
    ∀ x ∈ (twistedDatum k θ).rootGroup δ, ∀ y ∈ (twistedDatum k θ).rootGroup γ,
      Commute x y := by
  intro x hx y hy
  have hδlo := teRad_level_ge_neg_two θ hδ
  have hγhi := teRad_level_le_two θ hγ
  have hδl : 1 ≤ δ (teRad_last θ) := by omega
  have hγlo := teRad_level_ge_neg_two θ hγ
  have hδhi := teRad_level_le_two θ hδ
  have hγl : 1 ≤ γ (teRad_last θ) := by omega
  by_cases heq : δ = γ
  · have hx' : x ∈ (twistedDatum k θ).rootGroup γ := by rwa [heq] at hx
    have hmem : ⁅x, y⁆ ∈
        ⁅(twistedDatum k θ).rootGroup γ, (twistedDatum k θ).rootGroup γ⁆ :=
      Subgroup.commutator_mem_commutator hx' hy
    rw [(twistedDatum_rootGroupCommutators θ).commutator_eq_bot γ hγ
      (teRad_two_smul_notMem θ hγ), Subgroup.mem_bot] at hmem
    exact commutatorElement_eq_one_iff_commute.1 hmem
  · have hli : LinIndepPair δ γ := by
      by_contra h
      exact heq (teRad_eq_of_level_pos_of_not_linIndep θ hδ hγ hδl hγl h)
    have hc := (twistedDatum_steinbergExtras θ hθ).commutator_mem δ hδ γ hγ hli x hx y hy
    have hempty : openCone (twistedDatum k θ).roots δ γ = ∅ := by
      refine Set.eq_empty_of_forall_notMem ?_
      rintro ε ⟨hε, a, b, ha, hb, rfl⟩
      have hlevel : (a • δ + b • γ) (teRad_last θ) =
          (a : ℤ) * (δ (teRad_last θ)) + (b : ℤ) * (γ (teRad_last θ)) :=
        teRad_level_smul_add (teRad_last θ) a b δ γ
      have h3 : 3 ≤ (a • δ + b • γ) (teRad_last θ) := by
        rw [hlevel]
        have ha1 : (1 : ℤ) ≤ a := by exact_mod_cast ha
        have hb1 : (1 : ℤ) ≤ b := by exact_mod_cast hb
        nlinarith
      have := teRad_level_le_two θ hε
      omega
    rw [hempty] at hc
    simp only [Set.mem_empty_iff_false, iSup_false, iSup_bot, Subgroup.mem_bot] at hc
    exact commutatorElement_eq_one_iff_commute.1 hc

private theorem teRad_cen_le_centralizer_rad
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) :
    twE6Cen θ ≤ Subgroup.centralizer ((twE6Rad θ : Subgroup _) : Set (fixedGroup k θ)) := by
  refine iSup₂_le fun δ hδ x hx => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hy' : y ∈ ⨆ γ ∈ {γ | γ ∈ (twistedDatum k θ).roots ∧ 1 ≤ γ twE6Last},
      (twistedDatum k θ).rootGroup γ := hy
  have h := CFSG.LieType.TitsSimplicity.iSup₂_induction (C := fun y => Commute x y) hy'
    (fun γ hγ y hy => by
      have hγlo : 1 ≤ γ (teRad_last θ) := hγ.2
      have hsum : 3 ≤ δ (teRad_last θ) + γ (teRad_last θ) := by
        have hδlo : 2 ≤ δ (teRad_last θ) := hδ.2
        omega
      exact teRad_commute_of_level_sum θ hθ hδ.1 hγ.1 hsum x hx y hy)
    (Commute.one_right x)
    (fun y z hy hz => hy.mul_right hz)
  exact h.eq.symm

private theorem teRad_commutator_mem_cen
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)
    {δ γ : Fin (twistedDatum k θ).rank → ℤ}
    (hδ : δ ∈ (twistedDatum k θ).roots) (hγ : γ ∈ (twistedDatum k θ).roots)
    (hδl : 1 ≤ δ (teRad_last θ)) (hγl : 1 ≤ γ (teRad_last θ)) :
    ∀ x ∈ (twistedDatum k θ).rootGroup δ, ∀ y ∈ (twistedDatum k θ).rootGroup γ,
      ⁅x, y⁆ ∈ twE6Cen θ := by
  intro x hx y hy
  by_cases heq : δ = γ
  · have hx' : x ∈ (twistedDatum k θ).rootGroup γ := by rwa [heq] at hx
    have hmem : ⁅x, y⁆ ∈
        ⁅(twistedDatum k θ).rootGroup γ, (twistedDatum k θ).rootGroup γ⁆ :=
      Subgroup.commutator_mem_commutator hx' hy
    rw [(twistedDatum_rootGroupCommutators θ).commutator_eq_bot γ hγ
      (teRad_two_smul_notMem θ hγ), Subgroup.mem_bot] at hmem
    rw [hmem]
    exact one_mem _
  · have hli : LinIndepPair δ γ := by
      by_contra h
      exact heq (teRad_eq_of_level_pos_of_not_linIndep θ hδ hγ hδl hγl h)
    have hc := (twistedDatum_steinbergExtras θ hθ).commutator_mem δ hδ γ hγ hli x hx y hy
    have hle : ⨆ ε ∈ openCone (twistedDatum k θ).roots δ γ, (twistedDatum k θ).rootGroup ε ≤
        twE6Cen θ := by
      refine iSup₂_le fun ε hε => ?_
      obtain ⟨a, b, ha, hb, rfl⟩ := hε.2
      refine le_iSup₂_of_le (a • δ + b • γ) ⟨hε.1, ?_⟩ le_rfl
      change 2 ≤ (a • δ + b • γ) (teRad_last θ)
      rw [teRad_level_smul_add (teRad_last θ) a b δ γ]
      have ha1 : (1 : ℤ) ≤ a := by exact_mod_cast ha
      have hb1 : (1 : ℤ) ≤ b := by exact_mod_cast hb
      nlinarith
    exact hle hc

theorem isPGroup_two_twistedRootGroup
    {k : Type} [Field k] [CharP k 2] (θ : k →+* k)
    {γ : Fin (Tag.rank .F4) → ℤ} (hγ : γ ∈ (twistedDatum k θ).roots) :
    IsPGroup 2 ↥((twistedDatum k θ).rootGroup γ) := by
  rw [isPGroup_iff_pow_pow_eq_one]
  intro g
  refine ⟨1, ?_⟩
  rw [pow_one]
  apply Subtype.ext
  apply Subtype.ext
  change (g : e6Data_valid.minGroup k) ^ 2 = 1
  obtain ⟨α₀, hα₀, hp⟩ := exists_proj_eq (isRoot_of_mem_twistedDatum_roots θ hγ)
  by_cases hfix : rho α₀ = α₀
  · obtain ⟨c, hc, hg⟩ := (mem_twistedRootGroup_iff_of_fixed θ hα₀ hp hfix g).1 g.2
    rw [hg, pow_two, ← e6Data_valid.xm_add, CharTwo.add_self_eq_zero,
      e6Data_valid.xm_zero]
  · obtain ⟨c, hg⟩ := (mem_twistedRootGroup_iff_of_pair θ hα₀ hp hfix g).1 g.2
    rw [hg, pow_two]
    set x : e6Data_valid.minGroup k := e6Data_valid.xm k α₀ c with hx
    set y : e6Data_valid.minGroup k :=
      e6Data_valid.xm k (rho α₀) ((twistSign α₀ : k) * θ c) with hy
    have hx2 : x * x = 1 := by
      rw [hx, ← e6Data_valid.xm_add, CharTwo.add_self_eq_zero, e6Data_valid.xm_zero]
    have hy2 : y * y = 1 := by
      rw [hy, ← e6Data_valid.xm_add, CharTwo.add_self_eq_zero, e6Data_valid.xm_zero]
    have hcomm : Commute x y := by
      rw [hx, hy]
      exact commute_xm_rho hα₀ hfix c ((twistSign α₀ : k) * θ c)
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [hcomm.eq.symm]
      _ = x * x * (y * y) := by group
      _ = 1 := by rw [hx2, hy2, one_mul]

theorem isPGroup_two_twE6Rad
    {k : Type} [Field k] [CharP k 2] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) :
    IsPGroup 2 ↥(twE6Rad θ) := by
  have hX : ∀ γ ∈ (twistedDatum k θ).roots, IsPGroup 2
      ((twistedDatum k θ).rootGroup γ) :=
    fun γ hγ => isPGroup_two_twistedRootGroup θ hγ
  have h := isPGroup_iSup_posSet (twistedDatum_steinbergExtras θ hθ) hX
    (Pi.evalAddMonoidHom (fun _ => ℤ) (teRad_last θ))
  have hset : {γ | γ ∈ (twistedDatum k θ).roots ∧ 1 ≤ γ (teRad_last θ)} =
      posSet (twistedDatum k θ).roots
        (Pi.evalAddMonoidHom (fun _ => ℤ) (teRad_last θ)) := by
    ext γ
    rw [mem_posSet, Pi.evalAddMonoidHom_apply]
    exact and_congr_right fun _ => by
      constructor <;> intro h <;> omega
  have hEq : twE6Rad θ = ⨆ γ ∈ posSet (twistedDatum k θ).roots
      (Pi.evalAddMonoidHom (fun _ => ℤ) (teRad_last θ)),
      (twistedDatum k θ).rootGroup γ := by
    rw [twE6Rad, ggSub, hset]
  exact h.to_le (le_of_eq hEq)

theorem twE6Rad_le_centralizer_alpha
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) :
    twE6Rad θ ≤ Subgroup.centralizer (((twistedDatum k θ).rootGroup twE6Alpha : Subgroup _) :
      Set (fixedGroup k θ)) := by
  refine iSup₂_le fun δ hδ x hx => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hsum : 3 ≤ δ (teRad_last θ) + twE6Alpha (teRad_last θ) := by
    have hδl : 1 ≤ δ (teRad_last θ) := hδ.2
    have hα : twE6Alpha (teRad_last θ) = 2 := teRad_alpha_level
    omega
  exact (teRad_commute_of_level_sum θ hθ hδ.1 (twE6_alpha_mem_roots θ) hsum x hx y hy).eq.symm

theorem twE6_commutator_rad_le_cen
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) :
    ⁅twE6Rad θ, twE6Rad θ⁆ ≤ twE6Cen θ := by
  have hN : twE6Rad θ ≤ Subgroup.normalizer (twE6Cen θ : Set (fixedGroup k θ)) :=
    (Subgroup.le_centralizer_iff.mp (teRad_cen_le_centralizer_rad θ hθ)).trans
      (Subgroup.centralizer_le_normalizer _)
  rw [Subgroup.commutator_le]
  have hA : ∀ δ ∈ (twistedDatum k θ).roots, 1 ≤ δ twE6Last →
      ∀ x ∈ (twistedDatum k θ).rootGroup δ, ∀ y ∈ twE6Rad θ, ⁅x, y⁆ ∈ twE6Cen θ := by
    intro δ hδ hδl x hx y hy
    have hy' : y ∈ ⨆ γ ∈ {γ | γ ∈ (twistedDatum k θ).roots ∧ 1 ≤ γ twE6Last},
        (twistedDatum k θ).rootGroup γ := hy
    have h := CFSG.LieType.TitsSimplicity.iSup₂_induction
      (C := fun y => y ∈ twE6Rad θ ∧ ⁅x, y⁆ ∈ twE6Cen θ) hy'
      (fun γ hγ y hy => ⟨Subgroup.mem_iSup_of_mem γ (Subgroup.mem_iSup_of_mem hγ hy),
        teRad_commutator_mem_cen θ hθ hδ hγ.1 hδl hγ.2 x hx y hy⟩)
      ⟨one_mem _, by rw [commutatorElement_one_right]; exact one_mem _⟩
      (fun y z hy hz => ⟨mul_mem hy.1 hz.1, by
        have e : ⁅x, y * z⁆ = ⁅x, y⁆ * (y * ⁅x, z⁆ * y⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact mul_mem hy.2 ((Subgroup.mem_normalizer_iff.1 (hN hy.1) _).1 hz.2)⟩)
    exact h.2
  intro x hx y hy
  have hx' : x ∈ ⨆ γ ∈ {γ | γ ∈ (twistedDatum k θ).roots ∧ 1 ≤ γ twE6Last},
      (twistedDatum k θ).rootGroup γ := hx
  have h := CFSG.LieType.TitsSimplicity.iSup₂_induction
    (C := fun x => x ∈ twE6Rad θ ∧ ⁅x, y⁆ ∈ twE6Cen θ) hx'
    (fun δ hδ x hx => ⟨Subgroup.mem_iSup_of_mem δ (Subgroup.mem_iSup_of_mem hδ hx),
      hA δ hδ.1 hδ.2 x hx y hy⟩)
    ⟨one_mem _, by rw [commutatorElement_one_left]; exact one_mem _⟩
    (fun x x' hx hx' => ⟨mul_mem hx.1 hx'.1, by
      have e : ⁅x * x', y⁆ = x * ⁅x', y⁆ * x⁻¹ * ⁅x, y⁆ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact mul_mem ((Subgroup.mem_normalizer_iff.1 (hN hx.1) _).1 hx'.2) hx.2⟩)
  exact h.2

theorem twE6Cen_le_centralizer_rad
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) :
    twE6Cen θ ≤ Subgroup.centralizer ((twE6Rad θ : Subgroup _) : Set (fixedGroup k θ)) :=
  teRad_cen_le_centralizer_rad θ hθ

end CFSG.StandardType.LieKnownR2.Short
