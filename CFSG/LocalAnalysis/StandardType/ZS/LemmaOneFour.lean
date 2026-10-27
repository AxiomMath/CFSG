module

public import CFSG.LocalAnalysis.StandardType.ZS.TableDefs
import CFSG.LocalAnalysis.StandardType.ZS.Transvection
import CFSG.LocalAnalysis.StandardType.ZS.TransvectionTwo
import CFSG.LocalAnalysis.StandardType.ZS.LemmaOneTwo
import CFSG.LocalAnalysis.StandardType.ZS.Subquotient

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

private theorem transvection_pow_apply {t : U ≃ₗ[ZMod p] U} {u : U} {ψ : Module.Dual (ZMod p) U}
    (hψu : ψ u = 0) (htu : ∀ v, t v = v + ψ v • u) (n : ℕ) (v : U) :
    (t ^ n) v = v + (n * ψ v) • u := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', LinearEquiv.mul_apply, ih, htu]
    simp only [map_add, map_smul, hψu, smul_zero, add_zero]
    module

private theorem not_isTransvectionLin_of_finrank_le_one
    [Module.Finite (ZMod p) U]
    (h1 : Module.finrank (ZMod p) U ≤ 1)
    {t : U ≃ₗ[ZMod p] U} (ht : QTwoLin.IsTransvectionLin t) : False := by
  obtain ⟨u, ψ, hu, hψ, hψu, _⟩ := ht
  have hker : u ∈ LinearMap.ker ψ := by
    rw [LinearMap.mem_ker]
    exact hψu
  have hfin : Module.finrank (ZMod p) (LinearMap.ker ψ) + 1 = Module.finrank (ZMod p) U :=
    Module.Dual.finrank_ker_add_one_of_ne_zero hψ
  have h0 : Module.finrank (ZMod p) (LinearMap.ker ψ) = 0 := by omega
  have hbot : LinearMap.ker ψ = ⊥ := Submodule.finrank_eq_zero.mp h0
  rw [hbot] at hker
  exact hu (by simpa using hker)

private theorem neg_mem_of_transvection_mem_ge_three
    (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {J : Subgroup (U ≃ₗ[ZMod p] U)} (hJ : ReflGen p J)
    (hirr : ∀ W : Submodule (ZMod p) U, (∀ g ∈ J, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤)
    (ht : ∃ t ∈ J, QTwoLin.IsTransvectionLin t)
    (h3 : 3 ≤ Module.finrank (ZMod p) U) :
    (LinearEquiv.neg (ZMod p) : U ≃ₗ[ZMod p] U) ∈ J := by
  have hneg_sq : (LinearEquiv.neg (ZMod p) : U ≃ₗ[ZMod p] U) *
      (LinearEquiv.neg (ZMod p) : U ≃ₗ[ZMod p] U) = 1 := by
    ext v
    simp [LinearEquiv.neg]
  have hsq : (LinearEquiv.det (LinearEquiv.neg (ZMod p) : U ≃ₗ[ZMod p] U)) ^ 2 = 1 := by
    rw [pow_two, ← map_mul, hneg_sq, map_one]
  have hsq' :
      ((LinearEquiv.det (LinearEquiv.neg (ZMod p) : U ≃ₗ[ZMod p] U) : ZMod p)) ^ 2 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hsq, Units.val_one]
  have hdet : LinearEquiv.det (LinearEquiv.neg (ZMod p) : U ≃ₗ[ZMod p] U) = 1 ∨
      LinearEquiv.det (LinearEquiv.neg (ZMod p) : U ≃ₗ[ZMod p] U) = -1 := by
    rcases sq_eq_one_iff.mp hsq' with h | h
    · exact Or.inl (Units.ext h)
    · exact Or.inr (Units.ext h)
  exact (slpm_of_transvection hp h3 hJ hirr ht _).mpr hdet

theorem neg_mem_of_transvection_mem (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {J : Subgroup (U ≃ₗ[ZMod p] U)} (hJ : ReflGen p J)
    (hirr : ∀ W : Submodule (ZMod p) U, (∀ g ∈ J, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤)
    (ht : ∃ t ∈ J, QTwoLin.IsTransvectionLin t) :
    (LinearEquiv.neg (ZMod p) : U ≃ₗ[ZMod p] U) ∈ J := by
  by_cases h1 : Module.finrank (ZMod p) U ≤ 1
  · exfalso
    obtain ⟨t, _, htT⟩ := ht
    exact not_isTransvectionLin_of_finrank_le_one h1 htT
  · push Not at h1
    by_cases h2 : Module.finrank (ZMod p) U = 2
    · exact neg_mem_of_transvection_mem_of_finrank_eq_two h2 hirr ht
    · have h3 : 3 ≤ Module.finrank (ZMod p) U := by omega
      exact neg_mem_of_transvection_mem_ge_three hp hJ hirr ht h3

private theorem apply_eq_neg_of_subquotHom_eq_neg [Module.Finite (ZMod p) U]
    {V : Submodule (ZMod p) U} {F : Subgroup (U ≃ₗ[ZMod p] U)}
    (h₁ : ∀ g ∈ F, (⊥ : Submodule (ZMod p) U).map (g : U →ₗ[ZMod p] U) = ⊥)
    (h₂ : ∀ g ∈ F, V.map (g : U →ₗ[ZMod p] U) = V)
    {z : F} (hz : subquotHom F ⊥ V h₁ h₂ z =
      (LinearEquiv.neg (ZMod p) : (Subquot ⊥ V) ≃ₗ[ZMod p] (Subquot ⊥ V))) :
    ∀ v ∈ V, (z : U ≃ₗ[ZMod p] U) v = -v := by
  intro v hv
  have key := LinearEquiv.congr_fun hz (Submodule.Quotient.mk (⟨v, hv⟩ : V))
  change subquotEquiv ⊥ V (z : U ≃ₗ[ZMod p] U) (h₁ z z.2) (h₂ z z.2)
    (Submodule.Quotient.mk (⟨v, hv⟩ : V)) = _ at key
  rw [subquotEquiv_mk, LinearEquiv.neg_apply, ← Submodule.Quotient.mk_neg] at key
  have hmem : ((z : U ≃ₗ[ZMod p] U) v + v) ∈ (⊥ : Submodule (ZMod p) U) := by
    have h := (Submodule.Quotient.eq ((⊥ : Submodule (ZMod p) U).comap V.subtype)).mp key
    rw [Submodule.mem_comap, Submodule.mem_bot] at h
    have h2 : (z : U ≃ₗ[ZMod p] U) v + v = 0 := by
      simpa [sub_eq_add_neg, neg_neg] using h
    exact h2
  rw [Submodule.mem_bot] at hmem
  exact eq_neg_of_add_eq_zero_left hmem

private theorem inf_commutatorSpace_ker_sub_one_eq_bot (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {F : Subgroup (U ≃ₗ[ZMod p] U)} {z : U ≃ₗ[ZMod p] U}
    (hzneg : ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace F, z v = -v) :
    HardMathSupport.Kantor79.commutatorSpace F ⊓
      LinearMap.ker ((z : U →ₗ[ZMod p] U) - 1) = ⊥ := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  refine (Submodule.eq_bot_iff _).mpr fun w hw => ?_
  have hneg : z w = -w := hzneg w hw.1
  have hfix : z w = w := by
    have h := hw.2
    change ((z : U →ₗ[ZMod p] U) - 1) w = 0 at h
    simpa [LinearMap.sub_apply, sub_eq_zero] using h
  rw [hneg] at hfix
  have hw2 : (2 : ZMod p) • w = 0 := by
    rw [two_smul]
    nth_rewrite 2 [← hfix]
    rw [add_neg_cancel]
  exact (smul_eq_zero.mp hw2).resolve_left h2

private theorem sup_centralizerSpace_eq_top_of_neg_mem
    (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {F : Subgroup (U ≃ₗ[ZMod p] U)} {z : U ≃ₗ[ZMod p] U} (hzF : z ∈ F)
    (hz2 : z * z = 1) (hzcent : ∀ f ∈ F, z * f = f * z)
    (hzneg : ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace F, z v = -v) :
    HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F = ⊤ := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hker := inf_commutatorSpace_ker_sub_one_eq_bot hp hzneg
  rw [Submodule.eq_top_iff']
  intro v
  have hv : v = (2 : ZMod p)⁻¹ • (v - z v) + (2 : ZMod p)⁻¹ • (v + z v) := by
    rw [← smul_add]
    have hsum : (v - z v) + (v + z v) = (2 : ZMod p) • v := by
      rw [show (2 : ZMod p) • v = v + v by rw [two_smul]]
      abel
    rw [hsum]
    exact (inv_smul_smul₀ h2 v).symm
  rw [hv]
  refine Submodule.add_mem_sup ?_ ?_
  · apply Submodule.smul_mem
    have h : (z : U ≃ₗ[ZMod p] U) v - v ∈ HardMathSupport.Kantor79.commutatorSpace F :=
      Submodule.subset_span (show (z : U ≃ₗ[ZMod p] U) v - v ∈
        {w : U | ∃ h ∈ F, ∃ v : U, w = h v - v} from ⟨z, hzF, v, rfl⟩)
    simpa using Submodule.neg_mem _ h
  · apply Submodule.smul_mem
    rw [mem_centralizerSpace]
    intro f hf
    have hzw : (z : U →ₗ[ZMod p] U) (v + z v) = v + z v := by
      have hz2v : (z : U →ₗ[ZMod p] U) (z v) = v := by
        simpa [LinearEquiv.mul_apply] using congrArg (fun e => e v) hz2
      rw [map_add, hz2v]
      exact add_comm _ _
    have hmem : f (v + z v) - (v + z v) ∈
        HardMathSupport.Kantor79.commutatorSpace F ⊓ LinearMap.ker ((z : U →ₗ[ZMod p] U) - 1) := by
      refine ⟨Submodule.subset_span (show f (v + z v) - (v + z v) ∈
        {w : U | ∃ h ∈ F, ∃ v : U, w = h v - v} from ⟨f, hf, v + z v, rfl⟩),
        LinearMap.mem_ker.mpr ?_⟩
      rw [LinearMap.sub_apply, sub_eq_zero]
      change (z : U →ₗ[ZMod p] U) (f (v + z v) - (v + z v)) = f (v + z v) - (v + z v)
      rw [map_sub]
      have hcomm : (z : U →ₗ[ZMod p] U) (f (v + z v)) =
          f ((z : U →ₗ[ZMod p] U) (v + z v)) := by
        simpa [LinearEquiv.mul_apply] using congrArg (fun e => e (v + z v)) (hzcent f hf)
      rw [hcomm, hzw]
    rw [hker] at hmem
    have h0 : f (v + z v) - (v + z v) = 0 := by simpa using hmem
    exact sub_eq_zero.mp h0

private theorem subquotHom_injective_of_irredOnSection (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {F : Subgroup (U ≃ₗ[ZMod p] U)} (hF : IsRGroup p F)
    (hirr : IrredOnSection F ⊥ (HardMathSupport.Kantor79.commutatorSpace F))
    (h₁ : ∀ g ∈ F, (⊥ : Submodule (ZMod p) U).map (g : U →ₗ[ZMod p] U) = ⊥)
    (h₂ : ∀ g ∈ F, (HardMathSupport.Kantor79.commutatorSpace F).map (g : U →ₗ[ZMod p] U) =
      HardMathSupport.Kantor79.commutatorSpace F) :
    Function.Injective (subquotHom F ⊥ (HardMathSupport.Kantor79.commutatorSpace F) h₁ h₂) := by
  intro x y hxy
  have h1 : subquotHom F ⊥ (HardMathSupport.Kantor79.commutatorSpace F) h₁ h₂ (x * y⁻¹) = 1 := by
    rw [map_mul, map_inv, hxy, mul_inv_cancel]
  have hfix : ((x * y⁻¹ : F) : U ≃ₗ[ZMod p] U) ∈
      fixingSubgroup (U ≃ₗ[ZMod p] U)
        (HardMathSupport.Kantor79.commutatorSpace F : Set U) := by
    rw [mem_fixingSubgroup_iff]
    intro v hv
    have h3 := (subquotEquiv_eq_one_iff (h₁ (x * y⁻¹) (x * y⁻¹).2)
      (h₂ (x * y⁻¹) (x * y⁻¹).2)).mp h1 v hv
    simpa [sub_eq_zero] using h3
  have hmem : ((x * y⁻¹ : F) : U ≃ₗ[ZMod p] U) ∈
      F ⊓ fixingSubgroup (U ≃ₗ[ZMod p] U)
        (HardMathSupport.Kantor79.commutatorSpace F : Set U) :=
    ⟨(x * y⁻¹).2, hfix⟩
  have hbot := fixing_commutatorSpace_eq_bot hp hF
    (commutatorSpace_inf_centralizerSpace_eq_bot hp hF.1 hirr)
  have hz : ((x * y⁻¹ : F) : U ≃ₗ[ZMod p] U) = 1 := by
    have := hmem
    rw [hbot] at this
    exact Subgroup.mem_bot.mp this
  exact mul_inv_eq_one.mp (Subtype.ext hz)

private theorem reflGen_range_subquotHom (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {F : Subgroup (U ≃ₗ[ZMod p] U)} (hF : ZS.ReflGen p F)
    (h₁ : ∀ g ∈ F, (⊥ : Submodule (ZMod p) U).map (g : U →ₗ[ZMod p] U) = ⊥)
    (h₂ : ∀ g ∈ F, (HardMathSupport.Kantor79.commutatorSpace F).map (g : U →ₗ[ZMod p] U) =
      HardMathSupport.Kantor79.commutatorSpace F) :
    ZS.ReflGen p (subquotHom F ⊥ (HardMathSupport.Kantor79.commutatorSpace F) h₁ h₂).range := by
  let ρ := subquotHom F ⊥ (HardMathSupport.Kantor79.commutatorSpace F) h₁ h₂
  let S : Set ((Subquot ⊥ (HardMathSupport.Kantor79.commutatorSpace F)) ≃ₗ[ZMod p]
      (Subquot ⊥ (HardMathSupport.Kantor79.commutatorSpace F))) :=
    {t | t ∈ ρ.range ∧ ZS.IsRefl p t}
  let K : Subgroup (U ≃ₗ[ZMod p] U) := ((Subgroup.closure S).comap ρ).map F.subtype
  have hR : {t : U ≃ₗ[ZMod p] U | t ∈ F ∧ ZS.IsRefl p t} ⊆ K := by
    rintro r ⟨hrF, hrRefl⟩
    have hrS : ρ ⟨r, hrF⟩ ∈ S := by
      refine ⟨⟨⟨r, hrF⟩, rfl⟩, ?_⟩
      exact isRefl_subquotHom hp h₁ h₂
        (fun g hg w hw => by rw [show w = 0 from by simpa using hw, map_zero])
        (fun g hg v => Submodule.subset_span ⟨g, hg, v, rfl⟩) hrRefl
    exact Subgroup.mem_map_of_mem F.subtype
      (Subgroup.mem_comap.mpr (Subgroup.subset_closure hrS))
  have hFK : F ≤ K := hF.le.trans ((Subgroup.closure_le K).2 hR)
  rw [ZS.ReflGen]
  refine le_antisymm ?_ ?_
  · rintro s ⟨f, rfl⟩
    have hfK : (f : U ≃ₗ[ZMod p] U) ∈ K := hFK f.2
    obtain ⟨f', hf', hff'⟩ := Subgroup.mem_map.mp hfK
    have hf'' := Subgroup.mem_comap.mp hf'
    rwa [Subtype.ext hff'] at hf''
  · rw [Subgroup.closure_le]
    rintro t ⟨ht, _⟩
    exact ht

private theorem irred_range_subquotHom [Module.Finite (ZMod p) U]
    {F : Subgroup (U ≃ₗ[ZMod p] U)}
    (hirr : IrredOnSection F ⊥ (HardMathSupport.Kantor79.commutatorSpace F))
    (h₁ : ∀ g ∈ F, (⊥ : Submodule (ZMod p) U).map (g : U →ₗ[ZMod p] U) = ⊥)
    (h₂ : ∀ g ∈ F, (HardMathSupport.Kantor79.commutatorSpace F).map (g : U →ₗ[ZMod p] U) =
      HardMathSupport.Kantor79.commutatorSpace F) :
    ∀ W : Submodule (ZMod p) (Subquot ⊥ (HardMathSupport.Kantor79.commutatorSpace F)),
      (∀ g ∈ (subquotHom F ⊥ (HardMathSupport.Kantor79.commutatorSpace F) h₁ h₂).range,
        ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤ := by
  intro W hW
  let V := HardMathSupport.Kantor79.commutatorSpace F
  let q : V →ₗ[ZMod p] Subquot ⊥ V := Submodule.mkQ _
  let W' : Submodule (ZMod p) U := (W.comap q).map V.subtype
  have hW'le : W' ≤ V := Submodule.map_subtype_le _ _
  have hW'inv : ∀ f ∈ F, ∀ w ∈ W', f w ∈ W' := by
    intro f hf w hw
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hw
    have hfv : (f : U →ₗ[ZMod p] U) (v : U) ∈ V := by
      have hmem := Submodule.mem_map_of_mem (f := (f : U →ₗ[ZMod p] U)) (v : V).2
      rwa [h₂ f hf] at hmem
    let fv : V := ⟨(f : U →ₗ[ZMod p] U) (v : U), hfv⟩
    have hq : (subquotHom F ⊥ V h₁ h₂ ⟨f, hf⟩) (q v) = q fv := by
      change subquotEquiv ⊥ V f (h₁ f hf) (h₂ f hf) (Submodule.Quotient.mk v) = _
      rw [subquotEquiv_mk]
      rfl
    refine Submodule.mem_map.mpr ⟨fv, ?_, rfl⟩
    rw [Submodule.mem_comap, ← hq]
    exact hW _ ⟨⟨f, hf⟩, rfl⟩ _ hv
  rcases hirr W' bot_le hW'le hW'inv with hbot | htop
  · left
    rw [Submodule.eq_bot_iff] at hbot ⊢
    intro w hw
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    have hmem : V.subtype v ∈ W' :=
      Submodule.mem_map.mpr ⟨v, Submodule.mem_comap.mpr hw, rfl⟩
    have hzero : V.subtype v = 0 := hbot (V.subtype v) hmem
    have hv0 : v = 0 := Subtype.ext hzero
    rw [hv0]
    rfl
  · right
    rw [Submodule.eq_top_iff']
    intro w
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    have hmem : V.subtype v ∈ W' := by rw [htop]; exact v.2
    obtain ⟨v', hv', hvv'⟩ := Submodule.mem_map.mp hmem
    have hveq : v' = v := Subtype.ext hvv'
    rw [hveq] at hv'
    exact Submodule.mem_comap.mp hv'

private theorem dLarge_range_subquotHom (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {F : Subgroup (U ≃ₗ[ZMod p] U)}
    (h₁ : ∀ g ∈ F, (⊥ : Submodule (ZMod p) U).map (g : U →ₗ[ZMod p] U) = ⊥)
    (h₂ : ∀ g ∈ F, (HardMathSupport.Kantor79.commutatorSpace F).map (g : U →ₗ[ZMod p] U) =
      HardMathSupport.Kantor79.commutatorSpace F)
    (hinj : Function.Injective (subquotHom F ⊥ (HardMathSupport.Kantor79.commutatorSpace F) h₁ h₂))
    (hd : ∃ x ∈ F, ∃ y ∈ F, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y)) :
    ∃ x ∈ (subquotHom F ⊥ (HardMathSupport.Kantor79.commutatorSpace F) h₁ h₂).range,
      ∃ y ∈ (subquotHom F ⊥ (HardMathSupport.Kantor79.commutatorSpace F) h₁ h₂).range,
        IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y) := by
  let ρ := subquotHom F ⊥ (HardMathSupport.Kantor79.commutatorSpace F) h₁ h₂
  obtain ⟨x, hxF, y, hyF, hxr, hyr, hxy⟩ := hd
  refine ⟨ρ ⟨x, hxF⟩, ⟨⟨x, hxF⟩, rfl⟩, ρ ⟨y, hyF⟩, ⟨⟨y, hyF⟩, rfl⟩, ?_, ?_, ?_⟩
  · exact isRefl_subquotHom hp h₁ h₂
      (fun g hg w hw => by rw [show w = 0 from by simpa using hw, map_zero])
      (fun g hg v => Submodule.subset_span ⟨g, hg, v, rfl⟩) hxr
  · exact isRefl_subquotHom hp h₁ h₂
      (fun g hg w hw => by rw [show w = 0 from by simpa using hw, map_zero])
      (fun g hg v => Submodule.subset_span ⟨g, hg, v, rfl⟩) hyr
  · rw [← map_mul, orderOf_injective ρ hinj (⟨x, hxF⟩ * ⟨y, hyF⟩)]
    simpa using hxy

private theorem finrank_subquot_eq [Module.Finite (ZMod p) U]
    {F : Subgroup (U ≃ₗ[ZMod p] U)} {l : ℕ}
    (hl : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace F) = l) :
    Module.finrank (ZMod p) (Subquot ⊥ (HardMathSupport.Kantor79.commutatorSpace F)) = l := by
  have : Module.Finite (ZMod p) (HardMathSupport.Kantor79.commutatorSpace F) :=
    Module.Finite.of_injective (HardMathSupport.Kantor79.commutatorSpace F).subtype
      (HardMathSupport.Kantor79.commutatorSpace F).subtype_injective
  have hq := Submodule.finrank_quotient_add_finrank
    ((⊥ : Submodule (ZMod p) U).comap (HardMathSupport.Kantor79.commutatorSpace F).subtype)
  have h0 : Module.finrank (ZMod p)
      ((⊥ : Submodule (ZMod p) U).comap
        (HardMathSupport.Kantor79.commutatorSpace F).subtype) = 0 := by
    rw [show (⊥ : Submodule (ZMod p) U).comap
        (HardMathSupport.Kantor79.commutatorSpace F).subtype = ⊥ from
      Submodule.ker_subtype _, finrank_bot]
  rw [h0, add_zero] at hq
  rw [hq]
  exact hl

private theorem sup_eq_top_of_neg_mem_range (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {F : Subgroup (U ≃ₗ[ZMod p] U)}
    (h₁ : ∀ g ∈ F, (⊥ : Submodule (ZMod p) U).map (g : U →ₗ[ZMod p] U) = ⊥)
    (h₂ : ∀ g ∈ F, (HardMathSupport.Kantor79.commutatorSpace F).map (g : U →ₗ[ZMod p] U) =
      HardMathSupport.Kantor79.commutatorSpace F)
    (hinj : Function.Injective (subquotHom F ⊥ (HardMathSupport.Kantor79.commutatorSpace F) h₁ h₂))
    (hneg : (LinearEquiv.neg (ZMod p) : (Subquot ⊥ (HardMathSupport.Kantor79.commutatorSpace F))
        ≃ₗ[ZMod p] (Subquot ⊥ (HardMathSupport.Kantor79.commutatorSpace F))) ∈
      (subquotHom F ⊥ (HardMathSupport.Kantor79.commutatorSpace F) h₁ h₂).range) :
    HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F = ⊤ := by
  let ρ := subquotHom F ⊥ (HardMathSupport.Kantor79.commutatorSpace F) h₁ h₂
  obtain ⟨z, hz⟩ := hneg
  have hzneg : ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace F, (z : U ≃ₗ[ZMod p] U) v = -v :=
    apply_eq_neg_of_subquotHom_eq_neg h₁ h₂ hz
  have hz2 : (z : U ≃ₗ[ZMod p] U) * z = 1 := by
    have h : ρ (z * z) = ρ 1 := by
      rw [map_mul, hz, map_one]
      ext w
      simp [LinearEquiv.mul_apply]
    exact congrArg Subtype.val (hinj h)
  have hzcent : ∀ f ∈ F, (z : U ≃ₗ[ZMod p] U) * f = f * z := by
    intro f hf
    have h : ρ ((z : F) * ⟨f, hf⟩) = ρ (⟨f, hf⟩ * z) := by
      rw [map_mul, map_mul, hz]
      ext w
      simp [LinearEquiv.mul_apply]
    exact congrArg Subtype.val (hinj h)
  exact sup_centralizerSpace_eq_top_of_neg_mem hp z.2 hz2 hzcent hzneg

private theorem card_eq_of_closure_range [Module.Finite (ZMod p) U] {l : ℕ}
    {F : Subgroup (U ≃ₗ[ZMod p] U)} {s : Finset ((Subquot ⊥
      (HardMathSupport.Kantor79.commutatorSpace F)) ≃ₗ[ZMod p]
      (Subquot ⊥ (HardMathSupport.Kantor79.commutatorSpace F)))}
    {y : s → F} (hy : ∀ i, IsRefl p (y i : U ≃ₗ[ZMod p] U))
    (hFgen : F = Subgroup.closure (Set.range (fun i : s => (y i : U ≃ₗ[ZMod p] U))))
    (hl : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace F) = l)
    (hscard : s.card ≤ l) : s.card = l := by
  have hle : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace F) ≤ s.card := by
    have h := HardMathSupport.Kantor79.finrank_commutatorSpace_le
      (fun i : s => (y i : U ≃ₗ[ZMod p] U)) (r := 1) (fun i => le_of_eq (hy i).2)
    rw [← hFgen] at h
    simpa using h
  exact le_antisymm hscard (hl ▸ hle)

private theorem splitSupport_of_closure_range (hp : p ≠ 2) [Module.Finite (ZMod p) U] {l : ℕ}
    {F : Subgroup (U ≃ₗ[ZMod p] U)}
    (hirr : IrredOnSection F ⊥ (HardMathSupport.Kantor79.commutatorSpace F))
    (hl : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace F) = l)
    (h₁ : ∀ g ∈ F, (⊥ : Submodule (ZMod p) U).map (g : U →ₗ[ZMod p] U) = ⊥)
    (h₂ : ∀ g ∈ F, (HardMathSupport.Kantor79.commutatorSpace F).map (g : U →ₗ[ZMod p] U) =
      HardMathSupport.Kantor79.commutatorSpace F)
    (hinj : Function.Injective (subquotHom F ⊥ (HardMathSupport.Kantor79.commutatorSpace F) h₁ h₂))
    (s : Finset ((Subquot ⊥ (HardMathSupport.Kantor79.commutatorSpace F)) ≃ₗ[ZMod p]
      (Subquot ⊥ (HardMathSupport.Kantor79.commutatorSpace F))))
    (hscard : s.card ≤ l)
    (hsrefl : ∀ x ∈ s, x ∈ (subquotHom F ⊥ (HardMathSupport.Kantor79.commutatorSpace F) h₁ h₂).range
      ∧ IsRefl p x)
    (hgen : (subquotHom F ⊥ (HardMathSupport.Kantor79.commutatorSpace F) h₁ h₂).range =
      Subgroup.closure (s : Set ((Subquot ⊥ (HardMathSupport.Kantor79.commutatorSpace F)) ≃ₗ[ZMod p]
        (Subquot ⊥ (HardMathSupport.Kantor79.commutatorSpace F))))) :
    SplitSupport F l := by
  let V := HardMathSupport.Kantor79.commutatorSpace F
  obtain ⟨y, hy, hFgen⟩ := exists_isRefl_closure_eq_of_injective hp h₁ h₂
    (fun g hg w hw => by rw [show w = 0 from by simpa using hw, map_zero])
    (fun g hg v => Submodule.subset_span ⟨g, hg, v, rfl⟩) hinj
    (fun i : s => (i : (Subquot ⊥ V) ≃ₗ[ZMod p] (Subquot ⊥ V)))
    (fun i => (hsrefl i i.2).2)
    (by rw [hgen]; congr 1; exact Subtype.range_coe.symm)
  have hcard := card_eq_of_closure_range (fun i => (hy i).1) hFgen hl hscard
  let e : s ≃ Fin l := Fintype.equivFinOfCardEq (by simpa using hcard)
  let x : Fin l → U ≃ₗ[ZMod p] U := fun j => (y (e.symm j) : U ≃ₗ[ZMod p] U)
  have hx : ∀ j, IsRefl p (x j) := fun j => (hy (e.symm j)).1
  have hrange : Set.range x = Set.range (fun i : s => (y i : U ≃ₗ[ZMod p] U)) := by
    ext z
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨e.symm j, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨e i, by simp [x]⟩
  have hdim : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace
      (Subgroup.closure (Set.range x))) = l := by
    rw [hrange, ← hFgen, hl]
  have hss := splitSupport_of_isRefl hp x hx hdim (by rwa [hrange, ← hFgen])
  rwa [hrange, ← hFgen] at hss

theorem splitSupport_of_irredOnSection (hp : p ≠ 2) [Module.Finite (ZMod p) U] {l : ℕ}
    (htab : l < Module.finrank (ZMod p) U → TFNegOrGen p l) {F : Subgroup (U ≃ₗ[ZMod p] U)}
    (hF : IsRGroup p F) (hirr : IrredOnSection F ⊥ (HardMathSupport.Kantor79.commutatorSpace F))
    (hl : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace F) = l)
    (hd : ∃ x ∈ F, ∃ y ∈ F, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y)) :
    SplitSupport F l := by
  refine ⟨?_, hl, hirr⟩
  by_cases hln : l = Module.finrank (ZMod p) U
  · have hVtop : HardMathSupport.Kantor79.commutatorSpace F = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [hl, hln]
    have hCbot : centralizerSpace F = ⊥ := by
      have h := commutatorSpace_inf_centralizerSpace_eq_bot hp hF.1 hirr
      rwa [hVtop, top_inf_eq] at h
    rw [hVtop, hCbot]
    exact ⟨disjoint_iff.mpr (by simp), codisjoint_iff.mpr (by simp)⟩
  · have hle : l ≤ Module.finrank (ZMod p) U := by
      rw [← hl]
      exact Submodule.finrank_le _
    have hlt : l < Module.finrank (ZMod p) U := lt_of_le_of_ne hle hln
    have htab' := htab hlt
    have h₁ : ∀ g ∈ F, (⊥ : Submodule (ZMod p) U).map (g : U →ₗ[ZMod p] U) = ⊥ :=
      fun g _ => by simp
    have h₂ : ∀ g ∈ F, (HardMathSupport.Kantor79.commutatorSpace F).map
        (g : U →ₗ[ZMod p] U) = HardMathSupport.Kantor79.commutatorSpace F :=
      fun g hg => map_commutatorSpace_of_mem_normalizer (Subgroup.le_normalizer hg)
    have hinj := subquotHom_injective_of_irredOnSection hp hF hirr h₁ h₂
    let ρ := subquotHom F ⊥ (HardMathSupport.Kantor79.commutatorSpace F) h₁ h₂
    let J : Subgroup ((Subquot ⊥ (HardMathSupport.Kantor79.commutatorSpace F)) ≃ₗ[ZMod p]
        (Subquot ⊥ (HardMathSupport.Kantor79.commutatorSpace F))) := ρ.range
    have hJrefl : ReflGen p J := reflGen_range_subquotHom hp hF.1 h₁ h₂
    have hJirr := irred_range_subquotHom hirr h₁ h₂
    have hJd := dLarge_range_subquotHom hp h₁ h₂ hinj hd
    have hJfin := finrank_subquot_eq hl
    have hinf : HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F = ⊥ :=
      commutatorSpace_inf_centralizerSpace_eq_bot hp hF.1 hirr
    have htop_of_neg : (LinearEquiv.neg (ZMod p) : (Subquot ⊥
        (HardMathSupport.Kantor79.commutatorSpace F)) ≃ₗ[ZMod p] (Subquot ⊥
        (HardMathSupport.Kantor79.commutatorSpace F))) ∈ J →
        HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F = ⊤ :=
      fun hneg => sup_eq_top_of_neg_mem_range hp h₁ h₂ hinj hneg
    by_cases htv : ∃ t ∈ J, QTwoLin.IsTransvectionLin t
    · exact ⟨disjoint_iff.mpr hinf, codisjoint_iff.mpr (htop_of_neg
        (neg_mem_of_transvection_mem hp hJrefl hJirr htv))⟩
    · have hJtf : QTwoLin.TransvectionFree J := fun t ht htrans => htv ⟨t, ht, htrans⟩
      rcases htab' (Subquot ⊥ (HardMathSupport.Kantor79.commutatorSpace F)) J hJfin hJrefl
        hJtf hJirr hJd with hneg | ⟨s, hscard, hsrefl, hgen⟩
      · exact ⟨disjoint_iff.mpr hinf, codisjoint_iff.mpr (htop_of_neg hneg)⟩
      · exact (splitSupport_of_closure_range hp hirr hl h₁ h₂ hinj s hscard hsrefl hgen).1
end CFSG.StandardType.ZS
