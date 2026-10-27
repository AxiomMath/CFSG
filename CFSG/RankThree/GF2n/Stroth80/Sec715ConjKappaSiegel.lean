module

public import CFSG.RankThree.GF2n.Stroth80.Sec715ConjKappaAlg
public import CFSG.RankThree.GF2n.Stroth80.Sec5OmegaPoints
public import CFSG.RankThree.GF2n.Stroth80.Sec5OmegaSingular
public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsCentre
public import CFSG.RankThree.GF2n.Stroth80.Sec7Transport

public section

namespace CFSG.RankThree.GF2n.Stroth80.S715K

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.LieType.Universal.Spin
open scoped Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal] {hc : Ctx M Q Z B} {n : ℕ} {K : Type} [Field K] [Finite K]
  {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} {ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)}
  {b : M₀.E}

theorem exists_sectionIso (hS : IsTensorSetup hc n M₀ ρ b) (t : G)
    [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    (e : ↥(hc.VtSub hS.model t) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) :
    ∃ ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
        Multiplicative (Fin 4 ⊕ Fin 4 → K),
      ∀ (v : ↥(Vt M (LB M Q B) B Z t)) (h : M₀.π v ∈ hc.VtSub hS.model t),
        Multiplicative.toAdd (ψ (QuotientGroup.mk v)) = e ⟨M₀.π v, h⟩ := by
  classical
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hπV : ∀ v : ↥(Vt M (LB M Q B) B Z t), M₀.π v ∈ hc.VtSub hS.model t := fun v =>
    (hc.mem_VtSub hS.model t).mpr (M₀.pi_mem_img v.2 (hVQ v.2))
  let κ : ↥(Vt M (LB M Q B) B Z t) →* Multiplicative (Fin 4 ⊕ Fin 4 → K) :=
    { toFun := fun v => Multiplicative.ofAdd (e ⟨M₀.π v, hπV v⟩)
      map_one' := by
        apply congrArg Multiplicative.ofAdd
        rw [← e.map_zero]
        exact congrArg e (Subtype.ext M₀.pi_one)
      map_mul' := fun x y => by
        show Multiplicative.ofAdd (e ⟨M₀.π ((x * y : ↥(Vt M (LB M Q B) B Z t)) : G),
            hπV (x * y)⟩) =
          Multiplicative.ofAdd (e ⟨M₀.π x, hπV x⟩) * Multiplicative.ofAdd (e ⟨M₀.π y, hπV y⟩)
        rw [← ofAdd_add, ← e.map_add]
        exact congrArg (fun w => Multiplicative.ofAdd (e w))
          (Subtype.ext (M₀.π_mul x (hVQ x.2) y (hVQ y.2))) }
  have hκsurj : Function.Surjective κ := by
    intro a
    obtain ⟨x, hxV, -, hx⟩ := M₀.mem_img.mp
      ((hc.mem_VtSub hS.model t).mp (e.symm (Multiplicative.toAdd a)).2)
    refine ⟨⟨x, hxV⟩, ?_⟩
    show Multiplicative.ofAdd (e ⟨M₀.π x, hπV ⟨x, hxV⟩⟩) = a
    have : (⟨M₀.π x, hπV ⟨x, hxV⟩⟩ : ↥(hc.VtSub hS.model t)) =
        e.symm (Multiplicative.toAdd a) := Subtype.ext hx
    rw [this, LinearEquiv.apply_symm_apply]
    rfl
  have hker : κ.ker = Z.subgroupOf (Vt M (LB M Q B) B Z t) := by
    ext v
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← M₀.π_ker _ (hVQ v.2)]
    constructor
    · intro h
      have h1 : e ⟨M₀.π v, hπV v⟩ = 0 := Multiplicative.ofAdd.injective h
      rw [LinearEquiv.map_eq_zero_iff] at h1
      exact congrArg Subtype.val h1
    · intro h
      apply congrArg Multiplicative.ofAdd
      rw [← e.map_zero]
      exact congrArg e (Subtype.ext h)
  let ψ := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective κ hκsurj)
  exact ⟨ψ, fun v h => rfl⟩

theorem exists_point_LB (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (hS : IsTensorSetup hc n M₀ ρ b) {t : G} (hs : Sec7Hyp hc n t)
    (φ₈ : ↥(bar M Q (Rt M (LB M Q B) t)) →* GL (Fin 4 ⊕ Fin 4) K)
    (hφr : φ₈.range = StatedOmega (StatedQuadPlus 4 K))
    (hφk : ∀ x, φ₈ x = 1 ↔ (x : Mbar M Q) ∈ bar M Q (hc.CN t))
    (e : ↥(hc.VtSub hS.model t) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K))
    (he : ∀ (x : ↥(bar M Q (Rt M (LB M Q B) t))) (w : ↥(hc.VtSub hS.model t)),
      e ⟨(ρ (x : Mbar M Q)).toAdd w, hc.act_mem_VtSub hS hs.toSec5.mem _ x.2 _ w.2⟩ =
        (φ₈ x : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ e w) :
    ∃ u : Fin 4 ⊕ Fin 4 → K, u ≠ 0 ∧ quadPlus 4 K u = 0 ∧
      ∀ x : ↥(bar M Q (Rt M (LB M Q B) t)), (x : Mbar M Q) ∈ bar M Q (LB M Q B) →
        φ₈ x ∈ LomGLPlus (by norm_num : 3 ≤ 4) u := by
  classical
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hRM : Rt M (LB M Q B) t ≤ M := hc.Rt_le_M t
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hQN : Q ≤ hc.CN t := hc.Q_le_CN' ht
  haveI : (Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (fun v hv =>
      hc.hyp.Z_normal.2 (hc.hyp.Q_normal.1 (hVQ hv)))
  let f₀ : ↥(Rt M (LB M Q B) t) →* Mbar M Q :=
    (QuotientGroup.mk' (Q.subgroupOf M)).comp (Subgroup.inclusion hRM)
  have hf₀ : ∀ r : ↥(Rt M (LB M Q B) t),
      f₀ r = QuotientGroup.mk' (Q.subgroupOf M) ⟨(r : G), hRM r.2⟩ := fun r => rfl
  have hmem : ∀ r : ↥(Rt M (LB M Q B) t), f₀ r ∈ bar M Q (Rt M (LB M Q B) t) := fun r =>
    Subgroup.mem_map.mpr ⟨⟨(r : G), hRM r.2⟩, Subgroup.mem_subgroupOf.mpr r.2, rfl⟩
  let f : ↥(Rt M (LB M Q B) t) →* ↥(bar M Q (Rt M (LB M Q B) t)) := f₀.codRestrict _ hmem
  have hfsurj : Function.Surjective f := by
    intro y
    obtain ⟨r, hr, hry⟩ := Subgroup.mem_map.mp y.2
    exact ⟨⟨(r : G), Subgroup.mem_subgroupOf.mp hr⟩, Subtype.ext hry⟩
  let φ' : ↥(Rt M (LB M Q B) t) →* GL (Fin 4 ⊕ Fin 4) K := φ₈.comp f
  have hφ'r : φ'.range = StatedOmega (StatedQuadPlus 4 K) := by
    rw [← hφr]
    ext g
    constructor
    · rintro ⟨r, rfl⟩
      exact ⟨f r, rfl⟩
    · rintro ⟨x, rfl⟩
      obtain ⟨r, rfl⟩ := hfsurj x
      exact ⟨r, rfl⟩
  have hφ'k : φ'.ker = (hc.CN t).subgroupOf (Rt M (LB M Q B) t) := by
    ext r
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show φ₈ (f r) = 1 ↔ _
    rw [hφk]
    show f₀ r ∈ bar M Q (hc.CN t) ↔ _
    rw [hf₀, mk_mem_bar_iff_sec4 hQN]
  obtain ⟨ψ, hψ⟩ := exists_sectionIso hS t e
  have hπV : ∀ v : ↥(Vt M (LB M Q B) B Z t), M₀.π v ∈ hc.VtSub hS.model t := fun v =>
    (hc.mem_VtSub hS.model t).mpr (M₀.pi_mem_img v.2 (hVQ v.2))
  have hψ' : ∀ (s : ↥(Rt M (LB M Q B) t)) (v w : ↥(Vt M (LB M Q B) B Z t)),
      (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ' s : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ
          Multiplicative.toAdd (ψ (QuotientGroup.mk v)) := by
    intro s v w hw
    rw [hψ w (hπV w), hψ v (hπV v)]
    have hact : M₀.π w = (ρ ((f s : ↥(bar M Q (Rt M (LB M Q B) t))) : Mbar M Q)).toAdd
        (M₀.π v) := by
      rw [hw]
      exact hS.conj ⟨(s : G), hRM s.2⟩ v (hVQ v.2)
    have h1 : (⟨M₀.π w, hπV w⟩ : ↥(hc.VtSub hS.model t)) =
        ⟨(ρ ((f s : ↥(bar M Q (Rt M (LB M Q B) t))) : Mbar M Q)).toAdd
          ((⟨M₀.π v, hπV v⟩ : ↥(hc.VtSub hS.model t)) : M₀.E),
          hc.act_mem_VtSub hS ht _ (f s).2 _ (hπV v)⟩ := Subtype.ext hact
    rw [h1, he]
    rfl
  have hm : 3 ≤ 4 := by norm_num
  have h3 : 3 ≤ Module.finrank K (Fin 4 ⊕ Fin 4 → K) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    norm_num
  have hnatSO : SpNat hc t ∨ OmegaNat hc t := Or.inr hs.omegaNat
  obtain ⟨u, hQu, hu0, -, -, hL, -⟩ := hc.omega_points_core h34 hRoot hs.toSec5 hnatSO hS.card
    (ElemMatrixIso.plus hm) (nondegenerate_polarBilin_quadPlus 4 K) h3
    (addCommutantScalar_statedOmegaPlus hm) φ' hφ'r hφ'k ψ hψ'
    (hc.omega_singular h34 hRoot hs.toSec5 hnatSO hS.card (ElemMatrixIso.plus hm)
      (nondegenerate_polarBilin_quadPlus 4 K) h3 (addCommutantScalar_statedOmegaPlus hm)
      φ' hφ'r ψ hψ')
  rw [ElemMatrixIso.LomGL_plus hm] at hL
  refine ⟨u, hu0, hQu, fun x hx => ?_⟩
  obtain ⟨ℓ, hℓL, hℓx⟩ := S714.exists_of_mem_bar hx
  have hℓR : (ℓ : G) ∈ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht hℓL
  have hfx : f ⟨(ℓ : G), hℓR⟩ = x := Subtype.ext hℓx
  rw [← hL, ← hfx]
  exact Subgroup.mem_map.mpr ⟨⟨(ℓ : G), hℓR⟩, Subgroup.mem_subgroupOf.mpr hℓL, rfl⟩

theorem finrank_LB_le_two {u : Fin 4 ⊕ Fin 4 → K} (hu0 : u ≠ 0) (hQu : quadPlus 4 K u = 0)
    {g : GL (Fin 4 ⊕ Fin 4) K} (hg : g ∈ LomGLPlus (by norm_num : 3 ≤ 4) u) :
    Module.finrank K (LinearMap.range
      (Matrix.toLin' ((g : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) - 1))) ≤ 2 := by
  obtain ⟨-, -, hmove, -⟩ := (mem_LomGLPlus_iff (by norm_num : 3 ≤ 4) hQu hu0).mp hg
  refine finrank_range_le_two (Qf := quadPlus 4 K) (nondegenerate_polarBilin_quadPlus 4 K) hu0
    fun x hx => ?_
  obtain ⟨c, hc⟩ := hmove x hx
  refine ⟨c, ?_⟩
  rw [Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.one_mulVec, hc]

end CFSG.RankThree.GF2n.Stroth80.S715K
