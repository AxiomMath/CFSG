module

public import CFSG.RankThree.GF2n.Stroth80.Sec5NatScalars
public import CFSG.RankThree.GF2n.Stroth80.DictModel

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.RankThree.GF2n.Tim79
open Matrix

variable {G : Type} [Group G]

theorem exists_ringEquiv_natural {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {Kg K' : Type} [Field Kg] [Field K'] [Finite Kg] [Finite K']
    (hcard : Nat.card Kg = Nat.card K') {Q Z V R : Subgroup G} {γ : G → Kg}
    (M₀ : QuadModel Q Z Kg γ) (hVQ : V ≤ Q) {X : Subgroup (GL ι K')}
    (hX : AddCommutantScalar X) (hS : ∀ (c : Kg) (e : M₀.E), e ∈ M₀.img V → c • e ∈ M₀.img V)
    (hlin : ∀ r ∈ R, ∃ T : M₀.E →ₗ[Kg] M₀.E, ∀ x ∈ Q, M₀.π (r * x * r⁻¹) = T (M₀.π x))
    (φ : ↥R →* GL ι K') (hφ : φ.range = X) [(Z.subgroupOf V).Normal]
    (hVR : R ≤ Subgroup.normalizer (V : Set G))
    (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (ι → K'))
    (hψ : ∀ (s : ↥R) (v w : ↥V), (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix ι ι K') *ᵥ Multiplicative.toAdd (ψ (QuotientGroup.mk v))) :
    ∃ θ : Kg ≃+* K', ∀ (c : Kg) (v w : ↥V), M₀.π w = c • M₀.π v →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        θ c • Multiplicative.toAdd (ψ (QuotientGroup.mk v)) := by
  classical
  let A : Submodule Kg M₀.E :=
    { toAddSubmonoid := (M₀.img V).toAddSubmonoid
      smul_mem' := fun c e he => hS c e he }
  have hπV : ∀ v : ↥V, M₀.π v ∈ A := fun v => M₀.pi_mem_img v.2 (hVQ v.2)
  let κ : ↥V →* Multiplicative ↥A :=
    { toFun := fun v => Multiplicative.ofAdd ⟨M₀.π v, hπV v⟩
      map_one' := by
        apply congrArg Multiplicative.ofAdd
        exact Subtype.ext (QuadModel.pi_one M₀)
      map_mul' := fun x y => by
        apply congrArg Multiplicative.ofAdd
        exact Subtype.ext (M₀.π_mul x (hVQ x.2) y (hVQ y.2)) }
  have hκsurj : Function.Surjective κ := by
    intro a
    obtain ⟨x, hxV, hxQ, hx⟩ := a.toAdd.2
    exact ⟨⟨x, hxV⟩, by
      show Multiplicative.ofAdd (⟨M₀.π x, hπV ⟨x, hxV⟩⟩ : ↥A) = a
      apply congrArg Multiplicative.ofAdd
      exact Subtype.ext hx⟩
  have hker : κ.ker = Z.subgroupOf V := by
    ext v
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← M₀.π_ker _ (hVQ v.2)]
    constructor
    · intro h
      exact congrArg Subtype.val (Multiplicative.ofAdd.injective h)
    · intro h
      exact congrArg Multiplicative.ofAdd (Subtype.ext h)
  let e₁ : ↥V ⧸ κ.ker ≃* Multiplicative ↥A := QuotientGroup.quotientKerEquivOfSurjective κ hκsurj
  let e₂ : ↥V ⧸ Z.subgroupOf V ≃* ↥V ⧸ κ.ker := QuotientGroup.quotientMulEquivOfEq hker.symm
  let Ψm : Multiplicative ↥A ≃* Multiplicative (ι → K') :=
    e₁.symm.trans (e₂.symm.trans ψ)
  let Ψ : ↥A ≃+ (ι → K') := AddEquiv.toMultiplicative.symm Ψm
  have hΨ : ∀ v : ↥V, Ψ ⟨M₀.π v, hπV v⟩ = Multiplicative.toAdd (ψ (QuotientGroup.mk v)) := by
    intro v
    show Multiplicative.toAdd (Ψm (Multiplicative.ofAdd ⟨M₀.π v, hπV v⟩)) = _
    have h1 : e₁.symm (κ v) = QuotientGroup.mk v := by
      apply e₁.injective
      rw [MulEquiv.apply_symm_apply]
      rfl
    have h2 : e₂.symm (QuotientGroup.mk v) = QuotientGroup.mk v := rfl
    show Multiplicative.toAdd (ψ (e₂.symm (e₁.symm (κ v)))) = _
    rw [h1, h2]
  have hΨsurj : ∀ u : ι → K', ∃ v : ↥V, Ψ ⟨M₀.π v, hπV v⟩ = u := by
    intro u
    obtain ⟨q, hq⟩ := QuotientGroup.mk_surjective (ψ.symm (Multiplicative.ofAdd u))
    refine ⟨q, ?_⟩
    rw [hΨ, hq, MulEquiv.apply_symm_apply, toAdd_ofAdd]
  have hcomm : ∀ (c : Kg), ∀ B ∈ X, ∀ u : ι → K',
      Ψ (c • Ψ.symm ((B : Matrix ι ι K') *ᵥ u)) =
        (B : Matrix ι ι K') *ᵥ Ψ (c • Ψ.symm u) := by
    intro c B hB u
    rw [← hφ] at hB
    obtain ⟨s, rfl⟩ := MonoidHom.mem_range.mp hB
    obtain ⟨x, hx⟩ := hΨsurj u
    have hxu : Ψ.symm u = ⟨M₀.π x, hπV x⟩ := by rw [← hx]; exact Ψ.symm_apply_apply _
    have hsx : (s : G) * x * (s : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hVR s.2) x).mp x.2
    set w : ↥V := ⟨(s : G) * x * (s : G)⁻¹, hsx⟩ with hw
    have hu' : (φ s : Matrix ι ι K') *ᵥ u = Ψ ⟨M₀.π w, hπV w⟩ := by
      rw [hΨ, ← hx, hΨ]
      exact (hψ s x w rfl).symm
    obtain ⟨T, hT⟩ := hlin s s.2
    have hπw : M₀.π w = T (M₀.π x) := hT x (hVQ x.2)
    obtain ⟨y, hyV, hyQ, hy⟩ : c • M₀.π x ∈ M₀.img V := hS c _ (M₀.pi_mem_img x.2 (hVQ x.2))
    set y' : ↥V := ⟨y, hyV⟩ with hy'
    have hsy : (s : G) * y * (s : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hVR s.2) y).mp hyV
    set w' : ↥V := ⟨(s : G) * y * (s : G)⁻¹, hsy⟩ with hw'
    have hπw' : M₀.π w' = c • M₀.π w := by
      have := hT y hyQ
      rw [hπw]
      show M₀.π ((s : G) * y * (s : G)⁻¹) = c • T (M₀.π x)
      rw [this, hy, map_smul]
    have hL : Ψ (c • Ψ.symm ((φ s : Matrix ι ι K') *ᵥ u)) = Ψ ⟨M₀.π w', hπV w'⟩ := by
      rw [hu', Ψ.symm_apply_apply]
      congr 1
      exact Subtype.ext hπw'.symm
    have hR : Ψ (c • Ψ.symm u) = Ψ ⟨M₀.π y', hπV y'⟩ := by
      rw [hxu]
      congr 1
      exact Subtype.ext hy.symm
    rw [hL, hR, hΨ, hΨ]
    exact hψ s y' w' rfl
  obtain ⟨θ, hθ⟩ := exists_ringEquiv_of_scalar_commutant hcard hX Ψ hcomm
  refine ⟨θ, fun c v w hvw => ?_⟩
  have h := hθ c ⟨M₀.π v, hπV v⟩
  rw [hΨ] at h
  have h2 : (⟨M₀.π w, hπV w⟩ : ↥A) = c • ⟨M₀.π v, hπV v⟩ := Subtype.ext hvw
  rw [← hΨ w, h2, h]

end CFSG.RankThree.GF2n.Stroth80
