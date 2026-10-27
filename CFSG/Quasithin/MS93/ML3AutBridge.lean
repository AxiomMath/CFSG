module

public import CFSG.Quasithin.MS93.ML3Aut
public import CFSG.Quasithin.MS93.ML3RecBridge

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Matrix ML3
open scoped commutatorElement

variable {G : Type} [Group G] {K V Z : Subgroup G} {F : Type} [Field F]

theorem isSumOfNaturalModulesVia_of_surj {F' : Type} [Field F'] [Finite F] [CharP F 2]
    [Finite F'] [CharP F' 2] {α : ↥K →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)}
    (hα : Function.Surjective α) {α' : ↥K →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F')}
    (hα' : Function.Surjective α') (hker : α.ker ≤ α'.ker)
    (h : IsSumOfNaturalModulesVia K V Z α' false 1) :
    ∃ dual : Bool, IsSumOfNaturalModulesVia K V Z α dual 1 := by
  set N := NatSec.ofIsSum h with hN
  have hKV := N.norm
  have hZV := N.le
  have hKZ : K ≤ Subgroup.normalizer (Z : Set G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      have hzV := hZV hz
      rw [← N.coord_eq_zero_iff (N.conj_mem ⟨l, hl⟩ hzV), N.coord_conj ⟨l, hl⟩ hzV,
        (N.coord_eq_zero_iff hzV).mpr hz, Matrix.mulVec_zero]
    · intro hz
      have hz' : z ∈ V := by
        have := N.conj_mem ⟨l, hl⟩⁻¹ (hZV hz)
        simpa [mul_assoc] using this
      rw [← N.coord_eq_zero_iff hz']
      have h0 := (N.coord_eq_zero_iff (N.conj_mem ⟨l, hl⟩ hz')).mpr hz
      rw [N.coord_conj ⟨l, hl⟩ hz'] at h0
      have h1 := congrArg (fun u => natAct false (toSL3 α' ⟨l, hl⟩⁻¹) *ᵥ u) h0
      simp only [natAct_false, Matrix.mulVec_mulVec, Matrix.mulVec_zero] at h1
      rwa [← coe_mul_SL3, ← map_mul, inv_mul_cancel, map_one, coe_one_SL3,
        Matrix.one_mulVec] at h1
  have hVc : ∀ v ∈ V, ∀ w ∈ V, ⁅v, w⁆ ∈ Z := by
    intro v hv w hw
    have hm : ⁅v, w⁆ ∈ V := by
      rw [commutatorElement_def]
      exact V.mul_mem (V.mul_mem (V.mul_mem hv hw) (V.inv_mem hv)) (V.inv_mem hw)
    rw [← N.coord_eq_zero_iff hm, commutatorElement_def,
      N.coord_mul (V.mul_mem (V.mul_mem hv hw) (V.inv_mem hv)) (V.inv_mem hw),
      N.coord_mul (V.mul_mem hv hw) (V.inv_mem hv), N.coord_mul hv hw, N.coord_inv hv,
      N.coord_inv hw]
    abel
  have hkerV : ∀ l : ↥K, α l = 1 → ∀ v ∈ V, v⁻¹ * ((l : G) * v * (l : G)⁻¹) ∈ Z := by
    intro l hl v hv
    have hl' : α' l = 1 := hker hl
    rw [← N.coord_eq_zero_iff (V.mul_mem (V.inv_mem hv) (N.conj_mem l hv)),
      N.coord_mul (V.inv_mem hv) (N.conj_mem l hv), N.coord_inv hv, N.coord_conj l hv]
    have h1 : toSL3 α' l = 1 := by
      rw [toSL3, MonoidHom.comp_apply, hl', map_one]
    rw [h1, natAct_false, coe_one_SL3, Matrix.one_mulVec, neg_add_cancel]
  obtain ⟨Q, _, π, ρ, hπs, hπk, hπρ⟩ := ML3.exists_quotient_action hα hKV hZV hKZ hVc hkerV
  let βV : ↥V →* Multiplicative (Fin 3 → F') := N.β
  have hβk : π.ker ≤ βV.ker := by
    intro v hv
    rw [MonoidHom.mem_ker] at hv ⊢
    exact (N.ker v).mpr ((hπk v).mp hv)
  let e₀ : Q →* Multiplicative (Fin 3 → F') := π.liftOfSurjective hπs ⟨βV, hβk⟩
  have he₀ : ∀ v : ↥V, e₀ (π v) = N.β v := fun v =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨βV, hβk⟩ v
  have he₀b : Function.Bijective e₀ := by
    constructor
    · rw [injective_iff_map_eq_one]
      intro q hq
      obtain ⟨v, rfl⟩ := hπs q
      rw [he₀] at hq
      exact (hπk v).mpr ((N.ker v).mp hq)
    · intro y
      obtain ⟨v, hv⟩ := N.surj y
      exact ⟨π v, by rw [he₀, hv]⟩
  let e : Q ≃* Multiplicative (Fin 3 → F') := MulEquiv.ofBijective e₀ he₀b
  have hkerle : (toSL3 α).ker ≤ (toSL3 α').ker := by
    intro l hl
    rw [MonoidHom.mem_ker] at hl ⊢
    have hl' : α l = 1 := by
      have := congrArg (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F) hl
      simpa [toSL3] using this
    rw [toSL3, MonoidHom.comp_apply, hker hl', map_one]
  let θ : SL3 F →* SL3 F' :=
    (QuotientGroup.lift (toSL3 α).ker (toSL3 α') hkerle).comp
      (QuotientGroup.quotientKerEquivOfSurjective (toSL3 α) (toSL3_surjective hα)).symm.toMonoidHom
  have hθ : ∀ l : ↥K, θ (toSL3 α l) = toSL3 α' l := by
    intro l
    have h1 : (QuotientGroup.quotientKerEquivOfSurjective (toSL3 α) (toSL3_surjective hα)).symm
        (toSL3 α l) = (l : ↥K ⧸ (toSL3 α).ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    simp only [θ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h1, QuotientGroup.lift_mk]
  have hθs : Function.Surjective θ := by
    intro g'
    obtain ⟨l, rfl⟩ := toSL3_surjective hα' g'
    exact ⟨toSL3 α l, hθ l⟩
  have he : ∀ (g : SL3 F) (q : Q), Multiplicative.toAdd (e (ρ g q)) =
      ((θ g : SL3 F') : Matrix (Fin 3) (Fin 3) F') *ᵥ Multiplicative.toAdd (e q) := by
    intro g q
    obtain ⟨l, rfl⟩ := toSL3_surjective hα g
    obtain ⟨v, rfl⟩ := hπs q
    change Multiplicative.toAdd (e₀ (ρ (toSL3 α l) (π v))) = _ *ᵥ Multiplicative.toAdd (e₀ (π v))
    rw [hπρ, he₀, he₀, hθ, N.equiv l v (conjOn hKV l v) (coe_conjOn_apply _ _ _), natAct_false]
  obtain ⟨dual, β, hβ, -⟩ := exists_natEquiv_or_dual_of_surj θ hθs ρ e he
  let e1 : Multiplicative (Fin 1 → Fin 3 → F) ≃* Multiplicative (Fin 3 → F) :=
    AddEquiv.toMultiplicative (AddEquiv.funUnique (Fin 1) (Fin 3 → F))
  refine ⟨dual, hKV, hZV, e1.symm.toMonoidHom.comp (β.toMonoidHom.comp π),
    e1.symm.surjective.comp (β.surjective.comp hπs), ?_, ?_⟩
  · ext v
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hπk]
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
  · intro a u v huv i
    have hv : v = conjOn hKV a u := Subtype.ext (by rw [coe_conjOn_apply]; exact huv)
    have h1 := hβ (toSL3 α a) (π u)
    rw [hπρ, ← hv] at h1
    rw [moduleAct_eq_natAct]
    change Multiplicative.toAdd (β (π v)) = natAct dual (toSL3 α a) *ᵥ
      Multiplicative.toAdd (β (π u))
    exact h1

end CFSG.Quasithin.MS93
