module

public import CFSG.LieType.Steinberg.CentralExt.SLCentrallyClosed
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.Subnormal
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Steinberg.Classical.SpinFrame
public import CFSG.LieType.Steinberg.Exceptional.E6E7
public import CFSG.LieType.Universal.Spin.Generation
public import CFSG.LieType.Universal.Spin.OddCT
public import CFSG.LieType.Universal.Spin.PlusCT
public import CFSG.LieType.Universal.Spin.Structure
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LieType.Universal.Unitary
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.StandardType

open Matrix CFSG.LieType.Steinberg.CentralExt.SLClosed CFSG.Assembly.LowTwoRank
open scoped commutatorElement

theorem commutatorElement_mul_mem_center {X : Type*} [Group X] {a b z w : X}
    (hz : z ∈ Subgroup.center X) (hw : w ∈ Subgroup.center X) : ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
  have hz' := Subgroup.mem_center_iff.mp hz
  have hw' := Subgroup.mem_center_iff.mp hw
  have h1 : ⁅a * z, b * w⁆ = ⁅a, b * w⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    calc a * z * (b * w) * (a * z)⁻¹ * (b * w)⁻¹
        = a * (z * (b * w)) * z⁻¹ * a⁻¹ * (b * w)⁻¹ := by group
      _ = a * ((b * w) * z) * z⁻¹ * a⁻¹ * (b * w)⁻¹ := by rw [← hz' (b * w)]
      _ = a * (b * w) * a⁻¹ * (b * w)⁻¹ := by group
  have h2 : ⁅a, b * w⁆ = ⁅a, b⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    calc a * (b * w) * a⁻¹ * (b * w)⁻¹ = a * b * (w * a⁻¹) * w⁻¹ * b⁻¹ := by group
      _ = a * b * (a⁻¹ * w) * w⁻¹ * b⁻¹ := by rw [← hw' a⁻¹]
      _ = a * b * a⁻¹ * b⁻¹ := by group
  rw [h1, h2]

section Lift

variable {n : ℕ} {F : Type} [Field F] [Finite F] {K : Type*} [Group K]

theorem exists_slLift_of_mulEquiv (hn : 2 ≤ n) (hsep : Separating n F) (hK : commutator K = ⊤)
    (θ : K ⧸ Subgroup.center K ≃* ProjectiveSpecialLinearGroup (Fin (n + 1)) F) :
    ∃ φ : SpecialLinearGroup (Fin (n + 1)) F →* K, Function.Surjective φ ∧
      φ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) F) ∧
      ∀ g, θ (QuotientGroup.mk (φ g)) = QuotientGroup.mk g := by
  obtain ⟨E, hE⟩ : ∃ E : Subgroup (K × SpecialLinearGroup (Fin (n + 1)) F),
      E = MonoidHom.eqLocus
        ((θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))).comp (MonoidHom.fst _ _))
        ((QuotientGroup.mk' (Subgroup.center _)).comp (MonoidHom.snd _ _)) := ⟨_, rfl⟩
  have hmem : ∀ e : K × SpecialLinearGroup (Fin (n + 1)) F,
      e ∈ E ↔ θ (QuotientGroup.mk e.1) = QuotientGroup.mk e.2 := by
    intro e
    rw [hE]
    rfl
  let π : E →* SpecialLinearGroup (Fin (n + 1)) F := (MonoidHom.snd _ _).comp E.subtype
  have hπ : Function.Surjective π := by
    intro g
    obtain ⟨l, hl⟩ := QuotientGroup.mk_surjective (θ.symm (QuotientGroup.mk g))
    refine ⟨⟨(l, g), (hmem _).mpr ?_⟩, rfl⟩
    change θ (QuotientGroup.mk l) = QuotientGroup.mk g
    rw [hl, MulEquiv.apply_symm_apply]
  have hcen : π.ker ≤ Subgroup.center E := by
    intro e he
    have h2 : (e : K × SpecialLinearGroup (Fin (n + 1)) F).2 = 1 := he
    have h1 : (e : K × SpecialLinearGroup (Fin (n + 1)) F).1 ∈ Subgroup.center K := by
      have h := (hmem _).mp e.2
      rw [h2, QuotientGroup.mk_one, ← map_one θ] at h
      exact (QuotientGroup.eq_one_iff _).mp (θ.injective h)
    rw [Subgroup.mem_center_iff]
    intro e'
    apply Subtype.ext
    apply Prod.ext
    · exact (Subgroup.mem_center_iff.mp h1 _)
    · change (e' : K × SpecialLinearGroup (Fin (n + 1)) F).2 *
          (e : K × SpecialLinearGroup (Fin (n + 1)) F).2 =
        (e : K × SpecialLinearGroup (Fin (n + 1)) F).2 *
          (e' : K × SpecialLinearGroup (Fin (n + 1)) F).2
      rw [h2, one_mul, mul_one]
  obtain ⟨σ, hσ⟩ := sl_exists_section_of_separating hn hsep hπ hcen
  let φ : SpecialLinearGroup (Fin (n + 1)) F →* K := (MonoidHom.fst _ _).comp (E.subtype.comp σ)
  have hφθ : ∀ g, θ (QuotientGroup.mk (φ g)) = QuotientGroup.mk g := by
    intro g
    have h := (hmem _).mp (σ g).2
    have h' : ((σ g : E) : K × SpecialLinearGroup (Fin (n + 1)) F).2 = g := hσ g
    rw [h'] at h
    exact h
  have hdecomp : ∀ l : K, ∃ g, (φ g)⁻¹ * l ∈ Subgroup.center K := by
    intro l
    obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (θ (QuotientGroup.mk l))
    refine ⟨g, (QuotientGroup.eq (s := Subgroup.center K)).mp (θ.injective ?_)⟩
    rw [hφθ, hg]
  refine ⟨φ, ?_, ?_, hφθ⟩
  ·
    have hle : commutator K ≤ φ.range := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      obtain ⟨g₁, hg₁⟩ := hdecomp a
      obtain ⟨g₂, hg₂⟩ := hdecomp b
      have ea : a = φ g₁ * ((φ g₁)⁻¹ * a) := by group
      have eb : b = φ g₂ * ((φ g₂)⁻¹ * b) := by group
      rw [ea, eb, commutatorElement_mul_mem_center hg₁ hg₂, ← map_commutatorElement]
      exact ⟨_, rfl⟩
    intro l
    exact (hle (hK ▸ Subgroup.mem_top l) : l ∈ φ.range)
  · intro g hg
    have h := hφθ g
    rw [show φ g = 1 from hg, QuotientGroup.mk_one, map_one] at h
    exact (QuotientGroup.eq_one_iff _).mp h.symm

end Lift

theorem exists_slLift_of_classicalModel {G : Type} [Group G] {H : Subgroup G} {n f : ℕ}
    (hn : 2 ≤ n) (hf : 2 ≤ f) (hnf : ¬ (n = 2 ∧ f = 2)) (hH : commutator H = ⊤)
    (hmod : StatedClassicalModel (H ⧸ Subgroup.center H) .PSL (n + 1) 2 f) :
    ∃ φ : SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f) →* G, φ.range = H ∧
      φ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)) := by
  obtain ⟨-, K', _, _, hK', ⟨e⟩⟩ := hmod
  have h4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hsep : Separating n K' := by
    refine separating_of_card hn (by omega) (fun h => hnf ⟨h.1, ?_⟩) (fun h => ?_)
    · have h' : 2 ^ f = 2 ^ 2 := by rw [← hK', h.2]; norm_num
      exact Nat.pow_right_injective le_rfl h'
    · have hev : Even (2 ^ f) := (Nat.even_pow' (by omega)).mpr even_two
      rw [← hK', h.2] at hev
      exact absurd hev (by decide)
  obtain ⟨φ₀, hφ₀, hker₀, -⟩ := exists_slLift_of_mulEquiv hn hsep hH
    (e.trans (projectiveSpecialLinearGroupEquivStatedProj (n + 1) K').symm)
  have : Fintype K' := Fintype.ofFinite K'
  have : Fintype (GaloisField 2 f) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 2 f) = Fintype.card K' := by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, GaloisField.card 2 f (by omega), hK']
  let ε : GaloisField 2 f ≃+* K' := FiniteField.ringEquivOfCardEq hcard
  let μ : SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f) →*
      SpecialLinearGroup (Fin (n + 1)) K' := SpecialLinearGroup.map ε.toRingHom
  let μ' : SpecialLinearGroup (Fin (n + 1)) K' →*
      SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f) := SpecialLinearGroup.map ε.symm.toRingHom
  have hμμ' : ∀ g, μ (μ' g) = g := by
    intro g
    ext i j
    simp [μ, μ']
  have hμ'μ : ∀ g, μ' (μ g) = g := by
    intro g
    ext i j
    simp [μ, μ']
  refine ⟨H.subtype.comp (φ₀.comp μ), ?_, ?_⟩
  · have hsurj : Function.Surjective (φ₀.comp μ) := by
      intro l
      obtain ⟨g, rfl⟩ := hφ₀ l
      exact ⟨μ' g, by simp only [MonoidHom.comp_apply, hμμ']⟩
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hsurj, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  · intro g hg
    have hg' : φ₀ (μ g) = 1 := by
      have : H.subtype (φ₀ (μ g)) = 1 := hg
      exact H.subtype_injective (by rw [this, map_one])
    have hc := Subgroup.mem_center_iff.mp (hker₀ hg')
    rw [Subgroup.mem_center_iff]
    intro h
    have := hc (μ h)
    rw [← map_mul, ← map_mul] at this
    have h2 := congrArg μ' this
    rwa [hμ'μ, hμ'μ] at h2

end CFSG.StandardType
