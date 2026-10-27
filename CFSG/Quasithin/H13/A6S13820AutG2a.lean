module

public import CFSG.Quasithin.Vol2.RootDataG2
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LieType.Chevalley.CoordinateFieldFixedSubgroup
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2 CFSG.Quasithin.H13.RootData.G2
open CFSG.QuasithinUnique (IsSylowTwoOf)
open scoped Pointwise

namespace Aut20

theorem comm_mem_of_mul20 {G : Type*} [Group G] {H U : Subgroup G}
    (hHN : H ≤ Subgroup.normalizer (U : Set G)) (hcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a)
    {h' u h : G} (hh' : h' ∈ H) (hu : u ∈ U) (hh : h ∈ H) :
    h' * u * h * (h' * u)⁻¹ * h⁻¹ ∈ U := by
  have h1 : h * u⁻¹ * h⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp (hHN hh) _).mp (U.inv_mem hu)
  have h2 : h' * (u * (h * u⁻¹ * h⁻¹)) * h'⁻¹ ∈ U :=
    (Subgroup.mem_normalizer_iff.mp (hHN hh') _).mp (U.mul_mem hu h1)
  have e : h' * u * h * (h' * u)⁻¹ * h⁻¹ =
      h' * (u * (h * u⁻¹ * h⁻¹)) * h'⁻¹ * (h' * h * h'⁻¹ * h⁻¹) := by group
  have e2 : h' * h * h'⁻¹ * h⁻¹ = 1 := by rw [hcomm h' hh' h hh]; group
  rw [e, e2, mul_one]
  exact h2

theorem exists_map_conj_eq20 {G : Type*} [Group G] [Finite G] {S S₀ : Subgroup G}
    (hS : IsSylowTwoOf S ⊤) (hS₀ : IsSylowTwoOf S₀ ⊤) :
    ∃ x : G, S.map (MulAut.conj x).toMonoidHom = S₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have i1 : ¬ 2 ∣ S.index := by
    have := hS.2.2
    rwa [show (S.subgroupOf ⊤).index = S.relIndex ⊤ from rfl, Subgroup.relIndex_top_right] at this
  have i2 : ¬ 2 ∣ S₀.index := by
    have := hS₀.2.2
    rwa [show (S₀.subgroupOf ⊤).index = S₀.relIndex ⊤ from rfl,
      Subgroup.relIndex_top_right] at this
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq G (hS.2.1.toSylow i1) (hS₀.2.1.toSylow i2)
  refine ⟨x, ?_⟩
  have h : MulAut.conj x • S = S₀ := by
    have h1 := congrArg (fun P : Sylow 2 G => (P : Subgroup G)) hx
    simp only [Sylow.coe_subgroup_smul] at h1
    exact h1
  rw [← h]
  ext y
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Subgroup.mem_map]
  constructor
  · rintro ⟨s, hs, rfl⟩
    simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using hs
  · intro hy
    refine ⟨_, hy, ?_⟩
    simp [MulAut.smul_def, MulAut.conj_apply, mul_assoc]

theorem pair_rC_i0 : ∑ j, Tag.G2.cartan i0 j * rC j = 1 := by decide

theorem pair_rC_i1 : ∑ j, Tag.G2.cartan i1 j * rC j = 0 := by decide

theorem pair_rV_i0 : ∑ j, Tag.G2.cartan i0 j * rV j = 0 := by decide

theorem pair_rV_i1 : ∑ j, Tag.G2.cartan i1 j * rV j = 1 := by decide

theorem rV_isRoot : IsRoot Tag.G2 rV :=
  (isRoot_pos_iff.2 (by simp)).1

section Torus

variable {K : Type} [Field K]

@[expose] noncomputable def tor20 (s₁ s₂ : Kˣ) : ModGL Tag.G2 K :=
  torusElt Tag.G2 K i0 s₁ * torusElt Tag.G2 K i1 s₂

theorem tor20_mem_torusGroup (s₁ s₂ : Kˣ) : tor20 s₁ s₂ ∈ torusGroup Tag.G2 K :=
  mul_mem (torusElt_mem_torusGroup _ _) (torusElt_mem_torusGroup _ _)

theorem tor20_mem_adjointGroup (s₁ s₂ : Kˣ) : tor20 s₁ s₂ ∈ adjointGroup Tag.G2 K :=
  mul_mem (torusElt_mem_adjointGroup _ _) (torusElt_mem_adjointGroup _ _)

theorem tor20_conj_rC (s₁ s₂ : Kˣ) (x : K) :
    tor20 s₁ s₂ * gX rC x * (tor20 s₁ s₂)⁻¹ = gX rC ((s₁ : K) * x) := by
  have h1 := root_torus_conjugation (τ := Tag.G2) (R := K) i1 rC_isRoot s₂ x
  rw [pair_rC_i1, zpow_zero, Units.val_one, one_mul] at h1
  have h0 := root_torus_conjugation (τ := Tag.G2) (R := K) i0 rC_isRoot s₁ x
  rw [pair_rC_i0, zpow_one] at h0
  calc tor20 s₁ s₂ * gX rC x * (tor20 s₁ s₂)⁻¹
      = torusElt Tag.G2 K i0 s₁ * (torusElt Tag.G2 K i1 s₂ * gX rC x *
          (torusElt Tag.G2 K i1 s₂)⁻¹) * (torusElt Tag.G2 K i0 s₁)⁻¹ := by
        rw [tor20]; group
    _ = gX rC ((s₁ : K) * x) := by rw [h1, h0]

theorem tor20_conj_rV (s₁ s₂ : Kˣ) (x : K) :
    tor20 s₁ s₂ * gX rV x * (tor20 s₁ s₂)⁻¹ = gX rV ((s₂ : K) * x) := by
  have h1 := root_torus_conjugation (τ := Tag.G2) (R := K) i1 rV_isRoot s₂ x
  rw [pair_rV_i1, zpow_one] at h1
  have h0 := root_torus_conjugation (τ := Tag.G2) (R := K) i0 rV_isRoot s₁ ((s₂ : K) * x)
  rw [pair_rV_i0, zpow_zero, Units.val_one, one_mul] at h0
  calc tor20 s₁ s₂ * gX rV x * (tor20 s₁ s₂)⁻¹
      = torusElt Tag.G2 K i0 s₁ * (torusElt Tag.G2 K i1 s₂ * gX rV x *
          (torusElt Tag.G2 K i1 s₂)⁻¹) * (torusElt Tag.G2 K i0 s₁)⁻¹ := by
        rw [tor20]; group
    _ = gX rV ((s₂ : K) * x) := by rw [h1, h0]

theorem tor20_injective {s₁ s₂ s₁' s₂' : Kˣ} (h : tor20 s₁ s₂ = tor20 s₁' s₂') :
    s₁ = s₁' ∧ s₂ = s₂' := by
  have hc := tor20_conj_rC s₁ s₂ 1
  rw [h, tor20_conj_rC] at hc
  have hv := tor20_conj_rV s₁ s₂ 1
  rw [h, tor20_conj_rV] at hv
  have e1 := pinnedX_injective Tag.G2 K rC hc
  have e2 := pinnedX_injective Tag.G2 K rV hv
  rw [mul_one, mul_one] at e1 e2
  exact ⟨Units.ext e1.symm, Units.ext e2.symm⟩

theorem tor20_one : tor20 (1 : Kˣ) 1 = 1 := by
  rw [tor20, torusElt_one, torusElt_one, one_mul]

theorem tor20_mul (s₁ s₂ s₁' s₂' : Kˣ) :
    tor20 (s₁ * s₁') (s₂ * s₂') = tor20 s₁ s₂ * tor20 s₁' s₂' := by
  have hc := (triangular_borel_structure.{0, 0} Tag.G2 K).1 _
    (torusElt_mem_torusGroup i1 s₂) _ (torusElt_mem_torusGroup i0 s₁')
  rw [tor20, tor20, tor20, torusElt_mul, torusElt_mul]
  calc torusElt Tag.G2 K i0 s₁ * torusElt Tag.G2 K i0 s₁' *
        (torusElt Tag.G2 K i1 s₂ * torusElt Tag.G2 K i1 s₂')
      = torusElt Tag.G2 K i0 s₁ * (torusElt Tag.G2 K i0 s₁' * torusElt Tag.G2 K i1 s₂) *
          torusElt Tag.G2 K i1 s₂' := by group
    _ = _ := by rw [← hc]; group

@[expose] noncomputable def torHom20 : Kˣ × Kˣ →* ↥(adjointGroup Tag.G2 K) where
  toFun p := ⟨tor20 p.1 p.2, tor20_mem_adjointGroup _ _⟩
  map_one' := Subtype.ext tor20_one
  map_mul' p q := Subtype.ext (tor20_mul p.1 p.2 q.1 q.2)

theorem coe_torHom20 (p : Kˣ × Kˣ) :
    ((torHom20 p : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K) = tor20 p.1 p.2 := rfl

theorem torHom20_injective : Function.Injective (torHom20 (K := K)) := fun p q h => by
  have h' := tor20_injective (congrArg Subtype.val h)
  exact Prod.ext h'.1 h'.2

theorem entrywise_tor20 (σ : K ≃+* K) (s₁ s₂ : Kˣ) :
    Units.map (entrywiseHom σ.toRingHom) (tor20 s₁ s₂) =
      tor20 (Units.map σ.toRingHom.toMonoidHom s₁) (Units.map σ.toRingHom.toMonoidHom s₂) := by
  rw [tor20, map_mul, entrywise_torusElt, entrywise_torusElt, tor20]

end Torus

end Aut20

end CFSG.Quasithin.H13.A6
