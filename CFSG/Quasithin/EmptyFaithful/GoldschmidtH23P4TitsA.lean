module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4Cen
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4Core

public section

namespace CFSG.Quasithin.H23P4

open CFSG.QuasithinUnique
open scoped Pointwise

@[expose] def CenAt {Γ : Type*} [Group Γ] (T : Subgroup Γ) : Prop :=
  ∀ U : Subgroup Γ, T ≤ U → ∀ b : ℕ, 0 < b → T.relIndex U = 5 ^ b →
    ∀ z ∈ T, (∀ s ∈ T, s * z = z * s) → ∀ u ∈ U, u * z = z * u

theorem cenOvergroup_iff {Γ : Type*} [Group Γ] :
    CenOvergroup Γ ↔ ∀ S₀ : Subgroup Γ, IsSylowTwoOf S₀ ⊤ → CenAt S₀ :=
  ⟨fun h S₀ hS U hle b hb hidx => h S₀ U hS hle b hb hidx,
    fun h S₀ U hS hle b hb hidx => h S₀ hS U hle b hb hidx⟩

theorem CenAt.of_map {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) {T : Subgroup X}
    (h : CenAt (T.map (e : X →* Y))) : CenAt T := by
  intro U hle b hb hidx z hz hzc u hu
  have h1 : (T.map (e : X →* Y)).relIndex (U.map (e : X →* Y)) = 5 ^ b := by
    rw [Subgroup.relIndex_map_map_of_injective _ _ e.injective]
    exact hidx
  have h2 := h (U.map (e : X →* Y)) (Subgroup.map_mono hle) b hb h1 (e z)
    (Subgroup.mem_map_of_mem _ hz)
    (by
      rintro _ ⟨s, hs, rfl⟩
      show e s * e z = e z * e s
      rw [← map_mul, ← map_mul]
      exact congrArg e (hzc s hs)) (e u) (Subgroup.mem_map_of_mem _ hu)
  apply e.injective
  rw [map_mul, map_mul]
  exact h2

theorem CenAt.of_conj {Γ : Type*} [Group Γ] {S T : Subgroup Γ} (m : Γ)
    (hm : ∀ x : Γ, x ∈ S ↔ m⁻¹ * x * m ∈ T) (h : CenAt T) : CenAt S := by
  refine CenAt.of_map (MulAut.conj m⁻¹ : Γ ≃* Γ) ?_
  have hST : S.map ((MulAut.conj m⁻¹ : Γ ≃* Γ) : Γ →* Γ) = T := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have := (hm x).1 hx
      simpa [MulAut.conj_apply] using this
    · intro hy
      refine ⟨m * y * m⁻¹, (hm _).2 ?_, ?_⟩
      · simpa [mul_assoc] using hy
      · simp [mul_assoc]
  rw [hST]
  exact h

theorem exists_conj_of_isSylowTwoOf {Γ : Type*} [Group Γ] [Finite Γ] {S T : Subgroup Γ}
    (hS : IsSylowTwoOf S ⊤) (hT : IsSylowTwoOf T ⊤) :
    ∃ m : Γ, ∀ x : Γ, x ∈ S ↔ m⁻¹ * x * m ∈ T := by
  rw [isSylowTwoOf_top_iff] at hS hT
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S' : Sylow 2 Γ := hS.1.toSylow hS.2
  let T' : Sylow 2 Γ := hT.1.toSylow hT.2
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ T' S'
  refine ⟨g, fun x => ?_⟩
  have h1 : ((g • T' : Sylow 2 Γ) : Subgroup Γ) = MulAut.conj g • (T' : Subgroup Γ) :=
    Sylow.coe_subgroup_smul
  rw [hg] at h1
  have h2 : S = MulAut.conj g • T := h1
  rw [h2, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  rfl

theorem cenOvergroup_of_cenAt {Γ : Type*} [Group Γ] [Finite Γ] {T₀ : Subgroup Γ}
    (hT₀ : IsSylowTwoOf T₀ ⊤) (h : CenAt T₀) : CenOvergroup Γ := by
  rw [cenOvergroup_iff]
  intro S₀ hS
  obtain ⟨m, hm⟩ := exists_conj_of_isSylowTwoOf hS hT₀
  exact CenAt.of_conj m hm h

theorem CenOvergroup.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : CenOvergroup Y) : CenOvergroup X := by
  rw [cenOvergroup_iff]
  intro S₀ hS
  refine CenAt.of_map e ((cenOvergroup_iff.1 h) _ ?_)
  rw [isSylowTwoOf_top_iff] at hS ⊢
  exact ⟨hS.1.map _, by rw [Subgroup.index_map_equiv]; exact hS.2⟩

theorem center_eq_bot_transport {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : Subgroup.center Y = ⊥) : Subgroup.center X = ⊥ := by
  have h1 := Subgroup.map_center_eq e
  rw [h] at h1
  exact Subgroup.map_injective e.injective (h1.trans (Subgroup.map_bot _).symm)

end CFSG.Quasithin.H23P4
