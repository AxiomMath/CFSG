module

public import CFSG.Quasithin.Vol2.Ch12Sec8NonabTen
public import CFSG.Quasithin.Vol2.Ch12Sec8OneAbs
public import CFSG.Quasithin.Vol2.Ch12Sec8OneAbsHat

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace L128A

namespace HatU

variable {G : Type} [Group G] {U : Subgroup G} (D : HatModelU U)

@[expose] def fixSpace (K : Subgroup G) : Submodule (ZMod 2) D.V where
  carrier := {v | ∀ γ ∈ D.img K, γ v = v}
  add_mem' := fun ha hb γ hγ => by rw [map_add, ha γ hγ, hb γ hγ]
  zero_mem' := fun γ _ => map_zero γ
  smul_mem' := fun c v hv γ hγ => by rw [map_smul, hv γ hγ]

theorem mem_fixSpace {K : Subgroup G} {v : D.V} :
    v ∈ fixSpace D K ↔ ∀ γ ∈ D.img K, γ v = v := Iff.rfl

end HatU

namespace Setting

variable {G : Type} [Group G] [Finite G] {V V₁ L T : Subgroup G}

variable {G : Type} [Group G] [Finite G] {V V₁ L T : Subgroup G}

theorem hat_V_cases (S : Setting V V₁ L T)
    (D : HatModelU (uA V V₁)) {a : G} (haV : a ∈ V) (haZ : a ∉ V₁) :
    D.π a ≠ 0 ∧ D.π a ∈ D.hat (V) ∧ ∀ v ∈ D.hat (V), v = 0 ∨ v = D.π a := by
  obtain ⟨z, hzZ, hz1, hall⟩ := S.exists_gen
  have hcases := S.V_cases hzZ hz1 haV haZ
  have haU : a ∈ uA V V₁ := le_uA V V₁ haV
  have hπz : D.π z = 0 := (HatU.π_eq_zero_iff D (le_uA V V₁ (S.V₁_le hzZ))).mpr
    (S.V₁_le_centerOf hzZ)
  refine ⟨?_, HatU.π_mem_hat D haV haU, ?_⟩
  · intro h0
    have hmem := (HatU.π_eq_zero_iff D haU).mp h0
    apply haZ
    rw [← S.inf_centerOf]
    exact ⟨haV, hmem⟩
  · intro v hv
    obtain ⟨c, hcV, hcU, rfl⟩ := (HatU.mem_hat D).mp hv
    rcases hcases c hcV with h1 | h1 | h1 | h1
    · left
      rw [h1, HatU.π_one D]
    · left
      rw [h1, hπz]
    · right
      rw [h1]
    · right
      rw [h1, D.π_mul z (le_uA V V₁ (S.V₁_le hzZ)) a haU, hπz, zero_add]

theorem mem_hat_wA_iff (S : Setting V V₁ L T)
    (D : HatModelU (uA V V₁)) {a : G} (haV : a ∈ V) (haZ : a ∉ V₁)
    {v : D.V} : v ∈ D.hat (wA V V₁) ↔ D.B (D.π a) v = 0 := by
  obtain ⟨z, hzZ, hz1, hall⟩ := S.exists_gen
  have hcases := S.V_cases hzZ hz1 haV haZ
  have haU : a ∈ uA V V₁ := le_uA V V₁ haV
  constructor
  · intro hv
    obtain ⟨w, hwW, hwU, rfl⟩ := (HatU.mem_hat D).mp hv
    rw [D.B_spec a haU w hwU]
    have := Subgroup.mem_centralizer_iff.mp hwW.2 a haV
    rw [this]
    group
  · intro hv
    obtain ⟨u, huU, rfl⟩ := D.π_surj v
    have h1 := (D.B_spec a haU u huU).mp hv
    have h2 : a * u = u * a := by
      calc a * u = (a * u * a⁻¹ * u⁻¹) * u * a := by group
        _ = u * a := by rw [h1]; group
    have hzu : z * u = u * z :=
      (Subgroup.mem_centralizer_iff.mp (S.V₁_le_centerOf hzZ).2 u huU).symm
    refine HatU.π_mem_hat D ⟨huU, Subgroup.mem_centralizer_iff.mpr fun c hc => ?_⟩ huU
    rcases hcases c hc with h3 | h3 | h3 | h3
    · rw [h3]; simp
    · rw [h3]; exact hzu
    · rw [h3]; exact h2
    · rw [h3, mul_assoc, h2, ← mul_assoc, hzu, mul_assoc]

theorem π_mem_span_of_mem_sup (S : Setting V V₁ L T) (D : HatModelU (uA V V₁)) {a : G}
    (haV : a ∈ V) (haZ : a ∉ V₁) {y : G}
    (hy : y ∈ centerOf (uA V V₁) ⊔ V) :
    D.π y ∈ Submodule.span (ZMod 2) {D.π a} := by
  obtain ⟨z, hzZ, hz1, hall⟩ := S.exists_gen
  have hcases := S.V_cases hzZ hz1 haV haZ
  have haU : a ∈ uA V V₁ := le_uA V V₁ haV
  have hzV : z ∈ V := S.V₁_le hzZ
  have hπz : D.π z = 0 := (HatU.π_eq_zero_iff D (le_uA V V₁ hzV)).mpr
    (S.V₁_le_centerOf hzZ)
  obtain ⟨c, hc, v, hv, rfl⟩ := exists_eq_mul_of_mem_sup_of_forall_commute
    (A := centerOf (uA V V₁)) (B := V)
    (fun c hc v hv => (Subgroup.mem_centralizer_iff.mp hc.2 v (le_uA V V₁ hv)).symm) hy
  rw [D.π_mul c hc.1 v (le_uA V V₁ hv), (HatU.π_eq_zero_iff D hc.1).mpr hc, zero_add]
  rcases hcases v hv with h1 | h1 | h1 | h1
  · rw [h1, HatU.π_one D]
    exact Submodule.zero_mem _
  · rw [h1, hπz]
    exact Submodule.zero_mem _
  · rw [h1]
    exact Submodule.subset_span (Set.mem_singleton _)
  · rw [h1, D.π_mul z (le_uA V V₁ hzV) a haU, hπz, zero_add]
    exact Submodule.subset_span (Set.mem_singleton _)

end Setting

end L128A

end CFSG.Quasithin.H13
