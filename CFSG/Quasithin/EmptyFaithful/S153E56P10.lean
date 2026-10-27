module

public import CFSG.Quasithin.EmptyFaithful.S153E56P6

public section

namespace CFSG.Quasithin

namespace S153E56p

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S153E CFSG.Quasithin.S153E57
  CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

section Swap

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {s : ℕ} {y t₁ : G}
  (S : Ctx56 T Mc M V₁ V₂ t N₁ N₂ s y t₁)

include S

theorem U_le_normalizer_of_Z_le {B : Subgroup G} (hZB : quasithinOmegaOneCenter T ≤ B)
    (hBU : B ≤ UH153 T M V₁ Mc) : UH153 T M V₁ Mc ≤ Subgroup.normalizer (B : Set G) :=
  le_normalizer_of_conj_mem fun u hu b hb => by
    have e : u * b * u⁻¹ = ⁅u, b⁆ * b := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact B.mul_mem (hZB (commutator_U_mem S.cx hu (hBU hb))) hb

theorem t₁_sq_mem_normalizer_E : t₁ * t₁ ∈ Subgroup.normalizer (Egp153 T M V₁ Mc y : Set G) := by
  obtain ⟨u, huU, c, hc, hsq⟩ := sq_mem_UCT S.cx S.c.h51 S.c.h52 (t₁_mem_T S)
  rw [hsq]
  refine Subgroup.mul_mem _ (U_le_normalizer_of_Z_le S (Z_le_E S) (E_le_U S) huU) ?_
  have h1 : c ∈ Subgroup.centralizer ((quasithinOmegaOneCenter T ⊔
      conjSubgroup (quasithinOmegaOneCenter T) y : Subgroup G) : Set G) :=
    Subgroup.centralizer_le (fun v hv => V0_le_V S hv) hc.2
  exact S.hG.EN (Subgroup.centralizer_le_normalizer _ h1)

theorem t₁_sq_conj_E {e : G} (he : e ∈ Egp153 T M V₁ Mc y) :
    (t₁ * t₁) * e * (t₁ * t₁)⁻¹ ∈ Egp153 T M V₁ Mc y :=
  (Subgroup.mem_normalizer_iff.1 (t₁_sq_mem_normalizer_E S) e).1 he

theorem t₁_sq_inv_conj_E {e : G} (he : e ∈ Egp153 T M V₁ Mc y) :
    (t₁ * t₁)⁻¹ * e * (t₁ * t₁)⁻¹⁻¹ ∈ Egp153 T M V₁ Mc y :=
  (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer (Egp153 T M V₁ Mc y : Set G)).inv_mem
    (t₁_sq_mem_normalizer_E S)) e).1 he

theorem t₁_mem_NZ' : t₁ ∈ NZ T := Mc_le_NZ S.cx (t₁_mem_Mc S)

@[expose] noncomputable def tau : MulAut (Ut T M V₁ Mc) := rho S.cx ⟨t₁, t₁_mem_NZ' S⟩

theorem tau_pi (u : ↥(UH153 T M V₁ Mc)) :
    tau S (pi S.cx u) = pi S.cx ⟨t₁ * u * t₁⁻¹, conj_t₁_U S u.2⟩ :=
  (pi_conj S.cx ⟨t₁, t₁_mem_NZ' S⟩ (t₁_mem_Mc S) u).symm

theorem tau_inv_pi (u : ↥(UH153 T M V₁ Mc)) :
    (tau S)⁻¹ (pi S.cx u) = pi S.cx ⟨t₁⁻¹ * u * t₁, conj_t₁_inv_U S u.2⟩ := by
  have h := pi_conj S.cx ⟨t₁⁻¹, Subgroup.inv_mem _ (t₁_mem_NZ' S)⟩ (Mc.inv_mem (t₁_mem_Mc S)) u
  have e : rho S.cx ⟨t₁⁻¹, Subgroup.inv_mem _ (t₁_mem_NZ' S)⟩ = (tau S)⁻¹ := by
    unfold tau
    rw [← map_inv]
    rfl
  rw [e] at h
  rw [← h]
  congr 1
  apply Subtype.ext
  simp

theorem tau_iso (q q' : Ut T M V₁ Mc) : bet S.cx (tau S q) (tau S q') = bet S.cx q q' :=
  bet_rho S (t₁_mem_Mc S) q q'

theorem tau_map₂ : ∀ e ∈ Et2 T M V₁ Mc y t₁, tau S e ∈ Et1 T M V₁ Mc y := by
  intro q hq
  obtain ⟨u, hu, rfl⟩ := (mem_Et2 S).1 hq
  rw [tau_pi]
  exact (mem_Et1 S).2 ⟨_, mem_conjSubgroup_iff.1 hu, rfl⟩

theorem tau_map₁ : ∀ e ∈ Et1 T M V₁ Mc y, tau S e ∈ Et2 T M V₁ Mc y t₁ := by
  intro q hq
  obtain ⟨u, hu, rfl⟩ := (mem_Et1 S).1 hq
  rw [tau_pi]
  refine (mem_Et2 S).2 ⟨_, ?_, rfl⟩
  rw [mem_conjSubgroup_iff]
  have := t₁_sq_conj_E S hu
  have e : t₁ * (t₁ * (u : G) * t₁⁻¹) * t₁⁻¹ = (t₁ * t₁) * u * (t₁ * t₁)⁻¹ := by group
  show t₁ * (t₁ * (u : G) * t₁⁻¹) * t₁⁻¹ ∈ Egp153 T M V₁ Mc y
  rw [e]
  exact this

theorem tauInv_map₁ : ∀ e ∈ Et1 T M V₁ Mc y, (tau S)⁻¹ e ∈ Et2 T M V₁ Mc y t₁ := by
  intro q hq
  obtain ⟨u, hu, rfl⟩ := (mem_Et1 S).1 hq
  rw [tau_inv_pi]
  refine (mem_Et2 S).2 ⟨_, ?_, rfl⟩
  rw [mem_conjSubgroup_iff]
  have e : t₁ * (t₁⁻¹ * (u : G) * t₁) * t₁⁻¹ = u := by group
  show t₁ * (t₁⁻¹ * (u : G) * t₁) * t₁⁻¹ ∈ Egp153 T M V₁ Mc y
  rw [e]
  exact hu

theorem tauInv_map₂ : ∀ e ∈ Et2 T M V₁ Mc y t₁, (tau S)⁻¹ e ∈ Et1 T M V₁ Mc y := by
  intro q hq
  obtain ⟨u, hu, rfl⟩ := (mem_Et2 S).1 hq
  rw [tau_inv_pi]
  refine (mem_Et1 S).2 ⟨_, ?_, rfl⟩
  have h1 : t₁ * (u : G) * t₁⁻¹ ∈ Egp153 T M V₁ Mc y := mem_conjSubgroup_iff.1 hu
  have h2 := t₁_sq_inv_conj_E S h1
  have e : (t₁ * t₁)⁻¹ * (t₁ * (u : G) * t₁⁻¹) * (t₁ * t₁)⁻¹⁻¹ = t₁⁻¹ * (u : G) * t₁ := by group
  show t₁⁻¹ * (u : G) * t₁ ∈ Egp153 T M V₁ Mc y
  rw [← e]
  exact h2

end Swap

end S153E56p

end CFSG.Quasithin
