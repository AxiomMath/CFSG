module

public import CFSG.Permutation.UnitaryThreeRecognition.HeisField
public import CFSG.Permutation.UnitaryThreeRecognition.HeisForm

public section

namespace CFSG.UnitaryThreeRecognition.Heisenberg

open scoped commutatorElement

namespace Hyp

variable {G : Type*} [Group G] [Finite G] {Q T Z W : Subgroup G} {p f d : ℕ} [Fact p.Prime]
  (S : Hyp Q T Z W p f d)
include S

@[expose] noncomputable def piV : S.V →ₗ[ZMod p] S.Vp :=
  Submodule.projectionOnto S.Vp S.Zs S.isCompl_Zs_Vp.symm

@[expose] noncomputable def piZ : S.V →ₗ[ZMod p] S.Zs :=
  Submodule.projectionOnto S.Zs S.Vp S.isCompl_Zs_Vp

theorem piV_add_piZ (u : S.V) : (S.piV u : S.V) + (S.piZ u : S.V) = u := by
  rw [add_comm]
  exact Submodule.projection_add_projection_eq_self S.isCompl_Zs_Vp u

theorem piV_eq_zero_iff {u : S.V} : S.piV u = 0 ↔ u ∈ S.Zs :=
  Submodule.projectionOnto_apply_eq_zero_iff _

theorem piZ_eq_zero_iff {u : S.V} : S.piZ u = 0 ↔ u ∈ S.Vp :=
  Submodule.projectionOnto_apply_eq_zero_iff _

theorem piV_of_mem {u : S.V} (hu : u ∈ S.Vp) : S.piV u = ⟨u, hu⟩ :=
  Submodule.projectionOnto_apply_of_mem_left _ hu

theorem piZ_of_mem {u : S.V} (hu : u ∈ S.Zs) : S.piZ u = ⟨u, hu⟩ :=
  Submodule.projectionOnto_apply_of_mem_left _ hu

theorem piV_rho (t : T) (u : S.V) : S.piV (S.rho t u) = S.rhoV t (S.piV u) := by
  conv_lhs => rw [← S.piV_add_piZ u]
  rw [map_add, map_add, S.piV_of_mem (S.rho_mem_Vp t (S.piV u).2),
    S.piV_eq_zero_iff.mpr (S.rho_mem_Zs t (S.piZ u).2), add_zero]
  rfl

theorem piZ_rho (t : T) (u : S.V) : (S.piZ (S.rho t u) : S.V) = S.rho t (S.piZ u) := by
  conv_lhs => rw [← S.piV_add_piZ u]
  rw [map_add, map_add, S.piZ_eq_zero_iff.mpr (S.rho_mem_Vp t (S.piV u).2),
    S.piZ_of_mem (S.rho_mem_Zs t (S.piZ u).2), zero_add]

omit [Finite G] in
theorem bracket_mem_Zs (u v : S.V) : Baer.bracket u v ∈ S.Zs :=
  S.toB_commutator_mem_Zs _ _

omit [Finite G] in
theorem mem_center_of_mem_Zs {z : S.V} (hz : z ∈ S.Zs) :
    (Baer.ofB z : Q) ∈ Subgroup.center Q := by
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext (S.hZcent g g.2 _ hz)

omit [Finite G] in
theorem bracket_eq_zero_left {z : S.V} (hz : z ∈ S.Zs) (v : S.V) : Baer.bracket z v = 0 := by
  rw [Baer.bracket_apply, commutatorElement_eq_one_of_mem_center_left (S.mem_center_of_mem_Zs hz)]
  rfl

omit [Finite G] in
theorem bracket_eq_zero_right (u : S.V) {z : S.V} (hz : z ∈ S.Zs) : Baer.bracket u z = 0 := by
  rw [Baer.bracket_apply,
    commutatorElement_eq_one_of_mem_center_right (S.mem_center_of_mem_Zs hz)]
  rfl

theorem bracket_proj (u v : S.V) :
    Baer.bracket u v = Baer.bracket (S.piV u : S.V) (S.piV v : S.V) := by
  conv_lhs => rw [← S.piV_add_piZ u, ← S.piV_add_piZ v]
  simp only [map_add, AddMonoidHom.add_apply, S.bracket_eq_zero_left (S.piZ u).2,
    S.bracket_eq_zero_right _ (S.piZ v).2, add_zero]

omit [Finite G] in
theorem rho_bracket (t : T) (u v : S.V) :
    S.rho t (Baer.bracket u v) = Baer.bracket (S.rho t u) (S.rho t v) := by
  apply S.rho_ext
  rw [coe_ofB_rho, Baer.bracket_apply, Baer.bracket_apply, Baer.ofB_toB, Baer.ofB_toB,
    commutatorElement_def, commutatorElement_def]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_ofB_rho]
  group

omit [Finite G] in
theorem rho_of_mem_Zs {w' : G} (hw' : w' ∈ W) {z : S.V} (hz : z ∈ S.Zs) :
    S.rho ⟨w', S.hWT hw'⟩ z = z := by
  apply S.rho_ext
  rw [coe_ofB_rho]
  change w' * _ * w'⁻¹ = _
  rw [S.hWZ _ hw' _ hz]
  group

@[expose] noncomputable def iotaV : S.A →+ S.V :=
  S.Vp.subtype.toAddMonoidHom.comp S.iota.toAddMonoidHom

theorem iotaV_apply (c : S.A) : S.iotaV c = (S.iota c : S.V) := rfl

@[expose] noncomputable def beta : S.A →+ S.A →+ S.V :=
  (Baer.bracket.comp S.iotaV).compl₂ S.iotaV

theorem beta_apply (c c' : S.A) :
    S.beta c c' = Baer.bracket (S.iota c : S.V) (S.iota c' : S.V) := rfl

theorem beta_self (c : S.A) : S.beta c c = 0 := Baer.bracket_self _

theorem beta_mem_Zs (c c' : S.A) : S.beta c c' ∈ S.Zs := S.bracket_mem_Zs _ _

theorem rho_beta (t : T) (c c' : S.A) :
    S.rho t (S.beta c c') = S.beta ((S.tau t : S.A) * c) ((S.tau t : S.A) * c') := by
  rw [beta_apply, beta_apply, S.rho_bracket, S.iota_tau_mul, S.iota_tau_mul]
  rfl

@[expose] noncomputable def Omega : Subgroup S.Aˣ := (W.subgroupOf T).map S.tau

theorem card_Omega : Nat.card S.Omega * Nat.gcd (p ^ f + 1) 3 = p ^ f + 1 := by
  rw [Omega, Subgroup.card_map_of_injective S.tau_injective,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe S.hWT).toEquiv, ← S.hd, S.hWcard]

theorem beta_Omega (ω : S.Aˣ) (hω : ω ∈ S.Omega) (c c' : S.A) :
    S.beta ((ω : S.A) * c) ((ω : S.A) * c') = S.beta c c' := by
  obtain ⟨w', hw', rfl⟩ := hω
  rw [← S.rho_beta]
  exact S.rho_of_mem_Zs (w' := (w' : G)) hw' (S.beta_mem_Zs c c')

theorem beta_eq (c c' : S.A) : S.beta c c' = S.beta 1 (c ^ p ^ f * c') := by
  have := S.charP_A
  exact form_eq_conj_mul S.hpodd S.hf S.card_A S.beta S.beta_self S.Omega S.card_Omega
    S.beta_Omega c c'

end Hyp

end CFSG.UnitaryThreeRecognition.Heisenberg
