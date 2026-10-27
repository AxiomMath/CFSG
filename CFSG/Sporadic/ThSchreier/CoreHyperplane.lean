
module

public import CFSG.Sporadic.ThSchreier.CoreHyperplaneBase1

public import CFSG.Sporadic.ThSchreier.NoTransvection
public import CFSG.Sporadic.ThSchreier.Max3Aut
public import Mathlib
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.Certificates.SchreierStabilizerGenerators
public import Certificates.Data.CFSGNative.Th.Certificate
public import CFSG.Sporadic.Th.Max3.Core
public import CFSG.Sporadic.Th.Max3.AltNine
public import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalCarmichael
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.Sporadic.Th.Max3.QuotientInputs
public import CFSG.Sporadic.Th.Max3.Data
public import CFSG.Sporadic.ThSchreier.NoTransvectionInputs
public meta import CFSG.Sporadic.ThSchreier.Rigidity

public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3 CFSG.Certificates Matrix

theorem perp_perp {a b : Fin 8 → ZMod 2} (ha : a ≠ 0) (h : ∀ v, a ⬝ᵥ v = 0 → b ⬝ᵥ v = 0) :
    b = 0 ∨ b = a := by
  obtain ⟨j, hj⟩ := exists_eq_one_of_ne_zero ha
  have key : ∀ i, b i = a i * b j := by
    intro i
    by_cases hij : i = j
    · rw [hij, hj, one_mul]
    · have hv := h (Pi.single i 1 + a i • Pi.single j 1) (by
        rw [dotProduct_add, dotProduct_smul, dotProduct_single_one, dotProduct_single_one, hj,
          smul_eq_mul, mul_one, zmod2_add_self])
      rw [dotProduct_add, dotProduct_smul, dotProduct_single_one, dotProduct_single_one,
        smul_eq_mul] at hv
      calc b i = b i + (b i + a i * b j) := by rw [hv, add_zero]
        _ = a i * b j := by rw [← add_assoc, zmod2_add_self, zero_add]
  rcases ExtraspecialNF.zmod_two_cases (b j) with h0 | h1
  · left
    funext i
    rw [key, h0, mul_zero]
    rfl
  · right
    funext i
    rw [key, h1, mul_one]

@[expose] noncomputable def qv
    (g : Q) : Fin 8 → ZMod 2 := Multiplicative.toAdd (piQ g)

theorem z_pow_mem_center
    (k : ℕ) (h : z ^ k ∈ Q) : (⟨z ^ k, h⟩ : Q) ∈ Subgroup.center Q := by
  rw [center_Q, Subgroup.mem_subgroupOf]
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers z) k

theorem qv_nf
    (s : ZMod 2) (v : Fin 8 → ZMod 2) : qv ⟨nf s v, nf_mem_Q s v⟩ = v := by
  have hz : z ^ s.val ∈ Q := Subgroup.pow_mem _ z_mem_Q _
  have e : (⟨nf s v, nf_mem_Q s v⟩ : Q) = ⟨z ^ s.val, hz⟩ * ⟨nf 0 v, nf_mem_Q 0 v⟩ := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mk, Subgroup.coe_mk, Subgroup.coe_mk]
    exact nf_eq_mul s v
  rw [qv, e, map_mul, (piQ_eq_one_iff _).2 (z_pow_mem_center _ hz), one_mul, piQ_nf]
  rfl

theorem comm_iff
    {g h : J} (hg : g ∈ Q) (hh : h ∈ Q) :
    g * h = h * g ↔ ExtraspecialNF.bil c (qv ⟨g, hg⟩) (qv ⟨h, hh⟩) = 0 := by
  obtain ⟨s, v, rfl⟩ := mem_Q_iff.1 hg
  obtain ⟨t, w, rfl⟩ := mem_Q_iff.1 hh
  rw [qv_nf, qv_nf]
  have hc := ExtraspecialNF.commutator_eq_zpow symplectic_rel (fun i j => c_symm j i) c_diag s t
    v w
  rw [← nf_eq_generic, ← nf_eq_generic] at hc
  rw [← commutatorElement_eq_one_iff_mul_comm, hc]
  rcases ExtraspecialNF.zmod_two_cases (ExtraspecialNF.bil c v w) with h0 | h1
  · rw [h0, ZMod.val_zero, pow_zero]
    exact ⟨fun _ => rfl, fun _ => rfl⟩
  · rw [h1, ExtraspecialNF.val_one_two, pow_one]
    exact ⟨fun h => absurd h z_ne_one, fun h => absurd h (by decide)⟩

theorem qv_eq_zero_iff
    (g : Q) : qv g = 0 ↔ (g : J) ∈ Subgroup.zpowers z := by
  rw [← Subgroup.mem_subgroupOf, ← center_Q, ← piQ_eq_one_iff]
  constructor
  · intro h
    exact (congrArg Multiplicative.ofAdd h).trans ofAdd_zero
  · intro h
    exact (congrArg Multiplicative.toAdd h).trans toAdd_one

theorem max3Data_ρ
    (m : ↥M) : max3Data.ρ m = rhoMat m := rfl

theorem centralizer_centralizer_le
    {q : J} (hq : q ∈ Q) (hqz : q ∉ Subgroup.zpowers z)
    {m : J} (hmc : ∀ h ∈ Q, h * q = q * h → h * m = m * h) (hmM : m ∈ M) :
    m ∈ Subgroup.closure {z, q} := by
  have hu : qv ⟨q, hq⟩ ≠ 0 := fun h => hqz ((qv_eq_zero_iff _).1 h)
  set u := qv ⟨q, hq⟩
  have hℓ : Matrix.of c *ᵥ u ≠ 0 := fun h =>
    hu (c_mulVec_injective (h.trans (Matrix.mulVec_zero _).symm))
  have hcomm : ∀ v, (Matrix.of c *ᵥ u) ⬝ᵥ v = 0 → nf 0 v * m = m * nf 0 v := by
    intro v hv
    refine hmc _ (nf_mem_Q 0 v) ((comm_iff (nf_mem_Q 0 v) hq).2 ?_)
    rw [qv_nf, bil_eq_dot]
    exact hv
  have hfix : ∀ v, (Matrix.of c *ᵥ u) ⬝ᵥ v = 0 → max3Data.ρ ⟨m, hmM⟩ *ᵥ v = v := by
    intro v hv
    rw [max3Data_ρ, rhoMat_mulVec, ← piQ_nf v, rhoM_piQ]
    have e : conjQ ⟨m, hmM⟩ ⟨nf 0 v, nf_mem_Q 0 v⟩ = ⟨nf 0 v, nf_mem_Q 0 v⟩ := by
      apply Subtype.ext
      rw [conjQ_apply]
      show m * nf 0 v * m⁻¹ = nf 0 v
      rw [← hcomm v hv, mul_inv_cancel_right]
    rw [e, piQ_nf]
    rfl
  have hρ := max3Data.rho_eq_one_of_fix ⟨m, hmM⟩ hℓ hfix
  rw [max3Data_ρ] at hρ
  have hmQ : m ∈ Q := (rhoMat_eq_one_iff _).1 hρ
  have hperp : ∀ v, (Matrix.of c *ᵥ u) ⬝ᵥ v = 0 →
      (Matrix.of c *ᵥ qv ⟨m, hmQ⟩) ⬝ᵥ v = 0 := by
    intro v hv
    have h1 := (comm_iff hmQ (nf_mem_Q 0 v)).1 (hcomm v hv).symm
    rwa [qv_nf, bil_eq_dot'] at h1
  rcases perp_perp hℓ hperp with h0 | h1
  · have hw : qv ⟨m, hmQ⟩ = 0 := c_mulVec_injective (h0.trans (Matrix.mulVec_zero _).symm)
    have hz := (qv_eq_zero_iff _).1 hw
    exact Subgroup.zpowers_le.2 (Subgroup.subset_closure (Set.mem_insert _ _)) hz
  · have hw : qv ⟨m, hmQ⟩ = u := c_mulVec_injective h1
    have hmq : m * q⁻¹ ∈ Q := Q.mul_mem hmQ (Q.inv_mem hq)
    have hq0 : qv ⟨m * q⁻¹, hmq⟩ = 0 := by
      have e : (⟨m * q⁻¹, hmq⟩ : Q) = ⟨m, hmQ⟩ * (⟨q, hq⟩ : Q)⁻¹ := rfl
      rw [qv, e, map_mul, map_inv, toAdd_mul, toAdd_inv]
      change qv ⟨m, hmQ⟩ + -u = 0
      rw [hw]
      exact add_neg_cancel u
    have hz := (qv_eq_zero_iff _).1 hq0
    have e : m = m * q⁻¹ * q := by group
    rw [e]
    exact Subgroup.mul_mem _
      (Subgroup.zpowers_le.2 (Subgroup.subset_closure (Set.mem_insert _ _)) hz)
      (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))

theorem closure_le_centralizer
    {q : J} (hq : q ∈ Q) :
    Subgroup.closure {z, q} ≤
      Subgroup.centralizer ((Subgroup.centralizer {q} ⊓ M : Subgroup J) : Set J) ⊓
        (Subgroup.centralizer {q} ⊓ M) := by
  rw [Subgroup.closure_le]
  rintro g (rfl | rfl)
  · refine ⟨Subgroup.mem_centralizer_iff.2 fun h hh => ?_,
      Subgroup.mem_centralizer_singleton_iff.2 ?_, z_mem_M⟩
    · exact (commute_z_of_mem_M hh.2).eq.symm
    · exact (commute_z_of_mem_M (Q_le_M hq)).eq
  · refine ⟨Subgroup.mem_centralizer_iff.2 fun h hh => ?_,
      Subgroup.mem_centralizer_singleton_iff.2 rfl, Q_le_M hq⟩
    exact Subgroup.mem_centralizer_singleton_iff.1 hh.1

theorem ctuc_Th_core_hyperplane_centralizers
    (q : J) (hq : q ∈ Q)
    (hqZ : (⟨q, hq⟩ : Q) ∉ Subgroup.center Q) :
    Subgroup.centralizer ((Subgroup.centralizer {q} ⊓ Q : Subgroup J) : Set J) ⊓ M =
      Subgroup.closure {z, q} ∧
    Subgroup.centralizer ((Subgroup.centralizer {q} ⊓ M : Subgroup J) : Set J) ⊓
      (Subgroup.centralizer {q} ⊓ M) = Subgroup.closure {z, q} := by
  have hqz : q ∉ Subgroup.zpowers z := by
    rw [center_Q, Subgroup.mem_subgroupOf] at hqZ
    exact hqZ
  have hle := closure_le_centralizer hq
  constructor
  · apply le_antisymm
    · intro m hm
      obtain ⟨hmc, hmM⟩ := hm
      refine centralizer_centralizer_le hq hqz (fun h hh hhq => ?_) hmM
      exact Subgroup.mem_centralizer_iff.1 hmc h
        ⟨Subgroup.mem_centralizer_singleton_iff.2 hhq, hh⟩
    · intro g hg
      obtain ⟨hgc, -, hgM⟩ := hle hg
      refine ⟨Subgroup.mem_centralizer_iff.2 fun h hh => ?_, hgM⟩
      exact Subgroup.mem_centralizer_iff.1 hgc h ⟨hh.1, Q_le_M hh.2⟩
  · apply le_antisymm _ hle
    intro m hm
    obtain ⟨hmc, -, hmM⟩ := hm
    refine centralizer_centralizer_le hq hqz (fun h hh hhq => ?_) hmM
    exact Subgroup.mem_centralizer_iff.1 hmc h
      ⟨Subgroup.mem_centralizer_singleton_iff.2 hhq, Q_le_M hh⟩

end CFSG.Sporadic.ThSchreier
