
module

public import CFSG.Sporadic.ThSchreier.AutCoreBase

public import CFSG.Sporadic.ThSchreier.Rigidity
public import CFSG.Milestones.AT_alternating_automorphism_permutation
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import Mathlib
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.Certificates.SchreierStabilizerGenerators
public import Certificates.Data.CFSGNative.Th.Certificate
public import CFSG.Sporadic.Th.Max3.Data
public import CFSG.Sporadic.ThSchreier.RigidityInputs
public meta import CFSG.Sporadic.ThSchreier.Enc8
public import CFSG.Sporadic.Th.Max3.Relations

public section

namespace CFSG.Sporadic.ThSchreier.AutCore

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3 CFSG.Sporadic.ThSchreier CFSG.Certificates
open scoped commutatorElement

structure Data
    (G : Type*) [Group G] where
  Q : Subgroup G
  normal : Q.Normal
  core : CFSG.pCore 2 G = Q
  x : G
  y : G
  gen : Subgroup.closure ({x, y} : Set G) = ⊤
  κ : G ⧸ Q ≃* alternatingGroup (Fin 9)
  κx : (κ (QuotientGroup.mk x) : Equiv.Perm (Fin 9)) = aPerm
  κy : (κ (QuotientGroup.mk y) : Equiv.Perm (Fin 9)) = bPerm
  ρ : G →* Matrix (Fin 8) (Fin 8) (ZMod 2)
  ρx : ρ x = B1
  ρy : ρ y = B2
  ρQ : ∀ m, ρ m = 1 ↔ m ∈ Q
  π : Q →* Multiplicative (Fin 8 → ZMod 2)
  π_surj : Function.Surjective π
  π_ker : ∀ g, π g = 1 ↔ g ∈ Subgroup.center Q
  π_conj : ∀ (m : G) (g : Q),
    π ⟨m * g * m⁻¹, normal.conj_mem g g.2 m⟩ =
      Multiplicative.ofAdd ((ρ m).mulVec (Multiplicative.toAdd (π g)))
  z : G
  z_mem : z ∈ Q
  z_ne_one : z ≠ 1
  z_sq : z * z = 1
  center : ∀ g : Q, g ∈ Subgroup.center Q ↔ (g : G) ∈ Subgroup.zpowers z
  z_central : ∀ m : G, z * m = m * z
  s : (Fin 8 → ZMod 2) → G
  s_mem : ∀ v, s v ∈ Q
  s_π : ∀ v, π ⟨s v, s_mem v⟩ = Multiplicative.ofAdd v
  s_comm : ∀ v w, ⁅s v, s w⁆ = z ^ (ExtraspecialNF.bil c v w).val
  Q_gen : Q = Subgroup.closure (insert z (Set.range fun j : Fin 8 => s (Pi.single j 1)))
  centralizer : ∀ m : G, (∀ g ∈ Q, m * g = g * m) → m ∈ Subgroup.zpowers z
  perfect : Group.IsPerfect G

variable {G : Type*} [Group G] (D : Data G)

namespace Data

instance : D.Q.Normal := D.normal

theorem map_Q (α : MulAut G) : D.Q.map (α : G →* G) = D.Q := by
  have h := CFSG.pCore_map_iso (G := G) (G' := G) 2 α
  rw [D.core] at h
  exact h

theorem mem_Q_iff (α : MulAut G) (m : G) : α m ∈ D.Q ↔ m ∈ D.Q := by
  constructor
  · intro hm
    rw [← D.map_Q α] at hm
    obtain ⟨m', hm', he⟩ := hm
    rw [← α.injective he]
    exact hm'
  · intro hm
    rw [← D.map_Q α]
    exact ⟨m, hm, rfl⟩

@[expose] noncomputable def autA9 (α : MulAut G) : MulAut (alternatingGroup (Fin 9)) :=
  (D.κ.symm.trans (QuotientGroup.congr D.Q D.Q α (D.map_Q α))).trans D.κ

theorem κ_aut (α : MulAut G) (m : G) :
    D.κ (QuotientGroup.mk (α m)) = D.autA9 α (D.κ (QuotientGroup.mk m)) := by
  simp [autA9]

theorem exists_κ_eq (s : alternatingGroup (Fin 9)) : ∃ n : G, D.κ (QuotientGroup.mk n) = s := by
  obtain ⟨q, hq⟩ := D.κ.surjective s
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨n, hq⟩

@[expose] noncomputable def κPerm : G →* Equiv.Perm (Fin 9) :=
  (alternatingGroup (Fin 9)).subtype.comp (D.κ.toMonoidHom.comp (QuotientGroup.mk' D.Q))

theorem κPerm_apply (m : G) :
    D.κPerm m = (D.κ (QuotientGroup.mk m) : Equiv.Perm (Fin 9)) := rfl

theorem κ_posWord (w : List ℕ) :
    (D.κ (QuotientGroup.mk (posWord D.x D.y w)) : Equiv.Perm (Fin 9)) =
      posWord aPerm bPerm w := by
  rw [← κPerm_apply, map_posWord, κPerm_apply, κPerm_apply, D.κx, D.κy]

theorem ρ_eq_of_κ_eq {m n : G} (h : D.κ (QuotientGroup.mk m) = D.κ (QuotientGroup.mk n)) :
    D.ρ m = D.ρ n := by
  have h1 := D.κ.injective h
  have h2 : n⁻¹ * m ∈ D.Q := QuotientGroup.eq.1 h1.symm
  have e : m = n * (n⁻¹ * m) := by group
  rw [e, map_mul, (D.ρQ _).2 h2, mul_one]

@[expose] noncomputable def autQ (α : MulAut G) : D.Q →* D.Q where
  toFun g := ⟨α g, (D.mem_Q_iff α g).2 g.2⟩
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

theorem autQ_apply (α : MulAut G) (g : D.Q) : (D.autQ α g : G) = α g := rfl

theorem autQ_injective (α : MulAut G) : Function.Injective (D.autQ α) := fun _ _ e =>
  Subtype.ext (α.injective (congrArg Subtype.val e))

theorem autQ_surjective [Finite D.Q] (α : MulAut G) : Function.Surjective (D.autQ α) :=
  Finite.surjective_of_injective (D.autQ_injective α)

theorem autQ_center_le [Finite D.Q] (α : MulAut G) :
    Subgroup.center D.Q ≤ (Subgroup.center D.Q).comap (D.autQ α) := by
  intro g hg
  rw [Subgroup.mem_comap, Subgroup.mem_center_iff]
  intro h
  obtain ⟨h', rfl⟩ := D.autQ_surjective α h
  rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hg) h']

theorem ker_π :
    D.π.ker = Subgroup.center D.Q := by
  ext g
  exact D.π_ker g

@[expose] noncomputable def eπ : D.Q ⧸ Subgroup.center D.Q ≃* Multiplicative (Fin 8 → ZMod 2) :=
  (QuotientGroup.quotientMulEquivOfEq D.ker_π.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective D.π D.π_surj)

theorem eπ_mk
    (g : D.Q) : D.eπ (QuotientGroup.mk g) = D.π g := rfl

theorem conj_s_basis
    (v : Fin 8 → ZMod 2) (j : Fin 8) :
    D.s v * D.s (Pi.single j 1) * (D.s v)⁻¹ =
      D.z ^ (ExtraspecialNF.bil c v (Pi.single j 1)).val * D.s (Pi.single j 1) := by
  rw [← D.s_comm, commutatorElement_def]
  group


@[expose] noncomputable def TM [Finite D.Q] (α : MulAut G) :
    Multiplicative (Fin 8 → ZMod 2) →* Multiplicative (Fin 8 → ZMod 2) :=
  D.eπ.toMonoidHom.comp ((QuotientGroup.map _ _ (D.autQ α) (D.autQ_center_le α)).comp
    D.eπ.symm.toMonoidHom)


theorem TM_π [Finite D.Q] (α : MulAut G) (g : D.Q) : D.TM α (D.π g) = D.π (D.autQ α g) := by
  rw [← eπ_mk, TM]
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
  rfl

theorem TM_surjective [Finite D.Q] (α : MulAut G) : Function.Surjective (D.TM α) := by
  intro v
  obtain ⟨g, rfl⟩ := D.π_surj v
  obtain ⟨h, rfl⟩ := D.autQ_surjective α g
  exact ⟨D.π h, D.TM_π α h⟩

@[expose] noncomputable def TLin [Finite D.Q] (α : MulAut G) :
    (Fin 8 → ZMod 2) →ₗ[ZMod 2] (Fin 8 → ZMod 2) where
  toFun v := Multiplicative.toAdd (D.TM α (Multiplicative.ofAdd v))
  map_add' v w := by
    show Multiplicative.toAdd (D.TM α (Multiplicative.ofAdd v * Multiplicative.ofAdd w)) = _
    rw [map_mul]
    rfl
  map_smul' c v := by
    rcases ExtraspecialNF.zmod_two_cases c with rfl | rfl
    · rw [zero_smul, RingHom.id_apply, zero_smul]
      show Multiplicative.toAdd (D.TM α 1) = 0
      rw [map_one]
      rfl
    · rw [one_smul, RingHom.id_apply, one_smul]

@[expose] noncomputable def TMat [Finite D.Q] (α : MulAut G) : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  LinearMap.toMatrix' (D.TLin α)

theorem TMat_mulVec [Finite D.Q] (α : MulAut G) (v : Fin 8 → ZMod 2) :
    (D.TMat α).mulVec v = Multiplicative.toAdd (D.TM α (Multiplicative.ofAdd v)) := by
  rw [TMat, LinearMap.toMatrix'_mulVec]
  rfl

theorem TMat_ne_zero [Finite D.Q] (α : MulAut G) : D.TMat α ≠ 0 := by
  intro h
  obtain ⟨v, hv⟩ := D.TM_surjective α (Multiplicative.ofAdd e0)
  have h1 := D.TMat_mulVec α (Multiplicative.toAdd v)
  rw [h, Matrix.zero_mulVec, ofAdd_toAdd, hv, toAdd_ofAdd] at h1
  have h0 : (0 : Fin 8 → ZMod 2) 0 = e0 0 := by rw [h1]
  exact absurd h0 (by decide)

theorem TMat_mul_ρ [Finite D.Q] (α : MulAut G) (m : G) :
    D.TMat α * D.ρ m = D.ρ (α m) * D.TMat α := by
  apply matrix_ext
  intro v
  obtain ⟨g, hg⟩ := D.π_surj (Multiplicative.ofAdd v)
  have hv : v = Multiplicative.toAdd (D.π g) := by rw [hg]; rfl
  have hconj : D.autQ α ⟨m * g * m⁻¹, D.normal.conj_mem g g.2 m⟩ =
      ⟨α m * (D.autQ α g) * (α m)⁻¹, D.normal.conj_mem _ (D.autQ α g).2 _⟩ := by
    ext
    simp [autQ_apply]
  have e1 : (D.ρ m).mulVec (Multiplicative.toAdd (D.π g)) =
      Multiplicative.toAdd (D.π ⟨m * g * m⁻¹, D.normal.conj_mem g g.2 m⟩) := by
    rw [D.π_conj]
    rfl
  have e2 : ∀ h : D.Q, (D.TMat α).mulVec (Multiplicative.toAdd (D.π h)) =
      Multiplicative.toAdd (D.π (D.autQ α h)) := by
    intro h
    rw [D.TMat_mulVec, ofAdd_toAdd, D.TM_π]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv, e1, e2, hconj, e2, D.π_conj]
  rfl

theorem TMat_eq_one [Finite D.Q] {α : MulAut G}
    (h : ∀ m, D.κ (QuotientGroup.mk (α m)) = D.κ (QuotientGroup.mk m)) : D.TMat α = 1 := by
  have h1 := D.TMat_mul_ρ α D.x
  have h2 := D.TMat_mul_ρ α D.y
  rw [D.ρ_eq_of_κ_eq (h D.x), D.ρx] at h1
  rw [D.ρ_eq_of_κ_eq (h D.y), D.ρy] at h2
  rcases commutant_B.1 ⟨h1, h2⟩ with h0 | h1'
  · exact absurd h0 (D.TMat_ne_zero α)
  · exact h1'

theorem not_conj_t [Finite D.Q] (α : MulAut G)
    (h : ∀ m, (D.κ (QuotientGroup.mk (α m)) : Equiv.Perm (Fin 9)) =
      tPerm * D.κ (QuotientGroup.mk m) * tPerm⁻¹) : False := by
  have hx : D.κ (QuotientGroup.mk (α D.x)) =
      D.κ (QuotientGroup.mk (posWord D.x D.y oddWord1)) := by
    apply Subtype.ext
    rw [h D.x, D.κ_posWord, oddWords_perm.1, D.κx]
  have hy : D.κ (QuotientGroup.mk (α D.y)) =
      D.κ (QuotientGroup.mk (posWord D.x D.y oddWord2)) := by
    apply Subtype.ext
    rw [h D.y, D.κ_posWord, oddWords_perm.2, D.κy]
  have h1 := D.TMat_mul_ρ α D.x
  have h2 := D.TMat_mul_ρ α D.y
  rw [D.ρ_eq_of_κ_eq hx, map_posWord, D.ρx, D.ρy, ← oddD1] at h1
  rw [D.ρ_eq_of_κ_eq hy, map_posWord, D.ρx, D.ρy, ← oddD2] at h2
  exact D.TMat_ne_zero α (intertwiner_D.1 ⟨h1, h2⟩)

theorem κ_conj (n m : G) :
    (D.κ (QuotientGroup.mk (n⁻¹ * m * n)) : Equiv.Perm (Fin 9)) =
      (D.κ (QuotientGroup.mk n) : Equiv.Perm (Fin 9))⁻¹ * D.κ (QuotientGroup.mk m) *
        D.κ (QuotientGroup.mk n) := by
  rw [← κPerm_apply, ← κPerm_apply, ← κPerm_apply, map_mul, map_mul, map_inv]

theorem exists_reduction [Finite D.Q] (α : MulAut G) :
    ∃ n : G, ∀ m, D.κ (QuotientGroup.mk (n⁻¹ * α m * n)) = D.κ (QuotientGroup.mk m) := by
  obtain ⟨σ, hσ⟩ :=
    CFSG.Milestones.alternating_automorphism_permutation (n := 9) (Or.inr (by norm_num))
      (D.autA9 α)
  have hκ : ∀ m, (D.κ (QuotientGroup.mk (α m)) : Equiv.Perm (Fin 9)) =
      σ * D.κ (QuotientGroup.mk m) * σ⁻¹ := fun m => by rw [D.κ_aut, hσ]
  by_cases hs : Equiv.Perm.sign σ = 1
  · obtain ⟨n, hn⟩ := D.exists_κ_eq ⟨σ, Equiv.Perm.mem_alternatingGroup.2 hs⟩
    refine ⟨n, fun m => Subtype.ext ?_⟩
    rw [D.κ_conj, hκ, hn]
    simp only [mul_assoc, inv_mul_cancel, mul_one]
    group
  · exfalso
    have ht : Equiv.Perm.sign tPerm = -1 := by decide
    have hst : Equiv.Perm.sign (σ * tPerm) = 1 := by
      rw [Equiv.Perm.sign_mul, ht]
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
      · exact absurd h hs
      · rw [h]; decide
    obtain ⟨n, hn⟩ := D.exists_κ_eq ⟨σ * tPerm, Equiv.Perm.mem_alternatingGroup.2 hst⟩
    refine D.not_conj_t ((MulAut.conj n⁻¹) * α) fun m => ?_
    have e : ((MulAut.conj n⁻¹) * α) m = n⁻¹ * α m * n := by
      simp
    rw [e, D.κ_conj, hκ, hn]
    have htt : tPerm⁻¹ = tPerm := by decide
    show (σ * tPerm)⁻¹ * (σ * (D.κ (QuotientGroup.mk m) : Equiv.Perm (Fin 9)) * σ⁻¹) *
      (σ * tPerm) = tPerm * D.κ (QuotientGroup.mk m) * tPerm⁻¹
    rw [mul_inv_rev, htt]
    group

theorem zpowers_z (g : G) (hg : g ∈ Subgroup.zpowers D.z) : g = 1 ∨ g = D.z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
  have h2 : D.z ^ (2 : ℤ) = 1 := by rw [zpow_two, D.z_sq]
  have e : D.z ^ k = D.z ^ (k % 2) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 2]
    rw [zpow_add, zpow_mul, h2, one_zpow, mul_one]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [e, h, zpow_zero]
  · right
    rw [e, h, zpow_one]

theorem aut_z [Finite D.Q] (α : MulAut G) : α D.z = D.z := by
  have hz : (⟨D.z, D.z_mem⟩ : D.Q) ∈ Subgroup.center D.Q :=
    (D.center _).2 (Subgroup.mem_zpowers _)
  have hc := D.autQ_center_le α hz
  rw [Subgroup.mem_comap, D.center, autQ_apply] at hc
  rcases D.zpowers_z _ hc with h | h
  · exact absurd (α.injective (h.trans (map_one α).symm)) D.z_ne_one
  · exact h

theorem exists_conj_on_Q [Finite D.Q] {α : MulAut G} (hT : D.TMat α = 1) :
    ∃ q₀ ∈ D.Q, ∀ g ∈ D.Q, α g = q₀ * g * q₀⁻¹ := by
  have hπ : ∀ g : D.Q, D.π (D.autQ α g) = D.π g := by
    intro g
    have h := D.TMat_mulVec α (Multiplicative.toAdd (D.π g))
    rw [hT, Matrix.one_mulVec, ofAdd_toAdd, D.TM_π] at h
    exact (congrArg Multiplicative.ofAdd h).symm
  have hdev : ∀ g : D.Q, α g * (g : G)⁻¹ ∈ Subgroup.zpowers D.z := by
    intro g
    have hk : D.autQ α g * g⁻¹ ∈ Subgroup.center D.Q := by
      rw [← D.π_ker, map_mul, map_inv, hπ]
      exact mul_inv_cancel _
    exact (D.center _).1 hk
  have hℓ : ∀ j : Fin 8, ∃ b : ZMod 2,
      α (D.s (Pi.single j 1)) = D.z ^ b.val * D.s (Pi.single j 1) := by
    intro j
    rcases D.zpowers_z _ (hdev ⟨_, D.s_mem (Pi.single j 1)⟩) with h | h
    · exact ⟨0, by rw [ZMod.val_zero, pow_zero, one_mul]; exact mul_inv_eq_one.1 h⟩
    · exact ⟨1, by rw [ExtraspecialNF.val_one_two, pow_one]; exact mul_inv_eq_iff_eq_mul.1 h⟩
  choose ℓ hℓ using hℓ
  refine ⟨D.s (cInv.mulVec ℓ), D.s_mem _, ?_⟩
  set q₀ := D.s (cInv.mulVec ℓ) with hq₀
  have hgen : D.Q ≤ (MonoidHom.eqLocus (α : G →* G) ((MulAut.conj q₀ : MulAut G) : G →* G)) := by
    rw [D.Q_gen, Subgroup.closure_le]
    rintro g (rfl | ⟨j, rfl⟩)
    · show α D.z = q₀ * D.z * q₀⁻¹
      rw [D.aut_z, ← D.z_central, mul_inv_cancel_right]
    · show α (D.s (Pi.single j 1)) = q₀ * D.s (Pi.single j 1) * q₀⁻¹
      rw [hℓ j, hq₀, D.conj_s_basis, bil_cInv]
  intro g hg
  exact hgen hg

theorem eq_one_of_fix_Q {β : MulAut G} (hβ : ∀ g ∈ D.Q, β g = g) : β = 1 := by
  have hcent : ∀ m : G, m⁻¹ * β m ∈ Subgroup.zpowers D.z := by
    intro m
    refine D.centralizer _ fun g hg => ?_
    have h1 : β (m * g * m⁻¹) = m * g * m⁻¹ := hβ _ (D.normal.conj_mem g hg m)
    rw [map_mul, map_mul, map_inv, hβ g hg] at h1
    calc m⁻¹ * β m * g = m⁻¹ * (β m * g * (β m)⁻¹) * β m := by group
      _ = m⁻¹ * (m * g * m⁻¹) * β m := by rw [h1]
      _ = g * (m⁻¹ * β m) := by group
  have hzc : ∀ m : G, ∀ w ∈ Subgroup.zpowers D.z, w * m = m * w := by
    intro m w hw
    rcases D.zpowers_z w hw with rfl | rfl
    · simp
    · exact D.z_central m
  let F : G →* G :=
    { toFun := fun m => m⁻¹ * β m
      map_one' := by simp
      map_mul' := fun m n => by
        have h := hzc n⁻¹ _ (hcent m)
        calc (m * n)⁻¹ * β (m * n) = n⁻¹ * (m⁻¹ * β m) * β n := by rw [map_mul]; group
          _ = m⁻¹ * β m * n⁻¹ * β n := by rw [← h]
          _ = m⁻¹ * β m * (n⁻¹ * β n) := by group }
  have hrange : F.range ≤ Subgroup.zpowers D.z := by
    rintro _ ⟨m, rfl⟩
    exact hcent m
  have hcomm : ⁅F.range, F.range⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rcases D.zpowers_z u (hrange hu) with rfl | rfl
    · simp
    · exact (D.z_central w).symm
  have hker : commutator G ≤ F.ker := by
    rw [← Subgroup.map_eq_bot_iff, map_commutator_eq, hcomm]
  rw [D.perfect.commutator_eq_top] at hker
  refine MulEquiv.ext fun m => ?_
  have hm : F m = 1 := hker (Subgroup.mem_top m)
  have : m⁻¹ * β m = 1 := hm
  rw [MulAut.one_apply]
  exact (inv_mul_eq_one.1 this).symm

theorem allInner
    [Finite D.Q] (α : MulAut G) : ∃ g : G, α = MulAut.conj g := by
  obtain ⟨n, hn⟩ := D.exists_reduction α
  set α' : MulAut G := MulAut.conj n⁻¹ * α with hα'
  have hα'apply : ∀ m, α' m = n⁻¹ * α m * n := fun m => by simp [hα']
  have hT : D.TMat α' = 1 := D.TMat_eq_one fun m => by rw [hα'apply]; exact hn m
  obtain ⟨q₀, -, hq₀⟩ := D.exists_conj_on_Q hT
  set β : MulAut G := MulAut.conj q₀⁻¹ * α' with hβ
  have hβ1 : β = 1 := D.eq_one_of_fix_Q fun g hg => by
    simp only [hβ, MulAut.mul_apply, MulAut.conj_apply, hq₀ g hg, inv_inv]
    group
  refine ⟨n * q₀, MulEquiv.ext fun m => ?_⟩
  have h1 : β m = m := by rw [hβ1]; rfl
  simp only [hβ, MulAut.mul_apply, MulAut.conj_apply, inv_inv] at h1
  rw [hα'apply] at h1
  rw [MulAut.conj_apply]
  calc α m = n * (q₀ * (q₀⁻¹ * (n⁻¹ * α m * n) * q₀) * q₀⁻¹) * n⁻¹ := by group
    _ = n * q₀ * m * (n * q₀)⁻¹ := by rw [h1]; group

end Data

end CFSG.Sporadic.ThSchreier.AutCore
