module

public import CFSG.RankThree.PartOne.K159H.O3Rot

public noncomputable section

namespace CFSG.RankThree.PartOne.K159H

open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
  CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.LieType.Universal.Spin
  CFSG.RankThree.OrthogonalInvolutions Module

section GroupTheory

variable {G : Type*} [Group G]

theorem conj_mem_closure {s : Set G} {g : G} (h : ∀ x ∈ s, g * x * g⁻¹ ∈ Subgroup.closure s) :
    ∀ x ∈ Subgroup.closure s, g * x * g⁻¹ ∈ Subgroup.closure s := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact h x hx
  | one => simp
  | mul a b _ _ ha hb =>
    have : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [this]
    exact mul_mem ha hb
  | inv a _ ha =>
    have : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
    rw [this]
    exact inv_mem ha

theorem mem_normalizer_closure {s : Set G} {g : G} (h1 : ∀ x ∈ s, g * x * g⁻¹ ∈ Subgroup.closure s)
    (h2 : ∀ x ∈ s, g⁻¹ * x * g ∈ Subgroup.closure s) : g ∈ Subgroup.normalizer ((Subgroup.closure s : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact conj_mem_closure h1 x
  · intro hx
    have := conj_mem_closure (g := g⁻¹) (by simpa using h2) _ hx
    have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
    rwa [e] at this

theorem commutator_sup_le {R A : Subgroup G} (hn : A ≤ Subgroup.normalizer (R : Set G))
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) : ⁅R ⊔ A, R ⊔ A⁆ ≤ R := by
  have hMN : R ⊔ A ≤ Subgroup.normalizer (R : Set G) := sup_le Subgroup.le_normalizer hn
  have hRM : R ≤ R ⊔ A := le_sup_left
  have hAM : A ≤ R ⊔ A := le_sup_right
  have hnorm : (R.subgroupOf (R ⊔ A)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hRM]
    intro h g hh hg
    exact ((Subgroup.mem_normalizer_iff.mp (hMN hg)) h).mp hh
  have hcomm : IsMulCommutative (A.subgroupOf (R ⊔ A)) :=
    ⟨⟨fun a b => Subtype.ext (Subtype.ext (hA a.1.1 a.2 b.1.1 b.2))⟩⟩
  have hsup : R.subgroupOf (R ⊔ A) ⊔ A.subgroupOf (R ⊔ A) = ⊤ := by
    apply Subgroup.map_injective (R ⊔ A).subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hRM, Subgroup.map_subgroupOf_eq_of_le hAM,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have h1 := Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup hcomm
  have h2 := Subgroup.map_mono (f := (R ⊔ A).subtype) h1
  rw [Subgroup.map_subtype_commutator, Subgroup.map_subgroupOf_eq_of_le hRM] at h2
  exact h2

end GroupTheory

abbrev VG (K : Type) [Field K] (A : Type) [AddCommGroup A] [Module K A] (r : ℕ) : Type :=
  ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)

variable {K : Type} [Field K] {A : Type} [AddCommGroup A] [Module K A] {r : ℕ} {qA : QuadraticForm K A}
  {S : Subgroup (Fin r → Kˣ)}

theorem torH_conj_mem_rootSet (d : Fin r → Kˣ) {x : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)}
    (hx : x ∈ rootSet qA S) : torH K A r d * x * (torH K A r d)⁻¹ ∈ rootSet qA S := by
  rcases hx with ⟨t, j, j', hne, hsim, rfl⟩ | ⟨j, a, hj, rfl⟩
  · rw [torH_conj_rEl]
    exact rEl_mem_rootSet hne hsim
  · rw [eichler_conj (torH_mem_orth qA d), torH_hypVec, torH_snd_zero, eichler_smul_left]
    refine Or.inr ⟨j, (wt d j : K) • a, hj, ?_⟩
    rw [Prod.smul_mk, smul_zero]

theorem Tor_le_normalizer_Rts : Tor K A r ≤ Subgroup.normalizer ((Rts qA S : Subgroup _) : Set _) := by
  rintro _ ⟨d, rfl⟩
  refine mem_normalizer_closure (fun x hx => ?_) (fun x hx => ?_)
  · exact Subgroup.subset_closure (torH_conj_mem_rootSet d hx)
  · have := torH_conj_mem_rootSet d⁻¹ hx
    rw [map_inv] at this
    simpa using Subgroup.subset_closure this

section Facts

variable [Finite K] [CharP K 2] [FiniteDimensional K A] (hreg : (polarBilin qA).Nondegenerate) (hr : 3 ≤ r)

omit [Finite K] [CharP K 2] [FiniteDimensional K A] in
theorem rot_conj_mem_rootSet {ρ : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)}
    (hρ : ρ ∈ Rot qA r) {x : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)}
    (hx : x ∈ rootSet qA S) : ρ * x * ρ⁻¹ ∈ rootSet qA S := by
  have hρO := Om_le_orth hρ.1
  rcases hx with ⟨t, j, j', hne, hsim, rfl⟩ | ⟨j, a, hj, rfl⟩
  · unfold rEl
    rw [eichler_conj hρO, hρ.2, map_smul, hρ.2]
    exact rEl_mem_rootSet hne hsim
  · rw [eichler_conj hρO, hρ.2]
    have h1 : (ρ ((0 : Fin r ⊕ Fin r → K), a)).1 = 0 := by
      funext c
      rw [rot_coord hρO hρ.2]
    refine Or.inr ⟨j, (ρ ((0 : Fin r ⊕ Fin r → K), a)).2, hj, ?_⟩
    congr 1
    exact Prod.ext h1 rfl

omit [Finite K] [CharP K 2] [FiniteDimensional K A] in
theorem Rot_le_normalizer_Rts : Rot qA r ≤ Subgroup.normalizer ((Rts qA S : Subgroup _) : Set _) := by
  intro ρ hρ
  refine mem_normalizer_closure (fun x hx => ?_) (fun x hx => ?_)
  · exact Subgroup.subset_closure (rot_conj_mem_rootSet hρ hx)
  · have := rot_conj_mem_rootSet (S := S) (inv_mem hρ) hx
    exact Subgroup.subset_closure (by simpa using this)

include hreg hr in
theorem A_comm (hdim : finrank K A = 2) :
    ∀ a ∈ Tor K A r ⊔ Rot qA r, ∀ b ∈ Tor K A r ⊔ Rot qA r, a * b = b * a := by
  have hcl : Tor K A r ⊔ Rot qA r =
      Subgroup.closure ((Tor K A r : Set (VG K A r)) ∪ (Rot qA r : Set (VG K A r))) := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
  have hpair : ((Tor K A r : Set (VG K A r)) ∪ (Rot qA r : Set (VG K A r))).Pairwise Commute := by
    intro x hx y hy _
    rcases hx with ⟨d, rfl⟩ | hx <;> rcases hy with ⟨d', rfl⟩ | hy
    · exact (by rw [← map_mul, ← map_mul, mul_comm] : torH K A r d * torH K A r d' = torH K A r d' * torH K A r d)
    · exact torH_comm_Rot d hy
    · exact (torH_comm_Rot d' hx).symm
    · exact Rot_comm hreg hr hdim hx hy
  have := Subgroup.isMulCommutative_closure hpair
  intro a ha b hb
  rw [hcl] at ha hb
  exact congrArg Subtype.val (this.is_comm.comm (⟨a, ha⟩ : Subgroup.closure _) ⟨b, hb⟩)

end Facts

end CFSG.RankThree.PartOne.K159H
