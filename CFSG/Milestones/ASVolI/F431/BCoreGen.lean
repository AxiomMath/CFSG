module

public import CFSG.Milestones.ASVolI.F4Conjugacy

public section

namespace CFSG.ASVolI

open CFSG.ASVolI.ChF CFSG.Quasithin
open scoped commutatorElement

section PerfectCore

variable {G : Type} [Group G]

theorem burnsideF4m_perfectCore_eq_of_commutator_le {H M : Subgroup G} (hHM : H ≤ M)
    (hMH : ⁅M, M⁆ ≤ H) : perfectCore M = perfectCore H := by
  refine le_antisymm ?_ (perfectCore_mono hHM)
  have key : ∀ n, derivedSeriesOf M (n + 1) ≤ derivedSeriesOf H n := by
    intro n
    induction n with
    | zero => exact hMH
    | succ n ih =>
      rw [derivedSeriesOf_succ M (n + 1), derivedSeriesOf_succ H n]
      exact Subgroup.commutator_mono ih ih
  exact le_iInf fun n => (perfectCore_le_derivedSeriesOf M (n + 1)).trans (key n)

theorem burnsideF4m_perfectCore_eq_inf {Gp : Subgroup G} (hc : ∀ a b : G, ⁅a, b⁆ ∈ Gp)
    (M : Subgroup G) : perfectCore M = perfectCore (Gp ⊓ M) := by
  refine burnsideF4m_perfectCore_eq_of_commutator_le inf_le_right ?_
  rw [Subgroup.commutator_le]
  intro a ha b hb
  refine ⟨hc a b, ?_⟩
  rw [commutatorElement_def]
  exact M.mul_mem (M.mul_mem (M.mul_mem ha hb) (M.inv_mem ha)) (M.inv_mem hb)

theorem burnsideF4m_perfectCore_map {C : Type} [Group C] (φ : C →* G)
    (hφ : Function.Injective φ) (P : Subgroup C) :
    perfectCore (P.map φ) = (perfectCore P).map φ := by
  unfold perfectCore
  rw [Subgroup.map_iInf φ hφ]
  congr 1
  funext n
  exact (map_derivedSeriesOf φ P n).symm

theorem burnsideF4m_centerOf_map {C : Type} [Group C] (φ : C →* G)
    (hφ : Function.Injective φ) (X : Subgroup C) :
    centerOf (X.map φ) = (centerOf X).map φ := by
  ext g
  constructor
  · rintro ⟨hgX, hgc⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hgX
    refine Subgroup.mem_map.mpr ⟨x, ⟨hx, ?_⟩, rfl⟩
    show x ∈ Subgroup.centralizer (X : Set C)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have := Subgroup.mem_centralizer_iff.mp hgc (φ y) (Subgroup.mem_map_of_mem φ hy)
    exact hφ (by simpa [map_mul] using this)
  · rintro hg
    obtain ⟨x, ⟨hx, hxc⟩, rfl⟩ := Subgroup.mem_map.mp hg
    refine ⟨Subgroup.mem_map_of_mem φ hx, ?_⟩
    show φ x ∈ Subgroup.centralizer ((X.map φ : Subgroup G) : Set G)
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨y, hy, rfl⟩
    have := Subgroup.mem_centralizer_iff.mp hxc y hy
    simp only [← map_mul]
    exact congrArg φ this

theorem burnsideF4m_ctr_map {C : Type} [Group C] (φ : C →* G) (hφ : Function.Injective φ)
    (X : Subgroup C) : ctr (X.map φ) = (ctr X).map φ :=
  burnsideF4m_centerOf_map φ hφ X

end PerfectCore

section Out

theorem burnsideF4m_innRange_normal (C : Type) [Group C] :
    ((MulAut.conj : C →* MulAut C).range).Normal := by
  constructor
  rintro _ ⟨x, rfl⟩ φ
  refine ⟨φ x, ?_⟩
  ext y
  simp [MulAut.conj_apply]

theorem burnsideF4m_out_comm_of_normalForm {C A : Type} [Group C] [Group A] (F : A →* MulAut C)
    (hA : ∀ σ τ : A, σ * τ = τ * σ)
    (hnf : ∀ φ : MulAut C, ∃ (g : C) (σ : A), φ = MulAut.conj g * F σ) (α β : MulAut C) :
    ⁅α, β⁆ ∈ (MulAut.conj : C →* MulAut C).range := by
  haveI := burnsideF4m_innRange_normal C
  obtain ⟨g, σ, rfl⟩ := hnf α
  obtain ⟨h, τ, rfl⟩ := hnf β
  rw [← QuotientGroup.ker_mk' (MulAut.conj : C →* MulAut C).range, MonoidHom.mem_ker,
    map_commutatorElement]
  have h1 : ∀ x : C, QuotientGroup.mk' (MulAut.conj : C →* MulAut C).range (MulAut.conj x) = 1 :=
    fun x => (QuotientGroup.eq_one_iff _).2 ⟨x, rfl⟩
  rw [map_mul, map_mul, h1, h1, one_mul, one_mul, ← map_commutatorElement,
    ← map_commutatorElement, commutatorElement_eq_one_iff_mul_comm.2 (hA σ τ), map_one, map_one]

theorem burnsideF4m_congr_conj {C D : Type} [Group C] [Group D] (e : C ≃* D) (x : C) :
    MulAut.congr e (MulAut.conj x) = MulAut.conj (e x) := by
  ext y
  simp [MulAut.conj_apply]

theorem burnsideF4m_out_transport {C D : Type} [Group C] [Group D] (e : C ≃* D)
    (h : ∀ α β : MulAut C, ⁅α, β⁆ ∈ (MulAut.conj : C →* MulAut C).range) (α β : MulAut D) :
    ⁅α, β⁆ ∈ (MulAut.conj : D →* MulAut D).range := by
  obtain ⟨g, hg⟩ := h ((MulAut.congr e).symm α) ((MulAut.congr e).symm β)
  refine ⟨e g, ?_⟩
  have h2 := congrArg (MulAut.congr e) hg
  rw [map_commutatorElement, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h2
  rw [← h2]
  exact (burnsideF4m_congr_conj e g).symm

theorem burnsideF4m_commutator_mem_of_out {E : Type} [Group E] {Gp : Subgroup E} [Gp.Normal]
    (hcen : Subgroup.centralizer (Gp : Set E) = ⊥)
    (hOut : ∀ α β : MulAut ↥Gp, ⁅α, β⁆ ∈ (MulAut.conj : ↥Gp →* MulAut ↥Gp).range) (a b : E) :
    ⁅a, b⁆ ∈ Gp := by
  obtain ⟨g, hg⟩ := hOut (burnsideF4d_rho Gp a) (burnsideF4d_rho Gp b)
  have hinj := burnsideF4d_rho_injective hcen
  have h1 : burnsideF4d_rho Gp (g : E) = MulAut.conj g := by
    refine MulEquiv.ext fun x => Subtype.ext ?_
    rw [burnsideF4d_rho_apply]
    rfl
  have h2 : burnsideF4d_rho Gp ⁅a, b⁆ = burnsideF4d_rho Gp g := by
    rw [map_commutatorElement, ← hg, h1]
  rw [hinj h2]
  exact g.2

end Out

section Core

variable {E C : Type} [Group E] [Group C] {Gp M : Subgroup E}

theorem burnsideF4m_centerOf_perfectCore_eq_map (hc : ∀ a b : E, ⁅a, b⁆ ∈ Gp) (φ : C →* E)
    (hφ : Function.Injective φ) {P : Subgroup C} (hP : Gp ⊓ M = P.map φ) :
    centerOf (perfectCore M) = (centerOf (perfectCore P)).map φ := by
  rw [burnsideF4m_perfectCore_eq_inf hc, hP, burnsideF4m_perfectCore_map φ hφ,
    burnsideF4m_centerOf_map φ hφ]

theorem burnsideF4m_core1_of_model (hc : ∀ a b : E, ⁅a, b⁆ ∈ Gp) (φ : C →* E)
    (hφ : Function.Injective φ) {P : Subgroup C} (hP : Gp ⊓ M = P.map φ)
    (hm : centerOf (perfectCore P) ≤ ctr (oPPrime 2 P)) :
    ∀ x ∈ centerOf (perfectCore M), x ≠ 1 → x * x = 1 → x ∈ ctr (oPPrime 2 (Gp ⊓ M)) := by
  intro x hx _ _
  rw [burnsideF4m_centerOf_perfectCore_eq_map hc φ hφ hP] at hx
  rw [hP, burnsideF4gD4Inv_map_oPPrime φ hφ, burnsideF4m_ctr_map φ hφ]
  exact Subgroup.map_mono hm hx

theorem burnsideF4m_centerOf_perfectCore_eq_bot_of_model (hc : ∀ a b : E, ⁅a, b⁆ ∈ Gp)
    (φ : C →* E) (hφ : Function.Injective φ) {P : Subgroup C} (hP : Gp ⊓ M = P.map φ)
    (hm : centerOf (perfectCore P) = ⊥) : centerOf (perfectCore M) = ⊥ := by
  rw [burnsideF4m_centerOf_perfectCore_eq_map hc φ hφ hP, hm, Subgroup.map_bot]

theorem burnsideF4m_inf_eq_map {D : Type} [Group D] (Ψ : D ≃* ↥Gp) {P : Subgroup D}
    (h : M.subgroupOf Gp = P.map Ψ.toMonoidHom) :
    Gp ⊓ M = P.map (Gp.subtype.comp Ψ.toMonoidHom) := by
  rw [← Subgroup.map_map, ← h, Subgroup.subgroupOf_map_subtype, inf_comm]

end Core

end CFSG.ASVolI
