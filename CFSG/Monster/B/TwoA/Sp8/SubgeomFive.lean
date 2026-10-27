
module


public import CFSG.Monster.B.TwoA.Sp8.SubgeomBuilding

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA MulAction

open scoped Pointwise

attribute [local instance] parAction

@[expose] def k3S :
    K3 →* Shat := Subgroup.inclusion K3_le_Shat

@[expose, instance_reducible] def k3SetAction :
    MulAction K3 (Set ParGeom) :=
  MulAction.compHom _ k3S

theorem fixes_of_normal_of_coprime {K Ω : Type*} [Group K] [MulAction K Ω] [Finite Ω]
    [IsPretransitive K Ω] {p : ℕ} (hp : p.Prime) (hΩ : Nat.card Ω = p) (N : Subgroup K)
    [N.Normal] [Finite N] (hN : ¬ p ∣ Nat.card N) (n : N) (ω : Ω) : n • ω = ω := by
  have hB := IsBlock.orbit_of_normal (G := K) (N := N) ω
  have hdvd := hB.ncard_dvd_card ⟨ω, mem_orbit_self ω⟩
  rw [hΩ] at hdvd
  rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | h5
  · obtain ⟨a, ha⟩ := Set.ncard_eq_one.1 h1
    have hω : ω ∈ orbit N ω := mem_orbit_self ω
    have hn : n • ω ∈ orbit N ω := mem_orbit ω n
    rw [ha] at hω hn
    rw [Set.mem_singleton_iff] at hω hn
    rw [hn, hω]
  · exfalso
    apply hN
    rw [← h5, ← index_stabilizer]
    exact Subgroup.index_dvd_card _

theorem surjective_toPermHom_of_card_five {K Ω : Type*} [Group K] [Finite K] [MulAction K Ω]
    [Finite Ω] [IsPretransitive K Ω] (hΩ : Nat.card Ω = 5) (σ : K →* Equiv.Perm (Fin 5))
    (hσ : Function.Surjective σ) (hker : ¬ 5 ∣ Nat.card σ.ker) :
    Function.Surjective (toPermHom K Ω) := by
  set φ := toPermHom K Ω
  have hle : σ.ker ≤ φ.ker := fun n hn => by
    rw [MonoidHom.mem_ker]
    refine Equiv.ext fun ω => ?_
    exact fixes_of_normal_of_coprime Nat.prime_five hΩ σ.ker hker ⟨n, hn⟩ ω
  set ψ : Equiv.Perm (Fin 5) →* Equiv.Perm Ω :=
    (QuotientGroup.lift σ.ker φ hle).comp
      (QuotientGroup.quotientKerEquivOfSurjective σ hσ).symm.toMonoidHom with hψ
  have hψσ : ∀ k, ψ (σ k) = φ k := fun k => by
    rw [hψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    have : (QuotientGroup.quotientKerEquivOfSurjective σ hσ).symm (σ k) =
        (QuotientGroup.mk k : K ⧸ σ.ker) :=
      (MulEquiv.symm_apply_eq _).2 rfl
    rw [this]
    rfl
  have hrange : ψ.range = φ.range := by
    ext g
    constructor
    · rintro ⟨p, rfl⟩
      obtain ⟨k, rfl⟩ := hσ p
      exact ⟨k, (hψσ k).symm⟩
    · rintro ⟨k, rfl⟩
      exact ⟨σ k, hψσ k⟩
  have h5 : 5 ≤ Nat.card φ.range := by
    obtain ⟨ω₀⟩ : Nonempty Ω := (Nat.card_pos_iff.1 (by omega)).1
    have hs : Function.Surjective fun g : φ.range => (g : Equiv.Perm Ω) ω₀ := by
      intro ω
      obtain ⟨k, hk⟩ := exists_smul_eq K ω₀ ω
      exact ⟨⟨φ k, k, rfl⟩, hk⟩
    rw [← hΩ]
    exact Nat.card_le_card_of_surjective _ hs
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    by_contra hne
    have hnt : Nontrivial ψ.ker := (Subgroup.nontrivial_iff_ne_bot _).2 hne
    have hA := Equiv.Perm.alternatingGroup_le_of_normal (α := Fin 5) (by simp) hnt
    have hidx : ψ.ker.index ≤ 2 := by
      have h1 := Subgroup.index_dvd_of_le hA
      rw [alternatingGroup.index_eq_two] at h1
      exact Nat.le_of_dvd two_pos h1
    have : Nat.card ψ.range ≤ 2 := by
      rw [← Subgroup.index_ker]
      exact hidx
    rw [hrange] at this
    omega
  have hcard : Nat.card ψ.range = Nat.card (Equiv.Perm Ω) := by
    rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm]
    have : Fintype Ω := Fintype.ofFinite Ω
    rw [Nat.card_perm, Nat.card_perm, hΩ, Nat.card_eq_fintype_card, Fintype.card_fin]
  have htop : ψ.range = ⊤ := (Subgroup.card_eq_iff_eq_top _).1 hcard
  rw [hrange] at htop
  exact MonoidHom.range_eq_top.1 htop

attribute [local instance] k3SetAction

@[expose] def fiveConj :
    Set (Set ParGeom) :=
  {C' | (∃ s : Shat, C' = subgeomConj s) ∧ stdObj 3 (by norm_num) (by norm_num) ∈ C'}

instance finite_orbit_subgeom :
    Finite (orbit K3 subgeom) := inferInstance

attribute [local instance] k3SetAction

theorem k3_smul_set
    (k : K3) (C' : Set ParGeom) : k • C' = (k3S k • ·) '' C' := rfl

theorem k3_smul_subgeom
    (k : K3) : k • subgeom = subgeomConj (k3S k) := rfl

theorem k3S_smul_stdObj
    (k : K3) :
    k3S k • stdObj 3 (by norm_num) (by norm_num) = stdObj 3 (by norm_num) (by norm_num) := by
  apply Subtype.ext
  refine Prod.ext rfl ?_
  show conjSub (k : Dfull) (Echain 3) = Echain 3
  exact conjSub_eq_self_iff.2 k.2

theorem fiveConj_eq_orbit :
    fiveConj = orbit K3 subgeom := by
  ext C'
  constructor
  · rintro ⟨⟨s, rfl⟩, hs⟩
    obtain ⟨-, h, hh, e⟩ := mem_subgeom.1 (mem_subgeomConj_iff_inv.1 hs)
    have e' : conjSub (s : Dfull)⁻¹ E3 = conjSub h E3 := e
    have hk : (s : Dfull) * h ∈ K3 := by
      rw [← conjSub_eq_self_iff, conjSub_mul, ← e', conjSub_conjSub_inv]
    refine ⟨⟨_, hk⟩, ?_⟩
    have hks : k3S ⟨_, hk⟩ = s * ⟨h, Xgrp_le_Shat hh⟩ := Subtype.ext rfl
    show (⟨_, hk⟩ : K3) • subgeom = subgeomConj s
    rw [k3_smul_subgeom, hks, subgeomConj_mul_of_mem s hh]
  · rintro ⟨k, rfl⟩
    exact ⟨⟨k3S k, rfl⟩, stdObj 3 (by norm_num) (by norm_num), stdObj_mem_subgeom 3
      (by norm_num) (by norm_num), k3S_smul_stdObj k⟩

theorem k3_smul_subgeom_eq_iff
    (k : K3) : k • subgeom = subgeom ↔ (k : Dfull) ∈ Xgrp :=
  stab_S_iff (k3S k)

theorem stabilizer_K3_subgeom :
    stabilizer K3 subgeom = Xgrp.subgroupOf K3 := by
  ext k
  rw [mem_stabilizer_iff, Subgroup.mem_subgroupOf]
  exact k3_smul_subgeom_eq_iff k

theorem natCard_X_inf_K3 :
    Nat.card ↥(Xgrp ⊓ K3) = 138538465099776 :=
  natCard_X_inf_Kchain_three

theorem index_X_subgroupOf_K3 :
    (Xgrp.subgroupOf K3).index = 5 := by
  have h := (Xgrp.subgroupOf K3).card_mul_index
  rw [← natCard_inf_eq_subgroupOf, inf_comm, natCard_X_inf_K3, natCard_K3] at h
  omega

theorem ncard_fiveConj :
    fiveConj.ncard = 5 := by
  rw [fiveConj_eq_orbit, ← index_stabilizer, stabilizer_K3_subgeom, index_X_subgroupOf_K3]

theorem sigma3_surjective :
    Function.Surjective sigma3 := by
  obtain ⟨e, he⟩ := exists_k3QuotProd
  intro p
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (e.symm (1, p))
  refine ⟨g, ?_⟩
  have h := he g
  rw [hg, MulEquiv.apply_symm_apply] at h
  exact (congrArg Prod.snd h).symm

theorem natCard_ker_sigma3 :
    Nat.card sigma3.ker = 5772436045824 := by
  have h := Subgroup.card_mul_index sigma3.ker
  have h120 : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
    rw [Nat.card_perm, Nat.card_fin]
    rfl
  rw [Subgroup.index_ker, (MonoidHom.range_eq_top.2 sigma3_surjective), Subgroup.card_top,
    h120, natCard_K3] at h
  generalize Nat.card sigma3.ker = n at h ⊢
  omega

theorem natCard_orbit_subgeom :
    Nat.card (orbit K3 subgeom) = 5 := by
  rw [← fiveConj_eq_orbit, Nat.card_coe_set_eq, ncard_fiveConj]

theorem surjective_toPermHom_fiveConj :
    Function.Surjective (toPermHom K3 (orbit K3 subgeom)) :=
  surjective_toPermHom_of_card_five natCard_orbit_subgeom sigma3 sigma3_surjective (by
    rw [natCard_ker_sigma3]
    norm_num)

theorem short_symplectic_subgeometry_five_conjugates :
    fiveConj = {C' | (∃ s : Shat, C' = subgeomConj s) ∧
      stdObj 3 (by norm_num) (by norm_num) ∈ C'} ∧
    fiveConj.ncard = 5 ∧ subgeom ∈ fiveConj ∧
    fiveConj = orbit K3 subgeom ∧
    (∀ k : K3, k • subgeom = subgeomConj (k3S k)) ∧
    (∀ C' ∈ fiveConj, ∀ C'' ∈ fiveConj, ∃ k : K3, k • C' = C'') ∧
    Function.Surjective (toPermHom K3 (orbit K3 subgeom)) ∧
    Nonempty (Equiv.Perm (orbit K3 subgeom) ≃* Equiv.Perm (Fin 5)) ∧
    (∀ k : K3, k • subgeom = subgeom ↔ (k : Dfull) ∈ Xgrp) ∧
    stabilizer K3 subgeom = Xgrp.subgroupOf K3 ∧
    Nat.card ↥(Xgrp ⊓ K3) = 138538465099776 ∧ (Xgrp.subgroupOf K3).index = 5 := by
  refine ⟨rfl, ncard_fiveConj, ?_, fiveConj_eq_orbit, k3_smul_subgeom, ?_,
    surjective_toPermHom_fiveConj,
    ⟨Equiv.permCongrHom (Finite.equivFinOfCardEq natCard_orbit_subgeom)⟩,
    k3_smul_subgeom_eq_iff, stabilizer_K3_subgeom, natCard_X_inf_K3, index_X_subgroupOf_K3⟩
  · rw [fiveConj_eq_orbit]
    exact ⟨1, one_smul _ _⟩
  · intro C' hC' C'' hC''
    rw [fiveConj_eq_orbit] at hC' hC''
    obtain ⟨k₁, rfl⟩ := hC'
    obtain ⟨k₂, rfl⟩ := hC''
    exact ⟨k₂ * k₁⁻¹, by rw [mul_smul, inv_smul_smul]⟩

end CFSG.Monster.B.TwoA.Sp8
