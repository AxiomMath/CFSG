module

public import CFSG.Monster.B.TwoA.Amalgam.Flag1Native
public import CFSG.Monster.B.TwoA.Amalgam.Flag4
public import CFSG.Monster.B.TwoA.Amalgam.CentralExt
public import CFSG.Monster.B.Classical.MinusEight

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
  CFSG.Monster.B.TwoA.Unitary
open scoped Pointwise commutatorElement

@[expose] def psuSub : Subgroup SigmaU6 := (SemidirectProduct.inl : SUh ⧸ Zh →* SigmaU6).range

instance psuSub_normal : psuSub.Normal := by
  rw [psuSub, SemidirectProduct.range_inl_eq_ker_rightHom]
  infer_instance

@[expose] def psuSubEquiv : SUh ⧸ Zh ≃* psuSub :=
  MonoidHom.ofInjective SemidirectProduct.inl_injective

theorem isSimpleGroup_psuSub : IsSimpleGroup psuSub := by
  have : IsSimpleGroup (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU hF4 6) :=
    isSimpleGroup_unitaryPSU
  exact (psuSubEquiv.symm.trans CFSG.Monster.B.TwoA.Unitary.psiQ).isSimpleGroup

theorem natCard_psuSub : Nat.card psuSub = 9196830720 := by
  rw [← Nat.card_congr psuSubEquiv.toEquiv, natCard_quot]

theorem eleven_dvd_natCard_psuSub : 11 ∣ Nat.card psuSub := by
  rw [natCard_psuSub]
  norm_num

theorem natCard_quotient_psuSub : Nat.card (SigmaU6 ⧸ psuSub) = 2 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup psuSub
  rw [natCard_SigmaU6, natCard_psuSub] at h
  omega

abbrev OA8 : Subgroup (V8 ≃ₗ[ZMod 2] V8) := TauCeti.QuadraticMap.orthogonalGroup qForm

@[expose] def orthD : Subgroup OA8 := ⁅OA8, OA8⁆.subgroupOf OA8

theorem commutator_OA8_le : ⁅OA8, OA8⁆ ≤ OA8 :=
  Subgroup.commutator_le.2 fun g₁ h₁ g₂ h₂ => by
    rw [commutatorElement_def]
    exact OA8.mul_mem (OA8.mul_mem (OA8.mul_mem h₁ h₂) (OA8.inv_mem h₁)) (OA8.inv_mem h₂)

theorem isSimpleGroup_orthD : IsSimpleGroup orthD := by
  have := (CFSG.Monster.B.Classical.MinusEight.minus_eight_derived_flag_action_of_equivalent
    equivalent_quadMinus).1.2
  exact (Subgroup.subgroupOfEquivOfLe commutator_OA8_le).isSimpleGroup

theorem sq_mem_orthD (x : OA8) : x ^ 2 ∈ orthD := by
  have h := (CFSG.Monster.B.Classical.MinusEight.minus_eight_derived_flag_action_of_equivalent
    equivalent_quadMinus).2.1
  have h2 := Monoid.exponent_dvd_iff_forall_pow_eq_one.1 h
    (x : OA8 ⧸ ⁅OA8, OA8⁆.subgroupOf OA8)
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h2
  exact h2

theorem flag4W_lt
    (i j : Fin 3) (hij : i < j) : flag4W i < flag4W j :=
  lt_of_le_of_ne (flag4W_mono hij.le) fun h => (ne_of_lt hij) (Fin.ext (by
    have := congrArg (fun W : Submodule (ZMod 2) V8 => Module.finrank (ZMod 2) W) h
    simp only [(flag4W_mem i).1, (flag4W_mem j).1] at this
    omega))

theorem exists_orthD_flag_moves
    {M : Submodule (ZMod 2) V8} (hM1 : Module.finrank (ZMod 2) M = 1)
    (hM2 : M ≤ flag4W 1) (hMne : M ≠ flag4W 0) :
    ∃ d ∈ orthD, (flag4W 0).map (d : V8 →ₗ[ZMod 2] V8) = flag4W 0 ∧
      (flag4W 1).map (d : V8 →ₗ[ZMod 2] V8) = flag4W 1 ∧
      (flag4W 2).map (d : V8 →ₗ[ZMod 2] V8) = flag4W 2 ∧
      M.map (d : V8 →ₗ[ZMod 2] V8) ≠ M := by
  obtain ⟨L, L', hne, hset, g, hg, hg1, hg2, hg3, hgL, hgL'⟩ :=
    (CFSG.Monster.B.Classical.MinusEight.minus_eight_derived_flag_action_of_equivalent
      equivalent_quadMinus).2.2 (flag4W 0) (flag4W 1) (flag4W 2) (flag4W_lt 0 1 (by decide))
      (flag4W_lt 1 2 (by decide)) (flag4W_mem 0).1 (flag4W_mem 1).1 (flag4W_mem 2).1
      (flag4W_mem 2).2
  have hM : M ∈ ({L, L'} : Set (Submodule (ZMod 2) V8)) := hset ▸ ⟨hM1, hM2, hMne⟩
  refine ⟨⟨g, commutator_OA8_le hg⟩, hg, hg1, hg2, hg3, ?_⟩
  rcases hM with rfl | hM
  · change M.map (g : V8 →ₗ[ZMod 2] V8) ≠ M
    rw [hgL]
    exact hne.symm
  · rw [Set.mem_singleton_iff] at hM
    subst hM
    change M.map (g : V8 →ₗ[ZMod 2] V8) ≠ M
    rw [hgL']
    exact hne

@[expose] def flagStabU : Subgroup SigmaU6 := sigStab Rsp ⊓ sigStab Hsp ⊓ sigStab Tsp

@[expose] def flagStabO :
    Subgroup OA8 :=
  MulAction.stabilizer OA8 (flag4W 0) ⊓ MulAction.stabilizer OA8 (flag4W 1) ⊓
    MulAction.stabilizer OA8 (flag4W 2)

theorem mem_Bam_iff_of_mem
    {x : Dfull} {i : Fin 4} (hx : x ∈ Pc i) :
    x ∈ Bam ↔ ∀ j : Fin 4, j ≠ i → x ∈ Pc j := by
  constructor
  · exact fun h j _ => Bam_le_Pc j h
  · intro h
    refine Subgroup.mem_iInf.2 fun j => ?_
    by_cases hj : j = i
    · exact hj ▸ hx
    · exact h j hj

theorem Bam_subgroupOf_Pc0 :
    Bam.subgroupOf (Pc 0) = flagStabU.comap rhoP1 := by
  ext g
  have e1 := Subgroup.ext_iff.1 Pc_one_subgroupOf g
  have e2 := Subgroup.ext_iff.1 Pc_two_subgroupOf g
  have e3 := Subgroup.ext_iff.1 Pc_three_subgroupOf g
  rw [Subgroup.mem_subgroupOf] at e1 e2 e3
  rw [Subgroup.mem_subgroupOf, mem_Bam_iff_of_mem g.2]
  simp only [Subgroup.mem_comap, flagStabU, Subgroup.mem_inf]
  simp only [Subgroup.mem_comap] at e1 e2 e3
  constructor
  · intro h
    exact ⟨⟨e3.1 (h 3 (by decide)), e2.1 (h 2 (by decide))⟩, e1.1 (h 1 (by decide))⟩
  · rintro ⟨⟨h3, h2⟩, h1⟩ j hj
    fin_cases j
    · exact absurd rfl hj
    · exact e1.2 h1
    · exact e2.2 h2
    · exact e3.2 h3

theorem Bam_subgroupOf_P4 :
    Bam.subgroupOf P4 = flagStabO.comap p4Proj := by
  ext g
  have e : ∀ j : Fin 3, (g : Dfull) ∈ Pc j.castSucc ↔
      p4Proj g ∈ MulAction.stabilizer OA8 (flag4W j) := fun j => by
    have h := Subgroup.ext_iff.1 (flag4H_eq j) g
    rw [Subgroup.mem_comap] at h
    rw [← h, flag4H, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun hj => ⟨g.2, hj⟩, fun hj => hj.2⟩
  have e0 := e 0
  have e1 := e 1
  have e2 := e 2
  rw [Subgroup.mem_subgroupOf, mem_Bam_iff_of_mem (i := 3) g.2]
  simp only [Subgroup.mem_comap, flagStabO, Subgroup.mem_inf]
  constructor
  · intro h
    exact ⟨⟨e0.1 (h 0 (by decide)), e1.1 (h 1 (by decide))⟩, e2.1 (h 2 (by decide))⟩
  · rintro ⟨⟨h0, h1⟩, h2⟩ j hj
    fin_cases j
    · exact e0.2 h0
    · exact e1.2 h1
    · exact e2.2 h2
    · exact absurd rfl hj

theorem natCard_ker_rhoP1 :
    Nat.card rhoP1.ker = 2 ^ 22 := by
  rw [ker_rhoP1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Nc_le_Pc 0 0)).toEquiv]
  exact natCard_Nc.1

theorem isPGroup_ker_rhoP1 :
    IsPGroup 2 rhoP1.ker := IsPGroup.of_card natCard_ker_rhoP1

theorem commutator_ker_rhoP1 :
    ⁅rhoP1.ker, ⊤⁆ = rhoP1.ker := by
  apply Subgroup.map_injective (f := (Pc 0).subtype) Subtype.coe_injective
  rw [Subgroup.map_commutator, ker_rhoP1, Subgroup.subgroupOf_map_subtype, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype, inf_eq_left.2 (Nc_le_Pc 0 0), Nc_zero]
  exact commutator_N1_P1

theorem natCard_ker_p4Proj :
    Nat.card p4Proj.ker = 2 ^ 25 := by
  rw [ker_p4Proj, Nat.card_congr (Subgroup.subgroupOfEquivOfLe Lgrp_le_P4).toEquiv]
  exact natCard_Lgrp

theorem isPGroup_ker_p4Proj :
    IsPGroup 2 p4Proj.ker := IsPGroup.of_card natCard_ker_p4Proj

theorem natCard_P4_inf_Pc0 :
    Nat.card ↥(Pc 3 ⊓ Pc 0) = 111325552312320 := by
  have h := (flag4H 0).card_mul_index
  have h119 : (flag4H 0).index = 119 := (index_flag4H 0).trans natCard_singularSubspaces_qForm.1
  have hc : Nat.card (flag4H 0) = Nat.card ↥(Pc 3 ⊓ Pc 0) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : Pc 3 ⊓ Pc 0 ≤ Pc 3)).toEquiv
  rw [h119, natCard_P4, hc] at h
  omega

theorem exists_orderOf_eq_five :
    ∃ x : Dfull, x ∈ Pc 0 ∧ x ∈ P4 ∧ orderOf x = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Pc 3 ⊓ Pc 0)) 5
    (by rw [natCard_P4_inf_Pc0]; norm_num)
  exact ⟨x, x.2.2, x.2.1, by rw [← hx, Subgroup.orderOf_coe]⟩

theorem not_mem_of_isPGroup_two {H : Type*} [Group H] {S : Subgroup H} (hS : IsPGroup 2 S)
    {x : H} (hx : orderOf x = 5) : x ∉ S := by
  intro hxS
  obtain ⟨n, hn⟩ := hS ⟨x, hxS⟩
  have hxn : x ^ 2 ^ n = 1 := by
    have := congrArg Subtype.val hn
    simpa using this
  have h5 := hx ▸ orderOf_dvd_of_pow_eq_one hxn
  have h52 : 5 ∣ 2 := (Nat.prime_iff.1 (by norm_num : Nat.Prime 5)).dvd_of_dvd_pow h5
  omega

theorem ker_eq_map_of_comp {P P' M : Type*} [Group P] [Group P'] [Group M] {φ : P →* P'}
    (hφ : Function.Surjective φ) {α : P' →* M} {ρ : P →* M} (h : ∀ g, α (φ g) = ρ g) :
    α.ker = ρ.ker.map φ := by
  ext z
  obtain ⟨g, rfl⟩ := hφ z
  constructor
  · intro hz
    exact ⟨g, MonoidHom.mem_ker.2 ((h g).symm.trans (MonoidHom.mem_ker.1 hz)), rfl⟩
  · rintro ⟨g', hg', hgg'⟩
    rw [MonoidHom.mem_ker, ← hgg', h g']
    exact hg'

theorem surjective_of_comp {P P' M : Type*} [Group P] [Group P'] [Group M] {φ : P →* P'}
    {α : P' →* M} {ρ : P →* M} (h : ∀ g, α (φ g) = ρ g) (hρ : Function.Surjective ρ) :
    Function.Surjective α := fun m => by
  obtain ⟨g, rfl⟩ := hρ m
  exact ⟨φ g, h g⟩

theorem comap_eq_map_comap_of_comp {P P' M : Type*} [Group P] [Group P'] [Group M]
    {φ : P →* P'} (hφ : Function.Surjective φ) {α : P' →* M} {ρ : P →* M}
    (h : ∀ g, α (φ g) = ρ g) (S : Subgroup M) : S.comap α = (S.comap ρ).map φ := by
  have hρ : ρ = α.comp φ := MonoidHom.ext fun g => (h g).symm
  rw [hρ, ← Subgroup.comap_comap, Subgroup.map_comap_eq_self_of_surjective hφ]

theorem commutator_map_eq {P P' : Type*} [Group P] [Group P'] {φ : P →* P'}
    (hφ : Function.Surjective φ) {N : Subgroup P} (hN : ⁅N, ⊤⁆ = N) :
    ⁅N.map φ, ⊤⁆ = N.map φ := by
  rw [← Subgroup.map_top_of_surjective φ hφ, ← Subgroup.map_commutator, hN]

end CFSG.Monster.B.TwoA.Amalgam
