module

public import CFSG.Quasithin.EmptyFaithful.SzN28PRank

public section

namespace CFSG.Quasithin.SzN28P

open Equiv

def s7_d8Set : Finset (Perm (Fin 4)) :=
  let r : Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3
  let s : Perm (Fin 4) := Equiv.swap 0 2
  {1, r, r * r, r * r * r, s, r * s, r * r * s, r * r * r * s}

theorem s7_d8Set_mul : ∀ x ∈ s7_d8Set, ∀ y ∈ s7_d8Set, x * y ∈ s7_d8Set := by decide +kernel

theorem s7_d8Set_inv : ∀ x ∈ s7_d8Set, x⁻¹ ∈ s7_d8Set := by decide +kernel

theorem s7_d8Set_card : s7_d8Set.card = 8 := by decide +kernel

def s7_D8 : Subgroup (Perm (Fin 4)) where
  carrier := (s7_d8Set : Set (Perm (Fin 4)))
  one_mem' := by
    show (1 : Perm (Fin 4)) ∈ s7_d8Set
    decide +kernel
  mul_mem' := fun {a b} ha hb => s7_d8Set_mul a ha b hb
  inv_mem' := fun {a} ha => s7_d8Set_inv a ha

theorem s7_D8_card : Nat.card s7_D8 = 8 := by
  have : Nat.card s7_D8 = Nat.card ((s7_d8Set : Set (Perm (Fin 4)))) := rfl
  rw [this, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  exact s7_d8Set_card

theorem s7_D8_isPGroup : IsPGroup 2 s7_D8 :=
  IsPGroup.of_card (n := 3) (by rw [s7_D8_card]; norm_num)

theorem s7_D8_nonabelian : ¬ IsMulCommutative ↥s7_D8 := by
  intro h
  have h1 : (Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 : Perm (Fin 4)) ∈ s7_D8 := by
    show _ ∈ (s7_d8Set : Set (Perm (Fin 4)))
    simp only [Finset.mem_coe]
    decide +kernel
  have h2 : (Equiv.swap 0 2 : Perm (Fin 4)) ∈ s7_D8 := by
    show _ ∈ (s7_d8Set : Set (Perm (Fin 4)))
    simp only [Finset.mem_coe]
    decide +kernel
  have h3 := congrArg Subtype.val (h.is_comm.comm ⟨_, h1⟩ ⟨_, h2⟩)
  simp only [Subgroup.coe_mul] at h3
  revert h3
  decide +kernel

def s7_C2 : Subgroup (Perm (Fin 3)) := Subgroup.zpowers (Equiv.swap 0 1)

theorem s7_C2_card : Nat.card s7_C2 = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [s7_C2, Nat.card_zpowers]
  exact orderOf_eq_prime (by decide +kernel) (by decide +kernel)

def s7_C3a : Subgroup (Perm (Fin 4)) := Subgroup.zpowers (Equiv.swap 0 1 * Equiv.swap 1 2)

theorem s7_C3a_card : Nat.card s7_C3a = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [s7_C3a, Nat.card_zpowers]
  exact orderOf_eq_prime (by decide +kernel) (by decide +kernel)

theorem s7_C3a_comm : ∀ x ∈ s7_C3a, ∀ y ∈ s7_C3a, x * y = y * x := fun x hx y hy =>
  congrArg Subtype.val ((Subgroup.zpowers_isMulCommutative (Equiv.swap 0 1 * Equiv.swap 1 2 :
    Perm (Fin 4))).is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

def s7_C3b : Subgroup (Perm (Fin 3)) := Subgroup.zpowers (Equiv.swap 0 1 * Equiv.swap 1 2)

theorem s7_C3b_card : Nat.card s7_C3b = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [s7_C3b, Nat.card_zpowers]
  exact orderOf_eq_prime (by decide +kernel) (by decide +kernel)

theorem s7_C3b_comm : ∀ x ∈ s7_C3b, ∀ y ∈ s7_C3b, x * y = y * x := fun x hx y hy =>
  congrArg Subtype.val ((Subgroup.zpowers_isMulCommutative (Equiv.swap 0 1 * Equiv.swap 1 2 :
    Perm (Fin 3))).is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem s7_card_perm4 : Nat.card (Perm (Fin 4)) = 24 := by
  rw [Nat.card_perm]
  simp [Nat.factorial]

theorem s7_card_perm3 : Nat.card (Perm (Fin 3)) = 6 := by
  rw [Nat.card_perm]
  simp [Nat.factorial]

theorem s7_card_perm7 : Nat.card (Perm (Fin 7)) = 5040 := by
  rw [Nat.card_perm]
  simp [Nat.factorial]

def s7_phi : Perm (Fin 4) × Perm (Fin 3) →* Perm (Fin 7) :=
  ((Equiv.permCongrHom (finSumFinEquiv : Fin 4 ⊕ Fin 3 ≃ Fin 7)).toMonoidHom).comp
    (Perm.sumCongrHom (Fin 4) (Fin 3))

theorem s7_phi_injective : Function.Injective s7_phi :=
  (Equiv.permCongrHom _).injective.comp Perm.sumCongrHom_injective

theorem s7_card_prod {G N : Type*} [Group G] [Group N] (K : Subgroup G) (L : Subgroup N) :
    Nat.card (K.prod L) = Nat.card K * Nat.card L := by
  rw [Nat.card_congr (Subgroup.prodEquiv K L).toEquiv, Nat.card_prod]

@[expose] def s7_Conf {Γ : Type*} [Group Γ] (T A B E : Subgroup Γ) : Prop :=
  T ≤ A ∧ T ≤ B ∧ T.relIndex A = 3 ∧ T.relIndex B = 3 ∧ Nat.card E = 9 ∧
    (∀ x ∈ E, x ^ 3 = 1) ∧ (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧
    ∀ x ∈ E, ∃ y ∈ A, ∃ z ∈ B, x = y * z

theorem s7_Conf.map {Γ Γ' : Type*} [Group Γ] [Group Γ'] (f : Γ →* Γ')
    (hf : Function.Injective f) {T A B E : Subgroup Γ} (h : s7_Conf T A B E) :
    s7_Conf (T.map f) (A.map f) (B.map f) (E.map f) := by
  obtain ⟨hTA, hTB, hrA, hrB, hE9, hE3, hEc, hEd⟩ := h
  refine ⟨Subgroup.map_mono hTA, Subgroup.map_mono hTB, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.relIndex_map_map_of_injective _ _ hf]
    exact hrA
  · rw [Subgroup.relIndex_map_map_of_injective _ _ hf]
    exact hrB
  · rw [Subgroup.card_map_of_injective hf]
    exact hE9
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hE3 x hx, map_one]
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hEc x hx y hy]
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := hEd x hx
    exact ⟨f y, ⟨y, hy, rfl⟩, f z, ⟨z, hz, rfl⟩, map_mul f y z⟩

theorem s7_relIndex_eq_three {Γ : Type*} [Group Γ] {T A : Subgroup Γ} (hTA : T ≤ A)
    (hT : Nat.card T = 16) (hA : Nat.card A = 48) : T.relIndex A = 3 := by
  have h := Subgroup.relIndex_mul_card T A
  rw [inf_eq_left.mpr hTA, hT, hA] at h
  omega

theorem s7_pow_three_of_card {Γ : Type*} [Group Γ] {C : Subgroup Γ} (hC : Nat.card C = 3) {u : Γ}
    (hu : u ∈ C) : u ^ 3 = 1 := by
  have := Subgroup.orderOf_dvd_natCard C hu
  rw [hC] at this
  exact orderOf_dvd_iff_pow_eq_one.mp this

theorem s7_conf0 : ∃ T A B E : Subgroup (Perm (Fin 7)), IsPGroup 2 T ∧ Nat.card T = 16 ∧
    s7_Conf T A B E := by
  have hcT : Nat.card ((s7_D8.prod s7_C2).map s7_phi) = 16 := by
    rw [Subgroup.card_map_of_injective s7_phi_injective, s7_card_prod, s7_D8_card, s7_C2_card]
  have hcA : Nat.card (((⊤ : Subgroup (Perm (Fin 4))).prod s7_C2).map s7_phi) = 48 := by
    rw [Subgroup.card_map_of_injective s7_phi_injective, s7_card_prod, Subgroup.card_top,
      s7_card_perm4, s7_C2_card]
  have hcB : Nat.card ((s7_D8.prod (⊤ : Subgroup (Perm (Fin 3)))).map s7_phi) = 48 := by
    rw [Subgroup.card_map_of_injective s7_phi_injective, s7_card_prod, Subgroup.card_top,
      s7_card_perm3, s7_D8_card]
  have hTA : (s7_D8.prod s7_C2).map s7_phi ≤
      ((⊤ : Subgroup (Perm (Fin 4))).prod s7_C2).map s7_phi :=
    Subgroup.map_mono (Subgroup.prod_mono le_top le_rfl)
  have hTB : (s7_D8.prod s7_C2).map s7_phi ≤
      (s7_D8.prod (⊤ : Subgroup (Perm (Fin 3)))).map s7_phi :=
    Subgroup.map_mono (Subgroup.prod_mono le_rfl le_top)
  refine ⟨_, _, _, (s7_C3a.prod s7_C3b).map s7_phi,
    IsPGroup.of_card (n := 4) (by rw [hcT]; norm_num), hcT, hTA, hTB,
    s7_relIndex_eq_three hTA hcT hcA, s7_relIndex_eq_three hTB hcT hcB, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective s7_phi_injective, s7_card_prod, s7_C3a_card,
      s7_C3b_card]
  · rintro _ ⟨⟨u, v⟩, ⟨hu, hv⟩, rfl⟩
    rw [← map_pow, Prod.pow_mk, s7_pow_three_of_card s7_C3a_card hu,
      s7_pow_three_of_card s7_C3b_card hv]
    exact map_one s7_phi
  · rintro _ ⟨⟨u, v⟩, ⟨hu, hv⟩, rfl⟩ _ ⟨⟨u', v'⟩, ⟨hu', hv'⟩, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Prod.ext (s7_C3a_comm u hu u' hu') (s7_C3b_comm v hv v' hv')
  · rintro _ ⟨⟨u, v⟩, ⟨hu, hv⟩, rfl⟩
    refine ⟨s7_phi (u, 1), ⟨(u, 1), ⟨Subgroup.mem_top _, one_mem _⟩, rfl⟩, s7_phi (1, v),
      ⟨(1, v), ⟨one_mem _, Subgroup.mem_top _⟩, rfl⟩, ?_⟩
    rw [← map_mul]
    simp

theorem s7_exists_conj {Γ : Type*} [Group Γ] [Finite Γ] {p : ℕ} [Fact p.Prime] {P Q : Subgroup Γ}
    (hP : IsPGroup p P) (hPi : ¬ p ∣ P.index) (hQ : IsPGroup p Q) (hQi : ¬ p ∣ Q.index) :
    ∃ g : Γ, Q = P.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ (hP.toSylow hPi) (hQ.toSylow hQi)
  refine ⟨g, ?_⟩
  have h := congrArg (fun S : Sylow p Γ => (S : Subgroup Γ)) hg
  simp only [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] at h
  rw [← h, Subgroup.pointwise_smul_def]
  rfl

theorem s7_exists_conf_perm {Q : Subgroup (Perm (Fin 7))} (hQ : IsPGroup 2 Q)
    (hQi : ¬ 2 ∣ Q.index) : ∃ A B E : Subgroup (Perm (Fin 7)), s7_Conf Q A B E := by
  obtain ⟨T, A, B, E, hT2, hTc, hconf⟩ := s7_conf0
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTi : ¬ 2 ∣ T.index := by
    have h := Subgroup.card_mul_index T
    rw [hTc, s7_card_perm7] at h
    have : T.index = 315 := by omega
    rw [this]
    norm_num
  obtain ⟨g, hg⟩ := s7_exists_conj hT2 hTi hQ hQi
  rw [hg]
  exact ⟨_, _, _, hconf.map _ (MulAut.conj g).injective⟩

theorem s7_exists_conf {Γ : Type*} [Group Γ] (e : Γ ≃* Perm (Fin 7)) {T : Subgroup Γ}
    (hT : IsPGroup 2 T) (hTi : ¬ 2 ∣ T.index) : ∃ A B E : Subgroup Γ, s7_Conf T A B E := by
  have hQ : IsPGroup 2 (T.map e.toMonoidHom) :=
    hT.of_surjective (e.toMonoidHom.subgroupMap T) (e.toMonoidHom.subgroupMap_surjective T)
  have hQi : ¬ 2 ∣ (T.map e.toMonoidHom).index := by
    have h : (T.map e.toMonoidHom).index = T.index := Subgroup.index_map_equiv T e
    rw [h]
    exact hTi
  obtain ⟨A, B, E, h⟩ := s7_exists_conf_perm hQ hQi
  have h' := h.map e.symm.toMonoidHom e.symm.injective
  have hT' : (T.map e.toMonoidHom).map e.symm.toMonoidHom = T := by
    rw [Subgroup.map_map]
    ext x
    simp
  rw [hT'] at h'
  exact ⟨_, _, _, h'⟩

theorem s7_factorization_two : Nat.factorization 5040 2 = 3 + 1 := by
  rw [Nat.factorization_def _ Nat.prime_two]
  decide +kernel

theorem s7_card_le_eight {Γ : Type*} [Group Γ] (e : Γ ≃* Perm (Fin 7)) {X : Subgroup Γ}
    (hX2 : ∀ x ∈ X, x * x = 1) (hXc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) : Nat.card X ≤ 8 := by
  have : Finite Γ := Finite.of_equiv _ e.symm.toEquiv
  have hcard : Nat.card Γ = 5040 := by
    rw [Nat.card_congr e.toEquiv, s7_card_perm7]
  have hm : (Nat.card Γ).factorization 2 = 3 + 1 := by
    rw [hcard, s7_factorization_two]
  let f : Perm (Fin 4) →* Γ := e.symm.toMonoidHom.comp (s7_phi.comp (MonoidHom.inl _ _))
  have hf : Function.Injective f := e.symm.injective.comp (s7_phi_injective.comp (fun a b hab => by
    simpa [MonoidHom.inl] using congrArg Prod.fst hab))
  obtain ⟨hP, hPn⟩ := map_nonabelian f hf s7_D8_isPGroup s7_D8_nonabelian
  have := card_le_of_elemAbelian hP hPn hX2 hXc hm
  simpa using this

end CFSG.Quasithin.SzN28P
