module

public import CFSG.Monster.B.TwoA.Base.PairStab
public import CFSG.Sporadic.Mathieu.M22

public section

namespace CFSG.Monster.B.TwoA

open CFSG.Monster.Code MulAction CFSG.Sporadic.Mathieu

@[expose] def jCat : Fin 22 → Fin 24 :=
  ![2, 3, 4, 16, 21, 22, 17, 13, 12, 5, 9, 8, 10, 23, 19, 11, 14, 6, 20, 7, 18, 15]

@[expose] def jSplit : Fin 24 ≃ Fin 2 ⊕ Fin 22 where
  toFun := ![.inl 0, .inl 1, .inr 0, .inr 1, .inr 2, .inr 9, .inr 17, .inr 19, .inr 11, .inr 10,
    .inr 12, .inr 15, .inr 8, .inr 7, .inr 16, .inr 21, .inr 3, .inr 6, .inr 20, .inr 14, .inr 18,
    .inr 4, .inr 5, .inr 13]
  invFun := Sum.elim ![0, 1] jCat
  left_inv := by decide
  right_inv := by decide

theorem jSplit_jCat : ∀ i : Fin 22, jSplit (jCat i) = .inr i := by decide

theorem jCat_injective : Function.Injective jCat := by decide

theorem jCat_ne : ∀ i : Fin 22, jCat i ≠ 0 ∧ jCat i ≠ 1 := by decide

theorem exists_jCat : ∀ m : Fin 24, m ≠ 0 → m ≠ 1 → ∃ i, jCat i = m := by decide

@[expose] def psiFun (g : Equiv.Perm (Fin 22)) : Equiv.Perm (Fin 24) :=
  (jSplit.trans (Equiv.sumCongr (Equiv.refl (Fin 2)) g)).trans jSplit.symm

@[expose] def psiHom : Equiv.Perm (Fin 22) →* Equiv.Perm (Fin 24) where
  toFun := psiFun
  map_one' := Equiv.ext fun x => by
    simp only [psiFun, Equiv.trans_apply, Equiv.Perm.one_apply]
    cases h : jSplit x <;> simp [← h]
  map_mul' g h := Equiv.ext fun x => by
    simp only [psiFun, Equiv.trans_apply, Equiv.Perm.mul_apply, Equiv.apply_symm_apply]
    cases jSplit x <;> rfl

theorem psiHom_zero (g : Equiv.Perm (Fin 22)) : psiHom g 0 = 0 := rfl

theorem psiHom_one (g : Equiv.Perm (Fin 22)) : psiHom g 1 = 1 := rfl

theorem psiHom_jCat (g : Equiv.Perm (Fin 22)) (i : Fin 22) : psiHom g (jCat i) = jCat (g i) := by
  change jSplit.symm (Equiv.sumCongr (Equiv.refl (Fin 2)) g (jSplit (jCat i))) = jCat (g i)
  rw [jSplit_jCat]
  rfl

theorem psiHom_injective : Function.Injective psiHom := by
  intro g h hgh
  refine Equiv.ext fun i => jCat_injective ?_
  rw [← psiHom_jCat, ← psiHom_jCat, hgh]

@[expose] def mogA : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 10, 13, 11, 12, 6, 7, 16, 23, 2, 4, 5, 3, 17, 22, 8, 14, 18, 19, 20, 21, 15, 9]
  invFun := ![0, 1, 10, 13, 11, 12, 6, 7, 16, 23, 2, 4, 5, 3, 17, 22, 8, 14, 18, 19, 20, 21, 15, 9]
  left_inv := by decide
  right_inv := by decide

@[expose] def mogB : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 15, 6, 18, 13, 16, 5, 21, 17, 3, 11, 12, 23, 20, 4, 10, 19, 2, 22, 14, 8, 9, 7]
  invFun := ![0, 1, 18, 10, 15, 7, 3, 23, 21, 22, 16, 11, 12, 5, 20, 2, 6, 9, 4, 17, 14, 8, 19, 13]
  left_inv := by decide
  right_inv := by decide

theorem psi_m22gA : psiHom m22gA = mogA := by
  ext x
  revert x
  decide

theorem psi_m22gB : psiHom m22gB = mogB := by
  ext x
  revert x
  decide

theorem mogA_mem : mogA ∈ AutPerm := mem_AutPerm_of_basis (by decide +kernel) (by decide +kernel)

theorem mogB_mem : mogB ∈ AutPerm := mem_AutPerm_of_basis (by decide +kernel) (by decide +kernel)

theorem psiHom_mem_AutPerm {g : Equiv.Perm (Fin 22)} (hg : g ∈ CFSG.Blueprint.NativeSporadic.M22) :
    psiHom g ∈ AutPerm := by
  have h : CFSG.Blueprint.NativeSporadic.M22 ≤ AutPerm.comap psiHom := by
    rw [m22_eq, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · rw [SetLike.mem_coe, Subgroup.mem_comap, psi_m22gA]; exact mogA_mem
    · rw [SetLike.mem_coe, Subgroup.mem_comap, psi_m22gB]; exact mogB_mem
  exact h hg

@[expose] def P0 : Subgroup AutPerm := MulAction.stabilizer AutPerm ((0, 1) : Fin 24 × Fin 24)

theorem mem_P0_iff (p : AutPerm) :
    p ∈ P0 ↔ (p : Equiv.Perm (Fin 24)) 0 = 0 ∧ (p : Equiv.Perm (Fin 24)) 1 = 1 := by
  rw [P0, MulAction.mem_stabilizer_iff, Prod.smul_mk, Prod.mk.injEq]
  rfl

theorem P0_le_Ppair : P0 ≤ Ppair := fun p hp =>
  mem_Ppair_of_fix p ((mem_P0_iff p).1 hp).1 ((mem_P0_iff p).1 hp).2

theorem orbit_zero_one :
    MulAction.orbit AutPerm ((0, 1) : Fin 24 × Fin 24) = {x | x.1 ≠ x.2} := by
  ext ⟨u, v⟩
  constructor
  · rintro ⟨p, hp⟩
    change p • ((0 : Fin 24), (1 : Fin 24)) = (u, v) at hp
    rw [Prod.smul_mk, Prod.mk.injEq] at hp
    rw [← hp.1, ← hp.2]
    exact (p : Equiv.Perm (Fin 24)).injective.ne (by decide)
  · intro huv
    obtain ⟨p, hp, h0, h1⟩ := autPerm_maps_two u v huv
    refine ⟨⟨p, hp⟩, ?_⟩
    change (⟨p, hp⟩ : AutPerm) • ((0 : Fin 24), (1 : Fin 24)) = (u, v)
    rw [Prod.smul_mk, Prod.mk.injEq]
    exact ⟨h0, h1⟩

theorem ncard_offDiag : ({x | x.1 ≠ x.2} : Set (Fin 24 × Fin 24)).ncard = 552 := by
  rw [show ({x | x.1 ≠ x.2} : Set (Fin 24 × Fin 24)) =
    ↑(Finset.univ : Finset (Fin 24)).offDiag by ext; simp, Set.ncard_coe_finset,
    Finset.offDiag_card, Finset.card_univ, Fintype.card_fin]

theorem natCard_P0 : Nat.card P0 = 443520 := by
  have h1 := Subgroup.index_mul_card P0
  rw [P0, MulAction.index_stabilizer, orbit_zero_one, ncard_offDiag, card_AutPerm] at h1
  rw [P0]
  omega

@[expose] def psiM : CFSG.Blueprint.NativeSporadic.M22 →* AutPerm :=
  (psiHom.comp CFSG.Blueprint.NativeSporadic.M22.subtype).codRestrict AutPerm
    fun g => psiHom_mem_AutPerm g.2

theorem coe_psiM (g : CFSG.Blueprint.NativeSporadic.M22) :
    ((psiM g : AutPerm) : Equiv.Perm (Fin 24)) = psiHom g := rfl

theorem psiM_injective : Function.Injective psiM := fun _ _ hgh =>
  Subtype.ext (psiHom_injective (congrArg Subtype.val hgh))

theorem range_psiM :
    psiM.range = P0 := by
  have hle : psiM.range ≤ P0 := by
    rintro _ ⟨g, rfl⟩
    exact (mem_P0_iff _).2 ⟨psiHom_zero g, psiHom_one g⟩
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [natCard_P0, ← Nat.card_congr (MonoidHom.ofInjective psiM_injective).toEquiv, card_M22]

@[expose] noncomputable def m22EquivP0 :
    CFSG.Blueprint.NativeSporadic.M22 ≃* P0 :=
  (MonoidHom.ofInjective psiM_injective).trans (MulEquiv.subgroupCongr range_psiM)

theorem coe_m22EquivP0
    (g : CFSG.Blueprint.NativeSporadic.M22) :
    (((m22EquivP0 g : P0) : AutPerm) : Equiv.Perm (Fin 24)) = psiHom g := rfl

@[expose] def P0in : Subgroup Ppair := P0.subgroupOf Ppair

theorem natCard_P0in : Nat.card P0in = 443520 := by
  rw [P0in, Nat.card_congr (Subgroup.subgroupOfEquivOfLe P0_le_Ppair).toEquiv, natCard_P0]

theorem index_P0in : P0in.index = 2 := by
  have h := P0in.card_mul_index
  rw [natCard_P0in, natCard_Ppair] at h
  omega

instance P0in_normal :
    P0in.Normal := Subgroup.normal_of_index_eq_two index_P0in

theorem P0_maps_two
    (a b : Fin 24) (ha0 : a ≠ 0) (ha1 : a ≠ 1) (hb0 : b ≠ 0) (hb1 : b ≠ 1)
    (hab : a ≠ b) :
    ∃ p ∈ P0, (p : Equiv.Perm (Fin 24)) 2 = a ∧ (p : Equiv.Perm (Fin 24)) 3 = b := by
  obtain ⟨p, hp, h0, h1, h2, h3⟩ := autPerm_maps_four 0 1 a b (by decide) (Ne.symm ha0)
    (Ne.symm hb0) (Ne.symm ha1) (Ne.symm hb1) hab
  exact ⟨⟨p, hp⟩, (mem_P0_iff _).2 ⟨h0, h1⟩, h2, h3⟩

theorem P0_maps_fix
    (a b c : Fin 24) (ha0 : a ≠ 0) (ha1 : a ≠ 1) (hb0 : b ≠ 0) (hb1 : b ≠ 1)
    (hc0 : c ≠ 0) (hc1 : c ≠ 1) (hab : a ≠ b) (hac : a ≠ c) :
    ∃ p ∈ P0, (p : Equiv.Perm (Fin 24)) a = a ∧ (p : Equiv.Perm (Fin 24)) b = c := by
  obtain ⟨p, hp, p2, p3⟩ := P0_maps_two a b ha0 ha1 hb0 hb1 hab
  obtain ⟨q, hq, q2, q3⟩ := P0_maps_two a c ha0 ha1 hc0 hc1 hac
  refine ⟨q * p⁻¹, P0.mul_mem hq (P0.inv_mem hp), ?_, ?_⟩
  · change (q : Equiv.Perm (Fin 24)) ((p : Equiv.Perm (Fin 24))⁻¹ a) = a
    have e : (p : Equiv.Perm (Fin 24))⁻¹ a = 2 := by
      rw [← p2]; exact Equiv.symm_apply_apply _ _
    rw [e, q2]
  · change (q : Equiv.Perm (Fin 24)) ((p : Equiv.Perm (Fin 24))⁻¹ b) = c
    have e : (p : Equiv.Perm (Fin 24))⁻¹ b = 3 := by
      rw [← p3]; exact Equiv.symm_apply_apply _ _
    rw [e, q3]

theorem centralizer_P0 :
    Subgroup.centralizer (P0in : Set Ppair) = ⊥ := by
  rw [eq_bot_iff]
  intro c hc
  rw [Subgroup.mem_bot]
  have hcomm : ∀ p : AutPerm, p ∈ P0 → ∀ i : Fin 24,
      ((c : AutPerm) : Equiv.Perm (Fin 24)) ((p : Equiv.Perm (Fin 24)) i) =
        (p : Equiv.Perm (Fin 24)) (((c : AutPerm) : Equiv.Perm (Fin 24)) i) := by
    intro p hp i
    have h := Subgroup.mem_centralizer_iff.1 hc ⟨p, P0_le_Ppair hp⟩ (by
      rw [SetLike.mem_coe, P0in, Subgroup.mem_subgroupOf]; exact hp)
    have h' := congrArg (fun x : Ppair => ((x : AutPerm) : Equiv.Perm (Fin 24)) i) h
    exact h'.symm
  refine eq_one_of_fix_rest fun i => Subtype.ext ?_
  change ((c : AutPerm) : Equiv.Perm (Fin 24)) i = i
  by_contra hne
  obtain ⟨i, hi0, hi1⟩ := i
  set ci := ((c : AutPerm) : Equiv.Perm (Fin 24)) i with hci
  have hc0 : ci ≠ 0 := (Ppair_apply_ne c.2 hi0 hi1).1
  have hc1 : ci ≠ 1 := (Ppair_apply_ne c.2 hi0 hi1).2
  obtain ⟨t, ht0, ht1, hti, htc⟩ : ∃ t : Fin 24, t ≠ 0 ∧ t ≠ 1 ∧ t ≠ i ∧ t ≠ ci := by
    by_contra h
    push Not at h
    have : ∀ t : Fin 24, t = 0 ∨ t = 1 ∨ t = i ∨ t = ci := by
      intro t
      by_cases h0 : t = 0
      · exact .inl h0
      by_cases h1 : t = 1
      · exact .inr (.inl h1)
      by_cases h2 : t = i
      · exact .inr (.inr (.inl h2))
      exact .inr (.inr (.inr (h t h0 h1 h2)))
    have hcard : (Finset.univ : Finset (Fin 24)) ⊆ {0, 1, i, ci} := fun t _ => by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact this t
    have := Finset.card_le_card hcard
    rw [Finset.card_univ, Fintype.card_fin] at this
    have h4 := Finset.card_le_four (a := (0 : Fin 24)) (b := 1) (c := i) (d := ci)
    omega
  obtain ⟨p, hp, hpi, hpc⟩ := P0_maps_fix i ci t hi0 hi1 hc0 hc1 ht0 ht1 (Ne.symm hne)
    (Ne.symm hti)
  have := hcomm p hp i
  rw [hpi, hpc] at this
  exact htc this.symm

@[expose] noncomputable def P0inEquiv :
    P0in ≃* CFSG.Blueprint.NativeSporadic.M22 :=
  (Subgroup.subgroupOfEquivOfLe P0_le_Ppair).trans m22EquivP0.symm

@[expose] noncomputable def autEmbed :
    Ppair →* MulAut CFSG.Blueprint.NativeSporadic.M22 :=
  (MulAut.congr P0inEquiv).toMonoidHom.comp (MulAut.conjNormal (H := P0in))

theorem autEmbed_injective :
    Function.Injective autEmbed := by
  rw [injective_iff_map_eq_one]
  intro c hc
  have hc' : MulAut.conjNormal (H := P0in) c = 1 := by
    have : autEmbed c = (MulAut.congr P0inEquiv).toMonoidHom 1 := by rw [hc, map_one]
    exact (MulAut.congr P0inEquiv).injective this
  have hcen : c ∈ Subgroup.centralizer (P0in : Set Ppair) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have := congrArg (fun f : MulAut P0in => ((f ⟨h, hh⟩ : P0in) : Ppair)) hc'
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  rw [centralizer_P0] at hcen
  exact hcen

theorem native_pair_stabilizer_catalog_M22_embedding :
    Function.Injective jCat ∧ (∀ m : Fin 24, (m ≠ 0 ∧ m ≠ 1) ↔ ∃ i, jCat i = m) ∧
    (∀ g : Equiv.Perm (Fin 22), psiHom g 0 = 0 ∧ psiHom g 1 = 1 ∧
      ∀ i, psiHom g (jCat i) = jCat (g i)) ∧
    (∃ e : CFSG.Blueprint.NativeSporadic.M22 ≃* P0, ∀ g,
      (((e g : P0) : AutPerm) : Equiv.Perm (Fin 24)) = psiHom g) ∧
    P0 ≤ Ppair ∧ P0in.Normal ∧ P0in.index = 2 ∧
    Subgroup.centralizer (P0in : Set Ppair) = ⊥ ∧
    Function.Injective autEmbed ∧ Nat.card autEmbed.range = 887040 := by
  refine ⟨jCat_injective, fun m => ⟨fun h => exists_jCat m h.1 h.2, ?_⟩,
    fun g => ⟨psiHom_zero g, psiHom_one g, psiHom_jCat g⟩, ⟨m22EquivP0, coe_m22EquivP0⟩,
    P0_le_Ppair, inferInstance, index_P0in, centralizer_P0, autEmbed_injective, ?_⟩
  · rintro ⟨i, rfl⟩
    exact jCat_ne i
  · rw [← Nat.card_congr (MonoidHom.ofInjective autEmbed_injective).toEquiv, natCard_Ppair]

end CFSG.Monster.B.TwoA
