
module

public import CFSG.Monster.B.TwoA.Base.PlaneBase

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Lifts CFSG.Monster.Visible
  CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.SpinLattice
  CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.VisCert CFSG.Sporadic.Mathieu

open scoped Pointwise

structure PairSpace
    (U : Submodule (ZMod 2) (Wv v0))
    (A : Finset (Set.powersetCard (Fin 24) 2)) : Prop where
  pairs : ∀ D ∈ A, ∃ x y : Fin 24, ∃ h : OffPair x y, D = duad x y h.ne
  mem_iff : ∀ z, z ∈ U ↔ z = 0 ∨ z = wFr ∨
    ∃ x y : Fin 24, ∃ h : OffPair x y, duad x y h.ne ∈ A ∧ ∃ b, z = pairW x y h b

variable {U : Submodule (ZMod 2) (Wv v0)} {A : Finset (Set.powersetCard (Fin 24) 2)}

theorem PairSpace.wFr_mem (hU : PairSpace U A) : wFr ∈ U := (hU.mem_iff _).2 (.inr (.inl rfl))

theorem PairSpace.pairW_mem (hU : PairSpace U A) {x y : Fin 24} (h : OffPair x y)
    (hA : duad x y h.ne ∈ A) (b : ZMod 2) : pairW x y h b ∈ U :=
  (hU.mem_iff _).2 (.inr (.inr ⟨x, y, h, hA, b, rfl⟩))

theorem autPerm_smul_duad (p : AutPerm) {x y : Fin 24} (hxy : x ≠ y) :
    p • duad x y hxy = duad ((p : Equiv.Perm (Fin 24)) x) ((p : Equiv.Perm (Fin 24)) y)
      ((p : Equiv.Perm (Fin 24)).injective.ne hxy) := Subtype.ext (by
  change p • ((duad x y hxy : Set.powersetCard (Fin 24) 2) : Finset (Fin 24)) = _
  rw [duad_val, duad_val, Finset.smul_finset_insert, Finset.smul_finset_singleton]
  rfl)

theorem duad_eq_duad_iff {x y x' y' : Fin 24} (h : x ≠ y) (h' : x' ≠ y') :
    duad x y h = duad x' y' h' ↔ (x = x' ∧ y = y') ∨ (x = y' ∧ y = x') := by
  rw [← Subtype.coe_inj, duad_val, duad_val, pair_eq_pair_iff h h']

theorem smul_eq_of_subset {p : AutPerm} (h : ∀ D ∈ A, p • D ∈ A) : p • A = A := by
  refine Finset.eq_of_subset_of_card_le (fun D hD => ?_) (by rw [Finset.card_smul_finset])
  rw [Finset.mem_smul_finset] at hD
  obtain ⟨D', hD', rfl⟩ := hD
  exact h D' hD'

theorem monomial_mem_Mfr {a : C} {p : AutPerm}
    (hk : (QuotientGroup.mk (gO a * PO p) : OLq) ∈ Kstab v0) : (⟨_, hk⟩ : Kstab v0) ∈ Mfr := by
  rw [mem_Mfr_iff]
  obtain ⟨hp, ha⟩ := (mk_mem_Kstab_iff_monomial a p).1 hk
  exact mk_mem_monoSub ceqHyp ha hp

theorem monomial_mem_wSetStab_iff (hU : PairSpace U A) {a : C} {p : AutPerm}
    (hk : (QuotientGroup.mk (gO a * PO p) : OLq) ∈ Kstab v0) :
    (⟨_, hk⟩ : Kstab v0) ∈ wSetStab U ↔ p • A = A := by
  have hp := ((mk_mem_Kstab_iff_monomial a p).1 hk).1
  constructor
  · intro hN
    refine smul_eq_of_subset fun D hD => ?_
    obtain ⟨x, y, h, rfl⟩ := hU.pairs D hD
    have h1 := hN _ (hU.pairW_mem h hD 0)
    rw [wAct_monomial_pairW hk h 0] at h1
    rcases (hU.mem_iff _).1 h1 with h2 | h2 | ⟨x', y', h', hA', b', h2⟩
    · exact absurd h2 (pairW_ne_zero _ _)
    · exact absurd h2 (pairW_ne_wFr _ _)
    · rw [pairW_eq_iff] at h2
      rw [autPerm_smul_duad]
      rcases h2.1 with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rwa [duad_congr _ h'.ne e1 e2]
      · rw [duad_congr _ h'.ne.symm e1 e2, ← duad_comm]
        exact hA'
  · intro hA z hz
    rcases (hU.mem_iff z).1 hz with rfl | rfl | ⟨x, y, h, hD, b, rfl⟩
    · rw [map_zero]
      exact U.zero_mem
    · rw [show wAct v0 ⟨_, hk⟩ wFr = wFr from monomial_mem_Mfr hk]
      exact hU.wFr_mem
    · rw [wAct_monomial_pairW hk h b]
      refine hU.pairW_mem _ ?_ _
      have h1 : p • duad x y h.ne ∈ p • A := Finset.smul_mem_smul_finset hD
      rw [hA, autPerm_smul_duad] at h1
      exact h1

theorem monomial_mem_wFix_iff (hU : PairSpace U A) {a : C} {p : AutPerm}
    (hk : (QuotientGroup.mk (gO a * PO p) : OLq) ∈ Kstab v0) :
    (⟨_, hk⟩ : Kstab v0) ∈ wFix (U : Set (Wv v0)) ↔
      (∀ D ∈ A, p • D = D) ∧ ∀ x y : Fin 24, ∀ h : OffPair x y, duad x y h.ne ∈ A →
        (a : Fin 24 → ZMod 2) x = (a : Fin 24 → ZMod 2) y := by
  have hc0 : ∀ s t : ZMod 2, (0 + s + t = 0 ↔ s = t) := by decide
  rw [mem_wFix]
  constructor
  · intro hF
    refine ⟨fun D hD => ?_, fun x y h hD => ?_⟩
    · obtain ⟨x, y, h, rfl⟩ := hU.pairs D hD
      have h1 := hF _ (hU.pairW_mem h hD 0)
      rw [wAct_monomial_pairW hk h 0, pairW_eq_iff] at h1
      rw [autPerm_smul_duad, duad_eq_duad_iff]
      exact h1.1
    · have h1 := hF _ (hU.pairW_mem h hD 0)
      rw [wAct_monomial_pairW hk h 0, pairW_eq_iff, hc0] at h1
      exact h1.2
  · rintro ⟨hD, ha⟩ z hz
    rcases (hU.mem_iff z).1 hz with rfl | rfl | ⟨x, y, h, hA, b, rfl⟩
    · rw [map_zero]
    · exact monomial_mem_Mfr hk
    · rw [wAct_monomial_pairW hk h b, pairW_eq_iff]
      have h1 := hD _ hA
      rw [autPerm_smul_duad, duad_eq_duad_iff] at h1
      refine ⟨h1, ?_⟩
      rw [add_assoc, (by decide : ∀ s t : ZMod 2, s = t → s + t = 0) _ _ (ha x y h hA), add_zero]

@[expose] def FofA (A : Finset (Set.powersetCard (Fin 24) 2)) : Subgroup AutPerm :=
  Ppair ⊓ MulAction.stabilizer AutPerm A

@[expose] def KofA (A : Finset (Set.powersetCard (Fin 24) 2)) : Subgroup AutPerm :=
  Ppair ⊓ ⨅ D ∈ A, MulAction.stabilizer AutPerm D

theorem mem_KofA {p : AutPerm} : p ∈ KofA A ↔ p ∈ Ppair ∧ ∀ D ∈ A, p • D = D := by
  simp only [KofA, Subgroup.mem_inf, Subgroup.mem_iInf, MulAction.mem_stabilizer_iff]

@[expose] def DofA (A : Finset (Set.powersetCard (Fin 24) 2)) :
    Submodule (ZMod 2) (Fin 24 → ZMod 2) :=
  Ceq ⊓ ⨅ D ∈ A, ⨅ x ∈ (D : Finset (Fin 24)), ⨅ y ∈ (D : Finset (Fin 24)), coordEq x y

theorem mem_DofA {c : Fin 24 → ZMod 2} :
    c ∈ DofA A ↔ c ∈ Ceq ∧ ∀ D ∈ A, ∀ x ∈ (D : Finset (Fin 24)), ∀ y ∈ (D : Finset (Fin 24)),
      c x = c y := by
  simp only [DofA, Submodule.mem_inf, Submodule.mem_iInf, mem_coordEq]

theorem ceqFofAHyp (A : Finset (Set.powersetCard (Fin 24) 2)) : MonoHyp Ceq (FofA A) :=
  ⟨ceqHyp.le_C, ceqHyp.Ω_mem, fun p hp => ceqHyp.preserves p hp.1⟩

theorem dofAKofAHyp (A : Finset (Set.powersetCard (Fin 24) 2)) : MonoHyp (DofA A) (KofA A) where
  le_C := fun x hx => ((mem_DofA.1 hx).1 |> mem_Ceq.1).1
  Ω_mem := mem_DofA.2 ⟨ceqHyp.Ω_mem, fun _ _ _ _ _ _ => rfl⟩
  preserves p hp a ha := by
    rw [mem_DofA] at ha ⊢
    obtain ⟨hp1, hp2⟩ := mem_KofA.1 hp
    refine ⟨ceqHyp.preserves p hp1 a ha.1, fun D hD x hx y hy => ?_⟩
    have hD' : p⁻¹ • D = D := by
      conv_lhs => rw [← hp2 D hD]
      rw [inv_smul_smul]
    have hmem : ∀ z ∈ (D : Finset (Fin 24)), (p : Equiv.Perm (Fin 24))⁻¹ z ∈
        (D : Finset (Fin 24)) := by
      intro z hz
      have h1 : (p⁻¹ : AutPerm) • z ∈ ((p⁻¹ • D : Set.powersetCard (Fin 24) 2) :
          Finset (Fin 24)) := by
        change (p⁻¹ : AutPerm) • z ∈ (p⁻¹ : AutPerm) •
          ((D : Set.powersetCard (Fin 24) 2) : Finset (Fin 24))
        exact Finset.smul_mem_smul_finset hz
      rw [hD'] at h1
      exact h1
    change a ((p : Equiv.Perm (Fin 24))⁻¹ x) = a ((p : Equiv.Perm (Fin 24))⁻¹ y)
    exact ha.2 D hD _ (hmem x hx) _ (hmem y hy)

theorem monoSub_ceqFofA_le_Kstab : monoSub (ceqFofAHyp A) ≤ Kstab v0 :=
  (monoSub_mono (ceqFofAHyp A) ceqHyp le_rfl inf_le_left).trans monoSub_ceq_le_Kstab

theorem monoSub_dofAKofA_le_Kstab : monoSub (dofAKofAHyp A) ≤ Kstab v0 :=
  (monoSub_mono (dofAKofAHyp A) ceqHyp inf_le_left inf_le_left).trans monoSub_ceq_le_Kstab

theorem mem_wSetStab_inf_Mfr_iff (hU : PairSpace U A) (k : Kstab v0) :
    k ∈ wSetStab U ⊓ Mfr ↔ (k : OLq) ∈ monoSub (ceqFofAHyp A) := by
  constructor
  · intro hNM
    obtain ⟨hN, hM⟩ := Subgroup.mem_inf.1 hNM
    obtain ⟨a, ha, p, hp, hk⟩ := (mem_monoSub_iff ceqHyp).1 ((mem_Mfr_iff k).1 hM)
    have hk' : (QuotientGroup.mk (gO a * PO p) : OLq) ∈ Kstab v0 := hk ▸ k.2
    have e : k = ⟨_, hk'⟩ := Subtype.ext hk
    rw [e, monomial_mem_wSetStab_iff hU hk'] at hN
    rw [hk]
    exact mk_mem_monoSub (ceqFofAHyp A) ha ⟨hp, hN⟩
  · intro h
    obtain ⟨a, ha, p, hp, hk⟩ := (mem_monoSub_iff (ceqFofAHyp A)).1 h
    have hk' : (QuotientGroup.mk (gO a * PO p) : OLq) ∈ Kstab v0 := hk ▸ k.2
    have e : k = ⟨_, hk'⟩ := Subtype.ext hk
    rw [e]
    exact Subgroup.mem_inf.2 ⟨(monomial_mem_wSetStab_iff hU hk').2 hp.2, monomial_mem_Mfr hk'⟩

theorem mem_wFix_iff (hU : PairSpace U A) (k : Kstab v0) :
    k ∈ wFix (U : Set (Wv v0)) ↔ (k : OLq) ∈ monoSub (dofAKofAHyp A) := by
  constructor
  · intro hF
    have hM : k ∈ Mfr := (mem_wFix.1 hF) wFr hU.wFr_mem
    obtain ⟨a, ha, p, hp, hk⟩ := (mem_monoSub_iff ceqHyp).1 ((mem_Mfr_iff k).1 hM)
    have hk' : (QuotientGroup.mk (gO a * PO p) : OLq) ∈ Kstab v0 := hk ▸ k.2
    have e : k = ⟨_, hk'⟩ := Subtype.ext hk
    rw [e, monomial_mem_wFix_iff hU hk'] at hF
    rw [hk]
    refine mk_mem_monoSub (dofAKofAHyp A) (mem_DofA.2 ⟨ha, fun D hD x hx y hy => ?_⟩)
      (mem_KofA.2 ⟨hp, hF.1⟩)
    obtain ⟨x', y', h', rfl⟩ := hU.pairs D hD
    rw [duad_val, Finset.mem_insert, Finset.mem_singleton] at hx hy
    have e2 := hF.2 x' y' h' hD
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · rfl
    · exact e2
    · exact e2.symm
    · rfl
  · intro h
    obtain ⟨a, ha, p, hp, hk⟩ := (mem_monoSub_iff (dofAKofAHyp A)).1 h
    have hk' : (QuotientGroup.mk (gO a * PO p) : OLq) ∈ Kstab v0 := hk ▸ k.2
    have e : k = ⟨_, hk'⟩ := Subtype.ext hk
    rw [e, monomial_mem_wFix_iff hU hk']
    refine ⟨(mem_KofA.1 hp).2, fun x y h hD => ?_⟩
    refine (mem_DofA.1 ha).2 _ hD x ?_ y ?_
    · rw [duad_val]; exact Finset.mem_insert_self _ _
    · rw [duad_val]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

@[expose] def resEndU (U : Submodule (ZMod 2) (Wv v0)) (k : wSetStab U) :
    Module.End (ZMod 2) U :=
  (wAct v0 ((k : Kstab v0)⁻¹)).restrict fun x hx => ((wSetStab U).inv_mem k.2) x hx

theorem coe_resEndU (k : wSetStab U) (x : U) :
    ((resEndU U k x : U) : Wv v0) = wAct v0 ((k : Kstab v0)⁻¹) x := rfl

theorem resEndU_mul (k k' : wSetStab U) : resEndU U (k * k') = resEndU U k * resEndU U k' := by
  refine LinearMap.ext fun x => Subtype.ext ?_
  rw [coe_resEndU, Module.End.mul_apply, coe_resEndU, coe_resEndU, Subgroup.coe_mul, mul_inv_rev,
    wAct_mul, Module.End.mul_apply]

theorem resEndU_one : resEndU U 1 = 1 := by
  refine LinearMap.ext fun x => Subtype.ext ?_
  rw [coe_resEndU, Module.End.one_apply, OneMemClass.coe_one, inv_one, wAct_one,
    Module.End.one_apply]

@[expose] def resEndHomU (U : Submodule (ZMod 2) (Wv v0)) :
    wSetStab U →* Module.End (ZMod 2) U where
  toFun := resEndU U
  map_one' := resEndU_one
  map_mul' := resEndU_mul

@[expose] def resHomU (U : Submodule (ZMod 2) (Wv v0)) :
    wSetStab U →* (Module.End (ZMod 2) U)ˣ :=
  (resEndHomU U).toHomUnits

theorem resHomU_eq_one_iff (k : wSetStab U) :
    resHomU U k = 1 ↔ ∀ x ∈ U, wAct v0 ((k : Kstab v0)⁻¹) x = x := by
  constructor
  · intro h x hx
    exact congrArg (fun u : (Module.End (ZMod 2) U)ˣ =>
      (((u : Module.End (ZMod 2) U) ⟨x, hx⟩ : U) : Wv v0)) h
  · intro h
    exact Units.ext (LinearMap.ext fun x => Subtype.ext (h x x.2))

theorem ker_resHomU : (resHomU U).ker = (wFix (U : Set (Wv v0))).subgroupOf (wSetStab U) := by
  ext k
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, resHomU_eq_one_iff]
  constructor
  · intro h
    exact mem_wFix.2 fun x hx => (fix_inv_iff _ x).1 (h x hx)
  · intro h x hx
    exact (fix_inv_iff _ x).2 (mem_wFix.1 h x hx)

theorem wFix_le_wSetStab : wFix (U : Set (Wv v0)) ≤ wSetStab U := fun _ hk x hx => by
  rw [(mem_wFix.1 hk) x hx]
  exact hx

end CFSG.Monster.B.TwoA
