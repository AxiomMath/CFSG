module

public import CFSG.Quasithin.H13.L32AH65b

public section

namespace CFSG.Quasithin.H6

open scoped MatrixGroups Pointwise

theorem IsoMod.symm {M N : Type} [AddGroup M] [AddGroup N] {ρ : Γ →* AddMonoid.End M}
    {σ : Γ →* AddMonoid.End N} (h : IsoMod ρ σ) : IsoMod σ ρ := by
  obtain ⟨f, hf, hfe⟩ := h
  let e := AddEquiv.ofBijective f hf
  refine ⟨e.symm.toAddMonoidHom, e.symm.bijective, fun g m => hf.1 ?_⟩
  show f (e.symm (ρ g m)) = f (σ g (e.symm m))
  rw [hfe]
  have h1 : ∀ x, f (e.symm x) = x := e.apply_symm_apply
  rw [h1, h1]

theorem card_gamma_factorization : (Nat.card Γ).factorization 2 = 3 := by
  rw [card_gamma, show (168 : ℕ) = 2 ^ 3 * 21 by norm_num, Nat.factorization_mul (by norm_num)
    (by norm_num), Nat.Prime.factorization_pow Nat.prime_two]
  simp [Nat.factorization_eq_zero_of_not_dvd (show ¬ 2 ∣ 21 by norm_num)]

@[expose] noncomputable def sylowBorel : Sylow 2 Γ :=
  Sylow.ofCard borel (by rw [card_borel, card_gamma_factorization]; norm_num)

theorem exists_conj_borel (α : Γ ≃* Γ) : ∃ y : Γ, ∀ t ∈ borel, y⁻¹ * α t * y ∈ borel := by
  have hcard : Nat.card ↥(borel.map α.toMonoidHom) = 2 ^ (Nat.card Γ).factorization 2 := by
    rw [Subgroup.card_map_of_injective α.injective, card_borel, card_gamma_factorization]
    norm_num
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq Γ sylowBorel (Sylow.ofCard _ hcard)
  have e := congrArg (fun Q : Sylow 2 Γ => (Q : Subgroup Γ)) hy
  simp only [Sylow.coe_subgroup_smul, sylowBorel, Sylow.coe_ofCard] at e
  refine ⟨y, fun t ht => ?_⟩
  have h1 : α t ∈ borel.map α.toMonoidHom := ⟨t, ht, rfl⟩
  rw [← e, Subgroup.mem_smul_pointwise_iff_exists] at h1
  obtain ⟨s, hs, hse⟩ := h1
  rw [MulAut.smul_def, MulAut.conj_apply] at hse
  rw [← hse, show y⁻¹ * (y * s * y⁻¹) * y = s by group]
  exact hs

theorem card_Lp : Nat.card ↥Lp = 24 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem card_Ll : Nat.card ↥Ll = 24 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem borel_trans_off : ∀ v w : V3, v 2 ≠ 0 → w 2 ≠ 0 → ∃ i : Fin 8, bel i • v = w := by
  decide +kernel

theorem mem_Ll_of_smul : ∀ g : Γ, (g • (![1, 0, 0] : V3)) 2 = 0 →
    (g • (![0, 1, 0] : V3)) 2 = 0 → g ∈ Ll := by
  decide +kernel

theorem cases_on_l : ∀ v : V3, v 2 = 0 → v ≠ ![1, 0, 0] → v ≠ 0 →
    v = ![0, 1, 0] ∨ v = ![1, 1, 0] := by
  decide

theorem bel1_smul : bel 1 • (![1, 1, 0] : V3) = ![0, 1, 0] := by decide

theorem eq_Lp_or_Ll {H : Subgroup Γ} (hTH : borel ≤ H) (hH : Nat.card ↥H = 24) :
    H = Lp ∨ H = Ll := by
  classical
  have hl : ∀ h ∈ H, (h • (![1, 0, 0] : V3)) 2 = 0 := by
    intro h hh
    by_contra hne
    have hsub : (({![1, 0, 0], ![0, 0, 1], ![1, 0, 1], ![0, 1, 1], ![1, 1, 1]} : Finset V3) :
        Set V3) ⊆ MulAction.orbit ↥H (![1, 0, 0] : V3) := by
      intro w hw
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hw
      rcases hw with rfl | hw
      · exact ⟨1, one_smul _ _⟩
      · have hw2 : w 2 ≠ 0 := by rcases hw with rfl | rfl | rfl | rfl <;> decide
        obtain ⟨i, hi⟩ := borel_trans_off _ w hne hw2
        refine ⟨⟨bel i * h, mul_mem (hTH (bel_mem i)) hh⟩, ?_⟩
        show (bel i * h) • (![1, 0, 0] : V3) = w
        rw [mul_smul, hi]
    have horb : 5 ≤ (MulAction.orbit ↥H (![1, 0, 0] : V3)).ncard := by
      have hc : ({![1, 0, 0], ![0, 0, 1], ![1, 0, 1], ![0, 1, 1], ![1, 1, 1]} :
          Finset V3).card = 5 := by decide
      rw [← hc, ← Set.ncard_coe_finset]
      exact Set.ncard_le_ncard hsub (Set.toFinite _)
    have hstab : 8 ≤ Nat.card ↥(MulAction.stabilizer ↥H (![1, 0, 0] : V3)) := by
      rw [← card_borel]
      refine Nat.card_le_card_of_injective
        (fun t : ↥borel => (⟨⟨t, hTH t.2⟩, (Subgroup.mem_inf.mp t.2).1⟩ :
          ↥(MulAction.stabilizer ↥H (![1, 0, 0] : V3)))) fun s t e => ?_
      exact Subtype.ext (congrArg (fun x : ↥(MulAction.stabilizer ↥H (![1, 0, 0] : V3)) =>
        ((x : ↥H) : Γ)) e)
    have hmul := (MulAction.stabilizer ↥H (![1, 0, 0] : V3)).card_mul_index
    rw [MulAction.index_stabilizer, hH] at hmul
    have := Nat.mul_le_mul hstab horb
    omega
  by_cases hfix : ∀ h ∈ H, h • (![1, 0, 0] : V3) = ![1, 0, 0]
  · exact Or.inl (Subgroup.eq_of_le_of_card_ge (fun h hh => hfix h hh) (by rw [hH, card_Lp]))
  · right
    push Not at hfix
    obtain ⟨h₀, hh₀, hne⟩ := hfix
    obtain ⟨h', hh', he⟩ : ∃ h' ∈ H, h' • (![1, 0, 0] : V3) = ![0, 1, 0] := by
      have hne0 : h₀ • (![1, 0, 0] : V3) ≠ 0 := by
        rw [Ne, smul_eq_zero_iff_eq]
        decide
      rcases cases_on_l _ (hl h₀ hh₀) hne hne0 with e | e
      · exact ⟨h₀, hh₀, e⟩
      · exact ⟨bel 1 * h₀, mul_mem (hTH (bel_mem 1)) hh₀, by rw [mul_smul, e, bel1_smul]⟩
    refine Subgroup.eq_of_le_of_card_ge (fun h hh => mem_Ll_of_smul h (hl h hh) ?_)
      (by rw [hH, card_Ll])
    rw [← he, ← mul_smul]
    exact hl _ (mul_mem hh hh')

@[expose] def stE23 : St := ⟨!![0, 0, 0; 0, 0, 1; 0, 0, 0], by decide⟩

@[expose] def stE12 : St := ⟨!![0, 1, 0; 0, 0, 0; 0, 0, 0], by decide⟩

@[expose] def stLl : AddSubgroup St where
  carrier := {x | x = 0 ∨ x = stE13 ∨ x = stE23 ∨ x = stE13 + stE23}
  add_mem' := by
    rintro a b (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl) <;> decide
  zero_mem' := Or.inl rfl
  neg_mem' := by
    rintro a (rfl | rfl | rfl | rfl) <;> decide

@[expose] def stLp : AddSubgroup St where
  carrier := {x | x = 0 ∨ x = stE13 ∨ x = stE12 ∨ x = stE13 + stE12}
  add_mem' := by
    rintro a b (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl) <;> decide
  zero_mem' := Or.inl rfl
  neg_mem' := by
    rintro a (rfl | rfl | rfl | rfl) <;> decide

instance : DecidablePred (· ∈ stLl) := fun x =>
  inferInstanceAs (Decidable (x = 0 ∨ x = stE13 ∨ x = stE23 ∨ x = stE13 + stE23))

instance : DecidablePred (· ∈ stLp) := fun x =>
  inferInstanceAs (Decidable (x = 0 ∨ x = stE13 ∨ x = stE12 ∨ x = stE13 + stE12))

theorem card_stLl : Nat.card ↥stLl = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem card_stLp : Nat.card ↥stLp = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem Ll_smul_E13 : ∀ g : Γ, g ∈ Ll →
    g • stE13 = 0 ∨ g • stE13 = stE13 ∨ g • stE13 = stE23 ∨ g • stE13 = stE13 + stE23 := by
  decide +kernel

theorem Lp_smul_E13 : ∀ g : Γ, g ∈ Lp →
    g • stE13 = 0 ∨ g • stE13 = stE13 ∨ g • stE13 = stE12 ∨ g • stE13 = stE13 + stE12 := by
  decide +kernel

@[expose] def llS : Γ := ⟨!![0, 1, 0; 1, 0, 0; 0, 0, 1], by decide⟩

@[expose] def lpS : Γ := ⟨!![1, 0, 0; 0, 0, 1; 0, 1, 0], by decide⟩

theorem llS_mem : llS ∈ Ll := by decide

theorem lpS_mem : lpS ∈ Lp := by decide

theorem llS_E13 : llS • stE13 = stE23 := by decide

theorem lpS_E13 : lpS • stE13 = stE12 := by decide

theorem closure_Ll_E13 : AddSubgroup.closure {y : St | ∃ g ∈ Ll, g • stE13 = y} = stLl := by
  have h1 : stE13 ∈ AddSubgroup.closure {y : St | ∃ g ∈ Ll, g • stE13 = y} :=
    AddSubgroup.subset_closure ⟨1, one_mem _, one_smul _ _⟩
  have h2 : stE23 ∈ AddSubgroup.closure {y : St | ∃ g ∈ Ll, g • stE13 = y} :=
    AddSubgroup.subset_closure ⟨llS, llS_mem, llS_E13⟩
  refine le_antisymm ((AddSubgroup.closure_le _).mpr ?_) fun x hx => ?_
  · rintro _ ⟨g, hg, rfl⟩
    exact Ll_smul_E13 g hg
  · rcases hx with rfl | rfl | rfl | rfl
    · exact zero_mem _
    · exact h1
    · exact h2
    · exact add_mem h1 h2

theorem closure_Lp_E13 : AddSubgroup.closure {y : St | ∃ g ∈ Lp, g • stE13 = y} = stLp := by
  have h1 : stE13 ∈ AddSubgroup.closure {y : St | ∃ g ∈ Lp, g • stE13 = y} :=
    AddSubgroup.subset_closure ⟨1, one_mem _, one_smul _ _⟩
  have h2 : stE12 ∈ AddSubgroup.closure {y : St | ∃ g ∈ Lp, g • stE13 = y} :=
    AddSubgroup.subset_closure ⟨lpS, lpS_mem, lpS_E13⟩
  refine le_antisymm ((AddSubgroup.closure_le _).mpr ?_) fun x hx => ?_
  · rintro _ ⟨g, hg, rfl⟩
    exact Lp_smul_E13 g hg
  · rcases hx with rfl | rfl | rfl | rfl
    · exact zero_mem _
    · exact h1
    · exact h2
    · exact add_mem h1 h2

theorem st_faithful : ∀ g : Γ, g • stE13 = stE13 → g • stE31 = stE31 → g = 1 := by
  decide +kernel

theorem x3_pow : x3 ^ 3 = 1 := by decide

theorem x3_ne : x3 ≠ 1 := by decide

theorem isoMod_twist_of_borel (h65 : VolI_H_6_5) (α : Γ ≃* Γ) (hα : ∀ t ∈ borel, α t ∈ borel) :
    IsoMod ρSt (ρSt.comp α.toMonoidHom) := by
  have hαT : borel.map α.toMonoidHom = borel :=
    Subgroup.eq_of_le_of_card_ge (by rintro _ ⟨t, ht, rfl⟩; exact hα t ht)
      (by rw [Subgroup.card_map_of_injective α.injective])
  have hH : Ll.map α.toMonoidHom = Lp ∨ Ll.map α.toMonoidHom = Ll :=
    eq_Lp_or_Ll (by rw [← hαT]; exact Subgroup.map_mono inf_le_right)
      (by rw [Subgroup.card_map_of_injective α.injective, card_Ll])
  have hfaith : ∀ g : Γ, (∀ x : St, (ρSt.comp α.toMonoidHom) g x = x) → g = 1 := fun g hg => by
    have h1 := st_faithful (α g) (hg stE13) (hg stE31)
    rwa [MulEquiv.map_eq_one_iff] at h1
  have hmT : ∀ t ∈ borel, (ρSt.comp α.toMonoidHom) t stE13 = stE13 := fun t ht => by
    obtain ⟨i, hi⟩ := exists_bel (α t) (hα t ht)
    show α t • stE13 = stE13
    rw [← hi]
    exact stE13_fix_bel i
  have hgen : AddSubgroup.closure
      (Set.range fun g : Γ => (ρSt.comp α.toMonoidHom) g stE13) = ⊤ := by
    have e : (Set.range fun g : Γ => (ρSt.comp α.toMonoidHom) g stE13) =
        Set.range fun h : Γ => ρSt h stE13 :=
      α.surjective.range_comp (fun h : Γ => ρSt h stE13)
    rw [e]
    exact st_closure_E13
  have hset : {y | ∃ g ∈ Ll, (ρSt.comp α.toMonoidHom) g stE13 = y} =
      {y : St | ∃ h ∈ Ll.map α.toMonoidHom, h • stE13 = y} := by
    ext y
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨α g, ⟨g, hg, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
      exact ⟨g, hg, rfl⟩
  have hl : Nat.card ↥(AddSubgroup.closure
      {y | ∃ g ∈ Ll, (ρSt.comp α.toMonoidHom) g stE13 = y}) = 4 := by
    rw [hset]
    rcases hH with e | e <;> rw [e]
    · rw [closure_Lp_E13, card_stLp]
    · rw [closure_Ll_E13, card_stLl]
  have hx3 : (α x3) ^ 3 = 1 := by rw [← map_pow, x3_pow, map_one]
  have hx1 : α x3 ≠ 1 := by
    rw [Ne, MulEquiv.map_eq_one_iff]
    exact x3_ne
  have hidx : Nat.card St = 64 * Nat.card {y : St // (ρSt.comp α.toMonoidHom) x3 y = y} := by
    have h4 : Nat.card {y : St // ρSt (α x3) y = y} = 4 := card_fix_st (α x3) hx3 hx1
    rw [card_st]
    exact (congrArg (64 * ·) h4).symm
  exact (isoMod_st_of_index h65 st_add_self hfaith hmT hgen hl x3_pow x3_ne hidx).symm

theorem isoMod_twist (h65 : VolI_H_6_5) (α : Γ ≃* Γ) : IsoMod ρSt (ρSt.comp α.toMonoidHom) := by
  obtain ⟨y, hy⟩ := exists_conj_borel α
  let α' : Γ ≃* Γ := α.trans (MulAut.conj y⁻¹)
  have hα' : ∀ g, α' g = y⁻¹ * α g * y := fun g => by
    show MulAut.conj y⁻¹ (α g) = _
    rw [MulAut.conj_apply, inv_inv]
  obtain ⟨f, hf, hfe⟩ := isoMod_twist_of_borel h65 α' fun t ht => by rw [hα']; exact hy t ht
  refine ⟨f.comp (ρSt y⁻¹), hf.comp (MulAction.bijective y⁻¹), fun g x => ?_⟩
  show f (y⁻¹ • (α g • x)) = g • f (y⁻¹ • x)
  have e : y⁻¹ • (α g • x) = α' g • (y⁻¹ • x) := by
    rw [hα', ← mul_smul, ← mul_smul, show y⁻¹ * α g * y * y⁻¹ = y⁻¹ * α g by group]
  rw [e]
  exact hfe g (y⁻¹ • x)

theorem volI_H_6_3 : VolI_H_6_3 :=
  ⟨fun _ _ _ ρ h2 f hf hfe => st_projective ρ h2 f hf hfe,
    fun _ _ _ ρ h2 f hf hfe => st_injective ρ h2 f hf hfe,
    ⟨stForm, stForm_nondeg, stForm_conj⟩, isoMod_twist volI_H_6_5,
    fun x _ hx3 hx1 => card_fix_st x hx3 hx1, st_fix_borel, st_stabilizer, st_comm_Ll,
    st_comm_Lp⟩

end CFSG.Quasithin.H6
