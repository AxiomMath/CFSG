module

public import CFSG.Quasithin.EmptyFaithful.S153G93DCases
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.FFC2Sym

public section

namespace CFSG.Quasithin

namespace S153G93D

namespace CovPerm

theorem permAct_swap_mul_swap {n : ℕ} {a b c : Fin n} {x : G6.PermMod n}
    (hb : Multiplicative.toAdd x a = Multiplicative.toAdd x b)
    (hc : Multiplicative.toAdd x a = Multiplicative.toAdd x c) :
    G6.permAct n (Equiv.swap a b * Equiv.swap a c) x = x := by
  apply Multiplicative.toAdd.injective
  funext i
  rw [G6.permAct_apply, mul_inv_rev, Equiv.swap_inv, Equiv.swap_inv, Equiv.Perm.mul_apply,
    Equiv.apply_swap_eq_self hc, Equiv.apply_swap_eq_self hb]

theorem exists_isThreeCycle_permAct_eq {n : ℕ} (hn : 5 ≤ n) (x : G6.PermMod n) :
    ∃ σ : Equiv.Perm (Fin n), σ.IsThreeCycle ∧ G6.permAct n σ x = x := by
  have hcard : Fintype.card (ZMod 2) * 2 < Fintype.card (Fin n) := by
    rw [ZMod.card, Fintype.card_fin]
    omega
  obtain ⟨y, hy⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card
    (f := Multiplicative.toAdd x) hcard
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.1 hy
  have hua : Multiplicative.toAdd x a = y := (Finset.mem_filter.1 ha).2
  have hub : Multiplicative.toAdd x b = y := (Finset.mem_filter.1 hb).2
  have huc : Multiplicative.toAdd x c = y := (Finset.mem_filter.1 hc).2
  exact ⟨Equiv.swap a b * Equiv.swap a c,
    Equiv.Perm.isThreeCycle_swap_mul_swap_same hab hac hbc,
    permAct_swap_mul_swap (hua.trans hub.symm) (hua.trans huc.symm)⟩

theorem symDn_faithful {n : ℕ} (hn : 5 ≤ n) : (FFModel.symDn n).Faithful := by
  intro σ h
  by_contra hne
  obtain ⟨m, hm, hmove⟩ := FFC.exists_core_move hn hne
  exact hmove (Subgroup.mem_inf.1 (h m hm)).1

theorem altDn_faithful {n : ℕ} (hn : 5 ≤ n) : (FFModel.altDn n).Faithful := by
  intro (σ : ↥(alternatingGroup (Fin n))) h
  exact Subtype.ext (symDn_faithful hn (σ : Equiv.Perm (Fin n)) fun m hm => h m hm)

section Realization

variable {W : Type} [CommGroup W]

theorem exists_sec_rep {D : FFModel} {J : Subgroup (MulAut W)} {π : D.Gam →* ↥J}
    (h : D.RealizesVia J ⊤ ⊥ π) (w : W) :
    ∃ m ∈ D.sec, ∀ γ : D.Gam, D.act γ m = m → ((π γ : ↥J) : MulAut W) w = w := by
  obtain ⟨-, -, -, -, -, hsec, -, β, -, hβk, hβe⟩ := h
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨w, Subgroup.mem_top w⟩)
  refine ⟨m, m.2, fun γ hγ => ?_⟩
  have hact : D.act γ (m : D.Amb) ∈ D.sec := hsec γ m m.2
  have hu : ((π γ : ↥J) : MulAut W) w ∈ (⊤ : Subgroup W) := Subgroup.mem_top _
  have h1 := hβe γ ⟨w, Subgroup.mem_top w⟩ m hu hact hm.symm
  have h2 : (⟨D.act γ (m : D.Amb), hact⟩ : ↥D.sec) = m := Subtype.ext hγ
  rw [h2, hm] at h1
  have h3 : β (⟨((π γ : ↥J) : MulAut W) w, hu⟩ *
      (⟨w, Subgroup.mem_top w⟩ : ↥(⊤ : Subgroup W))⁻¹) = 1 := by
    rw [map_mul, map_inv, h1, mul_inv_cancel]
  have h5 : ((π γ : ↥J) : MulAut W) w * w⁻¹ = 1 := Subgroup.mem_bot.1 ((hβk _).1 h3)
  exact mul_inv_eq_one.1 h5

end Realization

theorem covAlt_of_five_le {n : ℕ} (hn : 5 ≤ n) (W : Type) [CommGroup W] [Finite W]
    (J : Subgroup (MulAut W)) (hJ : AlternatingNatural J ⊤ ⊥ n) : CovOrder3 J := by
  intro w _
  obtain ⟨π, hπ⟩ : ∃ π : ↥(alternatingGroup (Fin n)) →* ↥J,
      (FFModel.altDn n).RealizesVia J ⊤ ⊥ π := hJ
  obtain ⟨m, -, hfix⟩ := exists_sec_rep hπ w
  obtain ⟨σ, hσ, hσm⟩ := exists_isThreeCycle_permAct_eq hn m
  have hσA : σ ∈ alternatingGroup (Fin n) := Equiv.Perm.mem_alternatingGroup.2 hσ.sign
  have hinj : Function.Injective π :=
    FFModel.RealizesVia.injective_of_faithful (altDn_faithful hn) hπ
  refine ⟨((π ⟨σ, hσA⟩ : ↥J) : MulAut W), (π ⟨σ, hσA⟩).2, ?_, hfix ⟨σ, hσA⟩ hσm⟩
  rw [Subgroup.orderOf_coe, orderOf_injective π hinj, Subgroup.orderOf_mk, hσ.orderOf]

theorem covSym_of_five_le {n : ℕ} (hn : 5 ≤ n) (W : Type) [CommGroup W] [Finite W]
    (J : Subgroup (MulAut W)) (hJ : SymmetricNatural J ⊤ ⊥ n) : CovOrder3 J := by
  intro w _
  obtain ⟨π, hπ⟩ : ∃ π : Equiv.Perm (Fin n) →* ↥J, (FFModel.symDn n).RealizesVia J ⊤ ⊥ π := hJ
  obtain ⟨m, -, hfix⟩ := exists_sec_rep hπ w
  obtain ⟨σ, hσ, hσm⟩ := exists_isThreeCycle_permAct_eq hn m
  have hinj : Function.Injective π :=
    FFModel.RealizesVia.injective_of_faithful (symDn_faithful hn) hπ
  refine ⟨((π σ : ↥J) : MulAut W), (π σ).2, ?_, hfix σ hσm⟩
  rw [Subgroup.orderOf_coe, orderOf_injective π hinj, hσ.orderOf]

theorem covAlt7_holds : CovAlt7 :=
  fun W _ _ J hJ => covAlt_of_five_le (by norm_num) W J hJ

theorem covSym7_holds : CovSym7 :=
  fun W _ _ J hJ => covSym_of_five_le (by norm_num) W J hJ

end CovPerm

end S153G93D

end CFSG.Quasithin
