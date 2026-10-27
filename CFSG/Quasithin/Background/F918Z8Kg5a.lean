module

public import CFSG.Quasithin.Background.F918Z8Kg5
public import CFSG.Quasithin.Background.B5Statement

public section

namespace CFSG.Quasithin

open G6 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

theorem lka_zpowers_inf_core (x : PermMod 5) (hx : x ∈ Subgroup.zpowers (allOnes 5))
    (hc : x ∈ coreMod 5) : x = 1 := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  have h2 : allOnes 5 ^ (2 : ℕ) = 1 := by decide
  rw [zpow_eq_zpow_emod' n h2] at hc ⊢
  simp only [Nat.cast_ofNat] at hc ⊢
  rcases Int.emod_two_eq_zero_or_one n with h | h
  · rw [h]
    simp
  · exfalso
    rw [h, zpow_one] at hc
    revert hc
    rw [mem_coreMod]
    decide

theorem lka_copy {Y : Type} [CommGroup Y] {Λ : Subgroup (MulAut Y)} {J : Subgroup Y}
    {π : (FFModel.altDn 5).Gam →* ↥Λ} (h : (FFModel.altDn 5).RealizesVia Λ J ⊥ π) :
    ∃ θ : lka_E ≃* ↥J, ∀ (γ : ↥(alternatingGroup (Fin 5))) (m : lka_E),
      ((π γ : ↥Λ) : MulAut Y) ((θ m : ↥J) : Y) = ((θ (coreAct 5 γ.1 m) : ↥J) : Y) := by
  obtain ⟨-, -, -, hinv, -, -, -, β, hβs, hβk, hβe⟩ := h
  have hker : ((FFModel.altDn 5).ker).subgroupOf (FFModel.altDn 5).sec = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun m hm => ?_
    exact Subtype.ext (lka_zpowers_inf_core m.1 hm.1 hm.2)
  have hq_inj : Function.Injective
      (QuotientGroup.mk' (((FFModel.altDn 5).ker).subgroupOf (FFModel.altDn 5).sec)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hker]
  have hβinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.1 ((hβk u).1 hu))
  let eβ := MulEquiv.ofBijective β ⟨hβinj, hβs⟩
  let eQ := MulEquiv.ofBijective
    (QuotientGroup.mk' (((FFModel.altDn 5).ker).subgroupOf (FFModel.altDn 5).sec))
    ⟨hq_inj, QuotientGroup.mk'_surjective _⟩
  refine ⟨eQ.trans eβ.symm, fun γ m => ?_⟩
  set u : ↥J := eβ.symm (eQ m) with hu_def
  have hβu : β u = QuotientGroup.mk m := eβ.apply_symm_apply (eQ m)
  have hu : ((π γ : ↥Λ) : MulAut Y) (u : Y) ∈ J := hinv (π γ) u u.2
  have hm : (FFModel.altDn 5).act γ m.1 ∈ (FFModel.altDn 5).sec :=
    permAct_mem_coreMod γ.1 m.2
  have key := hβe γ u m hu hm hβu
  have hfin : eβ.symm (eQ (coreAct 5 γ.1 m)) = ⟨((π γ : ↥Λ) : MulAut Y) (u : Y), hu⟩ := by
    rw [MulEquiv.symm_apply_eq]
    exact key.symm
  show ((π γ : ↥Λ) : MulAut Y) (u : Y) = ((eβ.symm (eQ (coreAct 5 γ.1 m)) : ↥J) : Y)
  rw [hfin]

theorem lka_coord {Y : Type} [CommGroup Y] {Λ : Subgroup (MulAut Y)}
    (hds : DirectSumOfCopies Λ ⊤ ⊥ (FFModel.altDn 5) 2) :
    ∃ (π : ↥(alternatingGroup (Fin 5)) →* ↥Λ) (Φ : (lka_E × lka_E) ≃* Y),
      ∀ (γ : ↥(alternatingGroup (Fin 5))) (x : lka_E × lka_E),
        ((π γ : ↥Λ) : MulAut Y) (Φ x) = Φ (lka_diag γ x) := by
  obtain ⟨I, π, -, hind, hsum, hreal⟩ := hds
  have hI : I 0 ⊓ I 1 = ⊥ := by
    have h0 := hind 0
    have e : (⨆ (j : Fin 2) (_ : j ≠ 0), I j) = I 1 := by
      refine le_antisymm (iSup₂_le fun j hj => ?_) (le_iSup₂_of_le 1 (by decide) le_rfl)
      have : j = 1 := by omega
      rw [this]
    rwa [e, bot_sup_eq] at h0
  have hS : I 0 ⊔ I 1 = ⊤ := by
    rw [eq_top_iff, ← hsum]
    refine sup_le bot_le (iSup_le fun i => ?_)
    fin_cases i
    · exact le_sup_left
    · exact le_sup_right
  obtain ⟨θ0, hθ0⟩ := lka_copy (hreal 0)
  obtain ⟨θ1, hθ1⟩ := lka_copy (hreal 1)
  let Ψ : lka_E × lka_E →* Y :=
    ((I 0).subtype.comp θ0.toMonoidHom).coprod ((I 1).subtype.comp θ1.toMonoidHom)
  have hΨ : ∀ x, Ψ x = ((θ0 x.1 : ↥(I 0)) : Y) * ((θ1 x.2 : ↥(I 1)) : Y) := fun x => rfl
  have hinj : Function.Injective Ψ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, b⟩ hab
    rw [hΨ] at hab
    have hmem : ((θ0 a : ↥(I 0)) : Y) ∈ I 0 ⊓ I 1 := by
      refine ⟨(θ0 a).2, ?_⟩
      rw [eq_inv_of_mul_eq_one_left hab]
      exact (I 1).inv_mem (θ1 b).2
    rw [hI, Subgroup.mem_bot] at hmem
    have ha : a = 1 := θ0.injective (Subtype.ext (by simpa using hmem))
    have hb : b = 1 := by
      rw [hmem, one_mul] at hab
      exact θ1.injective (Subtype.ext (by simpa using hab))
    rw [ha, hb]
    rfl
  have hsurj : Function.Surjective Ψ := by
    intro y
    have hy : y ∈ I 0 ⊔ I 1 := by rw [hS]; trivial
    obtain ⟨y0, hy0, y1, hy1, rfl⟩ := Subgroup.mem_sup.1 hy
    obtain ⟨a, ha⟩ := θ0.surjective ⟨y0, hy0⟩
    obtain ⟨b, hb⟩ := θ1.surjective ⟨y1, hy1⟩
    refine ⟨(a, b), ?_⟩
    rw [hΨ]
    simp [ha, hb]
  refine ⟨π, MulEquiv.ofBijective Ψ ⟨hinj, hsurj⟩, fun γ x => ?_⟩
  show ((π γ : ↥Λ) : MulAut Y) (Ψ x) = Ψ (lka_diag γ x)
  rw [hΨ, hΨ, map_mul, hθ0, hθ1]
  rfl

theorem lka_pow_of_comm {Y : Type} [CommGroup Y] {Λ : Subgroup (MulAut Y)}
    (hds : DirectSumOfCopies Λ ⊤ ⊥ (FFModel.altDn 5) 2) (c : MulAut Y)
    (hc : ∀ l ∈ Λ, c * l = l * c) : c ^ 24 = 1 := by
  obtain ⟨π, Φ, hΦ⟩ := lka_coord hds
  let ψ : MulAut Y ≃* MulAut (lka_E × lka_E) := MulAut.congr Φ.symm
  have hψ : ∀ (d : MulAut Y) (x : lka_E × lka_E), ψ d x = Φ.symm (d (Φ x)) := fun d x => rfl
  have hφ : ∀ (γ : ↥(alternatingGroup (Fin 5))) (x : lka_E × lka_E),
      ψ c (lka_diag γ x) = lka_diag γ (ψ c x) := by
    intro γ x
    rw [hψ, hψ, ← hΦ γ x]
    have h1 : c ((π γ : MulAut Y) (Φ x)) = (π γ : MulAut Y) (c (Φ x)) :=
      congrArg (fun f : MulAut Y => f (Φ x)) (hc (π γ) (π γ).2)
    rw [h1]
    apply Φ.injective
    rw [MulEquiv.apply_symm_apply, ← hΦ, MulEquiv.apply_symm_apply]
  have h24 := lka_pow_one (ψ c) hφ
  rw [← map_pow] at h24
  exact ψ.injective (by rw [h24, map_one])

end CFSG.Quasithin
