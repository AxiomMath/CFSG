module

public import CFSG.Quasithin.Background.A7Q528Class
public import CFSG.Quasithin.Background.A7Q528Split
public import CFSG.Quasithin.Background.SL3SmallSect

public section

namespace CFSG.Quasithin.A7Q528

open Equiv Equiv.Perm CFSG.QuasithinUnique.Setup.X3E CFSG.QuasithinUnique.Setup.X3
open CFSG.Quasithin.B45Alt7

variable {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]

theorem eq_top_of_card_quot {ρ : Representation (ZMod 2) A7 M} {H : Subgroup A7}
    (hspan : ∀ C : Submodule (ZMod 2) M, (∀ g ∈ H, ∀ v, ρ g v - v ∈ C) → C = ⊤)
    {U' : Submodule (ZMod 2) M} (hU'inv : ∀ g, ∀ v ∈ U', ρ g v ∈ U')
    (hq : Nat.card (M ⧸ U') ≤ 4) : U' = ⊤ := by
  classical
  let ρQ := ρ.quotient U' fun g => by
    intro v hv
    exact hU'inv g v hv
  have hker : ρQ.ker = ⊤ := by
    rcases alternatingGroup.normal_subgroup_eq_bot_or_eq_top (α := Fin 7) (by simp)
      (N := ρQ.ker) with h | h
    · exfalso
      have hinj : Function.Injective fun g : A7 => (ρQ g : M ⧸ U' → M ⧸ U') :=
        DFunLike.coe_injective.comp ((MonoidHom.ker_eq_bot_iff ρQ).mp h)
      have h1 := Nat.card_le_card_of_injective _ hinj
      rw [Nat.card_fun] at h1
      have hA : Nat.card A7 = 2520 := by
        rw [nat_card_alternatingGroup]
        simp [Nat.factorial]
      have h2 : Nat.card (M ⧸ U') ^ Nat.card (M ⧸ U') ≤ 4 ^ 4 :=
        (Nat.pow_le_pow_left hq _).trans (Nat.pow_le_pow_right (by norm_num) hq)
      have h3 := h1.trans h2
      rw [hA] at h3
      norm_num at h3
    · exact h
  apply hspan U'
  intro g _ v
  have hg : ρQ g = 1 := MonoidHom.mem_ker.mp (hker ▸ Subgroup.mem_top g)
  have h1 : ρQ g (Submodule.Quotient.mk v) = Submodule.Quotient.mk v := by
    rw [hg, Module.End.one_apply]
  have h2 : (Submodule.Quotient.mk (ρ g v) : M ⧸ U') = Submodule.Quotient.mk v := h1
  exact (Submodule.Quotient.eq U').mp h2

theorem card_coreMod7 : Nat.card (G6.coreMod 7) = 2 ^ 6 := by
  have h : (G6.coreMod 7 : Set (G6.PermMod 7)) =
      ↑(Finset.univ.filter fun x : G6.PermMod 7 => ∑ i, Multiplicative.toAdd x i = 0) := by
    ext x
    simp [G6.mem_coreMod]
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, h, Set.ncard_coe_finset]
  decide

theorem exists_not_mem_orbit {H : Subgroup A7} (h7 : ¬ 7 ∣ Nat.card H) :
    ∃ j : Fin 7, j ∉ MulAction.orbit ↥H (0 : Fin 7) := by
  by_contra hall
  push Not at hall
  apply h7
  have h1 : (MulAction.stabilizer ↥H (0 : Fin 7)).index = 7 := by
    rw [MulAction.index_stabilizer, Set.eq_univ_of_forall hall, Set.ncard_univ,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  have h2 := Subgroup.index_dvd_card (MulAction.stabilizer ↥H (0 : Fin 7))
  rwa [h1] at h2

theorem inv_mem_orbit_iff {H : Subgroup A7} {σ : A7} (hσ : σ ∈ H) (i : Fin 7) :
    (σ : Perm (Fin 7))⁻¹ i ∈ MulAction.orbit ↥H (0 : Fin 7) ↔
      i ∈ MulAction.orbit ↥H (0 : Fin 7) := by
  simp only [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨⟨σ, hσ⟩ * x, ?_⟩
    rw [mul_smul, hx]
    show (σ : Perm (Fin 7)) ((σ : Perm (Fin 7))⁻¹ i) = i
    simp
  · rintro ⟨x, hx⟩
    refine ⟨⟨σ, hσ⟩⁻¹ * x, ?_⟩
    rw [mul_smul, hx]
    rfl

theorem sum_orbit_permAct {H : Subgroup A7} {σ : A7} (hσ : σ ∈ H) (y : G6.PermMod 7)
    [DecidablePred (· ∈ MulAction.orbit ↥H (0 : Fin 7))] :
    ∑ i ∈ Finset.univ.filter (· ∈ MulAction.orbit ↥H (0 : Fin 7)),
        Multiplicative.toAdd (G6.permAct 7 (σ : Perm (Fin 7)) y) i =
      ∑ i ∈ Finset.univ.filter (· ∈ MulAction.orbit ↥H (0 : Fin 7)), Multiplicative.toAdd y i := by
  rw [Finset.sum_filter, Finset.sum_filter]
  simp only [G6.permAct_apply]
  set g : Fin 7 → ZMod 2 := fun k =>
    if k ∈ MulAction.orbit ↥H (0 : Fin 7) then Multiplicative.toAdd y k else 0 with hg
  have e : ∀ i, (if i ∈ MulAction.orbit ↥H (0 : Fin 7) then
      Multiplicative.toAdd y ((σ : Perm (Fin 7))⁻¹ i) else 0) = g ((σ : Perm (Fin 7))⁻¹ i) := by
    intro i
    simp only [hg, inv_mem_orbit_iff hσ i]
  simp only [e]
  exact Equiv.sum_comp ((σ : Perm (Fin 7))⁻¹) g

theorem main (ρ : Representation (ZMod 2) A7 M) (H : Subgroup A7) (h7 : ¬ 7 ∣ Nat.card H)
    (hcard : Nat.card M ≤ 2 ^ 6) (hnt : ∃ g v, ρ g v ≠ v)
    (hspan : ∀ C : Submodule (ZMod 2) M, (∀ g ∈ H, ∀ v, ρ g v - v ∈ C) → C = ⊤) :
    Nat.card M = 2 ^ 4 ∧
      ∀ C : Submodule (ZMod 2) M, (∀ g, ∀ v ∈ C, ρ g v ∈ C) → C = ⊥ ∨ C = ⊤ := by
  classical
  have hperf : commutator A7 = ⊤ := commutator_alternatingGroup_eq_top (by simp)
  obtain ⟨U, U', hUU', hU'inv, hUtriv, hmin, g₀, v₀, hv₀, hgv₀⟩ :=
    SL3Small.exists_section hperf hnt
  set N : Submodule (ZMod 2) U' := U.comap U'.subtype with hN
  let ρ' := ρ.subrepresentation U' fun g => by
    intro v hv
    exact hU'inv g v hv
  let ρS := ρ'.quotient N fun g => by
    intro w hw
    show ((ρ' g w : U') : M) ∈ U
    have e : ((ρ' g w : U') : M) = ρ g w := rfl
    rw [e, hUtriv g (w : M) hw]
    exact hw
  have hρS : ∀ g (w : U'), ρS g (N.mkQ w) = N.mkQ ⟨ρ g w, hU'inv g w w.2⟩ := fun g w => rfl
  have hmkQ : ∀ w w' : U', N.mkQ w = N.mkQ w' ↔ (w : M) - w' ∈ U := fun w w' => by
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    rfl
  have hirrS : ∀ J : Submodule (ZMod 2) (U' ⧸ N), (∀ g, ∀ s ∈ J, ρS g s ∈ J) →
      J = ⊥ ∨ J = ⊤ := by
    intro J hJ
    set X : Submodule (ZMod 2) M := (J.comap N.mkQ).map U'.subtype with hX
    have hUX : U ≤ X := by
      intro u hu
      refine ⟨⟨u, hUU'.le hu⟩, ?_, rfl⟩
      show N.mkQ ⟨u, hUU'.le hu⟩ ∈ J
      have h0 : N.mkQ ⟨u, hUU'.le hu⟩ = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact hu
      rw [h0]
      exact J.zero_mem
    have hXU' : X ≤ U' := by
      rintro _ ⟨w, -, rfl⟩
      exact w.2
    have hXinv : ∀ g, ∀ v ∈ X, ρ g v ∈ X := by
      rintro g _ ⟨w, hw, rfl⟩
      exact ⟨⟨ρ g w, hU'inv g w w.2⟩, hJ g _ hw, rfl⟩
    rcases hmin X hUX hXU' hXinv with h | h
    · left
      rw [eq_bot_iff]
      intro s hs
      obtain ⟨w, rfl⟩ := N.mkQ_surjective s
      have hwX : (w : M) ∈ X := ⟨w, hs, rfl⟩
      rw [h] at hwX
      rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hwX
    · right
      rw [eq_top_iff]
      intro s _
      obtain ⟨w, rfl⟩ := N.mkQ_surjective s
      have hwX : (w : M) ∈ X := by
        rw [h]
        exact w.2
      obtain ⟨w', hw', hww'⟩ := hwX
      have e : w' = w := Subtype.ext hww'
      rw [← e]
      exact hw'
  have hntS : ∃ g s, ρS g s ≠ s := by
    refine ⟨g₀, N.mkQ ⟨v₀, hv₀⟩, ?_⟩
    rw [hρS]
    intro h
    exact hgv₀ ((hmkQ _ _).mp h)
  have hcardU' : Nat.card U' = Nat.card N * Nat.card (U' ⧸ N) :=
    Submodule.card_eq_card_quotient_mul_card N
  have hcardM : Nat.card M = Nat.card U' * Nat.card (M ⧸ U') :=
    Submodule.card_eq_card_quotient_mul_card U'
  have hNpos : 0 < Nat.card N := Nat.card_pos
  have hQpos : 0 < Nat.card (M ⧸ U') := Nat.card_pos
  have hSle : Nat.card (U' ⧸ N) ≤ 2 ^ 12 := by
    have h1 : Nat.card (U' ⧸ N) ≤ Nat.card U' := by
      rw [hcardU']
      exact Nat.le_mul_of_pos_left _ hNpos
    have h2 : Nat.card U' ≤ Nat.card M := by
      rw [hcardM]
      exact Nat.le_mul_of_pos_right _ hQpos
    have h3 : (2 : ℕ) ^ 6 ≤ 2 ^ 12 := by norm_num
    omega
  have htop : 16 ≤ Nat.card (U' ⧸ N) → U' = ⊤ := by
    intro h16
    apply eq_top_of_card_quot hspan hU'inv
    have h1 : 16 ≤ Nat.card U' := by
      rw [hcardU']
      exact h16.trans (Nat.le_mul_of_pos_left _ hNpos)
    have h2 : Nat.card U' * Nat.card (M ⧸ U') ≤ 2 ^ 6 := hcardM ▸ hcard
    by_contra hc
    push Not at hc
    have h3 : 16 * 5 ≤ Nat.card U' * Nat.card (M ⧸ U') := Nat.mul_le_mul h1 hc
    exact absurd (h3.trans h2) (by norm_num)
  rcases section_cases ρS hirrS hntS hSle with ⟨β, hβ⟩ | ⟨j, hj, Ψ, hΨ⟩
  ·
    exfalso
    have hcS : Nat.card (U' ⧸ N) = 2 ^ 6 :=
      (Nat.card_congr β.toEquiv).trans card_coreMod7
    have hU'top := htop (by rw [hcS]; norm_num)
    have hmemU' : ∀ v : M, v ∈ U' := fun v => hU'top ▸ Submodule.mem_top
    obtain ⟨j, hj⟩ := exists_not_mem_orbit h7
    have h0O : (0 : Fin 7) ∈ MulAction.orbit ↥H (0 : Fin 7) := MulAction.mem_orbit_self 0
    let f : (Fin 7 → ZMod 2) →+ ZMod 2 :=
      ∑ i ∈ Finset.univ.filter (· ∈ MulAction.orbit ↥H (0 : Fin 7)),
        Pi.evalAddMonoidHom (fun _ : Fin 7 => ZMod 2) i
    have hf : ∀ x, f x = ∑ i ∈ Finset.univ.filter (· ∈ MulAction.orbit ↥H (0 : Fin 7)), x i :=
      fun x => by simp [f]
    let e₃ : (U' ⧸ N) →+ (Fin 7 → ZMod 2) :=
      AddMonoidHom.toMultiplicative.symm ((G6.coreMod 7).subtype.comp β.toMonoidHom)
    let F : M →+ ZMod 2 := f.comp (e₃.comp (N.mkQ.toAddMonoidHom.comp
      (LinearEquiv.ofTop U' hU'top).symm.toLinearMap.toAddMonoidHom))
    have hF : ∀ v, F v = f (Multiplicative.toAdd
        ((β (Multiplicative.ofAdd (N.mkQ ⟨v, hmemU' v⟩)) : G6.PermMod 7))) := fun v => rfl
    have hker : AddSubgroup.toZModSubmodule 2 F.ker = ⊤ := hspan _ fun g hg v => by
      rw [AddSubgroup.mem_toZModSubmodule, AddMonoidHom.mem_ker, map_sub]
      refine sub_eq_zero.mpr ?_
      rw [hF, hF]
      have e1 : N.mkQ ⟨ρ g v, hmemU' _⟩ = ρS g (N.mkQ ⟨v, hmemU' v⟩) := rfl
      rw [e1, hβ, hf, hf, sum_orbit_permAct hg]
    obtain ⟨w₀, hw₀⟩ := N.mkQ_surjective
      (Multiplicative.toAdd (β.symm ⟨Multiplicative.ofAdd (pv 0 j), pv_mem_coreMod 0 j⟩))
    have h1 : F (w₀ : M) = 1 := by
      rw [hF]
      have e : (⟨(w₀ : M), hmemU' _⟩ : U') = w₀ := rfl
      rw [e, hw₀, ofAdd_toAdd, MulEquiv.apply_symm_apply, hf]
      simp only [toAdd_ofAdd, pv, Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single',
        Finset.mem_filter, Finset.mem_univ, true_and, h0O, hj, ite_true, ite_false, add_zero]
    have h2 : (w₀ : M) ∈ AddSubgroup.toZModSubmodule 2 F.ker := hker ▸ Submodule.mem_top
    rw [AddSubgroup.mem_toZModSubmodule, AddMonoidHom.mem_ker, h1] at h2
    exact one_ne_zero h2
  ·
    have hcS : Nat.card (U' ⧸ N) = 2 ^ 4 := by
      rw [← Nat.card_congr Ψ.toEquiv, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
        Fintype.card_fin]
    have hU'top := htop (by rw [hcS]; norm_num)
    have hmemU' : ∀ v : M, v ∈ U' := fun v => hU'top ▸ Submodule.mem_top
    have hUbot : U = ⊥ := by
      refine eq_bot_of_split hUtriv (fun v hv => ?_) fun C hC => hspan C fun g _ v => hC g v
      have h1 : ρS (gen7 false) (N.mkQ ⟨v, hmemU' v⟩) = N.mkQ ⟨v, hmemU' v⟩ := by
        rw [hρS]
        exact (hmkQ _ _).mpr hv
      have h2 : lin 4 (indBlk true j false) (Ψ.symm (N.mkQ ⟨v, hmemU' v⟩)) =
          Ψ.symm (N.mkQ ⟨v, hmemU' v⟩) := by
        apply Ψ.injective
        rw [hΨ, LinearEquiv.apply_symm_apply, h1]
      have h3 := lin_fpf hj h2
      have h4 : N.mkQ ⟨v, hmemU' v⟩ = 0 := by
        rw [← Ψ.apply_symm_apply (N.mkQ ⟨v, hmemU' v⟩), h3, map_zero]
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h4
      exact h4
    have hNone : Nat.card N = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      refine ⟨⟨fun x y => ?_⟩, inferInstance⟩
      have hx : ((x : U') : M) ∈ U := x.2
      have hy : ((y : U') : M) ∈ U := y.2
      rw [hUbot, Submodule.mem_bot] at hx hy
      exact Subtype.ext (Subtype.ext (hx.trans hy.symm))
    refine ⟨?_, fun C hC => ?_⟩
    · rw [← Nat.card_congr (LinearEquiv.ofTop U' hU'top).toEquiv, hcardU', hNone, hcS, one_mul]
    · rcases hmin C (hUbot ▸ bot_le) (hU'top ▸ le_top) hC with h | h
      · left
        rw [h, hUbot]
      · right
        rw [h, hU'top]

end CFSG.Quasithin.A7Q528
