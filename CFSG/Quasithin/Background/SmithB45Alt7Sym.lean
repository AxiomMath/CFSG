module

public import CFSG.Quasithin.Background.SmithB45Alt7Triv
public import CFSG.Quasithin.Background.SmithB45AltBase
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57Basic

public section

namespace CFSG.Quasithin.B45Alt7

open Equiv Equiv.Perm CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X3E

theorem permAct_pv (σ : Perm (Fin 7)) (a b : Fin 7) :
    G6.permAct 7 σ (Multiplicative.ofAdd (pv a b)) = Multiplicative.ofAdd (pv (σ a) (σ b)) := by
  apply Multiplicative.toAdd.injective
  funext i
  rw [G6.permAct_apply, toAdd_ofAdd, toAdd_ofAdd]
  have h := congrFun (permL_single σ a) i
  have h' := congrFun (permL_single σ b) i
  rw [permL_apply] at h h'
  simp only [pv, Pi.add_apply]
  rw [h, h']

theorem fix_pv01 : ∀ y : G6.PermMod 7, y ∈ G6.coreMod 7 →
    G6.permAct 7 (c[2, 3, 4, 5, 6]) y = y → G6.permAct 7 (swap 0 1 * swap 2 3) y = y →
      y = 1 ∨ y = Multiplicative.ofAdd (pv 0 1) := by
  intro y
  rw [G6.mem_coreMod]
  revert y
  decide +kernel

@[expose] def pg (i j : Fin 7) : Perm (Fin 7) :=
  if sign (swap (swap 0 i 1) j * swap 0 i) = 1 then swap (swap 0 i 1) j * swap 0 i
  else swap (swap 0 i 1) j * swap 0 i * swap 5 6

theorem pg_facts : ∀ i j : Fin 7, i ≠ j →
    pg i j ∈ alternatingGroup (Fin 7) ∧ pg i j 0 = i ∧ pg i j 1 = j := by
  simp only [mem_alternatingGroup]
  decide +kernel

theorem coreMod_eq_prod : ∀ y : G6.PermMod 7, y ∈ G6.coreMod 7 →
    y = ∏ j : Fin 7, (if j ≠ 0 ∧ Multiplicative.toAdd y j = 1 then
      Multiplicative.ofAdd (pv 0 j) else 1) := by
  intro y
  rw [G6.mem_coreMod]
  revert y
  decide +kernel

theorem schur_coreMod (F : ↥(G6.coreMod 7) →* ↥(G6.coreMod 7)) (hFi : Function.Injective F)
    (hF : ∀ σ ∈ alternatingGroup (Fin 7), ∀ x : ↥(G6.coreMod 7),
      (F ⟨G6.permAct 7 σ x, G6.permAct_mem_coreMod σ x.2⟩ : G6.PermMod 7) =
        G6.permAct 7 σ (F x)) :
    ∀ x, F x = x := by
  classical
  let u : ↥(G6.coreMod 7) := ⟨Multiplicative.ofAdd (pv 0 1), pv_mem_coreMod 0 1⟩
  have hfixu : ∀ σ ∈ alternatingGroup (Fin 7), pv (σ 0) (σ 1) = pv 0 1 →
      G6.permAct 7 σ (F u : G6.PermMod 7) = F u := by
    intro σ hσ h01
    rw [← hF σ hσ u]
    congr 2
    apply Subtype.ext
    change G6.permAct 7 σ (Multiplicative.ofAdd (pv 0 1)) = Multiplicative.ofAdd (pv 0 1)
    rw [permAct_pv, h01]
  have hFu : F u = u := by
    have h1 := hfixu (c[2, 3, 4, 5, 6]) (by rw [mem_alternatingGroup]; decide) (by decide)
    have h2 := hfixu (swap 0 1 * swap 2 3) (by rw [mem_alternatingGroup]; decide) (by decide)
    rcases fix_pv01 _ (F u).2 h1 h2 with h | h
    · exfalso
      have hu1 : u = 1 := hFi ((Subtype.ext h).trans (map_one F).symm)
      have := congrArg (fun x : ↥(G6.coreMod 7) => Multiplicative.toAdd (x : G6.PermMod 7) 0) hu1
      simp [u, pv] at this
    · exact Subtype.ext h
  have hpair : ∀ j : Fin 7, j ≠ 0 →
      F ⟨Multiplicative.ofAdd (pv 0 j), pv_mem_coreMod 0 j⟩ =
        ⟨Multiplicative.ofAdd (pv 0 j), pv_mem_coreMod 0 j⟩ := by
    intro j hj
    obtain ⟨hgA, hg0, hg1⟩ := pg_facts 0 j (Ne.symm hj)
    have h1 : (⟨Multiplicative.ofAdd (pv 0 j), pv_mem_coreMod 0 j⟩ : ↥(G6.coreMod 7)) =
        ⟨G6.permAct 7 (pg 0 j) u, G6.permAct_mem_coreMod _ u.2⟩ := by
      apply Subtype.ext
      change Multiplicative.ofAdd (pv 0 j) = G6.permAct 7 (pg 0 j) (Multiplicative.ofAdd (pv 0 1))
      rw [permAct_pv, hg0, hg1]
    rw [h1]
    apply Subtype.ext
    rw [hF _ hgA u, hFu]
  let S : Subgroup (G6.PermMod 7) :=
    { carrier := {y | ∃ hy : y ∈ G6.coreMod 7, (F ⟨y, hy⟩ : G6.PermMod 7) = y}
      one_mem' := ⟨(G6.coreMod 7).one_mem, by
        have := map_one F
        exact congrArg Subtype.val this⟩
      mul_mem' := fun {a b} ⟨ha, ha'⟩ ⟨hb, hb'⟩ => ⟨(G6.coreMod 7).mul_mem ha hb, by
        have : F ⟨a * b, (G6.coreMod 7).mul_mem ha hb⟩ = F ⟨a, ha⟩ * F ⟨b, hb⟩ :=
          map_mul F ⟨a, ha⟩ ⟨b, hb⟩
        rw [this, Subgroup.coe_mul, ha', hb']⟩
      inv_mem' := fun {a} ⟨ha, ha'⟩ => ⟨(G6.coreMod 7).inv_mem ha, by
        change ((F ((⟨a, ha⟩ : ↥(G6.coreMod 7))⁻¹)) : G6.PermMod 7) = a⁻¹
        rw [map_inv, Subgroup.coe_inv, ha']
        rfl⟩ }
  intro x
  have hxS : (x : G6.PermMod 7) ∈ S := by
    rw [coreMod_eq_prod _ x.2]
    refine Subgroup.prod_mem _ fun j _ => ?_
    split_ifs with h
    · exact ⟨pv_mem_coreMod 0 j, congrArg Subtype.val (hpair j h.1)⟩
    · exact S.one_mem
  obtain ⟨hx, hx'⟩ := hxS
  exact Subtype.ext hx'

theorem card_coreMod7 : Nat.card (G6.coreMod 7) = 64 := by
  have h : (G6.coreMod 7 : Set (G6.PermMod 7)) =
      ↑(Finset.univ.filter fun x : G6.PermMod 7 => ∑ i, Multiplicative.toAdd x i = 0) := by
    ext x
    simp [G6.mem_coreMod]
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, h, Set.ncard_coe_finset]
  decide

theorem card_fix01 :
    Nat.card {y : G6.PermMod 7 // y ∈ G6.coreMod 7 ∧ G6.permAct 7 (swap 0 1) y = y} = 32 := by
  have h : {y : G6.PermMod 7 | y ∈ G6.coreMod 7 ∧ G6.permAct 7 (swap 0 1) y = y} =
      ↑(Finset.univ.filter fun x : G6.PermMod 7 =>
        ∑ i, Multiplicative.toAdd x i = 0 ∧ G6.permAct 7 (swap 0 1) x = x) := by
    ext x
    simp [G6.mem_coreMod]
  rw [← Set.coe_ofPred, Nat.card_coe_set_eq, h, Set.ncard_coe_finset]
  decide +kernel

section Sym

variable {V : Type} [CommGroup V] [Finite V] {G L : Subgroup (MulAut V)}

theorem qhatOf_le_one_of_not_le (hV : ∀ v : V, v ^ 2 = 1) (C : Bridge.Alt57.Ctx G L 7)
    (ι : ↥L ≃* A7) (e : ↥G →* Perm (Fin 7)) (hinj : Function.Injective e)
    (hL : ∀ l : ↥L, e ⟨(l : MulAut V), C.le_G l.2⟩ = (ι l : Perm (Fin 7)))
    (hconj : ∀ (g : ↥G) (l l' : ↥L), (g : MulAut V) * (l : MulAut V) * (g : MulAut V)⁻¹ =
      (l' : MulAut V) → (ι l' : Perm (Fin 7)) = e g * (ι l : Perm (Fin 7)) * (e g)⁻¹)
    (β : V ≃* ↥(G6.coreMod 7))
    (hβ : ∀ (γ : A7) (s : V), (β ((ι.symm γ : MulAut V) s) : G6.PermMod 7) =
      G6.permAct 7 (γ : Perm (Fin 7)) (β s))
    (hGL : ¬ G ≤ L) : qhatOf G ≤ ((1 : ℚ) : WithTop ℚ) := by
  classical
  obtain ⟨g, hgG, hgL⟩ := Set.not_subset.1 hGL
  set σ₀ : Perm (Fin 7) := e ⟨g, hgG⟩ with hσ₀def
  have hσ₀ : σ₀ ∉ alternatingGroup (Fin 7) := by
    intro h
    apply hgL
    obtain ⟨l, hl⟩ := ι.surjective ⟨σ₀, h⟩
    have h1 : (⟨(l : MulAut V), C.le_G l.2⟩ : ↥G) = ⟨g, hgG⟩ := hinj (by rw [hL, hl])
    have h2 : (l : MulAut V) = g := congrArg Subtype.val h1
    exact h2 ▸ l.2
  have hsign : sign σ₀ = -1 :=
    (Int.units_eq_one_or _).resolve_left fun h => hσ₀ (mem_alternatingGroup.2 h)
  have hτ : σ₀⁻¹ * swap 0 1 ∈ alternatingGroup (Fin 7) := by
    rw [mem_alternatingGroup, Perm.sign_mul, Perm.sign_inv, hsign, Perm.sign_swap (by decide)]
    decide
  set l₀ : ↥L := ι.symm ⟨_, hτ⟩ with hl₀
  set t : ↥G := ⟨g, hgG⟩ * ⟨(l₀ : MulAut V), C.le_G l₀.2⟩ with ht
  have het : e t = swap 0 1 := by
    rw [ht, map_mul, hL, hl₀, MulEquiv.apply_symm_apply, ← hσ₀def]
    group
  set T : MulAut V := (t : MulAut V) with hT
  have hconjA : ∀ γ : A7, swap 0 1 * (γ : Perm (Fin 7)) * swap 0 1 ∈ alternatingGroup (Fin 7) :=
    fun γ => by
      have := (alternatingGroup.normal (α := Fin 7)).conj_mem _ γ.2 (swap 0 1)
      rwa [swap_inv] at this
  have hTconj : ∀ γ : A7, T * (ι.symm γ : MulAut V) =
      (ι.symm ⟨_, hconjA γ⟩ : MulAut V) * T := by
    intro γ
    have hmem : T * (ι.symm γ : MulAut V) * T⁻¹ ∈ L := C.normal T t.2 _ (ι.symm γ).2
    have h1 := hconj t (ι.symm γ) ⟨_, hmem⟩ rfl
    rw [MulEquiv.apply_symm_apply, het, swap_inv] at h1
    have h2 : (⟨_, hmem⟩ : ↥L) = ι.symm ⟨_, hconjA γ⟩ := by
      rw [MulEquiv.eq_symm_apply]
      exact Subtype.ext h1
    have h3 := congrArg Subtype.val h2
    simp only at h3
    rw [← h3]
    group
  let P01 : ↥(G6.coreMod 7) →* ↥(G6.coreMod 7) :=
    ((G6.permAct 7 (swap 0 1)).toMonoidHom.comp (G6.coreMod 7).subtype).codRestrict _
      fun x => G6.permAct_mem_coreMod _ x.2
  have hP01 : ∀ x, (P01 x : G6.PermMod 7) = G6.permAct 7 (swap 0 1) x := fun x => rfl
  let F : ↥(G6.coreMod 7) →* ↥(G6.coreMod 7) :=
    P01.comp (β.toMonoidHom.comp (T.toMonoidHom.comp β.symm.toMonoidHom))
  have hF : ∀ x, F x = P01 (β (T (β.symm x))) := fun x => rfl
  have hFi : Function.Injective F := by
    intro x y h
    rw [hF, hF] at h
    have h1 : G6.permAct 7 (swap 0 1) (β (T (β.symm x)) : G6.PermMod 7) =
        G6.permAct 7 (swap 0 1) (β (T (β.symm y))) := by
      rw [← hP01, ← hP01, h]
    have h2 := (G6.permAct 7 (swap 0 1)).injective h1
    exact β.symm.injective (T.injective (β.injective (Subtype.ext h2)))
  have hβinv : ∀ (γ : A7) (x : ↥(G6.coreMod 7)),
      β.symm ⟨G6.permAct 7 (γ : Perm (Fin 7)) x, G6.permAct_mem_coreMod _ x.2⟩ =
        (ι.symm γ : MulAut V) (β.symm x) := by
    intro γ x
    rw [MulEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [hβ, MulEquiv.apply_symm_apply]
  have hFeq : ∀ σ ∈ alternatingGroup (Fin 7), ∀ x : ↥(G6.coreMod 7),
      (F ⟨G6.permAct 7 σ x, G6.permAct_mem_coreMod σ x.2⟩ : G6.PermMod 7) =
        G6.permAct 7 σ (F x) := by
    intro σ hσ x
    rw [hF, hF, hP01, hP01]
    have h1 := hβinv ⟨σ, hσ⟩ x
    simp only at h1
    rw [h1]
    have h2 : T ((ι.symm ⟨σ, hσ⟩ : MulAut V) (β.symm x)) =
        (ι.symm ⟨_, hconjA ⟨σ, hσ⟩⟩ : MulAut V) (T (β.symm x)) := by
      rw [← MulAut.mul_apply, hTconj, MulAut.mul_apply]
    rw [h2, hβ, ← MulAut.mul_apply, ← MulAut.mul_apply, ← map_mul, ← map_mul]
    congr 1
    simp only
    rw [← mul_assoc, ← mul_assoc, swap_mul_self, one_mul]
  have hFid := schur_coreMod F hFi hFeq
  have hTact : ∀ v : V, (β (T v) : G6.PermMod 7) = G6.permAct 7 (swap 0 1) (β v) := by
    intro v
    have h1 := hFid (β v)
    rw [hF, MulEquiv.symm_apply_apply] at h1
    have h2 := congrArg Subtype.val h1
    rw [hP01] at h2
    have h3 := congrArg (G6.permAct 7 (swap 0 1)) h2
    rw [← MulAut.mul_apply, ← map_mul, swap_mul_self, map_one, MulAut.one_apply] at h3
    exact h3
  have ht2 : T ^ 2 = 1 := by
    have h1 : t ^ 2 = 1 := hinj (by rw [map_pow, het, map_one, pow_two, swap_mul_self])
    have := congrArg Subtype.val h1
    simpa using this
  have hT1 : T ≠ 1 := by
    intro h
    have h1 : t = 1 := Subtype.ext h
    rw [h1, map_one] at het
    exact absurd het.symm (by decide)
  set A : Subgroup (MulAut V) := Subgroup.zpowers T with hA
  have hord : orderOf T = 2 := orderOf_eq_prime ht2 hT1
  have hA2 : Nat.card A = 2 := by rw [hA, Nat.card_zpowers, hord]
  have hAe : IsElemAbelian2 A := by
    refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
    · obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      rw [← zpow_add, ← zpow_add, add_comm]
    · obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ht2, one_zpow]
  have hAG : A ≤ G := Subgroup.zpowers_le.2 t.2
  have hA1 : A ≠ ⊥ := by
    intro h
    apply hT1
    have : T ∈ A := Subgroup.mem_zpowers T
    rw [h, Subgroup.mem_bot] at this
    exact this
  have hA3 : commSeries A 3 = ⊥ := by
    have h2 : commSeries A 2 = ⊥ :=
      (isQuadratic_iff_commSeries_two A).1 (isQuadratic_zpowers hV ht2)
    change commSub (commSeries A 2) A = ⊥
    rw [h2]
    exact commSub_bot_left A
  have hfixcard : Nat.card (fixV A) = 32 := by
    rw [← card_fix01]
    refine Nat.card_congr
      { toFun := fun v => ⟨β v, (β v).2, ?_⟩
        invFun := fun y => ⟨β.symm ⟨y.1, y.2.1⟩, ?_⟩
        left_inv := fun v => Subtype.ext (by simp)
        right_inv := fun y => Subtype.ext (by simp) }
    · rw [← hTact]
      have hv : T v = v := mem_fixV_zpowers_iff.1 v.2
      rw [hv]
    · rw [hA, mem_fixV_zpowers_iff]
      apply β.injective
      apply Subtype.ext
      rw [hTact, MulEquiv.apply_symm_apply]
      exact y.2.2
  have hcardV : Nat.card V = 64 := by
    rw [← card_coreMod7]
    exact Nat.card_congr β.toEquiv
  have hidx : (fixV A).index ≤ Nat.card A := by
    have e1 := (fixV A).card_mul_index
    rw [hfixcard, hcardV] at e1
    rw [hA2]
    omega
  exact B45Alt.qhatOf_le_one_of_index_le hV ⟨hAG, hA1, hAe⟩ hA3 hidx

end Sym

end CFSG.Quasithin.B45Alt7
