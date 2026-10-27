module

public import CFSG.Quasithin.Vol2.Ch12Sec6E16
public import CFSG.Quasithin.Vol2.Ch12Sec6L1a

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126E Equiv

namespace S126F

@[expose] noncomputable def fixD (P : Subgroup (Perm (Fin 8))) : Subgroup D8 where
  carrier := {y | ∀ σ ∈ P, dAct σ y = y}
  one_mem' := fun σ _ => map_one (dAct σ)
  mul_mem' := fun {a b} ha hb σ hσ => by rw [map_mul, ha σ hσ, hb σ hσ]
  inv_mem' := fun {a} ha σ hσ => by rw [map_inv, ha σ hσ]

theorem mem_fixD {P : Subgroup (Perm (Fin 8))} {y : D8} : y ∈ fixD P ↔ ∀ σ ∈ P, dAct σ y = y :=
  ⟨fun h => h, fun h => h⟩

theorem zmod2_eq_of_add : ∀ a b : ZMod 2, a + b = 0 → a = b := by
  decide

theorem zmod2_cases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by
  decide

theorem zmod2_add_add : ∀ a b c : ZMod 2, (a + c) + (b + c) = a + b := by
  decide

@[expose] def nrm : PermMod 8 →* PermMod 8 where
  toFun x := Multiplicative.ofAdd fun i => Multiplicative.toAdd x i + Multiplicative.toAdd x 0
  map_one' := by
    apply Multiplicative.toAdd.injective
    funext i
    simp
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    funext i
    simp only [toAdd_ofAdd, toAdd_mul, Pi.add_apply]
    ring

theorem nrm_apply (x : PermMod 8) (i : Fin 8) :
    Multiplicative.toAdd (nrm x) i = Multiplicative.toAdd x i + Multiplicative.toAdd x 0 := rfl

theorem nrm_allOnes : nrm (allOnes 8) = 1 := by
  apply Multiplicative.toAdd.injective
  funext i
  rw [nrm_apply]
  revert i
  decide

theorem natKer_le_ker : natKer 8 ≤ (nrm.comp (coreMod 8).subtype).ker := by
  intro m hm
  have hm' : (m : PermMod 8) ∈ Subgroup.zpowers (allOnes 8) := hm
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hm'
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype, ← hk, map_zpow, nrm_allOnes,
    one_zpow]

@[expose] noncomputable def iota : D8 →* PermMod 8 :=
  QuotientGroup.lift (natKer 8) (nrm.comp (coreMod 8).subtype) natKer_le_ker

theorem iota_mk (m : ↥(coreMod 8)) : iota (QuotientGroup.mk m) = nrm m := rfl

theorem iota_inj : Function.Injective iota := by
  rw [injective_iff_map_eq_one]
  intro y hy
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective y
  rw [iota_mk] at hy
  have h : ∀ i, Multiplicative.toAdd (m : PermMod 8) i =
      Multiplicative.toAdd (m : PermMod 8) 0 := fun i => by
    have h1 := congrArg (fun x : PermMod 8 => (Multiplicative.toAdd x : Fin 8 → ZMod 2) i) hy
    simp only [nrm_apply, toAdd_one, Pi.zero_apply] at h1
    exact zmod2_eq_of_add _ _ h1
  refine (QuotientGroup.eq_one_iff _).2 ?_
  change (m : PermMod 8) ∈ Subgroup.zpowers (allOnes 8)
  rcases zmod2_cases (Multiplicative.toAdd (m : PermMod 8) 0) with h0 | h0
  · have hm1 : (m : PermMod 8) = 1 := Multiplicative.toAdd.injective (funext fun i => by
      rw [h i, h0]
      rfl)
    rw [hm1]
    exact Subgroup.one_mem _
  · have hm1 : (m : PermMod 8) = allOnes 8 := Multiplicative.toAdd.injective (funext fun i => by
      rw [h i, h0]
      rfl)
    rw [hm1]
    exact Subgroup.mem_zpowers _

theorem iota_zero (y : D8) : Multiplicative.toAdd (iota y) 0 = 0 := by
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective y
  rw [iota_mk, nrm_apply]
  exact CharTwo.add_self_eq_zero _

theorem sum_add_zero : ∀ x : Fin 8 → ZMod 2, ∑ i, x i = 0 → ∑ i, (x i + x 0) = 0 := by
  decide +kernel

theorem iota_sum (y : D8) : ∑ i, Multiplicative.toAdd (iota y) i = 0 := by
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective y
  exact sum_add_zero _ m.2

theorem iota_dAct (σ : Perm (Fin 8)) (y : D8) (i : Fin 8) :
    Multiplicative.toAdd (iota (dAct σ y)) i =
      Multiplicative.toAdd (iota y) (σ⁻¹ i) + Multiplicative.toAdd (iota y) (σ⁻¹ 0) := by
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective y
  rw [dAct_mk, iota_mk, iota_mk, nrm_apply, nrm_apply, nrm_apply, coreAct_coe, permAct_apply,
    permAct_apply, zmod2_add_add]

theorem cond_of_fix {σ : Perm (Fin 8)} {y : D8} (h : dAct σ y = y) (i : Fin 8) :
    Multiplicative.toAdd (iota y) (σ⁻¹ i) + Multiplicative.toAdd (iota y) (σ⁻¹ 0) =
      Multiplicative.toAdd (iota y) i := by
  rw [← iota_dAct, h]

@[expose] def emb (z : Fin 6 → ZMod 2) : Fin 8 → ZMod 2 :=
  ![0, z 0, z 1, z 2, z 3, z 4, z 5, z 0 + z 1 + z 2 + z 3 + z 4 + z 5]

@[expose] def cmp (x : Fin 8 → ZMod 2) : Fin 6 → ZMod 2 := fun j => x j.succ.castSucc

theorem emb_cmp : ∀ x : Fin 8 → ZMod 2, x 0 = 0 → ∑ i, x i = 0 → emb (cmp x) = x := by
  decide +kernel

theorem cmp_emb : ∀ z : Fin 6 → ZMod 2, cmp (emb z) = z := by
  decide +kernel

theorem sum_emb : ∀ z : Fin 6 → ZMod 2, ∑ i, emb z i = 0 := by
  decide +kernel

theorem emb_zero (z : Fin 6 → ZMod 2) : emb z 0 = 0 := rfl

theorem emb_iota (y : D8) :
    emb (cmp (Multiplicative.toAdd (iota y))) = Multiplicative.toAdd (iota y) :=
  emb_cmp _ (iota_zero y) (iota_sum y)

theorem card_D8 : 64 ≤ Nat.card D8 := by
  let f : (Fin 6 → ZMod 2) → D8 := fun z =>
    QuotientGroup.mk ⟨Multiplicative.ofAdd (emb z), (mem_coreMod).2 (sum_emb z)⟩
  have hf : Function.Injective f := by
    intro z₁ z₂ h
    have h1 := congrArg (fun y => cmp (Multiplicative.toAdd (iota y))) h
    have e : ∀ z : Fin 6 → ZMod 2, cmp (Multiplicative.toAdd (iota (f z))) = z := fun z => by
      have : Multiplicative.toAdd (iota (f z)) = emb z := by
        funext i
        change Multiplicative.toAdd (nrm (Multiplicative.ofAdd (emb z))) i = emb z i
        rw [nrm_apply, toAdd_ofAdd, emb_zero, add_zero]
      rw [this, cmp_emb]
    simpa only [e] using h1
  have h := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_eq_fintype_card (α := Fin 6 → ZMod 2), Fintype.card_fun, ZMod.card,
    Fintype.card_fin] at h

@[expose] def cnt (S : List (Fin 4 × Fin 4)) : ℕ :=
  (Finset.univ.filter fun z : Fin 6 → ZMod 2 =>
    ∀ p ∈ S, ∀ i : Fin 8, emb z (tf p.1 p.2 i) + emb z (tf p.1 p.2 0) = emb z i).card

theorem card_fixD_le (P : Subgroup (Perm (Fin 8))) (S : List (Fin 4 × Fin 4))
    (hS : ∀ p ∈ S, tau p.1 p.2 ∈ P) : Nat.card (fixD P) ≤ cnt S := by
  let s := Finset.univ.filter fun z : Fin 6 → ZMod 2 =>
    ∀ p ∈ S, ∀ i : Fin 8, emb z (tf p.1 p.2 i) + emb z (tf p.1 p.2 0) = emb z i
  have hmem : ∀ y : fixD P, cmp (Multiplicative.toAdd (iota y)) ∈ s := by
    intro y
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, fun p hp i => ?_⟩
    rw [emb_iota]
    have h1 := cond_of_fix (y.2 _ (hS p hp)) i
    rwa [tau_inv_apply, tau_inv_apply] at h1
  have hinj : Function.Injective fun y : fixD P => (⟨_, hmem y⟩ : s) := by
    intro y₁ y₂ h
    have h1 : cmp (Multiplicative.toAdd (iota y₁)) = cmp (Multiplicative.toAdd (iota y₂)) :=
      congrArg Subtype.val h
    have h2 : Multiplicative.toAdd (iota y₁) = Multiplicative.toAdd (iota y₂) := by
      rw [← emb_iota y₁, ← emb_iota y₂, h1]
    exact Subtype.ext (iota_inj (Multiplicative.toAdd.injective h2))
  have h := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_eq_finsetCard] at h
  exact h

theorem cnt1 : ∀ u v : Fin 4, (u, v) ≠ (0, 0) → cnt [(u, v)] ≤ 16 := by
  decide +kernel

theorem cnt2 : ∀ u v u' v' : Fin 4, (u, v) ≠ (0, 0) → (u', v') ≠ (0, 0) → (u', v') ≠ (u, v) →
    cnt [(u, v), (u', v')] ≤ 8 := by
  decide +kernel

theorem cnt3 : ∀ u v w₁ w₂ : Fin 4, (u ≠ 0 ∧ v ≠ 0) → ((w₁, w₂) ≠ (0, 0) ∧ (w₁, w₂) ≠ (u, 0) ∧
    (w₁, w₂) ≠ (0, v) ∧ (w₁, w₂) ≠ (u, v)) → cnt [(u, 0), (0, v), (w₁, w₂)] ≤ 4 := by
  decide +kernel

theorem cnt4 : cnt [(1, 0), (2, 0), (0, 1), (0, 2)] ≤ 2 := by
  decide +kernel

theorem card_le_of_forall_mem (P : Subgroup (Perm (Fin 8))) (s : Finset (Perm (Fin 8)))
    (h : ∀ x ∈ P, x ∈ s) : Nat.card P ≤ s.card := by
  have hinj : Function.Injective fun x : P => (⟨x, h x x.2⟩ : s) := fun a b hab => by
    have h1 := congrArg Subtype.val hab
    exact Subtype.ext h1
  have h1 := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_eq_finsetCard] at h1

theorem tf_four : ∀ u v : Fin 4, (tf u v 4).val % 4 = v.val := by
  decide

theorem tf_zero_val : ∀ u v : Fin 4, (tf u v 0).val % 4 = u.val := by
  decide

theorem exists_K1 (P : Subgroup (Perm (Fin 8))) (hP : P ≤ E16) (h4 : 4 < Nat.card P) :
    ∃ u : Fin 4, u ≠ 0 ∧ tau u 0 ∈ P := by
  by_contra hK
  push Not at hK
  let f : P → Fin 4 := fun σ => ⟨((σ : Perm (Fin 8)) 4).val % 4, Nat.mod_lt _ (by norm_num)⟩
  have hf : Function.Injective f := by
    rintro ⟨σ₁, hσ₁⟩ ⟨σ₂, hσ₂⟩ h
    obtain ⟨a, b, rfl⟩ := hP hσ₁
    obtain ⟨a', b', rfl⟩ := hP hσ₂
    have hb : b = b' := Fin.ext (by
      have := congrArg Fin.val h
      simp only [f, tau_apply, tf_four] at this
      exact this)
    subst hb
    have hm : tau a b * tau a' b ∈ P := by
      have := P.mul_mem (P.inv_mem hσ₁) hσ₂
      rwa [tau_inv] at this
    rw [tau_mul, xr_self] at hm
    by_cases ha : xr a a' = 0
    · obtain rfl := eq_of_xr_eq_zero a a' ha
      rfl
    · exact absurd hm (hK _ ha)
  have h1 := Nat.card_le_card_of_injective f hf
  rw [Nat.card_fin] at h1
  omega

theorem exists_K2 (P : Subgroup (Perm (Fin 8))) (hP : P ≤ E16) (h4 : 4 < Nat.card P) :
    ∃ v : Fin 4, v ≠ 0 ∧ tau 0 v ∈ P := by
  by_contra hK
  push Not at hK
  let f : P → Fin 4 := fun σ => ⟨((σ : Perm (Fin 8)) 0).val % 4, Nat.mod_lt _ (by norm_num)⟩
  have hf : Function.Injective f := by
    rintro ⟨σ₁, hσ₁⟩ ⟨σ₂, hσ₂⟩ h
    obtain ⟨a, b, rfl⟩ := hP hσ₁
    obtain ⟨a', b', rfl⟩ := hP hσ₂
    have ha : a = a' := Fin.ext (by
      have := congrArg Fin.val h
      simp only [f, tau_apply, tf_zero_val] at this
      exact this)
    subst ha
    have hm : tau a b * tau a b' ∈ P := by
      have := P.mul_mem (P.inv_mem hσ₁) hσ₂
      rwa [tau_inv] at this
    rw [tau_mul, xr_self] at hm
    by_cases hb : xr b b' = 0
    · obtain rfl := eq_of_xr_eq_zero b b' hb
      rfl
    · exact absurd hm (hK _ hb)
  have h1 := Nat.card_le_card_of_injective f hf
  rw [Nat.card_fin] at h1
  omega

theorem eq_bot_of_le_E16 (P : Subgroup (Perm (Fin 8))) (hP : P ≤ E16)
    (h64 : 64 ≤ Nat.card P * Nat.card (fixD P)) : P = ⊥ := by
  by_contra hne
  obtain ⟨p, hpP, hp1⟩ := (Subgroup.bot_or_exists_ne_one P).resolve_left hne
  obtain ⟨u, v, rfl⟩ := hP hpP
  have huv : (u, v) ≠ (0, 0) := fun h => hp1 (tau_eq_one_iff.2 (Prod.mk.inj h))
  have hP16 : Nat.card P ≤ 16 := (Subgroup.card_le_of_le hP).trans card_E16_le
  have hf1 : Nat.card (fixD P) ≤ 16 :=
    (card_fixD_le P [(u, v)] (by simpa using hpP)).trans (cnt1 u v huv)
  by_cases hc3 : Nat.card P ≤ 3
  · have := Nat.mul_le_mul hc3 hf1
    omega
  obtain ⟨q, hqP, hq⟩ : ∃ q ∈ P, q ∉ ({1, tau u v} : Finset (Perm (Fin 8))) := by
    by_contra h
    push Not at h
    have h1 := card_le_of_forall_mem P _ h
    have h2 : ({1, tau u v} : Finset (Perm (Fin 8))).card ≤ 2 := Finset.card_le_two
    omega
  obtain ⟨u', v', rfl⟩ := hP hqP
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hq
  have hq1 : (u', v') ≠ (0, 0) := fun h => hq.1 (tau_eq_one_iff.2 (Prod.mk.inj h))
  have hq2 : (u', v') ≠ (u, v) := fun h => by
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact hq.2 rfl
  have hf2 : Nat.card (fixD P) ≤ 8 := by
    refine (card_fixD_le P [(u, v), (u', v')] fun p hp => ?_).trans (cnt2 u v u' v' huv hq1 hq2)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    exacts [hpP, hqP]
  by_cases hc7 : Nat.card P ≤ 7
  · have := Nat.mul_le_mul hc7 hf2
    omega
  obtain ⟨a, ha, haP⟩ := exists_K1 P hP (by omega)
  obtain ⟨b, hb, hbP⟩ := exists_K2 P hP (by omega)
  obtain ⟨r, hrP, hr⟩ : ∃ r ∈ P,
      r ∉ ({1, tau a 0, tau 0 b, tau a b} : Finset (Perm (Fin 8))) := by
    by_contra h
    push Not at h
    have h1 := card_le_of_forall_mem P _ h
    have h2 : ({1, tau a 0, tau 0 b, tau a b} : Finset (Perm (Fin 8))).card ≤ 4 :=
      Finset.card_le_four
    omega
  obtain ⟨w₁, w₂, rfl⟩ := hP hrP
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hr
  obtain ⟨hr1, hr2, hr3, hr4⟩ := hr
  have hw : (w₁, w₂) ≠ (0, 0) ∧ (w₁, w₂) ≠ (a, 0) ∧ (w₁, w₂) ≠ (0, b) ∧ (w₁, w₂) ≠ (a, b) := by
    refine ⟨fun h => hr1 (tau_eq_one_iff.2 (Prod.mk.inj h)), fun h => ?_, fun h => ?_,
      fun h => ?_⟩ <;>
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      first | exact hr2 rfl | exact hr3 rfl | exact hr4 rfl
  have hf3 : Nat.card (fixD P) ≤ 4 := by
    refine (card_fixD_le P [(a, 0), (0, b), (w₁, w₂)] fun p hp => ?_).trans
      (cnt3 a b w₁ w₂ ⟨ha, hb⟩ hw)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    exacts [haP, hbP, hrP]
  by_cases hc15 : Nat.card P ≤ 15
  · have := Nat.mul_le_mul hc15 hf3
    omega
  have hPE : P = E16 := Subgroup.eq_of_le_of_card_ge hP (by have := card_E16_le; omega)
  have hf4 : Nat.card (fixD P) ≤ 2 := by
    refine (card_fixD_le P [(1, 0), (2, 0), (0, 1), (0, 2)] fun p _ => ?_).trans cnt4
    rw [hPE]
    exact tau_mem _ _
  have := Nat.mul_le_mul hP16 hf4
  omega

end S126F

end CFSG.Quasithin.H13
