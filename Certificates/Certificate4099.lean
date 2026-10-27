module

public import Certificates.Kernel.LocalQT.Six4099
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115List

public section

namespace CFSG.KD.LQT.Six4099
open Equiv Equiv.Perm CFSG.QuasithinUnique.Ch1.AltSix

theorem foldl_set_getElem?_of_not_mem {α β : Type} (k : α → ℕ) (v : α → β)
    (hk : Function.Injective k) (x : α) :
    ∀ (l : List α) (t : Array β), x ∉ l →
      (l.foldl (fun t a => t.set! (k a) (v a)) t)[k x]? = t[k x]?
  | [], _, _ => rfl
  | y :: l, t, h => by
    rw [List.foldl_cons, foldl_set_getElem?_of_not_mem k v hk x l _
      fun hm => h (List.mem_cons_of_mem _ hm), Array.set!_eq_setIfInBounds,
      Array.getElem?_setIfInBounds_ne]
    exact fun e => h (hk e ▸ List.mem_cons_self)

theorem foldl_set_getElem?_of_mem {α β : Type} (k : α → ℕ) (v : α → β)
    (hk : Function.Injective k) (x : α) :
    ∀ (l : List α) (t : Array β), x ∈ l → k x < t.size →
      (l.foldl (fun t a => t.set! (k a) (v a)) t)[k x]? = some (v x)
  | y :: l, t, h, hs => by
    rw [List.foldl_cons]
    by_cases hm : x ∈ l
    · exact foldl_set_getElem?_of_mem k v hk x l _ hm (by simpa using hs)
    · obtain rfl : x = y := by simpa [hm] using h
      rw [foldl_set_getElem?_of_not_mem k v hk x l _ hm, Array.set!_eq_setIfInBounds,
        Array.getElem?_setIfInBounds_self_of_lt hs]

theorem permKey_injective : Function.Injective permKey := by
  intro σ τ h
  unfold permKey at h
  have := (σ 0).isLt
  have := (σ 1).isLt
  have := (σ 2).isLt
  have := (σ 3).isLt
  have := (σ 4).isLt
  have := (σ 5).isLt
  have := (τ 0).isLt
  have := (τ 1).isLt
  have := (τ 2).isLt
  have := (τ 3).isLt
  have := (τ 4).isLt
  have := (τ 5).isLt
  have e0 : (σ 0).val = (τ 0).val := by omega
  have e1 : (σ 1).val = (τ 1).val := by omega
  have e2 : (σ 2).val = (τ 2).val := by omega
  have e3 : (σ 3).val = (τ 3).val := by omega
  have e4 : (σ 4).val = (τ 4).val := by omega
  have e5 : (σ 5).val = (τ 5).val := by omega
  refine Equiv.ext fun i => Fin.ext ?_
  fin_cases i
  · exact e0
  · exact e1
  · exact e2
  · exact e3
  · exact e4
  · exact e5

theorem permKey_lt (σ : Perm (Fin 6)) : permKey σ < 46656 := by
  unfold permKey
  have := (σ 0).isLt
  have := (σ 1).isLt
  have := (σ 2).isLt
  have := (σ 3).isLt
  have := (σ 4).isLt
  have := (σ 5).isLt
  omega

theorem mem_perms6 (σ : Perm (Fin 6)) : σ ∈ permsOfList (List.finRange 6) :=
  mem_permsOfList_of_mem fun x _ => List.mem_finRange x

theorem flat_eq (σ : Perm (Fin 6)) : flat σ = σ := Equiv.ext fun i => tabOf_getD σ i

theorem not_decide_units (u : ℤˣ) : (!decide (u = 1)) = decide (-1 * u = 1) := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> decide

theorem castSucc_ne_succ (k : Fin 5) : k.castSucc ≠ k.succ :=
  (Fin.castSucc_lt_succ : k.castSucc < k.succ).ne

theorem pl_fst (l : List (Fin 6)) : (pl l).map Prod.fst = permsOfList l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [pl, permsOfList, ← ih, List.map_append, List.map_flatMap]
    simp only [List.map_map]
    rfl

theorem conj_trivial (τ : Perm (Fin 6)) (h : ∀ a : Perm (Fin 6), sign a = 1 → τ * a * τ⁻¹ = a) :
    τ = 1 := by
  have hc : ∀ a : Perm (Fin 6), sign a = 1 → τ * a = a * τ := fun a ha =>
    mul_inv_eq_iff_eq_mul.mp (h a ha)
  exact central6 τ (hc _ (by decide)) (hc _ (by decide)) (hc _ (by decide)) (hc _ (by decide))


theorem epsPerm_apply (σ : Perm (Fin 6)) (i : Fin 6) : epsPerm σ i = epsFun σ i := rfl

theorem epsFast_eq (a : Perm (Fin 6)) : epsFast a = epsPerm a := by
  have h := foldl_set_getElem?_of_mem permKey (fun a => flat (epsPerm a)) permKey_injective a
    (permsOfList (List.finRange 6)) (Array.replicate 46656 1) (mem_perms6 a)
    (by simpa using permKey_lt a)
  rw [epsFast, epsTable, Array.getD_eq_getD_getElem?, h, Option.getD_some, flat_eq]

theorem epsPerm_swap {a b : Fin 6} (h : a ≠ b) : epsPerm (swap a b) = epsT a b :=
  Equiv.ext fun i => epsT_ok a b h i

theorem epsPerm_epsPerm (σ : Perm (Fin 6)) : epsPerm (epsPerm σ) = σ := by
  have h : epsPerm.comp epsPerm = MonoidHom.id (Perm (Fin 6)) := by
    refine MonoidHom.eq_of_eqOn_denseM (mclosure_swap_castSucc_succ 5) ?_
    rintro _ ⟨k, rfl⟩
    rw [MonoidHom.comp_apply, MonoidHom.id_apply, epsPerm_swap (castSucc_ne_succ k)]
    exact Equiv.ext fun i => epsSq_ok k i
  exact DFunLike.congr_fun h σ

theorem sign_epsPerm (σ : Perm (Fin 6)) : sign (epsPerm σ) = sign σ := by
  have h : sign.comp epsPerm = sign := by
    refine MonoidHom.eq_of_eqOn_denseM (mclosure_swap_castSucc_succ 5) ?_
    rintro _ ⟨k, rfl⟩
    rw [MonoidHom.comp_apply, epsPerm_swap (castSucc_ne_succ k), sign_ok k,
      sign_swap (castSucc_ne_succ k)]
  exact DFunLike.congr_fun h σ

theorem pl_inv (l : List (Fin 6)) (hl : l.Nodup) :
    ∀ p ∈ pl l, p.2.1 = epsPerm p.1 ∧ p.2.2 = decide (sign p.1 = 1) := by
  induction l with
  | nil =>
    intro p hp
    rw [pl, List.mem_singleton] at hp
    subst hp
    exact ⟨(map_one epsPerm).symm, by simp⟩
  | cons a l ih =>
    have ha : a ∉ l := (List.nodup_cons.mp hl).1
    intro p hp
    rw [pl, List.mem_append, List.mem_flatMap] at hp
    rcases hp with hp | ⟨b, hb, hp⟩
    · exact ih hl.of_cons p hp
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      obtain ⟨h1, h2⟩ := ih hl.of_cons q hq
      have hab : a ≠ b := fun e => ha (e ▸ hb)
      refine ⟨?_, ?_⟩
      · rw [map_mul, epsPerm_swap hab, h1]
      · rw [h2, Perm.sign_mul, sign_swap hab]
        exact not_decide_units (sign q.1)

theorem mem_L (σ : Perm (Fin 6)) : (σ, epsPerm σ, decide (sign σ = 1)) ∈ L := by
  have hσ : σ ∈ L.map Prod.fst := by
    rw [L, pl_fst]
    exact mem_perms6 σ
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hσ
  obtain ⟨h1, h2⟩ := pl_inv _ (List.nodup_finRange 6) p hp
  rw [← h1, ← h2]
  exact hp

theorem card_fixed_eq (σ : Perm (Fin 6)) :
    (Finset.univ.filter fun a : Perm (Fin 6) => sign a = 1 ∧ σ * epsPerm a * σ⁻¹ = a).card =
      (L.filter fun q => q.2.2 && decide (σ * q.2.1 = q.1 * σ)).length := by
  set P : Perm (Fin 6) → Bool := fun a => decide (sign a = 1) && decide (σ * epsPerm a = a * σ)
  have hl := nodup_permsOfList (List.nodup_finRange 6)
  have hf : (Finset.univ.filter fun a : Perm (Fin 6) => sign a = 1 ∧ σ * epsPerm a * σ⁻¹ = a) =
      ((permsOfList (List.finRange 6)).filter P).toFinset := by
    ext a
    simp [P, mem_perms6, mul_inv_eq_iff_eq_mul]
  rw [hf, List.toFinset_card_of_nodup (hl.filter _), ← List.countP_eq_length_filter,
    ← List.countP_eq_length_filter, ← pl_fst, ← L, List.countP_map]
  refine List.countP_congr fun q hq => ?_
  obtain ⟨h1, h2⟩ := pl_inv _ (List.nodup_finRange 6) q hq
  simp [P, h1, h2]

end CFSG.KD.LQT.Six4099

namespace CFSG.QuasithinUnique.Ch1.AltSix
open Equiv Equiv.Perm CFSG.QuasithinUnique CFSG.KD.LQT.Six4099


private theorem stabilizer_trivial :
    ∀ σ : Perm (Fin 6), (∀ i, act σ (total i) = total i) → σ = 1 := by
  intro σ h
  have h1 : epsPerm σ = 1 := by
    refine Equiv.ext fun i => ?_
    rw [epsPerm_apply, Perm.one_apply]
    apply total_injective
    rw [← act_total_epsFun, h]
  rw [← epsPerm_epsPerm σ, h1, map_one]

private theorem sign_epsFast :
    ∀ σ : Perm (Fin 6), Perm.sign (epsFast σ) = Perm.sign σ := fun σ => by
  rw [epsFast_eq, sign_epsPerm]

private theorem support_epsPerm_threeCycle :
    (epsPerm (swap 0 1 * swap 1 2)).support.card = 6 := by
  rw [map_mul, epsPerm_swap (by decide), epsPerm_swap (by decide)]
  exact supp3

private theorem classification :
    ∀ (σ : Perm (Fin 6)) (b : Bool), DatumPremise σ b →
        b = false ∧ σ * σ = 1 ∧ σ ≠ 1 := by
  intro σ b h
  obtain ⟨hi, hii, hiii⟩ := h
  cases b with
  | false =>
    refine ⟨rfl, conj_trivial _ fun a ha => ?_, ?_⟩
    · have := hi a ha
      simp only [phi, twist] at this
      simpa only [mul_assoc, mul_inv_rev] using this
    · rintro rfl
      obtain ⟨a, _, ha⟩ := hiii
      exact ha (by simp [phi, twist])
  | true =>
    exfalso
    have hphi : ∀ a, phi σ true a = σ * epsPerm a * σ⁻¹ := fun a => by
      simp only [phi, twist, epsFast_eq]
    have hs : σ * epsPerm σ = 1 := conj_trivial _ fun a ha => by
      have := hi a ha
      rw [hphi, hphi] at this
      simp only [map_mul, map_inv, epsPerm_epsPerm] at this
      simpa only [mul_assoc, mul_inv_rev] using this
    have hcls := List.all_eq_true.mp clsTrue _ (mem_L σ)
    simp only [hphi] at hii
    rw [card_fixed_eq] at hii
    simp [hs, hii] at hcls

private theorem involution_types_fast :
    ∀ σ : Perm (Fin 6), σ * σ = 1 → σ ≠ 1 →
        Perm.sign σ = 1 ∨ σ.support.card = 2 ∨ (epsFast σ).support.card = 2 := by
  intro σ h1 h2
  rw [epsFast_eq]
  have := List.all_eq_true.mp invTypes _ (mem_L σ)
  simp only [h1, h2, Bool.or_eq_true, decide_eq_true_eq, decide_true, Bool.not_true,
    decide_false, Bool.false_or] at this
  tauto

end CFSG.QuasithinUnique.Ch1.AltSix

namespace Certificates

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.QuasithinUnique.Ch1.AltSix in
open Equiv Equiv.Perm CFSG.QuasithinUnique in
theorem certificate4099 : (∀ σ : Perm (Fin 6), (∀ i, act σ (total i) = total i) → σ = 1)
    ∧ (∀ a : Perm (Fin 6), epsFast a = epsPerm a)
    ∧ (∀ σ : Perm (Fin 6), Perm.sign (epsFast σ) = Perm.sign σ)
    ∧ ((epsPerm (swap 0 1 * swap 1 2)).support.card = 6)
    ∧ (∀ τ : Perm (Fin 6), τ * (swap 0 1 * swap 1 2) = (swap 0 1 * swap 1 2) * τ →
          τ * (swap 1 2 * swap 2 3) = (swap 1 2 * swap 2 3) * τ →
          τ * (swap 2 3 * swap 3 4) = (swap 2 3 * swap 3 4) * τ →
          τ * (swap 3 4 * swap 4 5) = (swap 3 4 * swap 4 5) * τ → τ = 1)
    ∧ (∀ (σ : Perm (Fin 6)) (b : Bool), DatumPremise σ b →
          b = false ∧ σ * σ = 1 ∧ σ ≠ 1)
    ∧ (∀ σ : Perm (Fin 6), σ * σ = 1 → σ ≠ 1 →
          Perm.sign σ = 1 ∨ σ.support.card = 2 ∨ (epsFast σ).support.card = 2) :=
  ⟨CFSG.QuasithinUnique.Ch1.AltSix.stabilizer_trivial, CFSG.KD.LQT.Six4099.epsFast_eq,
    CFSG.QuasithinUnique.Ch1.AltSix.sign_epsFast,
    CFSG.QuasithinUnique.Ch1.AltSix.support_epsPerm_threeCycle,
    CFSG.KD.LQT.Six4099.central6, CFSG.QuasithinUnique.Ch1.AltSix.classification,
    CFSG.QuasithinUnique.Ch1.AltSix.involution_types_fast⟩

end Certificates
