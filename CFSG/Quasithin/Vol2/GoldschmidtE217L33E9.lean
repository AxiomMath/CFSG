module

public import Certificates.Certificate4211
public import CFSG.GH74.KGroups.L33Tables

public section

namespace CFSG.Quasithin

open CFSG.GH74.KGroups CFSG.Quasithin.E217L33

namespace E217R4

theorem e9Check_sound {L : List (Equiv.Perm (Fin 26))} {t a b : Equiv.Perm (Fin 26)}
    (h : e9Check L t a b = true) :
    t ∈ L ∧ t * t = 1 ∧ t ≠ 1 ∧ (nine a b).Nodup ∧
      (∀ x ∈ nine a b, x ∈ L ∧ t * x * t⁻¹ = x⁻¹ ∧ x⁻¹ ∈ nine a b ∧
        ∀ y ∈ nine a b, x * y ∈ nine a b) ∧
      (∀ c ∈ L, c * t = t * c → ∀ x ∈ nine a b, c * x * c⁻¹ ∈ nine a b) ∧
      ∀ f ∈ nine a b, f = 1 ∨ (stabList L t f).length ≤ 12 := by
  simp only [e9Check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  refine ⟨h1, h2, h3, h4, fun x hx => ?_, fun c hc hct x hx => ?_, h7⟩
  · obtain ⟨⟨⟨hxL, hxt⟩, hxi⟩, hxy⟩ := h5 x hx
    exact ⟨hxL, hxt, hxi, fun y hy => by simpa using hxy y hy⟩
  · rcases h6 c hc with h | h
    · exact absurd hct h
    · simpa using h x hx

theorem l33_e9_ok :
    e9Check (elemsT L33.QP) L33.t0 ea eb = true :=
  Certificates.certificate4211

theorem l33_e9
    {X : Type} [Group X] (e : X ≃* L33.QP.originalSubgroup)
    {s : X} (hs : orderOf s = 2) :
    ∃ E : Subgroup X, Nat.card E = 9 ∧ (∀ x ∈ E, s * x * s⁻¹ = x⁻¹) ∧
      (∀ c : X, c * s = s * c → c ∈ Subgroup.normalizer (E : Set X)) ∧
      ∀ F ≤ E, Nat.card F = 3 → ∀ T' : Subgroup X, (∀ c ∈ T', c * s = s * c) →
        T' ≤ Subgroup.normalizer (F : Set X) → Nat.card T' ≤ 12 := by
  have hQ := L33.QP_ok
  obtain ⟨-, -, -, hnd, hnine, hcent, hstab⟩ := e9Check_sound l33_e9_ok
  have hs2 : s ^ 2 = 1 := by
    have := pow_orderOf_eq_one s
    rwa [hs] at this
  have hs1 : s ≠ 1 := fun h => by
    rw [h, orderOf_one] at hs
    omega
  obtain ⟨g, hgP, hg⟩ := invConjCheck_sound L33.QP hQ L33.inv_ok (e s : Equiv.Perm (Fin 26))
    (e s).2
    (by
      have := congrArg (fun z : X => ((e z : L33.QP.originalSubgroup) : Equiv.Perm (Fin 26))) hs2
      simpa [← Subgroup.coe_pow, ← map_pow] using this)
    (fun h => hs1 (e.injective (Subtype.ext (by simpa using h))))
  let f : X →* Equiv.Perm (Fin 26) :=
    { toFun := fun x => g⁻¹ * ((e x : L33.QP.originalSubgroup) : Equiv.Perm (Fin 26)) * g
      map_one' := by simp
      map_mul' := fun x y => by simp [mul_assoc] }
  have hfx : ∀ x, f x = g⁻¹ * ((e x : L33.QP.originalSubgroup) : Equiv.Perm (Fin 26)) * g :=
    fun x => rfl
  have hfinj : Function.Injective f := fun x y hxy => by
    rw [hfx, hfx] at hxy
    exact e.injective (Subtype.ext (mul_left_cancel (mul_right_cancel hxy)))
  have hfs : f s = L33.t0 := by
    rw [hfx, ← hg]
    group
  have hfL : ∀ x, f x ∈ elemsT L33.QP := fun x =>
    (mem_elemsT L33.QP hQ _).2 (L33.QP.originalSubgroup.mul_mem
      (L33.QP.originalSubgroup.mul_mem (L33.QP.originalSubgroup.inv_mem hgP) (e x).2) hgP)
  have hfsurj : ∀ y ∈ elemsT L33.QP, ∃ x, f x = y := fun y hy => by
    have hyP := (mem_elemsT L33.QP hQ y).1 hy
    have hz : g * y * g⁻¹ ∈ L33.QP.originalSubgroup :=
      L33.QP.originalSubgroup.mul_mem (L33.QP.originalSubgroup.mul_mem hgP hyP)
        (L33.QP.originalSubgroup.inv_mem hgP)
    refine ⟨e.symm ⟨_, hz⟩, ?_⟩
    rw [hfx, MulEquiv.apply_symm_apply]
    group
  let E₁ : Subgroup (Equiv.Perm (Fin 26)) :=
    { carrier := {x | x ∈ nine ea eb}
      mul_mem' := fun {x y} hx hy => (hnine x hx).2.2.2 y hy
      one_mem' := by simp [nine]
      inv_mem' := fun {x} hx => (hnine x hx).2.2.1 }
  have hE₁ : ∀ x, x ∈ E₁ ↔ x ∈ nine ea eb := fun x => Iff.rfl
  have hE₁card : Nat.card E₁ = 9 := by
    have h1 : (E₁ : Set (Equiv.Perm (Fin 26))) = ↑(nine ea eb).toFinset := by
      ext x
      simp [hE₁]
    show Nat.card (E₁ : Set (Equiv.Perm (Fin 26))) = 9
    rw [h1, Nat.card_coe_set_eq, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd]
    rfl
  refine ⟨E₁.comap f, ?_, ?_, ?_, ?_⟩
  · have hle : E₁ ≤ f.range := fun y hy => by
      obtain ⟨x, hx⟩ := hfsurj y ((hnine y hy).1)
      exact ⟨x, hx⟩
    rw [← Subgroup.card_map_of_injective hfinj, Subgroup.map_comap_eq, inf_eq_right.2 hle,
      hE₁card]
  · intro x hx
    apply hfinj
    rw [map_mul, map_mul, map_inv, hfs, map_inv]
    exact (hnine (f x) hx).2.1
  · intro c hc
    have key : ∀ d : X, d * s = s * d → ∀ x ∈ E₁.comap f, d * x * d⁻¹ ∈ E₁.comap f := by
      intro d hd x hx
      show f (d * x * d⁻¹) ∈ E₁
      rw [map_mul, map_mul, map_inv]
      refine hcent (f d) (hfL d) ?_ (f x) hx
      rw [← hfs, ← map_mul, ← map_mul, hd]
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨key c hc x, fun h => ?_⟩
    have := key c⁻¹ (Commute.inv_left (show Commute c s from hc)).eq _ h
    rwa [show c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x by group] at this
  · intro F hFE hF3 T' hT' hTF
    have hFne : F ≠ ⊥ := fun h => by
      rw [h, Subgroup.card_bot] at hF3
      omega
    obtain ⟨⟨x, hxF⟩, hx1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hFne
    have hx1 : x ≠ 1 := fun h => hx1' (Subtype.ext h)
    have hx3 : x ^ 3 = 1 := by
      have := pow_card_eq_one' (x := (⟨x, hxF⟩ : ↥F))
      rw [hF3] at this
      exact congrArg Subtype.val this
    have hord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
    have : Finite ↥F := Nat.finite_of_card_ne_zero (by rw [hF3]; norm_num)
    have hzF : Subgroup.zpowers x = F := by
      refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 hxF) ?_
      rw [Nat.card_zpowers, hord, hF3]
    have hy : f x ∈ nine ea eb := hFE hxF
    have hy1 : f x ≠ 1 := fun h => hx1 (hfinj (by rw [h, map_one]))
    have hbound := (hstab (f x) hy).resolve_left hy1
    have hmem : ∀ c : T', f c ∈ (stabList (elemsT L33.QP) L33.t0 (f x)).toFinset := by
      intro c
      rw [List.mem_toFinset, stabList, List.mem_filter]
      refine ⟨hfL c, ?_⟩
      have hct : f c * L33.t0 = L33.t0 * f c := by
        rw [← hfs, ← map_mul, ← map_mul, hT' c c.2]
      have hcx : (c : X) * x * (c : X)⁻¹ ∈ F := by
        have := Subgroup.mem_normalizer_iff.1 (hTF c.2) x
        exact this.1 hxF
      rw [← hzF, Subgroup.mem_zpowers_iff] at hcx
      obtain ⟨k, hk⟩ := hcx
      have hk3 : x ^ k = x ^ (k % 3) := by
        simpa [hord] using (zpow_mod_orderOf x k).symm
      have hcases : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
      have hfk : f c * f x * (f c)⁻¹ = f x ^ (k % 3) := by
        rw [← map_inv, ← map_mul, ← map_mul, ← map_zpow, ← hk3, hk]
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true]
      refine ⟨hct, ?_⟩
      rcases hcases with h | h | h
      · exfalso
        rw [h, zpow_zero] at hfk
        have : (c : X) * x * (c : X)⁻¹ = 1 :=
          hfinj (by rw [map_mul, map_mul, map_inv, hfk, map_one])
        exact hx1 (by simpa using this)
      · left
        rwa [h, zpow_one] at hfk
      · right
        rwa [h, zpow_two, ← pow_two] at hfk
    have hinj : Function.Injective fun c : T' =>
        (⟨f c, hmem c⟩ : ↥((stabList (elemsT L33.QP) L33.t0 (f x)).toFinset)) :=
      fun c d hcd => Subtype.ext (hfinj (congrArg Subtype.val hcd))
    have hcard := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_eq_fintype_card (α := ↥((stabList (elemsT L33.QP) L33.t0 (f x)).toFinset)),
      Fintype.card_coe] at hcard
    exact hcard.trans ((List.toFinset_card_le _).trans hbound)

end E217R4

end CFSG.Quasithin
