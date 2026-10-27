module

public import Certificates.Certificate4218
public import CFSG.GH74.KGroups.L27
public import CFSG.GH74.KGroups.Generic2
public import CFSG.GH74.E2.Shapes

public section

namespace CFSG.Quasithin

open CFSG.GH74.KGroups CFSG.Quasithin.E217B1L27

namespace E217R4

theorem l27Check_sound {LP : List (Equiv.Perm (Fin 8))} (h : l27Check LP = true) :
    sList.Nodup ∧ sList.length = 8 ∧
    (∀ x ∈ sList, x ∈ LP ∧ x⁻¹ ∈ sList ∧ ∀ y ∈ sList, x * y ∈ sList) ∧
    z0 ∈ sList ∧ z0 * z0 = 1 ∧ z0 ≠ 1 ∧ (∀ s ∈ sList, z0 * s = s * z0) ∧
    (∀ g ∈ LP, g * z0 = z0 * g → g ∈ sList) ∧
    (∀ g ∈ LP, (∀ s ∈ sList, g * s * g⁻¹ ∈ sList) → g ∈ sList) := by
  simp only [l27Check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', Bool.eq_false_iff, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  refine ⟨h1, h2, fun x hx => ?_, h4, h5, h6, h7, fun g hg hc => ?_, fun g hg hs => ?_⟩
  · obtain ⟨⟨a, b⟩, c⟩ := h3 x hx
    exact ⟨a, b, c⟩
  · rcases h8 g hg with h | h
    · exact absurd hc h
    · exact h
  · rcases h9 g hg with h | h
    · exact absurd hs h
    · exact h

theorem l27_check_ok : l27Check (elemsT L27.QP) = true :=
  Certificates.certificate4218

@[expose] def listSubgroup8 (l : List (Equiv.Perm (Fin 8))) (hne : 0 < l.length)
    (hcl : ∀ x ∈ l, x⁻¹ ∈ l ∧ ∀ y ∈ l, x * y ∈ l) : Subgroup (Equiv.Perm (Fin 8)) where
  carrier := {x | x ∈ l}
  mul_mem' := fun {x y} hx hy => (hcl x hx).2 y hy
  one_mem' := by
    obtain ⟨x, hx⟩ := List.exists_mem_of_length_pos hne
    simpa using (hcl x hx).2 x⁻¹ (hcl x hx).1
  inv_mem' := fun {x} hx => (hcl x hx).1

theorem card_listSubgroup8 {l : List (Equiv.Perm (Fin 8))} {hne : 0 < l.length}
    {hcl : ∀ x ∈ l, x⁻¹ ∈ l ∧ ∀ y ∈ l, x * y ∈ l} (hnd : l.Nodup) :
    Nat.card (listSubgroup8 l hne hcl) = l.length := by
  have h1 : ((listSubgroup8 l hne hcl : Subgroup (Equiv.Perm (Fin 8))) :
      Set (Equiv.Perm (Fin 8))) = ↑l.toFinset := by
    ext x
    simp [listSubgroup8]
  show Nat.card ((listSubgroup8 l hne hcl : Subgroup (Equiv.Perm (Fin 8))) :
    Set (Equiv.Perm (Fin 8))) = l.length
  rw [h1, Nat.card_coe_set_eq, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd]

theorem l27_table
    {K : Type} [Group K] (hK : CFSG.GH74.E2.ShapeL27 K) (S : Subgroup K) (hS : IsPGroup 2 S)
    (hSi : ¬ 2 ∣ S.index) :
    Nat.card K = 168 ∧ Nat.card S = 8 ∧ (∀ g : K, (∀ s ∈ S, g * s * g⁻¹ ∈ S) → g ∈ S) ∧
      ∃ z ∈ S, z * z = 1 ∧ z ≠ 1 ∧ (∀ s ∈ S, z * s = s * z) ∧ ∀ g : K, g * z = z * g → g ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e0⟩ : Nonempty (K ≃* L27.QP.originalSubgroup) := by
    rcases hK with h | h
    · exact L27.equiv_of_lieModel h
    · exact L27.equiv_of_lieModel3 h
  have hQ := L27.QP_ok
  obtain ⟨hs_nd, hs_len, hs_cl, hz0, hz02, hz01, hz0c, hz0N, hs_norm⟩ :=
    l27Check_sound l27_check_ok
  have : Finite K := Finite.of_equiv _ e0.symm.toEquiv
  let S0 := listSubgroup8 sList (by rw [hs_len]; norm_num)
    (fun x hx => ⟨(hs_cl x hx).2.1, (hs_cl x hx).2.2⟩)
  have hmemP : ∀ y ∈ elemsT L27.QP, y ∈ L27.QP.originalSubgroup := fun y hy =>
    (mem_elemsT L27.QP hQ y).1 hy
  have hSP : S0 ≤ L27.QP.originalSubgroup := fun x hx => hmemP x (hs_cl x hx).1
  have hcardS : Nat.card S0 = 2 ^ 3 := by
    rw [card_listSubgroup8 hs_nd, hs_len]
    norm_num
  have hcardK : Nat.card K = 2 ^ 3 * 21 := by
    rw [Nat.card_congr e0.toEquiv, card_group L27.QP hQ, L27.QP_valid.2]
    norm_num
  obtain ⟨e', he'⟩ := exists_iso_of_sylow L27.QP.originalSubgroup e0 S0 hSP hcardS hcardK
    (by decide) (hS.toSylow hSi)
  have he'S : ∀ k : K, k ∈ S ↔ ((e' k : L27.QP.originalSubgroup) : Equiv.Perm (Fin 8)) ∈ sList :=
    fun k => show k ∈ S ↔ ((e' k : L27.QP.originalSubgroup) : Equiv.Perm (Fin 8)) ∈ S0 by
      simpa using he' k
  have hsurj : ∀ y ∈ L27.QP.originalSubgroup, ∃ k : K,
      ((e' k : L27.QP.originalSubgroup) : Equiv.Perm (Fin 8)) = y := fun y hy =>
    ⟨e'.symm ⟨y, hy⟩, by simp⟩
  have hLP : ∀ k : K, ((e' k : L27.QP.originalSubgroup) : Equiv.Perm (Fin 8)) ∈ elemsT L27.QP :=
    fun k => (mem_elemsT L27.QP hQ _).2 (e' k).2
  have hcoe : ∀ x y : K, ((e' (x * y) : L27.QP.originalSubgroup) : Equiv.Perm (Fin 8)) =
      ((e' x : L27.QP.originalSubgroup) : Equiv.Perm (Fin 8)) *
        ((e' y : L27.QP.originalSubgroup) : Equiv.Perm (Fin 8)) :=
    fun x y => by rw [map_mul, Subgroup.coe_mul]
  have hcoeinv : ∀ x : K, ((e' x⁻¹ : L27.QP.originalSubgroup) : Equiv.Perm (Fin 8)) =
      ((e' x : L27.QP.originalSubgroup) : Equiv.Perm (Fin 8))⁻¹ := fun x => by
    rw [map_inv, Subgroup.coe_inv]
  have hinj : ∀ x y : K, ((e' x : L27.QP.originalSubgroup) : Equiv.Perm (Fin 8)) =
      ((e' y : L27.QP.originalSubgroup) : Equiv.Perm (Fin 8)) → x = y := fun x y h =>
    e'.injective (Subtype.ext h)
  refine ⟨by rw [hcardK]; norm_num, ?_, ?_, ?_⟩
  · have hS' : S = S0.comap (L27.QP.originalSubgroup.subtype.comp e'.toMonoidHom) := by
      ext k
      exact (he'S k)
    have hle : S0 ≤ (L27.QP.originalSubgroup.subtype.comp e'.toMonoidHom).range := fun y hy => by
      obtain ⟨k, hk⟩ := hsurj y (hSP hy)
      exact ⟨k, hk⟩
    have hinj' : Function.Injective (L27.QP.originalSubgroup.subtype.comp e'.toMonoidHom) :=
      Subtype.val_injective.comp e'.injective
    rw [hS', ← Subgroup.card_map_of_injective hinj', Subgroup.map_comap_eq, inf_eq_right.2 hle,
      card_listSubgroup8 hs_nd, hs_len]
  · intro g hg
    refine (he'S g).2 (hs_norm _ (hLP g) fun s0 hs0 => ?_)
    obtain ⟨k, hk⟩ := hsurj s0 (hSP hs0)
    have hkS : k ∈ S := (he'S k).2 (hk ▸ hs0)
    have := (he'S _).1 (hg k hkS)
    rwa [hcoe, hcoe, hcoeinv, hk] at this
  · obtain ⟨z, hz⟩ := hsurj z0 (hmemP z0 (hs_cl z0 hz0).1)
    have hzS : z ∈ S := (he'S z).2 (hz ▸ hz0)
    refine ⟨z, hzS, hinj _ _ ?_, fun h => hz01 ?_, fun s hs => hinj _ _ ?_, fun g hg => ?_⟩
    · rw [hcoe, hz, hz02, map_one, Subgroup.coe_one]
    · rw [← hz, h, map_one, Subgroup.coe_one]
    · rw [hcoe, hcoe, hz]
      exact hz0c _ ((he'S s).1 hs)
    · have := congrArg (fun x : K => ((e' x : L27.QP.originalSubgroup) : Equiv.Perm (Fin 8))) hg
      simp only [hcoe, hz] at this
      exact (he'S g).2 (hz0N _ (hLP g) this)

end E217R4

end CFSG.Quasithin
