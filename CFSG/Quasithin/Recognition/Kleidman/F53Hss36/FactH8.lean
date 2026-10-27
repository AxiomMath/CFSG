module

public import CFSG.Quasithin.Recognition.Kleidman.F53Hss36.SevenCover

public section

namespace CFSG.Quasithin.Kleidman.F53Hss36

open Equiv

theorem even_pow_eight : ∀ y : Perm (Fin 5), Perm.sign y = 1 → y ^ 8 = 1 → y * y = 1 := by
  decide +kernel

theorem card_evenInvFix : ∀ p₀ : Fin 5,
    (Finset.univ.filter (fun y : Perm (Fin 5) => Perm.sign y = 1 ∧ y * y = 1 ∧ y p₀ = p₀)).card
      = 4 := by
  decide +kernel

theorem factH8 : FactH8 := by
  intro P hP p₀ hfix y
  set S : Subgroup (Perm (Fin 5)) := P ⊓ alternatingGroup (Fin 5) with hS
  have hsub : ∀ z ∈ S, Perm.sign z = 1 ∧ z * z = 1 ∧ z p₀ = p₀ := by
    intro z hz
    have hzP : z ∈ P := hz.1
    have hsg : Perm.sign z = 1 := Perm.mem_alternatingGroup.mp hz.2
    have hord : orderOf (⟨z, hzP⟩ : P) ∣ 8 := hP ▸ orderOf_dvd_natCard _
    have h8 : z ^ 8 = 1 := by
      have := (orderOf_dvd_iff_pow_eq_one.mp hord)
      simpa [Subtype.ext_iff] using congrArg Subtype.val this
    exact ⟨hsg, even_pow_eight z hsg h8, hfix z hzP⟩
  have hidx : S.relIndex P ≤ 2 := by
    have hker : S.subgroupOf P = (Perm.sign.comp P.subtype).ker := by
      ext z
      simp [hS, Subgroup.mem_subgroupOf, Perm.mem_alternatingGroup, MonoidHom.mem_ker]
    unfold Subgroup.relIndex
    rw [hker, Subgroup.index_ker]
    have : Nat.card (Perm.sign.comp P.subtype).range ≤ Nat.card ℤˣ :=
      Nat.card_le_card_of_injective (fun a => (a : ℤˣ)) Subtype.val_injective
    have h2 : Nat.card ℤˣ = 2 := by simp
    omega
  have hcardS : 4 ≤ Nat.card S := by
    have h1 := Subgroup.relIndex_mul_card (H := S) (K := P)
    have hSP : S ⊓ P = S := inf_of_le_left inf_le_left
    rw [hSP, hP] at h1
    have hpos : 0 < Nat.card S := Nat.card_pos
    by_contra hlt
    have : S.relIndex P * Nat.card S ≤ 2 * 3 := Nat.mul_le_mul hidx (by omega)
    omega
  let V : Set (Perm (Fin 5)) := {z | Perm.sign z = 1 ∧ z * z = 1 ∧ z p₀ = p₀}
  have hVfin : V.Finite := Set.toFinite _
  have hVcard : V.ncard = 4 := by
    have : V = ↑(Finset.univ.filter (fun z : Perm (Fin 5) =>
        Perm.sign z = 1 ∧ z * z = 1 ∧ z p₀ = p₀)) := by ext z; simp [V]
    rw [this, Set.ncard_coe_finset]
    exact card_evenInvFix p₀
  have hSV : (S : Set (Perm (Fin 5))) ⊆ V := fun z hz => hsub z hz
  have hSeq : (S : Set (Perm (Fin 5))) = V := by
    apply Set.eq_of_subset_of_ncard_le hSV _ hVfin
    rw [hVcard, ← Nat.card_coe_set_eq]
    exact hcardS
  constructor
  · intro hy
    exact hsub y hy
  · intro hy
    have : y ∈ (S : Set (Perm (Fin 5))) := hSeq ▸ hy
    exact this

end CFSG.Quasithin.Kleidman.F53Hss36
