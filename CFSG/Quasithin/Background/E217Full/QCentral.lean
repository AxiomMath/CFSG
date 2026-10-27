module

public import CFSG.Quasithin.Background.Module

public section

namespace CFSG.Quasithin.E217Full.LemmaQ

open CFSG.Quasithin

variable {V : Type*} [CommGroup V]

theorem exists_central_involution [Finite V] {X : Subgroup (MulAut V)} (hX : IsPGroup 2 X)
    (hne : X ≠ ⊥) : ∃ z ∈ X, z ≠ 1 ∧ z * z = 1 ∧ ∀ x ∈ X, x * z = z * x := by
  haveI : Finite (MulAut V) := Finite.of_injective _ (DFunLike.coe_injective (F := MulAut V))
  haveI : Nontrivial X := (Subgroup.nontrivial_iff_ne_bot X).mpr hne
  haveI : Nontrivial (Subgroup.center X) := hX.center_nontrivial
  have hZp : IsPGroup 2 (Subgroup.center X) := hX.to_subgroup (Subgroup.center X)
  have hdvd : 2 ∣ Nat.card (Subgroup.center X) := by
    obtain ⟨n, hn0, hn⟩ := hZp.nontrivial_iff_card.mp inferInstance
    rw [hn]
    exact dvd_pow_self 2 hn0.ne'
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hz : orderOf ((c : X) : MulAut V) = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hc]
  refine ⟨((c : X) : MulAut V), (c : X).2, ?_, ?_, ?_⟩
  · intro h
    rw [h, orderOf_one] at hz
    norm_num at hz
  · rw [← sq]
    have h2 := pow_orderOf_eq_one ((c : X) : MulAut V)
    rwa [hz] at h2
  · intro x hx
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp c.2 ⟨x, hx⟩)

end CFSG.Quasithin.E217Full.LemmaQ
