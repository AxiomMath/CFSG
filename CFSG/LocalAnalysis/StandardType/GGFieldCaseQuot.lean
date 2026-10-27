module

public import Mathlib.GroupTheory.FiniteAbelian.Basic

public section

namespace CFSG.StandardType

theorem exists_monoidHom_zmod_ne_one_of_commGroup {A : Type*} [CommGroup A] [Finite A] {p : ℕ}
    [hp : Fact p.Prime] {a : A} (ha : a ≠ 1) (hap : a ^ p = 1) :
    ∃ ψ : A →* Multiplicative (ZMod p), ψ ≠ 1 := by
  classical
  obtain ⟨ι, _, n, hn, ⟨e⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite A
  have hpA : p ∣ Nat.card A := orderOf_eq_prime hap ha ▸ orderOf_dvd_natCard a
  have hcard : Nat.card A = ∏ i, n i := by
    rw [Nat.card_congr e.toEquiv, Nat.card_pi]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod (n i)) ≃ ZMod (n i)),
      Nat.card_zmod]
  obtain ⟨i, -, hi⟩ := (Nat.Prime.prime hp.out).exists_mem_finset_dvd (hcard ▸ hpA)
  let c : ZMod (n i) →+ ZMod p := (ZMod.castHom hi (ZMod p)).toAddMonoidHom
  refine ⟨(AddMonoidHom.toMultiplicative c).comp ((Pi.evalMonoidHom _ i).comp e.toMonoidHom),
    fun h => ?_⟩
  have h1 := congrArg (fun ψ : A →* Multiplicative (ZMod p) => ψ (e.symm
    (Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod (n i)))))) h
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply, Pi.evalMonoidHom_apply, Pi.mulSingle_eq_same,
    MonoidHom.one_apply] at h1
  have h2 : c 1 = 0 := ofAdd_eq_one.mp h1
  have h3 : c 1 = 1 := map_one (ZMod.castHom hi (ZMod p))
  exact one_ne_zero (h3 ▸ h2)

theorem exists_monoidHom_zmod_ne_one_of_not_mem_commutator {H : Type*} [Group H] [Finite H]
    {p : ℕ} [Fact p.Prime] {x : H} (hxp : x ^ p = 1) (hx : x ∉ commutator H) :
    ∃ ψ : H →* Multiplicative (ZMod p), ψ ≠ 1 := by
  have : Finite (Abelianization H) := inferInstanceAs (Finite (H ⧸ commutator H))
  have ha : Abelianization.of x ≠ 1 := by
    intro h
    exact hx (Abelianization.ker_of (G := H) ▸ (MonoidHom.mem_ker.mpr h))
  obtain ⟨ψ, hψ⟩ := exists_monoidHom_zmod_ne_one_of_commGroup ha (by rw [← map_pow, hxp, map_one])
  refine ⟨ψ.comp Abelianization.of, fun h => hψ (Abelianization.hom_ext _ _ ?_)⟩
  rw [h, MonoidHom.one_comp]

theorem exists_monoidHom_zmod_ne_one_of_not_mem_commutator' {G : Type*} [Group G]
    {N₀ : Subgroup G} [Finite N₀] {p : ℕ} [Fact p.Prime] {x : G} (hxN : x ∈ N₀)
    (hxp : x ^ p = 1) (hx : x ∉ ⁅N₀, N₀⁆) :
    ∃ ψ : N₀ →* Multiplicative (ZMod p), ψ ≠ 1 := by
  refine exists_monoidHom_zmod_ne_one_of_not_mem_commutator (x := ⟨x, hxN⟩)
    (Subtype.ext (by simp [hxp])) fun h => hx ?_
  rw [← N₀.map_subtype_commutator]
  exact ⟨_, h, rfl⟩

end CFSG.StandardType

end
