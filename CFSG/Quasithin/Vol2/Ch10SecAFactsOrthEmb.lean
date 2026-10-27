module

public import CFSG.Quasithin.Vol2.Ch10SecAShape

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

theorem exists_injective_zmod_of_isCyclic {C : Type} [Group C] [Finite C] [IsCyclic C] {m : ℕ}
    (hm : m ≠ 0) (hd : Nat.card C ∣ m) :
    ∃ f : C →* Multiplicative (ZMod m), Function.Injective f := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := C)
  have hord : orderOf g = Nat.card C := orderOf_eq_card_of_forall_mem_zpowers hg
  set z : Multiplicative (ZMod m) := Multiplicative.ofAdd ((m / Nat.card C : ℕ) : ZMod m) with hzdef
  have hz : orderOf z = Nat.card C := by
    rw [hzdef, orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_coe _ hm,
      Nat.gcd_eq_right (Nat.div_dvd_of_dvd hd), Nat.div_div_self hd hm]
  refine ⟨monoidHomOfForallMemZpowers hg (dvd_of_eq (hz.trans hord.symm)), ?_⟩
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg x)
  rw [map_zpow, monoidHomOfForallMemZpowers_apply_gen] at hx
  rw [← orderOf_dvd_iff_zpow_eq_one] at hx ⊢
  rwa [hz, ← hord] at hx

theorem exists_injective_zmod_of_units {A : Type} [Group A] [Finite A] {K : Type} [Field K]
    (χ : A →* Kˣ) (hχ : Function.Injective χ) {m : ℕ} (hm : m ≠ 0) (hpow : ∀ a, χ a ^ m = 1) :
    ∃ f : A →* Multiplicative (ZMod m), Function.Injective f := by
  have : IsCyclic A :=
    isCyclic_of_injective_ringHom ((Units.coeHom K).comp χ) (Units.val_injective.comp hχ)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := A)
  have hgm : g ^ m = 1 := hχ (by rw [map_pow, hpow, map_one])
  have hd : Nat.card A ∣ m := by
    rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
    exact orderOf_dvd_of_pow_eq_one hgm
  exact exists_injective_zmod_of_isCyclic hm hd

end CFSG.Quasithin.Vol2.Ch10.SecA
