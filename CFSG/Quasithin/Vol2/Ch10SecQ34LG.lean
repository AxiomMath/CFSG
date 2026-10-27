module

public import CFSG.LocalAnalysis.ComponentInitial.LinearTwoOuterOrder
public import CFSG.Quasithin.Background.A3Structure38Basic
public import CFSG.Quasithin.Vol2.Ch10SecQ34LE

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C10P34

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped MatrixGroups

section Conj

variable {G : Type} [Group G]

noncomputable def conjQuot (H H' : Subgroup G) (g : G)
    (hg : H.map (MulAut.conj g).toMonoidHom = H') :
    (↥H ⧸ CFSG.pCore 2 ↥H) ≃* (↥H' ⧸ CFSG.pCore 2 ↥H') :=
  QuotientGroup.congr (CFSG.pCore 2 ↥H) (CFSG.pCore 2 ↥H')
    ((H.equivMapOfInjective _ (MulAut.conj g).injective).trans (MulEquiv.subgroupCongr hg))
    (CFSG.pCore_map_iso 2 _)

theorem conjQuot_mk {H H' : Subgroup G} {g : G} (hg : H.map (MulAut.conj g).toMonoidHom = H')
    {k : G} (hk : k ∈ H) (hk' : g * k * g⁻¹ ∈ H') :
    conjQuot H H' g hg ((⟨k, hk⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) =
      ((⟨g * k * g⁻¹, hk'⟩ : ↥H') : ↥H' ⧸ CFSG.pCore 2 ↥H') := by
  rfl

theorem conjQuot_pow_mk {H : Subgroup G} {g : G} (hg : H.map (MulAut.conj g).toMonoidHom = H)
    (n : ℕ) {k : G} (hk : k ∈ H) (hk' : g ^ n * k * (g ^ n)⁻¹ ∈ H) :
    (conjQuot H H g hg ^ n) ((⟨k, hk⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) =
      ((⟨g ^ n * k * (g ^ n)⁻¹, hk'⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) := by
  induction n generalizing k with
  | zero =>
    rw [pow_zero, MulAut.one_apply]
    congr 2
    simp
  | succ n ih =>
    have hm : g ^ n * k * (g ^ n)⁻¹ ∈ H := by
      have h1 : g ^ n * k * (g ^ n)⁻¹ = g⁻¹ * (g ^ (n + 1) * k * (g ^ (n + 1))⁻¹) * g := by
        group
      rw [h1]
      have h2 : (g⁻¹ * (g ^ (n + 1) * k * (g ^ (n + 1))⁻¹) * g⁻¹⁻¹) ∈ H := by
        have : g⁻¹ ∈ Subgroup.normalizer (H : Set G) :=
          Subgroup.inv_mem _ ((A38.map_conj_eq_iff).mp hg)
        exact (Subgroup.mem_normalizer_iff.mp this _).mp hk'
      simpa using h2
    have hm' : g * (g ^ n * k * (g ^ n)⁻¹) * g⁻¹ ∈ H := by
      have e1 : g * (g ^ n * k * (g ^ n)⁻¹) * g⁻¹ = g ^ (n + 1) * k * (g ^ (n + 1))⁻¹ := by
        group
      rw [e1]
      exact hk'
    rw [pow_succ', MulAut.mul_apply, ih hk hm, conjQuot_mk hg hm hm']
    congr 2
    group

end Conj

section Inner

variable {Q : Type} [Group Q] {p : ℕ} [hp : Fact p.Prime]

theorem exists_inner_of_pow_eq_one (e : Q ≃* PSL(2, ZMod p)) {γ : MulAut Q} {m : ℕ}
    (hm : Odd m) (hγ : γ ^ m = 1) : ∃ a : Q, MulAut.conj a = γ ∧ Odd (orderOf a) := by
  have hcard := (CFSG.LocalAnalysis.ComponentInitial.linear_two_outer_order_divisor hp.out
    (ZMod p) (by rw [Nat.card_zmod, pow_one])).2 Q ⟨e⟩
  rw [one_mul, pow_one] at hcard
  set γ' : Outer Q := QuotientGroup.mk γ with hγ'
  have h1 : γ' ^ m = 1 := by
    rw [hγ', ← QuotientGroup.mk_pow, hγ, QuotientGroup.mk_one]
  have h2 : γ' ^ Nat.card (Outer Q) = 1 := pow_card_eq_one'
  have hd : orderOf γ' ∣ Nat.gcd m 2 :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1)
      ((orderOf_dvd_of_pow_eq_one h2).trans (hcard.trans (Nat.gcd_dvd_left 2 _)))
  have hg : Nat.gcd m 2 = 1 :=
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
      (Nat.not_even_iff_odd.mpr hm ∘ even_iff_two_dvd.mpr))
  rw [hg, Nat.dvd_one, orderOf_eq_one_iff, hγ', QuotientGroup.eq_one_iff] at hd
  obtain ⟨a, ha⟩ := hd
  refine ⟨a, ha, ?_⟩
  have hcen : a ^ m ∈ Subgroup.center Q := by
    rw [Subgroup.mem_center_iff]
    intro x
    have := congrArg (fun f : MulAut Q => f x) (show MulAut.conj (a ^ m) = 1 by
      rw [map_pow, ha, hγ])
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc x * a ^ m = a ^ m * x * (a ^ m)⁻¹ * a ^ m := by rw [this]
      _ = a ^ m * x := by group
  rw [center_eq_bot_of_mulEquiv e, Subgroup.mem_bot] at hcen
  exact hm.of_dvd_nat (orderOf_dvd_of_pow_eq_one hcen)

theorem five_le_of_isPerfect [Group.IsPerfect Q] (hp2 : p ≠ 2) (e : Q ≃* PSL(2, ZMod p)) :
    5 ≤ p := by
  by_contra h5
  have h3 : p = 3 := by
    have := hp.out.two_le
    have hp4 : p ≠ 4 := by rintro rfl; exact absurd hp.out (by norm_num)
    omega
  subst h3
  have hperf : Group.IsPerfect (alternatingGroup (Fin 4)) :=
    Group.IsPerfect.ofSurjective (f := (e.trans
      CFSG.GorensteinWalter.psl2_three_equiv_alternatingGroup).toMonoidHom)
      (MulEquiv.surjective _)
  have hnt : Nontrivial (alternatingGroup (Fin 4)) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [card_alt4]; norm_num)
  exact Group.IsPerfect.not_isSolvable _ (alternatingGroup.isSolvable (le_of_eq (Nat.card_fin 4)))

end Inner

end CFSG.Quasithin.Vol2.Ch10.SecB.C10P34
