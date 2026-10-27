module

public import CFSG.Quasithin.Vol2.Ch10SecKIK2e
public import CFSG.Quasithin.Background.A3Structure313SL2

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem false_of_sl2_quot {Y X : Type} [Group Y] [Finite Y] [Group X] (π : Y →* X)
    (hπ : Function.Surjective π) (hX : CFSG.IsQuasisimple X) (hlist : B56QuasisimpleList X)
    {p : ℕ} (hp : p.Prime) (hp8 : p % 8 = 3 ∨ p % 8 = 5) (hp5 : p ^ 2 % 5 = 1)
    (hY : IsSL2 p (↥(⊤ : Subgroup Y) ⧸ CFSG.oddCore ↥(⊤ : Subgroup Y))) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite X := Finite.of_surjective π hπ
  have hp11 : 11 ≤ p := by
    by_contra h
    push Not at h
    interval_cases p <;> simp_all (config := { decide := true })
  set T := (⊤ : Subgroup Y) with hT
  obtain ⟨e⟩ := hY
  set φ : ↥T →* Matrix.SpecialLinearGroup (Fin 2) (ZMod p) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.oddCore ↥T)) with hφ
  have hφs : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hφk : ∀ t, φ t = 1 ↔ t ∈ CFSG.oddCore ↥T := fun t => by
    rw [hφ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hcardY := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.oddCore ↥T)
  rw [Nat.card_congr e.toEquiv, A313.card_sl2 hp] at hcardY
  have hodd := A312.odd_card_oddCore ↥T
  have h16Y : ¬ 16 ∣ Nat.card ↥T := by
    rw [hcardY]
    intro h
    have hcop : Nat.Coprime (2 ^ 4) (Nat.card (CFSG.oddCore ↥T)) :=
      Nat.Coprime.pow_left 4 (Nat.coprime_two_left.mpr hodd)
    norm_num at hcop
    exact not_sixteen_dvd hp8 (hcop.dvd_of_dvd_mul_right h)
  have h16X : ¬ 16 ∣ Nat.card X := fun h => h16Y (by
    rw [hT, Subgroup.card_top]
    exact h.trans (Subgroup.card_dvd_of_surjective hπ))
  set Z := π.ker with hZ
  set M := (Z.subgroupOf T).map φ with hM
  have hMn : M.Normal := Subgroup.Normal.map (Subgroup.Normal.subgroupOf inferInstance T) φ hφs
  have hMtop : M ≠ ⊤ := by
    intro htop
    have hsurj : Function.Surjective (π.comp (T.subtype.comp (CFSG.oddCore ↥T).subtype)) := by
      intro x
      obtain ⟨y, rfl⟩ := hπ x
      have hy : φ ⟨y, Subgroup.mem_top y⟩ ∈ M := by rw [htop]; trivial
      obtain ⟨z, hz, hzy⟩ := hy
      have ho : z⁻¹ * ⟨y, Subgroup.mem_top y⟩ ∈ CFSG.oddCore ↥T := by
        rw [← hφk, map_mul, map_inv, hzy, inv_mul_cancel]
      refine ⟨⟨_, ho⟩, ?_⟩
      have hz1 : π (z : Y) = 1 := hz
      simp [hz1]
    have : Group.IsSolvable ↥(CFSG.oddCore ↥T) := A312.oddCore_isSolvable _
    have hs : Group.IsSolvable X := Group.isSolvable_of_surjective hsurj
    have : Group.IsPerfect X := hX.1
    have : Nontrivial X := CFSG.LocalCores.isQuasisimple_nontrivial hX
    exact Group.IsPerfect.not_isSolvable X hs
  have hMc : M ≤ Subgroup.center _ := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups (A36B.isQuasisimple_sl2 hp (by omega))
      hMn with h | h
    · exact absurd h hMtop
    · exact h
  have hpS : p ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) := by
    rw [A313.card_sl2 hp]
    exact dvd_mul_right p _
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' p hpS
  obtain ⟨t, rfl⟩ := hφs u
  obtain ⟨a, m, hpm, hm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos t).ne' p
    hp.one_lt.ne'
  have hcop : Nat.Coprime (orderOf (φ t)) m := by
    rw [hu]
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 hpm
  have hum : orderOf (φ (t ^ m)) = p := by rw [map_pow, hcop.orderOf_pow, hu]
  set ψ := π.comp T.subtype with hψ
  have hψp : ψ (t ^ m) ^ p ^ a = 1 := by
    rw [← map_pow, ← pow_mul, mul_comm, ← hm, pow_orderOf_eq_one, map_one]
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one hψp)
  have hpX : p ∣ Nat.card X := by
    rcases b with _ | b
    · exfalso
      rw [pow_zero, orderOf_eq_one_iff] at hb
      have hZm : t ^ m ∈ Z.subgroupOf T := hb
      have hc := hMc ⟨t ^ m, hZm, rfl⟩
      have h2 := A36B.sq_eq_one_of_mem_center_sl2 hp (by omega) hc
      have := orderOf_dvd_of_pow_eq_one h2
      rw [hum] at this
      exact absurd (Nat.le_of_dvd (by norm_num) this) (by omega)
    · exact (dvd_pow_self p (Nat.succ_ne_zero b)).trans (hb ▸ orderOf_dvd_natCard _)
  have := le_seven_of_dvd hp (hpX.trans (dvd_of_b56Card (b56Card_of_list hlist) h16X))
  omega

end CFSG.Quasithin.Vol2.Ch10.SecC.C10KH
