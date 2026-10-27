module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R3Defs
import CFSG.RankThree.PartTwo.KFacts.AutKinds

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R3

namespace Res3Datum

open scoped commutatorElement

variable {J : Type} [Group J] {c g : MulAut J} {V U : Subgroup (MulAut J)}

private theorem map_center_equiv {J' : Type} [Group J'] (e : J ≃* J') :
    (Subgroup.center J).map e.toMonoidHom = Subgroup.center J' :=
  Subgroup.map_center_eq e

private theorem mem_center_equiv {J' : Type} [Group J'] (e : J ≃* J') (x : J') :
    x ∈ Subgroup.center J' ↔ e.symm x ∈ Subgroup.center J := by
  rw [← Subgroup.mem_map_equiv, map_center_equiv]

private theorem congr_fix_iff {J' : Type} [Group J'] (e : J ≃* J') (x' : J') :
    MulAut.congr e c x' = x' ↔ c (e.symm x') = e.symm x' := by
  change e (c (e.symm x')) = x' ↔ _
  exact e.eq_symm_apply.symm

theorem of_mulEquiv_congr {J' : Type} [Group J'] (e : J ≃* J') (h : Res3Datum c g V U) :
    Res3Datum (MulAut.congr e c) (MulAut.congr e g) (V.map (MulAut.congr e).toMonoidHom)
      (U.map (MulAut.congr e).toMonoidHom) where
  center_pGroup := by
    have h1 := h.center_pGroup.map e.toMonoidHom
    rwa [map_center_equiv] at h1
  center_ne := by
    intro hbot
    apply h.center_ne
    have h1 := map_center_equiv e
    rw [hbot] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h1
  c_pow := by rw [← map_pow, h.c_pow, map_one]
  comm := h.comm.map (MulAut.congr e)
  g_primes := fun p hp hpd => h.g_primes p hp (by rwa [MulEquiv.orderOf_eq] at hpd)
  V_isPGroup := h.V_isPGroup.map _
  U_le := Subgroup.map_mono h.U_le
  c_mem := by
    rw [← Subgroup.map_equiv_normalizer_eq V (MulAut.congr e)]
    exact Subgroup.mem_map_of_mem _ h.c_mem
  g_mem := by
    rw [← Subgroup.map_equiv_normalizer_eq V (MulAut.congr e)]
    exact Subgroup.mem_map_of_mem _ h.g_mem
  g_memU := by
    rw [← Subgroup.map_equiv_normalizer_eq U (MulAut.congr e)]
    exact Subgroup.mem_map_of_mem _ h.g_memU
  U_comm := by
    have h1 := congrArg (Subgroup.map (MulAut.congr e).toMonoidHom) h.U_comm
    rw [Subgroup.map_commutator, MonoidHom.map_zpowers] at h1
    exact h1
  U_ne := fun hbot => h.U_ne
    ((Subgroup.map_eq_bot_iff_of_injective U (f := (MulAut.congr e).toMonoidHom)
      (MulAut.congr e).injective).mp hbot)
  F_cent := by
    intro v' hv' hcv
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hv'
    have hcv' : Commute (MulAut.congr e c) (MulAut.congr e v) := hcv
    exact (h.F_cent v hv (hcv'.of_map (MulAut.congr e).injective)).map (MulAut.congr e)
  outer_threes := by
    intro hc x' hx' hx3
    have hc0 : c ∉ (MulAut.conj : J →* MulAut J).range := by
      rintro ⟨y, rfl⟩
      exact hc ⟨e y, (KFacts.congr_mulAutConj e y).symm⟩
    rw [mem_center_equiv e]
    refine h.outer_threes hc0 _ ((congr_fix_iff e x').mp hx') ?_
    rw [← map_pow, hx3, map_one]
  inner_threes := by
    intro j' hj'
    have hj : MulAut.conj (e.symm j') = c := by
      apply (MulAut.congr e).injective
      rw [KFacts.congr_mulAutConj, MulEquiv.apply_symm_apply]
      exact hj'
    obtain ⟨h3, hrest⟩ := h.inner_threes _ hj
    refine ⟨?_, ?_⟩
    · have h1 : e.symm (j' ^ 3) = 1 := by rw [map_pow]; exact h3
      exact e.symm.injective (h1.trans (map_one e.symm).symm)
    · intro x' hxj hx3
      have hx30 : (e.symm x') ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
      have hmem := hrest _ (hxj.map e.symm) hx30
      have hK : (Subgroup.zpowers (e.symm j') ⊔ Subgroup.center J).map e.toMonoidHom =
          Subgroup.zpowers j' ⊔ Subgroup.center J' := by
        rw [Subgroup.map_sup, MonoidHom.map_zpowers, map_center_equiv]
        simp
      rw [← hK, Subgroup.mem_map_equiv]
      exact hmem
  cube := by
    intro x' hx' hx3
    have hz : (e.symm x') ^ 3 ∈ Subgroup.center J := by
      rw [← map_pow]
      exact (mem_center_equiv e _).mp hx3
    have h1 : e.symm (x' ^ 3) = 1 := by
      rw [map_pow]
      exact h.cube _ ((congr_fix_iff e x').mp hx') hz
    exact e.symm.injective (h1.trans (map_one e.symm).symm)
  primes := by
    intro x' hx' hp
    have ho : orderOf (e.symm x') = orderOf x' := MulEquiv.orderOf_eq e.symm x'
    rw [← ho] at hp ⊢
    exact h.primes _ ((congr_fix_iff e x').mp hx') hp
  rank5 := by
    intro E R hE hE5 hR hRne hnorm
    refine h.rank5 (E.map e.symm.toMonoidHom) (R.map e.symm.toMonoidHom) ?_ ?_ (hR.map _) ?_ ?_
    · rw [Subgroup.card_map_of_injective e.symm.injective]
      exact hE
    · rintro _ ⟨y, hy, rfl⟩
      change (e.symm y) ^ 5 = 1
      rw [← map_pow, hE5 y hy, map_one]
    · intro hbot
      exact hRne ((Subgroup.map_eq_bot_iff_of_injective R e.symm.injective).mp hbot)
    · rintro _ ⟨y, hy, rfl⟩
      rw [← Subgroup.map_equiv_normalizer_eq R e.symm]
      exact Subgroup.mem_map_of_mem _ (hnorm hy)

theorem false_of_commutator_inf_eq_bot {N : Subgroup (MulAut J)} (h : Res3Datum c g V U)
    (hN : commutator (MulAut J) ≤ N) (hV : V ⊓ N = ⊥) : False := by
  have hcomm : ∀ v ∈ V, Commute c v := by
    intro v hv
    have hcv : c * v * c⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp h.c_mem v).mp hv
    have h1 : ⁅c, v⁆ ∈ V ⊓ N :=
      ⟨by rw [commutatorElement_def]; exact V.mul_mem hcv (V.inv_mem hv),
        hN (Subgroup.commutator_mem_commutator (Subgroup.mem_top c) (Subgroup.mem_top v))⟩
    rw [hV, Subgroup.mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  apply h.U_ne
  rw [← h.U_comm, Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.le_centralizer_iff,
    Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
  intro u hu
  exact (h.F_cent u (h.U_le hu) (hcomm u (h.U_le hu))).eq.symm

theorem false_of_outer_threes_noncentral (h : Res3Datum c g V U)
    (hc : c ∉ (MulAut.conj : J →* MulAut J).range) {x : J} (hx : c x = x) (hx3 : x ^ 3 = 1)
    (hxz : x ∉ Subgroup.center J) : False :=
  hxz (h.outer_threes hc x hx hx3)

private theorem commute_of_conj_apply_eq {j x : J} (hx : MulAut.conj j x = x) : Commute x j := by
  rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul] at hx
  exact hx.symm

private theorem commute_of_mem_zpowers_sup_center {j x y : J}
    (hx : x ∈ Subgroup.zpowers j ⊔ Subgroup.center J)
    (hy : y ∈ Subgroup.zpowers j ⊔ Subgroup.center J) : Commute x y := by
  obtain ⟨a, ha, z₁, hz₁, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
  obtain ⟨b, hb, z₂, hz₂, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hy
  have hab : Commute a b := by
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.refl j).zpow_zpow m n
  have h1 : Commute a z₂ := Subgroup.mem_center_iff.mp hz₂ a
  have h2 : Commute z₁ (b * z₂) := (Subgroup.mem_center_iff.mp hz₁ (b * z₂)).symm
  exact (hab.mul_right h1).mul_left h2

theorem false_of_fixed_noncomm (h : Res3Datum c g V U) {x y : J} (hx : c x = x) (hy : c y = y)
    (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1) (hxy : x * y ≠ y * x) : False := by
  by_cases hc : c ∈ (MulAut.conj : J →* MulAut J).range
  · obtain ⟨j, hj⟩ := hc
    obtain ⟨-, hrest⟩ := h.inner_threes j hj
    rw [← hj] at hx hy
    exact hxy (commute_of_mem_zpowers_sup_center
      (hrest x (commute_of_conj_apply_eq hx) hx3)
      (hrest y (commute_of_conj_apply_eq hy) hy3))
  · exact hxy (Subgroup.mem_center_iff.mp (h.outer_threes hc x hx hx3) y).symm

theorem exists_commuting_prime_order_aut (h : Res3Datum c g V U) :
    ∃ (α : MulAut J) (p : ℕ), p.Prime ∧ 5 ≤ p ∧ orderOf α = p ∧ Commute c α := by
  have h0 : orderOf g ≠ 0 := fun h0 => h.not_two_dvd (by rw [h0]; exact dvd_zero 2)
  have h1 : orderOf g ≠ 1 := fun h1 => h.g_ne_one (orderOf_eq_one_iff.mp h1)
  have hp : (orderOf g).minFac.Prime := Nat.minFac_prime h1
  have hpd : (orderOf g).minFac ∣ orderOf g := Nat.minFac_dvd _
  have h57 := h.g_primes _ hp hpd
  exact ⟨g ^ (orderOf g / (orderOf g).minFac), (orderOf g).minFac, hp, by omega,
    orderOf_pow_orderOf_div h0 hpd, h.comm.pow_right _⟩

theorem inner_pow_three_of_conj (h : Res3Datum c g V U) {j : J} (hj : MulAut.conj j = c) :
    j ^ 3 = 1 ∧ j ∉ Subgroup.center J := by
  refine ⟨(h.inner_threes j hj).1, fun hz => h.c_ne_one ?_⟩
  rw [← hj]
  ext x
  have hjx := Subgroup.mem_center_iff.mp hz x
  show j * x * j⁻¹ = x
  rw [← hjx, mul_inv_cancel_right]

end Res3Datum

end CFSG.RankThree.PartTwo.Sec15.Sylow155R3
