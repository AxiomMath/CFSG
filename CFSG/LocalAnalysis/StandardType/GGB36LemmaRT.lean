module

public import CFSG.LocalAnalysis.StandardType.GGTPNDefs
public import CFSG.GroupActions.SubgroupStabilizerOuterBound


public section

namespace CFSG.StandardType.B36

open CFSG CFSG.Assembly CFSG.StandardType

private theorem ltqRt_map_eq {X : Type} [Group X] [Finite X] {A : Subgroup (MulAut X)}
    {J : Subgroup X} (hnorm : ∀ a ∈ A, ∀ j ∈ J, a j ∈ J) {a : MulAut X} (ha : a ∈ A) :
    J.map a.toMonoidHom = J := by
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact hnorm a ha y hy
  · rw [Subgroup.card_map_of_injective a.injective]

private theorem ltqRt_ab_le_stab {X : Type} [Group X] [Finite X] {Ab : Subgroup (MulAut X)}
    {J : Subgroup X} (hnorm : ∀ a ∈ Ab, ∀ j ∈ J, a j ∈ J) :
    Ab ≤ CFSG.GroupActions.subgroupStabAut J := by
  intro a ha
  show J.map a.toMonoidHom = J
  exact ltqRt_map_eq hnorm ha

private noncomputable def ltqRtRestrict {X : Type} [Group X] [Finite X]
    (Ab : Subgroup (MulAut X)) (J : Subgroup X) (hnorm : ∀ a ∈ Ab, ∀ j ∈ J, a j ∈ J) :
    Ab →* MulAut ↥J where
  toFun a := CFSG.GroupActions.subgroupStabRestrict J
    ⟨(a : MulAut X), ltqRt_ab_le_stab hnorm a.2⟩
  map_one' := by ext j; rfl
  map_mul' a b := by ext j; rfl

private theorem ltqRtRestrict_apply {X : Type} [Group X] [Finite X]
    {Ab : Subgroup (MulAut X)} {J : Subgroup X}
    {hnorm : ∀ a ∈ Ab, ∀ j ∈ J, a j ∈ J} (a : Ab) (j : ↥J) :
    ((ltqRtRestrict Ab J hnorm a j : ↥J) : X) = (a : MulAut X) j.1 := rfl

theorem card_le_of_kernel_le_zpowers {p : ℕ} (hp : p.Prime) {X : Type} [Group X] [Finite X]
    {Ab : Subgroup (MulAut X)} {σ : MulAut X} {J : Subgroup X} (hAb : IsElemAbelian p Ab)
    (hσ : σ ∈ Ab) (hnorm : ∀ a ∈ Ab, ∀ j ∈ J, a j ∈ J) (hker : GGTPNKernel Ab σ J) {k : ℕ}
    (hAut : ∀ E : Subgroup (MulAut ↥J), IsElemAbelian p E → Nat.card E ≤ p ^ k) :
    Nat.card Ab ≤ p ^ (k + 1) := by
  classical
  let ρ : Ab →* MulAut ↥J := ltqRtRestrict Ab J hnorm
  have hker_le : (ρ.ker.map (Subgroup.subtype Ab) : Subgroup (MulAut X)) ≤ Subgroup.zpowers σ := by
    intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    rw [MonoidHom.mem_ker] at ha
    exact hker a a.2 (fun j hj => by
      have h := congrArg (fun φ : MulAut ↥J => ((φ ⟨j, hj⟩ : ↥J) : X)) ha
      simpa [ρ, ltqRtRestrict_apply] using h)
  have hcard_ker : Nat.card ρ.ker ≤ p := by
    have h1 : Nat.card (ρ.ker.map (Subgroup.subtype Ab)) ≤ Nat.card (Subgroup.zpowers σ) :=
      Subgroup.card_le_of_le hker_le
    have h2 : Nat.card ρ.ker = Nat.card (ρ.ker.map (Subgroup.subtype Ab)) :=
      (Subgroup.card_map_of_injective (Subgroup.subtype_injective Ab)).symm
    have h3 : Nat.card (Subgroup.zpowers σ) = orderOf σ := Nat.card_zpowers (a := σ)
    have h4 : orderOf σ ≤ p := Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one (hAb.2 σ hσ))
    omega
  have hrange : IsElemAbelian p ρ.range := by
    refine ⟨?_, ?_⟩
    · refine IsMulCommutative.of_comm (fun x y => ?_)
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rcases MonoidHom.mem_range.mp x.2 with ⟨a, ha⟩
      rcases MonoidHom.mem_range.mp y.2 with ⟨b, hb⟩
      rw [← ha, ← hb]
      simpa only [← map_mul, hAb.1.is_comm.comm a b]
    · intro x hx
      rcases MonoidHom.mem_range.mp hx with ⟨a, rfl⟩
      rw [← map_pow]
      have hap : a ^ p = 1 := Subtype.ext (hAb.2 a a.2)
      rw [hap, map_one]
  have hcard_range : Nat.card ρ.range ≤ p ^ k := hAut ρ.range hrange
  calc Nat.card Ab = Nat.card ρ.ker * Nat.card ρ.range :=
        (Subgroup.card_ker_mul_card_range ρ).symm
    _ ≤ p * p ^ k := Nat.mul_le_mul hcard_ker hcard_range
    _ = p ^ (k + 1) := by rw [mul_comm, pow_succ]

theorem mem_of_commute_inner {p : ℕ} (hp : p.Prime) {X : Type} [Group X] [Finite X]
    {A : Subgroup (MulAut X)} {J : Subgroup X} (hself : GGTPNSelfCent p A)
    (hnorm : ∀ a ∈ A, ∀ j ∈ J, a j ∈ J) (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥J))
    {u : X} (hu : u ∈ J) (hcomm : ∀ a ∈ A, ∀ v ∈ J, a (u * v * u⁻¹) = u * a v * u⁻¹)
    (hup : ∀ v ∈ J, u ^ p * v = v * u ^ p) :
    ∃ a ∈ A, ∀ v ∈ J, a v = u * v * u⁻¹ := by
  classical
  set m : ℕ := orderOf (u ^ p) with hm
  have hmpos : 0 < m := by rw [hm]; exact orderOf_pos _
  have hnotdvd : ¬ p ∣ m := by
    intro hdvd
    have hdivpos : 0 < m / p := Nat.div_pos (Nat.le_of_dvd hmpos hdvd) hp.pos
    let w : X := (u ^ p) ^ (m / p)
    have hwpow : w ^ p = 1 := by
      simp only [w]
      rw [← pow_mul, Nat.div_mul_cancel hdvd, hm, pow_orderOf_eq_one]
    have hwne : w ≠ 1 := by
      intro hw1
      have hdvd2 : m ∣ m / p := by
        have h := orderOf_dvd_of_pow_eq_one (x := u ^ p) (n := m / p)
          (by simpa only [w] using hw1)
        rwa [← hm] at h
      have hle : m ≤ m / p := Nat.le_of_dvd hdivpos hdvd2
      have hlt : m / p < m := by
        have h1 : m / p * p = m := Nat.div_mul_cancel hdvd
        have h2 : m / p * 1 < m / p * p := mul_lt_mul_of_pos_left hp.one_lt hdivpos
        rwa [mul_one, h1] at h2
      omega
    have hwJ : w ∈ J := by
      simp only [w]
      exact J.pow_mem (J.pow_mem hu p) (m / p)
    have hwcent : (⟨w, hwJ⟩ : ↥J) ∈ Subgroup.center ↥J := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      have hcomm_uw : Commute (u ^ p) y.1 := hup y.1 y.2
      exact ((hcomm_uw.pow_left (m / p)).symm).eq
    have hworder : orderOf w = p := by
      have hdvd' : orderOf w ∣ p := orderOf_dvd_of_pow_eq_one hwpow
      rcases (Nat.dvd_prime hp).mp hdvd' with h1 | h1
      · exact absurd (orderOf_eq_one_iff.mp h1) hwne
      · exact h1
    have hpdiv : p ∣ Nat.card (Subgroup.center ↥J) := by
      have h := Subgroup.orderOf_dvd_natCard (Subgroup.center ↥J) hwcent
      rwa [Subgroup.orderOf_mk, hworder] at h
    exact hZ hpdiv
  have hcop : Nat.Coprime m p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnotdvd).symm
  obtain ⟨m', hm'lt, hm'mod⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  let j : X := u ^ (m * m')
  have hjpow : j ^ p = 1 := by
    simp only [j]
    rw [← pow_mul, mul_comm (m * m') p, pow_mul, pow_mul, hm, pow_orderOf_eq_one, one_pow]
  let t : ℕ := (m * m') / p
  have hmm' : m * m' = p * t + 1 := by
    have h := Nat.div_add_mod (m * m') p
    rw [hm'mod] at h
    simpa only [t, Nat.add_comm] using h.symm
  have hj_eq : j = (u ^ p) ^ t * u := by
    simp only [j, hmm']
    rw [pow_add, pow_one, pow_mul]
  have haj : ∀ a ∈ A, a j = j := by
    intro a ha
    set c : X := u⁻¹ * a u with hc
    have hcJ : c ∈ J := by
      rw [hc]
      exact J.mul_mem (J.inv_mem hu) (hnorm a ha u hu)
    have hccomm : ∀ v ∈ J, c * v = v * c := by
      intro v hv
      have hmap : J.map a.toMonoidHom = J := ltqRt_map_eq hnorm ha
      have hv' : v ∈ J.map a.toMonoidHom := by rw [hmap]; exact hv
      rw [Subgroup.mem_map] at hv'
      obtain ⟨w, hw, hwv⟩ := hv'
      rw [← hwv]
      have h1 : a u * a w * (a u)⁻¹ = a (u * w * u⁻¹) := by
        simp only [map_mul, map_inv]
      have hkey : c * (a w) * c⁻¹ = a w := by
        rw [hc]
        calc (u⁻¹ * a u) * (a w) * (u⁻¹ * a u)⁻¹
            = u⁻¹ * (a u * a w * (a u)⁻¹) * u := by group
          _ = u⁻¹ * a (u * w * u⁻¹) * u := by rw [h1]
          _ = u⁻¹ * (u * a w * u⁻¹) * u := by rw [hcomm a ha w hw]
          _ = a w := by group
      calc c * (a w) = c * (a w) * c⁻¹ * c := by group
        _ = a w * c := by rw [hkey]
    have hau : a u = u * c := by rw [hc]; group
    have huc : Commute u c := (hccomm u hu).symm
    have hjc : Commute j (c ^ (m * m')) := by
      dsimp only [j]
      exact (huc.pow_left (m * m')).pow_right (m * m')
    have haj_eq : a j = j * c ^ (m * m') := by
      dsimp only [j]
      rw [map_pow, hau]
      exact huc.mul_pow (m * m')
    have hzpow : (c ^ (m * m')) ^ p = 1 := by
      have h1 : (a j) ^ p = 1 := by rw [← map_pow, hjpow, map_one]
      rw [haj_eq, hjc.mul_pow, hjpow, one_mul] at h1
      exact h1
    have hzcJ : c ^ (m * m') ∈ J := J.pow_mem hcJ (m * m')
    have hzc_comm : ∀ v ∈ J, c ^ (m * m') * v = v * c ^ (m * m') := fun v hv =>
      (Commute.pow_left (hccomm v hv) (m * m')).eq
    have hzcenter : (⟨c ^ (m * m'), hzcJ⟩ : ↥J) ∈ Subgroup.center ↥J := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact (hzc_comm y.1 y.2).symm
    have hzone : c ^ (m * m') = 1 := by
      by_contra hne
      have hdvd' : orderOf (c ^ (m * m')) ∣ p := orderOf_dvd_of_pow_eq_one hzpow
      have horder : orderOf (c ^ (m * m')) = p := by
        rcases (Nat.dvd_prime hp).mp hdvd' with h1 | h1
        · exact absurd (orderOf_eq_one_iff.mp h1) hne
        · exact h1
      have hpdiv : p ∣ Nat.card (Subgroup.center ↥J) := by
        have h := Subgroup.orderOf_dvd_natCard (Subgroup.center ↥J) hzcenter
        rwa [Subgroup.orderOf_mk, horder] at h
      exact hZ hpdiv
    rw [haj_eq, hzone, mul_one]
  refine ⟨MulAut.conj j, hself j haj hjpow, ?_⟩
  intro v hv
  rw [MulAut.conj_apply]
  have hzvJ : u * v * u⁻¹ ∈ J := J.mul_mem (J.mul_mem hu hv) (J.inv_mem hu)
  have hzcomm : (u ^ p) ^ t * (u * v * u⁻¹) = (u * v * u⁻¹) * (u ^ p) ^ t :=
    (Commute.pow_left (hup (u * v * u⁻¹) hzvJ) t).eq
  calc j * v * j⁻¹ = ((u ^ p) ^ t * u) * v * ((u ^ p) ^ t * u)⁻¹ := by rw [hj_eq]
    _ = (u ^ p) ^ t * (u * v * u⁻¹) * ((u ^ p) ^ t)⁻¹ := by group
    _ = (u * v * u⁻¹) * (u ^ p) ^ t * ((u ^ p) ^ t)⁻¹ := by rw [hzcomm]
    _ = u * v * u⁻¹ := by group

end CFSG.StandardType.B36

end
