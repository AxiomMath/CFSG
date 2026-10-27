module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeT79H0

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V T A K S X : Subgroup G} {p : ℕ} {g x : G}
variable {Y : Type} [Group Y]

theorem nine3_dcal_inf_ker (h : Nine3T79Setup V T A K S X p g x)
    {π : ↥(nineH0 V K g) →* Y} (hπ : Nine3QuotHyp (nineH0 V K g) π) {D : Subgroup G}
    (hD : D ∈ nine3Dcal V (nineH0 V K g)) {d : ↥(nineH0 V K g)} (hd : (d : G) ∈ D) :
    π d = 1 ↔ (d : G) ∈ pCoreOf 2 (nineH0 V K g) := by
  constructor
  · intro hπd
    obtain ⟨a, ha, rfl⟩ := hD
    have hsq : (d : G) ^ 2 = 1 :=
      (E3.isElemAbelian_conjSubgroup h.hc.core.hyp7.1 a).2 (d : G) hd
    have hdvd : orderOf d ∣ 2 ^ 1 := by
      rw [pow_one, ← Subgroup.orderOf_coe d]
      exact orderOf_dvd_iff_pow_eq_one.mpr hsq
    obtain ⟨n, -, hn⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact hπ.two_elt d hπd n hn
  · intro hdp
    exact hπ.pcore_le d hdp

private theorem nine3_dcal_image_eq (h : Nine3T79Setup V T A K S X p g x)
    {π : ↥(nineH0 V K g) →* Y} (hπ : Nine3QuotHyp (nineH0 V K g) π)
    {D : Subgroup G} (hD : D ∈ nine3Dcal V (nineH0 V K g))
    {d u : ↥(nineH0 V K g)} (hdD : (d : G) ∈ D) (huD : (u : G) ∈ D)
    (hd1 : π d ≠ 1) (hu1 : π u ≠ 1) : π u = π d := by
  have hrel : (D ⊓ pCoreOf 2 (nineH0 V K g)).relIndex D = 2 := by
    rw [Subgroup.inf_relIndex_left]
    exact (nine3_dcal_not_le_pCore h hD).2
  let Hsub : Subgroup ↥D := (D ⊓ pCoreOf 2 (nineH0 V K g)).subgroupOf D
  have hidx : Hsub.index = 2 := hrel
  let dD : ↥D := ⟨(d : G), hdD⟩
  let uD : ↥D := ⟨(u : G), huD⟩
  have hdD_not : dD⁻¹ ∉ Hsub := by
    intro hmem
    have h2 : (d : G) ∈ pCoreOf 2 (nineH0 V K g) := by
      have hmem' := (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hmem)).2
      simpa [dD] using (pCoreOf 2 (nineH0 V K g)).inv_mem hmem'
    exact hd1 ((nine3_dcal_inf_ker h hπ hD hdD).mpr h2)
  have huD_not : uD ∉ Hsub := by
    intro hmem
    have h2 : (u : G) ∈ pCoreOf 2 (nineH0 V K g) :=
      (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hmem)).2
    exact hu1 ((nine3_dcal_inf_ker h hπ hD huD).mpr h2)
  have hprod : uD * dD⁻¹ ∈ Hsub := by
    rw [Subgroup.mul_mem_iff_of_index_two hidx]
    exact ⟨fun hh => absurd hh huD_not, fun hh => absurd hh hdD_not⟩
  have hmemO : (u : G) * (d : G)⁻¹ ∈ pCoreOf 2 (nineH0 V K g) := by
    have hmem := (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hprod)).2
    simpa [uD, dD] using hmem
  have h1 : π (u * d⁻¹) = 1 := hπ.pcore_le (u * d⁻¹) (by simpa using hmemO)
  have h2 : π u * (π d)⁻¹ = 1 := by
    rw [← map_inv, ← map_mul]
    exact h1
  exact eq_of_mul_inv_eq_one h2

theorem nine3_dcal_comm_of_quot (h : Nine3T79Setup V T A K S X p g x)
    {π : ↥(nineH0 V K g) →* Y} (hπ : Nine3QuotHyp (nineH0 V K g) π) {D D' : Subgroup G}
    (hD : D ∈ nine3Dcal V (nineH0 V K g)) (hD' : D' ∈ nine3Dcal V (nineH0 V K g))
    {d d' : ↥(nineH0 V K g)} (hdD : (d : G) ∈ D) (hd'D' : (d' : G) ∈ D')
    (hd : π d ≠ 1) (hd' : π d' ≠ 1) (hne : π d ≠ π d') (hcomm : π d * π d' = π d' * π d) :
    ∀ u ∈ D, ∀ u' ∈ D', u * u' = u' * u := by
  have hcentral : D ≤ Subgroup.centralizer (D' : Set G) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
    by_contra hne_comm
    obtain ⟨a, ha, rfl⟩ := hD
    obtain ⟨b, hb, rfl⟩ := hD'
    have hDmem : conjSubgroup V a ∈ nine3Dcal V (nineH0 V K g) := ⟨a, ha, rfl⟩
    have hD'mem : conjSubgroup V b ∈ nine3Dcal V (nineH0 V K g) := ⟨b, hb, rfl⟩
    have hVab : IsElemAbelian 2 V := h.hc.core.hyp7.1
    have hTI : IsTI V := h.hc.core.hyp7.2.2
    have hVp : IsPGroup 2 V := CFSG.Open.IsElemAbelian.isPGroup hVab
    set Nsub : Subgroup G := π.ker.map (nineH0 V K g).subtype with hNsub
    have hNsub_mem : ∀ z : ↥(nineH0 V K g), (z : G) ∈ Nsub ↔ z ∈ π.ker := by
      intro z
      constructor
      · intro hz
        rw [hNsub] at hz
        obtain ⟨k, hk, hkG⟩ := hz
        have hkz : k = z := Subtype.ext hkG
        rwa [hkz] at hk
      · intro hz
        rw [hNsub]
        exact ⟨z, hz, rfl⟩
    have hkerD' : conjSubgroup V b ⊓ Nsub =
        conjSubgroup V b ⊓ pCoreOf 2 (nineH0 V K g) := by
      ext x
      constructor
      · rintro ⟨hxD, hxN⟩
        rw [hNsub] at hxN
        obtain ⟨k, hk, hkG⟩ := hxN
        have hkD : (k : G) ∈ conjSubgroup V b := by
          have h1 : (k : G) = x := hkG
          rw [h1]
          exact hxD
        refine ⟨hxD, ?_⟩
        rw [← hkG]
        exact (nine3_dcal_inf_ker h hπ hD'mem (d := k) hkD).mp (MonoidHom.mem_ker.mp hk)
      · rintro ⟨hxD, hxO⟩
        have hxH0 : x ∈ nineH0 V K g := nine3_dcal_le_H0 h.hc hD'mem hxD
        refine ⟨hxD, ?_⟩
        rw [hNsub]
        exact ⟨⟨x, hxH0⟩,
          MonoidHom.mem_ker.mpr ((nine3_dcal_inf_ker h hπ hD'mem (d := ⟨x, hxH0⟩)
            hxD).mpr hxO), rfl⟩
    have hD'notNsub : ¬ conjSubgroup V b ≤ Nsub := by
      intro hle
      have hEq : conjSubgroup V b ⊓ Nsub = conjSubgroup V b :=
        le_antisymm inf_le_left (le_inf le_rfl hle)
      rw [hEq] at hkerD'
      exact (nine3_dcal_not_le_pCore h hD'mem).1 (hkerD'.symm ▸ inf_le_right)
    have hDinfN : conjSubgroup V a ⊓ normalizer (conjSubgroup V b : Set G) ≠ ⊥ := by
      intro hbot
      have hI0N : nineI0 V K g ≤ normalizer (conjSubgroup V b : Set G) :=
        (nine3_dcal_inf_I0 h hD'mem).2
      have hle : conjSubgroup V a ⊓ nineI0 V K g ≤
          conjSubgroup V a ⊓ normalizer (conjSubgroup V b : Set G) :=
        le_inf inf_le_left (le_trans inf_le_right hI0N)
      exact (nine3_dcal_inf_I0 h hDmem).1 (le_bot_iff.mp (hbot ▸ hle))
    have hD'infN : conjSubgroup V b ⊓ normalizer (conjSubgroup V a : Set G) ≠ ⊥ := by
      intro hbot
      have hI0N : nineI0 V K g ≤ normalizer (conjSubgroup V a : Set G) :=
        (nine3_dcal_inf_I0 h hDmem).2
      have hle : conjSubgroup V b ⊓ nineI0 V K g ≤
          conjSubgroup V b ⊓ normalizer (conjSubgroup V a : Set G) :=
        le_inf inf_le_left (le_trans inf_le_right hI0N)
      exact (nine3_dcal_inf_I0 h hD'mem).1 (le_bot_iff.mp (hbot ▸ hle))
    have hnorm_comm : conjSubgroup V a ≤ normalizer (conjSubgroup V b : Set G) →
        conjSubgroup V a ≤ Subgroup.centralizer (conjSubgroup V b : Set G) := by
      intro hle
      have hP : IsPGroup 2 ↥(conjSubgroup V a ⊔ conjSubgroup V b) :=
        IsPGroup.to_sup_of_normal_right' (E3.isPGroup_conjSubgroup hVp a)
          (E3.isPGroup_conjSubgroup hVp b) hle
      have hc := commute_of_isPGroup_sup hVab hTI ⟨a, rfl⟩ ⟨b, rfl⟩ hDinfN hP
      intro u hu
      rw [Subgroup.mem_centralizer_iff]
      intro u' hu'
      exact (hc u hu u' hu').symm
    have hDnotnorm : ¬ conjSubgroup V a ≤ normalizer (conjSubgroup V b : Set G) :=
      fun hle => hne_comm (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hnorm_comm hle))
    have hD'notnorm : ¬ conjSubgroup V b ≤ normalizer (conjSubgroup V a : Set G) := by
      intro hle
      have hP : IsPGroup 2 ↥(conjSubgroup V b ⊔ conjSubgroup V a) :=
        IsPGroup.to_sup_of_normal_right' (E3.isPGroup_conjSubgroup hVp b)
          (E3.isPGroup_conjSubgroup hVp a) hle
      have hc := commute_of_isPGroup_sup hVab hTI ⟨b, rfl⟩ ⟨a, rfl⟩ hD'infN hP
      have hcentral' : conjSubgroup V b ≤ Subgroup.centralizer (conjSubgroup V a : Set G) := by
        intro u hu
        rw [Subgroup.mem_centralizer_iff]
        intro u' hu'
        exact (hc u hu u' hu').symm
      have hbot : ⁅conjSubgroup V a, conjSubgroup V b⁆ = ⊥ := by
        rw [Subgroup.commutator_comm]
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcentral'
      exact hne_comm hbot
    obtain ⟨u'g, hu'D', hu'notNnorm, hu'notNsub⟩ :
        ∃ x ∈ conjSubgroup V b,
          x ∉ normalizer (conjSubgroup V a : Set G) ∧ x ∉ Nsub := by
      by_contra hcon
      have hcover : (conjSubgroup V b : Set G) ⊆
          (((conjSubgroup V b ⊓ normalizer (conjSubgroup V a : Set G) : Subgroup G)) : Set G) ∪
            (((conjSubgroup V b ⊓ Nsub : Subgroup G)) : Set G) := by
        intro x hx
        by_cases h1 : x ∈ normalizer (conjSubgroup V a : Set G)
        · exact Or.inl ⟨hx, h1⟩
        · by_cases h2 : x ∈ Nsub
          · exact Or.inr ⟨hx, h2⟩
          · exact absurd ⟨x, hx, h1, h2⟩ hcon
      rcases (SubgroupClass.subset_union.mp hcover) with hle | hle
      · exact hD'notnorm (le_trans hle inf_le_right)
      · exact hD'notNsub (le_trans hle inf_le_right)
    have hu'H0 : u'g ∈ nineH0 V K g := nine3_dcal_le_H0 h.hc hD'mem hu'D'
    let u' : ↥(nineH0 V K g) := ⟨u'g, hu'H0⟩
    have hu'D'' : (u' : G) ∈ conjSubgroup V b := hu'D'
    have hu'notker : u' ∉ π.ker := fun hk => hu'notNsub ((hNsub_mem u').mpr hk)
    have hyN : u'g ∉ conjSubgroup V b ⊓ normalizer (conjSubgroup V a : Set G) :=
      fun hh => hu'notNnorm (Subgroup.mem_inf.mp hh).2
    have hDinfNsub_le : conjSubgroup V a ⊓ Nsub ≤
        normalizer (conjSubgroup V b : Set G) := by
      intro x hx
      by_contra hxN
      have hxD : x ∈ conjSubgroup V a := (Subgroup.mem_inf.mp hx).1
      have hxNsub : x ∈ Nsub := (Subgroup.mem_inf.mp hx).2
      have hxH0 : x ∈ nineH0 V K g := nine3_dcal_le_H0 h.hc hDmem hxD
      let d₀ : ↥(nineH0 V K g) := ⟨x, hxH0⟩
      have hxnot : x ∉ conjSubgroup V a ⊓ normalizer (conjSubgroup V b : Set G) :=
        fun hh => hxN (Subgroup.mem_inf.mp hh).2
      have hodd : Odd (orderOf (x * u'g)) :=
        odd_orderOf_mul_of_conj hVab hTI hDinfN hxD hxnot hu'D' hyN
      have hπx : π d₀ = 1 := by
        rw [hNsub] at hxNsub
        obtain ⟨k, hk, hkG⟩ := hxNsub
        have hkz : k = d₀ := Subtype.ext (by simpa [d₀] using hkG)
        rw [← hkz]
        exact MonoidHom.mem_ker.mp hk
      have hπu' : π u' = π d' := nine3_dcal_image_eq h hπ hD'mem hd'D' hu'D'' hd' hu'notker
      have hoddH : Odd (orderOf (d₀ * u')) := by
        have hcoe : ((d₀ * u' : ↥(nineH0 V K g)) : G) = x * u'g := by simp [d₀, u']
        rw [← Subgroup.orderOf_coe (d₀ * u'), hcoe]
        exact hodd
      have himg : π (d₀ * u') = π d' := by rw [map_mul, hπx, one_mul, hπu']
      have hoddπ : Odd (orderOf (π (d₀ * u'))) :=
        hoddH.of_dvd_nat (orderOf_map_dvd π (d₀ * u'))
      rw [himg] at hoddπ
      have horder2 : orderOf (π d') = 2 := by
        have hsq' : (π d') ^ 2 = 1 := by
          have hd'2 : d' * d' = 1 := by
            apply Subtype.ext
            have hh := (E3.isElemAbelian_conjSubgroup hVab b).2 (d' : G) hd'D'
            simpa [pow_two] using hh
          rw [pow_two, ← map_mul, hd'2, map_one]
        rcases (Nat.dvd_prime Nat.prime_two).mp
          (orderOf_dvd_iff_pow_eq_one.mpr hsq') with h1 | h1
        · exact absurd (orderOf_eq_one_iff.mp h1) hd'
        · exact h1
      rw [horder2] at hoddπ
      exact absurd hoddπ (by decide)
    obtain ⟨ug, hugD, hugNotN⟩ : ∃ x ∈ conjSubgroup V a,
        x ∉ normalizer (conjSubgroup V b : Set G) := by
      by_contra hcon
      have hle : conjSubgroup V a ≤ normalizer (conjSubgroup V b : Set G) := by
        intro y hy
        by_contra hyn
        exact hcon ⟨y, hy, hyn⟩
      exact hDnotnorm hle
    have huH0 : ug ∈ nineH0 V K g := nine3_dcal_le_H0 h.hc hDmem hugD
    let u : ↥(nineH0 V K g) := ⟨ug, huH0⟩
    have huD : (u : G) ∈ conjSubgroup V a := hugD
    have huNotker : u ∉ π.ker := by
      intro hk
      have hxNsub : ug ∈ Nsub := (hNsub_mem u).mpr hk
      exact hugNotN (hDinfNsub_le (Subgroup.mem_inf.mpr ⟨hugD, hxNsub⟩))
    have hxnot : ug ∉ conjSubgroup V a ⊓ normalizer (conjSubgroup V b : Set G) :=
      fun hh => hugNotN (Subgroup.mem_inf.mp hh).2
    have hodd : Odd (orderOf (ug * u'g)) :=
      odd_orderOf_mul_of_conj hVab hTI hDinfN hugD hxnot hu'D' hyN
    have hπu : π u = π d := nine3_dcal_image_eq h hπ hDmem hdD huD hd huNotker
    have hπu' : π u' = π d' := nine3_dcal_image_eq h hπ hD'mem hd'D' hu'D'' hd' hu'notker
    have hoddH : Odd (orderOf (u * u')) := by
      have hcoe : ((u * u' : ↥(nineH0 V K g)) : G) = ug * u'g := by simp [u, u']
      rw [← Subgroup.orderOf_coe (u * u'), hcoe]
      exact hodd
    have himg : π (u * u') = π d * π d' := by rw [map_mul, hπu, hπu']
    have hoddπ : Odd (orderOf (π (u * u'))) :=
      hoddH.of_dvd_nat (orderOf_map_dvd π (u * u'))
    rw [himg] at hoddπ
    have horder2 : orderOf (π d * π d') = 2 := by
      have hsqd : (π d) ^ 2 = 1 := by
        have hd2 : d * d = 1 := by
          apply Subtype.ext
          have hh := (E3.isElemAbelian_conjSubgroup hVab a).2 (d : G) hdD
          simpa [pow_two] using hh
        rw [pow_two, ← map_mul, hd2, map_one]
      have hsqd' : (π d') ^ 2 = 1 := by
        have hd'2 : d' * d' = 1 := by
          apply Subtype.ext
          have hh := (E3.isElemAbelian_conjSubgroup hVab b).2 (d' : G) hd'D'
          simpa [pow_two] using hh
        rw [pow_two, ← map_mul, hd'2, map_one]
      have hsq : (π d * π d') ^ 2 = 1 := by
        rw [Commute.mul_pow hcomm 2, hsqd, hsqd', one_mul]
      have hne1 : orderOf (π d * π d') ≠ 1 := by
        intro h1
        have hprod : π d * π d' = 1 := orderOf_eq_one_iff.mp h1
        have hπ : π d = π d' := by
          calc π d = π d * 1 := (mul_one _).symm
            _ = π d * (π d' * π d') := by rw [← pow_two, hsqd']
            _ = (π d * π d') * π d' := by rw [mul_assoc]
            _ = 1 * π d' := by rw [hprod]
            _ = π d' := one_mul _
        exact hne hπ
      rcases (Nat.dvd_prime Nat.prime_two).mp
        (orderOf_dvd_iff_pow_eq_one.mpr hsq) with h1 | h1
      · exact absurd h1 hne1
      · exact h1
    rw [horder2] at hoddπ
    exact absurd hoddπ (by decide)
  intro u hu u' hu'
  exact ((Subgroup.mem_centralizer_iff.mp (hcentral hu)) u' hu').symm

end CFSG.LocalAnalysis.WeakClosure81
