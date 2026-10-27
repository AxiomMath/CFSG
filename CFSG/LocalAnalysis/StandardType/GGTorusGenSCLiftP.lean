module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenSCLift

public section

namespace CFSG.StandardType

namespace TorusSCLift

theorem exists_lift_isPGroup_subgroup {p : ℕ} (hp : p.Prime) {M R : Type} [Group M]
    [Finite M] [Group R] {L' J' : Subgroup M} {ψ : L' →* R}
    (hpker : ¬ p ∣ Nat.card ψ.ker) {Sbar : Subgroup R} (hSbar : IsPGroup p Sbar)
    (hSbarJ : Sbar ≤ (J'.subgroupOf L').map ψ) :
    ∃ S : Subgroup L', IsPGroup p S ∧ S ≤ J'.subgroupOf L' ∧ S.map ψ = Sbar := by
  let SL : Subgroup L' := J'.subgroupOf L'
  let P0 : Subgroup L' := Sbar.comap ψ ⊓ SL
  have hP0comap : P0 ≤ Sbar.comap ψ := inf_le_left
  have hP0SL : P0 ≤ SL := inf_le_right
  let φ : P0 →* Sbar := (ψ.comp P0.subtype).codRestrict Sbar fun x =>
    Subgroup.mem_comap.mp (Subgroup.mem_inf.mp x.2).1
  have hφ : Function.Surjective φ := by
    intro s
    have hsJ : (s : R) ∈ SL.map ψ := hSbarJ s.2
    obtain ⟨j, hjSL, hjs⟩ := Subgroup.mem_map.mp hsJ
    have hjP0 : j ∈ P0 := ⟨Subgroup.mem_comap.mpr (by rw [hjs]; exact s.2), hjSL⟩
    refine ⟨⟨j, hjP0⟩, ?_⟩
    apply Subtype.ext
    exact hjs
  have hfin : Finite Sbar := Finite.of_surjective φ hφ
  obtain ⟨n, hncard⟩ := (@IsPGroup.iff_card p Sbar _ (Fact.mk hp) hfin).mp hSbar
  have hmapker_le : (φ.ker).map P0.subtype ≤ ψ.ker := by
    rintro _ ⟨x, hx, rfl⟩
    have hx1 : φ x = 1 := hx
    have hval := congrArg Subtype.val hx1
    simpa [φ] using hval
  have hcardφdvd : Nat.card φ.ker ∣ Nat.card ψ.ker := by
    have hcard : Nat.card φ.ker = Nat.card ((φ.ker).map P0.subtype) := by
      rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective P0)]
    rw [hcard]
    exact Subgroup.card_dvd_of_le hmapker_le
  have hpkerφ : ¬ p ∣ Nat.card φ.ker := fun h => hpker (h.trans hcardφdvd)
  have hcop : Nat.Coprime (Nat.card φ.ker) φ.ker.index := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hφ, Subgroup.card_top, hncard]
    exact Nat.Prime.coprime_pow_of_not_dvd hp hpkerφ
  obtain ⟨K, hcomp⟩ := Subgroup.exists_right_complement'_of_coprime (N := φ.ker) hcop
  let fK : K →* Sbar := φ.comp K.subtype
  have hfKinj : Function.Injective fK := by
    intro a b hab
    change φ (a : P0) = φ (b : P0) at hab
    apply Subtype.ext
    have habP : (a : P0) * (b : P0)⁻¹ ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hab, mul_inv_cancel]
    have habK : (a : P0) * (b : P0)⁻¹ ∈ K := K.mul_mem a.2 (K.inv_mem b.2)
    have hdisj := hcomp.symm.isCompl.disjoint
    have hbot : (a : P0) * (b : P0)⁻¹ ∈ (⊥ : Subgroup P0) :=
      Subgroup.disjoint_def.mp hdisj habK habP
    exact mul_inv_eq_one.mp (Subgroup.mem_bot.mp hbot)
  have hfKsurj : Function.Surjective fK := by
    intro s
    obtain ⟨x, rfl⟩ := hφ s
    have hsup : K ⊔ φ.ker = ⊤ := hcomp.symm.isCompl.sup_eq_top
    have hxsup : x ∈ K ⊔ φ.ker := by rw [hsup]; trivial
    rw [Subgroup.mem_sup_of_normal_right] at hxsup
    obtain ⟨k, hkK, m, hmker, hkm⟩ := hxsup
    refine ⟨⟨k, hkK⟩, ?_⟩
    change φ k = φ x
    have hm1 : φ m = 1 := hmker
    calc φ k = φ (k * m) := by rw [map_mul, hm1, mul_one]
      _ = φ x := by rw [← hkm]
  let S : Subgroup L' := K.map P0.subtype
  refine ⟨S, ?_, ?_, ?_⟩
  · let eK : K ≃* Sbar := MulEquiv.ofBijective fK ⟨hfKinj, hfKsurj⟩
    have hKp : IsPGroup p K := IsPGroup.of_equiv hSbar eK.symm
    exact hKp.map P0.subtype
  · rintro _ ⟨k, hk, rfl⟩
    exact hP0SL k.2
  · apply le_antisymm
    · rintro s ⟨x, hxS, rfl⟩
      obtain ⟨k, hk, rfl⟩ := hxS
      exact Subgroup.mem_comap.mp (Subgroup.mem_inf.mp k.2).1
    · intro s hs
      obtain ⟨k, hk⟩ := hfKsurj ⟨s, hs⟩
      refine ⟨(k : P0), ⟨k, k.2, rfl⟩, ?_⟩
      have hval := congrArg Subtype.val hk
      change ψ ((k : P0) : L') = s
      simpa [fK, φ] using hval

private theorem conj_eq_of_mem_centralizer_range {p : ℕ} {M R : Type} [Group M]
    [Group R] {L' E : Subgroup M} {θ : L' ⧸ Subgroup.center L' ≃* R}
    (hp : p.Prime) (hcpZ : ¬ p ∣ Nat.card (Subgroup.center (↥L')))
    {ρ : E →* R} (hρψ : ∀ (e : E) (he : (e : M) ∈ L'),
      ρ e = ggQuotHom θ ⟨(e : M), he⟩)
    {SL : Subgroup L'} (hSLp : IsPGroup p SL)
    (hSLcent : ∀ s ∈ SL, ggQuotHom θ s ∈ Subgroup.centralizer (ρ.range : Set R))
    {a : M} (haE : a ∈ E) (haL : a ∈ L') {sL : L'} (hsL : sL ∈ SL) :
    a * (sL : M) * a⁻¹ = (sL : M) := by
  have hψa : ggQuotHom θ ⟨a, haL⟩ = ρ ⟨a, haE⟩ := (hρψ ⟨a, haE⟩ haL).symm
  have hcomm : ggQuotHom θ ⟨a, haL⟩ * ggQuotHom θ sL =
      ggQuotHom θ sL * ggQuotHom θ ⟨a, haL⟩ := by
    rw [hψa]
    exact Subgroup.mem_centralizer_iff.mp (hSLcent sL hsL) (ρ ⟨a, haE⟩) ⟨⟨a, haE⟩, rfl⟩
  have hwmem : a * (sL : M) * a⁻¹ * (sL : M)⁻¹ ∈ L' :=
    L'.mul_mem (L'.mul_mem (L'.mul_mem haL sL.2) (L'.inv_mem haL)) (L'.inv_mem sL.2)
  let w : L' := ⟨a * (sL : M) * a⁻¹ * (sL : M)⁻¹, hwmem⟩
  have hwψ : ggQuotHom θ w = 1 := by
    change ggQuotHom θ ⟨a * (sL : M) * a⁻¹ * (sL : M)⁻¹, hwmem⟩ = 1
    change ggQuotHom θ ((⟨a, haL⟩ : L') * sL * (⟨a, haL⟩ : L')⁻¹ * sL⁻¹) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    rw [hcomm]
    group
  have hwcent : w ∈ Subgroup.center (↥L') := by
    rw [← ker_ggQuotHom θ]
    exact MonoidHom.mem_ker.mpr hwψ
  obtain ⟨k, hk⟩ := IsPGroup.exists_orderOf_dvd_pow hSLp ⟨sL, hsL⟩
  have hsLpow : sL ^ p ^ k = 1 := by
    simpa using congrArg Subtype.val ((orderOf_dvd_iff_pow_eq_one).mp hk)
  have has : (⟨a, haL⟩ : L') * sL * (⟨a, haL⟩ : L')⁻¹ = w * sL := by
    apply Subtype.ext
    change a * (sL : M) * a⁻¹ = (w : M) * (sL : M)
    rw [show (w : M) = a * (sL : M) * a⁻¹ * (sL : M)⁻¹ from rfl]
    group
  have hwpow : w ^ p ^ k = 1 := by
    have hconj : ((⟨a, haL⟩ : L') * sL * (⟨a, haL⟩ : L')⁻¹) ^ p ^ k = 1 := by
      rw [conj_pow, hsLpow, mul_one, mul_inv_cancel]
    have hwcomm : Commute w sL := (Subgroup.mem_center_iff.mp hwcent sL).symm
    rw [has, hwcomm.mul_pow, hsLpow, mul_one] at hconj
    exact hconj
  have hw1 : w = 1 :=
    TorusSCLift.eq_one_of_mem_center_of_pow hp hcpZ hwcent ⟨k, hwpow⟩
  have has_eq : (⟨a, haL⟩ : L') * sL * (⟨a, haL⟩ : L')⁻¹ = sL := by
    rw [has, hw1, one_mul]
  exact congrArg Subtype.val has_eq

theorem map_le_centralizer_of_mem_range {p : ℕ} {M R : Type} [Group M]
    [Group R] {L' E E₁ : Subgroup M} {θ : L' ⧸ Subgroup.center L' ≃* R}
    (hp : p.Prime) (hE₁ : E₁ ≤ E)
    (hdec : ∀ x ∈ E, ∃ a ∈ E ⊓ L', ∃ z ∈ E ⊓ Subgroup.centralizer (L' : Set M),
      x = a * z)
    (hcpZ : ¬ p ∣ Nat.card (Subgroup.center (↥L')))
    {ρ : E →* R} (hρψ : ∀ (e : E) (he : (e : M) ∈ L'),
      ρ e = ggQuotHom θ ⟨(e : M), he⟩)
    {SL : Subgroup L'} (hSLp : IsPGroup p SL)
    (hSLcent : ∀ s ∈ SL, ggQuotHom θ s ∈ Subgroup.centralizer (ρ.range : Set R)) :
    SL.map L'.subtype ≤ Subgroup.centralizer (E₁ : Set M) := by
  intro s hs
  obtain ⟨sL, hsL, rfl⟩ := Subgroup.mem_map.mp hs
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  obtain ⟨a, ha, z, hz, rfl⟩ := hdec x (hE₁ hx)
  obtain ⟨haE, haL⟩ := Subgroup.mem_inf.mp ha
  obtain ⟨-, hzC⟩ := Subgroup.mem_inf.mp hz
  have hsa : a * (sL : M) * a⁻¹ = (sL : M) :=
    conj_eq_of_mem_centralizer_range hp hcpZ hρψ hSLp hSLcent haE haL hsL
  have hsa' : a * (sL : M) = (sL : M) * a := by
    calc a * (sL : M) = (a * (sL : M) * a⁻¹) * a := by group
      _ = (sL : M) * a := by rw [hsa]
  have hsz : (sL : M) * z = z * (sL : M) :=
    Subgroup.mem_centralizer_iff.mp hzC (sL : M) sL.2
  calc (a * z) * (sL : M) = a * (z * (sL : M)) := by group
    _ = a * ((sL : M) * z) := by rw [hsz.symm]
    _ = (a * (sL : M)) * z := by group
    _ = ((sL : M) * a) * z := by rw [hsa']
    _ = (sL : M) * (a * z) := by group

end TorusSCLift

end CFSG.StandardType
