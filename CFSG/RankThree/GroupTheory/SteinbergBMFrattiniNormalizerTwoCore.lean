module

public import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore

public section

namespace CFSG.RankThree.GroupTheory.SteinbergBM

open Subgroup CFSG.RankThree.LocalRank
open scoped Pointwise

variable {G : Type*} [Group G]

theorem le_normalizer_of_forall_conj_mem {M K : Subgroup G}
    (h : ∀ k ∈ K, ∀ x ∈ M, k * x * k⁻¹ ∈ M) : K ≤ normalizer (M : Set G) := by
  intro k hk
  rw [mem_normalizer_iff]
  intro x
  refine ⟨h k hk x, fun hx => ?_⟩
  have := h k⁻¹ (K.inv_mem hk) _ hx
  simpa [mul_assoc] using this

theorem exists_mul_mem_normalizer_sylow [Finite G] {p : ℕ} [Fact p.Prime] {R : Subgroup G}
    (S : Sylow p R) {h : G} (hh : h ∈ normalizer (R : Set G)) :
    ∃ r ∈ R, r * h ∈ normalizer (((S : Subgroup R).map R.subtype : Subgroup G) : Set G) := by
  let σ : MulAut R := R.normalizerMonoidHom ⟨h, hh⟩
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq R (σ • S) S
  refine ⟨n, n.2, ?_⟩
  rw [Sylow.smul_def, ← mul_smul, Sylow.ext_iff, Sylow.pointwise_smul_def] at hn
  have hτ : ∀ y : R, (((MulAut.conj n * σ) • y : R) : G) = n * h * y * (n * h)⁻¹ := by
    intro y
    change (n : G) * (h * y * h⁻¹) * (n : G)⁻¹ = _
    group
  rw [mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : (MulAut.conj n * σ) • y ∈ (S : Subgroup R) := by
      rw [← hn]
      exact Subgroup.smul_mem_pointwise_smul y _ _ hy
    exact ⟨_, hy', hτ y⟩
  · rintro ⟨z, hz, hzx⟩
    rw [← hn] at hz
    have hy := (Subgroup.mem_pointwise_smul_iff_inv_smul_mem).mp hz
    refine ⟨(MulAut.conj n * σ)⁻¹ • z, hy, ?_⟩
    have h1 := hτ ((MulAut.conj n * σ)⁻¹ • z)
    rw [smul_inv_smul] at h1
    change (z : G) = _ at hzx
    have h2 : n * h * (((MulAut.conj n * σ)⁻¹ • z : R) : G) * (n * h)⁻¹ =
        n * h * x * (n * h)⁻¹ := h1.symm.trans hzx
    simpa using h2

theorem le_normalizer_inSubgroup_pCore (p : ℕ) (N : Subgroup G) :
    N ≤ normalizer ((CFSG.inSubgroup (CFSG.pCore p) N : Subgroup G) : Set G) :=
  le_normalizer_of_forall_conj_mem fun k hk _ ⟨y, hy, hyx⟩ => hyx ▸
    ⟨⟨k, hk⟩ * y * ⟨k, hk⟩⁻¹, (CFSG.pCore_normal (p := p) (G := N)).conj_mem y hy _, rfl⟩

theorem isSolvable_and_not_dvd_of_mul_two_group [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {R U M : Subgroup G} (hRM : R ≤ M) (hMR : M ≤ normalizer (R : Set G)) (hU : IsPGroup 2 U)
    (hUM : U ≤ M) (hM : ∀ x ∈ M, ∃ r ∈ R, ∃ u ∈ U, r * u = x) (hRs : Group.IsSolvable R)
    (hRp : ¬ p ∣ Nat.card R) : Group.IsSolvable M ∧ ¬ p ∣ Nat.card M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R₀ := R.subgroupOf M with hR₀
  have : R₀.Normal := (normal_subgroupOf_iff_le_normalizer hRM).mpr hMR
  have hQ : IsPGroup 2 (M ⧸ R₀) := by
    intro q
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective R₀ q
    obtain ⟨r, hr, u, hu, hru⟩ := hM m m.2
    obtain ⟨k, hk⟩ := hU ⟨u, hu⟩
    refine ⟨k, ?_⟩
    have hm : m = ⟨r, hRM hr⟩ * ⟨u, hUM hu⟩ := Subtype.ext hru.symm
    have hr1 : QuotientGroup.mk' R₀ (⟨r, hRM hr⟩ : M) = 1 := (QuotientGroup.eq_one_iff _).mpr hr
    have hu' : u ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hu1 : (⟨u, hUM hu⟩ : M) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hu')
    rw [hm, map_mul, hr1, one_mul, ← map_pow, hu1, map_one]
  have hR₀R : R₀ ≃* R := subgroupOfEquivOfLe hRM
  have hR₀s : Group.IsSolvable R₀ := Group.isSolvable_of_isSolvable_injective
    (f := hR₀R.toMonoidHom) hR₀R.injective
  refine ⟨?_, ?_⟩
  · have := hQ.isNilpotent
    refine Group.isSolvable_of_ker_le_range R₀.subtype (QuotientGroup.mk' R₀) fun x hx => ?_
    rw [QuotientGroup.ker_mk'] at hx
    exact ⟨⟨x, hx⟩, rfl⟩
  · obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ
    have hcard := card_eq_card_quotient_mul_card_subgroup R₀
    rw [hk, Nat.card_congr hR₀R.toEquiv] at hcard
    rw [hcard]
    intro hdvd
    rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
    · exact hRp h

theorem frattini_normalizer_two_core_solvable_prime_complement_containment [Finite G] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {D R : Subgroup G} (hRH : R ≤ centralizer (D : Set G))
    (hRn : (R.subgroupOf (centralizer (D : Set G))).Normal) (hRs : Group.IsSolvable R)
    (hRp : ¬ p ∣ Nat.card R) (S : Sylow 2 R) :
    CFSG.inSubgroup (CFSG.pCore 2)
        (normalizer (((S : Subgroup R).map R.subtype : Subgroup G) : Set G)) ⊓
        centralizer (D : Set G) ≤
      CFSG.inSubgroup (aschbacherSolvableCore p) (centralizer (D : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := centralizer (D : Set G) with hHdef
  set N := normalizer (((S : Subgroup R).map R.subtype : Subgroup G) : Set G) with hNdef
  set P := CFSG.inSubgroup (CFSG.pCore 2) N with hPdef
  set U := P ⊓ H with hUdef
  have hHR : H ≤ normalizer (R : Set G) := (normal_subgroupOf_iff_le_normalizer hRH).mp hRn
  have hNP : N ≤ normalizer (P : Set G) := le_normalizer_inSubgroup_pCore 2 N
  have hP2 : IsPGroup 2 P := (CFSG.pCore_isPGroup (p := 2) (G := N)).map N.subtype
  have hUR : U ≤ normalizer (R : Set G) := inf_le_right.trans hHR
  set M := R ⊔ U with hMdef
  have hMcoe : (M : Set G) = (R : Set G) * (U : Set G) :=
    coe_mul_of_right_le_normalizer_left R U hUR
  have hMdec : ∀ x ∈ M, ∃ r ∈ R, ∃ u ∈ U, r * u = x := fun x hx => by
    have hx' : x ∈ (M : Set G) := hx
    rw [hMcoe] at hx'
    obtain ⟨r, hr, u, hu, rfl⟩ := hx'
    exact ⟨r, hr, u, hu, rfl⟩
  have hMH : M ≤ H := sup_le hRH inf_le_right
  have hKM : H ⊓ N ≤ normalizer (M : Set G) := by
    refine le_normalizer_of_forall_conj_mem fun k hk x hx => ?_
    obtain ⟨r, hr, u, hu, rfl⟩ := hMdec x hx
    have hkr : k * r * k⁻¹ ∈ R := (mem_normalizer_iff.mp (hHR hk.1) r).mp hr
    have hku : k * u * k⁻¹ ∈ U :=
      ⟨(mem_normalizer_iff.mp (hNP hk.2) u).mp hu.1, H.mul_mem (H.mul_mem hk.1 hu.2)
        (H.inv_mem hk.1)⟩
    have he : k * (r * u) * k⁻¹ = (k * r * k⁻¹) * (k * u * k⁻¹) := by group
    rw [he]
    exact mul_mem (mem_sup_left hkr) (mem_sup_right hku)
  have hHM : H ≤ normalizer (M : Set G) := by
    intro h hh
    obtain ⟨r, hr, hrh⟩ := exists_mul_mem_normalizer_sylow S (hHR hh)
    have hk : r * h ∈ normalizer (M : Set G) :=
      hKM ⟨H.mul_mem (hRH hr) hh, hrh⟩
    have hr' : r⁻¹ ∈ normalizer (M : Set G) := le_normalizer (M.inv_mem (mem_sup_left hr))
    simpa using mul_mem hr' hk
  have hMn : (M.subgroupOf H).Normal := (normal_subgroupOf_iff_le_normalizer hMH).mpr hHM
  obtain ⟨hMs, hMp⟩ := isSolvable_and_not_dvd_of_mul_two_group hp hp2 le_sup_left
    (sup_le le_normalizer hUR) (hP2.to_le inf_le_left) le_sup_right hMdec hRs hRp
  have hMHe : M.subgroupOf H ≃* M := subgroupOfEquivOfLe hMH
  have hle := (solvable_prime_complement_core_characterization (H := H) hp).2.2.2.1
    (M.subgroupOf H) hMn
    (Group.isSolvable_of_isSolvable_injective (f := hMHe.toMonoidHom) hMHe.injective)
    (by rwa [Nat.card_congr hMHe.toEquiv])
  intro x hx
  have hxM : x ∈ M := mem_sup_right hx
  exact ⟨⟨x, hMH hxM⟩, hle (show (⟨x, hMH hxM⟩ : H) ∈ M.subgroupOf H from hxM), rfl⟩

end CFSG.RankThree.GroupTheory.SteinbergBM
