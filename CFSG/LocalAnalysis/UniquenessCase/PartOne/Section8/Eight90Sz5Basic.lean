module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight90Sz5Defs
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
import CFSG.Blueprint.LieModelAPI

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Sz5

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped IsMulCommutative

theorem exists_two_lift {K D : Type} [Group K] [Finite K] [Group D] (φ : K →* D) (d : D)
    (hd : d ∈ φ.range) (h2 : IsPGroup 2 (Subgroup.zpowers d)) :
    ∃ t : K, φ t = d ∧ IsPGroup 2 (Subgroup.zpowers t) := by
  obtain ⟨k, rfl⟩ := hd
  have hpos : orderOf k ≠ 0 := (orderOf_pos k).ne'
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd hpos
  set m' : ℕ := m ^ Nat.totient (2 ^ a) with hm'
  have hcop : Nat.Coprime m (2 ^ a) := by
    apply Nat.Coprime.pow_right
    exact (Nat.coprime_two_right.mpr hm)
  have hm'1 : m' ≡ 1 [MOD 2 ^ a] := Nat.ModEq.pow_totient hcop
  have hdvd : m ∣ m' :=
    dvd_pow_self m (Nat.totient_pos.mpr (by positivity)).ne'
  have hord : orderOf (φ k) ∣ 2 ^ a := by
    obtain ⟨j, hj⟩ := h2 ⟨φ k, Subgroup.mem_zpowers _⟩
    have hj' : (φ k) ^ (2 ^ j) = 1 := by
      have := congrArg Subtype.val hj
      simpa using this
    obtain ⟨i, hi, hio⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hj')
    have hdk : orderOf (φ k) ∣ 2 ^ a * m := hn ▸ orderOf_map_dvd φ k
    rw [hio] at hdk ⊢
    exact (Nat.Coprime.dvd_of_dvd_mul_right
      (Nat.Coprime.pow_left i (Nat.coprime_two_left.mpr hm)) hdk)
  have hpow : (φ k) ^ (2 ^ a) = 1 := orderOf_dvd_iff_pow_eq_one.mp hord
  refine ⟨k ^ m', ?_, ?_⟩
  · rw [map_pow]
    have h1 : (φ k) ^ m' = (φ k) ^ (m' % 2 ^ a) := pow_eq_pow_mod _ hpow
    have h2' : (φ k) ^ 1 = (φ k) ^ (1 % 2 ^ a) := pow_eq_pow_mod _ hpow
    rw [h1, hm'1, ← h2', pow_one]
  · have hkm : (k ^ m') ^ (2 ^ a) = 1 := by
      rw [← pow_mul]
      apply orderOf_dvd_iff_pow_eq_one.mp
      rw [hn, mul_comm m' (2 ^ a)]
      exact Nat.mul_dvd_mul_left _ hdvd
    intro g
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp g.2
    refine ⟨a, Subtype.ext ?_⟩
    calc ((g ^ 2 ^ a : ↥(Subgroup.zpowers (k ^ m'))) : K) = (g : K) ^ 2 ^ a := rfl
      _ = ((k ^ m') ^ i) ^ (2 ^ a) := by rw [hi]
      _ = ((k ^ m') ^ (2 ^ a)) ^ i := by
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
      _ = 1 := by rw [hkm, one_zpow]
      _ = ((1 : ↥(Subgroup.zpowers (k ^ m'))) : K) := rfl

theorem isSz_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (h : IsSz X 3) :
    IsSz Y 3 := by
  unfold IsSz at h ⊢
  rw [CFSG.Blueprint.LieModel.twistedB2_iff] at h ⊢
  obtain ⟨h0, h2, a, ha, K, iK, fK, hf, hc, ⟨e'⟩⟩ := h
  exact ⟨h0, h2, a, ha, K, iK, fK, hf, hc, ⟨e.symm.trans e'⟩⟩

theorem SzSetup.simple {K : Type} [Group K] {R : Subgroup K} [R.Normal] (h : SzSetup K R) :
    IsSimpleGroup (K ⧸ R) :=
  CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 h.2.2

theorem SzSetup.of_subgroup {G : Type} [Group G] (K : Subgroup G) (hK : ⁅K, K⁆ = K)
    (hSz : IsSz (Bar2 K) 3) : SzSetup ↥K (CFSG.pCore 2 ↥K) :=
  ⟨Subgroup.isPerfect_iff.mpr hK, CFSG.pCore_isPGroup, hSz⟩

theorem SzSetup.quotient {K : Type} [Group K] {R : Subgroup K} [R.Normal] (h : SzSetup K R)
    (N : Subgroup K) [N.Normal] (hNR : N ≤ R) :
    SzSetup (K ⧸ N) (R.map (QuotientGroup.mk' N)) := by
  have := h.1
  exact ⟨inferInstance, h.2.1.map (QuotientGroup.mk' N),
    isSz_of_mulEquiv (QuotientGroup.quotientQuotientEquivQuotient N R hNR).symm h.2.2⟩

theorem ker_le_of_nontrivial {K H : Type} [Group K] [Finite K] [Group H] (R : Subgroup K)
    [R.Normal] (hK : SzSetup K R) (ρ : K →* H) (hρ : ∃ k, ρ k ≠ 1) : ρ.ker ≤ R := by
  have := hK.simple
  obtain ⟨hperf, hR, -⟩ := hK
  have hN : (ρ.ker.map (QuotientGroup.mk' R)).Normal :=
    Subgroup.Normal.map inferInstance (QuotientGroup.mk' R) (QuotientGroup.mk'_surjective R)
  have := hN
  rcases Subgroup.Normal.eq_bot_or_eq_top (ρ.ker.map (QuotientGroup.mk' R)) with h | h
  · intro n hn
    have hmem : (QuotientGroup.mk' R) n ∈ ρ.ker.map (QuotientGroup.mk' R) := ⟨n, hn, rfl⟩
    rw [h] at hmem
    simpa [QuotientGroup.eq_one_iff] using hmem
  · exfalso
    have hrange : ρ.range ≤ R.map ρ := by
      rintro _ ⟨k, rfl⟩
      have hk : (QuotientGroup.mk' R) k ∈ ρ.ker.map (QuotientGroup.mk' R) := by rw [h]; trivial
      obtain ⟨n, hn, hnk⟩ := hk
      refine ⟨n⁻¹ * k, ?_, ?_⟩
      · simp only [QuotientGroup.mk'_apply] at hnk
        exact QuotientGroup.eq.mp hnk
      · have : ρ n = 1 := hn
        simp [this]
    have hp2 : IsPGroup 2 ↥(R.map ρ) := hR.map ρ
    have hp2' : IsPGroup 2 ↥ρ.range := by
      have e : ρ.range = R.map ρ := le_antisymm hrange (by
        rintro _ ⟨r, -, rfl⟩; exact ⟨r, rfl⟩)
      rw [e]; exact hp2
    have : Finite ↥ρ.range := Finite.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
    have hnil : Group.IsNilpotent ↥ρ.range := IsPGroup.isNilpotent hp2'
    have : Group.IsPerfect ↥ρ.range := Group.IsPerfect.range ρ
    obtain ⟨k, hk⟩ := hρ
    have : Nontrivial ↥ρ.range := ⟨⟨⟨ρ k, k, rfl⟩, 1, fun h => hk (congrArg Subtype.val h)⟩⟩
    exact Group.IsPerfect.not_isNilpotent ↥ρ.range hnil

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Sz5
