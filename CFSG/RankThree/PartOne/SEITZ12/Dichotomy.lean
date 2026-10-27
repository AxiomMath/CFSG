module

public import CFSG.RankThree.PartOne.SEITZ12.Classes

public section

namespace CFSG.RankThree.PartOne.SEITZ12

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution CFSG.LieType.Ree.LargeReeCover
  CFSG.RankThree.PartOne.SEITZ7

theorem phi4_mem_sup_of_le_normalizer {G : Type*} [Group G] {N H : Subgroup G}
    (h : H ≤ Subgroup.normalizer (N : Set G)) {x : G} (hx : x ∈ N ⊔ H) :
    ∃ v ∈ N, ∃ r ∈ H, x = v * r := by
  let S : Subgroup G :=
    { carrier := {x | ∃ v ∈ N, ∃ r ∈ H, x = v * r}
      mul_mem' := by
        rintro _ _ ⟨v, hv, r, hr, rfl⟩ ⟨v', hv', r', hr', rfl⟩
        refine ⟨v * (r * v' * r⁻¹), N.mul_mem hv ?_, r * r', H.mul_mem hr hr', by group⟩
        exact (Subgroup.mem_normalizer_iff.1 (h hr) v').1 hv'
      one_mem' := ⟨1, N.one_mem, 1, H.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨v, hv, r, hr, rfl⟩
        refine ⟨r⁻¹ * v⁻¹ * r, ?_, r⁻¹, H.inv_mem hr, by group⟩
        have h1 := (Subgroup.mem_normalizer_iff.1 (h (H.inv_mem hr)) v⁻¹).1 (N.inv_mem hv)
        simpa using h1 }
  have : N ⊔ H ≤ S := sup_le (fun v hv => ⟨v, hv, 1, H.one_mem, by simp⟩)
    (fun r hr => ⟨1, N.one_mem, r, hr, by simp⟩)
  exact this hx

set_option linter.unusedSectionVars false

variable {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K F4.prime]

theorem phi4_mem_Z₁_iff {z : ModGL F4.tag K} :
    z ∈ conjSub (zTwo m K) (szNw K) ↔ ∃ c : K, z = centralZ K m c := by
  have ht : (szNw K)⁻¹ = szNw K := inv_eq_of_mul_eq_one_right szNw_mul_self
  have h2 := szNw_mul_self (K := K)
  rw [mem_conjSub, mem_zTwo_iff, ht]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    have h := szNw_conj_sylowB_zero (m := m) (K := K) c
    rw [ht] at h
    have : z = szNw K * (szNw K * z * szNw K) * szNw K := by
      calc z = (szNw K * szNw K) * z * (szNw K * szNw K) := by rw [h2]; group
        _ = _ := by group
    rw [this, hc]
    exact h
  · rintro ⟨c, rfl⟩
    refine ⟨c, ?_⟩
    have h := szNw_conj_sylowH (m := m) (K := K) 0 c
    rw [ht, sylowH_zero_eq_centralZ] at h
    exact h

theorem phi4_inf_centralizer_centralZ (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1)) {c : K}
    (hc : c ≠ 0) :
    F4.reeGamma K m ⊓ Subgroup.centralizer {centralZ K m c} =
      F4.reeGamma K m ⊓ Subgroup.centralizer {centralZ K m 1} := by
  have : Finite (ModGL F4.tag K) := finite_modGL
  obtain ⟨g, hg, hgz⟩ := inTwoA_centralZ hK hc
  have hle : F4.reeGamma K m ⊓ Subgroup.centralizer {centralZ K m 1} ≤
      F4.reeGamma K m ⊓ Subgroup.centralizer {centralZ K m c} := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    have hx' : x ∈ centralizerZ K m := by
      rw [← reeGamma_inf_centralizer_eq hm hK]
      exact hx
    exact centralizerZ_le_centralizer hm hK c hx'
  have hcard : Nat.card (F4.reeGamma K m ⊓ Subgroup.centralizer {centralZ K m c} :
      Subgroup (ModGL F4.tag K)) =
      Nat.card (F4.reeGamma K m ⊓ Subgroup.centralizer {centralZ K m 1} :
        Subgroup (ModGL F4.tag K)) := by
    rw [← hgz]
    exact card_inf_centralizer_conj hg
  exact (Subgroup.eq_of_le_of_card_ge hle hcard.le).symm

theorem phi4_centralZ_injective (hK : Nat.card K = 2 ^ (2 * m + 1)) {c c' : K}
    (h : centralZ K m c = centralZ K m c') : c = c' := by
  have hz : ∀ c : K, sylowVec m K (Pi.single 8 c) = centralZ K m c := by
    intro c
    rw [← sylowH_zero_eq_centralZ]
    simp [sylowVec, sylowV, sylowA, sylowB, sylowD, sylowF, sylowJ, sylowK, sylowL, sylowX,
      largeReeSigma_zero, pinnedX_zero]
  have h1 := (bijOn_sylowVec hK).injOn (Set.mem_univ _) (Set.mem_univ _)
    ((hz c).trans (h.trans (hz c').symm))
  simpa using congrFun h1 8

theorem phi4_centralZ_zero : centralZ K m 0 = 1 := centralZ_zero

theorem phi4_centralZ_ne_one (hK : Nat.card K = 2 ^ (2 * m + 1)) : centralZ K m 1 ≠ 1 := by
  intro h
  exact one_ne_zero (phi4_centralZ_injective hK (h.trans phi4_centralZ_zero.symm))

theorem phi4_two_element_centralizes (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1))
    {n : ModGL F4.tag K} (hn : n ∈ F4.reeGamma K m) {k : ℕ} (hord : n ^ 2 ^ k = 1)
    (hnorm : ∀ z ∈ conjSub (zTwo m K) (szNw K), n * z * n⁻¹ ∈ conjSub (zTwo m K) (szNw K)) :
    ∀ z ∈ conjSub (zTwo m K) (szNw K), n * z = z * n := by
  obtain ⟨c₁, hc₁⟩ :=
    phi4_mem_Z₁_iff.1 (hnorm (centralZ K m 1) (phi4_mem_Z₁_iff.2 ⟨1, rfl⟩))
  have hc₁0 : c₁ ≠ 0 := by
    rintro rfl
    rw [phi4_centralZ_zero] at hc₁
    apply phi4_centralZ_ne_one hK
    have : centralZ K m 1 = n⁻¹ * (n * centralZ K m 1 * n⁻¹) * n := by group
    rw [this, hc₁]
    group
  obtain ⟨T, hTΓ, hT⟩ : ∃ T ∈ F4.reeGamma K m,
      ∀ i : K, T * centralZ K m i * T⁻¹ = centralZ K m (c₁ * i) := by
    let s : Kˣ := Units.mk0 (largeReeSigma m c₁) ((largeReeSigma_eq_zero_iff _).not.2 hc₁0)
    have hs : (s : K) ^ 2 ^ m = c₁ := largeReeSigma_pow_two_pow hK c₁
    refine ⟨pairedTorusHom m (f4i 0) (f4i 3) s,
      reeFixedTorus_le_reeGamma' (torusOne_mem hK s), fun i => ?_⟩
    have h := torusOne_conj_sylowH hK s i
    rw [sylowH_zero_eq_centralZ, sylowH_zero_eq_centralZ, hs] at h
    exact h
  have hn' : T⁻¹ * n ∈ F4.reeGamma K m ⊓ Subgroup.centralizer {centralZ K m 1} := by
    refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hTΓ) hn, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := hT 1
    rw [mul_one] at h1
    have e1 : T⁻¹ * n * centralZ K m 1 * (T⁻¹ * n)⁻¹ = T⁻¹ * (n * centralZ K m 1 * n⁻¹) * T := by
      group
    have e2 : T⁻¹ * (n * centralZ K m 1 * n⁻¹) * T = T⁻¹ * (T * centralZ K m 1 * T⁻¹) * T := by
      rw [hc₁, ← h1]
    have e3 : T⁻¹ * (T * centralZ K m 1 * T⁻¹) * T = centralZ K m 1 := by group
    have h2 : T⁻¹ * n * centralZ K m 1 * (T⁻¹ * n)⁻¹ = centralZ K m 1 := e1.trans (e2.trans e3)
    exact mul_inv_eq_iff_eq_mul.1 h2
  have hn'c : ∀ c : K, (T⁻¹ * n) * centralZ K m c = centralZ K m c * (T⁻¹ * n) := by
    intro c
    have hn'' : T⁻¹ * n ∈ centralizerZ K m := by
      rw [← reeGamma_inf_centralizer_eq hm hK]
      exact hn'
    have h3 : T⁻¹ * n ∈ Subgroup.centralizer {centralZ K m c} :=
      centralizerZ_le_centralizer hm hK c hn''
    exact Subgroup.mem_centralizer_singleton_iff.1 h3
  have hact : ∀ c : K, n * centralZ K m c * n⁻¹ = centralZ K m (c₁ * c) := by
    intro c
    have e1 : n * centralZ K m c * n⁻¹ =
        T * ((T⁻¹ * n) * centralZ K m c * (T⁻¹ * n)⁻¹) * T⁻¹ := by group
    have e2 : (T⁻¹ * n) * centralZ K m c * (T⁻¹ * n)⁻¹ = centralZ K m c :=
      mul_inv_eq_iff_eq_mul.2 (hn'c c)
    exact e1.trans ((congrArg (fun y => T * y * T⁻¹) e2).trans (hT c))
  have hit : ∀ j : ℕ, n ^ j * centralZ K m 1 * (n ^ j)⁻¹ = centralZ K m (c₁ ^ j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc n ^ (j + 1) * centralZ K m 1 * (n ^ (j + 1))⁻¹
          = n * (n ^ j * centralZ K m 1 * (n ^ j)⁻¹) * n⁻¹ := by group
        _ = n * centralZ K m (c₁ ^ j) * n⁻¹ := by rw [ih]
        _ = centralZ K m (c₁ * c₁ ^ j) := hact _
        _ = centralZ K m (c₁ ^ (j + 1)) := by rw [pow_succ']
  have hc₁1 : c₁ = 1 := by
    have h1 := hit (2 ^ k)
    rw [hord] at h1
    have h2 : centralZ K m 1 = centralZ K m (c₁ ^ 2 ^ k) := by simpa using h1
    have h3 : c₁ ^ 2 ^ k = 1 := (phi4_centralZ_injective hK h2).symm
    have : Fintype K := Fintype.ofFinite K
    have h4 : c₁ ^ (Nat.card K - 1) = 1 := by
      rw [Nat.card_eq_fintype_card]
      exact FiniteField.pow_card_sub_one_eq_one c₁ hc₁0
    have h5 := pow_gcd_eq_one.2 ⟨h3, h4⟩
    have hodd : Nat.Coprime (2 ^ k) (Nat.card K - 1) := by
      refine Nat.Coprime.pow_left k ?_
      rw [hK]
      have h2' : 2 ∣ 2 ^ (2 * m + 1) := dvd_pow_self 2 (by omega)
      have h1' : 1 ≤ 2 ^ (2 * m + 1) := Nat.one_le_two_pow
      rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
      omega
    rwa [hodd, pow_one] at h5
  intro z hz
  obtain ⟨c, rfl⟩ := phi4_mem_Z₁_iff.1 hz
  have h1 := hact c
  rw [hc₁1, one_mul] at h1
  calc n * centralZ K m c = (n * centralZ K m c * n⁻¹) * n := by group
    _ = centralZ K m c * n := by rw [h1]

theorem phi4_decomp_centralizer (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1))
    {x : ModGL F4.tag K} (hx : x ∈ F4.reeGamma K m)
    (hxz : x * centralZ K m 1 = centralZ K m 1 * x) :
    ∃ v ∈ F4.reeFixedOrbitComplementUnipotent K m ⟨1, by decide⟩,
      ∃ r ∈ rankOneGroupTwo K m, x = v * r := by
  have hx' : x ∈ F4.reeGamma K m ⊓ Subgroup.centralizer {centralZ K m 1} :=
    Subgroup.mem_inf.2 ⟨hx, Subgroup.mem_centralizer_singleton_iff.2 hxz⟩
  rw [reeGamma_inf_centralizer_eq hm hK] at hx'
  exact phi4_mem_sup_of_le_normalizer (rankOneGroupTwo_le_normalizer_complement hK) hx'

end CFSG.RankThree.PartOne.SEITZ12
