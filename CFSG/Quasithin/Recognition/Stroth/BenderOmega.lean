module

public import CFSG.Quasithin.Recognition.Stroth.BenderBorel
public import CFSG.Quasithin.MS93.S36Frat
public import CFSG.ClassicalInvolution.Asc77.WP3S28BR3Z
public import CFSG.GH74.Generic.S3.Lem26Z
public import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Recognition.Stroth.BenderFF

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

@[expose] def IsSzU3Quot (X : Type) [Group X] (q : ℕ) : Prop :=
  (∃ a : ℕ, 1 ≤ a ∧ q = 2 ^ (2 * a + 1) ∧ Nonempty (X ≃* CFSG.Open.Sz a)) ∨
  (∃ n : ℕ, 2 ≤ n ∧ q = 2 ^ n ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F),
    Nat.card F = (2 ^ n) ^ 2 ∧
    (Nonempty (X ≃* CFSG.Open.StatedSU 3 (2 ^ n) F) ∨
      Nonempty (X ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (2 ^ n) F))))

theorem exists_isSzU3Quot {L : Subgroup G} (h : VSzBig L ∨ VU3Big L) :
    ∃ q, IsSzU3Quot (oTwoQuot ↥L) q := by
  rcases h with ⟨a, ha, ⟨e⟩⟩ | ⟨n, hn, F, hFld, hFin, hF, he⟩
  · exact ⟨2 ^ (2 * a + 1), Or.inl ⟨a, ha, rfl, ⟨e⟩⟩⟩
  · exact ⟨2 ^ n, Or.inr ⟨n, hn, rfl, F, hFld, hFin, hF, he⟩⟩

theorem IsSzU3Quot.of_mulEquiv {X Y : Type} [Group X] [Group Y] {q : ℕ} (e : X ≃* Y)
    (h : IsSzU3Quot Y q) : IsSzU3Quot X q := by
  rcases h with ⟨a, ha, hq, ⟨eY⟩⟩ | ⟨n, hn, hq, F, hFld, hFin, hF, he⟩
  · exact Or.inl ⟨a, ha, hq, ⟨e.trans eY⟩⟩
  · refine Or.inr ⟨n, hn, hq, F, hFld, hFin, hF, ?_⟩
    rcases he with he | he
    · obtain ⟨eY⟩ := he
      exact Or.inl ⟨e.trans eY⟩
    · obtain ⟨eY⟩ := he
      exact Or.inr ⟨e.trans eY⟩

theorem IsSzU3Quot.four_le {X : Type} [Group X] {q : ℕ} (h : IsSzU3Quot X q) : 4 ≤ q := by
  rcases h with ⟨a, ha, hq, -⟩ | ⟨n, hn, hq, -⟩
  · rw [hq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  · rw [hq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn

theorem IsSzU3Quot.facts {X : Type} [Group X] {q : ℕ} (h : IsSzU3Quot X q) :
    CFSG.IsQuasisimple X ∧ ∀ z ∈ Subgroup.center X, z * z = 1 → z = 1 := by
  rcases h with ⟨a, ha, -, ⟨e⟩⟩ | ⟨n, hn, -, F, hFld, hFin, hF, he⟩
  · refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm (isQuasisimple_sz a ha), ?_⟩
    intro z hz hz2
    have hz' : e z ∈ Subgroup.center (CFSG.Open.Sz a) := by
      rw [← Subgroup.map_center_eq e]
      exact Subgroup.mem_map_of_mem e.toMonoidHom hz
    rw [center_sz a ha] at hz'
    exact e.injective (by simpa using Subgroup.mem_bot.mp hz')
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    letI : Field F := hFld
    letI : Finite F := hFin
    letI : Fintype F := Fintype.ofFinite F
    have hcard : Fintype.card F = 2 ^ (2 * n) := by
      rw [← Nat.card_eq_fintype_card, hF, ← pow_mul, Nat.mul_comm n 2]
    haveI : CharP F 2 := charP_of_card_eq_prime_pow (f := 2 * n) hcard
    have hnq : ((3 : ℕ), 2 ^ n) ≠ (3, 2) := by
      intro h3
      have h2 : 2 ^ n = 2 := congrArg Prod.snd h3
      have hle : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      omega
    have hSU := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
      (p := 2) (f := n) (F := F) hF (by norm_num) hnq
    rcases he with he | he
    · obtain ⟨e⟩ := he
      refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hSU.1, ?_⟩
      intro z hz hz2
      have hz' : e z ∈ Subgroup.center (CFSG.Open.StatedSU 3 (2 ^ n) F) := by
        rw [← Subgroup.map_center_eq e]
        exact Subgroup.mem_map_of_mem e.toMonoidHom hz
      have h3 := center_statedSU_pow_three hn hF (e z) hz'
      have h2 : e z * e z = 1 := by rw [← map_mul, hz2, map_one]
      have h1 : e z = 1 := by
        calc e z = (e z) ^ 3 * (e z * e z)⁻¹ := by group
          _ = 1 := by rw [h3, h2, inv_one, one_mul]
      exact e.injective (h1.trans (map_one e).symm)
    · obtain ⟨e⟩ := he
      have hSimple : IsSimpleGroup
          (CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (2 ^ n) F)) :=
        CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F 2 n hF 3
          (by norm_num) hnq
      haveI : IsSimpleGroup (CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (2 ^ n) F)) := hSimple
      have hnc := CFSG.Quasithin.F6.InspRest.exists_noncomm_statedProj
        (H := CFSG.Open.StatedSU 3 (2 ^ n) F) hSU.1 hSimple
      have hP := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc
      have hZ : Subgroup.center X = ⊥ := by
        rw [← Subgroup.map_center_eq e.symm, hP.2, Subgroup.map_bot]
      refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hP.1, ?_⟩
      intro z hz _
      rw [hZ] at hz
      exact Subgroup.mem_bot.mp hz

theorem eq_or_mem_pCoreOf_of_normal {H K : Subgroup G} {q : ℕ}
    (hX : IsSzU3Quot (oTwoQuot ↥H) q) (hKH : K ≤ H)
    (hK : H ≤ Subgroup.normalizer (K : Set G)) (hQK : pCoreOf 2 H ≤ K) :
    K = H ∨ ∀ k ∈ K, (∃ n : ℕ, k ^ (2 ^ n) = 1) → k ∈ pCoreOf 2 H := by
  classical
  obtain ⟨hQ, hZinv⟩ := IsSzU3Quot.facts hX
  let Kq : Subgroup (oTwoQuot ↥H) :=
    (K.subgroupOf H).map (QuotientGroup.mk' (pCore 2 ↥H))
  have hKnorm : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hK
  have hKqnorm : Kq.Normal :=
    Subgroup.Normal.map hKnorm _ (QuotientGroup.mk'_surjective _)
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hQ hKqnorm with htop | hcen
  · left
    refine le_antisymm hKH ?_
    intro x hx
    have hmem : QuotientGroup.mk' (pCore 2 ↥H) (⟨x, hx⟩ : ↥H) ∈ Kq := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hmem
    have hyK : (y : G) ∈ K := Subgroup.mem_subgroupOf.mp hy
    have hdiff : (y : G)⁻¹ * x ∈ pCoreOf 2 H := by
      have h1 : (y⁻¹ * (⟨x, hx⟩ : ↥H) : ↥H) ∈ pCore 2 ↥H := by
        have hq : (QuotientGroup.mk' (pCore 2 ↥H)) (y⁻¹ * (⟨x, hx⟩ : ↥H)) = 1 := by
          rw [map_mul, map_inv, hyx, inv_mul_cancel]
        exact (QuotientGroup.eq_one_iff (N := pCore 2 ↥H)
          (x := y⁻¹ * (⟨x, hx⟩ : ↥H))).mp hq
      exact (CFSG.mem_openPCoreOf_iff (y⁻¹ * (⟨x, hx⟩ : ↥H))).mpr h1
    have hxeq : x = (y : G) * ((y : G)⁻¹ * x) := by group
    rw [hxeq]
    exact K.mul_mem hyK (hQK hdiff)
  · right
    intro k hk hkpow
    obtain ⟨n, hn⟩ := hkpow
    have hkH : k ∈ H := hKH hk
    let z : oTwoQuot ↥H := QuotientGroup.mk' (pCore 2 ↥H) (⟨k, hkH⟩ : ↥H)
    have hzKq : z ∈ Kq :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hk)
    have hzcenter : z ∈ Subgroup.center (oTwoQuot ↥H) := hcen hzKq
    have hzpow : z ^ (2 ^ n) = 1 := by
      change (QuotientGroup.mk (⟨k, hkH⟩ : ↥H) : oTwoQuot ↥H) ^ (2 ^ n) = 1
      rw [← QuotientGroup.mk_pow]
      have h1 : (⟨k, hkH⟩ : ↥H) ^ (2 ^ n) = 1 := by
        ext
        simpa using hn
      rw [h1, QuotientGroup.mk_one]
    have hdvd : orderOf z ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hzpow
    obtain ⟨j, -, horder⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    have hodd : Odd (Nat.card (Subgroup.center (oTwoQuot ↥H))) :=
      CFSG.ClassicalInvolution.Asc77.S28B.odd_card_center_of_no_involution hZinv
    have hz1 : z = 1 :=
      CFSG.GH74.Generic.S3.eq_one_of_odd_center_of_two_power hodd hzcenter horder
    have hkR : (⟨k, hkH⟩ : ↥H) ∈ pCore 2 ↥H := by
      rw [← QuotientGroup.eq_one_iff]
      exact hz1
    exact (CFSG.mem_openPCoreOf_iff (⟨k, hkH⟩ : ↥H)).mpr hkR

theorem eq_of_forall_pow_mem {H K : Subgroup G} {q : ℕ}
    (hX : IsSzU3Quot (oTwoQuot ↥H) q) (hKH : K ≤ H)
    (hK : H ≤ Subgroup.normalizer (K : Set G)) (hQK : pCoreOf 2 H ≤ K)
    (h2 : ∀ h ∈ H, ∃ n : ℕ, h ^ (2 ^ n) ∈ K) : K = H := by
  classical
  obtain ⟨hQ, -⟩ := IsSzU3Quot.facts hX
  haveI : Group.IsPerfect (oTwoQuot ↥H) := hQ.1
  let Kq : Subgroup (oTwoQuot ↥H) :=
    (K.subgroupOf H).map (QuotientGroup.mk' (pCore 2 ↥H))
  have hKnorm : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hK
  haveI : Kq.Normal :=
    Subgroup.Normal.map hKnorm _ (QuotientGroup.mk'_surjective _)
  have hKqtop : Kq = ⊤ := by
    refine CFSG.Quasithin.MS93.S36.eq_top_of_perfect_of_pow_mem Kq ?_
    intro z
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective z
    obtain ⟨n, hn⟩ := h2 h h.2
    refine ⟨n, ?_⟩
    change (QuotientGroup.mk h : oTwoQuot ↥H) ^ (2 ^ n) ∈ Kq
    rw [← QuotientGroup.mk_pow]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hn)
  refine le_antisymm hKH ?_
  intro x hx
  have hmem : QuotientGroup.mk' (pCore 2 ↥H) (⟨x, hx⟩ : ↥H) ∈ Kq := by
    rw [hKqtop]
    exact Subgroup.mem_top _
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hmem
  have hyK : (y : G) ∈ K := Subgroup.mem_subgroupOf.mp hy
  have hdiff : (y : G)⁻¹ * x ∈ pCoreOf 2 H := by
    have h1 : (y⁻¹ * (⟨x, hx⟩ : ↥H) : ↥H) ∈ pCore 2 ↥H := by
      have hq : (QuotientGroup.mk' (pCore 2 ↥H)) (y⁻¹ * (⟨x, hx⟩ : ↥H)) = 1 := by
        rw [map_mul, map_inv, hyx, inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff (N := pCore 2 ↥H)
        (x := y⁻¹ * (⟨x, hx⟩ : ↥H))).mp hq
    exact (CFSG.mem_openPCoreOf_iff (y⁻¹ * (⟨x, hx⟩ : ↥H))).mpr h1
  have hxeq : x = (y : G) * ((y : G)⁻¹ * x) := by group
  rw [hxeq]
  exact K.mul_mem hyK (hQK hdiff)

theorem exists_X0 {L T : Subgroup G} {q : ℕ}
    (hX : IsSzU3Quot (oTwoQuot ↥L) q) (hT : IsSylowTwoOf T L) :
    ∃ X₀ : Subgroup G, (∀ t, t ∈ X₀ ↔ t ∈ T ∧ t ^ 2 ∈ pCoreOf 2 L) ∧
      pCoreOf 2 L ≤ X₀ ∧ (pCoreOf 2 L).relIndex X₀ = q ∧ (∀ t ∈ T, t * t = 1 → t ∈ X₀) := by
  rcases hX with ⟨a, ha, hq, ⟨e⟩⟩ | ⟨n, hn, hq, F, hFld, hFin, hF, he⟩
  · obtain ⟨X₀, hmem, hle, hrel, -, hinv, -⟩ := exists_X0_sz ha e hT
    exact ⟨X₀, hmem, hle, hrel.trans hq.symm, hinv⟩
  · letI : Field F := hFld
    letI : Finite F := hFin
    rcases he with he | he
    · obtain ⟨e⟩ := he
      obtain ⟨X₀, hmem, hle, hrel, -, hinv, -⟩ := exists_X0_su hn hF e hT
      exact ⟨X₀, hmem, hle, hrel.trans hq.symm, hinv⟩
    · obtain ⟨e⟩ := he
      obtain ⟨X₀, hmem, hle, hrel, -, hinv, -⟩ := exists_X0_psu hn hF e hT
      exact ⟨X₀, hmem, hle, hrel.trans hq.symm, hinv⟩

theorem relIndex_inf_pCoreOf_le {L T A : Subgroup G} {q : ℕ}
    (hX : IsSzU3Quot (oTwoQuot ↥L) q) (hT : IsSylowTwoOf T L) (hAT : A ≤ T)
    (hA : ∀ a ∈ A, a ^ 2 ∈ pCoreOf 2 L) : (A ⊓ pCoreOf 2 L).relIndex A ≤ q := by
  obtain ⟨X₀, hmem, hRle, hrel, -⟩ := exists_X0 hX hT
  have hAX₀ : A ≤ X₀ := by
    intro a ha
    rw [hmem a]
    exact ⟨hAT ha, hA a ha⟩
  rw [Subgroup.inf_relIndex_left]
  calc (pCoreOf 2 L).relIndex A ≤ (pCoreOf 2 L).relIndex X₀ :=
        Subgroup.relIndex_le_of_le_right hAX₀ Subgroup.index_ne_zero_of_finite
    _ = q := hrel

end CFSG.Quasithin.Stroth
