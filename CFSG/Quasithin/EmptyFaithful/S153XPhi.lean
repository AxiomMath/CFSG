module

public import CFSG.Quasithin.Background.C2Defs
public import CFSG.Quasithin.Background.A4V
public import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

private theorem exists_odd_orderOf_pow_two_pow {K : Type*} [Group K] [Finite K] (y : K) :
    ∃ k : ℕ, Odd (orderOf (y ^ 2 ^ k)) := by
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
  refine ⟨k, ?_⟩
  have h2k : (2 ^ k : ℕ) ≠ 0 := by positivity
  rw [orderOf_pow' _ h2k, hkm, Nat.gcd_mul_right_left, Nat.mul_div_cancel_left _ (by positivity)]
  exact hm

private theorem pCore_two_quotient_pCore_two_eq_bot {H : Type*} [Group H] :
    CFSG.pCore 2 (H ⧸ CFSG.pCore 2 H) = ⊥ := by
  set N : Subgroup H := CFSG.pCore 2 H with hN
  set M : Subgroup H := (CFSG.pCore 2 (H ⧸ N)).comap (QuotientGroup.mk' N) with hM
  have hMp : IsPGroup 2 M := by
    rintro ⟨k, hk⟩
    obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup (G := H ⧸ N) (p := 2)) ⟨_, hk⟩
    have h1 : k ^ 2 ^ a ∈ N := by
      have := congrArg Subtype.val ha
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at this
      rwa [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    obtain ⟨b, hb⟩ := (CFSG.pCore_isPGroup (G := H) (p := 2)) ⟨_, h1⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have := congrArg Subtype.val hb
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at this ⊢
    rw [pow_add, pow_mul]
    exact this
  have hMn : M.Normal := Subgroup.Normal.comap CFSG.pCore_normal _
  have hMN : M ≤ N := le_sSup ⟨hMn, hMp⟩
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective N y
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hMN hy

private theorem exists_odd_mem_inf_generalizedFitting {K : Type*} [Group K] [Finite K]
    (h2 : CFSG.pCore 2 K = ⊥) {N : Subgroup K} [N.Normal] (hN : N ≠ ⊥) :
    ∃ x ∈ N ⊓ CFSG.generalizedFitting K, x ≠ 1 ∧ Odd (orderOf x) := by
  by_contra hcon
  push Not at hcon
  have hFn : (CFSG.generalizedFitting K).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := K)).2
  have hD2 : IsPGroup 2 (N ⊓ CFSG.generalizedFitting K : Subgroup K) := by
    intro x
    obtain ⟨k, hk⟩ := exists_odd_orderOf_pow_two_pow (x : K)
    refine ⟨k, ?_⟩
    by_contra hne
    exact hcon _ ((N ⊓ CFSG.generalizedFitting K).pow_mem x.2 _)
      (fun h1 => hne (Subtype.ext h1)) hk
  have hDbot : N ⊓ CFSG.generalizedFitting K = ⊥ := by
    have hle : N ⊓ CFSG.generalizedFitting K ≤ CFSG.pCore 2 K := le_sSup ⟨inferInstance, hD2⟩
    rwa [h2, le_bot_iff] at hle
  have hcomm : ⁅N, CFSG.generalizedFitting K⁆ = ⊥ :=
    le_bot_iff.mp (hDbot ▸ Subgroup.commutator_le_inf N (CFSG.generalizedFitting K))
  have hNF : N ≤ CFSG.generalizedFitting K :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm).trans
      (CFSG.centralizer_generalizedFitting_le K)
  apply hN
  rw [eq_bot_iff, ← hDbot]
  exact le_inf le_rfl hNF

private def pCoreCommSubgroup {G : Type*} [Group G] (H Z : Subgroup G)
    (hZn : H ≤ Subgroup.normalizer (Z : Set G)) : Subgroup ↥H where
  carrier := {g | ∀ q ∈ pCoreOf 2 H, (g : G) * q * (g : G)⁻¹ * q⁻¹ ∈ Z}
  one_mem' := fun q _ => by simp
  mul_mem' := by
    intro a b ha hb q hq
    have hZ' : ∀ z ∈ Z, (a : G) * z * (a : G)⁻¹ ∈ Z := fun z hz =>
      (Subgroup.mem_normalizer_iff.mp (hZn a.2) z).mp hz
    have e : ((a * b : ↥H) : G) * q * ((a * b : ↥H) : G)⁻¹ * q⁻¹ =
        (a : G) * ((b : G) * q * (b : G)⁻¹ * q⁻¹) * (a : G)⁻¹ *
          ((a : G) * q * (a : G)⁻¹ * q⁻¹) := by
      simp only [Subgroup.coe_mul]
      group
    rw [e]
    exact Z.mul_mem (hZ' _ (hb q hq)) (ha q hq)
  inv_mem' := by
    intro a ha q hq
    have hq' : (a : G)⁻¹ * q * (a : G) ∈ pCoreOf 2 H := by
      have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H (a⁻¹).2) q).mp hq
      simpa using this
    have e : ((a⁻¹ : ↥H) : G) * q * ((a⁻¹ : ↥H) : G)⁻¹ * q⁻¹ =
        ((a : G) * ((a : G)⁻¹ * q * (a : G)) * (a : G)⁻¹ * ((a : G)⁻¹ * q * (a : G))⁻¹)⁻¹ := by
      simp only [Subgroup.coe_inv]
      group
    rw [e]
    exact Z.inv_mem (ha _ hq')

private theorem mem_pCoreCommSubgroup {G : Type*} [Group G] {H Z : Subgroup G}
    {hZn : H ≤ Subgroup.normalizer (Z : Set G)} {g : ↥H} :
    g ∈ pCoreCommSubgroup H Z hZn ↔ ∀ q ∈ pCoreOf 2 H, (g : G) * q * (g : G)⁻¹ * q⁻¹ ∈ Z :=
  Iff.rfl

private theorem pCoreCommSubgroup_normal {G : Type*} [Group G] {H Z : Subgroup G}
    (hZn : H ≤ Subgroup.normalizer (Z : Set G)) : (pCoreCommSubgroup H Z hZn).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [mem_pCoreCommSubgroup] at hn ⊢
  intro q hq
  have hq' : (g : G)⁻¹ * q * (g : G) ∈ pCoreOf 2 H := by
    have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H (g⁻¹).2) q).mp hq
    simpa using this
  have e : ((g * n * g⁻¹ : ↥H) : G) * q * ((g * n * g⁻¹ : ↥H) : G)⁻¹ * q⁻¹ =
      (g : G) * ((n : G) * ((g : G)⁻¹ * q * (g : G)) * (n : G)⁻¹ *
        ((g : G)⁻¹ * q * (g : G))⁻¹) * (g : G)⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp (hZn g.2) _).mp (hn _ hq')

private theorem mem_pCoreOf_of_odd_commutator_mem {G : Type*} [Group G] {H Z : Subgroup G}
    (hH : CharTwo H) (hZ2 : ∀ z ∈ Z, z ^ 2 = 1) {g : G} (hgH : g ∈ H)
    (hodd : Odd (orderOf g)) (hgZ : g ∈ Subgroup.centralizer (Z : Set G))
    (hgq : ∀ q ∈ pCoreOf 2 H, g * q * g⁻¹ * q⁻¹ ∈ Z) : g ∈ pCoreOf 2 H := by
  have hsq : g ^ 2 ∈ Subgroup.centralizer (pCoreOf 2 H : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hcZ : g * q * g⁻¹ * q⁻¹ ∈ Z := hgq q hq
    have hcg : g * q * g⁻¹ * q⁻¹ * g = g * (g * q * g⁻¹ * q⁻¹) :=
      Subgroup.mem_centralizer_iff.mp hgZ _ hcZ
    have hc2 : (g * q * g⁻¹ * q⁻¹) * (g * q * g⁻¹ * q⁻¹) = 1 := by
      rw [← sq]
      exact hZ2 _ hcZ
    have h2 : g * (g * q * g⁻¹) * g⁻¹ = q := by
      calc g * (g * q * g⁻¹) * g⁻¹
          = (g * (g * q * g⁻¹ * q⁻¹) * g⁻¹) * (g * q * g⁻¹) := by group
        _ = (g * q * g⁻¹ * q⁻¹) * (g * q * g⁻¹) := by
          rw [← hcg]
          group
        _ = ((g * q * g⁻¹ * q⁻¹) * (g * q * g⁻¹ * q⁻¹)) * q := by group
        _ = q := by rw [hc2, one_mul]
    calc q * g ^ 2 = (g * (g * q * g⁻¹) * g⁻¹) * g ^ 2 := by rw [h2]
      _ = g ^ 2 * q := by
        rw [pow_two]
        group
  have hg : g ∈ Subgroup.centralizer (pCoreOf 2 H : Set G) := by
    obtain ⟨a, ha⟩ := hodd
    have h1 : g ^ (2 * a + 1) = 1 := by
      rw [← ha]
      exact pow_orderOf_eq_one g
    have h2 : g = (g ^ 2) ^ (a + 1) := by
      calc g = g ^ (2 * a + 1) * g := by rw [h1, one_mul]
        _ = (g ^ 2) ^ (a + 1) := by
          rw [← pow_succ, ← pow_mul]
          congr 1
    rw [h2]
    exact Subgroup.pow_mem _ hsq _
  exact hH ⟨hgH, hg⟩

private theorem coe_mem_pCoreOf_iff_mem_pCore {G : Type*} [Group G] {H : Subgroup G} (x : ↥H) :
    (x : G) ∈ pCoreOf 2 H ↔ x ∈ CFSG.pCore 2 ↥H := CFSG.mem_openPCoreOf_iff x

theorem centralizerMod_le_pCoreOf {G : Type} [Group G] [Finite G] {H Z : Subgroup G}
    (hH : CharTwo H) (hZn : H ≤ Subgroup.normalizer (Z : Set G))
    (_hZQ : Z ≤ centerOf (pCoreOf 2 H)) (hZ2 : ∀ z ∈ Z, z ^ 2 = 1)
    (hY : oTwoUpper (oTwoFstarIn H) ≤ Subgroup.centralizer (Z : Set G)) :
    ∀ g ∈ H, (∀ q ∈ pCoreOf 2 H, g * q * g⁻¹ * q⁻¹ ∈ Z) → g ∈ pCoreOf 2 H := by
  intro g hgH hgq
  by_contra hgQ
  have hNn : (pCoreCommSubgroup H Z hZn).Normal := pCoreCommSubgroup_normal hZn
  set N := pCoreCommSubgroup H Z hZn with hN
  set P : Subgroup ↥H := CFSG.pCore 2 ↥H with hP
  set π : ↥H →* ↥H ⧸ P := QuotientGroup.mk' P with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective P
  have hNbn : (N.map π).Normal := Subgroup.Normal.map hNn π hπs
  have hg0 : (⟨g, hgH⟩ : ↥H) ∈ N := hgq
  have hne : N.map π ≠ ⊥ := by
    intro hbot
    have h1 : π ⟨g, hgH⟩ ∈ N.map π := Subgroup.mem_map_of_mem π hg0
    rw [hbot, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact hgQ ((coe_mem_pCoreOf_iff_mem_pCore ⟨g, hgH⟩).mpr h1)
  obtain ⟨x, hx, hx1, hxodd⟩ :=
    exists_odd_mem_inf_generalizedFitting (pCore_two_quotient_pCore_two_eq_bot (H := ↥H)) hne
  obtain ⟨hxN, hxF⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨n, hnN, rfl⟩ := Subgroup.mem_map.mp hxN
  obtain ⟨k, hk⟩ := exists_odd_orderOf_pow_two_pow n
  have hn'N : n ^ 2 ^ k ∈ N := N.pow_mem hnN _
  have hn'F : π (n ^ 2 ^ k) ∈ CFSG.generalizedFitting (↥H ⧸ P) := by
    rw [map_pow]
    exact Subgroup.pow_mem _ hxF _
  have hn'Y : ((n ^ 2 ^ k : ↥H) : G) ∈ oTwoFstarIn H :=
    Subgroup.mem_map.mpr ⟨n ^ 2 ^ k, hn'F, rfl⟩
  have hn'odd : Odd (orderOf ((n ^ 2 ^ k : ↥H) : G)) := by
    rw [Subgroup.orderOf_coe]
    exact hk
  have hn'C := hY (mem_oTwoUpper_of_odd hn'Y hn'odd)
  have hn'Q : ((n ^ 2 ^ k : ↥H) : G) ∈ pCoreOf 2 H :=
    mem_pCoreOf_of_odd_commutator_mem hH hZ2 (n ^ 2 ^ k).2 hn'odd hn'C hn'N
  have h1 : π (n ^ 2 ^ k) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ((coe_mem_pCoreOf_iff_mem_pCore _).mp hn'Q)
  rw [map_pow] at h1
  have hord : orderOf (π n ^ 2 ^ k) = orderOf (π n) :=
    Nat.Coprime.orderOf_pow (Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hxodd))
  rw [h1, orderOf_one] at hord
  exact hx1 (orderOf_eq_one_iff.mp hord.symm)

theorem centralizerMod_le_pCoreOf_omegaOneCenter {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hH : CharTwo H)
    (hY : oTwoUpper (oTwoFstarIn H) ≤
      Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 H) : Set G)) :
    ∀ g ∈ H, (∀ q ∈ pCoreOf 2 H, g * q * g⁻¹ * q⁻¹ ∈ omegaOneCenterOf (pCoreOf 2 H)) →
      g ∈ pCoreOf 2 H :=
  centralizerMod_le_pCoreOf hH
    ((le_normalizer_pCoreOf 2 H).trans (A4.normalizer_le_normalizer_omegaOneCenterOf _))
    (A4.omegaOneCenterOf_le_centerOf _) (fun _ hz => A4.sq_eq_one_of_mem_omegaOneCenterOf hz) hY

end CFSG.Quasithin
