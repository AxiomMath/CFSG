module

public import CFSG.Quasithin.Vol2.Ch11SecBFactsHB

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

theorem mem_normalizer_subgroupOf {Γ : Type*} [Group Γ] {K S : Subgroup Γ} {g : ↥K}
    (h : (g : Γ) ∈ Subgroup.normalizer (S : Set Γ)) :
    g ∈ Subgroup.normalizer ((S.subgroupOf K : Subgroup ↥K) : Set ↥K) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  simpa using Subgroup.mem_normalizer_iff.mp h (y : Γ)

variable {G : Type} [Group G] [Finite G]

theorem inf_pCoreOf_le_pCoreOf {K H : Subgroup G} (hKH : K ≤ H) :
    K ⊓ pCoreOf 2 H ≤ pCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le inf_le_right)
  intro k hk
  exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hk,
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (hKH hk)⟩

theorem isPGroup_commutator_inf_of_isBorelIn (hFB : FactBorelComm) {H X K : Subgroup G}
    (hKH : K ≤ H) (hKperf : ⁅K, K⁆ = K) (hOK : pCoreOf 2 K ≤ kerIn X H)
    (hcent : ∀ k ∈ K, k ∈ kerIn X H → ∀ y ∈ K, k * y * k⁻¹ * y⁻¹ ∈ pCoreOf 2 K)
    {n : ℕ} (hn : 2 ≤ n)
    (htype : E2.IsBenderOf n ↥(E2.star X H K) ∨ IsPSL 3 2 n ↥(E2.star X H K) ∨
      IsPSp4 2 n ↥(E2.star X H K))
    (hB : E2.IsBorelIn (E2.star X H K) (E2.star X H (X ⊓ K))) :
    IsPGroup 2 ↥⁅X ⊓ K, X ⊓ K⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set J := kerIn X H with hJdef
  set Ks := E2.star X H K with hKsdef
  set π : ↥H →* E2.StarQuot X H := QuotientGroup.mk' (J.subgroupOf H) with hπdef
  have hmem : ∀ k : ↥K, π (Subgroup.inclusion hKH k) ∈ Ks := fun k =>
    ⟨Subgroup.inclusion hKH k, Subgroup.mem_subgroupOf.mpr k.2, rfl⟩
  set ψ : ↥K →* ↥Ks := (π.comp (Subgroup.inclusion hKH)).codRestrict Ks hmem with hψdef
  have hψs : Function.Surjective ψ := by
    rintro ⟨_, h, hh, rfl⟩
    exact ⟨⟨h, Subgroup.mem_subgroupOf.mp hh⟩, Subtype.ext rfl⟩
  have hON : (CFSG.Open.pCore 2 ↥K).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hmemO : ∀ x : ↥K, (x : G) ∈ pCoreOf 2 K → x ∈ CFSG.Open.pCore 2 ↥K := by
    rintro x ⟨x', hx', hxx'⟩
    rwa [show x = x' from Subtype.ext hxx'.symm]
  have hOKψ : CFSG.Open.pCore 2 ↥K ≤ ψ.ker := by
    intro k hk
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    show π (Subgroup.inclusion hKH k) = 1
    rw [hπdef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hOK ⟨k, hk, rfl⟩
  set φ : ↥K ⧸ CFSG.Open.pCore 2 ↥K →* ↥Ks := QuotientGroup.lift _ ψ hOKψ with hφdef
  have hφk : ∀ k : ↥K, φ (k : ↥K ⧸ CFSG.Open.pCore 2 ↥K) = ψ k := fun k => rfl
  have hφs : Function.Surjective φ := by
    intro y
    obtain ⟨k, rfl⟩ := hψs y
    exact ⟨k, hφk k⟩
  have hperf : commutator (↥K ⧸ CFSG.Open.pCore 2 ↥K) = ⊤ := by
    have hXp : commutator ↥K = ⊤ := Group.isPerfect_def.1 (Subgroup.isPerfect_iff.2 hKperf)
    have hsurj := QuotientGroup.mk'_surjective (CFSG.Open.pCore 2 ↥K)
    rw [commutator_def, ← Subgroup.map_top_of_surjective _ hsurj, ← Subgroup.map_commutator,
      ← commutator_def, hXp]
  have hcentker : φ.ker ≤ Subgroup.center (↥K ⧸ CFSG.Open.pCore 2 ↥K) := by
    intro z hz
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective z
    have hkJ : (k : G) ∈ J := by
      have h1 : ψ k = 1 := by rw [← hφk]; exact hz
      have h2 := congrArg Subtype.val h1
      change π (Subgroup.inclusion hKH k) = 1 at h2
      rw [hπdef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h2
      exact h2
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective w
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    apply hmemO
    have := hcent _ (K.inv_mem k.2) (J.inv_mem hkJ) _ (K.inv_mem y.2)
    simpa [mul_assoc] using this
  have hodd : Odd (Nat.card φ.ker) := by
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥φ.ker) 2 (even_iff_two_dvd.mp hev)
    obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective (z : ↥K ⧸ CFSG.Open.pCore 2 ↥K)
    have hzo : orderOf (z : ↥K ⧸ CFSG.Open.pCore 2 ↥K) = 2 := by
      rw [Subgroup.orderOf_coe]
      exact hz
    have hzc := hcentker z.2
    set P := (Subgroup.zpowers (z : ↥K ⧸ CFSG.Open.pCore 2 ↥K)).comap
      (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥K)) with hPdef
    have hPn : P.Normal := by
      refine Subgroup.Normal.comap ⟨fun a ha g => ?_⟩ _
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      have hc : g * (z : ↥K ⧸ CFSG.Open.pCore 2 ↥K) ^ m * g⁻¹ =
          (z : ↥K ⧸ CFSG.Open.pCore 2 ↥K) ^ m := by
        rw [Subgroup.mem_center_iff.mp (Subgroup.zpow_mem _ hzc m) g, mul_inv_cancel_right]
      rw [hc]
      exact Subgroup.zpow_mem_zpowers _ m
    have hPp : IsPGroup 2 P := by
      refine IsPGroup.comap_of_ker_isPGroup ?_ _ ?_
      · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzo, pow_one])
      · rw [QuotientGroup.ker_mk']
        exact CFSG.LieType.BorelTits.pCore_isPGroup 2
    have hkP : k ∈ P := by
      rw [hPdef, Subgroup.mem_comap, QuotientGroup.mk'_apply, hk]
      exact Subgroup.mem_zpowers _
    have hkO : k ∈ CFSG.Open.pCore 2 ↥K := CFSG.LieType.BorelTits.le_pCore 2 hPn hPp hkP
    have h1 : (z : ↥K ⧸ CFSG.Open.pCore 2 ↥K) = 1 := by
      rw [← hk, QuotientGroup.eq_one_iff]
      exact hkO
    rw [h1, orderOf_one] at hzo
    exact absurd hzo (by norm_num)
  obtain ⟨S, hS, hMK⟩ := hB
  set S' : Subgroup ↥Ks := S.subgroupOf Ks with hS'def
  have hS' : IsSylowTwoOf S' ⊤ := by
    refine ⟨le_top, hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm, ?_⟩
    show ¬ 2 ∣ S'.relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact hS.2.2
  have hW := hFB (↥K ⧸ CFSG.Open.pCore 2 ↥K) ↥Ks n φ hn hφs hperf hcentker hodd htype S' hS'
  set ρ := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥K) with hρdef
  set A := (X ⊓ K).subgroupOf K with hAdef
  have hAW : A.map ρ ≤ (Subgroup.normalizer (S' : Set ↥Ks)).comap φ := by
    rintro _ ⟨a, ha, rfl⟩
    show φ (a : ↥K ⧸ CFSG.Open.pCore 2 ↥K) ∈ Subgroup.normalizer (S' : Set ↥Ks)
    rw [hφk]
    apply mem_normalizer_subgroupOf
    have h2 : ((ψ a : ↥Ks) : E2.StarQuot X H) ∈ E2.star X H (X ⊓ K) :=
      ⟨Subgroup.inclusion hKH a, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp ha),
        rfl⟩
    rw [hMK] at h2
    exact h2.2
  have hcomm : IsPGroup 2 ↥(⁅A, A⁆.map ρ) := by
    rw [Subgroup.map_commutator]
    exact hW.to_le (Subgroup.commutator_mono hAW hAW)
  have hA : IsPGroup 2 ↥⁅A, A⁆ := by
    have h1 := hcomm.comap_of_ker_isPGroup ρ (by
      rw [hρdef, QuotientGroup.ker_mk']
      exact CFSG.LieType.BorelTits.pCore_isPGroup 2)
    exact h1.to_le (Subgroup.le_comap_map ρ _)
  have heq : ⁅X ⊓ K, X ⊓ K⁆ = ⁅A, A⁆.map K.subtype := by
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le inf_le_right]
  rw [heq]
  exact hA.map K.subtype

end CFSG.Quasithin.Vol2.Ch11.SecB
