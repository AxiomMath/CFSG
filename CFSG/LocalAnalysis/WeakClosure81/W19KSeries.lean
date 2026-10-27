module

public import CFSG.Quasithin.Background.E1Sec6

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_pow_mem_of_mem_sup_pGroup {p : ℕ} {R L : Subgroup G} (hR : IsPGroup p R)
    (hRL : R ≤ normalizer (L : Set G)) {u : G} (hu : u ∈ R ⊔ L) :
    ∃ e : ℕ, u ^ p ^ e ∈ L := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right R L hRL] at hu
  obtain ⟨v, hv, c, hc, rfl⟩ := hu
  obtain ⟨e, he⟩ := hR ⟨v, hv⟩
  have hve : v ^ p ^ e = 1 := by simpa using congrArg Subtype.val he
  obtain ⟨c', hc', hn⟩ := E1.mul_pow_eq_of_mem_normalizer (O := L) (hRL hv) hc (p ^ e)
  exact ⟨e, by rw [hn, hve, one_mul]; exact hc'⟩

theorem isSylowIn_two_of_pow_mem {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {O N : Subgroup G}
    (hO : IsPGroup 2 O) (hON : O ≤ N) (hNO : N ≤ normalizer (O : Set G))
    (hpow : ∀ x ∈ N, ∃ k : ℕ, x ^ p ^ k ∈ O) : IsSylowIn 2 O N := by
  refine ⟨hON, hO, fun hdvd => ?_⟩
  haveI : (O.subgroupOf N).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hNO
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd' : 2 ∣ Nat.card (↥N ⧸ O.subgroupOf N) := hdvd
  obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' (G := ↥N ⧸ O.subgroupOf N) 2 hdvd'
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective q
  have h2 : ((n : ↥N) : ↥N ⧸ O.subgroupOf N) ^ 2 = 1 := by
    rw [← hq]
    exact pow_orderOf_eq_one _
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h2
  obtain ⟨k, hk⟩ := hpow (n : G) n.2
  have hn : (n : G) ∈ O := E1.mem_of_pow_mem_two_p (j := 1) hp hp2 hk (by simpa using h2)
  have h1 : ((n : ↥N) : ↥N ⧸ O.subgroupOf N) = 1 :=
    (QuotientGroup.eq_one_iff n).2 (by rwa [Subgroup.mem_subgroupOf])
  rw [h1, orderOf_one] at hq
  exact absurd hq (by norm_num)

theorem eOneAmb_sup_mod {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {O P₀ τ A : Subgroup G}
    (hO : IsPGroup 2 O) (hOP : O ≤ P₀) (hPO : P₀ ≤ normalizer (O : Set G))
    (hτO : τ ≤ normalizer (O : Set G)) (hpow : ∀ x ∈ P₀, ∃ k : ℕ, x ^ p ^ k ∈ O)
    (hτ : IsPGroup 2 τ) (hτP : τ ≤ normalizer (P₀ : Set G)) (hne : ¬ P₀ ≤ O) (hAτ : A ≤ τ)
    (hcomm : P₀ ≤ ⁅P₀, A⁆ ⊔ O) (hrel : O.relIndex A = 2) :
    E1.EOneAmb (P₀ ⊔ τ) A := by
  set S := P₀ ⊔ τ with hS
  set N := pCoreOf 2 S with hN
  have hPS : P₀ ≤ S := le_sup_left
  have hSP : S ≤ normalizer (P₀ : Set G) := sup_le Subgroup.le_normalizer hτP
  have hSO : S ≤ normalizer (O : Set G) := sup_le hPO hτO
  have hN2 : IsPGroup 2 N := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 S
  have hNS : N ≤ S := CFSG.LieType.BorelTits.pCoreOf_le 2 S
  have hSN : S ≤ normalizer (N : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 S
  have hON : O ≤ N :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hOP.trans hPS) hSO hO
  have hP₀N : ¬ P₀ ≤ N := by
    intro hPN
    apply hne
    intro x hx
    obtain ⟨k, hk⟩ := hpow x hx
    obtain ⟨j, hj⟩ := hN2 ⟨x, hPN hx⟩
    refine E1.mem_of_pow_mem_two_p (j := j) hp hp2 hk ?_
    have : x ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    rw [this]
    exact O.one_mem
  have hAN : ¬ A ≤ N := by
    intro hAN
    apply hP₀N
    refine hcomm.trans (sup_le ?_ hON)
    refine Subgroup.commutator_le.mpr fun x hx a ha => ?_
    have h1 : x * a * x⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hSN (hPS hx)) a).mp (hAN ha)
    have e : ⁅x, a⁆ = (x * a * x⁻¹) * a⁻¹ := commutatorElement_def x a
    rw [e]
    exact N.mul_mem h1 (N.inv_mem (hAN ha))
  have hrel' : N.relIndex A = 2 := by
    have h1 : N.relIndex A ∣ O.relIndex A := Subgroup.relIndex_dvd_of_le_left A hON
    rw [hrel] at h1
    have hle : N.relIndex A ≤ 2 := Nat.le_of_dvd (by norm_num) h1
    have hne1 : N.relIndex A ≠ 1 := fun h => hAN (Subgroup.relIndex_eq_one.mp h)
    have hne0 : N.relIndex A ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  refine ⟨p, hp, hp2, P₀ ⊔ N, sup_le hPS hNS, ?_, le_sup_right, ?_, ?_, ?_, ?_, hrel'⟩
  · intro s hs
    exact E1.mem_normalizer_sup (hSP hs) (hSN hs)
  · intro x hx
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left P₀ N (hNS.trans hSP)]
      at hx
    obtain ⟨v, hv, n, hn, rfl⟩ := hx
    obtain ⟨k, hk⟩ := hpow v hv
    obtain ⟨n', hn', hvn⟩ := E1.mul_pow_eq_of_mem_normalizer (O := N) (hSN (hPS hv)) hn (p ^ k)
    exact ⟨k, by rw [hvn]; exact N.mul_mem (hON hk) hn'⟩
  · intro s hs
    obtain ⟨j, hj⟩ := E1.exists_pow_mem_of_mem_sup hτ hτP hs
    exact ⟨j, Subgroup.mem_sup_left hj⟩
  · intro h
    apply hP₀N
    have h' : P₀ ⊔ N = N := h
    exact h' ▸ le_sup_left
  · exact sup_le (hcomm.trans (sup_le_sup (Subgroup.commutator_mono le_sup_left le_rfl) hON))
      le_sup_right

theorem comm_le_comm_comm_sup_of_pow_mem {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {N A O : Subgroup G} (hON : O ≤ N) (hNO : N ≤ normalizer (O : Set G))
    (hAO : A ≤ normalizer (O : Set G)) (hAN : A ≤ normalizer (N : Set G)) (hA : IsPGroup 2 A)
    (hpow : ∀ x ∈ N, ∃ k : ℕ, x ^ p ^ k ∈ O) :
    ⁅N, A⁆ ≤ ⁅⁅N, A⁆, A⁆ ⊔ O := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S : Subgroup G := N ⊔ A with hS
  have hNS : N ≤ S := le_sup_left
  have hAS : A ≤ S := le_sup_right
  have hOS : O ≤ S := hON.trans hNS
  have hSO : S ≤ normalizer (O : Set G) := sup_le hNO hAO
  haveI hOn : (O.subgroupOf S).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hSO
  set π : ↥S →* ↥S ⧸ O.subgroupOf S := QuotientGroup.mk' (O.subgroupOf S) with hπ
  have hker : π.ker = O.subgroupOf S := QuotientGroup.ker_mk' _
  set N' : Subgroup ↥S := N.subgroupOf S with hN'
  set A' : Subgroup ↥S := A.subgroupOf S with hA'
  have hA'N' : ∀ a ∈ A', ∀ n ∈ N', a * n * a⁻¹ ∈ N' := by
    intro a ha n hn
    rw [Subgroup.mem_subgroupOf] at ha hn ⊢
    have := (Subgroup.mem_normalizer_iff.1 (hAN ha) (n : G)).1 hn
    simpa using this
  have hA'p : IsPGroup 2 A' := hA.of_equiv (Subgroup.subgroupOfEquivOfLe hAS).symm
  have hN'p : IsPGroup p (N'.map π) := by
    intro y
    obtain ⟨n, hn, hny⟩ := y.2
    obtain ⟨k, hk⟩ := hpow (n : G) (Subgroup.mem_subgroupOf.1 hn)
    refine ⟨k, Subtype.ext ?_⟩
    show (y : ↥S ⧸ O.subgroupOf S) ^ p ^ k = 1
    rw [← hny, ← map_pow]
    exact (QuotientGroup.eq_one_iff _).2 (by rw [Subgroup.mem_subgroupOf]; simpa using hk)
  have hcop : Nat.Coprime 2 (Nat.card ↥(N'.map π)) := by
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 hN'p
    rw [hm]
    exact Nat.Coprime.pow_right m ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
  haveI : Group.IsNilpotent ↥(N'.map π) := hN'p.isNilpotent
  have hAbar : A'.map π ≤ normalizer ((N'.map π : Subgroup (↥S ⧸ O.subgroupOf S)) : Set _) := by
    rw [Subgroup.le_normalizer_iff]
    rintro _ ⟨a, ha, rfl⟩ _ ⟨n, hn, rfl⟩
    exact ⟨a * n * a⁻¹, hA'N' a ha n hn, by simp⟩
  have hcc := E1.comm_comm_eq hAbar (hA'p.map π) hcop inferInstance
  have hmap : (⁅N', A'⁆).map π = (⁅⁅N', A'⁆, A'⁆).map π := by
    simp only [Subgroup.map_commutator]
    exact hcc.symm
  have h1 : ⁅N', A'⁆ ≤ ⁅⁅N', A'⁆, A'⁆ ⊔ O.subgroupOf S := by
    intro x hx
    have hx' : π x ∈ (⁅⁅N', A'⁆, A'⁆).map π := hmap ▸ Subgroup.mem_map_of_mem π hx
    obtain ⟨y, hy, hyx⟩ := hx'
    have h3 : x * y⁻¹ ∈ O.subgroupOf S := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hyx, mul_inv_cancel]
    have e : x = (x * y⁻¹) * y := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right h3) (Subgroup.mem_sup_left hy)
  have hN'm : N'.map S.subtype = N := Subgroup.map_subgroupOf_eq_of_le hNS
  have hA'm : A'.map S.subtype = A := Subgroup.map_subgroupOf_eq_of_le hAS
  have hO'm : (O.subgroupOf S).map S.subtype = O := Subgroup.map_subgroupOf_eq_of_le hOS
  have e1 : (⁅N', A'⁆).map S.subtype = ⁅N, A⁆ := by
    rw [Subgroup.map_commutator, hN'm, hA'm]
  have e2 : (⁅⁅N', A'⁆, A'⁆).map S.subtype = ⁅⁅N, A⁆, A⁆ := by
    rw [Subgroup.map_commutator, e1, hA'm]
  have h2 := Subgroup.map_mono (f := S.subtype) h1
  rwa [Subgroup.map_sup, e1, e2, hO'm] at h2

end CFSG.LocalAnalysis.WeakClosure81

end
