module

public import CFSG.Quasithin.H13.L32AHStr

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_of_odd_of_mem_mul {K N : Subgroup G} (hNK : N ≤ K)
    (hn : K ≤ Subgroup.normalizer (N : Set G)) {x n q : G} (hxK : x ∈ K) (hqK : q ∈ K)
    (hnN : n ∈ N) (hxnq : x = n * q) (hx : Odd (orderOf x)) {a : ℕ} (hq : q ^ 2 ^ a = 1) :
    x ∈ N := by
  have : (N.subgroupOf K).Normal := ⟨fun y hy k => by
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hn k.2) y).mp hy⟩
  have hnK : n ∈ K := hNK hnN
  have h1 : (QuotientGroup.mk (⟨x, hxK⟩ : ↥K) : ↥K ⧸ N.subgroupOf K) =
      QuotientGroup.mk (⟨q, hqK⟩ : ↥K) := by
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have e : (((⟨x, hxK⟩ : ↥K)⁻¹ * ⟨q, hqK⟩ : ↥K) : G) = q⁻¹ * n⁻¹ * q := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hxnq]
      group
    rw [e]
    have := (Subgroup.mem_normalizer_iff.mp (hn (inv_mem hqK)) _).mp (inv_mem hnN)
    simpa using this
  have h2 : orderOf (QuotientGroup.mk (⟨x, hxK⟩ : ↥K) : ↥K ⧸ N.subgroupOf K) ∣ orderOf x := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← QuotientGroup.mk_pow]
    have : (⟨x, hxK⟩ : ↥K) ^ orderOf x = 1 := Subtype.ext (by simp [pow_orderOf_eq_one])
    rw [this, QuotientGroup.mk_one]
  have h3 : orderOf (QuotientGroup.mk (⟨x, hxK⟩ : ↥K) : ↥K ⧸ N.subgroupOf K) ∣ 2 ^ a := by
    apply orderOf_dvd_of_pow_eq_one
    rw [h1, ← QuotientGroup.mk_pow]
    have : (⟨q, hqK⟩ : ↥K) ^ 2 ^ a = 1 := Subtype.ext (by simpa using hq)
    rw [this, QuotientGroup.mk_one]
  have hcop : Nat.Coprime (orderOf x) (2 ^ a) :=
    Nat.Coprime.pow_right a (Nat.coprime_two_right.mpr hx)
  have h4 := Nat.eq_one_of_dvd_coprimes hcop h2 h3
  have h5 := orderOf_eq_one_iff.mp h4
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h5
  exact h5

section Phi

variable {H : Subgroup G} {φ : ↥H →* Equiv.Perm (Fin 5)}
variable (hs : Function.Surjective φ) (hk : φ.ker = CFSG.Open.pCore 2 ↥H)
include hs hk

omit hs in
theorem eq_oTwoUpper_of {N : Subgroup G} (hNK : N ≤ oTwoUpper H)
    (hO : oTwoUpper H ⊓ pCoreOf 2 H ≤ Subgroup.normalizer (N : Set G))
    (hφ : alternatingGroup (Fin 5) ≤ (N.subgroupOf H).map φ) : N = oTwoUpper H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hdec : ∀ x ∈ oTwoUpper H, ∃ n ∈ N, ∃ q ∈ oTwoUpper H ⊓ pCoreOf 2 H, x = n * q := by
    intro x hx
    have hxA : φ ⟨x, hKH hx⟩ ∈ (N.subgroupOf H).map φ := by
      apply hφ
      rw [Equiv.Perm.mem_alternatingGroup]
      exact sign_phi_kz hx
    obtain ⟨n, hnN, hnx⟩ := hxA
    have hq : n⁻¹ * ⟨x, hKH hx⟩ ∈ CFSG.Open.pCore 2 ↥H := by
      rw [← hk, MonoidHom.mem_ker, map_mul, map_inv, hnx, inv_mul_cancel]
    have hnN' : (n : G) ∈ N := Subgroup.mem_subgroupOf.mp hnN
    refine ⟨n, hnN', (n : G)⁻¹ * x, Subgroup.mem_inf.mpr
      ⟨mul_mem (inv_mem (hNK hnN')) hx, ?_⟩, by group⟩
    have := mem_pCoreOf_iff'.mpr hq
    simpa using this
  have hn : oTwoUpper H ≤ Subgroup.normalizer (N : Set G) := by
    intro x hx
    obtain ⟨n, hnN, q, hq, rfl⟩ := hdec x hx
    exact mul_mem (Subgroup.le_normalizer hnN) (hO hq)
  refine le_antisymm hNK ((Subgroup.closure_le N).mpr fun x hx => ?_)
  obtain ⟨hxH, hxo⟩ := hx
  have hxK : x ∈ oTwoUpper H := mem_oTwoUpper_of_odd hxH hxo
  obtain ⟨n, hnN, q, hq, hxnq⟩ := hdec x hxK
  obtain ⟨a, ha⟩ := (pCoreOf_isPGroup 2 H) ⟨q, (Subgroup.mem_inf.mp hq).2⟩
  exact mem_of_odd_of_mem_mul hNK hn hxK (Subgroup.mem_inf.mp hq).1 hnN hxnq hxo
    (by simpa using congrArg Subtype.val ha)

theorem eq_oTwoUpper_of_normal {N : Subgroup G} (hNK : N ≤ oTwoUpper H)
    (hn : oTwoUpper H ≤ Subgroup.normalizer (N : Set G)) (hNQ : ¬ N ≤ pCoreOf 2 H) :
    N = oTwoUpper H := by
  have hKH : oTwoUpper H ≤ H := oTwoUpper_le H
  refine eq_oTwoUpper_of hk hNK (inf_le_left.trans hn) ?_
  set M := (N.subgroupOf H).map φ with hM
  have hMA : M ≤ alternatingGroup (Fin 5) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Equiv.Perm.mem_alternatingGroup]
    exact sign_phi_kz (hNK (Subgroup.mem_subgroupOf.mp hx))
  have hMn : (M.subgroupOf (alternatingGroup (Fin 5))).Normal := ⟨fun y hy g => by
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have hg : (g : Equiv.Perm (Fin 5)) ∈ ((oTwoUpper H).subgroupOf H).map φ := by
      rw [phi_map_kz hs hk]
      exact g.2
    obtain ⟨k, hkK, hkg⟩ := hg
    obtain ⟨x, hxN, hxy⟩ := hy
    refine ⟨k * x * k⁻¹, Subgroup.mem_subgroupOf.mpr ?_,
      by rw [map_mul, map_mul, map_inv, hkg, hxy]⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hn (Subgroup.mem_subgroupOf.mp hkK)) _).mp
      (Subgroup.mem_subgroupOf.mp hxN)⟩
  have hsimp : IsSimpleGroup ↥(alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup (by simp)
  rcases hMn.eq_bot_or_eq_top with hb | ht
  · exfalso
    apply hNQ
    intro x hxN
    have hxH := hKH (hNK hxN)
    have h1 : (⟨φ ⟨x, hxH⟩, hMA ⟨⟨x, hxH⟩, Subgroup.mem_subgroupOf.mpr hxN, rfl⟩⟩ :
        ↥(alternatingGroup (Fin 5))) ∈ M.subgroupOf (alternatingGroup (Fin 5)) :=
      Subgroup.mem_subgroupOf.mpr ⟨⟨x, hxH⟩, Subgroup.mem_subgroupOf.mpr hxN, rfl⟩
    rw [hb, Subgroup.mem_bot] at h1
    have h2 : φ ⟨x, hxH⟩ = 1 := congrArg Subtype.val h1
    have h3 : (⟨x, hxH⟩ : ↥H) ∈ CFSG.Open.pCore 2 ↥H := by
      rw [← hk, MonoidHom.mem_ker]
      exact h2
    exact mem_pCoreOf_iff'.mpr h3
  · intro σ hσ
    have : (⟨σ, hσ⟩ : ↥(alternatingGroup (Fin 5))) ∈ M.subgroupOf (alternatingGroup (Fin 5)) := by
      rw [ht]
      exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this

end Phi

theorem pCoreOf_oTwoUpper_eq (H : Subgroup G) :
    pCoreOf 2 (oTwoUpper H) = oTwoUpper H ⊓ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm (le_inf (pCoreOf_le 2 _) ?_) ?_
  · exact le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans (oTwoUpper_le H))
      ((le_normalizer_oTwoUpper H).trans (normalizer_le_normalizer_pCoreOf 2 _))
      (pCoreOf_isPGroup 2 _)
  · exact le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun k hk => Subgroup.mem_normalizer_iff.mpr fun x => by
        constructor
        · intro hx
          exact Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hk (Subgroup.mem_inf.mp hx).1)
            (inv_mem hk), (Subgroup.mem_normalizer_iff.mp
              (le_normalizer_pCoreOf 2 H (oTwoUpper_le H hk)) x).mp (Subgroup.mem_inf.mp hx).2⟩
        · intro hx
          have h := Subgroup.mem_inf.mp hx
          refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
          · have := mul_mem (mul_mem (inv_mem hk) h.1) hk
            simpa [mul_assoc] using this
          · have := (Subgroup.mem_normalizer_iff.mp
              (le_normalizer_pCoreOf 2 H (oTwoUpper_le H (inv_mem hk))) _).mp h.2
            simpa [mul_assoc] using this)
      ((pCoreOf_isPGroup 2 H).to_le inf_le_right)

end CFSG.Quasithin.H13.L32A
