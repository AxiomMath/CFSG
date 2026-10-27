module

public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.Quasithin.H13.P31A

open scoped Pointwise

variable {G : Type*} [Group G]

theorem commutator_le_of_forall_comm {X N L T : Subgroup G}
    (hX : ∀ x ∈ X, ∀ y ∈ X, x * y * x⁻¹ * y⁻¹ ∈ N) (hL : L ≤ X) (hT : T ≤ X) :
    ⁅L, T⁆ ≤ N := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rw [commutatorElement_def]
  exact hX x (hL hx) y (hT hy)

theorem le_sup_centralizer_of_out_comm {X K L₁ T : Subgroup G}
    (hX : ∀ x ∈ X, ∀ y ∈ X, x * y * x⁻¹ * y⁻¹ ∈ K ⊔ (X ⊓ Subgroup.centralizer (K : Set G)))
    (hL₁ : L₁ ≤ X) (hT : T ≤ X) (hLT : ⁅L₁, T⁆ = L₁) :
    L₁ ≤ K ⊔ (X ⊓ Subgroup.centralizer (K : Set G)) := by
  have h := commutator_le_of_forall_comm hX hL₁ hT
  rwa [hLT] at h

theorem le_normalizer_of_comm {K C H : Subgroup G} (hHK : H ≤ K)
    (hcomm : ∀ k ∈ K, ∀ c ∈ C, k * c = c * k) : C ≤ Subgroup.normalizer H := by
  intro c hc
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have hh' := hcomm h (hHK hh) c hc
    have e : c * h * c⁻¹ = h := by
      calc c * h * c⁻¹ = h * c * c⁻¹ := by rw [hh']
        _ = h := by group
    rw [e]
    exact hh
  · intro hh
    have hk : c * h * c⁻¹ ∈ K := hHK hh
    have hk' := hcomm (c * h * c⁻¹) hk c⁻¹ (C.inv_mem hc)
    have key : h = c * h * c⁻¹ := by
      calc h = c⁻¹ * (c * h * c⁻¹) * c := by group
        _ = (c * h * c⁻¹) * c⁻¹ * c := by rw [← hk']
        _ = c * h * c⁻¹ := by group
    rw [key]
    exact hh

theorem le_of_threeRank [Finite G] {X K C L₁ : Subgroup G}
    (hKC : K ⊓ C = ⊥) (hcomm : ∀ k ∈ K, ∀ c ∈ C, k * c = c * k)
    (hrank : CFSG.Open.pRank 3 K + CFSG.Open.pRank 3 C ≤ CFSG.Open.pRank 3 X)
    (hK2 : CFSG.Open.pRank 3 K = 2) (hX2 : CFSG.Open.pRank 3 X = 2)
    (hL₁ : L₁ ≤ K ⊔ C)
    (hL₁gen : L₁ = Subgroup.closure {x : G | x ∈ L₁ ∧ ∃ k : ℕ, x ^ (3 ^ k) = 1}) :
    ¬ 3 ∣ Nat.card C ∧ L₁ ≤ K := by
  have hC0 : CFSG.Open.pRank 3 C = 0 := by omega
  have h3C : ¬ 3 ∣ Nat.card C := by
    intro hdvd
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := ↥C) 3 hdvd
    have hxord : orderOf (c : G) = 3 := by rw [Subgroup.orderOf_coe, hc]
    have hEC : Subgroup.zpowers (c : G) ≤ C := Subgroup.zpowers_le.2 c.2
    have h3 : (c : G) ^ 3 = 1 := by
      have h := pow_orderOf_eq_one (c : G)
      rwa [hxord] at h
    have h3z : (c : G) ^ (3 : ℤ) = 1 := by exact_mod_cast h3
    have hE : CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers (c : G)) := by
      refine ⟨inferInstance, fun y hy => ?_⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      calc ((c : G) ^ k) ^ 3 = (c : G) ^ (k * 3) := by
            rw [← zpow_natCast, ← zpow_mul]; norm_num
        _ = (c : G) ^ (3 * k) := by rw [mul_comm]
        _ = ((c : G) ^ (3 : ℤ)) ^ k := zpow_mul _ _ _
        _ = 1 := by rw [h3z, one_zpow]
    have hcard : Nat.card (Subgroup.zpowers (c : G)) = 3 ^ 1 := by
      rw [Nat.card_zpowers, hxord]; norm_num
    have h1 : 1 ≤ CFSG.Open.pRank 3 C :=
      CFSG.SectionRank.le_pRank (by norm_num) hEC hE hcard
    omega
  have hCN : C ≤ Subgroup.normalizer K := le_normalizer_of_comm le_rfl hcomm
  have hsup : ((K ⊔ C : Subgroup G) : Set G) = (K : Set G) * (C : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left K C hCN
  have hKCel : ∀ y ∈ K ⊔ C, ∀ n : ℕ, y ^ (3 ^ n) = 1 → y ∈ K := by
    intro y hy n hyn
    have hy' : y ∈ (K : Set G) * (C : Set G) := by rw [← hsup]; exact hy
    obtain ⟨a, ha, c, hc, rfl⟩ := Set.mem_mul.1 hy'
    have hac : Commute a c := hcomm a ha c hc
    rw [hac.mul_pow] at hyn
    have hu : a ^ (3 ^ n) = (c ^ (3 ^ n))⁻¹ := eq_inv_of_mul_eq_one_left hyn
    have hu1 : a ^ (3 ^ n) = 1 := by
      have hmem : a ^ (3 ^ n) ∈ K ⊓ C :=
        Subgroup.mem_inf.2 ⟨K.pow_mem ha _, by rw [hu]; exact C.inv_mem (C.pow_mem hc _)⟩
      rw [hKC, Subgroup.mem_bot] at hmem
      exact hmem
    have hv1 : c ^ (3 ^ n) = 1 := by
      rw [hu1, one_mul] at hyn
      exact hyn
    have hcop : Nat.Coprime (3 ^ n) (Nat.card C) :=
      Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3C)
    have hcC : (⟨c, hc⟩ : ↥C) ^ (3 ^ n) = 1 := Subtype.ext (by simpa using hv1)
    have hcC' : (⟨c, hc⟩ : ↥C) ^ Nat.card C = 1 := pow_card_eq_one'
    have hg := pow_gcd_eq_one.2 ⟨hcC, hcC'⟩
    rw [Nat.Coprime.gcd_eq_one hcop, pow_one] at hg
    have hc1 : c = 1 := congrArg Subtype.val hg
    rw [hc1, mul_one]
    exact ha
  refine ⟨h3C, ?_⟩
  have hgen : Subgroup.closure {x : G | x ∈ L₁ ∧ ∃ k : ℕ, x ^ (3 ^ k) = 1} ≤ K := by
    rw [Subgroup.closure_le]
    rintro x ⟨hxL, k, hk⟩
    exact hKCel x (hL₁ hxL) k hk
  exact hL₁gen.trans_le hgen

@[expose] def commProj (A B T : Subgroup G) (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    Subgroup G where
  carrier := {a | a ∈ A ∧ ∃ b ∈ B, a * b ∈ T}
  one_mem' := ⟨A.one_mem, 1, B.one_mem, by simpa using T.one_mem⟩
  mul_mem' := by
    rintro a b' ⟨ha, c, hc, hac⟩ ⟨hb, d, hd, hbd⟩
    refine ⟨A.mul_mem ha hb, c * d, B.mul_mem hc hd, ?_⟩
    have e : a * b' * (c * d) = (a * c) * (b' * d) := by
      calc a * b' * (c * d) = a * (b' * c) * d := by group
        _ = a * (c * b') * d := by rw [hcomm b' hb c hc]
        _ = (a * c) * (b' * d) := by group
    rw [e]
    exact T.mul_mem hac hbd
  inv_mem' := by
    rintro a ⟨ha, c, hc, hac⟩
    refine ⟨A.inv_mem ha, c⁻¹, B.inv_mem hc, ?_⟩
    have e : a⁻¹ * c⁻¹ = (a * c)⁻¹ := by
      rw [← mul_inv_rev, hcomm a ha c hc]
    rw [e]
    exact T.inv_mem hac

theorem mem_commProj {A B T : Subgroup G} {hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a} {x : G} :
    x ∈ commProj A B T hcomm ↔ x ∈ A ∧ ∃ b ∈ B, x * b ∈ T :=
  Iff.rfl

theorem sylow_inter_prod {K C T : Subgroup G} (hKC : K ⊓ C = ⊥)
    (hcomm : ∀ k ∈ K, ∀ c ∈ C, k * c = c * k)
    (hT2 : IsPGroup 2 T) (hTKC : T ≤ K ⊔ C)
    (hmax : ∀ S : Subgroup G, S ≤ K ⊔ C → IsPGroup 2 S → T ≤ S → S = T) :
    T = (T ⊓ K) ⊔ (T ⊓ C) := by
  have hcomm' : ∀ c ∈ C, ∀ k ∈ K, c * k = k * c := fun c hc k hk => (hcomm k hk c hc).symm
  have hCN : C ≤ Subgroup.normalizer K := le_normalizer_of_comm le_rfl hcomm
  have hsup : ((K ⊔ C : Subgroup G) : Set G) = (K : Set G) * (C : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left K C hCN
  have hdec : ∀ y ∈ K ⊔ C, ∃ a ∈ K, ∃ c ∈ C, a * c = y := by
    intro y hy
    have hy' : y ∈ (K : Set G) * (C : Set G) := by rw [← hsup]; exact hy
    obtain ⟨a, ha, c, hc, hac⟩ := Set.mem_mul.1 hy'
    exact ⟨a, ha, c, hc, hac⟩
  have hPKK : commProj K C T hcomm ≤ K := fun a ha => (mem_commProj.1 ha).1
  have hPCC : commProj C K T hcomm' ≤ C := fun c hc => (mem_commProj.1 hc).1
  have hPCN : commProj C K T hcomm' ≤ Subgroup.normalizer (commProj K C T hcomm) :=
    hPCC.trans (le_normalizer_of_comm hPKK hcomm)
  have hsS : ((commProj K C T hcomm ⊔ commProj C K T hcomm' : Subgroup G) : Set G)
      = (commProj K C T hcomm : Set G) * (commProj C K T hcomm' : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left _ _ hPCN
  have hpow2 : ∀ t ∈ T, ∃ n : ℕ, t ^ (2 ^ n) = 1 := by
    intro t ht
    obtain ⟨n, hn⟩ := hT2 ⟨t, ht⟩
    exact ⟨n, by simpa using congrArg Subtype.val hn⟩
  have hPK2 : ∀ a ∈ commProj K C T hcomm, ∃ n : ℕ, a ^ (2 ^ n) = 1 := by
    intro a ha
    obtain ⟨haK, c, hc, hac⟩ := mem_commProj.1 ha
    obtain ⟨n, hn⟩ := hpow2 _ hac
    refine ⟨n, ?_⟩
    have hcm : Commute a c := hcomm a haK c hc
    rw [hcm.mul_pow] at hn
    have hu : a ^ (2 ^ n) = (c ^ (2 ^ n))⁻¹ := eq_inv_of_mul_eq_one_left hn
    have hmem : a ^ (2 ^ n) ∈ K ⊓ C :=
      Subgroup.mem_inf.2 ⟨K.pow_mem haK _, by rw [hu]; exact C.inv_mem (C.pow_mem hc _)⟩
    rw [hKC, Subgroup.mem_bot] at hmem
    exact hmem
  have hPC2 : ∀ c ∈ commProj C K T hcomm', ∃ n : ℕ, c ^ (2 ^ n) = 1 := by
    intro c hc
    obtain ⟨hcC, a, ha, hca⟩ := mem_commProj.1 hc
    obtain ⟨n, hn⟩ := hpow2 _ hca
    refine ⟨n, ?_⟩
    have hcm : Commute c a := hcomm' c hcC a ha
    rw [hcm.mul_pow] at hn
    have hu : c ^ (2 ^ n) = (a ^ (2 ^ n))⁻¹ := eq_inv_of_mul_eq_one_left hn
    have hmem : c ^ (2 ^ n) ∈ K ⊓ C :=
      Subgroup.mem_inf.2 ⟨by rw [hu]; exact K.inv_mem (K.pow_mem ha _), C.pow_mem hcC _⟩
    rw [hKC, Subgroup.mem_bot] at hmem
    exact hmem
  have hS2 : IsPGroup 2 (commProj K C T hcomm ⊔ commProj C K T hcomm' : Subgroup G) := by
    intro g
    obtain ⟨x, hx⟩ := g
    have hx' : x ∈ (commProj K C T hcomm : Set G) * (commProj C K T hcomm' : Set G) := by
      rw [← hsS]; exact hx
    obtain ⟨a, ha, c, hc, rfl⟩ := Set.mem_mul.1 hx'
    obtain ⟨n, hn⟩ := hPK2 a ha
    obtain ⟨m, hm⟩ := hPC2 c hc
    refine ⟨n + m, Subtype.ext ?_⟩
    have hac : Commute a c := hcomm a (hPKK ha) c (hPCC hc)
    have ha1 : a ^ (2 ^ (n + m)) = 1 := by rw [pow_add, pow_mul, hn, one_pow]
    have hc1 : c ^ (2 ^ (n + m)) = 1 := by rw [pow_add, mul_comm, pow_mul, hm, one_pow]
    show (a * c) ^ (2 ^ (n + m)) = 1
    rw [hac.mul_pow, ha1, hc1, one_mul]
  have hTS : T ≤ commProj K C T hcomm ⊔ commProj C K T hcomm' := by
    intro t ht
    obtain ⟨a, ha, c, hc, hac⟩ := hdec t (hTKC ht)
    have hat : a * c ∈ T := by rw [hac]; exact ht
    have ha' : a ∈ commProj K C T hcomm := mem_commProj.2 ⟨ha, c, hc, hat⟩
    have hc' : c ∈ commProj C K T hcomm' :=
      mem_commProj.2 ⟨hc, a, ha, by rw [hcomm' c hc a ha]; exact hat⟩
    have h := Subgroup.mul_mem_sup ha' hc'
    rw [hac] at h
    exact h
  have hSle : commProj K C T hcomm ⊔ commProj C K T hcomm' ≤ K ⊔ C :=
    sup_le (fun a ha => Subgroup.mem_sup_left (hPKK ha))
      (fun c hc => Subgroup.mem_sup_right (hPCC hc))
  have hS_eq : commProj K C T hcomm ⊔ commProj C K T hcomm' = T :=
    hmax _ hSle hS2 hTS
  have hPKT : commProj K C T hcomm ≤ T := fun a ha => by
    rw [← hS_eq]; exact Subgroup.mem_sup_left ha
  have hPCT : commProj C K T hcomm' ≤ T := fun c hc => by
    rw [← hS_eq]; exact Subgroup.mem_sup_right hc
  apply le_antisymm
  · calc T = commProj K C T hcomm ⊔ commProj C K T hcomm' := hS_eq.symm
      _ ≤ (T ⊓ K) ⊔ (T ⊓ C) := sup_le_sup (le_inf hPKT hPKK) (le_inf hPCT hPCC)
  · exact sup_le inf_le_left inf_le_left

end CFSG.Quasithin.H13.P31A
