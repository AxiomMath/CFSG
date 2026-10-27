module

public import CFSG.Quasithin.H13.A6S13721b

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace A6L24

theorem commute_check : ∀ σ : Perm (Fin 5), σ * σ * σ = 1 → σ ≠ 1 → ∀ τ : Perm (Fin 5),
    τ * σ = σ * τ → Perm.sign τ = 1 → τ * τ * τ = 1 := by
  decide +kernel

theorem eq_one_of_commute5 {σ τ : Perm (Fin 5)} (h3 : σ ^ 3 = 1) (h1 : σ ≠ 1)
    (hτ : τ ∈ alternatingGroup (Fin 5)) (hc : τ * σ = σ * τ) {k : ℕ} (hk : τ ^ 2 ^ k = 1) :
    τ = 1 := by
  have h3' : σ * σ * σ = 1 := by rw [← pow_three', h3]
  have hτ3 : τ ^ 3 = 1 := by
    rw [pow_three']
    exact commute_check σ h3' h1 τ hc (Perm.mem_alternatingGroup.mp hτ)
  have h2 : orderOf τ ∣ Nat.gcd 3 (2 ^ k) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hτ3) (orderOf_dvd_of_pow_eq_one hk)
  have h4 : Nat.gcd 3 (2 ^ k) = 1 := Nat.Coprime.pow_right _ (by decide : Nat.Coprime 3 2)
  rw [h4, Nat.dvd_one, orderOf_eq_one_iff] at h2
  exact h2

theorem card_le_two_of_eq {X : Type*} [Group X] [Finite X] {D : Subgroup X}
    (h : ∀ x ∈ D, ∀ y ∈ D, x ≠ 1 → y ≠ 1 → x = y) : Nat.card D ≤ 2 := by
  classical
  by_cases hex : ∃ x ∈ D, x ≠ 1
  · obtain ⟨x, hx, hx1⟩ := hex
    have hsub : (D : Set X) ⊆ (({1, x} : Finset X) : Set X) := by
      intro y hy
      by_cases hy1 : y = 1
      · simp [hy1]
      · simp [h y hy x hx hy1 hx1]
    have h1 : Nat.card D ≤ Nat.card (({1, x} : Finset X) : Set X) :=
      Nat.card_mono (Finset.finite_toSet _) hsub
    rw [Nat.card_coe_set_eq, Set.ncard_coe_finset] at h1
    exact h1.trans Finset.card_le_two
  · push Not at hex
    rw [(Subgroup.eq_bot_iff_forall D).2 hex, Subgroup.card_bot]
    norm_num

end A6L24

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem exists_comm_not_mem_A5 (hhat : ¬ IsHatA6 L)
    {H K : Subgroup G} (hH : H ∈ S.Hz) (hKH : K ≤ H) (hHK : H ≤ Subgroup.normalizer (K : Set G))
    (hL1K : S.L1 ≤ K) {α : ↥K →* alternatingGroup (Fin 5)} (hαs : Function.Surjective α)
    (hαk : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ pCoreOf 2 H) {c : G} (hc : c ∈ S.L1)
    (hc3 : c ^ 3 = 1) (hcQ : c ∉ pCoreOf 2 H) :
    ∃ o ∈ pCoreOf 2 S.L1, c * o * c⁻¹ * o⁻¹ ∉ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hall
  push Not at hall
  set γ : ↥K := ⟨c, hL1K hc⟩ with hγ
  set σ : Perm (Fin 5) := (α γ : Perm (Fin 5)) with hσ
  have hσ3 : σ ^ 3 = 1 := by
    have h1 : γ ^ 3 = 1 := Subtype.ext (by simpa [hγ] using hc3)
    have h2 : (α γ) ^ 3 = 1 := by rw [← map_pow, h1, map_one]
    rw [hσ, ← Subgroup.coe_pow, h2, Subgroup.coe_one]
  have hα1 : α γ ≠ 1 := fun h1 => hcQ ((hαk γ).1 h1)
  have hσ1 : σ ≠ 1 := fun h1 => hα1 (Subtype.ext h1)
  have h2el : ∀ x : ↥K, (∃ k : ℕ, (x : G) ^ 2 ^ k = 1) →
      (α x : Perm (Fin 5)) * σ = σ * α x → α x = 1 := by
    rintro x ⟨k, hk⟩ hcx
    have hxk : (α x : Perm (Fin 5)) ^ 2 ^ k = 1 := by
      have h1 : x ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk)
      rw [← Subgroup.coe_pow, ← map_pow, h1, map_one, Subgroup.coe_one]
    exact Subtype.ext (A6L24.eq_one_of_commute5 hσ3 hσ1 (α x).2 hcx hxk)
  have hO1 : ∀ o (ho : o ∈ pCoreOf 2 S.L1), α ⟨o, hL1K (pCoreOf_le 2 S.L1 ho)⟩ = 1 := by
    intro o ho
    set ω : ↥K := ⟨o, hL1K (pCoreOf_le 2 S.L1 ho)⟩ with hω
    have hcomm : α (γ * ω * γ⁻¹ * ω⁻¹) = 1 := (hαk _).2 (hall o ho)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at hcomm
    have hc' : (α ω : Perm (Fin 5)) * σ = σ * α ω := by
      have h1 : α γ * α ω = α ω * α γ := by
        calc α γ * α ω = (α γ * α ω * (α γ)⁻¹ * (α ω)⁻¹) * α ω * α γ := by group
          _ = α ω * α γ := by rw [hcomm, one_mul]
      exact (congrArg Subtype.val h1).symm
    obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 S.L1 ⟨o, ho⟩
    have hok : o ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact h2el ω ⟨k, hok⟩ hc'
  set c₀ : G := (S.cL1 hhat : G) with hc₀
  have hc₀L : c₀ ∈ S.L1 := S.cL1_mem hhat
  set a := α ⟨c₀, hL1K hc₀L⟩ with ha
  have ha3 : a ^ 3 = 1 := by
    have h1 : (⟨c₀, hL1K hc₀L⟩ : ↥K) ^ 3 = 1 := Subtype.ext (by simpa using S.cL1_cube hhat)
    rw [ha, ← map_pow, h1, map_one]
  have hcases : ∀ x (hx : x ∈ S.L1), α ⟨x, hL1K hx⟩ ≠ 1 →
      α ⟨x, hL1K hx⟩ = a ∨ α ⟨x, hL1K hx⟩ = a * a := by
    intro x hx hx1
    rcases S.L1_decomp hhat hx with h | h | h
    · exact absurd (hO1 x h) hx1
    · have h1 := hO1 _ h
      have e : (⟨c₀ * c₀ * x, hL1K (pCoreOf_le 2 S.L1 h)⟩ : ↥K) =
          ⟨c₀, hL1K hc₀L⟩ * ⟨c₀, hL1K hc₀L⟩ * ⟨x, hL1K hx⟩ := rfl
      rw [e, map_mul, map_mul] at h1
      left
      calc α ⟨x, hL1K hx⟩ = a ^ 3 * α ⟨x, hL1K hx⟩ := by rw [ha3, one_mul]
        _ = a * (a * a * α ⟨x, hL1K hx⟩) := by rw [pow_succ, pow_two]; simp only [mul_assoc]
        _ = a := by rw [h1, mul_one]
    · have h1 := hO1 _ h
      have e : (⟨c₀ * x, hL1K (pCoreOf_le 2 S.L1 h)⟩ : ↥K) =
          ⟨c₀, hL1K hc₀L⟩ * ⟨x, hL1K hx⟩ := rfl
      rw [e, map_mul] at h1
      right
      calc α ⟨x, hL1K hx⟩ = a ^ 3 * α ⟨x, hL1K hx⟩ := by rw [ha3, one_mul]
        _ = a * a * (a * α ⟨x, hL1K hx⟩) := by rw [pow_succ, pow_two]; simp only [mul_assoc]
        _ = a * a := by rw [h1, mul_one]
  have hca : α γ = a ∨ α γ = a * a := hcases c hc hα1
  have hnorm : ∀ t : ↥K, (t : G) ∈ T →
      (α t : Perm (Fin 5)) * σ = σ * α t ∨ (α t : Perm (Fin 5)) * σ = σ * σ * α t := by
    intro t htT
    set d := α t with hd
    have hxL : (t : G) * c * (t : G)⁻¹ ∈ S.L1 :=
      (Subgroup.mem_normalizer_iff.mp (S.T_le_normalizer_L1 htT) c).mp hc
    have hαx : α ⟨(t : G) * c * (t : G)⁻¹, hL1K hxL⟩ = d * α γ * d⁻¹ := by
      have e : (⟨(t : G) * c * (t : G)⁻¹, hL1K hxL⟩ : ↥K) = t * γ * t⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv]
    have hx1 : α ⟨(t : G) * c * (t : G)⁻¹, hL1K hxL⟩ ≠ 1 := by
      rw [hαx]
      intro h
      apply hα1
      calc α γ = d⁻¹ * (d * α γ * d⁻¹) * d := by group
        _ = 1 := by rw [h]; group
    have hxa := hcases _ hxL hx1
    rw [hαx] at hxa
    have ha4 : a * a * (a * a) = a := by
      calc a * a * (a * a) = a ^ 3 * a := by rw [pow_succ, pow_two]; simp only [mul_assoc]
        _ = a := by rw [ha3, one_mul]
    have key : d * α γ * d⁻¹ = α γ ∨ d * α γ * d⁻¹ = α γ * α γ := by
      rcases hca with h | h <;> rcases hxa with h' | h'
      · exact Or.inl (h'.trans h.symm)
      · exact Or.inr (by rw [h', h])
      · exact Or.inr (by rw [h', h, ha4])
      · exact Or.inl (h'.trans h.symm)
    rcases key with h | h
    · left
      have h1 : d * α γ = α γ * d := by
        calc d * α γ = (d * α γ * d⁻¹) * d := by group
          _ = α γ * d := by rw [h]
      exact congrArg Subtype.val h1
    · right
      have h1 : d * α γ = α γ * α γ * d := by
        calc d * α γ = (d * α γ * d⁻¹) * d := by group
          _ = α γ * α γ * d := by rw [h]
      exact congrArg Subtype.val h1
  have hTel : ∀ t : ↥K, (t : G) ∈ T → ∃ k : ℕ, (t : G) ^ 2 ^ k = 1 := by
    intro t ht
    obtain ⟨k, hk⟩ := S.h13.sylow.1 ⟨t, ht⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hinv : ∀ t : ↥K, (t : G) ∈ T → α t ≠ 1 →
      (α t : Perm (Fin 5)) * σ = σ * σ * α t := by
    intro t ht h1
    rcases hnorm t ht with h | h
    · exact absurd (h2el t (hTel t ht) h) h1
    · exact h
  set Dα : Subgroup (alternatingGroup (Fin 5)) := ((T ⊓ K).subgroupOf K).map α with hDα
  have huniq : ∀ x ∈ Dα, ∀ y ∈ Dα, x ≠ 1 → y ≠ 1 → x = y := by
    rintro _ ⟨t, ht, rfl⟩ _ ⟨t', ht', rfl⟩ hx hy
    have htT : (t : G) ∈ T := (Subgroup.mem_subgroupOf.mp ht).1
    have ht'T : (t' : G) ∈ T := (Subgroup.mem_subgroupOf.mp ht').1
    have e1 := hinv t htT hx
    have e2 := hinv t' ht'T hy
    have hT2 : ((t⁻¹ * t' : ↥K) : G) ∈ T := T.mul_mem (T.inv_mem htT) ht'T
    have hcomm : (α (t⁻¹ * t') : Perm (Fin 5)) * σ = σ * α (t⁻¹ * t') := by
      rw [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
      have hσa : σ * (α t : Perm (Fin 5))⁻¹ = (α t : Perm (Fin 5))⁻¹ * σ * σ := by
        calc σ * (α t : Perm (Fin 5))⁻¹ =
            (α t : Perm (Fin 5))⁻¹ * ((α t : Perm (Fin 5)) * σ) * (α t : Perm (Fin 5))⁻¹ := by
              group
          _ = (α t : Perm (Fin 5))⁻¹ * (σ * σ * (α t : Perm (Fin 5))) *
              (α t : Perm (Fin 5))⁻¹ := by rw [e1]
          _ = (α t : Perm (Fin 5))⁻¹ * σ * σ := by group
      calc (α t : Perm (Fin 5))⁻¹ * (α t' : Perm (Fin 5)) * σ =
          (α t : Perm (Fin 5))⁻¹ * ((α t' : Perm (Fin 5)) * σ) := by group
        _ = (α t : Perm (Fin 5))⁻¹ * (σ * σ * (α t' : Perm (Fin 5))) := by rw [e2]
        _ = (α t : Perm (Fin 5))⁻¹ * σ * σ * (α t' : Perm (Fin 5)) := by group
        _ = σ * (α t : Perm (Fin 5))⁻¹ * (α t' : Perm (Fin 5)) := by rw [← hσa]
        _ = σ * ((α t : Perm (Fin 5))⁻¹ * (α t' : Perm (Fin 5))) := by group
    have h1 := h2el _ (hTel _ hT2) hcomm
    rw [map_mul, map_inv] at h1
    calc α t = α t * ((α t)⁻¹ * α t') := by rw [h1, mul_one]
      _ = α t' := by group
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hTs : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.h13.sylow hTH
  have hKn : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hHK
  have hTK : IsSylowTwoOf (T ⊓ K) K :=
    CFSG.QuasithinUnique.RankOneRecog.isSylowTwoOf_inf_of_subnormal hTs hKH hKn.isSubnormal
  have hodd : ¬ 2 ∣ Dα.index := fun h => hTK.2.2 (h.trans (Subgroup.index_map_dvd _ hαs))
  have hcard : Nat.card Dα * Dα.index = 60 := by
    rw [Subgroup.card_mul_index, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    rfl
  have hcop : Nat.Coprime (2 ^ 2) Dα.index :=
    Nat.Coprime.pow_left 2
      (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd)))
  have h4 : 2 ^ 2 ∣ Nat.card Dα := hcop.dvd_of_dvd_mul_right (by rw [hcard]; norm_num)
  have h2 := A6L24.card_le_two_of_eq huniq
  have hpos : 0 < Nat.card Dα := Nat.card_pos
  have := Nat.le_of_dvd hpos h4
  omega

section NonAb

variable (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15) (h1356two : Input1356Two)
  {H : Subgroup G} (hH : H ∈ S.Hz) (hab : IsElemAbelian 2 (conjClosure S.V3 H))
include hNS h13315 h1356two hH hab

omit hab in
theorem not_mem_QH_of_L1 {c : G} (hcL : c ∈ S.L1)
    (hcO : c ∉ pCoreOf 2 S.L1) : c ∉ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL1H := S.L1_le_of_mem_Hz hNS h13315 h1356two hH
  have hHQ : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := le_normalizer_pCoreOf 2 H
  have hL1Q : S.L1 ⊓ pCoreOf 2 H ≤ pCoreOf 2 S.L1 := by
    refine le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
      ((pCoreOf_isPGroup 2 H).to_le inf_le_right)
    exact fun l hl => mem_normalizer_inf_of (Subgroup.le_normalizer hl) (hHQ (hL1H hl))
  exact fun h => hcO (hL1Q ⟨hcL, h⟩)

theorem four_pow_five_le_nu
    {K : Subgroup G} (hL1K : S.L1 ≤ K)
    (hKU0 : K ≤ Subgroup.centralizer ((conjClosure S.V3 H ⊓
      Subgroup.centralizer (pCoreOf 2 H : Set G) : Subgroup G) : Set G))
    {c : G} (hcL : c ∈ S.L1) (hc3 : c ^ 3 = 1)
    (hO : ∃ o ∈ pCoreOf 2 S.L1, c * o * c⁻¹ * o⁻¹ ∉ pCoreOf 2 H)
    (hU : 4 ^ 2 ≤ nu c (conjClosure S.V3 H)) :
    4 ^ 5 ≤ nu c (pCoreOf 2 S.L1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF := S.hypF91 hNS h13315 h1356two hH
  have hL1H := S.L1_le_of_mem_Hz hNS h13315 h1356two hH
  have hcH : c ∈ H := hL1H hcL
  have hHQ : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := le_normalizer_pCoreOf 2 H
  have hHU : H ≤ Subgroup.normalizer (conjClosure S.V3 H : Set G) :=
    le_normalizer_conjClosure S.V3 H
  have hQH : pCoreOf 2 H ≤ H := pCoreOf_le 2 H
  have hQL1 := S.QH_le_normalizer_L1 hNS h13315 h1356two hH
  have hQO : pCoreOf 2 H ≤ Subgroup.normalizer (pCoreOf 2 S.L1 : Set G) :=
    hQL1.trans (normalizer_le_normalizer_pCoreOf 2 S.L1)
  have hcO' : c ∈ Subgroup.normalizer (pCoreOf 2 S.L1 : Set G) := le_normalizer_pCoreOf 2 S.L1 hcL
  have hOH : pCoreOf 2 S.L1 ≤ H := (pCoreOf_le 2 S.L1).trans hL1H
  have hL1Q : S.L1 ⊓ pCoreOf 2 H ≤ pCoreOf 2 S.L1 := by
    refine le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
      ((pCoreOf_isPGroup 2 H).to_le inf_le_right)
    exact fun l hl => mem_normalizer_inf_of (Subgroup.le_normalizer hl) (hHQ (hL1H hl))
  have hA : 4 * nu c (pCoreOf 2 S.L1 ⊓ pCoreOf 2 H) ≤ nu c (pCoreOf 2 S.L1) := by
    obtain ⟨o, ho, hno⟩ := hO
    refine four_mul_nu_le hc3 (pCoreOf_isPGroup 2 S.L1) inf_le_left hcO'
      (mem_normalizer_inf_of hcO' (hHQ hcH)) ?_ ⟨o, ho, fun h => hno h.2⟩
    exact fun x hx => mem_normalizer_inf_of (Subgroup.le_normalizer (mem_cfix.1 hx).1)
      (hHQ (hOH (mem_cfix.1 hx).1))
  have hB : nu c (pCoreOf 2 S.L1 ⊓ pCoreOf 2 H) = nu c (pCoreOf 2 H) := by
    have hY3 : ¬ 3 ∣ Nat.card ↥(pCoreOf 2 S.L1 ⊓ pCoreOf 2 H) := by
      obtain ⟨e, he⟩ := IsPGroup.iff_card.mp ((pCoreOf_isPGroup 2 H).to_le
        (inf_le_right : pCoreOf 2 S.L1 ⊓ pCoreOf 2 H ≤ pCoreOf 2 H))
      rw [he]
      intro h
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
      omega
    have hcY : ∀ y ∈ pCoreOf 2 S.L1 ⊓ pCoreOf 2 H, c * y * c⁻¹ ∈ pCoreOf 2 S.L1 ⊓ pCoreOf 2 H :=
      fun y hy => (Subgroup.mem_normalizer_iff.mp (mem_normalizer_inf_of hcO' (hHQ hcH)) y).mp hy
    have hcX : ∀ q ∈ pCoreOf 2 H, q⁻¹ * (c * q * c⁻¹) ∈ pCoreOf 2 S.L1 ⊓ pCoreOf 2 H := by
      intro q hq
      have h1 : q⁻¹ * c * q⁻¹⁻¹ ∈ S.L1 :=
        (Subgroup.mem_normalizer_iff.mp (hQL1 ((pCoreOf 2 H).inv_mem hq)) _).mp hcL
      have hmem : q⁻¹ * (c * q * c⁻¹) ∈ S.L1 ⊓ pCoreOf 2 H := by
        refine ⟨?_, (pCoreOf 2 H).mul_mem ((pCoreOf 2 H).inv_mem hq)
          ((Subgroup.mem_normalizer_iff.mp (hHQ hcH) q).mp hq)⟩
        have e : q⁻¹ * (c * q * c⁻¹) = (q⁻¹ * c * q⁻¹⁻¹) * c⁻¹ := by group
        rw [e]
        exact S.L1.mul_mem h1 (S.L1.inv_mem hcL)
      exact ⟨hL1Q hmem, hmem.2⟩
    have hN : cfix c (pCoreOf 2 H) ≤
        Subgroup.normalizer ((pCoreOf 2 S.L1 ⊓ pCoreOf 2 H : Subgroup G) : Set G) :=
      fun x hx => mem_normalizer_inf_of (hQO (mem_cfix.1 hx).1)
        (Subgroup.le_normalizer (mem_cfix.1 hx).1)
    rw [nu_mul c (inf_le_right : pCoreOf 2 S.L1 ⊓ pCoreOf 2 H ≤ pCoreOf 2 H) hN,
      relIndex_cfix_sup_eq_one hc3 inf_le_right hY3 hcY hcX, one_mul]
  have hHCQ : pCoreOf 2 H ⊓ Subgroup.centralizer (conjClosure S.V3 H : Set G) ≤ pCoreOf 2 H :=
    inf_le_left
  have hNHC : cfix c (pCoreOf 2 H) ≤ Subgroup.normalizer ((pCoreOf 2 H ⊓
      Subgroup.centralizer (conjClosure S.V3 H : Set G) : Subgroup G) : Set G) := by
    intro x hx
    have hxH := hQH (mem_cfix.1 hx).1
    exact mem_normalizer_inf_of (hHQ hxH) (normalizes_of_conj_mem (X := H) (fun l hl y hy =>
      conj_centralizer_mem (hHU hl) hy) hxH)
  have hU0U : conjClosure S.V3 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) ≤
      conjClosure S.V3 H := inf_le_left
  have hNU0 : cfix c (conjClosure S.V3 H) ≤ Subgroup.normalizer ((conjClosure S.V3 H ⊓
      Subgroup.centralizer (pCoreOf 2 H : Set G) : Subgroup G) : Set G) := by
    intro x hx
    have hxH := hQH (hF.conjClosure_Vp_le_pCoreOf (mem_cfix.1 hx).1)
    exact mem_normalizer_inf_of (hHU hxH) (normalizes_of_conj_mem (X := H) (fun l hl y hy =>
      conj_centralizer_mem (hHQ hl) hy) hxH)
  have hnuU0 : nu c (conjClosure S.V3 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G)) = 1 := by
    rw [nu, Subgroup.relIndex_eq_one]
    intro u hu
    refine mem_cfix.2 ⟨hu, ?_⟩
    exact (Subgroup.mem_centralizer_iff.mp (hKU0 (hL1K hcL)) u hu).symm
  have hdual := nu_dual_F97 hF hab hcH hc3
  have hC : nu c (pCoreOf 2 H) = nu c (conjClosure S.V3 H) *
      nu c (pCoreOf 2 H ⊓ Subgroup.centralizer (conjClosure S.V3 H : Set G)) := by
    rw [nu_mul c hHCQ hNHC, hdual, nu_mul c hU0U hNU0, hnuU0, mul_one]
  have hVQ := S.VH_le_QH hNS h13315 h1356two hH hab
  have hUHC : conjClosure S.V3 H ≤
      pCoreOf 2 H ⊓ Subgroup.centralizer (conjClosure S.V3 H : Set G) :=
    le_inf (S.UH_le_VH.trans hVQ)
      (S.UH_le_VH.trans (S.VH_le_centralizer_UH hNS h13315 h1356two hH hab))
  have hD : nu c (conjClosure S.V3 H) ≤
      nu c (pCoreOf 2 H ⊓ Subgroup.centralizer (conjClosure S.V3 H : Set G)) :=
    nu_le_nu hUHC fun x hx => hHU (hQH (mem_cfix.1 hx).1.1)
  calc 4 ^ 5 = 4 * (4 ^ 2 * 4 ^ 2) := by norm_num
    _ ≤ 4 * (nu c (conjClosure S.V3 H) * nu c (conjClosure S.V3 H)) := by gcongr
    _ ≤ 4 * (nu c (conjClosure S.V3 H) * nu c (pCoreOf 2 H ⊓
        Subgroup.centralizer (conjClosure S.V3 H : Set G))) := by gcongr
    _ = 4 * nu c (pCoreOf 2 S.L1 ⊓ pCoreOf 2 H) := by rw [hB, hC]
    _ ≤ nu c (pCoreOf 2 S.L1) := hA

end NonAb

end Setting4

end CFSG.Quasithin.H13.A6
