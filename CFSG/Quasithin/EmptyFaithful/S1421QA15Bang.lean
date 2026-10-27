module

public import CFSG.Quasithin.EmptyFaithful.S1421STC3Fac
public import CFSG.Quasithin.EmptyFaithful.S1421STf

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace S1421

variable {G : Type} [Group G] [Finite G] {T M H K1 : Subgroup G}

omit [Finite G] in
theorem odd_mem_of_sup_normal {N P T : Subgroup G} (hP : (P.subgroupOf N).Normal)
    (hPN : P ≤ N) (hTN : T ≤ N) (hN : N = P ⊔ T) (hT2 : IsPGroup 2 T) {x : G} (hx : x ∈ N)
    (hodd : Odd (orderOf x)) : x ∈ P := by
  have : (P.subgroupOf N).Normal := hP
  have hsup : P.subgroupOf N ⊔ T.subgroupOf N = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hPN hTN, ← hN, Subgroup.subgroupOf_self]
  have hxmem : (⟨x, hx⟩ : ↥N) ∈ P.subgroupOf N ⊔ T.subgroupOf N := by
    rw [hsup]
    exact Subgroup.mem_top _
  obtain ⟨p, hp, t, ht, hpt⟩ :=
    (Subgroup.mem_sup_of_normal_left (s := P.subgroupOf N) (t := T.subgroupOf N)).mp hxmem
  have hmk : (QuotientGroup.mk ⟨x, hx⟩ : ↥N ⧸ P.subgroupOf N) = QuotientGroup.mk t := by
    rw [← hpt, QuotientGroup.mk_mul]
    have : (QuotientGroup.mk p : ↥N ⧸ P.subgroupOf N) = 1 := (QuotientGroup.eq_one_iff p).mpr hp
    rw [this, one_mul]
  have ht' : (t : G) ∈ T := ht
  obtain ⟨k, hk⟩ := hT2 ⟨(t : G), ht'⟩
  have hk' : t ^ (2 ^ k) = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
  have h1 : orderOf (QuotientGroup.mk t : ↥N ⧸ P.subgroupOf N) ∣ 2 ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← QuotientGroup.mk_pow, hk', QuotientGroup.mk_one]
  have h2 : orderOf (QuotientGroup.mk t : ↥N ⧸ P.subgroupOf N) ∣ orderOf x := by
    rw [← hmk]
    apply orderOf_dvd_of_pow_eq_one
    rw [← QuotientGroup.mk_pow]
    have : (⟨x, hx⟩ : ↥N) ^ orderOf x = 1 := Subtype.ext (by simp [pow_orderOf_eq_one])
    rw [this, QuotientGroup.mk_one]
  have hcop : Nat.Coprime (2 ^ k) (orderOf x) :=
    Nat.Coprime.pow_left k ((Nat.coprime_two_left).mpr hodd)
  have h3 : orderOf (QuotientGroup.mk t : ↥N ⧸ P.subgroupOf N) ∣ 1 := by
    have := Nat.dvd_gcd h1 h2
    rwa [hcop] at this
  have h4 : (QuotientGroup.mk t : ↥N ⧸ P.subgroupOf N) = 1 :=
    orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
  rw [h4] at hmk
  exact (QuotientGroup.eq_one_iff (N := P.subgroupOf N) (⟨x, hx⟩ : ↥N)).mp hmk

theorem oTwoUpper_le_centralizer_omegaOneCenter_sOf (st : Setting1427 T M H K1)
    (hlt : sOf T K1 < T) {Kc : Subgroup G} (hKc : Kc ∈ cComp (mcOf T))
    (hKT : oTwoUpper H ≤ Kc ⊔ T) :
    oTwoUpper H ≤ Subgroup.centralizer (omegaOneCenterOf (sOf T K1) : Set G) := by
  set Zs := omegaOneCenterOf (sOf T K1) with hZs
  set N := Kc ⊔ T with hN
  have hKcC : Kc ≤ Subgroup.centralizer (Zs : Set G) := le_centralizer_omegaOneCenter_sOf st hKc hKT
  have hTN : T ≤ Subgroup.normalizer (Zs : Set G) :=
    (T_le_normalizer_sOf st hlt.ne).trans (A4.normalizer_le_normalizer_omegaOneCenterOf _)
  have hNN : N ≤ Subgroup.normalizer (Zs : Set G) :=
    sup_le (hKcC.trans (Subgroup.centralizer_le_normalizer _)) hTN
  set P := N ⊓ Subgroup.centralizer (Zs : Set G) with hP
  have hPN : P ≤ N := inf_le_left
  have hPnorm : (P.subgroupOf N).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hPN).mpr ?_
    exact CFSG.RankThreeCoreUniqueness.Helpers.common_normalizer_le_normalizer_inf N N
      (Subgroup.centralizer (Zs : Set G)) Subgroup.le_normalizer
      (hNN.trans (CFSG.RankThreeCoreUniqueness.Helpers.normalizer_le_normalizer_centralizer Zs))
  have hKcP : Kc ≤ P := le_inf le_sup_left hKcC
  have hNP : N = P ⊔ T := by
    refine le_antisymm (sup_le_sup_right hKcP T) (sup_le hPN le_sup_right)
  have hT2 : IsPGroup 2 T := st.hyp.sylow.1
  refine (Subgroup.closure_le _).mpr fun x hx => ?_
  have hxN : x ∈ N := hKT (Subgroup.subset_closure hx)
  exact (odd_mem_of_sup_normal hPnorm hPN le_sup_right hNP hT2 hxN hx.2).2

end S1421

end CFSG.Quasithin
