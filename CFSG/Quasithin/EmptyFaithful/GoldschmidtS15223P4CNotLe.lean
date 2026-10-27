module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4CVoc
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223Y1Main
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace S15223P4

namespace C

variable {G : Type} [Group G] [Finite G]
  {T Mc M H : Subgroup G} {B₀ : Subgroup (MulAut (V154 T Mc M))} {I X : Subgroup G}

namespace CData

variable (d : CData T Mc M H B₀ I X)

include d

theorem card_autOn_NI : Nat.card (autOn (M ⊓ I) (V154 T Mc M)) = 6 := by
  obtain ⟨-, -, hΩ, -, -, -, -, hidx⟩ := d.c.concl
  have h36 := (om4_card152 (fun _ _ _ _ hX => S152O4.om4_facts hX) hΩ).1
  have hMV : M ≤ Subgroup.normalizer (V154 T Mc M : Set G) := le_normalizer_V154 T Mc M
  have hNiM : M ⊓ I ≤ M := inf_le_left
  have hCvNi : M ⊓ Subgroup.centralizer (V154 T Mc M : Set G) ≤ M ⊓ I :=
    le_inf inf_le_left ((cv_le_inf152 d.c.setting d.c.inputs).trans inf_le_right)
  have h1 := relIndex_autOn hNiM hMV hCvNi
  have hmul := Subgroup.relIndex_mul_card (autOn (M ⊓ I) (V154 T Mc M)) (autOn M (V154 T Mc M))
  rw [inf_of_le_left (A4.autOn_mono hNiM), h1, hidx, h36] at hmul
  omega

theorem exists_three_elt_not_Mc : ∃ y ∈ X ⊓ (M ⊓ I), y ∉ Mc := by
  have hs := d.c.setting
  have hD := d.c.inputs
  have hMV : M ≤ Subgroup.normalizer (V154 T Mc M : Set G) := le_normalizer_V154 T Mc M
  have hTV : T ≤ Subgroup.normalizer (V154 T Mc M : Set G) := (T_le_M152 hs).trans hMV
  have h3 : 3 ∣ Nat.card (autOn (M ⊓ I) (V154 T Mc M)) := by
    rw [d.card_autOn_NI]
    norm_num
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨yb, hyb⟩ := exists_prime_orderOf_dvd_card' 3 h3
  obtain ⟨y₀, hy₀V, hy₀N, hy₀⟩ := mem_autOn_iff_exists.mp yb.2
  have hy₀ne : orderOf y₀ ≠ 0 := (orderOf_pos y₀).ne'
  obtain ⟨a, m, hm3, hord⟩ := Nat.exists_eq_pow_mul_and_not_dvd hy₀ne 3 (by norm_num)
  have hmdvd : m ∣ orderOf y₀ := ⟨3 ^ a, by rw [hord]; ring⟩
  have hm0 : 0 < m := Nat.pos_of_ne_zero fun h => hy₀ne (by rw [hord, h, mul_zero])
  have hord' : orderOf (y₀ ^ m) = 3 ^ a := by
    rw [orderOf_pow_of_dvd hm0.ne' hmdvd, hord, Nat.mul_div_cancel _ hm0]
  refine ⟨y₀ ^ m, ⟨?_, ?_⟩, ?_⟩
  · rw [← d.oP]
    exact Subgroup.subset_closure ⟨(inf_le_right : M ⊓ I ≤ I) (pow_mem hy₀N m), a, hord'⟩
  · exact pow_mem hy₀N m
  · intro hyMc
    have hyU : y₀ ^ m ∈ (M ⊓ Subgroup.centralizer (V154 T Mc M : Set G)) ⊔ T := by
      rw [← hD.h14.inf_eq.2, ← hD.h14.inf_eq.1]
      exact ⟨(inf_le_left : M ⊓ I ≤ M) (pow_mem hy₀N m), hyMc⟩
    have hyV : y₀ ^ m ∈ Subgroup.normalizer (V154 T Mc M : Set G) := pow_mem hy₀V m
    have h := mem_autOn_of_mem hyV hyU
    rw [S15223.autOn_sup (inf_le_left.trans hMV) hTV, S15223.autOn_inf_centralizer_eq_bot,
      bot_sup_eq] at h
    have hpow : conjAct (V154 T Mc M) ⟨y₀ ^ m, hyV⟩ = (yb : MulAut (V154 T Mc M)) ^ m := by
      rw [← hy₀, ← map_pow]
      rfl
    have hyb' : orderOf (yb : MulAut (V154 T Mc M)) = 3 := by
      rw [← Subgroup.orderOf_coe] at hyb
      exact hyb
    have hcop : Nat.Coprime (orderOf (yb : MulAut (V154 T Mc M))) m := by
      rw [hyb']
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hm3
    have hord3 : orderOf (conjAct (V154 T Mc M) ⟨y₀ ^ m, hyV⟩) = 3 := by
      rw [hpow, Nat.Coprime.orderOf_pow hcop, hyb']
    have hT2 : IsPGroup 2 (autOn T (V154 T Mc M)) := isPGroup_autOn hs.qtfe.sylow.1 hTV
    obtain ⟨k, hk⟩ := hT2 ⟨_, h⟩
    have hk' : (conjAct (V154 T Mc M) ⟨y₀ ^ m, hyV⟩) ^ 2 ^ k = 1 := by
      simpa using congrArg Subtype.val hk
    have hdvd : 3 ∣ 2 ^ k := by
      rw [← hord3]
      exact orderOf_dvd_of_pow_eq_one hk'
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd) (by norm_num)

theorem X_not_le_Mc : ¬ X ≤ Mc := by
  intro h
  obtain ⟨y, hy, hyM⟩ := d.exists_three_elt_not_Mc
  exact hyM (h hy.1)

end CData

end C

end S15223P4

end CFSG.Quasithin
