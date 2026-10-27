module

public import CFSG.Quasithin.EmptyFaithful.S146zYCfg
public import CFSG.Quasithin.EmptyFaithful.S146zYFD3

public section

namespace CFSG.Quasithin.S146zY

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.F134.LieD4

namespace D4Five

theorem false_of_forall_conj_eq_pow_twentyFive {A : Type} [Group A] {L P T : Subgroup A}
    (hcfg : E25Config L P T)
    (h : ∀ t ∈ T ⊓ Subgroup.normalizer (P : Set A), ∃ k : ℕ, ∀ x ∈ P, t * x * t⁻¹ = x ^ k) :
    False := by
  obtain ⟨x₀, hx₀, hx₀1⟩ : ∃ x ∈ P, x ≠ 1 := by
    by_contra hcon
    have hbot : P = ⊥ := (Subgroup.eq_bot_iff_forall P).2 fun x hx => by
      by_contra hx1
      exact hcon ⟨x, hx, hx1⟩
    have := hcfg.card
    rw [hbot, Subgroup.card_bot] at this
    norm_num at this
  have key : ∀ t ∈ T ⊓ Subgroup.normalizer (P : Set A), ∀ y ∈ Subgroup.zpowers x₀,
      t * y * t⁻¹ ∈ Subgroup.zpowers x₀ := by
    intro t ht y hy
    obtain ⟨k, hk⟩ := h t ht
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    rw [← conj_zpow, hk x₀ hx₀]
    exact zpow_mem (pow_mem (Subgroup.mem_zpowers x₀) _) m
  have hQN : T ⊓ Subgroup.normalizer (P : Set A) ≤
      Subgroup.normalizer (Subgroup.zpowers x₀ : Set A) := by
    intro t ht
    refine Subgroup.mem_normalizer_iff.2 fun y => ⟨key t ht y, fun hy => ?_⟩
    have := key t⁻¹ (inv_mem ht) _ hy
    simpa [mul_assoc] using this
  rcases hcfg.irred _ ((Subgroup.zpowers_le).2 hx₀) hQN with h' | h'
  · exact hx₀1 (Subgroup.zpowers_eq_bot.1 h')
  · have h1 : Nat.card (Subgroup.zpowers x₀) = 25 := by rw [h', hcfg.card]
    rw [Nat.card_zpowers] at h1
    have := orderOf_dvd_of_pow_eq_one (hcfg.exp x₀ hx₀)
    rw [h1] at this
    norm_num at this

end D4Five

theorem facts134Five_d4Even :
    ∀ n : ℕ,
      NoE25Config fun (X : Type) [Group X] => ChevalleyExceptionalModel X .trialityD4 2 n := by
  intro n A _ _ L P T hL hcfg
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hn, -⟩ := exists_mulEquiv_graphFixedRootGroup hL
  rcases Nat.lt_or_ge n 2 with hlt | hn2
  ·
    obtain rfl : n = 1 := by omega
    have h25 := hcfg.twentyFive_dvd_card
    rw [CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hL] at h25
    change 25 ∣ CFSG.Open.ordTrialityD4 (2 ^ 1) at h25
    norm_num [CFSG.Open.ordTrialityD4] at h25
  have : L.Normal := hcfg.normal
  have hS := E25Config.isSylowTwoOf_inf hcfg
  let U : Sylow 2 L :=
    (hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm).toSylow hS.2.2
  have hU : (U : Subgroup L) = (T ⊓ L).subgroupOf L := rfl
  have hP' : Nat.card (P.subgroupOf L) = 25 := by
    rw [← hcfg.card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcfg.le).toEquiv
  have hmul' : ∀ u ∈ (U : Subgroup L), ∀ x ∈ P.subgroupOf L, ∃ y ∈ P.subgroupOf L,
      ∃ s ∈ (U : Subgroup L), u * x = y * s := by
    intro u hu x hx
    rw [hU] at hu
    obtain ⟨y, hy, s, hs, he⟩ := E25Config.mul_inf hcfg u (Subgroup.mem_subgroupOf.mp hu) x
      (Subgroup.mem_subgroupOf.mp hx)
    exact ⟨⟨y, hcfg.le hy⟩, Subgroup.mem_subgroupOf.mpr hy, ⟨s, hs.2⟩,
      by rw [hU]; exact Subgroup.mem_subgroupOf.mpr hs, Subtype.ext he⟩
  have hPN := D4Five.le_normalizer_of_mul_twentyFive hL hn2 U hP' hmul'
  refine D4Five.false_of_forall_conj_eq_pow_twentyFive hcfg fun t ht => ?_
  obtain ⟨htT, htN⟩ := Subgroup.mem_inf.1 ht
  have hαU : (U : Subgroup L).map (MulAut.conjNormal t).toMonoidHom = U := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      have hy' : (y : A) ∈ T ⊓ L := by
        have := SetLike.mem_coe.1 hy
        rw [hU, Subgroup.mem_subgroupOf] at this
        exact this
      rw [hU, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom, MulAut.conjNormal_apply]
      exact Subgroup.mem_inf.2 ⟨mul_mem (mul_mem htT (Subgroup.mem_inf.1 hy').1) (inv_mem htT),
        (MulAut.conjNormal t y).2⟩
    · rw [Subgroup.card_map_of_injective (MulEquiv.injective _)]
  obtain ⟨k, hk⟩ := exists_inv_mul_pow_mem_of_map_eq hL U (MulAut.conjNormal t) hαU
  refine ⟨2 ^ k, fun x hx => ?_⟩
  have hx' : (⟨x, hcfg.le hx⟩ : L) ∈ P.subgroupOf L := hx
  have h1 := hk _ (hPN hx')
  have hαx : MulAut.conjNormal t (⟨x, hcfg.le hx⟩ : L) ∈ P.subgroupOf L := by
    rw [Subgroup.mem_subgroupOf, MulAut.conjNormal_apply]
    exact (Subgroup.mem_normalizer_iff.1 htN x).1 hx
  have h2 : (MulAut.conjNormal t (⟨x, hcfg.le hx⟩ : L))⁻¹ * ⟨x, hcfg.le hx⟩ ^ (2 ^ k) ∈
      P.subgroupOf L := mul_mem (inv_mem hαx) (pow_mem hx' _)
  have hdisj : (U : Subgroup L) ⊓ P.subgroupOf L = ⊥ := by
    refine disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard ?_)
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 U.isPGroup'
    rw [hm, hP']
    exact Nat.Coprime.pow_left m (by norm_num)
  have h3 : (MulAut.conjNormal t (⟨x, hcfg.le hx⟩ : L))⁻¹ * ⟨x, hcfg.le hx⟩ ^ (2 ^ k) = 1 := by
    have h13 : _ ∈ (U : Subgroup L) ⊓ P.subgroupOf L := ⟨h1, h2⟩
    rwa [hdisj, Subgroup.mem_bot] at h13
  have h5 := congrArg Subtype.val (inv_mul_eq_one.1 h3)
  rw [MulAut.conjNormal_apply] at h5
  simpa using h5

end CFSG.Quasithin.S146zY
