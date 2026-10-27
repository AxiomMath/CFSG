module

public import CFSG.LocalAnalysis.WeakClosure81.EightTwelveDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup

variable {G : Type} [Group G]

theorem wcgapsp_eq_one_of_pow_two_eq_one_of_odd_card {H : Type*} [Group H] [Finite H]
    (hodd : Odd (Nat.card H)) {x : H} (hx : ∃ k : ℕ, x ^ 2 ^ k = 1) : x = 1 := by
  obtain ⟨k, hk⟩ := hx
  have hdvd2 : orderOf x ∣ 2 ^ k := orderOf_dvd_iff_pow_eq_one.mpr hk
  have hdvdH : orderOf x ∣ Nat.card H := orderOf_dvd_natCard x
  have hoddx : Odd (orderOf x) := hodd.of_dvd_nat hdvdH
  obtain ⟨j, -, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd2
  rw [hjeq] at hoddx
  have hj0 : j = 0 := by
    by_contra hjne
    have heven : Even (2 ^ j) := by
      rw [even_iff_two_dvd]
      exact dvd_pow_self 2 hjne
    exact (Nat.not_even_iff_odd.mpr hoddx) heven
  rw [hj0, pow_zero] at hjeq
  exact orderOf_eq_one_iff.mp hjeq

private def wcgapsp_oTwoSet (K : Subgroup G) : Set (Subgroup G) :=
  {W | (⊥ : Subgroup G) ≤ W ∧ W ≤ K ∧ (W.subgroupOf K).Normal ∧
    ∀ w ∈ W, ∃ k : ℕ, w ^ 2 ^ k ∈ (⊥ : Subgroup G)}

theorem wcgapsp_le_oTwoMod_of_isPGroup {K W : Subgroup G} (hWK : W ≤ K)
    (hWn : (W.subgroupOf K).Normal) (hW2 : IsPGroup 2 W) :
    W ≤ oTwoMod (⊥ : Subgroup G) K := by
  refine le_iSup₂ (f := fun (W : Subgroup G) (_ : W ∈ wcgapsp_oTwoSet K) => W) W
    ⟨bot_le, hWK, hWn, ?_⟩
  intro w hw
  obtain ⟨k, hk⟩ := hW2 ⟨w, hw⟩
  exact ⟨k, Subgroup.mem_bot.mpr (Subtype.ext_iff.mp hk)⟩

theorem wcgapsp_le_of_surj_simple {K P Q R : Subgroup G} [Finite G]
    (hKP : K ≤ P) (hQn : (Q.subgroupOf P).Normal) (hQodd : Odd (Q.relIndex P))
    (hRK : R ≤ K) (hR2 : IsPGroup 2 R)
    {H : Type*} [Group H] (q : ↥K →* H) (hq : Function.Surjective q)
    (hqker : q.ker = R.subgroupOf K) (hHsimple : IsSimpleGroup H)
    (hHeven : Even (Nat.card H)) : K ≤ Q := by
  haveI : (Q.subgroupOf P).Normal := hQn
  have hRn : (R.subgroupOf K).Normal := hqker ▸ MonoidHom.normal_ker q
  let ψ : ↥K →* (↥P ⧸ (Q.subgroupOf P)) :=
    (QuotientGroup.mk' (Q.subgroupOf P)).comp (Subgroup.inclusion hKP)
  have hψk : ∀ k : ↥K, ψ k = QuotientGroup.mk' (Q.subgroupOf P) ⟨(k : G), hKP k.2⟩ :=
    fun k => rfl
  have hker : q.ker ≤ ψ.ker := by
    rw [hqker]
    intro r hr
    rw [MonoidHom.mem_ker]
    have hrR : (r : G) ∈ R := hr
    obtain ⟨k, hk⟩ := hR2 ⟨(r : G), hrR⟩
    have hk' : (r : G) ^ 2 ^ k = 1 := Subtype.ext_iff.mp hk
    have hodd : Odd (Nat.card (↥P ⧸ (Q.subgroupOf P))) := hQodd
    have hψ : ψ r = 1 := by
      rw [hψk]
      refine wcgapsp_eq_one_of_pow_two_eq_one_of_odd_card hodd ⟨k, ?_⟩
      rw [← map_pow]
      rw [show (⟨(r : G), hKP r.2⟩ : ↥P) ^ 2 ^ k = 1 from Subtype.ext hk', map_one]
    simpa using hψ
  let χ : H →* (↥P ⧸ (Q.subgroupOf P)) :=
    q.liftOfRightInverse (Function.surjInv hq) (Function.rightInverse_surjInv hq) ⟨ψ, hker⟩
  have hχq : ∀ k : ↥K, χ (q k) = ψ k := fun k =>
    q.liftOfRightInverse_comp_apply _ _ ⟨ψ, hker⟩ k
  have hχ1 : χ = 1 := by
    rcases hHsimple.eq_bot_or_eq_top_of_normal χ.ker with h | h
    · exfalso
      have hinj : Function.Injective χ := (MonoidHom.ker_eq_bot_iff χ).mp h
      have hdvd : Nat.card H ∣ Nat.card (↥P ⧸ (Q.subgroupOf P)) :=
        Subgroup.card_dvd_of_injective χ hinj
      have hcard : Nat.card (↥P ⧸ (Q.subgroupOf P)) = Q.relIndex P := rfl
      rw [hcard] at hdvd
      exact (Nat.not_even_iff_odd.mpr hQodd) (hHeven.trans_dvd hdvd)
    · exact (MonoidHom.ker_eq_top_iff).mp h
  intro k hk
  have h1 : ψ ⟨k, hk⟩ = 1 := by
    rw [← hχq ⟨k, hk⟩, hχ1, MonoidHom.one_apply]
  rw [hψk] at h1
  exact (QuotientGroup.eq_one_iff (⟨k, hKP hk⟩ : ↥P)).mp h1

theorem wcgapsp_oddResMod_le_of_mem {G : Type} [Group G] {P K : Subgroup G}
    (h : (⊥ : Subgroup G) ≤ K) (hKP : K ≤ P) (hn : (K.subgroupOf P).Normal)
    (ho : Odd (K.relIndex P)) : oddResMod (⊥ : Subgroup G) P ≤ K := by
  rw [oddResMod]
  exact iInf_le_of_le K (iInf_le_of_le ⟨h, hKP, hn, ho⟩ le_rfl)

end CFSG.LocalAnalysis.WeakClosure81

end
