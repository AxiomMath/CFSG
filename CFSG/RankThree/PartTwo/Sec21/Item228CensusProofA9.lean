module

public import CFSG.RankThree.PartTwo.Sec21.Item22Res4ProofNarrow
import CFSG.RankThree.PartTwo.Sec21.Item223CensusProofA9

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open Equiv

namespace Item228CensusProof

theorem apply_eq_self_or_of_commute {σ κ : Perm (Fin 9)} (hσ : σ ^ 3 = 1) (hκ : κ ^ 5 = 1)
    (hc : Commute σ κ) (x : Fin 9) : σ x = x ∨ κ x = x := by
  have h15 : (σ * κ) ^ 15 = 1 := by
    rw [hc.mul_pow, show 15 = 3 * 5 by rfl, pow_mul, hσ, one_pow, one_mul, pow_mul', hκ, one_pow]
  have hper : Function.IsPeriodicPt (σ * κ) 15 x := by
    change (⇑(σ * κ))^[15] x = x
    rw [Perm.iterate_eq_pow, h15, Perm.one_apply]
  have hdvd := hper.minimalPeriod_dvd
  have hle : Function.minimalPeriod (σ * κ) x ≤ 9 := by
    have := Function.minimalPeriod_le_card (f := ⇑(σ * κ)) (x := x)
    simpa using this
  have hfix : ∀ n : ℕ, Function.minimalPeriod (σ * κ) x ∣ n → ((σ * κ) ^ n) x = x := by
    intro n hn
    have := Function.isPeriodicPt_iff_minimalPeriod_dvd.mpr hn
    change (⇑(σ * κ))^[n] x = x at this
    rwa [Perm.iterate_eq_pow] at this
  have hcases : Function.minimalPeriod (σ * κ) x ∣ 5 ∨
      Function.minimalPeriod (σ * κ) x ∣ 3 := by
    generalize Function.minimalPeriod (σ * κ) x = d at hdvd hle
    interval_cases d <;> revert hdvd <;> decide
  rcases hcases with h5 | h3
  · left
    have hx := hfix 5 h5
    have h2 : (σ * κ) ^ 5 = σ ^ 2 := by
      rw [hc.mul_pow, hκ, mul_one, show 5 = 3 + 2 by rfl, pow_add, hσ, one_mul]
    rw [h2] at hx
    have hσ4 : σ = σ ^ 2 * σ ^ 2 := by
      rw [← pow_add, show 2 + 2 = 3 + 1 by rfl, pow_add, hσ, one_mul, pow_one]
    rw [hσ4, Perm.mul_apply, hx, hx]
  · right
    have hx := hfix 3 h3
    have h3' : (σ * κ) ^ 3 = κ ^ 3 := by rw [hc.mul_pow, hσ, one_mul]
    rw [h3'] at hx
    have hκ6 : κ = κ ^ 3 * κ ^ 3 := by
      rw [← pow_add, show 3 + 3 = 5 + 1 by rfl, pow_add, hκ, one_mul, pow_one]
    rw [hκ6, Perm.mul_apply, hx, hx]

theorem five_le_card_support {κ : Perm (Fin 9)} (hκ : orderOf κ = 5) : 5 ≤ κ.support.card := by
  have hne : κ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hκ
    norm_num at hκ
  have hct : κ.cycleType ≠ 0 := by rwa [Ne, Perm.cycleType_eq_zero]
  obtain ⟨n, hn⟩ := Multiset.exists_mem_of_ne_zero hct
  have hn5 : n ∣ 5 := hκ ▸ Perm.dvd_of_mem_cycleType hn
  have hn2 := Perm.two_le_of_mem_cycleType hn
  have hn5' : n = 5 := by
    rcases (Nat.dvd_prime Nat.prime_five).mp hn5 with h | h <;> omega
  rw [← Perm.sum_cycleType]
  exact hn5' ▸ Multiset.le_sum_of_mem hn

theorem card_support_eq_three {σ : Perm (Fin 9)} (hσ : orderOf σ = 3)
    (h4 : σ.support.card ≤ 4) : σ.support.card = 3 := by
  have hne : σ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hσ
    norm_num at hσ
  have hct : σ.cycleType ≠ 0 := by rwa [Ne, Perm.cycleType_eq_zero]
  have hmem : ∀ n ∈ σ.cycleType, n = 3 := by
    intro n hn
    have h1 : n ∣ 3 := hσ ▸ Perm.dvd_of_mem_cycleType hn
    have h2 := Perm.two_le_of_mem_cycleType hn
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h <;> omega
  have hrep : σ.cycleType = Multiset.replicate (Multiset.card σ.cycleType) 3 :=
    Multiset.eq_replicate.mpr ⟨rfl, hmem⟩
  have hc0 : Multiset.card σ.cycleType ≠ 0 := fun h => hct (Multiset.card_eq_zero.mp h)
  rw [← Perm.sum_cycleType] at h4 ⊢
  rw [hrep, Multiset.sum_replicate, smul_eq_mul] at h4 ⊢
  omega

theorem card_support_eq_three_of_commute {σ κ : Perm (Fin 9)} (hσ : orderOf σ = 3)
    (hκ : orderOf κ = 5) (hc : Commute σ κ) : σ.support.card = 3 := by
  have hdisj : Disjoint σ.support κ.support := by
    rw [Finset.disjoint_left]
    intro x hxσ hxκ
    rw [Perm.mem_support] at hxσ hxκ
    rcases apply_eq_self_or_of_commute (hσ ▸ pow_orderOf_eq_one σ) (hκ ▸ pow_orderOf_eq_one κ)
      hc x with h | h
    · exact hxσ h
    · exact hxκ h
  have hcard : σ.support.card + κ.support.card ≤ 9 := by
    rw [← Finset.card_union_of_disjoint hdisj]
    exact (Finset.card_le_univ _).trans (by simp)
  have := five_le_card_support hκ
  exact card_support_eq_three hσ (by omega)

theorem apply_mem_support_iff_of_commute {σ τ : Perm (Fin 9)} (hc : Commute σ τ) (x : Fin 9) :
    τ x ∈ σ.support ↔ x ∈ σ.support := by
  rw [Perm.mem_support, Perm.mem_support, ← Perm.mul_apply, hc.eq, Perm.mul_apply, Ne, Ne,
    τ.injective.eq_iff]

theorem card_projSL_two_ne_360 {m : ℕ} (hm : 0 < m) :
    Nat.card (projSL 2 (GaloisField 2 m)) ≠ 360 := by
  rw [card_projSL_two m hm]
  intro h
  have hlt : m < 4 := by
    by_contra hge
    push Not at hge
    have h16 : 16 ≤ 2 ^ m := by
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hge
    have h255 : 255 ≤ (2 ^ m) ^ 2 - 1 := by
      have : 256 ≤ (2 ^ m) ^ 2 := by nlinarith
      omega
    have := Nat.mul_le_mul h16 h255
    omega
  interval_cases m <;> norm_num at h

theorem isSimpleGroup_and_card_ne_360 {S : Type} [Group S] {N Kb : Subgroup S} {m : ℕ}
    (eK : Kb ≃* projSL 2 (GaloisField 2 m)) (hm : 0 < m) (he : Even m)
    (hU : Kb = N ∨ StatedClassicalModel N .PSU 3 2 2) :
    IsSimpleGroup N ∧ Nat.card N ≠ 360 := by
  have hm2 : 2 ≤ m := by
    obtain ⟨r, hr⟩ := he
    omega
  rcases hU with heq | hU
  · subst heq
    have : IsSimpleGroup (projSL 2 (GaloisField 2 m)) := isSimpleGroup_projSL_two hm2
    exact ⟨eK.isSimpleGroup, by rw [Nat.card_congr eK.toEquiv]; exact card_projSL_two_ne_360 hm⟩
  · refine ⟨(CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity _ _ _ _ hU).2, ?_⟩
    rw [Item22Res4Proof.card_of_statedU34 hU]
    norm_num

@[expose] noncomputable def altEmbed (T : Finset (Fin 9)) :
    alternatingGroup T →* alternatingGroup (Fin 9) :=
  ((Perm.ofSubtype : Perm T →* Perm (Fin 9)).comp (alternatingGroup T).subtype).codRestrict
    (alternatingGroup (Fin 9)) fun g => by
      rw [MonoidHom.comp_apply, Perm.mem_alternatingGroup, Perm.sign_ofSubtype]
      exact g.2

theorem altEmbed_injective (T : Finset (Fin 9)) : Function.Injective (altEmbed T) := by
  intro a b h
  apply Subtype.ext
  apply Perm.ofSubtype_injective
  exact congrArg Subtype.val h

theorem coe_altEmbed (T : Finset (Fin 9)) (g : alternatingGroup T) :
    ((altEmbed T g : alternatingGroup (Fin 9)) : Perm (Fin 9)) = Perm.ofSubtype (g : Perm T) :=
  rfl

theorem noL2Normal228_alternatingGroup_nine : NoL2Normal228 (alternatingGroup (Fin 9)) := by
  intro y N Kb m hyZ hy3 hcomm hnorm hKbN ⟨eK⟩ hm he hU
  have : IsSimpleGroup (alternatingGroup (Fin 9)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; norm_num)
  have hZ : Subgroup.center (alternatingGroup (Fin 9)) = ⊥ :=
    Item223CensusProof.center_eq_bot_of_isSimpleGroup
      (by rw [Item223CensusProof.card_alternatingGroup_nine]; norm_num)
  rw [hZ, Subgroup.mem_bot] at hyZ hy3
  have hyo : orderOf y = 3 := orderOf_eq_prime hy3 hyZ
  obtain ⟨hNs, hN360⟩ := isSimpleGroup_and_card_ne_360 eK hm he hU
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h5K : 5 ∣ Nat.card Kb := by
    rw [Nat.card_congr eK.toEquiv]
    exact Item22Res4Proof.five_dvd_card_projSL_two hm he
  obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' 5 h5K
  set σ : Perm (Fin 9) := ((y : alternatingGroup (Fin 9)) : Perm (Fin 9)) with hσdef
  set κ : Perm (Fin 9) := (((k : Kb) : alternatingGroup (Fin 9)) : Perm (Fin 9)) with hκdef
  have hσo : orderOf σ = 3 := by rw [hσdef, Subgroup.orderOf_coe, hyo]
  have hκo : orderOf κ = 5 := by rw [hκdef, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hk]
  have hcommP : ∀ g : alternatingGroup (Fin 9), g * y = y * g →
      Commute σ (g : Perm (Fin 9)) := by
    intro g hg
    have h1 := congrArg (fun z : alternatingGroup (Fin 9) => (z : Perm (Fin 9))) hg
    simp only [Subgroup.coe_mul] at h1
    exact h1.symm
  have hcN : ∀ n ∈ N, Commute σ ((n : alternatingGroup (Fin 9)) : Perm (Fin 9)) :=
    fun n hn => hcommP n (hcomm n hn).symm
  have hσκ : Commute σ κ := hcN _ (hKbN k.2)
  set S : Finset (Fin 9) := σ.support with hSdef
  have hS3 : S.card = 3 := card_support_eq_three_of_commute hσo hκo hσκ
  have hfixS : ∀ n ∈ N, ∀ x ∈ S, ((n : alternatingGroup (Fin 9)) : Perm (Fin 9)) x = x := by
    let M : Subgroup N :=
      { carrier := {n | ∀ x ∈ S, (((n : N) : alternatingGroup (Fin 9)) : Perm (Fin 9)) x = x}
        one_mem' := fun x _ => rfl
        mul_mem' := fun {a b} ha hb x hx => by
          simp only [Set.mem_ofPred_eq, Subgroup.coe_mul, Perm.mul_apply] at ha hb ⊢
          rw [hb x hx, ha x hx]
        inv_mem' := fun {a} ha x hx => by
          simp only [Set.mem_ofPred_eq, InvMemClass.coe_inv] at ha ⊢
          rw [Perm.inv_eq_iff_eq]
          exact (ha x hx).symm }
    have hMn : M.Normal := by
      refine ⟨fun n hn g x hx => ?_⟩
      simp only [M, Subgroup.mem_mk, Subgroup.coe_mul, InvMemClass.coe_inv, Perm.mul_apply]
        at hn ⊢
      have hgx : (((g⁻¹ : N) : alternatingGroup (Fin 9)) : Perm (Fin 9)) x ∈ S :=
        (apply_mem_support_iff_of_commute (hcN _ (g⁻¹ : N).2) x).mpr hx
      simp only [InvMemClass.coe_inv] at hgx
      rw [hn _ hgx, ← Perm.mul_apply, mul_inv_cancel, Perm.one_apply]
    have hkM : (⟨(k : alternatingGroup (Fin 9)), hKbN k.2⟩ : N) ∈ M := by
      intro x hx
      rcases apply_eq_self_or_of_commute (hσo ▸ pow_orderOf_eq_one σ)
        (hκo ▸ pow_orderOf_eq_one κ) hσκ x with h | h
      · exact absurd h (Perm.mem_support.mp hx)
      · exact h
    have hMtop : M = ⊤ := by
      rcases hMn.eq_bot_or_eq_top with hb | ht
      · exfalso
        rw [hb, Subgroup.mem_bot] at hkM
        have hk1 : (k : alternatingGroup (Fin 9)) = 1 := congrArg Subtype.val hkM
        have : (k : Kb) = 1 := Subtype.ext hk1
        rw [this, orderOf_one] at hk
        norm_num at hk
      · exact ht
    intro n hn x hx
    have : (⟨n, hn⟩ : N) ∈ M := hMtop ▸ Subgroup.mem_top _
    exact this x hx
  set T : Finset (Fin 9) := Sᶜ with hTdef
  have hT6 : T.card = 6 := by
    rw [hTdef, Finset.card_compl, hS3]
    rfl
  have hNle : N ≤ (altEmbed T).range := by
    intro n hn
    have hsupp : ((n : Perm (Fin 9)).support : Set (Fin 9)) ⊆ Set.ofPred (· ∈ T) := by
      intro x hx
      change x ∈ T
      rw [hTdef, Finset.mem_compl]
      intro hxS
      exact (Perm.mem_support.mp hx) (hfixS n hn x hxS)
    obtain ⟨g, hg⟩ := Perm.mem_range_ofSubtype_iff.mpr hsupp
    have hgA : g ∈ alternatingGroup T := by
      rw [Perm.mem_alternatingGroup, ← Perm.sign_ofSubtype, hg]
      exact n.2
    exact ⟨⟨g, hgA⟩, Subtype.ext hg⟩
  have hrange : ∀ g : alternatingGroup T, altEmbed T g * y = y * altEmbed T g := by
    intro g
    have hd : Perm.Disjoint (Perm.ofSubtype (g : Perm T)) σ := by
      intro x
      by_cases hx : x ∈ T
      · right
        rw [hTdef, Finset.mem_compl, hSdef, Perm.mem_support, not_not] at hx
        exact hx
      · left
        exact Perm.ofSubtype_apply_of_not_mem _ hx
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [coe_altEmbed]
    exact hd.commute.eq
  have hTs : IsSimpleGroup (alternatingGroup T) :=
    alternatingGroup.isSimpleGroup
      (by rw [Nat.card_eq_fintype_card, Fintype.card_coe, hT6]; norm_num)
  have hN'n : (N.comap (altEmbed T)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact hnorm _ (hrange g) _ hn
  have hN'top : N.comap (altEmbed T) = ⊤ := by
    rcases hN'n.eq_bot_or_eq_top with hb | ht
    · exfalso
      obtain ⟨⟨n, hn⟩, hn1⟩ := exists_ne (1 : N)
      obtain ⟨g, hg⟩ := hNle hn
      have hgN : g ∈ N.comap (altEmbed T) := by
        rw [Subgroup.mem_comap, hg]
        exact hn
      rw [hb, Subgroup.mem_bot] at hgN
      have hn1' : n = 1 := by rw [← hg, hgN, map_one]
      exact hn1 (Subtype.ext hn1')
    · exact ht
  have hNeq : N = (altEmbed T).range := by
    refine le_antisymm hNle ?_
    rintro _ ⟨g, rfl⟩
    have : g ∈ N.comap (altEmbed T) := hN'top ▸ Subgroup.mem_top g
    exact this
  have : Nontrivial T := by
    rw [← Finite.one_lt_card_iff_nontrivial, Nat.card_eq_fintype_card, Fintype.card_coe, hT6]
    norm_num
  apply hN360
  rw [hNeq, MonoidHom.range_eq_map, ← Nat.card_congr
    ((⊤ : Subgroup (alternatingGroup T)).equivMapOfInjective _ (altEmbed_injective T)).toEquiv,
    Subgroup.card_top, nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_coe,
    hT6]
  rfl

end Item228CensusProof

open Item228CensusProof

theorem census228AltNine_holds : Census228AltNine :=
  Or.inr noL2Normal228_alternatingGroup_nine

end CFSG.RankThree.PartTwo.Sec21
