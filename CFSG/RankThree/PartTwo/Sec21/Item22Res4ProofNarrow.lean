module

public import CFSG.RankThree.PartTwo.Sec21.Item22Res4ProofFamilies
public import CFSG.RankThree.PartTwo.KFacts.KP4
import CFSG.RankThree.PartTwo.Sec4.Item426A6U43
import CFSG.RankThree.PartTwo.Sec21.Item223CensusProofFamilies

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open scoped commutatorElement

@[expose] def Census228AltNine : Prop :=
  Census228Fact (alternatingGroup (Fin 9))

@[expose] def Census228SporRest : Prop :=
  (∀ s ∈ ([.M11, .M12, .J2, .J3, .McL] : List TauCeti.SporadicName),
      Census228Fact (Blueprint.NativeSporadic.Carrier s)) ∧
  ∀ s ∈ ([.J3, .McL, .ONan] : List TauCeti.SporadicName), ∀ (Y : Type) [Group Y] [Finite Y],
    Sec4.IsExtOf Y (Blueprint.NativeSporadic.Carrier s) (Multiplicative (ZMod 3)) →
      Census228Fact Y

@[expose] def Census228CharThreeLin : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y],
    (Nonempty (Y ≃* projSL 3 (GaloisField 3 2)) ∨ Nonempty (Y ≃* projSU 3 3 2) ∨
      Nonempty (Y ≃* projSL 4 (GaloisField 3 1))) → Census228Fact Y

namespace Item22Res4Proof

theorem noL2Normal228_of_hom {S T : Type} [Group S] [Group T] (f : S →* T)
    (hker : f.ker = Subgroup.center S) (h5 : ¬ 5 ∣ Nat.card (Subgroup.center S))
    (hT : ∀ x : T, orderOf x = 3 → ¬ 5 ∣ Nat.card (Subgroup.centralizer ({x} : Set T))) :
    NoL2Normal228 S := by
  intro y N Kb m hyZ hy3 hcomm _ hKbN ⟨eK⟩ hm he _
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h5K : 5 ∣ Nat.card Kb := by
    rw [Nat.card_congr eK.toEquiv]
    exact five_dvd_card_projSL_two hm he
  have : Finite Kb := by
    apply Nat.finite_of_card_ne_zero
    intro h0
    rw [Nat.card_congr eK.toEquiv, card_projSL_two m hm] at h0
    have h1 : 1 < 2 ^ m := Nat.one_lt_two_pow (by omega)
    have h2 : 1 < (2 ^ m) ^ 2 := by nlinarith
    rcases Nat.mul_eq_zero.mp h0 with h | h <;> omega
  obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' 5 h5K
  have hk5 : orderOf (k : S) = 5 := by rw [Subgroup.orderOf_coe, hk]
  have hyk : y * k = k * y := hcomm k (hKbN k.2)
  have hx3 : f y ^ 3 = 1 := by
    rw [← map_pow, ← MonoidHom.mem_ker, hker]
    exact hy3
  have hx1 : f y ≠ 1 := fun h => hyZ (hker ▸ MonoidHom.mem_ker.mpr h)
  have hxo : orderOf (f y) = 3 := orderOf_eq_prime hx3 hx1
  have hfk1 : f k ≠ 1 := by
    intro h
    have hkZ : (k : S) ∈ Subgroup.center S := hker ▸ MonoidHom.mem_ker.mpr h
    apply h5
    have := orderOf_dvd_natCard (⟨k, hkZ⟩ : Subgroup.center S)
    rwa [Subgroup.orderOf_mk, hk5] at this
  have hfk5 : orderOf (f k) = 5 := by
    refine orderOf_eq_prime ?_ hfk1
    rw [← map_pow, ← hk5, pow_orderOf_eq_one, map_one]
  have hmem : f k ∈ Subgroup.centralizer ({f y} : Set T) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hyk]
  apply hT (f y) hxo
  have := orderOf_dvd_natCard (⟨f k, hmem⟩ : Subgroup.centralizer ({f y} : Set T))
  rwa [Subgroup.orderOf_mk, hfk5] at this

theorem not_five_dvd_centralizer_of_no15 {T : Type} [Group T] [Finite T]
    (h15 : ∀ g : T, orderOf g ≠ 15) {x : T} (hx : orderOf x = 3) :
    ¬ 5 ∣ Nat.card (Subgroup.centralizer ({x} : Set T)) := by
  intro h5
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 5 h5
  have hco : Commute x (c : T) := (Subgroup.mem_centralizer_singleton_iff.mp c.2).symm
  apply h15 (x * c)
  rw [hco.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hx, Subgroup.orderOf_coe, hc]; norm_num),
    hx, Subgroup.orderOf_coe, hc]

theorem isPerfect_of_simple {S : Type*} [Group S] [IsSimpleGroup S] {a b : S}
    (hab : a * b ≠ b * a) : Group.IsPerfect S := by
  rw [Group.isPerfect_def]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator S) with h | h
  · exfalso
    apply hab
    have hc : ⁅a, b⁆ ∈ commutator S :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rwa [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
  · exact h

theorem exists_ne_comm_of_center_eq_bot {S : Type*} [Group S] [Nontrivial S]
    (hZ : Subgroup.center S = ⊥) : ∃ a b : S, a * b ≠ b * a := by
  obtain ⟨a, ha⟩ := exists_ne (1 : S)
  have haZ : a ∉ Subgroup.center S := by rw [hZ, Subgroup.mem_bot]; exact ha
  rw [Subgroup.mem_center_iff] at haZ
  push Not at haZ
  obtain ⟨b, hb⟩ := haZ
  exact ⟨a, b, fun h => hb h.symm⟩

theorem exists_hom_of_isExtOf {Y T : Type} [Group Y] [Group T] [Group.IsPerfect T]
    (hZT : Subgroup.center T = ⊥) (h : Sec4.IsExtOf Y T (Multiplicative (ZMod 3))) :
    ∃ f : Y →* T, f.ker = Subgroup.center Y ∧ Nat.card (Subgroup.center Y) = 3 := by
  obtain ⟨K, hK, ⟨eK⟩, ⟨eQ⟩⟩ := h
  have h3 : Nat.card K = 3 := by
    rw [Nat.card_congr eK.toEquiv, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
      ZMod.card]
  have : Group.IsPerfect (Y ⧸ K) := Group.IsPerfect.ofSurjective (f := eQ.symm.toMonoidHom)
    eQ.symm.surjective
  have hKZ : K ≤ Subgroup.center Y := Item223CensusProof.le_center_of_card_eq_three h3
  set f : Y →* T := eQ.toMonoidHom.comp (QuotientGroup.mk' K) with hf
  have hfs : Function.Surjective f :=
    eQ.surjective.comp (QuotientGroup.mk'_surjective K)
  have hker : f.ker = K := by
    ext z
    rw [MonoidHom.mem_ker, hf, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hZK : Subgroup.center Y ≤ K := by
    intro z hz
    rw [← hker, MonoidHom.mem_ker]
    have : f z ∈ Subgroup.center T := by
      rw [Subgroup.mem_center_iff]
      intro t
      obtain ⟨w, rfl⟩ := hfs t
      rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz w)]
    rwa [hZT, Subgroup.mem_bot] at this
  have hKeq : K = Subgroup.center Y := le_antisymm hKZ hZK
  exact ⟨f, hker.trans hKeq, hKeq ▸ h3⟩

theorem orderOf_perm_ne_fifteen {n : ℕ} (hn : n ≤ 7) (σ : Equiv.Perm (Fin n)) :
    orderOf σ ≠ 15 := by
  intro h15
  have hdvd : ∀ b ∈ σ.cycleType, b ∣ 15 := fun b hb => h15 ▸ Equiv.Perm.dvd_of_mem_cycleType hb
  have hsum : σ.cycleType.sum ≤ 7 :=
    (Equiv.Perm.sum_cycleType_le σ).trans (by simpa using hn)
  have hex : ∀ p : ℕ, p.Prime → p ∣ 15 → ∃ b ∈ σ.cycleType, p ∣ b := by
    intro p hp hp15
    by_contra hcon
    push Not at hcon
    obtain ⟨k, hk⟩ := hp15
    have hl : σ.cycleType.lcm ∣ k := Multiset.lcm_dvd.mpr fun b hb =>
      Nat.Coprime.dvd_of_dvd_mul_left ((Nat.Prime.coprime_iff_not_dvd hp).mpr (hcon b hb)).symm
        (hk ▸ hdvd b hb)
    rw [Equiv.Perm.lcm_cycleType, h15] at hl
    have hk0 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · rw [h0, mul_zero] at hk; norm_num at hk
      · exact h0
    have h1 := Nat.le_of_dvd hk0 hl
    have h2 : 2 * k ≤ p * k := Nat.mul_le_mul_right k hp.two_le
    omega
  obtain ⟨a, ha, h3a⟩ := hex 3 Nat.prime_three (by norm_num)
  obtain ⟨b, hb, h5b⟩ := hex 5 Nat.prime_five (by norm_num)
  have ha2 := Equiv.Perm.two_le_of_mem_cycleType ha
  have hb2 := Equiv.Perm.two_le_of_mem_cycleType hb
  have ha3 : 3 ≤ a := Nat.le_of_dvd (by omega) h3a
  have hb5 : 5 ≤ b := Nat.le_of_dvd (by omega) h5b
  by_cases hab : a = b
  · subst hab
    have h15a : 15 ∣ a := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h3a h5b
    have := Nat.le_of_dvd (by omega) h15a
    have := Multiset.le_sum_of_mem ha
    omega
  · obtain ⟨t, ht⟩ := Multiset.exists_cons_of_mem ha
    have hbt : b ∈ t := by
      rw [ht, Multiset.mem_cons] at hb
      exact hb.resolve_left (Ne.symm hab)
    have h1 : σ.cycleType.sum = a + t.sum := by rw [ht, Multiset.sum_cons]
    have h2 := Multiset.le_sum_of_mem hbt
    omega

theorem orderOf_alternating_ne_fifteen {n : ℕ} (hn : n ≤ 7) (g : alternatingGroup (Fin n)) :
    orderOf g ≠ 15 := by
  rw [← Subgroup.orderOf_coe]
  exact orderOf_perm_ne_fifteen hn _

theorem center_eq_bot_and_isPerfect_alternating {n : ℕ} (hn : 5 ≤ n) :
    Subgroup.center (alternatingGroup (Fin n)) = ⊥ ∧
      Group.IsPerfect (alternatingGroup (Fin n)) := by
  have hZ := alternatingGroup.center_eq_bot (α := Fin n) (by rw [Nat.card_fin]; omega)
  have : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; omega)
  have : Nontrivial (alternatingGroup (Fin n)) :=
    alternatingGroup.nontrivial_of_three_le_card (by rw [Nat.card_fin]; omega)
  obtain ⟨a, b, hab⟩ := exists_ne_comm_of_center_eq_bot hZ
  exact ⟨hZ, isPerfect_of_simple hab⟩

theorem census228Fact_alternating {n : ℕ} (hn : n ≤ 7) :
    Census228Fact (alternatingGroup (Fin n)) := by
  right
  rcases Nat.lt_or_ge n 5 with hn5 | hn5
  · intro y N Kb m _ _ _ _ hKbN ⟨eK⟩ hm he _
    have h5 : 5 ∣ Nat.card Kb := by
      rw [Nat.card_congr eK.toEquiv]
      exact five_dvd_card_projSL_two hm he
    have hdvd := h5.trans ((Subgroup.card_dvd_of_le (hKbN.trans le_top)).trans
      ((Subgroup.card_top (G := alternatingGroup (Fin n))).symm ▸
        (Subgroup.card_subgroup_dvd_card (alternatingGroup (Fin n))).trans
          (by rw [Nat.card_perm, Nat.card_fin])))
    interval_cases n <;> revert hdvd <;> decide
  · obtain ⟨hZ, -⟩ := center_eq_bot_and_isPerfect_alternating hn5
    refine noL2Normal228_of_hom (MonoidHom.id _) (by rw [MonoidHom.ker_id, hZ]) ?_
      fun x hx => not_five_dvd_centralizer_of_no15 (orderOf_alternating_ne_fifteen hn) hx
    rw [hZ, Subgroup.card_bot]
    norm_num

theorem census228Fact_alternating_cover {Y : Type} [Group Y] {n : ℕ} (hn5 : 5 ≤ n) (hn : n ≤ 7)
    (h : Sec4.IsExtOf Y (alternatingGroup (Fin n)) (Multiplicative (ZMod 3))) :
    Census228Fact Y := by
  obtain ⟨hZ, hP⟩ := center_eq_bot_and_isPerfect_alternating hn5
  obtain ⟨f, hker, h3⟩ := exists_hom_of_isExtOf hZ h
  exact Or.inr (noL2Normal228_of_hom f hker (by rw [h3]; norm_num)
    fun x hx => not_five_dvd_centralizer_of_no15 (orderOf_alternating_ne_fifteen hn) hx)

section M22


theorem m22_not_five_dvd {x : Blueprint.NativeSporadic.Carrier .M22} (hx : orderOf x = 3) :
    ¬ 5 ∣ Nat.card (Subgroup.centralizer ({x} : Set (Blueprint.NativeSporadic.Carrier .M22))) := by
  rw [(KFacts.KP4.m22_centralizer_facts_of_orderOf
    (L := Blueprint.NativeSporadic.Carrier .M22) ⟨MulEquiv.refl _⟩ hx).1]
  norm_num

theorem m22_center_eq_bot_and_isPerfect :
    Subgroup.center (Blueprint.NativeSporadic.Carrier .M22) = ⊥ ∧
      Group.IsPerfect (Blueprint.NativeSporadic.Carrier .M22) := by
  have : Finite (Blueprint.NativeSporadic.Carrier .M22) :=
    CFSG.Sporadic.Mathieu.fam_m22_simplicity.1
  have : Nontrivial (Blueprint.NativeSporadic.Carrier .M22) :=
    CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.1
  have : IsSimpleGroup (Blueprint.NativeSporadic.Carrier .M22) :=
    CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card (Blueprint.NativeSporadic.Carrier .M22) = 443520 :=
    CFSG.Sporadic.Mathieu.card_M22
  have hZ : Subgroup.center (Blueprint.NativeSporadic.Carrier .M22) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.center (Blueprint.NativeSporadic.Carrier .M22)) with hb | ht
    · exact hb
    · exfalso
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card'
        (G := Blueprint.NativeSporadic.Carrier .M22) 3 (by rw [hcard]; norm_num)
      have h36 := (KFacts.KP4.m22_centralizer_facts_of_orderOf
        (L := Blueprint.NativeSporadic.Carrier .M22) ⟨MulEquiv.refl _⟩ hx).1
      have htop : Subgroup.centralizer ({x} : Set (Blueprint.NativeSporadic.Carrier .M22)) =
          ⊤ := by
        rw [eq_top_iff]
        intro g _
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_center_iff.mp (ht ▸ Subgroup.mem_top x) g)
      rw [htop, Subgroup.card_top, hcard] at h36
      norm_num at h36
  obtain ⟨a, b, hab⟩ := exists_ne_comm_of_center_eq_bot hZ
  exact ⟨hZ, isPerfect_of_simple hab⟩

theorem census228Fact_m22 : Census228Fact (Blueprint.NativeSporadic.Carrier .M22) := by
  obtain ⟨hZ, -⟩ := m22_center_eq_bot_and_isPerfect
  refine Or.inr (noL2Normal228_of_hom (MonoidHom.id _) (by rw [MonoidHom.ker_id, hZ]) ?_
    fun x hx => m22_not_five_dvd hx)
  rw [hZ, Subgroup.card_bot]
  norm_num

theorem census228Fact_m22_cover {Y : Type} [Group Y]
    (h : Sec4.IsExtOf Y (Blueprint.NativeSporadic.Carrier .M22) (Multiplicative (ZMod 3))) :
    Census228Fact Y := by
  obtain ⟨hZ, hP⟩ := m22_center_eq_bot_and_isPerfect
  obtain ⟨f, hker, h3⟩ := exists_hom_of_isExtOf hZ h
  exact Or.inr (noL2Normal228_of_hom f hker (by rw [h3]; norm_num) fun x hx => m22_not_five_dvd hx)

end M22

theorem pRank_le_one_of_not_nine_dvd {S : Type} [Group S] [Finite S]
    (h : ¬ 9 ∣ Nat.card S) : CFSG.pRank 3 (S ⧸ Subgroup.center S) ≤ 1 := by
  refine csSup_le' ?_
  rintro r ⟨B, -, hr⟩
  by_contra hr1
  apply h
  have h9 : 9 ∣ Nat.card B := by
    rw [hr, show (9 : ℕ) = 3 ^ 2 by norm_num]
    exact pow_dvd_pow 3 (by omega)
  exact h9.trans ((Subgroup.card_subgroup_dvd_card B).trans
    (Subgroup.card_quotient_dvd_card _))

theorem census228Fact_j1 :
    Census228Fact (Blueprint.NativeSporadic.Carrier .J1) := by
  have hfin : Finite (Blueprint.NativeSporadic.Carrier .J1) :=
    CFSG.Sporadic.J1.fam_j1_simplicity.1
  refine Or.inl (pRank_le_one_of_not_nine_dvd ?_)
  rw [show Nat.card (Blueprint.NativeSporadic.Carrier .J1) = 175560 from
    CFSG.Sporadic.J1.card_J1]
  norm_num

theorem census228Fact_u43_cover {Y : Type} [Group Y] [Finite Y]
    (hZ3 : Nat.card (Subgroup.center Y) ≤ 3) (e : Y ⧸ Subgroup.center Y ≃* projSU 4 3 1) :
    Census228Fact Y := by
  refine Or.inr (noL2Normal228_of_hom (e.toMonoidHom.comp (QuotientGroup.mk' _)) ?_ ?_
    fun x hx => Sec4.Item426.u43ThreeCentralizer x hx)
  · ext z
    rw [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  · intro h5
    have := Nat.le_of_dvd Nat.card_pos h5
    omega

end Item22Res4Proof

open Item22Res4Proof

theorem census228Alt_of (h : Census228AltNine) : Census228Alt := by
  refine ⟨fun n hn hn8 => ?_, fun Y _ _ hY => ?_⟩
  · rcases (show n ≤ 7 ∨ n = 9 by omega) with h7 | rfl
    · exact census228Fact_alternating h7
    · exact h
  · rcases hY with hA6 | hA7
    · exact census228Fact_alternating_cover (by norm_num) (by norm_num) hA6
    · exact census228Fact_alternating_cover (by norm_num) (by norm_num) hA7

theorem census228Spor_of
    (h : Census228SporRest) : Census228Spor := by
  refine ⟨fun s hs hsS => ?_, fun s hs Y _ _ hY => ?_⟩
  · simp only [Sec4.sporadics46, List.mem_cons, List.mem_nil_iff, or_false] at hs
    simp only [sporadicsStar228, List.mem_cons, List.mem_nil_iff, or_false] at hsS
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h.1 _ (by simp)
    · exact h.1 _ (by simp)
    · exact census228Fact_m22
    · exact (hsS (Or.inl rfl)).elim
    · exact (hsS (by simp)).elim
    · exact census228Fact_j1
    · exact h.1 _ (by simp)
    · exact h.1 _ (by simp)
    · exact (hsS (by simp)).elim
    · exact h.1 _ (by simp)
    · exact (hsS (by simp)).elim
    · exact (hsS (by simp)).elim
    · exact (hsS (by simp)).elim
  · simp only [Sec4.sporadicCovers46, List.mem_cons, List.mem_nil_iff, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact census228Fact_m22_cover hY
    · exact h.2 _ (by simp) Y hY
    · exact h.2 _ (by simp) Y hY
    · exact h.2 _ (by simp) Y hY

theorem census228CharThree_of (h : Census228CharThreeLin) : Census228CharThree := by
  intro Y _ _ hY
  rcases hY with h1 | h2 | h3 | ⟨hZ3, ⟨e⟩⟩
  · exact h Y (Or.inl h1)
  · exact h Y (Or.inr (Or.inl h2))
  · exact h Y (Or.inr (Or.inr h3))
  · exact census228Fact_u43_cover hZ3 e

end CFSG.RankThree.PartTwo.Sec21
