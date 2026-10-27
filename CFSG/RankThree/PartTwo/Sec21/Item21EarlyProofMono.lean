module

public import CFSG.RankThree.PartTwo.Sec21.Item221ProofStatements
import CFSG.RankThree.PartTwo.KFacts.KP14MonomialStructure
import CFSG.RankThree.PartTwo.Sec21.Item2131One
import CFSG.RankThree.PartTwo.Sec6.Item612Local
import CFSG.RankThree.PartOne.KC.LinearSubfieldPointwise
import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
public import CFSG.RankThree.PartTwo.Sec21.Item21Statements

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

namespace Item21EarlyProof

section Linear

variable {P : Type*}

@[expose] def commHom [CommGroup P] (φ : MulAut P) : P →* P where
  toFun a := a⁻¹ * φ a
  map_one' := by rw [map_one, inv_one, one_mul]
  map_mul' a b := by
    rw [map_mul, mul_inv_rev, mul_comm b⁻¹ a⁻¹, mul_mul_mul_comm]

theorem commHom_apply [CommGroup P] (φ : MulAut P) (a : P) : commHom φ a = a⁻¹ * φ a := rfl

theorem commOf_eq_range [CommGroup P] (φ : MulAut P) : commOf φ = (commHom φ).range := by
  have h : (Set.range fun a : P => a⁻¹ * φ a) = ((commHom φ).range : Set P) :=
    (MonoidHom.coe_range (commHom φ)).symm
  rw [commOf, h, Subgroup.closure_eq]

theorem fixedSubgroupOf_eq_ker [CommGroup P] (φ : MulAut P) :
    fixedSubgroupOf φ = (commHom φ).ker := by
  ext x
  rw [mem_fixedSubgroupOf, MonoidHom.mem_ker, commHom_apply, inv_mul_eq_one]
  exact eq_comm

theorem commHom_cube [CommGroup P] (hP3 : ∀ x : P, x ^ 3 = 1) {φ : MulAut P}
    (hφ3 : φ ^ 3 = 1) (a : P) : commHom φ (commHom φ (commHom φ a)) = 1 := by
  set b := commHom φ a with hb
  have h3 : φ (φ (φ a)) = a := by
    have := congrArg (fun ψ : MulAut P => ψ a) hφ3
    simpa [pow_succ, MulAut.mul_apply] using this
  have hφa : φ a = a * b := by rw [hb, commHom_apply, mul_inv_cancel_left]
  have key : φ (φ b) = (b * φ b)⁻¹ := by
    rw [hφa, map_mul, hφa, map_mul, map_mul, hφa, mul_assoc, mul_assoc] at h3
    have h : b * φ b * φ (φ b) = 1 := by
      rw [mul_assoc]
      exact mul_left_cancel (h3.trans (mul_one a).symm)
    exact eq_inv_of_mul_eq_one_right h
  rw [commHom_apply, commHom_apply, map_mul, map_inv, key]
  set y := φ b
  calc (b⁻¹ * y)⁻¹ * (y⁻¹ * (b * y)⁻¹) = (y ^ 3)⁻¹ := by
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv, ofMul_pow]
        abel
    _ = 1 := by rw [hP3 y, inv_one]

theorem eq_bot_of_injOn [CommGroup P] [Finite P] (hP3 : ∀ x : P, x ^ 3 = 1) {φ : MulAut P}
    (hφ3 : φ ^ 3 = 1) {S : Subgroup P} (hS : ∀ s ∈ S, commHom φ s ∈ S)
    (hinj : ∀ s ∈ S, commHom φ s = 1 → s = 1) : S = ⊥ := by
  let g : S → S := fun s => ⟨commHom φ s, hS s s.2⟩
  have hg : Function.Injective g := by
    intro s t hst
    have h1 : commHom φ ((s : P) * (t : P)⁻¹) = 1 := by
      have h := congrArg Subtype.val hst
      change commHom φ (s : P) = commHom φ (t : P) at h
      rw [map_mul, map_inv, h, mul_inv_cancel]
    have h2 := hinj _ (S.mul_mem s.2 (S.inv_mem t.2)) h1
    exact Subtype.ext (mul_inv_eq_one.mp h2)
  have hgs : Function.Surjective g := Finite.surjective_of_injective hg
  rw [eq_bot_iff]
  intro s hs
  obtain ⟨s1, hs1⟩ := hgs ⟨s, hs⟩
  obtain ⟨s2, hs2⟩ := hgs s1
  obtain ⟨s3, hs3⟩ := hgs s2
  have e : s = commHom φ (commHom φ (commHom φ (s3 : P))) := by
    have h1 := congrArg Subtype.val hs1
    have h2 := congrArg Subtype.val hs2
    have h3 := congrArg Subtype.val hs3
    change commHom φ (s1 : P) = s at h1
    change commHom φ (s2 : P) = s1 at h2
    change commHom φ (s3 : P) = s2 at h3
    rw [h3, h2, h1]
  rw [Subgroup.mem_bot, e, commHom_cube hP3 hφ3]

theorem isTransvectionOn_of_inf_zpowers_eq_bot [Group P] [Finite P]
    (hP : ∀ x y : P, x * y = y * x) (hP3 : ∀ x : P, x ^ 3 = 1) (hcard : Nat.card P = 27)
    {φ : MulAut P} (hφ1 : φ ≠ 1) (hφ3 : φ ^ 3 = 1) {c : P} (hc1 : c ≠ 1) (hφc : φ c = c)
    (hcc : commOf φ ⊓ Subgroup.zpowers c = ⊥) : IsTransvectionOn φ := by
  let _ : CommGroup P := { (inferInstance : Group P) with mul_comm := hP }
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set ψ := commHom φ with hψ
  have hR : commOf φ = ψ.range := commOf_eq_range φ
  have hK : fixedSubgroupOf φ = ψ.ker := fixedSubgroupOf_eq_ker φ
  have hcK : c ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, hψ, commHom_apply, hφc, inv_mul_cancel]
  have hc3 : orderOf c = 3 := orderOf_eq_prime (hP3 c) hc1
  have hZc : Nat.card (Subgroup.zpowers c) = 3 := by rw [Nat.card_zpowers, hc3]
  have hmul : Nat.card ψ.ker * Nat.card ψ.range = 27 := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index, hcard]
  have h3K : 3 ∣ Nat.card ψ.ker := by
    rw [← hZc]
    exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hcK)
  have hRne : ψ.range ≠ ⊥ := by
    rw [← hR, Ne, commOf_eq_bot_iff]
    exact hφ1
  have hRinv : ∀ s ∈ ψ.range, ψ s ∈ ψ.range := fun s _ => ⟨s, rfl⟩
  have hRdvd : Nat.card ψ.range ∣ 3 ^ 3 := ⟨Nat.card ψ.ker, by rw [mul_comm, hmul]; norm_num⟩
  obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hRdvd
  interval_cases k
  · exact (hRne (Subgroup.eq_bot_of_card_eq _ (by simpa using hk))).elim
  ·
    have hR3 : Nat.card ψ.range = 3 := by simpa using hk
    have hnot : ¬ ∀ s ∈ ψ.range, ψ s = 1 → s = 1 := fun h =>
      hRne (eq_bot_of_injOn hP3 hφ3 hRinv h)
    push Not at hnot
    obtain ⟨s, hsR, hs1, hsne⟩ := hnot
    have hsK : s ∈ ψ.ker := hs1
    have hzs : Subgroup.zpowers s = ψ.range := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hsR) ?_
      rw [Nat.card_zpowers, orderOf_eq_prime (hP3 s) hsne, hR3]
    refine ⟨by rw [hR, hR3], ?_⟩
    rw [hR, hK, ← hzs]
    exact Subgroup.zpowers_le.mpr hsK
  ·
    exfalso
    have hR9 : Nat.card ψ.range = 9 := by simpa using hk
    have hK3 : Nat.card ψ.ker = 3 := by
      rw [hR9] at hmul
      omega
    have hKc : Subgroup.zpowers c = ψ.ker :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hcK) (by rw [hK3, hZc])
    refine hRne (eq_bot_of_injOn hP3 hφ3 hRinv fun s hsR hs1 => ?_)
    have hsc : s ∈ commOf φ ⊓ Subgroup.zpowers c := ⟨hR ▸ hsR, hKc ▸ hs1⟩
    rwa [hcc, Subgroup.mem_bot] at hsc
  ·
    exfalso
    have hK1 : Nat.card ψ.ker = 1 := by
      rw [hk] at hmul
      omega
    rw [hK1] at h3K
    omega

end Linear

variable {G : Type} [Group G]

theorem coe_mem_of_mem_commOf {A L : Subgroup G} (hA : IsMulCommutative A)
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) {w : MulAut A} (hw : w ∈ starOf A L)
    {x : A} (hx : x ∈ commOf w) : (x : G) ∈ L := by
  obtain ⟨a, rfl⟩ := (mem_commOf_iff hA w x).mp hx
  obtain ⟨⟨l, hlN⟩, hl, rfl⟩ := hw
  have hlL : l ∈ L := Subgroup.mem_subgroupOf.mp hl
  change (a : G)⁻¹ * (l * a * l⁻¹) ∈ L
  have h1 : (a : G)⁻¹ * l * a ∈ L := by
    have := (Subgroup.mem_normalizer_iff.mp (hAL (A.inv_mem a.2)) l).mp hlL
    simpa [mul_assoc] using this
  have h2 : (a : G)⁻¹ * (l * a * l⁻¹) = (a : G)⁻¹ * l * a * l⁻¹ := by group
  rw [h2]
  exact L.mul_mem h1 (L.inv_mem hlL)

theorem mem_of_zpow_mem [Finite G] {L : Subgroup G} {c : G} (hc3 : orderOf c = 3) {k : ℤ}
    (hk : c ^ k ∈ L) (hk1 : c ^ k ≠ 1) : c ∈ L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hck3 : (c ^ k) ^ 3 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hc3, pow_orderOf_eq_one,
      one_zpow]
  have hzk : Subgroup.zpowers (c ^ k) = Subgroup.zpowers c := by
    refine Subgroup.eq_of_le_of_card_ge
      (Subgroup.zpowers_le.mpr (Subgroup.zpow_mem_zpowers c k)) ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hck3 hk1, hc3]
  have hc : c ∈ Subgroup.zpowers (c ^ k) := hzk ▸ Subgroup.mem_zpowers c
  exact (Subgroup.zpowers_le.mpr hk) hc

theorem isTransvectionOn_of_mem_starOf [Finite G] (h45 : Sec4.Item4_5) {A E U L : Subgroup G}
    {c : G} (hpair : Sec21Pair G A E U c L) (hA27 : Nat.card A = 3 ^ 3) (hcL : c ∉ L)
    {w : MulAut A} (hwL : w ∈ starOf A L) (hw3 : orderOf w = 3) : IsTransvectionOn w := by
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hcA : c ∈ A := hpair.mem_E.2 hpairs.1.1
  have hc1 : c ≠ 1 := hpairs.2.1
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hpair.mem_S.1.1
  have hLc : L ∈ thetaComponentsAt 3 c := (lZeroStarAt_subset A c) hpairs.2.2.1
  have hLC : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hLc
  have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hpair.standing.toTheoremFourHyp hAe hcA hc1
      L hLc
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc3 : orderOf c = 3 := orderOf_eq_prime (hAe.2 c hcA) hc1
  refine isTransvectionOn_of_inf_zpowers_eq_bot (c := ⟨c, hcA⟩) (fun x y => hAe.1.is_comm.comm x y)
    (fun x => Subtype.ext (by simpa using hAe.2 x x.2)) (by rw [hA27]; norm_num)
    (fun h => by rw [h, orderOf_one] at hw3; omega)
    (by rw [← hw3, pow_orderOf_eq_one]) (fun h => hc1 (congrArg Subtype.val h))
    (Item2131One.apply_eq_of_mem_starOf hcA hLC hwL) ?_
  rw [eq_bot_iff]
  rintro x ⟨hxw, hxc⟩
  rw [Subgroup.mem_bot]
  by_contra hx1
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxc
  have hxL := coe_mem_of_mem_commOf hAe.1 hAL hwL hxw
  rw [Subgroup.coe_zpow] at hxL
  exact hcL (mem_of_zpow_mem hc3 hxL fun h => hx1 (Subtype.ext (by
    rw [Subgroup.coe_zpow, Subgroup.coe_one]
    exact h)))

theorem not_mem_of_center_lBar_eq_bot [Finite G] {L : Subgroup G} {c : G} (hc3 : orderOf c = 3)
    (hLC : L ≤ Subgroup.centralizer ({c} : Set G)) (hZ : Subgroup.center (lBar L) = ⊥) :
    c ∉ L := by
  intro hcL
  obtain ⟨-, -, hT3, -⟩ := solvable_prime_complement_core_characterization (H := L)
    Nat.prime_three
  set x : L := ⟨c, hcL⟩
  have hxZ : (x : lBar L) ∈ Subgroup.center (lBar L) := by
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hLC y.2))
  rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hxZ
  apply hT3
  have h := orderOf_dvd_natCard (⟨x, hxZ⟩ : aschbacherSolvableCore 3 L)
  rwa [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hc3] at h

theorem center_eq_bot_of_isSimpleGroup {X : Type*} [Group X] [IsSimpleGroup X]
    (hX : ∃ a b : X, a * b ≠ b * a) : Subgroup.center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · obtain ⟨a, b, hab⟩ := hX
    exact (hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)).elim

theorem exists_ne_comm_lBar [Finite G] {L : Subgroup G} {c : G}
    (hLc : L ∈ thetaComponentsAt 3 c) : ∃ a b : lBar L, a * b ≠ b * a := by
  obtain ⟨-, -, a, b, hab⟩ := Sec6.isQuasisimple_of_mem_thetaComponentsAt hLc
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  refine ⟨a, b, fun h => hab ?_⟩
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h]

theorem not_mem_of_lBar_equiv_projSL [Finite G] {L : Subgroup G} {c : G} (hc3 : orderOf c = 3)
    (hLc : L ∈ thetaComponentsAt 3 c) {F : Type} [Field F] (e : lBar L ≃* projSL 3 F) :
    c ∉ L := by
  have : IsSimpleGroup (projSL 3 F) := by
    have := CFSG.RankThree.PartOne.KCLinearSubfield.isSimpleGroup_projectiveSL (K := F) (n := 3)
      le_rfl
    exact (Sec4.projSLEquivProjectiveSL 3 F).isSimpleGroup
  have : IsSimpleGroup (lBar L) := e.isSimpleGroup
  exact not_mem_of_center_lBar_eq_bot hc3 (Sec6.le_centralizer_of_mem_thetaComponentsAt hLc)
    (center_eq_bot_of_isSimpleGroup (exists_ne_comm_lBar hLc))

theorem orderOf_cycle_three : orderOf (Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime (by decide) (by decide)

end Item21EarlyProof

open Item21EarlyProof

theorem item2131Two_of (h211 : Item211) (h2131One : Item2131One) (h218 : Item218)
    (h2116 : Item2116) (h45 : Sec4.Item4_5) : Item2131Two := by
  intro G _ _ A E U c L hpair hA27
  obtain ⟨f, hf, -⟩ := h2131One G A E U c L hpair hA27
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hcA : c ∈ A := hpair.mem_E.2 hpairs.1.1
  have hc1 : c ≠ 1 := hpairs.2.1
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hpair.mem_S.1.1
  have hLc : L ∈ thetaComponentsAt 3 c := (lZeroStarAt_subset A c) hpairs.2.2.1
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc3 : orderOf c = 3 := orderOf_eq_prime (hAe.2 c hcA) hc1
  have hm : ∀ φ ∈ starOf A L, coordGL f φ ∈ KFacts.KP14.monomial := fun φ hφ =>
    hf ⟨φ, starOf_le_wStar A L hφ, rfl⟩
  have hmono : ∀ φ ∈ starOf A L, ¬ 8 ∣ orderOf φ := by
    intro φ hφ h8
    have h12 := KFacts.KP14.pow_twelve_eq_one (hm φ hφ)
    rw [← orderOf_injective (coordGL f) (coordGL_injective f) φ] at h8
    have := (orderOf_dvd_of_pow_eq_one h12)
    have := h8.trans this
    omega
  obtain ⟨hM24, hHe, hJ2, hRu, hJ4, hG2, hD4⟩ := h218 G A E U c L hpair
  rcases h211 G A E U c L hpair with ⟨-, -, -, -, h9⟩ | ⟨-, -, ⟨e⟩⟩ | ⟨-, -, ⟨e⟩⟩ |
      ⟨hL, -⟩ | ⟨hL, -⟩ | ⟨hL, -⟩ | ⟨⟨n, hn, he, hL⟩, -, ⟨e⟩⟩ | ⟨⟨n, -, -, hL⟩, -⟩ |
      ⟨hL, -⟩ | ⟨-, h81, -⟩ | ⟨-, h81, -⟩ | ⟨hL, -⟩ | ⟨-, h81, -⟩
  ·
    exfalso
    have hcard : Nat.card ((starOf A L).map (coordGL f)) = 9 := by
      rw [Subgroup.card_map_of_injective (coordGL_injective f), h9]
    have hle : (starOf A L).map (coordGL f) ≤ KFacts.KP14.monomial := by
      rintro _ ⟨φ, hφ, rfl⟩
      exact hm φ hφ
    have := Subgroup.card_dvd_of_le hle
    rw [hcard, KFacts.KP14.card_monomial] at this
    omega
  ·
    exfalso
    refine KFacts.KP14.not_quaternion_le
      ((coordGL f).comp ((starOf A L).subtype.comp e.symm.toMonoidHom)) ?_ ?_
    · exact (coordGL_injective f).comp (Subtype.val_injective.comp e.symm.injective)
    · rintro _ ⟨q, rfl⟩
      exact hm _ (e.symm q).2
  ·
    exfalso
    refine hmono _ (e.symm (CFSG.Semidihedral.r 4)).2 ?_
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, CFSG.Semidihedral.orderOf_r 4 (by norm_num)]
    decide
  ·
    exfalso
    rcases hL with e | e
    · exact hM24.false e.some
    · exact hHe.false e.some
  ·
    exact (hJ2.false hL.some).elim
  ·
    exfalso
    rcases hL with e | e
    · exact hRu.false e.some
    · exact hJ4.false e.some
  ·
    rcases hL with ⟨⟨eL⟩, -⟩ | ⟨eL, -⟩
    · exfalso
      have hcL := not_mem_of_lBar_equiv_projSL hc3 hLc eL
      set w : MulAut A :=
        ((e.symm (Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2) : starOf A L) : MulAut A)
      have hw3 : orderOf w = 3 := by
        rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
        exact orderOf_cycle_three
      exact not_isTransvectionOn_of_mem_monomial hAe.1 f (hm w (e.symm _).2)
        (isTransvectionOn_of_mem_starOf h45 hpair hA27 hcL (e.symm _).2 hw3)
    · exact Or.inl ⟨n, hn, he, Or.inr (Or.inr eL)⟩
  ·
    exfalso
    rcases hL with h | h
    · exact hG2 n h
    · exact hD4 n h
  ·
    rcases hL with ⟨n, hn, he, h | h⟩ | h
    · exact Or.inl ⟨n, hn, he, Or.inl h⟩
    · exact Or.inl ⟨n, hn, he, Or.inr (Or.inl h)⟩
    · exact Or.inr h
  · exact absurd (hA27.symm.trans h81) (by norm_num)
  · exact absurd (hA27.symm.trans h81) (by norm_num)
  ·
    exact (h2116 G A E U c L hpair (hL.elim Or.inl (fun h => Or.inr (Or.inl h)))).elim
  · exact absurd (hA27.symm.trans h81) (by norm_num)

end CFSG.RankThree.PartTwo.Sec21
