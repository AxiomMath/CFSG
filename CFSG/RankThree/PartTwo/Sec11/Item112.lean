module

public import CFSG.RankThree.PartTwo.Sec11.FixedCentralizer
public import CFSG.RankThree.PartTwo.KFacts.K72FixL2
public import CFSG.RankThree.PartTwo.KFacts.K72L3Fix
public import CFSG.RankThree.PartTwo.KFacts.K72Moving
public import CFSG.RankThree.PartTwo.Sec9.Item97
public import CFSG.RankThree.PartTwo.Sec11.Item111

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartOne.EmbeddingFixedResidual
open scoped commutatorElement

theorem exists_mulEquiv_psl2_cube_of_isList1016 {X : Type} [Group X] (hX : Sec9.IsList1016 X)
    (hL3 : ¬ ∃ n : ℕ, 1 ≤ n ∧ Sec8.IsoLThreeMinusPi X 2 (3 * n)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (q₀ : ℕ), 4 ≤ q₀ ∧ Nat.card K = q₀ ^ 3 ∧
      Nonempty (X ≃* CFSG.GorensteinWalter.PSL2 K) := by
  rcases hX with ⟨p, e, _, hp, he, ⟨eq⟩⟩ | ⟨n, hn, ⟨eq⟩⟩ | hL
  · refine ⟨_, inferInstance, inferInstance, p ^ e, ?_, ?_, ⟨eq.trans (Sec4.projSLEquivPSL _)⟩⟩
    · exact le_trans (by omega) (Nat.le_self_pow (by omega) p)
    · rw [GaloisField.card p (3 * e) (by omega), ← pow_mul, mul_comm]
  · refine ⟨_, inferInstance, inferInstance, 2 ^ n, ?_, ?_, ⟨eq.trans (Sec4.projSLEquivPSL _)⟩⟩
    · calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    · rw [GaloisField.card 2 (3 * n) (by omega), ← pow_mul, mul_comm]
  · exact absurd hL hL3

theorem fixedPoints_facts_of_isList1016 {X : Type} [Group X] [Finite X]
    (hX : Sec9.IsList1016 X) {α : MulAut X} (hα3 : α ^ 3 = 1) (hout : ¬ KFacts.IsInnerAut α) :
    Subgroup.center (α.toMonoidHom.eqLocus (MonoidHom.id X)) = ⊥ ∧
      IsQuasisimple (α.toMonoidHom.eqLocus (MonoidHom.id X)) ∧
      3 ∣ Nat.card (α.toMonoidHom.eqLocus (MonoidHom.id X)) := by
  by_cases hL3 : ∃ n : ℕ, 1 ≤ n ∧ Sec8.IsoLThreeMinusPi X 2 (3 * n)
  · obtain ⟨n, hn, hL⟩ := hL3
    exact KFacts.fixedPoints_facts_of_isoLThreeMinusPi hn hL hα3 hout
  · obtain ⟨K, _, _, q₀, hq₀, hK, ⟨e⟩⟩ := exists_mulEquiv_psl2_cube_of_isList1016 hX hL3
    obtain ⟨h1, h2, h3, -⟩ := KFacts.fixedPoints_facts_of_mulEquiv_psl2 e hq₀ hK hα3 hout
    exact ⟨h1, h2, h3⟩

theorem exists_ne_of_sylow_of_isList1016 {X : Type} [Group X] [Finite X]
    (hX : Sec9.IsList1016 X) {α : MulAut X} (hα3 : α ^ 3 = 1) (hout : ¬ KFacts.IsInnerAut α)
    (S : Sylow 3 X) : ∃ y ∈ (S : Subgroup X), α y ≠ y := by
  by_cases hL3 : ∃ n : ℕ, 1 ≤ n ∧ Sec8.IsoLThreeMinusPi X 2 (3 * n)
  · obtain ⟨n, hn, hL⟩ := hL3
    exact KFacts.exists_ne_of_sylow_of_isoLThreeMinusPi hn hL α hα3 hout S
  · obtain ⟨K, _, _, q₀, hq₀, hK, ⟨e⟩⟩ := exists_mulEquiv_psl2_cube_of_isList1016 hX hL3
    obtain ⟨-, -, -, h4⟩ := KFacts.fixedPoints_facts_of_mulEquiv_psl2 e hq₀ hK hα3 hout
    refine KFacts.exists_ne_of_sylow_of_card_dvd α (fun T hT => ?_) h4 S
    have hle : T ≤ α.toMonoidHom.eqLocus (MonoidHom.id X) := fun t ht => hT t ht
    exact Subgroup.card_dvd_of_le hle

section Core

variable {G : Type} [Group G] [Finite G]

theorem closure_triple_eq {A : Subgroup G} (hexp : ∀ y ∈ A, y ^ 3 = 1)
    (h27 : Nat.card A = 27) {p q r : G} (hp : p ∈ A) (hq : q ∈ A) (hr : r ∈ A) (hp1 : p ≠ 1)
    (hqp : q ∉ Subgroup.zpowers p) (hrpq : r ∉ Subgroup.closure ({p, q} : Set G)) :
    Subgroup.closure ({p, q, r} : Set G) = A := by
  have hA3 : IsPGroup 3 A := fun y => ⟨1, Subtype.ext (by simpa using hexp y y.2)⟩
  have hp3 : orderOf p = 3 := orderOf_eq_prime (hexp p hp) hp1
  have hpq : Subgroup.closure ({p, q} : Set G) ≤ A := by
    rw [Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact hp
    · exact hq
  have hpqr : Subgroup.closure ({p, q, r} : Set G) ≤ A := by
    rw [Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · exact hp
    · exact hq
    · exact hr
  have h1 : Subgroup.zpowers p ≤ Subgroup.closure ({p, q} : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
  have h2 : Subgroup.closure ({p, q} : Set G) ≤ Subgroup.closure ({p, q, r} : Set G) :=
    Subgroup.closure_mono (by intro y hy; simp only [Set.mem_insert_iff,
      Set.mem_singleton_iff] at hy ⊢; tauto)
  have h9 := Sec9.three_mul_card_le_of_le_of_ne hA3 hpq h1 (fun h => hqp (by
    rw [h]
    exact Subgroup.subset_closure (by simp)))
  have h27' := Sec9.three_mul_card_le_of_le_of_ne hA3 hpqr h2 (fun h => hrpq (by
    rw [h]
    exact Subgroup.subset_closure (by simp)))
  rw [Nat.card_zpowers, hp3] at h9
  exact Subgroup.eq_of_le_of_card_ge hpqr (by omega)

theorem not_isInnerAut_of_not_mem_closure {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
    {R : Subgroup G} (h : Sec9.Hyp91 G A c L a R) {d : G} (hdL : A ⊓ L = Subgroup.zpowers d)
    (hA : A = Subgroup.closure {c, a, d}) {x : G} (hxA : x ∈ A)
    (hx : x ∉ Subgroup.closure ({c, d} : Set G)) (hxN : x ∈ Subgroup.normalizer (L : Set G)) :
    ¬ KFacts.IsInnerAut (Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨x, hxN⟩)) := by
  have hAe := h.mem_partTwoF.1
  have hexp : ∀ y ∈ A, y ^ 3 = 1 := hAe.2
  have hcA := h.mem_A
  have hdAL : d ∈ A ⊓ L := by
    rw [hdL]
    exact Subgroup.mem_zpowers d
  set N := Subgroup.normalizer (L : Set G) with hN
  set ρ : N →* MulAut (L ⧸ aschbacherSolvableCore 3 L) :=
    (Sec4.thetaQuotMulAut L).comp (Sec4.compAction L) with hρ
  set I := (MulAut.conj : L ⧸ aschbacherSolvableCore 3 L →*
    MulAut (L ⧸ aschbacherSolvableCore 3 L)).range with hI
  set B₀ := (I.comap ρ).map N.subtype with hB₀
  have hmem : ∀ (y : G) (hy : y ∈ N), y ∈ B₀ ↔ KFacts.IsInnerAut (ρ ⟨y, hy⟩) := by
    intro y hy
    constructor
    · rintro ⟨y', hy', rfl⟩
      exact hy'
    · intro hin
      exact ⟨⟨y, hy⟩, hin, rfl⟩
  have hLc := Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt
  have hcN : c ∈ N := Subgroup.centralizer_le_normalizer _
    (Subgroup.mem_centralizer_iff.mpr fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.mp (hLc hy))
  have hcB : c ∈ B₀ := by
    rw [hmem c hcN]
    have h1 : ρ ⟨c, hcN⟩ = 1 := by
      ext q
      induction q using QuotientGroup.induction_on with
      | H l =>
        rw [hρ, MonoidHom.comp_apply, Sec4.thetaQuotMulAut_mk, MulAut.one_apply]
        congr 1
        apply Subtype.ext
        change c * (l : G) * c⁻¹ = l
        rw [← Subgroup.mem_centralizer_singleton_iff.mp (hLc l.2), mul_inv_cancel_right]
    rw [h1]
    exact ⟨1, map_one _⟩
  have hdB : d ∈ B₀ := by
    rw [hmem d (Subgroup.le_normalizer hdAL.2)]
    refine ⟨((⟨d, hdAL.2⟩ : L) : L ⧸ aschbacherSolvableCore 3 L), ?_⟩
    ext q
    induction q using QuotientGroup.induction_on with
    | H w => rfl
  intro hin
  have hxB : x ∈ B₀ := (hmem x hxN).mpr hin
  have hcd : d ∉ Subgroup.zpowers c := by
    intro hdc
    have hle : A ≤ Subgroup.closure ({c, a} : Set G) := by
      rw [hA, Subgroup.closure_le]
      have hc : c ∈ Subgroup.closure ({c, a} : Set G) := Subgroup.subset_closure (by simp)
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with hy | hy | hy <;> rw [hy]
      · exact hc
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.zpowers_le.mpr hc hdc
    have h1 := Subgroup.card_le_of_le hle
    have hca : c * a = a * c :=
      congrArg Subtype.val (hAe.1.is_comm.comm ⟨c, hcA⟩ ⟨a, h.a_mem⟩)
    have h2 := Sec10.card_closure_pair_le hca (hexp c hcA) (hexp a h.a_mem)
    rw [h.card_eq] at h1
    omega
  have hAeq := closure_triple_eq hexp h.card_eq hcA hdAL.1 hxA h.ne_one hcd hx
  have haB : a ∈ B₀ := by
    have hle : Subgroup.closure ({c, d, x} : Set G) ≤ B₀ := by
      rw [Subgroup.closure_le]
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      · exact hcB
      · exact hdB
      · exact hxB
    exact hle (hAeq ▸ h.a_mem)
  exact h.toHyp81.not_isInnerAut_induced ((hmem a h.toHyp81.a_mem_normalizer).mp haB)

theorem le_inSubgroup_perfectResidual {P X : Subgroup G} (hP : Group.IsPerfect P) (hPX : P ≤ X) :
    P ≤ inSubgroup perfectResidual X := by
  have hP' : Group.IsPerfect (P.subgroupOf X) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hPX).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hPX).symm.surjective
  have h1 := (CFSG.perfect_residual_transport (MonoidHom.id X)).2.2 _ hP'
  intro y hy
  exact ⟨⟨y, hPX hy⟩, h1 (Subgroup.mem_subgroupOf.mpr hy), rfl⟩

theorem not_three_dvd_of_mem_thetaComponentsAt_ne (h45 : Sec4.Item4_5) {A : Subgroup G} {c : G}
    {L : Subgroup G} {a : G} {R : Subgroup G} (h : Sec9.Hyp91 G A c L a R) {Y' : Subgroup G}
    (hY' : Y' ∈ thetaComponentsAt 3 c) (hne : Y' ≠ L)
    (hZ : Subgroup.center (Y' ⧸ aschbacherSolvableCore 3 Y') = ⊥) : ¬ 3 ∣ Nat.card Y' := by
  intro h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe := h.mem_partTwoF.1
  have hexp : ∀ y ∈ A, y ^ 3 = 1 := hAe.2
  have hA3 : IsPGroup 3 A := fun y => ⟨1, Subtype.ext (by simpa using hexp y y.2)⟩
  have hAY : A ≤ Subgroup.normalizer (Y' : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 h.toTheoremFourHyp hAe h.mem_A h.ne_one Y'
      hY'
  have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 h.toTheoremFourHyp hAe h.mem_A h.ne_one L
      h.mem_thetaComponentsAt
  obtain ⟨y, ⟨hyY, hyA'⟩, hy3⟩ := KFacts.exists_mem_centralizer_orderOf_eq hA3 hAY h3
  have hy3' : y ^ 3 = 1 := by
    rw [← hy3]
    exact pow_orderOf_eq_one y
  have hyA : y ∈ A := Sec15.mem_of_mem_partTwoF h.mem_partTwoF hy3' fun z hz =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hyA' z hz)
  have hysec : y ∈ Late.sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype) := by
    refine ⟨hyA, fun l hl => ?_⟩
    have h1 := Sec10.commutator_mem_theta_of_ne hY' h.mem_thetaComponentsAt hne hyY hl
    have h2 : y * l * y⁻¹ * l⁻¹ ∈ L :=
      L.mul_mem ((Subgroup.mem_normalizer_iff.mp (hAL hyA) l).mp hl) (L.inv_mem hl)
    show y * l * y⁻¹ * l⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) L
    rw [Sec6.theta_eq_inf_of_mem_thetaComponentsAt h.mem_thetaComponentsAt]
    exact ⟨h2, h1⟩
  rw [h.sectionCentralizer_eq] at hysec
  have hy1 : y ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hy3
    exact absurd hy3 (by norm_num)
  have hcy : c ∈ Subgroup.zpowers y := by
    have heq : Subgroup.zpowers y = Subgroup.zpowers c :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hysec)
        (by rw [Nat.card_zpowers, Nat.card_zpowers, hy3,
          orderOf_eq_prime (hexp c h.mem_A) h.ne_one])
    rw [heq]
    exact Subgroup.mem_zpowers c
  have hcY : c ∈ Y' := Subgroup.zpowers_le.mpr hyY hcy
  have hYc := Sec6.le_centralizer_of_mem_thetaComponentsAt hY'
  have hcC : c ∈ Sec4.thetaQuotCentralizer Y' := by
    refine Sec6.mem_thetaQuotCentralizer_iff.mpr ⟨hAY h.mem_A, fun l hl => ?_⟩
    rw [← Subgroup.mem_centralizer_singleton_iff.mp (hYc hl), mul_inv_cancel_right,
      inv_mul_cancel]
    exact Subgroup.one_mem _
  have h1 := mem_theta_of_mem_thetaQuotCentralizer hZ hcY hcC
  have h2 := eq_one_of_mem_theta_of_pow_eq_one h1 (k := 1)
    (Subtype.ext (by simpa using hexp c h.mem_A))
  exact h.ne_one (congrArg Subtype.val h2)

theorem kMap_eq_one_of_commute {L : Subgroup G} {x : G}
    (hxN : x ∈ Subgroup.normalizer (L : Set G)) (hx3 : x ^ 3 = 1)
    (hQ : IsQuasisimple ((Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨x, hxN⟩)).toMonoidHom.eqLocus
      (MonoidHom.id (L ⧸ aschbacherSolvableCore 3 L))))
    (hZ : Subgroup.center ((Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨x, hxN⟩)).toMonoidHom.eqLocus
      (MonoidHom.id (L ⧸ aschbacherSolvableCore 3 L))) = ⊥)
    (k : sec11K L x) (hk : ∀ k' : sec11K L x, kMap L x k * kMap L x k' = kMap L x k' * kMap L x k) :
    kMap L x k = 1 := by
  set F := (Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨x, hxN⟩)).toMonoidHom.eqLocus
    (MonoidHom.id (L ⧸ aschbacherSolvableCore 3 L)) with hF
  have hrange : (kMap L x).range = F := by
    rw [range_kMap_eq hxN hx3 hQ.1, range_cMap hxN hx3]
  have hmem : ∀ k, kMap L x k ∈ F := fun k => hrange ▸ ⟨k, rfl⟩
  have hcen : (⟨kMap L x k, hmem k⟩ : F) ∈ Subgroup.center F := by
    rw [Subgroup.mem_center_iff]
    rintro ⟨f, hf⟩
    rw [← hrange] at hf
    obtain ⟨k', rfl⟩ := hf
    exact Subtype.ext (hk k').symm
  rw [hZ, Subgroup.mem_bot] at hcen
  exact congrArg Subtype.val hcen

theorem center_eq_bot_of_eq_sup {L Y : Subgroup G} {x : G}
    (hxN : x ∈ Subgroup.normalizer (L : Set G)) (hx3 : x ^ 3 = 1)
    (hQ : IsQuasisimple ((Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨x, hxN⟩)).toMonoidHom.eqLocus
      (MonoidHom.id (L ⧸ aschbacherSolvableCore 3 L))))
    (hZ : Subgroup.center ((Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨x, hxN⟩)).toMonoidHom.eqLocus
      (MonoidHom.id (L ⧸ aschbacherSolvableCore 3 L))) = ⊥)
    (hKY : sec11K L x ≤ Y) (hsup : Y = sec11K L x ⊔ inSubgroup (aschbacherSolvableCore 3) Y) :
    Subgroup.center (Y ⧸ aschbacherSolvableCore 3 Y) = ⊥ := by
  set ψ : sec11K L x →* Y ⧸ aschbacherSolvableCore 3 Y :=
    (QuotientGroup.mk' (aschbacherSolvableCore 3 Y)).comp (Subgroup.inclusion hKY) with hψ
  have hψs : Function.Surjective ψ := surjective_inclusion_quotient hKY hsup
  obtain ⟨hθYs, -, -, -⟩ := solvable_prime_complement_core_characterization (H := Y)
    Nat.prime_three
  obtain ⟨hθLs, -, hθL3, -⟩ := solvable_prime_complement_core_characterization (H := L)
    Nat.prime_three
  have hψker : ∀ k : ψ.ker, Subgroup.inclusion hKY (k : sec11K L x) ∈ aschbacherSolvableCore 3 Y :=
    fun k => by
      have h1 : ψ (k : sec11K L x) = 1 := MonoidHom.mem_ker.mp k.2
      change QuotientGroup.mk' (aschbacherSolvableCore 3 Y)
        (Subgroup.inclusion hKY (k : sec11K L x)) = 1 at h1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact h1
  have hk1 : ψ.ker ≤ (kMap L x).ker := by
    set f : ψ.ker →* aschbacherSolvableCore 3 Y :=
      ((Subgroup.inclusion hKY).comp ψ.ker.subtype).codRestrict _ hψker with hf
    have hfinj : Function.Injective f := fun y z hyz => Subtype.ext (Subtype.ext (by
      have := congrArg (fun w : aschbacherSolvableCore 3 Y => ((w : Y) : G)) hyz
      exact this))
    exact le_ker_kMap_of_normal_solvable hxN hx3 hQ hZ ψ.ker
      (Group.isSolvable_of_isSolvable_injective hfinj)
  have hkker : ∀ k : (kMap L x).ker,
      Subgroup.inclusion (sec11K_le L x) (k : sec11K L x) ∈ aschbacherSolvableCore 3 L :=
    fun k => by
      have h1 : kMap L x (k : sec11K L x) = 1 := MonoidHom.mem_ker.mp k.2
      change QuotientGroup.mk' (aschbacherSolvableCore 3 L)
        (Subgroup.inclusion (sec11K_le L x) (k : sec11K L x)) = 1 at h1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact h1
  have hk2 : (kMap L x).ker ≤ ψ.ker := by
    set f : (kMap L x).ker →* aschbacherSolvableCore 3 L :=
      ((Subgroup.inclusion (sec11K_le L x)).comp (kMap L x).ker.subtype).codRestrict _ hkker
      with hf
    have hfinj : Function.Injective f := fun y z hyz => Subtype.ext (Subtype.ext (by
      have := congrArg (fun w : aschbacherSolvableCore 3 L => ((w : L) : G)) hyz
      exact this))
    have h3 : ¬ 3 ∣ Nat.card (kMap L x).ker := fun h3 => hθL3 (by
      rw [Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv] at h3
      exact h3.trans (Subgroup.card_subgroup_dvd_card _))
    exact le_ker_of_normal_solvable ψ hψs _ (Group.isSolvable_of_isSolvable_injective hfinj) h3
  rw [eq_bot_iff]
  intro q hq
  rw [Subgroup.mem_bot]
  obtain ⟨k, rfl⟩ := hψs q
  have h1 : kMap L x k = 1 := by
    refine kMap_eq_one_of_commute hxN hx3 hQ hZ k fun k' => ?_
    have h2 : k * k' * k⁻¹ * k'⁻¹ ∈ ψ.ker := by
      have hc := Subgroup.mem_center_iff.mp hq (ψ k')
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv]
      calc ψ k * ψ k' * (ψ k)⁻¹ * (ψ k')⁻¹ = (ψ k' * ψ k) * (ψ k)⁻¹ * (ψ k')⁻¹ := by rw [hc]
        _ = 1 := by group
    have h3 := MonoidHom.mem_ker.mp (hk1 h2)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h3
    calc kMap L x k * kMap L x k' = (kMap L x k * kMap L x k' * (kMap L x k)⁻¹ *
          (kMap L x k')⁻¹) * (kMap L x k' * kMap L x k) := by group
      _ = kMap L x k' * kMap L x k := by rw [h3, one_mul]
  exact MonoidHom.mem_ker.mp (hk2 (MonoidHom.mem_ker.mpr h1))

theorem basic_facts_of_conj_hyp91 (h45 : Sec4.Item4_5) {A : Subgroup G} {c : G}
    {L : Subgroup G} {a : G} {R : Subgroup G} (h : Sec9.Hyp91 G A c L a R)
    (hl : Sec9.IsList1016 (L ⧸ aschbacherSolvableCore 3 L)) {d : G}
    (hdL : A ⊓ L = Subgroup.zpowers d) (hA : A = Subgroup.closure {c, a, d}) {x : G}
    (hxA : x ∈ A) (hxcd : x ∉ Subgroup.closure ({c, d} : Set G)) :
    ∃ hxN : x ∈ Subgroup.normalizer (L : Set G), x ^ 3 = 1 ∧
      Subgroup.center ((Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨x, hxN⟩)).toMonoidHom.eqLocus
        (MonoidHom.id (L ⧸ aschbacherSolvableCore 3 L))) = ⊥ ∧
      IsQuasisimple ((Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨x, hxN⟩)).toMonoidHom.eqLocus
        (MonoidHom.id (L ⧸ aschbacherSolvableCore 3 L))) ∧
      d ∈ sec11K L x := by
  have hAe := h.mem_partTwoF.1
  have hexp : ∀ y ∈ A, y ^ 3 = 1 := hAe.2
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have hdAL : d ∈ A ⊓ L := by
    rw [hdL]
    exact Subgroup.mem_zpowers d
  have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 h.toTheoremFourHyp hAe h.mem_A h.ne_one L
      h.mem_thetaComponentsAt
  have hxN := hAL hxA
  have hx3 := hexp x hxA
  have hτ3 : Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨x, hxN⟩) ^ 3 = 1 := by
    have h1 : (⟨x, hxN⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hx3)
    rw [← map_pow, ← map_pow, h1, map_one, map_one]
  have hout := not_isInnerAut_of_not_mem_closure h hdL hA hxA hxcd hxN
  obtain ⟨hZ, hQ, -⟩ := fixedPoints_facts_of_isList1016 hl hτ3 hout
  refine ⟨hxN, hx3, hZ, hQ, ?_⟩
  exact mem_sec11K_of_pow_eq_one hxN hx3 hQ.1
    ⟨hdAL.2, Subgroup.mem_centralizer_singleton_iff.mpr (hcomm d hdAL.1 x hxA)⟩
    (k := 1) (by rw [pow_one]; exact hexp d hdAL.1)

theorem basic_facts_of_conj (h45 : Sec4.Item4_5) {A : Subgroup G} {c : G} {L : Subgroup G}
    {a : G} {R Y : Subgroup G} (h : Sec11Std G A c L a R Y) {d : G}
    (hdL : A ⊓ L = Subgroup.zpowers d) (hA : A = Subgroup.closure {c, a, d}) {x : G}
    (hxA : x ∈ A) (hxcd : x ∉ Subgroup.closure ({c, d} : Set G)) :
    ∃ hxN : x ∈ Subgroup.normalizer (L : Set G), x ^ 3 = 1 ∧
      Subgroup.center ((Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨x, hxN⟩)).toMonoidHom.eqLocus
        (MonoidHom.id (L ⧸ aschbacherSolvableCore 3 L))) = ⊥ ∧
      IsQuasisimple ((Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨x, hxN⟩)).toMonoidHom.eqLocus
        (MonoidHom.id (L ⧸ aschbacherSolvableCore 3 L))) ∧
      d ∈ sec11K L x :=
  basic_facts_of_conj_hyp91 h45 h.toHyp91 h.isList1016 hdL hA hxA hxcd

theorem eq_map_conj_of_sec11K_le (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) {A : Subgroup G}
    {c : G} {L : Subgroup G} {a : G} {R Y : Subgroup G} (h : Sec11Std G A c L a R Y) {d : G}
    (hdL : A ⊓ L = Subgroup.zpowers d) (hA : A = Subgroup.closure {c, a, d}) {g : G}
    (hxA : g * c * g⁻¹ ∈ A) (hxcd : g * c * g⁻¹ ∉ Subgroup.closure ({c, d} : Set G))
    {Yx : Subgroup G} (hYx : Yx ∈ thetaComponentsAt 3 (g * c * g⁻¹))
    (hKY : sec11K L (g * c * g⁻¹) ≤ Yx) : Yx = L.map (MulAut.conj g).toMonoidHom := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set x := g * c * g⁻¹ with hx
  set Lg := L.map (MulAut.conj g).toMonoidHom with hLg
  have hG := h.toTheoremFourHyp
  have hAe := h.mem_partTwoF.1
  have hexp : ∀ y ∈ A, y ^ 3 = 1 := hAe.2
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have hA3 : IsPGroup 3 A := fun y => ⟨1, Subtype.ext (by simpa using hexp y y.2)⟩
  have hcA := h.mem_A
  have hc1 := h.ne_one
  have hcord : orderOf c = 3 := orderOf_eq_prime (hexp c hcA) hc1
  have hΩ : ∀ y : G, y ^ 3 = 1 → (∀ z ∈ A, z * y = y * z) → y ∈ A := fun y hy3 hy =>
    Sec15.mem_of_mem_partTwoF h.mem_partTwoF hy3 fun z hz =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hy z hz)
  have hdAL : d ∈ A ⊓ L := by
    rw [hdL]
    exact Subgroup.mem_zpowers d
  have hx1 : x ≠ 1 := by
    intro hx1
    apply hc1
    calc c = g⁻¹ * x * g := by rw [hx]; group
      _ = 1 := by rw [hx1]; group
  have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hG hAe hcA hc1 L h.mem_thetaComponentsAt
  have hθL : A ≤ Subgroup.normalizer (inSubgroup (aschbacherSolvableCore 3) L : Set G) :=
    hAL.trans (Sec6.normalizer_le_normalizer_theta L)
  obtain ⟨hxN, hx3, hZ, hQ, hdK⟩ := basic_facts_of_conj h45 h hdL hA hxA hxcd
  have hLx : Lg ∈ thetaComponentsAt 3 x :=
    map_mem_thetaComponentsAt (MulAut.conj g) h.mem_thetaComponentsAt
  have hALg : A ≤ Subgroup.normalizer (Lg : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hG hAe hxA hx1 Lg hLx
  have hAY : A ≤ Subgroup.normalizer (Yx : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hG hAe hxA hx1 Yx hYx
  have hθY : A ≤ Subgroup.normalizer (inSubgroup (aschbacherSolvableCore 3) Yx : Set G) :=
    hAY.trans (Sec6.normalizer_le_normalizer_theta Yx)
  have hAK : A ≤ Subgroup.normalizer (sec11K L x : Set G) := by
    intro z hz
    refine GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual _ ?_
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hzx : z * x = x * z := hcomm z hz x hxA
    have hzC : z ∈ Subgroup.normalizer
        ((Subgroup.centralizer ({x} : Set G) : Subgroup G) : Set G) :=
      Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr hzx)
    constructor
    · rintro ⟨hy1, hy2⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp (hAL hz) y).mp hy1,
        (Subgroup.mem_normalizer_iff.mp hzC y).mp hy2⟩
    · rintro ⟨hy1, hy2⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp (hAL hz) y).mpr hy1,
        (Subgroup.mem_normalizer_iff.mp hzC y).mpr hy2⟩
  have hcsec : c ∈ Late.sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype) := by
    rw [h.sectionCentralizer_eq]
    exact Subgroup.mem_zpowers c
  have hcK : c ∈ sectionCentralizerSubgroup A (sec11K L x)
      (inSubgroup (aschbacherSolvableCore 3) L) hAK hθL :=
    ⟨hcA, fun k hk => hcsec.2 k (sec11K_le L x hk)⟩
  have hdK' : d ∉ sectionCentralizerSubgroup A (sec11K L x)
      (inSubgroup (aschbacherSolvableCore 3) L) hAK hθL := by
    rintro ⟨-, hd⟩
    have hd1 := eq_one_of_forall_mem_theta hxN hx3 hQ hZ hdK (hexp d hdAL.1) hd
    rw [hd1] at hA
    have hle : A ≤ Subgroup.closure ({c, a} : Set G) := by
      rw [hA, Subgroup.closure_le]
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.one_mem _
    have h1 := Subgroup.card_le_of_le hle
    have h2 := Sec10.card_closure_pair_le (hcomm c hcA a h.a_mem) (hexp c hcA) (hexp a h.a_mem)
    rw [h.card_eq] at h1
    omega
  by_contra hne
  have h3L : 3 ∣ Nat.card L := by
    have hd3 : orderOf d = 3 := orderOf_eq_prime (hexp d hdAL.1) (fun hd1 => hdK' (by
      rw [hd1]
      exact Subgroup.one_mem _))
    rw [← hd3, ← Subgroup.orderOf_mk d hdAL.2]
    exact orderOf_dvd_natCard _
  have h3Lg : 3 ∣ Nat.card Lg := by
    rw [hLg, Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact h3L
  obtain ⟨u, ⟨huLg, huA'⟩, hu3⟩ := KFacts.exists_mem_centralizer_orderOf_eq hA3 hALg h3Lg
  have hu3' : u ^ 3 = 1 := by
    rw [← hu3]
    exact pow_orderOf_eq_one u
  have huA : u ∈ A := hΩ u hu3' fun z hz => Subgroup.mem_centralizer_iff.mp huA' z hz
  have hYxC := Sec6.le_centralizer_of_mem_thetaComponentsAt hYx
  have hxY : x ∈ sectionCentralizerSubgroup A Yx
      (inSubgroup (aschbacherSolvableCore 3) Yx) hAY hθY := by
    refine ⟨hxA, fun y hy => ?_⟩
    rw [← Subgroup.mem_centralizer_singleton_iff.mp (hYxC hy), mul_inv_cancel_right,
      mul_inv_cancel]
    exact Subgroup.one_mem _
  have huY : u ∈ sectionCentralizerSubgroup A Yx
      (inSubgroup (aschbacherSolvableCore 3) Yx) hAY hθY := by
    refine ⟨huA, fun y hy => ?_⟩
    have h1 := Sec10.commutator_mem_theta_of_ne hLx hYx (Ne.symm hne) huLg hy
    have h2 : u * y * u⁻¹ * y⁻¹ ∈ Yx :=
      Yx.mul_mem ((Subgroup.mem_normalizer_iff.mp (hAY huA) y).mp hy) (Yx.inv_mem hy)
    rw [Sec6.theta_eq_inf_of_mem_thetaComponentsAt hYx]
    exact ⟨h2, h1⟩
  have hxK : x ∈ sectionCentralizerSubgroup A (sec11K L x)
      (inSubgroup (aschbacherSolvableCore 3) L) hAK hθL :=
    ⟨hxA, mem_theta_of_mem_sectionCentralizer_of_le hxN hx3 hQ hZ hKY (hAK hxA) hxY⟩
  have huK : u ∈ sectionCentralizerSubgroup A (sec11K L x)
      (inSubgroup (aschbacherSolvableCore 3) L) hAK hθL :=
    ⟨huA, mem_theta_of_mem_sectionCentralizer_of_le hxN hx3 hQ hZ hKY (hAK huA) huY⟩
  have hux : u ∉ Subgroup.zpowers x := by
    intro hux
    have hLgList : Sec9.IsList1016 (Lg ⧸ aschbacherSolvableCore 3 Lg) :=
      isList1016_of_mulEquiv (Sec13.thetaQuotEquiv (MulAut.conj g) L).symm h.isList1016
    have hZg := center_eq_bot_of_isList1016 hLgList
    have hLgC := Sec6.le_centralizer_of_mem_thetaComponentsAt hLx
    have huC : u ∈ Sec4.thetaQuotCentralizer Lg := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hux
      refine Sec6.mem_thetaQuotCentralizer_iff.mpr ⟨hALg huA, fun l hl => ?_⟩
      have hl' : x ^ k * l * (x ^ k)⁻¹ = l := by
        rw [(Commute.zpow_left (Subgroup.mem_centralizer_singleton_iff.mp (hLgC hl)).symm
          k).eq, mul_inv_cancel_right]
      rw [hl', inv_mul_cancel]
      exact Subgroup.one_mem _
    have h1 := mem_theta_of_mem_thetaQuotCentralizer hZg huLg huC
    have h2 := eq_one_of_mem_theta_of_pow_eq_one h1 (k := 1)
      (Subtype.ext (by simpa using hu3'))
    have hu1 : u = 1 := congrArg Subtype.val h2
    rw [hu1, orderOf_one] at hu3
    exact absurd hu3 (by norm_num)
  have hcxu : c ∈ Subgroup.closure ({x, u} : Set G) := by
    by_contra hcxu
    have hAeq := closure_triple_eq hexp h.card_eq hxA huA hcA hx1 hux hcxu
    apply hdK'
    have hle : Subgroup.closure ({x, u, c} : Set G) ≤ sectionCentralizerSubgroup A (sec11K L x)
        (inSubgroup (aschbacherSolvableCore 3) L) hAK hθL := by
      rw [Subgroup.closure_le]
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      · exact hxK
      · exact huK
      · exact hcK
    exact hle (hAeq ▸ hdAL.1)
  have hcY : c ∈ sectionCentralizerSubgroup A Yx
      (inSubgroup (aschbacherSolvableCore 3) Yx) hAY hθY := by
    have hle : Subgroup.closure ({x, u} : Set G) ≤ sectionCentralizerSubgroup A Yx
        (inSubgroup (aschbacherSolvableCore 3) Yx) hAY hθY := by
      rw [Subgroup.closure_le]
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact hxY
      · exact huY
    exact hle hcxu
  have hxcc : x * c = c * x := hcomm x hxA c hcA
  obtain ⟨hsupY, P', hP', hP'eq⟩ := fixed_residual_ambient Nat.prime_three hxcc
    ⟨1, by rw [hcord, pow_one]⟩ hYx (hAY hcA) hcY.2
  have := hG.isSimpleGroup
  have hAC : A ≤ Subgroup.centralizer ({c} : Set G) := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm y hy c hcA)
  have hC4 : SectionFourHyp (Subgroup.centralizer ({c} : Set G)) :=
    hG.sectionFourHyp (centralizer_ne_top_of_simple hG.nonabelian hc1)
  have hA' : CFSG.Assembly.IsElemAbelian 3 (A.subgroupOf (Subgroup.centralizer ({c} : Set G))) := by
    refine ⟨⟨⟨fun y z => Subtype.ext (Subtype.ext ?_)⟩⟩, fun y hy => ?_⟩
    · exact hcomm _ (Subgroup.mem_subgroupOf.mp y.2) _ (Subgroup.mem_subgroupOf.mp z.2)
    · exact Subtype.ext (by simpa using hexp _ (Subgroup.mem_subgroupOf.mp hy))
  have h27 : ∃ n : ℕ, 3 ≤ n ∧
      Nat.card (A.subgroupOf (Subgroup.centralizer ({c} : Set G))) = 3 ^ n :=
    ⟨3, le_rfl, by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAC).toEquiv, h.card_eq]
      norm_num⟩
  have hxC : x ∈ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hxcc
  obtain ⟨J', hJ', hPJ⟩ := h48 (Subgroup.centralizer ({c} : Set G)) hC4
    (A.subgroupOf (Subgroup.centralizer ({c} : Set G))) hA' h27 ⟨x, hxC⟩
    (Subgroup.mem_subgroupOf.mpr hxA) (fun h1 => hx1 (congrArg Subtype.val h1)) P' hP'
  set J := J'.map (Subgroup.centralizer ({c} : Set G)).subtype with hJ
  have hJc : J ∈ thetaComponentsAt 3 c := ⟨J', hJ', rfl⟩
  have hIJ : inSubgroup perfectResidual (Yx ⊓ Subgroup.centralizer ({c} : Set G)) ≤ J :=
    hP'eq.symm.le.trans (Subgroup.map_mono hPJ)
  have hKperf : Group.IsPerfect (sec11K L x) := Sec6.isPerfect_inSubgroup_perfectResidual _
  have hLC := Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt
  have hKIx : sec11K L x ≤ inSubgroup perfectResidual (Yx ⊓ Subgroup.centralizer ({c} : Set G)) :=
    le_inSubgroup_perfectResidual hKperf (le_inf hKY ((sec11K_le L x).trans hLC))
  have hK1 : sec11K L x ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.mem_bot] at hdK
    apply hdK'
    rw [hdK]
    exact Subgroup.one_mem _
  have hJL : J = L := eq_of_perfect_le_of_mem_thetaComponentsAt Nat.prime_three hJc
    h.mem_thetaComponentsAt hK1 hKperf (hKIx.trans hIJ) (sec11K_le L x)
  have hIxK : inSubgroup perfectResidual (Yx ⊓ Subgroup.centralizer ({c} : Set G)) ≤
      sec11K L x := by
    refine le_inSubgroup_perfectResidual (Sec6.isPerfect_inSubgroup_perfectResidual _)
      (le_inf (hJL ▸ hIJ) ?_)
    exact ((Subgroup.map_subtype_le _).trans inf_le_left).trans hYxC
  have hsupK : Yx = sec11K L x ⊔ inSubgroup (aschbacherSolvableCore 3) Yx := by
    rw [← le_antisymm hIxK hKIx, sup_comm]
    exact hsupY.symm
  have hZY := center_eq_bot_of_eq_sup hxN hx3 hQ hZ hKY hsupK
  set Y' := Yx.map (MulAut.conj g).symm.toMonoidHom with hY'
  have hY'c : Y' ∈ thetaComponentsAt 3 c := by
    have h1 := map_mem_thetaComponentsAt (MulAut.conj g).symm hYx
    have h2 : (MulAut.conj g).symm x = c := by
      rw [hx, ← MulAut.conj_apply, MulEquiv.symm_apply_apply]
    rwa [h2] at h1
  have hY'L : Y' ≠ L := by
    intro hY'L
    apply hne
    rw [← map_map_symm (MulAut.conj g) Yx]
    exact congrArg (fun K : Subgroup G => K.map (MulAut.conj g).toMonoidHom) hY'L
  have hZY' : Subgroup.center (Y' ⧸ aschbacherSolvableCore 3 Y') = ⊥ :=
    KFacts.center_eq_bot_of_mulEquiv_of_center_eq_bot
      (Sec13.thetaQuotEquiv (MulAut.conj g).symm Yx).symm hZY
  have h3Y' : 3 ∣ Nat.card Y' := by
    rw [hY', Subgroup.card_map_of_injective (MulAut.conj g).symm.injective]
    have hd3 : orderOf d = 3 := orderOf_eq_prime (hexp d hdAL.1) (fun hd1 => hdK' (by
      rw [hd1]
      exact Subgroup.one_mem _))
    rw [← hd3, ← Subgroup.orderOf_mk d (hKY hdK)]
    exact orderOf_dvd_natCard _
  exact not_three_dvd_of_mem_thetaComponentsAt_ne h45 h.toHyp91 hY'c hY'L hZY' h3Y'

theorem isQuasisimple_sec11K_quotient {L : Subgroup G} {x : G}
    (hxN : x ∈ Subgroup.normalizer (L : Set G)) (hx3 : x ^ 3 = 1)
    (hQ : IsQuasisimple ((Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨x, hxN⟩)).toMonoidHom.eqLocus
      (MonoidHom.id (L ⧸ aschbacherSolvableCore 3 L))))
    (hZ : Subgroup.center ((Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨x, hxN⟩)).toMonoidHom.eqLocus
      (MonoidHom.id (L ⧸ aschbacherSolvableCore 3 L))) = ⊥) :
    IsQuasisimple (sec11K L x ⧸ aschbacherSolvableCore 3 (sec11K L x)) := by
  obtain ⟨hθs, -, hθ3, hmax, -⟩ := solvable_prime_complement_core_characterization
    (H := sec11K L x) Nat.prime_three
  obtain ⟨hθLs, -, hθL3, -⟩ := solvable_prime_complement_core_characterization (H := L)
    Nat.prime_three
  have hkker : ∀ k : (kMap L x).ker,
      Subgroup.inclusion (sec11K_le L x) (k : sec11K L x) ∈ aschbacherSolvableCore 3 L :=
    fun k => by
      have h1 : kMap L x (k : sec11K L x) = 1 := MonoidHom.mem_ker.mp k.2
      change QuotientGroup.mk' (aschbacherSolvableCore 3 L)
        (Subgroup.inclusion (sec11K_le L x) (k : sec11K L x)) = 1 at h1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact h1
  set f : (kMap L x).ker →* aschbacherSolvableCore 3 L :=
    ((Subgroup.inclusion (sec11K_le L x)).comp (kMap L x).ker.subtype).codRestrict _ hkker with hf
  have hfinj : Function.Injective f := fun y z hyz => Subtype.ext (Subtype.ext (by
    have := congrArg (fun w : aschbacherSolvableCore 3 L => ((w : L) : G)) hyz
    exact this))
  have hker : (kMap L x).ker = aschbacherSolvableCore 3 (sec11K L x) := by
    apply le_antisymm
    · refine hmax _ inferInstance (Group.isSolvable_of_isSolvable_injective hfinj) ?_
      intro h3
      apply hθL3
      rw [Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv] at h3
      exact h3.trans (Subgroup.card_subgroup_dvd_card _)
    · exact le_ker_kMap_of_normal_solvable hxN hx3 hQ hZ _ hθs
  have hrange : (kMap L x).range =
      (Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨x, hxN⟩)).toMonoidHom.eqLocus
        (MonoidHom.id (L ⧸ aschbacherSolvableCore 3 L)) := by
    rw [range_kMap_eq hxN hx3 hQ.1, range_cMap hxN hx3]
  have e := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivRange (kMap L x)).trans (MulEquiv.subgroupCongr hrange))
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hQ

theorem exists_mem_thetaComponentsAt_sec11K_le_hyp91 (h45 : Sec4.Item4_5)
    (h48 : Sec4.Item4_8) {A : Subgroup G} {c : G} {L : Subgroup G} {a : G} {R : Subgroup G}
    (h : Sec9.Hyp91 G A c L a R) (hl : Sec9.IsList1016 (L ⧸ aschbacherSolvableCore 3 L)) {d : G}
    (hdL : A ⊓ L = Subgroup.zpowers d)
    (hA : A = Subgroup.closure {c, a, d}) {x : G} (hxA : x ∈ A)
    (hxcd : x ∉ Subgroup.closure ({c, d} : Set G)) :
    ∃ Yx ∈ thetaComponentsAt 3 x, sec11K L x ≤ Yx := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hxN, hx3, hZ, hQ, -⟩ := basic_facts_of_conj_hyp91 h45 h hl hdL hA hxA hxcd
  have hG := h.toTheoremFourHyp
  have := hG.isSimpleGroup
  have hAe := h.mem_partTwoF.1
  have hexp : ∀ y ∈ A, y ^ 3 = 1 := hAe.2
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have hcA := h.mem_A
  have hx1 : x ≠ 1 := fun hx1 => hxcd (hx1 ▸ Subgroup.one_mem _)
  set Cx := Subgroup.centralizer ({x} : Set G) with hCx
  have hcCx : c ∈ Cx := Subgroup.mem_centralizer_singleton_iff.mpr (hcomm c hcA x hxA)
  set c' : Cx := ⟨c, hcCx⟩ with hc'
  set Dc := Subgroup.centralizer ({c'} : Set Cx) with hDc
  obtain ⟨hLC, hL'⟩ := mem_thetaComponentsIn_iff.mp h.mem_thetaComponentsAt
  set K := sec11K L x with hK
  have hKCx : K ≤ Cx := (Subgroup.map_subtype_le _).trans inf_le_right
  have hKDc : K.subgroupOf Cx ≤ Dc := by
    intro k hk
    rw [Subgroup.mem_subgroupOf] at hk
    rw [hDc, Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp (hLC (sec11K_le L x hk))
  set T : Subgroup Dc := (K.subgroupOf Cx).subgroupOf Dc with hT
  set e : T ≃* K := (Subgroup.subgroupOfEquivOfLe hKDc).trans (Subgroup.subgroupOfEquivOfLe hKCx)
    with he
  have he_apply : ∀ t : T, ((e t : K) : G) = (((t : Dc) : Cx) : G) := fun t => rfl
  have hTperf : Group.IsPerfect T := by
    have hKp : Group.IsPerfect K := Sec6.isPerfect_inSubgroup_perfectResidual _
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hTsn : T.IsSubnormal := by
    set ι : Dc →* Subgroup.centralizer ({c} : Set G) :=
      (Cx.subtype.comp Dc.subtype).codRestrict _ (fun y => by
        have hy := Subgroup.mem_centralizer_singleton_iff.mp y.2
        exact Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hy)) with hι
    set MD := (L.subgroupOf (Subgroup.centralizer ({c} : Set G))).comap ι with hMD
    have hMDsn : MD.IsSubnormal := hL'.2.1.comap ι
    have hTMD : T ≤ MD := by
      intro t ht
      rw [hT, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at ht
      rw [hMD, Subgroup.mem_comap, Subgroup.mem_subgroupOf]
      exact sec11K_le L x ht
    have hTn : (T.subgroupOf MD).Normal := by
      constructor
      intro t ht m
      rw [Subgroup.mem_subgroupOf] at ht ⊢
      rw [hT, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at ht ⊢
      have hmL : (((m : Dc) : Cx) : G) ∈ L := m.2
      have hmM : (((m : Dc) : Cx) : G) ∈ L ⊓ Subgroup.centralizer ({x} : Set G) :=
        ⟨hmL, ((m : Dc) : Cx).2⟩
      have := GroupTheory.conj_mem_inSubgroup_perfectResidual hmM ht
      simpa [hK, sec11K] using this
    exact Subgroup.IsSubnormal.trans hTMD hTn.isSubnormal hMDsn
  have hTq : IsQuasisimple (T ⧸ aschbacherSolvableCore 3 T) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.congr _ _ e (CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv
        Nat.prime_three e)).symm (isQuasisimple_sec11K_quotient hxN hx3 hQ hZ)
  have hTmem : T ∈ thetaComponents 3 Dc := ⟨hTperf, hTsn, hTq⟩
  have hAC : A ≤ Cx := fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr (hcomm y hy x hxA)
  have hC4 : SectionFourHyp Cx := hG.sectionFourHyp (centralizer_ne_top_of_simple hG.nonabelian hx1)
  have hA' : CFSG.Assembly.IsElemAbelian 3 (A.subgroupOf Cx) := by
    refine ⟨⟨⟨fun y z => Subtype.ext (Subtype.ext ?_)⟩⟩, fun y hy => ?_⟩
    · exact hcomm _ (Subgroup.mem_subgroupOf.mp y.2) _ (Subgroup.mem_subgroupOf.mp z.2)
    · exact Subtype.ext (by simpa using hexp _ (Subgroup.mem_subgroupOf.mp hy))
  have h27 : ∃ n : ℕ, 3 ≤ n ∧ Nat.card (A.subgroupOf Cx) = 3 ^ n :=
    ⟨3, le_rfl, by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAC).toEquiv, h.card_eq]
      norm_num⟩
  obtain ⟨J', hJ', hTJ⟩ := h48 Cx hC4 (A.subgroupOf Cx) hA' h27 c'
    (Subgroup.mem_subgroupOf.mpr hcA) (fun h1 => h.ne_one (congrArg Subtype.val h1))
    (T.map Dc.subtype) ⟨T, hTmem, rfl⟩
  refine ⟨J'.map Cx.subtype, ⟨J', hJ', rfl⟩, fun k hk => ?_⟩
  have hk' : (⟨k, hKCx hk⟩ : Cx) ∈ T.map Dc.subtype := by
    exact ⟨⟨⟨k, hKCx hk⟩, hKDc (Subgroup.mem_subgroupOf.mpr hk)⟩, hk, rfl⟩
  exact ⟨_, hTJ hk', rfl⟩

theorem exists_mem_thetaComponentsAt_sec11K_le (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8)
    {A : Subgroup G} {c : G} {L : Subgroup G} {a : G} {R Y : Subgroup G}
    (h : Sec11Std G A c L a R Y) {d : G} (hdL : A ⊓ L = Subgroup.zpowers d)
    (hA : A = Subgroup.closure {c, a, d}) {x : G} (hxA : x ∈ A)
    (hxcd : x ∉ Subgroup.closure ({c, d} : Set G)) :
    ∃ Yx ∈ thetaComponentsAt 3 x, sec11K L x ≤ Yx :=
  exists_mem_thetaComponentsAt_sec11K_le_hyp91 h45 h48 h.toHyp91 h.isList1016 hdL hA hxA hxcd

theorem thetaQuotMulAut_compAction_of_mem (L : Subgroup G) {y : G} (hy : y ∈ L) :
    Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨y, Subgroup.le_normalizer hy⟩) =
      MulAut.conj ((⟨y, hy⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) := by
  ext q
  induction q using QuotientGroup.induction_on with
  | H w => rfl

theorem not_isInnerAut_conj (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) {A : Subgroup G} {c : G}
    {L : Subgroup G} {a : G} {R Y : Subgroup G} (h : Sec11Std G A c L a R Y) {d : G}
    (hdL : A ⊓ L = Subgroup.zpowers d) (hA : A = Subgroup.closure {c, a, d}) {g : G}
    (hxA : g * c * g⁻¹ ∈ A) (hxcd : g * c * g⁻¹ ∉ Subgroup.closure ({c, d} : Set G))
    (hKLg : sec11K L (g * c * g⁻¹) ≤ L.map (MulAut.conj g).toMonoidHom)
    (hcN : c ∈ Subgroup.normalizer ((L.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)) :
    ¬ KFacts.IsInnerAut (Sec4.thetaQuotMulAut (L.map (MulAut.conj g).toMonoidHom)
      (Sec4.compAction (L.map (MulAut.conj g).toMonoidHom) ⟨c, hcN⟩)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set x := g * c * g⁻¹ with hx
  set Lg := L.map (MulAut.conj g).toMonoidHom with hLg
  have hG := h.toTheoremFourHyp
  have hAe := h.mem_partTwoF.1
  have hexp : ∀ y ∈ A, y ^ 3 = 1 := hAe.2
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have hcA := h.mem_A
  have hdAL : d ∈ A ⊓ L := by
    rw [hdL]
    exact Subgroup.mem_zpowers d
  have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hG hAe hcA h.ne_one L h.mem_thetaComponentsAt
  have hθL : A ≤ Subgroup.normalizer (inSubgroup (aschbacherSolvableCore 3) L : Set G) :=
    hAL.trans (Sec6.normalizer_le_normalizer_theta L)
  obtain ⟨hxN, hx3, hZ, hQ, hdK⟩ := basic_facts_of_conj h45 h hdL hA hxA hxcd
  have hdLg : d ∈ Lg := hKLg hdK
  have hgA : (Subgroup.zpowers c).map (MulAut.conj g).toMonoidHom ≤ A := by
    rw [MonoidHom.map_zpowers]
    exact Subgroup.zpowers_le.mpr hxA
  have hgne : (Subgroup.zpowers c).map (MulAut.conj g).toMonoidHom ≠ Subgroup.zpowers c := by
    intro heq
    apply hxcd
    have hxc : x ∈ Subgroup.zpowers c := by
      rw [← heq]
      exact ⟨c, Subgroup.mem_zpowers c, rfl⟩
    exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) hxc
  have hnc := item111First_of h45 h48 G A c L a R Y h g hgA hgne
  have hAK : A ≤ Subgroup.normalizer (sec11K L x : Set G) := by
    intro z hz
    refine GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual _ ?_
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hzC : z ∈ Subgroup.normalizer
        ((Subgroup.centralizer ({x} : Set G) : Subgroup G) : Set G) :=
      Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr (hcomm z hz x hxA))
    constructor
    · rintro ⟨hy1, hy2⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp (hAL hz) y).mp hy1,
        (Subgroup.mem_normalizer_iff.mp hzC y).mp hy2⟩
    · rintro ⟨hy1, hy2⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp (hAL hz) y).mpr hy1,
        (Subgroup.mem_normalizer_iff.mp hzC y).mpr hy2⟩
  set S := sectionCentralizerSubgroup A (sec11K L x) (inSubgroup (aschbacherSolvableCore 3) L)
    hAK hθL with hS
  have hcsec : c ∈ Late.sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype) := by
    rw [h.sectionCentralizer_eq]
    exact Subgroup.mem_zpowers c
  have hcS : c ∈ S := ⟨hcA, fun k hk => hcsec.2 k (sec11K_le L x hk)⟩
  have hd3 : d ^ 3 = 1 := hexp d hdAL.1
  have hdS : d ∉ S := by
    rintro ⟨-, hd⟩
    have hd1 := eq_one_of_forall_mem_theta hxN hx3 hQ hZ hdK hd3 hd
    rw [hd1] at hA
    have hle : A ≤ Subgroup.closure ({c, a} : Set G) := by
      rw [hA, Subgroup.closure_le]
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.one_mem _
    have h1 := Subgroup.card_le_of_le hle
    have h2 := Sec10.card_closure_pair_le (hcomm c hcA a h.a_mem) (hexp c hcA) (hexp a h.a_mem)
    rw [h.card_eq] at h1
    omega
  have hd1 : d ≠ 1 := fun hd1 => hdS (hd1 ▸ S.one_mem)
  have hLgList : Sec9.IsList1016 (Lg ⧸ aschbacherSolvableCore 3 Lg) :=
    isList1016_of_mulEquiv (Sec13.thetaQuotEquiv (MulAut.conj g) L).symm h.isList1016
  have hZg := center_eq_bot_of_isList1016 hLgList
  have hcyc := isCyclic_sylow_three_of_isList1016 hLgList
  rintro ⟨w, hw⟩
  set ρ : Subgroup.normalizer (Lg : Set G) →* MulAut (Lg ⧸ aschbacherSolvableCore 3 Lg) :=
    (Sec4.thetaQuotMulAut Lg).comp (Sec4.compAction Lg) with hρ
  set db : Lg ⧸ aschbacherSolvableCore 3 Lg :=
    ((⟨d, hdLg⟩ : Lg) : Lg ⧸ aschbacherSolvableCore 3 Lg) with hdb
  have hτd : ρ ⟨d, Subgroup.le_normalizer hdLg⟩ = MulAut.conj db :=
    thetaQuotMulAut_compAction_of_mem Lg hdLg
  have hw' : ρ ⟨c, hcN⟩ = MulAut.conj w := hw.symm
  have hconj_inj : ∀ y z : Lg ⧸ aschbacherSolvableCore 3 Lg, MulAut.conj y = MulAut.conj z →
      y = z := by
    intro y z hyz
    have h1 : z⁻¹ * y ∈ Subgroup.center (Lg ⧸ aschbacherSolvableCore 3 Lg) := by
      rw [Subgroup.mem_center_iff]
      intro q
      have h2 := congrArg (fun φ : MulAut (Lg ⧸ aschbacherSolvableCore 3 Lg) => φ q) hyz
      simp only [MulAut.conj_apply] at h2
      calc q * (z⁻¹ * y) = z⁻¹ * (z * q * z⁻¹) * z * z⁻¹ * y := by group
        _ = z⁻¹ * (y * q * y⁻¹) * y := by rw [← h2]; group
        _ = z⁻¹ * y * q := by group
    rw [hZg, Subgroup.mem_bot, inv_mul_eq_one] at h1
    exact h1.symm
  have hcd : (⟨c, hcN⟩ : Subgroup.normalizer (Lg : Set G)) * ⟨d, Subgroup.le_normalizer hdLg⟩ =
      ⟨d, Subgroup.le_normalizer hdLg⟩ * ⟨c, hcN⟩ :=
    Subtype.ext (hcomm c hcA d hdAL.1)
  have hwd : w * db = db * w := by
    apply hconj_inj
    have h1 := congrArg ρ hcd
    rw [map_mul, map_mul, hτd, hw'] at h1
    rw [map_mul, map_mul]
    exact h1
  have hw3 : w ^ 3 = 1 := by
    apply hconj_inj
    rw [map_pow, map_one, ← hw']
    have h1 : (⟨c, hcN⟩ : Subgroup.normalizer (Lg : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hexp c hcA)
    rw [← map_pow, h1, map_one]
  have hdb3 : db ^ 3 = 1 := by
    rw [hdb, ← QuotientGroup.mk_pow]
    have : (⟨d, hdLg⟩ : Lg) ^ 3 = 1 := Subtype.ext (by simpa using hd3)
    rw [this, QuotientGroup.mk_one]
  have hdb1 : db ≠ 1 := by
    intro h1
    rw [hdb, QuotientGroup.eq_one_iff] at h1
    have := eq_one_of_mem_theta_of_pow_eq_one h1 (k := 1) (Subtype.ext (by simpa using hd3))
    exact hd1 (congrArg Subtype.val this)
  set E := Subgroup.closure ({w, db} : Set (Lg ⧸ aschbacherSolvableCore 3 Lg)) with hE
  have hE3 : ∀ y ∈ E, y ^ 3 = 1 := by
    intro y hy
    obtain ⟨i, j, -, -, rfl⟩ := KFacts.exists_pow_mul_pow_of_mem_closure_pair hwd hw3 hdb3 hy
    rw [(Commute.pow_pow hwd i j).mul_pow, ← pow_mul, ← pow_mul, mul_comm i 3, mul_comm j 3,
      pow_mul, pow_mul, hw3, hdb3, one_pow, one_pow, one_mul]
  have hEcard : Nat.card E ≤ 3 := KFacts.card_le_of_isCyclic_sylow hcyc hE3
  have hdbE : Subgroup.zpowers db = E :=
    Subgroup.eq_of_le_of_card_ge
      (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Set.mem_insert_of_mem w rfl)))
      (by rw [Nat.card_zpowers, orderOf_eq_prime hdb3 hdb1]; exact hEcard)
  have hwE : w ∈ Subgroup.zpowers db := hdbE ▸ Subgroup.subset_closure (Set.mem_insert w _)
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hwE
  have hdjN : d ^ j ∈ Subgroup.normalizer (Lg : Set G) :=
    Subgroup.le_normalizer (Lg.zpow_mem hdLg j)
  have hτdj : ρ ⟨d ^ j, hdjN⟩ = MulAut.conj w := by
    have h1 : (⟨d ^ j, hdjN⟩ : Subgroup.normalizer (Lg : Set G)) =
        ⟨d, Subgroup.le_normalizer hdLg⟩ ^ j := Subtype.ext (by simp)
    rw [h1, map_zpow, hτd, ← hj, map_zpow]
  set y := c * (d ^ j)⁻¹ with hy
  have hyN : y ∈ Subgroup.normalizer (Lg : Set G) :=
    Subgroup.mul_mem _ hcN (Subgroup.inv_mem _ hdjN)
  have hρy : ρ ⟨y, hyN⟩ = 1 := by
    have h1 : (⟨y, hyN⟩ : Subgroup.normalizer (Lg : Set G)) =
        ⟨c, hcN⟩ * (⟨d ^ j, hdjN⟩)⁻¹ := rfl
    rw [h1, map_mul, map_inv, hw', hτdj, mul_inv_cancel]
  have hyC : y ∈ Sec4.thetaQuotCentralizer Lg := ⟨⟨y, hyN⟩, hρy, rfl⟩
  have hyA : y ∈ A := A.mul_mem hcA (A.inv_mem (A.zpow_mem hdAL.1 j))
  have hyS : y ∈ S :=
    ⟨hyA, mem_theta_of_mem_sectionCentralizer_of_le hxN hx3 hQ hZ hKLg (hAK hyA)
      (mem_sectionCentralizer_of_mem_thetaQuotCentralizer hyA hyC)⟩
  have hdjS : d ^ j ∈ S := by
    have h1 : d ^ j = (c⁻¹ * y)⁻¹ := by rw [hy]; group
    rw [h1]
    exact S.inv_mem (S.mul_mem (S.inv_mem hcS) hyS)
  by_cases hdj1 : d ^ j = 1
  ·
    apply hnc
    have hw1 : w = 1 := by
      rw [← hj, hdb, ← QuotientGroup.mk_zpow]
      have : (⟨d, hdLg⟩ : Lg) ^ j = 1 := Subtype.ext (by simpa using hdj1)
      rw [this, QuotientGroup.mk_one]
    have hρc : ρ ⟨c, hcN⟩ = 1 := by rw [hw', hw1, map_one]
    exact ⟨⟨c, hcN⟩, hρc, rfl⟩
  ·
    apply hdS
    have hdj3 : orderOf (d ^ j) = 3 := orderOf_eq_prime (by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hd3, one_zpow]) hdj1
    have heq : Subgroup.zpowers (d ^ j) = Subgroup.zpowers d :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr (Subgroup.zpow_mem_zpowers d j))
        (by rw [Nat.card_zpowers, Nat.card_zpowers, hdj3, orderOf_eq_prime hd3 hd1])
    have hdmem : d ∈ Subgroup.zpowers (d ^ j) := heq ▸ Subgroup.mem_zpowers d
    exact Subgroup.zpowers_le.mpr hdjS hdmem

theorem sylow_commute_of_isCyclic (L : Subgroup G)
    (hcyc : ∀ S : Sylow 3 (L ⧸ aschbacherSolvableCore 3 L), IsCyclic S) :
    ∀ Q : Sylow 3 L, ∀ x ∈ (Q : Subgroup L), ∀ y ∈ (Q : Subgroup L), x * y = y * x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hθ3 : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 L) :=
    (solvable_prime_complement_core_characterization Nat.prime_three).2.2.1
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 L) with hπ
  intro Q x hx y hy
  have hinj : ∀ z ∈ (Q : Subgroup L), π z = 1 → z = 1 := by
    intro z hz hz1
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hz1
    obtain ⟨k, hk⟩ := Q.isPGroup' ⟨z, hz⟩
    have hk' : z ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact eq_one_of_mem_theta_of_pow_eq_one hz1 hk'
  obtain ⟨S, hS⟩ := (Q.isPGroup'.map π).exists_le_sylow
  have := hcyc S
  have hc : π x * π y = π y * π x := by
    have h1 := (IsCyclic.commGroup (α := S)).mul_comm ⟨π x, hS ⟨x, hx, rfl⟩⟩
      ⟨π y, hS ⟨y, hy, rfl⟩⟩
    exact congrArg Subtype.val h1
  have h2 : π (x * y * (y * x)⁻¹) = 1 := by
    rw [map_mul, map_inv, map_mul, map_mul, hc, mul_inv_cancel]
  have h3 := hinj _ ((Q : Subgroup L).mul_mem ((Q : Subgroup L).mul_mem hx hy)
    ((Q : Subgroup L).inv_mem ((Q : Subgroup L).mul_mem hy hx))) h2
  exact mul_inv_eq_one.mp h3

theorem card_inf_le_three {A L : Subgroup G} (hexp : ∀ y ∈ A, y ^ 3 = 1)
    (hcyc : ∀ S : Sylow 3 (L ⧸ aschbacherSolvableCore 3 L), IsCyclic S) :
    Nat.card (A ⊓ L : Subgroup G) ≤ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set ψ : (A ⊓ L : Subgroup G) →* L ⧸ aschbacherSolvableCore 3 L :=
    (QuotientGroup.mk' (aschbacherSolvableCore 3 L)).comp (Subgroup.inclusion inf_le_right)
    with hψ
  have hψinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro y hy
    rw [MonoidHom.mem_ker, hψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hy
    have h1 := eq_one_of_mem_theta_of_pow_eq_one hy (k := 1)
      (Subtype.ext (by simpa using hexp y y.2.1))
    exact Subgroup.mem_bot.mpr (Subtype.ext (by simpa using congrArg Subtype.val h1))
  rw [Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv]
  refine KFacts.card_le_of_isCyclic_sylow hcyc ?_
  rintro _ ⟨y, rfl⟩
  rw [← map_pow]
  have : y ^ 3 = 1 := Subtype.ext (by simpa using hexp y y.2.1)
  rw [this, map_one]

theorem exists_fusion_of_sec11K_le (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) {A : Subgroup G}
    {c : G} {L : Subgroup G} {a : G} {R Y : Subgroup G} (h : Sec11Std G A c L a R Y) {d : G}
    (hdL : A ⊓ L = Subgroup.zpowers d) (hA : A = Subgroup.closure {c, a, d}) {g : G}
    (hxA : g * c * g⁻¹ ∈ A) (hxcd : g * c * g⁻¹ ∉ Subgroup.closure ({c, d} : Set G))
    (hKLg : sec11K L (g * c * g⁻¹) ≤ L.map (MulAut.conj g).toMonoidHom) :
    ∃ w ∈ L.map (MulAut.conj g).toMonoidHom ⊓ Subgroup.normalizer (A : Set G),
      (Subgroup.zpowers c).map (MulAut.conj w).toMonoidHom ≤ Subgroup.closure {c, d} ∧
        (Subgroup.zpowers c).map (MulAut.conj w).toMonoidHom ≠ Subgroup.zpowers c := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set x := g * c * g⁻¹ with hx
  set Lg := L.map (MulAut.conj g).toMonoidHom with hLg
  have hG := h.toTheoremFourHyp
  have hAe := h.mem_partTwoF.1
  have hexp : ∀ y ∈ A, y ^ 3 = 1 := hAe.2
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have hcA := h.mem_A
  have hΩ : ∀ y : G, y ^ 3 = 1 → (∀ z ∈ A, z * y = y * z) → y ∈ A := fun y hy3 hy =>
    Sec15.mem_of_mem_partTwoF h.mem_partTwoF hy3 fun z hz =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hy z hz)
  have hdAL : d ∈ A ⊓ L := by
    rw [hdL]
    exact Subgroup.mem_zpowers d
  have hd3 : d ^ 3 = 1 := hexp d hdAL.1
  obtain ⟨hxN, hx3, hZ, hQ, hdK⟩ := basic_facts_of_conj h45 h hdL hA hxA hxcd
  have hdLg : d ∈ Lg := hKLg hdK
  have hx1 : x ≠ 1 := fun hx1 => hxcd (hx1 ▸ Subgroup.one_mem _)
  have hLx : Lg ∈ thetaComponentsAt 3 x :=
    map_mem_thetaComponentsAt (MulAut.conj g) h.mem_thetaComponentsAt
  have hALg : A ≤ Subgroup.normalizer (Lg : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hG hAe hxA hx1 Lg hLx
  have hcN := hALg hcA
  have hout := not_isInnerAut_conj h45 h48 h hdL hA hxA hxcd hKLg hcN
  have hLgList : Sec9.IsList1016 (Lg ⧸ aschbacherSolvableCore 3 Lg) :=
    isList1016_of_mulEquiv (Sec13.thetaQuotEquiv (MulAut.conj g) L).symm h.isList1016
  have hcyc := isCyclic_sylow_three_of_isList1016 hLgList
  have hcd : d ∉ Subgroup.zpowers c := by
    intro hdc
    have hle : A ≤ Subgroup.closure ({c, a} : Set G) := by
      rw [hA, Subgroup.closure_le]
      have hc : c ∈ Subgroup.closure ({c, a} : Set G) := Subgroup.subset_closure (by simp)
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with hy | hy | hy <;> rw [hy]
      · exact hc
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.zpowers_le.mpr hc hdc
    have h1 := Subgroup.card_le_of_le hle
    have h2 := Sec10.card_closure_pair_le (hcomm c hcA a h.a_mem) (hexp c hcA) (hexp a h.a_mem)
    rw [h.card_eq] at h1
    omega
  have hd1 : d ≠ 1 := fun hd1 => hcd (hd1 ▸ Subgroup.one_mem _)
  have hdord : orderOf d = 3 := orderOf_eq_prime hd3 hd1
  have hALg' : A ⊓ Lg = Subgroup.zpowers d := by
    refine (Subgroup.eq_of_le_of_card_ge
      (Subgroup.zpowers_le.mpr (show d ∈ A ⊓ Lg from ⟨hdAL.1, hdLg⟩)) ?_).symm
    rw [Nat.card_zpowers, hdord]
    exact card_inf_le_three hexp hcyc
  set τ := Sec4.thetaQuotMulAut Lg (Sec4.compAction Lg ⟨c, hcN⟩) with hτ
  have hτ3 : τ ^ 3 = 1 := by
    have h1 : (⟨c, hcN⟩ : Subgroup.normalizer (Lg : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hexp c hcA)
    rw [hτ, ← map_pow, ← map_pow, h1, map_one, map_one]
  have hQc : ∀ Q : Sylow 3 Lg, ¬ ∀ y ∈ (Q : Subgroup Lg), c * (y : G) = y * c := by
    intro Q hQa
    obtain ⟨y, hy, hy'⟩ := exists_ne_of_sylow_of_isList1016 hLgList hτ3 hout
      (Q.mapSurjective (QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 Lg)))
    apply hy'
    rw [Sylow.coe_mapSurjective] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    rw [QuotientGroup.mk'_apply, hτ, Sec4.thetaQuotMulAut_mk]
    congr 1
    apply Subtype.ext
    show c * z * c⁻¹ = z
    rw [hQa z hz, mul_inv_cancel_right]
  obtain ⟨l, ⟨hlLg, hlA⟩, ⟨k, hk⟩, x', hx'A, hx'⟩ :=
    KFacts.exists_moving_of_not_centralizes_sylow hcomm hexp hΩ hALg hcA
      (sylow_commute_of_isCyclic Lg hcyc) hQc
  have hLgC := Sec6.le_centralizer_of_mem_thetaComponentsAt hLx
  have hlx : l * x = x * l := Subgroup.mem_centralizer_singleton_iff.mp (hLgC hlLg)
  have hld : l * d = d * l := by
    refine Sec12.commute_of_conj_mem_zpowers hdord ?_ hk
    rw [← hALg']
    exact ⟨(Subgroup.mem_normalizer_iff.mp hlA d).mp hdAL.1,
      Lg.mul_mem (Lg.mul_mem hlLg hdLg) (Lg.inv_mem hlLg)⟩
  have hdx : d ∉ Subgroup.zpowers x := by
    intro hdx
    apply hxcd
    have heq : Subgroup.zpowers d = Subgroup.zpowers x :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hdx)
        (by rw [Nat.card_zpowers, Nat.card_zpowers, hdord,
          orderOf_eq_prime (hexp x hxA) hx1])
    have : x ∈ Subgroup.zpowers d := heq ▸ Subgroup.mem_zpowers x
    exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) this
  have hcxd : c ∉ Subgroup.closure ({x, d} : Set G) := by
    intro hc
    apply hout
    set ρ : Subgroup.normalizer (Lg : Set G) →* MulAut (Lg ⧸ aschbacherSolvableCore 3 Lg) :=
      (Sec4.thetaQuotMulAut Lg).comp (Sec4.compAction Lg) with hρ
    set B₀ := ((MulAut.conj : Lg ⧸ aschbacherSolvableCore 3 Lg →*
      MulAut (Lg ⧸ aschbacherSolvableCore 3 Lg)).range.comap ρ).map
        (Subgroup.normalizer (Lg : Set G)).subtype with hB₀
    have hxB : x ∈ B₀ := by
      refine ⟨⟨x, hALg hxA⟩, ⟨1, ?_⟩, rfl⟩
      rw [map_one]
      symm
      ext q
      induction q using QuotientGroup.induction_on with
      | H w =>
        rw [hρ, MonoidHom.comp_apply, Sec4.thetaQuotMulAut_mk, MulAut.one_apply]
        congr 1
        apply Subtype.ext
        change x * (w : G) * x⁻¹ = w
        rw [← Subgroup.mem_centralizer_singleton_iff.mp (hLgC w.2), mul_inv_cancel_right]
    have hdB : d ∈ B₀ := ⟨⟨d, Subgroup.le_normalizer hdLg⟩,
      ⟨((⟨d, hdLg⟩ : Lg) : Lg ⧸ aschbacherSolvableCore 3 Lg),
        (thetaQuotMulAut_compAction_of_mem Lg hdLg).symm⟩, rfl⟩
    have hle : Subgroup.closure ({x, d} : Set G) ≤ B₀ := by
      rw [Subgroup.closure_le]
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact hxB
      · exact hdB
    obtain ⟨⟨c', hc'N⟩, hc'in, hc'eq⟩ := hle hc
    have hcc' : (⟨c', hc'N⟩ : Subgroup.normalizer (Lg : Set G)) = ⟨c, hcN⟩ := Subtype.ext hc'eq
    rw [hcc'] at hc'in
    exact hc'in
  have hAeq := closure_triple_eq hexp h.card_eq hxA hdAL.1 hcA hx1 hdx hcxd
  have hlc : l * c * l⁻¹ ≠ c := by
    intro hlc
    apply hx'
    have hcen : A ≤ Subgroup.centralizer ({l} : Set G) := by
      rw [← hAeq, Subgroup.closure_le]
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      rcases hy with hy | hy | hy <;> rw [hy]
      · exact hlx.symm
      · exact hld.symm
      · calc c * l = l * c * l⁻¹ * l := by rw [hlc]
          _ = l * c := by group
    rw [← Subgroup.mem_centralizer_singleton_iff.mp (hcen hx'A), mul_inv_cancel_right]
  have hlcd : l * c * l⁻¹ * c⁻¹ ∈ Subgroup.zpowers d := by
    rw [← hALg']
    refine ⟨A.mul_mem ((Subgroup.mem_normalizer_iff.mp hlA c).mp hcA) (A.inv_mem hcA), ?_⟩
    rw [show l * c * l⁻¹ * c⁻¹ = l * (c * l⁻¹ * c⁻¹) by group]
    exact Lg.mul_mem hlLg ((Subgroup.mem_normalizer_iff.mp hcN _).mp (Lg.inv_mem hlLg))
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hlcd
  have hlc' : l * c * l⁻¹ = d ^ j * c := by rw [hj]; group
  refine ⟨l, ⟨hlLg, hlA⟩, ?_, ?_⟩
  · rw [MonoidHom.map_zpowers]
    refine Subgroup.zpowers_le.mpr ?_
    change l * c * l⁻¹ ∈ _
    rw [hlc']
    exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) j)
      (Subgroup.subset_closure (by simp))
  · rw [MonoidHom.map_zpowers]
    intro heq
    have h1 : l * c * l⁻¹ ∈ Subgroup.zpowers c := by
      rw [← heq]
      exact Subgroup.mem_zpowers _
    have h2 : d ^ j ∈ Subgroup.zpowers c := by
      have : d ^ j = l * c * l⁻¹ * c⁻¹ := by rw [hlc']; group
      rw [this]
      exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ (Subgroup.mem_zpowers c))
    have hdj1 : d ^ j ≠ 1 := fun hdj1 => hlc (by rw [hlc', hdj1, one_mul])
    have hdj3 : orderOf (d ^ j) = 3 := orderOf_eq_prime (by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hd3, one_zpow]) hdj1
    have heq' : Subgroup.zpowers (d ^ j) = Subgroup.zpowers d :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr (Subgroup.zpow_mem_zpowers d j))
        (by rw [Nat.card_zpowers, Nat.card_zpowers, hdj3, hdord])
    exact hcd (Subgroup.zpowers_le.mpr h2 (heq' ▸ Subgroup.mem_zpowers d))

end Core

theorem item112_of (h97 : Sec9.Item97) (h98 : Sec9.Item98) (h45 : Sec4.Item4_5)
    (h48 : Sec4.Item4_8) : Item112 := by
  intro G _ _ A c L a R Y h d hdL
  have hA := (h97 G A c L a R h.toHyp91).2 d hdL
  obtain ⟨g, hgA, hgne⟩ := h98 G A c L a R h.toHyp91
  by_cases hcd : (Subgroup.zpowers c).map (MulAut.conj g).toMonoidHom ≤ Subgroup.closure {c, d}
  · exact ⟨g, hcd, hgne⟩
  · have hxA : g * c * g⁻¹ ∈ A := hgA ⟨c, Subgroup.mem_zpowers c, rfl⟩
    have hxcd : g * c * g⁻¹ ∉ Subgroup.closure ({c, d} : Set G) := by
      intro hx
      apply hcd
      rw [MonoidHom.map_zpowers]
      exact Subgroup.zpowers_le.mpr hx
    obtain ⟨Yx, hYx, hKY⟩ := exists_mem_thetaComponentsAt_sec11K_le h45 h48 h hdL hA hxA hxcd
    have hYeq := eq_map_conj_of_sec11K_le h45 h48 h hdL hA hxA hxcd hYx hKY
    obtain ⟨w, -, hw⟩ := exists_fusion_of_sec11K_le h45 h48 h hdL hA hxA hxcd (hYeq ▸ hKY)
    exact ⟨w, hw⟩

end CFSG.RankThree.PartTwo.Sec11
