module

public import CFSG.RankThree.PartTwo.KFacts.K71Basic
import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.RankThree.PartTwo.Sec8.Pairs

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4

section Coset

variable {L : Type*} [Group L] [Finite L] {p : ℕ} [Fact p.Prime]

theorem exists_fixed_of_coprime {P : Type*} [Group P] (hP : IsPGroup p P) (φ : P →* MulAut L)
    (N : Subgroup L) [N.Normal] (hN : ¬ p ∣ Nat.card N) (hφN : ∀ g, ∀ n ∈ N, φ g n ∈ N)
    (y : L) (hy : ∀ g, ((φ g y : L) : L ⧸ N) = (y : L ⧸ N)) :
    ∃ y' : L, (y' : L ⧸ N) = (y : L ⧸ N) ∧ ∀ g, φ g y' = y' := by
  classical
  let _ : MulAction P L := MulAction.compHom L φ
  have hsmul : ∀ (g : P) (l : L), g • l = φ g l := fun _ _ => rfl
  let S : SubMulAction P L :=
    { carrier := {l | (l : L ⧸ N) = (y : L ⧸ N)}
      smul_mem' := by
        intro g l hl
        change ((g • l : L) : L ⧸ N) = (y : L ⧸ N)
        rw [hsmul]
        have hl' : y⁻¹ * l ∈ N := QuotientGroup.eq.mp hl.symm
        have h1 : (φ g y)⁻¹ * φ g l ∈ N := by
          rw [← map_inv, ← map_mul]
          exact hφN g _ hl'
        rw [← hy g]
        exact (QuotientGroup.eq.mpr h1).symm
      }
  have hcard : Nat.card S = Nat.card N := by
    refine Nat.card_congr
      { toFun := fun l => ⟨y⁻¹ * (l : L), QuotientGroup.eq.mp l.2.symm⟩
        invFun := fun n => ⟨y * (n : L), by
          change ((y * (n : L) : L) : L ⧸ N) = (y : L ⧸ N)
          rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff (n : L)).mpr n.2, mul_one]⟩
        left_inv := fun l => by
          apply Subtype.ext
          change y * (y⁻¹ * (l : L)) = l
          group
        right_inv := fun n => by
          apply Subtype.ext
          change y⁻¹ * (y * (n : L)) = n
          group }
  have hmod := hP.card_modEq_card_fixedPoints S
  have hne : (MulAction.fixedPoints P S).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have h0 : Nat.card (MulAction.fixedPoints P S) = 0 := by
      rw [hemp]
      simp
    rw [h0, hcard] at hmod
    exact hN (Nat.modEq_zero_iff_dvd.mp hmod)
  obtain ⟨⟨y', hy'⟩, hfix⟩ := hne
  refine ⟨y', hy', fun g => ?_⟩
  have := congrArg Subtype.val (hfix g)
  exact this

end Coset

section Bar

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem not_three_dvd_card_aschbacherSolvableCore (L : Subgroup G) :
    ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 L) :=
  (solvable_prime_complement_core_characterization (H := L) Nat.prime_three).2.2.1

theorem imageModTheta_centralizer_eq {d : G} (hd : d ∈ Subgroup.normalizer (L : Set G))
    (hd3 : ∃ j : ℕ, d ^ 3 ^ j = 1) :
    Sec8.imageModTheta L (L ⊓ Subgroup.centralizer {d}) =
      Sec8.barCentralizer (Subgroup.zpowers d) L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set x : Subgroup.normalizer (L : Set G) := ⟨d, hd⟩ with hx
  set τ₀ := thetaQuotMulAut L (compAction L x) with hτ₀
  ext ybar
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_barCentralizer_zpowers_iff hd]
    have hy' : (y : G) ∈ L ⊓ Subgroup.centralizer {d} := hy
    have hyc : d * (y : G) * d⁻¹ = y := by
      have := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hy').2
      rw [← this, mul_inv_cancel_right]
    change thetaQuotMulAut L (compAction L x) ((y : L) : L ⧸ aschbacherSolvableCore 3 L) = _
    rw [thetaQuotMulAut_mk]
    congr 1
    exact Subtype.ext hyc
  · intro hybar
    rw [mem_barCentralizer_zpowers_iff hd] at hybar
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective ybar
    have hxP : IsPGroup 3 (Subgroup.zpowers x) := by
      obtain ⟨j, hj⟩ := hd3
      rw [IsPGroup.iff_orderOf]
      rintro ⟨g, hg⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      have h1 : (x ^ k) ^ 3 ^ j = 1 := by
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
        have : x ^ 3 ^ j = 1 := Subtype.ext (by simpa [hx] using hj)
        rw [this, one_zpow]
      obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one
        (show (⟨x ^ k, hg⟩ : Subgroup.zpowers x) ^ 3 ^ j = 1 from Subtype.ext h1))
      exact ⟨i, hi⟩
    set φ : Subgroup.zpowers x →* MulAut L := (compAction L).comp (Subgroup.zpowers x).subtype
    have hφN : ∀ g, ∀ n ∈ aschbacherSolvableCore 3 L, φ g n ∈ aschbacherSolvableCore 3 L := by
      intro g n hn
      have h := map_aschbacherSolvableCore (φ g)
      rw [← h]
      exact ⟨n, hn, rfl⟩
    have hy : ∀ g, ((φ g y : L) : L ⧸ aschbacherSolvableCore 3 L) =
        (y : L ⧸ aschbacherSolvableCore 3 L) := by
      rintro ⟨g, hg⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      change ((compAction L (x ^ k) y : L) : L ⧸ aschbacherSolvableCore 3 L) = _
      rw [← thetaQuotMulAut_mk, map_zpow, map_zpow]
      exact MulAction.mem_fixedBy_zpow (show (y : L ⧸ aschbacherSolvableCore 3 L) ∈
        MulAction.fixedBy _ (thetaQuotMulAut L (compAction L x)) from hybar) k
    obtain ⟨y', hy'eq, hy'fix⟩ := exists_fixed_of_coprime hxP φ (aschbacherSolvableCore 3 L)
      (not_three_dvd_card_aschbacherSolvableCore L) hφN y hy
    refine ⟨y', ?_, hy'eq⟩
    refine Subgroup.mem_inf.mpr ⟨y'.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have h1 := congrArg Subtype.val (hy'fix ⟨x, Subgroup.mem_zpowers x⟩)
    change d * (y' : G) * d⁻¹ = y' at h1
    calc (y' : G) * d = d * (y' : G) * d⁻¹ * d := by rw [h1]
      _ = d * y' := by group

theorem perfectResidual_map_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (perfectResidual A).map e.toMonoidHom = perfectResidual B := by
  rw [perfectResidual, perfectResidual, Subgroup.map_iInf _ e.injective]
  exact iInf_congr fun n => map_derivedSeries_eq e.surjective n

theorem map_inSubgroup_perfectResidual {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (X : Subgroup A) :
    (inSubgroup perfectResidual X).map e.toMonoidHom =
      inSubgroup perfectResidual (X.map e.toMonoidHom) := by
  rw [MulEquiv.toMonoidHom_eq_coe, inSubgroup, inSubgroup,
    ← perfectResidual_map_mulEquiv (e.subgroupMap X), Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem inSubgroup_perfectResidual_congr {A : Type*} [Group A] {X Y : Subgroup A} (h : X = Y) :
    inSubgroup perfectResidual X = inSubgroup perfectResidual Y := by
  subst h
  rfl

theorem subgroupOf_inSubgroup_perfectResidual {A : Type*} [Group A] {M L : Subgroup A}
    (hML : M ≤ L) :
    (inSubgroup perfectResidual M).subgroupOf L = inSubgroup perfectResidual (M.subgroupOf L) := by
  set e : M.subgroupOf L ≃* M := Subgroup.subgroupOfEquivOfLe hML with he
  have hmap := perfectResidual_map_mulEquiv e
  ext x
  rw [Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨m, hm, hmx⟩
    have hm' : m ∈ (perfectResidual (M.subgroupOf L)).map e.toMonoidHom := by rw [hmap]; exact hm
    obtain ⟨m', hm', hm'e⟩ := hm'
    refine ⟨m', hm', ?_⟩
    apply Subtype.ext
    rw [← hmx, ← hm'e]
    rfl
  · rintro ⟨m', hm', rfl⟩
    refine ⟨e m', ?_, rfl⟩
    rw [← hmap]
    exact ⟨m', hm', rfl⟩

theorem imageModTheta_perfectResidual_centralizer_eq {d : G}
    (hd : d ∈ Subgroup.normalizer (L : Set G)) (hd3 : ∃ j : ℕ, d ^ 3 ^ j = 1) :
    Sec8.imageModTheta L (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {d})) =
      inSubgroup perfectResidual (Sec8.barCentralizer (Subgroup.zpowers d) L) := by
  have hC := imageModTheta_centralizer_eq hd hd3
  set M' := (L ⊓ Subgroup.centralizer {d}).subgroupOf L with hM'
  set q := QuotientGroup.mk' (aschbacherSolvableCore 3 L) with hq
  set f : M' →* L ⧸ aschbacherSolvableCore 3 L := q.comp M'.subtype with hf
  have hrange : f.range = Sec8.barCentralizer (Subgroup.zpowers d) L := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype, ← hC]
    rfl
  have htrans := (CFSG.perfect_residual_transport f).1
  rw [Sec8.imageModTheta, subgroupOf_inSubgroup_perfectResidual inf_le_left]
  change ((perfectResidual M').map M'.subtype).map q = _
  rw [Subgroup.map_map, ← hf, htrans]
  exact inSubgroup_perfectResidual_congr hrange

theorem nonempty_imageModTheta_perfectResidual_mulEquiv {M : Type*} [Group M] {d : G}
    (hd : d ∈ Subgroup.normalizer (L : Set G)) (hd3 : ∃ j : ℕ, d ^ 3 ^ j = 1)
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* M) (S : Subgroup M)
    (hS : ∀ z, z ∈ S ↔ inducedAutHom L e ⟨d, hd⟩ z = z) :
    Nonempty (Sec8.imageModTheta L (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {d})) ≃*
      inSubgroup perfectResidual S) := by
  rw [imageModTheta_perfectResidual_centralizer_eq hd hd3]
  refine ⟨(e.subgroupMap _).trans (MulEquiv.subgroupCongr ?_)⟩
  rw [← MulEquiv.toMonoidHom_eq_coe, map_inSubgroup_perfectResidual,
    map_barCentralizer_eq hd e S hS]

theorem ne_bot_of_imageModTheta_mulEquiv {X : Subgroup G} {Y : Type*} [Group Y] [Nontrivial Y]
    (e : Sec8.imageModTheta L X ≃* Y) : X ≠ ⊥ := by
  rintro rfl
  obtain ⟨y, hy⟩ := exists_ne (1 : Y)
  apply hy
  obtain ⟨x, hx⟩ := e.surjective y
  have hx1 : x = 1 := by
    obtain ⟨z, hz, hzx⟩ := x.2
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.mem_bot] at hz
    have hz1 : z = 1 := Subtype.ext hz
    apply Subtype.ext
    rw [← hzx, hz1, map_one, Subgroup.coe_one]
  rw [← hx, hx1, map_one]

end Bar

end CFSG.RankThree.PartTwo.KFacts
