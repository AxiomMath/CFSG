module

import CFSG.LocalAnalysis.ComponentInitial.LinearCoverLarge
import CFSG.RankThree.CentralCover.SteinbergBNLinearTorus
import CFSG.Models.PGLSimple
public import CFSG.RankThree.PartTwo.Sec11.LSSolvableProofKlein

public section

namespace CFSG.RankThree.PartTwo.Sec11.SimsR1.L38Solvable

open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.BenderSuzuki.PFchapter1section1 (TwoRankAtLeastTwo)
open CFSG.LocalAnalysis.ComponentInitial.LinearCover
  (even_linear_three_large_field_catalog_central_two_cover_trivial)
open scoped MatrixGroups

theorem card_projSL_three_eight : Nat.card (projSL 3 (GaloisField 2 3)) = 16482816 := by
  have h8 : Nat.card (GaloisField 2 3) = 8 := by
    rw [GaloisField.card 2 3 (by norm_num)]; norm_num
  rw [Nat.card_congr (CFSG.PGLModel.projSLEquivStatedProj 3 (GaloisField 2 3)).toEquiv,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num), h8,
    show Finset.Icc 2 3 = ({2, 3} : Finset ℕ) by decide, Finset.prod_pair (by norm_num)]
  norm_num

instance finite_projSL_three_eight : Finite (projSL 3 (GaloisField 2 3)) :=
  Nat.finite_of_card_ne_zero (by rw [card_projSL_three_eight]; norm_num)

theorem isSimpleGroup_projSL_three_eight : IsSimpleGroup (projSL 3 (GaloisField 2 3)) :=
  CFSG.PGLModel.isSimpleGroup_projSL_of_two_le _ (by norm_num) (Or.inl (by norm_num))
    (Or.inl (by norm_num))

private noncomputable def equivPSL (n : ℕ) (F : Type) [Field F] :
    projSL n F ≃* PSL(n, F) :=
  (CFSG.PGLModel.projSLEquivStatedProj n F).trans
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj n F).symm

theorem not_dvd_card_ker_of_cover {E J : Type} [Group E] [Finite E] [Group.IsPerfect E] [Group J]
    (π : E →* J) (hπ : Function.Surjective π) (hC : π.ker ≤ Subgroup.center E)
    (p : ℕ) [Fact p.Prime]
    (hcov : ∀ (E' : Type) [Group E'] [Finite E'] [Group.IsPerfect E'] (π' : E' →* J),
        Function.Surjective π' → π'.ker ≤ Subgroup.center E' → IsPGroup p π'.ker →
          π'.ker = ⊥) :
    ¬ p ∣ Nat.card π.ker := by
  intro hdvd
  have hcomm : ∀ a b : π.ker, a * b = b * a := fun a b =>
    Subtype.ext ((Subgroup.mem_center_iff.mp (hC a.2) b.1).symm)
  let pw : π.ker →* π.ker :=
    MonoidHom.mk' (fun a => a ^ p) (fun a b => Commute.mul_pow (hcomm a b) p)
  set S : Subgroup E := pw.range.map π.ker.subtype with hS
  have hSker : S ≤ π.ker := Subgroup.map_subtype_le _
  have hSc : S ≤ Subgroup.center E := hSker.trans hC
  haveI hSn : S.Normal := Subgroup.normal_of_le_center hSc
  have hpS : ∀ x ∈ π.ker, x ^ p ∈ S := fun x hx =>
    ⟨pw ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩, rfl⟩
  let η : E ⧸ S →* J := QuotientGroup.lift S π (fun x hx => hSker hx)
  have hη : ∀ x, η (QuotientGroup.mk' S x) = π x := fun x => rfl
  have hηs : Function.Surjective η := by
    intro j
    obtain ⟨x, rfl⟩ := hπ j
    exact ⟨QuotientGroup.mk' S x, hη x⟩
  have hηker : ∀ g ∈ η.ker, ∃ x ∈ π.ker, QuotientGroup.mk' S x = g := by
    intro g hg
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective S g
    exact ⟨x, by rwa [MonoidHom.mem_ker, ← hη], rfl⟩
  have hηc : η.ker ≤ Subgroup.center (E ⧸ S) := by
    intro g hg
    obtain ⟨x, hx, rfl⟩ := hηker g hg
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective S q
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp (hC hx) y]
  have hηp : IsPGroup p η.ker := by
    intro g
    obtain ⟨x, hx, hxg⟩ := hηker g.1 g.2
    refine ⟨1, ?_⟩
    apply Subtype.ext
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one, ← hxg, ← map_pow, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    exact hpS x hx
  have hbot := hcov (E ⧸ S) η hηs hηc hηp
  have hle : π.ker ≤ S := by
    intro x hx
    have : QuotientGroup.mk' S x ∈ η.ker := by rwa [MonoidHom.mem_ker, hη]
    rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    exact this
  have hsurj : Function.Surjective pw := by
    intro m
    obtain ⟨y, ⟨a, rfl⟩, hy⟩ := hle m.2
    exact ⟨a, Subtype.ext hy⟩
  have hinj : Function.Injective pw := Finite.injective_iff_surjective.mpr hsurj
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := π.ker) p hdvd
  have h1 : pw z = pw 1 := by
    change z ^ p = (1 : π.ker) ^ p
    rw [one_pow, ← hz]
    exact pow_orderOf_eq_one z
  have h2 : z = 1 := hinj h1
  rw [h2, orderOf_one] at hz
  exact (Fact.out : p.Prime).one_lt.ne hz

theorem cover_two {E : Type} [Group E] [Finite E] [Group.IsPerfect E]
    (π : E →* projSL 3 (GaloisField 2 3)) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 π.ker) : π.ker = ⊥ := by
  have hLie : CFSG.Blueprint.LieModel (projSL 3 (GaloisField 2 3)) .PSL 3 2 3 :=
    Or.inl ⟨by decide, CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSL
      ⟨Nat.prime_two, by norm_num, by norm_num, by decide, by decide⟩ (MulEquiv.refl _)⟩
  exact (even_linear_three_large_field_catalog_central_two_cover_trivial π hπ hC h2 (f := 3)
    le_rfl hLie).1

theorem isCyclic_sylow_of_ne_seven {p : ℕ} [Fact p.Prime] (hp3 : 3 < p) (hp7 : p ≠ 7)
    (Q : Sylow p (projSL 3 (GaloisField 2 3))) : IsCyclic Q := by
  have hp : p.Prime := Fact.out
  have hQ := Sylow.card_eq_multiplicity Q
  rw [card_projSL_three_eight] at hQ
  by_cases hp73 : p = 73
  · subst hp73
    have hfac : (16482816 : ℕ).factorization 73 = 1 := by
      have h : (16482816 : ℕ) = (2 ^ 9 * 3 ^ 2 * 7 ^ 2) * 73 := by norm_num
      rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num), zero_add,
        Nat.Prime.factorization_self (by norm_num)]
    rw [hfac, pow_one] at hQ
    haveI : Fact (Nat.Prime (Nat.card Q)) := ⟨by rw [hQ]; exact hp⟩
    exact isCyclic_of_prime_card hQ
  · have hnd : ¬ p ∣ 16482816 := by
      intro hd
      have h : (16482816 : ℕ) = 2 ^ 9 * 3 ^ 2 * 7 ^ 2 * 73 := by norm_num
      rw [h] at hd
      rcases (Nat.Prime.dvd_mul hp).mp hd with hd | hd
      · rcases (Nat.Prime.dvd_mul hp).mp hd with hd | hd
        · rcases (Nat.Prime.dvd_mul hp).mp hd with hd | hd
          · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd)
            omega
          · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow hd)
            omega
        · have := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7)).mp
            (hp.dvd_of_dvd_pow hd)
          omega
      · exact hp73 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 73)).mp hd)
    rw [Nat.factorization_eq_zero_of_not_dvd hnd, pow_zero] at hQ
    have : Subsingleton Q := (Nat.card_eq_one_iff_unique.mp hQ).1
    infer_instance

theorem cover_seven {E : Type} [Group E] [Finite E] [Group.IsPerfect E]
    (π : E →* projSL 3 (GaloisField 2 3)) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (hCp : IsPGroup 7 π.ker) : π.ker = ⊥ := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  set ε := equivPSL 3 (GaloisField 2 3) with hε
  set φ : E →* PSL(3, GaloisField 2 3) := ε.toMonoidHom.comp π with hφ
  have hφs : Function.Surjective φ := ε.surjective.comp hπ
  have hker : φ.ker = π.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  have hφC : φ.ker ≤ Subgroup.center E := hker ▸ hC
  have hcard : 7 ∣ Nat.card (GaloisField 2 3)ˣ := by
    rw [Nat.card_units, GaloisField.card 2 3 (by norm_num)]; norm_num
  obtain ⟨ζ, hζo⟩ := exists_prime_orderOf_dvd_card' 7 hcard
  have hζ : ζ ^ 7 = 1 := by
    have h := pow_orderOf_eq_one ζ
    rwa [hζo] at h
  obtain ⟨hDexp, hDcomm, hDcard⟩ := CFSG.RankThree.CentralCover.torusPSL_package (p := 7)
    (by norm_num) (by norm_num) hζo hζ (m := 2) (by norm_num) (φ := φ) hφs hφC
  set D : Subgroup PSL(3, GaloisField 2 3) := (CFSG.RankThree.CentralCover.torusPSL ζ hζ 2).range
    with hD
  have hDp : IsPGroup 7 D := fun x => ⟨1, by rw [pow_one]; exact Subtype.ext (hDexp x.1 x.2)⟩
  have hD49 : 49 ≤ Nat.card D := by
    have h := hDcard
    norm_num at h
    exact h
  have hPSLcard : Nat.card PSL(3, GaloisField 2 3) = 16482816 := by
    rw [← Nat.card_congr ε.toEquiv]
    exact card_projSL_three_eight
  haveI : Finite PSL(3, GaloisField 2 3) :=
    Nat.finite_of_card_ne_zero (by rw [hPSLcard]; norm_num)
  have hDidx : ¬ 7 ∣ D.index := by
    have hmul := D.card_mul_index
    rw [hPSLcard] at hmul
    obtain ⟨n, hn⟩ := hDp.exists_card_eq
    rw [hn] at hD49 hmul
    have hn2 : 2 ≤ n := by
      by_contra h
      push Not at h
      have : 7 ^ n ≤ 7 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hn3 : n ≤ 2 := by
      by_contra h
      push Not at h
      have h1 : 7 ^ 3 ∣ 7 ^ n := pow_dvd_pow 7 h
      have h2 : 7 ^ n ∣ 16482816 := ⟨D.index, hmul.symm⟩
      have := h1.trans h2
      norm_num at this
    have : n = 2 := le_antisymm hn3 hn2
    subst this
    norm_num at hmul
    omega
  let Q : Sylow 7 PSL(3, GaloisField 2 3) := hDp.toSylow hDidx
  obtain ⟨P, hP⟩ := Sylow.mapSurjective_surjective hφs 7 Q
  have hPD : (P : Subgroup E).map φ = D := by
    have h := Sylow.ext_iff.mp hP
    simpa [Sylow.coe_mapSurjective, Q] using h
  have hPle : (P : Subgroup E) ≤ D.comap φ := fun x hx => by
    rw [Subgroup.mem_comap, ← hPD]
    exact Subgroup.mem_map_of_mem φ hx
  haveI : IsMulCommutative (P : Subgroup E) :=
    ⟨⟨fun a b => Subtype.ext (hDcomm a (hPle a.2) b (hPle b.2))⟩⟩
  have hPbot : commutator (P : Subgroup E) = ⊥ := commutator_eq_bot (P : Subgroup E)
  have h := CFSG.ShultStronglyClosedTI.central_pSubgroup_le_sylow_derived P π.ker hC hCp
  rw [hPbot, Subgroup.map_bot] at h
  exact le_bot_iff.mp h

theorem cover_large_prime {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {E : Type} [Group E] [Finite E]
    [Group.IsPerfect E] (π : E →* projSL 3 (GaloisField 2 3)) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (hCp : IsPGroup p π.ker) : π.ker = ⊥ := by
  haveI := Fact.mk hp
  by_cases hp7 : p = 7
  · subst hp7
    exact cover_seven π hπ hC hCp
  · obtain ⟨Q⟩ : Nonempty (Sylow p (projSL 3 (GaloisField 2 3))) := inferInstance
    obtain ⟨C⟩ : Nonempty (Sylow p π.ker) := inferInstance
    have hCtop : (C : Subgroup π.ker) = ⊤ :=
      (C.is_maximal' (Q := ⊤) (hCp.to_subgroup ⊤) le_top).symm
    have hbot := CFSG.ShultStronglyClosedTI.central_cover_cyclic_sylow_kernel_eq_bot π hπ hC C Q
      (isCyclic_sylow_of_ne_seven hp3 hp7 Q)
    rw [hCtop] at hbot
    refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
    have h : (⟨x, hx⟩ : π.ker) ∈ (⊤ : Subgroup π.ker) := Subgroup.mem_top _
    rw [hbot, Subgroup.mem_bot] at h
    exact congrArg Subtype.val h

theorem kernel_eq_bot_of_central {E : Type} [Group E] [Finite E] [Group.IsPerfect E]
    (π : E →* projSL 3 (GaloisField 2 3)) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (h3 : ¬ 3 ∣ Nat.card π.ker) : π.ker = ⊥ := by
  have hall : ∀ p : ℕ, p.Prime → ¬ p ∣ Nat.card π.ker := by
    intro p hp
    haveI := Fact.mk hp
    by_cases h2 : p = 2
    · subst h2
      exact not_dvd_card_ker_of_cover π hπ hC 2 fun E' _ _ _ π' hπ' hC' hp' =>
        cover_two π' hπ' hC' hp'
    by_cases h3' : p = 3
    · subst h3'
      exact h3
    have hp3 : 3 < p := by have := hp.two_le; omega
    exact not_dvd_card_ker_of_cover π hπ hC p fun E' _ _ _ π' hπ' hC' hp' =>
      cover_large_prime hp hp3 π' hπ' hC' hp'
  exact Subgroup.card_eq_one.mp (Nat.eq_one_iff_not_exists_prime_dvd.mpr hall)

theorem exists_klein_of_surjective {Y G : Type*} [Group Y] [Finite Y] [Group G]
    (π : Y →* G) (hπ : Function.Surjective π) (U : Subgroup G)
    (hUexp : ∀ x : U, x * x = 1) (hUcard : 4 < Nat.card U) :
    ∃ a b : Y, a * a = 1 ∧ b * b = 1 ∧ a * b = b * a ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  classical
  by_cases hY : TwoRankAtLeastTwo Y
  · exact LSSolvableProof.exists_klein_of_twoRank hY
  exfalso
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite U := Nat.finite_of_card_ne_zero (by omega)
  set Ut : Subgroup Y := U.comap π with hUt
  let πU : Ut →* U := (π.comp Ut.subtype).codRestrict U (fun x => x.2)
  have hπU : Function.Surjective πU := by
    rintro ⟨u, hu⟩
    obtain ⟨y, rfl⟩ := hπ u
    exact ⟨⟨y, hu⟩, rfl⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 Ut) := inferInstance
  have hUp : IsPGroup 2 U := fun x => ⟨1, by rw [pow_one, sq]; exact hUexp x⟩
  have hPU : (P : Subgroup Ut).map πU = ⊤ := by
    have h := (P.mapSurjective hπU).is_maximal' (Q := ⊤) (hUp.to_subgroup ⊤) le_top
    rw [Sylow.coe_mapSurjective] at h
    exact h.symm
  have hPY : ¬ TwoRankAtLeastTwo P := fun h => hY
    (CFSG.BenderSuzuki.twoRankAtLeastTwo_of_injective (Ut.subtype.comp (P : Subgroup Ut).subtype)
      (Subtype.val_injective.comp Subtype.val_injective) h)
  obtain ⟨S⟩ : Nonempty (Sylow 2 P) := inferInstance
  have hS : (S : Subgroup P) = ⊤ := by
    have h := S.is_maximal' (Q := ⊤) (P.isPGroup'.to_subgroup ⊤) le_top
    exact h.symm
  set θ : (S : Subgroup P) →* U :=
    (πU.comp (P : Subgroup Ut).subtype).comp (S : Subgroup P).subtype with hθ
  have hθ : Function.Surjective θ := by
    intro u
    have hu : u ∈ (P : Subgroup Ut).map πU := by rw [hPU]; exact Subgroup.mem_top u
    obtain ⟨x, hx, rfl⟩ := hu
    refine ⟨⟨⟨x, hx⟩, ?_⟩, rfl⟩
    rw [hS]
    exact Subgroup.mem_top _
  have hU4 : Nat.card U ≤ 4 := by
    rcases CFSG.BenderSuzuki.sylowTwo_cyclic_or_quaternion_of_not_twoRank hPY S with hcyc | hq
    ·
      have : IsCyclic U := isCyclic_of_surjective θ hθ
      obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := U)
      have hcard := Nat.card_zpowers g
      have hzp : Subgroup.zpowers g = ⊤ := by
        rw [eq_top_iff]
        intro x _
        exact hg x
      rw [hzp, Subgroup.card_top] at hcard
      have hord : orderOf g ≤ 2 :=
        orderOf_le_of_pow_eq_one (by norm_num) (by rw [sq]; exact hUexp g)
      omega
    · obtain ⟨r, -, ⟨ϕ⟩⟩ := hq
      exact LSSolvableProof.natCard_le_four_of_quaternion (θ.comp ϕ.symm.toMonoidHom)
        (hθ.comp ϕ.symm.surjective) hUexp
  omega

private noncomputable def rootPSL (F : Type) [Field F] : Multiplicative F →* PSL(3, F) :=
  (QuotientGroup.mk' (Subgroup.center SL(3, F))).comp
    { toFun := fun t => CFSG.RankThree.CentralCover.rootElem
        (show (0 : Fin 3) ≠ 1 by decide) (Multiplicative.toAdd t)
      map_one' := CFSG.RankThree.CentralCover.rootElem_zero _
      map_mul' := fun a b => CFSG.RankThree.CentralCover.rootElem_add _ _ _ }

private theorem rootPSL_injective (F : Type) [Field F] : Function.Injective (rootPSL F) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  by_contra hne
  have hmem : CFSG.RankThree.CentralCover.rootElem (show (0 : Fin 3) ≠ 1 by decide)
      (Multiplicative.toAdd a) ∈ Subgroup.center SL(3, F) := (QuotientGroup.eq_one_iff _).1 ha
  exact CFSG.RankThree.CentralCover.rootElem_not_mem_center (show (0 : Fin 3) ≠ 1 by decide)
    (t := Multiplicative.toAdd a) (fun h => hne (Multiplicative.toAdd.injective h)) hmem

theorem exists_klein_four_L38 {Y : Type*} [Group Y] [Finite Y]
    (π : Y →* projSL 3 (GaloisField 2 3)) (hπ : Function.Surjective π) :
    ∃ a b : Y, a * a = 1 ∧ b * b = 1 ∧ a * b = b * a ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  set ε := equivPSL 3 (GaloisField 2 3) with hε
  set φ := rootPSL (GaloisField 2 3) with hφ
  set U : Subgroup PSL(3, GaloisField 2 3) := φ.range with hU
  have hUcard : Nat.card U = 8 := by
    rw [hU, ← Nat.card_congr (MonoidHom.ofInjective (rootPSL_injective _)).toEquiv,
      Nat.card_congr Multiplicative.toAdd, GaloisField.card 2 3 (by norm_num)]
    norm_num
  have hUexp : ∀ x : U, x * x = 1 := by
    rintro ⟨_, a, rfl⟩
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_one]
    rw [← map_mul, ← map_one φ]
    congr 1
    apply Multiplicative.toAdd.injective
    simp only [toAdd_mul, toAdd_one]
    exact CharTwo.add_self_eq_zero _
  exact exists_klein_of_surjective (ε.toMonoidHom.comp π) (ε.surjective.comp hπ) U hUexp
    (by rw [hUcard]; norm_num)

end CFSG.RankThree.PartTwo.Sec11.SimsR1.L38Solvable
