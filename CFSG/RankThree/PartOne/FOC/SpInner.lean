module

public import CFSG.RankThree.PartOne.FOC.ComponentFact
public import CFSG.RankThree.PartOne.FOC.PlaneOfPair
public import CFSG.RankThree.PartOne.FOC.InnerCase
public import CFSG.RankThree.PartOne.KC.SymplecticInnerPlane
public import CFSG.RankThree.PartOne.KC.SymplecticMultiplicity
import CFSG.RankThree.PartOne.KF.F128Cls
import CFSG.RankThree.PartOne.KC.LinearCommutantFactors
import CFSG.LieType.SeitzGeneration.SpHyperRad
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.RankThree.PartOne.FOC

open Polynomial Module Subgroup CFSG CFSG.RankThree.Classical CFSG.LocalAnalysis.ComponentInitial
  CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCSpIsotypic
open CFSG.RankThree.PartOne.Sec66T (LocalRankLeTwo)
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

section Aux

variable {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem one_le_primaryMultiplicity_of_mem {x : Module.End K V}
    (hsq : Squarefree (minpoly K x)) {h : K[X]} [Fact (Irreducible h)]
    (hh : h ∈ primaryFactors x) : 1 ≤ primaryMultiplicity x h := by
  have hne := primaryComponent_ne_bot hsq hh
  have : Nontrivial ↥(primaryComponent x h) := Submodule.nontrivial_iff_ne_bot.mpr hne
  exact Module.finrank_pos

end Aux

section Pow

variable {r : ℕ} {K : Type} [Field K]

theorem spEnd_pow (a : StatedSp r K) (n : ℕ) : spEnd (a ^ n) = spEnd a ^ n :=
  CFSG.LieType.SeitzGeneration.spEnd_pow a n

theorem spEnd_eq_one_of_pow {a : StatedSp r K} {n : ℕ} (h : a ^ n = 1) : spEnd a ^ n = 1 := by
  rw [← spEnd_pow, h]
  change ((spLin r K 1 : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
    Module.End K (Fin r ⊕ Fin r → K)) = _
  rw [map_one, Units.val_one]

end Pow

section Lift

variable {r : ℕ} {K : Type} [Field K] [Finite K]

theorem exists_lift_orderOf_sp (hr : 1 ≤ r) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {a : StatedProj (StatedSp r K)} (ha : a ^ p = 1) (ha1 : a ≠ 1) :
    ∃ x : StatedSp r K, proj r K x = a ∧ orderOf x = p := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x₀, rfl⟩ := SymplecticHigher.proj_surjective (r := r) (K := K) a
  have hker : proj r K (x₀ ^ p) = 1 := by rw [map_pow]; exact ha
  have hsq : (x₀ ^ p) ^ 2 = 1 := sq_eq_one_of_proj_eq_one hr hker
  obtain ⟨m, hm⟩ := hp.odd_of_ne_two hp2
  refine ⟨x₀ ^ (p + 1), ?_, ?_⟩
  · rw [map_pow, pow_succ, ha, one_mul]
  · have hx : (x₀ ^ (p + 1)) ^ p = 1 := by
      calc (x₀ ^ (p + 1)) ^ p = (x₀ ^ p) ^ (p + 1) := by
            rw [← pow_mul, ← pow_mul, mul_comm]
        _ = ((x₀ ^ p) ^ 2) ^ (m + 1) := by
            rw [← pow_mul (x₀ ^ p) 2 (m + 1)]
            congr 1
            omega
        _ = 1 := by rw [hsq, one_pow]
    refine orderOf_eq_prime hx ?_
    intro h1
    apply ha1
    have := congrArg (proj r K) h1
    rw [map_pow, map_one, pow_succ, ha, one_mul] at this
    exact this

end Lift

section Main

variable {K : Type} [Field K]

theorem mem_sup_centralizer_of_component_sp {ℓ f r p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hr : 2 ≤ r) (hrq : ¬ (r = 2 ∧ ℓ ^ f = 2)) (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpℓ : p ≠ ℓ) (hrank : LocalRankLeTwo p (StatedProj (StatedSp r K)))
    {b y : StatedProj (StatedSp r K)} (hbp : b ^ p = 1) (hyp : y ^ p = 1) (hby : b * y = y * b)
    {E : Subgroup (StatedProj (StatedSp r K))}
    (hE : IsComponentOf (Subgroup.centralizer ({b} : Set (StatedProj (StatedSp r K)))) E) :
    y ∈ E ⊔ Subgroup.centralizer (E : Set (StatedProj (StatedSp r K))) := by
  classical
  have hp3 : 3 < p := by omega
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  have hq0 : ℓ ^ f ≠ 0 := pow_ne_zero f hℓ.ne_zero
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact hq0)
  have hcharK : CharP K ℓ := by
    have := Fintype.ofFinite K
    have : Fact ℓ.Prime := ⟨hℓ⟩
    exact charP_of_card_eq_prime_pow (f := f) (by rw [Fintype.card_eq_nat_card, hK])
  have hpK : (p : K) ≠ 0 := by
    intro h
    have := (CharP.cast_eq_zero_iff K ℓ p).mp h
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp this).symm
  obtain ⟨hTs, hTc, hTi⟩ := spProj_facts hℓ hf hK hr hrq
  have hloc : localRank p (StatedProj (StatedSp r K)) ≤ 3 := by
    by_contra h
    exact false_of_three_le_localRank hp hrank (by omega)
  by_cases hy1 : y = 1
  · rw [hy1]
    exact Subgroup.one_mem _
  by_cases hb1 : b = 1
  · subst hb1
    have hcent : Subgroup.centralizer ({1} : Set (StatedProj (StatedSp r K))) = ⊤ := by
      ext g
      simp [Subgroup.mem_centralizer_singleton_iff]
    rw [hcent] at hE
    have : IsSimpleGroup ↥(⊤ : Subgroup (StatedProj (StatedSp r K))) :=
      (Subgroup.topEquiv : ↥(⊤ : Subgroup (StatedProj (StatedSp r K))) ≃* _).isSimpleGroup
    have hEtop : E = ⊤ := eq_of_isComponentOf_simple hE
    rw [hEtop]
    exact Subgroup.mem_sup_left (Subgroup.mem_top _)
  by_cases hyb : y ∈ Subgroup.zpowers b
  · refine Subgroup.mem_sup_right ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hyb
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have : e * b = b * e := Subgroup.mem_centralizer_singleton_iff.mp (hE.1 he)
    exact (Commute.zpow_right (show Commute e b from this) k).eq
  obtain ⟨A, hA, hAcard, hbA, hyA⟩ := exists_plane hp hbp hyp hb1 hby hyb
  obtain ⟨x, hxb, hxp⟩ := exists_lift_orderOf_sp (by omega : 1 ≤ r) hp hp2 hbp hb1
  have hbord : orderOf b = p := orderOf_eq_prime hbp hb1
  have hyord : orderOf y = p := orderOf_eq_prime hyp hy1
  have hxp1 : x ^ p = 1 := hxp ▸ pow_orderOf_eq_one x
  have hsqx : Squarefree (minpoly K (spEnd x)) :=
    KCLinComm.squarefree_minpoly_of_pow_eq_one hpK (spEnd_eq_one_of_pow hxp1)
  have hpm : ∀ h : primaryFactors (spEnd x), (h : K[X]) ≠ X - 1 →
      ¬ p ∣ primaryMultiplicity (spEnd x) (h : K[X]) := by
    intro h hh hdvd
    have : Fact (Irreducible (h : K[X])) := ⟨irreducible_of_mem_primaryFactors h.2⟩
    have hpos := one_le_primaryMultiplicity_of_mem hsqx h.2
    have hlt := (symplectic_primary_multiplicity_actual_central_cover_local_rank
      (⊤ : Subgroup (StatedProj (StatedSp r K))) hℓ hf hK hp hp3 hpℓ hr
      (Subgroup.subtype _) (fun t => ⟨⟨t, Subgroup.mem_top t⟩, rfl⟩)
      (by
        rw [(MonoidHom.ker_eq_bot_iff _).mpr (Subgroup.subtype_injective _)]
        exact bot_le) b hbord x hxb hxp h hh).2 hloc
    exact absurd (Nat.le_of_dvd hpos hdvd) (not_le.mpr hlt.2)
  obtain ⟨h1, h2, -, h4, -, -, h7, -⟩ :=
    symplectic_inner_plane_below_prime_local_core_centralization hℓ hf hK hp hp3 hpℓ hr hrq
      (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))).range le_rfl
      A hA hAcard b hbA hb1 x hxb hxp
  obtain ⟨hfac, -, -⟩ := h7 hpm
  have hyN : y ∈ Subgroup.centralizer ({b} : Set (StatedProj (StatedSp r K))) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hby.symm
  obtain ⟨z, k, hyzk, -, hzc, -, hk⟩ := hfac y hyN hyord
  let J : Option (primaryFactors (spEnd x)) → Subgroup (StatedProj (StatedSp r K)) := fun o =>
    match o with
    | none => spFixedLayerImage x
    | some h => ⨆ (_ : (h : K[X]) ≠ X - 1 ∧ 2 ≤ primaryMultiplicity (spEnd x) (h : K[X])),
        spBlockImage x (h : K[X])
  have hJ : ∀ o, J o = ⊥ ∨ IsComponentOf (Subgroup.centralizer ({b} : Set _)) (J o) := by
    intro o
    cases o with
    | none =>
      by_cases hl : SpFixedListed x
      · obtain ⟨hle, hq, hn, -⟩ := h2 hl
        exact Or.inr ⟨hle, hq, hn.isSubnormal⟩
      · exact Or.inl (h4 hl)
    | some h =>
      by_cases hP : (h : K[X]) ≠ X - 1 ∧ 2 ≤ primaryMultiplicity (spEnd x) (h : K[X])
      · obtain ⟨hle, hq, hn, -⟩ := h1 h hP.1 hP.2
        refine Or.inr ?_
        show IsComponentOf _ (⨆ (_ : _ ∧ _), spBlockImage x (h : K[X]))
        rw [iSup_pos hP]
        exact ⟨hle, hq, hn.isSubnormal⟩
      · refine Or.inl ?_
        show (⨆ (_ : _ ∧ _), spBlockImage x (h : K[X])) = ⊥
        rw [iSup_neg hP]
  have hD : spListedProduct x = ⨆ o, J o := by
    rw [iSup_option, sup_comm]
    rfl
  exact mem_sup_centralizer_of_factorization J hJ hyzk hzc (hD ▸ hk) hE

end Main

end CFSG.RankThree.PartOne.FOC
