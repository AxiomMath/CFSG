module

import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.Walter.Bender1970.S4.Solvable

public section

namespace CFSG.Walter

open CFSG.GorensteinWalter

variable {G : Type} [Group G] [Finite G]

theorem exists_isKleinFour_le_of_not_isCyclic {U : Subgroup G} (hUp : IsPGroup 2 U)
    (hU : IsMulCommutative U) (hcyc : ¬ IsCyclic U) :
    ∃ U₀ : Subgroup G, U₀ ≤ U ∧ IsKleinFour U₀ := by
  obtain ⟨r, hr, E, hEU, hEcomm, hEexp, hEcard⟩ := exists_elementary_of_not_isCyclic hU hcyc
  have hr2 : r = 2 := by
    have : Fact r.Prime := ⟨hr⟩
    have hE1 : Nontrivial E := by
      rw [← Finite.one_lt_card_iff_nontrivial]
      have := hr.two_le
      nlinarith
    obtain ⟨x, hx⟩ := exists_ne (1 : E)
    have hxo : orderOf (x : G) = r := orderOf_eq_prime (hEexp x x.2)
      (fun h => hx (Subtype.ext h))
    obtain ⟨k, hk⟩ := hUp ⟨x, hEU x.2⟩
    have hdvd : r ∣ 2 ^ k := by
      rw [← hxo]
      exact orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
    exact (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow hdvd)
  subst hr2
  obtain ⟨a, haE, ha1, -⟩ := exists_mem_ne_one_ne (Q := E) (by nlinarith) (1 : G)
  obtain ⟨b, hbE, hb1, hba⟩ := exists_mem_ne_one_ne (Q := E) (by nlinarith) a
  have ha : a * a = 1 := by rw [← pow_two]; exact hEexp a haE
  have hb : b * b = 1 := by rw [← pow_two]; exact hEexp b hbE
  have hab : Commute a b := congrArg Subtype.val (hEcomm.is_comm.comm ⟨a, haE⟩ ⟨b, hbE⟩)
  refine ⟨kleinFourOfCommutingInvolutions a b ha hb hab, ?_,
    isKleinFour_kleinFourOfCommutingInvolutions a b ha hb ha1 hb1 (Ne.symm hba) hab⟩
  intro x hx
  have hx' : x = a * b ∨ x = a ∨ x = b ∨ x = 1 := hx
  rcases hx' with rfl | rfl | rfl | rfl
  · exact hEU (E.mul_mem haE hbE)
  · exact hEU haE
  · exact hEU hbE
  · exact U.one_mem

theorem le_of_forall_centralizer_le_of_odd {U₀ D H : Subgroup G} (hU₀ : IsKleinFour U₀)
    (hU₀D : U₀ ≤ Subgroup.normalizer (D : Set G)) (hD : Odd (Nat.card D))
    (hC : ∀ u ∈ U₀, u ≠ 1 → Subgroup.centralizer ({u} : Set G) ≤ H) : D ≤ H := by
  have hcomm : IsMulCommutative U₀ := IsKleinFour.isMulCommutative
  have hexp : ∀ x ∈ U₀, x ^ 2 = 1 := fun x hx => by
    rw [pow_two]
    exact congrArg Subtype.val (IsKleinFour.mul_self (⟨x, hx⟩ : U₀))
  have hcard : 2 ^ 2 ≤ Nat.card U₀ := by rw [hU₀.card_four]; norm_num
  refine (le_iSup_inf_centralizer Nat.prime_two hcomm hexp hcard hU₀D fun h =>
    (Nat.not_even_iff_odd.mpr hD) (even_iff_two_dvd.mpr h)).trans ?_
  exact iSup₂_le fun u hu => iSup_le fun hu1 => inf_le_right.trans (hC u hu hu1)

theorem le_of_isComponentOf_of_not_isTypeL2Even
    {U₀ Y D H : Subgroup G} (hY : IsAStar Y)
    (hU₀Y : U₀ ≤ Y) (hU₀ : IsKleinFour U₀)
    (hC : ∀ u ∈ U₀, u ≠ 1 → Subgroup.centralizer ({u} : Set G) ≤ H)
    (hD : IsComponentOf D Y) (hD2 : ¬ IsTypeL2Even (D ⧸ Subgroup.center D)) : D ≤ H := by
  rw [bender1970_2_6_subgroup hY hU₀Y hU₀ hD hD2]
  exact iSup₂_le fun u hu => iSup_le fun hu1 => inf_le_right.trans (hC u hu hu1)

theorem exists_le_rank_eq_sub_one (T : Sylow 2 G) (hT : IsMulCommutative (T : Subgroup G))
    {t : G} (htT : t ∈ (T : Subgroup G)) (ht : orderOf t = 2) :
    ∃ R ≤ (T : Subgroup G), rank R = rank (T : Subgroup G) - 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcommT : ∀ x ∈ (T : Subgroup G), ∀ y ∈ (T : Subgroup G), x * y = y * x :=
    fun x hx y hy => congrArg Subtype.val (hT.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  set A := omegaOneOfComm 2 (T : Subgroup G) hcommT with hAdef
  have hAT : A ≤ T := omegaOneOfComm_le _ hcommT
  have hAp : IsPGroup 2 A := T.isPGroup'.to_le hAT
  have htA : t ∈ A := ⟨htT, by rw [← ht, pow_orderOf_eq_one]⟩
  have : Nontrivial A := by
    refine ⟨⟨⟨t, htA⟩, 1, fun h => ?_⟩⟩
    have h1 : t = 1 := congrArg Subtype.val h
    rw [h1, orderOf_one] at ht
    exact absurd ht (by norm_num)
  obtain ⟨B, hB⟩ := CFSG.SolvableHall.exists_index_eq_prime hAp
  exact ⟨B.map A.subtype, (Subgroup.map_subtype_le B).trans hAT,
    rank_hyperplane T.isPGroup' hcommT B hB⟩

theorem BenderCounterexample.exists_mem_benderM_ne_of_mem_benderM (hG : BenderCounterexample G)
    {t : G} (ht : orderOf t = 2) {H : Subgroup G} (hH : H ∈ benderM t) (T : Sylow 2 G)
    (htT : t ∈ (T : Subgroup G)) :
    ∃ s ∈ (T : Subgroup G), orderOf s = 2 ∧ ∃ M ∈ benderM s, M ≠ H := by
  obtain ⟨R, hRT, hR⟩ := exists_le_rank_eq_sub_one T (hG.hasAbelianSylowTwo T) htT ht
  obtain ⟨s, hsR, hs, hsH⟩ := bender1970_3_3 hG ht hH T htT hRT hR
  exact ⟨s, hRT hsR, hs, hG.exists_mem_benderM_ne hs hsH⟩

theorem le_of_oddCoreOf_le {M H : Subgroup G} (hMA : IsAStar M)
    (hMs : Group.IsSolvable (M ⧸ (componentLayerOf M).subgroupOf M)) (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ M) (hO : oddCoreOf M ≤ H) (hE : componentLayerOf M ≤ H)
    (hTH : (T : Subgroup G) ≤ H)
    (hN : M ⊓ Subgroup.normalizer ((T : Subgroup G) : Set G) ≤ H) : M ≤ H := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := pPrimeCore 2 M with hQ
  set π := QuotientGroup.mk' Q with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Q
  set T' : Sylow 2 M := T.subtype hTM with hT'
  set E' := (componentLayerOf M).subgroupOf M with hE'
  have hF : CFSG.fittingSubgroupOf (⊤ : Subgroup (M ⧸ Q)) ≤ (T' : Subgroup M).map π := by
    have hn : (CFSG.fittingSubgroupOf (⊤ : Subgroup (M ⧸ Q))).Normal :=
      normal_of_isNormalIn_top' (fittingSubgroupOf_isNormalIn ⊤)
    have hp : IsPGroup 2 (CFSG.fittingSubgroupOf (⊤ : Subgroup (M ⧸ Q))) :=
      CFSG.isPGroup_of_nilpotent_normal _ hn (CFSG.fittingSubgroupOf_isNilpotent _)
        (pPrimeCore_quotient_pPrimeCore_eq_bot 2)
    have h := hp.le_sylow_of_normal (T'.mapSurjective hπs)
    rwa [Sylow.coe_mapSurjective] at h
  have hEb : componentLayerOf (⊤ : Subgroup (M ⧸ Q)) ≤ E'.map π := by
    obtain ⟨n, hn⟩ := exists_derivedSeries_succ_eq M
    have : Group.IsPerfect (derivedSeries M n) :=
      Subgroup.isPerfect_iff.mpr (by rw [← derivedSeries_succ, hn])
    have hDE : derivedSeries M n ≤ E' := by
      have h := le_ker_of_isPerfect (derivedSeries M n) (QuotientGroup.mk' E')
      rwa [QuotientGroup.ker_mk'] at h
    have : Group.IsPerfect (componentLayerOf (⊤ : Subgroup (M ⧸ Q))) :=
      componentLayerOf_isPerfect _
    have hle : ∀ k, componentLayerOf (⊤ : Subgroup (M ⧸ Q)) ≤ derivedSeries (M ⧸ Q) k := by
      intro k
      induction k with
      | zero => exact le_top
      | succ k ih =>
        rw [derivedSeries_succ, ← Subgroup.commutator_eq_self
          (H := componentLayerOf (⊤ : Subgroup (M ⧸ Q)))]
        exact Subgroup.commutator_mono ih ih
    calc componentLayerOf (⊤ : Subgroup (M ⧸ Q)) ≤ derivedSeries (M ⧸ Q) n := hle n
      _ = (derivedSeries M n).map π := (map_derivedSeries_eq hπs n).symm
      _ ≤ E'.map π := Subgroup.map_mono hDE
  have hOstar : oStar M ≤ ((T' : Subgroup M) ⊔ E') ⊔ Q := by
    have h1 : generalizedFittingSubgroupOf (⊤ : Subgroup (M ⧸ Q)) ≤
        ((T' : Subgroup M) ⊔ E').map π := by
      rw [Subgroup.map_sup]
      exact sup_le (hF.trans le_sup_left) (hEb.trans le_sup_right)
    intro x hx
    have hx' : π x ∈ generalizedFittingSubgroupOf (⊤ : Subgroup (M ⧸ Q)) := hx
    have h2 := h1 hx'
    rw [← Subgroup.mem_comap, Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h2
    exact h2
  have hT'O : (T' : Subgroup M) ≤ oStar M := le_oStar_of_isPGroup hMA T'.isPGroup'
  have : (oStar M).Normal := oStar_normal
  have hfr := Sylow.normalizer_sup_eq_top' T' hT'O
  have htop : (⊤ : Subgroup M) ≤ H.subgroupOf M := by
    rw [← hfr]
    refine sup_le ?_ (hOstar.trans (sup_le (sup_le ?_ ?_) ?_))
    · intro x hx
      rw [Subgroup.mem_subgroupOf]
      refine hN ⟨x.2, ?_⟩
      have hx' : x ∈ Subgroup.normalizer ((T.subgroupOf M : Subgroup M) : Set M) := hx
      rw [← Subgroup.subgroupOf_normalizer_eq hTM, Subgroup.mem_subgroupOf] at hx'
      exact hx'
    · intro x hx
      rw [hT', Sylow.coe_subtype, Subgroup.mem_subgroupOf] at hx
      exact Subgroup.mem_subgroupOf.mpr (hTH hx)
    · intro x hx
      exact Subgroup.mem_subgroupOf.mpr (hE (Subgroup.mem_subgroupOf.mp hx))
    · intro x hx
      exact Subgroup.mem_subgroupOf.mpr (hO ⟨x, hx, rfl⟩)
  intro m hm
  exact Subgroup.mem_subgroupOf.mp (htop (Subgroup.mem_top ⟨m, hm⟩))

end CFSG.Walter
