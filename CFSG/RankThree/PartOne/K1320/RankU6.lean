module

public import CFSG.RankThree.PartOne.KF.ClsSULift
public import CFSG.RankThree.PartOne.KF.ClsCenter
public import CFSG.RankThree.PartOne.KF.ClsCover
public import CFSG.RankThree.PartTwo.Census.Classical.EvenPrimes
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.Assembly.GL83LieDefs
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.RankThree.PartTwo.Census.Classical.EvenUnitary

public section

namespace CFSG.RankThree.PartOne.K1320

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PerfectCover CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag Matrix
  CFSG.RankThree.PartTwo.Census

theorem charP_two_of_card_eq_pow {K : Type} [Field K] [Finite K] {m : ℕ}
    (h : Nat.card K = 2 ^ m) : CharP K 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype K := Fintype.ofFinite K
  exact charP_of_card_eq_prime_pow (f := m) (by rw [← Nat.card_eq_fintype_card]; exact h)

theorem card_multiplier_psu_six {f : ℕ} (hf : 2 ≤ f) :
    Nat.card (Blueprint.Multiplier.generic .PSU 6 2 f ×
      Blueprint.Multiplier.exceptional .PSU 6 2 f) = Nat.gcd 6 (2 ^ f + 1) := by
  have hgen : Blueprint.Multiplier.genericOrders .PSU 6 2 f = (Nat.gcd 6 (2 ^ f + 1), 1) := rfl
  have hexc : Blueprint.Multiplier.exceptionalOrders .PSU 6 2 f = (1, 1) := by
    unfold Blueprint.Multiplier.exceptionalOrders
    split <;> simp_all
  unfold Blueprint.Multiplier.generic Blueprint.Multiplier.exceptional
  rw [hgen, hexc]
  simp [Nat.card_prod, Nat.card_congr Multiplicative.toAdd]

theorem card_center_dvd_gcd_six
    (hGA : CFSG.Open.GriessAllModelsStatement)
    {I : Type} [Group I] [Finite I] (hperf : Group.IsPerfect I) {f : ℕ} (hf : 2 ≤ f)
    (hmodel : StatedClassicalModel (I ⧸ Subgroup.center I) .PSU 6 2 f) :
    Nat.card (Subgroup.center I) ∣ Nat.gcd 6 (2 ^ f + 1) := by
  have hm : Models.LieModel (I ⧸ Subgroup.center I) .PSU 6 2 f := ⟨hmodel.1, .inl hmodel⟩
  obtain ⟨hperfQ, hcard⟩ := card_hopfMultiplier_of_model hGA hm
  have hd := card_ker_dvd_card_hopfMultiplier hperfQ hperf (QuotientGroup.mk' (Subgroup.center I))
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk'])
  rwa [QuotientGroup.ker_mk', hcard, card_multiplier_psu_six hf] at hd

section Torus

variable {K : Type} [Field K]

theorem exists_torus_swap [Finite K] [CharP K 2] {p f : ℕ} (h : UnitaryFieldData p f K)
    {r k n : ℕ} (hr : r.Prime) (hrq : r ∣ p ^ f + 1) (hkn : k + 2 < n) :
    ∃ (E : Subgroup (StatedSU n (p ^ f) K)) (t : StatedSU n (p ^ f) K),
      IsElemAbelian r E ∧ Nat.card E = r ^ (k + 1) ∧ orderOf t = 2 ∧
        ∀ x ∈ E, x * t = t * x := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hn2 : 2 ≤ n := by omega
  have hrK : r ∣ Nat.card Kˣ := by
    rw [Nat.card_units, h.card, pow_mul', sq,
      show p ^ f * p ^ f - 1 = p ^ f * p ^ f - 1 * 1 by rw [mul_one],
      Nat.mul_self_sub_mul_self_eq]
    exact dvd_mul_of_dvd_left hrq _
  have hμ := card_rootsOfUnity_of_dvd hr hrK
  set μ := rootsOfUnity r K
  set incl := μ.subtype
  set u : (Fin (k + 1) → μ) →* (Fin n → μ) := (torusEntries μ (k + 2) n).comp (dupHom μ k)
  set d : (Fin (k + 1) → μ) →* (Fin n → Kˣ) := (incl.compLeft (Fin n)).comp u
  set ψ := (diagGL n K).comp d
  have hd : ∀ s i, d s i = incl (u s i) := fun _ _ => rfl
  have hdr : ∀ s i, (d s i : K) ^ r = 1 := by
    intro s i
    rw [hd, ← Units.val_pow_eq_pow_val, ← map_pow, rootsOfUnity_pow_eq_one, map_one,
      Units.val_one]
  have hcoe : ∀ s, ((ψ s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      diagonal fun i => (d s i : K) := fun _ => rfl
  have hmem : ∀ s, ψ s ∈ StatedSU n (p ^ f) K := by
    intro s
    refine (mem_unitarySU_iff h).mpr ⟨?_, ?_⟩
    · rw [hcoe, det_diagonal, ← Units.coe_prod]
      have : ∏ i, d s i = incl (∏ i, torusEntries μ (k + 2) n (dupHom μ k s) i) := by
        rw [map_prod]
        rfl
      rw [this, prod_torusEntries hkn, map_one, Units.val_one]
    · rw [hcoe, diagonal_map (map_zero _), diagonal_transpose, diagonal_mul_diagonal,
        ← diagonal_one]
      refine congrArg diagonal (funext fun i => ?_)
      obtain ⟨m, hm⟩ := hrq
      rw [h.bar_apply, ← pow_succ, hm, pow_mul, hdr, one_pow]
  set ψ' : (Fin (k + 1) → μ) →* StatedSU n (p ^ f) K := ψ.codRestrict _ hmem
  have hψ' : Function.Injective ψ' := by
    intro s t hst
    have h1 : ψ s = ψ t := congrArg Subtype.val hst
    have h2 : d s = d t := by
      funext i
      have := congrArg (fun A : GL (Fin n) K => (A : Matrix (Fin n) (Fin n) K) i i) h1
      simp only [hcoe, diagonal_apply_eq] at this
      exact Units.ext this
    have h3 : u s = u t := funext fun i => Subtype.ext (congrFun h2 i)
    exact dupHom_injective k (torusEntries_injective hkn.le h3)
  set t : StatedSU n (p ^ f) K := ⟨swapGL hn2, swapGL_mem_statedSU h hn2⟩
  have ht2 : t ^ 2 = 1 := Subtype.ext (Units.ext (by
    rw [pow_two]
    exact one_add_mul_one_add (swapBlock_mul_self hn2)))
  have ht1 : t ≠ 1 := by
    intro ht
    have h01 := congrArg (fun A : StatedSU n (p ^ f) K =>
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ⟨0, by omega⟩ ⟨1, by omega⟩) ht
    simp only [t, coe_swapGL, swapBlock, Matrix.add_apply, of_apply, Matrix.one_apply] at h01
    simp at h01
  refine ⟨ψ'.range, t,
    isElemAbelian_range (fun s => funext fun j => rootsOfUnity_pow_eq_one (s j)) ψ', ?_,
    orderOf_eq_prime ht2 ht1, ?_⟩
  · rw [← Nat.card_congr (MonoidHom.ofInjective hψ').toEquiv]
    exact card_fun_rootsOfUnity hμ
  · rintro _ ⟨s, rfl⟩
    refine Subtype.ext (Units.ext ?_)
    change ((ψ s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (1 + swapBlock n K) =
      (1 + swapBlock n K) * ((ψ s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    rw [hcoe]
    refine diagonal_mul_swap fun i j hi hj => ?_
    have key : ∀ l : Fin n, l.val < 2 → (d s l : K) = ((incl (s ⟨0, by omega⟩) : Kˣ) : K) := by
      intro l hl
      rw [hd]
      change ((incl (torusEntries μ (k + 2) n (dupHom μ k s) l) : Kˣ) : K) = _
      rw [torusEntries_of_lt _ (by omega), dupHom_apply]
      congr 3
      ext
      simp only
      omega
    rw [key i hi, key j hj]

theorem four_le_localRank_statedSU_six_eight [Finite K] [CharP K 2]
    (h : UnitaryFieldData 2 3 K) : 4 ≤ localRank 3 ↥(StatedSU 6 (2 ^ 3) K) := by
  obtain ⟨E, t, hE, hc, ht, hEt⟩ := exists_torus_swap h (r := 3) (k := 3) (n := 6) Nat.prime_three
    (by norm_num) (by norm_num)
  exact le_localRank_of_commute_involution Nat.prime_three ht hE hc hEt

end Torus

theorem four_le_localRank_psu_six_eight
    (hGA : CFSG.Open.GriessAllModelsStatement)
    {I : Type} [Group I] [Finite I] (hperf : Group.IsPerfect I)
    (hmodel : StatedClassicalModel (I ⧸ Subgroup.center I) .PSU 6 2 3) :
    4 ≤ localRank 3 I := by
  obtain ⟨hadm, K, hKf, hKfin, hK, ⟨e⟩⟩ := id hmodel
  have hcharK : CharP K 2 := charP_two_of_card_eq_pow (m := 2 * 3) (by rw [hK]; norm_num)
  have hU : UnitaryFieldData 2 3 K := ⟨Nat.prime_two, by norm_num, by rw [hK]; norm_num⟩
  by_cases hZ : Subgroup.center I = ⊥
  · have eI : I ≃* StatedProj (StatedSU 6 (2 ^ 3) K) :=
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans e
    rw [localRank_eq_of_mulEquiv eI Nat.prime_three]
    have h4 := le_localRank_statedSU_lift hU Nat.prime_three (by norm_num)
      (by norm_num : 3 ^ 2 ∣ 2 ^ 3 + 1) (by norm_num : 3 ∣ 6) (by norm_num : ¬ 3 ^ 2 ∣ 6)
      (by norm_num : 4 ≤ 6)
    simpa using h4
  · have hcen3 : Nat.card (Subgroup.center I) = 3 := by
      have hd := card_center_dvd_gcd_six hGA hperf (by norm_num : 2 ≤ 3) hmodel
      have h9 : Nat.gcd 6 (2 ^ 3 + 1) = 3 := by norm_num
      rw [h9] at hd
      have h1 : Nat.card (Subgroup.center I) ≠ 1 := fun h1 => hZ (Subgroup.card_eq_one.1 h1)
      rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h
      · exact absurd h h1
      · exact h
    set Z₀ : Subgroup ↥(StatedSU 6 (2 ^ 3) K) :=
      (StatedScalars (Fin 6) K).subgroupOf (StatedSU 6 (2 ^ 3) K) with hZ₀
    have hSU : Group.IsPerfect ↥(StatedSU 6 (2 ^ 3) K) :=
      CFSG.ClassicalGroups.Unitary.isPerfect_statedSU (p := 2) (f := 3) hK (by omega) (by
        intro h
        simp only [Prod.mk.injEq] at h
        omega)
    have hm : Models.LieModel (StatedProj (StatedSU 6 (2 ^ 3) K)) .PSU 6 2 3 :=
      ⟨hadm, Or.inl ⟨hadm, K, hKf, hKfin, hK, ⟨MulEquiv.refl _⟩⟩⟩
    obtain ⟨hSperf, hcardM⟩ := card_hopfMultiplier_of_model hGA hm
    set π : ↥(StatedSU 6 (2 ^ 3) K) →* StatedProj (StatedSU 6 (2 ^ 3) K) :=
      QuotientGroup.mk' Z₀ with hπ
    have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
    have hπk : π.ker = Z₀ := QuotientGroup.ker_mk' _
    have hπc : π.ker ≤ Subgroup.center ↥(StatedSU 6 (2 ^ 3) K) := by
      rw [hπk]
      exact statedScalars_subgroupOf_le_center _
    have hZ₀card : Nat.card Z₀ = 3 := by
      rw [hZ₀, (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hK (by omega)).2.2]
      norm_num
    have hcard : Nat.card (hopfMultiplier (StatedProj (StatedSU 6 (2 ^ 3) K))) =
        Nat.card π.ker := by
      rw [hcardM, card_multiplier_psu_six (by norm_num), hπk, hZ₀card]
      norm_num
    set πI : I →* StatedProj (StatedSU 6 (2 ^ 3) K) :=
      (e : I ⧸ Subgroup.center I →* StatedProj (StatedSU 6 (2 ^ 3) K)).comp
        (QuotientGroup.mk' (Subgroup.center I)) with hπI
    have hπIs : Function.Surjective πI := e.surjective.comp (QuotientGroup.mk'_surjective _)
    have hπIc : πI.ker ≤ Subgroup.center I := by
      intro x hx
      rw [MonoidHom.mem_ker] at hx
      have h1 : (QuotientGroup.mk' (Subgroup.center I)) x = 1 :=
        e.injective (hx.trans (map_one e).symm)
      exact (QuotientGroup.eq_one_iff x).1 h1
    obtain ⟨ρ, -, hρs⟩ := exists_hom_of_card_multiplier_eq hSperf hSU π hπs hπc hcard πI hπIs hπIc
    have hρsurj := hρs hperf
    have hbij : Function.Bijective ρ := by
      refine hρsurj.bijective_of_nat_card_le ?_
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup Z₀
      have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center I)
      have h3 : Nat.card (I ⧸ Subgroup.center I) =
          Nat.card (StatedProj (StatedSU 6 (2 ^ 3) K)) := Nat.card_congr e.toEquiv
      rw [hZ₀card] at h1
      rw [hcen3, h3] at h2
      exact h1.trans_le h2.ge
    rw [← localRank_eq_of_mulEquiv (MulEquiv.ofBijective ρ hbij) Nat.prime_three]
    exact four_le_localRank_statedSU_six_eight hU

theorem exists_localRank_four_of_psu_six_ne_three
    (hGA : CFSG.Open.GriessAllModelsStatement)
    {I : Type} [Group I] [Finite I] (hperf : Group.IsPerfect I) {f : ℕ} (hf : 2 ≤ f)
    (hf3 : f ≠ 3) (hmodel : StatedClassicalModel (I ⧸ Subgroup.center I) .PSU 6 2 f) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ 4 ≤ localRank r I := by
  obtain ⟨-, K, hKf, hKfin, hK, ⟨e⟩⟩ := id hmodel
  have hcharK : CharP K 2 := charP_two_of_card_eq_pow (m := 2 * f) (by rw [hK]; ring)
  have hU : UnitaryFieldData 2 f K := ⟨Nat.prime_two, by omega, by rw [hK]; ring⟩
  obtain ⟨s, hs, hs5, hsd⟩ := exists_prime_five_le_dvd_two_pow_add_one hf hf3
  have hn6s : ¬ s ∣ 6 := by
    intro hd
    have := Nat.le_of_dvd (by norm_num) hd
    interval_cases s <;> first | omega | exact absurd hs (by norm_num)
  have h4 := le_localRank_statedSU_torus (k := 3) hU hs hsd (by norm_num) (Or.inr hn6s)
  have hs2 : s ≠ 2 := by omega
  have hZ : ¬ s ∣ Nat.card (Subgroup.center I) := fun hd =>
    hn6s ((hd.trans (card_center_dvd_gcd_six hGA hperf hf hmodel)).trans (Nat.gcd_dvd_left 6 _))
  refine ⟨s, hs, hs2, ?_⟩
  calc 4 ≤ localRank s (StatedProj (StatedSU 6 (2 ^ f) K)) := h4
    _ = localRank s (I ⧸ Subgroup.center I) := (localRank_eq_of_mulEquiv e hs).symm
    _ ≤ localRank s I :=
        CFSG.RankThree.Classical2.localRank_quotient_le hs hs2 (Subgroup.center I) hZ

theorem exists_localRank_four_of_psu_six
    (hGA : CFSG.Open.GriessAllModelsStatement)
    {I : Type} [Group I] [Finite I] (hperf : Group.IsPerfect I) {f : ℕ} (hf : 3 ≤ f)
    (hmodel : StatedClassicalModel (I ⧸ Subgroup.center I) .PSU 6 2 f) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ 4 ≤ localRank r I := by
  by_cases hf3 : f = 3
  · subst hf3
    exact ⟨3, Nat.prime_three, by norm_num, four_le_localRank_psu_six_eight hGA hperf hmodel⟩
  · exact exists_localRank_four_of_psu_six_ne_three hGA hperf (by omega) hf3 hmodel

theorem false_of_psu_six
    (hGA : CFSG.Open.GriessAllModelsStatement)
    {G : Type} [Group G] [Finite G] {I : Subgroup G} (hperf : Group.IsPerfect ↥I) {f : ℕ}
    (hf : 3 ≤ f) (hmodel : StatedClassicalModel (↥I ⧸ Subgroup.center ↥I) .PSU 6 2 f)
    (he : CFSG.twoLocalOddRank G = 3) : False := by
  obtain ⟨r, hr, hr2, h4⟩ := exists_localRank_four_of_psu_six hGA hperf hf hmodel
  have h5 : 4 ≤ localRank r G := h4.trans (CFSG.RankThree.PartTwo.localRank_subgroup_le hr I)
  have hrG : r ∣ Nat.card G :=
    CFSG.RankThree.LocalRank.prime_dvd_card_of_localRank_pos hr (by omega)
  have h3 := CFSG.RankThree.Theta.localRank_le_twoLocalOddRank hr hr2 hrG
  omega

end CFSG.RankThree.PartOne.K1320
