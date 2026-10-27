module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U34NormalizerRanksHolds
public import CFSG.RankThree.PartTwo.Sec14.Ronan148JHJSix
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20ya

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.SU3
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped Matrix

theorem exists_mem_u34FiveScalar_mul_eq {K : Type} [Field K] [Finite K] (hK : Nat.card K = 16)
    {x : MulAut (StdMod (Fin 3) K)} (hx : x ∈ natScalImage K ⊔ natImage (StatedSU 3 4 K))
    {k : ℕ} (hk : orderOf x = 5 ^ k) :
    ∃ s ∈ u34FiveScalar K, ∃ l ∈ natImage (StatedSU 3 4 K), s * l = x := by
  obtain ⟨s, hs, l, hl, hxsl⟩ :=
    (CFSG.mem_sup_of_commute fun a ha b hb => commute_of_mem_natImage_statedScalars ha hb).mp hx
  refine ⟨s, ?_, l, hl, hxsl⟩
  have hcomm : Commute s l := commute_of_mem_natImage_statedScalars hs hl
  have hdvd_mul : orderOf s ∣ orderOf (s * l) := by
    rw [orderOf_dvd_iff_pow_eq_one]
    have h1 : (s * l) ^ orderOf (s * l) = 1 := pow_orderOf_eq_one _
    have h2 : s ^ orderOf (s * l) * l ^ orderOf (s * l) = 1 := by
      rw [← hcomm.mul_pow (orderOf (s * l)), h1]
    have h3 : s ^ orderOf (s * l) = (l ^ orderOf (s * l))⁻¹ :=
      eq_inv_of_mul_eq_one_left h2
    have h4 : s ^ orderOf (s * l) ∈ natScalImage K := Subgroup.pow_mem _ hs _
    have h5 : (l ^ orderOf (s * l))⁻¹ ∈ natImage (StatedSU 3 4 K) :=
      Subgroup.inv_mem _ (Subgroup.pow_mem _ hl _)
    rw [h3] at h4
    have h6 : (l ^ orderOf (s * l))⁻¹ ∈ natScalImage K ⊓ natImage (StatedSU 3 4 K) := ⟨h4, h5⟩
    rw [natScalImage_inf_natImage_statedSU hK, Subgroup.mem_bot] at h6
    rw [h3, h6]
  rw [hxsl, hk] at hdvd_mul
  have hS0 : IsMulCommutative ↥(natScalImage K) := by
    have : IsMulCommutative ↥(StatedScalars (Fin 3) K) :=
      Subgroup.range_isMulCommutative (Matrix.GeneralLinearGroup.scalar (Fin 3))
    exact Subgroup.range_isMulCommutative (natAut (StatedScalars (Fin 3) K))
  exact (uc22pws_mem_pCoreOf_iff Nat.prime_five hS0).mpr
    ⟨hs, k, orderOf_dvd_iff_pow_eq_one.mp hdvd_mul⟩

theorem k_U34FiveResidual_holds : K_U34FiveResidual := by
  intro K _ _ hK X hLX hXN
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hK' : Nat.card K = (2 ^ 2) ^ 2 := by rw [hK]; norm_num
  let Γ : Subgroup (GL (Fin 3) K) := StatedSU 3 4 K
  let N : Subgroup (MulAut (StdMod (Fin 3) K)) := natNorm Γ
  let L : Subgroup (MulAut (StdMod (Fin 3) K)) := natImage Γ
  let S0 : Subgroup (MulAut (StdMod (Fin 3) K)) := natScalImage K
  let Z : Subgroup (MulAut (StdMod (Fin 3) K)) := u34FiveScalar K
  let KxS : Subgroup (MulAut (StdMod (Fin 3) K)) := S0 ⊔ L
  have hKxS_eq : N ⊓ linSub = KxS := by
    change natNorm Γ ⊓ linSub = natScalImage K ⊔ natImage Γ
    rw [show natImage Γ = natImage (StatedSU 3 4 K) from rfl]
    exact natNorm_statedSU_inf_linSub_eq hK
  have hS0N : S0 ≤ N := natImage_statedScalars_le_natNorm _
  have hLN : L ≤ N := by
    change natImage Γ ≤ natNorm Γ
    exact Subgroup.le_normalizer
  have hKxSN : KxS ≤ N := sup_le hS0N hLN
  have hZle : Z ≤ S0 := by
    change (CFSG.pCore 5 ↥S0).map S0.subtype ≤ S0
    exact Subgroup.map_subtype_le _
  have hKxScard : Nat.card ↥KxS = 936000 := by
    rw [← hKxS_eq]
    exact card_natNorm_statedSU_inf_linSub hK
  have hsubcard : Nat.card ↥(KxS.subgroupOf N) = Nat.card ↥KxS := by
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1.1, x.2⟩
        invFun := fun x => ⟨⟨x.1, hKxSN x.2⟩, x.2⟩
        left_inv := fun x => rfl
        right_inv := fun x => rfl }
  have hKxSindex : (KxS.subgroupOf N).index = 4 := by
    have h := Subgroup.index_mul_card (KxS.subgroupOf N)
    rw [hsubcard, hKxScard, card_natNorm_statedSU_three_four hK] at h
    have hnum : 2 ^ 8 * 3 ^ 2 * 5 ^ 3 * 13 = 4 * 936000 := by norm_num
    rw [hnum] at h
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h
  have hmemKxS : ∀ x ∈ N, (∃ k : ℕ, orderOf x = 5 ^ k) → x ∈ KxS := by
    intro x hxN hex
    obtain ⟨k, hk⟩ := hex
    have hxP : IsPGroup 5 ↥(Subgroup.zpowers (⟨x, hxN⟩ : ↥N)) := by
      rw [IsPGroup.iff_orderOf]
      intro z
      have hdvd : orderOf z ∣ orderOf (⟨x, hxN⟩ : ↥N) := by
        rw [← Subgroup.orderOf_coe z]
        exact orderOf_dvd_of_mem_zpowers z.2
      have hxord : orderOf (⟨x, hxN⟩ : ↥N) = orderOf x := Subgroup.orderOf_mk x hxN
      rw [hxord, hk] at hdvd
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_five).mp hdvd
      exact ⟨j, hj⟩
    let α := ↥N ⧸ KxS.subgroupOf N
    let b : α := QuotientGroup.mk (1 : ↥N)
    have hα : Nat.card α = 4 := by
      rw [← Subgroup.index_eq_card]
      exact hKxSindex
    obtain ⟨n, hn⟩ := IsPGroup.card_orbit (p := 5) hxP (α := α) b
    have hle : 5 ^ n ≤ 4 := by
      rw [← hn]
      have h := Nat.card_le_card_of_injective
        (f := (Subtype.val : ↥(MulAction.orbit (Subgroup.zpowers (⟨x, hxN⟩ : ↥N)) b) → α))
        Subtype.val_injective
      rwa [hα] at h
    have hn0 : n = 0 := by
      by_contra h
      have h1 : 5 ≤ 5 ^ n := by
        calc 5 = 5 ^ 1 := by norm_num
          _ ≤ 5 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hO1 : Nat.card ↥(MulAction.orbit (Subgroup.zpowers (⟨x, hxN⟩ : ↥N)) b) = 1 := by
      rw [hn, hn0, pow_zero]
    have hb : b ∈ MulAction.orbit (Subgroup.zpowers (⟨x, hxN⟩ : ↥N)) b :=
      MulAction.mem_orbit_self b
    have hxb : (⟨x, hxN⟩ : ↥N) • b ∈
        MulAction.orbit (Subgroup.zpowers (⟨x, hxN⟩ : ↥N)) b :=
      MulAction.mem_orbit_iff.mpr ⟨⟨⟨x, hxN⟩, Subgroup.mem_zpowers _⟩, rfl⟩
    have hEq : (⟨x, hxN⟩ : ↥N) • b = b := by
      obtain ⟨y, hy⟩ := Nat.card_eq_one_iff_exists.mp hO1
      have h1 : (⟨b, hb⟩ : ↥(MulAction.orbit (Subgroup.zpowers (⟨x, hxN⟩ : ↥N)) b)) = y :=
        hy _
      have h2 : (⟨_, hxb⟩ : ↥(MulAction.orbit (Subgroup.zpowers (⟨x, hxN⟩ : ↥N)) b)) = y :=
        hy _
      exact congrArg Subtype.val (h2.trans h1.symm)
    have hq : (QuotientGroup.mk (s := KxS.subgroupOf N) (⟨x, hxN⟩ : ↥N)) =
        (QuotientGroup.mk (s := KxS.subgroupOf N) (1 : ↥N)) := by
      have hx1 : (⟨x, hxN⟩ : ↥N) = (⟨x, hxN⟩ : ↥N) * 1 := by rw [mul_one]
      rw [hx1]
      change (QuotientGroup.mk (s := KxS.subgroupOf N)
        ((⟨x, hxN⟩ : ↥N) • (1 : ↥N))) =
        (QuotientGroup.mk (s := KxS.subgroupOf N) (1 : ↥N))
      rw [← MulAction.Quotient.smul_coe (H := KxS.subgroupOf N)]
      simpa [α, b] using hEq
    have hmem : (⟨x, hxN⟩ : ↥N) ∈ KxS.subgroupOf N := by
      have h := QuotientGroup.eq.mp hq
      simpa using (KxS.subgroupOf N).inv_mem h
    exact Subgroup.mem_subgroupOf.mp hmem
  have h5L : 5 ∣ Nat.card ↥L := by
    change 5 ∣ Nat.card ↥(natImage Γ)
    rw [show natImage Γ = natImage (StatedSU 3 4 K) from rfl, card_natImage_statedSU_three_four hK]
    norm_num
  have hProjSimple : IsSimpleGroup (StatedProj Γ) := by
    change IsSimpleGroup (StatedProj (StatedSU 3 4 K))
    exact CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K 2 2 hK' 3
      (by norm_num) (by norm_num)
  have hΓsimple : IsSimpleGroup Γ := by
    change IsSimpleGroup (StatedSU 3 4 K)
    exact (statedProjStatedSUEquiv hK).symm.isSimpleGroup
  have hLsimple : IsSimpleGroup ↥L := by
    have hinj : Function.Injective (natAut Γ) :=
      matHom_injective.comp Subtype.coe_injective
    exact (MonoidHom.ofInjective hinj).symm.isSimpleGroup
  have hOppL : Opp 5 L = L := by
    apply le_antisymm
    · change CFSG.RankThree.PartOne.pElementSubgroup 5 L ≤ L
      exact (Subgroup.closure_le _).mpr (fun x hx => hx.1)
    · have hcl := CFSG.RankThree.PartTwo.Sec14.Ronan148J.closure_pow_eq_top
        (G := ↥L) h5L
      have hle : (Subgroup.closure {z : ↥L | z ^ 5 = 1}).map L.subtype ≤
          CFSG.RankThree.PartOne.pElementSubgroup 5 L := by
        rw [Subgroup.map_le_iff_le_comap]
        refine (Subgroup.closure_le _).mpr ?_
        intro z hz
        refine Subgroup.subset_closure ⟨z.2, ?_⟩
        have hdvd : orderOf z ∣ 5 := orderOf_dvd_of_pow_eq_one hz
        rcases (Nat.dvd_prime Nat.prime_five).mp hdvd with h1 | h1
        · refine ⟨0, ?_⟩
          rw [pow_zero]
          simpa [Subgroup.orderOf_coe] using h1
        · refine ⟨1, ?_⟩
          rw [pow_one]
          simpa [Subgroup.orderOf_coe] using h1
      intro x hx
      let y : ↥L := ⟨x, hx⟩
      have hy : y ∈ Subgroup.closure {z : ↥L | z ^ 5 = 1} := by
        rw [hcl]
        exact Subgroup.mem_top y
      exact hle (Subgroup.mem_map.mpr ⟨y, hy, rfl⟩)
  have hOppL_le : L ≤ Opp 5 X := by
    rw [← hOppL]
    change CFSG.RankThree.PartOne.pElementSubgroup 5 L ≤
      CFSG.RankThree.PartOne.pElementSubgroup 5 X
    refine (Subgroup.closure_le _).mpr ?_
    intro x hx
    exact Subgroup.subset_closure ⟨hLX hx.1, hx.2⟩
  have hOpp_le : Opp 5 X ≤ L ⊔ Z := by
    change CFSG.RankThree.PartOne.pElementSubgroup 5 X ≤ L ⊔ Z
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hxX, k, hk⟩
    obtain ⟨s, hsZ, l, hl, hxsl⟩ :=
      exists_mem_u34FiveScalar_mul_eq hK (hmemKxS x (hXN hxX) ⟨k, hk⟩) hk
    rw [← hxsl, sup_comm]
    exact Subgroup.mul_mem_sup hsZ hl
  by_cases h : Opp 5 X = L
  · exact Or.inl h
  · right
    have hnotle : ¬ Opp 5 X ≤ L := by
      intro hle
      exact h (le_antisymm hle hOppL_le)
    have hex : ∃ x ∈ X, x ∉ L ∧ ∃ k : ℕ, orderOf x = 5 ^ k := by
      by_contra hcon
      push Not at hcon
      apply hnotle
      change CFSG.RankThree.PartOne.pElementSubgroup 5 X ≤ L
      refine (Subgroup.closure_le _).mpr ?_
      rintro x ⟨hxX, k, hk⟩
      by_cases hxL : x ∈ L
      · exact hxL
      · exact (hcon x hxX hxL k hk).elim
    obtain ⟨x, hxX, hxL, k, hk⟩ := hex
    have hxN : x ∈ N := hXN hxX
    have hxKxS : x ∈ KxS := hmemKxS x hxN ⟨k, hk⟩
    obtain ⟨s, hsZ, l, hl, hxsl⟩ := exists_mem_u34FiveScalar_mul_eq hK hxKxS hk
    have hsL : s ∉ L := by
      intro hsL
      apply hxL
      rw [← hxsl]
      exact Subgroup.mul_mem _ hsL hl
    have hs1 : s ≠ 1 := by
      intro hs1
      apply hsL
      rw [hs1]
      exact Subgroup.one_mem _
    have hsOpp : s ∈ Opp 5 X := by
      have hxOpp : x ∈ Opp 5 X := Subgroup.subset_closure ⟨hxX, k, hk⟩
      have hlOpp : l ∈ Opp 5 X := hOppL_le hl
      rw [show s = x * l⁻¹ by rw [← hxsl]; group]
      exact Subgroup.mul_mem _ hxOpp (Subgroup.inv_mem _ hlOpp)
    have hZcard : Nat.card ↥Z = 5 := by
      have hZP : IsPGroup 5 ↥Z := by
        change IsPGroup 5 ↥(pCoreOf 5 S0)
        rw [show pCoreOf 5 S0 = (CFSG.pCore 5 ↥S0).map S0.subtype from rfl]
        exact CFSG.pCore_isPGroup.map S0.subtype
      obtain ⟨j, hj⟩ := hZP.exists_card_eq
      have hdvd : Nat.card ↥Z ∣ 15 := by
        have h := Subgroup.card_dvd_of_le hZle
        rwa [show Nat.card ↥S0 = 15 from card_natScalImage hK] at h
      have hle : 5 ^ j ≤ 15 := Nat.le_of_dvd (by norm_num) (hj ▸ hdvd)
      have hj1 : j = 1 := by
        rcases j with _ | j
        · rw [pow_zero] at hj
          exact absurd (Subgroup.card_eq_one.mp hj) (by
            intro hbot
            have : s ∈ (⊥ : Subgroup (MulAut (StdMod (Fin 3) K))) := hbot ▸ hsZ
            rw [Subgroup.mem_bot] at this
            exact hs1 this)
        · rcases j with _ | j
          · rfl
          · exfalso
            have : 5 ^ (j + 1 + 1) ≤ 15 := by simpa using hle
            have h25 : 25 ≤ 5 ^ (j + 1 + 1) := by
              calc 25 = 5 ^ 2 := by norm_num
                _ ≤ 5 ^ (j + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
            omega
      rw [hj1, pow_one] at hj
      exact hj
    have hsord : orderOf s = 5 := by
      have hsP : orderOf s ∣ Nat.card ↥Z := by
        have h := orderOf_dvd_natCard (⟨s, hsZ⟩ : ↥Z)
        rwa [Subgroup.orderOf_mk] at h
      rw [hZcard] at hsP
      rcases (Nat.dvd_prime Nat.prime_five).mp hsP with h2 | h2
      · exact absurd (orderOf_eq_one_iff.mp h2) hs1
      · exact h2
    have hZleOpp : Z ≤ Opp 5 X := by
      intro z hz
      by_cases hz1 : z = 1
      · rw [hz1]
        exact Subgroup.one_mem _
      · have hzord : orderOf z = 5 := by
          have hzP : orderOf z ∣ Nat.card ↥Z := by
            have h := orderOf_dvd_natCard (⟨z, hz⟩ : ↥Z)
            rwa [Subgroup.orderOf_mk] at h
          rw [hZcard] at hzP
          rcases (Nat.dvd_prime Nat.prime_five).mp hzP with h1 | h1
          · exact absurd (orderOf_eq_one_iff.mp h1) hz1
          · exact h1
        have hzZ : Subgroup.zpowers z = Z := by
          refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hz) ?_
          rw [Nat.card_zpowers, hzord, hZcard]
        have hszle : Subgroup.zpowers s ≤ Subgroup.zpowers z := by
          rw [Subgroup.zpowers_le, hzZ]
          exact hsZ
        have hsz : Subgroup.zpowers s = Subgroup.zpowers z := by
          refine Subgroup.eq_of_le_of_card_ge hszle ?_
          rw [Nat.card_zpowers, Nat.card_zpowers, hsord, hzord]
        have hzmem : z ∈ Subgroup.zpowers z := Subgroup.mem_zpowers z
        rw [← hsz] at hzmem
        exact Subgroup.zpowers_le.mpr hsOpp hzmem
    exact le_antisymm hOpp_le (sup_le hOppL_le hZleOpp)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
