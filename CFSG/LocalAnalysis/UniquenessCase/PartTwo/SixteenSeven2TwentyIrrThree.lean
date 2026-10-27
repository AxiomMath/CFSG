module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenResults2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCase2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyEndAlt
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyEndOmega
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyEndLn
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyOdd
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyIrrAbs
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.Bridge
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOAut
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOCoords
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOEightSwap
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOKlein
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOPlusLevi
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Quot
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12b
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenAk
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B216Quotient
public import CFSG.Quasithin.Background.B5CompA
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.C124B51Hyp
public import CFSG.Quasithin.Background.C124BlkTransfer
public import CFSG.Quasithin.Background.C124InterfaceDefs
public import CFSG.Quasithin.Background.C1GNC124
public import CFSG.Quasithin.Background.C1GNSolvConnect
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.F918V2GDA
public import CFSG.Quasithin.Background.InternalSecAutOn
public import CFSG.Quasithin.Background.InternalSecB4
public import CFSG.Quasithin.EmptyFaithful.S14117
public import CFSG.Quasithin.EmptyFaithful.S14117Coprime
public import CFSG.Quasithin.EmptyFaithful.S14117Rank
public import CFSG.Quasithin.EmptyFaithful.S1417Glue
public import CFSG.Quasithin.EmptyFaithful.S1421Defs
public import CFSG.Quasithin.EmptyFaithful.S151ZC
public import CFSG.Quasithin.EmptyFaithful.S151cA2
public import CFSG.Quasithin.EmptyFaithful.S151cCases
public import CFSG.Quasithin.EmptyFaithful.S152UGen
public import CFSG.Quasithin.EmptyFaithful.S153ZN
public import CFSG.Quasithin.EmptyFaithful.S153ZO
public import CFSG.Quasithin.EmptyFaithful.S153ZP
public import CFSG.Quasithin.EmptyFaithful.T1515Top9
public import CFSG.Quasithin.H13.J4Core
public import CFSG.Quasithin.Vol2.Ch3Sec1Thm311
public import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearBridge

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem s16c167_perm_fin_three_cube_transitive :
    ∀ g : Equiv.Perm (Fin 3), g ^ 3 = 1 → g ≠ 1 →
    ∀ i j : Fin 3, ∃ t : Fin 3, (g ^ (t : ℕ)) i = j := by
  decide

private theorem s16c167_perm_fin_three_centralizer_cube :
    ∀ g h : Equiv.Perm (Fin 3), g ^ 3 = 1 → g ≠ 1 → h * g = g * h → h ^ 3 = 1 := by
  decide

private theorem s16c167_exists_mul_of_mem_sup_of_commute {A : Type*} [Group A]
    {K L : Subgroup A} (hcomm : ∀ k ∈ K, ∀ l ∈ L, k * l = l * k) {x : A}
    (hx : x ∈ K ⊔ L) : ∃ k ∈ K, ∃ l ∈ L, k * l = x := by
  rw [Subgroup.sup_eq_closure] at hx
  refine Subgroup.closure_induction (p := fun x _ => ∃ k ∈ K, ∃ l ∈ L, k * l = x)
    ?_ ?_ ?_ ?_ hx
  · intro y hy
    rcases hy with hy | hy
    · exact ⟨y, hy, 1, L.one_mem, mul_one y⟩
    · exact ⟨1, K.one_mem, y, hy, one_mul y⟩
  · exact ⟨1, K.one_mem, 1, L.one_mem, mul_one 1⟩
  · intro y z hy hz hyz hyz'
    obtain ⟨k₁, hk₁, l₁, hl₁, rfl⟩ := hyz
    obtain ⟨k₂, hk₂, l₂, hl₂, rfl⟩ := hyz'
    refine ⟨k₁ * k₂, K.mul_mem hk₁ hk₂, l₁ * l₂, L.mul_mem hl₁ hl₂, ?_⟩
    calc (k₁ * k₂) * (l₁ * l₂) = k₁ * (k₂ * l₁) * l₂ := by group
      _ = k₁ * (l₁ * k₂) * l₂ := by rw [hcomm k₂ hk₂ l₁ hl₁]
      _ = (k₁ * l₁) * (k₂ * l₂) := by group
  · intro y hy hyz
    obtain ⟨k, hk, l, hl, rfl⟩ := hyz
    refine ⟨k⁻¹, K.inv_mem hk, l⁻¹, L.inv_mem hl, ?_⟩
    calc k⁻¹ * l⁻¹ = (l * k)⁻¹ := by group
      _ = (k * l)⁻¹ := by rw [hcomm k hk l hl]

theorem s16c167_irr_three (D : Data G) {V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hC : Counterex16 D ⊥ V L hV) (hS : Case168_2Small D ⊥ V hV L) :
    ∃ (F : Fin 3 → Subgroup (Vtil ⊥ V hV))
      (π : ↥(Mbar D.M ⊥ V hV) →* Equiv.Perm (Fin 3)),
      Function.Injective F ∧ irrBar L ⊥ V hV = Set.range F ∧
      (∀ (x : ↥(Mbar D.M ⊥ V hV)) (i : Fin 3),
        (F i).map (x : MulAut (Vtil ⊥ V hV)).toMonoidHom = F (π x i)) ∧
      (∀ x : ↥(Mbar D.M ⊥ V hV), (∃ k : ℕ, x ^ (2 ^ k) = 1) →
        ((∀ y ∈ oddBar D.M ⊥ V hV, (x : MulAut (Vtil ⊥ V hV)) * y = y * x) ↔ π x = 1)) ∧
      (∀ i j : Fin 3, ∃ y : ↥(Mbar D.M ⊥ V hV),
        (y : MulAut (Vtil ⊥ V hV)) ∈ oddBar D.M ⊥ V hV ∧ π y i = j) := by
  have h2 : Case168_2 D ⊥ V hV L := hS.case168_2
  have hK : IsSym ↥(kBar D.M ⊥ V hV L) 3 := hS.1
  obtain ⟨L₀, hI, hfam⟩ := hS.2.1
  have key : ∃ J₀ J₁ : Subgroup (Vtil ⊥ V hV),
      J₀ ∈ irrSet (lBar ⊥ V hV L) ∧ J₁ ∈ irrSet (lBar ⊥ V hV L) ∧
      J₀ ⊓ J₁ = ⊥ ∧ J₀ ⊔ J₁ = ⊤ ∧
      Z391.EndUnitsTrivial (lBar ⊥ V hV L) J₀ ∧
      Z391.EndUnitsTrivial (lBar ⊥ V hV L) J₁ := by
    rcases hfam with ⟨-, -, hsum⟩ | ⟨-, -, hsum⟩ | ⟨-, -, hsum⟩ | ⟨-, -, hsum⟩
    · obtain ⟨J₀, J₁, hN₀, hN₁, hinf, hsup⟩ := s16c167_sumOfNat_two hsum
      exact ⟨J₀, J₁,
        s16c167_mem_irrSet_alt (n := 6) (by norm_num) hN₀,
        s16c167_mem_irrSet_alt (n := 6) (by norm_num) hN₁, hinf, hsup,
        s16c167_endUnits_alt (n := 6) (by norm_num) hN₀,
        s16c167_endUnits_alt (n := 6) (by norm_num) hN₁⟩
    · obtain ⟨J₀, J₁, hN₀, hN₁, hinf, hsup⟩ := s16c167_sumOfNat_two hsum
      exact ⟨J₀, J₁,
        s16c167_mem_irrSet_alt (n := 7) (by norm_num) hN₀,
        s16c167_mem_irrSet_alt (n := 7) (by norm_num) hN₁, hinf, hsup,
        s16c167_endUnits_alt (n := 7) (by norm_num) hN₀,
        s16c167_endUnits_alt (n := 7) (by norm_num) hN₁⟩
    · obtain ⟨J₀, J₁, hN₀, hN₁, hinf, hsup⟩ := s16c167_sumOfNat_two hsum
      exact ⟨J₀, J₁,
        s16c167_mem_irrSet_ln (m := 4) (by norm_num) hN₀,
        s16c167_mem_irrSet_ln (m := 4) (by norm_num) hN₁, hinf, hsup,
        s16c167_endUnits_ln (m := 4) (by norm_num) hN₀,
        s16c167_endUnits_ln (m := 4) (by norm_num) hN₁⟩
    · obtain ⟨J₀, J₁, hN₀, hN₁, hinf, hsup⟩ := s16c167_sumOfNat_two hsum
      exact ⟨J₀, J₁,
        s16c167_mem_irrSet_omegaMinus (Or.inl rfl) hN₀,
        s16c167_mem_irrSet_omegaMinus (Or.inl rfl) hN₁, hinf, hsup,
        s16c167_endUnits_omegaMinus hN₀,
        s16c167_endUnits_omegaMinus hN₁⟩
  obtain ⟨J₀, J₁, hJ0, hJ1, hinf, hsup, hE₀, hE₁⟩ := key
  have hW : ∀ w : Vtil ⊥ V hV, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one ⊥ V hV
  have hsimple : IsSimpleGroup ↥(lBar ⊥ V hV L) := s16c167_cfg2_simple D h2
  have hfix : fixV (lBar ⊥ V hV L) = ⊥ := s16c167_cfg2_fix D h2
  have hLbot : lBar ⊥ V hV L ≠ ⊥ := by
    haveI := hsimple.toNontrivial
    exact (Subgroup.nontrivial_iff_ne_bot _).1 inferInstance
  have hall : commSub ⊤ (lBar ⊥ V hV L) = ⊤ := by
    refine top_le_iff.1 (hsup.symm.le.trans (sup_le ?_ ?_))
    · calc J₀ = commSub J₀ (lBar ⊥ V hV L) := hJ0.1.symm
        _ ≤ commSub ⊤ (lBar ⊥ V hV L) := commSub_mono le_top le_rfl
    · calc J₁ = commSub J₁ (lBar ⊥ V hV L) := hJ1.1.symm
        _ ≤ commSub ⊤ (lBar ⊥ V hV L) := commSub_mono le_top le_rfl
  have hLX : lBar ⊥ V hV L ≤ Mbar D.M ⊥ V hV :=
    barSub_mono ⊥ V hV hC.setting.hyp151.le
  have hnorm : ∀ x ∈ Mbar D.M ⊥ V hV,
      (lBar ⊥ V hV L).map (MulAut.conj x).toMonoidHom = lBar ⊥ V hV L := by
    obtain ⟨t, -, -, -, -, hW136⟩ := hC.conc
    exact s16c167_cfg2_normal hLbot hall hW136
  have hcenter : ∀ κ ∈ kBar D.M ⊥ V hV L,
      (∀ y ∈ kBar D.M ⊥ V hV L, y * κ = κ * y) → κ = 1 := by
    intro κ hκ hc
    have h1 := s16c167_center_of_isSym_three hK ⟨κ, hκ⟩ (fun y => Subtype.ext (hc y y.2))
    simpa using congrArg Subtype.val h1
  have hperf : ⁅lBar ⊥ V hV L, lBar ⊥ V hV L⁆ = lBar ⊥ V hV L :=
    s16c167_cfg2_perfect hLX hsimple rfl hcenter
  have F : Cfg2Setting (Mbar D.M ⊥ V hV) (lBar ⊥ V hV L) J₀ J₁ :=
    ⟨hW, hnorm, hsimple, hperf, hfix, hJ0, hJ1, hinf, hsup⟩
  have hKX : kBar D.M ⊥ V hV L ≤ Mbar D.M ⊥ V hV :=
    fun _ hx => (Subgroup.mem_inf.1 hx).1
  have hKL : ∀ k ∈ kBar D.M ⊥ V hV L, ∀ l ∈ lBar ⊥ V hV L, k * l = l * k := by
    intro k hk l hl
    rw [kBar, Subgroup.mem_inf] at hk
    exact ((Subgroup.mem_centralizer_iff.1 hk.2) l hl).symm
  obtain ⟨G3, π, hG3inj, hrange, hact, hsurj, hfaith⟩ :=
    s16c167_irr_three_abs (W := Vtil ⊥ V hV) F hKX hKL hK hE₀ hE₁
  have hodd := s16c167_oddBar_case2 D h2
  haveI : Nontrivial ↥(oddBar D.M ⊥ V hV) := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    have h1 : Nat.card ↥(oddBar D.M ⊥ V hV) = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨1⟩⟩
    rw [hodd.2] at h1
    norm_num at h1
  obtain ⟨y0, hy0⟩ := exists_ne (1 : ↥(oddBar D.M ⊥ V hV))
  have hy0cube : (y0 : ↥(oddBar D.M ⊥ V hV)) ^ 3 = 1 := by
    have h := pow_card_eq_one' (x := y0) (G := ↥(oddBar D.M ⊥ V hV))
    rwa [hodd.2] at h
  let ky : ↥(kBar D.M ⊥ V hV L) := ⟨(y0 : MulAut (Vtil ⊥ V hV)), hodd.1 y0.2⟩
  let yM : ↥(Mbar D.M ⊥ V hV) := ⟨(ky : MulAut (Vtil ⊥ V hV)), hKX ky.2⟩
  have hyMval : (yM : MulAut (Vtil ⊥ V hV)) ^ 3 = 1 := by
    change ((y0 : MulAut (Vtil ⊥ V hV))) ^ 3 = 1
    have h := congrArg (fun z : ↥(oddBar D.M ⊥ V hV) => (z : MulAut (Vtil ⊥ V hV))) hy0cube
    simpa using h
  have hyMcube : yM ^ 3 = 1 := Subtype.ext hyMval
  have hg3 : (π yM) ^ 3 = 1 := by
    rw [← map_pow, hyMcube, map_one]
  have hgy0ne : π yM ≠ 1 := by
    intro h
    have hk1 : ky = 1 := hfaith ky h
    have hval : (y0 : MulAut (Vtil ⊥ V hV)) = 1 := congrArg Subtype.val hk1
    exact hy0 (Subtype.ext hval)
  refine ⟨G3, π, hG3inj, hrange, hact, ?_, ?_⟩
  · intro x hx2
    constructor
    · intro hxc
      have hxcomm : (x : MulAut (Vtil ⊥ V hV)) * (y0 : MulAut (Vtil ⊥ V hV)) =
          (y0 : MulAut (Vtil ⊥ V hV)) * (x : MulAut (Vtil ⊥ V hV)) :=
        hxc (y0 : MulAut (Vtil ⊥ V hV)) y0.2
      have hcomm_sub : x * yM = yM * x := Subtype.ext hxcomm
      have hcommπ : π x * π yM = π yM * π x := by
        rw [← map_mul, ← map_mul, hcomm_sub]
      have hh3 : (π x) ^ 3 = 1 :=
        s16c167_perm_fin_three_centralizer_cube (π yM) (π x) hg3 hgy0ne hcommπ
      obtain ⟨k, hk⟩ := hx2
      have hh2 : (π x) ^ (2 ^ k) = 1 := by
        rw [← map_pow, hk, map_one]
      have hdiv3 : orderOf (π x) ∣ 3 := orderOf_dvd_iff_pow_eq_one.2 hh3
      have hdiv2 : orderOf (π x) ∣ 2 ^ k := orderOf_dvd_iff_pow_eq_one.2 hh2
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).1 hdiv3 with h1 | h3
      · exact orderOf_eq_one_iff.1 h1
      · exfalso
        rw [h3] at hdiv2
        have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 3) hdiv2
        norm_num at h32
    · intro hπx y hy
      have hIsup : kBar D.M ⊥ V hV L ⊔ L₀ = Mbar D.M ⊥ V hV := hI.2.2
      have hKL0 : ∀ k ∈ kBar D.M ⊥ V hV L, ∀ l ∈ L₀, k * l = l * k := by
        intro k hk l hl
        have hkcent : k ∈ Subgroup.centralizer (L₀ : Set (MulAut (Vtil ⊥ V hV))) :=
          (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hI.1) hk
        exact (Subgroup.mem_centralizer_iff.1 hkcent l hl).symm
      have hxsup : (x : MulAut (Vtil ⊥ V hV)) ∈
          kBar D.M ⊥ V hV L ⊔ L₀ := hIsup.symm ▸ x.2
      obtain ⟨κ, hκ, l, hl, hκl⟩ :=
        s16c167_exists_mul_of_mem_sup_of_commute hKL0 hxsup
      have hKM : kBar D.M ⊥ V hV L ≤ Mbar D.M ⊥ V hV := hKX
      have hL0M : L₀ ≤ Mbar D.M ⊥ V hV := hIsup ▸ le_sup_right
      let lM : ↥(Mbar D.M ⊥ V hV) := ⟨l, hL0M hl⟩
      have hπl : π lM = 1 := by
        have hcent : ∀ σ : Equiv.Perm (Fin 3), σ * π lM = π lM * σ := by
          intro σ
          obtain ⟨k, hk⟩ := hsurj σ
          have hcomm_sub : (⟨(k : MulAut (Vtil ⊥ V hV)), hKX k.2⟩ : ↥(Mbar D.M ⊥ V hV)) * lM =
              lM * ⟨(k : MulAut (Vtil ⊥ V hV)), hKX k.2⟩ := by
            apply Subtype.ext
            exact hKL0 (k : MulAut (Vtil ⊥ V hV)) k.2 l hl
          calc σ * π lM = π ⟨(k : MulAut (Vtil ⊥ V hV)), hKX k.2⟩ * π lM := by rw [hk]
            _ = π (⟨(k : MulAut (Vtil ⊥ V hV)), hKX k.2⟩ * lM) := by rw [map_mul]
            _ = π (lM * ⟨(k : MulAut (Vtil ⊥ V hV)), hKX k.2⟩) := by rw [hcomm_sub]
            _ = π lM * π ⟨(k : MulAut (Vtil ⊥ V hV)), hKX k.2⟩ := by rw [map_mul]
            _ = π lM * σ := by rw [hk]
        have hcenter_perm : ∀ κ : Equiv.Perm (Fin 3),
            (∀ y : Equiv.Perm (Fin 3), y * κ = κ * y) → κ = 1 :=
          s16c167_center_of_isSym_three (A := Equiv.Perm (Fin 3)) ⟨MulEquiv.refl _⟩
        exact hcenter_perm (π lM) hcent
      have hx_decomp : x = (⟨κ, hKM hκ⟩ : ↥(Mbar D.M ⊥ V hV)) * lM := by
        apply Subtype.ext
        exact hκl.symm
      have hπκ : π (⟨κ, hKM hκ⟩ : ↥(Mbar D.M ⊥ V hV)) = 1 := by
        have h1 : π x = π ((⟨κ, hKM hκ⟩ : ↥(Mbar D.M ⊥ V hV)) * lM) := by rw [hx_decomp]
        rw [h1, map_mul, hπl, mul_one] at hπx
        exact hπx
      have hκ1 : (⟨κ, hκ⟩ : ↥(kBar D.M ⊥ V hV L)) = 1 := hfaith ⟨κ, hκ⟩ hπκ
      have hκval : κ = 1 := congrArg Subtype.val hκ1
      have hx_eq_l : (x : MulAut (Vtil ⊥ V hV)) = l := by
        rw [← hκl, hκval, one_mul]
      rw [hx_eq_l]
      exact (hKL0 y (hodd.1 hy) l hl).symm
  · intro i j
    obtain ⟨t, ht⟩ := s16c167_perm_fin_three_cube_transitive (π yM) hg3 hgy0ne i j
    refine ⟨yM ^ (t : ℕ), ?_, ?_⟩
    · show ((yM ^ (t : ℕ) : ↥(Mbar D.M ⊥ V hV)) : MulAut (Vtil ⊥ V hV)) ∈
        oddBar D.M ⊥ V hV
      have hpow : (y0 : MulAut (Vtil ⊥ V hV)) ^ (t : ℕ) ∈ oddBar D.M ⊥ V hV :=
        (oddBar D.M ⊥ V hV).pow_mem y0.2 (t : ℕ)
      simpa [yM, ky] using hpow
    · show π (yM ^ (t : ℕ)) i = j
      rw [map_pow]
      exact ht

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
