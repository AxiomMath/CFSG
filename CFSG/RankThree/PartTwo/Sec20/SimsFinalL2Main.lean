module

public import CFSG.RankThree.PartTwo.Sec20.SimsFinalL2Lc
public import CFSG.RankThree.PartTwo.Sec20.SimsFinalL2Torus
public import CFSG.RankThree.PartTwo.Sec20.SimsFinalL2KFact
public import CFSG.RankThree.PartTwo.Sec20.SimsFinalL2Cons
import CFSG.RankThree.PartTwo.Sec20.Item20Res6ProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL)


theorem step204FinalL2CYcThreePrime_of (h1812 : Sec18.Item181_2) (h1841 : Sec18.Item184_1)
    (h1842 : Sec18.Item184_2) (hA : KFactL34QEightTop) : Step204FinalL2CYcThreePrime := by
  intro G _ _ A M L N c T i j P hset X hX hXM hm hL2 y hy hy3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hT1 : Ctx20One G A M L N c T := ⟨hset.toCtx20, hset.one_of_L2 ⟨X, hX, hXM, hm, hL2⟩⟩
  obtain ⟨m, ⟨e⟩⟩ := hL2
  obtain ⟨H, hH, -, hL, -⟩ := exists_sec18H_of_ctx20One hT1
  have h201 : Hyp201One G A M L N c := ⟨hset.toHyp201, hT1.one⟩
  have h9 := card_inf_of_hyp201One h1812 h1841 h201
  have hNB := normalizer_inf_le_of_hyp201One h201 h9
  have hLM := not_le_of_hyp201One h201
  have hO2L := pCoreOf_le_of_hyp201One h201
  have hB3 : IsPGroup 3 (A ⊓ L : Subgroup G) :=
    (isSylowOf_three_inf_of_hyp201One h1812 h1841 h201).isPGroup
  have hAM : A ≤ M := le_of_hyp201 hset.toHyp201
  subst hL
  have hc := Res6.orderOf_c_of_setting204 hset
  set K := kTwenty M c with hKdef
  set Y := yTwenty X c with hYdef
  set R := CFSG.Open.pCoreOf 2 (K ⊔ T) with hRdef
  set W := Y ⊔ R with hWdef
  set O := oThreePrimeYR M X T c with hOdef
  set Cc := Subgroup.centralizer ({c} : Set G) with hCc
  set 𝒥 := Y ⊓ Cc with h𝒥
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥W) with hπ
  have hOeq : O = inSubgroup (CFSG.pPrimeCore 3) W := rfl
  have hKX : K ≤ X := fun x hx => hX.2 (Subgroup.mem_sup_left hx)
  have hTX : T ≤ X := fun x hx => hX.2 (Subgroup.mem_sup_right hx)
  have hKY : K ≤ Y := Res6.kTwenty_le_yTwenty hset hKX
  have hYW : Y ≤ W := le_sup_left
  have hKW : K ≤ W := hKY.trans hYW
  have hcK : c ∈ K := self_mem_normalClosureIn M c
  have hcY : c ∈ Y := hKY hcK
  have h𝒥W : 𝒥 ≤ W := inf_le_left.trans hYW
  have hWO : W ≤ Subgroup.normalizer (O : Set G) := Res6.le_normalizer_inSubgroup_pPrimeCore 3 W
  have hO3 : Nat.Coprime 3 (Nat.card O) := Res6.coprime_card_inSubgroup_pPrimeCore 3 W
  have hker : ∀ w : ↥W, π w = 1 ↔ (w : G) ∈ O := by
    intro w
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · intro h
      exact ⟨w, h, rfl⟩
    · rintro ⟨w', hw', hww'⟩
      rwa [← Subtype.ext hww']
  have hTY : T ≤ Subgroup.normalizer (Y : Set G) := hTX.trans (le_normalizer_normalClosureIn X c)
  have hTR : T ≤ Subgroup.normalizer (R : Set G) :=
    le_sup_right.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hTO : T ≤ Subgroup.normalizer (O : Set G) := fun t ht =>
    Res6.normalizer_le_normalizer_inSubgroup_pPrimeCore 3 W
      (Res6.mem_normalizer_sup (hTY ht) (hTR ht))
  have hTC𝒥 : ∀ t ∈ T ⊓ Cc, t ∈ Subgroup.normalizer (𝒥 : Set G) := fun t ht =>
    mem_normalizer_inf_of_mem (hTY ht.1) (Subgroup.le_normalizer ht.2)
  have hφmem : ∀ k : ↥K, π ⟨k, hKW k.2⟩ ∈ yAlpha M X T c := fun k =>
    ⟨⟨k, hKW k.2⟩, Subgroup.mem_subgroupOf.mpr (hKY k.2), rfl⟩
  let φ : ↥K →* ↥(yAlpha M X T c) :=
    (π.comp (Subgroup.inclusion hKW)).codRestrict (yAlpha M X T c) hφmem
  have hφ : ∀ k : ↥K, ((φ k : ↥(yAlpha M X T c)) : ↥W ⧸ CFSG.pPrimeCore 3 ↥W) =
      π ⟨k, hKW k.2⟩ := fun k => rfl
  have hcO : c ∉ O := by
    intro h
    have hord : orderOf (⟨c, h⟩ : O) = 3 := by rw [Subgroup.orderOf_mk, hc]
    have := orderOf_dvd_natCard (⟨c, h⟩ : O)
    rw [hord] at this
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hO3 this
  set x₀ := φ ⟨c, hcK⟩ with hx₀
  have hx₀1 : x₀ ≠ 1 := by
    intro h1
    apply hcO
    have h3 : π ⟨c, hKW hcK⟩ = 1 := by
      have := congrArg Subtype.val h1
      rw [hφ] at this
      simpa using this
    exact (hker _).mp h3
  have hc3 : c ^ 3 = 1 := by rw [← hc]; exact pow_orderOf_eq_one c
  have hx₀3 : orderOf x₀ = 3 := by
    refine orderOf_eq_prime ?_ hx₀1
    rw [hx₀, ← map_pow]
    have : (⟨c, hcK⟩ : ↥K) ^ 3 = 1 := Subtype.ext (by simpa using hc3)
    rw [this, map_one]
  have hns : ¬ Group.IsSolvable ↥(yAlpha M X T c) := by
    intro hs
    have hperfK : Group.IsPerfect ↥K :=
      isPerfect_of_mem_oTwoComponentsIn hset.mem_oTwoComponentsIn
    have : Group.IsPerfect φ.range := Group.IsPerfect.range φ
    have : Nontrivial φ.range :=
      ⟨⟨⟨x₀, ⟨c, hcK⟩, rfl⟩, 1, fun h => hx₀1 (congrArg Subtype.val h)⟩⟩
    have : Group.IsSolvable φ.range := inferInstance
    exact Group.IsPerfect.not_isSolvable φ.range this
  set D := (𝒥.subgroupOf W).map π with hD
  have hDY : D ≤ yAlpha M X T c := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨w, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hw).1, rfl⟩
  have hD₀ : D.subgroupOf (yAlpha M X T c) ≤ Subgroup.centralizer ({x₀} : Set _) := by
    intro d hd
    rw [Subgroup.mem_subgroupOf] at hd
    obtain ⟨⟨g, hgW⟩, hg, hgd⟩ := hd
    have hg' : g ∈ 𝒥 := Subgroup.mem_subgroupOf.mp hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hx₀, hφ, ← hgd, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp hg'.2
  obtain ⟨hcycD₀, hoddD₀⟩ := SimsFinalL2.isCyclic_odd_of_le_centralizer e hns hx₀3 hD₀
  have hDeq : D.subgroupOf (yAlpha M X T c) ≃* D := Subgroup.subgroupOfEquivOfLe hDY
  have hcycD : IsCyclic D := isCyclic_of_surjective hDeq.toMonoidHom hDeq.surjective
  have hoddD : Odd (Nat.card D) := by rwa [← Nat.card_congr hDeq.toEquiv]
  obtain ⟨J₁, hJ₁𝒥, hOcJ₁, hJ₁3, hJ₁N, g₁, hg₁, hJ₁g, k, hk6, hg₁k⟩ :=
    SimsFinalL2.exists_threePrime_part h𝒥W hcycD hoddD
  set Oc := 𝒥 ⊓ O with hOc
  set Lc := Sec18.lc H c with hLc
  set B := A ⊓ inSubgroup perfectResidual H with hB
  set πL := QuotientGroup.mk' (CFSG.pCore 2 ↥Lc) with hπL
  set Bb := (B.subgroupOf Lc).map πL with hBb
  set Tc := T ⊓ Cc ⊓ (Lc ⊓ M) with hTc
  set Q := (Tc.subgroupOf Lc).map πL with hQ
  set NL := Subgroup.normalizer (Lc : Set G) with hNL
  set ρ := SimsFinalL2.rho Lc with hρ
  have hCNL : Cc ≤ NL := SimsFinalL2.centralizer_le_normalizer_lc h1842 hH
  have hJ₁NL : J₁ ≤ NL := hJ₁𝒥.trans (inf_le_right.trans hCNL)
  have hOcNL : Oc ≤ NL := inf_le_left.trans (inf_le_right.trans hCNL)
  obtain ⟨eL⟩ := Sec18.SylowFusion.nonempty_quotient_lc h1841 hH
  have hBb9 : Nat.card Bb = 9 := SimsFinalL2.card_map_inf_lc h1812 h1841 hH
  obtain ⟨hQ8, hQB⟩ := SimsFinalL2.card_map_sylow_eq_eight h1812 h1841 h1842 hH hAM hNB hLM hO2L
    hset.sylow_centralizer
  set Jm := (J₁.subgroupOf NL).map ρ with hJm
  set Om := (Oc.subgroupOf NL).map ρ with hOm
  have hOcJ₁' : Oc.subgroupOf NL ≤ J₁.subgroupOf NL := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hOcJ₁ (Subgroup.mem_subgroupOf.mp hx))
  have hOmJm : Om ≤ Jm := Subgroup.map_mono hOcJ₁'
  have hJ₁Oc : ∀ s ∈ J₁, s ∈ Subgroup.normalizer (Oc : Set G) := fun s hs =>
    mem_normalizer_inf_of_mem (Subgroup.le_normalizer (hJ₁𝒥 hs)) (hWO (h𝒥W (hJ₁𝒥 hs)))
  have hJmN : Jm ≤ Subgroup.normalizer (Om : Set _) := by
    rintro _ ⟨s, hs, rfl⟩
    exact SimsFinalL2.rho_mem_normalizer_map (hJ₁Oc s (Subgroup.mem_subgroupOf.mp hs))
  have hnormal : (Om.subgroupOf Jm).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOmJm).mpr hJmN
  have hQρ : ∀ q ∈ Q, ∃ t ∈ Tc, ∃ ht : t ∈ NL, MulAut.conj q = ρ ⟨t, ht⟩ := by
    rintro _ ⟨⟨t, htLc⟩, ht, rfl⟩
    have ht' : t ∈ Tc := Subgroup.mem_subgroupOf.mp ht
    exact ⟨t, ht', Subgroup.le_normalizer htLc, (SimsFinalL2.rho_eq_conj Lc htLc).symm⟩
  have hTcN : ∀ t ∈ Tc, t ∈ T ⊓ Cc := fun t ht => ht.1
  have hQJ : Q.map (MulAut.conj : _ →* MulAut (↥Lc ⧸ CFSG.pCore 2 ↥Lc)) ≤
      Subgroup.normalizer (Jm : Set (MulAut (↥Lc ⧸ CFSG.pCore 2 ↥Lc))) := by
    rintro _ ⟨q, hq, rfl⟩
    obtain ⟨t, ht, htN, hqt⟩ := hQρ q hq
    rw [hqt]
    exact SimsFinalL2.rho_mem_normalizer_map
      (hJ₁N t (hTC𝒥 t (hTcN t ht)) (hTO (hTcN t ht).1))
  have hQO : Q.map (MulAut.conj : _ →* MulAut (↥Lc ⧸ CFSG.pCore 2 ↥Lc)) ≤
      Subgroup.normalizer (Om : Set (MulAut (↥Lc ⧸ CFSG.pCore 2 ↥Lc))) := by
    rintro _ ⟨q, hq, rfl⟩
    obtain ⟨t, ht, htN, hqt⟩ := hQρ q hq
    rw [hqt]
    exact SimsFinalL2.rho_mem_normalizer_map
      (mem_normalizer_inf_of_mem (hTC𝒥 t (hTcN t ht)) (hTO (hTcN t ht).1))
  have hOm3 : Nat.Coprime (Nat.card Om) 3 := by
    have h1 : Nat.card Om ∣ Nat.card O := by
      refine (Subgroup.card_map_dvd (H := Oc.subgroupOf NL) ρ).trans ?_
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOcNL).toEquiv]
      exact Subgroup.card_dvd_of_le inf_le_right
    exact (hO3.coprime_dvd_right h1).symm
  have hg₁NL : g₁ ∈ NL := hJ₁NL hg₁
  have hgJm : ρ ⟨g₁, hg₁NL⟩ ∈ Jm := ⟨⟨g₁, hg₁NL⟩, Subgroup.mem_subgroupOf.mpr hg₁, rfl⟩
  have hg₁N : Subgroup.zpowers g₁ ≤ Subgroup.normalizer (Oc : Set G) :=
    Subgroup.zpowers_le.mpr (hJ₁Oc g₁ hg₁)
  have hJmle : Jm ≤ Om ⊔ Subgroup.zpowers (ρ ⟨g₁, hg₁NL⟩) := by
    rintro _ ⟨s, hs, rfl⟩
    have hs' : (s : G) ∈ ((Subgroup.zpowers g₁ ⊔ Oc : Subgroup G) : Set G) := by
      rw [sup_comm]
      exact hJ₁g (Subgroup.mem_subgroupOf.mp hs)
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hg₁N] at hs'
    obtain ⟨u, hu, o, ho, huo⟩ := hs'
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    have hoNL : o ∈ NL := hOcNL ho
    have hsplit : s = (⟨g₁, hg₁NL⟩ : NL) ^ n * ⟨o, hoNL⟩ := Subtype.ext (by simpa using huo.symm)
    rw [hsplit, map_mul, map_zpow, sup_comm]
    exact Subgroup.mul_mem_sup (Subgroup.zpow_mem_zpowers _ n)
      ⟨⟨o, hoNL⟩, Subgroup.mem_subgroupOf.mpr ho, rfl⟩
  have hidx : Nat.Coprime (Om.relIndex Jm) 6 := by
    have hk : (ρ ⟨g₁, hg₁NL⟩) ^ k ∈ Om := by
      have hmem : (⟨g₁, hg₁NL⟩ : NL) ^ k ∈ Oc.subgroupOf NL :=
        Subgroup.mem_subgroupOf.mpr (by rw [Subgroup.coe_pow]; exact hg₁k)
      have h1 := Subgroup.mem_map_of_mem ρ hmem
      rwa [map_pow] at h1
    exact hk6.coprime_dvd_left
      (SimsFinalL2.relIndex_dvd_of_le_sup_zpowers hOmJm hnormal hgJm hJmle hk)
  have hJO := hA (↥Lc ⧸ CFSG.pCore 2 ↥Lc) ⟨eL⟩ Bb Q hBb9 hQ8 hQB Jm Om hOmJm hnormal hQJ hQO
    hOm3 ⟨_, hgJm, hJmle⟩ hidx
  have hy𝒥 : y ∈ 𝒥 := hy
  have hyJ₁ : y ∈ J₁ := hJ₁3 y hy𝒥 hy3
  have hyNL : y ∈ NL := hJ₁NL hyJ₁
  have hyJm : ρ ⟨y, hyNL⟩ ∈ Jm := ⟨⟨y, hyNL⟩, Subgroup.mem_subgroupOf.mpr hyJ₁, rfl⟩
  rw [hJO] at hyJm
  obtain ⟨o, ho, hoy⟩ := hyJm
  have ho' : (o : G) ∈ Oc := Subgroup.mem_subgroupOf.mp ho
  have hρ1 : ρ (o⁻¹ * ⟨y, hyNL⟩) = 1 := by rw [map_mul, map_inv, hoy, inv_mul_cancel]
  have hM : (o : G)⁻¹ * y ∈ M := by
    have h1 := SimsFinalL2.mem_normalizer_of_rho_eq_one (SimsFinalL2.inf_le_lc hH) hρ1
    exact SimsFinalL2.normalizer_sup_pCoreOf_lc_le h1842 hH hAM hB3 hNB (by simpa using h1)
  have hYy : (o : G)⁻¹ * y ∈ Y := Y.mul_mem (Y.inv_mem ho'.1.1) hy.1
  have e1 : y = (o : G) * ((o : G)⁻¹ * y) := by group
  rw [e1, sup_comm]
  exact Subgroup.mul_mem_sup ho'.2 ⟨hYy, hM⟩

theorem step204FinalL2ZNe_of_sec18 (h1812 : Sec18.Item181_2)
    (h1841 : Sec18.Item184_1) (h1842 : Sec18.Item184_2) (hA : KFactL34QEightTop) :
    Step204FinalL2ZNe :=
  step204FinalL2ZNe_of_threePrime kFactL2CentThreePrime_holds
    (step204FinalL2CYcThreePrime_of h1812 h1841 h1842 hA)

end CFSG.RankThree.PartTwo.Sec20
