module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCoreASevenNormalizerControl
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCoreBInterM
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCoreMaximal
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseCyclicTwoCoreInfra
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ComponentLayerCentralizesSolvableNormalized
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27Infra
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.QuasisimpleNotTwoGroupQuotient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2Cardinality
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Center
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2Center
import Mathlib.GroupTheory.Coset.Card
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonClassification
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Section 3: A₇-layer normalizer transfer

The source paragraph (p. 223) needs
`componentLayerOf (N_G(X)) = componentLayerOf M` for every nontrivial
`X ≤ B ∩ M`.  This module proves that equality.

The forward half is obtained from Lemma 2.9 and the quasisimple A₇ layer
structure: `V₂ ∩ O₂(N)` and `V₂ ∩ E(N)` are the two alternatives, and the
intersection with the corresponding normal subgroup of `N` is a nontrivial
normal subgroup of the quasisimple layer `E(M)`, forcing
`E(M) ≤ E(N)`.
-/

noncomputable section

open scoped commutatorElement

namespace CFSG.GorensteinWalter

universe u v

/-! ## Local layer infrastructure -/

/-- The component layer is perfect. -/
private theorem componentLayerOf_isPerfect {G : Type u} [Group G]
    (N : Subgroup G) :
    Group.IsPerfect (↥(componentLayerOf N)) := by
  apply Subgroup.isPerfect_iff.mpr
  let L : Subgroup G := componentLayerOf N
  apply le_antisymm
  · exact (Subgroup.commutator_le_sup L L).trans (sup_idem L).le
  · rw [componentLayerOf]
    refine sSup_le ?_
    intro E hE
    have hEperf : Group.IsPerfect E := (Group.isPerfect_def).2 hE.2.2.2.1
    have hEE : ⁅E, E⁆ = E := (Subgroup.isPerfect_iff).mp hEperf
    rw [← hEE]
    exact Subgroup.commutator_mono (le_sSup hE) (le_sSup hE)

/-- The ambient odd core of the component layer is central in the layer. -/
private theorem componentLayerOf_oddCore_le_center {G : Type u} [Group G]
    [Finite G] (M : Subgroup G) (hMmax : IsCoatom M) :
    pPrimeCore 2 (↥(componentLayerOf M)) ≤
      Subgroup.center (↥(componentLayerOf M)) := by
  let E : Subgroup G := componentLayerOf M
  let O : Subgroup E := pPrimeCore 2 E
  let Z : Subgroup E := Subgroup.center E
  have hOmap_le_Zmap :
      O.map E.subtype ≤ Z.map E.subtype :=
    firstCase_cyclic_layer_oddCore_le_center hMmax
  intro o ho
  have ho_map : (E.subtype o) ∈ Z.map E.subtype :=
    hOmap_le_Zmap (Subgroup.mem_map.mpr ⟨o, ho, rfl⟩)
  rcases Subgroup.mem_map.mp ho_map with ⟨z, hz, hz_eq⟩
  have hz_o : z = o := by
    apply Subtype.ext
    exact hz_eq
  simpa [hz_o] using hz

/-- A quasisimple layer with `A₇` odd-core quotient is quasisimple with
`A₇` central quotient and odd center. -/
private theorem componentLayerOf_quasisimple_of_a7
    {G : Type u} [Group G] [Finite G]
    (M : Subgroup G) (hMmax : IsCoatom M)
    (hEne : componentLayerOf M ≠ ⊥)
    (hA7 : Nonempty ((componentLayerOf M) ⧸
      pPrimeCore 2 (componentLayerOf M) ≃* alternatingGroup (Fin 7))) :
    IsQuasisimple (componentLayerOf M) ∧
      Nonempty ((componentLayerOf M) ⧸
        Subgroup.center (componentLayerOf M) ≃* alternatingGroup (Fin 7)) ∧
        Odd (Nat.card (Subgroup.center (componentLayerOf M))) := by
  classical
  let E : Subgroup G := componentLayerOf M
  let O : Subgroup E := pPrimeCore 2 E
  let Z : Subgroup E := Subgroup.center E
  have : O.Normal := by
    dsimp [O]
    infer_instance
  have hOleZ : O ≤ Z := componentLayerOf_oddCore_le_center M hMmax
  have hZnormal : Z.Normal := by
    dsimp [Z]
    infer_instance
  let q : E →* E ⧸ O := QuotientGroup.mk' O
  let Zbar : Subgroup (E ⧸ O) := Z.map q
  have hZbar_normal : Zbar.Normal := hZnormal.map q (QuotientGroup.mk'_surjective O)
  let : IsSimpleGroup (E ⧸ O) :=
    (MulEquiv.isSimpleGroup_congr hA7.some).mpr
      (alternatingGroup.isSimpleGroup (by norm_num : 5 ≤ Nat.card (Fin 7)))
  have hZbar_bot_or_top :=
    (@IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ _ Zbar hZbar_normal)
  have hperf : Group.IsPerfect E := componentLayerOf_isPerfect M
  have hZbar_bot : Zbar = ⊥ := by
    rcases hZbar_bot_or_top with hbot | htop
    · exact hbot
    · exfalso
      have hZeq : Z = ⊤ := by
        have hcomap : (Z.map q).comap q = O ⊔ Z :=
          QuotientGroup.comap_map_mk' O Z
        have hmap_top : Z.map q = ⊤ := by
          simpa [Zbar] using htop
        have hcomap_top : (Z.map q).comap q = ⊤ := by
          rw [hmap_top, Subgroup.comap_top]
        have hOsupZ : O ⊔ Z = ⊤ := by
          rw [← hcomap]
          exact hcomap_top
        apply le_antisymm
        · exact le_top
        · intro e _he
          have heSup : e ∈ O ⊔ Z := by
            rw [hOsupZ]
            trivial
          rwa [sup_of_le_right hOleZ] at heSup
      have hEcomm : IsMulCommutative (↥E) := by
        refine ⟨⟨fun x y => ?_⟩⟩
        apply Subtype.ext
        have hxZ : (x : E) ∈ Z := by
          rw [hZeq]
          trivial
        exact congrArg Subtype.val
          (Subgroup.mem_center_iff.mp hxZ y).symm
      have hcomm_bot : ⁅E, E⁆ = ⊥ :=
        Subgroup.commutator_self_eq_bot_iff.mpr hEcomm
      have hEbot : E = ⊥ := by
        calc
          E = ⁅E, E⁆ := (Subgroup.isPerfect_iff.mp hperf).symm
          _ = ⊥ := hcomm_bot
      have hEne' : E ≠ ⊥ := by
        intro hbot
        apply hEne
        exact hbot
      exact hEne' hEbot
  have hZeqO : Z = O := by
    apply le_antisymm
    · intro z hz
      have hz_map : q z ∈ Zbar := Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
      rw [hZbar_bot] at hz_map
      have hzO : z ∈ O :=
        (QuotientGroup.eq_one_iff (N := O) z).mp (Subgroup.mem_bot.mp hz_map)
      exact hzO
    · exact hOleZ
  have hcenter_eq : Subgroup.center E = pPrimeCore 2 E := hZeqO
  have hcenter_odd : Odd (Nat.card (Subgroup.center E)) := by
    rw [hcenter_eq]
    exact Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := E))
  have hZquotient : Nonempty ((E ⧸ Subgroup.center E) ≃* alternatingGroup (Fin 7)) := by
    have heq : E ⧸ Subgroup.center E ≃* E ⧸ pPrimeCore 2 E :=
      QuotientGroup.quotientMulEquivOfEq (G := E)
        (M := Subgroup.center E) (N := pPrimeCore 2 E) hcenter_eq
    exact ⟨heq.trans hA7.some⟩
  have hE_nontriv : Nontrivial E :=
    (Subgroup.nontrivial_iff_ne_bot E).2 hEne
  have hE_simple : IsSimpleGroup (E ⧸ Subgroup.center E) :=
    (MulEquiv.isSimpleGroup_congr hZquotient.some).mpr
      (alternatingGroup.isSimpleGroup (by norm_num : 5 ≤ Nat.card (Fin 7)))
  have hE_quasisimple : IsQuasisimple E := by
    refine ⟨hE_nontriv, ?_, hE_simple⟩
    exact (Group.isPerfect_def).1 hperf
  exact ⟨hE_quasisimple, hZquotient, hcenter_odd⟩

/-- A normal subgroup of a quasisimple group that contains an involution
cannot be central when the center is odd; hence it is the whole group. -/
private theorem normal_subgroup_eq_top_of_a7_quasisimple
    {Q : Type u} [Group Q]
    (hQ : IsQuasisimple Q)
    (hZodd : Odd (Nat.card (Subgroup.center Q)))
    (N : Subgroup Q) (hNnormal : N.Normal)
    (hinv : ∃ v : Q, v ∈ N ∧ v ≠ 1 ∧ v ^ 2 = 1) :
    N = ⊤ := by
  rcases normal_subgroup_le_center_or_eq_top hQ N hNnormal with hNc | hNtop
  · exfalso
    rcases hinv with ⟨v, hvN, hvne, hvsq⟩
    have hvZ : v ∈ Subgroup.center Q := hNc hvN
    have hord2 : orderOf v = 2 :=
      orderOf_eq_prime (by simpa [pow_two] using hvsq) hvne
    have htwo_dvd : 2 ∣ Nat.card (Subgroup.center Q) := by
      have hord_eq : orderOf (⟨v, hvZ⟩ : Subgroup.center Q) = orderOf v :=
        (orderOf_injective (Subgroup.center Q).subtype
          (Subgroup.center Q).subtype_injective ⟨v, hvZ⟩).symm
      have hdvd_sub : orderOf (⟨v, hvZ⟩ : Subgroup.center Q) ∣
          Nat.card (Subgroup.center Q) :=
        orderOf_dvd_natCard (⟨v, hvZ⟩ : Subgroup.center Q)
      simpa [hord_eq, hord2] using hdvd_sub
    exact hZodd.not_two_dvd_nat htwo_dvd
  · exact hNtop

/-- If a quasisimple A₇-layer subgroup meets a normal subgroup of its
ambient group in an involution, it is contained in that normal subgroup. -/
private theorem a7_quasisimple_le_of_normal_intersection_involution
    {G : Type u} [Group G]
    (E L N : Subgroup G) (hE : IsQuasisimple E)
    (hZodd : Odd (Nat.card (Subgroup.center E)))
    (hEN : E ≤ N) (hLnorm : IsNormalIn L N)
    (hinv : ∃ v : G, v ∈ E ⊓ L ∧ v ≠ 1 ∧ v ^ 2 = 1) :
    E ≤ L := by
  classical
  let I : Subgroup G := E ⊓ L
  have hI_normal_E : IsNormalIn I E := by
    refine ⟨inf_le_left, ?_⟩
    intro e he x hx
    exact ⟨E.mul_mem (E.mul_mem he hx.1) (E.inv_mem he),
      hLnorm.2 e (hEN he) x hx.2⟩
  let IE : Subgroup E := I.subgroupOf E
  have hIE_normal : IE.Normal :=
    (Subgroup.normal_subgroupOf_iff (show I ≤ E from inf_le_left)).2
      (fun h k hh hk => hI_normal_E.2 k hk h hh)
  have hIE_inv : ∃ v : E, v ∈ IE ∧ v ≠ 1 ∧ v ^ 2 = 1 := by
    rcases hinv with ⟨v, hvI, hvne, hvsq⟩
    refine ⟨⟨v, hvI.1⟩, ?_, ?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.mpr hvI
    · intro h1
      exact hvne (congrArg Subtype.val h1)
    · exact Subtype.ext hvsq
  have hIE_top : IE = ⊤ :=
    normal_subgroup_eq_top_of_a7_quasisimple hE hZodd IE hIE_normal hIE_inv
  intro e he
  have hIE_mem : (⟨e, he⟩ : E) ∈ IE := by
    rw [hIE_top]
    trivial
  have hIL : e ∈ E ⊓ L := Subgroup.mem_subgroupOf.mp hIE_mem
  exact (Subgroup.mem_inf.mp hIL).2

/-- A subgroup of a solvable group is solvable. -/
private theorem isSolvable_of_le_of_isSolvable {G : Type u} [Group G]
    (A B : Subgroup G) (hAB : A ≤ B) (hB : Group.IsSolvable B) :
    Group.IsSolvable A := by
  let : Group.IsSolvable B := hB
  let : Group.IsSolvable (A.subgroupOf B) := inferInstance
  exact isSolvable_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hAB)

/-- The two-core of `N` is normal in `N`. -/
private theorem twoCoreOf_isNormalIn {G : Type u} [Group G] (N : Subgroup G) :
    IsNormalIn (twoCoreOf N) N := by
  refine ⟨Subgroup.map_subtype_le (H := N) (pCore 2 N), ?_⟩
  intro n hn k hk
  rcases Subgroup.mem_map.mp hk with ⟨k0, hk0, rfl⟩
  refine Subgroup.mem_map.mpr
    ⟨(⟨n, hn⟩ : N) * k0 * (⟨n, hn⟩ : N)⁻¹, ?_, rfl⟩
  exact (pCore_normal (p := 2) (G := N)).conj_mem k0 hk0 ⟨n, hn⟩

/-- The two-core of `N` is a `2`-group. -/
private theorem twoCoreOf_isPGroup {G : Type u} [Group G] [Finite G]
    (N : Subgroup G) : IsPGroup 2 (twoCoreOf N) := by
  change IsPGroup 2 ((pCore 2 N).map N.subtype)
  exact (pCore_isPGroup (p := 2) (G := N)).map N.subtype

/-- An involution in a Klein-four subgroup. -/
private theorem involution_of_kleinFour {G : Type u} [Group G]
    {V : Subgroup G} (hV : IsKleinFour V) {v : G}
    (hvV : v ∈ V) (_hvne : v ≠ 1) :
    v ^ 2 = 1 := by
  have h := congrArg Subtype.val (hV.mul_self (⟨v, hvV⟩ : V))
  simpa [pow_two] using h

/-! ## Odd `PSL₂` has no `A₇` quotient -/

/-- Odd `PSL₂(K)` is never isomorphic to `A₇`. -/
public theorem psl2_ne_a7
    {K : Type u} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (e : Nonempty (PSL2 K ≃* alternatingGroup (Fin 7))) : False := by
  classical
  rcases e with ⟨e⟩
  let q : ℕ := Nat.card K
  have hqpos : 0 < q := Nat.card_pos
  have hKodd : Odd q := by
    dsimp [q]
    rcases hK with ⟨p, n, _hp, hpodd, _hn, hcard⟩
    rw [hcard]
    exact hpodd.pow
  have hdvd2 : 2 ∣ q * (q ^ 2 - 1) := by
    have hEven : Even (q ^ 2 - 1) := Nat.Odd.sub_odd hKodd.pow odd_one
    exact dvd_mul_of_dvd_right hEven.two_dvd _
  have hcardPSL : Nat.card (PSL2 K) = q * (q ^ 2 - 1) / 2 :=
    by simpa [q] using psl2_card_formula K hK
  have hcardA : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
    rw [nat_card_alternatingGroup]
    norm_num
  have hEq : q * (q ^ 2 - 1) / 2 = 2520 := by
    rw [← hcardPSL]
    rw [Nat.card_congr e.toEquiv, hcardA]
  have hEq' : q * (q ^ 2 - 1) = 2 * 2520 := by
    rw [← Nat.div_eq_iff_eq_mul_right (by norm_num) hdvd2]
    exact hEq
  have hEq'' : q * (q ^ 2 - 1) = 5040 := by
    norm_num at hEq'
    exact hEq'
  have hqle : q ≤ 17 := by
    by_contra hnot
    have hge : 18 ≤ q := by omega
    have hqsq_pos : 0 < q ^ 2 := pow_pos hqpos 2
    have h1 : 1 ≤ q ^ 2 := Nat.succ_le_of_lt hqsq_pos
    have hz : (q : ℤ) * ((q : ℤ) ^ 2 - 1) = 5040 := by
      have hsq : (q : ℤ) ^ 2 = (q ^ 2 : ℕ) := by norm_num
      rw [hsq]
      have hcast : ((q ^ 2 : ℕ) : ℤ) - 1 = ((q ^ 2 - 1 : ℕ) : ℤ) :=
        (Int.ofNat_sub h1).symm
      rw [hcast]
      exact_mod_cast hEq''
    have hprod : (18 : ℤ) * (18 ^ 2 - 1) ≤
        (q : ℤ) * ((q : ℤ) ^ 2 - 1) := by
      nlinarith [sq_nonneg (q : ℤ)]
    norm_num at hprod
    omega
  interval_cases q <;> norm_num at hEq''

/-- Odd `PGL₂(K)` is never isomorphic to `A₇`. -/
public theorem pgl2_ne_a7
    {K : Type u} [Field K] [Finite K]
    (_hK : IsOddPrimePower (Nat.card K))
    (e : Nonempty (PGL2 K ≃* alternatingGroup (Fin 7))) : False := by
  classical
  rcases e with ⟨e⟩
  let q : ℕ := Nat.card K
  have hqpos : 0 < q := Nat.card_pos
  have hcardPGL : Nat.card (PGL2 K) = q * (q ^ 2 - 1) := by
    simpa [q] using pgl2_card_formula K
  have hcardA : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
    rw [nat_card_alternatingGroup]
    norm_num
  have hEq : q * (q ^ 2 - 1) = 2520 := by
    rw [← hcardPGL]
    rw [Nat.card_congr e.toEquiv, hcardA]
  have hqle : q ≤ 13 := by
    by_contra hnot
    have hge : 14 ≤ q := by omega
    have hqsq_pos : 0 < q ^ 2 := pow_pos hqpos 2
    have h1 : 1 ≤ q ^ 2 := Nat.succ_le_of_lt hqsq_pos
    have hz : (q : ℤ) * ((q : ℤ) ^ 2 - 1) = 2520 := by
      have hsq : (q : ℤ) ^ 2 = (q ^ 2 : ℕ) := by norm_num
      rw [hsq]
      have hcast : ((q ^ 2 : ℕ) : ℤ) - 1 = ((q ^ 2 - 1 : ℕ) : ℤ) :=
        (Int.ofNat_sub h1).symm
      rw [hcast]
      exact_mod_cast hEq
    have hprod : (14 : ℤ) * (14 ^ 2 - 1) ≤
        (q : ℤ) * ((q : ℤ) ^ 2 - 1) := by
      nlinarith [sq_nonneg (q : ℤ)]
    norm_num at hprod
    omega
  interval_cases q <;> norm_num at hEq

/-- An `A₇` central quotient has order `2520` dividing the group order. -/
public theorem a7_quotient_card_dvd {G : Type u} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal]
    (hA : Nonempty (G ⧸ N ≃* alternatingGroup (Fin 7))) :
    (2520 : ℕ) ∣ Nat.card G := by
  have hqcard : Nat.card (G ⧸ N) = 2520 := by
    rw [Nat.card_congr hA.some.toEquiv, nat_card_alternatingGroup]
    norm_num
  have hdvd : Nat.card (G ⧸ N) ∣ Nat.card G := Subgroup.card_quotient_dvd_card N
  simpa [hqcard] using hdvd

/-- A cyclic group is solvable. -/
private theorem isSolvable_of_isCyclic {G : Type u} [Group G] [Finite G]
    (h : IsCyclic G) : Group.IsSolvable G := by
  let : CommGroup G := IsCyclic.commGroup
  infer_instance

/-- The rotation subgroup of a finite dihedral group is normal. -/
private instance dihedralRotation_normal (z : ℕ) [NeZero z] :
    (Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup z)).Normal := by
  refine ⟨?_⟩
  intro x hx g
  rcases dihedralGroup_cases g with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · rw [Subgroup.mem_zpowers_iff] at hx ⊢
    rcases hx with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have hconj : DihedralGroup.r i * x * (DihedralGroup.r i)⁻¹ =
        (DihedralGroup.r 1 : DihedralGroup z) ^ k := by
      rw [← hk, DihedralGroup.r_one_zpow, DihedralGroup.inv_r]
      simp [DihedralGroup.r_mul_r]
    exact hconj.symm
  · rw [Subgroup.mem_zpowers_iff] at hx ⊢
    rcases hx with ⟨k, hk⟩
    refine ⟨-k, ?_⟩
    have hconj : DihedralGroup.sr i * x * (DihedralGroup.sr i)⁻¹ =
        (DihedralGroup.r 1 : DihedralGroup z) ^ (-k) := by
      rw [← hk, DihedralGroup.r_one_zpow, DihedralGroup.inv_sr]
      simp [DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr]
    exact hconj.symm

/-- A finite dihedral group is solvable. -/
private theorem isSolvable_of_dihedralGroup (z : ℕ) [NeZero z] :
    Group.IsSolvable (DihedralGroup z) := by
  classical
  let R : Subgroup (DihedralGroup z) :=
    Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup z)
  have : R.Normal := dihedralRotation_normal z
  let : Group.IsSolvable R := by
    have : IsCyclic R := Subgroup.isCyclic_zpowers (DihedralGroup.r 1 : DihedralGroup z)
    let : CommGroup R := IsCyclic.commGroup
    infer_instance
  have hRcard : Nat.card R = z := by
    rw [Nat.card_zpowers, DihedralGroup.orderOf_r_one]
  have hDcard : Nat.card (DihedralGroup z) = 2 * z := DihedralGroup.nat_card
  have hindex : R.index = 2 := by
    have hmul : Nat.card R * R.index = Nat.card (DihedralGroup z) :=
      Subgroup.card_mul_index R
    rw [hRcard, hDcard] at hmul
    have hz_pos : 0 < z := Nat.pos_of_ne_zero (‹NeZero z›.out)
    nlinarith
  have hQcard : Nat.card (DihedralGroup z ⧸ R) = 2 := by
    rw [← Subgroup.index_eq_card R]
    exact hindex
  let : Group.IsSolvable (DihedralGroup z ⧸ R) := by
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hQcyc : IsCyclic (DihedralGroup z ⧸ R) := isCyclic_of_prime_card hQcard
    let : CommGroup (DihedralGroup z ⧸ R) := IsCyclic.commGroup
    infer_instance
  exact isSolvable_of_normal_solvable_quotient_solvable R inferInstance inferInstance

/-- A semidirect product of a normal solvable subgroup and a cyclic quotient
is solvable. -/
private theorem isSolvable_of_semidirect {G : Type u} [Group G] [Finite G]
    (N C : Subgroup G) [N.Normal]
    (hN : Group.IsSolvable N) (hC : IsCyclic C)
    (hsup : N ⊔ C = ⊤) :
    Group.IsSolvable G := by
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  let f : C →* G ⧸ N := q.comp C.subtype
  have hf_surj : Function.Surjective f := by
    intro y
    rcases QuotientGroup.mk'_surjective N y with ⟨g, hg⟩
    have hgNC : g ∈ N ⊔ C := by
      rw [hsup]
      trivial
    rcases (Subgroup.mem_sup_of_normal_left (s := N) (t := C)).mp hgNC with
      ⟨n, hn, c, hc, hgc⟩
    have hqn : q n = 1 :=
      (QuotientGroup.eq_one_iff (N := N) n).mpr hn
    refine ⟨⟨c, hc⟩, ?_⟩
    calc
      f ⟨c, hc⟩ = q c := rfl
      _ = q (n * c) := by rw [map_mul, hqn, one_mul]
      _ = q g := by rw [hgc]
      _ = y := hg
  have : IsCyclic C := hC
  have hQcyc : IsCyclic (G ⧸ N) := isCyclic_of_surjective f hf_surj
  let : Group.IsSolvable (G ⧸ N) := isSolvable_of_isCyclic hQcyc
  exact isSolvable_of_normal_solvable_quotient_solvable N hN inferInstance

/-- A solvable group has no `A₇` quotient. -/
public theorem a7_quotient_absurd_of_solvable {G : Type u} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] (hG : Group.IsSolvable G)
    (hA : Nonempty (G ⧸ N ≃* alternatingGroup (Fin 7))) : False := by
  let : Group.IsSolvable (G ⧸ N) := inferInstance
  have hA7solv : Group.IsSolvable (alternatingGroup (Fin 7)) :=
    Group.isSolvable_of_surjective (f := hA.some.toMonoidHom) hA.some.surjective
  let : Group.IsPerfect (alternatingGroup (Fin 7)) :=
    ⟨commutator_alternatingGroup_eq_top (by norm_num)⟩
  have : Nontrivial (alternatingGroup (Fin 7)) := inferInstance
  exact Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 7)) hA7solv

/-- The image of the center under a group equivalence is the center. -/
private lemma map_center_eq_center_of_mulEquiv
    {A B : Type u} [Group A] [Group B]
    (e : A ≃* B) :
    (Subgroup.center A).map e.toMonoidHom = Subgroup.center B := by
  apply le_antisymm
  · intro x hx
    rcases hx with ⟨y, hy, rfl⟩
    exact (Subgroup.centerCongr e ⟨y, hy⟩).2
  · intro x hx
    refine ⟨e.symm x, ?_, ?_⟩
    · exact ((Subgroup.centerCongr e).symm ⟨x, hx⟩).2
    · exact e.apply_symm_apply x

/-- If the image of a quasisimple subgroup modulo an odd normal kernel is
isomorphic to a centerless group, then the central quotient is that group. -/
private theorem quasisimple_center_quotient_of_simple_image
    {H : Type u} [Group H] [Finite H]
    (E : Subgroup H) (hEq : IsQuasisimple E)
    (O : Subgroup H) [O.Normal] (hOodd : Odd (Nat.card O))
    (S : Type v) [Group S] [Finite S]
    (hScenter : Subgroup.center S = ⊥)
    (e : E.map (QuotientGroup.mk' O) ≃* S) :
    pPrimeCore 2 E = Subgroup.center E ∧
      Nonempty (E ⧸ Subgroup.center E ≃* S) := by
  classical
  let g : E →* E.map (QuotientGroup.mk' O) :=
    ((QuotientGroup.mk' O).comp E.subtype).codRestrict
      (E.map (QuotientGroup.mk' O)) (fun x =>
      Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩)
  have hgsurj : Function.Surjective g := by
    intro y
    rcases Subgroup.mem_map.mp y.2 with ⟨x, hx, hyq⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    simpa [g] using hyq
  let f : E →* S := e.toMonoidHom.comp g
  have hfsurj : Function.Surjective f := e.surjective.comp hgsurj
  let N : Subgroup E := f.ker
  have hNleO : N ≤ O.comap E.subtype := by
    intro x hx
    rw [Subgroup.mem_comap]
    have hf1 : (QuotientGroup.mk' O) (E.subtype x) = 1 := by
      have hcomp : e.toMonoidHom (g x) = 1 := MonoidHom.mem_ker.mp hx
      exact congrArg Subtype.val (e.injective (by simpa using hcomp))
    exact (QuotientGroup.eq_one_iff (N := O) (E.subtype x)).mp hf1
  have hNodd : Odd (Nat.card N) := by
    have hNleOcard : Nat.card N ∣ Nat.card (O.comap E.subtype) :=
      Subgroup.card_dvd_of_le hNleO
    have hOcomap_dvd : Nat.card (O.comap E.subtype) ∣ Nat.card O :=
      Subgroup.card_comap_dvd_of_injective O E.subtype E.subtype_injective
    exact Odd.of_dvd_nat hOodd (hNleOcard.trans hOcomap_dvd)
  have hNcop : Nat.Coprime 2 (Nat.card N) := Nat.coprime_two_left.mpr hNodd
  have hNleCore : N ≤ pPrimeCore 2 E := le_sSup ⟨inferInstance, hNcop⟩
  have hZleN : Subgroup.center E ≤ N := by
    intro x hx
    apply MonoidHom.mem_ker.mpr
    have hxcentS : e.toMonoidHom (g x) ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro y
      rcases hfsurj y with ⟨z, rfl⟩
      have hcommE : z * x = x * z := (Subgroup.mem_center_iff.mp hx z)
      have hf : f (z * x) = f (x * z) := congrArg f hcommE
      simpa [f, g, map_mul] using hf
    have hxbot : e.toMonoidHom (g x) ∈ (⊥ : Subgroup S) := by
      simpa [hScenter] using hxcentS
    exact Subgroup.mem_bot.mp hxbot
  have hP_le_N : pPrimeCore 2 E ≤ N :=
    (pPrimeCore_le_center_of_isQuasisimple hEq).trans hZleN
  have hN_eq_core : N = pPrimeCore 2 E := le_antisymm hNleCore hP_le_N
  have hcore_eq : pPrimeCore 2 E = Subgroup.center E :=
    le_antisymm (pPrimeCore_le_center_of_isQuasisimple hEq)
      (hZleN.trans hNleCore)
  have hker : N = Subgroup.center E := hN_eq_core.trans hcore_eq
  let eQuot : E ⧸ f.ker ≃* S :=
    QuotientGroup.quotientKerEquivOfSurjective f hfsurj
  exact ⟨hcore_eq,
    ⟨(QuotientGroup.quotientMulEquivOfEq (M := Subgroup.center E) (N := f.ker) hker.symm).trans
      eQuot⟩⟩

/-- An `A₇` quotient forces order at least `2520`. -/
public theorem a7_quotient_absurd_of_card_lt {G : Type u} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal]
    (hcard : Nat.card G < 2520)
    (hA : Nonempty (G ⧸ N ≃* alternatingGroup (Fin 7))) : False := by
  have hdvd := a7_quotient_card_dvd N hA
  have hle : 2520 ≤ Nat.card G := Nat.le_of_dvd (by norm_num) hdvd
  omega

/-- No subgroup of odd `PSL₂` has an `A₇` central quotient. -/
public theorem no_a7_quotient_subgroup_of_psl2_odd
    {K : Type u} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (H : Subgroup (PSL2 K))
    (hA : Nonempty (H ⧸ Subgroup.center H ≃* alternatingGroup (Fin 7))) :
    False := by
  classical
  rcases hK with ⟨p, f, hp, hpodd, hf, hcard⟩
  let : Fact p.Prime := ⟨hp⟩
  have hFcard : Nat.card K = p ^ f := hcard
  rcases Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification
      (p := p) (f := f) hFcard H with
    hElementary | hCyclic | hDihedral | hA4 | hS4 | hA5 |
      hSemidirect | hPSL | hPGL
  · -- elementary abelian `p`-group: solvable, so no `A₇` quotient
    let : IsElementaryAbelian p H := hElementary
    have hHp : IsPGroup p H := IsElementaryAbelian.isPGroup p H
    exact a7_quotient_absurd_of_solvable (N := Subgroup.center H)
      (isSolvable_of_isPGroup hHp) hA
  · -- cyclic: solvable
    rcases hCyclic with ⟨_z, _hzdiv, _hcard, hcyc⟩
    exact a7_quotient_absurd_of_solvable (N := Subgroup.center H)
      (isSolvable_of_isCyclic hcyc) hA
  · -- dihedral: solvable
    rcases hDihedral with ⟨z, _hzdiv, hcardH, hdiso⟩
    have hz_ne : z ≠ 0 := by
      intro hz
      have hcard0 : Nat.card H = 0 := by
        simpa [hcardH, hz]
      exact Nat.card_pos.ne' hcard0
    let : NeZero z := ⟨hz_ne⟩
    have hDsolv : Group.IsSolvable (DihedralGroup z) := isSolvable_of_dihedralGroup z
    have hHsolv : Group.IsSolvable H :=
      Group.isSolvable_of_surjective (f := hdiso.some.symm.toMonoidHom)
        hdiso.some.symm.surjective
    exact a7_quotient_absurd_of_solvable (N := Subgroup.center H) hHsolv hA
  · -- A₄
    have hHcard : Nat.card H = 12 := by
      rw [Nat.card_congr hA4.2.some.toEquiv, nat_card_alternatingGroup]
      norm_num
    exact a7_quotient_absurd_of_card_lt (N := Subgroup.center H) (by omega) hA
  · -- S₄
    have hHcard : Nat.card H = 24 := by
      rw [Nat.card_congr hS4.2.some.toEquiv, Nat.card_perm]
      norm_num
    exact a7_quotient_absurd_of_card_lt (N := Subgroup.center H) (by omega) hA
  · -- A₅
    have hHcard : Nat.card H = 60 := by
      rw [Nat.card_congr hA5.2.some.toEquiv, nat_card_alternatingGroup]
      norm_num
    exact a7_quotient_absurd_of_card_lt (N := Subgroup.center H) (by omega) hA
  · -- semidirect `N ⋊ C`: solvable
    rcases hSemidirect with
      ⟨m, t, hmt, hmt2, N, C, hNnorm, hNp, hNcard, hCcyc, hCcard, hdisj, hsup⟩
    let : N.Normal := hNnorm
    let : IsElementaryAbelian p N := hNp
    have hNp' : IsPGroup p N := IsElementaryAbelian.isPGroup p N
    have hNsolv : Group.IsSolvable N := isSolvable_of_isPGroup hNp'
    have hHsolv : Group.IsSolvable H :=
      isSolvable_of_semidirect N C hNsolv hCcyc hsup
    exact a7_quotient_absurd_of_solvable (N := Subgroup.center H) hHsolv hA
  · -- `PSL₂` over a subfield
    rcases hPSL with ⟨m, hm, hmdiv, hHpsl⟩
    let : Field (GaloisField p m) := inferInstance
    let : Finite (GaloisField p m) := inferInstance
    have hGFcard : Nat.card (GaloisField p m) = p ^ m := by
      exact GaloisField.card p m hm
    have hGFodd : IsOddPrimePower (Nat.card (GaloisField p m)) :=
      ⟨p, m, hp, hpodd, Nat.pos_of_ne_zero hm, hGFcard⟩
    by_cases h3 : 3 < Nat.card (GaloisField p m)
    · have hcenter : Subgroup.center (PSL2 (GaloisField p m)) = ⊥ :=
        psl2_center_eq_bot (K := GaloisField p m)
      have hHcenter : Subgroup.center H = ⊥ := by
        have hc : Nat.card (Subgroup.center H) =
            Nat.card (Subgroup.center (PSL2 (GaloisField p m))) :=
          Nat.card_congr (Subgroup.centerCongr hHpsl.some).toEquiv
        have hcb : Nat.card (Subgroup.center (PSL2 (GaloisField p m))) = 1 := by
          rw [hcenter]
          simp
        exact Subgroup.eq_bot_of_card_eq (Subgroup.center H) (by rw [hc, hcb])
      have hA7iso : Nonempty (H ≃* alternatingGroup (Fin 7)) := by
        let eBot : H ⧸ Subgroup.center H ≃* H :=
          (QuotientGroup.quotientMulEquivOfEq (G := H)
            (M := Subgroup.center H) (N := ⊥) hHcenter).trans
            (QuotientGroup.quotientBot (G := H))
        exact ⟨eBot.symm.trans hA.some⟩
      exact psl2_ne_a7 hGFodd ⟨hHpsl.some.symm.trans hA7iso.some⟩
    · have hGFge3 : 3 ≤ Nat.card (GaloisField p m) := by
        rw [hGFcard]
        have hp_ne_two : p ≠ 2 := by
          intro h
          subst p
          exact hpodd.not_two_dvd_nat (by norm_num)
        have hp2 : 2 ≤ p := hp.two_le
        have hp3 : 3 ≤ p := by omega
        have hpm : 1 ≤ m := Nat.pos_of_ne_zero hm
        calc
          3 ≤ p := hp3
          _ ≤ p ^ m := by
            simpa using (Nat.pow_le_pow_right (by omega : 0 < p) hpm : p ^ 1 ≤ p ^ m)
      have hcardGF : Nat.card (GaloisField p m) = 3 := by
        apply le_antisymm
        · exact le_of_not_gt h3
        · exact hGFge3
      have hHcard : Nat.card H = 12 := by
        have hHcard' : Nat.card H = Nat.card (PSL2 (GaloisField p m)) :=
          Nat.card_congr hHpsl.some.toEquiv
        rw [hHcard', psl2_card_formula (K := GaloisField p m) hGFodd, hcardGF]
        norm_num
      exact a7_quotient_absurd_of_card_lt (N := Subgroup.center H) (by omega) hA
  · -- `PGL₂` over a subfield
    rcases hPGL with ⟨m, hm, hmdiv, hHpgl⟩
    let : Field (GaloisField p m) := inferInstance
    let : Finite (GaloisField p m) := inferInstance
    have hGFcard : Nat.card (GaloisField p m) = p ^ m := by
      exact GaloisField.card p m hm
    have hGFodd : IsOddPrimePower (Nat.card (GaloisField p m)) :=
      ⟨p, m, hp, hpodd, Nat.pos_of_ne_zero hm, hGFcard⟩
    have hcenter : Subgroup.center (PGL2 (GaloisField p m)) = ⊥ :=
      pgl2_center_eq_bot (K := GaloisField p m)
    have hHcenter : Subgroup.center H = ⊥ := by
      have hc : Nat.card (Subgroup.center H) =
          Nat.card (Subgroup.center (PGL2 (GaloisField p m))) :=
        Nat.card_congr (Subgroup.centerCongr hHpgl.some).toEquiv
      have hcb : Nat.card (Subgroup.center (PGL2 (GaloisField p m))) = 1 := by
        rw [hcenter]
        simp
      exact Subgroup.eq_bot_of_card_eq (Subgroup.center H) (by rw [hc, hcb])
    have hA7iso : Nonempty (H ≃* alternatingGroup (Fin 7)) := by
      let eBot : H ⧸ Subgroup.center H ≃* H :=
        (QuotientGroup.quotientMulEquivOfEq (G := H)
          (M := Subgroup.center H) (N := ⊥) hHcenter).trans
          (QuotientGroup.quotientBot (G := H))
      exact ⟨eBot.symm.trans hA.some⟩
    exact pgl2_ne_a7 hGFodd ⟨hHpgl.some.symm.trans hA7iso.some⟩

/-! ## Forward layer containment -/

/-- The layer centralizes `B ∩ M = O₂'(M)`, hence every `X ≤ B ∩ M`. -/
private theorem firstCase_cyclic_componentLayer_le_centralizer
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (hfirst : FirstCase c)
    (M : Subgroup G) (hMmax : IsCoatom M)
    (hSM : (c.S : Subgroup G) ≤ M)
    (fd : FirstCaseFourData c od.d)
    (hV2 : fd.V2 ≤ componentLayerOf M)
    (hA7 : Nonempty ((componentLayerOf M) ⧸
      pPrimeCore 2 (componentLayerOf M) ≃* alternatingGroup (Fin 7)))
    (X : Subgroup G) (hXle : X ≤ od.d.bg.B ⊓ M) :
    componentLayerOf M ≤ Subgroup.centralizer (X : Set G) := by
  classical
  let E : Subgroup G := componentLayerOf M
  let O : Subgroup G := (pPrimeCore 2 M).map M.subtype
  have hU : od.d.bg.U = fittingSubgroupOf od.d.bg.U ⊔ od.d.bg.B :=
    firstCase_cyclic_U_eq_FU_sup_B c hfirst od
  have hBM : od.d.bg.B ⊓ M = O :=
    firstCase_cyclic_B_inter_M_eq_oddCore_of_a7_layer
      hmin c od M hMmax hSM fd hV2 hA7 hU
  have hXleO : X ≤ O := by
    rw [← hBM]
    exact hXle
  have hOleM : O ≤ M := Subgroup.map_subtype_le (H := M) (pPrimeCore 2 M)
  have hOodd : Odd (Nat.card O) := by
    have hcard : Nat.card O = Nat.card (pPrimeCore 2 M) :=
      Subgroup.card_map_of_injective M.subtype_injective
    rw [hcard]
    exact Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥M))
  have hOsolv : Group.IsSolvable O := odd_order_theorem O hOodd
  have hOnorm : IsNormalIn O M := by
    refine ⟨hOleM, ?_⟩
    intro m hm o ho
    rcases Subgroup.mem_map.mp ho with ⟨o0, ho0, rfl⟩
    refine Subgroup.mem_map.mpr
      ⟨(⟨m, hm⟩ : M) * o0 * (⟨m, hm⟩ : M)⁻¹, ?_, rfl⟩
    exact (pPrimeCore_normal (p := 2) (G := ↥M)).conj_mem
      o0 ho0 ⟨m, hm⟩
  have hE_norm_O : E ≤ Subgroup.normalizer (O : Set G) :=
    (componentLayerOf_isNormalIn M).1.trans (le_normalizer_of_isNormalIn hOnorm)
  have hcomm : ⁅E, O⁆ = ⊥ :=
    componentLayerOf_centralizes_solvable_of_le_normalizer
      M O hOleM hOsolv hE_norm_O
  have hEcentO : E ≤ Subgroup.centralizer (O : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := E) (H₂ := O)).mp hcomm
  exact hEcentO.trans
    (Subgroup.centralizer_le (show (X : Set G) ⊆ (O : Set G) from hXleO))

/-- In the A₇ layer model, both the layer and `V₂` normalize/normalize the
given nontrivial `X ≤ B ∩ M`. -/
private theorem firstCase_cyclic_layer_and_V2_le_normalizer
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (hfirst : FirstCase c)
    (M : Subgroup G) (hMmax : IsCoatom M)
    (hSM : (c.S : Subgroup G) ≤ M)
    (fd : FirstCaseFourData c od.d)
    (hV2 : fd.V2 ≤ componentLayerOf M)
    (hA7 : Nonempty ((componentLayerOf M) ⧸
      pPrimeCore 2 (componentLayerOf M) ≃* alternatingGroup (Fin 7)))
    (X : Subgroup G) (hXle : X ≤ od.d.bg.B ⊓ M) :
    componentLayerOf M ≤ Subgroup.normalizer (X : Set G) ∧
      fd.V2 ≤ Subgroup.normalizer (X : Set G) := by
  classical
  let N : Subgroup G := Subgroup.normalizer (X : Set G)
  have hEcentX := firstCase_cyclic_componentLayer_le_centralizer
    hmin c od hfirst M hMmax hSM fd hV2 hA7 X hXle
  have hEleN : componentLayerOf M ≤ N :=
    hEcentX.trans (Subgroup.centralizer_le_normalizer (X : Set G))
  have hV2leCentX : fd.V2 ≤ Subgroup.centralizer (X : Set G) := by
    have hXleB : X ≤ od.d.bg.B := hXle.trans inf_le_left
    have hScentB : (od.d.bg.S : Subgroup G) ≤
        Subgroup.centralizer ((od.d.bg.B : Subgroup G) : Set G) :=
      S_centralizes_B od.d.bg
    have hScentX : (od.d.bg.S : Subgroup G) ≤
        Subgroup.centralizer (X : Set G) :=
      hScentB.trans (Subgroup.centralizer_le (show (X : Set G) ⊆
        (od.d.bg.B : Set G) from hXleB))
    have hV2leS : fd.V2 ≤ (c.S : Subgroup G) := fd.V2_le_S
    have hV2leSbg : fd.V2 ≤ (od.d.bg.S : Subgroup G) := by
      simpa [od.d.S_eq] using hV2leS
    exact hV2leSbg.trans hScentX
  have hV2leN : fd.V2 ≤ N :=
    hV2leCentX.trans (Subgroup.centralizer_le_normalizer (X : Set G))
  exact ⟨hEleN, hV2leN⟩

/-- `N_G(X)` is proper for nontrivial `X ≤ B` (the odd subgroup `B` cannot
contain the whole simple group). -/
private theorem firstCase_cyclic_normalizer_proper
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (hfirst : FirstCase c)
    (M : Subgroup G)
    (X : Subgroup G) (hXne : X ≠ ⊥) (hXle : X ≤ od.d.bg.B ⊓ M) :
    Subgroup.normalizer (X : Set G) ≠ ⊤ := by
  classical
  have hXleB : X ≤ od.d.bg.B := hXle.trans inf_le_left
  intro hNtop
  have hXnormal : X.Normal :=
    (Subgroup.normalizer_eq_top_iff (H := X)).mp hNtop
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ (minimalCounterexample_isSimple hmin)
      X hXnormal with hXbot | hXtop
  · exact hXne hXbot
  · have hU : od.d.bg.U = fittingSubgroupOf od.d.bg.U ⊔ od.d.bg.B :=
      firstCase_cyclic_U_eq_FU_sup_B c hfirst od
    have hBodd : Odd (Nat.card (↥od.d.bg.B)) := firstCase_cyclic_B_odd c od hU
    have hGodd : Odd (Nat.card G) := by
      have hXtop' : X = ⊤ := hXtop
      have hGleB : (⊤ : Subgroup G) ≤ od.d.bg.B := by
        intro g _hg
        have hgX : g ∈ X := by
          rw [hXtop']
          trivial
        exact hXleB hgX
      have hGcard_dvd_top : Nat.card (⊤ : Subgroup G) ∣ Nat.card (↥od.d.bg.B) :=
        Subgroup.card_dvd_of_le hGleB
      have hGcard_dvd : Nat.card G ∣ Nat.card (↥od.d.bg.B) := by
        simpa using hGcard_dvd_top
      exact Odd.of_dvd_nat hBodd hGcard_dvd
    have htwo_dvd : 2 ∣ Nat.card G := by
      have hord2 : orderOf c.t = 2 :=
        orderOf_eq_prime (by simpa [pow_two] using c.t_involution.2) c.t_involution.1
      have hdvd : orderOf c.t ∣ Nat.card G := orderOf_dvd_natCard c.t
      rwa [hord2] at hdvd
    exact hGodd.not_two_dvd_nat htwo_dvd

/-- Forward containment `E(M) ≤ E(N_G(X))` for the A₇ layer model. -/
private theorem firstCase_cyclic_componentLayer_le_componentLayer_of_normalizer
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (hfirst : FirstCase c) (hHhat : c.Hhat = c.H)
    (M : Subgroup G) (hMmax : IsCoatom M)
    (hSM : (c.S : Subgroup G) ≤ M)
    (fd : FirstCaseFourData c od.d)
    (hV2 : fd.V2 ≤ componentLayerOf M)
    (hA7 : Nonempty ((componentLayerOf M) ⧸
      pPrimeCore 2 (componentLayerOf M) ≃* alternatingGroup (Fin 7)))
    (X : Subgroup G) (hXne : X ≠ ⊥) (hXle : X ≤ od.d.bg.B ⊓ M) :
    componentLayerOf M ≤ componentLayerOf (Subgroup.normalizer (X : Set G)) := by
  classical
  let E : Subgroup G := componentLayerOf M
  let N : Subgroup G := Subgroup.normalizer (X : Set G)
  have hEne : E ≠ ⊥ := by
    intro hbot
    apply (by
      have hV2ne : fd.V2 ≠ ⊥ := by
        intro hVbot
        have hcard : Nat.card fd.V2 = 4 := fd.V2_klein.card_four
        rw [hVbot] at hcard
        norm_num at hcard
      exact hV2ne)
    apply le_bot_iff.mp
    intro x hx
    exact Subgroup.mem_bot.mp (by simpa [E, hbot] using hV2 hx)
  obtain ⟨hE_qs, hE7, hZodd⟩ :=
    componentLayerOf_quasisimple_of_a7 M hMmax hEne hA7
  have hEleN : E ≤ N :=
    (firstCase_cyclic_layer_and_V2_le_normalizer
      hmin c od hfirst M hMmax hSM fd hV2 hA7 X hXle).1
  have hV2leN : fd.V2 ≤ N :=
    (firstCase_cyclic_layer_and_V2_le_normalizer
      hmin c od hfirst M hMmax hSM fd hV2 hA7 X hXle).2
  have hNtop : N ≠ ⊤ :=
    firstCase_cyclic_normalizer_proper hmin c od hfirst M X hXne hXle
  have hVN : fd.V2 ≤ N := hV2leN
  have hV2klein : IsKleinFour fd.V2 := fd.V2_klein
  have hVS : fd.V2 ≤ (c.S : Subgroup G) := fd.V2_le_S
  have hbranch := lemma_2_9 (V := fd.V2) (N := N)
    hmin c (firstCase_lemma29Hypothesis c hfirst hHhat)
    hVN fd.t_mem_V2 hV2klein hNtop hVS
  rcases hbranch with htwo | hlayer
  · exfalso
    let K : Subgroup G := twoCoreOf N
    have hKnorm : IsNormalIn K N := twoCoreOf_isNormalIn N
    have hinv : ∃ v : G, v ∈ E ⊓ K ∧ v ≠ 1 ∧ v ^ 2 = 1 := by
      rcases Subgroup.ne_bot_iff_exists_ne_one.mp htwo with ⟨v, hvne⟩
      have hv_mem : (v : G) ∈ fd.V2 ⊓ K := v.2
      have hvV2 : (v : G) ∈ fd.V2 := (Subgroup.mem_inf.mp hv_mem).1
      have hvE : (v : G) ∈ E := hV2 hvV2
      refine ⟨v, ⟨hvE, (Subgroup.mem_inf.mp hv_mem).2⟩, ?_, ?_⟩
      · intro h1
        exact hvne (Subtype.ext h1)
      · exact involution_of_kleinFour fd.V2_klein hvV2 (by
          intro h1
          exact hvne (Subtype.ext h1))
    have hE_le_K : E ≤ K :=
      a7_quasisimple_le_of_normal_intersection_involution
        E K N hE_qs hZodd hEleN hKnorm hinv
    have hKp : IsPGroup 2 K := twoCoreOf_isPGroup N
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hKsolv : Group.IsSolvable K := by
      let : Group.IsNilpotent (↥K) := hKp.isNilpotent
      infer_instance
    have hEsolv : Group.IsSolvable E :=
      isSolvable_of_le_of_isSolvable E K hE_le_K hKsolv
    exact quasisimple_not_solvable hE_qs hEsolv
  · let L : Subgroup G := componentLayerOf N
    have hLnorm : IsNormalIn L N := componentLayerOf_isNormalIn N
    have hinv : ∃ v : G, v ∈ E ⊓ L ∧ v ≠ 1 ∧ v ^ 2 = 1 := by
      rcases Subgroup.ne_bot_iff_exists_ne_one.mp hlayer with ⟨v, hvne⟩
      have hv_mem : (v : G) ∈ fd.V2 ⊓ L := v.2
      have hvV2 : (v : G) ∈ fd.V2 := (Subgroup.mem_inf.mp hv_mem).1
      have hvE : (v : G) ∈ E := hV2 hvV2
      refine ⟨v, ⟨hvE, (Subgroup.mem_inf.mp hv_mem).2⟩, ?_, ?_⟩
      · intro h1
        exact hvne (Subtype.ext h1)
      · exact involution_of_kleinFour fd.V2_klein hvV2 (by
          intro h1
          exact hvne (Subtype.ext h1))
    exact a7_quasisimple_le_of_normal_intersection_involution
      E L N hE_qs hZodd hEleN hLnorm hinv

/-! ## Reverse layer containment -/

/-- The image of a nontrivial perfect subgroup across a solvable normal
kernel remains nontrivial and perfect. -/
private theorem perfect_image_ne_bot_of_solvable_kernel
    {H : Type u} [Group H] [Finite H]
    (E : Subgroup H) (hEperf : Group.IsPerfect E) (hEne : E ≠ ⊥)
    (O : Subgroup H) [O.Normal] (hOsolv : Group.IsSolvable O) :
    let q : H →* H ⧸ O := QuotientGroup.mk' O
    let Ebar : Subgroup (H ⧸ O) := E.map q
    Ebar ≠ ⊥ ∧ Group.IsPerfect Ebar := by
  classical
  dsimp
  let q : H →* H ⧸ O := QuotientGroup.mk' O
  let Ebar : Subgroup (H ⧸ O) := E.map q
  have hEbarperf : Group.IsPerfect Ebar := by
    dsimp [Ebar]
    let : Group.IsPerfect E := hEperf
    exact Group.IsPerfect.map q
  have hEbarne : Ebar ≠ ⊥ := by
    intro hbot
    have hEleO : E ≤ O := by
      have hker : E ≤ q.ker := (Subgroup.map_eq_bot_iff E).mp hbot
      simpa [q, QuotientGroup.ker_mk'] using hker
    let : Group.IsSolvable O := hOsolv
    let : Group.IsSolvable (E.subgroupOf O) := inferInstance
    have hEsolv : Group.IsSolvable E :=
      isSolvable_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hEleO)
    let : Nontrivial E := (Subgroup.nontrivial_iff_ne_bot E).2 hEne
    let : Group.IsPerfect E := hEperf
    exact Group.IsPerfect.not_isSolvable E hEsolv
  exact ⟨hEbarne, hEbarperf⟩

/-- The image of a nontrivial perfect subgroup lies in every normal
odd-index subgroup of the quotient by a solvable normal kernel. -/
private theorem perfect_image_le_normal_odd_index
    {H : Type u} [Group H] [Finite H]
    (E : Subgroup H) (hEperf : Group.IsPerfect E) (hEne : E ≠ ⊥)
    (O : Subgroup H) [O.Normal] (hOsolv : Group.IsSolvable O)
    (L : Subgroup (H ⧸ O)) (hLnormal : L.Normal) (hLindex : Odd L.index) :
    let q : H →* H ⧸ O := QuotientGroup.mk' O
    let Ebar : Subgroup (H ⧸ O) := E.map q
    Ebar ≠ ⊥ ∧ Group.IsPerfect Ebar ∧ Ebar ≤ L := by
  classical
  dsimp
  let q : H →* H ⧸ O := QuotientGroup.mk' O
  let Ebar : Subgroup (H ⧸ O) := E.map q
  obtain ⟨hEbarne, hEbarperf⟩ :=
    perfect_image_ne_bot_of_solvable_kernel E hEperf hEne O hOsolv
  let : L.Normal := hLnormal
  let pi : (H ⧸ O) →* (H ⧸ O) ⧸ L := QuotientGroup.mk' L
  let I : Subgroup ((H ⧸ O) ⧸ L) := Ebar.map pi
  have hIperf : Group.IsPerfect I := by
    dsimp [I]
    let : Group.IsPerfect Ebar := hEbarperf
    exact Group.IsPerfect.map pi
  have hQodd : Odd (Nat.card ((H ⧸ O) ⧸ L)) := by
    simpa only [Subgroup.index_eq_card] using hLindex
  have hQsolv : Group.IsSolvable ((H ⧸ O) ⧸ L) :=
    odd_order_theorem ((H ⧸ O) ⧸ L) hQodd
  have hIbot : I = ⊥ := by
    by_contra hIne
    let : Group.IsSolvable ((H ⧸ O) ⧸ L) := hQsolv
    have hIsolv : Group.IsSolvable I := inferInstance
    let : Nontrivial I := (Subgroup.nontrivial_iff_ne_bot I).2 hIne
    let : Group.IsPerfect I := hIperf
    exact Group.IsPerfect.not_isSolvable I hIsolv
  have hEbarL : Ebar ≤ L := by
    have hker : Ebar ≤ pi.ker := (Subgroup.map_eq_bot_iff Ebar).mp hIbot
    simpa [pi, QuotientGroup.ker_mk'] using hker
  exact ⟨hEbarne, hEbarperf, hEbarL⟩

/-- The central quotient of a group transported across an isomorphism. -/
public lemma central_quotient_of_mulEquiv
    {A B : Type u} [Group A] [Group B]
    (e : A ≃* B)
    (hA : Nonempty (A ⧸ Subgroup.center A ≃* alternatingGroup (Fin 7))) :
    Nonempty (B ⧸ Subgroup.center B ≃* alternatingGroup (Fin 7)) := by
  have hmap := map_center_eq_center_of_mulEquiv e
  exact ⟨(QuotientGroup.congr (Subgroup.center A) (Subgroup.center B) e hmap).symm.trans hA.some⟩

/-- The image of a quasisimple `A₇` group across a central normal kernel
retains its `A₇` central quotient. -/
public theorem a7_central_quotient_of_image_of_central_kernel
    {H : Type u} [Group H] [Finite H]
    (E : Subgroup H) (hEq : IsQuasisimple E)
    (O : Subgroup H) [O.Normal] (hOsolv : Group.IsSolvable O)
    (hEO : E ≤ Subgroup.centralizer (O : Set H))
    (hA : Nonempty (E ⧸ Subgroup.center E ≃* alternatingGroup (Fin 7))) :
    let q : H →* H ⧸ O := QuotientGroup.mk' O
    let Ebar : Subgroup (H ⧸ O) := E.map q
    Nonempty (Ebar ⧸ Subgroup.center Ebar ≃* alternatingGroup (Fin 7)) := by
  classical
  dsimp
  let q : H →* H ⧸ O := QuotientGroup.mk' O
  let Ebar : Subgroup (H ⧸ O) := E.map q
  let f : E →* Ebar :=
    (q.comp E.subtype).codRestrict Ebar (fun x => Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩)
  have hf : Function.Surjective f := by
    intro y
    rcases Subgroup.mem_map.mp y.2 with ⟨x, hx, hxy⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    exact hxy
  have hker_le_center : f.ker ≤ Subgroup.center E := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hxO : (x : H) ∈ O := by
      have hfx1 : q (E.subtype x) = 1 :=
        congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
      exact (QuotientGroup.eq_one_iff (N := O) (E.subtype x)).mp hfx1
    have hy_cent : (y : H) ∈ Subgroup.centralizer (O : Set H) := hEO y.2
    exact (Subgroup.mem_centralizer_iff.mp hy_cent (h := (x : H)) hxO).symm
  have hcent_map : Subgroup.center E ≤ (Subgroup.center Ebar).comap f := by
    intro z hz
    exact Subgroup.mem_comap.mpr (by
      rw [Subgroup.mem_center_iff]
      intro y
      rcases hf y with ⟨x, rfl⟩
      have hcomm : x * z = z * x := Subgroup.mem_center_iff.mp hz x
      simpa [f] using congrArg f hcomm)
  have hEperf : Group.IsPerfect E := (Group.isPerfect_def).2 hEq.2.1
  have hEbarperf : Group.IsPerfect Ebar := by
    let : Group.IsPerfect E := hEperf
    exact Group.IsPerfect.ofSurjective hf
  have hEbarne : Ebar ≠ ⊥ := by
    intro hbot
    have hEleO : E ≤ O := by
      have hker : E ≤ q.ker := (Subgroup.map_eq_bot_iff E).mp hbot
      simpa [q, QuotientGroup.ker_mk'] using hker
    let : Group.IsSolvable O := hOsolv
    let : Group.IsSolvable (E.subgroupOf O) := inferInstance
    have hEsolv : Group.IsSolvable E :=
      isSolvable_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hEleO)
    let : Nontrivial E := hEq.1
    let : Group.IsPerfect E := hEperf
    exact Group.IsPerfect.not_isSolvable E hEsolv
  let φ : E ⧸ Subgroup.center E →* Ebar ⧸ Subgroup.center Ebar :=
    QuotientGroup.map (Subgroup.center E) (Subgroup.center Ebar) f hcent_map
  have hφ_surj : Function.Surjective φ := by
    dsimp [φ]
    exact QuotientGroup.map_surjective_of_surjective
      (Subgroup.center E) (Subgroup.center Ebar) f
      ((QuotientGroup.mk'_surjective (Subgroup.center Ebar)).comp hf)
      hcent_map
  let : IsSimpleGroup (E ⧸ Subgroup.center E) :=
    (MulEquiv.isSimpleGroup_congr hA.some).mpr
      (alternatingGroup.isSimpleGroup (by norm_num : 5 ≤ Nat.card (Fin 7)))
  have hφker_bot_or_top :=
    (@IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ _ φ.ker inferInstance)
  rcases hφker_bot_or_top with hbot | htop
  · have hφ_inj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hbot
    let e : E ⧸ Subgroup.center E ≃* Ebar ⧸ Subgroup.center Ebar :=
      MulEquiv.ofBijective φ ⟨hφ_inj, hφ_surj⟩
    exact ⟨e.symm.trans hA.some⟩
  · have hφ_one : ∀ x : E ⧸ Subgroup.center E, φ x = 1 := by
      intro x
      have hxker : x ∈ φ.ker := by
        rw [htop]
        trivial
      exact MonoidHom.mem_ker.mp hxker
    have hsub : Subsingleton (Ebar ⧸ Subgroup.center Ebar) := by
      constructor
      intro a b
      rcases hφ_surj a with ⟨x, rfl⟩
      rcases hφ_surj b with ⟨y, rfl⟩
      simp [hφ_one]
    have hZbar_top : Subgroup.center Ebar = ⊤ :=
      QuotientGroup.subgroup_eq_top_of_subsingleton (Subgroup.center Ebar) hsub
    have hEbar_comm : IsMulCommutative Ebar := by
      refine ⟨⟨fun x y => ?_⟩⟩
      apply Subtype.ext
      have hxZ : x ∈ Subgroup.center Ebar := by
        rw [hZbar_top]
        trivial
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hxZ y).symm
    have hcomm_bot : ⁅Ebar, Ebar⁆ = ⊥ :=
      Subgroup.commutator_self_eq_bot_iff.mpr hEbar_comm
    have hEbar_bot : Ebar = ⊥ := by
      calc
        Ebar = ⁅Ebar, Ebar⁆ := (Subgroup.isPerfect_iff.mp hEbarperf).symm
        _ = ⊥ := hcomm_bot
    exact False.elim (hEbarne hEbar_bot)

/-- Commutators of central-decomposed elements reduce to the `E`-part. -/
private lemma commutator_central_decomposition
    {G : Type u} [Group G]
    {z₁ z₂ e₁ e₂ x y : G}
    (hx : x = z₁ * e₁) (hy : y = z₂ * e₂)
    (hz₁e₁ : z₁ * e₁ = e₁ * z₁) (hz₁e₂ : z₁ * e₂ = e₂ * z₁)
    (hz₂e₁ : z₂ * e₁ = e₁ * z₂) (hz₂e₂ : z₂ * e₂ = e₂ * z₂)
    (hz₁y : z₁ * y = y * z₁) (hz₂x : z₂ * x = x * z₂) :
    ⁅x, y⁆ = ⁅e₁, e₂⁆ := by
  have hz₁z₂ : z₁ * z₂ = z₂ * z₁ := by
    have h1 : z₁ * z₂ * e₂ = z₂ * z₁ * e₂ := by
      calc
        z₁ * z₂ * e₂ = z₁ * (z₂ * e₂) := by rw [mul_assoc]
        _ = (z₂ * e₂) * z₁ := by
          rw [hy] at hz₁y
          exact hz₁y
        _ = z₂ * (e₂ * z₁) := by rw [mul_assoc]
        _ = z₂ * (z₁ * e₂) := by rw [hz₁e₂]
        _ = z₂ * z₁ * e₂ := by rw [mul_assoc]
    exact mul_right_cancel h1
  have hz₂z₁ : z₂ * z₁ = z₁ * z₂ := by
    have h2 : z₂ * z₁ * e₁ = z₁ * z₂ * e₁ := by
      calc
        z₂ * z₁ * e₁ = z₂ * (z₁ * e₁) := by rw [mul_assoc]
        _ = (z₁ * e₁) * z₂ := by
          rw [hx] at hz₂x
          exact hz₂x
        _ = z₁ * (e₁ * z₂) := by rw [mul_assoc]
        _ = z₁ * (z₂ * e₁) := by rw [hz₂e₁]
        _ = z₁ * z₂ * e₁ := by rw [mul_assoc]
    exact mul_right_cancel h2
  have hz1_y : ⁅z₁, z₂ * e₂⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    calc
      z₁ * (z₂ * e₂) = (z₁ * z₂) * e₂ := by rw [mul_assoc]
      _ = (z₂ * z₁) * e₂ := by rw [hz₁z₂]
      _ = z₂ * (z₁ * e₂) := by rw [mul_assoc]
      _ = z₂ * (e₂ * z₁) := by rw [hz₁e₂]
      _ = (z₂ * e₂) * z₁ := by rw [mul_assoc]
  have hz2_e1 : ⁅e₁, z₂⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact hz₂e₁.symm
  have hc₂e₁ : Commute z₂ e₁ := hz₂e₁
  have hc₂e₂ : Commute z₂ e₂ := hz₂e₂
  have hc₂c : Commute z₂ (e₁ * e₂ * e₁⁻¹ * e₂⁻¹) :=
    (((hc₂e₁.mul_right hc₂e₂).mul_right hc₂e₁.inv_right).mul_right hc₂e₂.inv_right)
  have hcomm1 : ⁅e₁, z₂ * e₂⁆ = ⁅e₁, e₂⁆ := by
    rw [commutatorElement_mul_right_eq_mul_conj]
    rw [hz2_e1, one_mul]
    rw [commutatorElement_def]
    rw [hc₂c.eq, mul_assoc, mul_inv_cancel, mul_one]
  have hc₁e₁ : Commute z₁ e₁ := hz₁e₁
  have hc₁e₂ : Commute z₁ e₂ := hz₁e₂
  have hc₁c : Commute z₁ (e₁ * e₂ * e₁⁻¹ * e₂⁻¹) :=
    (((hc₁e₁.mul_right hc₁e₂).mul_right hc₁e₁.inv_right).mul_right hc₁e₂.inv_right)
  calc
    ⁅x, y⁆ = ⁅z₁ * e₁, z₂ * e₂⁆ := by rw [hx, hy]
    _ = z₁ * ⁅e₁, z₂ * e₂⁆ * z₁⁻¹ * ⁅z₁, z₂ * e₂⁆ :=
      commutatorElement_mul_left_eq_conj_mul z₁ e₁ (z₂ * e₂)
    _ = z₁ * ⁅e₁, e₂⁆ * z₁⁻¹ * 1 := by rw [hcomm1, hz1_y]
    _ = ⁅e₁, e₂⁆ := by
      rw [mul_one]
      rw [commutatorElement_def]
      rw [hc₁c.eq, mul_assoc, mul_inv_cancel, mul_one]

/-- Reverse layer containment in the `A₇` normalizer model. -/
public theorem firstCase_cyclic_componentLayer_normalizer_eq_of_a7
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (hfirst : FirstCase c) (hHhat : c.Hhat = c.H)
    (M : Subgroup G) (hMmax : IsCoatom M)
    (hSM : (c.S : Subgroup G) ≤ M)
    (fd : FirstCaseFourData c od.d)
    (hV2 : fd.V2 ≤ componentLayerOf M)
    (hA7 : Nonempty ((componentLayerOf M) ⧸
      pPrimeCore 2 (componentLayerOf M) ≃* alternatingGroup (Fin 7)))
    (X : Subgroup G) (hXne : X ≠ ⊥) (hXle : X ≤ od.d.bg.B ⊓ M) :
    componentLayerOf (Subgroup.normalizer (X : Set G)) = componentLayerOf M := by
  classical
  let E : Subgroup G := componentLayerOf M
  let N : Subgroup G := Subgroup.normalizer (X : Set G)
  let L : Subgroup G := componentLayerOf N
  have hforward : E ≤ L :=
    firstCase_cyclic_componentLayer_le_componentLayer_of_normalizer
      hmin c od hfirst hHhat M hMmax hSM fd hV2 hA7 X hXne hXle
  have hEne : E ≠ ⊥ := by
    intro hbot
    have hV2ne : fd.V2 ≠ ⊥ := by
      intro hVbot
      have hcard : Nat.card fd.V2 = 4 := fd.V2_klein.card_four
      rw [hVbot] at hcard
      norm_num at hcard
    apply hV2ne
    apply le_bot_iff.mp
    intro x hx
    exact Subgroup.mem_bot.mp (by simpa [E, hbot] using hV2 hx)
  obtain ⟨hEqE, hEcenterA7, _hZodd⟩ :=
    componentLayerOf_quasisimple_of_a7 M hMmax hEne hA7
  have hEleN : E ≤ N :=
    (firstCase_cyclic_layer_and_V2_le_normalizer
      hmin c od hfirst M hMmax hSM fd hV2 hA7 X hXle).1
  have hNtop : N ≠ ⊤ :=
    firstCase_cyclic_normalizer_proper hmin c od hfirst M X hXne hXle
  have hDN : IsDGroup N := properSubgroups_areDGroups hmin N hNtop
  let EN : Subgroup N := E.subgroupOf N
  let O : Subgroup N := pPrimeCore 2 N
  let q : N →* N ⧸ O := QuotientGroup.mk' O
  let Ebar : Subgroup (N ⧸ O) := EN.map q
  let eEN : EN ≃* E := Subgroup.subgroupOfEquivOfLe hEleN
  have hEN_q : IsQuasisimple EN := isQuasisimple_mulEquiv_local eEN.symm hEqE
  have hEN_centerA7 :
      Nonempty (EN ⧸ Subgroup.center EN ≃* alternatingGroup (Fin 7)) :=
    central_quotient_of_mulEquiv eEN.symm hEcenterA7
  have hEperf : Group.IsPerfect E := (Group.isPerfect_def).2 hEqE.2.1
  have hENperf : Group.IsPerfect EN := by
    let : Group.IsPerfect E := hEperf
    exact Group.IsPerfect.ofSurjective (f := eEN.symm.toMonoidHom) eEN.symm.surjective
  have hENne : EN ≠ ⊥ := by
    intro hbot
    have hmap : EN.map N.subtype = E := Subgroup.map_subgroupOf_eq_of_le hEleN
    rw [hbot, Subgroup.map_bot] at hmap
    exact hEne hmap.symm
  have hOodd : Odd (Nat.card O) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := N))
  have hOsolv : Group.IsSolvable O := odd_order_theorem O hOodd
  let Oamb : Subgroup G := O.map N.subtype
  have hOamb_le_N : Oamb ≤ N := Subgroup.map_subtype_le (H := N) O
  have hOamb_solv : Group.IsSolvable Oamb :=
    isSolvable_of_mulEquiv (Subgroup.equivMapOfInjective O N.subtype N.subtype_injective)
  have hOamb_norm : IsNormalIn Oamb N := by
    refine ⟨hOamb_le_N, ?_⟩
    intro n _hn o ho
    rcases Subgroup.mem_map.mp ho with ⟨o0, ho0, rfl⟩
    refine Subgroup.mem_map.mpr
      ⟨(⟨n, _hn⟩ : N) * o0 * (⟨n, _hn⟩ : N)⁻¹, ?_, rfl⟩
    exact (pPrimeCore_normal (p := 2) (G := N)).conj_mem o0 ho0 ⟨n, _hn⟩
  have hL_norm_Oamb : L ≤ Subgroup.normalizer (Oamb : Set G) :=
    (componentLayerOf_isNormalIn N).1.trans (le_normalizer_of_isNormalIn hOamb_norm)
  have hcomm_LO : ⁅L, Oamb⁆ = ⊥ :=
    componentLayerOf_centralizes_solvable_of_le_normalizer
      N Oamb hOamb_le_N hOamb_solv hL_norm_Oamb
  have hLcentOamb : L ≤ Subgroup.centralizer (Oamb : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := L) (H₂ := Oamb)).mp hcomm_LO
  have hENcentO : EN ≤ Subgroup.centralizer (O : Set N) := by
    intro e he o ho
    apply Subtype.ext
    have heL : (e : G) ∈ L := by
      have heE : (e : G) ∈ E := Subgroup.mem_subgroupOf.mp he
      exact hforward heE
    have hoOamb : (o : G) ∈ Oamb := Subgroup.mem_map.mpr ⟨o, ho, rfl⟩
    have he_cent : (e : G) ∈ Subgroup.centralizer (Oamb : Set G) := hLcentOamb heL
    exact Subgroup.mem_centralizer_iff.mp he_cent (h := (o : G)) hoOamb
  have hAbar : Nonempty (Ebar ⧸ Subgroup.center Ebar ≃* alternatingGroup (Fin 7)) :=
    a7_central_quotient_of_image_of_central_kernel EN hEN_q O hOsolv hENcentO hEN_centerA7
  have hEbar_ne_perf :=
    perfect_image_ne_bot_of_solvable_kernel EN hENperf hENne O hOsolv
  rcases hDN with
      ⟨_hSylowN, hQtwo⟩ | ⟨_hSylowN, hA7q⟩ |
        ⟨_hSylowN, K, hK, Lq, hLqnormal, hLqindex, hlin⟩
  · exfalso
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hQsolv : Group.IsSolvable (N ⧸ O) := isSolvable_of_isPGroup hQtwo
    have hTopSolv : Group.IsSolvable (⊤ : Subgroup (N ⧸ O)) :=
      isSolvable_of_mulEquiv (Subgroup.topEquiv (G := N ⧸ O)).symm
    have hEbar_solv : Group.IsSolvable Ebar :=
      isSolvable_of_le_of_isSolvable Ebar (⊤ : Subgroup (N ⧸ O)) le_top hTopSolv
    let : Group.IsPerfect Ebar := hEbar_ne_perf.2
    let : Nontrivial Ebar := (Subgroup.nontrivial_iff_ne_bot Ebar).2 hEbar_ne_perf.1
    exact Group.IsPerfect.not_isSolvable Ebar hEbar_solv
  · have hcard_dvd : (2520 : ℕ) ∣ Nat.card Ebar :=
      a7_quotient_card_dvd (Subgroup.center Ebar) hAbar
    have h2520_le : 2520 ≤ Nat.card Ebar := Nat.le_of_dvd (by norm_num) hcard_dvd
    have : Finite (N ⧸ O) := inferInstance
    have hEbar_card : Nat.card Ebar ≤ Nat.card (N ⧸ O) :=
      Subgroup.card_le_card_group (H := Ebar)
    have hNq_card : Nat.card (N ⧸ O) = 2520 := by
      rw [Nat.card_congr hA7q.some.toEquiv, nat_card_alternatingGroup]
      norm_num
    have hEbar_top : Ebar = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      omega
    have hEN_Osup : O ⊔ EN = ⊤ := by
      have hcomap : (EN.map q).comap q = O ⊔ EN := QuotientGroup.comap_map_mk' O EN
      have htop : (EN.map q).comap q = ⊤ := by
        change EN.map q = ⊤ at hEbar_top
        rw [hEbar_top, Subgroup.comap_top]
      rwa [← hcomap]
    have hLL_le_E : ⁅L, L⁆ ≤ E := by
      rw [Subgroup.commutator_le]
      intro x hx y hy
      have hLleN : L ≤ N := (componentLayerOf_isNormalIn N).1
      have hxN : (⟨x, hLleN hx⟩ : N) ∈ O ⊔ EN := by
        rw [hEN_Osup]
        trivial
      have hyN : (⟨y, hLleN hy⟩ : N) ∈ O ⊔ EN := by
        rw [hEN_Osup]
        trivial
      rcases (Subgroup.mem_sup_of_normal_left (s := O) (t := EN)).mp hxN with
        ⟨z₁, hz₁, e₁, he₁, hx_eq⟩
      rcases (Subgroup.mem_sup_of_normal_left (s := O) (t := EN)).mp hyN with
        ⟨z₂, hz₂, e₂, he₂, hy_eq⟩
      have hxG : x = (z₁ : G) * (e₁ : G) := by
        simpa using (congrArg Subtype.val hx_eq).symm
      have hyG : y = (z₂ : G) * (e₂ : G) := by
        simpa using (congrArg Subtype.val hy_eq).symm
      have he₁E : (e₁ : G) ∈ E := Subgroup.mem_subgroupOf.mp he₁
      have he₂E : (e₂ : G) ∈ E := Subgroup.mem_subgroupOf.mp he₂
      have he₁L : (e₁ : G) ∈ L := hforward he₁E
      have he₂L : (e₂ : G) ∈ L := hforward he₂E
      have hz₁Oamb : (z₁ : G) ∈ Oamb := Subgroup.mem_map.mpr ⟨z₁, hz₁, rfl⟩
      have hz₂Oamb : (z₂ : G) ∈ Oamb := Subgroup.mem_map.mpr ⟨z₂, hz₂, rfl⟩
      have hz₁e₁ : (z₁ : G) * (e₁ : G) = (e₁ : G) * (z₁ : G) := by
        have he_cent : (e₁ : G) ∈ Subgroup.centralizer (Oamb : Set G) := hLcentOamb he₁L
        exact Subgroup.mem_centralizer_iff.mp he_cent (h := (z₁ : G)) hz₁Oamb
      have hz₁e₂ : (z₁ : G) * (e₂ : G) = (e₂ : G) * (z₁ : G) := by
        have he_cent : (e₂ : G) ∈ Subgroup.centralizer (Oamb : Set G) := hLcentOamb he₂L
        exact Subgroup.mem_centralizer_iff.mp he_cent (h := (z₁ : G)) hz₁Oamb
      have hz₂e₁ : (z₂ : G) * (e₁ : G) = (e₁ : G) * (z₂ : G) := by
        have he_cent : (e₁ : G) ∈ Subgroup.centralizer (Oamb : Set G) := hLcentOamb he₁L
        exact Subgroup.mem_centralizer_iff.mp he_cent (h := (z₂ : G)) hz₂Oamb
      have hz₂e₂ : (z₂ : G) * (e₂ : G) = (e₂ : G) * (z₂ : G) := by
        have he_cent : (e₂ : G) ∈ Subgroup.centralizer (Oamb : Set G) := hLcentOamb he₂L
        exact Subgroup.mem_centralizer_iff.mp he_cent (h := (z₂ : G)) hz₂Oamb
      have hz₁y : (z₁ : G) * y = y * (z₁ : G) := by
        have hy_cent : y ∈ Subgroup.centralizer (Oamb : Set G) := hLcentOamb hy
        exact Subgroup.mem_centralizer_iff.mp hy_cent (h := (z₁ : G)) hz₁Oamb
      have hz₂x : (z₂ : G) * x = x * (z₂ : G) := by
        have hx_cent : x ∈ Subgroup.centralizer (Oamb : Set G) := hLcentOamb hx
        exact Subgroup.mem_centralizer_iff.mp hx_cent (h := (z₂ : G)) hz₂Oamb
      have hcomm_eq : ⁅x, y⁆ = ⁅(e₁ : G), (e₂ : G)⁆ :=
        commutator_central_decomposition hxG hyG hz₁e₁ hz₁e₂ hz₂e₁ hz₂e₂ hz₁y hz₂x
      rw [hcomm_eq]
      exact Subgroup.commutator_le_self E (E.commutator_mem_commutator he₁E he₂E)
    have hLleE : L ≤ E := by
      have hLL : ⁅L, L⁆ = L := (Subgroup.isPerfect_iff.mp (componentLayerOf_isPerfect N))
      rw [← hLL]
      exact hLL_le_E
    exact le_antisymm hLleE hforward
  · exfalso
    rcases hlin with hPSL | hPGL
    · rcases hPSL with ⟨eL⟩
      have hIm := perfect_image_le_normal_odd_index
        EN hENperf hENne O hOsolv Lq hLqnormal hLqindex
      have hEbarL : Ebar ≤ Lq := hIm.2.2
      let EL : Subgroup Lq := Ebar.subgroupOf Lq
      have hEL_ne : EL ≠ ⊥ := by
        intro hbot
        have hmap : EL.map Lq.subtype = Ebar := Subgroup.map_subgroupOf_eq_of_le hEbarL
        rw [hbot, Subgroup.map_bot] at hmap
        exact hIm.1 hmap.symm
      have hEL_perf : Group.IsPerfect EL := by
        let eEL : EL ≃* Ebar := Subgroup.subgroupOfEquivOfLe hEbarL
        let : Group.IsPerfect Ebar := hIm.2.1
        exact Group.IsPerfect.ofSurjective (f := eEL.symm.toMonoidHom) eEL.symm.surjective
      let J : Subgroup (PSL2 K) := EL.map eL.toMonoidHom
      have hJ_perf : Group.IsPerfect J := by
        dsimp [J]
        let : Group.IsPerfect EL := hEL_perf
        exact Group.IsPerfect.map eL.toMonoidHom
      have hJ_A7 : Nonempty (J ⧸ Subgroup.center J ≃* alternatingGroup (Fin 7)) := by
        let eEL : EL ≃* Ebar := Subgroup.subgroupOfEquivOfLe hEbarL
        let eMap : EL ≃* J :=
          Subgroup.equivMapOfInjective EL eL.toMonoidHom eL.injective
        exact central_quotient_of_mulEquiv (eEL.symm.trans eMap) hAbar
      exact no_a7_quotient_subgroup_of_psl2_odd hK J hJ_A7
    · rcases hPGL with ⟨eL⟩
      have hIm := perfect_image_le_normal_odd_index
        EN hENperf hENne O hOsolv Lq hLqnormal hLqindex
      have hEbarL : Ebar ≤ Lq := hIm.2.2
      let EL : Subgroup Lq := Ebar.subgroupOf Lq
      have hEL_ne : EL ≠ ⊥ := by
        intro hbot
        have hmap : EL.map Lq.subtype = Ebar := Subgroup.map_subgroupOf_eq_of_le hEbarL
        rw [hbot, Subgroup.map_bot] at hmap
        exact hIm.1 hmap.symm
      have hEL_perf : Group.IsPerfect EL := by
        let eEL : EL ≃* Ebar := Subgroup.subgroupOfEquivOfLe hEbarL
        let : Group.IsPerfect Ebar := hIm.2.1
        exact Group.IsPerfect.ofSurjective (f := eEL.symm.toMonoidHom) eEL.symm.surjective
      let J : Subgroup (PGL2 K) := EL.map eL.toMonoidHom
      have hJ_perf : Group.IsPerfect J := by
        dsimp [J]
        let : Group.IsPerfect EL := hEL_perf
        exact Group.IsPerfect.map eL.toMonoidHom
      have hJ_A7 : Nonempty (J ⧸ Subgroup.center J ≃* alternatingGroup (Fin 7)) := by
        let eEL : EL ≃* Ebar := Subgroup.subgroupOfEquivOfLe hEbarL
        let eMap : EL ≃* J :=
          Subgroup.equivMapOfInjective EL eL.toMonoidHom eL.injective
        exact central_quotient_of_mulEquiv (eEL.symm.trans eMap) hAbar
      let : Finite (PGL2 K) :=
        Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
      by_cases hK3 : Nat.card K = 3
      · have hPGLcard : Nat.card (PGL2 K) = 3 * (3 ^ 2 - 1) := by
          simp [pgl2_card_formula K, hK3]
        have hcardJ : Nat.card J < 2520 := by
          have hle : Nat.card J ≤ Nat.card (PGL2 K) :=
            Subgroup.card_le_card_group (H := J)
          rw [hPGLcard] at hle
          omega
        exact a7_quotient_absurd_of_card_lt (N := Subgroup.center J) hcardJ hJ_A7
      · have hcard_ge : 3 ≤ Nat.card K := by
          rcases hK with ⟨p, n, hp, hpodd, hn, hcard⟩
          have hpne2 : p ≠ 2 := by
            intro hp2
            subst p
            exact hpodd.not_two_dvd_nat (by simp)
          have hpge : 3 ≤ p := by
            have hp2 := hp.two_le
            omega
          rw [hcard]
          exact hpge.trans (by
            calc
              p = p ^ 1 := by simp
              _ ≤ p ^ n := Nat.pow_le_pow_right hp.pos hn)
        have hcard_gt : 3 < Nat.card K := by omega
        have hJleComm : J ≤ commutator (PGL2 K) := by
          let : Group.IsPerfect J := hJ_perf
          have hJJ : ⁅J, J⁆ = J := Subgroup.commutator_eq_self
          rw [← hJJ]
          exact Subgroup.commutator_mono le_top le_top
        let C : Subgroup (PGL2 K) := commutator (PGL2 K)
        have eC : Nonempty (C ≃* PSL2 K) :=
          commutator_mulEquiv_psl2_of_mulEquiv_pgl2_card_gt_three
            K hK hcard_gt (MulEquiv.refl (PGL2 K))
        let JC : Subgroup C := J.subgroupOf C
        let JPSL : Subgroup (PSL2 K) := JC.map eC.some.toMonoidHom
        have hJPSL_A7 :
            Nonempty (JPSL ⧸ Subgroup.center JPSL ≃* alternatingGroup (Fin 7)) := by
          let eJCJ : JC ≃* J := Subgroup.subgroupOfEquivOfLe hJleComm
          let eMap : JC ≃* JPSL :=
            Subgroup.equivMapOfInjective JC eC.some.toMonoidHom eC.some.injective
          exact central_quotient_of_mulEquiv (eJCJ.symm.trans eMap) hJ_A7
        exact no_a7_quotient_subgroup_of_psl2_odd hK JPSL hJPSL_A7

end CFSG.GorensteinWalter
