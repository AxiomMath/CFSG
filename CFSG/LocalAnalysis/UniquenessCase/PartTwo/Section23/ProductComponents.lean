module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsComponents
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21c
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
public import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
public import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22m
public import CFSG.RankThree.PartOne.S12K.OrdRigid
public import CFSG.Adapters.LieModelOrders
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20d
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22rj

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem uc22s23pc_component
    {M : Subgroup G} {A B : Type} [Group A] [Group B] [IsSimpleGroup A]
    (hAab : ¬ ∀ x y : A, x * y = y * x)
    (e : Bar2 (Hinf M) ≃* A × B) :
    ∃ K : Subgroup G, K ≤ Hinf M ∧ K ∈ calC M ∧ Nonempty (Bar2 K ≃* A) ∧
      (∀ a : A, ∃ y : ↥(Hinf M), (y : G) ∈ K ∧
        (e (uc22p21cPi (Hinf M) y)).1 = a) ∧
      (∀ y : ↥(Hinf M), (y : G) ∈ K → (e (uc22p21cPi (Hinf M) y)).2 = 1) := by
  classical
  let Y : Subgroup G := Hinf M
  let π : ↥Y →* Bar2 Y := QuotientGroup.mk' (CFSG.pCore 2 ↥Y)
  let φ : ↥Y →* A × B := e.toMonoidHom.comp π
  let ψA : ↥Y →* A := (MonoidHom.fst A B).comp φ
  let ψB : ↥Y →* B := (MonoidHom.snd A B).comp φ
  let H : Subgroup G := (ψB.ker).map Y.subtype
  let K : Subgroup G := Hinf H
  have hπ : π = uc22p21cPi Y := rfl
  have hAab' : ∃ a b : A, a * b ≠ b * a := by
    by_contra h
    apply hAab
    intro x y
    by_contra hxy
    exact h ⟨x, y, hxy⟩
  have hAq : CFSG.Open.IsQuasisimple A := uc22p22a_isQuasisimple_of_simple hAab'
  have hAperf : Group.IsPerfect A := ⟨hAq.1⟩
  have hYM : Y ≤ M := uc22p21c_Hinf_le M
  have hYnorm : (Y.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYM).2 (uc22p22m_le_normalizer_Hinf M)
  have hHY : H ≤ Y := Subgroup.map_subtype_le _
  have hHeq : H.subgroupOf Y = ψB.ker := by
    ext y
    constructor
    · intro hy
      rw [Subgroup.mem_subgroupOf] at hy
      obtain ⟨k, hk, hky⟩ := Subgroup.mem_map.1 hy
      have hky' : k = y := Subtype.ext hky
      simpa [hky'] using hk
    · intro hy
      rw [Subgroup.mem_subgroupOf]
      exact Subgroup.mem_map.2 ⟨y, hy, rfl⟩
  have hHnorm : (H.subgroupOf Y).Normal := by
    rw [hHeq]
    infer_instance
  have hker_surj : (ψB.ker).map ψA = ⊤ := by
    rw [eq_top_iff]
    intro a _
    obtain ⟨q, hq⟩ := e.surjective (a, 1)
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥Y) q
    refine Subgroup.mem_map.2 ⟨y, ?_, ?_⟩
    · change (e (π y)).2 = 1
      rw [show π y = QuotientGroup.mk' (CFSG.pCore 2 ↥Y) y from rfl, hq]
    · change (e (π y)).1 = a
      rw [show π y = QuotientGroup.mk' (CFSG.pCore 2 ↥Y) y from rfl, hq]
  have hf : Function.Surjective (ψA.comp (Subgroup.inclusion hHY)) := by
    intro a
    have ha : a ∈ (ψB.ker).map ψA := by
      rw [hker_surj]
      exact Subgroup.mem_top a
    obtain ⟨y, hy, hya⟩ := Subgroup.mem_map.1 ha
    have hyH : (y : G) ∈ H := by
      rw [← Subgroup.mem_subgroupOf (H := H) (K := Y), hHeq]
      exact hy
    refine ⟨⟨(y : G), hyH⟩, ?_⟩
    show ψA (Subgroup.inclusion hHY ⟨(y : G), hyH⟩) = a
    rw [show Subgroup.inclusion hHY ⟨(y : G), hyH⟩ = y from Subtype.ext rfl, hya]
  have htopA : CFSG.perfectResidual A = ⊤ := by
    rw [eq_top_iff]
    intro x _
    change x ∈ ⨅ n : ℕ, derivedSeries A n
    rw [Subgroup.mem_iInf]
    intro n
    rw [Group.IsPerfect.derivedSeries_eq_top]
    exact Subgroup.mem_top x
  have hmap := uc22p21c_map_perfectResidual (ψA.comp (Subgroup.inclusion hHY)) hf
  have hK_surj : ∀ a : A, ∃ y : ↥Y, (y : G) ∈ K ∧ ψA y = a := by
    intro a
    have ha : a ∈ (CFSG.perfectResidual ↥H).map (ψA.comp (Subgroup.inclusion hHY)) := by
      rw [hmap, htopA]
      exact Subgroup.mem_top a
    obtain ⟨h, hh, hha⟩ := Subgroup.mem_map.1 ha
    refine ⟨Subgroup.inclusion hHY h, ?_, hha⟩
    exact uc22p21c_mem_Hinf.2 ⟨h, hh, rfl⟩
  have hKH : K ≤ H := uc22p21c_Hinf_le H
  have hKnormH : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).2 (uc22p22m_le_normalizer_Hinf H)
  have hKY : CFSG.Open.IsSubnormal K Y :=
    .step hKH hKnormH (.step hHY hHnorm (.refl Y))
  let K' : Subgroup (Bar2 Y) := (K.subgroupOf Y).map π
  have hK'sub : K'.IsSubnormal := by
    have h1 : (K.subgroupOf Y).IsSubnormal :=
      (CFSG.Open.IsSubnormal.iff_subgroupOf (hKH.trans hHY)).1 hKY
    exact h1.map (by rw [hπ]; exact QuotientGroup.mk'_surjective _)
  have hK'ne : K' ≠ ⊥ := by
    intro hbot
    obtain ⟨a, ha1⟩ := exists_ne (1 : A)
    obtain ⟨y, hy, hya⟩ := hK_surj a
    have hyY : y ∈ K.subgroupOf Y := Subgroup.mem_subgroupOf.2 hy
    have hmem : π y ∈ K' := Subgroup.mem_map.2 ⟨y, hyY, rfl⟩
    rw [hbot] at hmem
    have hπy : π y = 1 := by simpa using hmem
    have hψ1 : ψA y = 1 := by simp [ψA, φ, hπy]
    rw [hψ1] at hya
    exact ha1 hya.symm
  have hK'le : K' ≤ ((MonoidHom.snd A B).comp e.toMonoidHom).ker := by
    intro q hq
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hq
    have hyK : (y : G) ∈ K := Subgroup.mem_subgroupOf.1 hy
    have hyH : (y : G) ∈ H := hKH hyK
    have hyker : y ∈ ψB.ker := by
      rw [← hHeq]
      exact Subgroup.mem_subgroupOf.2 hyH
    change (e (π y)).2 = 1
    exact hyker
  have hK'equiv : Nonempty (↥K' ≃* A) :=
    uc22p22r_equiv_factor e hK'sub hK'ne hK'le
  have hKequiv : Nonempty (Bar2 K ≃* A) := by
    obtain ⟨e1⟩ := uc22p20d_bar2Equiv (hKH.trans hHY) hKY
    obtain ⟨e2⟩ := hK'equiv
    exact ⟨e1.trans e2⟩
  have hKmem : K ∈ calC M := by
    refine ⟨?_, uc22p21c_Hinf_perfect H, ?_⟩
    · exact .step hKH hKnormH (.step hHY hHnorm (.step hYM hYnorm (.refl M)))
    · obtain ⟨eK⟩ := hKequiv
      exact CFSG.Open.IsQuasisimple.of_mulEquiv eK hAq
  refine ⟨K, hKH.trans hHY, hKmem, hKequiv, ?_, ?_⟩
  · intro a
    obtain ⟨y, hy, hya⟩ := hK_surj a
    refine ⟨y, hy, ?_⟩
    simpa [ψA, φ, hπ] using hya
  · intro y hy
    have hyY : y ∈ K.subgroupOf Y := Subgroup.mem_subgroupOf.2 hy
    have hyH : (y : G) ∈ H := hKH hy
    have hyker : y ∈ ψB.ker := by
      rw [← hHeq]
      exact Subgroup.mem_subgroupOf.2 hyH
    have hψ : ψB y = 1 := hyker
    simpa [ψB, φ, hπ] using hψ

theorem exists_two_calC_of_bar2_hinf_prod {M : Subgroup G} {A B : Type} [Group A] [Group B]
    [IsSimpleGroup A] [IsSimpleGroup B]
    (hAab : ¬ ∀ x y : A, x * y = y * x)
    (hBab : ¬ ∀ x y : B, x * y = y * x)
    (e : Bar2 (Hinf M) ≃* A × B) :
    ∃ KA KB : Subgroup G, KA ∈ calC M ∧ KB ∈ calC M ∧ Nonempty (Bar2 KA ≃* A) ∧
      Nonempty (Bar2 KB ≃* B) ∧ barImage M KA ≠ barImage M KB := by
  classical
  obtain ⟨KA, hKAleY, hKAcalC, ⟨eA⟩, hAsurj, hAker⟩ := uc22s23pc_component hAab e
  obtain ⟨KB, hKBleY, hKBcalC, ⟨eB⟩, hBsurj, hBker⟩ :=
    uc22s23pc_component (A := B) (B := A) hBab (e.trans MulEquiv.prodComm)
  refine ⟨KA, KB, hKAcalC, hKBcalC, ⟨eA⟩, ⟨eB⟩, ?_⟩
  have hne : barImage M KA ≠ barImage M KB := by
    intro hEq
    obtain ⟨a, ha1⟩ := exists_ne (1 : A)
    obtain ⟨y, hyKA, hya⟩ := hAsurj a
    have hyY : (y : G) ∈ Hinf M := hKAleY hyKA
    have hyM : (y : G) ∈ M := (uc22p21c_Hinf_le M) hyY
    have hmem : uc22p21cPi M ⟨(y : G), hyM⟩ ∈ barImage M KA :=
      uc22p21c_mem_barImage.2 ⟨⟨(y : G), hyM⟩, hyKA, rfl⟩
    rw [hEq] at hmem
    obtain ⟨b, hbKB, hbeq⟩ := uc22p21c_mem_barImage.1 hmem
    have hbY : (b : G) ∈ Hinf M := hKBleY hbKB
    have hbM : (b : G) ∈ M := (uc22p21c_Hinf_le M) hbY
    have hdiffM : ((b : G)⁻¹ * (y : G)) ∈ pCoreOf 2 M := by
      have h1 : (b : ↥M)⁻¹ * ⟨(y : G), hyM⟩ ∈ CFSG.pCore 2 ↥M :=
        (QuotientGroup.eq).1 hbeq
      exact Subgroup.mem_map.2 ⟨_, h1, rfl⟩
    have hdiffM' : ((y : G)⁻¹ * (b : G)) ∈ pCoreOf 2 M := by
      have h := (pCoreOf 2 M).inv_mem hdiffM
      simpa using h
    have hdiffY : ((y : G)⁻¹ * (b : G)) ∈ Hinf M :=
      (Hinf M).mul_mem ((Hinf M).inv_mem hyY) hbY
    have hMnorm : M ≤ normalizer (pCoreOf 2 M : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M
    have hNnorm : Hinf M ≤ normalizer ((pCoreOf 2 M ⊓ Hinf M : Subgroup G) : Set G) := by
      intro z hz
      exact Subgroup.inf_normalizer_le_normalizer_inf
        ⟨hMnorm ((uc22p21c_Hinf_le M) hz), Subgroup.le_normalizer hz⟩
    have hle : pCoreOf 2 M ⊓ Hinf M ≤ pCoreOf 2 (Hinf M) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right hNnorm
        ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_le inf_le_left)
    have hdiffO2Y : ((y : G)⁻¹ * (b : G)) ∈ pCoreOf 2 (Hinf M) :=
      hle ⟨hdiffM', hdiffY⟩
    have hπeq : uc22p21cPi (Hinf M) y = uc22p21cPi (Hinf M) ⟨(b : G), hbY⟩ := by
      rw [uc22p21cPi]
      change (QuotientGroup.mk y : Bar2 (Hinf M)) =
        QuotientGroup.mk (⟨(b : G), hbY⟩ : ↥(Hinf M))
      rw [QuotientGroup.eq]
      obtain ⟨x, hx, hxeq⟩ := Subgroup.mem_map.1 hdiffO2Y
      have hxy : x = (⟨(y : G), hyY⟩ : ↥(Hinf M))⁻¹ * ⟨(b : G), hbY⟩ :=
        Subtype.ext (by simpa using hxeq)
      rw [← hxy]
      exact hx
    have heq : e (uc22p21cPi (Hinf M) y) = e (uc22p21cPi (Hinf M) ⟨(b : G), hbY⟩) := by
      rw [hπeq]
    have hfirst : (e (uc22p21cPi (Hinf M) y)).1
        = (e (uc22p21cPi (Hinf M) ⟨(b : G), hbY⟩)).1 := congrArg Prod.fst heq
    have hb1 : (e (uc22p21cPi (Hinf M) ⟨(b : G), hbY⟩)).1 = 1 := by
      have h := hBker ⟨(b : G), hbY⟩ hbKB
      simpa [MulEquiv.trans_apply] using h
    exact ha1 (hya.symm.trans (hfirst.trans hb1))
  exact hne

private theorem uc22s23pc_isL2_param_eq {X : Type} [Group X] {a n : ℕ}
    (ha : IsL2 X a) (hn : IsL2 X n) (ha1 : 1 ≤ a) (hn1 : 1 ≤ n) : a = n := by
  have h1 : Nat.card X = ordA 1 (2 ^ a) := ha.card_eq_lieOrd (by norm_num)
  have h2 : Nat.card X = ordA 1 (2 ^ n) := hn.card_eq_lieOrd (by norm_num)
  exact CFSG.RankThree.PartOne.S12K.ordA_one_inj ha1 hn1 (h1.symm.trans h2)

private theorem uc22s23pc_false_isL2_isL2 {X : Type} [Group X] {a n : ℕ}
    (ha : IsL2 X a) (hn : IsL2 X n) (haodd : Odd a) (hneven : Even n)
    (ha1 : 1 ≤ a) (hn1 : 1 ≤ n) : False := by
  have heq : a = n := uc22s23pc_isL2_param_eq ha hn ha1 hn1
  rw [heq] at haodd
  exact (Nat.not_even_iff_odd.mpr haodd) hneven

private theorem uc22s23pc_false_isL2_isU3 {X : Type} [Group X] {a n : ℕ}
    (ha : IsL2 X a) (hn : IsU3 X n) (ha1 : 1 ≤ a) (hn2 : 2 ≤ n) : False := by
  have h1 : Nat.card X = ordA 1 (2 ^ a) := ha.card_eq_lieOrd (by norm_num)
  have h2 : Nat.card X = ordTwistedA 2 (2 ^ n) := hn.card_eq_lieOrd (by norm_num)
  exact CFSG.Timmesfeld.Orders.ordA_ne_ordTwistedA (n := 1) (f := a) (u := 2) (g := n)
    (by norm_num) ha1 (by norm_num) (by omega) (h1.symm.trans h2)

private theorem uc22s23pc_false_isSz_isL2 {X : Type} [Group X] {a n : ℕ}
    (hS : IsSz X a) (hL : IsL2 X n) : False :=
  CFSG.LocalAnalysis.EvenBN.GMSK.not_three_dvd_card_of_lieModel_twistedB2 hS
    (CFSG.Open.StatedAPI.three_dvd_card_of_statedClassicalModel_psl_two_two
      (CFSG.Blueprint.LieModel.statedClassicalModel hL (by decide)))

private theorem uc22s23pc_false_isSz_isU3 {X : Type} [Group X] {a n : ℕ}
    (hS : IsSz X a) (hU : IsU3 X n) : False := by
  refine CFSG.LocalAnalysis.EvenBN.GMSK.not_three_dvd_card_of_lieModel_twistedB2 hS ?_
  have h2 : Nat.card X = ordTwistedA 2 (2 ^ n) := hU.card_eq_lieOrd (by norm_num)
  rw [h2]
  exact uc22p21k_three_dvd_ordTwistedA_two n

private theorem uc22s23pc_not_comm_of_isL2_or_isU3 {X : Type} [Group X] [Finite X] {n : ℕ}
    (h : IsL2 X n ∨ IsU3 X n) : ¬ ∀ x y : X, x * y = y * x := by
  intro hcomm
  have hsimp : IsSimpleGroup X := by
    rcases h with hL | hU
    · exact CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (t := .PSL) (by decide) hL
    · exact CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (t := .PSU) (by decide) hU
  have h2 : 2 ≤ n := by
    rcases h with hL | hU
    · have hadm := hL.admissible
      simp only [CFSG.Open.StatedLieAdmissible] at hadm
      obtain ⟨-, h1, -, hne, -⟩ := hadm
      by_contra hlt
      have hn1 : n = 1 := by omega
      subst hn1
      exact hne (by norm_num)
    · have hadm := hU.admissible
      simp only [CFSG.Open.StatedLieAdmissible] at hadm
      obtain ⟨-, h1, -, hne⟩ := hadm
      by_contra hlt
      have hn1 : n = 1 := by omega
      subst hn1
      exact hne (by norm_num)
  haveI : IsMulCommutative X := ⟨⟨fun a b => hcomm a b⟩⟩
  have h1 : 1 ≤ n := by
    rcases h with hL | hU
    · exact hL.admissible.2.1
    · exact hU.admissible.2.1
  have h4 : 4 ∣ Nat.card X := by
    rcases h with hL | hU
    · have hcard : Nat.card X = ordA 1 (2 ^ n) := hL.card_eq_lieOrd (by norm_num)
      rw [hcard]
      obtain ⟨r, -, hr⟩ :=
        (CFSG.Timmesfeld.Orders.profile_ordA (n := 1) (f := n) (by norm_num) h1).two
      have hexp : n * (1 * (1 + 1) / 2) = n := by norm_num
      rw [hr, hexp]
      exact dvd_mul_of_dvd_left (dvd_trans (by norm_num : 4 ∣ 2 ^ 2) (pow_dvd_pow 2 h2)) r
    · have hcard : Nat.card X = ordTwistedA 2 (2 ^ n) := hU.card_eq_lieOrd (by norm_num)
      rw [hcard]
      obtain ⟨r, -, hr⟩ :=
        (CFSG.Timmesfeld.Orders.profile_ordTwistedA (n := 2) (g := n) (by norm_num) h1).two
      have hexp : n * (2 * (2 + 1) / 2) = 3 * n := by ring
      rw [hr, hexp]
      exact dvd_mul_of_dvd_left
        (dvd_trans (by norm_num : 4 ∣ 2 ^ 2) (pow_dvd_pow 2 (by omega))) r
  have hprime : (Nat.card X).Prime := (Group.is_simple_iff_prime_card (α := X)).1 hsimp
  have h2' : Nat.card X = 2 :=
    (Nat.Prime.dvd_iff_eq hprime (by norm_num : (2 : ℕ) ≠ 1)).1
      (dvd_trans (by norm_num : 2 ∣ 4) h4)
  rw [h2'] at h4
  norm_num at h4

theorem false_of_s23_8_of_hinf_prod (D : Data G) (Ch : Choice2011 G) (h8 : S23_8 D Ch)
    (h1930 : H1930 D) (c : Ctx23L D Ch) {n : ℕ} (hn : IsPowTwo n) {A B : Type} [Group A] [Group B]
    (e : Bar2 (Hinf D.M) ≃* A × B) (hA : IsL2 A n ∨ IsU3 A n) (hB : IsL2 B n) : False := by
  classical
  have hBsimp : IsSimpleGroup B :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (t := .PSL) (by decide) hB
  have hAsimp : IsSimpleGroup A := by
    rcases hA with hL | hU
    · exact CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (t := .PSL) (by decide) hL
    · exact CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (t := .PSU) (by decide) hU
  haveI : Nontrivial B := hBsimp.toNontrivial
  haveI : Nontrivial A := hAsimp.toNontrivial
  haveI : Finite (Bar2 (Hinf D.M)) := inferInstance
  haveI : Finite (A × B) :=
    Finite.of_injective e.toEquiv.symm e.toEquiv.symm.injective
  haveI : Finite A := Finite.prod_left B
  haveI : Finite B := Finite.prod_right A
  have hAab : ¬ ∀ x y : A, x * y = y * x := uc22s23pc_not_comm_of_isL2_or_isU3 hA
  have hBab : ¬ ∀ x y : B, x * y = y * x := uc22s23pc_not_comm_of_isL2_or_isU3 (Or.inl hB)
  have hbadm := hB.admissible
  simp only [CFSG.Open.StatedLieAdmissible] at hbadm
  obtain ⟨-, hn1, -, hne2, -⟩ := hbadm
  have hn2 : 2 ≤ n := by
    by_contra hlt
    have hn1' : n = 1 := by omega
    subst hn1'
    exact hne2 (by norm_num)
  have hneven : Even n := by
    obtain ⟨k, rfl⟩ := hn
    have hk : k ≠ 0 := by
      rintro rfl
      norm_num at hn2
    exact Nat.even_pow.mpr ⟨even_two, hk⟩
  obtain ⟨KA, KB, hKAcalC, hKBcalC, ⟨eA⟩, ⟨eB⟩, hne⟩ :=
    exists_two_calC_of_bar2_hinf_prod hAab hBab e
  have h8A := h8 h1930 c KA hKAcalC
  have h8B := h8 h1930 c KB hKBcalC
  by_cases hcaseA : ∃ a : ℕ, Odd a ∧ (IsL2 (Bar2 KA) a ∨ IsSz (Bar2 KA) a)
  · obtain ⟨a, haodd, ha | ha⟩ := hcaseA
    · have ha' : IsL2 A a := CFSG.Blueprint.LieModel.of_mulEquiv eA ha
      have ha1 : 1 ≤ a := ha'.admissible.2.1
      rcases hA with hAn | hUn
      · exact uc22s23pc_false_isL2_isL2 ha' hAn haodd hneven ha1 hn1
      · exact uc22s23pc_false_isL2_isU3 ha' hUn ha1 hn2
    · have ha' : IsSz A a := CFSG.Blueprint.LieModel.of_mulEquiv eA ha
      rcases hA with hAn | hUn
      · exact uc22s23pc_false_isSz_isL2 ha' hAn
      · exact uc22s23pc_false_isSz_isU3 ha' hUn
  · rcases h8A.2 with hAfirst | hAsecond
    · exact hcaseA hAfirst
    · rcases h8B.2 with hBfirst | hBsecond
      · obtain ⟨b, hbodd, hb | hb⟩ := hBfirst
        · have hb' : IsL2 B b := CFSG.Blueprint.LieModel.of_mulEquiv eB hb
          have hb1 : 1 ≤ b := hb'.admissible.2.1
          exact uc22s23pc_false_isL2_isL2 hb' hB hbodd hneven hb1 hn1
        · have hb' : IsSz B b := CFSG.Blueprint.LieModel.of_mulEquiv eB hb
          exact uc22s23pc_false_isSz_isL2 hb' hB
      · exact hne (hAsecond.2.trans hBsecond.2.symm)
