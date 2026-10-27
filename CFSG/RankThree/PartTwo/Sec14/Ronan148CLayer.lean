module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148CRow
public import CFSG.RankThree.PartTwo.Sec4.RonanK429CfgTools
import CFSG.RankThree.GroupTheory.CentralLineDetection
import CFSG.RankThree.PartTwo.Sec4.T444.Lift

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148C

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4.Ronan148C
open CFSG.RankThree.PartTwo.Sec4.RonanK429 (descAut descAut_eq_one_iff aBar mem_aBar_iff
  descAut_mem_aBar isE27_aBar descAut_comp_inclusion_injective isPGroup_center_of_isComponent)
open CFSG.GH74.GLS (pPrimeCoreOf)
open scoped commutatorElement

variable {M : Type} [Group M] [Finite M]

theorem le_normalizer_component {A Q : Subgroup M}
    (hAJ : ∀ J : Subgroup M, IsComponent J → A ≤ Subgroup.normalizer (J : Set M))
    (hQA : Q = ⁅Q, A⁆) {J : Subgroup M} (hJ : IsComponent J) :
    Q ≤ Subgroup.normalizer (J : Set M) := by
  set K : Subgroup M := ⨅ (K : Subgroup M) (_ : IsComponent K), Subgroup.normalizer (K : Set M)
    with hK
  haveI hKn : K.Normal := CFSG.RankThree.iInf_normalizer_components_normal
  have hAK : A ≤ K := le_iInf₂ fun K hK => hAJ K hK
  have hQK : Q ≤ K := by
    rw [hQA]
    exact (Subgroup.commutator_mono le_rfl hAK).trans (Subgroup.commutator_le_right Q K)
  exact hQK.trans (iInf₂_le J hJ)

theorem three_dvd_card_of_isComponent (hM : CFSG.pPrimeCore 3 M = ⊥) {J : Subgroup M}
    (hJ : IsComponent J) : 3 ∣ Nat.card J := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra h3
  have hle : J ≤ CFSG.pPrimeCore 3 M :=
    CFSG.GH74.GLS.le_pPrimeCore_of_subnormal 3 hJ.2
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3)
  rw [hM, le_bot_iff] at hle
  have : Nontrivial J := CFSG.LocalCores.isQuasisimple_nontrivial hJ.1
  exact (Subgroup.nontrivial_iff_ne_bot J).mp this hle

theorem map_center_le_pCore (hM : CFSG.pPrimeCore 3 M = ⊥) {J : Subgroup M} (hJ : IsComponent J) :
    (Subgroup.center J).map J.subtype ≤ CFSG.pCore 3 M := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hθ : LocalRank.aschbacherSolvableCore 3 M = ⊥ :=
    le_bot_iff.mp (hM ▸ Sec4.aschbacherSolvableCore_le_pPrimeCore)
  have hZ3 : IsPGroup 3 (Subgroup.center J) := isPGroup_center_of_isComponent hθ hJ
  have hZn : ((Subgroup.center J).map J.subtype).subgroupOf J = Subgroup.center J :=
    Subgroup.comap_map_eq_self_of_injective J.subtype_injective _
  have hn : (((Subgroup.center J).map J.subtype).subgroupOf J).Normal := by
    rw [hZn]
    infer_instance
  exact CFSG.Quasithin.S14110.Commute.le_pCore_of_isSubnormal 3 hJ.2 (Subgroup.map_subtype_le _)
    hn (hZ3.map J.subtype)

section Image

variable (J : Subgroup M)

theorem aBar_eq_map {W : Subgroup M} (hW : W ≤ Subgroup.normalizer (J : Set M)) :
    aBar hW = (W.subgroupOf (Subgroup.normalizer (J : Set M))).map (descAut J) := by
  rw [aBar, MonoidHom.range_comp]
  congr 1
  ext x
  constructor
  · rintro ⟨w, rfl⟩
    exact w.2
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

variable {J}

theorem aBar_mono {W₁ W₂ : Subgroup M} (h₁ : W₁ ≤ Subgroup.normalizer (J : Set M))
    (h₂ : W₂ ≤ Subgroup.normalizer (J : Set M)) (h : W₁ ≤ W₂) : aBar h₁ ≤ aBar h₂ := by
  rw [aBar_eq_map, aBar_eq_map]
  exact Subgroup.map_mono (Subgroup.subgroupOf_mono _ h)

theorem commutator_subgroupOf {N Q A : Subgroup M} (hQ : Q ≤ N) (hA : A ≤ N) :
    ⁅Q, A⁆.subgroupOf N = ⁅Q.subgroupOf N, A.subgroupOf N⁆ := by
  apply Subgroup.map_injective N.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hQ, inf_eq_left.mpr hA,
    inf_eq_left.mpr (Subgroup.commutator_le.mpr fun q hq a ha =>
      N.mul_mem (N.mul_mem (N.mul_mem (hQ hq) (hA ha)) (N.inv_mem (hQ hq))) (N.inv_mem (hA ha)))]

theorem aBar_sup {B C : Subgroup M} (hB : B ≤ Subgroup.normalizer (J : Set M))
    (hC : C ≤ Subgroup.normalizer (J : Set M)) (hBC : B ⊔ C ≤ Subgroup.normalizer (J : Set M)) :
    aBar hBC = aBar hB ⊔ aBar hC := by
  apply le_antisymm
  · rw [aBar_eq_map, aBar_eq_map, aBar_eq_map, ← Subgroup.map_sup]
    apply Subgroup.map_mono
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    have hmem : (x : M) ∈ (B.subgroupOf (Subgroup.normalizer (J : Set M)) ⊔
        C.subgroupOf (Subgroup.normalizer (J : Set M))).map
          (Subgroup.normalizer (J : Set M)).subtype := by
      rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
        inf_eq_left.mpr hB, inf_eq_left.mpr hC]
      exact hx
    obtain ⟨y, hy, hyx⟩ := hmem
    rwa [Subtype.ext hyx] at hy
  · exact sup_le (aBar_mono hB hBC le_sup_left) (aBar_mono hC hBC le_sup_right)

theorem le_centralizer_of_aBar_eq_bot (hJ : IsComponent J) {Q : Subgroup M}
    (hQ : Q ≤ Subgroup.normalizer (J : Set M)) (h : aBar hQ = ⊥) :
    Q ≤ Subgroup.centralizer (J : Set M) := by
  intro q hq
  have h1 : descAut J ⟨q, hQ hq⟩ = 1 := by
    have := descAut_mem_aBar hQ hq
    rwa [h, Subgroup.mem_bot] at this
  exact (descAut_eq_one_iff hJ.1.1 _).mp h1

theorem descAut_of_mem {j : M} (hj : j ∈ J) (hjN : j ∈ Subgroup.normalizer (J : Set M)) :
    descAut J ⟨j, hjN⟩ = MulAut.conj ((⟨j, hj⟩ : J) : J ⧸ Subgroup.center J) := by
  have h1 : J.normalizerMonoidHom ⟨j, hjN⟩ = MulAut.conj (⟨j, hj⟩ : J) := by
    ext l
    rfl
  change KFacts.centerDescend J (J.normalizerMonoidHom ⟨j, hjN⟩) = _
  rw [h1, Sec4.Res423Five.centerDescend_conj']

end Image

section Normalizers

variable {G : Type*} [Group G]

theorem mem_normalizer_inf {H K : Subgroup G} {g : G} (hH : g ∈ Subgroup.normalizer (H : Set G))
    (hK : g ∈ Subgroup.normalizer (K : Set G)) : g ∈ Subgroup.normalizer ((H ⊓ K : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hH hK ⊢
  intro y
  simp only [Subgroup.mem_inf]
  exact ⟨fun ⟨h1, h2⟩ => ⟨(hH y).mp h1, (hK y).mp h2⟩, fun ⟨h1, h2⟩ => ⟨(hH y).mpr h1, (hK y).mpr h2⟩⟩

theorem mem_normalizer_centralizer {U : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (U : Set G)) :
    g ∈ Subgroup.normalizer (Subgroup.centralizer (U : Set G) : Set G) := by
  have key : ∀ x : G, x ∈ Subgroup.normalizer (U : Set G) → ∀ y ∈ Subgroup.centralizer (U : Set G),
      x * y * x⁻¹ ∈ Subgroup.centralizer (U : Set G) := by
    intro x hx y hy
    rw [Subgroup.mem_centralizer_iff] at hy ⊢
    intro u hu
    have hu' : x⁻¹ * u * x⁻¹⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx) u).mp hu
    rw [inv_inv] at hu'
    have := hy _ hu'
    calc u * (x * y * x⁻¹) = x * ((x⁻¹ * u * x) * y) * x⁻¹ := by group
      _ = x * (y * (x⁻¹ * u * x)) * x⁻¹ := by rw [this]
      _ = x * y * x⁻¹ * u := by group
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact key g hg y
  · intro h
    have := key g⁻¹ (Subgroup.inv_mem _ hg) _ h
    simpa [mul_assoc] using this

end Normalizers

section Image

variable {J : Subgroup M}

theorem aBar_congr {W₁ W₂ : Subgroup M} (h : W₁ = W₂) (h₁ : W₁ ≤ Subgroup.normalizer (J : Set M))
    (h₂ : W₂ ≤ Subgroup.normalizer (J : Set M)) : aBar h₁ = aBar h₂ := by
  subst h
  rfl

theorem descAut_mem_normalizer_aBar {W : Subgroup M} (hW : W ≤ Subgroup.normalizer (J : Set M))
    {g : M} (hgN : g ∈ Subgroup.normalizer (J : Set M)) (hg : g ∈ Subgroup.normalizer (W : Set M)) :
    descAut J ⟨g, hgN⟩ ∈ Subgroup.normalizer ((aBar hW : Subgroup _) : Set _) := by
  have key : ∀ (x : M) (hxN : x ∈ Subgroup.normalizer (J : Set M)),
      x ∈ Subgroup.normalizer (W : Set M) → ∀ y ∈ aBar hW,
        descAut J ⟨x, hxN⟩ * y * (descAut J ⟨x, hxN⟩)⁻¹ ∈ aBar hW := by
    intro x hxN hx y hy
    obtain ⟨w, hw, rfl⟩ := (mem_aBar_iff hW).mp hy
    refine (mem_aBar_iff hW).mpr ⟨x * w * x⁻¹, (Subgroup.mem_normalizer_iff.mp hx w).mp hw, ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact key g hgN hg y
  · intro h
    have := key g⁻¹ (Subgroup.inv_mem _ hgN) (Subgroup.inv_mem _ hg) _ h
    have he : descAut J ⟨g⁻¹, Subgroup.inv_mem _ hgN⟩ = (descAut J ⟨g, hgN⟩)⁻¹ := by
      rw [← map_inv]
      rfl
    rw [he, inv_inv] at this
    simpa [mul_assoc] using this

end Image

theorem le_centralizer_of_le_centralizer (hM : CFSG.pPrimeCore 3 M = ⊥) {J Q : Subgroup M}
    (hJ : IsComponent J) {b : M} (hJb : J ≤ Subgroup.centralizer ({b} : Set M))
    (hQb : Q ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set M))) :
    Q ≤ Subgroup.centralizer (J : Set M) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C := Subgroup.centralizer ({b} : Set M) with hC
  have hJ' := CFSG.LocalCores.component_overgroup hJ hJb
  rcases CFSG.LocalCores.component_normal_subgroup hJ'
      (CFSG.pPrimeCore_normal (p := 3) (G := C)) with h | h
  · exfalso
    have h3 := three_dvd_card_of_isComponent hM hJ
    have hcop : Nat.Coprime 3 (Nat.card (J.subgroupOf C)) :=
      Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le h) CFSG.pPrimeCore_coprime_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJb).toEquiv] at hcop
    exact absurd (Nat.Coprime.eq_one_of_dvd hcop h3) (by norm_num)
  · intro q hq
    obtain ⟨n, hn, rfl⟩ := hQb hq
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    have hjC : (⟨j, hJb hj⟩ : C) ∈ J.subgroupOf C := Subgroup.mem_subgroupOf.mpr hj
    have hc := Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h hjC) n hn
    have := congrArg Subtype.val hc
    simp only [Subgroup.coe_mul] at this
    exact this.symm

theorem le_centralizer_of_mem_centralizer {A B Q J : Subgroup M} (hJ : IsComponent J)
    (hA : Late.IsE27 A) (hBA : B ≤ A) (hB : Nat.card B = 9)
    (hAN : A ≤ Subgroup.normalizer (J : Set M)) (hQN : Q ≤ Subgroup.normalizer (J : Set M))
    (hQA : Q = ⁅Q, A⁆) (hQB : B ≤ Subgroup.centralizer (Q : Set M)) {a : M} (haA : a ∈ A)
    (haB : a ∉ B) (haJ : a ∈ Subgroup.centralizer (J : Set M)) :
    Q ≤ Subgroup.centralizer (J : Set M) := by
  have hBN : B ≤ Subgroup.normalizer (J : Set M) := hBA.trans hAN
  have hzN : Subgroup.zpowers a ≤ Subgroup.normalizer (J : Set M) :=
    Subgroup.zpowers_le.mpr (hAN haA)
  have hAeq : B ⊔ Subgroup.zpowers a = A := by
    have hle : B ⊔ Subgroup.zpowers a ≤ A := sup_le hBA (Subgroup.zpowers_le.mpr haA)
    have hlt : B < B ⊔ Subgroup.zpowers a := lt_of_le_of_ne le_sup_left fun h =>
      haB (h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers a))
    have h1 : 9 < Nat.card (B ⊔ Subgroup.zpowers a : Subgroup M) :=
      hB ▸ Subgroup.card_lt_of_lt hlt
    have h2 : Nat.card (B ⊔ Subgroup.zpowers a : Subgroup M) ∣ 27 :=
      hA.2 ▸ Subgroup.card_dvd_of_le hle
    have h3 : Nat.card (B ⊔ Subgroup.zpowers a : Subgroup M) = 27 := by
      have h27 : (27 : ℕ).divisors = {1, 3, 9, 27} := by decide
      have hmem := Nat.mem_divisors.mpr ⟨h2, by norm_num⟩
      rw [h27] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      omega
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [h3, hA.2])
  have hz : aBar hzN = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (mem_aBar_iff hzN).mp hy
    rw [Subgroup.mem_bot]
    refine (descAut_eq_one_iff hJ.1.1 _).mpr ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact Subgroup.zpow_mem _ haJ k
  have hρA : aBar hAN = aBar hBN := by
    rw [← aBar_congr hAeq (hAeq ▸ hAN) hAN, aBar_sup hBN hzN, hz, sup_bot_eq]
  have hQbot : aBar hQN = ⊥ := by
    have hcomm : aBar hQN = ⁅aBar hQN, aBar hBN⁆ := by
      calc aBar hQN = (Q.subgroupOf (Subgroup.normalizer (J : Set M))).map (descAut J) :=
            aBar_eq_map J hQN
        _ = (⁅Q, A⁆.subgroupOf (Subgroup.normalizer (J : Set M))).map (descAut J) := by
            rw [← hQA]
        _ = ⁅aBar hQN, aBar hAN⁆ := by
            rw [commutator_subgroupOf hQN hAN, Subgroup.map_commutator, ← aBar_eq_map,
              ← aBar_eq_map]
        _ = ⁅aBar hQN, aBar hBN⁆ := by rw [hρA]
    rw [hcomm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    obtain ⟨q, hq, rfl⟩ := (mem_aBar_iff hQN).mp hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨b, hb, rfl⟩ := (mem_aBar_iff hBN).mp hy
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp (hQB hb) q hq).symm
  exact le_centralizer_of_aBar_eq_bot hJ hQN hQbot

theorem conj_mem_closure_insert {J : Subgroup M} (hJ : IsComponent J) {b : M}
    (hbN : b ∈ Subgroup.normalizer (J : Set M)) {g : M} (hgJ : g ∈ J)
    (hgN : g ∈ Subgroup.normalizer (J : Set M))
    (hgc : descAut J ⟨g, hgN⟩ * descAut J ⟨b, hbN⟩ = descAut J ⟨b, hbN⟩ * descAut J ⟨g, hgN⟩) :
    ∀ u ∈ Subgroup.closure (insert b ((Subgroup.center J).map J.subtype : Set M)),
      g * u * g⁻¹ ∈ Subgroup.closure (insert b ((Subgroup.center J).map J.subtype : Set M)) := by
  set Z : Subgroup M := (Subgroup.center J).map J.subtype with hZ
  set U := Subgroup.closure (insert b (Z : Set M)) with hU
  have hcJ : ⁅g, b⁆ ∈ J := by
    have h1 : b * g⁻¹ * b⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp hbN g⁻¹).mp (J.inv_mem hgJ)
    have : ⁅g, b⁆ = g * (b * g⁻¹ * b⁻¹) := by rw [commutatorElement_def]; group
    rw [this]
    exact J.mul_mem hgJ h1
  have hcN : ⁅g, b⁆ ∈ Subgroup.normalizer (J : Set M) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hgN hbN) (Subgroup.inv_mem _ hgN))
      (Subgroup.inv_mem _ hbN)
  have hcC : ⁅g, b⁆ ∈ Subgroup.centralizer (J : Set M) := by
    refine (descAut_eq_one_iff hJ.1.1 ⟨⁅g, b⁆, hcN⟩).mp ?_
    have he : (⟨⁅g, b⁆, hcN⟩ : Subgroup.normalizer (J : Set M)) =
        ⁅(⟨g, hgN⟩ : Subgroup.normalizer (J : Set M)), ⟨b, hbN⟩⁆ := rfl
    rw [he, map_commutatorElement, commutatorElement_def, hgc]
    group
  have hcZ : ⁅g, b⁆ ∈ Z := by
    refine ⟨⟨⁅g, b⁆, hcJ⟩, Subgroup.mem_center_iff.mpr fun y => Subtype.ext ?_, rfl⟩
    exact Subgroup.mem_centralizer_iff.mp hcC y y.2
  have hle : U ≤ U.comap (MulAut.conj g).toMonoidHom := by
    rw [hU, Subgroup.closure_le]
    intro s hs
    rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rcases hs with hs | hs
    · rw [hs]
      have : g * b * g⁻¹ = ⁅g, b⁆ * b := by rw [commutatorElement_def]; group
      rw [this]
      exact U.mul_mem (Subgroup.subset_closure (Set.mem_insert_of_mem _ hcZ))
        (Subgroup.subset_closure (Set.mem_insert _ _))
    · obtain ⟨z, hz, rfl⟩ := hs
      have h1 := congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨g, hgJ⟩)
      simp only [Subgroup.coe_mul] at h1
      have : g * (z : M) * g⁻¹ = z := by rw [h1]; group
      change g * (z : M) * g⁻¹ ∈ _
      rw [this]
      exact Subgroup.subset_closure (Set.mem_insert_of_mem _ ⟨z, hz, rfl⟩)
  intro u hu
  have := hle hu
  rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this

theorem le_core_aux (hM : CFSG.pPrimeCore 3 M = ⊥) {J Q : Subgroup M} (hJ : IsComponent J)
    (hQN : Q ≤ Subgroup.normalizer (J : Set M)) (hDN : J ⊔ Q ≤ Subgroup.normalizer (J : Set M))
    {b : M} (hbN : b ∈ Subgroup.normalizer (J : Set M))
    (hQb : Q ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set M)))
    (hQO : CFSG.pCore 3 M ≤ Subgroup.centralizer (Q : Set M)) :
    aBar hQN ≤ pPrimeCoreOf 3 (aBar hDN ⊓
      Subgroup.centralizer ({descAut J ⟨b, hbN⟩} : Set (MulAut (J ⧸ Subgroup.center J)))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := Subgroup.normalizer (J : Set M) with hN
  set Z : Subgroup M := (Subgroup.center J).map J.subtype with hZ
  set U := Subgroup.closure (insert b (Z : Set M)) with hU
  set T := pPrimeCoreOf 3 (Subgroup.centralizer (U : Set M)) with hT
  set e := descAut J ⟨b, hbN⟩ with he
  set X := aBar hDN with hX
  set Ce := X ⊓ Subgroup.centralizer ({e} : Set (MulAut (J ⧸ Subgroup.center J))) with hCe
  have hQC : Q ≤ Subgroup.centralizer ({b} : Set M) :=
    hQb.trans (Sec14.pPrimeCoreOf_le 3 _)
  have hZQ : Z ≤ Subgroup.centralizer (Q : Set M) := (map_center_le_pCore hM hJ).trans hQO
  have hQU : Q ≤ Subgroup.centralizer (U : Set M) := by
    rw [Subgroup.le_centralizer_iff, hU, Subgroup.closure_le]
    intro s hs
    rcases hs with hs | hs
    · rw [hs, SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro q hq
      exact Subgroup.mem_centralizer_singleton_iff.mp (hQC hq)
    · exact hZQ hs
  have hQT : Q ≤ T := by
    set N₀ := pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set M)) ⊓
      Subgroup.centralizer (U : Set M) with hN₀
    have hbU : b ∈ U := Subgroup.subset_closure (Set.mem_insert _ _)
    have hCUb : Subgroup.centralizer (U : Set M) ≤ Subgroup.centralizer ({b} : Set M) :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hbU)
    refine (le_inf hQb hQU).trans (Sec14.le_pPrimeCoreOf inf_le_right ?_ ?_)
    · intro x hx
      exact mem_normalizer_inf
        (Sec14.le_normalizer_pPrimeCoreOf 3 _ (hCUb hx)) (Subgroup.le_normalizer hx)
    · exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
        (Sec14.coprime_card_pPrimeCoreOf 3 _)
  have hTN : T ⊓ N ≤ N := inf_le_right
  set P := aBar hTN ⊓ Ce with hP
  have hρq : ∀ q (hq : q ∈ Q), descAut J ⟨q, hQN hq⟩ ∈
      Subgroup.centralizer ({e} : Set (MulAut (J ⧸ Subgroup.center J))) := by
    intro q hq
    rw [Subgroup.mem_centralizer_singleton_iff, he, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp (hQC hq)
  have hRP : aBar hQN ≤ P := by
    refine le_inf (aBar_mono hQN hTN (le_inf hQT hQN)) (le_inf (aBar_mono hQN hDN le_sup_right) ?_)
    intro x hx
    obtain ⟨q, hq, rfl⟩ := (mem_aBar_iff hQN).mp hx
    exact hρq q hq
  have hCeN : Ce ≤ Subgroup.normalizer (P : Set (MulAut (J ⧸ Subgroup.center J))) := by
    intro x hx
    refine mem_normalizer_inf ?_ (Subgroup.le_normalizer hx)
    obtain ⟨d, hd, rfl⟩ := (mem_aBar_iff hDN).mp hx.1
    have hd' : d ∈ ((J ⊔ Q : Subgroup M) : Set M) := hd
    rw [Subgroup.coe_mul_of_right_le_normalizer_left J Q hQN] at hd'
    obtain ⟨j, hj, q, hq, rfl⟩ := hd'
    have hjN : j ∈ N := hDN (Subgroup.mem_sup_left hj)
    have hqN : q ∈ N := hQN hq
    have hρj : descAut J ⟨j, hjN⟩ ∈
        Subgroup.centralizer ({e} : Set (MulAut (J ⧸ Subgroup.center J))) := by
      have h1 : descAut J ⟨j * q, hDN hd⟩ = descAut J ⟨j, hjN⟩ * descAut J ⟨q, hqN⟩ := by
        rw [← map_mul]
        rfl
      have h2 := hx.2
      rw [h1] at h2
      have h3 := Subgroup.mul_mem _ h2 (Subgroup.inv_mem _ (hρq q hq))
      rwa [mul_inv_cancel_right] at h3
    have hjU : j ∈ Subgroup.normalizer (U : Set M) := by
      have hc1 := Subgroup.mem_centralizer_singleton_iff.mp hρj
      have hjiN : j⁻¹ ∈ N := Subgroup.inv_mem _ hjN
      have hc2 : descAut J ⟨j⁻¹, hjiN⟩ * e = e * descAut J ⟨j⁻¹, hjiN⟩ := by
        have hinv : descAut J ⟨j⁻¹, hjiN⟩ = (descAut J ⟨j, hjN⟩)⁻¹ := by
          rw [← map_inv]
          rfl
        rw [hinv]
        calc (descAut J ⟨j, hjN⟩)⁻¹ * e
            = (descAut J ⟨j, hjN⟩)⁻¹ * (e * descAut J ⟨j, hjN⟩) * (descAut J ⟨j, hjN⟩)⁻¹ := by
              group
          _ = (descAut J ⟨j, hjN⟩)⁻¹ * (descAut J ⟨j, hjN⟩ * e) * (descAut J ⟨j, hjN⟩)⁻¹ := by
              rw [← hc1]
          _ = e * (descAut J ⟨j, hjN⟩)⁻¹ := by group
      have k1 := conj_mem_closure_insert hJ hbN hj hjN hc1
      have k2 := conj_mem_closure_insert hJ hbN (J.inv_mem hj) hjiN hc2
      rw [Subgroup.mem_normalizer_iff]
      intro u
      constructor
      · exact k1 u
      · intro h
        have := k2 _ h
        rwa [show j⁻¹ * (j * u * j⁻¹) * j⁻¹⁻¹ = u by group] at this
    have hdT : j * q ∈ Subgroup.normalizer ((T ⊓ N : Subgroup M) : Set M) := by
      refine mem_normalizer_inf ?_ (Subgroup.le_normalizer (hDN hd))
      exact Subgroup.mul_mem _
        (Sec14.normalizer_le_normalizer_pPrimeCoreOf 3 _ (mem_normalizer_centralizer hjU))
        (Subgroup.le_normalizer (hQT hq))
    exact descAut_mem_normalizer_aBar hTN (hDN hd) hdT
  have hPcop : Nat.Coprime 3 (Nat.card P) := by
    refine Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left) ?_
    rw [aBar_eq_map]
    refine Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd _ _) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTN).toEquiv]
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
      (Sec14.coprime_card_pPrimeCoreOf 3 _)
  exact hRP.trans (Sec14.le_pPrimeCoreOf inf_le_right hCeN hPcop)

theorem cfgS148_of_component (hM : CFSG.pPrimeCore 3 M = ⊥) {A B Q J : Subgroup M}
    (hJ : IsComponent J) (hA : Late.IsE27 A) (hBA : B ≤ A) (hB : Nat.card B = 9)
    (hAN : A ≤ Subgroup.normalizer (J : Set M)) (hQN : Q ≤ Subgroup.normalizer (J : Set M))
    (hDN : J ⊔ Q ≤ Subgroup.normalizer (J : Set M))
    (hAC : A ⊓ Subgroup.centralizer (J : Set M) = ⊥)
    (hAQ : A ≤ Subgroup.normalizer (Q : Set M)) (hQA : Q = ⁅Q, A⁆)
    (hQB : ∀ b ∈ B, b ≠ 1 → Q ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set M)))
    (hQO : CFSG.pCore 3 M ≤ Subgroup.centralizer (Q : Set M)) :
    CfgS148 (J ⧸ Subgroup.center J) (aBar hAN) (aBar (hBA.trans hAN)) (aBar hDN) (aBar hQN) where
  isE27 := isE27_aBar hJ.1.1 hAN hAC hA
  le := aBar_mono _ _ hBA
  card := by
    have hBC : B ⊓ Subgroup.centralizer (J : Set M) = ⊥ :=
      le_bot_iff.mp (hAC ▸ inf_le_inf_right _ hBA)
    have hinj := descAut_comp_inclusion_injective hJ.1.1 (hBA.trans hAN) hBC
    rw [← hB]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  inner_le := by
    rintro _ ⟨s, rfl⟩
    obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective s
    refine (mem_aBar_iff hDN).mpr ⟨j, Subgroup.mem_sup_left j.2, ?_⟩
    rw [descAut_of_mem j.2]
  le_core := by
    intro e he he1
    obtain ⟨b, hbB, rfl⟩ := (mem_aBar_iff (hBA.trans hAN)).mp he
    have hb1 : b ≠ 1 := by
      rintro rfl
      exact he1 (by rw [show (⟨1, _⟩ : Subgroup.normalizer (J : Set M)) = 1 from rfl, map_one])
    exact le_core_aux hM hJ hQN hDN _ (hQB b hbB hb1) hQO
  le_normalizer := by
    intro f hf
    obtain ⟨a, ha, rfl⟩ := (mem_aBar_iff hAN).mp hf
    exact descAut_mem_normalizer_aBar hQN (hAN ha) (hAQ ha)
  eq_commutator := by
    calc aBar hQN = (Q.subgroupOf (Subgroup.normalizer (J : Set M))).map (descAut J) :=
          aBar_eq_map J hQN
      _ = (⁅Q, A⁆.subgroupOf (Subgroup.normalizer (J : Set M))).map (descAut J) := by
          rw [← hQA]
      _ = ⁅aBar hQN, aBar hAN⁆ := by
          rw [commutator_subgroupOf hQN hAN, Subgroup.map_commutator, ← aBar_eq_map,
            ← aBar_eq_map]

theorem layer_le_centralizer_of_rows (hM : CFSG.pPrimeCore 3 M = ⊥) {A B Q : Subgroup M}
    (hA : Late.IsE27 A) (hBA : B ≤ A) (hB : Nat.card B = 9)
    (hAQ : A ≤ Subgroup.normalizer (Q : Set M)) (hQA : Q = ⁅Q, A⁆)
    (hQB : ∀ b ∈ B, b ≠ 1 → Q ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set M)))
    (hQO : CFSG.pCore 3 M ≤ Subgroup.centralizer (Q : Set M))
    (hAJ : ∀ J : Subgroup M, IsComponent J → A ≤ Subgroup.normalizer (J : Set M))
    (hrow : ∀ J : Subgroup M, IsComponent J → RowS148 (J ⧸ Subgroup.center J)) :
    CFSG.layer M ≤ Subgroup.centralizer (Q : Set M) := by
  rw [← Subgroup.le_centralizer_iff, CFSG.RankThree.le_centralizer_layer_iff]
  intro J hJ
  have hQN := le_normalizer_component hAJ hQA hJ
  have hAN := hAJ J hJ
  have hQCB : B ≤ Subgroup.centralizer (Q : Set M) := by
    intro b hb
    by_cases hb1 : b = 1
    · rw [hb1]
      exact Subgroup.one_mem _
    · rw [Subgroup.mem_centralizer_iff]
      intro q hq
      exact Subgroup.mem_centralizer_singleton_iff.mp
        ((hQB b hb hb1).trans (Sec14.pPrimeCoreOf_le 3 _) hq)
  by_cases hAC : A ⊓ Subgroup.centralizer (J : Set M) = ⊥
  ·
    have hDN : J ⊔ Q ≤ Subgroup.normalizer (J : Set M) := sup_le Subgroup.le_normalizer hQN
    have hR := hrow J hJ _ _ _ _
      (cfgS148_of_component hM hJ hA hBA hB hAN hQN hDN hAC hAQ hQA hQB hQO)
    exact le_centralizer_of_aBar_eq_bot hJ hQN hR
  ·
    obtain ⟨a, ⟨haA, haJ⟩, ha1⟩ : ∃ a, a ∈ A ⊓ Subgroup.centralizer (J : Set M) ∧ a ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact hAC ((Subgroup.eq_bot_iff_forall _).mpr hcon)
    by_cases haB : a ∈ B
    · refine le_centralizer_of_le_centralizer hM hJ (b := a) ?_ (hQB a haB ha1)
      intro j hj
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp haJ j hj
    · exact le_centralizer_of_mem_centralizer hJ hA hBA hB hAN hQN hQA hQCB haA haB haJ

end CFSG.RankThree.PartTwo.Sec14.Ronan148C
