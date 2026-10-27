module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec6Quot
public import CFSG.RankThree.GF2n.Tim79a34BigBarLemmas
public import CFSG.RankThree.GF2n.Tim79a34BigOddCore
public import CFSG.RankThree.PartTwo.Sec14.Ronan148BA6Sylow
public import CFSG.RankThree.GF2n.Stroth80.Sec4Classical
public import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.SectionRank.AmbientRank

public section

namespace CFSG.RankThree.GF2n.Stroth80.Sec108

open CFSG CFSG.Open CFSG.CGT.Timmesfeld75
open scoped commutatorElement

structure LeviStd {𝔊 : Type} [Group 𝔊] (K : Type) [Field K] [Finite K] [CharP K 2]
    (X Yh Nf : Subgroup 𝔊) : Prop where
  four_le_card : 4 ≤ Nat.card K
  mulEquiv : Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin 2) K)
  elemAb : IsElemAbelian 2 Yh
  card_Yh : Nat.card Yh = Nat.card K
  Yh_le_centralizer : Yh ≤ Subgroup.centralizer (X : Set 𝔊)
  X_le : X ≤ Nf
  le_normalizer : Nf ≤ Subgroup.normalizer (X : Set 𝔊)
  centralizer_le : ∀ r ∈ Yh, r ≠ 1 → Subgroup.centralizer ({r} : Set 𝔊) ≤ Nf
  normalizer_le : Subgroup.normalizer (Yh : Set 𝔊) ≤ Nf
  mem_of_pow : ∀ k ∈ Subgroup.centralizer (X : Set 𝔊), ∀ n : ℕ, k ^ 2 ^ n = 1 → k ∈ Yh
  le_of_perfect : ∀ J : Subgroup 𝔊, J ≤ Nf → ⁅J, J⁆ = J → J ≤ X

variable {𝔊 : Type} [Group 𝔊] [Finite 𝔊] {K : Type} [Field K] [Finite K] [CharP K 2]
  {X Yh Nf : Subgroup 𝔊}

abbrev oddBar (H : Subgroup 𝔊) : Subgroup (𝔊 ⧸ standardComponentOddCore 𝔊) :=
  H.map (QuotientGroup.mk' (standardComponentOddCore 𝔊))

theorem LeviStd.isSimpleGroup (hS : LeviStd K X Yh Nf) : IsSimpleGroup X := by
  have h4 : ∃ s : Finset K, s.card = 4 := by
    letI : Fintype K := Fintype.ofFinite K
    have h : 4 ≤ (Finset.univ : Finset K).card := by
      simpa [Nat.card_eq_fintype_card] using hS.four_le_card
    obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq h
    exact ⟨t, ht⟩
  haveI : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) K) :=
    CFSG.ComponentClassification.GMS78.u3_isSimpleGroup_SL2 K h4
  obtain ⟨e⟩ := hS.mulEquiv
  exact e.isSimpleGroup

theorem LeviStd.not_isMulCommutative (hS : LeviStd K X Yh Nf) :
    ¬ IsMulCommutative X := by
  obtain ⟨e⟩ := hS.mulEquiv
  have hnc : ¬ IsMulCommutative (Matrix.SpecialLinearGroup (Fin 2) K) := by
    haveI : Nontrivial (Matrix.SpecialLinearGroup (Fin 2) K) := by
      rw [← Finite.one_lt_card_iff_nontrivial]
      obtain ⟨m, hm⟩ := CFSG.ComponentClassification.GMS78.u3_even_card_SL2 K
      have hpos : 0 < Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) := Nat.card_pos
      omega
    intro hc
    have htop : Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) = ⊤ :=
      Subgroup.center_eq_top_iff.mpr hc
    have hbot : Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) = ⊥ :=
      CFSG.ComponentClassification.GMS78.u3_center_SL2_eq_bot K
    have hbt : (⊥ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)) = ⊤ := by
      rw [← hbot, htop]
    have hsub : Subsingleton (Matrix.SpecialLinearGroup (Fin 2) K) :=
      Subgroup.subsingleton_iff.mp ((subsingleton_iff_bot_eq_top).mp hbt)
    exact (not_subsingleton _) hsub
  intro hc
  exact hnc (e.surjective.isMulCommutative hc)

theorem LeviStd.even_card (hS : LeviStd K X Yh Nf) : Even (Nat.card X) := by
  obtain ⟨e⟩ := hS.mulEquiv
  rw [Nat.card_congr e.toEquiv]
  exact CFSG.ComponentClassification.GMS78.u3_even_card_SL2 K

theorem LeviStd.commutator_eq (hS : LeviStd K X Yh Nf) : ⁅X, X⁆ = X := by
  haveI := hS.isSimpleGroup
  have hcomm : commutator X = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator X) with h | h
    · exfalso
      exact hS.not_isMulCommutative
        (Subgroup.center_eq_top_iff.mp ((commutator_eq_bot_iff_center_eq_top X).mp h))
    · exact h
  rw [← Subgroup.map_subtype_commutator X, hcomm, Subgroup.map_top, X.range_subtype]

private theorem oddCore_inf_eq_bot (hS : LeviStd K X Yh Nf) :
    X ⊓ standardComponentOddCore 𝔊 = ⊥ := by
  have hbot : (standardComponentOddCore 𝔊).subgroupOf X = ⊥ := by
    rcases hS.isSimpleGroup.eq_bot_or_eq_top_of_normal
      ((standardComponentOddCore 𝔊).subgroupOf X) with h | h
    · exact h
    · exfalso
      have hXO : X ≤ standardComponentOddCore 𝔊 := by
        intro x hx
        have hx' : (⟨x, hx⟩ : X) ∈
            (standardComponentOddCore 𝔊).subgroupOf X := h ▸ Subgroup.mem_top _
        exact Subgroup.mem_subgroupOf.mp hx'
      have h2 : 2 ∣ Nat.card X := even_iff_two_dvd.mp hS.even_card
      exact (CFSG.ComponentClassification.GMS78.odd_card_standardComponentOddCore'
        (H := 𝔊)).not_two_dvd_nat (h2.trans (Subgroup.card_dvd_of_le hXO))
  ext x
  constructor
  · intro hx
    have hx' : (⟨x, hx.1⟩ : X) ∈ (standardComponentOddCore 𝔊).subgroupOf X :=
      Subgroup.mem_subgroupOf.mpr hx.2
    rw [hbot, Subgroup.mem_bot] at hx'
    exact Subtype.ext_iff.mp hx'
  · intro hx
    rw [hx]
    exact ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩

private theorem oddCore_le_normalizer (hS : LeviStd K X Yh Nf) :
    standardComponentOddCore 𝔊 ≤ Subgroup.normalizer (X : Set 𝔊) := by
  let O := standardComponentOddCore 𝔊
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA : 2 ^ 2 ≤ Nat.card Yh := by
    rw [show 2 ^ 2 = 4 by norm_num, hS.card_Yh]
    exact hS.four_le_card
  have hodd : ¬ 2 ∣ Nat.card O :=
    (CFSG.ComponentClassification.GMS78.odd_card_standardComponentOddCore'
      (H := 𝔊)).not_two_dvd_nat
  haveI : CFSG.IsElementaryAbelian 2 Yh :=
    { toIsMulCommutative := hS.elemAb.1
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (by
          rw [Subgroup.coe_pow, hS.elemAb.2 x x.2, Subgroup.coe_one]) }
  let _action : MulDistribMulAction Yh O :=
    MulDistribMulAction.compHom O ((MulAut.conjNormal (H := O)).comp Yh.subtype)
  have hgen := CFSG.SolvableHall.coprime_centralizer_generation (p := 2)
    (A := Yh) (H := O) hA hodd
  have hle : (⊤ : Subgroup O) ≤ (Subgroup.normalizer (X : Set 𝔊)).comap O.subtype := by
    rw [← hgen]
    refine iSup₂_le fun a ha => ?_
    intro o ho
    rw [CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff] at ho
    have hfix : (a : 𝔊) * (o : 𝔊) * (a : 𝔊)⁻¹ = (o : 𝔊) := congrArg Subtype.val ho
    have hcomm : (o : 𝔊) * (a : 𝔊) = (a : 𝔊) * (o : 𝔊) :=
      (mul_inv_eq_iff_eq_mul.mp hfix).symm
    have hoC : (o : 𝔊) ∈ Subgroup.centralizer ({(a : 𝔊)} : Set 𝔊) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hcomm.symm
    have ha1 : (a : 𝔊) ≠ 1 := fun h => ha (Subtype.ext h)
    exact hS.le_normalizer (hS.centralizer_le a a.2 ha1 hoC)
  intro o ho
  have hm := hle (Subgroup.mem_top (⟨o, ho⟩ : O))
  exact Subgroup.mem_subgroupOf.mp hm

theorem LeviStd.oddCore_le_centralizer (hS : LeviStd K X Yh Nf) :
    standardComponentOddCore 𝔊 ≤ Subgroup.centralizer (X : Set 𝔊) :=
  CFSG.RankThree.GF2n.Tim79a.le_centralizer_of_odd_card_of_le_normalizer
    hS.isSimpleGroup hS.even_card
    (CFSG.ComponentClassification.GMS78.odd_card_standardComponentOddCore' (H := 𝔊))
    (oddCore_le_normalizer hS)

theorem LeviStd.inf_oddCore (hS : LeviStd K X Yh Nf) :
    X ⊓ standardComponentOddCore 𝔊 = ⊥ := oddCore_inf_eq_bot hS

private theorem oddBar_centralizer_le (hS : LeviStd K X Yh Nf) :
    oddBar (Subgroup.centralizer (X : Set 𝔊)) ≤
      Subgroup.centralizer (oddBar X : Set (𝔊 ⧸ standardComponentOddCore 𝔊)) := by
  intro z hz
  obtain ⟨c, hc, rfl⟩ := hz
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  obtain ⟨x, hx, rfl⟩ := hw
  rw [← map_mul, ← map_mul, (Subgroup.mem_centralizer_iff.mp hc x hx)]

private theorem inv_mul_mem_oddCore_of_mem_centralizer (hS : LeviStd K X Yh Nf)
    {k : 𝔊 ⧸ standardComponentOddCore 𝔊}
    (hk : k ∈ Subgroup.centralizer (oddBar X : Set (𝔊 ⧸ standardComponentOddCore 𝔊)))
    {g : 𝔊} (hg : QuotientGroup.mk' (standardComponentOddCore 𝔊) g = k) {x : X} :
    (x : 𝔊)⁻¹ * g * (x : 𝔊) * g⁻¹ ∈ standardComponentOddCore 𝔊 := by
  have hcomm : QuotientGroup.mk' (standardComponentOddCore 𝔊) (x : 𝔊) * k =
      k * QuotientGroup.mk' (standardComponentOddCore 𝔊) (x : 𝔊) :=
    Subgroup.mem_centralizer_iff.mp hk _ (Subgroup.mem_map_of_mem _ x.2)
  have h1 : QuotientGroup.mk' (standardComponentOddCore 𝔊)
      ((x : 𝔊) * g * (x : 𝔊)⁻¹ * g⁻¹) = 1 := by
    have hc := hcomm
    rw [← hg] at hc
    have h2 : QuotientGroup.mk' (standardComponentOddCore 𝔊) (x : 𝔊) *
        QuotientGroup.mk' (standardComponentOddCore 𝔊) g *
        (QuotientGroup.mk' (standardComponentOddCore 𝔊) (x : 𝔊))⁻¹ *
        (QuotientGroup.mk' (standardComponentOddCore 𝔊) g)⁻¹ = 1 := by
      rw [hc]; group
    simpa [map_mul] using h2
  have hcO : (x : 𝔊) * g * (x : 𝔊)⁻¹ * g⁻¹ ∈ standardComponentOddCore 𝔊 :=
    (QuotientGroup.eq_one_iff _).mp h1
  have hconj := (inferInstance : (standardComponentOddCore 𝔊).Normal).conj_mem _
    ((standardComponentOddCore 𝔊).inv_mem hcO) (x : 𝔊)⁻¹
  simpa [mul_assoc] using hconj

private theorem exists_hom_to_oddCore (hS : LeviStd K X Yh Nf)
    {k : 𝔊 ⧸ standardComponentOddCore 𝔊}
    (hk : k ∈ Subgroup.centralizer (oddBar X : Set (𝔊 ⧸ standardComponentOddCore 𝔊)))
    {g : 𝔊} (hg : QuotientGroup.mk' (standardComponentOddCore 𝔊) g = k) :
    ∃ φ : X →* ↥(standardComponentOddCore 𝔊),
      ∀ x : X, (φ x : 𝔊) = (x : 𝔊)⁻¹ * g * (x : 𝔊) * g⁻¹ := by
  let φ : X →* ↥(standardComponentOddCore 𝔊) :=
    { toFun := fun x => ⟨(x : 𝔊)⁻¹ * g * (x : 𝔊) * g⁻¹,
        inv_mul_mem_oddCore_of_mem_centralizer hS hk hg⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by
        change ((x : 𝔊) * (y : 𝔊))⁻¹ * g * ((x : 𝔊) * (y : 𝔊)) * g⁻¹ =
          ((x : 𝔊)⁻¹ * g * (x : 𝔊) * g⁻¹) *
            ((y : 𝔊)⁻¹ * g * (y : 𝔊) * g⁻¹)
        have hxO : (x : 𝔊)⁻¹ * g * (x : 𝔊) * g⁻¹ ∈ standardComponentOddCore 𝔊 :=
          inv_mul_mem_oddCore_of_mem_centralizer hS hk hg
        have hcy : ((x : 𝔊)⁻¹ * g * (x : 𝔊) * g⁻¹) * (y : 𝔊)⁻¹ =
            (y : 𝔊)⁻¹ * ((x : 𝔊)⁻¹ * g * (x : 𝔊) * g⁻¹) :=
          (Subgroup.mem_centralizer_iff.mp (hS.oddCore_le_centralizer hxO)
            ((y : 𝔊)⁻¹) (X.inv_mem y.2)).symm
        calc
          ((x : 𝔊) * (y : 𝔊))⁻¹ * g * ((x : 𝔊) * (y : 𝔊)) * g⁻¹
              = (y : 𝔊)⁻¹ * (x : 𝔊)⁻¹ * g * (x : 𝔊) * (y : 𝔊) * g⁻¹ := by group
          _ = (y : 𝔊)⁻¹ * ((x : 𝔊)⁻¹ * g * (x : 𝔊) * g⁻¹) *
                  (g * (y : 𝔊) * g⁻¹) := by group
          _ = ((x : 𝔊)⁻¹ * g * (x : 𝔊) * g⁻¹) *
                ((y : 𝔊)⁻¹ * g * (y : 𝔊) * g⁻¹) := by rw [← hcy]; group) }
  exact ⟨φ, fun x => rfl⟩

private theorem mem_centralizer_of_mem_centralizer_oddBar (hS : LeviStd K X Yh Nf)
    {k : 𝔊 ⧸ standardComponentOddCore 𝔊}
    (hk : k ∈ Subgroup.centralizer (oddBar X : Set (𝔊 ⧸ standardComponentOddCore 𝔊)))
    {g : 𝔊} (hg : QuotientGroup.mk' (standardComponentOddCore 𝔊) g = k) :
    g ∈ Subgroup.centralizer (X : Set 𝔊) := by
  obtain ⟨φ, hφ⟩ := exists_hom_to_oddCore hS hk hg
  rcases hS.isSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with hker | hker
  · exfalso
    have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hker
    have hcard : Nat.card X = Nat.card φ.range :=
      Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
    have hdvd : Nat.card φ.range ∣ Nat.card (standardComponentOddCore 𝔊) := by
      have h := Subgroup.card_dvd_of_le (le_top : φ.range ≤
        (⊤ : Subgroup ↥(standardComponentOddCore 𝔊)))
      simpa using h
    have h2 : 2 ∣ Nat.card X := even_iff_two_dvd.mp hS.even_card
    have h2' : 2 ∣ Nat.card φ.range := by rwa [hcard] at h2
    exact (CFSG.ComponentClassification.GMS78.odd_card_standardComponentOddCore'
      (H := 𝔊)).not_two_dvd_nat (h2'.trans hdvd)
  · have htriv : ∀ x : X, φ x = 1 := fun x =>
      MonoidHom.mem_ker.mp (hker ▸ Subgroup.mem_top x)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hx' : (x : 𝔊)⁻¹ * g * (x : 𝔊) * g⁻¹ = 1 := by
      simpa [hφ] using congrArg Subtype.val (htriv ⟨x, hx⟩)
    calc (x : 𝔊) * g = (x : 𝔊) * ((x : 𝔊)⁻¹ * g * (x : 𝔊)) := by
          rw [mul_inv_eq_one.mp hx']
      _ = g * (x : 𝔊) := by group

private theorem centralizer_le_oddBar (hS : LeviStd K X Yh Nf) :
    Subgroup.centralizer (oddBar X : Set (𝔊 ⧸ standardComponentOddCore 𝔊)) ≤
      oddBar (Subgroup.centralizer (X : Set 𝔊)) := by
  intro k hk
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective (standardComponentOddCore 𝔊) k
  exact Subgroup.mem_map.mpr
    ⟨g, mem_centralizer_of_mem_centralizer_oddBar hS hk hg, hg⟩

theorem LeviStd.centralizer_oddBar (hS : LeviStd K X Yh Nf) :
    Subgroup.centralizer (oddBar X : Set (𝔊 ⧸ standardComponentOddCore 𝔊)) =
      oddBar (Subgroup.centralizer (X : Set 𝔊)) :=
  le_antisymm (centralizer_le_oddBar hS) (oddBar_centralizer_le hS)

theorem LeviStd.mem_oddBar_of_pow (hS : LeviStd K X Yh Nf)
    {k : 𝔊 ⧸ standardComponentOddCore 𝔊}
    (hk : k ∈ Subgroup.centralizer (oddBar X : Set (𝔊 ⧸ standardComponentOddCore 𝔊)))
    {n : ℕ} (hkn : k ^ 2 ^ n = 1) : k ∈ oddBar Yh := by
  rw [hS.centralizer_oddBar] at hk
  obtain ⟨g, hgC, hgk⟩ := Subgroup.mem_map.mp hk
  let O := standardComponentOddCore 𝔊
  have hOodd : Odd (Nat.card O) :=
    CFSG.ComponentClassification.GMS78.odd_card_standardComponentOddCore' (H := 𝔊)
  have hoO : g ^ 2 ^ n ∈ O := by
    rw [← QuotientGroup.eq_one_iff (g ^ 2 ^ n)]
    change QuotientGroup.mk' O (g ^ 2 ^ n) = 1
    rw [map_pow, hgk, hkn]
  have hco : Nat.Coprime (Nat.card O) (2 ^ n) :=
    Nat.Prime.coprime_pow_of_not_dvd Nat.prime_two hOodd.not_two_dvd_nat
  obtain ⟨M, hM0, hM1⟩ := Nat.chineseRemainder hco 0 1
  have hOdvd : Nat.card O ∣ M := Nat.modEq_zero_iff_dvd.mp hM0
  have hdvd : orderOf (g ^ 2 ^ n) ∣ M :=
    (Subgroup.orderOf_dvd_natCard O hoO).trans hOdvd
  have hpow : (g ^ M) ^ 2 ^ n = 1 := by
    calc
      (g ^ M) ^ 2 ^ n = g ^ (M * 2 ^ n) := by rw [← pow_mul]
      _ = (g ^ 2 ^ n) ^ M := by rw [mul_comm, ← pow_mul]
      _ = 1 := orderOf_dvd_iff_pow_eq_one.mp hdvd
  have hY : g ^ M ∈ Yh :=
    hS.mem_of_pow (g ^ M) ((Subgroup.centralizer (X : Set 𝔊)).pow_mem hgC M) n hpow
  have hk_eq : QuotientGroup.mk' O (g ^ M) = k := by
    rw [map_pow, hgk, pow_eq_pow_of_modEq hM1 hkn, pow_one]
  rw [← hk_eq]
  exact Subgroup.mem_map.mpr ⟨g ^ M, hY, rfl⟩

private noncomputable def oddBarMulEquivX (hS : LeviStd K X Yh Nf) :
    oddBar X ≃* X := by
  let f : X →* oddBar X :=
    ((QuotientGroup.mk' (standardComponentOddCore 𝔊)).comp X.subtype).codRestrict
      (oddBar X) fun x => Subgroup.mem_map.mpr ⟨(x : 𝔊), x.2, rfl⟩
  have hker : f.ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hxO : (x : 𝔊) ∈ standardComponentOddCore 𝔊 := by
      have hxq : QuotientGroup.mk' (standardComponentOddCore 𝔊) (x : 𝔊) = 1 := by
        simpa [f] using congrArg Subtype.val hx
      exact (QuotientGroup.eq_one_iff (x : 𝔊)).mp hxq
    have hxbot : (x : 𝔊) ∈ X ⊓ standardComponentOddCore 𝔊 := ⟨x.2, hxO⟩
    rw [oddCore_inf_eq_bot hS, Subgroup.mem_bot] at hxbot
    exact Subtype.ext hxbot
  have hinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp hker
  have hsurj : Function.Surjective f := by
    intro z
    obtain ⟨x, hx, hxz⟩ := Subgroup.mem_map.mp z.2
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    simpa [f] using hxz
  exact (MulEquiv.ofBijective f ⟨hinj, hsurj⟩).symm

private theorem oddBar_isSimpleGroup (hS : LeviStd K X Yh Nf) :
    IsSimpleGroup (oddBar X) := by
  haveI := hS.isSimpleGroup
  exact (oddBarMulEquivX hS).isSimpleGroup

private theorem oddBar_not_isMulCommutative (hS : LeviStd K X Yh Nf) :
    ¬ IsMulCommutative (oddBar X) := by
  intro hc
  exact hS.not_isMulCommutative ((oddBarMulEquivX hS).surjective.isMulCommutative hc)

private theorem oddBar_even_card (hS : LeviStd K X Yh Nf) :
    Even (Nat.card (oddBar X)) := by
  rw [Nat.card_congr (oddBarMulEquivX hS).toEquiv]
  exact hS.even_card

private theorem elemAb_oddBar_yHat (hS : LeviStd K X Yh Nf) :
    IsElemAbelian 2 (oddBar Yh) :=
  hS.elemAb.map (QuotientGroup.mk' _)

private theorem card_oddBar_yHat (hS : LeviStd K X Yh Nf) :
    Nat.card (oddBar Yh) = Nat.card K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← hS.card_Yh]
  exact CFSG.RankThree.PartTwo.Sec14.Ronan148B.card_map_mk'_of_isPGroup
    (p := 2) (N := standardComponentOddCore 𝔊)
    (CFSG.ComponentClassification.GMS78.odd_card_standardComponentOddCore'
      (H := 𝔊)).not_two_dvd_nat hS.elemAb.isPGroup

private theorem four_le_card_oddBar_yHat (hS : LeviStd K X Yh Nf) :
    4 ≤ Nat.card (oddBar Yh) := by
  rw [card_oddBar_yHat hS]
  exact hS.four_le_card

private theorem oddBar_yHat_le_centralizer (hS : LeviStd K X Yh Nf) :
    oddBar Yh ≤ Subgroup.centralizer (oddBar X : Set (𝔊 ⧸ standardComponentOddCore 𝔊)) := by
  intro z hz
  obtain ⟨y, hy, rfl⟩ := hz
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  obtain ⟨x, hx, rfl⟩ := hw
  rw [← map_mul, ← map_mul, (Subgroup.mem_centralizer_iff.mp (hS.Yh_le_centralizer hy) x hx)]

private theorem normalizer_le_normalizer_yHat (hS : LeviStd K X Yh Nf) :
    Subgroup.normalizer (X : Set 𝔊) ≤ Subgroup.normalizer (Yh : Set 𝔊) := by
  intro n hn
  have hCn : n ∈ Subgroup.normalizer (Subgroup.centralizer (X : Set 𝔊) : Set 𝔊) :=
    CFSG.RankThree.GF2n.Tim79a.bar_normalizer_le_normalizer_centralizer X hn
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have hmem : n * y * n⁻¹ ∈ Subgroup.centralizer (X : Set 𝔊) :=
      (Subgroup.mem_normalizer_iff.mp hCn y).mp (hS.Yh_le_centralizer hy)
    have h2 : (n * y * n⁻¹) ^ 2 = 1 := by
      rw [conj_pow, hS.elemAb.2 y hy]; simp
    exact hS.mem_of_pow _ hmem 1 (by simpa using h2)
  · intro hy
    have hmem : n⁻¹ * (n * y * n⁻¹) * n ∈ Subgroup.centralizer (X : Set 𝔊) := by
      simpa using (Subgroup.mem_normalizer_iff.mp (inv_mem hCn) (n * y * n⁻¹)).mp
        (hS.Yh_le_centralizer hy)
    have hyC : y ∈ Subgroup.centralizer (X : Set 𝔊) := by
      simpa [mul_assoc] using hmem
    have h2 : (n * y * n⁻¹) ^ 2 = 1 := hS.elemAb.2 _ hy
    have hy2 : y ^ 2 = 1 := by
      have h3 : n * (y ^ 2) * n⁻¹ = 1 := by
        have h4 : (n * y * n⁻¹) * (n * y * n⁻¹) = 1 := by
          simpa [pow_two] using h2
        calc n * (y ^ 2) * n⁻¹ = (n * y * n⁻¹) * (n * y * n⁻¹) := by
              rw [pow_two]; group
          _ = 1 := h4
      have := congrArg (fun z => n⁻¹ * z * n) h3
      simpa [mul_assoc] using this
    exact hS.mem_of_pow y hyC 1 (by simpa using hy2)

private theorem exists_lift_conj_yHat (hS : LeviStd K X Yh Nf)
    {z : 𝔊 ⧸ standardComponentOddCore 𝔊}
    (hne : oddBar Yh ⊓ conjSubgroup z (oddBar Yh) ≠ ⊥) :
    ∃ g : 𝔊, QuotientGroup.mk' (standardComponentOddCore 𝔊) g = z ∧
      ∃ y₂ ∈ Yh, ∃ y ∈ Yh, y ≠ 1 ∧
        QuotientGroup.mk' (standardComponentOddCore 𝔊) (g * y₂ * g⁻¹) =
          QuotientGroup.mk' (standardComponentOddCore 𝔊) y ∧ g * y₂ * g⁻¹ ≠ 1 := by
  obtain ⟨g, hgz⟩ := QuotientGroup.mk'_surjective (standardComponentOddCore 𝔊) z
  subst z
  obtain ⟨t, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have htne : (t : 𝔊 ⧸ standardComponentOddCore 𝔊) ≠ 1 := fun h => ht1 (Subtype.ext h)
  obtain ⟨y, hy, hyz⟩ := Subgroup.mem_map.mp t.2.1
  have htg : (t : 𝔊 ⧸ standardComponentOddCore 𝔊) ∈
      conjSubgroup (QuotientGroup.mk' (standardComponentOddCore 𝔊) g) (oddBar Yh) := t.2.2
  obtain ⟨y₂, hy₂, hy₂eq⟩ := Subgroup.mem_map.mp (mem_conjSubgroup.mp htg)
  have hy1 : y ≠ 1 := by
    intro h
    exact htne (by rw [← hyz, h, map_one])
  have hzmk : QuotientGroup.mk' (standardComponentOddCore 𝔊) (g * y₂ * g⁻¹) =
      QuotientGroup.mk' (standardComponentOddCore 𝔊) y := by
    rw [map_mul, map_mul, map_inv, hy₂eq, hyz]
    group
  have hz1 : g * y₂ * g⁻¹ ≠ 1 := by
    intro h
    have : QuotientGroup.mk' (standardComponentOddCore 𝔊) y = 1 := by
      rw [← hzmk, h, map_one]
    exact htne (by rw [← hyz, this])
  exact ⟨g, rfl, y₂, hy₂, y, hy, hy1, hzmk, hz1⟩

private theorem exists_conj_zpowers_eq (hS : LeviStd K X Yh Nf) {g y y₂ : 𝔊}
    (hy : y ∈ Yh) (hy₂ : y₂ ∈ Yh) (hy1 : y ≠ 1) (hz1 : g * y₂ * g⁻¹ ≠ 1)
    (himg : QuotientGroup.mk' (standardComponentOddCore 𝔊) (g * y₂ * g⁻¹) =
      QuotientGroup.mk' (standardComponentOddCore 𝔊) y) :
    ∃ n ∈ standardComponentOddCore 𝔊,
      Subgroup.zpowers (g * y₂ * g⁻¹) = Subgroup.zpowers (n * y * n⁻¹) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hy2 : y ^ 2 = 1 := hS.elemAb.2 y hy
  have hP₁ : IsPGroup 2 (Subgroup.zpowers y) := by
    have ho : orderOf y = 2 := orderOf_eq_prime hy2 hy1
    exact IsPGroup.of_card (n := 1) (by simp [Nat.card_zpowers, ho])
  have hz2 : (g * y₂ * g⁻¹) ^ 2 = 1 := by
    rw [conj_pow, hS.elemAb.2 y₂ hy₂]; simp
  have hP₂ : IsPGroup 2 (Subgroup.zpowers (g * y₂ * g⁻¹)) := by
    have ho : orderOf (g * y₂ * g⁻¹) = 2 := orderOf_eq_prime hz2 hz1
    exact IsPGroup.of_card (n := 1) (by simp [Nat.card_zpowers, ho])
  have hcard : Nat.card (Subgroup.zpowers (g * y₂ * g⁻¹)) =
      Nat.card (Subgroup.zpowers y) := by
    have h1 : Nat.card (Subgroup.zpowers y) = 2 := by
      simp [Nat.card_zpowers, orderOf_eq_prime hy2 hy1]
    have h2 : Nat.card (Subgroup.zpowers (g * y₂ * g⁻¹)) = 2 := by
      simp [Nat.card_zpowers, orderOf_eq_prime hz2 hz1]
    rw [h1, h2]
  have hmap : (Subgroup.zpowers y).map (QuotientGroup.mk' (standardComponentOddCore 𝔊)) =
      (Subgroup.zpowers (g * y₂ * g⁻¹)).map
        (QuotientGroup.mk' (standardComponentOddCore 𝔊)) := by
    rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers, himg]
  have hNodd : ¬ 2 ∣ Nat.card (standardComponentOddCore 𝔊) :=
    (CFSG.ComponentClassification.GMS78.odd_card_standardComponentOddCore'
      (H := 𝔊)).not_two_dvd_nat
  obtain ⟨n, hn, hconj⟩ := CFSG.RankThree.PartTwo.Sec14.Ronan148B.exists_mem_map_conj_eq_of_map_eq
    (p := 2) (N := standardComponentOddCore 𝔊) hNodd hP₁ hcard hmap
  refine ⟨n, hn, ?_⟩
  simpa [MonoidHom.map_zpowers] using hconj

private theorem exists_conj_eq_of_zpowers_eq (hS : LeviStd K X Yh Nf) {g y y₂ n : 𝔊}
    (hy : y ∈ Yh) (hy1 : y ≠ 1) (hz1 : g * y₂ * g⁻¹ ≠ 1)
    (hn : n ∈ standardComponentOddCore 𝔊)
    (hconj : Subgroup.zpowers (g * y₂ * g⁻¹) = Subgroup.zpowers (n * y * n⁻¹)) :
    ∃ g' : 𝔊, QuotientGroup.mk' (standardComponentOddCore 𝔊) g' =
        QuotientGroup.mk' (standardComponentOddCore 𝔊) g ∧ g' * y₂ * g'⁻¹ = y := by
  have hmem : g * y₂ * g⁻¹ ∈ Subgroup.zpowers (n * y * n⁻¹) := by
    rw [← hconj]; exact Subgroup.mem_zpowers _
  have hy2 : y ^ 2 = 1 := hS.elemAb.2 y hy
  have hx2 : (n * y * n⁻¹) ^ 2 = 1 := by
    rw [show n * y * n⁻¹ = (MulAut.conj n) y by rfl, ← map_pow, hy2, map_one]
  have hnmk : QuotientGroup.mk' (standardComponentOddCore 𝔊) n = 1 :=
    (QuotientGroup.eq_one_iff n).mpr hn
  have hxmk : QuotientGroup.mk' (standardComponentOddCore 𝔊) (n * y * n⁻¹) =
      QuotientGroup.mk' (standardComponentOddCore 𝔊) y := by
    rw [map_mul, map_mul, map_inv, hnmk]; group
  have hymk : QuotientGroup.mk' (standardComponentOddCore 𝔊) y ≠ 1 := by
    intro h
    have hyO : y ∈ standardComponentOddCore 𝔊 := (QuotientGroup.eq_one_iff y).mp h
    exact hy1 (CFSG.RankThree.GF2n.Tim79a.eq_one_of_odd_card_of_sq_eq_one
      (CFSG.ComponentClassification.GMS78.odd_card_standardComponentOddCore' (H := 𝔊))
      hyO hy2)
  have hx1 : n * y * n⁻¹ ≠ 1 := by
    intro h
    exact hymk (by rw [← hxmk, h, map_one])
  have hxord : orderOf (n * y * n⁻¹) = 2 := orderOf_eq_prime hx2 hx1
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hkmod : (n * y * n⁻¹) ^ (k % 2) = g * y₂ * g⁻¹ := by
    rw [← hk]
    simpa [hxord] using zpow_mod_orderOf (n * y * n⁻¹) k
  have heq : g * y₂ * g⁻¹ = n * y * n⁻¹ := by
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · rw [h0, zpow_zero] at hkmod
      exact absurd hkmod.symm hz1
    · rw [h1, zpow_one] at hkmod
      exact hkmod.symm
  refine ⟨n⁻¹ * g, ?_, ?_⟩
  · rw [map_mul, map_inv, hnmk, inv_one, one_mul]
  · calc (n⁻¹ * g) * y₂ * (n⁻¹ * g)⁻¹ = n⁻¹ * (g * y₂ * g⁻¹) * n := by group
      _ = n⁻¹ * (n * y * n⁻¹) * n := by rw [heq]
      _ = y := by group

private theorem exists_conj_yHat_eq_of_inf_ne_bot (hS : LeviStd K X Yh Nf)
    {z : 𝔊 ⧸ standardComponentOddCore 𝔊}
    (hne : oddBar Yh ⊓ conjSubgroup z (oddBar Yh) ≠ ⊥) :
    ∃ g' : 𝔊, QuotientGroup.mk' (standardComponentOddCore 𝔊) g' = z ∧
      ∃ y₂ ∈ Yh, ∃ y ∈ Yh, y ≠ 1 ∧ g' * y₂ * g'⁻¹ = y := by
  obtain ⟨g, hgz, y₂, hy₂, y, hy, hy1, himg, hz1⟩ := exists_lift_conj_yHat hS hne
  obtain ⟨n, hn, hconj⟩ := exists_conj_zpowers_eq hS hy hy₂ hy1 hz1 himg
  obtain ⟨g', hg'g, heq⟩ := exists_conj_eq_of_zpowers_eq hS hy hy1 hz1 hn hconj
  exact ⟨g', hg'g.trans hgz, y₂, hy₂, y, hy, hy1, heq⟩

private theorem mem_normalizer_of_conj_yHat_eq (hS : LeviStd K X Yh Nf)
    {g' y₂ y : 𝔊} (hy₂ : y₂ ∈ Yh) (hy : y ∈ Yh) (hy1 : y ≠ 1)
    (hconj : g' * y₂ * g'⁻¹ = y) :
    g' ∈ Subgroup.normalizer (X : Set 𝔊) := by
  have hXg_le : conjSubgroup g' X ≤ Subgroup.centralizer ({y} : Set 𝔊) := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hw
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    have hcomm : x * y₂ = y₂ * x :=
      Subgroup.mem_centralizer_iff.mp (hS.Yh_le_centralizer hy₂) x hx
    calc y * (g' * x * g'⁻¹) = (g' * y₂ * g'⁻¹) * (g' * x * g'⁻¹) := by
          rw [← hconj]
      _ = g' * (y₂ * x) * g'⁻¹ := by group
      _ = g' * (x * y₂) * g'⁻¹ := by rw [hcomm]
      _ = (g' * x * g'⁻¹) * y := by rw [← hconj]; group
  have hleNf : conjSubgroup g' X ≤ Nf :=
    hXg_le.trans (hS.centralizer_le y hy hy1)
  have hperf : ⁅conjSubgroup g' X, conjSubgroup g' X⁆ = conjSubgroup g' X := by
    rw [show conjSubgroup g' X = X.map (MulAut.conj g').toMonoidHom from rfl,
      ← Subgroup.map_commutator, hS.commutator_eq]
  have hle : conjSubgroup g' X ≤ X := hS.le_of_perfect _ hleNf hperf
  have hcard : Nat.card X ≤ Nat.card (conjSubgroup g' X) := by
    change Nat.card X ≤ Nat.card (X.map (MulAut.conj g').toMonoidHom)
    rw [Subgroup.card_map_of_injective (f := (MulAut.conj g').toMonoidHom)
      (MulAut.conj g').injective]
  have heq : conjSubgroup g' X = X := Subgroup.eq_of_le_of_card_ge hle hcard
  rw [Subgroup.mem_normalizer_iff'']
  intro x
  have h1 : x ∈ conjSubgroup g' X ↔ x ∈ X := by rw [heq]
  calc x ∈ X ↔ x ∈ conjSubgroup g' X := h1.symm
    _ ↔ g'⁻¹ * x * g' ∈ X := mem_conjSubgroup

private theorem normalizer_of_inf_ne_bot (hS : LeviStd K X Yh Nf)
    {z : 𝔊 ⧸ standardComponentOddCore 𝔊}
    (hne : oddBar Yh ⊓ conjSubgroup z (oddBar Yh) ≠ ⊥) :
    z ∈ Subgroup.normalizer (oddBar Yh : Set (𝔊 ⧸ standardComponentOddCore 𝔊)) := by
  obtain ⟨g', hg'z, y₂, hy₂, y, hy, hy1, hconj⟩ := exists_conj_yHat_eq_of_inf_ne_bot hS hne
  have hg'NX : g' ∈ Subgroup.normalizer (X : Set 𝔊) :=
    mem_normalizer_of_conj_yHat_eq hS hy₂ hy hy1 hconj
  have hg'NY : g' ∈ Subgroup.normalizer (Yh : Set 𝔊) :=
    normalizer_le_normalizer_yHat hS hg'NX
  rw [← hg'z]
  exact Subgroup.le_normalizer_map _ (Subgroup.mem_map_of_mem _ hg'NY)

theorem LeviStd.isTI_oddBar (hS : LeviStd K X Yh Nf) : IsTI (oddBar Yh) := by
  intro z
  by_cases hne : oddBar Yh ⊓ conjSubgroup z (oddBar Yh) = ⊥
  · exact Or.inl hne
  · right
    have hz : z ∈ Subgroup.normalizer (oddBar Yh : Set (𝔊 ⧸ standardComponentOddCore 𝔊)) :=
      normalizer_of_inf_ne_bot hS hne
    have hconj : conjSubgroup z (oddBar Yh) = oddBar Yh := by
      ext w
      rw [mem_conjSubgroup]
      exact (Subgroup.mem_normalizer_iff''.mp hz w).symm
    rw [hconj, inf_idem]

private theorem map_conjSubgroup_oddBar (hS : LeviStd K X Yh Nf) (g : 𝔊) :
    (conjSubgroup g Yh).map (QuotientGroup.mk' (standardComponentOddCore 𝔊)) =
      conjSubgroup (QuotientGroup.mk' (standardComponentOddCore 𝔊) g) (oddBar Yh) := by
  ext w
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨y0, hy0, rfl⟩ := Subgroup.mem_map.mp hy
    refine Subgroup.mem_map.mpr ⟨QuotientGroup.mk' (standardComponentOddCore 𝔊) y0,
      Subgroup.mem_map.mpr ⟨y0, hy0, rfl⟩, ?_⟩
    simp [MulAut.conj_apply, map_mul]
  · intro hw
    rw [mem_conjSubgroup] at hw
    obtain ⟨y0, hy0, hyw⟩ := Subgroup.mem_map.mp hw
    refine Subgroup.mem_map.mpr ⟨g * y0 * g⁻¹, ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨y0, hy0, rfl⟩
    · rw [map_mul, map_mul, map_inv, hyw]
      group

private theorem normalizer_oddBar_le (hS : LeviStd K X Yh Nf) :
    Subgroup.normalizer (oddBar X : Set (𝔊 ⧸ standardComponentOddCore 𝔊)) ≤
      Subgroup.normalizer (oddBar Yh : Set (𝔊 ⧸ standardComponentOddCore 𝔊)) := by
  intro z hz
  have hC : z ∈ Subgroup.normalizer
      (Subgroup.centralizer (oddBar X : Set (𝔊 ⧸ standardComponentOddCore 𝔊)) :
        Set (𝔊 ⧸ standardComponentOddCore 𝔊)) :=
    CFSG.RankThree.GF2n.Tim79a.bar_normalizer_le_normalizer_centralizer (oddBar X) hz
  have h2 : ∀ c ∈ Subgroup.centralizer
      (oddBar X : Set (𝔊 ⧸ standardComponentOddCore 𝔊)), c ^ 2 = 1 → c ∈ oddBar Yh :=
    fun c hc hc2 => hS.mem_oddBar_of_pow hc (n := 1) (by simpa using hc2)
  exact CFSG.RankThree.GF2n.Tim79a.bar_normalizer_le (oddBar_yHat_le_centralizer hS)
    (fun b hb => (elemAb_oddBar_yHat hS).2 b hb) h2 hC

private theorem normalizer_oddBar_ge (hS : LeviStd K X Yh Nf) :
    Subgroup.normalizer (oddBar Yh : Set (𝔊 ⧸ standardComponentOddCore 𝔊)) ≤
      Subgroup.normalizer (oddBar X : Set (𝔊 ⧸ standardComponentOddCore 𝔊)) := by
  intro z hz
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (standardComponentOddCore 𝔊) z
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNodd : ¬ 2 ∣ Nat.card (standardComponentOddCore 𝔊) :=
    (CFSG.ComponentClassification.GMS78.odd_card_standardComponentOddCore'
      (H := 𝔊)).not_two_dvd_nat
  have hP₁ : IsPGroup 2 Yh := hS.elemAb.isPGroup
  have hP₂ : IsPGroup 2 (conjSubgroup g Yh) := hP₁.map (MulAut.conj g).toMonoidHom
  have hcard : Nat.card (conjSubgroup g Yh) = Nat.card Yh :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hconjB : conjSubgroup (QuotientGroup.mk' (standardComponentOddCore 𝔊) g)
      (oddBar Yh) = oddBar Yh := by
    ext w
    rw [mem_conjSubgroup]
    exact (Subgroup.mem_normalizer_iff''.mp hz w).symm
  have hmap : (conjSubgroup g Yh).map (QuotientGroup.mk' (standardComponentOddCore 𝔊)) =
      Yh.map (QuotientGroup.mk' (standardComponentOddCore 𝔊)) := by
    rw [map_conjSubgroup_oddBar hS g]
    exact hconjB
  obtain ⟨n, hn, hconj⟩ := CFSG.RankThree.PartTwo.Sec14.Ronan148B.exists_mem_map_conj_eq_of_map_eq
    (p := 2) (N := standardComponentOddCore 𝔊) hNodd hP₁ hcard hmap.symm
  have hc : conjSubgroup (n⁻¹ * g) Yh = Yh := by
    ext y
    rw [mem_conjSubgroup]
    rw [show (n⁻¹ * g)⁻¹ * y * (n⁻¹ * g) = g⁻¹ * (n * y * n⁻¹) * g by group]
    rw [← mem_conjSubgroup, hconj]
    change n * y * n⁻¹ ∈ conjSubgroup n Yh ↔ y ∈ Yh
    rw [mem_conjSubgroup]
    rw [show n⁻¹ * (n * y * n⁻¹) * n = y by group]
  have hg'Y : n⁻¹ * g ∈ Subgroup.normalizer (Yh : Set 𝔊) := by
    rw [Subgroup.mem_normalizer_iff'']
    intro y
    calc y ∈ Yh ↔ y ∈ conjSubgroup (n⁻¹ * g) Yh := by rw [hc]
      _ ↔ (n⁻¹ * g)⁻¹ * y * (n⁻¹ * g) ∈ Yh := mem_conjSubgroup
  have hg'X : n⁻¹ * g ∈ Subgroup.normalizer (X : Set 𝔊) :=
    hS.le_normalizer (hS.normalizer_le hg'Y)
  have hnX : n ∈ Subgroup.normalizer (X : Set 𝔊) := oddCore_le_normalizer hS hn
  have hgX : g ∈ Subgroup.normalizer (X : Set 𝔊) := by
    have hg : g = n * (n⁻¹ * g) := by group
    rw [hg]
    exact (Subgroup.normalizer (X : Set 𝔊)).mul_mem hnX hg'X
  exact Subgroup.le_normalizer_map _ (Subgroup.mem_map_of_mem _ hgX)

theorem LeviStd.normalizer_oddBar (hS : LeviStd K X Yh Nf) :
    Subgroup.normalizer (oddBar X : Set (𝔊 ⧸ standardComponentOddCore 𝔊)) =
      Subgroup.normalizer (oddBar Yh : Set (𝔊 ⧸ standardComponentOddCore 𝔊)) :=
  le_antisymm (normalizer_oddBar_le hS) (normalizer_oddBar_ge hS)

theorem LeviStd.standard (hS : LeviStd K X Yh Nf) : standardComponentIsStandard (oddBar X) := by
  rw [standardComponentIsStandard_eq_fullStandardCore]
  have h2 : ∀ c ∈ Subgroup.centralizer (oddBar X : Set (𝔊 ⧸ standardComponentOddCore 𝔊)),
      c ^ 2 = 1 → c ∈ oddBar Yh :=
    fun c hc hc2 => hS.mem_oddBar_of_pow hc (n := 1) (by simpa using hc2)
  have hNB : Subgroup.normalizer (oddBar Yh : Set (𝔊 ⧸ standardComponentOddCore 𝔊)) ≤
      Subgroup.normalizer
        (Subgroup.centralizer (oddBar X : Set (𝔊 ⧸ standardComponentOddCore 𝔊)) :
          Set (𝔊 ⧸ standardComponentOddCore 𝔊)) := by
    rw [← hS.normalizer_oddBar]
    exact CFSG.RankThree.GF2n.Tim79a.bar_normalizer_le_normalizer_centralizer (oddBar X)
  haveI := oddBar_isSimpleGroup hS
  refine ⟨CFSG.RankThree.GF2n.Tim79a.bar_isQuasisimple
    (oddBar_not_isMulCommutative hS), ?_, ?_, ?_, ?_⟩
  · have hB4 := four_le_card_oddBar_yHat hS
    obtain ⟨k, hk2, hk⟩ := CFSG.RankThree.GF2n.Tim79a.bar_exists_card_pow
      (B := oddBar Yh) (elemAb_oddBar_yHat hS) hB4
    have hevenB : Even (Nat.card (oddBar Yh)) := by
      rw [hk]
      exact even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega))
    have hdvd : Nat.card (oddBar Yh) ∣
        Nat.card (Subgroup.centralizer (oddBar X : Set (𝔊 ⧸ standardComponentOddCore 𝔊))) :=
      Subgroup.card_dvd_of_le (oddBar_yHat_le_centralizer hS)
    exact even_iff_two_dvd.mpr ((even_iff_two_dvd.mp hevenB).trans hdvd)
  · intro g hg
    exact CFSG.RankThree.GF2n.Tim79a.bar_odd_card_inf_conj (hS.isTI_oddBar) h2 hNB hg
  · apply le_antisymm
    · have h := CFSG.RankThree.GF2n.Tim79a.bar_normalizer_le
        (oddBar_yHat_le_centralizer hS) (fun b hb => (elemAb_oddBar_yHat hS).2 b hb) h2
      rwa [← hS.normalizer_oddBar] at h
    · exact CFSG.RankThree.GF2n.Tim79a.bar_normalizer_le_normalizer_centralizer (oddBar X)
  · intro g
    have hCN : Subgroup.centralizer (oddBar X : Set (𝔊 ⧸ standardComponentOddCore 𝔊)) ≤
        Subgroup.normalizer (oddBar Yh : Set (𝔊 ⧸ standardComponentOddCore 𝔊)) :=
      (Subgroup.centralizer_le_normalizer _).trans hS.normalizer_oddBar.le
    exact CFSG.RankThree.GF2n.Tim79a.bar_commutator_ne_bot (oddBar_isSimpleGroup hS)
      (oddBar_not_isMulCommutative hS) (oddBar_even_card hS) (elemAb_oddBar_yHat hS).1 hCN h2 g

private theorem exists_card_pow_two (hS : LeviStd K X Yh Nf) :
    ∃ f : ℕ, 2 ≤ f ∧ Nat.card K = 2 ^ f := by
  letI : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hncard⟩ := FiniteField.card K 2
  refine ⟨(n : ℕ), ?_, ?_⟩
  · have hpos : 0 < (n : ℕ) := n.pos
    by_contra h
    have hn1 : (n : ℕ) = 1 := by omega
    have hK2 : Nat.card K = 2 := by
      rw [Nat.card_eq_fintype_card, hncard, hn1, pow_one]
    have h4 : 4 ≤ 2 := hK2 ▸ hS.four_le_card
    omega
  · rw [Nat.card_eq_fintype_card, hncard]

private theorem oddBar_mulEquiv_statedSp (hS : LeviStd K X Yh Nf) {f : ℕ}
    (hf : Nat.card K = 2 ^ f) (hf0 : f ≠ 0) :
    Nonempty (oddBar X ≃* StatedSp 1 (GaloisField 2 f)) := by
  let eX : oddBar X ≃* X := oddBarMulEquivX hS
  obtain ⟨eSL⟩ := hS.mulEquiv
  letI : Fintype K := Fintype.ofFinite K
  letI : Fintype (GaloisField 2 f) := Fintype.ofFinite _
  have hc : Fintype.card K = Fintype.card (GaloisField 2 f) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hf,
      GaloisField.card 2 f hf0]
  let e : K ≃+* GaloisField 2 f := FiniteField.ringEquivOfCardEq hc
  let s : Matrix.SpecialLinearGroup (Fin 2) K ≃*
      Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f) :=
    MonoidHom.toMulEquiv (Matrix.SpecialLinearGroup.map e.toRingHom)
      (Matrix.SpecialLinearGroup.map e.symm.toRingHom)
      (MonoidHom.ext fun A => Matrix.SpecialLinearGroup.ext _ _ fun i j => by simp)
      (MonoidHom.ext fun A => Matrix.SpecialLinearGroup.ext _ _ fun i j => by simp)
  let eSt : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f) ≃*
      StatedSL 2 (GaloisField 2 f) :=
    CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 (GaloisField 2 f)
  obtain ⟨eSp⟩ := nonempty_statedSp_one_mulEquiv_statedSL_two (GaloisField 2 f)
  let e₁ : oddBar X ≃* Matrix.SpecialLinearGroup (Fin 2) K := MulEquiv.trans eX eSL
  let e₂ : oddBar X ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f) :=
    MulEquiv.trans e₁ s
  let e₃ : oddBar X ≃* StatedSL 2 (GaloisField 2 f) := MulEquiv.trans e₂ eSt
  exact ⟨MulEquiv.trans e₃ eSp.symm⟩

theorem LeviStd.std_hyps (hS : LeviStd K X Yh Nf) :
    ∃ f : ℕ, 2 ≤ f ∧ Nat.card K = 2 ^ f ∧
      Nonempty (oddBar X ≃* StatedSp 1 (GaloisField 2 f)) ∧
      standardComponentOddCore (𝔊 ⧸ standardComponentOddCore 𝔊) = ⊥ ∧
      standardComponentIsStandard (oddBar X) ∧
      2 ≤ pRank 2 (Subgroup.centralizer (oddBar X : Set (𝔊 ⧸ standardComponentOddCore 𝔊))) := by
  obtain ⟨f, hf2, hKf⟩ := exists_card_pow_two hS
  refine ⟨f, hf2, hKf, ?_, ?_, hS.standard, ?_⟩
  · exact oddBar_mulEquiv_statedSp hS hKf (by omega)
  · exact CFSG.ComponentClassification.GMS78.standardComponentOddCore_quot_eq_bot (H := 𝔊)
  · have h := CFSG.RankThree.GF2n.Tim79a.two_le_pRank_centralizer_of_bar
      (oddBar X) (oddBar Yh) (elemAb_oddBar_yHat hS) (four_le_card_oddBar_yHat hS)
      (oddBar_yHat_le_centralizer hS)
    rwa [← CFSG.SectionRank.pRank_coe_eq_openPRank 2
      (Subgroup.centralizer (oddBar X : Set (𝔊 ⧸ standardComponentOddCore 𝔊)))] at h

end CFSG.RankThree.GF2n.Stroth80.Sec108
