module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.Vol2.Ch10SecQ4A14
public import CFSG.Quasithin.Vol2.Ch10SecQ4A23
public import CFSG.Quasithin.Vol2.Ch10SecQ4NQ1

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped commutatorElement

theorem fitting_facts {Y : Type} [Group Y] [Finite Y] {X : Subgroup Y} (h : Vol2Native.A36CoreCat X)
    (hnq : ¬ CFSG.IsQuasisimple ↥X) :
    CFSG.generalizedFitting ↥X = CFSG.fittingSubgroup ↥X ∧
      Odd (Nat.card (CFSG.fittingSubgroup ↥X)) ∧ ¬ 3 ∣ Nat.card (CFSG.fittingSubgroup ↥X) := by
  obtain ⟨hcase, hcommon, -⟩ := h
  have hodd : Odd (Nat.card (CFSG.fittingSubgroup ↥X)) := by
    rw [hcommon.1]
    exact A312.odd_card_oddCore _
  rcases hcase with hc | ⟨p, hp, hp3, hF, ⟨e⟩, -⟩ | ⟨hF, -, -, hprimes⟩
  · exact absurd hc.1 hnq
  · refine ⟨hF, hodd, fun h3 => ?_⟩
    rw [Nat.card_congr (e.toEquiv.trans Multiplicative.toAdd), Nat.card_fun, Nat.card_zmod,
      Nat.card_fin] at h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  · refine ⟨hF, hodd, fun h3 => ?_⟩
    have := (hprimes 3 Nat.prime_three h3).1
    omega

theorem exists_sl2_hom {Y : Type} [Group Y] [Finite Y] {X : Subgroup Y}
    (h : Vol2Native.A36CoreCat X) (hnq : ¬ CFSG.IsQuasisimple ↥X) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ∃ ψ : ↥X →* Matrix.SpecialLinearGroup (Fin 2) (ZMod p),
      Function.Surjective ψ ∧ ψ.ker = CFSG.fittingSubgroup ↥X := by
  obtain ⟨hcase, -, -⟩ := h
  rcases hcase with hc | ⟨p, hp, hp3, -, -, -, ψ, hψs, hψk, -⟩ | ⟨-, -, ⟨e⟩, -⟩
  · exact absurd hc.1 hnq
  · exact ⟨p, hp, by omega, ψ, hψs, hψk⟩
  · refine ⟨5, Nat.prime_five, by norm_num, e.toMonoidHom.comp (QuotientGroup.mk' _),
      e.surjective.comp (QuotientGroup.mk'_surjective _), ?_⟩
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def quotTop (J : Subgroup G) :
    ↥J →* ↥(⊤ : Subgroup (↥J ⧸ CFSG.pCore 2 ↥J)) :=
  (Subgroup.topEquiv.symm : (↥J ⧸ CFSG.pCore 2 ↥J) ≃* ↥(⊤ : Subgroup (↥J ⧸ CFSG.pCore 2 ↥J))
    ).toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥J))

omit [Finite G] in
theorem quotTop_surjective (J : Subgroup G) : Function.Surjective (quotTop J) :=
  (Subgroup.topEquiv.symm.surjective).comp (QuotientGroup.mk'_surjective _)

omit [Finite G] in
theorem quotTop_eq_one_iff (J : Subgroup G) (j : ↥J) :
    quotTop J j = 1 ↔ (j : G) ∈ pCoreOf 2 J := by
  rw [quotTop, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  constructor
  · intro h
    exact ⟨j, h, rfl⟩
  · rintro ⟨y, hy, hyj⟩
    have : y = j := Subtype.ext hyj
    rwa [← this]

omit [Finite G] in
theorem mem_normalizer_of_normal {Y : Type*} [Group Y] {N : Subgroup Y} [N.Normal] (g : Y) :
    g ∈ Subgroup.normalizer (N : Set Y) :=
  (Subgroup.normalizer_eq_top_iff (H := N)).mpr inferInstance ▸ Subgroup.mem_top g

variable {T L I : Subgroup G}

theorem exists_E (h36 : Vol2Native.A36CoreForSQTKCat) (h113 : ASInputs.AS_C_1_13)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I)
    {K : Subgroup G} (hK : Ch10.IsLi T L K) (hKs : IsShort2 K) (hKa : IsAltType K 5)
    {X J : Subgroup G} (hXs : CFSG.SectionRank.IsSQTKCat ↥X)
    (hsyl : IsSylowTwoOf (Ch10.T1 T L) X) (hJ : J ∈ cComp X) (hKJ : K ≤ J)
    (hq : ¬ CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J)) (hUQ : blockU K ≤ pCoreOf 2 J)
    {z : G} (hzK : z ∈ K) (hzC : z ∈ Subgroup.centralizer (K : Set G))
    (hzQ : z ∉ pCoreOf 2 J) (hz2 : z * z = 1) :
    ∃ E : Subgroup ↥(⊤ : Subgroup (↥J ⧸ CFSG.pCore 2 ↥J)),
      E ≠ ⊥ ∧ Odd (Nat.card E) ∧ ¬ 3 ∣ Nat.card E ∧
      ⁅E, Subgroup.zpowers (quotTop J ⟨z, hKJ hzK⟩)⁆ = E ∧
      quotTop J ⟨z, hKJ hzK⟩ ∈ Subgroup.normalizer (E : Set _) ∧
      (∀ k : ↥J, (k : G) ∈ K → quotTop J k ∈ Subgroup.normalizer (E : Set _)) ∧
      ∀ e ∈ E, ∃ c : ↥J, (c : G) ∈ Subgroup.centralizer (conjClosure (blockU K) J : Set G) ∧
        quotTop J c = e := by
  have hJX := le_of_mem_cComp hJ
  have hTK := C10E4.T1_le_normalizer_of_isLi h37 h38 hyp hK
  have hQT : pCoreOf 2 J ≤ Ch10.T1 T L :=
    (EscapingLocal.pCoreOf_le_of_isSylowTwoOf
      (A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp hJ) hsyl)).trans inf_le_left
  have hQK := hQT.trans hTK
  have hTs := C10E4.isSylowTwoOf_sup hsyl (hKJ.trans hJX)
  have hZ := C10E4.blockZ_eq_bot_of_c113 h113 hTs hTK hKs hKa
  have hzW : ∀ w ∈ conjClosure (blockU K) J, z * w = w * z := fun w hw =>
    C10E4.commute_of_mem_center hKs hKJ hQK hUQ hZ hzK hzC hw
  have h36Y := h36 _ (C10E4.sqtkHypCat_quot hJX hXs) ⊤ (C10E4.top_mem_cComp_quot hJ)
  have hnq' : ¬ CFSG.IsQuasisimple ↥(⊤ : Subgroup (↥J ⧸ CFSG.pCore 2 ↥J)) := fun h =>
    hq ((CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr Subgroup.topEquiv).mp h)
  obtain ⟨hF, hFodd, hF3⟩ := fitting_facts h36Y hnq'
  set F := CFSG.fittingSubgroup ↥(⊤ : Subgroup (↥J ⧸ CFSG.pCore 2 ↥J)) with hFdef
  set zb := quotTop J ⟨z, hKJ hzK⟩ with hzb
  have hzb2 : zb * zb = 1 := by
    rw [hzb, ← map_mul]
    have : (⟨z, hKJ hzK⟩ : ↥J) * ⟨z, hKJ hzK⟩ = 1 := Subtype.ext hz2
    rw [this, map_one]
  have hzbN : zb ∈ Subgroup.normalizer (F : Set _) := mem_normalizer_of_normal zb
  have hne : ∃ f ∈ F, ⁅f, zb⁆ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hzc : zb ∈ Subgroup.centralizer
        ((CFSG.generalizedFitting ↥(⊤ : Subgroup (↥J ⧸ CFSG.pCore 2 ↥J))) : Set _) := by
      rw [hF, Subgroup.mem_centralizer_iff]
      intro f hf
      have h1 := hcon f hf
      rw [commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    have hzF := CFSG.centralizer_generalizedFitting_le _ hzc
    rw [hF] at hzF
    have h1 : orderOf zb ∣ Nat.card F := by
      have := orderOf_dvd_natCard (⟨zb, hzF⟩ : ↥F)
      rwa [Subgroup.orderOf_mk] at this
    have h2 : orderOf zb ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq, hzb2])
    have h3 : orderOf zb = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
      · exact h
      · rw [h] at h1
        exact absurd (even_iff_two_dvd.mpr h1) (Nat.not_even_iff_odd.mpr hFodd)
    exact hzQ ((quotTop_eq_one_iff J _).mp (orderOf_eq_one_iff.mp h3))
  set CW : Subgroup ↥J := (Subgroup.centralizer (conjClosure (blockU K) J : Set G)).subgroupOf J
    with hCW
  have hJW := le_normalizer_conjClosure (blockU K) J
  have hCWn : CW.Normal := ⟨fun c hc j => by
    rw [hCW, Subgroup.mem_subgroupOf] at hc ⊢
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro w hw
    have hw' : (j : G)⁻¹ * w * j ∈ conjClosure (blockU K) J := by
      have := (Subgroup.mem_normalizer_iff.mp (hJW (J.inv_mem j.2)) w).mp hw
      simpa using this
    have h1 := hc _ hw'
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc w * (j * c * (j : G)⁻¹) = j * ((j : G)⁻¹ * w * j * c) * (j : G)⁻¹ := by group
      _ = j * (c * ((j : G)⁻¹ * w * j)) * (j : G)⁻¹ := by rw [h1]
      _ = j * c * (j : G)⁻¹ * w := by group⟩
  set Cb := CW.map (quotTop J) with hCb
  have hCbn : Cb.Normal := hCWn.map _ (quotTop_surjective J)
  have hzbC : zb ∈ Cb := ⟨⟨z, hKJ hzK⟩, Subgroup.mem_subgroupOf.mpr
    (Subgroup.mem_centralizer_iff.mpr fun w hw => (hzW w hw).symm), rfl⟩
  have hEC : ⁅F, Subgroup.zpowers zb⁆ ≤ Cb := by
    rw [Subgroup.commutator_le]
    intro f _ y hy
    have hyC : y ∈ Cb := (Subgroup.zpowers_le.mpr hzbC) hy
    rw [commutatorElement_def]
    exact Cb.mul_mem (hCbn.conj_mem y hyC f) (Cb.inv_mem hyC)
  have hEF : ⁅F, Subgroup.zpowers zb⁆ ≤ F := commutator_zpowers_le hzbN
  have hzbz : Subgroup.zpowers zb ≤ Subgroup.normalizer (Subgroup.zpowers zb : Set _) :=
    Subgroup.le_normalizer
  refine ⟨⁅F, Subgroup.zpowers zb⁆, ?_, ?_, ?_, commutator_zpowers_idem hFodd hzb2 hzbN,
    SecA.le_normalizer_commutator (Subgroup.zpowers_le.mpr hzbN) hzbz (Subgroup.mem_zpowers zb),
    fun k hk => ?_, fun e he => ?_⟩
  · obtain ⟨f, hf, hfz⟩ := hne
    intro hb
    apply hfz
    have h1 : ⁅f, zb⁆ ∈ ⁅F, Subgroup.zpowers zb⁆ :=
      Subgroup.commutator_mem_commutator hf (Subgroup.mem_zpowers zb)
    rw [hb] at h1
    exact h1
  · exact hFodd.of_dvd_nat (Subgroup.card_dvd_of_le hEF)
  · exact fun h3 => hF3 (h3.trans (Subgroup.card_dvd_of_le hEF))
  · have hkz : quotTop J k ∈ Subgroup.centralizer (Subgroup.zpowers zb : Set _) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hc : (k : ↥J) * ⟨z, hKJ hzK⟩ = ⟨z, hKJ hzK⟩ * k :=
        Subtype.ext (Subgroup.mem_centralizer_iff.mp hzC (k : G) hk)
      have hc' : Commute (quotTop J k) zb := by
        show quotTop J k * quotTop J ⟨z, hKJ hzK⟩ = quotTop J ⟨z, hKJ hzK⟩ * quotTop J k
        rw [← map_mul, ← map_mul, hc]
      exact (hc'.zpow_right n).eq.symm
    exact SecA.le_normalizer_commutator (Subgroup.zpowers_le.mpr (mem_normalizer_of_normal _))
      (Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ hkz))
      (Subgroup.mem_zpowers _)
  · obtain ⟨c, hc, hce⟩ := Subgroup.mem_map.mp (hEC he)
    exact ⟨c, Subgroup.mem_subgroupOf.mp hc, hce⟩

end CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F
