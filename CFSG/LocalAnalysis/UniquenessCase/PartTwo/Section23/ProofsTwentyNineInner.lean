module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsThirtySevenBTwo
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20i
public import CFSG.Quasithin.H13.NQCoreWholeModuleFrattini
public import CFSG.GroupTheory.WielandtProductSetup
public import CFSG.LocalAnalysis.WeakClosure81.SLTwoNormalizer
public import CFSG.Quasithin.Vol2.Ch6Semilinear
public import CFSG.LinearAlgebra.SL2CharTwoScalar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.SigmaCentZ
public import CFSG.LocalAnalysis.UniquenessCase.UC22R847FieldsCZ

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup Matrix
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Ctx23L

private theorem mul_conj_mem_sup_zpowers_pCoreOf {L : Subgroup G} {a : G}
    (haN : a ∈ Subgroup.normalizer (L : Set G)) (hInd : InducedBar L a 1) {l : G}
    (hl : l ∈ L) :
    l * a * l⁻¹ ∈ Subgroup.zpowers a ⊔ CFSG.Open.pCoreOf 2 L := by
  have hconj : a⁻¹ * l * a ∈ L := by
    simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ haN) l).mp hl
  have hconv : a * (a⁻¹ * l * a) * a⁻¹ = l := by group
  have hmk : QuotientGroup.mk (s := CFSG.pCore 2 ↥L) (⟨a⁻¹ * l * a, hconj⟩ : ↥L) =
      QuotientGroup.mk (s := CFSG.pCore 2 ↥L) (⟨l, hl⟩ : ↥L) := by
    have := hInd ⟨a⁻¹ * l * a, hconj⟩ ⟨l, hl⟩ hconv.symm
    simpa using this
  have hmem : (⟨a⁻¹ * l * a, hconj⟩ : ↥L)⁻¹ * ⟨l, hl⟩ ∈ CFSG.pCore 2 ↥L :=
    QuotientGroup.eq.mp hmk
  have hG : L.subtype ((⟨a⁻¹ * l * a, hconj⟩ : ↥L)⁻¹ * ⟨l, hl⟩) ∈
      CFSG.Open.pCoreOf 2 L := by
    change L.subtype ((⟨a⁻¹ * l * a, hconj⟩ : ↥L)⁻¹ * ⟨l, hl⟩) ∈
      (CFSG.pCore 2 ↥L).map L.subtype
    exact Subgroup.mem_map.mpr ⟨_, hmem, rfl⟩
  have hG' : (a⁻¹ * l * a)⁻¹ * l ∈ CFSG.Open.pCoreOf 2 L := by
    simpa using hG
  have hlc : l * ((a⁻¹ * l * a)⁻¹ * l) * l⁻¹ ∈ CFSG.Open.pCoreOf 2 L :=
    (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L hl) _).mp hG'
  have hinv : ((a⁻¹ * l * a) * l⁻¹) ∈ CFSG.Open.pCoreOf 2 L := by
    have heq : ((a⁻¹ * l * a) * l⁻¹) = (l * ((a⁻¹ * l * a)⁻¹ * l) * l⁻¹)⁻¹ := by
      group
    rw [heq]
    exact (CFSG.Open.pCoreOf 2 L).inv_mem hlc
  have hdecomp : l * a * l⁻¹ = a * ((a⁻¹ * l * a) * l⁻¹) := by group
  rw [hdecomp]
  exact Subgroup.mul_mem_sup (Subgroup.mem_zpowers a) hinv

private theorem le_normalizer_sup_zpowers_pCoreOf {L : Subgroup G} {a : G}
    (haN : a ∈ Subgroup.normalizer (L : Set G)) (hInd : InducedBar L a 1) :
    L ≤ Subgroup.normalizer
      ((Subgroup.zpowers a ⊔ CFSG.Open.pCoreOf 2 L : Subgroup G) : Set G) := by
  have hla : ∀ l ∈ L, l * a * l⁻¹ ∈ Subgroup.zpowers a ⊔ CFSG.Open.pCoreOf 2 L :=
    fun l hl => mul_conj_mem_sup_zpowers_pCoreOf haN hInd hl
  have hstep : ∀ m ∈ L, ∀ x ∈ Subgroup.zpowers a ⊔ CFSG.Open.pCoreOf 2 L,
      m * x * m⁻¹ ∈ Subgroup.zpowers a ⊔ CFSG.Open.pCoreOf 2 L := by
    intro m hm x hx
    have hPY : (Subgroup.zpowers a).map (MulAut.conj m).toMonoidHom ≤
        Subgroup.zpowers a ⊔ CFSG.Open.pCoreOf 2 L := by
      rintro y ⟨p, hp, rfl⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
      have hpow : (MulAut.conj m) (a ^ k) = ((MulAut.conj m) a) ^ k := map_zpow _ _ _
      change (MulAut.conj m) (a ^ k) ∈ Subgroup.zpowers a ⊔ CFSG.Open.pCoreOf 2 L
      rw [hpow]
      exact Subgroup.zpow_mem (Subgroup.zpowers a ⊔ CFSG.Open.pCoreOf 2 L) (hla m hm) k
    have hOY : (CFSG.Open.pCoreOf 2 L).map (MulAut.conj m).toMonoidHom ≤
        Subgroup.zpowers a ⊔ CFSG.Open.pCoreOf 2 L := by
      rintro y ⟨o, ho, rfl⟩
      exact Subgroup.mem_sup_right
        ((Subgroup.mem_normalizer_iff.mp
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L hm) o).mp ho)
    have hmap_le : (Subgroup.zpowers a ⊔ CFSG.Open.pCoreOf 2 L).map
        (MulAut.conj m).toMonoidHom ≤ Subgroup.zpowers a ⊔ CFSG.Open.pCoreOf 2 L := by
      rw [Subgroup.map_sup]
      exact sup_le hPY hOY
    exact hmap_le (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
  intro l hl
  rw [Subgroup.mem_normalizer_iff]
  intro x
  exact ⟨fun hx => hstep l hl x hx, fun hx => by
    have h2 := hstep l⁻¹ (L.inv_mem hl) (l * x * l⁻¹) hx
    have heq : l⁻¹ * (l * x * l⁻¹) * l⁻¹⁻¹ = x := by group
    rwa [heq] at h2⟩

private theorem isSylowOf_zpowers_sup_pCoreOf {L : Subgroup G} {a : G}
    (haN : a ∈ Subgroup.normalizer (L : Set G)) (hInd : InducedBar L a 1)
    (hprime : (orderOf a).Prime) (hodd : Odd (orderOf a)) (h2 : orderOf a ≠ 2) :
    CFSG.ABGLocalTools.IsSylowOf (orderOf a) (Subgroup.zpowers a)
        (Subgroup.zpowers a ⊔ CFSG.Open.pCoreOf 2 L) ∧
      L ≤ Subgroup.normalizer
        ((Subgroup.zpowers a ⊔ CFSG.Open.pCoreOf 2 L : Subgroup G) : Set G) := by
  classical
  let P : Subgroup G := Subgroup.zpowers a
  let O : Subgroup G := CFSG.Open.pCoreOf 2 L
  let Y : Subgroup G := P ⊔ O
  have hPN : P ≤ Subgroup.normalizer (O : Set G) :=
    Subgroup.zpowers_le.mpr
      ((CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L) haN)
  obtain ⟨m, hm⟩ := (uc22main1_isPGroup_pCoreOf L).exists_card_eq
  have hcardP : Nat.card P = orderOf a := Nat.card_zpowers a
  have hcardO : Nat.card O = 2 ^ m := hm
  have hcop : Nat.Coprime (Nat.card P) (Nat.card O) := by
    rw [hcardP, hcardO]
    exact ((Nat.coprime_two_left.mpr hodd).symm).pow_right m
  have hdisj : Disjoint P O := Subgroup.disjoint_of_coprime_natCard hcop
  have hcardY : Nat.card Y = Nat.card P * Nat.card O := by
    have h := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      O P hPN hdisj.symm
    rw [show Y = O ⊔ P by simp [Y, sup_comm], h, Nat.mul_comm]
  have hnotdvd : ¬ orderOf a ∣ 2 ^ m := by
    intro hd
    have hd2 : orderOf a ∣ 2 := hprime.dvd_of_dvd_pow hd
    rcases (Nat.dvd_prime Nat.prime_two).mp hd2 with h1' | h2'
    · exact hprime.ne_one h1'
    · exact h2 h2'
  have hfactor : (Nat.card Y).factorization (orderOf a) = 1 := by
    rw [hcardY, hcardP, hcardO,
      Nat.factorization_mul hprime.ne_zero (pow_ne_zero m two_ne_zero),
      Finsupp.add_apply, hprime.factorization_self,
      Nat.factorization_eq_zero_of_not_dvd hnotdvd, add_zero]
  haveI : Fact (orderOf a).Prime := ⟨hprime⟩
  have hSyl : CFSG.ABGLocalTools.IsSylowOf (orderOf a) P Y := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card le_sup_left ?_
    rw [hcardP, hfactor, pow_one]
  refine ⟨by simpa [P, Y], ?_⟩
  simpa [P, O, Y] using le_normalizer_sup_zpowers_pCoreOf haN hInd

theorem eq_one_of_inducedBar_one {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (h1930 : H1930 D) (h4 : S23_4 D Ch) (h847 : R847ThinCZ D)
    {K : Subgroup G} (hK : K ∈ calC D.M) (hthin : F08.Thin8 K) {a : G} (haK : a ∈ K)
    (hodd : Odd (orderOf a)) (haN : a ∈ Subgroup.normalizer (c.L : Set G))
    (h1 : InducedBar c.L a 1) : a = 1 := by
  classical
  by_contra ha1
  obtain ⟨k, hkprime⟩ := CFSG.GroupTheory.WielandtProduct.exists_pow_prime_orderOf ha1
  set a₀ : G := a ^ k with ha₀
  have ha₀K : a₀ ∈ K := K.pow_mem haK k
  have ha₀N : a₀ ∈ Subgroup.normalizer (c.L : Set G) :=
    (Subgroup.normalizer (c.L : Set G)).pow_mem haN k
  have hodd₀ : Odd (orderOf a₀) := hodd.of_dvd_nat (orderOf_pow_dvd k)
  have hInd₀ : InducedBar c.L a₀ 1 := by
    have h := inducedBar_pow haN h1 k
    simpa [ha₀] using h
  have hr2 : orderOf a₀ ≠ 2 := by
    intro h2
    have ho2 : Odd (2 : ℕ) := h2 ▸ hodd₀
    obtain ⟨m, hm⟩ := ho2
    omega
  let P : Subgroup G := Subgroup.zpowers a₀
  let Y : Subgroup G := Subgroup.zpowers a₀ ⊔ CFSG.Open.pCoreOf 2 c.L
  haveI : Fact (orderOf a₀).Prime := ⟨hkprime⟩
  obtain ⟨hSyl, hLY⟩ := isSylowOf_zpowers_sup_pCoreOf ha₀N hInd₀ hkprime hodd₀ hr2
  have hPleM : P ≤ D.M :=
    (Subgroup.zpowers_le.mpr ha₀K).trans (CFSG.Open.IsSubnormal.le hK.1)
  have hYleM : Y ≤ D.M :=
    sup_le hPleM ((Ctx23L.pCoreOf_L_le_T D Ch c).trans D.sylowM.le)
  have hLle : c.L ≤ Y ⊔ Subgroup.normalizer (P : Set G) := by
    intro l hl
    obtain ⟨n, hn, q, hq, hln⟩ :=
      CFSG.Quasithin.H13.NQCore.exists_mul_of_isSylowOf' hSyl (hLY hl)
    rw [hln]
    exact Subgroup.mul_mem_sup hn hq
  have hNleM : Subgroup.normalizer (P : Set G) ≤ D.M :=
    Ctx23L.normalizer_zpowers_le_M_of_r847ThinCZ c h1930 h4 h847 hK hthin ha₀K
      hkprime hr2 rfl
  exact uc22p20i_not_le_M D c.hL.1 (hLle.trans (sup_le hYleM hNleM))

private theorem le_normalizer_of_normal_subgroupOf {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (hLN : (c.L.subgroupOf c.N).Normal) :
    c.N ≤ Subgroup.normalizer (c.L : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer
    (le_sup_left.trans (Ctx23L.sup_le_N D Ch c))).mp hLN

private theorem mem_pCore_of_mem_inf_centralizer_V {D : Data G} {Ch : Choice2011 G}
    (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch)
    {x : ↥c.L} (hx : (x : G) ∈ c.L ⊓ Subgroup.centralizer (c.V : Set G)) :
    x ∈ CFSG.pCore 2 ↥c.L := by
  have hG : (x : G) ∈ CFSG.Open.pCoreOf 2 c.L :=
    (Ctx23L.inf_centralizer_V_le_pCoreOf_L D Ch h4 h23 h1930 c) hx
  obtain ⟨q, hq, hqval⟩ := Subgroup.mem_map.mp
    (show (x : G) ∈ (CFSG.pCore 2 ↥c.L).map c.L.subtype from hG)
  have hqk : q = x := Subtype.ext hqval
  rwa [← hqk]

private theorem conj_mul_conj_inf_centralizer {L V : Subgroup G} {a l : G}
    (haNL : a ∈ Subgroup.normalizer (L : Set G))
    (haC : a ∈ Subgroup.centralizer (V : Set G))
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hl : l ∈ L) :
    a * l * a⁻¹ * l⁻¹ ∈ L ⊓ Subgroup.centralizer (V : Set G) := by
  have halL : a * l * a⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.mp haNL l).mp hl
  refine Subgroup.mem_inf.mpr ⟨L.mul_mem halL (L.inv_mem hl), ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hvl : l⁻¹ * v * l ∈ V := by
    have hnorm := hLV (Subgroup.inv_mem _ hl)
    simpa using (Subgroup.mem_normalizer_iff.mp hnorm v).mp hv
  have hcw : (l⁻¹ * v * l) * a = a * (l⁻¹ * v * l) :=
    Subgroup.mem_centralizer_iff.mp haC _ hvl
  have hinv : a⁻¹ * (l⁻¹ * v * l) * a = l⁻¹ * v * l := by
    calc a⁻¹ * (l⁻¹ * v * l) * a = a⁻¹ * ((l⁻¹ * v * l) * a) := by group
      _ = a⁻¹ * (a * (l⁻¹ * v * l)) := by rw [hcw]
      _ = l⁻¹ * v * l := by group
  have hmain : (a * l * a⁻¹ * l⁻¹) * v * (a * l * a⁻¹ * l⁻¹)⁻¹ = v := by
    calc (a * l * a⁻¹ * l⁻¹) * v * (a * l * a⁻¹ * l⁻¹)⁻¹
        = a * l * (a⁻¹ * (l⁻¹ * v * l) * a) * l⁻¹ * a⁻¹ := by group
      _ = a * l * (l⁻¹ * v * l) * l⁻¹ * a⁻¹ := by rw [hinv]
      _ = a * v * a⁻¹ := by group
      _ = v := by
        have hv' : v * a = a * v := Subgroup.mem_centralizer_iff.mp haC v hv
        calc a * v * a⁻¹ = (a * v) * a⁻¹ := by group
          _ = (v * a) * a⁻¹ := by rw [← hv']
          _ = v := by group
  calc v * (a * l * a⁻¹ * l⁻¹)
      = ((a * l * a⁻¹ * l⁻¹) * v * (a * l * a⁻¹ * l⁻¹)⁻¹) *
          (a * l * a⁻¹ * l⁻¹) := by rw [hmain]
    _ = (a * l * a⁻¹ * l⁻¹) * v := by group

private theorem inducedBar_one_of_mem_centralizer_V {L V : Subgroup G} {a : G}
    (haNL : a ∈ Subgroup.normalizer (L : Set G))
    (haC : a ∈ Subgroup.centralizer (V : Set G))
    (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hker : L ⊓ Subgroup.centralizer (V : Set G) ≤ CFSG.Open.pCoreOf 2 L) :
    InducedBar L a 1 := by
  intro l l' hll'
  show QuotientGroup.mk l = QuotientGroup.mk l'
  have hl' : l' = ⟨a * (l : G) * a⁻¹,
      (Subgroup.mem_normalizer_iff.mp haNL (l : G)).mp l.2⟩ := Subtype.ext hll'
  rw [hl', QuotientGroup.eq]
  have hmem : a * (l : G) * a⁻¹ * (l : G)⁻¹ ∈ CFSG.Open.pCoreOf 2 L :=
    hker (conj_mul_conj_inf_centralizer haNL haC hLV l.2)
  let u : ↥L := ⟨a * (l : G) * a⁻¹,
    (Subgroup.mem_normalizer_iff.mp haNL (l : G)).mp l.2⟩
  have hconj : (l : G)⁻¹ * ((u : G) * (l : G)⁻¹) * (l : G) ∈ CFSG.Open.pCoreOf 2 L := by
    have h := (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L (L.inv_mem l.2)) _).mp
      (show (u : G) * (l : G)⁻¹ ∈ CFSG.Open.pCoreOf 2 L from hmem)
    simpa using h
  have hkG : ((⟨l, l.2⟩⁻¹ * u : ↥L) : G) ∈ (CFSG.pCore 2 ↥L).map L.subtype := by
    have heq : ((⟨l, l.2⟩⁻¹ * u : ↥L) : G) =
        (l : G)⁻¹ * ((u : G) * (l : G)⁻¹) * (l : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [heq]
    exact hconj
  obtain ⟨q, hq, hqval⟩ := Subgroup.mem_map.mp hkG
  have hqk : q = ⟨l, l.2⟩⁻¹ * u := Subtype.ext hqval
  rw [← hqk]
  exact hq

theorem not_mem_centralizer_V {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (h1930 : H1930 D) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h847 : R847ThinCZ D)
    (hLN : (c.L.subgroupOf c.N).Normal) {K : Subgroup G}
    (hK : K ∈ calC D.M) (hthin : F08.Thin8 K) {a : G} (haK : a ∈ K) (ha1 : a ≠ 1)
    (hodd : Odd (orderOf a)) :
    a ∉ Subgroup.centralizer (c.V : Set G) := by
  intro haC
  have haN : a ∈ c.N := Ctx23L.centralizer_V_le_N c h4 h1930 haC
  have haNL : a ∈ Subgroup.normalizer (c.L : Set G) :=
    (le_normalizer_of_normal_subgroupOf c hLN) haN
  have hInd : InducedBar c.L a 1 :=
    inducedBar_one_of_mem_centralizer_V haNL haC
      (le_sup_left.trans (Ctx23L.sup_le_normalizer_V D Ch c))
      (Ctx23L.inf_centralizer_V_le_pCoreOf_L D Ch h4 h23 h1930 c)
  exact ha1 (Ctx23L.eq_one_of_inducedBar_one c h1930 h4 h847 hK hthin haK hodd haNL hInd)

namespace B2Data

variable {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}

@[expose] noncomputable def conjVEquiv (a : G) (ha : a ∈ c.N) : ↥c.V ≃* ↥c.V where
  toFun v := CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjV
    (uc22p22v_le_normalizer_conjClosure c.N D.Z) ⟨a, ha⟩ v
  invFun v := CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjV
    (uc22p22v_le_normalizer_conjClosure c.N D.Z) ⟨a⁻¹, c.N.inv_mem ha⟩ v
  left_inv v := Subtype.ext (by
    simp only [CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjV]
    group)
  right_inv v := Subtype.ext (by
    simp only [CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjV]
    group)
  map_mul' v w := Subtype.ext (by
    simp only [CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjV, Subgroup.coe_mul]
    group)

variable (X : B2Data D Ch c)

@[expose] noncomputable def betaMulEquiv : ↥c.V ≃* Multiplicative (Fin 2 → X.κ.K) :=
  MulEquiv.ofBijective X.κ.β X.κ.β_bij

noncomputable def phiMulAut (a : G) (ha : a ∈ c.N) :
    MulAut (Multiplicative (Fin 2 → X.κ.K)) :=
  (betaMulEquiv X).symm.trans ((conjVEquiv a ha).trans (betaMulEquiv X))

noncomputable def phiAdd (a : G) (ha : a ∈ c.N) :
    (Fin 2 → X.κ.K) ≃+ (Fin 2 → X.κ.K) :=
  (AddEquiv.toMultiplicative).symm (phiMulAut X a ha)

theorem phiAdd_apply (a : G) (ha : a ∈ c.N) (v : Fin 2 → X.κ.K) :
    phiAdd X a ha v = Multiplicative.toAdd (X.κ.β (conjVEquiv a ha
      ((betaMulEquiv X).symm (Multiplicative.ofAdd v)))) := by
  change Multiplicative.toAdd (phiMulAut X a ha (Multiplicative.ofAdd v)) = _
  simp only [phiMulAut, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rfl

theorem phiAdd_mulVec (a : G) (ha : a ∈ c.N)
    (haL : a ∈ Subgroup.normalizer (c.L : Set G)) (l : ↥c.L) (v : Fin 2 → X.κ.K) :
    phiAdd X a ha ((X.κ.α l : Matrix (Fin 2) (Fin 2) X.κ.K) *ᵥ v) =
      (X.κ.α ⟨a * (l : G) * a⁻¹,
        (Subgroup.mem_normalizer_iff.mp haL (l : G)).mp l.2⟩ :
        Matrix (Fin 2) (Fin 2) X.κ.K) *ᵥ phiAdd X a ha v := by
  have hLV : c.L ≤ Subgroup.normalizer (c.V : Set G) :=
    (le_sup_left : c.L ≤ c.L ⊔ D.T).trans (Ctx23L.sup_le_normalizer_V D Ch c)
  let w : ↥c.V := (betaMulEquiv X).symm (Multiplicative.ofAdd v)
  have hβw : X.κ.β w = Multiplicative.ofAdd v := (betaMulEquiv X).apply_symm_apply _
  have hL : Multiplicative.ofAdd
      ((X.κ.α l : Matrix (Fin 2) (Fin 2) X.κ.K) *ᵥ v) =
      X.κ.β (CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjV hLV l w) := by
    have hvv : v = Multiplicative.toAdd (X.κ.β w) := by rw [hβw]; rfl
    rw [hvv]
    exact (X.κ.β_act l w).symm
  have hVeq : conjVEquiv a ha
      (CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjV hLV l w) =
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjV hLV
        ⟨a * (l : G) * a⁻¹,
          (Subgroup.mem_normalizer_iff.mp haL (l : G)).mp l.2⟩
        (conjVEquiv a ha w) := by
    apply Subtype.ext
    change a * (↑(CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjV hLV l w) : G) * a⁻¹ =
      (a * (l : G) * a⁻¹) * (a * (w : G) * a⁻¹) * (a * (l : G) * a⁻¹)⁻¹
    simp only [CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjV]
    group
  rw [phiAdd_apply]
  rw [show (betaMulEquiv X).symm (Multiplicative.ofAdd
      ((X.κ.α l : Matrix (Fin 2) (Fin 2) X.κ.K) *ᵥ v)) =
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjV hLV l w from by
    rw [hL]
    change (betaMulEquiv X).symm
      ((betaMulEquiv X) (CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjV hLV l w)) = _
    rw [MulEquiv.symm_apply_apply]]
  rw [hVeq]
  have hβw' : Multiplicative.toAdd (X.κ.β (conjVEquiv a ha w)) =
      phiAdd X a ha v := rfl
  have h := X.κ.β_act ⟨a * (l : G) * a⁻¹,
    (Subgroup.mem_normalizer_iff.mp haL (l : G)).mp l.2⟩ (conjVEquiv a ha w)
  rw [h, hβw']
  rfl

theorem phiMulAut_mul (a b : G) (ha : a ∈ c.N) (hb : b ∈ c.N) :
    phiMulAut X (a * b) (c.N.mul_mem ha hb) = phiMulAut X a ha * phiMulAut X b hb := by
  ext x
  rw [MulAut.mul_apply]
  have hsub : conjVEquiv (a * b) (c.N.mul_mem ha hb) ((betaMulEquiv X).symm x) =
      conjVEquiv a ha (conjVEquiv b hb ((betaMulEquiv X).symm x)) := by
    apply Subtype.ext
    change (a * b) * (↑((betaMulEquiv X).symm x)) * (a * b)⁻¹ =
      a * (b * (↑((betaMulEquiv X).symm x)) * b⁻¹) * a⁻¹
    group
  simp only [phiMulAut, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rw [hsub]

theorem phiAdd_mul (a b : G) (ha : a ∈ c.N) (hb : b ∈ c.N) :
    phiAdd X (a * b) (c.N.mul_mem ha hb) = (phiAdd X b hb).trans (phiAdd X a ha) := by
  apply AddEquiv.ext
  intro v
  change Multiplicative.toAdd (phiMulAut X (a * b) (c.N.mul_mem ha hb)
      (Multiplicative.ofAdd v)) =
    Multiplicative.toAdd (phiMulAut X a ha (phiMulAut X b hb (Multiplicative.ofAdd v)))
  rw [phiMulAut_mul, MulAut.mul_apply]

theorem phiAdd_normalizesSL2 {a : G} (ha : a ∈ c.N)
    (haL : a ∈ Subgroup.normalizer (c.L : Set G)) :
    ∀ g : Matrix.SpecialLinearGroup (Fin 2) X.κ.K,
      ∃ g' : Matrix.SpecialLinearGroup (Fin 2) X.κ.K,
        ∀ v, phiAdd X a ha (g • v) = g' • phiAdd X a ha v := by
  intro g
  obtain ⟨l, rfl⟩ := X.κ.α_surj g
  refine ⟨X.κ.α ⟨a * (l : G) * a⁻¹,
    (Subgroup.mem_normalizer_iff.mp haL (l : G)).mp l.2⟩, fun v => ?_⟩
  rw [Matrix.SpecialLinearGroup.smul_def, Matrix.SpecialLinearGroup.smul_def]
  exact phiAdd_mulVec X a ha haL l v

theorem phiAdd_eOf (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch)
    (X : B2Data D Ch c)
    {a : G} (ha : a ∈ c.N) (haZ : a ∈ Subgroup.centralizer (D.Z : Set G))
    (z : ↥D.Z) (hzV : (z : G) ∈ c.V) :
    phiAdd X a ha (Multiplicative.toAdd (X.κ.β ⟨z, hzV⟩)) =
      Multiplicative.toAdd (X.κ.β ⟨z, hzV⟩) := by
  rw [phiAdd_apply]
  have hsym : (betaMulEquiv X).symm
      (Multiplicative.ofAdd (Multiplicative.toAdd (X.κ.β ⟨z, hzV⟩))) =
      (⟨z, hzV⟩ : ↥c.V) := by
    apply (betaMulEquiv X).injective
    rw [MulEquiv.apply_symm_apply]
    rfl
  rw [hsym]
  have hconj : conjVEquiv a ha ⟨z, hzV⟩ = ⟨z, hzV⟩ := by
    apply Subtype.ext
    have hcomm : (z : G) * a = a * z := Subgroup.mem_centralizer_iff.mp haZ z z.2
    calc a * (z : G) * a⁻¹ = (z : G) * a * a⁻¹ := by rw [← hcomm]
      _ = z := by group
  rw [hconj]

theorem exists_eOf_eq_smul (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h1930 : H1930 D)
    (u : X.κ.K) : ∃ z : ↥D.Z, ∃ hzV : (z : G) ∈ c.V,
      u • X.e = Multiplicative.toAdd (X.κ.β ⟨z, hzV⟩) := by
  classical
  have hZcard : Nat.card ↥D.Z = Nat.card X.κ.K := by
    rw [CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian Nat.prime_two
      (c.isElemAbelian_Z h4 h1930), X.κ.cardK]
  have hPle : X.P ≤ CFSG.LinearAlgebra.lineStabilizer X.e :=
    le_of_eq (X.P_eq_lineStabilizer h4 h23 h1930)
  have hcoef : ∀ z : ↥D.Z, ∃ u : X.κ.K,
      Multiplicative.toAdd (X.κ.β ⟨z, uc22p22v_le_conjClosure c.N D.Z z.2⟩) = u • X.e :=
    fun z => CFSG.LinearAlgebra.exists_eq_smul_of_forall_mulVec_eq_self hPle
      (X.P_ne_bot h4 h23 h1930) X.e_ne_zero (X.P_mulVec_eOf z)
  let f : ↥D.Z → X.κ.K := fun z => Classical.choose (hcoef z)
  have hf : ∀ z : ↥D.Z, Multiplicative.toAdd (X.κ.β
      ⟨z, uc22p22v_le_conjClosure c.N D.Z z.2⟩) = f z • X.e :=
    fun z => Classical.choose_spec (hcoef z)
  have hinj : Function.Injective f := by
    intro z w hzw
    have h1 : Multiplicative.toAdd (X.κ.β
        ⟨z, uc22p22v_le_conjClosure c.N D.Z z.2⟩) =
        Multiplicative.toAdd (X.κ.β ⟨w, uc22p22v_le_conjClosure c.N D.Z w.2⟩) := by
      rw [hf z, hf w, hzw]
    have h2 : (⟨z, uc22p22v_le_conjClosure c.N D.Z z.2⟩ : ↥c.V) =
        ⟨w, uc22p22v_le_conjClosure c.N D.Z w.2⟩ := by
      apply (betaMulEquiv X).injective
      simpa [betaMulEquiv] using congrArg Multiplicative.ofAdd h1
    exact Subtype.ext (congrArg (fun x : ↥c.V => (x : G)) h2)
  letI : Fintype ↥D.Z := Fintype.ofFinite _
  letI : Fintype X.κ.K := Fintype.ofFinite _
  have hcard' : Fintype.card ↥D.Z = Fintype.card X.κ.K := by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hZcard]
  have hsurj : Function.Surjective f :=
    (Finite.injective_iff_surjective_of_equiv (Fintype.equivOfCardEq hcard')).mp hinj
  obtain ⟨z, hz⟩ := hsurj u
  exact ⟨z, uc22p22v_le_conjClosure c.N D.Z z.2,
    by rw [← hz]; exact (hf z).symm⟩

theorem phiAdd_smul_e (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h1930 : H1930 D)
    {a : G} (ha : a ∈ c.N) (haZ : a ∈ Subgroup.centralizer (D.Z : Set G)) (u : X.κ.K) :
    phiAdd X a ha (u • X.e) = u • X.e := by
  obtain ⟨z, hzV, hz⟩ := exists_eOf_eq_smul X h4 h23 h1930 u
  rw [hz, phiAdd_eOf D Ch c X ha haZ z hzV]

theorem ringHom_eq_one_of_phiAdd (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h1930 : H1930 D)
    {a : G} (ha : a ∈ c.N) (haZ : a ∈ Subgroup.centralizer (D.Z : Set G))
    (σ : X.κ.K →+* X.κ.K)
    (hσ : ∀ (u : X.κ.K) (w : Fin 2 → X.κ.K),
      phiAdd X a ha (u • w) = σ u • phiAdd X a ha w) :
    σ = 1 := by
  have hefix : phiAdd X a ha X.e = X.e := by
    rw [X.e_eq_eOf]
    exact phiAdd_eOf D Ch c X ha haZ X.z₀
      (uc22p22v_le_conjClosure c.N D.Z X.z₀.2)
  ext u
  have h1 : phiAdd X a ha (u • X.e) = σ u • X.e := by
    rw [hσ u X.e, hefix]
  have h2 : u • X.e = σ u • X.e :=
    (phiAdd_smul_e X h4 h23 h1930 ha haZ u).symm.trans h1
  have h3 : (u - σ u) • X.e = 0 := by rw [sub_smul, h2, sub_self]
  rcases smul_eq_zero.mp h3 with h4' | h4'
  · exact (sub_eq_zero.mp h4').symm
  · exact absurd h4' X.e_ne_zero

theorem exists_phiLinear (h1930 : H1930 D) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch)
    {a : G} (ha : a ∈ c.N) (haL : a ∈ Subgroup.normalizer (c.L : Set G))
    (haZ : a ∈ Subgroup.centralizer (D.Z : Set G)) :
    ∃ L : (Fin 2 → X.κ.K) ≃ₗ[X.κ.K] (Fin 2 → X.κ.K),
      ∀ v, L v = phiAdd X a ha v := by
  obtain ⟨σ, hσ⟩ :=
    CFSG.LocalAnalysis.WeakClosure81.exists_ringHom_map_smul_of_normalizes
      (phiAdd X a ha) (phiAdd_normalizesSL2 X ha haL)
  have hσ1 : σ = 1 := ringHom_eq_one_of_phiAdd X h4 h23 h1930 ha haZ σ hσ
  let L : (Fin 2 → X.κ.K) ≃ₗ[X.κ.K] (Fin 2 → X.κ.K) :=
    { toFun := phiAdd X a ha
      invFun := (phiAdd X a ha).symm
      left_inv := (phiAdd X a ha).left_inv
      right_inv := (phiAdd X a ha).right_inv
      map_add' := (phiAdd X a ha).map_add
      map_smul' := by
        intro u v
        rw [hσ u v, hσ1]
        rfl }
  exact ⟨L, fun _ => rfl⟩

end B2Data

theorem nonempty_b2Data (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch)
    (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h1930 : H1930 D) :
    Nonempty (B2Data D Ch c) := by
  obtain ⟨hV, hLV, κ, hker_eq, -⟩ := Ctx23L.exists_coordinates_V D Ch h4 h23 h1930 c
  have hC2 : IsPGroup 2 ↥(c.L ⊓ Subgroup.centralizer (c.V : Set G)) :=
    (Ctx23L.isPGroup_sup_inf_centralizer_V D Ch h4 h23 h1930 c).to_le
      (inf_le_inf (le_sup_left : c.L ≤ c.L ⊔ D.T) le_rfl)
  have hker : CFSG.pCore 2 ↥c.L ≤ κ.α.ker := le_of_eq (κ.ker_α hC2).symm
  obtain ⟨z₀, hz₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (uc22main1_Z_ne_bot D)
  let X : B2Data D Ch c :=
    { hV := hV, hLV := hLV, κ := κ, hker := hker, hker_eq := hker_eq,
      z₀ := z₀, hz₀1 := hz₀1 }
  exact ⟨X⟩

private def conjOnL {L : Subgroup G} {a : G}
    (haL : a ∈ Subgroup.normalizer (L : Set G)) (l : ↥L) : ↥L :=
  ⟨a * (l : G) * a⁻¹, (Subgroup.mem_normalizer_iff.mp haL (l : G)).mp l.2⟩

private theorem matrix_conj_alpha {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (X : B2Data D Ch c) {a : G} (ha : a ∈ c.N)
    (haL : a ∈ Subgroup.normalizer (c.L : Set G))
    (L : (Fin 2 → X.κ.K) ≃ₗ[X.κ.K] (Fin 2 → X.κ.K))
    (hL : ∀ v, L v = B2Data.phiAdd X a ha v)
    (M : Matrix (Fin 2) (Fin 2) X.κ.K) (hM : ∀ v, M.mulVec v = L v)
    (hMunit : IsUnit M.det) (l : ↥c.L) :
    M * (X.κ.α l : Matrix (Fin 2) (Fin 2) X.κ.K) * M⁻¹ =
      (X.κ.α (conjOnL haL l) : Matrix (Fin 2) (Fin 2) X.κ.K) := by
  apply CFSG.Quasithin.H13.matrix_eq_of_mulVec_eq
  intro v
  calc (M * (X.κ.α l : Matrix (Fin 2) (Fin 2) X.κ.K) * M⁻¹) *ᵥ v
      = M *ᵥ ((X.κ.α l : Matrix (Fin 2) (Fin 2) X.κ.K) *ᵥ (M⁻¹ *ᵥ v)) := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    _ = B2Data.phiAdd X a ha ((X.κ.α l : Matrix (Fin 2) (Fin 2) X.κ.K) *ᵥ
          (M⁻¹ *ᵥ v)) := by
        rw [hM, hL]
    _ = (X.κ.α (conjOnL haL l) : Matrix (Fin 2) (Fin 2) X.κ.K) *ᵥ
          B2Data.phiAdd X a ha (M⁻¹ *ᵥ v) :=
        B2Data.phiAdd_mulVec X a ha haL l (M⁻¹ *ᵥ v)
    _ = (X.κ.α (conjOnL haL l) : Matrix (Fin 2) (Fin 2) X.κ.K) *ᵥ
          (M *ᵥ (M⁻¹ *ᵥ v)) := by rw [hM, hL]
    _ = (X.κ.α (conjOnL haL l) : Matrix (Fin 2) (Fin 2) X.κ.K) *ᵥ v := by
        have hMM : M *ᵥ (M⁻¹ *ᵥ v) = v := by
          rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hMunit, Matrix.one_mulVec]
        rw [hMM]

private theorem conj_alpha_of_matrix_conj {D : Data G} {Ch : Choice2011 G}
    {c : Ctx23L D Ch} (X : B2Data D Ch c) {a : G}
    (haL : a ∈ Subgroup.normalizer (c.L : Set G))
    (s : Matrix.SpecialLinearGroup (Fin 2) X.κ.K)
    (M : Matrix (Fin 2) (Fin 2) X.κ.K)
    (hconjM : ∀ l : ↥c.L, M * (X.κ.α l : Matrix (Fin 2) (Fin 2) X.κ.K) * M⁻¹ =
      (X.κ.α (conjOnL haL l) : Matrix (Fin 2) (Fin 2) X.κ.K))
    (hconj : ∀ A : Matrix (Fin 2) (Fin 2) X.κ.K,
      M * A * M⁻¹ = (s : Matrix (Fin 2) (Fin 2) X.κ.K) * A *
        (s : Matrix (Fin 2) (Fin 2) X.κ.K)⁻¹)
    (l : ↥c.L) :
    X.κ.α (conjOnL haL l) = s * X.κ.α l * s⁻¹ := by
  have hsunit : IsUnit (s : Matrix (Fin 2) (Fin 2) X.κ.K).det := by
    rw [Matrix.SpecialLinearGroup.det_coe]
    exact isUnit_one
  have hmat : (s : Matrix (Fin 2) (Fin 2) X.κ.K) *
        (X.κ.α l : Matrix (Fin 2) (Fin 2) X.κ.K) *
        (s : Matrix (Fin 2) (Fin 2) X.κ.K)⁻¹ =
      (X.κ.α (conjOnL haL l) : Matrix (Fin 2) (Fin 2) X.κ.K) :=
    (hconj (X.κ.α l)).symm.trans (hconjM l)
  have hsA : (s : Matrix (Fin 2) (Fin 2) X.κ.K) *
        (X.κ.α l : Matrix (Fin 2) (Fin 2) X.κ.K) =
      (X.κ.α (conjOnL haL l) : Matrix (Fin 2) (Fin 2) X.κ.K) *
        (s : Matrix (Fin 2) (Fin 2) X.κ.K) := by
    have h1 : (s : Matrix (Fin 2) (Fin 2) X.κ.K) *
          (X.κ.α l : Matrix (Fin 2) (Fin 2) X.κ.K) *
          (s : Matrix (Fin 2) (Fin 2) X.κ.K)⁻¹ *
          (s : Matrix (Fin 2) (Fin 2) X.κ.K) =
        (X.κ.α (conjOnL haL l) : Matrix (Fin 2) (Fin 2) X.κ.K) *
          (s : Matrix (Fin 2) (Fin 2) X.κ.K) := by
      rw [hmat]
    rwa [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hsunit, Matrix.mul_one] at h1
  have hsA' : s * X.κ.α l = X.κ.α (conjOnL haL l) * s := Subtype.ext hsA
  calc X.κ.α (conjOnL haL l) = X.κ.α (conjOnL haL l) * s * s⁻¹ := by group
    _ = s * X.κ.α l * s⁻¹ := by rw [← hsA']

private theorem exists_specialLinear_conj_of_linear (D : Data G) (Ch : Choice2011 G)
    (c : Ctx23L D Ch) (X : B2Data D Ch c)
    {a : G} (ha : a ∈ c.N) (haL : a ∈ Subgroup.normalizer (c.L : Set G))
    (L : (Fin 2 → X.κ.K) ≃ₗ[X.κ.K] (Fin 2 → X.κ.K))
    (hL : ∀ v, L v = B2Data.phiAdd X a ha v) :
    ∃ (s : Matrix.SpecialLinearGroup (Fin 2) X.κ.K) (ℓ₀ : ↥c.L),
      X.κ.α ℓ₀ = s ∧ ∀ l : ↥c.L, X.κ.α ⟨a * (l : G) * a⁻¹,
        (Subgroup.mem_normalizer_iff.mp haL (l : G)).mp l.2⟩ = s * X.κ.α l * s⁻¹ := by
  classical
  let M : Matrix (Fin 2) (Fin 2) X.κ.K :=
    LinearMap.toMatrix' (L : (Fin 2 → X.κ.K) →ₗ[X.κ.K] (Fin 2 → X.κ.K))
  have hM : ∀ v, M.mulVec v = L v := fun v => LinearMap.toMatrix'_mulVec _ v
  have hMdet : M.det = LinearMap.det (L : (Fin 2 → X.κ.K) →ₗ[X.κ.K]
      (Fin 2 → X.κ.K)) := LinearMap.det_toMatrix' _
  have hunit : IsUnit (LinearMap.det (L : (Fin 2 → X.κ.K) →ₗ[X.κ.K]
      (Fin 2 → X.κ.K))) := LinearEquiv.isUnit_det' L
  have hMdet0 : M.det ≠ 0 := by rw [hMdet]; exact hunit.ne_zero
  have hMunit : IsUnit M.det := by rw [hMdet]; exact hunit
  obtain ⟨s, -, -, -, hconj⟩ :=
    CFSG.LinearAlgebra.exists_specialLinear_conj_eq_of_det_ne_zero M hMdet0
  have hconjM : ∀ l : ↥c.L,
      M * (X.κ.α l : Matrix (Fin 2) (Fin 2) X.κ.K) * M⁻¹ =
        (X.κ.α (conjOnL haL l) : Matrix (Fin 2) (Fin 2) X.κ.K) :=
    fun l => matrix_conj_alpha X ha haL L hL M hM hMunit l
  obtain ⟨ℓ₀, hℓ₀⟩ := X.κ.α_surj s
  refine ⟨s, ℓ₀, hℓ₀, ?_⟩
  intro l
  simpa only [conjOnL] using conj_alpha_of_matrix_conj X haL s M hconjM hconj l

private theorem inducedBar_conj_mk_of_alpha_eq {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h1930 : H1930 D)
    (X : B2Data D Ch c) {a : G} (haNL : a ∈ Subgroup.normalizer (c.L : Set G))
    (ℓ₀ : ↥c.L)
    (hα : ∀ l : ↥c.L, X.κ.α ⟨a * (l : G) * a⁻¹,
      (Subgroup.mem_normalizer_iff.mp haNL (l : G)).mp l.2⟩ = X.κ.α (ℓ₀ * l * ℓ₀⁻¹)) :
    InducedBar c.L a (MulAut.conj (QuotientGroup.mk (s := CFSG.pCore 2 ↥c.L) ℓ₀)) := by
  intro l l' hll'
  let lcan : ↥c.L := ⟨a * (l : G) * a⁻¹,
    (Subgroup.mem_normalizer_iff.mp haNL (l : G)).mp l.2⟩
  have hl' : l' = lcan := Subtype.ext hll'
  have hmemKer : ((ℓ₀ * l * ℓ₀⁻¹)⁻¹ * lcan : ↥c.L) ∈ X.κ.α.ker := by
    have hα' : X.κ.α (ℓ₀ * l * ℓ₀⁻¹) = X.κ.α lcan := (hα l).symm
    rw [MonoidHom.mem_ker, map_mul, map_inv, hα']
    group
  have hmem : ((ℓ₀ * l * ℓ₀⁻¹)⁻¹ * lcan : ↥c.L) ∈ CFSG.pCore 2 ↥c.L := by
    rw [X.hker_eq] at hmemKer
    exact mem_pCore_of_mem_inf_centralizer_V h4 h23 h1930 c
      (Subgroup.mem_subgroupOf.mp hmemKer)
  have hquot : QuotientGroup.mk (s := CFSG.pCore 2 ↥c.L) l' =
      QuotientGroup.mk (s := CFSG.pCore 2 ↥c.L) (ℓ₀ * l * ℓ₀⁻¹) := by
    rw [hl', QuotientGroup.eq]
    simpa using (CFSG.pCore 2 ↥c.L).inv_mem hmem
  show (MulAut.conj (QuotientGroup.mk (s := CFSG.pCore 2 ↥c.L) ℓ₀))
      (QuotientGroup.mk (s := CFSG.pCore 2 ↥c.L) l) =
    QuotientGroup.mk (s := CFSG.pCore 2 ↥c.L) l'
  rw [MulAut.conj_apply]
  change QuotientGroup.mk (s := CFSG.pCore 2 ↥c.L) ℓ₀ *
      QuotientGroup.mk (s := CFSG.pCore 2 ↥c.L) l *
      (QuotientGroup.mk (s := CFSG.pCore 2 ↥c.L) ℓ₀)⁻¹ =
    QuotientGroup.mk (s := CFSG.pCore 2 ↥c.L) l'
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  exact hquot.symm

theorem exists_inducedBar_conj_of_mem (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch)
    (h1930 : H1930 D) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch)
    (hLN : (c.L.subgroupOf c.N).Normal) {K : Subgroup G} (hK : K ∈ calC D.M)
    {a : G} (ha : a ∈ K ⊓ c.N) :
    ∃ ℓ : Bar2 c.L, InducedBar c.L a (MulAut.conj ℓ) := by
  classical
  obtain ⟨X⟩ := nonempty_b2Data D Ch c h4 h23 h1930
  have haK : a ∈ K := ha.1
  have haN : a ∈ c.N := ha.2
  have haZ : a ∈ Subgroup.centralizer (D.Z : Set G) :=
    le_centralizer_Z_of_perfect D Ch h4 h1930 c (CFSG.Open.IsSubnormal.le hK.1) hK.2.1 haK
  have haNL : a ∈ Subgroup.normalizer (c.L : Set G) :=
    (le_normalizer_of_normal_subgroupOf c hLN) haN
  obtain ⟨L, hL⟩ := B2Data.exists_phiLinear X h1930 h4 h23 haN haNL haZ
  obtain ⟨s, ℓ₀, hℓ₀, hαl⟩ :=
    exists_specialLinear_conj_of_linear D Ch c X haN haNL L hL
  have hα : ∀ l : ↥c.L, X.κ.α ⟨a * (l : G) * a⁻¹,
      (Subgroup.mem_normalizer_iff.mp haNL (l : G)).mp l.2⟩ =
      X.κ.α (ℓ₀ * l * ℓ₀⁻¹) := by
    intro l
    rw [map_mul, map_mul, map_inv, hℓ₀]
    exact hαl l
  exact ⟨QuotientGroup.mk (s := CFSG.pCore 2 ↥c.L) ℓ₀,
    inducedBar_conj_mk_of_alpha_eq c h4 h23 h1930 X haNL ℓ₀ hα⟩

private noncomputable def linearAction {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (X : B2Data D Ch c) {A : Subgroup G} (h4 : S23_4 D Ch) (h23 : S23_23 D Ch)
    (h1930 : H1930 D) (haN : ∀ a : ↥A, (a : G) ∈ c.N)
    (haNL : ∀ a : ↥A, (a : G) ∈ Subgroup.normalizer (c.L : Set G))
    (haZ : ∀ a : ↥A, (a : G) ∈ Subgroup.centralizer (D.Z : Set G)) (a : ↥A) :
    (Fin 2 → X.κ.K) ≃ₗ[X.κ.K] (Fin 2 → X.κ.K) :=
  Classical.choose (B2Data.exists_phiLinear X h1930 h4 h23 (haN a) (haNL a) (haZ a))

private theorem linearAction_apply {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (X : B2Data D Ch c) {A : Subgroup G} (h4 : S23_4 D Ch) (h23 : S23_23 D Ch)
    (h1930 : H1930 D) (haN : ∀ a : ↥A, (a : G) ∈ c.N)
    (haNL : ∀ a : ↥A, (a : G) ∈ Subgroup.normalizer (c.L : Set G))
    (haZ : ∀ a : ↥A, (a : G) ∈ Subgroup.centralizer (D.Z : Set G)) (a : ↥A)
    (v : Fin 2 → X.κ.K) :
    linearAction X h4 h23 h1930 haN haNL haZ a v =
      B2Data.phiAdd X (a : G) (haN a) v :=
  Classical.choose_spec (B2Data.exists_phiLinear X h1930 h4 h23 (haN a) (haNL a) (haZ a)) v

private theorem linearAction_mul {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (X : B2Data D Ch c) {A : Subgroup G} (h4 : S23_4 D Ch) (h23 : S23_23 D Ch)
    (h1930 : H1930 D) (haN : ∀ a : ↥A, (a : G) ∈ c.N)
    (haNL : ∀ a : ↥A, (a : G) ∈ Subgroup.normalizer (c.L : Set G))
    (haZ : ∀ a : ↥A, (a : G) ∈ Subgroup.centralizer (D.Z : Set G)) (a b : ↥A) :
    linearAction X h4 h23 h1930 haN haNL haZ (a * b) =
      linearAction X h4 h23 h1930 haN haNL haZ a *
        linearAction X h4 h23 h1930 haN haNL haZ b := by
  apply LinearEquiv.ext
  intro v
  have hproof : c.N.mul_mem (haN a) (haN b) = haN (a * b) := Subsingleton.elim _ _
  have hmul := B2Data.phiAdd_mul X (a : G) (b : G) (haN a) (haN b)
  rw [hproof] at hmul
  rw [linearAction_apply X h4 h23 h1930 haN haNL haZ (a * b) v, LinearEquiv.mul_apply,
    linearAction_apply X h4 h23 h1930 haN haNL haZ a
      (linearAction X h4 h23 h1930 haN haNL haZ b v),
    linearAction_apply X h4 h23 h1930 haN haNL haZ b v]
  change (B2Data.phiAdd X ((a : G) * (b : G)) (haN (a * b))) v =
    (B2Data.phiAdd X (a : G) (haN a))
      ((B2Data.phiAdd X (b : G) (haN b)) v)
  rw [hmul, AddEquiv.trans_apply]

private noncomputable def detChar {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (X : B2Data D Ch c) {A : Subgroup G} (h4 : S23_4 D Ch) (h23 : S23_23 D Ch)
    (h1930 : H1930 D) (haN : ∀ a : ↥A, (a : G) ∈ c.N)
    (haNL : ∀ a : ↥A, (a : G) ∈ Subgroup.normalizer (c.L : Set G))
    (haZ : ∀ a : ↥A, (a : G) ∈ Subgroup.centralizer (D.Z : Set G)) :
    ↥A →* X.κ.Kˣ :=
  LinearEquiv.det.comp
    (MonoidHom.mk' (linearAction X h4 h23 h1930 haN haNL haZ)
      (linearAction_mul X h4 h23 h1930 haN haNL haZ))

private theorem detChar_apply {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (X : B2Data D Ch c) {A : Subgroup G} (h4 : S23_4 D Ch) (h23 : S23_23 D Ch)
    (h1930 : H1930 D) (haN : ∀ a : ↥A, (a : G) ∈ c.N)
    (haNL : ∀ a : ↥A, (a : G) ∈ Subgroup.normalizer (c.L : Set G))
    (haZ : ∀ a : ↥A, (a : G) ∈ Subgroup.centralizer (D.Z : Set G)) (a : ↥A) :
    detChar X h4 h23 h1930 haN haNL haZ a =
      LinearEquiv.det (linearAction X h4 h23 h1930 haN haNL haZ a) := rfl

private theorem eq_one_of_det_eq_one_of_fixes_e {D : Data G} {Ch : Choice2011 G}
    {c : Ctx23L D Ch} (X : B2Data D Ch c)
    (L : (Fin 2 → X.κ.K) ≃ₗ[X.κ.K] (Fin 2 → X.κ.K))
    (hLdet : LinearEquiv.det L = 1) (he : L X.e = X.e)
    {n : ℕ} (hpow : L ^ n = 1) (hodd : Odd n) : L = 1 := by
  have hLdet' : LinearMap.det (L : (Fin 2 → X.κ.K) →ₗ[X.κ.K]
      (Fin 2 → X.κ.K)) = 1 := by
    rw [← LinearEquiv.coe_det, hLdet, Units.val_one]
  let M : Matrix (Fin 2) (Fin 2) X.κ.K :=
    LinearMap.toMatrix' (L : (Fin 2 → X.κ.K) →ₗ[X.κ.K] (Fin 2 → X.κ.K))
  have hMdet : M.det = 1 := by
    change (LinearMap.toMatrix' (L : (Fin 2 → X.κ.K) →ₗ[X.κ.K]
      (Fin 2 → X.κ.K))).det = 1
    rw [LinearMap.det_toMatrix']
    exact hLdet'
  have hM : ∀ v, M.mulVec v = L v := fun v => LinearMap.toMatrix'_mulVec _ v
  have hMe : M.mulVec X.e = X.e := by rw [hM, he]
  have hsqM : M * M = 1 :=
    CFSG.LinearAlgebra.mul_self_eq_one_of_mulVec_eq_self M hMdet X.e_ne_zero hMe
  have hsq : L * L = 1 := by
    apply LinearEquiv.ext
    intro v
    change L (L v) = v
    have h1 : M.mulVec (M.mulVec v) = v := by
      calc M.mulVec (M.mulVec v) = (M * M).mulVec v := Matrix.mulVec_mulVec v M M
        _ = v := by rw [hsqM, Matrix.one_mulVec]
    rwa [hM, hM] at h1
  have hdvd2 : orderOf L ∣ 2 := by
    apply orderOf_dvd_of_pow_eq_one
    rw [pow_two]
    exact hsq
  have hdvda : orderOf L ∣ n := orderOf_dvd_of_pow_eq_one hpow
  rw [← orderOf_eq_one_iff]
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h | h
  · exact h
  · exact absurd (h ▸ hdvda) hodd.not_two_dvd_nat

private theorem det_eq_one_imp_eq_one {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (X : B2Data D Ch c) {A : Subgroup G}
    (hom : ↥A →* ((Fin 2 → X.κ.K) ≃ₗ[X.κ.K] (Fin 2 → X.κ.K)))
    {a : ↥A} (haN : (a : G) ∈ c.N)
    (haZ : (a : G) ∈ Subgroup.centralizer (D.Z : Set G))
    (hLf : ∀ v, hom a v = B2Data.phiAdd X (a : G) haN v)
    (hdet : LinearEquiv.det (hom a) = 1) (hodd : Odd (orderOf a)) :
    hom a = 1 := by
  let L : (Fin 2 → X.κ.K) ≃ₗ[X.κ.K] (Fin 2 → X.κ.K) := hom a
  have hL : ∀ v, L v = B2Data.phiAdd X (a : G) haN v := hLf
  have he : L X.e = X.e := by
    rw [hL, X.e_eq_eOf]
    exact B2Data.phiAdd_eOf D Ch c X haN haZ X.z₀
      (uc22p22v_le_conjClosure c.N D.Z X.z₀.2)
  have hpow : L ^ orderOf a = 1 := by
    change (hom a) ^ orderOf a = 1
    rw [← map_pow hom a (orderOf a), pow_orderOf_eq_one, map_one]
  have hone := eq_one_of_det_eq_one_of_fixes_e X L hdet he hpow hodd
  change L = 1
  exact hone

theorem mem_centralizer_V_of_phiAdd_eq_one {D : Data G} {Ch : Choice2011 G}
    {c : Ctx23L D Ch} (X : B2Data D Ch c) {a : G} (haN : a ∈ c.N)
    (hphi : ∀ v, B2Data.phiAdd X a haN v = v) :
    a ∈ Subgroup.centralizer (c.V : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  let vV : ↥c.V := ⟨v, hv⟩
  have hβ : X.κ.β (B2Data.conjVEquiv a haN vV) = X.κ.β vV := by
    have h1 := hphi (Multiplicative.toAdd (X.κ.β vV))
    rw [B2Data.phiAdd_apply] at h1
    have h2 : (B2Data.betaMulEquiv X).symm
        (Multiplicative.ofAdd (Multiplicative.toAdd (X.κ.β vV))) = vV :=
      MulEquiv.symm_apply_apply (B2Data.betaMulEquiv X) vV
    rw [h2] at h1
    simpa using congrArg Multiplicative.ofAdd h1
  have hvV : B2Data.conjVEquiv a haN vV = vV :=
    (B2Data.betaMulEquiv X).injective hβ
  have hmul : a * v * a⁻¹ = v := by
    simpa [B2Data.conjVEquiv, CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjV]
      using congrArg Subtype.val hvV
  calc v * a = (a * v * a⁻¹) * a := by rw [hmul]
    _ = a * v := by group

private theorem detChar_injective {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (X : B2Data D Ch c) {A : Subgroup G} (h4 : S23_4 D Ch) (h23 : S23_23 D Ch)
    (h1930 : H1930 D) (haN : ∀ a : ↥A, (a : G) ∈ c.N)
    (haNL : ∀ a : ↥A, (a : G) ∈ Subgroup.normalizer (c.L : Set G))
    (haZ : ∀ a : ↥A, (a : G) ∈ Subgroup.centralizer (D.Z : Set G))
    (h847 : R847ThinCZ D) (hLN : (c.L.subgroupOf c.N).Normal)
    {K : Subgroup G} (hK : K ∈ calC D.M) (hthin : F08.Thin8 K)
    (haK : ∀ a : ↥A, (a : G) ∈ K) (hoddA : Odd (Nat.card A)) :
    Function.Injective (detChar X h4 h23 h1930 haN haNL haZ) := by
  rw [injective_iff_map_eq_one]
  intro a hχ
  have hdet : LinearEquiv.det (linearAction X h4 h23 h1930 haN haNL haZ a) = 1 := by
    rw [← detChar_apply X h4 h23 h1930 haN haNL haZ a]
    exact hχ
  have hodd_a : Odd (orderOf (a : ↥A)) := by
    rw [← Subgroup.orderOf_coe a]
    exact hoddA.of_dvd_nat (Subgroup.orderOf_dvd_natCard A a.2)
  have hone : linearAction X h4 h23 h1930 haN haNL haZ a = 1 :=
    det_eq_one_imp_eq_one X
      (MonoidHom.mk' (linearAction X h4 h23 h1930 haN haNL haZ)
        (linearAction_mul X h4 h23 h1930 haN haNL haZ))
      (haN a) (haZ a)
      (fun v => linearAction_apply X h4 h23 h1930 haN haNL haZ a v) hdet hodd_a
  by_contra ha1
  have ha1G : (a : G) ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hphi : ∀ v, B2Data.phiAdd X (a : G) (haN a) v = v := by
    intro v
    rw [← linearAction_apply X h4 h23 h1930 haN haNL haZ a v, hone]
    rfl
  have haC := mem_centralizer_V_of_phiAdd_eq_one X (haN a) hphi
  have hodd_aG : Odd (orderOf (a : G)) := by
    rw [Subgroup.orderOf_coe]
    exact hodd_a
  exact (Ctx23L.not_mem_centralizer_V c h1930 h4 h23 h847 hLN hK hthin
    (haK a) ha1G hodd_aG) haC

private theorem isCyclic_and_card_dvd_of_injective_detChar {D : Data G} {Ch : Choice2011 G}
    {c : Ctx23L D Ch} (X : B2Data D Ch c) {A : Subgroup G}
    (χ : ↥A →* X.κ.Kˣ) (hinj : Function.Injective χ) :
    IsCyclic ↥A ∧ Nat.card A ∣ 2 ^ CFSG.Open.pRank 2 D.Z - 1 := by
  refine ⟨isCyclic_of_injective χ hinj, ?_⟩
  have hcard : Nat.card ↥A = Nat.card ↥χ.range :=
    Nat.card_congr (MulEquiv.ofBijective χ.rangeRestrict
      ⟨fun a b hab => hinj (by simpa using congrArg Subtype.val hab),
        MonoidHom.rangeRestrict_surjective χ⟩).toEquiv
  have hdvd : Nat.card ↥A ∣ Nat.card X.κ.Kˣ := by
    rw [hcard]
    have h := Subgroup.card_dvd_of_le (H := χ.range) (K := ⊤) le_top
    simpa [Subgroup.card_top] using h
  have hdvd' : Nat.card ↥A ∣ Nat.card X.κ.K - 1 := by
    rw [← Nat.card_units]
    exact hdvd
  rwa [X.κ.cardK] at hdvd'

theorem isCyclic_and_card_dvd_of_le (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch)
    (h1930 : H1930 D) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h847 : R847ThinCZ D)
    (hLN : (c.L.subgroupOf c.N).Normal) {K : Subgroup G}
    (hK : K ∈ calC D.M) (hthin : F08.Thin8 K) {A : Subgroup G} (hA : A ≤ K ⊓ c.N)
    (hoddA : Odd (Nat.card A)) :
    IsCyclic ↥A ∧ Nat.card A ∣ 2 ^ CFSG.Open.pRank 2 D.Z - 1 := by
  classical
  obtain ⟨X⟩ := nonempty_b2Data D Ch c h4 h23 h1930
  have haK : ∀ a : ↥A, (a : G) ∈ K := fun a => (Subgroup.mem_inf.mp (hA a.2)).1
  have haN : ∀ a : ↥A, (a : G) ∈ c.N := fun a => (Subgroup.mem_inf.mp (hA a.2)).2
  have haZ : ∀ a : ↥A, (a : G) ∈ Subgroup.centralizer (D.Z : Set G) := fun a =>
    le_centralizer_Z_of_perfect D Ch h4 h1930 c (CFSG.Open.IsSubnormal.le hK.1) hK.2.1
      (haK a)
  have haNL : ∀ a : ↥A, (a : G) ∈ Subgroup.normalizer (c.L : Set G) :=
    fun a => (le_normalizer_of_normal_subgroupOf c hLN) (haN a)
  exact isCyclic_and_card_dvd_of_injective_detChar X
    (detChar X h4 h23 h1930 haN haNL haZ)
    (detChar_injective X h4 h23 h1930 haN haNL haZ h847 hLN hK hthin haK hoddA)

theorem isMulCommutative_of_le (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch)
    (h1930 : H1930 D) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h847 : R847ThinCZ D)
    (hLN : (c.L.subgroupOf c.N).Normal) {K : Subgroup G}
    (hK : K ∈ calC D.M) (hthin : F08.Thin8 K) {A : Subgroup G} (hA : A ≤ K ⊓ c.N)
    (hoddA : Odd (Nat.card A)) : IsMulCommutative ↥A :=
  (isCyclic_and_card_dvd_of_le D Ch c h1930 h4 h23 h847 hLN hK hthin hA
    hoddA).1.isMulCommutative

private theorem eq_one_of_detChar_eq_one_of_odd {D : Data G} {Ch : Choice2011 G}
    {c : Ctx23L D Ch} (X : B2Data D Ch c) {A : Subgroup G}
    (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h1930 : H1930 D)
    (haN : ∀ a : ↥A, (a : G) ∈ c.N)
    (haNL : ∀ a : ↥A, (a : G) ∈ Subgroup.normalizer (c.L : Set G))
    (haZ : ∀ a : ↥A, (a : G) ∈ Subgroup.centralizer (D.Z : Set G))
    (h847 : R847ThinCZ D)
    (hLN : (c.L.subgroupOf c.N).Normal) {K : Subgroup G} (hK : K ∈ calC D.M)
    (hthin : F08.Thin8 K) {a : ↥A} (haK : (a : G) ∈ K)
    (hdet : detChar X h4 h23 h1930 haN haNL haZ a = 1) (hodd : Odd (orderOf a)) :
    a = 1 := by
  have hdet' : LinearEquiv.det (linearAction X h4 h23 h1930 haN haNL haZ a) = 1 := by
    rw [← detChar_apply X h4 h23 h1930 haN haNL haZ a]
    exact hdet
  have hone : linearAction X h4 h23 h1930 haN haNL haZ a = 1 :=
    det_eq_one_imp_eq_one X
      (MonoidHom.mk' (linearAction X h4 h23 h1930 haN haNL haZ)
        (linearAction_mul X h4 h23 h1930 haN haNL haZ))
      (haN a) (haZ a)
      (fun v => linearAction_apply X h4 h23 h1930 haN haNL haZ a v) hdet' hodd
  have hphi : ∀ v, B2Data.phiAdd X (a : G) (haN a) v = v := by
    intro v
    rw [← linearAction_apply X h4 h23 h1930 haN haNL haZ a v, hone]
    rfl
  have hC : (a : G) ∈ Subgroup.centralizer (c.V : Set G) :=
    mem_centralizer_V_of_phiAdd_eq_one X (haN a) hphi
  by_contra ha1
  have ha1G : (a : G) ≠ 1 := fun h => ha1 (Subtype.ext h)
  exact (not_mem_centralizer_V c h1930 h4 h23 h847 hLN hK hthin haK ha1G
    (by rw [Subgroup.orderOf_coe]; exact hodd)) hC

private theorem exists_orderOf_eq_two_pow_of_detChar_eq_one {D : Data G} {Ch : Choice2011 G}
    {c : Ctx23L D Ch} (X : B2Data D Ch c) {A : Subgroup G}
    (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h1930 : H1930 D)
    (haN : ∀ a : ↥A, (a : G) ∈ c.N)
    (haNL : ∀ a : ↥A, (a : G) ∈ Subgroup.normalizer (c.L : Set G))
    (haZ : ∀ a : ↥A, (a : G) ∈ Subgroup.centralizer (D.Z : Set G))
    (h847 : R847ThinCZ D)
    (hLN : (c.L.subgroupOf c.N).Normal) {K : Subgroup G} (hK : K ∈ calC D.M)
    (hthin : F08.Thin8 K) {a : ↥A} (haK : (a : G) ∈ K)
    (hdet : detChar X h4 h23 h1930 haN haNL haZ a = 1) :
    ∃ i : ℕ, orderOf (a : G) = 2 ^ i := by
  obtain ⟨i, u, hodd_u, h_u⟩ :=
    Nat.exists_eq_two_pow_mul_odd (orderOf_pos (a : G)).ne'
  have hdvd : 2 ^ i ∣ orderOf (a : G) := ⟨u, h_u⟩
  let h : G := (a : G) ^ 2 ^ i
  have hu : orderOf h = u := by
    rw [show h = (a : G) ^ 2 ^ i from rfl,
      orderOf_pow_of_dvd (pow_ne_zero i two_ne_zero) hdvd, h_u,
      Nat.mul_div_cancel_left u (pow_pos two_pos i)]
  have hhA : h ∈ A := A.pow_mem a.2 (2 ^ i)
  have hhK : h ∈ K := K.pow_mem haK (2 ^ i)
  let hA : ↥A := ⟨h, hhA⟩
  have hχh : detChar X h4 h23 h1930 haN haNL haZ hA = 1 := by
    have hh_eq : hA = a ^ 2 ^ i := Subtype.ext rfl
    rw [hh_eq, map_pow, hdet, one_pow]
  have hoddhA : Odd (orderOf hA) := by
    rw [← Subgroup.orderOf_coe hA]
    rw [show (hA : G) = h from rfl, hu]
    exact hodd_u
  have h1A : hA = 1 :=
    eq_one_of_detChar_eq_one_of_odd X h4 h23 h1930 haN haNL haZ h847 hLN hK
      hthin hhK hχh hoddhA
  have hu1 : u = 1 := by
    have h1 : h = 1 := by simpa [hA] using congrArg Subtype.val h1A
    rw [← hu, h1, orderOf_one]
  refine ⟨i, ?_⟩
  rw [h_u, hu1, Nat.mul_one]

theorem exists_orderOf_commutator_eq_two_pow (D : Data G) (Ch : Choice2011 G)
    (c : Ctx23L D Ch) (h1930 : H1930 D) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch)
    (h847 : R847ThinCZ D) (hLN : (c.L.subgroupOf c.N).Normal)
    {K : Subgroup G} (hK : K ∈ calC D.M) (hthin : F08.Thin8 K) {x y : G}
    (hxN : x ∈ c.N) (hyN : y ∈ c.N)
    (hxZ : x ∈ Subgroup.centralizer (D.Z : Set G))
    (hyZ : y ∈ Subgroup.centralizer (D.Z : Set G))
    (hK' : x * y * x⁻¹ * y⁻¹ ∈ K) :
    ∃ i : ℕ, orderOf (x * y * x⁻¹ * y⁻¹) = 2 ^ i := by
  classical
  obtain ⟨X⟩ := nonempty_b2Data D Ch c h4 h23 h1930
  let A : Subgroup G :=
    c.N ⊓ Subgroup.normalizer (c.L : Set G) ⊓ Subgroup.centralizer (D.Z : Set G)
  have haN : ∀ a : ↥A, (a : G) ∈ c.N := fun a => (Subgroup.mem_inf.mp a.2).1.1
  have haNL : ∀ a : ↥A, (a : G) ∈ Subgroup.normalizer (c.L : Set G) :=
    fun a => (Subgroup.mem_inf.mp a.2).1.2
  have haZ : ∀ a : ↥A, (a : G) ∈ Subgroup.centralizer (D.Z : Set G) :=
    fun a => (Subgroup.mem_inf.mp a.2).2
  have hxA : x ∈ A := Subgroup.mem_inf.mpr
    ⟨Subgroup.mem_inf.mpr ⟨hxN, (le_normalizer_of_normal_subgroupOf c hLN) hxN⟩, hxZ⟩
  have hyA : y ∈ A := Subgroup.mem_inf.mpr
    ⟨Subgroup.mem_inf.mpr ⟨hyN, (le_normalizer_of_normal_subgroupOf c hLN) hyN⟩, hyZ⟩
  have hgA : x * y * x⁻¹ * y⁻¹ ∈ A :=
    A.mul_mem (A.mul_mem (A.mul_mem hxA hyA) (A.inv_mem hxA)) (A.inv_mem hyA)
  let xA : ↥A := ⟨x, hxA⟩
  let yA : ↥A := ⟨y, hyA⟩
  let gA : ↥A := ⟨x * y * x⁻¹ * y⁻¹, hgA⟩
  let χ : ↥A →* X.κ.Kˣ := detChar X h4 h23 h1930 haN haNL haZ
  have hχg : χ gA = 1 := by
    have hg_eq : gA = xA * yA * xA⁻¹ * yA⁻¹ := Subtype.ext rfl
    rw [hg_eq, map_mul, map_mul, map_mul, map_inv, map_inv]
    rw [(Commute.all (χ xA) (χ yA)).mul_inv_cancel]
    exact mul_inv_cancel (χ yA)
  have hgK : (gA : G) ∈ K := hK'
  exact exists_orderOf_eq_two_pow_of_detChar_eq_one X h4 h23 h1930 haN haNL haZ h847
    hLN hK hthin hgK (by simpa [χ] using hχg)

theorem exists_orderOf_conj_mul_inv_eq_two_pow (D : Data G) (Ch : Choice2011 G)
    (c : Ctx23L D Ch) (h1930 : H1930 D) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch)
    (h847 : R847ThinCZ D) (hLN : (c.L.subgroupOf c.N).Normal)
    {K : Subgroup G} (hK : K ∈ calC D.M) (hthin : F08.Thin8 K)
    (hKn : (K.subgroupOf D.M).Normal) {t b : G} (ht : t ∈ D.T) (hbK : b ∈ K)
    (hbN : b ∈ c.N) :
    ∃ i : ℕ, orderOf (t * b * t⁻¹ * b⁻¹) = 2 ^ i := by
  have hKM : K ≤ D.M := CFSG.Open.IsSubnormal.le hK.1
  have hM_le_NK : D.M ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).1 hKn
  have htN : t ∈ c.N :=
    (Ctx23L.sup_le_N D Ch c) ((le_sup_right : D.T ≤ c.L ⊔ D.T) ht)
  have htZ : t ∈ Subgroup.centralizer (D.Z : Set G) := uc22main1_T_le_centralizer D ht
  have hKZ : K ≤ Subgroup.centralizer (D.Z : Set G) :=
    le_centralizer_Z_of_perfect D Ch h4 h1930 c hKM hK.2.1
  have hbZ : b ∈ Subgroup.centralizer (D.Z : Set G) := hKZ hbK
  have htbK : t * b * t⁻¹ * b⁻¹ ∈ K :=
    K.mul_mem ((Subgroup.mem_normalizer_iff.mp (hM_le_NK (D.sylowM.le ht)) b).mp hbK)
      (K.inv_mem hbK)
  exact exists_orderOf_commutator_eq_two_pow D Ch c h1930 h4 h23 h847 hLN hK hthin
    htN hbN htZ hbZ htbK

end Ctx23L

end CFSG.LocalAnalysis.UniquenessCase.UC22
