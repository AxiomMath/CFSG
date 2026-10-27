module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsRootModule
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsSL3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.SemiregularBar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TIFusion
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20i
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22v
public import CFSG.RankThree.PartOne.S9.OddCore.TorsionCommon
public import CFSG.RankThree.PartOne.S9.Planes.SecondCenter

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def S23_20_2F (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx2311 D Ch, ∀ q : ℕ, q.Prime → q ≠ 2 →
    1 < CFSG.Open.pRank q (barPreimage D.M (CFSG.pCore q (Bar2 D.M))) →
    q ∉ piSet (c.CMETilde ⊓ barPreimage D.M (CFSG.pCore q (Bar2 D.M)))

private theorem uc22s2320_normalizes_CME {D : Data G} {Ch : Choice2011 G}
    (c : Ctx2311 D Ch) : D.M ≤ Subgroup.normalizer (c.CME : Set G) := by
  have hE : D.M ≤ Subgroup.normalizer (c.E : Set G) := by
    change D.M ≤ Subgroup.normalizer (conjClosure D.M c.V : Set G)
    exact uc22p22v_le_normalizer_conjClosure D.M c.V
  rw [Subgroup.le_normalizer_iff (H := D.M) (K := c.CME)]
  intro m hm x hx
  obtain ⟨hxM, hxcent⟩ := Subgroup.mem_inf.mp hx
  refine Subgroup.mem_inf.mpr ⟨D.M.mul_mem (D.M.mul_mem hm hxM) (D.M.inv_mem hm), ?_⟩
  rw [Subgroup.mem_centralizer_iff] at hxcent ⊢
  intro e he
  have he' : m⁻¹ * e * m ∈ c.E := by
    have h : m⁻¹ ∈ Subgroup.normalizer (c.E : Set G) :=
      (Subgroup.normalizer (c.E : Set G)).inv_mem (hE hm)
    have := (Subgroup.mem_normalizer_iff.mp h e).mp he
    simpa using this
  calc e * (m * x * m⁻¹) = m * ((m⁻¹ * e * m) * x) * m⁻¹ := by group
    _ = m * (x * (m⁻¹ * e * m)) * m⁻¹ := by rw [hxcent _ he']
    _ = (m * x * m⁻¹) * e := by group

private theorem uc22s2320_conj_Z_le_V {D : Data G} {Ch : Choice2011 G}
    (c : Ctx2311 D Ch) {g : G} (hgL : g ∈ c.L) :
    D.Z.map (MulAut.conj g).toMonoidHom ≤ c.V := by
  have hLN : c.L ≤ c.N := by
    have hNle : c.L ⊔ D.T ≤ c.N := by
      have hmem : c.N ∈ calMOf (c.L ⊔ D.T) := by rw [c.hN]; simp
      exact hmem.2
    exact (le_sup_left : c.L ≤ c.L ⊔ D.T).trans hNle
  have hle : D.Z.map (MulAut.conj g).toMonoidHom ≤ conjClosure c.N D.Z :=
    le_iSup₂_of_le (f := fun K (_ : K ∈ conjSetOf c.N D.Z) => K) _
      ⟨g, hLN hgL, rfl⟩ le_rfl
  simpa [Ctx23L.V] using hle

private theorem uc22s2320_element (D : Data G) (Ch : Choice2011 G)
    (h19 : S23_19 D Ch) (h201 : S23_20_1 D Ch) (h1930 : H1930 D)
    (c : Ctx2311 D Ch) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hpi : q ∈ piSet (c.CMETilde ⊓ barPreimage D.M (CFSG.pCore q (Bar2 D.M)))) :
    ∃ x : ↥(c.CMETilde ⊓ barPreimage D.M (CFSG.pCore q (Bar2 D.M))),
      (x : G) ∈ c.CME ∧ (x : G) ∈ barPreimage D.M (CFSG.pCore q (Bar2 D.M)) ∧
        orderOf (x : G) = q ∧ q ∉ D.sig := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  rw [piSet] at hpi
  obtain ⟨-, hdvd⟩ := hpi
  obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(c.CMETilde ⊓ barPreimage D.M (CFSG.pCore q (Bar2 D.M)))) q hdvd
  have hxmem : (x : G) ∈ c.CMETilde ⊓ barPreimage D.M (CFSG.pCore q (Bar2 D.M)) := x.2
  have hxPq : (x : G) ∈ barPreimage D.M (CFSG.pCore q (Bar2 D.M)) :=
    (Subgroup.mem_inf.mp hxmem).2
  have hxordG : orderOf (x : G) = q := (Subgroup.orderOf_coe x).trans hxord
  have hxodd : Odd (orderOf (x : G)) := by
    rw [hxordG]
    exact hq.odd_of_ne_two hq2
  have hxop : (x : G) ∈ CFSG.Quasithin.opResidual 2 c.CMETilde :=
    CFSG.Quasithin.mem_opResidual_of_coprime hxmem.1 (Nat.coprime_two_right.mpr hxodd)
  rw [h19 h1930 c] at hxop
  have hxCME : (x : G) ∈ c.CME := CFSG.Quasithin.opResidual_le 2 c.CME hxop
  have hqsig : q ∉ D.sig := by
    intro hqsig
    have hdvdCME : q ∣ Nat.card c.CMETilde :=
      hdvd.trans (Subgroup.card_dvd_of_le (inf_le_left :
        c.CMETilde ⊓ barPreimage D.M (CFSG.pCore q (Bar2 D.M)) ≤ c.CMETilde))
    have hpiCME : q ∈ piSet c.CMETilde := by
      rw [piSet]
      exact ⟨hq, hdvdCME⟩
    have hmem : q ∈ D.sig ∩ piSet c.CMETilde := ⟨hqsig, hpiCME⟩
    rw [h201 h1930 c] at hmem
    simpa using hmem
  exact ⟨x, hxCME, hxPq, hxordG, hqsig⟩

private theorem uc22s2320_pq_facts (D : Data G) {q p : ℕ} (hq : q.Prime)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ≠ q) :
    (barPreimage D.M (CFSG.pCore q (Bar2 D.M)) ≤ D.M) ∧
      (((barPreimage D.M (CFSG.pCore q (Bar2 D.M))).subgroupOf D.M).Normal) ∧
      (barPreimage D.M (CFSG.pCore q (Bar2 D.M)) ≤ CFSG.Open.relPPrimeCore p D.M) := by
  haveI hcore : (CFSG.pCore q (Bar2 D.M)).Normal := CFSG.pCore_normal
  have hPqM : barPreimage D.M (CFSG.pCore q (Bar2 D.M)) ≤ D.M :=
    uc22p21c_barPreimage_le D.M _
  have hPqNormM : D.M ≤ Subgroup.normalizer
      (barPreimage D.M (CFSG.pCore q (Bar2 D.M)) : Set G) :=
    uc22p22u_barPreimage_normalizes (M := D.M) (D := CFSG.pCore q (Bar2 D.M))
  have hPqN : ((barPreimage D.M (CFSG.pCore q (Bar2 D.M))).subgroupOf D.M).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hPqNormM
  have hPqRel : barPreimage D.M (CFSG.pCore q (Bar2 D.M)) ≤
      CFSG.Open.relPPrimeCore p D.M :=
    barPreimage_le_relPPrimeCore hcore (CFSG.pCore_isPGroup) hp hq hpq hp2
  exact ⟨hPqM, hPqN, hPqRel⟩

private theorem uc22s2320_sylow (D : Data G) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {Pq : Subgroup G} (hPqM : Pq ≤ D.M) {x : G} (hxPq : x ∈ Pq)
    (hxordG : orderOf x = q) (hPqrank : 1 < CFSG.Open.pRank q Pq) :
    ∃ Q0 : Subgroup G, CFSG.ABGLocalTools.IsSylowOf q Q0 Pq ∧ x ∈ Q0 ∧
      Q0 ≤ D.M ∧ IsPGroup q Q0 ∧ ¬ IsCyclic ↥Q0 := by
  haveI : Fact q.Prime := ⟨hq⟩
  let X : Subgroup G := Subgroup.zpowers x
  have hXPq : X ≤ Pq := Subgroup.zpowers_le.mpr hxPq
  have hXq : IsPGroup q X := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hxordG]
    simp
  obtain ⟨S, hXS⟩ := (hXq.comap_subtype (K := Pq)).exists_le_sylow
  let Q0 : Subgroup G := (S : Subgroup ↥Pq).map Pq.subtype
  have hQ0syl : CFSG.ABGLocalTools.IsSylowOf q Q0 Pq := ⟨S, rfl⟩
  have hxS : (⟨x, hxPq⟩ : ↥Pq) ∈ (S : Subgroup ↥Pq) :=
    hXS (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers x))
  have hxQ0 : x ∈ Q0 := Subgroup.mem_map.mpr ⟨⟨x, hxPq⟩, hxS, rfl⟩
  have hQ0M : Q0 ≤ D.M := hQ0syl.le.trans hPqM
  have hQ0p : IsPGroup q Q0 := hQ0syl.isPGroup
  have hQ0nc : ¬ IsCyclic ↥Q0 := by
    intro hcyc
    letI : IsCyclic ↥Q0 := hcyc
    have hcycTop : IsCyclic (⊤ : Subgroup ↥Q0) := Subgroup.isCyclic ⊤
    have h1 : CFSG.Open.pRank q (⊤ : Subgroup ↥Q0) ≤ 1 :=
      CFSG.SectionRank.pRank_le_one_of_isCyclic hq hcycTop
    have h2 : CFSG.Open.pRank q (⊤ : Subgroup ↥Q0) = CFSG.Open.pRank q Q0 :=
      (CFSG.SectionRank.pRank_eq_pRank_top_subgroup Q0).symm
    have h3 : 2 ≤ CFSG.Open.pRank q Q0 :=
      (Nat.succ_le_of_lt hPqrank).trans (uc22p22q_pRank_le_sylow hQ0syl)
    omega
  exact ⟨Q0, hQ0syl, hxQ0, hQ0M, hQ0p, hQ0nc⟩

private theorem uc22s2320_characteristic_q {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {Q0 : Subgroup G} (hQ0p : IsPGroup q Q0) (hQ0nc : ¬ IsCyclic ↥Q0) :
    ∃ Q : Subgroup G, Q ≤ Q0 ∧ (Q.subgroupOf Q0).Characteristic ∧ ¬ IsCyclic Q ∧
      (∀ y ∈ Q, y ^ q = 1) ∧ ⁅⁅Q, Q⁆, Q⁆ = ⊥ ∧
      (∀ y : ↥Q0, y ∈ Subgroup.center ↥Q0 → y ^ q = 1 → (y : G) ∈ Q) := by
  let W : Subgroup ↥Q0 :=
    Subgroup.closure {y : ↥Q0 | y ∈ Subgroup.upperCentralSeries ↥Q0 2 ∧ y ^ q = 1}
  obtain ⟨hWchar, hWmem, hWcentral, hWnc'⟩ :=
    CFSG.RankThree.PartOne.pgOddSecondCenterPrimeTorsion ↥Q0 q hq hq2 hQ0p
  have hWexp : ∀ y ∈ W, y ^ q = 1 := fun y hy => ((hWmem y).1 hy).2
  have hWnc : ¬ IsCyclic W := hWnc' hQ0nc
  have hWclass : ⁅⁅W, W⁆, W⁆ = ⊥ := by
    refine CFSG.RankThree.PartOne.Torsion37.commutator_commutator_eq_bot_of_central
      (W := W) (Q := ⊤) le_top ?_
    intro w hw g _ u _
    exact Subgroup.mem_center_iff.mp (hWcentral w hw g).1 u
  let Q : Subgroup G := W.map Q0.subtype
  have hQsub : Q.subgroupOf Q0 = W :=
    Subgroup.comap_map_eq_self_of_injective Q0.subtype_injective W
  have hQchar : (Q.subgroupOf Q0).Characteristic := by
    rw [hQsub]
    exact hWchar
  have hQnc : ¬ IsCyclic Q := by
    intro hcyc
    apply hWnc
    let e := W.equivMapOfInjective Q0.subtype Q0.subtype_injective
    exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
  have hQexp : ∀ y ∈ Q, y ^ q = 1 := by
    rintro y ⟨w, hw, rfl⟩
    simpa using congrArg Q0.subtype (hWexp w hw)
  have hQclass : ⁅⁅Q, Q⁆, Q⁆ = ⊥ := by
    change ⁅⁅W.map Q0.subtype, W.map Q0.subtype⁆, W.map Q0.subtype⁆ = ⊥
    rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, hWclass, Subgroup.map_bot]
  have hQcenter : ∀ y : ↥Q0, y ∈ Subgroup.center ↥Q0 → y ^ q = 1 → (y : G) ∈ Q := by
    intro y hy hya
    have hy' : y ∈ Subgroup.upperCentralSeries ↥Q0 1 := by
      rwa [Subgroup.upperCentralSeries_one]
    have hUZ : y ∈ Subgroup.upperCentralSeries ↥Q0 2 :=
      Subgroup.upperCentralSeries_mono ↥Q0 (Nat.le_succ 1) hy'
    exact Subgroup.mem_map.mpr ⟨y, (hWmem y).mpr ⟨hUZ, hya⟩, rfl⟩
  exact ⟨Q, Subgroup.map_subtype_le W, hQchar, hQnc, hQexp, hQclass, hQcenter⟩

private theorem uc22s2320_center_element {D : Data G} {Ch : Choice2011 G}
    (c : Ctx2311 D Ch) {q : ℕ} (hq : q.Prime) {Q0 : Subgroup G}
    (hQ0M : Q0 ≤ D.M) (hQ0p : IsPGroup q Q0) {x : G}
    (hxCME : x ∈ c.CME) (hxQ0 : x ∈ Q0) (hxordG : orderOf x = q) :
    ∃ z : ↥Q0, z ∈ (c.CME ⊓ Q0).subgroupOf Q0 ∧ z ∈ Subgroup.center ↥Q0 ∧
      z ≠ 1 ∧ orderOf z = q := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hx1 : x ≠ 1 := by
    intro h
    have hq1 : q = 1 := by rw [← hxordG, h, orderOf_one]
    exact hq.ne_one hq1
  have hQ0CME : Q0 ≤ Subgroup.normalizer (c.CME : Set G) :=
    hQ0M.trans (uc22s2320_normalizes_CME c)
  let N : Subgroup G := c.CME ⊓ Q0
  haveI hNn : (N.subgroupOf Q0).Normal := by
    have h := Subgroup.normal_subgroupOf_of_le_normalizer hQ0CME
    simpa [N, Subgroup.inf_subgroupOf_right] using h
  have hxN : x ∈ N := Subgroup.mem_inf.mpr ⟨hxCME, hxQ0⟩
  have hHne : (N.subgroupOf Q0) ≠ ⊥ := by
    intro hbot
    have hxH : (⟨x, hxQ0⟩ : ↥Q0) ∈ N.subgroupOf Q0 :=
      Subgroup.mem_subgroupOf.mpr hxN
    rw [hbot] at hxH
    exact hx1 (congrArg Subtype.val (Subgroup.mem_bot.mp hxH))
  haveI : Group.IsNilpotent ↥Q0 := hQ0p.isNilpotent
  have hZne : N.subgroupOf Q0 ⊓ Subgroup.center ↥Q0 ≠ ⊥ :=
    Group.IsNilpotent.inf_center_ne_bot_of_normal hHne
  obtain ⟨w, hwne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZne
  let z : ↥Q0 := (w : ↥Q0)
  have hzN : z ∈ N.subgroupOf Q0 := (Subgroup.mem_inf.mp w.2).1
  have hzcenter : z ∈ Subgroup.center ↥Q0 := (Subgroup.mem_inf.mp w.2).2
  have hzne : z ≠ 1 := fun h => hwne (Subtype.ext h)
  have hzq : q ∣ orderOf z := hQ0p.dvd_orderOf hzne
  let z0 : ↥Q0 := z ^ (orderOf z / q)
  have hz0ord : orderOf z0 = q := orderOf_pow_orderOf_div (orderOf_pos z).ne' hzq
  have hz0N : z0 ∈ N.subgroupOf Q0 := (N.subgroupOf Q0).pow_mem hzN _
  have hz0center : z0 ∈ Subgroup.center ↥Q0 := (Subgroup.center ↥Q0).pow_mem hzcenter _
  have hz0ne : z0 ≠ 1 := by
    intro h
    have h1 : orderOf z0 = 1 := by rw [h, orderOf_one]
    rw [hz0ord] at h1
    exact hq.ne_one h1
  exact ⟨z0, hz0N, hz0center, hz0ne, hz0ord⟩

private theorem uc22s2320_z_mem_conj_M (D : Data G) (Ch : Choice2011 G)
    (h4 : S23_4 D Ch) (h1930 : H1930 D) (c : Ctx2311 D Ch)
    {g : G} (hgL : g ∈ c.L) {z : G} (hzCME : z ∈ c.CME) :
    z ∈ D.M.map (MulAut.conj g).toMonoidHom := by
  have hVE : c.V ≤ c.E := by
    change c.V ≤ conjClosure D.M c.V
    exact uc22p22v_le_conjClosure D.M c.V
  have hZgE : D.Z.map (MulAut.conj g).toMonoidHom ≤ c.E :=
    (uc22s2320_conj_Z_le_V c hgL).trans hVE
  have hzcentE : z ∈ Subgroup.centralizer (c.E : Set G) := (Subgroup.mem_inf.mp hzCME).2
  have hzcentZg : z ∈ Subgroup.centralizer
      ((D.Z.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) :=
    Subgroup.centralizer_le (show ((D.Z.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) ⊆
      (c.E : Set G) from hZgE) hzcentE
  have hzNZg : z ∈ Subgroup.normalizer
      ((D.Z.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) :=
    Subgroup.centralizer_le_normalizer _ hzcentZg
  have hNZ : Subgroup.normalizer (D.Z : Set G) = D.M := by
    rw [← (h4 h1930 c.toCtx23L).1]
    exact Data.normalizer_U_eq D
  have hmap := Subgroup.map_equiv_normalizer_eq D.Z (MulAut.conj g)
  rw [hNZ] at hmap
  rw [← hmap] at hzNZg
  exact hzNZg

private theorem uc22s2320_final_contradiction (D : Data G) (Ch : Choice2011 G)
    (h71 : S23_7_1 D Ch) (h1930 : H1930 D) (c : Ctx2311 D Ch)
    {q p : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hp : p ∈ D.sig)
    {Pq Q0 Q : Subgroup G} (hPqM : Pq ≤ D.M) (hPqN : (Pq.subgroupOf D.M).Normal)
    (hPqRel : Pq ≤ relPPrimeCore p D.M)
    (hQ0syl : CFSG.ABGLocalTools.IsSylowOf q Q0 Pq) (hQ0M : Q0 ≤ D.M)
    (hQ0p : IsPGroup q Q0) (hQle : Q ≤ Q0) (hQchar : (Q.subgroupOf Q0).Characteristic)
    (hQnc : ¬ IsCyclic Q) (hQexp : ∀ y ∈ Q, y ^ q = 1) (hQcl : ⁅⁅Q, Q⁆, Q⁆ = ⊥)
    {g : G} (hgM : g ∉ D.M) {z : G} (hzQ : z ∈ Q)
    (hzMg : z ∈ D.M.map (MulAut.conj g).toMonoidHom) (hz1 : z ≠ 1) : False := by
  have hQM : Q ≤ D.M := hQle.trans hQ0M
  have hQp : IsPGroup q Q := hQ0p.to_le hQle
  have hQinf : Q ≤ D.M ⊓ Subgroup.normalizer (Q0 : Set G) :=
    le_inf hQM (hQle.trans (Subgroup.le_normalizer))
  have hQcharNorm : Subgroup.normalizer (Q0 : Set G) ≤ Subgroup.normalizer (Q : Set G) := by
    have h := CFSG.RankThreeCoreUniqueness.Helpers.normalizer_le_normalizer_characteristic_map
      Q0 (Q.subgroupOf Q0) hQchar
    have hmap : (Q.subgroupOf Q0).map Q0.subtype = Q := Subgroup.map_subgroupOf_eq_of_le hQle
    rwa [hmap] at h
  have hQnormal : (Q.subgroupOf (D.M ⊓ Subgroup.normalizer (Q0 : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQinf).mpr fun y hy => hQcharNorm hy.2
  have hdisj : Q ⊓ D.M.map (MulAut.conj g).toMonoidHom = ⊥ :=
    h71 h1930 c.toCtx23L q hq hq2 Q hQM hQp hQnc hQexp hQcl p hp Pq hPqM hPqN hPqRel
      Q0 hQ0syl hQinf hQnormal g hgM
  have hmem : z ∈ Q ⊓ D.M.map (MulAut.conj g).toMonoidHom := ⟨hzQ, hzMg⟩
  rw [hdisj] at hmem
  exact hz1 (Subgroup.mem_bot.mp hmem)

theorem s23_20_2F_of (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch) (h71 : S23_7_1 D Ch)
    (h19 : S23_19 D Ch) (h201 : S23_20_1 D Ch) (hsig : D.sig.Nonempty) : S23_20_2F D Ch := by
  intro h1930 c q hq hq2 hPqrank hpi
  obtain ⟨x, hxCME, hxPq, hxordG, hqsig⟩ :=
    uc22s2320_element D Ch h19 h201 h1930 c hq hq2 hpi
  obtain ⟨p, hp⟩ := hsig
  have hpp : p.Prime := (D.sig_prime p hp).1
  have hp2 : p ≠ 2 := (D.sig_prime p hp).2
  have hpq : p ≠ q := fun h => hqsig (h ▸ hp)
  obtain ⟨hPqM, hPqN, hPqRel⟩ := uc22s2320_pq_facts (D := D) hq hpp hp2 hpq
  obtain ⟨Q0, hQ0syl, hxQ0, hQ0M, hQ0p, hQ0nc⟩ :=
    uc22s2320_sylow D hq hq2 hPqM hxPq hxordG hPqrank
  obtain ⟨Q, hQle, hQchar, hQnc, hQexp, hQcl, hQcenter⟩ :=
    uc22s2320_characteristic_q hq hq2 hQ0p hQ0nc
  have hLnotM : ¬ c.L ≤ D.M := uc22p20i_not_le_M D c.hL.1
  obtain ⟨g, hgL, hgM⟩ : ∃ g ∈ c.L, g ∉ D.M := by
    by_contra h
    push Not at h
    exact hLnotM h
  obtain ⟨z, hzN, hzcenter, hzne, hzord⟩ :=
    uc22s2320_center_element c hq hQ0M hQ0p hxCME hxQ0 hxordG
  have hzCME : (z : G) ∈ c.CME :=
    (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hzN)).1
  have hzq : z ^ q = 1 := by
    have h := pow_orderOf_eq_one z
    rwa [hzord] at h
  have hzQ : (z : G) ∈ Q := hQcenter z hzcenter hzq
  have hz1 : (z : G) ≠ 1 := fun h => hzne (Subtype.ext h)
  have hzMg : (z : G) ∈ D.M.map (MulAut.conj g).toMonoidHom :=
    uc22s2320_z_mem_conj_M D Ch h4 h1930 c hgL hzCME
  exact uc22s2320_final_contradiction D Ch h71 h1930 c hq hq2 hp hPqM hPqN hPqRel
    hQ0syl hQ0M hQ0p hQle hQchar hQnc hQexp hQcl hgM hzQ hzMg hz1

end CFSG.LocalAnalysis.UniquenessCase.UC22
