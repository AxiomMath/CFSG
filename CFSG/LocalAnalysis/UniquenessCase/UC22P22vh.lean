module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S22b
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21p
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
import CFSG.LocalAnalysis.UniquenessCase.UC22P22ve
import CFSG.LocalAnalysis.UniquenessCase.UC22P22vf
import CFSG.LocalAnalysis.UniquenessCase.UC22P22vc
import CFSG.LocalAnalysis.UniquenessCase.UC22P22vd
import CFSG.LocalAnalysis.UniquenessCase.UC22P22o
import CFSG.LocalAnalysis.UniquenessCase.UC22P21b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22p22vh_contra1 (D : Data G) (Ch : Choice2011 G) (h1930 : H1930 D) (h9 : S22_9 D Ch)
    (c : Ctx22b D Ch) {Vmod : Type} [AddCommGroup Vmod] [Module (ZMod 2) Vmod] [Finite Vmod]
    (e : ↥c.V ≃* Multiplicative Vmod) (ρ : Representation (ZMod 2) (MBar D.M c.V) Vmod)
    (hc : ConjModule D.M c.V e ρ) : ¬ c.n + 1 < F05.mGV ρ :=
  fun h => h9 h1930 c ((mbarGT_bot_iff_lt_mGV D.M c.V c.hVM
    (uc22br4_isElemAbelian_of_equiv c.V e) e ρ hc (c.n + 1)).2 h)

private theorem uc22p22vh_pRank_mbarImage_le {M V Q : Subgroup G} (hV : M ≤ normalizer (V : Set G))
    (hQM : Q ≤ M) (hQV : Q ⊓ centralizer (V : Set G) = ⊥) {q : ℕ} (hq : 1 < q) :
    CFSG.Open.pRank q (mbarImage M V Q) ≤ CFSG.Open.pRank q M := by
  have hker : (uc22br4_phi M V Q hQM).ker = ⊥ := by
    rw [uc22br4_ker_phi M V Q hV hQM, eq_bot_iff]
    intro x hx
    have hx1 : (x : G) ∈ Q ⊓ centralizer (V : Set G) := Subgroup.mem_inf.2 ⟨x.2, hx⟩
    rw [hQV] at hx1
    exact Subtype.ext (Subgroup.mem_bot.1 hx1)
  have hinj : Function.Injective (uc22br4_phi M V Q hQM) := (MonoidHom.ker_eq_bot_iff _).1 hker
  have h1 := CFSG.SectionRank.pRank_top_eq_of_mulEquiv hq (MonoidHom.ofInjective hinj)
  rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup, ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup,
    uc22br4_range_phi] at h1
  exact h1.symm.le.trans (CFSG.SectionRank.pRank_mono hq hQM)

theorem uc22p22vh_contra2 (D : Data G) (Ch : Choice2011 G) (h1930 : H1930 D)
    (hV : S22_V D Ch) (h8 : S22_8 D Ch) (h10 : S22_10 D Ch) (h1110 : R1110W D)
    (hSg : UC6S846.SigmaStd D) (c : Ctx22b D Ch) :
    ¬ ∃ q ∈ F05.alphaSet (MBar D.M c.V), q ∣ Nat.card (mbarImage D.M c.V c.B0) ∧
      ∃ Q ∈ F05.calQ (G := MBar D.M c.V) q, 3 < CFSG.Open.pRank q Q := by
  rintro ⟨q, hqα, hqB, Qb, hQb, h3⟩
  have hq : q.Prime := hqα.1
  have hodd : Odd (Nat.card c.B0) :=
    uc22p22f_odd_card_B ({ c.toCtx21 with B := c.B0, hB := c.hB0, hle := le_rfl } : Ctx21 D Ch)
  have hqB0 : q ∣ Nat.card c.B0 := by
    refine hqB.trans ?_
    rw [uc22br4_card_mbarImage D.M c.V c.B0 c.hVM c.hBM]
    exact Subgroup.index_dvd_card _
  have hq2 : q ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hqB0)
  obtain ⟨Q, hQM, -, -, -, -, hQV, hmb, -⟩ := uc22p22ve_exists_lift D Ch h1930 hV h10 h1110 c q hq hq2
    Qb hQb ⊥ bot_le (Or.inr IsPGroup.of_bot)
  have h4 : 4 ≤ CFSG.Open.pRank q D.M := by
    have h := uc22p22vh_pRank_mbarImage_le c.hVM hQM hQV hq.one_lt
    rw [hmb] at h
    exact h3.trans_le h
  exact uc22p22vf_rank_bridge D Ch h8 hSg h1930 c ⟨hq, hqB0⟩ h4

private theorem uc22p22vh_mem_uniqueSet_of_sp {M X : Subgroup G} {q : ℕ} (hq : q.Prime)
    (hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded q M) (hXM : X ≤ M) (hXq : IsPGroup q ↥X)
    (hX1 : X ≠ ⊥) : X ∈ uniqueSet M := by
  haveI : Fact q.Prime := ⟨hq⟩
  refine ⟨hXM, fun g hg => ?_⟩
  by_cases hgM : g ∈ M
  · exact Subgroup.mem_normalizer_iff_map_conj_eq.1 (Subgroup.le_normalizer hgM)
  · exfalso
    refine hsp.2.2 g hgM ?_
    have hqX : q ∣ Nat.card X := by
      rcases hXq.card_eq_or_dvd with h | h
      · exact absurd (Subgroup.card_eq_one.1 h) hX1
      · exact h
    exact hqX.trans (Subgroup.card_dvd_of_le (le_inf hXM hg))

private theorem uc22p22vh_exists_cent_elt {M V Q A : Subgroup G} (hV : M ≤ normalizer (V : Set G))
    (hAM : A ≤ M) (hAQ : A ≤ normalizer (Q : Set G)) (hQV : Q ⊓ centralizer (V : Set G) = ⊥)
    {xb : MBar M V} (hxQ : xb ∈ mbarImage M V Q)
    (hxA : xb ∈ centralizer ((mbarImage M V A : Subgroup (MBar M V)) : Set (MBar M V)))
    (hx1 : xb ≠ 1) : ∃ x ∈ Q, x ≠ 1 ∧ ∀ a ∈ A, a * x = x * a := by
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hxQ
  have hyQ : (y : G) ∈ Q := hy
  have hy' : (QuotientGroup.mk y : MBar M V) = xb := hyx
  refine ⟨y, hyQ, fun h => hx1 ?_, fun a ha => ?_⟩
  · rw [← hy', show y = 1 from Subtype.ext h]
    rfl
  · have haM : a ∈ M := hAM ha
    have hab : (QuotientGroup.mk ⟨a, haM⟩ : MBar M V) ∈ mbarImage M V A :=
      Subgroup.mem_map.2 ⟨⟨a, haM⟩, ha, rfl⟩
    have h1 := Subgroup.mem_centralizer_iff.1 hxA _ hab
    rw [← hy'] at h1
    have h2 : (QuotientGroup.mk ((⟨a, haM⟩ : ↥M) * y * (⟨a, haM⟩ : ↥M)⁻¹ * y⁻¹) : MBar M V) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        QuotientGroup.mk_inv, h1, mul_inv_cancel_right, mul_inv_cancel]
    have h3 : a * y * a⁻¹ * (y : G)⁻¹ ∈ centralizer (V : Set G) := (uc22br_gt_mk_eq_one_iff hV _).1 h2
    have h4 : a * y * a⁻¹ * (y : G)⁻¹ ∈ Q :=
      Q.mul_mem ((Subgroup.mem_normalizer_iff.1 (hAQ ha) y).1 hyQ) (Q.inv_mem hyQ)
    have h5 : a * y * a⁻¹ * (y : G)⁻¹ ∈ Q ⊓ centralizer (V : Set G) := Subgroup.mem_inf.2 ⟨h4, h3⟩
    rw [hQV, Subgroup.mem_bot] at h5
    exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h5)

private theorem uc22p22vh_invertedIn_mbarImage {M V B : Subgroup G} (hM : InvertedIn M B) :
    F05.InvertedIn ⊤ (mbarImage M V B) := by
  obtain ⟨m, hmM, hm⟩ := hM
  refine ⟨QuotientGroup.mk ⟨m, hmM⟩, Subgroup.mem_top _, fun b hb => ?_⟩
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hb
  have hyB : (y : G) ∈ B := hy
  have e : (⟨m, hmM⟩ : ↥M) * y * (⟨m, hmM⟩ : ↥M)⁻¹ = y⁻¹ := Subtype.ext (hm y hyB)
  show (QuotientGroup.mk ⟨m, hmM⟩ : MBar M V) * QuotientGroup.mk y *
    (QuotientGroup.mk ⟨m, hmM⟩ : MBar M V)⁻¹ = (QuotientGroup.mk y)⁻¹
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, e, QuotientGroup.mk_inv]

theorem uc22p22vh_contra3 (D : Data G) (Ch : Choice2011 G) (h1930 : H1930 D)
    (hV : S22_V D Ch) (h8 : S22_8 D Ch) (h10 : S22_10 D Ch) (h1110 : R1110W D)
    (hSg : UC6S846.SigmaStd D) (c : Ctx22b D Ch) (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2)
    (P : Subgroup (MBar D.M c.V))
    (hP : P ∈ F05.calQ (G := MBar D.M c.V) q)
    (hPB : P ⊓ centralizer ((mbarImage D.M c.V c.B0 : Subgroup (MBar D.M c.V)) :
      Set (MBar D.M c.V)) ≠ ⊥) (h3 : 3 < CFSG.Open.pRank q P) :
    F05.InvertedIn ⊤ (mbarImage D.M c.V c.B0) := by
  by_cases hB0bot : c.B0 = ⊥
  · refine ⟨1, Subgroup.mem_top _, fun b hb => ?_⟩
    rw [hB0bot] at hb
    unfold mbarImage at hb
    rw [Subgroup.bot_subgroupOf, Subgroup.map_bot, Subgroup.mem_bot] at hb
    rw [hb, inv_one, mul_one, mul_one]
  obtain ⟨Q₁, hQ₁M, -, -, -, -, hQ₁V, hmb₁, -⟩ := uc22p22ve_exists_lift D Ch h1930 hV h10 h1110 c q hq hq2
    P hP ⊥ bot_le (Or.inr IsPGroup.of_bot)
  have h4 : 4 ≤ CFSG.Open.pRank q D.M := by
    have h := uc22p22vh_pRank_mbarImage_le c.hVM hQ₁M hQ₁V hq.one_lt
    rw [hmb₁] at h
    exact h3.trans_le h
  have hqσ : q ∈ D.sig := hSg.four_mem q hq hq2 h4
  have hqnd : ¬ q ∣ Nat.card c.B0 := fun hd =>
    uc22p22vf_rank_bridge D Ch h8 hSg h1930 c ⟨hq, hd⟩ h4
  have hodd : Odd (Nat.card c.B0) :=
    uc22p22f_odd_card_B ({ c.toCtx21 with B := c.B0, hB := c.hB0, hle := le_rfl } : Ctx21 D Ch)
  obtain ⟨Q, hQM, hQp, -, -, -, hQV, hmb, -, -, -, hBQ⟩ := uc22p22ve_exists_lift D Ch h1930 hV h10 h1110
    c q hq hq2 P hP c.B0 c.hBM (Or.inl ⟨hodd, c.hB0.2.1, hqnd⟩)
  obtain ⟨⟨xb, hxb⟩, hxb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hPB
  obtain ⟨x, hxQ, hx1, hcomm⟩ := uc22p22vh_exists_cent_elt c.hVM c.hBM hBQ hQV
    (hmb ▸ (Subgroup.mem_inf.1 hxb).1) (Subgroup.mem_inf.1 hxb).2 (fun h => hxb1 (Subtype.ext h))
  have hXne : Subgroup.zpowers x ≠ ⊥ := fun h => hx1 (Subgroup.zpowers_eq_bot.1 h)
  have hXQ : Subgroup.zpowers x ≤ Q := Subgroup.zpowers_le.2 hxQ
  have hXq : IsPGroup q ↥(Subgroup.zpowers x) := hQp.to_le hXQ
  have hXnorm : Subgroup.zpowers x ≤ normalizer (c.B0 : Set G) := by
    intro y hy
    refine Subgroup.centralizer_le_normalizer (c.B0 : Set G) ?_
    have hxc : x ∈ centralizer (c.B0 : Set G) := Subgroup.mem_centralizer_iff.2 fun b hb => hcomm b hb
    exact Subgroup.zpowers_le.2 hxc hy
  have hXuniq : Subgroup.zpowers x ∈ uniqueSet D.M :=
    uc22p22vh_mem_uniqueSet_of_sp hq (hSg.sig1_sp q ((h8 h1930 c) ▸ hqσ)) (hXQ.trans hQM) hXq hXne
  exact uc22p22vh_invertedIn_mbarImage (s21_10 D Ch h1930
    ({ c.toCtx21 with B := c.B0, hB := c.hB0, hle := le_rfl } : Ctx21 D Ch) c.B0 hB0bot le_rfl
    (Subgroup.zpowers x) hXne ⟨q, hq, hXq⟩ hXnorm hXuniq)

open scoped commutatorElement in
private theorem uc22p22vh_commutator_le_centralizer {H : Type*} [Group H] (X : Subgroup H) [X.Normal]
    [IsCyclic ↥X] : _root_.commutator H ≤ Subgroup.centralizer (X : Set H) := by
  have hcomm : ∀ a b : MulAut ↥X, a * b = b * a := fun a b =>
    (IsCyclic.mulAutMulEquiv ↥X).injective (by rw [map_mul, map_mul, mul_comm])
  rw [_root_.commutator_def, Subgroup.commutator_le]
  intro g₁ _ g₂ _
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have h1 : (MulAut.conjNormal ⁅g₁, g₂⁆ : MulAut ↥X) = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm _ _
  have h2 := congrArg (fun φ : MulAut ↥X => ((φ ⟨x, hx⟩ : ↥X) : H)) h1
  simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h2
  exact (mul_inv_eq_iff_eq_mul.1 h2).symm

private theorem uc22p22vh_odd_card_cyclic {H : Type*} [Group H] [Finite H]
    (hO2 : CFSG.pCore 2 H = ⊥) (X : Subgroup H) [X.Normal] [IsCyclic ↥X] :
    Odd (Nat.card ↥X) := by
  by_contra hodd
  have h2 : 2 ∣ Nat.card ↥X := even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hodd)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) 2 h2
  set Y : Subgroup ↥X := Subgroup.zpowers t with hY
  have hYcard : Nat.card ↥Y = 2 := by rw [hY, Nat.card_zpowers, ht]
  have hYchar : Y.Characteristic := by
    rw [Subgroup.characteristic_iff_map_eq]
    intro φ
    rw [IsCyclic.subgroup_eq_iff_card_eq, Subgroup.card_map_of_injective φ.injective]
  have hNnorm : (Y.map X.subtype).Normal := by
    refine Subgroup.normalizer_eq_top_iff.1 (eq_top_iff.2 ?_)
    calc (⊤ : Subgroup H) = Subgroup.normalizer (X : Set H) := (Subgroup.normalizer_eq_top X).symm
      _ ≤ _ := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic Y
  have hNp : IsPGroup 2 ↥(Y.map X.subtype) :=
    (IsPGroup.of_card (n := 1) (by rw [hYcard, pow_one]) : IsPGroup 2 ↥Y).map X.subtype
  have hle : Y.map X.subtype ≤ CFSG.pCore 2 H := CFSG.LieType.BorelTits.le_pCore 2 hNnorm hNp
  rw [hO2] at hle
  have ht1 : (t : H) ∈ Y.map X.subtype := Subgroup.mem_map.2 ⟨t, Subgroup.mem_zpowers t, rfl⟩
  have ht3 : t = 1 := Subtype.ext (Subgroup.mem_bot.1 (hle ht1))
  rw [ht3, orderOf_one] at ht
  exact absurd ht (by norm_num)

private theorem uc22p22vh_normal_fitting (H : Type*) [Group H] :
    ((CFSG.fittingSubgroup ↥(_root_.commutator H)).map (_root_.commutator H).subtype).Normal := by
  refine Subgroup.normalizer_eq_top_iff.1 (eq_top_iff.2 ?_)
  calc (⊤ : Subgroup H) = Subgroup.normalizer ((_root_.commutator H : Subgroup H) : Set H) :=
      (Subgroup.normalizer_eq_top (_root_.commutator H)).symm
    _ ≤ _ := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (CFSG.fittingSubgroup ↥(_root_.commutator H))

theorem uc22p22vh_centralized_of_cyclic (D : Data G) (Ch : Choice2011 G) (h1930 : H1930 D)
    (hV : S22_V D Ch) (c : Ctx22b D Ch)
    (hF : IsCyclic ↥(CFSG.fittingSubgroup ↥(_root_.commutator (MBar D.M c.V)))) :
    mbarImage D.M c.V c.B ≤
      Subgroup.centralizer
        (((CFSG.fittingSubgroup ↥(_root_.commutator (MBar D.M c.V))).map
          (_root_.commutator (MBar D.M c.V)).subtype : Subgroup (MBar D.M c.V)) :
          Set (MBar D.M c.V)) := by
  have hO2 : CFSG.pCore 2 (MBar D.M c.V) = ⊥ :=
    (uc22br4_pCore_bot_iff D.M c.V c.hVM).2 (hV h1930 c).1.2.2
  have hel : IsElemAbelian 2 c.V := (uc22p22o_inCalV_of_le_U D c.hVU c.hVne c.hVM).2.2.2
  obtain ⟨Vmod, i1, i2, i3, e, ρ, hc⟩ := uc22br4_exists_conjModule D.M c.V c.hVM hel
  set X : Subgroup (MBar D.M c.V) :=
    (CFSG.fittingSubgroup ↥(_root_.commutator (MBar D.M c.V))).map
      (_root_.commutator (MBar D.M c.V)).subtype
  haveI hXn : X.Normal := uc22p22vh_normal_fitting (MBar D.M c.V)
  haveI hXcyc : IsCyclic ↥X := by
    have f := Subgroup.equivMapOfInjective
      (CFSG.fittingSubgroup ↥(_root_.commutator (MBar D.M c.V)))
      (_root_.commutator (MBar D.M c.V)).subtype (_root_.commutator (MBar D.M c.V)).subtype_injective
    exact isCyclic_of_surjective f f.surjective
  have hXodd : Odd (Nat.card ↥X) := uc22p22vh_odd_card_cyclic hO2 X
  have hMc : _root_.commutator (MBar D.M c.V) ≤ Subgroup.centralizer (X : Set (MBar D.M c.V)) :=
    uc22p22vh_commutator_le_centralizer X
  obtain ⟨hT2, hBab, hBodd, hBperm⟩ :=
    uc22p22vd_mbarImage_basic D.M c.V D.T c.B0 D.sylowM.le c.hBM
  have hodd0 : Odd (Nat.card c.B0) :=
    uc22p22f_odd_card_B ({ c.toCtx21 with B := c.B0, hB := c.hB0, hle := le_rfl } : Ctx21 D Ch)
  obtain ⟨-, -, -, -, -, -, -, -, -, hperm0, -, -⟩ := c.hB0
  have hXS : X ≤ Subgroup.centralizer
      ((F05.sOf (mbarImage D.M c.V D.T) (mbarImage D.M c.V c.B0) (mbarImage D.M c.V c.B0) :
        Subgroup (MBar D.M c.V)) : Set (MBar D.M c.V)) := by
    rw [Subgroup.le_centralizer_iff]
    exact (Subgroup.commutator_mono le_top le_top).trans hMc
  have hXnorm : mbarImage D.M c.V c.B0 ⊔ mbarImage D.M c.V D.T ≤
      Subgroup.normalizer (X : Set (MBar D.M c.V)) := by
    rw [Subgroup.normalizer_eq_top X]
    exact le_top
  have key := uc22p22vc_thompson_step ρ (uc22br4_injective D.M c.V c.hVM e ρ hc)
    (mbarImage D.M c.V D.T) (mbarImage D.M c.V c.B0) X (hT2 D.sylowM.isPGroup) (hBab c.hB0.2.1)
    (hBodd hodd0) (hBperm hperm0) (uc22p22vd_hyp53_centralizesZ D Ch h1930 c e ρ hc) hXodd hXnorm hXS
  have hle : mbarImage D.M c.V c.B ≤ mbarImage D.M c.V c.B0 :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono D.M c.hle)
  exact hle.trans (Subgroup.le_centralizer_iff.2 key)

end CFSG.LocalAnalysis.UniquenessCase.UC22
