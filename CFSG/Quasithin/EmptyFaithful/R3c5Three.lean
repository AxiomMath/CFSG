module

public import CFSG.Quasithin.EmptyFaithful.R3c5Two
public import CFSG.Quasithin.EmptyFaithful.R3c5Cat
public import CFSG.Quasithin.EmptyFaithful.R3c5Rho
public import CFSG.Quasithin.EmptyFaithful.S153IRed

public section

namespace CFSG.Quasithin.R3c5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.OuterAutomorphisms
open scoped commutatorElement

section Commute

variable {G : Type} [Group G]

theorem commute_of_commutator_mem_centerOf {L : Subgroup G} (hperf : Group.IsPerfect ↥L) {k : G}
    (hk : ∀ y ∈ L, y * k * y⁻¹ * k⁻¹ ∈ centerOf L) : ∀ x ∈ L, x * k = k * x := by
  have hL : ∀ y ∈ L, y * k * y⁻¹ * k⁻¹ ∈ L := fun y hy => (hk y hy).1
  have hC : ∀ y ∈ L, y * k * y⁻¹ * k⁻¹ ∈ Subgroup.centralizer (L : Set G) := fun y hy => (hk y hy).2
  set f : ↥L → ↥L := fun y => ⟨(y : G) * k * (y : G)⁻¹ * k⁻¹, hL y y.2⟩ with hf
  have hfc : ∀ y, f y ∈ Subgroup.center ↥L := by
    intro y
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hC y y.2) g g.2)
  have hmul : ∀ y z, f (y * z) = f z * f y := by
    intro y z
    have hz := Subgroup.mem_center_iff.mp (hfc z) y
    apply Subtype.ext
    have hz'' : (y : G) * ((z : G) * k * (z : G)⁻¹ * k⁻¹) =
        ((z : G) * k * (z : G)⁻¹ * k⁻¹) * (y : G) := congrArg Subtype.val hz
    change ((y : G) * (z : G)) * k * ((y : G) * (z : G))⁻¹ * k⁻¹ =
      ((z : G) * k * (z : G)⁻¹ * k⁻¹) * ((y : G) * k * (y : G)⁻¹ * k⁻¹)
    calc ((y : G) * (z : G)) * k * ((y : G) * (z : G))⁻¹ * k⁻¹
        = (y : G) * ((z : G) * k * (z : G)⁻¹ * k⁻¹) * k * (y : G)⁻¹ * k⁻¹ := by group
      _ = ((z : G) * k * (z : G)⁻¹ * k⁻¹) * (y : G) * k * (y : G)⁻¹ * k⁻¹ := by rw [hz'']
      _ = _ := by group
  let g : ↥L →* ↥(Subgroup.center ↥L) :=
    { toFun := fun y => ⟨f y, hfc y⟩
      map_one' := by
        apply Subtype.ext
        apply Subtype.ext
        simp [hf]
      map_mul' := by
        intro y z
        apply Subtype.ext
        show f (y * z) = f y * f z
        rw [hmul y z]
        exact Subgroup.mem_center_iff.mp (hfc y) (f z) }
  have hker : commutator ↥L ≤ g.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (Subtype.ext (Subgroup.mem_center_iff.mp (g b).2 (g a)))
  intro x hx
  have hx' : (⟨x, hx⟩ : ↥L) ∈ g.ker := hker (by rw [hperf.commutator_eq_top]; exact Subgroup.mem_top _)
  have hx1 : f ⟨x, hx⟩ = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx')
  have hx2 : x * k * x⁻¹ * k⁻¹ = 1 := congrArg Subtype.val hx1
  exact commutatorElement_eq_one_iff_mul_comm.mp hx2

end Commute

section NotNormal

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem yp_le_sup_centralizer_of_ne (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h122 : Lemma122A)
    (c : CtxComp1 T Mc M V₁ V₂ Yp I L t) (hYe : ∀ z : OTwoQuot Yp, z ^ 3 = 1)
    (hne : L ≠ conjClosure L (Sgp153 T V₁)) : Yp ≤ L ⊔ Subgroup.centralizer (L : Set G) := by
  classical
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.hyp
  have hq := hh.hyp.qtfe
  have hLI : L ∈ cComp I := c.c33.mem
  have hLle : L ≤ I := le_of_mem_cComp hLI
  have hSI : Sgp153 T V₁ ≤ I := le_sup_right.trans c.inH.1.1
  have hYI : Yp ≤ I := le_sup_left.trans c.inH.1.1
  obtain ⟨s, hs, z, hz, hsz⟩ : ∃ s ∈ Sgp153 T V₁, ∃ z ∈ L, s * z * s⁻¹ ∉ L := by
    by_contra hno
    push Not at hno
    exact hne (le_antisymm (le_conjClosure _ _) (conjClosure_le hno))
  set L'' := L.map (MulAut.conj s).toMonoidHom with hL''
  have hL''mem : L'' ∈ conjSubgroupsBy I L := ⟨s, hSI hs, rfl⟩
  have hLmem : L ∈ conjSubgroupsBy I L := ⟨1, I.one_mem, by ext x; simp⟩
  have hLne : L ≠ L'' := by
    intro h
    apply hsz
    have : s * z * s⁻¹ ∈ L'' := by
      rw [hL'', A38.mem_map_conj]
      have e : s⁻¹ * (s * z * s⁻¹) * s = z := by group
      rw [e]
      exact hz
    rwa [← h] at this
  rcases lemma_1_2_1_three hq.qtke hq.simple hq.nonabelian h37 h38 c.inH.1.2 hLI with hn | ⟨hcard, -⟩
  · exact absurd (((Subgroup.normal_subgroupOf_iff_le_normalizer hLle).mp hn (hSI hs) z).mp hz) hsz
  obtain ⟨x, y, hxy, hset⟩ := Set.ncard_eq_two.mp hcard
  have hmem : ∀ K ∈ conjSubgroupsBy I L, K = L ∨ K = L'' := by
    intro K hK
    have hK' := hK
    have h1 := hLmem
    have h2 := hL''mem
    rw [hset] at hK' h1 h2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hK' h1 h2
    rcases hK' with rfl | rfl <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
      first | exact Or.inl h1.symm | exact Or.inr h2.symm | (exfalso; exact hLne (h1.trans h2.symm))
  have hcc : conjClosure L I ≤ L ⊔ L'' := by
    refine conjClosure_le fun g hg l hl => ?_
    have hK : L.map (MulAut.conj g).toMonoidHom ∈ conjSubgroupsBy I L := ⟨g, hg, rfl⟩
    have hgl : g * l * g⁻¹ ∈ L.map (MulAut.conj g).toMonoidHom := ⟨l, hl, rfl⟩
    rcases hmem _ hK with h | h
    · rw [h] at hgl
      exact Subgroup.mem_sup_left hgl
    · rw [h] at hgl
      exact Subgroup.mem_sup_right hgl
  have hdvd : 3 ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) := by
    have hr := pRank_modO2_eq L Nat.prime_three (by norm_num)
    obtain ⟨E, -, -, hE⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3)
      (⊤ : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L))
    have h3 : 3 ∣ Nat.card E := by
      rw [hE, hr]
      exact dvd_pow_self 3 (by have := c.c34.rank; omega)
    exact h3.trans (Subgroup.card_subgroup_dvd_card E)
  have h122' := h122 G hq.simple hq.qtke hq.nonabelian I L c.inH.1.2 hLI 3 Nat.prime_three
    (by norm_num) hcard hdvd
  have hYle : Yp ≤ Subgroup.closure {x : G | x ∈ I ∧ ∃ k : ℕ, orderOf x = 3 ^ k} := by
    calc Yp = oTwoUpper Yp := hh.oTwoUpper_eq.symm
      _ ≤ _ := by
        rw [oTwoUpper, Subgroup.closure_le]
        rintro x ⟨hx, hodd⟩
        have h1 : x ^ 3 = 1 := pow_three_eq_one_of_odd hYe hx hodd
        rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one h1) with h | h
        · exact Subgroup.subset_closure ⟨hYI hx, 0, by simpa using h⟩
        · exact Subgroup.subset_closure ⟨hYI hx, 1, by simpa using h⟩
  have hYc : Yp ≤ L ⊔ L'' := hYle.trans (h122'.le.trans hcc)
  have hL''c : L'' ∈ cComp I := map_conj_mem_cComp hLI (hSI hs)
  have hne' : L ≠ L'' := hLne
  obtain ⟨hc1, -⟩ := lemma_1_2_1_two hq.qtke hq.simple hq.nonabelian h37 c.inH.1.2 hLI hL''c hne'
  have hperf : Group.IsPerfect ↥L := c.c33.quasisimple.1
  have hL''C : L'' ≤ Subgroup.centralizer (L : Set G) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have := commute_of_commutator_mem_centerOf hperf (k := k) (fun y hy => by
      have h1 := (hc1 (Subgroup.commutator_mem_commutator hy hk)).1
      rw [c.c33.center_eq]
      simpa [commutatorElement_def] using h1) x hx
    exact this
  exact hYc.trans (sup_le_sup_left hL''C L)

end NotNormal

section RankTwoG

variable {G : Type} [Group G] [Finite G]

theorem rankTwo_G (h38 : A38ForSQTK) (h36 : A36ForSQTK) (hF : A318Facts)
    (hE3 : ∀ (X : Type) [Group X] [Finite X], A318Case3Group X → Nat.card (Subgroup.center X) = 3)
    (hidx : PGLIndex) {I L Y : Subgroup G} (hSQ : SQTKGroup ↥I) (hLc : L ∈ cComp I)
    (hQ : CFSG.IsQuasisimple ↥L) (hZ : IsPGroup 2 ↥(Subgroup.center ↥L))
    (hr : 2 ≤ CFSG.Open.pRank 3 L) (hI3 : CFSG.Open.pRank 3 I ≤ 2) (hYI : Y ≤ I)
    (hYo : oTwoUpper Y = Y) (hYe : ∀ z : OTwoQuot Y, z ^ 3 = 1) :
    Y ≤ L ∨ ∃ (s : Bool) (q : ℕ), Int.ModEq 3 (q : ℤ) (if s then 1 else -1) ∧
      IsPSLEps3q s q (↥L ⧸ Subgroup.center ↥L) ∧
      ∃ y ∈ Y, orderOf y = 3 ∧ y ∉ L ⊔ Subgroup.centralizer (L : Set G) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLI : L ≤ I := le_of_mem_cComp hLc
  have hSQ' := SQTKHyp.of_sqtkGroup ↥I hSQ
  have h3L : 3 ∣ Nat.card ↥L := R3c2.three_dvd_card_of_one_le_pRank L (by omega)
  have hLc' : L.subgroupOf I ∈ cComp (⊤ : Subgroup ↥I) := subgroupOf_mem_cComp hLc
  let eL : ↥(L.subgroupOf I) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLI
  have hQ' : CFSG.IsQuasisimple ↥(L.subgroupOf I) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eL.symm hQ
  have hZ' : IsPGroup 2 ↥(Subgroup.center ↥(L.subgroupOf I)) :=
    hZ.of_equiv (Subgroup.centerCongr eL).symm
  have hr' : 1 < CFSG.Open.pRank 3 (L.subgroupOf I) := by
    rw [R3c2.pRank_three_subgroupOf hLI]
    omega
  have h3L' : 3 ∣ Nat.card ↥(L.subgroupOf I) := by
    rw [Nat.card_congr eL.toEquiv]
    exact h3L
  have hYo' : oTwoUpper (Y.subgroupOf I) = Y.subgroupOf I := by
    apply Subgroup.map_injective I.subtype_injective
    rw [map_oTwoUpper_subgroupOf hYI, hYo, Subgroup.map_subgroupOf_eq_of_le hYI]
  have hYe' : ∀ z : OTwoQuot (Y.subgroupOf I), z ^ 3 = 1 := OTwoQuot_pow_three_subgroupOf hYI hYe
  have hLn : (L.subgroupOf I).Normal :=
    A318.normal_of_pRank_gt_one hSQ (h38 _ hSQ') hLc' Nat.prime_three (by norm_num) hr'
  have : (L.subgroupOf I).Normal := hLn
  rcases rankTwo_H hF hE3 hidx hSQ (h36 _ hSQ') (h38 _ hSQ') hLc' hQ' hZ' hr' hYo' hYe' with
    hYL | ⟨s, q, hqmod, hSq, hPGL, hXP, hcard, y', hy'Y, hy'ord, hy'L, hdec⟩
  · left
    have := Subgroup.map_mono (f := I.subtype) hYL
    rwa [Subgroup.map_subgroupOf_eq_of_le hYI, Subgroup.map_subgroupOf_eq_of_le hLI] at this
  · right
    obtain ⟨p, e, hp, he, hqp, hX'⟩ := hSq
    have hSq0 : IsPSLEps3q s q ↥(starImage 3 (L.subgroupOf I)) := ⟨p, e, hp, he, hqp, hX'⟩
    have hXs : IsSimpleGroup ↥(starImage 3 (L.subgroupOf I)) := (isPSLEps3_finite_simple hX').2
    obtain ⟨eX⟩ := nonempty_starImage_equiv_quotCenter hQ' h3L' hXs
    let eQ : (↥(L.subgroupOf I) ⧸ Subgroup.center ↥(L.subgroupOf I)) ≃*
        (↥L ⧸ Subgroup.center ↥L) :=
      QuotientGroup.congr _ _ eL (Subgroup.map_center_eq eL)
    have hSq' : IsPSLEps3q s q (↥L ⧸ Subgroup.center ↥L) :=
      isPSLEps3q_of_mulEquiv (eX.trans eQ).symm hSq0
    have hyL : (y' : G) ∉ L := hy'L
    refine ⟨s, q, hqmod, hSq', (y' : G), hy'Y, ?_, ?_⟩
    · rw [Subgroup.orderOf_coe]
      exact hy'ord
    · exact not_mem_sup_centralizer hLI hZ hr hI3 y'.2
        (by rw [Subgroup.orderOf_coe]; exact hy'ord) hyL

end RankTwoG

section Final

@[expose] def Input15343Diag : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    CtxComp1 T Mc M V₁ V₂ Yp I L t → Concl15343Open T M V₁ V₂ Yp I L →
      L = conjClosure L (Sgp153 T V₁) → CFSG.Open.pRank 3 L = 2 →
      ((∃ n : ℕ, IsPSL 3 2 n (↥L ⧸ Subgroup.center ↥L)) ∨
        (∃ n : ℕ, IsPSU 3 2 n (↥L ⧸ Subgroup.center ↥L))) →
      (∃ y ∈ Yp, orderOf y = 3 ∧ y ∉ L ⊔ Subgroup.centralizer (L : Set G)) → False

theorem input15343Inner_of_named (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h36 : A36ForSQTK)
    (hF : A318Facts) (hE : CFSG.Quasithin.Vol2.Ch11.SecA.FactA318Excl) (hlist : Lemma115_3_List)
    (hA : R3c2.Input15333Two) (h122 : Lemma122A) (kCat : RankTwoListCatalogue)
    (kDiag : Input15343Diag) : Input15343Inner := by
  classical
  intro G _ _ T Mc M V₁ V₂ Yp I L t c o
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.hyp
  have hq := hh.hyp.qtfe
  have hLc : L ∈ cComp I := c.c33.mem
  have hLI : L ≤ I := le_of_mem_cComp hLc
  have hYI : Yp ≤ I := le_sup_left.trans c.inH.1.1
  have hYe : ∀ z : OTwoQuot Yp, z ^ 3 = 1 := by
    intro z
    have h := pow_card_eq_one' (x := z)
    rwa [o.a_ord] at h
  by_cases hL0 : L = conjClosure L (Sgp153 T V₁)
  · have hSQ : SQTKGroup ↥I :=
      sqtkGroup_of_pCoreOf_ne_bot hq.qtke hq.simple hq.nonabelian c.inH.1.2
    have hQ : CFSG.IsQuasisimple ↥L := c.c33.quasisimple
    have hZ : IsPGroup 2 ↥(Subgroup.center ↥L) := R3c3.isPGroup_two_center c.c33.center_eq
    have hI3 : CFSG.Open.pRank 3 I ≤ 2 :=
      pRank_le_two_of_pCoreOf_ne_bot hq.qtke c.inH.1.2 Nat.prime_three (by norm_num)
    have h1 : 1 ≤ CFSG.Open.pRank 3 L := c.c34.rank
    have h2 : CFSG.Open.pRank 3 L ≤ 2 :=
      (CFSG.SectionRank.pRank_mono (by norm_num : 1 < 3) hLI).trans hI3
    obtain ⟨z, hz⟩ := hA G T Mc M V₁ V₂ Yp I t c.toCtxComp
    have hcomp : IsComponentIn L I :=
      Id2519.isComponentIn_of_mem_cComp c.c33.mem c.c33.quasisimple
    have hsimple : IsSimpleGroup G := hq.simple
    have hcore : QTKECore G := qtkeCore_of_cat hq.nonabelian hq.qtke
    have hcases : Lemma115Cases L z :=
      (Lemma115_3_List.component_cases hlist hsimple hq.nonabelian hcore hz hcomp).2.2.2
    rcases (by omega : CFSG.Open.pRank 3 L = 1 ∨ CFSG.Open.pRank 3 L = 2) with hr | hr
    ·
      have hperf : Group.IsPerfect ↥L := hQ.1
      have hOut : ∀ a b : Outer ↥L, a * b = b * a :=
        outer_comm_of_rankOneOut (rankOneOut_of_lemma115 hcases hQ c.c33.center_eq c.c34.not_Sz hr)
      have hYN : Yp ≤ Subgroup.normalizer (L : Set G) :=
        S153D.Yp_le_normalizer h37 h38 hh c.inH hLc
      have hSN : Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G) := by
        have := le_normalizer_conjClosure L (Sgp153 T V₁)
        rwa [← hL0] at this
      have hHN : Yp ⊔ Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G) := sup_le hYN hSN
      let ρ : ↥(Yp ⊔ Sgp153 T V₁) →* Outer ↥L :=
        (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner ↥L)).comp
          ((conjAct L).comp (Subgroup.inclusion hHN))
      obtain ⟨ψ, hψs, hψk⟩ := c.facts25.s3
      have key := rho_eq_one_of_s3 (H := Yp ⊔ Sgp153 T V₁) hOut le_sup_left hh.oTwoUpper_eq ψ hψs hψk ρ
      intro y hy
      have h1 : ρ ⟨y, (le_sup_left : Yp ≤ Yp ⊔ Sgp153 T V₁) hy⟩ = 1 := key y hy
      have hmem : conjAct L ⟨y, hYN hy⟩ ∈
          CFSG.ComponentClassification.OuterAutomorphisms.inner ↥L :=
        (QuotientGroup.eq_one_iff _).1 h1
      obtain ⟨l, hl⟩ := hmem
      have hyl : ∀ x ∈ L, y * x * y⁻¹ = (l : G) * x * (l : G)⁻¹ := by
        intro x hx
        have h2 := congrArg (fun a : MulAut ↥L => ((a ⟨x, hx⟩ : ↥L) : G)) hl
        simp only [MulAut.conj_apply, R3c3.coe_conjAct_apply'] at h2
        exact h2.symm
      have hlC : (l : G)⁻¹ * y ∈ Subgroup.centralizer (L : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        have h3 : y * x * y⁻¹ = (l : G) * x * (l : G)⁻¹ := hyl x hx
        have h4 : (l : G)⁻¹ * y * x = x * ((l : G)⁻¹ * y) := by
          calc (l : G)⁻¹ * y * x = (l : G)⁻¹ * (y * x * y⁻¹) * y := by group
            _ = (l : G)⁻¹ * ((l : G) * x * (l : G)⁻¹) * y := by rw [h3]
            _ = x * ((l : G)⁻¹ * y) := by group
        exact h4.symm
      have : y = (l : G) * ((l : G)⁻¹ * y) := by group
      rw [this]
      exact Subgroup.mul_mem_sup l.2 hlC
    ·
      rcases rankTwo_G h38 h36 hF hE.2 pglIndex_holds hSQ hLc hQ hZ (by omega) hI3 hYI hh.oTwoUpper_eq hYe with
        hYL | ⟨s, q, hqmod, hSq, y, hyY, hy3, hyout⟩
      · exact hYL.trans le_sup_left
      · exfalso
        obtain ⟨n, hqn, hLn⟩ := kCat G L z hcases hQ c.c33.center_eq c.c34.not_Sz hr s q hqmod hSq
        refine kDiag G T Mc M V₁ V₂ Yp I L t c o hL0 hr ?_ ⟨y, hyY, hy3, hyout⟩
        cases s
        · exact Or.inr ⟨n, hLn⟩
        · exact Or.inl ⟨n, hLn⟩
  · exact yp_le_sup_centralizer_of_ne h37 h38 h122 c hYe hL0

end Final

end CFSG.Quasithin.R3c5
