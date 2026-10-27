module

public import CFSG.Quasithin.EmptyFaithful.S146zYPair
public import CFSG.Quasithin.EmptyFaithful.S146zYNormal
public import CFSG.Quasithin.EmptyFaithful.S146zXFive
public import CFSG.Quasithin.H13.NQCoreP134Setup
public import CFSG.Quasithin.Vol2.Ch1Sec3E9Fitting

public section

namespace CFSG.Quasithin.S146zY

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.QuasithinUnique.Vol2Native CFSG.Quasithin.Ch1Sec3 CFSG.LieType.BorelTits
open CFSG.Quasithin.H13.NQCore CFSG.Quasithin.S146zX

section Quotient

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem quotient_main_five (hR : NormalInputs) (hOut : OutAbelianFact)
    (hBorel : Psl2BorelFact) (hSz : SzNoFiveFact) (hJ1 : J1NoFiveFact) (hyp : SQTKHypCat Γ)
    (h36 : A36CoreStatementCat Γ) (h37 : A37Statement Γ) (h38 : A38Part3 Γ)
    {p : ℕ} [hp : Fact p.Prime] (hp5 : p = 5) {P T N O : Subgroup Γ}
    (hexp : ∀ x ∈ P, x ^ p = 1) (hcard : Nat.card P = p ^ 2) (hT : IsSylowTwoOf T ⊤)
    (hNT : N ≤ T) (hNP : N ≤ Subgroup.normalizer (P : Set Γ))
    (hirr : ∀ U : Subgroup Γ, ⁅P, P⁆ ≤ U → U ≤ P → N ≤ Subgroup.normalizer (U : Set Γ) →
      U = ⁅P, P⁆ ∨ U = P)
    (hmul : ∀ t ∈ T, ∀ x ∈ P, ∃ y ∈ P, ∃ s ∈ T, t * x = y * s)
    (hTON : T ≤ O ⊔ N) (hOX : ∀ K : Subgroup Γ, K.Normal → P ≤ K → O ≤ K)
    (hPc : P ≤ commutator Γ) :
    P.Normal ∨
      (∃ L : Subgroup Γ, L ∈ cComp (⊤ : Subgroup Γ) ∧ CFSG.IsComponent L ∧ L.Normal ∧ P ≤ L ∧
        NormalOutcome p L P T) ∨
      (∃ L : Subgroup Γ, L ∈ cComp (⊤ : Subgroup Γ) ∧ CFSG.IsComponent L ∧
        ∃ n ∈ N, n ∉ Subgroup.normalizer (L : Set Γ) ∧
          L ⊓ L.map (MulAut.conj n).toMonoidHom = ⊥ ∧
          P ≤ L ⊔ L.map (MulAut.conj n).toMonoidHom ∧ Nat.card (P ⊓ L : Subgroup Γ) = p ∧
          Nat.card P = p ^ 2 ∧
          ((∃ m : ℕ, p ∣ 2 ^ m - 1 ∧ StatedClassicalModel ↥L .PSL 2 2 m) ∨
            ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ StatedClassicalModel ↥L .PSL 2 q 1)) := by
  have hp2 : p ≠ 2 := by omega
  have hrank : ∀ r : ℕ, r.Prime → r ≠ 2 → Open.pRank r (⊤ : Subgroup Γ) ≤ 2 :=
    CFSG.SectionRank.isStronglyQuasithin_iff.1 hyp.sqt
  have hPp : IsPGroup p P := fun x => ⟨1, Subtype.ext (by simpa using hexp x x.2)⟩
  have hc2 : p ^ 2 ≤ Nat.card P := hcard.ge
  have hc3 : Nat.card P ≤ p ^ 3 := by
    rw [hcard]
    exact Nat.pow_le_pow_right hp.out.pos (by norm_num)
  rcases P134.normal_or_centralizes_fitting hyp.o2 hrank hp2 hPp hexp hc2 hc3 hNP hirr hPc with
    hn | ⟨hFit, hrk⟩
  · exact Or.inl hn
  right
  have hrkP : 2 ≤ Open.pRank p P := two_le_pRank_of_pow_eq_one hexp hc2
  obtain ⟨L, hL, hLP⟩ := P134.exists_component_not_le_centralizer hPp hrkP hFit hrk
  have hLc : L ∈ cComp (⊤ : Subgroup Γ) := mem_cComp_top_of_isComponent hL
  by_cases hLn : L.Normal
  · obtain ⟨hPL, hout⟩ :=
      normal_case_five hR hyp h36 hp5 hexp hcard hPc hT hNT hNP hirr hmul hLc hL hLn hLP
    exact Or.inl ⟨L, hLc, hL, hLn, hPL, hout⟩
  · exact Or.inr ⟨L, hLc, hL, pair_case_five hOut hBorel hSz hJ1 hyp h37 h38 hp5 hexp hcard hT
      hNT hNP hirr hmul hTON hOX hLc hL hLn hLP⟩

end Quotient

variable {G : Type} [Group G] [Finite G]

theorem prop134Five_of_pairFacts (h36 : A36CoreForSQTKCat) (h37 : A37ForSQTKCat)
    (h38 : A38ForSQTKCat) (hR : NormalInputs) (hOut : OutAbelianFact)
    (hBorel : Psl2BorelFact) (hSz : SzNoFiveFact) (hJ1 : J1NoFiveFact) : Prop134Five := by
  intro p hp hp5 G _ _ H S X P hsqtk _ hS hXH hX hi hPX hPp hPc
  have hp2 : p ≠ 2 := by omega
  have hPcard : Nat.card P = (pCoreOf 2 X).relIndex X := hPc.trans hi.symm
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hπ
  have hyp : SQTKHypCat (↥H ⧸ CFSG.pCore 2 ↥H) := SQTKHypCat.quotient_pCore ↥H hsqtk
  obtain ⟨hpX, hSyl⟩ := sylow_of_card_eq_relIndex hX hp2 hPX hPp hPcard
  have hPH : P ≤ H := hPX.trans hXH
  have hexp := exp_of_sylow hX hp2 hpX hSyl
  have hPO : P ⊓ pCoreOf 2 H = ⊥ := inf_pCoreOf_eq_bot' hp2 hPp
  have hcardb : Nat.card (modO2Image H P) = p ^ 2 := by
    rw [card_bar_of_sylow hXH hp2 hSyl]
    exact hPc
  have hirr := irr_modO2Image' hPH (inf_le_left.trans hS.1) inf_le_right
    (irr_of_sylow hS hXH hX hp2 hpX hSyl)
  have hNT : modO2Image H (S ⊓ Subgroup.normalizer (P : Set G)) ≤ modO2Image H S :=
    P134.modO2Image_mono inf_le_left
  have hNP : modO2Image H (S ⊓ Subgroup.normalizer (P : Set G)) ≤
      Subgroup.normalizer (modO2Image H P : Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
    P134.modO2Image_le_normalizer inf_le_right
  have hXK : ∀ K : Subgroup G, H ≤ Subgroup.normalizer (K : Set G) → P ≤ K → X ≤ K := by
    intro K hHK hPK
    rw [cl_of_sylow hX hp2 hpX hSyl]
    exact conjClosure_le fun h hh z hz =>
      (Subgroup.mem_normalizer_iff.mp (hHK (hXH hh)) z).mp (hPK hz)
  have hPpull : ∀ K : Subgroup G, pCoreOf 2 H ≤ Subgroup.normalizer (K : Set G) →
      modO2Image H P ≤ modO2Image H K → P ≤ K := fun K hOK hPK a ha =>
    mem_of_mem_modO2Image' hp2 hOK (hPH ha) (hexp a ha)
      (hPK (P134.mk_mem_modO2Image ha (hPH ha)))
  rcases quotient_main_five hR hOut hBorel hSz hJ1 hyp (h36 _ hyp) (h37 _ hyp) (h38 _ hyp) hp5
      (exp_bar_of_sylow hX hp2 hpX hSyl) hcardb (P134.sylow_bar hS) hNT hNP hirr
      (mul_bar_of_sylow hS hXH hX hp2 hpX hSyl) (sup_bar_of_sylow hS hXH hX hp2 hpX hSyl)
      (oX_bar_of_sylow hXH hX hp2 hpX hSyl) (comm_bar_of_sylow hS hXH hX hp2 hpX hSyl) with
    hn | ⟨Lb, hLbc, hLb, hLbn, hPLb, hout⟩ |
      ⟨Lb, hLbc, hLb, nb, hnbN, hnbL, hinf, hPK, hpL, hP2, htype⟩
  ·
    exact Or.inl (le_normalizer_of_normal_of_sylow hS hXH hX hp2 hpX hSyl hn)
  ·
    right
    obtain ⟨L, hL, rfl⟩ := exists_cComp_modO2Image_eq hLbc
    obtain ⟨e⟩ := modO2_mulEquiv hL
    have hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hLb.1
    have hLH : L ≤ H := le_of_mem_cComp hL
    have hLnH : (L.subgroupOf H).Normal :=
      normal_of_normal_map_of_mem_cComp (CFSG.pCore 2 ↥H) (isSolvable_pCore_two_group ↥H)
        (subgroupOf_mem_cComp hL) hLbn
    have hHL : H ≤ Subgroup.normalizer (L : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hLH).mp hLnH
    have hSL : S ≤ Subgroup.normalizer (L : Set G) := hS.1.trans hHL
    have hPL : P ≤ L := hPpull L (P134.pCoreOf_le_normalizer_of_mem_cComp hL) hPLb
    have hcl : conjClosure L S = L := by
      refine le_antisymm (conjClosure_le fun g hg l hl => ?_) (le_conjClosure L S)
      exact (Subgroup.mem_normalizer_iff.mp (hSL hg) l).mp hl
    refine ⟨L, hL, hq, hcl.symm ▸ hXK L hHL hPL, ?_⟩
    rcases hout with h2 | hcyc
    · right; left
      refine ⟨hSL, ?_⟩
      rcases h2 with h | h'
      · exact Or.inl (CFSG.SectionRank.statedClassicalModel_of_mulEquiv e h)
      · obtain ⟨e'⟩ := h'
        exact Or.inr ⟨e.trans e'⟩
    · right; right
      exact ⟨hSL, autCyclic_of_bar_of_sylow hS hXH hX hp2 hpX hSyl hcyc⟩
  ·
    right
    obtain ⟨L, hL, rfl⟩ := exists_cComp_modO2Image_eq hLbc
    obtain ⟨e⟩ := modO2_mulEquiv hL
    have hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hLb.1
    obtain ⟨t', ht', rfl⟩ := hnbN
    set t : G := (t' : G) with ht
    have htSN : t ∈ S ⊓ Subgroup.normalizer (P : Set G) := ht'
    have htH : t ∈ H := t'.2
    set Lt := L.map (MulAut.conj t).toMonoidHom with hLt
    have hLtc : Lt ∈ cComp H := map_conj_mem_cComp hL htH
    have hLtb : modO2Image H Lt = (modO2Image H L).map (MulAut.conj (π t')).toMonoidHom :=
      modO2Image_conj t'
    have htL : t ∉ Subgroup.normalizer (L : Set G) := by
      intro h
      apply hnbL
      rw [← A38.map_conj_eq_iff, ← hLtb, hLt, A38.map_conj_eq_iff.mpr h]
    have hP2 : Nat.card P = p ^ 2 := hPc
    set A := P ⊓ L with hA
    have hAH : A ≤ H := inf_le_left.trans hPH
    have hAb : modO2Image H A = modO2Image H P ⊓ modO2Image H L := by
      refine le_antisymm (le_inf (P134.modO2Image_mono inf_le_left)
        (P134.modO2Image_mono inf_le_right)) fun x hx => ?_
      obtain ⟨⟨a, haH⟩, haP, rfl⟩ := hx.1
      have haL : a ∈ L := mem_of_mem_modO2Image' hp2 (P134.pCoreOf_le_normalizer_of_mem_cComp hL)
        haH (hexp a haP) hx.2
      exact P134.mk_mem_modO2Image (Y := A) (show a ∈ P ⊓ L from ⟨haP, haL⟩) haH
    have hAp : Nat.card A = p := by
      rw [← P134.card_modO2Image hAH (eq_bot_iff.mpr ((inf_le_inf_right _ inf_le_left).trans
        hPO.le)), hAb]
      exact hpL
    set A' := conjByElt t A with hA'
    have hA'P : A' ≤ P := by
      rintro _ ⟨a, ha, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp htSN.2 a).mp ha.1
    have hA'p : Nat.card A' = p := by
      rw [hA', conjByElt, Subgroup.card_map_of_injective (MulAut.conj t).injective, hAp]
    have hAA' : A ⊓ A' = ⊥ := by
      refine eq_bot_iff.mpr fun x hx => ?_
      have hxP : x ∈ P := hx.1.1
      have hxH : x ∈ H := hPH hxP
      have hxLt : x ∈ Lt := Subgroup.map_mono (inf_le_right : A ≤ L) hx.2
      have h1 : π ⟨x, hxH⟩ ∈
          modO2Image H L ⊓ (modO2Image H L).map (MulAut.conj (π t')).toMonoidHom :=
        ⟨P134.mk_mem_modO2Image hx.1.2 hxH, hLtb ▸ P134.mk_mem_modO2Image hxLt hxH⟩
      rw [hinf, Subgroup.mem_bot] at h1
      have h2 : π ⟨x, hxH⟩ = π ⟨1, H.one_mem⟩ := by
        rw [h1]
        exact (map_one π).symm
      rw [P134.eq_of_mk_eq hPO hxP P.one_mem hxH H.one_mem h2]
      exact Subgroup.one_mem _
    have hPab : IsMulCommutative ↥P := IsPGroup.isMulCommutative_of_card_eq_prime_sq hP2
    have hA'NA : A' ≤ Subgroup.normalizer (A : Set G) := by
      intro x hx
      rw [Subgroup.mem_normalizer_iff]
      intro a
      have hxa : ∀ b ∈ P, x * b * x⁻¹ = b := by
        intro b hb
        have := congrArg Subtype.val (hPab.is_comm.comm (⟨x, hA'P hx⟩ : P) ⟨b, hb⟩)
        simp only [Subgroup.coe_mul] at this
        rw [this]
        group
      constructor
      · intro ha
        rw [hxa a ha.1]
        exact ha
      · intro ha
        have ha' : a ∈ P := by
          have := P.mul_mem (P.mul_mem (P.inv_mem (hA'P hx)) ha.1) (hA'P hx)
          simpa [mul_assoc] using this
        rw [hxa a ha'] at ha
        exact ha
    have hPAA : P = A ⊔ A' := by
      refine (Subgroup.eq_of_le_of_card_ge (sup_le inf_le_left hA'P) ?_).symm
      rw [GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer A A' hA'NA
        (disjoint_iff.mpr hAA'), hAp, hA'p, hP2, sq]
    have hOLt : pCoreOf 2 H ≤ Subgroup.normalizer ((L ⊔ Lt : Subgroup G) : Set G) :=
      fun o ho => Subgroup.inf_normalizer_le_normalizer_sup L Lt
        ⟨P134.pCoreOf_le_normalizer_of_mem_cComp hL ho,
          P134.pCoreOf_le_normalizer_of_mem_cComp hLtc ho⟩
    have hPLLt : P ≤ L ⊔ Lt := by
      refine hPpull _ hOLt (hPK.trans ?_)
      rw [← hLtb]
      exact sup_le (P134.modO2Image_mono le_sup_left) (P134.modO2Image_mono le_sup_right)
    have hLLtS : L ⊔ Lt ≤ conjClosure L S := by
      refine sup_le (le_conjClosure L S) ?_
      rintro _ ⟨l, hl, rfl⟩
      exact mem_conjClosure htSN.1 hl
    have hHcl : H ≤ Subgroup.normalizer (conjClosure L S : Set G) :=
      normal_conjClosure_of_subgroup hS hL (h37 _ hyp) (h38 _ hyp)
    have hPL : P ⊓ L ≠ ⊥ := by
      intro hbot
      have hA0 : A = ⊥ := hbot
      have hP1 : Nat.card P = 1 := by
        have : P = ⊥ := by rw [hPAA, hA0]; simp [hA', hA0, conjByElt]
        rw [this]
        exact Subgroup.card_bot
      have hpp : p.Prime := Fact.out
      have : p ^ 2 = 1 := hP2.symm.trans hP1
      have h2 := hpp.two_le
      nlinarith
    refine ⟨L, hL, hq, hXK _ hHcl (hPLLt.trans hLLtS),
      Or.inl ⟨fun hSL => htL (hSL htSN.1), hPL, ?_⟩⟩
    rcases htype with ⟨m, hmp, hmod⟩ | ⟨q, hqp, hq2, hmod⟩
    · exact Or.inl ⟨m, hmp, CFSG.SectionRank.statedClassicalModel_of_mulEquiv e hmod⟩
    · exact Or.inr ⟨q, hqp, hq2, CFSG.SectionRank.statedClassicalModel_of_mulEquiv e hmod⟩

end CFSG.Quasithin.S146zY
