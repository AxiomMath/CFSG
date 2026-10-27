module

public import CFSG.RankThree.PartTwo.Sec12.Hering129CFam8
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.UnipotentThree
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Down
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.OddTop
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.Models.PGLSimple
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LComp
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LValid
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowVTools

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.HardMathSupport.Solomon.Coordinator
open TauCeti (LieTypeIndex PrimePower)

namespace Hering129C

section Constrained

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance

private theorem commute_zpowers_of_mem_fixSub {S : Type} [Group S] {s c : S}
    (hc : c ∈ Lemma510Ns.fixSub (MulAut.conj s)) {h : S} (hh : h ∈ Subgroup.zpowers s) :
    c * h = h * c := by
  have hcs : Commute c s := by
    have := Lemma510Ns.mem_fixSub.1 hc
    rw [MulAut.conj_apply] at this
    show c * s = s * c
    calc c * s = (s * c * s⁻¹) * s := by rw [this]
      _ = s * c := by group
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
  exact (hcs.zpow_right k).eq

private theorem fixSub_le_normalizer_zpowers {S : Type} [Group S] (s : S) :
    Lemma510Ns.fixSub (MulAut.conj s) ≤ Subgroup.normalizer (Subgroup.zpowers s : Set S) := by
  intro c hc
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have hcomm : ∀ {x : S}, x ∈ Subgroup.zpowers s → c * x * c⁻¹ = x := fun {x} hx => by
    rw [commute_zpowers_of_mem_fixSub hc hx]
    group
  constructor
  · intro hh
    rw [hcomm hh]
    exact hh
  · intro hh
    have e := hcomm hh
    have hy : h = c * h * c⁻¹ := by
      calc h = c⁻¹ * (c * h * c⁻¹) * c := by group
        _ = c⁻¹ * (c * (c * h * c⁻¹) * c⁻¹) * c := by rw [e]
        _ = c * h * c⁻¹ := by group
    rw [hy]
    exact hh

private theorem conj_mem_fixSub_of_mem_normalizer {S : Type} [Group S] {s n c : S}
    (hn : n ∈ Subgroup.normalizer (Subgroup.zpowers s : Set S))
    (hc : c ∈ Lemma510Ns.fixSub (MulAut.conj s)) :
    n * c * n⁻¹ ∈ Lemma510Ns.fixSub (MulAut.conj s) := by
  have ht : n⁻¹ * s * n ∈ Subgroup.zpowers s := by
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hn) s).1 (Subgroup.mem_zpowers s)
    simpa using this
  have hct := commute_zpowers_of_mem_fixSub hc ht
  rw [Lemma510Ns.mem_fixSub, MulAut.conj_apply]
  generalize hT : n⁻¹ * s * n = t at ht hct
  have hs : s = n * t * n⁻¹ := by
    rw [← hT]
    group
  rw [hs]
  calc n * t * n⁻¹ * (n * c * n⁻¹) * (n * t * n⁻¹)⁻¹ = n * (t * c * t⁻¹) * n⁻¹ := by group
    _ = n * (c * t * t⁻¹) * n⁻¹ := by rw [← hct]
    _ = n * c * n⁻¹ := by group

private theorem gLAPPrimeCore_three_eq_bot {G : Type*} [Group G] [Finite G] (N : Subgroup G)
    (hcen : ∀ h ∈ N, (∀ r ∈ pCoreOf 3 N, h * r = r * h) → h ∈ pCoreOf 3 N) :
    GLAPPrimeCore 3 ↥N = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  show CFSG.pPrimeCore 3 ↥N = ⊥
  rw [CFSG.pPrimeCore_eq_bot_iff]
  intro K hKn hKc
  have hBn : (CFSG.pCore 3 ↥N).Normal := CFSG.pCore_normal
  have hBp : IsPGroup 3 (CFSG.pCore 3 ↥N) := CFSG.pCore_isPGroup
  have hdisj : K ⊓ CFSG.pCore 3 ↥N = ⊥ := by
    apply Subgroup.inf_eq_bot_of_coprime
    obtain ⟨n, hn⟩ := hBp.exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_right _ hKc.symm
  rw [eq_bot_iff]
  intro k hk
  have hcomm : ∀ b ∈ CFSG.pCore 3 ↥N, k * b = b * k := by
    intro b hb
    have h1 : k * b * k⁻¹ * b⁻¹ ∈ K ⊓ CFSG.pCore 3 ↥N := by
      refine ⟨?_, ?_⟩
      · have h2 := hKn.conj_mem k⁻¹ (K.inv_mem hk) b
        have h3 : k * b * k⁻¹ * b⁻¹ = k * (b * k⁻¹ * b⁻¹) := by group
        rw [h3]
        exact K.mul_mem hk h2
      · exact (CFSG.pCore 3 ↥N).mul_mem (hBn.conj_mem b hb k) ((CFSG.pCore 3 ↥N).inv_mem hb)
    rw [hdisj, Subgroup.mem_bot] at h1
    calc k * b = (k * b * k⁻¹ * b⁻¹) * (b * k) := by group
      _ = b * k := by rw [h1, one_mul]
  have hmem := hcen k k.2 (by
    rintro r ⟨b, hb, rfl⟩
    exact congrArg Subtype.val (hcomm b hb))
  obtain ⟨b, hb, hbk⟩ := hmem
  have hbk' : b = k := Subtype.ext hbk
  rw [hbk'] at hb
  have hkb : k ∈ K ⊓ CFSG.pCore 3 ↥N := ⟨hk, hb⟩
  rwa [hdisj] at hkb

end Constrained

section Char3

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance

variable {Q Lb : Type} [Group Q] [Finite Q] [Group Lb] {c a : Q} {I X : Subgroup Q}
  {f : ↥I →* Lb}

theorem census_false_of_char3 (hD : Census129 c a I X f) (hs : IsSimpleGroup Q)
    (hS : IsChevOfChar 3 Q) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hna : ∃ x y : Q, x * y ≠ y * x := by
    obtain ⟨a', b', hab⟩ := hD.quasisimple.2.2
    induction a' using QuotientGroup.induction_on with
    | H x =>
      induction b' using QuotientGroup.induction_on with
      | H y =>
        exact ⟨x, y, fun h => hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h])⟩
  have hc1 : c ≠ 1 := c_ne_one hD
  have hc3 : c ^ 3 = 1 := c_pow_three hD
  have hno := LieComp.noThreeComponents_of_conj YS08.LieQ.lieQConstrainedInner_three_holds hs hna
    hS hc1 hc3
  have hQ1 : Subgroup.zpowers c ≠ ⊥ := fun h => hc1 (Subgroup.zpowers_eq_bot.1 h)
  have hQ3 : IsPGroup 3 (Subgroup.zpowers c) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hD.orderOf_c]; norm_num)
  have hcen := YS08.LieQ.lieQConstrainedInner_three_holds Q hs hna hS (Subgroup.zpowers c) hQ1 hQ3
  set N : Subgroup Q := Subgroup.normalizer (Subgroup.zpowers c : Set Q) with hN
  have hCN : Lemma510Ns.fixSub (MulAut.conj c) ≤ N := fixSub_le_normalizer_zpowers c
  have hCnorm : ((Lemma510Ns.fixSub (MulAut.conj c)).subgroupOf N).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hCN]
    intro x n hx hn
    exact conj_mem_fixSub_of_mem_normalizer hn hx
  have hfix : Sec4.autFix (MulAut.conj c) = Subgroup.centralizer ({c} : Set Q) :=
    Sec4.RonanK429.RowV.autFix_conj_eq_centralizer c
  have hIC : I ≤ Sec4.autFix (MulAut.conj c) := hfix ▸ hD.le_centralizer
  have hsnC : (I.subgroupOf (Sec4.autFix (MulAut.conj c))).IsSubnormal := by
    rw [hfix]
    exact hD.isSubnormal
  have hIC' : I ≤ Lemma510Ns.fixSub (MulAut.conj c) := by
    rw [← Sec4.Ronan148L.autFix_eq_fixSub]
    exact hIC
  have hsubC : IsSubnormal I (Lemma510Ns.fixSub (MulAut.conj c)) :=
    Sec4.Ronan148L.open_isSubnormal_of_subgroupOf hIC' (by
      rw [← Sec4.Ronan148L.autFix_eq_fixSub]
      exact hsnC)
  have hsubN : IsSubnormal I N := hsubC.trans (IsSubnormal.step hCN hCnorm (IsSubnormal.refl N))
  have hbotN : GLAPPrimeCore 3 ↥N = ⊥ := gLAPPrimeCore_three_eq_bot N hcen
  have hbotNof : GLAPPrimeCoreOf 3 N = ⊥ := by
    show (GLAPPrimeCore 3 ↥N).map N.subtype = ⊥
    rw [hbotN, Subgroup.map_bot]
  have hle := glaPPrimeCoreOf_le_of_isSubnormal 3 hsubN
  rw [hbotNof, le_bot_iff] at hle
  have hbotI : CFSG.pPrimeCore 3 ↥I = ⊥ := by
    have h1 : (GLAPPrimeCore 3 ↥I).map I.subtype = ⊥ := hle
    rwa [Subgroup.map_eq_bot_iff, Subgroup.ker_subtype, le_bot_iff] at h1
  have hker : f.ker = ⊥ :=
    (CFSG.pPrimeCore_eq_bot_iff.1 hbotI) f.ker f.normal_ker
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hD.ker_three)
  have hinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).1 hker
  let e : ↥I ≃* Lb := MulEquiv.ofBijective f ⟨hinj, hD.surjective⟩
  have hqI : CFSG.IsQuasisimple ↥I :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hD.quasisimple_Lb
  have h3I : 3 ∣ Nat.card I := by
    have ho : orderOf (⟨c, hD.c_mem⟩ : ↥I) = 3 := by
      rw [Subgroup.orderOf_mk]
      exact hD.orderOf_c
    rw [← ho]
    exact orderOf_dvd_natCard _
  exact hno I (Sec4.Ronan148L.glaPComponent_of_autFix hIC hqI hsnC h3I)

end Char3

section Groups

theorem isChevOfChar_three_projSL_three_nine : IsChevOfChar 3 (projSL 3 (GaloisField 3 2)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hv : (LieTypeIndex.A 2 ⟨3, 2, Fact.out, by norm_num⟩).Valid :=
    Sec4.Ronan148L.valid_A (by norm_num) (fun h => absurd h (by norm_num)) fun _ => by
      simp only [TauCeti.PrimePower.card_def]
      norm_num
  exact ⟨⟨_, hv⟩, YS08.isChevIndexOfChar_of_lieIndexChar_eq (by simp [lieIndexChar]),
    ⟨(Census.typeAGroupEquivProjSL 2 ⟨3, 2, Fact.out, by norm_num⟩ hv).symm⟩⟩

theorem isChevOfChar_three_projSU_three_nine : IsChevOfChar 3 (projSU 3 3 2) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hv : (LieTypeIndex.twistedA 2 ⟨3, 2, Fact.out, by norm_num⟩).Valid :=
    Sec4.Ronan148L.valid_twistedA le_rfl fun _ => by
      simp only [TauCeti.PrimePower.card_def]
      norm_num
  exact ⟨⟨_, hv⟩, YS08.isChevIndexOfChar_of_lieIndexChar_eq (by simp [lieIndexChar]),
    ⟨(Census.typeTwistedAGroupEquivProjSU 2 ⟨3, 2, Fact.out, by norm_num⟩ hv).symm⟩⟩

theorem isChevOfChar_three_projSL_four_three : IsChevOfChar 3 (projSL 4 (GaloisField 3 1)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hv : (LieTypeIndex.A 3 ⟨3, 1, Fact.out, Nat.one_pos⟩).Valid :=
    Sec4.Ronan148L.valid_A (by norm_num) (fun h => absurd h (by norm_num)) fun _ => by
      simp only [TauCeti.PrimePower.card_def]
      norm_num
  exact ⟨⟨_, hv⟩, YS08.isChevIndexOfChar_of_lieIndexChar_eq (by simp [lieIndexChar]),
    ⟨(Census.typeAGroupEquivProjSL 3 ⟨3, 1, Fact.out, Nat.one_pos⟩ hv).symm⟩⟩

end Groups

section Holds

theorem kFCensus46EightChar3_holds : KFCensus46EightChar3 := by
  intro Q Lb _ _ _ c a I X f hQ hD
  exfalso
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases hQ with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
  · haveI : IsSimpleGroup (projSL 3 (GaloisField 3 2)) :=
      Sec19.Step1914TriProof.isSimpleGroup_projSL_three_of_field _
    exact census_false_of_char3 hD φ.isSimpleGroup
      (let ⟨d, hd, ⟨ψ⟩⟩ := isChevOfChar_three_projSL_three_nine; ⟨d, hd, ⟨φ.trans ψ⟩⟩)
  · haveI : IsSimpleGroup (projSU 3 3 2) :=
      Sec19.Step1914TriProof.isSimpleGroup_projSU_three_of_ne_two 3 2 (by norm_num)
        (by norm_num)
    exact census_false_of_char3 hD φ.isSimpleGroup
      (let ⟨d, hd, ⟨ψ⟩⟩ := isChevOfChar_three_projSU_three_nine; ⟨d, hd, ⟨φ.trans ψ⟩⟩)
  · haveI : IsSimpleGroup (projSL 4 (GaloisField 3 1)) :=
      CFSG.PGLModel.isSimpleGroup_projSL_of_two_le _ (by norm_num) (Or.inl (by norm_num))
        (Or.inl (by norm_num))
    exact census_false_of_char3 hD φ.isSimpleGroup
      (let ⟨d, hd, ⟨ψ⟩⟩ := isChevOfChar_three_projSL_four_three; ⟨d, hd, ⟨φ.trans ψ⟩⟩)

end Holds

end Hering129C

end CFSG.RankThree.PartTwo.Sec12
