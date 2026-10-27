module

public import CFSG.RankThree.PartTwo.Sec8.Hering88NWire
public import CFSG.RankThree.PartTwo.Sec8.Hering88NLemmaBD4
public import CFSG.RankThree.PartTwo.Sec8.Hering88NOrderEight
import CFSG.RankThree.PartTwo.Sec8.Hering88NLemmaA
import CFSG.HardMathSupport.Lang.AnisoE6.E6InF4
public import CFSG.RankThree.PartTwo.Sec8.Hering88NBeta

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering88N

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSp)
open CFSG.Blueprint.Chevalley

theorem exists_surjective_imageModTheta_quot {G : Type} [Group G] [Finite G] {W M : Subgroup G}
    (hWM : W ≤ M) :
    ∃ f : imageModTheta M W →* W ⧸ aschbacherSolvableCore 3 W, Function.Surjective f := by
  obtain ⟨-, -, -, hθmax, -⟩ :=
    solvable_prime_complement_core_characterization (H := W) Nat.prime_three
  set ρ := Item87Proof.modThetaOnto hWM with hρ
  have hρs := Item87Proof.modThetaOnto_surjective hWM
  have hker : ρ.ker ≤ aschbacherSolvableCore 3 W :=
    hθmax _ (MonoidHom.normal_ker ρ) (Item87Proof.isSolvable_ker_modThetaOnto hWM)
      (Item87Proof.not_three_dvd_card_ker_modThetaOnto hWM)
  set e := QuotientGroup.quotientKerEquivOfSurjective ρ hρs with he
  refine ⟨(QuotientGroup.map ρ.ker (aschbacherSolvableCore 3 W) (MonoidHom.id W)
    (fun x hx => hker hx)).comp e.symm.toMonoidHom, ?_⟩
  intro y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ y
  refine ⟨e (QuotientGroup.mk x), ?_⟩
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
  rfl

theorem exists_zpow_mul_zpow_of_mem_closure {G : Type} [Group G] {A : Subgroup G}
    (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) {c b d : G} (hc : c ∈ A) (hb : b ∈ A)
    (hd : d ∈ Subgroup.closure ({c, b} : Set G)) : ∃ i j : ℤ, c ^ i * b ^ j = d := by
  letI : CommGroup A := { (inferInstance : Group A) with
    mul_comm := fun x y => Subtype.ext (hA x x.2 y y.2) }
  have hmap : (Subgroup.closure ({⟨c, hc⟩, ⟨b, hb⟩} : Set A)).map A.subtype =
      Subgroup.closure ({c, b} : Set G) := by
    rw [MonoidHom.map_closure, Set.image_pair]
    rfl
  rw [← hmap] at hd
  obtain ⟨y, hy, rfl⟩ := hd
  obtain ⟨i, j, hij⟩ := Subgroup.mem_closure_pair.mp hy
  exact ⟨i, j, by rw [← hij]; simp⟩

section Certified

theorem five_not_dvd_card_of_case1 {Q : Type} [Group Q] {m : ℕ} (hodd : Odd m)
    (hQ : IsoTrialityD4 Q m ∨ IsoGTwoEven Q (3 * m)) : ¬ 5 ∣ Nat.card Q := by
  rcases hQ with ⟨q, hv, hq2, hqe, ⟨e⟩⟩ | ⟨K, _, _, hK, ⟨e⟩⟩
  · rw [Nat.card_congr e.toEquiv, Sec11.KSListsProof.card_trialityD4_carrier,
      TauCeti.PrimePower.card_def, hq2, hqe]
    exact five_not_dvd_ordTrialityD4 hodd
  · rw [Nat.card_congr e.toEquiv, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hK]
    exact five_not_dvd_ordG2_cube hodd

theorem case83One_of_data83 {G : Type} [Group G] [Finite G] {a : G} {Y : Subgroup G} {x : G}
    {A₀ : Subgroup G} {d : G} {n m : ℕ} (hD : Data83 G a Y x A₀ d n) (hm : 1 ≤ m)
    (hY1 : IsoTrialityD4 (Y ⧸ aschbacherSolvableCore 3 Y) m ∨
      IsoGTwoEven (Y ⧸ aschbacherSolvableCore 3 Y) (3 * m)) :
    n = m ∧ Case83One Y x A₀ d n := by
  have hn : 1 ≤ n := hD.odd.pos
  have hsig : Item86ResProof.SigD4 (Y ⧸ aschbacherSolvableCore 3 Y) m ∨
      Item86ResProof.SigG2 (Y ⧸ aschbacherSolvableCore 3 Y) m := by
    rcases hY1 with hDm | hGm
    · exact Or.inl (Item86ResProof.sigD4_of_isoTrialityD4 hm hDm)
    · exact Or.inr (Item86ResProof.sigG2_of_isoGTwo hm
        (Item86ResProof.isoGTwo_of_isoGTwoEven (by omega) hGm))
  have hγm : Item86ResProof.IsGammaType (Y ⧸ aschbacherSolvableCore 3 Y) m := by
    rcases hY1 with hDm | hGm
    · exact Or.inr (Or.inl hDm)
    · exact Or.inr (Or.inr (Or.inl (Item86ResProof.isoGTwo_of_isoGTwoEven (by omega) hGm)))
  have hnm : n = m :=
    Item86ResProof.eq_of_isGammaType hn hm (Item86ResProof.isGammaType_of_data83 hD) hγm
  refine ⟨hnm, ?_⟩
  subst hnm
  rcases hD.cases with h1 | ⟨hR, -, -⟩ | ⟨hS, -, -⟩ | ⟨⟨e⟩, -, -⟩ | ⟨⟨e⟩, -, -⟩
  · exact h1
  · exfalso
    have hF := Item86ResProof.sigF4_of_reeF4 hn (Item86ResProof.reeF4_of_isoReeF4 (by omega) hR)
    rcases hsig with hDs | hGs
    · exact hF.false_of_sigD4 hDs hn
    · exact hF.false_of_sigG2 hGs hn
  · exfalso
    have hU := Item86ResProof.sigU_of_unitarySig
      (Item86ResProof.unitarySig_of_isoSUThree (by omega) hS)
    rcases hsig with hDs | hGs
    · exact hDs.false_of_sigU hU hn
    · exact hGs.false_of_sigU hU hn
  · exfalso
    have hU := Item86ResProof.sigU_of_unitarySig (Item86ResProof.unitarySig_of_projSU (by omega) e)
    rcases hsig with hDs | hGs
    · exact hDs.false_of_sigU hU hn
    · exact hGs.false_of_sigU hU hn
  · exfalso
    have hSs := Item86ResProof.sigSp4_of_projSp hn e
    rcases hsig with hDs | hGs
    · exact hDs.false_of_sigSp4 hSs hn
    · exact hGs.false_of_sigSp4 hSs hn hn

theorem sp4two_residual {Q : Type} [Group Q] [Finite Q] {C : Subgroup Q}
    (e : C ≃* projSp 2 (GaloisField 2 1)) :
    IsSimpleGroup (inSubgroup perfectResidual C) ∧
      5 ∣ Nat.card (inSubgroup perfectResidual C) := by
  have hF2 : Nat.card (GaloisField 2 1) = 2 := by rw [GaloisField.card 2 1 (by norm_num), pow_one]
  set φ : C ≃* CFSG.ComponentClassification.PresentationLocal.sympFour :=
    (e.trans (CFSG.Adapters.RankTwoModelTransports.statedProjEquivMapMk _).symm).trans
      (CFSG.RankThree.PartOne.KCSpComm.statedProjEquivSympFour hF2) with hφ
  obtain ⟨hq, hodd⟩ := CFSG.RankThree.PartOne.derived_of_mulEquiv_sympFour φ
  have heq : perfectResidual C = commutator C := by
    refine le_antisymm ?_ ((CFSG.perfect_residual_transport (MonoidHom.id C)).2.2 _ hq.1)
    have h := iInf_le (fun i => derivedSeries C i) 1
    rwa [derivedSeries_one] at h
  have e' : commutator C ≃* commutator CFSG.ComponentClassification.PresentationLocal.sympFour :=
    ((commutator C).equivMapOfInjective φ.toMonoidHom φ.injective).trans
      (MulEquiv.subgroupCongr (map_commutator_mulEquiv φ))
  haveI := CFSG.ComponentClassification.PresentationLocal.isSimpleGroup_commutator_sympFour
  haveI hs : IsSimpleGroup (commutator C) := e'.isSimpleGroup
  have hC : Nat.card C = 720 := by
    rw [Nat.card_congr e.toEquiv]
    exact Item812Res2.card_projSp_two_one
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := C) 5 (by rw [hC]; norm_num)
  have hwC : w ∈ commutator C :=
    hodd (p := 5) (by norm_num) (by norm_num) w (by rw [← hw]; exact pow_orderOf_eq_one w)
  have h5 : 5 ∣ Nat.card (commutator C) := by
    have := orderOf_dvd_natCard (⟨w, hwC⟩ : commutator C)
    rwa [Subgroup.orderOf_mk, hw] at this
  have eI : inSubgroup perfectResidual C ≃* commutator C :=
    ((perfectResidual C).equivMapOfInjective C.subtype C.subtype_injective).symm.trans
      (MulEquiv.subgroupCongr heq)
  exact ⟨eI.isSimpleGroup, by rw [Nat.card_congr eI.toEquiv]; exact h5⟩

theorem thetaQuotMulAut_eq_one_of_isInnerAut {G : Type} [Group G] [Finite G] {Y W : Subgroup G}
    {w : G} {m : ℕ} (hodd : Odd m)
    (hY1 : IsoTrialityD4 (Y ⧸ aschbacherSolvableCore 3 Y) m ∨
      IsoGTwoEven (Y ⧸ aschbacherSolvableCore 3 Y) (3 * m))
    (hwN : w ∈ Subgroup.normalizer (Y : Set G)) (hw3 : w ^ 3 = 1) (hWY : W ≤ Y)
    (hWw : W ≤ Subgroup.centralizer ({w} : Set G)) (hWp : Group.IsPerfect W)
    (h8 : ∃ t : W ⧸ aschbacherSolvableCore 3 W, (∃ k : ℕ, t ^ 2 ^ k = 1) ∧ t ^ 4 ≠ 1)
    (hin : KFacts.IsInnerAut (Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨w, hwN⟩))) :
    Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨w, hwN⟩) = 1 := by
  classical
  set α := Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨w, hwN⟩) with hα
  have hZ := Hering88F.center_eq_bot_of_case1 hY1
  have hinj := Item812Res7.conj_injective_of_center_trivial hZ
  obtain ⟨g, hg⟩ := hin
  have hgα : MulAut.conj g = α := hg
  by_contra hne
  have hα3 : α ^ 3 = 1 := by
    rw [hα, ← map_pow, ← map_pow]
    have : (⟨w, hwN⟩ : Subgroup.normalizer (Y : Set G)) ^ 3 = 1 := Subtype.ext (by simpa using hw3)
    rw [this, map_one, map_one]
  have hg3 : g ^ 3 = 1 := by
    apply hinj
    rw [map_pow, hgα, hα3, map_one]
  have hg1 : g ≠ 1 := by
    rintro rfl
    apply hne
    rw [← hgα]
    exact map_one _
  have hπ : imageModTheta Y W ≤ barCentralizer (Subgroup.zpowers w) Y := by
    rw [← KFacts.imageModTheta_centralizer_eq hwN ⟨1, by simpa using hw3⟩]
    exact Hering88F.imageModTheta_mono' (le_inf hWY hWw)
  have hπg : imageModTheta Y W ≤ Subgroup.centralizer ({g} : Set (Y ⧸ aschbacherSolvableCore 3 Y)) := by
    intro x hx
    have hx' := (KFacts.mem_barCentralizer_zpowers_iff hwN x).mp (hπ hx)
    rw [← hα, ← hgα, MulAut.conj_apply] at hx'
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * g = g * x * g⁻¹ * g := by rw [hx']
      _ = g * x := by group
  have hWbar : Group.IsPerfect (imageModTheta Y W) :=
    hWp.ofSurjective (f := Item87Proof.modThetaOnto hWY) (Item87Proof.modThetaOnto_surjective hWY)
  have hB : ∀ t : imageModTheta Y W, (∃ k : ℕ, t ^ 2 ^ k = 1) → t ^ 2 ^ 2 = 1 := by
    intro t ht
    obtain ⟨k, hk⟩ := ht
    have h4 := lemmaB hodd hY1 hg3 hg1 hWbar hπg t.2 ⟨k, by rw [← Subgroup.coe_pow, hk]; rfl⟩
    exact Subtype.ext (by rw [Subgroup.coe_pow]; simpa using h4)
  obtain ⟨f, hf⟩ := exists_surjective_imageModTheta_quot hWY
  obtain ⟨t, ht2, ht4⟩ := h8
  have h4 := pow_two_pow_eq_one_of_mem_range f (j := 2) hB ((MonoidHom.range_eq_top.mpr hf) ▸
    Subgroup.mem_top t) ht2
  exact ht4 (by simpa using h4)

theorem exists_pow_eight_adjointGroup_G2 {K : Type} [Field K] [Finite K] [CharP K 2] :
    ∃ t : adjointGroup .G2 K, t ^ 8 = 1 ∧ t ^ 4 ≠ 1 := by
  obtain ⟨φ, -⟩ := G2Two.exists_mulEquiv_cayley_two (k := ZMod 2) (by simp)
  set t₀ := φ.symm G2Two.ord8 with ht₀
  have h8 : t₀ ^ 8 = 1 := by rw [ht₀, ← map_pow, G2Two.ord8_pow_eight, map_one]
  have h4 : t₀ ^ 4 ≠ 1 := fun h => G2Two.ord8_pow_four (φ.symm.injective (by
    rw [map_pow, map_one]; exact h))
  set f : ZMod 2 →+* K := ZMod.castHom (dvd_refl 2) K with hf
  refine ⟨⟨CFSG.LieType.Chevalley.baseChangeGL f (t₀ : ModGL .G2 (ZMod 2)),
    CFSG.HardMathSupport.Lang.AnisoE6.baseChangeGL_mem_adjointGroup_of_mem f t₀.2⟩, ?_, ?_⟩
  · apply Subtype.ext
    rw [Subgroup.coe_pow, ← map_pow, ← Subgroup.coe_pow, h8, Subgroup.coe_one, map_one,
      Subgroup.coe_one]
  · intro h
    apply h4
    apply Subtype.ext
    apply CFSG.LieType.Chevalley.baseChangeGL_injective f
    have := congrArg Subtype.val h
    rw [Subgroup.coe_pow, ← map_pow] at this
    rw [Subgroup.coe_pow, this, Subgroup.coe_one, Subgroup.coe_one, map_one]

theorem exists_pow_eight_of_isoGTwoEven {Q : Type} [Group Q] [Finite Q] {R : Subgroup Q}
    {n : ℕ} (h : IsoGTwoEven R n) (hn : 1 ≤ n) :
    ∃ t ∈ inSubgroup perfectResidual R, t ^ 8 = 1 ∧ t ^ 4 ≠ 1 := by
  rcases Nat.lt_or_ge n 2 with h1 | h2
  · obtain rfl : n = 1 := by omega
    exact exists_pow_eight_of_isoGTwoEven_one h
  · rw [Hering88F.inSubgroup_perfectResidual_eq_of_isoGTwoEven h2 h]
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
    haveI : CharP K 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
        Nat.prime_two (k := n) (by omega) hK
    obtain ⟨t, ht8, ht4⟩ := exists_pow_eight_adjointGroup_G2 (K := K)
    refine ⟨(e.symm t : Q), (e.symm t).2, ?_, ?_⟩
    · rw [← Subgroup.coe_pow, ← map_pow, ht8, map_one, Subgroup.coe_one]
    · intro h4
      apply ht4
      apply e.symm.injective
      rw [map_pow, map_one]
      exact Subtype.ext (by rw [Subgroup.coe_pow]; exact h4)

theorem exists_order_eight_quot_of_isoGTwoEven {G : Type} [Group G] [Finite G] {W M : Subgroup G}
    (hWM : W ≤ M) {C : Subgroup (M ⧸ aschbacherSolvableCore 3 M)}
    (hW : imageModTheta M W = inSubgroup perfectResidual C) {n : ℕ} (hC : IsoGTwoEven C n)
    (hn : 1 ≤ n) :
    ∃ s : W ⧸ aschbacherSolvableCore 3 W, (∃ k : ℕ, s ^ 2 ^ k = 1) ∧ s ^ 4 ≠ 1 := by
  have hS : IsSimpleGroup (inSubgroup perfectResidual C) := by
    rcases Nat.lt_or_ge n 2 with h1 | h2
    · obtain rfl : n = 1 := by omega
      exact isSimpleGroup_inSubgroup_perfectResidual_of_isoGTwoEven_one hC
    · exact Hering88E.isSimpleGroup_perfectResidual_of_isoGTwoEven h2 hC
  have hθ : NoThetaNormal ↥(imageModTheta M W) := by
    haveI := hS
    exact Item87Proof.NoThetaNormal.of_mulEquiv (MulEquiv.subgroupCongr hW)
      (Item812Res10.noThetaNormal_of_isSimpleGroup_of_isPerfect (Item87Proof.isPerfect_residual _))
  obtain ⟨χ⟩ := Item87Proof.nonempty_quot_mulEquiv_imageModTheta hWM hθ
  obtain ⟨t, htR, ht8, ht4⟩ := exists_pow_eight_of_isoGTwoEven hC hn
  have htW : t ∈ imageModTheta M W := hW ▸ htR
  refine ⟨χ.symm ⟨t, htW⟩, ⟨3, ?_⟩, ?_⟩
  · rw [← map_pow]
    have : (⟨t, htW⟩ : imageModTheta M W) ^ 2 ^ 3 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; simpa using ht8)
    rw [this, map_one]
  · intro h4
    apply ht4
    have h1 : (⟨t, htW⟩ : imageModTheta M W) ^ 4 = 1 := by
      apply χ.symm.injective
      rw [map_pow, h4, map_one]
    have := congrArg Subtype.val h1
    rwa [Subgroup.coe_pow] at this

theorem swap_data_of_order_eight
    (h45 : Sec4.Item4_5) (h83 : Item83) (h84 : Pair84A)
    {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a b : G}
    {X : Subgroup G} {n : ℕ} (h : Sec8Pair G A c L a b X n)
    {Y : Subgroup G} (hY : Y ∈ thetaComponentsAt 3 a) (hIJ : sec8I L a ⊔ sec8J X a ≤ Y)
    (hxY : KFacts.InducesStdKind Y c .field ∨ KFacts.InducesStdKind Y c .graphField)
    {m : ℕ} (hodd : Odd m)
    (hY1 : IsoTrialityD4 (Y ⧸ aschbacherSolvableCore 3 Y) m ∨
      IsoGTwoEven (Y ⧸ aschbacherSolvableCore 3 Y) (3 * m))
    {d : G} (hdcl : d ∈ Subgroup.closure ({c, b} : Set G)) (hdx : d ∉ Subgroup.zpowers c)
    (hdN : d ∈ Subgroup.normalizer (Y : Set G))
    (hin : KFacts.IsInnerAut (Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨d, hdN⟩)))
    (hne : Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨d, hdN⟩) ≠ 1)
    (h8 : ∃ s : sec8J X a ⧸ aschbacherSolvableCore 3 (sec8J X a),
      (∃ k : ℕ, s ^ 2 ^ k = 1) ∧ s ^ 4 ≠ 1) :
    (KFacts.InducesStdKind Y b .field ∨ KFacts.InducesStdKind Y b .graphField) ∧
      d ∉ Subgroup.zpowers b ∧ ∃ (A₀' : Subgroup G) (d'' : G), Case83One Y b A₀' d'' m := by
  classical
  obtain ⟨hAc, hA3⟩ := Hering88C.pair_commute_pow_three h
  obtain ⟨hbA, hb1, -, -⟩ := Item87Proof.isGammaIndex_cases h.isGammaIndex
  have hb3 : b ^ 3 = 1 := hA3 b hbA
  have hc3 : c ^ 3 = 1 := hA3 c h.mem_A
  have hcN : c ∈ Subgroup.normalizer (Y : Set G) :=
    hxY.elim (fun h' => h'.mem_normalizer) (fun h' => h'.mem_normalizer)
  have hcout : Sec4.InducesOuterTheta c Y := by
    rcases hxY with h' | h'
    · exact KFacts.InducesStdKind.inducesOuterTheta Y h' (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta Y h' (by decide)
  have hX : X ∈ thetaComponentsAt 3 b := h.pairRel.2.2.1
  have hXb : X ≤ Subgroup.centralizer ({b} : Set G) := (PartOne.mem_thetaComponentsAt_iff.mp hX).1
  have hJX : sec8J X a ≤ X := (Item87Proof.residual_le _).trans inf_le_left
  have hJY : sec8J X a ≤ Y := le_sup_right.trans hIJ
  have hJb : sec8J X a ≤ Subgroup.centralizer ({b} : Set G) := hJX.trans hXb
  have hJp : Group.IsPerfect (sec8J X a) := Item87Proof.isPerfect_residual _
  obtain ⟨i, j, hij⟩ := exists_zpow_mul_zpow_of_mem_closure (fun u hu v hv => hAc u hu v hv)
    h.mem_A hbA hdcl
  have hbj1 : b ^ j ≠ 1 := by
    intro h1
    apply hdx
    rw [← hij, h1, mul_one]
    exact zpow_mem (Subgroup.mem_zpowers _) i
  have hbjN : b ^ j ∈ Subgroup.normalizer (Y : Set G) := by
    have e : b ^ j = (c ^ i)⁻¹ * d := by rw [← hij]; group
    rw [e]
    exact mul_mem (inv_mem (zpow_mem hcN i)) hdN
  have hbN : b ∈ Subgroup.normalizer (Y : Set G) :=
    (Subgroup.zpowers_le.mpr hbjN)
      (Item87Proof.mem_zpowers_of_mem_zpowers hb3 hbj1 (zpow_mem (Subgroup.mem_zpowers b) j))
  set α : Subgroup.normalizer (Y : Set G) →* MulAut (Y ⧸ aschbacherSolvableCore 3 Y) :=
    (Sec4.thetaQuotMulAut Y).comp (Sec4.compAction Y) with hαdef
  have hαd : α ⟨d, hdN⟩ = α ⟨c, hcN⟩ ^ i * α ⟨b, hbN⟩ ^ j := by
    rw [← map_zpow, ← map_zpow, ← map_mul]
    congr 1
    exact Subtype.ext (by simp [hij])
  have hαc3 : α ⟨c, hcN⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨c, hcN⟩ : Subgroup.normalizer (Y : Set G)) ^ 3 = 1 := Subtype.ext (by simpa using hc3)
    rw [this, map_one]
  have hαd1 : α ⟨d, hdN⟩ ≠ 1 := hne
  have hαdin : α ⟨d, hdN⟩ ∈ (MulAut.conj : Y ⧸ aschbacherSolvableCore 3 Y →*
      MulAut (Y ⧸ aschbacherSolvableCore 3 Y)).range := hin
  obtain ⟨hx', hxout⟩ := hcout
  have hbout : Sec4.InducesOuterTheta b Y := by
    refine ⟨hbN, fun hbin => ?_⟩
    have h1 := thetaQuotMulAut_eq_one_of_isInnerAut hodd hY1 hbN hb3 hJY hJb hJp h8 hbin
    have h1' : α ⟨b, hbN⟩ = 1 := h1
    have hαd' : α ⟨d, hdN⟩ = α ⟨c, hcN⟩ ^ i := by rw [hαd, h1', one_zpow, mul_one]
    have hmem : α ⟨c, hcN⟩ ∈ Subgroup.zpowers (α ⟨d, hdN⟩) :=
      Item87Proof.mem_zpowers_of_mem_zpowers hαc3 hαd1
        (hαd' ▸ zpow_mem (Subgroup.mem_zpowers _) i)
    exact hxout ((Subgroup.zpowers_le.mpr hαdin) hmem)
  have hbY : KFacts.InducesStdKind Y b .field ∨ KFacts.InducesStdKind Y b .graphField := by
    rcases hY1 with hD | hG
    · obtain ⟨hm1, K, _, _, σ, hK, hσ, ⟨e⟩⟩ := Item812Res7.exists_trialityD4_model hD
      exact Or.inr (KFacts.InducesStdKind.triality m hm1 K hK σ hσ
        (KFacts.inducesKindTriality_graphField hm1 hK hσ Y hb3 hbout e))
    · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hG
      haveI : CharP K 2 :=
        CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
          Nat.prime_two (k := 3 * m) (by have := hodd.pos; omega) hK
      have hK3 : ringChar K ≠ 3 := by rw [ringChar.eq K 2]; norm_num
      have hK4 : 4 ≤ Nat.card K := by
        rw [hK]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (3 * m) := Nat.pow_le_pow_right (by norm_num) (by have := hodd.pos; omega)
      exact Or.inl (KFacts.InducesStdKind.g2 K hK3 hK4
        (KFacts.inducesKindG2_field Y hK3 hK4 hb3 hbout e))
  have hdb : d ∉ Subgroup.zpowers b := by
    intro hdbm
    have hd1 : d ≠ 1 := by
      rintro rfl
      apply hαd1
      rw [show (⟨1, hdN⟩ : Subgroup.normalizer (Y : Set G)) = 1 from rfl, map_one]
    obtain ⟨hbN', hbout'⟩ := hbout
    apply hbout'
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
      (Item87Proof.mem_zpowers_of_mem_zpowers hb3 hd1 hdbm)
    have hbd : (⟨b, hbN'⟩ : Subgroup.normalizer (Y : Set G)) = ⟨d, hdN⟩ ^ k :=
      Subtype.ext (by simp [hk])
    show α ⟨b, hbN'⟩ ∈ _
    rw [hbd, map_zpow]
    exact zpow_mem hαdin k
  obtain ⟨A₀', d'', n', hD⟩ := kF88Data83Y_of h83 (kF88SwapCent_holds h45 h84)
    (kF88SwapInv_holds h45 h84) h hY hIJ (Or.inr rfl) hbY
  obtain ⟨hn', hc1'⟩ := case83One_of_data83 hD hodd.pos hY1
  subst hn'
  exact ⟨hbY, hdb, A₀', d'', hc1'⟩

theorem kF88Case1ClassBOneUnitary_of
    (h45 : Sec4.Item4_5) (h47 : Sec4.Inputs47ClassesD4) (h83 : Item83) (h84 : Pair84A)
    (hPG : PartnerGamma88) : KF88Case1ClassBOneUnitary := by
  intro G _ _ A c L a b X h hU Y hY hIJ x hxc hxY A₀ d' m hodd hc1 d hdcl hdx hdA hd3 hdN hin
    hne _
  subst hxc
  classical
  obtain ⟨-, hA3⟩ := Hering88C.pair_commute_pow_three h
  have ha3 : a ^ 3 = 1 := hA3 a h.a_mem
  have hY1 := hc1.1
  have hk := h84 G A x L a b X 1 h
  have haX : a ∈ Subgroup.normalizer (X : Set G) :=
    hk.elim (fun h' => h'.mem_normalizer) (fun h' => h'.mem_normalizer)
  have hJX : sec8J X a ≤ X := (Item87Proof.residual_le _).trans inf_le_left
  have hJY : sec8J X a ≤ Y := le_sup_right.trans hIJ
  have hJX_img : imageModTheta X (sec8J X a) =
      inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers a) X) :=
    KFacts.imageModTheta_perfectResidual_centralizer_eq haX ⟨1, by simpa using ha3⟩
  rcases h.centralizer_of_unitary ⟨3, hU⟩ with hCX | hSp
  swap
  ·
    exfalso
    obtain ⟨ι⟩ := hSp
    obtain ⟨hS, h5⟩ := sp4two_residual ι
    have hN := card_quot_theta_eq_of_isSimpleGroup hJX hJX_img hS
    have hdvd := card_quot_theta_dvd_card_imageModTheta hJY
    rw [hN] at hdvd
    exact five_not_dvd_card_of_case1 hodd hY1
      ((h5.trans hdvd).trans (Subgroup.card_subgroup_dvd_card _))
  have h8 := exists_order_eight_quot_of_isoGTwoEven hJX hJX_img hCX le_rfl
  obtain ⟨hbY, hdb, A₀', d'', hc1'⟩ :=
    swap_data_of_order_eight h45 h83 h84 h hY hIJ hxY hodd hY1 hdcl hdx hdN hin hne h8
  exact classBSwapOne h45 h47 h84 hPG h hY hIJ hbY hodd hc1' hdcl hdb hdA hd3 hdN hin hne

theorem kF88Case1ClassBOne_of
    (h45 : Sec4.Item4_5) (h47 : Sec4.Inputs47ClassesD4) (h83 : Item83) (h84 : Pair84A)
    (hPG : PartnerGamma88) : KF88Case1ClassBOne :=
  kF88Case1ClassBOne_of_unitary h45 h47 (kF88Case1ClassBOneUnitary_of h45 h47 h83 h84 hPG)

end Certified

end CFSG.RankThree.PartTwo.Sec8.Hering88N

end
