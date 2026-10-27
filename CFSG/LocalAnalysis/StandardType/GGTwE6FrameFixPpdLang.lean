module

public import CFSG.LocalAnalysis.StandardType.GGTwE6DD2Torus
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelLangTorus
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelLiftT
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeToralityTw
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeBlock
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.WeylTorusAct
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.Dihedral.DihedralFusionPrefixes
public import CFSG.HardMathSupport.Solomon.Coordinator.B3FamPC
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerBridge
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools

public section

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace CFSG.StandardType.TwE6FrameFixPpd

open CFSG.HardMathSupport.Timmesfeld.Tables.T1b CFSG.HardMathSupport.Lang.E6Descent
  CFSG.RankThree.Classical2

theorem exists_lang_datum_of_pow_three
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2]
    (halg : letI := ZMod.algebra Ω 2; Algebra.IsAlgebraic (ZMod 2) Ω) {n : ℕ} (hn : 1 ≤ n)
    (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ n) {s : ModGL Tag.E6 Ω}
    (hs : s ∈ TwistedDiag.Rgrp Ω Fr) (hs3 : s ^ 3 = 1) :
    ∃ y ∈ adjointGroup Tag.E6 Ω, ∃ (a : Fin Tag.E6.rank → Ωˣ) (u : WeylGroup Tag.E6),
      (∀ i, a i ^ 3 = 1) ∧ weylAct u (a ^ 2 ^ n)⁻¹ = a ∧ s = y * rootDiagUnit Tag.E6 a * y⁻¹ ∧
      y⁻¹ * twistE6 Ω Fr y = canonicalRep (coxeterSystem Tag.E6) Ω (u * twE6W0) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hsG, hsF⟩ := (TwistedDiag.mem_Rgrp Fr).1 hs
  obtain ⟨g, hgG, hgT⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.exists_conj_torusGroup_of_pow_eq_one
      (τ := Tag.E6) (p := 3) Nat.prime_three
      (hmon := CFSG.HardMathSupport.Timmesfeld.CrossChar.monomialToralAt_E6_three)
      (ℓ := 2) (by decide) halg (x := s) hsG hs3
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hgT
  have hs_eq : s = g * rootDiagUnit Tag.E6 a * g⁻¹ := by
    rw [← ha]
    group
  have ha3 : ∀ i, a i ^ 3 = 1 := by
    have hd3 : rootDiagUnit Tag.E6 (a ^ 3) = 1 := by
      rw [← rootDiagUnit_pow]
      calc (rootDiagUnit Tag.E6 a) ^ 3 = (g⁻¹ * s * g) ^ 3 := by rw [ha]
        _ = g⁻¹ * s ^ 3 * g := by
          simpa [inv_inv] using (conj_pow (a := g⁻¹) (b := s) (i := 3))
        _ = 1 := by rw [hs3]; group
    have hprof : a ^ 3 = 1 := rootDiagUnit_injective (by rw [rootDiagUnit_one]; exact hd3)
    intro i
    exact congrFun hprof i
  have hFrEq : Fr = iterateFrobenius Ω 2 n :=
    RingHom.ext fun c => by rw [hFr, iterateFrobenius_def]
  have htw : twistE6 Ω Fr = twistHom TwistTag.E6 Ω (iterateFrobenius Ω 2 n) := by
    rw [hFrEq]
    rfl
  have hfix : ∀ s' : Unit, (g⁻¹ * twistE6 Ω Fr g) *
      twistE6 Ω Fr (rootDiagUnit Tag.E6 a) *
      (g⁻¹ * twistE6 Ω Fr g)⁻¹ = rootDiagUnit Tag.E6 a := by
    intro _
    have h := hsF
    rw [hs_eq, map_mul, map_mul, map_inv] at h
    calc (g⁻¹ * twistE6 Ω Fr g) * twistE6 Ω Fr (rootDiagUnit Tag.E6 a) *
          (g⁻¹ * twistE6 Ω Fr g)⁻¹
        = g⁻¹ * (twistE6 Ω Fr g * twistE6 Ω Fr (rootDiagUnit Tag.E6 a) *
            (twistE6 Ω Fr g)⁻¹) * g := by group
      _ = g⁻¹ * (g * rootDiagUnit Tag.E6 a * g⁻¹) * g := by rw [h]
      _ = rootDiagUnit Tag.E6 a := by group
  rw [htw] at hfix
  let gT : ModGL TwistTag.E6.tag Ω := g
  have hfixT : ∀ s' : Unit, (gT⁻¹ * twistHom TwistTag.E6 Ω (iterateFrobenius Ω 2 n) gT) *
      twistHom TwistTag.E6 Ω (iterateFrobenius Ω 2 n) (rootDiagUnit Tag.E6 a) *
      (gT⁻¹ * twistHom TwistTag.E6 Ω (iterateFrobenius Ω 2 n) gT)⁻¹ =
      rootDiagUnit Tag.E6 a := by
    intro s'
    exact hfix s'
  obtain ⟨w', z, hz, hlang⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_lang_datum_of_plane_twisted (ℓ := 2)
      TwistTag.E6 n hn (fun _ : Unit => a) hgG hfixT
  let wE : WeylGroup Tag.E6 := w'
  let zE : ModGL Tag.E6 Ω := z
  have hzE : zE ∈ CFSG.HardMathSupport.Timmesfeld.Torality.familyGroup
      (τ := Tag.E6) (K := Ω) (a := fun _ : Unit => a) := hz
  have hlangE : (g * zE)⁻¹ * twistE6 Ω Fr (g * zE) =
      canonicalRep (coxeterSystem Tag.E6) Ω wE := by
    rw [htw]
    change (gT * z)⁻¹ * twistHom TwistTag.E6 Ω (iterateFrobenius Ω 2 n) (gT * z) =
      canonicalRep (coxeterSystem TwistTag.E6.tag) Ω w'
    exact hlang
  let y : ModGL Tag.E6 Ω := g * zE
  have hyG : y ∈ adjointGroup Tag.E6 Ω := mul_mem hgG
    (CFSG.HardMathSupport.Timmesfeld.Torality.mem_familyCentralizer.1
      (CFSG.HardMathSupport.Timmesfeld.Torality.familyGroup_le_familyCentralizer
        (a := fun _ : Unit => a) hzE)).1
  have hzcent : zE * rootDiagUnit Tag.E6 a * zE⁻¹ = rootDiagUnit Tag.E6 a := by
    have h := (CFSG.HardMathSupport.Timmesfeld.Torality.mem_familyCentralizer.1
      (CFSG.HardMathSupport.Timmesfeld.Torality.familyGroup_le_familyCentralizer
        (a := fun _ : Unit => a) hzE)).2 ()
    rw [mul_inv_eq_iff_eq_mul] at h
    rw [mul_inv_eq_iff_eq_mul]
    exact h.symm
  have hs_y : s = y * rootDiagUnit Tag.E6 a * y⁻¹ := by
    rw [hs_eq]
    rw [show (g * zE) * rootDiagUnit Tag.E6 a * (g * zE)⁻¹ =
      g * (zE * rootDiagUnit Tag.E6 a * zE⁻¹) * g⁻¹ by group]
    rw [hzcent]
  let u : WeylGroup Tag.E6 := wE * twE6W0⁻¹
  have hu : u * twE6W0 = wE := by
    dsimp [u]
    group
  have hlast : y⁻¹ * twistE6 Ω Fr y =
      canonicalRep (coxeterSystem Tag.E6) Ω (u * twE6W0) := by
    rw [hu]
    exact hlangE
  have hnconj : canonicalRep (coxeterSystem Tag.E6) Ω wE *
      twistE6 Ω Fr (rootDiagUnit Tag.E6 a) *
      (canonicalRep (coxeterSystem Tag.E6) Ω wE)⁻¹ = rootDiagUnit Tag.E6 a := by
    have hFy : twistE6 Ω Fr y = y * canonicalRep (coxeterSystem Tag.E6) Ω wE := by
      have h := inv_mul_eq_iff_eq_mul.1 hlast
      rwa [hu] at h
    have h := hsF
    rw [hs_y, map_mul, map_mul, map_inv, hFy] at h
    have h' : y * (canonicalRep (coxeterSystem Tag.E6) Ω wE *
        twistE6 Ω Fr (rootDiagUnit Tag.E6 a) *
        (canonicalRep (coxeterSystem Tag.E6) Ω wE)⁻¹) * y⁻¹ =
        y * rootDiagUnit Tag.E6 a * y⁻¹ := by
      calc y * (canonicalRep (coxeterSystem Tag.E6) Ω wE *
            twistE6 Ω Fr (rootDiagUnit Tag.E6 a) *
            (canonicalRep (coxeterSystem Tag.E6) Ω wE)⁻¹) * y⁻¹
          = (y * canonicalRep (coxeterSystem Tag.E6) Ω wE) *
              twistE6 Ω Fr (rootDiagUnit Tag.E6 a) *
              (y * canonicalRep (coxeterSystem Tag.E6) Ω wE)⁻¹ := by group
        _ = y * rootDiagUnit Tag.E6 a * y⁻¹ := h
    exact mul_left_cancel (mul_right_cancel h')
  have htheta : TwistedDiag.n0 Ω * twistE6 Ω Fr (rootDiagUnit Tag.E6 a) *
      (TwistedDiag.n0 Ω)⁻¹ = rootDiagUnit Tag.E6 ((a ^ 2 ^ n)⁻¹) := by
    rw [← TwistedDiag.theta_apply Fr (rootDiagUnit Tag.E6 a)]
    exact TwistedDiag.theta_rootDiagUnit Fr hFr a
  have hFd : twistE6 Ω Fr (rootDiagUnit Tag.E6 a) =
      (TwistedDiag.n0 Ω)⁻¹ * rootDiagUnit Tag.E6 ((a ^ 2 ^ n)⁻¹) * TwistedDiag.n0 Ω := by
    rw [← htheta]
    group
  have hconj0 : TwistedDiag.n0 Ω *
      rootDiagUnit Tag.E6 (weylAct twE6W0 ((a ^ 2 ^ n)⁻¹)) *
      (TwistedDiag.n0 Ω)⁻¹ = rootDiagUnit Tag.E6 ((a ^ 2 ^ n)⁻¹) := by
    rw [show TwistedDiag.n0 Ω = canonicalRep (coxeterSystem Tag.E6) Ω twE6W0 from rfl]
    rw [CFSG.HardMathSupport.Timmesfeld.Tables.T1b.canonicalRep_conj_rootDiagUnit]
    congr 1
    rw [← weylAct_mul, TwistedDiag.twE6W0_mul_self, weylAct_one]
  have hn0inv : (TwistedDiag.n0 Ω)⁻¹ * rootDiagUnit Tag.E6 ((a ^ 2 ^ n)⁻¹) *
      TwistedDiag.n0 Ω = rootDiagUnit Tag.E6 (weylAct twE6W0 ((a ^ 2 ^ n)⁻¹)) := by
    rw [← hconj0]
    group
  have hFd' : twistE6 Ω Fr (rootDiagUnit Tag.E6 a) =
      rootDiagUnit Tag.E6 (weylAct twE6W0 ((a ^ 2 ^ n)⁻¹)) := by
    rw [hFd, hn0inv]
  have hweyl : weylAct u ((a ^ 2 ^ n)⁻¹) = a := by
    have huw : wE * twE6W0 = u := by
      dsimp [u]
      rw [TwistedDiag.twE6W0_inv]
    have h1 : weylAct wE (weylAct twE6W0 ((a ^ 2 ^ n)⁻¹)) = a := by
      apply rootDiagUnit_injective
      rw [← CFSG.HardMathSupport.Timmesfeld.Tables.T1b.canonicalRep_conj_rootDiagUnit]
      rw [hFd'] at hnconj
      exact hnconj
    calc weylAct u ((a ^ 2 ^ n)⁻¹) = weylAct (wE * twE6W0) ((a ^ 2 ^ n)⁻¹) := by rw [huw]
      _ = weylAct wE (weylAct twE6W0 ((a ^ 2 ^ n)⁻¹)) := weylAct_mul wE twE6W0 _
      _ = a := h1
  exact ⟨y, hyG, a, u, ha3, hweyl, hs_y, hlast⟩

theorem exists_inn_conj_langCube
    {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) (h3 : 3 ∣ 2 ^ n + 1) {Ω : Type} [Field Ω]
    [Algebra K Ω] [IsAlgClosure K Ω] (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    {g₁ g₂ : ModGL Tag.E6 Ω} (hg₁ : g₁ ∈ adjointGroup Tag.E6 Ω)
    (hgn₁ : g₁⁻¹ * twistE6 Ω Fr g₁ = TwistedDiag.n0 Ω) (hg₂ : g₂ ∈ adjointGroup Tag.E6 Ω)
    (hgn₂ : g₂⁻¹ * twistE6 Ω Fr g₂ = TwistedDiag.n0 Ω) :
    ∃ β ∈ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) →*
        MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)).range,
      (TwE6DD2.langCube hn hK σ hσ Fr hFr g₁).map (MulAut.conj β).toMonoidHom =
        TwE6DD2.langCube hn hK σ hσ Fr hFr g₂ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  haveI : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap K Ω).injective 2
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have h30 : (3 : Ω) ≠ 0 := three_ne_zero_of_dvd_card_add_one (ℓ := 2) hn h3
  obtain ⟨ζ, hζ, hζo⟩ := TwistedDiag.exists_cube_root (Ω := Ω) h30
  have hL : CFSG.StandardType.E6ThreeModel.IsLang Fr g₁ := ⟨hg₁, hgn₁⟩
  obtain ⟨D, hD⟩ := CFSG.StandardType.E6ThreeModel.exists_tFrame hn hK σ hσ Fr hFr h3 hL hζ hζo
  have hnot :=
    CFSG.StandardType.E6ThreeModel.langTorus_not_le_cgrp hn hK σ hσ Fr hFr h3 hL hζ hζo hD
  push Not at hnot
  obtain ⟨x, hxθ, hxCnot⟩ := hnot
  let R : Subgroup (ModGL Tag.E6 Ω) := TwistedDiag.Rgrp Ω Fr
  let C : Subgroup (ModGL Tag.E6 Ω) := TwistedDiag.Cgrp K σ.toRingHom Ω
  obtain ⟨hfinR, hCRle, hCnorm, hCidx, -⟩ :=
    TwistedDiag.cgrp_facts (ℓ := 2) (f := n) hn K hK σ.toRingHom hσ h3 Ω Fr hFr
  haveI : Finite ↥R := hfinR
  obtain ⟨c, hc, rfl⟩ := TwistedDiag.mem_thetaTorus.1 hxθ
  have hxfix : rootDiagUnit Tag.E6 c ∈ TwistedDiag.thetaFixed Fr := by
    rw [TwistedDiag.mem_thetaFixed]
    exact ⟨torusGroup_le_adjointGroup_E6 (rootDiagUnit_mem_torusGroup c),
      (TwistedDiag.theta_rootDiagUnit_eq_iff Fr hFr c).2 hc⟩
  let t : ModGL Tag.E6 Ω := g₁ * rootDiagUnit Tag.E6 c * g₁⁻¹
  have htR : t ∈ R := (TwistedDiag.mem_thetaFixed_iff_conj Fr hg₁ hgn₁ _).1 hxfix
  have htCnot : t ∉ C := hxCnot
  let hR : ↥R := ⟨g₂ * g₁⁻¹, TwE6DD2.mul_inv_mem_Rgrp Fr hg₁ hgn₁ hg₂ hgn₂⟩
  let tR : ↥R := ⟨t, htR⟩
  let CR : Subgroup ↥R := C.subgroupOf R
  haveI : CR.Normal := hCnorm
  have hcardq : Nat.card (↥R ⧸ CR) = 3 := by
    rw [← Subgroup.index_eq_card]
    exact hCidx
  have htRnot : tR ∉ CR := fun h => htCnot (Subgroup.mem_subgroupOf.1 h)
  have htq : (QuotientGroup.mk' CR tR : ↥R ⧸ CR) ≠ 1 := by
    intro hq
    apply htRnot
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hq
    exact hq
  have htop := zpowers_eq_top_of_prime_card hcardq (g := QuotientGroup.mk' CR tR) htq
  have hmk : (QuotientGroup.mk' CR hR : ↥R ⧸ CR) ∈
      Subgroup.zpowers (QuotientGroup.mk' CR tR) := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨e, he⟩ := Subgroup.mem_zpowers_iff.1 hmk
  let j : ℤ := -e
  let k : ModGL Tag.E6 Ω := g₂ * rootDiagUnit Tag.E6 c ^ j * g₁⁻¹
  have hk_eq : k = g₂ * g₁⁻¹ * t ^ j := by
    dsimp [k, t]
    rw [conj_zpow]
    group
  have hk_eq_coe : ((hR * tR ^ j : ↥R) : ModGL Tag.E6 Ω) = k := by
    dsimp [hR, tR, t, k]
    rw [conj_zpow]
    group
  have hkC : k ∈ C := by
    have hq : (QuotientGroup.mk' CR (hR * tR ^ j) : ↥R ⧸ CR) = 1 := by
      rw [map_mul, map_zpow, ← he]
      dsimp [j]
      rw [← zpow_add, add_neg_cancel, zpow_zero]
    have hmem : hR * tR ^ j ∈ CR := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hq
      exact hq
    rw [← hk_eq_coe]
    exact Subgroup.mem_subgroupOf.1 hmem
  have hkR : k ∈ R := by
    rw [← hk_eq_coe]
    exact (hR * tR ^ j).2
  let Φ := CFSG.StandardType.NoOffTwE6Three.rgrpConjAut hn hK σ hσ Fr hFr
  let xk : ↥R := ⟨k, hkR⟩
  let β : MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := Φ xk
  have hβrange : β ∈ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) →*
      MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)).range :=
    TwE6DD2.rgrpConjAut_mem_range_conj (x := k) hn hK σ hσ Fr hFr hkR hkC
  refine ⟨β, hβrange, ?_⟩
  have hxjcomm : ∀ b : Fin Tag.E6.rank → Ωˣ,
      rootDiagUnit Tag.E6 c ^ j * rootDiagUnit Tag.E6 b =
        rootDiagUnit Tag.E6 b * rootDiagUnit Tag.E6 c ^ j :=
    fun b => (rootDiagUnit_mul_comm_of_mem_torusGroup b
      (Subgroup.zpow_mem (torusGroup Tag.E6 Ω) (rootDiagUnit_mem_torusGroup c) j)).symm
  have hkconj : ∀ b : Fin Tag.E6.rank → Ωˣ,
      k * (g₁ * rootDiagUnit Tag.E6 b * g₁⁻¹) * k⁻¹ = g₂ * rootDiagUnit Tag.E6 b * g₂⁻¹ := by
    intro b
    calc k * (g₁ * rootDiagUnit Tag.E6 b * g₁⁻¹) * k⁻¹
        = g₂ * (rootDiagUnit Tag.E6 c ^ j * rootDiagUnit Tag.E6 b *
            (rootDiagUnit Tag.E6 c ^ j)⁻¹) * g₂⁻¹ := by
          dsimp [k]
          group
      _ = g₂ * rootDiagUnit Tag.E6 b * g₂⁻¹ := by
          rw [show rootDiagUnit Tag.E6 c ^ j * rootDiagUnit Tag.E6 b *
              (rootDiagUnit Tag.E6 c ^ j)⁻¹ = rootDiagUnit Tag.E6 b by
                rw [hxjcomm b]; group]
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨b, hb, hzR, rfl⟩ := (TwE6DD2.mem_langCube hn hK σ hσ Fr hFr).1 hz
    have hmem : g₂ * rootDiagUnit Tag.E6 b * g₂⁻¹ ∈ R := by
      have h := mul_mem (mul_mem hkR hzR) (inv_mem hkR)
      rwa [hkconj b] at h
    refine (TwE6DD2.mem_langCube hn hK σ hσ Fr hFr).2 ⟨b, hb, hmem, ?_⟩
    change Φ ⟨g₂ * rootDiagUnit Tag.E6 b * g₂⁻¹, hmem⟩ =
      Φ xk * Φ ⟨g₁ * rootDiagUnit Tag.E6 b * g₁⁻¹, hzR⟩ * (Φ xk)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    refine Subtype.ext ?_
    change g₂ * rootDiagUnit Tag.E6 b * g₂⁻¹ =
      k * (g₁ * rootDiagUnit Tag.E6 b * g₁⁻¹) * k⁻¹
    exact (hkconj b).symm
  · intro hy
    obtain ⟨b, hb, hyR, rfl⟩ := (TwE6DD2.mem_langCube hn hK σ hσ Fr hFr).1 hy
    have hmem : g₁ * rootDiagUnit Tag.E6 b * g₁⁻¹ ∈ R := by
      have h := mul_mem (mul_mem (inv_mem hkR) hyR) hkR
      rwa [show (k)⁻¹ * (g₂ * rootDiagUnit Tag.E6 b * g₂⁻¹) * k =
        g₁ * rootDiagUnit Tag.E6 b * g₁⁻¹ by
          rw [← hkconj b]; group] at h
    refine ⟨Φ ⟨g₁ * rootDiagUnit Tag.E6 b * g₁⁻¹, hmem⟩,
      (TwE6DD2.mem_langCube hn hK σ hσ Fr hFr).2 ⟨b, hb, hmem, rfl⟩, ?_⟩
    change Φ xk * Φ ⟨g₁ * rootDiagUnit Tag.E6 b * g₁⁻¹, hmem⟩ * (Φ xk)⁻¹ =
      Φ ⟨g₂ * rootDiagUnit Tag.E6 b * g₂⁻¹, hyR⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    refine Subtype.ext ?_
    change k * (g₁ * rootDiagUnit Tag.E6 b * g₁⁻¹) * k⁻¹ =
      g₂ * rootDiagUnit Tag.E6 b * g₂⁻¹
    exact hkconj b

end CFSG.StandardType.TwE6FrameFixPpd
