module

public import CFSG.RankThree.PartTwo.Sec12.Hering129LD42
public import CFSG.RankThree.PartTwo.Sec12.Hering129D4HTwo
import CFSG.RankThree.PartTwo.Sec12.Hering129KEi
import CFSG.RankThree.PartTwo.Sec8.Hering418FDich
import CFSG.RankThree.PartTwo.Sec12.Hering129LTypEight
public import CFSG.RankThree.PartTwo.Sec12.Hering129KFix
public import CFSG.RankThree.PartTwo.Sec12.Hering129KSub
public import CFSG.RankThree.PartTwo.Sec12.Hering129KY5
public import CFSG.RankThree.PartTwo.Sec12.Hering129KYa
public import CFSG.RankThree.PartTwo.Sec8.Hering418ROuter

public section

namespace CFSG.RankThree.PartTwo.Sec12

namespace Hering129L

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)

section Num

theorem eq_eight_of_card_eq {q : ℕ} (h4 : 4 ≤ q)
    (hN : 504 * Nat.gcd 2 (q - 1) = q * (q ^ 2 - 1)) : q = 8 := by
  have hq : q < 12 := by
    by_contra hge
    push Not at hge
    have h1 : 12 * 12 ≤ q ^ 2 := by nlinarith
    have h2 : Nat.gcd 2 (q - 1) ≤ 2 := Nat.gcd_le_left _ (by norm_num)
    have h3 : q ^ 2 - 1 ≥ 143 := by omega
    have h5 : q * (q ^ 2 - 1) ≥ 12 * 143 := Nat.mul_le_mul hge h3
    have h6 : 504 * Nat.gcd 2 (q - 1) ≤ 504 * 2 := Nat.mul_le_mul_left _ h2
    omega
  interval_cases q <;> first | rfl | (exfalso; revert hN; decide)

end Num

section Model

open CFSG.RankThree.PartTwo.Sec19 (C0 Asub Bsub D4Par asubEquiv bsubEquiv finite_C0)
open CFSG.RankThree.PartTwo.Sec12.Hering129D4H


variable {X : Type} [Field X] [Finite X] {σ : X ≃+* X}

theorem eight_of_threeB (Ppar : D4Par 1 X σ) {t : C0 σ} (htB : t ∈ Bsub σ) (ht3 : orderOf t = 3)
    {Pg : Subgroup (C0 σ)} (hXg : Pg ≤ Subgroup.centralizer ({t} : Set (C0 σ)))
    (hperf : Group.IsPerfect ↥Pg)
    (hsubg : (Pg.subgroupOf (Subgroup.centralizer ({t} : Set (C0 σ)))).IsSubnormal)
    {p n : ℕ} [Fact p.Prime] (h4 : 4 ≤ p ^ n) (φ' : ↥Pg →* projSL 2 (GaloisField p n))
    (hφ's : Function.Surjective φ') : p ^ n = 8 := by
  haveI : Finite (C0 σ) := finite_C0 (σ := σ)
  haveI := Ppar.charP
  have hresB := d4_resCent_threeB' Ppar htB ht3
  have hX4 : 4 ≤ Nat.card X := by rw [Ppar.card]; norm_num
  have hPgA : Pg ≤ Asub σ := by
    rw [← hresB]
    exact le_inSubgroup_perfectResidual_of_isPerfect
      (X := (⊤ : Subgroup (C0 σ)) ⊓ Subgroup.centralizer ({t} : Set (C0 σ)))
      (le_inf le_top hXg) hperf
  have hAC : Asub σ ≤ Subgroup.centralizer ({t} : Set (C0 σ)) := by
    rw [← hresB]
    exact (resCent_le ⊤ t).trans inf_le_right
  have hsub : (Pg.subgroupOf (Asub σ)).IsSubnormal := by
    have heq : Pg.subgroupOf (Asub σ) = (Pg.subgroupOf (Subgroup.centralizer
        ({t} : Set (C0 σ)))).comap (Subgroup.inclusion hAC) := by
      ext u
      rfl
    rw [heq]
    exact hsubg.comap _
  have hQ : CFSG.IsQuasisimple ↥(Asub σ) :=
    Sec11.KS11Lie4Proof.isQuasisimple_d4ShortSL2 Ppar.sigma_pow_three hX4
  haveI hSs : Nontrivial (projSL 2 (GaloisField p n)) :=
    (isSimpleGroup_projSL_two h4).toNontrivial
  have hP' : Group.IsPerfect (Pg.subgroupOf (Asub σ)) := by
    haveI := hperf
    exact Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe hPgA).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hPgA).symm.surjective
  have hne : Pg.subgroupOf (Asub σ) ≠ ⊥ := by
    intro h0
    obtain ⟨s, s', hss⟩ := hSs.exists_pair_ne
    apply hss
    obtain ⟨x, rfl⟩ := hφ's s
    obtain ⟨x', rfl⟩ := hφ's s'
    have hx : x = 1 := by
      have : (⟨(x : C0 σ), hPgA x.2⟩ : ↥(Asub σ)) ∈ Pg.subgroupOf (Asub σ) := x.2
      rw [h0, Subgroup.mem_bot] at this
      exact Subtype.ext (by simpa using congrArg Subtype.val this)
    have hx' : x' = 1 := by
      have : (⟨(x' : C0 σ), hPgA x'.2⟩ : ↥(Asub σ)) ∈ Pg.subgroupOf (Asub σ) := x'.2
      rw [h0, Subgroup.mem_bot] at this
      exact Subtype.ext (by simpa using congrArg Subtype.val this)
    rw [hx, hx']
  have htop := Sec11.FieldCentRigid82.eq_top_of_isSubnormal_of_isQuasisimple hQ hsub hP' hne
  have hAP : Asub σ ≤ Pg := by
    intro d hd
    have : (⟨d, hd⟩ : ↥(Asub σ)) ∈ Pg.subgroupOf (Asub σ) := by rw [htop]; trivial
    exact this
  have hPeq : Pg = Asub σ := le_antisymm hPgA hAP
  obtain ⟨ψ, hψs⟩ : ∃ ψ : ↥(Asub σ) →* projSL 2 (GaloisField p n), Function.Surjective ψ :=
    ⟨φ'.comp (MulEquiv.subgroupCongr hPeq.symm).toMonoidHom,
      hφ's.comp (MulEquiv.subgroupCongr hPeq.symm).surjective⟩
  have hZ : Subgroup.center ↥(Asub σ) = ⊥ := by
    have h1 := Subgroup.map_center_eq (asubEquiv Ppar)
    rw [← h1, CFSG.Walter.sl2_center_eq_bot_of_charTwo, Subgroup.map_bot]
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases Sec6.subnormal_le_center_or_eq_top_of_isQuasisimple hQ
      (Subgroup.Normal.isSubnormal (MonoidHom.normal_ker ψ)) with hle | htop'
    · rw [hZ] at hle
      exact le_bot_iff.mp hle
    · exfalso
      obtain ⟨s, s', hss⟩ := hSs.exists_pair_ne
      apply hss
      obtain ⟨x, rfl⟩ := hψs s
      obtain ⟨x', rfl⟩ := hψs s'
      have hx : ψ x = 1 := MonoidHom.mem_ker.mp (htop' ▸ Subgroup.mem_top x)
      have hx' : ψ x' = 1 := MonoidHom.mem_ker.mp (htop' ▸ Subgroup.mem_top x')
      rw [hx, hx']
  have hcard : Nat.card (projSL 2 (GaloisField p n)) = Nat.card ↥(Asub σ) :=
    (Nat.card_congr (Equiv.ofBijective ψ ⟨hinj, hψs⟩)).symm
  have hA504 : Nat.card ↥(Asub σ) = 504 := by
    have h8 : Nat.card X = 8 := by rw [Ppar.card]; norm_num
    have := Sec11.KS11Lie4Proof.card_d4ShortSL2 (K := X) (σ := σ) Ppar.sigma_pow_three
    rw [h8] at this
    exact this
  have hn : n ≠ 0 := by
    rintro rfl
    norm_num at h4
  have hF : Nat.card (GaloisField p n) = p ^ n := GaloisField.card p n hn
  have hN := Sec11.KSListsProof.card_projSL_two_mul (GaloisField p n)
  rw [hF, hcard, hA504] at hN
  exact eq_eight_of_card_eq h4 hN

theorem eight_of_pair_model (Ppar : D4Par 1 X σ) {y : C0 σ} (hy3 : orderOf y = 3)
    {P : Subgroup (C0 σ)} (hPC : P ≤ Subgroup.centralizer ({y} : Set (C0 σ)))
    (hPp : Group.IsPerfect ↥P)
    (hPs : (P.subgroupOf (Subgroup.centralizer ({y} : Set (C0 σ)))).IsSubnormal)
    {p n : ℕ} [Fact p.Prime] (h4 : 4 ≤ p ^ n) (φ : ↥P →* projSL 2 (GaloisField p n))
    (hφ : Function.Surjective φ) : p ^ n = 8 := by
  haveI : Finite (C0 σ) := finite_C0 (σ := σ)
  haveI := Ppar.charP
  have hy31 : y ^ 3 = 1 := by rw [← hy3]; exact pow_orderOf_eq_one y
  have hy1 : y ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hy3
    omega
  have h3 : ¬ 3 ∣ 2 ^ 1 := by norm_num
  obtain ⟨g, hg⟩ := Sec11.KS11Lie6Proof.d4ThreeConj_holds X (2 ^ 1) σ Ppar.card Ppar.frob h3 y
    hy31 hy1
  let cg : C0 σ ≃* C0 σ := MulAut.conj g
  have hy1o : orderOf (g * y * g⁻¹) = 3 := by rw [orderOf_conj_eq]; exact hy3
  have hXg : P.map cg.toMonoidHom ≤ Subgroup.centralizer ({g * y * g⁻¹} : Set (C0 σ)) := by
    rw [centralizer_conj_eq_map]
    exact Subgroup.map_mono hPC
  have hperf : Group.IsPerfect (P.map cg.toMonoidHom) := by
    haveI := hPp
    exact Group.IsPerfect.ofSurjective
      (f := (P.equivMapOfInjective cg.toMonoidHom cg.injective).toMonoidHom)
      (P.equivMapOfInjective cg.toMonoidHom cg.injective).surjective
  have hsubg : ((P.map cg.toMonoidHom).subgroupOf
      (Subgroup.centralizer ({g * y * g⁻¹} : Set (C0 σ)))).IsSubnormal :=
    isSubnormal_map_centralizer cg hPs
  obtain ⟨φ', hφ's⟩ : ∃ φ' : ↥(P.map cg.toMonoidHom) →* projSL 2 (GaloisField p n),
      Function.Surjective φ' :=
    ⟨φ.comp (P.equivMapOfInjective cg.toMonoidHom cg.injective).symm.toMonoidHom,
      hφ.comp (P.equivMapOfInjective cg.toMonoidHom cg.injective).symm.surjective⟩
  rcases hg with hA | hB
  ·
    exfalso
    exact twoThreeAExcl_holds X σ Ppar (g * y * g⁻¹) hA hy1o (P.map cg.toMonoidHom) hXg hperf
      hsubg p n ‹_› h4 φ' hφ's
  ·
    exact eight_of_threeB Ppar hB hy1o hXg hperf hsubg h4 φ' hφ's

theorem kF3D42Inner_holds :
    ∀ (Q : Type) [Group Q] (r : TauCeti.PrimePower)
      (hr : (TauCeti.LieTypeIndex.trialityD4 r).Valid), r.card = 2 →
      Nonempty (Q ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 r, hr⟩).Group) →
      ∀ y : Q, orderOf y = 3 →
        ∀ P : Subgroup Q, P ≤ Subgroup.centralizer ({y} : Set Q) → Group.IsPerfect ↥P →
          (P.subgroupOf (Subgroup.centralizer ({y} : Set Q))).IsSubnormal →
          ∀ (p n : ℕ) [Fact p.Prime], 4 ≤ p ^ n →
            (∃ f : ↥P →* projSL 2 (GaloisField p n), Function.Surjective f) → p ^ n = 8 := by
  intro Q _ r hr hr2 ⟨eQ⟩ y hy3 P hPC hPp hPs p n _ h4 ⟨φ, hφ⟩
  obtain ⟨K, _, _, σ, hK, hσ, ⟨eK⟩⟩ := Hering129KModels.exists_d4_model eQ
  have Ppar : D4Par 1 K σ :=
    ⟨le_rfl, by rw [hK, hr2]; norm_num, fun c => by rw [hσ c, hr2]; norm_num⟩
  haveI : Finite (C0 σ) := finite_C0 (σ := σ)
  haveI : Finite Q := Finite.of_equiv _ eK.symm.toEquiv
  have hy3' : orderOf (eK y) = 3 := by rw [MulEquiv.orderOf_eq]; exact hy3
  have hPC' : P.map eK.toMonoidHom ≤ Subgroup.centralizer ({eK y} : Set (C0 σ)) := by
    rw [centralizer_map_equiv_eq eK y]
    exact Subgroup.map_mono hPC
  have hPp' : Group.IsPerfect (P.map eK.toMonoidHom) := by
    haveI := hPp
    exact Group.IsPerfect.ofSurjective
      (f := (P.equivMapOfInjective eK.toMonoidHom eK.injective).toMonoidHom)
      (P.equivMapOfInjective eK.toMonoidHom eK.injective).surjective
  exact eight_of_pair_model Ppar hy3' hPC' hPp' (isSubnormal_map_centralizer eK hPs) h4
    (φ.comp (P.equivMapOfInjective eK.toMonoidHom eK.injective).symm.toMonoidHom)
    (hφ.comp (P.equivMapOfInjective eK.toMonoidHom eK.injective).symm.surjective)

end Model

section EndE


variable {G : Type} [Group G] [Finite G]

theorem false_of_isoD42_inner (hN : Sec11.Item1134E27N) (hST : Sec21.Item1134E27ST)
    (hTL : KS129ThreeLocalFix) (hCen : Gap127TwoCfgPlus)
    {A : Subgroup G} {c : G} {L : Subgroup G} {b a : G} {K S : Subgroup G}
    (cfg : Cfg129 G A c L b a K S) {q : TauCeti.PrimePower} (hq : GTwoType129At L K q)
    {x : G} (hxD : x ∈ D129 a b) (hxb : x ∉ Subgroup.zpowers b)
    {Y : Subgroup G} (hY : Core129 A c x Y) (hXY : resCent K x ≤ Y) (h3 : Typ129IIIcType L Y)
    {r' : TauCeti.PrimePower} {hr' : (TauCeti.LieTypeIndex.trialityD4 r').Valid}
    (hr'2 : r'.card = 2)
    (eY : Nonempty (Y ⧸ CFSG.pCore 2 Y ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 r', hr'⟩).Group))
    (hqmod : ¬ PiModNine q.card) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hstd := cfg.std
  have hst : PartTwoStanding G := hstd.toPartTwoStanding
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hstd.isE27.1
  have hA27 : Nat.card A = 27 := hstd.isE27.2
  have hFE : partTwoF G = partTwoE G := hstd.partTwoF_eq
  have hAF : A ∈ partTwoF G := hFE ▸ cfg.mem_E
  obtain ⟨hbA, haA, haL, hb1, ha1, haB, hbL, hab, haD, -⟩ := cfg.point_facts
  have hDA : D129 a b ≤ A :=
    sup_le (Subgroup.zpowers_le.mpr haA) (Subgroup.zpowers_le.mpr hbA)
  have hxA : x ∈ A := hDA hxD
  have hx1 : x ≠ 1 := fun h => hxb (h ▸ Subgroup.one_mem _)
  have hx3 : x ^ 3 = 1 := hAe.2 x hxA
  have hb3 : b ^ 3 = 1 := hAe.2 b hbA
  obtain ⟨hYx, hAN, hAC, -⟩ := id hY
  have hbx : b ∉ Subgroup.zpowers x := fun h =>
    hxb (mem_of_mem_zpowers_of_ne_one (orderOf_eq_prime hx3 hx1) h hb1 (Subgroup.mem_zpowers b))
  have hYle : Y ≤ Subgroup.centralizer ({x} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hYx
  have hbN : b ∈ Subgroup.normalizer (Y : Set G) := hAN hbA
  have hKb : K ≤ Subgroup.centralizer ({b} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt cfg.hK
  have hXb : resCent K x ≤ Subgroup.centralizer ({b} : Set G) :=
    ((resCent_le K x).trans inf_le_left).trans hKb
  have hKK := gap129KFKStrong_of_fix hTL hCen
  obtain ⟨-, -, hXq, -⟩ := hKK G A c L b a K S cfg ⟨q, hq⟩ x hxD hxb
  obtain ⟨-, -, δ, -, hδ13, F, hFf, hFfin, hFcard, φK, hφK, hkerK⟩ :=
    exists_sl2_quotient_of_fix hTL hCen G A c L b a K S cfg q hq x hxD hxb
  obtain ⟨hq4, -, -⟩ := hCen.2 G A c L b a K S cfg q hq
  haveI : Finite F := Finite.of_fintype F
  haveI hqp : Fact q.p.Prime := ⟨q.prime_p⟩
  have hF4 : 4 ≤ Nat.card F := by
    rw [Nat.card_eq_fintype_card, hFcard]
    refine hq4.trans (Nat.le_self_pow ?_ _)
    rcases hδ13 with rfl | rfl <;> norm_num
  have hFpow : Nat.card F = q.p ^ (q.exponent * δ) := by
    rw [Nat.card_eq_fintype_card, hFcard, TauCeti.PrimePower.card_def, ← pow_mul]
  obtain ⟨eX⟩ := Hering129KYa.nonempty_quotTheta_equiv_projSL (p := q.p) (n := q.exponent * δ)
    hFpow hF4 φK hφK hkerK
  have hX4 : 4 ≤ q.p ^ (q.exponent * δ) := hFpow ▸ hF4
  have hXM : resCent K x ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({b} : Set G)) :=
    Sec6.mem_thetaComponentsIn_of (le_inf hXY hXb) (isPerfect_resCent K x)
      (resCent_isSubnormal cfg.hK (M := Y ⊓ Subgroup.centralizer ({b} : Set G)) inf_le_right
        (inf_le_left.trans hYle) (le_inf hXY hXb)) hXq
  have hYq := Sec6.isQuasisimple_of_mem_thetaComponentsAt hYx
  have hθ := theta_eq_pCore_of_typ129IIIcType hYq h3
  obtain ⟨eY'⟩ := eY
  have fQ : Y ⧸ aschbacherSolvableCore 3 Y ≃*
      (TauCeti.CFSGIndex.lie ⟨.trialityD4 r', hr'⟩).Group :=
    (QuotientGroup.quotientMulEquivOfEq hθ).trans eY'
  have hGD : IsG2D4 (Y ⧸ aschbacherSolvableCore 3 Y) r' 3 := Or.inr ⟨rfl, hr', ⟨fQ⟩⟩
  have hZ : Subgroup.center (Y ⧸ aschbacherSolvableCore 3 Y) = ⊥ :=
    Hering129KModels.center_eq_bot_of_isG2D4 hGD
  have hkind : ¬ KFacts.InducesStdKind Y b .field ∧ ¬ KFacts.InducesStdKind Y b .graphField := by
    obtain ⟨h8a, h8b⟩ := notEight_of_typ129IIIcType hθ h3
    exact not_stdKind_of_notEight hN hST hst hAF cfg.mem_S hFE hA27 hxA hx1 hYx hAN hAC
      h8a h8b hbA
  have hnoOuter : ¬ Sec4.InducesOuterTheta b Y := by
    intro hout
    obtain ⟨K', hK1, hK2, σ, hK, hσ, ⟨eK⟩⟩ := Hering129KModels.exists_d4_model fQ
    have hp2 : r'.p = 2 := by
      have hdvd : r'.p ∣ 2 := by
        have h := TauCeti.PrimePower.card_def r'
        rw [hr'2] at h
        rw [h]
        exact dvd_pow_self r'.p r'.exponent_pos.ne'
      exact (Nat.prime_dvd_prime_iff_eq r'.prime_p Nat.prime_two).mp hdvd
    have hrc : r'.card = 2 ^ r'.exponent := by rw [TauCeti.PrimePower.card_def, hp2]
    have hK' : Nat.card K' = (2 ^ r'.exponent) ^ 3 := by rw [hK, hrc]
    have hσ' : ∀ z, σ z = z ^ 2 ^ r'.exponent := fun z => by rw [hσ z, hrc]
    have hf1 : 1 ≤ r'.exponent := r'.exponent_pos
    exact hkind.2 (KFacts.InducesStdKind.triality r'.exponent hf1 K' hK' σ hσ'
      (KFacts.inducesKindTriality_graphField hf1 hK' hσ' Y hb3 hout eK))
  set β : MulAut (Y ⧸ aschbacherSolvableCore 3 Y) :=
    Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨b, hbN⟩) with hβdef
  have hβ3 : β ^ 3 = 1 := by
    have h1 : (⟨b, hbN⟩ : Subgroup.normalizer (Y : Set G)) ^ 3 = 1 := Subtype.ext hb3
    rw [hβdef, ← map_pow, ← map_pow, h1, map_one, map_one]
  have hβ1 : β ≠ 1 := by
    intro h1
    have hbθ : b ∈ Sec4.thetaQuotCentralizer Y := ⟨⟨b, hbN⟩, MonoidHom.mem_ker.mpr h1, rfl⟩
    have : b ∈ A ⊓ Sec4.thetaQuotCentralizer Y := ⟨hbA, hbθ⟩
    rw [hAC] at this
    exact hbx this
  have hrange : β ∈ (MulAut.conj : (Y ⧸ aschbacherSolvableCore 3 Y) →*
      MulAut (Y ⧸ aschbacherSolvableCore 3 Y)).range := by
    by_contra hnot
    exact hnoOuter ⟨hbN, hnot⟩
  obtain ⟨y, hy⟩ := hrange
  have hy3 : y ^ 3 = 1 := by
    apply Hering129KInner.eq_of_conj_eq_conj hZ
    rw [map_pow, map_one, hy]
    exact hβ3
  have hy1 : y ≠ 1 := by
    intro h1
    apply hβ1
    rw [← hy, h1, map_one]
  have hyo : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hfix : Sec8.barCentralizer (Subgroup.zpowers b) Y =
      Subgroup.centralizer ({y} : Set (Y ⧸ aschbacherSolvableCore 3 Y)) := by
    ext u
    rw [KFacts.mem_barCentralizer_zpowers_iff hbN u, Subgroup.mem_centralizer_singleton_iff]
    have hu : β u = y * u * y⁻¹ := by rw [← hy, MulAut.conj_apply]
    rw [hu]
    constructor
    · intro h
      calc u * y = (y * u * y⁻¹) * y := by rw [h]
        _ = y * u := by group
    · intro h
      calc y * u * y⁻¹ = (u * y) * y⁻¹ := by rw [h]
        _ = u := by group
  have hPle : Sec8.imageModTheta Y (resCent K x) ≤
      Subgroup.centralizer ({y} : Set (Y ⧸ aschbacherSolvableCore 3 Y)) := by
    rw [← hfix]
    exact Sec8.Hering418.imageModTheta_le_barCentralizer_of_le hbN hb3 hXY hXb
  have hPperf : Group.IsPerfect ↥(Sec8.imageModTheta Y (resCent K x)) :=
    Sec8.Hering418.isPerfect_imageModTheta hXM
  have hPsub : ((Sec8.imageModTheta Y (resCent K x)).subgroupOf
      (Subgroup.centralizer ({y} : Set (Y ⧸ aschbacherSolvableCore 3 Y)))).IsSubnormal := by
    rw [← hfix]
    exact Sec8.Hering418.imageModTheta_isSubnormal_barCentralizer hbN hb3 hXM
  obtain ⟨g, hg⟩ := exists_surjective_imageModTheta hXY
  have hp8 := kF3D42Inner_holds (Y ⧸ aschbacherSolvableCore 3 Y) r' hr' hr'2 ⟨fQ⟩ y hyo _ hPle
    hPperf hPsub q.p (q.exponent * δ) hX4 ⟨eX.toMonoidHom.comp g, eX.surjective.comp hg⟩
  have hqδ : q.card ^ δ = 8 := by
    rw [← hFcard, ← Nat.card_eq_fintype_card, hFpow, hp8]
  rcases hδ13 with rfl | rfl
  · have h8 : q.card = 8 := by simpa using hqδ
    apply hqmod
    unfold PiModNine
    omega
  · have h64 : 4 ^ 3 ≤ q.card ^ 3 := Nat.pow_le_pow_left hq4 3
    omega

theorem gap129EndE_of_notD42_inner (hN : Sec11.Item1134E27N) (hST : Sec21.Item1134E27ST)
    (hTL : KS129ThreeLocalFix) (hCen : Gap127TwoCfgPlus) (h : Gap129EndENotD42) :
    Gap129EndE := by
  intro G _ _ A c L b a K S cfg q hq x hxD hxb hxL Y hY hXY hNo h3 E hE d hdD hdb hdL Y' J hY'
    hXY' hJ hbJ r hr hrmod hqmod
  by_cases hD : ∀ (r' : TauCeti.PrimePower) (hr' : (TauCeti.LieTypeIndex.trialityD4 r').Valid),
      r'.card = 2 → ¬ Nonempty (Y ⧸ CFSG.pCore 2 Y ≃*
        (TauCeti.CFSGIndex.lie ⟨.trialityD4 r', hr'⟩).Group)
  · exact h G A c L b a K S cfg q hq x hxD hxb hxL Y hY hXY hNo h3 hD E hE d hdD hdb hdL Y' J hY'
      hXY' hJ hbJ r hr hrmod hqmod
  · exfalso
    push_neg at hD
    obtain ⟨r', hr', hr'2, eY⟩ := hD
    exact false_of_isoD42_inner hN hST hTL hCen cfg hq hxD hxb hY hXY h3 hr'2 eY hqmod

end EndE

end Hering129L

end CFSG.RankThree.PartTwo.Sec12
