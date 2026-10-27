module

public import CFSG.LocalAnalysis.StandardType.GGK1DDefs
public import CFSG.LocalAnalysis.StandardType.GGK1DMult
public import CFSG.LocalAnalysis.StandardType.GGK1DWitt
public import CFSG.LocalAnalysis.StandardType.GGK1DBlocks
public import CFSG.LocalAnalysis.StandardType.GGK1DFamily
public import CFSG.LocalAnalysis.StandardType.GGK1DKind
public import CFSG.LocalAnalysis.StandardType.GGK1DComp
public import CFSG.LocalAnalysis.StandardType.GGK1DCentreless
public import CFSG.LocalAnalysis.StandardType.GGK1DDvd
public import CFSG.LocalAnalysis.StandardType.GGK1DCenter
public import CFSG.LocalAnalysis.StandardType.GGK1DValid
public import CFSG.LocalAnalysis.StandardType.GGK1DLift

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Polynomial
open CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.PartOne.KCOrthogonal (OddOrderIsometry reciprocalPolynomial)
open CFSG.RankThree.Classical (IsReciprocalTransversal)

theorem ggK1D_orthBlocks_plus {p nf r : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1) (h4 : 4 ≤ r)
    (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf)
    {x : ↥(LargeEvenOmega (LargeEvenQPlus K r))} (hx : x ^ p = 1) :
    Nonempty (OrthPrimaryBlocks K (CFSG.StandardType.TableBOrth.qPlusForm K r) nf p
      (ggK1DLin (x : GL (Fin r ⊕ Fin r) K))) := by
  refine ggK1D_orthBlocks_abstract (nf := nf) hp hp2 hdvd hnf hK ?_
    (ggK1D_omegaLift_plus hp hp2 hnf hK hx)
  rw [Module.finrank_fintype_fun_eq_card]
  simp
  omega

theorem ggK1D_orthBlocks_minus {p nf r : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1) (h4 : 4 ≤ r)
    (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {x : ↥(LargeEvenOmega (LargeEvenQMinus (r - 1) b c))} (hx : x ^ p = 1) :
    Nonempty (OrthPrimaryBlocks K (CFSG.StandardType.TableBOrth.qMinusForm K (r - 1) b c) nf p
      (ggK1DLin (x : GL (LargeEvenMinusIdx (r - 1)) K))) := by
  refine ggK1D_orthBlocks_abstract (nf := nf) hp hp2 hdvd hnf hK ?_
    (ggK1D_omegaLift_minus hp hp2 hnf hK hirr hx)
  rw [Module.finrank_fintype_fun_eq_card]
  simp [LargeEvenMinusIdx]
  omega

theorem ggK1D_core_comp_plus {p nf d r : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1)
    (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf) (hd : d = ggMultOrd p nf)
    {x : ↥(LargeEvenOmega (LargeEvenQPlus K r))} {m : List ℕ}
    (hm : GGK1DMultOf p nf d r K (x : GL (Fin r ⊕ Fin r) K) m) (hx : x ^ p = 1)
    (hob : Nonempty (OrthPrimaryBlocks K (CFSG.StandardType.TableBOrth.qPlusForm K r) nf p
      (ggK1DLin (x : GL (Fin r ⊕ Fin r) K)))) :
    GGK1Comps nf (ggMultDatumD p nf d false m)
      (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K r)))
      (MulAut.conj (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K r)) x)) := by
  obtain ⟨F⟩ := ggK1DCo_family_of_orthBlocks_plus hp hp2 hdvd hnf hK hd hm hx hob
  refine ⟨?_, ?_⟩
  · intro J hJ
    obtain ⟨q, hq, hJeq⟩ := ggK1DCo_component_eq F hJ
    rw [hJeq]
    have hqs : ((F.blk q.1).get q.2).qs = true := F.hqs q hq
    obtain ⟨hdvdn, hlam⟩ := ggK1DCo_orbit_arith hnf (F.hmem q hq) hqs
    exact ⟨(F.blk q.1).get q.2, F.hmem q hq, hqs, hdvdn, hlam, F.hlab q hq⟩
  · intro o ho hqs
    obtain ⟨q, hq, hqo⟩ := F.hreal o ho hqs
    refine ⟨⁅F.A q.1 q.2, F.A q.1 q.2⁆, ggK1DCo_factor_component F q hq, ?_⟩
    rw [← hqo]
    exact F.hlab q hq

theorem ggK1D_core_comp_minus {p nf d r : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1)
    (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf) (hd : d = ggMultOrd p nf) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {x : ↥(LargeEvenOmega (LargeEvenQMinus (r - 1) b c))} {m : List ℕ}
    (hm : GGK1DMultOf p nf d r K (x : GL (LargeEvenMinusIdx (r - 1)) K) m) (hx : x ^ p = 1)
    (hob : Nonempty (OrthPrimaryBlocks K
      (CFSG.StandardType.TableBOrth.qMinusForm K (r - 1) b c) nf p
      (ggK1DLin (x : GL (LargeEvenMinusIdx (r - 1)) K)))) :
    GGK1Comps nf (ggMultDatumD p nf d true m)
      (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (r - 1) b c)))
      (MulAut.conj (LargeEvenProjMk
        (LargeEvenOmega (LargeEvenQMinus (r - 1) b c)) x)) := by
  obtain ⟨F⟩ := ggK1DCo_family_of_orthBlocks_minus hp hp2 hdvd hnf hK hd hirr hm hx hob
  refine ⟨?_, ?_⟩
  · intro J hJ
    obtain ⟨q, hq, hJeq⟩ := ggK1DCo_component_eq F hJ
    rw [hJeq]
    have hqs : ((F.blk q.1).get q.2).qs = true := F.hqs q hq
    obtain ⟨hdvdn, hlam⟩ := ggK1DCo_orbit_arith hnf (F.hmem q hq) hqs
    exact ⟨(F.blk q.1).get q.2, F.hmem q hq, hqs, hdvdn, hlam, F.hlab q hq⟩
  · intro o ho hqs
    obtain ⟨q, hq, hqo⟩ := F.hreal o ho hqs
    refine ⟨⁅F.A q.1 q.2, F.A q.1 q.2⁆, ggK1DCo_factor_component F q hq, ?_⟩
    rw [← hqo]
    exact F.hlab q hq

private theorem ggK1D_bij_aux {D : GGKacDatum} {R : Type} [Group R] {e : MulAut R} {Q : Type}
    (compSub : Q → Subgroup R)
    (hcomp : ∀ i, CFSG.Assembly.IsComponentOf (compSub i) (ggFixSub e))
    (hinj : Function.Injective compSub)
    (hsurj : ∀ J, CFSG.Assembly.IsComponentOf J (ggFixSub e) → ∃ i, compSub i = J)
    (g : Q ≃ {k : Fin D.orbits.length // D.orbits[k].qs = true}) (blk : Q → GGKacOrbit)
    (hg : ∀ i, D.orbits[(g i).1] = blk i)
    (hlab : ∀ i, GGHasLabel (blk i).lab (↥(compSub i) ⧸ Subgroup.center ↥(compSub i))) :
    GGKacCompBij D R e := by
  let c : Q → {J : Subgroup R // CFSG.Assembly.IsComponentOf J (ggFixSub e)} :=
    fun i => ⟨compSub i, hcomp i⟩
  have hc : Function.Bijective c := by
    refine ⟨fun i j hij => hinj (congrArg Subtype.val hij), ?_⟩
    rintro ⟨J, hJ⟩
    obtain ⟨i, hi⟩ := hsurj J hJ
    exact ⟨i, Subtype.ext hi⟩
  let e' := Equiv.ofBijective c hc
  refine ⟨e'.symm.trans g, fun J => ?_⟩
  have hJ : J.1 = compSub (e'.symm J) := (congrArg Subtype.val (e'.apply_symm_apply J)).symm
  have hpos : D.orbits[((e'.symm.trans g) J).1] = blk (e'.symm J) := hg (e'.symm J)
  have transport : ∀ (lab : LargeEvenLabel) (X Y : Subgroup R), X = Y →
      GGHasLabel lab (↥X ⧸ Subgroup.center ↥X) → GGHasLabel lab (↥Y ⧸ Subgroup.center ↥Y) := by
    intro lab X Y h
    subst h
    exact id
  rw [hpos]
  exact transport _ _ _ hJ.symm (hlab (e'.symm J))

theorem ggK1D_core_bij_plus {p nf d r : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1)
    (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf) (hd : d = ggMultOrd p nf)
    {x : ↥(LargeEvenOmega (LargeEvenQPlus K r))} {m : List ℕ}
    (hm : GGK1DMultOf p nf d r K (x : GL (Fin r ⊕ Fin r) K) m) (hx : x ^ p = 1)
    (hob : Nonempty (OrthPrimaryBlocks K (CFSG.StandardType.TableBOrth.qPlusForm K r) nf p
      (ggK1DLin (x : GL (Fin r ⊕ Fin r) K)))) :
    GGKacCompBij (ggMultDatumD p nf d false m)
      (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K r)))
      (MulAut.conj (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K r)) x)) := by
  obtain ⟨F⟩ := ggK1DCo_family_of_orthBlocks_plus hp hp2 hdvd hnf hK hd hm hx hob
  obtain ⟨g, hg⟩ := F.hbij
  refine ggK1D_bij_aux (fun q : {q : Σ i, Fin (F.blk i).length //
      CFSG.IsQuasisimple ↥⁅F.A q.1 q.2, F.A q.1 q.2⁆} =>
      ⁅F.A q.1.1 q.1.2, F.A q.1.1 q.1.2⁆)
    (fun q => ggK1DCo_factor_component F q.1 q.2) ?_ ?_ g
    (fun q => (F.blk q.1.1).get q.1.2) (fun q => hg q) (fun q => F.hlab q.1 q.2)
  · intro q q' h
    exact Subtype.ext (ggK1DCo_component_inj F q.2 q'.2 h)
  · intro J hJ
    obtain ⟨q, hq, hJeq⟩ := ggK1DCo_component_eq F hJ
    exact ⟨⟨q, hq⟩, hJeq.symm⟩

theorem ggK1D_core_bij_minus {p nf d r : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1)
    (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf) (hd : d = ggMultOrd p nf) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {x : ↥(LargeEvenOmega (LargeEvenQMinus (r - 1) b c))} {m : List ℕ}
    (hm : GGK1DMultOf p nf d r K (x : GL (LargeEvenMinusIdx (r - 1)) K) m) (hx : x ^ p = 1)
    (hob : Nonempty (OrthPrimaryBlocks K
      (CFSG.StandardType.TableBOrth.qMinusForm K (r - 1) b c) nf p
      (ggK1DLin (x : GL (LargeEvenMinusIdx (r - 1)) K)))) :
    GGKacCompBij (ggMultDatumD p nf d true m)
      (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (r - 1) b c)))
      (MulAut.conj (LargeEvenProjMk
        (LargeEvenOmega (LargeEvenQMinus (r - 1) b c)) x)) := by
  obtain ⟨F⟩ := ggK1DCo_family_of_orthBlocks_minus hp hp2 hdvd hnf hK hd hirr hm hx hob
  obtain ⟨g, hg⟩ := F.hbij
  refine ggK1D_bij_aux (fun q : {q : Σ i, Fin (F.blk i).length //
      CFSG.IsQuasisimple ↥⁅F.A q.1 q.2, F.A q.1 q.2⁆} =>
      ⁅F.A q.1.1 q.1.2, F.A q.1.1 q.1.2⁆)
    (fun q => ggK1DCo_factor_component F q.1 q.2) ?_ ?_ g
    (fun q => (F.blk q.1.1).get q.1.2) (fun q => hg q) (fun q => F.hlab q.1 q.2)
  · intro q q' h
    exact Subtype.ext (ggK1DCo_component_inj F q.2 q'.2 h)
  · intro J hJ
    obtain ⟨q, hq, hJeq⟩ := ggK1DCo_component_eq F hJ
    exact ⟨⟨q, hq⟩, hJeq.symm⟩

theorem ggK1D_core_sigma_plus {p nf d r : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1)
    (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf) (h2 : 2 ≤ r) (hd : d = ggMultOrd p nf)
    {x : ↥(LargeEvenOmega (LargeEvenQPlus K r))} {m : List ℕ}
    (hm : GGK1DMultOf p nf d r K (x : GL (Fin r ⊕ Fin r) K) m) (hx : x ^ p = 1)
    (hob : Nonempty (OrthPrimaryBlocks K (CFSG.StandardType.TableBOrth.qPlusForm K r) nf p
      (ggK1DLin (x : GL (Fin r ⊕ Fin r) K)))) :
    GGKacSigmaClause p
      (LargeEvenInnSet (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K r))))
      (ggMultDatumD p nf d false m)
      (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K r)))
      (MonoidHom.id (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K r))))
      (MulAut.conj (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K r)) x)) := by
  obtain ⟨F⟩ := ggK1DCo_family_of_orthBlocks_plus hp hp2 hdvd hnf hK hd hm hx hob
  intro o ho hqs A hxA hA hAI
  obtain ⟨q, hqo, t₀, ht₀, ht₀p, a₀, ha₀, hnc⟩ := F.hsolv o ho hqs
  have hZ : ∀ z : LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K r)),
      (∀ g : LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K r)), g * z = z * g) → z = 1 := by
    intro z hz
    have hmem : z ∈ Subgroup.center (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K r))) :=
      Subgroup.mem_center_iff.mpr fun g => hz g
    rw [ggK1D_centreless_plus hp hp2 hdvd hnf hK h2] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hI : ∀ φ ∈ LargeEvenInnSet (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K r))),
      ∃ s, φ = MulAut.conj s := by
    rintro φ ⟨s, rfl⟩
    exact ⟨s, rfl⟩
  have hle : ∀ q' (_ : q' ≠ q), F.A q'.1 q'.2 ≤
      Subgroup.centralizer (F.A q.1 q.2 : Set (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K
          r)))) := by
    intro q' hq' b hb
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact F.hcomm q q' (fun h => hq' h.symm) a ha b hb
  have hC : (⨆ (q' : Σ i, Fin (F.blk i).length) (_ : q' ≠ q), F.A q'.1 q'.2) ≤
      Subgroup.centralizer (F.A q.1 q.2 : Set (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K
          r)))) := by
    refine iSup_le fun q' => iSup_le fun hq' => ?_
    exact hle q' hq'
  have hSC : ∀ a ∈ F.A q.1 q.2,
      ∀ b ∈ (⨆ (q' : Σ i, Fin (F.blk i).length) (_ : q' ≠ q), F.A q'.1 q'.2),
        a * b = b * a := by
    intro a ha b hb
    exact (Subgroup.mem_centralizer_iff.mp (hC hb)) a ha
  have hdisj : Disjoint (F.A q.1 q.2)
      (⨆ (q' : Σ i, Fin (F.blk i).length) (_ : q' ≠ q), F.A q'.1 q'.2) := F.hindep q
  have hsup : F.A q.1 q.2 ⊔
      (⨆ (q' : Σ i, Fin (F.blk i).length) (_ : q' ≠ q), F.A q'.1 q'.2) =
      Subgroup.centralizer ({LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K r)) x} : Set
          (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K r)))) := by
    rw [← F.hjoin]
    exact (iSup_split_single (fun p : Σ i, Fin (F.blk i).length => F.A p.1 p.2) q).symm
  have hcomp : ∀ J : Subgroup (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K r))),
      CFSG.Assembly.IsComponentOf J
        (ggFixSub (MulAut.conj (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K r)) x))) →
        ∀ j ∈ J, ∀ a ∈ F.A q.1 q.2, a * j = j * a := by
    intro J hJ j hj a ha
    obtain ⟨q', hq', hJeq⟩ := ggK1DCo_component_eq F hJ
    rw [hJeq] at hj
    have hne : q' ≠ q := by
      intro h
      have h1 := F.hqs q' hq'
      rw [h] at h1
      rw [hqo] at h1
      rw [hqs] at h1
      exact absurd h1 (by decide)
    exact F.hcomm q q' (fun h => hne h.symm) a ha j (Subgroup.commutator_le_self _ hj)
  refine ggK1_sigma_abstract hZ _ hI (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K r)) x)
    (F.A q.1 q.2)
    (⨆ (q' : Σ i, Fin (F.blk i).length) (_ : q' ≠ q), F.A q'.1 q'.2)
    hSC hdisj hsup hcomp (t₀ := t₀) (a₀ := a₀) ht₀ ha₀ ht₀p hnc A hxA hA ?_
  intro a ha
  exact hAI a ha

theorem ggK1D_core_sigma_minus {p nf d r : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1)
    (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf) (h2 : 2 ≤ r) (hd : d = ggMultOrd p nf) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {x : ↥(LargeEvenOmega (LargeEvenQMinus (r - 1) b c))} {m : List ℕ}
    (hm : GGK1DMultOf p nf d r K (x : GL (LargeEvenMinusIdx (r - 1)) K) m) (hx : x ^ p = 1)
    (hob : Nonempty (OrthPrimaryBlocks K
      (CFSG.StandardType.TableBOrth.qMinusForm K (r - 1) b c) nf p
      (ggK1DLin (x : GL (LargeEvenMinusIdx (r - 1)) K)))) :
    GGKacSigmaClause p
      (LargeEvenInnSet (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (r - 1) b c))))
      (ggMultDatumD p nf d true m)
      (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (r - 1) b c)))
      (MonoidHom.id (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (r - 1) b c))))
      (MulAut.conj (LargeEvenProjMk
        (LargeEvenOmega (LargeEvenQMinus (r - 1) b c)) x)) := by
  obtain ⟨F⟩ := ggK1DCo_family_of_orthBlocks_minus hp hp2 hdvd hnf hK hd hirr hm hx hob
  intro o ho hqs A hxA hA hAI
  obtain ⟨q, hqo, t₀, ht₀, ht₀p, a₀, ha₀, hnc⟩ := F.hsolv o ho hqs
  have hZ : ∀ z : LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (r - 1) b c)),
      (∀ g : LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (r - 1) b c)), g * z = z * g) →
      z = 1 := by
    intro z hz
    have hmem : z ∈ Subgroup.center
        (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (r - 1) b c))) :=
      Subgroup.mem_center_iff.mpr fun g => hz g
    rw [ggK1D_centreless_minus hp hp2 hdvd hnf hK h2 hirr] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hI : ∀ φ ∈ LargeEvenInnSet
      (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (r - 1) b c))),
      ∃ s, φ = MulAut.conj s := by
    rintro φ ⟨s, rfl⟩
    exact ⟨s, rfl⟩
  have hle : ∀ q' (_ : q' ≠ q), F.A q'.1 q'.2 ≤
      Subgroup.centralizer (F.A q.1 q.2 : Set (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (r -
          1) b c)))) := by
    intro q' hq' b hb
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact F.hcomm q q' (fun h => hq' h.symm) a ha b hb
  have hC : (⨆ (q' : Σ i, Fin (F.blk i).length) (_ : q' ≠ q), F.A q'.1 q'.2) ≤
      Subgroup.centralizer (F.A q.1 q.2 : Set (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (r -
          1) b c)))) := by
    refine iSup_le fun q' => iSup_le fun hq' => ?_
    exact hle q' hq'
  have hSC : ∀ a ∈ F.A q.1 q.2,
      ∀ b ∈ (⨆ (q' : Σ i, Fin (F.blk i).length) (_ : q' ≠ q), F.A q'.1 q'.2),
        a * b = b * a := by
    intro a ha b hb
    exact (Subgroup.mem_centralizer_iff.mp (hC hb)) a ha
  have hdisj : Disjoint (F.A q.1 q.2)
      (⨆ (q' : Σ i, Fin (F.blk i).length) (_ : q' ≠ q), F.A q'.1 q'.2) := F.hindep q
  have hsup : F.A q.1 q.2 ⊔
      (⨆ (q' : Σ i, Fin (F.blk i).length) (_ : q' ≠ q), F.A q'.1 q'.2) =
      Subgroup.centralizer ({LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus (r - 1) b c)) x} :
          Set (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (r - 1) b c)))) := by
    rw [← F.hjoin]
    exact (iSup_split_single (fun p : Σ i, Fin (F.blk i).length => F.A p.1 p.2) q).symm
  have hcomp : ∀ J : Subgroup (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (r - 1) b c))),
      CFSG.Assembly.IsComponentOf J
        (ggFixSub (MulAut.conj (LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus (r - 1) b c)) x)))
            →
        ∀ j ∈ J, ∀ a ∈ F.A q.1 q.2, a * j = j * a := by
    intro J hJ j hj a ha
    obtain ⟨q', hq', hJeq⟩ := ggK1DCo_component_eq F hJ
    rw [hJeq] at hj
    have hne : q' ≠ q := by
      intro h
      have h1 := F.hqs q' hq'
      rw [h] at h1
      rw [hqo] at h1
      rw [hqs] at h1
      exact absurd h1 (by decide)
    exact F.hcomm q q' (fun h => hne h.symm) a ha j (Subgroup.commutator_le_self _ hj)
  refine ggK1_sigma_abstract hZ _ hI (LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus (r - 1) b
      c)) x)
    (F.A q.1 q.2)
    (⨆ (q' : Σ i, Fin (F.blk i).length) (_ : q' ≠ q), F.A q'.1 q'.2)
    hSC hdisj hsup hcomp (t₀ := t₀) (a₀ := a₀) ht₀ ha₀ ht₀p hnc A hxA hA ?_
  intro a ha
  exact hAI a ha

theorem ggK1D_core_plus {p nf r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1)
    (hlab : LargeEvenInLambda2 ⟨.D, r, nf⟩) (h4 : 4 ≤ r)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ nf) :
    GGK1Core GGMultValidCl p ⟨.D, r, nf⟩
      (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K r)))
      (LargeEvenInnSet (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K r)))) := by
  intro φ hφ hφp
  obtain ⟨x, hxp, rfl⟩ := ggK1D_exists_lift_plus hlab.1 hK (by omega) φ hφ hφp
  obtain ⟨m, hm⟩ := ggK1D_mult_exists_plus hp hp2 hdvd hlab.1 hK hxp
  have hob := ggK1D_orthBlocks_plus hp hp2 hdvd h4 hlab.1 hK hxp
  exact ⟨ggMultDatumD p nf (ggMultOrd p nf) false m,
    ggK1D_core_valid_plus hp hp2 hdvd h4 hlab.1 hK hm hxp,
    ggK1D_core_comp_plus hp hp2 hdvd hlab.1 hK rfl hm hxp hob,
    ggK1D_core_dvd_plus hp hp2 hdvd hlab.1 hK rfl hm hxp,
    ggK1D_core_center_plus hp hp2 hdvd h4 hlab.1 hK rfl hm hxp,
    ggK1D_core_bij_plus hp hp2 hdvd hlab.1 hK rfl hm hxp hob,
    ggK1D_core_sigma_plus hp hp2 hdvd hlab.1 hK (by omega) rfl hm hxp hob⟩

theorem ggK1D_core_minus {p nf r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1)
    (hlab : LargeEvenInLambda2 ⟨.twD, r, nf⟩) (h4 : 4 ≤ r)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ nf) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    GGK1Core GGMultValidCl p ⟨.twD, r, nf⟩
      (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (r - 1) b c)))
      (LargeEvenInnSet (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (r - 1) b c)))) := by
  intro φ hφ hφp
  obtain ⟨x, hxp, rfl⟩ := ggK1D_exists_lift_minus hlab.1 hK (by omega) hirr φ hφ hφp
  obtain ⟨m, hm⟩ := ggK1D_mult_exists_minus hp hp2 hdvd hlab.1 hK (by omega) hirr hxp
  have hob := ggK1D_orthBlocks_minus hp hp2 hdvd h4 hlab.1 hK hirr hxp
  exact ⟨ggMultDatumD p nf (ggMultOrd p nf) true m,
    ggK1D_core_valid_minus hp hp2 hdvd h4 hlab.1 hK hirr hm hxp,
    ggK1D_core_comp_minus hp hp2 hdvd hlab.1 hK rfl hirr hm hxp hob,
    ggK1D_core_dvd_minus hp hp2 hdvd hlab.1 hK rfl hirr hm hxp,
    ggK1D_core_center_minus hp hp2 hdvd h4 hlab.1 hK rfl hirr hm hxp,
    ggK1D_core_bij_minus hp hp2 hdvd hlab.1 hK rfl hirr hm hxp hob,
    ggK1D_core_sigma_minus hp hp2 hdvd hlab.1 hK (by omega) rfl hirr hm hxp hob⟩

end CFSG.StandardType

end
