module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeCompanion1632Frob
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeCompanion1632FrobTw
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeCompanion1625B1a
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeCompanion1625B1b
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwConj

public section

namespace CFSG.StandardType.S2MathAs1E6Companion1625

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.StandardType.E6Centralizer1585
open CFSG.StandardType.GGK0MarkedKacIface1587
open CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private lemma ltrb1f1_closure_rootDiagUnit_eq_torusGroup {Omega : Type} [Field Omega]
    [IsAlgClosed Omega] [CharP Omega 2]
    (τ : Tag) :
    Subgroup.closure (Set.range (fun b : Fin τ.rank → Omegaˣ => rootDiagUnit τ b)) =
      torusGroup τ Omega := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.closure_le]
    rintro _ ⟨b, rfl⟩
    exact rootDiagUnit_mem_torusGroup (τ := τ) b
  · intro g hg
    obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (τ := τ) hg
    exact Subgroup.subset_closure ⟨l, rfl⟩

private lemma ltrb1f1_map_step_torusGroup_le {Omega : Type} [Field Omega] [IsAlgClosed Omega]
    [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab p R I phi) :
    (torusGroup ρ.tau Omega).map ρ.setup.D.step ≤ torusGroup ρ.tau Omega := by
  rw [Subgroup.map_le_iff_le_comap]
  intro g hg
  obtain ⟨Q, _hQfix, hQnorm, hstep⟩ :=
    exists_step_frobTwist (S := ρ.setup) (r := 2) (e := lab.n) ρ.q_eq
  obtain ⟨σ, hσ⟩ := exists_ringEquiv_frob (L := Omega) 2 lab.n
  have hfrobσ : ∀ g : ModGL ρ.tau Omega,
      entrywiseFrobGL ρ.tau Omega 2 lab.n g = frobGL σ g := by
    intro g
    change Units.map (entrywiseHom (iterateFrobenius Omega 2 lab.n)) g =
      Units.map (entrywiseHom σ.toRingHom) g
    rw [hσ]
  change ρ.setup.D.step g ∈ torusGroup ρ.tau Omega
  rw [hstep g, frobTwistGL_apply, hfrobσ]
  exact (Subgroup.mem_normalizer_iff.1 hQnorm _).1 (frobGL_mem_torusGroup σ hg)

private lemma ltrb1f1_map_step_rootSpan_le {Omega : Type} [Field Omega] [IsAlgClosed Omega]
    [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab p R I phi) :
    (rootSpan ρ.tau Omega (kernelRoots (rootCharHom ρ.a))).map ρ.setup.D.step ≤
      rootSpan ρ.tau Omega (kernelRoots (rootCharHom ρ.a)) := by
  simp only [rootSpan, Subgroup.map_iSup]
  refine iSup_le fun α => iSup_le fun hα => ?_
  rw [ρ.setup.frob.map_rootSubgroup α hα.1]
  refine le_iSup₂_of_le (ρ.setup.ρ α) ⟨(ρ.setup.frob.isRoot_iff α).2 hα.1, ?_⟩ le_rfl
  show rootChar ρ.a (ρ.setup.ρ α) = 1
  rw [ρ.setup.frob.rootChar_eq ρ.a ρ.a_torus α hα.1]
  have h1 : rootChar ρ.a α = 1 := hα.2
  rw [h1, one_pow]

private lemma ltrb1f1_map_step_connectedCentralizer_le {Omega : Type} [Field Omega]
    [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab p R I phi) :
    (connectedCentralizer ρ).map ρ.setup.D.step ≤ connectedCentralizer ρ := by
  unfold connectedCentralizer
  rw [Subgroup.map_sup]
  refine sup_le ?_ ?_
  · rw [ltrb1f1_closure_rootDiagUnit_eq_torusGroup (Omega := Omega) ρ.tau]
    exact (ltrb1f1_map_step_torusGroup_le ρ).trans le_sup_left
  · exact (ltrb1f1_map_step_rootSpan_le ρ).trans le_sup_right

private lemma ltrb1f1_two_pow_mod_three_of_dvd_sub {n : ℕ} (h : 3 ∣ 2 ^ n - 1) :
    2 ^ n % 3 = 1 := by
  obtain ⟨k, hk⟩ := h
  have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hk' : 2 ^ n = 3 * k + 1 := by omega
  rw [hk', Nat.add_comm, Nat.add_mul_mod_self_left]

private lemma ltrb1f1_two_pow_mod_three_of_dvd_add {n : ℕ} (h : 3 ∣ 2 ^ n + 1) :
    2 ^ n % 3 = 2 := by
  obtain ⟨k, hk⟩ := h
  have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hk1 : 1 ≤ k := by omega
  have hk' : 2 ^ n = 3 * (k - 1) + 2 := by omega
  rw [hk', Nat.add_comm, Nat.add_mul_mod_self_left]

private lemma ltrb1f1_pow_eq_self_of_mod_one {M : Type*} [Group M] {x : M} (hx : x ^ 3 = 1)
    {q : ℕ} (hq : q % 3 = 1) : x ^ q = x := by
  rw [pow_eq_pow_mod (n := 3) q hx, hq, pow_one]

private lemma ltrb1f1_pow_eq_inv_of_mod_two {M : Type*} [Group M] {x : M} (hx : x ^ 3 = 1)
    {q : ℕ} (hq : q % 3 = 2) : x ^ q = x⁻¹ := by
  rw [pow_eq_pow_mod (n := 3) q hx, hq]
  exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; simpa using hx)

private lemma ltrb1f1_rootChar_pow_three {Omega : Type} [Field Omega] [IsAlgClosed Omega]
    [CharP Omega 2]
    {lab : LargeEvenLabel} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab 3 R I phi) (v : Fin ρ.tau.rank → ℤ) :
    rootChar ρ.a v ^ 3 = 1 := by
  rw [rootChar, ← Finset.prod_pow]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ρ.a_pow i, one_zpow]

private lemma ltrb1f1_weylStep_mem_stabilizer {Omega : Type} [Field Omega] [IsAlgClosed Omega]
    [CharP Omega 2]
    {lab : LargeEvenLabel} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab 3 R I phi) {t : WeylGroup ρ.tau}
    (ht : ∀ v : Fin ρ.tau.rank → ℤ,
      t • v = (if ρ.row.tw then (-1 : ℤ) else 1) • ρ.frobLinear v)
    (hq : (if ρ.row.tw then (2 : ℕ) else 1) = 2 ^ lab.n % 3) :
    t ∈ rootCharStabilizerSubgroup ρ.a := by
  rw [mem_rootCharStabilizerSubgroup]
  refine rootChar_smul_eq_of_forall_isRoot ?_
  intro α hα
  rw [ht α, rootChar_zsmul, ρ.frob_roots α hα,
    ρ.setup.frob.rootChar_eq ρ.a ρ.a_torus α hα, ρ.q_eq]
  have h3 : rootChar ρ.a α ^ 3 = 1 := ltrb1f1_rootChar_pow_three ρ α
  cases htw : ρ.row.tw with
  | false =>
    have hq1 : (2 ^ lab.n) % 3 = 1 := by
      have h := hq; rw [htw] at h; simpa using h.symm
    have hpow : rootChar ρ.a α ^ (2 ^ lab.n) = rootChar ρ.a α :=
      ltrb1f1_pow_eq_self_of_mod_one h3 hq1
    simp only [htw, Bool.false_eq_true, ↓reduceIte]
    rw [hpow, zpow_one]
  | true =>
    have hq2 : (2 ^ lab.n) % 3 = 2 := by
      have h := hq; rw [htw] at h; simpa using h.symm
    have hpow : rootChar ρ.a α ^ (2 ^ lab.n) = (rootChar ρ.a α)⁻¹ :=
      ltrb1f1_pow_eq_inv_of_mod_two h3 hq2
    simp only [htw, ↓reduceIte]
    rw [hpow, zpow_neg, zpow_one, inv_inv]

theorem comm_mem_of_relIndex_three {G : Type} [Group G] {H K : Subgroup G} (hHK : H ≤ K)
    (hN : (H.subgroupOf K).Normal) (h3 : H.relIndex K = 3) :
    ∀ x ∈ K, ∀ y ∈ K, x * y * x⁻¹ * y⁻¹ ∈ H := by
  intro x hx y hy
  let H' : Subgroup K := H.subgroupOf K
  haveI hN' : H'.Normal := hN
  have hindex : H'.index = 3 := h3
  have hcard : Nat.card (K ⧸ H') = 3 := by
    rw [← Subgroup.index_eq_card]; exact hindex
  haveI : Fact (Nat.card (K ⧸ H')).Prime := ⟨by rw [hcard]; norm_num⟩
  haveI : IsCyclic (K ⧸ H') := isCyclic_of_prime_card hcard
  letI : CommGroup (K ⧸ H') := IsCyclic.commGroup
  let xK : K := ⟨x, hx⟩
  let yK : K := ⟨y, hy⟩
  have hcomm : QuotientGroup.mk' H' (xK * yK * xK⁻¹ * yK⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    rw [mul_comm ((QuotientGroup.mk' H') xK) ((QuotientGroup.mk' H') yK)]
    group
  have hmem : (xK * yK * xK⁻¹ * yK⁻¹ : K) ∈ H' := by
    rw [← QuotientGroup.eq_one_iff]
    exact hcomm
  have hmem' : ((xK * yK * xK⁻¹ * yK⁻¹ : K) : G) ∈ H :=
    Subgroup.mem_subgroupOf.mp hmem
  simpa [xK, yK] using hmem'

theorem frobeniusTrivialAt_of_weylStep
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab 3 R I phi)
    (j : Fin ρ.row.D.orbits.length) (hW : WeylStepAt ρ) (hBr : B1BruhatAt ρ j)
    (hHG : connectedCentralizer ρ ≤ geomCentralizer ρ)
    (hN : ((connectedCentralizer ρ).subgroupOf (geomCentralizer ρ)).Normal)
    (hab : ∀ x ∈ geomCentralizer ρ, ∀ y ∈ geomCentralizer ρ,
      x * y * x⁻¹ * y⁻¹ ∈ connectedCentralizer ρ)
    (hq : (if ρ.row.tw then (2 : ℕ) else 1) = 2 ^ lab.n % 3) :
    FrobeniusTrivialAt ρ := by
  intro x hx
  obtain ⟨t, ht_smul, ht_step⟩ := hW
  have htW : t ∈ rootCharStabilizerSubgroup ρ.a :=
    ltrb1f1_weylStep_mem_stabilizer ρ ht_smul hq
  have htW' : t ∈ rootCharStabilizer ρ.a := mem_rootCharStabilizerSubgroup.mp htW
  obtain ⟨w, hw, h, hh, u, hu, v, hv, heq⟩ := hBr.bruhat x hx
  have hw' : w ∈ rootCharStabilizer ρ.a := hw ρ.a (by simp)
  have hwW : w ∈ rootCharStabilizerSubgroup ρ.a := mem_rootCharStabilizerSubgroup.mpr hw'
  have htwnW : t * w * t⁻¹ ∈ rootCharStabilizerSubgroup ρ.a :=
    (rootCharStabilizerSubgroup ρ.a).mul_mem
      ((rootCharStabilizerSubgroup ρ.a).mul_mem htW hwW)
      ((rootCharStabilizerSubgroup ρ.a).inv_mem htW)
  have htG : canonicalRep (coxeterSystem ρ.tau) Omega t ∈ geomCentralizer ρ :=
    canonicalRep_mem_toralCentralizer htW'
  have hwG : canonicalRep (coxeterSystem ρ.tau) Omega w ∈ geomCentralizer ρ :=
    canonicalRep_mem_toralCentralizer hw'
  have htwnG : canonicalRep (coxeterSystem ρ.tau) Omega (t * w * t⁻¹) ∈ geomCentralizer ρ :=
    canonicalRep_mem_toralCentralizer (mem_rootCharStabilizerSubgroup.mp htwnW)
  have htorus_le : torusGroup ρ.tau Omega ≤ connectedCentralizer ρ := by
    unfold connectedCentralizer
    rw [ltrb1f1_closure_rootDiagUnit_eq_torusGroup (Omega := Omega) ρ.tau]
    exact le_sup_left
  have hrootSpan_le : rootSpan ρ.tau Omega (kernelRoots (rootCharHom ρ.a)) ≤
      connectedCentralizer ρ := by
    unfold connectedCentralizer
    exact le_sup_right
  have hhH : h ∈ connectedCentralizer ρ := by
    obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
    exact htorus_le (rootDiagUnit_mem_torusGroup (τ := ρ.tau) l)
  have hfam_sub : CFSG.RankThree.PartOne.KE8F.famKernel
        ({ρ.a} : Set (Fin ρ.tau.rank → Omegaˣ)) ⊆ kernelRoots (rootCharHom ρ.a) := by
    intro γ hγ
    exact ⟨hγ.1, hγ.2 ρ.a (Set.mem_singleton ρ.a)⟩
  have huH : u ∈ connectedCentralizer ρ :=
    hrootSpan_le (rootSpan_mono (Set.inter_subset_left.trans hfam_sub) hu)
  have hvH : v ∈ connectedCentralizer ρ :=
    hrootSpan_le (rootSpan_mono (Set.inter_subset_left.trans hfam_sub) hv)
  have hmapH := ltrb1f1_map_step_connectedCentralizer_le ρ
  have hstep_hH : ρ.setup.D.step h ∈ connectedCentralizer ρ :=
    hmapH (Subgroup.mem_map.mpr ⟨h, hhH, rfl⟩)
  have hstep_uH : ρ.setup.D.step u ∈ connectedCentralizer ρ :=
    hmapH (Subgroup.mem_map.mpr ⟨u, huH, rfl⟩)
  have hstep_vH : ρ.setup.D.step v ∈ connectedCentralizer ρ :=
    hmapH (Subgroup.mem_map.mpr ⟨v, hvH, rfl⟩)
  have hnorm : ∀ g ∈ geomCentralizer ρ, ∀ y ∈ connectedCentralizer ρ,
      g * y * g⁻¹ ∈ connectedCentralizer ρ := by
    intro g hg y hy
    have hmem : (⟨g, hg⟩ : geomCentralizer ρ) * (⟨y, hHG hy⟩ : geomCentralizer ρ) *
        (⟨g, hg⟩ : geomCentralizer ρ)⁻¹ ∈
        (connectedCentralizer ρ).subgroupOf (geomCentralizer ρ) :=
      hN.conj_mem (⟨y, hHG hy⟩ : geomCentralizer ρ) (Subgroup.mem_subgroupOf.mpr hy)
        (⟨g, hg⟩ : geomCentralizer ρ)
    simpa using (Subgroup.mem_subgroupOf.mp hmem)
  have hstepx : ρ.setup.D.step x =
      ρ.setup.D.step h * ρ.setup.D.step u *
        canonicalRep (coxeterSystem ρ.tau) Omega (t * w * t⁻¹) * ρ.setup.D.step v := by
    rw [heq, map_mul, map_mul, map_mul, ht_step w]
  have hwn' : canonicalRep (coxeterSystem ρ.tau) Omega (t * w * t⁻¹) *
        (canonicalRep (coxeterSystem ρ.tau) Omega w)⁻¹ ∈ connectedCentralizer ρ := by
    obtain ⟨k, hk, hk_eq⟩ :=
      CFSG.HardMathSupport.Timmesfeld.CrossChar.canonicalRep_inv_mul_conj_mem (L := Omega) t w
    have hA : canonicalRep (coxeterSystem ρ.tau) Omega (t * w * t⁻¹) =
        canonicalRep (coxeterSystem ρ.tau) Omega t * k *
          canonicalRep (coxeterSystem ρ.tau) Omega w *
            (canonicalRep (coxeterSystem ρ.tau) Omega t)⁻¹ := by
      calc canonicalRep (coxeterSystem ρ.tau) Omega (t * w * t⁻¹)
          = canonicalRep (coxeterSystem ρ.tau) Omega t *
              ((canonicalRep (coxeterSystem ρ.tau) Omega t)⁻¹ *
                canonicalRep (coxeterSystem ρ.tau) Omega (t * w * t⁻¹) *
                  canonicalRep (coxeterSystem ρ.tau) Omega t) *
              (canonicalRep (coxeterSystem ρ.tau) Omega t)⁻¹ := by group
        _ = canonicalRep (coxeterSystem ρ.tau) Omega t *
              (k * canonicalRep (coxeterSystem ρ.tau) Omega w) *
              (canonicalRep (coxeterSystem ρ.tau) Omega t)⁻¹ := by rw [hk_eq]
        _ = canonicalRep (coxeterSystem ρ.tau) Omega t * k *
              canonicalRep (coxeterSystem ρ.tau) Omega w *
              (canonicalRep (coxeterSystem ρ.tau) Omega t)⁻¹ := by group
    rw [hA]
    have h1 : canonicalRep (coxeterSystem ρ.tau) Omega t * k *
        (canonicalRep (coxeterSystem ρ.tau) Omega t)⁻¹ ∈ connectedCentralizer ρ :=
      hnorm _ htG k (htorus_le hk)
    have h2 : canonicalRep (coxeterSystem ρ.tau) Omega t *
        canonicalRep (coxeterSystem ρ.tau) Omega w *
        (canonicalRep (coxeterSystem ρ.tau) Omega t)⁻¹ *
        (canonicalRep (coxeterSystem ρ.tau) Omega w)⁻¹ ∈ connectedCentralizer ρ :=
      hab _ htG _ hwG
    have he : canonicalRep (coxeterSystem ρ.tau) Omega t * k *
        canonicalRep (coxeterSystem ρ.tau) Omega w *
        (canonicalRep (coxeterSystem ρ.tau) Omega t)⁻¹ *
        (canonicalRep (coxeterSystem ρ.tau) Omega w)⁻¹ =
        (canonicalRep (coxeterSystem ρ.tau) Omega t * k *
          (canonicalRep (coxeterSystem ρ.tau) Omega t)⁻¹) *
        (canonicalRep (coxeterSystem ρ.tau) Omega t *
          canonicalRep (coxeterSystem ρ.tau) Omega w *
          (canonicalRep (coxeterSystem ρ.tau) Omega t)⁻¹ *
          (canonicalRep (coxeterSystem ρ.tau) Omega w)⁻¹) := by group
    rw [he]
    exact (connectedCentralizer ρ).mul_mem h1 h2
  have hxa : x * (canonicalRep (coxeterSystem ρ.tau) Omega w)⁻¹ ∈ connectedCentralizer ρ := by
    rw [heq]
    have he : h * u * canonicalRep (coxeterSystem ρ.tau) Omega w * v *
        (canonicalRep (coxeterSystem ρ.tau) Omega w)⁻¹ =
        h * u * (canonicalRep (coxeterSystem ρ.tau) Omega w * v *
          (canonicalRep (coxeterSystem ρ.tau) Omega w)⁻¹) := by group
    rw [he]
    exact (connectedCentralizer ρ).mul_mem
      ((connectedCentralizer ρ).mul_mem hhH huH) (hnorm _ hwG v hvH)
  have hsxa : ρ.setup.D.step x *
      (canonicalRep (coxeterSystem ρ.tau) Omega (t * w * t⁻¹))⁻¹ ∈ connectedCentralizer ρ := by
    rw [hstepx]
    have he : ρ.setup.D.step h * ρ.setup.D.step u *
        canonicalRep (coxeterSystem ρ.tau) Omega (t * w * t⁻¹) * ρ.setup.D.step v *
        (canonicalRep (coxeterSystem ρ.tau) Omega (t * w * t⁻¹))⁻¹ =
        (ρ.setup.D.step h * ρ.setup.D.step u) *
        (canonicalRep (coxeterSystem ρ.tau) Omega (t * w * t⁻¹) * ρ.setup.D.step v *
          (canonicalRep (coxeterSystem ρ.tau) Omega (t * w * t⁻¹))⁻¹) := by group
    rw [he]
    exact (connectedCentralizer ρ).mul_mem
      ((connectedCentralizer ρ).mul_mem hstep_hH hstep_uH) (hnorm _ htwnG _ hstep_vH)
  have hfinal : ρ.setup.D.step x * x⁻¹ ∈ connectedCentralizer ρ := by
    have he : ρ.setup.D.step x * x⁻¹ =
        (ρ.setup.D.step x * (canonicalRep (coxeterSystem ρ.tau) Omega (t * w * t⁻¹))⁻¹) *
        (canonicalRep (coxeterSystem ρ.tau) Omega (t * w * t⁻¹) *
          (canonicalRep (coxeterSystem ρ.tau) Omega w)⁻¹) *
        (x * (canonicalRep (coxeterSystem ρ.tau) Omega w)⁻¹)⁻¹ := by group
    rw [he]
    exact (connectedCentralizer ρ).mul_mem
      ((connectedCentralizer ρ).mul_mem hsxa hwn') ((connectedCentralizer ρ).inv_mem hxa)
  exact hfinal

theorem frobeniusTrivialOn_of_geom_three
    (Omega : Type) [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {row : LargeEvenLabel → LargeEvenLabel → Prop}
    (hrow : ∀ labL labJ : LargeEvenLabel, row labL labJ →
      (labL.tag = .E6 ∧ 3 ∣ 2 ^ labL.n - 1) ∨
        (labL.tag = .twE6 ∧ 3 ∣ 2 ^ labL.n + 1))
    (hg : B1GeomOn Omega row 3) : FrobeniusTrivialOn Omega row := by
  intro lab R _ I phi ρ j hΛ hj hqs hrowj
  have hb := b1bOn_holds Omega lab R I phi ρ j hΛ hj hqs
  have hHG : connectedCentralizer ρ ≤ geomCentralizer ρ := hb.1
  have hN : ((connectedCentralizer ρ).subgroupOf (geomCentralizer ρ)).Normal := hb.2.1
  have hBr : B1BruhatAt ρ j := (b1aOn_holds Omega lab R I phi ρ j hΛ hj hqs).2
  have hrel : (connectedCentralizer ρ).relIndex (geomCentralizer ρ) = 3 :=
    hg lab R I phi ρ j hΛ hj hqs hrowj
  have hab : ∀ x ∈ geomCentralizer ρ, ∀ y ∈ geomCentralizer ρ,
      x * y * x⁻¹ * y⁻¹ ∈ connectedCentralizer ρ :=
    comm_mem_of_relIndex_three hHG hN hrel
  have hW : WeylStepAt ρ := by
    by_cases htw : ρ.row.tw = true
    · exact weylStepAt_twisted ρ (rootActionAgreeAt_holds ρ) htw
    · exact weylStepAt_split ρ (rootActionAgreeAt_holds ρ) (by
        cases h : ρ.row.tw with
        | false => rfl
        | true => exact absurd h htw)
  have hq : (if ρ.row.tw then (2 : ℕ) else 1) = 2 ^ lab.n % 3 := by
    rcases hrow lab ρ.row.D.orbits[j].lab hrowj with ⟨hE6, h3⟩ | ⟨htwE6, h3⟩
    · have htw : ρ.row.tw = false := by
        have h := ρ.row.type_eq
        simp only [ggKacTypeOfLabel, hE6] at h
        have h' : some false = some (ρ.row.tw) := by
          simpa using congrArg (fun o : Option (GGKacType × Bool) => o.map Prod.snd) h
        exact ((Option.some.injEq _ _).mp h').symm
      rw [htw]
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact (ltrb1f1_two_pow_mod_three_of_dvd_sub h3).symm
    · have htw : ρ.row.tw = true := by
        have h := ρ.row.type_eq
        simp only [ggKacTypeOfLabel, htwE6] at h
        have h' : some true = some (ρ.row.tw) := by
          simpa using congrArg (fun o : Option (GGKacType × Bool) => o.map Prod.snd) h
        exact ((Option.some.injEq _ _).mp h').symm
      rw [htw]
      simp only [↓reduceIte]
      exact (ltrb1f1_two_pow_mod_three_of_dvd_add h3).symm
  exact frobeniusTrivialAt_of_weylStep ρ j hW hBr hHG hN hab hq

end CFSG.StandardType.S2MathAs1E6Companion1625

end
