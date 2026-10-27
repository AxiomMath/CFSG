module

public import CFSG.Timmesfeld.Transvection.ModelRankSp
public import CFSG.Timmesfeld.ARS.CaseOADegSpAlign
public import CFSG.ClassicalGroups.Symplectic.StandardForm

public section

namespace CFSG.Timmesfeld.Transvection

namespace ModelRank

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic
  CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.CaseM

variable {n : ℕ} {K : Type} [Field K]

private theorem IsTransGroup.exists_smul_of_isTransGroup {v w : Fin n ⊕ Fin n → K}
    {X : Subgroup (StatedSp n K)} (hv : IsTransGroup v X) (hw : IsTransGroup w X) (hv0 : v ≠ 0) :
    ∃ l : K, v = l • w := by
  obtain ⟨x, hx⟩ := hv.2 1
  have hxX : x ∈ X := (hv.1 x).2 ⟨1, hx⟩
  obtain ⟨c, hc⟩ := (hw.1 x).1 hxX
  have hmat : spTrans v 1 = spTrans w c := hx.symm.trans hc
  have hN : spNil v = c • spNil w := by
    have h := hmat
    simp only [spTrans, one_smul] at h
    exact add_left_cancel h
  obtain ⟨y, hy⟩ := exists_spForm_ne_zero hv0
  have hEq : spForm v y • v = (c * spForm w y) • w := by
    have h := congrArg (fun M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K => M *ᵥ y) hN
    simp only [smul_mulVec, spNil_mulVec, smul_smul, smul_eq_mul] at h
    exact h
  refine ⟨(spForm v y)⁻¹ * (c * spForm w y), ?_⟩
  calc v = (spForm v y)⁻¹ • (spForm v y • v) := by
        rw [smul_smul, inv_mul_cancel₀ hy, one_smul]
    _ = (spForm v y)⁻¹ • ((c * spForm w y) • w) := by rw [hEq]
    _ = ((spForm v y)⁻¹ * (c * spForm w y)) • w := by rw [smul_smul]

private def perp (e : Fin n ⊕ Fin n → K) : Submodule K (Fin n ⊕ Fin n → K) :=
  LinearMap.ker (spFormL e)

private def eMem {e : Fin n ⊕ Fin n → K} (he : e ≠ 0) : perp e :=
  ⟨e, by rw [perp, LinearMap.mem_ker]; simp [spFormL, spForm_self]⟩

private def line {e : Fin n ⊕ Fin n → K} (he : e ≠ 0) : Submodule K (perp e) :=
  Submodule.span K {eMem he}

private abbrev Good {e : Fin n ⊕ Fin n → K} (he : e ≠ 0) : Type :=
  {w : perp e // w ∉ line he}

private noncomputable def transvectionGroup (v : Fin n ⊕ Fin n → K) :
    Subgroup (StatedSp n K) := Classical.choose (exists_isTransGroup v)

private theorem isTransGroup_transvectionGroup (v : Fin n ⊕ Fin n → K) :
    IsTransGroup v (transvectionGroup v) := Classical.choose_spec (exists_isTransGroup v)

private noncomputable def phi {e : Fin n ⊕ Fin n → K} (he : e ≠ 0) (w : Good he) :
    Subgroup (StatedSp n K) := transvectionGroup (w.1 : Fin n ⊕ Fin n → K)

private theorem isTransGroup_phi {e : Fin n ⊕ Fin n → K} (he : e ≠ 0) (w : Good he) :
    IsTransGroup (w.1 : Fin n ⊕ Fin n → K) (phi he w) :=
  isTransGroup_transvectionGroup _

private theorem good_ne_zero {e : Fin n ⊕ Fin n → K} (he : e ≠ 0) (w : Good he) :
    (w.1 : Fin n ⊕ Fin n → K) ≠ 0 := by
  intro h
  apply w.2
  have h0 : w.1 = 0 := Subtype.ext (by simpa using h)
  rw [h0]
  exact (line he).zero_mem

private theorem natCard_line {e : Fin n ⊕ Fin n → K} (he : e ≠ 0) :
    Nat.card (line he) = Nat.card K := by
  have hne : eMem he ≠ 0 := by
    intro h
    exact he (by simpa [eMem] using congrArg Subtype.val h)
  have h := Nat.card_congr (LinearEquiv.toSpanNonzeroSingleton K (perp e) (eMem he) hne).toEquiv
  simpa [line] using h.symm

private theorem natCard_perp [Finite K] {e : Fin n ⊕ Fin n → K} (he : e ≠ 0) :
    Nat.card (perp e) = Nat.card K ^ (2 * n - 1) := by
  have hf : spFormL e ≠ 0 := by
    obtain ⟨y, hy⟩ := exists_spForm_ne_zero he
    intro h
    have h0 : spFormL e y = 0 := by rw [h]; rfl
    exact hy (by simpa [spFormL] using h0)
  have h := LinearMap.finrank_range_add_finrank_ker (spFormL e)
  rw [Module.Dual.range_eq_top_of_ne_zero hf, finrank_top, Module.finrank_self,
    Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin] at h
  have hfr : Module.finrank K (perp e) = 2 * n - 1 := by
    rw [perp]
    omega
  haveI hK : Fintype K := Fintype.ofFinite K
  haveI hV : Fintype (perp e) := Fintype.ofFinite (perp e)
  have hcard : Fintype.card (perp e) = Fintype.card K ^ (2 * n - 1) :=
    (Module.card_eq_pow_finrank (K := K) (V := perp e)).trans (by rw [hfr])
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact hcard

private abbrev ConjSet {e : Fin n ⊕ Fin n → K} (he : e ≠ 0) {T : Subgroup (StatedSp n K)}
    (hT : IsTransGroup e T) : Type :=
  {X : Subgroup (StatedSp n K) // (∃ g, X = conjSub T g) ∧ X ≠ T ∧ Commuting T X}

private theorem phi_conj {e : Fin n ⊕ Fin n → K} (he : e ≠ 0)
    {T : Subgroup (StatedSp n K)} (hT : IsTransGroup e T) (w : Good he) :
    ∃ g, phi he w = conjSub T g := by
  have hw0 : (w.1 : Fin n ⊕ Fin n → K) ≠ 0 := good_ne_zero he w
  obtain ⟨A, hA, hAe⟩ :=
    CFSG.ClassicalGroups.Symplectic.exists_statedSp_mulVec_eq (x := e) (y := (w.1 : _)) he hw0
  let g : StatedSp n K := ⟨A, hA⟩
  refine ⟨g, ?_⟩
  have hmat : SpExtras.mat n K g *ᵥ e = (w.1 : Fin n ⊕ Fin n → K) := by
    rw [SpExtras.mat_apply]
    exact hAe
  have hconj : IsTransGroup (w.1 : Fin n ⊕ Fin n → K) (conjSub T g) := by
    simpa only [hmat] using hT.conjSub g
  exact (isTransGroup_transvectionGroup _).eq hconj

private theorem phi_ne {e : Fin n ⊕ Fin n → K} (he : e ≠ 0)
    {T : Subgroup (StatedSp n K)} (hT : IsTransGroup e T) (w : Good he) :
    phi he w ≠ T := by
  intro h
  have hvT : IsTransGroup (w.1 : Fin n ⊕ Fin n → K) T := by
    simpa only [h] using isTransGroup_phi he w
  obtain ⟨l, hl⟩ :=
    IsTransGroup.exists_smul_of_isTransGroup hvT hT (good_ne_zero he w)
  apply w.2
  have h' : w.1 = l • eMem he := by
    apply Subtype.ext
    change (w.1 : Fin n ⊕ Fin n → K) = l • (eMem he : Fin n ⊕ Fin n → K)
    simpa only [eMem] using hl
  rw [h']
  exact (line he).smul_mem l (Submodule.subset_span (by simp))

private theorem phi_commuting {e : Fin n ⊕ Fin n → K} (he : e ≠ 0)
    {T : Subgroup (StatedSp n K)} (hT : IsTransGroup e T) (w : Good he) :
    Commuting T (phi he w) := by
  have hw : spForm e (w.1 : Fin n ⊕ Fin n → K) = 0 := by
    change (spFormL e) (w.1 : Fin n ⊕ Fin n → K) = 0
    exact w.1.2
  exact hT.commuting (isTransGroup_phi he w) hw

private noncomputable def toConj {e : Fin n ⊕ Fin n → K} (he : e ≠ 0)
    {T : Subgroup (StatedSp n K)} (hT : IsTransGroup e T) (w : Good he) : ConjSet he hT :=
  ⟨phi he w, phi_conj he hT w, phi_ne he hT w, phi_commuting he hT w⟩

private theorem exists_good_phi_eq {e : Fin n ⊕ Fin n → K} (he : e ≠ 0)
    {T : Subgroup (StatedSp n K)} (hT : IsTransGroup e T) (X : ConjSet he hT) :
    ∃ v : Good he, phi he v = X.1 := by
  obtain ⟨g, hg⟩ := X.2.1
  have hcomm : Commuting T (conjSub T g) := by
    have h := X.2.2.2
    rwa [hg] at h
  have hperp : spForm e (SpExtras.mat n K g *ᵥ e) = 0 :=
    spForm_eq_zero_of_commuting hT (hT.conjSub g) he hcomm
  let v0 : perp e := ⟨SpExtras.mat n K g *ᵥ e, by
    change spForm e (SpExtras.mat n K g *ᵥ e) = 0
    exact hperp⟩
  have hv0not : v0 ∉ line he := by
    intro hmem
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hmem
    have hae : a • e = SpExtras.mat n K g *ᵥ e := by
      have h := congrArg (fun x : perp e => (x : Fin n ⊕ Fin n → K)) ha
      change a • (eMem he : Fin n ⊕ Fin n → K) = (v0 : Fin n ⊕ Fin n → K) at h
      simpa only [v0, eMem] using h
    have hv0ne : SpExtras.mat n K g *ᵥ e ≠ 0 := mat_mulVec_ne_zero' g he
    have ha0 : a ≠ 0 := by
      intro ha0
      apply hv0ne
      rw [← hae, ha0, zero_smul]
    have hconj : IsTransGroup (a • e) (conjSub T g) := by
      simpa only [← hae] using hT.conjSub g
    have := (IsTransGroup.of_smul ha0 hconj).eq hT
    exact X.2.2.1 (hg.trans this)
  refine ⟨⟨v0, hv0not⟩, ?_⟩
  have hconj : IsTransGroup (v0 : Fin n ⊕ Fin n → K) (conjSub T g) := by
    change IsTransGroup (SpExtras.mat n K g *ᵥ e) (conjSub T g)
    exact hT.conjSub g
  show transvectionGroup (v0 : Fin n ⊕ Fin n → K) = X.1
  exact ((isTransGroup_transvectionGroup _).eq hconj).trans hg.symm

private def smulGood {e : Fin n ⊕ Fin n → K} (he : e ≠ 0) (v : Good he) (l : K) (hl : l ≠ 0) :
    Good he :=
  ⟨l • v.1, by
    intro hmem
    apply v.2
    have h := (line he).smul_mem l⁻¹ hmem
    simpa only [smul_smul, inv_mul_cancel₀ hl, one_smul] using h⟩

private theorem phi_smulGood {e : Fin n ⊕ Fin n → K} (he : e ≠ 0)
    {T : Subgroup (StatedSp n K)} (hT : IsTransGroup e T) (v : Good he) {l : K} (hl : l ≠ 0) :
    phi he (smulGood he v l hl) = phi he v := by
  have h := CaseOADeg.isTransGroup_smul hl (isTransGroup_phi he v)
  show transvectionGroup (l • (v.1 : Fin n ⊕ Fin n → K)) =
    transvectionGroup (v.1 : Fin n ⊕ Fin n → K)
  exact (isTransGroup_transvectionGroup _).eq h

private theorem natCard_fiber {e : Fin n ⊕ Fin n → K} (he : e ≠ 0)
    {T : Subgroup (StatedSp n K)} (hT : IsTransGroup e T) (X : ConjSet he hT) :
    Nat.card {w : Good he // toConj he hT w = X} = Nat.card K - 1 := by
  obtain ⟨v, hv⟩ := exists_good_phi_eq he hT X
  have hvT : IsTransGroup (v.1 : Fin n ⊕ Fin n → K) X.1 := by
    simpa only [hv] using isTransGroup_phi he v
  have hv0 : (v.1 : Fin n ⊕ Fin n → K) ≠ 0 := good_ne_zero he v
  let f : Kˣ → {w : Good he // toConj he hT w = X} := fun l =>
    ⟨smulGood he v (l : K) (Units.ne_zero l), by
      apply Subtype.ext
      show phi he (smulGood he v (l : K) (Units.ne_zero l)) = X.1
      rw [phi_smulGood he hT v (Units.ne_zero l), hv]⟩
  have hf_inj : Function.Injective f := by
    intro l l' h
    have hval : (l : K) • (v.1 : Fin n ⊕ Fin n → K) =
        (l' : K) • (v.1 : Fin n ⊕ Fin n → K) := by
      have h' := congrArg (fun w : {w : Good he // toConj he hT w = X} =>
        ((w.1.1 : perp e) : Fin n ⊕ Fin n → K)) h
      change (l : K) • (v.1 : Fin n ⊕ Fin n → K) =
        (l' : K) • (v.1 : Fin n ⊕ Fin n → K) at h'
      simpa only [f, smulGood] using h'
    have hlk : (l : K) = (l' : K) := (smul_left_inj hv0).1 hval
    exact Units.ext hlk
  have hf_surj : Function.Surjective f := by
    intro w
    have hwphi : phi he w.1 = X.1 := by
      have h := congrArg Subtype.val w.2
      simpa only [toConj] using h
    have hwT : IsTransGroup ((w.1).1 : Fin n ⊕ Fin n → K) X.1 := by
      simpa only [hwphi] using isTransGroup_phi he w.1
    have hw0 : ((w.1).1 : Fin n ⊕ Fin n → K) ≠ 0 := good_ne_zero he w.1
    obtain ⟨a, ha⟩ := IsTransGroup.exists_smul_of_isTransGroup hwT hvT hw0
    have ha0 : a ≠ 0 := by
      intro ha0
      apply w.1.2
      have h0 : w.1.1 = 0 := by
        apply Subtype.ext
        change (w.1.1 : Fin n ⊕ Fin n → K) = 0
        rw [ha, ha0, zero_smul]
      rw [h0]
      exact (line he).zero_mem
    refine ⟨Units.mk0 a ha0, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change (smulGood he v a ha0).1 = w.1.1
    apply Subtype.ext
    change a • (v.1 : Fin n ⊕ Fin n → K) = ((w.1).1 : Fin n ⊕ Fin n → K)
    exact ha.symm
  have hcard := Nat.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩)
  rw [← hcard]
  exact (Nat.card_units (α := K))

private theorem natCard_good [Finite K] {e : Fin n ⊕ Fin n → K} (he : e ≠ 0) :
    Nat.card (Good he) = Nat.card K ^ (2 * n - 1) - Nat.card K := by
  have hfin : ((line he : Submodule K (perp e)) : Set (perp e)).Finite := Set.toFinite _
  have hfin' : (((line he : Submodule K (perp e)) : Set (perp e))ᶜ).Finite := Set.toFinite _
  have h := Set.ncard_compl_add_ncard ((line he : Submodule K (perp e)) : Set (perp e)) hfin hfin'
  have hgood : Nat.card (Good he) =
      (((line he : Submodule K (perp e)) : Set (perp e))ᶜ).ncard :=
    Nat.card_coe_set_eq _
  have hline : ((line he : Submodule K (perp e)) : Set (perp e)).ncard = Nat.card K := by
    rw [← Nat.card_coe_set_eq]
    exact natCard_line he
  rw [← hgood, hline, natCard_perp he] at h
  omega

private theorem card_conjSub_commuting [Finite K] {e : Fin n ⊕ Fin n → K} (he : e ≠ 0)
    {T : Subgroup (StatedSp n K)} (hT : IsTransGroup e T) (hn : 2 ≤ n) :
    Nat.card (ConjSet he hT) = ∑ i ∈ Finset.Ico 1 (2 * n - 1), Nat.card K ^ i := by
  haveI hS : Fintype (ConjSet he hT) := Fintype.ofFinite _
  haveI hK : Fintype K := Fintype.ofFinite K
  have hsig : Nat.card (Good he) = ∑ X : ConjSet he hT,
      Nat.card {w : Good he // toConj he hT w = X} := by
    rw [Nat.card_congr (Equiv.sigmaFiberEquiv (toConj he hT)).symm]
    rw [Nat.card_sigma]
  have hsum : ∑ X : ConjSet he hT, Nat.card {w : Good he // toConj he hT w = X} =
      Nat.card (ConjSet he hT) * (Nat.card K - 1) := by
    simp_rw [natCard_fiber he hT]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card,
      Nat.cast_id]
  have hN : Nat.card (ConjSet he hT) * (Nat.card K - 1) =
      Nat.card K ^ (2 * n - 1) - Nat.card K := by
    rw [← hsum, ← hsig, natCard_good he]
  have hq2 : 2 ≤ Nat.card K := by
    have := Finite.one_lt_card (α := K)
    omega
  have hq1 : 1 ≤ Nat.card K := by omega
  have hNpos : 0 < 2 * n - 1 := by omega
  have hsplit := Finset.sum_range_eq_add_Ico (fun i : ℕ => Nat.card K ^ i) (n := 2 * n - 1)
    hNpos
  have hgeom := geom_sum_mul_of_one_le (x := Nat.card K) hq1 (2 * n - 1)
  rw [hsplit, pow_zero, Nat.add_mul, one_mul] at hgeom
  have hqN : Nat.card K ≤ Nat.card K ^ (2 * n - 1) := by
    calc Nat.card K = Nat.card K ^ 1 := by rw [pow_one]
      _ ≤ Nat.card K ^ (2 * n - 1) := Nat.pow_le_pow_right hq1 (by omega)
  have htarget : (Nat.card K - 1) + (Nat.card K ^ (2 * n - 1) - Nat.card K) =
      Nat.card K ^ (2 * n - 1) - 1 := by
    have hdecomp := add_tsub_cancel_of_le hqN
    omega
  have h2 : (Nat.card K - 1) +
      (∑ i ∈ Finset.Ico 1 (2 * n - 1), Nat.card K ^ i) * (Nat.card K - 1) =
      (Nat.card K - 1) + (Nat.card K ^ (2 * n - 1) - Nat.card K) := by
    rw [hgeom, htarget]
  have h3 : (∑ i ∈ Finset.Ico 1 (2 * n - 1), Nat.card K ^ i) * (Nat.card K - 1) =
      Nat.card K ^ (2 * n - 1) - Nat.card K := Nat.add_left_cancel h2
  rw [mul_comm] at h3
  have hN' : (Nat.card K - 1) * Nat.card (ConjSet he hT) =
      Nat.card K ^ (2 * n - 1) - Nat.card K := by
    rw [mul_comm]
    exact hN
  have hqne : Nat.card K - 1 ≠ 0 := by omega
  exact mul_left_cancel₀ hqne (hN'.trans h3.symm)

theorem card_commuting_conjSub_rootGroup_sp {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K]
    [Finite K] :
    Nat.card {X : Subgroup (StatedSp n K) //
      (∃ g, X = conjSub ((Symplectic.rootDatum n K).rootGroup
        (Pi.single (⟨n - 1, Nat.sub_one_lt_of_lt (Nat.zero_lt_of_lt hn)⟩ : Fin n) 1)) g) ∧
      X ≠ (Symplectic.rootDatum n K).rootGroup
        (Pi.single (⟨n - 1, Nat.sub_one_lt_of_lt (Nat.zero_lt_of_lt hn)⟩ : Fin n) 1) ∧
      Commuting ((Symplectic.rootDatum n K).rootGroup
        (Pi.single (⟨n - 1, Nat.sub_one_lt_of_lt (Nat.zero_lt_of_lt hn)⟩ : Fin n) 1))
        X} =
      ∑ i ∈ Finset.Ico 1 (2 * n - 1), Nat.card K ^ i := by
  let e : Fin n ⊕ Fin n → K := Pi.single (Sum.inl (⟨n - 1, by omega⟩ : Fin n)) 1
  let T : Subgroup (StatedSp n K) := (Symplectic.rootDatum n K).rootGroup
    (Pi.single (⟨n - 1, by omega⟩ : Fin n) 1)
  have he : e ≠ 0 := by
    intro h
    have h1 : e (Sum.inl (⟨n - 1, by omega⟩ : Fin n)) = 1 := by simp [e]
    rw [h] at h1
    exact one_ne_zero h1.symm
  have hT : IsTransGroup e T :=
    isTransGroup_rootGroup_last (K := K) (n := n) (by omega)
  exact card_conjSub_commuting (e := e) (T := T) he hT hn

theorem not_sq_dvd_card_commuting_conjSub_rootGroup_sp {n : ℕ} (hn : 2 ≤ n) {K : Type}
    [Field K] [Finite K] :
    ¬ Nat.card K ^ 2 ∣ Nat.card {X : Subgroup (StatedSp n K) //
      (∃ g, X = conjSub ((Symplectic.rootDatum n K).rootGroup
        (Pi.single (⟨n - 1, Nat.sub_one_lt_of_lt (Nat.zero_lt_of_lt hn)⟩ : Fin n) 1)) g) ∧
      X ≠ (Symplectic.rootDatum n K).rootGroup
        (Pi.single (⟨n - 1, Nat.sub_one_lt_of_lt (Nat.zero_lt_of_lt hn)⟩ : Fin n) 1) ∧
      Commuting ((Symplectic.rootDatum n K).rootGroup
        (Pi.single (⟨n - 1, Nat.sub_one_lt_of_lt (Nat.zero_lt_of_lt hn)⟩ : Fin n) 1))
        X} := by
  rw [card_commuting_conjSub_rootGroup_sp hn]
  have hq2 : 2 ≤ Nat.card K := by
    have := Finite.one_lt_card (α := K)
    omega
  have h1 : (∑ i ∈ Finset.Ico 1 (2 * n - 1), Nat.card K ^ i) =
      Nat.card K * (∑ k ∈ Finset.range (2 * n - 2), Nat.card K ^ k) := by
    rw [Finset.sum_Ico_eq_sum_range (fun i => Nat.card K ^ i) 1 (2 * n - 1)]
    have hsub : 2 * n - 1 - 1 = 2 * n - 2 := by omega
    rw [hsub]
    have hcongr : (∑ k ∈ Finset.range (2 * n - 2), Nat.card K ^ (1 + k)) =
        ∑ k ∈ Finset.range (2 * n - 2), Nat.card K * Nat.card K ^ k :=
      Finset.sum_congr rfl fun k _ => by
        rw [show 1 + k = k + 1 by omega, pow_succ']
    rw [hcongr, ← Finset.mul_sum]
  have h2 : (∑ k ∈ Finset.range (2 * n - 2), Nat.card K ^ k) =
      1 + Nat.card K * (∑ k ∈ Finset.range (2 * n - 3), Nat.card K ^ k) := by
    have hpos : 0 < 2 * n - 2 := by omega
    rw [Finset.sum_range_eq_add_Ico (fun k => Nat.card K ^ k) (n := 2 * n - 2) hpos,
      pow_zero]
    congr 1
    rw [Finset.sum_Ico_eq_sum_range (fun i => Nat.card K ^ i) 1 (2 * n - 2)]
    have hsub : 2 * n - 2 - 1 = 2 * n - 3 := by omega
    rw [hsub]
    have hcongr : (∑ k ∈ Finset.range (2 * n - 3), Nat.card K ^ (1 + k)) =
        ∑ k ∈ Finset.range (2 * n - 3), Nat.card K * Nat.card K ^ k :=
      Finset.sum_congr rfl fun k _ => by
        rw [show 1 + k = k + 1 by omega, pow_succ']
    rw [hcongr, ← Finset.mul_sum]
  have hS : (∑ i ∈ Finset.Ico 1 (2 * n - 1), Nat.card K ^ i) =
      Nat.card K + Nat.card K ^ 2 * (∑ k ∈ Finset.range (2 * n - 3), Nat.card K ^ k) := by
    rw [h1, h2]
    ring
  intro hdvd
  have hmod : (∑ i ∈ Finset.Ico 1 (2 * n - 1), Nat.card K ^ i) ≡
      Nat.card K [MOD Nat.card K ^ 2] := by
    rw [hS]
    have hcomm : Nat.card K + Nat.card K ^ 2 *
        (∑ k ∈ Finset.range (2 * n - 3), Nat.card K ^ k) =
        Nat.card K ^ 2 * (∑ k ∈ Finset.range (2 * n - 3), Nat.card K ^ k) +
          Nat.card K := by ring
    rw [hcomm]
    exact Nat.ModEq.modulus_mul_add
  have h0 : (∑ i ∈ Finset.Ico 1 (2 * n - 1), Nat.card K ^ i) ≡ 0 [MOD Nat.card K ^ 2] :=
    Dvd.dvd.modEq_zero_nat hdvd
  have hq0 : Nat.card K ≡ 0 [MOD Nat.card K ^ 2] := hmod.symm.trans h0
  have hdvdq : Nat.card K ^ 2 ∣ Nat.card K := Nat.modEq_zero_iff_dvd.1 hq0
  have hle : Nat.card K ^ 2 ≤ Nat.card K := Nat.le_of_dvd (by omega) hdvdq
  have hlt : Nat.card K < Nat.card K ^ 2 := by nlinarith
  omega

end ModelRank

end CFSG.Timmesfeld.Transvection
