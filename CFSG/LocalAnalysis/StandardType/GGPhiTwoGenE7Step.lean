module

public import CFSG.LocalAnalysis.StandardType.GGPhiTwoGenE7StepAux
public import CFSG.LocalAnalysis.StandardType.GGPhiTwoGenHyper
public import CFSG.LocalAnalysis.StandardType.GGPhiTwoGenRow
public import CFSG.LocalAnalysis.StandardType.GGPhiTwoGenE7Bridge
public import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenLabels
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoRank
public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
public import CFSG.LieType.Chevalley.RootCharacterConjugation

public section

namespace CFSG.StandardType.PhiTwoRootGen

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley Multiplicative
open CFSG.LieType.SeitzGeneration.ExcHigh CFSG.ComponentClassification.CatLeafProof

theorem e7A1D6_le_iSup_phiTwoComp
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK4 : 4 ≤ Nat.card K) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1) {g0 : ModGL .E7 (AlgebraicClosure K)}
    (hg0C : g0 ∈ adjointGroup .E7 (AlgebraicClosure K)) {ζ : (AlgebraicClosure K)ˣ}
    (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1)
    {T : Multiplicative (Fin Tag.E7.rank → ZMod p) →* adjointGroup .E7 K}
    (hT : ∀ t : Fin Tag.E7.rank → ZMod p,
      baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((T (ofAdd t) : adjointGroup .E7 K) : ModGL .E7 K) =
        g0 * rootDiagUnit .E7 (TableBExc.E6Three.zetaVec ζ hζ t) * g0⁻¹)
    (hTinj : Function.Injective T)
    (hV6 : ∀ t : Fin Tag.E7.rank → ZMod p, ∑ j, (e7Theta j : ZMod p) * t j = 0 →
      T (ofAdd t) ∈ e7D6Group K)
    (hV1 : ∀ s : ZMod p, T (ofAdd (Pi.single (0 : Fin Tag.E7.rank) s)) ∈ rootPairE7 K e7Theta)
    (hθ : rootPairE7 K e7Theta ≤ phiTwoComp g0 e7Theta) :
    e7A1D6 K ≤ ⨆ γ : {γ : Fin Tag.E7.rank → ℤ // IsRoot .E7 γ}, phiTwoComp g0 γ.1 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨fv, -, hfv⟩ := FiniteField.card K 2
  have hKcard : Nat.card K = 2 ^ (fv : ℕ) := by rw [Nat.card_eq_fintype_card, hfv]
  have hn : 2 ≤ (fv : ℕ) := by
    have h : 2 ^ 2 ≤ 2 ^ (fv : ℕ) := by rw [← hKcard]; norm_num at hK4 ⊢; exact hK4
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h
  have hp : p.Prime := Fact.out
  have h2ne : (2 : ZMod p) ≠ 0 := ggPhiTwoStep_two_ne_zero hp2
  have hθne : (fun j => (e7Theta j : ZMod p)) ≠ 0 := by
    intro hcon
    have hne : ¬ ∀ j, (p : ℤ) ∣ e7Theta j :=
      CFSG.HardMathSupport.C14G2Three.not_forall_dvd_of_isRoot isRoot_e7Theta (by
        rw [Int.isUnit_iff]
        rintro (h | h)
        · have h2 : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp.two_le
          omega
        · have h2 : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp.two_le
          omega)
    apply hne
    intro j
    have h2 : ((e7Theta j : ℤ) : ZMod p) = 0 := by
      have := congrFun hcon j
      simpa using this
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h2
  let f : (Fin Tag.E7.rank → ZMod p) → ZMod p := fun t => ∑ j, (e7Theta j : ZMod p) * t j
  let V6 : Subgroup (Multiplicative (Fin Tag.E7.rank → ZMod p)) :=
    { carrier := {x | f x.toAdd = 0}
      one_mem' := by simp [f]
      mul_mem' := by
        intro x y hx hy
        show (∑ j, (e7Theta j : ZMod p) * (x.toAdd j + y.toAdd j)) = 0
        rw [Finset.sum_congr rfl (fun j _ => mul_add _ _ _), Finset.sum_add_distrib]
        have hx' : ∑ j, (e7Theta j : ZMod p) * x.toAdd j = 0 := hx
        have hy' : ∑ j, (e7Theta j : ZMod p) * y.toAdd j = 0 := hy
        rw [hx', hy', add_zero]
      inv_mem' := by
        intro x hx
        show (∑ j, (e7Theta j : ZMod p) * (-x.toAdd j)) = 0
        rw [Finset.sum_congr rfl (fun j _ => mul_neg _ _), Finset.sum_neg_distrib]
        have hx' : ∑ j, (e7Theta j : ZMod p) * x.toAdd j = 0 := hx
        rw [hx', neg_zero] }
  have hV6mem : ∀ w : ↥V6, ∑ j, (e7Theta j : ZMod p) *
      (w.1 : Multiplicative (Fin Tag.E7.rank → ZMod p)).toAdd j = 0 := by
    intro w
    have hw := w.2
    change f w.1.toAdd = 0 at hw
    simpa [f] using hw
  let T6 : ↥V6 →* ↥(e7D6Group K) :=
    { toFun := fun x => ⟨T (ofAdd x.1.toAdd), hV6 x.1.toAdd (by
        have hx := x.2
        change f x.1.toAdd = 0 at hx
        simpa [f] using hx)⟩
      map_one' := by
        apply Subtype.ext
        show T (ofAdd (1 : Multiplicative (Fin Tag.E7.rank → ZMod p)).toAdd) = 1
        rw [toAdd_one, ofAdd_zero, map_one]
      map_mul' := by
        intro x y
        apply Subtype.ext
        show T (ofAdd (x.1 * y.1).toAdd) = T (ofAdd x.1.toAdd) * T (ofAdd y.1.toAdd)
        rw [toAdd_mul, ofAdd_add, map_mul] }
  have hT6inj : Function.Injective T6 := by
    intro x y hxy
    have h1 : T (ofAdd x.1.toAdd) = T (ofAdd y.1.toAdd) := congrArg Subtype.val hxy
    have h2 : ofAdd x.1.toAdd = ofAdd y.1.toAdd := hTinj h1
    have h3 : x.1.toAdd = y.1.toAdd := by simpa using congrArg Multiplicative.toAdd h2
    exact Subtype.ext (by simpa using h3)
  let E : Subgroup ↥(e7D6Group K) := T6.range
  have hV6card : Nat.card ↥V6 = p ^ 6 := by
    let e : ↥V6 ≃ {t : Fin Tag.E7.rank → ZMod p //
        ∑ j, (e7Theta j : ZMod p) * t j = 0} :=
      { toFun := fun x => ⟨x.1.toAdd, by
          have hx := x.2
          change f x.1.toAdd = 0 at hx
          simpa [f] using hx⟩
        invFun := fun t => ⟨ofAdd t.1, by
          change f (ofAdd t.1).toAdd = 0
          rw [toAdd_ofAdd]
          simpa [f] using t.2⟩
        left_inv := fun x => by
          apply Subtype.ext
          show ofAdd x.1.toAdd = x.1
          rw [ofAdd_toAdd]
        right_inv := fun t => by
          apply Subtype.ext
          show (ofAdd t.1).toAdd = t.1
          rw [toAdd_ofAdd] }
    rw [Nat.card_congr e]
    exact ggPhiTwoStep_card_ker_sum p (fun j => (e7Theta j : ZMod p)) hθne
  have hcardE : Nat.card E = p ^ 6 := by
    have h1 : Nat.card E = Nat.card ↥V6 :=
      Nat.card_congr (Equiv.ofInjective T6 hT6inj).symm
    rw [h1, hV6card]
  have hEelem : CFSG.Open.IsElemAbelian p E := by
    constructor
    · rw [isMulCommutative_iff]
      intro a b
      obtain ⟨x, hx⟩ := a.2
      obtain ⟨y, hy⟩ := b.2
      refine Subtype.ext ?_
      show (a : ↥(e7D6Group K)) * (b : ↥(e7D6Group K)) =
        (b : ↥(e7D6Group K)) * (a : ↥(e7D6Group K))
      rw [← hx, ← hy, ← map_mul, ← map_mul, mul_comm]
    · intro x hx
      obtain ⟨y, hy⟩ := hx
      have hyp : y ^ p = 1 := by
        apply Subtype.ext
        show (y.1 : Multiplicative (Fin Tag.E7.rank → ZMod p)) ^ p = 1
        rw [← ofAdd_toAdd y.1, ← ofAdd_nsmul]
        have h0 : p • y.1.toAdd = 0 := by
          funext j
          show p • (y.1.toAdd j) = 0
          rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
        rw [h0, ofAdd_zero]
      rw [← hy, ← map_pow, hyp, map_one]
  have hD6_centr : e7D6Group K ≤
      Subgroup.centralizer (rootPairE7 K e7Theta : Set (adjointGroup .E7 K)) :=
    ggPhiTwoStep_e7D6_le_centralizer_theta (K := K)
  obtain ⟨θR, hcommX, hZ⟩ := exists_mulEquiv_e7D6Group_rPlus (K := K) hK4
  have hsc : ∀ g : ↥(e7D6Group K), (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E := by
    intro g hgc hgp
    have hcommT : ∀ t : Fin Tag.E7.rank → ZMod p,
        (g : adjointGroup .E7 K) * T (ofAdd t) =
          T (ofAdd t) * (g : adjointGroup .E7 K) := by
      intro t
      set s : ZMod p := (2 : ZMod p)⁻¹ * (∑ j, (e7Theta j : ZMod p) * t j) with hs
      have h2s : (2 : ZMod p) * s = ∑ j, (e7Theta j : ZMod p) * t j := by
        rw [hs, ← mul_assoc, mul_inv_cancel₀ h2ne, one_mul]
      set t6 : Fin Tag.E7.rank → ZMod p := t - Pi.single (0 : Fin Tag.E7.rank) s with ht6
      have ht6mem : ∑ j, (e7Theta j : ZMod p) * t6 j = 0 := by
        rw [ht6]
        simp only [Pi.sub_apply]
        rw [Finset.sum_congr rfl (fun j _ => mul_sub _ _ _), Finset.sum_sub_distrib,
          ggPhiTwoStep_sum_single_theta p s, ← h2s, sub_self]
      have htdecomp : t = t6 + Pi.single (0 : Fin Tag.E7.rank) s := by
        rw [ht6]
        ext j
        simp only [Pi.sub_apply, Pi.add_apply]
        abel
      have hcomm6 : (g : adjointGroup .E7 K) * T (ofAdd t6) =
          T (ofAdd t6) * (g : adjointGroup .E7 K) := by
        have he : (⟨T (ofAdd t6), hV6 t6 ht6mem⟩ : ↥(e7D6Group K)) ∈ E := by
          show (⟨T (ofAdd t6), hV6 t6 ht6mem⟩ : ↥(e7D6Group K)) ∈ T6.range
          refine ⟨⟨ofAdd t6, ?_⟩, ?_⟩
          · show f (ofAdd t6).toAdd = 0
            rw [toAdd_ofAdd]
            simpa [f] using ht6mem
          · apply Subtype.ext
            rfl
        exact congrArg Subtype.val (hgc _ he)
      have hcomm1 : (g : adjointGroup .E7 K) *
            T (ofAdd (Pi.single (0 : Fin Tag.E7.rank) s)) =
          T (ofAdd (Pi.single (0 : Fin Tag.E7.rank) s)) * (g : adjointGroup .E7 K) :=
        (Subgroup.mem_centralizer_iff.mp (hD6_centr g.2)
          (T (ofAdd (Pi.single (0 : Fin Tag.E7.rank) s))) (hV1 s)).symm
      have hTeq : T (ofAdd t) =
          T (ofAdd t6) * T (ofAdd (Pi.single (0 : Fin Tag.E7.rank) s)) := by
        rw [htdecomp, ofAdd_add, map_mul]
      calc (g : adjointGroup .E7 K) * T (ofAdd t)
          = (g : _) * (T (ofAdd t6) * T (ofAdd (Pi.single (0 : Fin Tag.E7.rank) s))) := by
            rw [hTeq]
        _ = ((g : _) * T (ofAdd t6)) * T (ofAdd (Pi.single (0 : Fin Tag.E7.rank) s)) := by
            rw [mul_assoc]
        _ = (T (ofAdd t6) * (g : _)) * T (ofAdd (Pi.single (0 : Fin Tag.E7.rank) s)) := by
            rw [hcomm6]
        _ = T (ofAdd t6) * ((g : _) * T (ofAdd (Pi.single (0 : Fin Tag.E7.rank) s))) := by
            rw [mul_assoc]
        _ = T (ofAdd t6) * (T (ofAdd (Pi.single (0 : Fin Tag.E7.rank) s)) * (g : _)) := by
            rw [hcomm1]
        _ = (T (ofAdd t6) * T (ofAdd (Pi.single (0 : Fin Tag.E7.rank) s))) * (g : _) := by
            rw [mul_assoc]
        _ = T (ofAdd t) * (g : _) := by rw [← hTeq]
    set w : ModGL .E7 (AlgebraicClosure K) :=
      baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((g : adjointGroup .E7 K) : ModGL .E7 K) with hwdef
    set y : ModGL .E7 (AlgebraicClosure K) := g0⁻¹ * w * g0 with hydef
    have hyadj : y ∈ adjointGroup .E7 (AlgebraicClosure K) := by
      rw [hydef]
      exact mul_mem (mul_mem (inv_mem hg0C)
        (CFSG.StandardType.TableBExcTwo.baseChangeGL_mem_adjointGroup
          (algebraMap K (AlgebraicClosure K)) (g.1).2)) hg0C
    have hycomm : ∀ t : Fin Tag.E7.rank → ZMod p,
        y * rootDiagUnit .E7 (TableBExc.E6Three.zetaVec ζ hζ t) =
          rootDiagUnit .E7 (TableBExc.E6Three.zetaVec ζ hζ t) * y := by
      intro t
      set d : ModGL .E7 (AlgebraicClosure K) :=
        rootDiagUnit .E7 (TableBExc.E6Three.zetaVec ζ hζ t) with hd
      have hcommw : w * baseChangeGL (algebraMap K (AlgebraicClosure K))
            ((T (ofAdd t) : adjointGroup .E7 K) : ModGL .E7 K) =
          baseChangeGL (algebraMap K (AlgebraicClosure K))
            ((T (ofAdd t) : adjointGroup .E7 K) : ModGL .E7 K) * w := by
        have h2 := congrArg (fun z : adjointGroup .E7 K =>
          baseChangeGL (algebraMap K (AlgebraicClosure K)) (z : ModGL .E7 K)) (hcommT t)
        simpa [hwdef, map_mul, Subgroup.coe_mul] using h2
      have hXt : w * (g0 * d * g0⁻¹) = (g0 * d * g0⁻¹) * w := by
        rw [hd, ← hT t]
        exact hcommw
      calc y * d = g0⁻¹ * (w * (g0 * d * g0⁻¹)) * g0 :=
            ggPhiTwoStep_conj_mul_assoc g0 w d
        _ = g0⁻¹ * ((g0 * d * g0⁻¹) * w) * g0 := by rw [hXt]
        _ = d * y := ggPhiTwoStep_conj_mul_conj g0 d w
    have hytorus : y ∈ torusGroup .E7 (AlgebraicClosure K) :=
      mem_torusGroup_of_forall_commute_zetaVec hp2 hζo hζ hyadj hycomm
    have hypow : y ^ p = 1 := by
      have hgp' : ((g : adjointGroup .E7 K) ^ p) = 1 := by
        have := congrArg Subtype.val hgp
        simpa using this
      have hwp : w ^ p = 1 := by
        rw [hwdef, ← map_pow]
        have h1 : (((g : adjointGroup .E7 K) : ModGL .E7 K) ^ p) = 1 := by
          have := congrArg (fun z : adjointGroup .E7 K => (z : ModGL .E7 K)) hgp'
          simpa using this
        rw [h1, map_one]
      rw [hydef]
      have hyw : g0⁻¹ * w * g0 = (MulAut.conj g0⁻¹) w := by
        rw [MulAut.conj_apply, inv_inv]
      rw [hyw, ← map_pow, hwp, map_one]
    obtain ⟨t0, ht0⟩ :=
      ggPhiTwoStep_exists_rootDiagUnit_zetaVec_eq_of_pow_eq_one hζo hζ hytorus hypow
    have hTeq2 : T (ofAdd t0) = (g : adjointGroup .E7 K) := by
      have hbc : baseChangeGL (algebraMap K (AlgebraicClosure K))
            ((T (ofAdd t0) : adjointGroup .E7 K) : ModGL .E7 K) =
          baseChangeGL (algebraMap K (AlgebraicClosure K))
            ((g : adjointGroup .E7 K) : ModGL .E7 K) := by
        rw [hT t0, ← ht0, hydef, ← hwdef]
        group
      exact Subtype.ext (baseChangeGL_injective (algebraMap K (AlgebraicClosure K)) hbc)
    have ht0mem : ∑ j, (e7Theta j : ZMod p) * t0 j = 0 := by
      by_contra hne
      set s : ZMod p := (2 : ZMod p)⁻¹ * (∑ j, (e7Theta j : ZMod p) * t0 j) with hs
      have h2s : (2 : ZMod p) * s = ∑ j, (e7Theta j : ZMod p) * t0 j := by
        rw [hs, ← mul_assoc, mul_inv_cancel₀ h2ne, one_mul]
      have hsne : s ≠ 0 := by
        intro h0
        apply hne
        rw [← h2s, h0, mul_zero]
      set t6 : Fin Tag.E7.rank → ZMod p := t0 - Pi.single (0 : Fin Tag.E7.rank) s with ht6
      have ht6mem : ∑ j, (e7Theta j : ZMod p) * t6 j = 0 := by
        rw [ht6]
        simp only [Pi.sub_apply]
        rw [Finset.sum_congr rfl (fun j _ => mul_sub _ _ _), Finset.sum_sub_distrib,
          ggPhiTwoStep_sum_single_theta p s, ← h2s, sub_self]
      have htdecomp : t0 = t6 + Pi.single (0 : Fin Tag.E7.rank) s := by
        rw [ht6]
        ext j
        simp only [Pi.sub_apply, Pi.add_apply]
        abel
      have hTt0 : T (ofAdd t0) =
          T (ofAdd t6) * T (ofAdd (Pi.single (0 : Fin Tag.E7.rank) s)) := by
        rw [htdecomp, ofAdd_add, map_mul]
      have hzX : T (ofAdd (Pi.single (0 : Fin Tag.E7.rank) s)) ∈ e7D6Group K := by
        have hz_eq : T (ofAdd (Pi.single (0 : Fin Tag.E7.rank) s)) =
            (T (ofAdd t6))⁻¹ * (g : adjointGroup .E7 K) :=
          eq_inv_mul_of_mul_eq (hTt0.symm.trans hTeq2)
        rw [hz_eq]
        exact mul_mem (inv_mem (hV6 t6 ht6mem)) g.2
      have hzR : T (ofAdd (Pi.single (0 : Fin Tag.E7.rank) s)) ∈ rootPairE7 K e7Theta :=
        hV1 s
      have hz1 : T (ofAdd (Pi.single (0 : Fin Tag.E7.rank) s)) = 1 := by
        have hz_center : ∀ x : ↥(e7D6Group K),
            (⟨T (ofAdd (Pi.single (0 : Fin Tag.E7.rank) s)), hzX⟩ : ↥(e7D6Group K)) * x =
              x * (⟨T (ofAdd (Pi.single (0 : Fin Tag.E7.rank) s)), hzX⟩ :
                ↥(e7D6Group K)) := by
          intro x
          apply Subtype.ext
          exact Subgroup.mem_centralizer_iff.mp (hD6_centr x.2)
            (T (ofAdd (Pi.single (0 : Fin Tag.E7.rank) s))) hzR
        exact congrArg Subtype.val
          (hZ ⟨T (ofAdd (Pi.single (0 : Fin Tag.E7.rank) s)), hzX⟩ hz_center)
      have h1 : ofAdd (Pi.single (0 : Fin Tag.E7.rank) s : Fin Tag.E7.rank → ZMod p) = 1 := by
        apply hTinj
        rw [hz1, map_one]
      have h2 : Pi.single (0 : Fin Tag.E7.rank) s = (0 : Fin Tag.E7.rank → ZMod p) := by
        have := congrArg Multiplicative.toAdd h1
        simpa using this
      have h3 : s = 0 := by
        have := congrFun h2 (0 : Fin Tag.E7.rank)
        simpa using this
      exact hsne h3
    have hgE : g ∈ E := by
      show g ∈ T6.range
      refine ⟨⟨ofAdd t0, ?_⟩, ?_⟩
      · show f (ofAdd t0).toAdd = 0
        rw [toAdd_ofAdd]
        simpa [f] using ht0mem
      · apply Subtype.ext
        show T (ofAdd (ofAdd t0).toAdd) = (g : adjointGroup .E7 K)
        rw [toAdd_ofAdd]
        exact hTeq2
    exact hgE
  have hrow := ggTorusRootGenAvoidKG_omegaPlusNs (K := K) hKcard hn (by norm_num : 4 ≤ 6)
    hp hp2 hpq 0
  obtain ⟨ι, J, C, hCle, hEcard, hJperf, hJcent, hJtop⟩ :=
    exists_hyperplane_family_of_rootGenAvoidKG (p := p) (r := 0) hp hp2 hrow θR hcommX hZ
      hEelem hsc (fun x => ⟨θR x, rfl⟩)
      (by rw [pow_zero, hcardE]
          exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 6 hp.ne_zero))
      (by rw [hcardE]; exact Nat.pow_le_pow_right (le_of_lt hp.one_lt) (by norm_num))
  let S : ι → Subgroup (adjointGroup .E7 K) := fun i => (J i).map (e7D6Group K).subtype
  have hSperf : ∀ i, ⁅S i, S i⁆ = S i := by
    intro i
    rw [← Subgroup.map_commutator, hJperf i]
  let W : ι → Subgroup ↥V6 := fun i => (C i).comap T6
  let V : ι → Set (Fin Tag.E7.rank → ZMod p) := fun i =>
    {t | ∃ w : ↥V6, w ∈ W i ∧ ∃ s : ZMod p,
      t = (w.1 : Multiplicative (Fin Tag.E7.rank → ZMod p)).toAdd
        + Pi.single (0 : Fin Tag.E7.rank) s}
  have hVcard : ∀ i, (V i).ncard = p ^ (Tag.E7.rank - 1) := by
    intro i
    rw [← Nat.card_coe_set_eq]
    have h1 : Nat.card ↥(V i) = Nat.card (W i) * p := ggPhiTwoStep_card_V hp2 hV6mem (W i)
    have h2 : Nat.card (W i) = Nat.card (C i) := by
      have hmap : (W i).map T6 = C i := by
        rw [Subgroup.map_comap_eq_self]
        exact hCle i
      have h3 : Nat.card ((W i).map T6) = Nat.card (W i) :=
        Subgroup.card_map_of_injective hT6inj
      rw [hmap] at h3
      exact h3.symm
    rw [h1, h2, ← hEcard i, hcardE]
    rfl
  have hhyp : ∀ i, ∃ V' : Set (Fin Tag.E7.rank → ZMod p),
      V'.ncard = p ^ (Tag.E7.rank - 1) ∧
      ∀ x ∈ S i, ∀ t ∈ V', x * T (ofAdd t) = T (ofAdd t) * x := by
    intro i
    refine ⟨V i, hVcard i, ?_⟩
    intro x hx t ht
    obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨w, hw, s, rfl⟩ := ht
    have hcomm_w : (j : adjointGroup .E7 K) * T (ofAdd (w.1).toAdd) =
        T (ofAdd (w.1).toAdd) * (j : adjointGroup .E7 K) := by
      have := hJcent i j hj (T6 w) hw
      exact congrArg Subtype.val this
    have hcomm_1 : (j : adjointGroup .E7 K) *
          T (ofAdd (Pi.single (0 : Fin Tag.E7.rank) s)) =
        T (ofAdd (Pi.single (0 : Fin Tag.E7.rank) s)) * (j : adjointGroup .E7 K) :=
      (Subgroup.mem_centralizer_iff.mp (hD6_centr j.2)
        (T (ofAdd (Pi.single (0 : Fin Tag.E7.rank) s))) (hV1 s)).symm
    have hTeq : T (ofAdd ((w.1).toAdd + Pi.single (0 : Fin Tag.E7.rank) s)) =
        T (ofAdd (w.1).toAdd) * T (ofAdd (Pi.single (0 : Fin Tag.E7.rank) s)) := by
      rw [ofAdd_add, map_mul]
    rw [hTeq]
    calc (j : adjointGroup .E7 K)
          * (T (ofAdd (w.1).toAdd) * T (ofAdd (Pi.single (0 : Fin Tag.E7.rank) s)))
        = ((j : _) * T (ofAdd (w.1).toAdd))
            * T (ofAdd (Pi.single (0 : Fin Tag.E7.rank) s)) := by
          rw [mul_assoc]
      _ = (T (ofAdd (w.1).toAdd) * (j : _))
            * T (ofAdd (Pi.single (0 : Fin Tag.E7.rank) s)) := by
          rw [hcomm_w]
      _ = T (ofAdd (w.1).toAdd)
            * ((j : _) * T (ofAdd (Pi.single (0 : Fin Tag.E7.rank) s))) := by
          rw [mul_assoc]
      _ = T (ofAdd (w.1).toAdd)
            * (T (ofAdd (Pi.single (0 : Fin Tag.E7.rank) s)) * (j : _)) := by
          rw [hcomm_1]
      _ = (T (ofAdd (w.1).toAdd) * T (ofAdd (Pi.single (0 : Fin Tag.E7.rank) s)))
            * (j : _) := by
          rw [mul_assoc]
  have hS_le : (⨆ i, S i) ≤
      ⨆ γ : {γ : Fin Tag.E7.rank → ℤ // IsRoot .E7 γ}, phiTwoComp g0 γ.1 :=
    iSup_le_iSup_phiTwoComp_of_hyperplane_family (τ := .E7) (Or.inr (Or.inl rfl)) hp2 hg0C
      hζo hζ (T := T) hT S hSperf hhyp
  have htopmap : (⊤ : Subgroup ↥(e7D6Group K)).map (e7D6Group K).subtype = e7D6Group K := by
    ext x; constructor
    · rintro ⟨y, -, rfl⟩; exact y.2
    · intro hx; exact ⟨⟨x, hx⟩, trivial, rfl⟩
  have hmap_le : (⨆ i, J i).map (e7D6Group K).subtype ≤
      ⨆ i, (J i).map (e7D6Group K).subtype := by
    rw [Subgroup.map_le_iff_le_comap]
    refine iSup_le fun i => ?_
    intro x hx
    exact Subgroup.mem_iSup_of_mem i (Subgroup.mem_map_of_mem _ hx)
  have htop : (⨆ i, S i) = e7D6Group K := by
    apply le_antisymm
    · refine iSup_le fun i => ?_
      exact (Subgroup.map_mono (le_top : J i ≤ ⊤)).trans (le_of_eq htopmap)
    · rw [← htopmap, ← hJtop]
      exact hmap_le
  have hD6le : e7D6Group K ≤
      ⨆ γ : {γ : Fin Tag.E7.rank → ℤ // IsRoot .E7 γ}, phiTwoComp g0 γ.1 := by
    rw [← htop]
    exact hS_le
  rw [e7A1D6]
  refine sup_le hD6le ?_
  exact hθ.trans (le_iSup (fun γ : {γ : Fin Tag.E7.rank → ℤ // IsRoot .E7 γ} =>
    phiTwoComp g0 γ.1) ⟨e7Theta, isRoot_e7Theta⟩)

end CFSG.StandardType.PhiTwoRootGen

end
