module

public import CFSG.LocalAnalysis.StandardType.GGFamRatComp
public import CFSG.LieType.Chevalley.CoordinateFieldBaseChange
public import CFSG.LieType.AlgebraicGroups.RootWordRegular
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleSplit

public section

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.StandardType.TableCRes
open CFSG.LieType.Steinberg.Adjoint

namespace CFSG.LieType.AlgebraicGroups

private theorem reflect_exists_zero_of_isAlgClosed
    {K L : Type*} [Field K] [Field L] [IsAlgClosed K]
    (f : K →+* L) {σ : Type*} [Finite σ] (P : Set (MvPolynomial σ K)) (z : σ → L)
    (hz : ∀ p ∈ P, MvPolynomial.eval₂Hom f z p = 0) :
    ∃ x : σ → K, ∀ p ∈ P, MvPolynomial.aeval x p = 0 := by
  set I := Ideal.span P
  have hI : I ≠ ⊤ := by
    intro htop
    have hle : I ≤ RingHom.ker (MvPolynomial.eval₂Hom f z) := by
      rw [Ideal.span_le]
      intro p hp
      exact hz p hp
    have h1 : (1 : MvPolynomial σ K) ∈ RingHom.ker (MvPolynomial.eval₂Hom f z) :=
      hle (htop ▸ Submodule.mem_top)
    rw [RingHom.mem_ker, map_one] at h1
    exact one_ne_zero h1
  obtain ⟨J, hJ, hIJ⟩ := Ideal.exists_le_maximal I hI
  obtain ⟨x, hx⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal K hJ
  refine ⟨x, fun p hp => ?_⟩
  have hpJ : p ∈ J := hIJ (Ideal.subset_span hp)
  rw [hx, MvPolynomial.mem_vanishingIdeal_singleton_iff] at hpJ
  exact hpJ

private theorem reflect_apply_eq_of_baseChange
    {τ : Tag} {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S)
    {A : Module.End R (RootModule τ R)} {B : Module.End S (RootModule τ S)}
    (h : BaseChange f A B) (a b : Label τ) :
    f (A (Finsupp.single b 1) a) = B (Finsupp.single b 1) a := by
  have h1 := congrArg (fun y : RootModule τ S => y a) (BaseChange.apply h (Finsupp.single b 1))
  rw [Finsupp.mapRange_apply, Finsupp.mapRange_single, map_one] at h1
  simpa using h1

private theorem reflect_goodWord_of_mem_rootSpan
    {τ : Tag} {L : Type} [Field L]
    (Ψ : Set (Fin τ.rank → ℤ)) {x : ModGL τ L}
    (hx : x ∈ rootSpan τ L Ψ) :
    ∃ l : List ((Fin τ.rank → ℤ) × L),
      (∀ p ∈ l, p.1 ∈ Ψ) ∧ (l.map (fun p => pinnedX τ L p.1 p.2)).prod = x := by
  have hspan : rootSpan τ L Ψ = Subgroup.closure (⋃ α : Ψ, Set.range (pinnedX τ L α.1)) := by
    rw [rootSpan, iSup_subtype']
    simp only [rootSubgroup, Subgroup.closure_iUnion]
  rw [hspan] at hx
  induction hx using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨α, hα⟩ := Set.mem_iUnion.1 hg
    obtain ⟨c, hc⟩ := hα
    refine ⟨[(α.1, c)], ?_, ?_⟩
    · intro p hp
      rw [List.mem_singleton] at hp
      subst hp
      exact α.2
    · rw [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      exact hc
  | one => exact ⟨[], by simp, by simp⟩
  | mul g h hg hh ihg ihh =>
    obtain ⟨lg, hgl, hlg⟩ := ihg
    obtain ⟨lh, hhh, hlh⟩ := ihh
    refine ⟨lg ++ lh, ?_, ?_⟩
    · intro p hp
      rw [List.mem_append] at hp
      exact hp.elim (hgl p) (hhh p)
    · rw [List.map_append, List.prod_append, hlg, hlh]
  | inv g hg ih =>
    obtain ⟨l, hl, hlg⟩ := ih
    refine ⟨(l.map (fun p => (p.1, -p.2))).reverse, ?_, ?_⟩
    · intro p hp
      rw [List.mem_reverse, List.mem_map] at hp
      obtain ⟨q, hq, rfl⟩ := hp
      exact hl q hq
    · rw [List.map_reverse, List.map_map]
      change (List.map (fun p : (Fin τ.rank → ℤ) × L => pinnedX τ L p.1 (-p.2)) l).reverse.prod =
        g⁻¹
      have hmap : List.map (fun p : (Fin τ.rank → ℤ) × L => pinnedX τ L p.1 (-p.2)) l =
          List.map (fun x => x⁻¹)
            (List.map (fun p : (Fin τ.rank → ℤ) × L => pinnedX τ L p.1 p.2) l) := by
        rw [List.map_map]
        exact List.map_congr_left fun p _ => (pinnedX_neg τ L p.1 p.2).symm
      rw [hmap, ← List.prod_inv_reverse, hlg]

theorem mem_rootSpan_of_baseChangeGL_mem_algClosed
    {τ : Tag} {K L : Type} [Field K] [Field L] [IsAlgClosed K]
    (ι : K →+* L) (Ψ : Set (Fin τ.rank → ℤ)) {g : ModGL τ K}
    (hg : baseChangeGL ι g ∈ rootSpan τ L Ψ) :
    g ∈ rootSpan τ K Ψ := by
  classical
  obtain ⟨l, hl, hlg⟩ := reflect_goodWord_of_mem_rootSpan Ψ hg
  let R := MvPolynomial (Fin l.length) K
  let W : List (Letter τ × R) :=
    (List.ofFn fun k : Fin l.length =>
      CFSG.LieType.AlgebraicGroups.pinnedWord τ R (l.get k).1 (MvPolynomial.X k)).flatten
  let c : Fin l.length → L := fun k => (l.get k).2
  let P : (Module.End R (RootModule τ R))ˣ := wordUnit τ R W
  have hmapW : mapWord (MvPolynomial.eval₂Hom ι c) W =
      (List.ofFn fun k : Fin l.length =>
        CFSG.LieType.AlgebraicGroups.pinnedWord τ L (l.get k).1 (c k)).flatten := by
    dsimp only [W]
    rw [mapWord_flatten, List.map_ofFn]
    congr 1
    rw [List.ofFn_inj]
    funext k
    rw [Function.comp_apply, mapWord_pinnedWord, MvPolynomial.eval₂Hom_X']
  have hword : wordUnit τ L (mapWord (MvPolynomial.eval₂Hom ι c) W) = baseChangeGL ι g := by
    rw [hmapW, wordUnit_flatten]
    have hofn : List.map (wordUnit τ L) (List.ofFn fun k : Fin l.length =>
        CFSG.LieType.AlgebraicGroups.pinnedWord τ L (l.get k).1 (c k)) =
        List.ofFn fun k : Fin l.length => pinnedX τ L (l.get k).1 (c k) := by
      rw [List.map_ofFn, List.ofFn_inj]
      funext k
      rw [Function.comp_apply, wordUnit_pinnedWord]
    rw [hofn, ← hlg]
    congr 1
    have hofn' : List.map (fun p : (Fin τ.rank → ℤ) × L => pinnedX τ L p.1 p.2) l =
        List.ofFn (fun k : Fin l.length => pinnedX τ L (l.get k).1 (l.get k).2) := by
      conv_lhs => rw [← List.ofFn_get l, List.map_ofFn]
      rfl
    rw [hofn']
  let eqs : Set (MvPolynomial (Fin l.length) K) :=
    {q | ∃ a b : Label τ,
      q = (P : Module.End R (RootModule τ R)) (Finsupp.single b 1) a -
        MvPolynomial.C ((g : Module.End K (RootModule τ K)) (Finsupp.single b 1) a)}
  have hsol : ∀ q ∈ eqs, MvPolynomial.eval₂Hom ι c q = 0 := by
    rintro q ⟨a, b, rfl⟩
    rw [map_sub, MvPolynomial.eval₂Hom_C]
    have hbc := reflect_apply_eq_of_baseChange (MvPolynomial.eval₂Hom ι c)
      (baseChange_wordUnit (τ := τ) (MvPolynomial.eval₂Hom ι c) W) a b
    have hcoe : ((baseChangeGL ι g : ModGL τ L) : Module.End L (RootModule τ L))
        (Finsupp.single b 1) a =
        ι ((g : Module.End K (RootModule τ K)) (Finsupp.single b 1) a) := by
      rw [coe_baseChangeGL, baseChangeEnd_single, Finsupp.mapRange_apply]
    rw [hbc, hword, hcoe, sub_self]
  obtain ⟨x, hx⟩ := reflect_exists_zero_of_isAlgClosed ι eqs c hsol
  let Wx : List (Letter τ × K) := mapWord (MvPolynomial.aeval x).toRingHom W
  have hmapWx : Wx =
      (List.ofFn fun k : Fin l.length =>
        CFSG.LieType.AlgebraicGroups.pinnedWord τ K (l.get k).1 (x k)).flatten := by
    dsimp only [Wx, W]
    rw [mapWord_flatten, List.map_ofFn]
    congr 1
    rw [List.ofFn_inj]
    funext k
    rw [Function.comp_apply, mapWord_pinnedWord,
      show (MvPolynomial.aeval x).toRingHom (MvPolynomial.X k) = x k from MvPolynomial.aeval_X x k]
  have hwordx : wordUnit τ K Wx =
      (List.ofFn fun k : Fin l.length => pinnedX τ K (l.get k).1 (x k)).prod := by
    rw [hmapWx, wordUnit_flatten]
    have hofn : List.map (wordUnit τ K) (List.ofFn fun k : Fin l.length =>
        CFSG.LieType.AlgebraicGroups.pinnedWord τ K (l.get k).1 (x k)) =
        List.ofFn fun k : Fin l.length => pinnedX τ K (l.get k).1 (x k) := by
      rw [List.map_ofFn, List.ofFn_inj]
      funext k
      rw [Function.comp_apply, wordUnit_pinnedWord]
    rw [hofn]
  have hxmem : wordUnit τ K Wx ∈ rootSpan τ K Ψ := by
    rw [hwordx]
    exact list_prod_pinnedX_mem_rootSpan (fun k : Fin l.length => (l.get k).1)
      (fun k => hl (l.get k) (List.get_mem l k)) x
  have hg_eq : g = wordUnit τ K Wx := by
    have hbcx := baseChange_wordUnit (τ := τ) (MvPolynomial.aeval x).toRingHom W
    have hentry : ∀ a b,
        (wordUnit τ K Wx : Module.End K (RootModule τ K)) (Finsupp.single b 1) a =
        (g : Module.End K (RootModule τ K)) (Finsupp.single b 1) a := by
      intro a b
      have h := reflect_apply_eq_of_baseChange (τ := τ) (R := MvPolynomial (Fin l.length) K)
        (S := K) (MvPolynomial.aeval x).toRingHom hbcx a b
      rw [← h]
      have hq : ((P : Module.End R (RootModule τ R)) (Finsupp.single b 1) a -
          MvPolynomial.C ((g : Module.End K (RootModule τ K)) (Finsupp.single b 1) a)) ∈ eqs :=
        ⟨a, b, rfl⟩
      have hxq := hx _ hq
      rw [map_sub, MvPolynomial.aeval_C] at hxq
      exact sub_eq_zero.mp hxq
    refine Units.ext ?_
    refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
    ext a
    exact (hentry a b).symm
  rw [hg_eq]
  exact hxmem

end CFSG.LieType.AlgebraicGroups

end
