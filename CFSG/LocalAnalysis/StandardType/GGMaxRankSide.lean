module

public import CFSG.LocalAnalysis.StandardType.GGMaxRankLinear
public import CFSG.LocalAnalysis.StandardType.GGMaxRankE8Typed
public import CFSG.LocalAnalysis.StandardType.GGMaxRankE8Extra
public import CFSG.LocalAnalysis.StandardType.GGMaxRankE8Gen
public import CFSG.LocalAnalysis.StandardType.GGMaxRankWeyl
public import CFSG.LocalAnalysis.StandardType.GGMaxRankChain
public import CFSG.LocalAnalysis.StandardType.GGResMaxRankDefs
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfMaxNormTwo
public import CFSG.LocalAnalysis.StandardType.GGMaxRankPairing
public import CFSG.LocalAnalysis.StandardType.GGTBTorCartan

public section

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def ggMaxRankEmb : Fin 8 ⊕ Fin 1 → Fin 8 ⊕ Fin 2 :=
  Sum.map id (fun _ => 0)

@[expose] def GGMaxRankSideChain {G : Type} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (Bs X J : Subgroup G) (eJ : (CoxeterMatrix.A 8).Group ≃* ↥(ggAutomizer J Bs)) : Prop :=
  p = 3 ∧ ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
    (φ : Fin 8 ⊕ Fin 1 → MulAut ↥Bs) (h : Fin 8 ⊕ Fin 1 → V)
    (α : Fin 8 ⊕ Fin 1 → Module.Dual (ZMod p) V),
    (∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o) ∧
    (∀ o, GGIsReflection p (φ o)) ∧
    (∀ i, φ (Sum.inl i) =
      ((eJ ((CoxeterMatrix.A 8).simple i) : ↥(ggAutomizer J Bs)) : MulAut ↥Bs)) ∧
    (∀ o o', α o (h o') = ggMaxRankPairing p 0 0 false (ggMaxRankEmb o) (ggMaxRankEmb o')) ∧
    (∑ j : Fin 8, ((ggMaxRankMarks j : ℕ) : ZMod p) • h (Sum.inl j) = 0) ∧
    (Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) = p → Module.finrank (ZMod p) V = 9) ∧
    Module.finrank (ZMod p)
      ↥(Submodule.span (ZMod p) (Set.range fun j : Fin 8 => h (Sum.inl j))) = 7 ∧
    ggAutomizer X Bs = Subgroup.closure (Set.range φ) ∧
    (∃ fX : CoxeterMatrix.E₈.Group ≃* ↥(ggAutomizer X Bs),
      ∀ i, GGIsReflection p
        ((fX (CoxeterMatrix.E₈.simple i) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs))

private theorem l6m8_symmetrizedCartan_E8 :
    (Tag.E8).symmetrizedCartan = CartanMatrix.E₈ := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

private lemma l6m8_iform_eq (x y : Fin Tag.E8.rank → ℤ) :
    iform (τ := .E8) x y = ∑ k, ∑ l, x k * CartanMatrix.E₈ k l * y l := by
  simp only [CFSG.LieType.Steinberg.Adjoint.iform, l6m8_symmetrizedCartan_E8]
  rfl

private lemma l6m8_coeff_eq_marks (j : Fin 8) :
    (((![2, 4, 6, 5, 4, 3, 2, 1] : Fin 8 → ℤ) j : ℤ) : ZMod 3) =
      (ggMaxRankMarks j : ZMod 3) := by
  fin_cases j <;> decide

private lemma l6m8_marks_kerA : ∀ i : Fin 8,
    ∑ j : Fin 8, ((CartanMatrix.A 8 i j : ℤ) : ZMod 3) *
      ((ggMaxRankMarks j : ℕ) : ZMod 3) = 0 := by
  decide

private lemma l6m8_marks_ne :
    (fun j : Fin 8 => ((ggMaxRankMarks j : ℕ) : ZMod 3)) ≠ 0 := by
  decide

private lemma l6m8_pair_iform {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (hD8 : Fin Tag.E8.rank → V)
    (αD : Fin Tag.E8.rank → Module.Dual (ZMod p) V)
    (hpairD : ∀ i j : Fin Tag.E8.rank, αD i (hD8 j) = ((CartanMatrix.E₈ i j : ℤ) : ZMod p))
    (x y : Fin Tag.E8.rank → ℤ) :
    (∑ k, ((x k : ℤ) : ZMod p) • αD k) (∑ l, ((y l : ℤ) : ZMod p) • hD8 l)
      = ((iform (τ := .E8) x y : ℤ) : ZMod p) := by
  rw [l6m8_iform_eq]
  push_cast
  change ((∑ k, ((x k : ℤ) : ZMod p) • αD k : Module.Dual (ZMod p) V))
      (∑ l, ((y l : ℤ) : ZMod p) • hD8 l) = _
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, hpairD, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem ggMaxRank_sideChain {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp : p = 3)
    (hp2 : p ≠ 2) {Bs X J : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hD : GGResE8SeparatedDatum p Bs X)
    (hnt : ∀ g ∈ ggAutomizer X Bs, ¬ GGIsTransvection p g)
    (eJ : (CoxeterMatrix.A 8).Group ≃* ↥(ggAutomizer J Bs))
    (heJ : ∀ i, GGIsReflection p
      ((eJ ((CoxeterMatrix.A 8).simple i) : ↥(ggAutomizer J Bs)) : MulAut ↥Bs))
    (hJX : ggAutomizer J Bs ≤ ggAutomizer X Bs) :
    GGMaxRankSideChain p Bs X J eJ := by
  classical
  subst hp
  obtain ⟨V, hVadd, hVmod, ι, φD, hD8, αD, hlinD, hreflD, hpairD, ⟨f, hf⟩, hclD, hsepD⟩ := hD
  letI : AddCommGroup V := hVadd
  letI : Module (ZMod 3) V := hVmod
  have hrefl8 : ∀ i : Fin 8,
      GGIsReflection 3 ((f (CoxeterMatrix.E₈.simple i) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) :=
    fun i => by rw [hf i]; exact hreflD i
  obtain ⟨c, hc, hgram, hspec⟩ :=
    ggMaxRank_chainRoots hp2 hBs f hrefl8 hnt eJ heJ hJX
  let s : Fin 8 → WeylGroup .E8 := fun i => Classical.choose (hspec i)
  have hs := fun i => Classical.choose_spec (hspec i)
  obtain ⟨b, hbpair, hbb, hbrel, _hbker⟩ := e8_chain_extraVec c hgram
  have hb : IsRoot .E8 b :=
    CFSG.StandardType.ExcFramesHalf.isRoot_of_iform_self_eq_two (τ := .E8) (Or.inr rfl) hbb
  let sb : WeylGroup .E8 := rootReflection b
  have hsb : ∀ v : Fin Tag.E8.rank → ℤ, sb • v = v - iform (τ := .E8) v b • b := by
    intro v
    rw [rootReflection_smul hb v]
    have hc2 : corootPair b v = iform (τ := .E8) v b := by
      have hm := corootPair_mul hb v
      rw [hbb] at hm
      have h2 : corootPair b v = iform (τ := .E8) b v :=
        mul_right_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) (by rw [hm]; ring)
      rw [h2, iform_comm]
    rw [hc2]
  let A : Subgroup (MulAut ↥Bs) := ggAutomizer X Bs
  let Φ : WeylGroup .E8 →* ↥A := f.toMonoidHom.comp ggE8Equiv.symm.toMonoidHom
  let ρ : WeylGroup .E8 →* (V ≃ₗ[ZMod 3] V) := (ggLin (p := 3) ι).comp (A.subtype.comp Φ)
  have hρ : ∀ (i : Fin Tag.E8.rank) (v : V), ρ (simple .E8 i) v = v - αD i v • hD8 i := by
    intro i v
    have hsym : ggE8Equiv.symm (simple .E8 i) = CoxeterMatrix.E₈.simple i := by
      rw [← ggE8Equiv_simple i, MulEquiv.symm_apply_apply]
    have hfun : ρ (simple .E8 i) = ggLin (p := 3) ι (φD i) := by
      change ggLin (p := 3) ι (((Φ (simple .E8 i)) : ↥A) : MulAut ↥Bs) =
        ggLin (p := 3) ι (φD i)
      rw [show Φ (simple .E8 i) = f (CoxeterMatrix.E₈.simple i) by
        show f (ggE8Equiv.symm (simple .E8 i)) = f (CoxeterMatrix.E₈.simple i)
        rw [hsym]]
      rw [show ((f (CoxeterMatrix.E₈.simple i) : ↥A) : MulAut ↥Bs) = φD i from hf i]
    rw [hfun]
    exact hlinD i v
  let φ : Fin 8 ⊕ Fin 1 → MulAut ↥Bs := Sum.elim
    (fun i => ((f (ggE8Equiv.symm (s i)) : ↥A) : MulAut ↥Bs))
    (fun _ => ((f (ggE8Equiv.symm sb) : ↥A) : MulAut ↥Bs))
  let Hp : (Fin Tag.E8.rank → ZMod 3) →ₗ[ZMod 3] V :=
    { toFun := fun x => ∑ k, x k • hD8 k
      map_add' := by
        intro x y
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro r x
        simp only [Pi.smul_apply, smul_assoc]
        rw [Finset.smul_sum]
        rfl }
  let hv : Fin 8 ⊕ Fin 1 → V := Sum.elim
    (fun i => Hp (fun k => (c i k : ZMod 3)))
    (fun _ => Hp (fun k => (b k : ZMod 3)))
  let αv : Fin 8 ⊕ Fin 1 → Module.Dual (ZMod 3) V := Sum.elim
    (fun i => ∑ k, (c i k : ZMod 3) • αD k)
    (fun _ => ∑ k, (b k : ZMod 3) • αD k)
  have hHp_apply : ∀ x, Hp x = ∑ k, x k • hD8 k := fun x => rfl
  have hhv_inl : ∀ i, hv (Sum.inl i) = Hp (fun k => (c i k : ZMod 3)) := fun i => rfl
  have hhv_inr : ∀ k, hv (Sum.inr k) = Hp (fun k => (b k : ZMod 3)) := fun k => rfl
  have hαv_inl : ∀ i, αv (Sum.inl i) = ∑ k, (c i k : ZMod 3) • αD k := fun i => rfl
  have hαv_inr : ∀ k, αv (Sum.inr k) = ∑ k, (b k : ZMod 3) • αD k := fun k => rfl
  have hformula_inl : ∀ i w, ggLin (p := 3) ι (φ (Sum.inl i)) w =
      w - αv (Sum.inl i) w • hv (Sum.inl i) := by
    intro i w
    have h := ggMaxRank_weyl_refl_form (p := 3) hD8 αD hpairD ρ hρ (c i) (hc i) (s i) ((hs i).1) w
    rw [show ρ (s i) = ggLin (p := 3) ι (φ (Sum.inl i)) from rfl] at h
    simpa only [αv, hv, hHp_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      Sum.elim_inl] using h
  have hformula_inr : ∀ w, ggLin (p := 3) ι (φ (Sum.inr 0)) w =
      w - αv (Sum.inr 0) w • hv (Sum.inr 0) := by
    intro w
    have h := ggMaxRank_weyl_refl_form (p := 3) hD8 αD hpairD ρ hρ b hb sb hsb w
    rw [show ρ sb = ggLin (p := 3) ι (φ (Sum.inr 0)) from rfl] at h
    simpa only [αv, hv, hHp_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      Sum.elim_inr] using h
  have hformula : ∀ o w, ggLin (p := 3) ι (φ o) w = w - αv o w • hv o := by
    intro o w
    cases o with
    | inl i => exact hformula_inl i w
    | inr k => fin_cases k; exact hformula_inr w
  have hpair_all : ∀ o o',
      αv o (hv o') = ggMaxRankPairing 3 0 0 false (ggMaxRankEmb o) (ggMaxRankEmb o') := by
    intro o o'
    cases o with
    | inl i =>
      cases o' with
      | inl j =>
        change (∑ k, (c i k : ZMod 3) • αD k) (∑ l, (c j l : ZMod 3) • hD8 l) =
          ggMaxRankPairing 3 0 0 false (Sum.inl i) (Sum.inl j)
        rw [l6m8_pair_iform hD8 αD hpairD (c i) (c j), hgram i j]
        exact (ggMaxRankPairing_chain 3 0 0 false i j).symm
      | inr k =>
        fin_cases k
        change (∑ k, (c i k : ZMod 3) • αD k) (∑ l, (b l : ZMod 3) • hD8 l) =
          ggMaxRankPairing 3 0 0 false (Sum.inl i) (Sum.inr 0)
        rw [l6m8_pair_iform hD8 αD hpairD (c i) b, iform_comm (c i) b, hbpair i]
        fin_cases i <;>
          simp [ggMaxRankPairing, ggMaxRankEdge, ggMaxRankEmb] <;> norm_num
    | inr k =>
      fin_cases k
      cases o' with
      | inl j =>
        change (∑ k, (b k : ZMod 3) • αD k) (∑ l, (c j l : ZMod 3) • hD8 l) =
          ggMaxRankPairing 3 0 0 false (Sum.inr 0) (Sum.inl j)
        rw [l6m8_pair_iform hD8 αD hpairD b (c j), hbpair j]
        fin_cases j <;>
          simp [ggMaxRankPairing, ggMaxRankEdge, ggMaxRankEmb] <;> norm_num
      | inr k' =>
        fin_cases k'
        change (∑ k, (b k : ZMod 3) • αD k) (∑ l, (b l : ZMod 3) • hD8 l) =
          ggMaxRankPairing 3 0 0 false (Sum.inr 0) (Sum.inr 0)
        rw [l6m8_pair_iform hD8 αD hpairD b b, hbb]
        simp [ggMaxRankPairing, ggMaxRankEmb]
  have hself : ∀ o, αv o (hv o) = 2 := by
    intro o
    rw [hpair_all o o]
    cases o with
    | inl i => simp [ggMaxRankEmb, ggMaxRankPairing]
    | inr k => fin_cases k; simp [ggMaxRankEmb, ggMaxRankPairing]
  have hrefl_all : ∀ o, GGIsReflection 3 (φ o) := by
    intro o
    refine ggIsReflection_of_eq_reflection hp2 ι (hself o) ?_
    exact ggLin_eq_reflection ι (hself o) (fun w => hformula o w)
  have hrel : (∑ j : Fin 8, (![2, 4, 6, 5, 4, 3, 2, 1] : Fin 8 → ℤ) j • c j) +
      (3 : ℤ) • b = 0 := by
    simpa [Fin.sum_univ_eight] using hbrel
  have hMZ0 : (fun t : Fin Tag.E8.rank =>
      ∑ j : Fin 8, ((ggMaxRankMarks j : ℕ) : ZMod 3) * (c j t : ZMod 3)) = 0 := by
    funext t
    have ht := congrFun hrel t
    simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_apply, Pi.zero_apply, smul_eq_mul] at ht
    have h3 : (3 : ZMod 3) = 0 := ZMod.natCast_self 3
    have key : (∑ j : Fin 8,
        (((![2, 4, 6, 5, 4, 3, 2, 1] : Fin 8 → ℤ) j : ℤ) : ZMod 3) * (c j t : ZMod 3)) = 0 := by
      have hcast := congrArg (fun z : ℤ => (z : ZMod 3)) ht
      push_cast at hcast
      simpa [h3] using hcast
    calc (∑ j : Fin 8, ((ggMaxRankMarks j : ℕ) : ZMod 3) * (c j t : ZMod 3))
        = ∑ j : Fin 8,
            (((![2, 4, 6, 5, 4, 3, 2, 1] : Fin 8 → ℤ) j : ℤ) : ZMod 3) * (c j t : ZMod 3) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [l6m8_coeff_eq_marks j]
      _ = 0 := key
  have hmarks_mem : (∑ j : Fin 8, ((ggMaxRankMarks j : ℕ) : ZMod 3) • hv (Sum.inl j)) = 0 := by
    have hstep : ∀ j : Fin 8, hv (Sum.inl j) = Hp (fun t => (c j t : ZMod 3)) :=
      fun j => hhv_inl j
    calc (∑ j : Fin 8, ((ggMaxRankMarks j : ℕ) : ZMod 3) • hv (Sum.inl j))
        = ∑ j : Fin 8, ((ggMaxRankMarks j : ℕ) : ZMod 3) •
            Hp (fun t => (c j t : ZMod 3)) := by simp only [hstep]
      _ = Hp (∑ j : Fin 8,
            ((ggMaxRankMarks j : ℕ) : ZMod 3) • (fun t => (c j t : ZMod 3))) := by
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro j _
          rw [map_smul]
      _ = Hp (fun t => ∑ j : Fin 8,
            ((ggMaxRankMarks j : ℕ) : ZMod 3) * (c j t : ZMod 3)) := rfl
      _ = Hp 0 := by rw [hMZ0]
      _ = 0 := map_zero Hp
  let L : (Fin 8 → ZMod 3) →ₗ[ZMod 3] V :=
    { toFun := fun a => ∑ j, a j • hv (Sum.inl j)
      map_add' := by
        intro a b
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro r a
        simp only [Pi.smul_apply, smul_assoc]
        rw [Finset.smul_sum]
        rfl }
  have hrange : LinearMap.range L =
      Submodule.span (ZMod 3) (Set.range fun j : Fin 8 => hv (Sum.inl j)) := by
    apply le_antisymm
    · rintro _ ⟨a, rfl⟩
      change (∑ j : Fin 8, a j • hv (Sum.inl j)) ∈
        Submodule.span (ZMod 3) (Set.range fun j : Fin 8 => hv (Sum.inl j))
      exact Submodule.sum_mem _ fun j _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self j))
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact ⟨Pi.single j 1, by simp [L, Pi.single_apply]⟩
  have hmarks_kerA : ∀ i : Fin 8,
      ∑ j : Fin 8, ((CartanMatrix.A 8 i j : ℤ) : ZMod 3) *
        ((ggMaxRankMarks j : ℕ) : ZMod 3) = 0 := l6m8_marks_kerA
  have hmarks_ne : (fun j : Fin 8 => ((ggMaxRankMarks j : ℕ) : ZMod 3)) ≠ 0 := l6m8_marks_ne
  have hker : LinearMap.ker L =
      Submodule.span (ZMod 3)
        ({fun j : Fin 8 => ((ggMaxRankMarks j : ℕ) : ZMod 3)} : Set (Fin 8 → ZMod 3)) := by
    ext a
    constructor
    · intro ha
      have hLa : L a = 0 := ha
      have hkerA : ∀ i : Fin 8,
          ∑ j : Fin 8, ((CartanMatrix.A 8 i j : ℤ) : ZMod 3) * a j = 0 := by
        intro i
        have hα0 : αv (Sum.inl i) (L a) = 0 := by rw [hLa, map_zero]
        have hcomp : αv (Sum.inl i) (L a) =
            ∑ j : Fin 8, ((CartanMatrix.A 8 i j : ℤ) : ZMod 3) * a j := by
          change αv (Sum.inl i) (∑ j : Fin 8, a j • hv (Sum.inl j)) = _
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro j _
          rw [map_smul, hpair_all (Sum.inl i) (Sum.inl j)]
          simp only [ggMaxRankEmb, Sum.map_inl, id_eq]
          rw [ggMaxRankPairing_chain, smul_eq_mul]
          ring
        rw [← hcomp]
        exact hα0
      obtain ⟨l, hl⟩ :=
        ggCartanA_ker_le_one (N := 8)
          (fun j : Fin 8 => ((ggMaxRankMarks j : ℕ) : ZMod 3)) a hmarks_kerA hkerA hmarks_ne
      rw [Submodule.mem_span_singleton]
      exact ⟨l, hl.symm⟩
    · intro ha
      rw [Submodule.mem_span_singleton] at ha
      obtain ⟨l, rfl⟩ := ha
      rw [LinearMap.mem_ker]
      rw [LinearMap.map_smul]
      have hL0 : L (fun j : Fin 8 => ((ggMaxRankMarks j : ℕ) : ZMod 3)) = 0 := by
        change (∑ j : Fin 8, ((ggMaxRankMarks j : ℕ) : ZMod 3) • hv (Sum.inl j)) = 0
        exact hmarks_mem
      rw [hL0, smul_zero]
  have hkerdim : Module.finrank (ZMod 3) (LinearMap.ker L) = 1 := by
    rw [hker]
    exact finrank_span_singleton hmarks_ne
  have hdim7 : Module.finrank (ZMod 3)
      ↥(Submodule.span (ZMod 3) (Set.range fun j : Fin 8 => hv (Sum.inl j))) = 7 := by
    have hrank := LinearMap.finrank_range_add_finrank_ker L
    rw [hkerdim] at hrank
    have hfin : Module.finrank (ZMod 3) (Fin 8 → ZMod 3) = 8 := by
      simp
    rw [hfin] at hrank
    rw [← hrange]
    omega
  have hdim9 : Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) = 3 →
      Module.finrank (ZMod 3) V = 9 := by
    intro hcard
    exact ggMaxRank_finrank_of_datum (p := 3) ι hD8 αD hpairD hsepD hcard
  have hgen : Subgroup.closure (Set.range s ∪ {sb}) = ⊤ :=
    e8_weyl_generated_by_chain c b hc hb hgram hbpair s sb (fun i => (hs i).1) hsb
  have hgenA : ggAutomizer X Bs = Subgroup.closure (Set.range φ) := by
    let g : WeylGroup .E8 →* MulAut ↥Bs := A.subtype.comp Φ
    have hmap := MonoidHom.map_closure g (Set.range s ∪ {sb})
    rw [hgen] at hmap
    have htop : (⊤ : Subgroup (WeylGroup .E8)).map g = A := by
      ext y
      constructor
      · rintro ⟨x, -, rfl⟩
        exact (Φ x).2
      · intro hy
        obtain ⟨w, hw⟩ := MulEquiv.surjective (ggE8Equiv.symm.trans f) ⟨y, hy⟩
        refine ⟨w, Subgroup.mem_top w, ?_⟩
        have hw' : Φ w = ⟨y, hy⟩ := by simpa [Φ, MulEquiv.trans_apply] using hw
        rw [show g w = ((Φ w : ↥A) : MulAut ↥Bs) from rfl, hw']
    rw [htop] at hmap
    have hg_s : ∀ i, g (s i) = φ (Sum.inl i) := fun i => rfl
    have hg_sb : g sb = φ (Sum.inr 0) := rfl
    have himg : g '' (Set.range s ∪ {sb}) = Set.range φ := by
      ext r
      constructor
      · rintro ⟨x, hx, rfl⟩
        rcases hx with ⟨i, rfl⟩ | rfl
        · exact ⟨Sum.inl i, (hg_s i).symm⟩
        · exact ⟨Sum.inr 0, hg_sb.symm⟩
      · rintro ⟨o, rfl⟩
        cases o with
        | inl i => exact ⟨s i, Or.inl ⟨i, rfl⟩, hg_s i⟩
        | inr k => fin_cases k; exact ⟨sb, Or.inr rfl, hg_sb⟩
    rw [himg] at hmap
    exact hmap
  refine ⟨rfl, V, hVadd, hVmod, ι, φ, hv, αv, hformula, hrefl_all, ?_, hpair_all, ?_, hdim9,
    hdim7, hgenA, ?_⟩
  · intro i
    show ((f (ggE8Equiv.symm (s i)) : ↥A) : MulAut ↥Bs) =
      ((eJ ((CoxeterMatrix.A 8).simple i) : ↥(ggAutomizer J Bs)) : MulAut ↥Bs)
    rw [show s i = Classical.choose (hspec i) from rfl]
    exact ((hs i).2).symm
  · exact hmarks_mem
  · exact ⟨f, fun i => by rw [hf i]; exact hreflD i⟩

end CFSG.StandardType

end
