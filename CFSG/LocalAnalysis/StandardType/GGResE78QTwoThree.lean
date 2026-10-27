module

public import CFSG.LocalAnalysis.StandardType.GGResE78Module
public import CFSG.LocalAnalysis.StandardType.GGRCCardJoin
public import CFSG.LocalAnalysis.StandardType.GGPZWeylType
public import CFSG.LocalAnalysis.StandardType.GGCompListMarked
public import CFSG.LocalAnalysis.StandardType.GGE7TwoThreeComp
public import CFSG.LocalAnalysis.StandardType.GGE8TwoThreeComp
public import CFSG.LocalAnalysis.StandardType.GGResExcSplitExactTwoL
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1E7
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1E8
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2E7Rank
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2ExceptionalAction
public import CFSG.LocalAnalysis.StandardType.GGResHigherFieldI1
public import CFSG.LocalAnalysis.StandardType.GGResJOpenLabel
import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1Regimes
import CFSG.LocalAnalysis.StandardType.GGTCJHolds
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGTBTorLiftRowsHolds
import CFSG.LocalAnalysis.StandardType.GGTBE6
public import CFSG.LocalAnalysis.StandardType.GGRCTransfer
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeTenLinearAux1
public import CFSG.LocalAnalysis.StandardType.GGResIINegOne
public import CFSG.LocalAnalysis.StandardType.GGQ2P3Hyp
public import CFSG.LocalAnalysis.StandardType.GGRCCaseIIBasic
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
import Mathlib.LinearAlgebra.Projection

import CFSG.LocalAnalysis.StandardType.GGResTwoCells

public import CFSG.LocalAnalysis.StandardType.GGResCentBoundNbrHolds

public import CFSG.LocalAnalysis.StandardType.ZS.UseInputHolds

public import CFSG.LocalAnalysis.StandardType.ZS.Adapter

public section
namespace CFSG.StandardType
open CFSG CFSG.Assembly
open S2MathAs51642Interfaces

theorem GGResHyp.card_bstar_of_e7_two
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hL : GGInnerDiagOnLabel (fun _ lab => lab.tag = .E7 ∧ lab.n = 1) 3 Bs L) :
    Nat.card Bs = 3 ^ 8 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨V, _, _, ι, φ, h, α, _, _, _, _, _, hcard, _⟩ :=
    e78_e7_actual_module hH (hL.mono_label fun _ h => ⟨rfl, h⟩)
  exact hcard

theorem GGResHyp.card_bstar_of_e8_two
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hL : GGInnerDiagOnLabel (fun _ lab => lab.tag = .E8 ∧ lab.n = 1) 3 Bs L) :
    Nat.card Bs = 3 ^ 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨V, _, _, ι, φ, h, α, _, _, _, _, _, hcard, _⟩ :=
    e78_e8_actual_module hH (hL.mono_label fun _ h => ⟨rfl, h⟩)
  exact hcard

theorem GGResHyp.card_automizer_L_of_e7_two
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hL : GGInnerDiagOnLabel (fun _ lab => lab.tag = .E7 ∧ lab.n = 1) 3 Bs L) :
    Nat.card (ggAutomizer L Bs) = 2903040 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨V, _, _, ι, φ, h, α, _, _, _, ⟨e, _⟩, _⟩ :=
    e78_e7_actual_module hH (hL.mono_label fun _ h => ⟨rfl, h⟩)
  exact (Nat.card_congr e.toEquiv).symm.trans card_coxeterE7_group

theorem GGResHyp.card_automizer_L_of_e8_two
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hL : GGInnerDiagOnLabel (fun _ lab => lab.tag = .E8 ∧ lab.n = 1) 3 Bs L) :
    Nat.card (ggAutomizer L Bs) = 696729600 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨V, _, _, ι, φ, h, α, _, _, _, ⟨e, _⟩, _⟩ :=
    e78_e8_actual_module hH (hL.mono_label fun _ h => ⟨rfl, h⟩)
  exact (Nat.card_congr e.toEquiv).symm.trans card_coxeterE8_group

private theorem e78_matrix_of_large_order {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {M : CoxeterMatrix Λ} (hM : GGIsWeylMatrix M)
    (h6 : 6 < Fintype.card Λ) (h8 : Fintype.card Λ ≤ 8)
    (hbig : 2 ^ Fintype.card Λ * (Fintype.card Λ).factorial < Nat.card M.Group) :
    (∃ e : Fin 7 ≃ Λ, M = CoxeterMatrix.E₇.reindex e) ∨
      (∃ e : Fin 8 ≃ Λ, M = CoxeterMatrix.E₈.reindex e) := by
  rcases hM with ⟨n, e, hn, hA | ⟨hn2, hB⟩ | ⟨hn4, hD⟩⟩ |
      ⟨e, hE6⟩ | hE7 | hE8 | ⟨e, hF4⟩ | ⟨e, hG2⟩
  · have hc : Fintype.card Λ = n := by simpa using (Fintype.card_congr e).symm
    have hle := l05nK3a_card_reindex_le (CoxeterMatrix.A n) e hA
      (l05nK3a_coxeterA_le n)
    have hbig' : 2 ^ n * n.factorial < Nat.card M.Group := by simpa only [hc] using hbig
    exact False.elim (not_le_of_gt hbig' hle)
  · have hc : Fintype.card Λ = n := by simpa using (Fintype.card_congr e).symm
    have hle := l05nK3a_card_reindex_le (CoxeterMatrix.B n) e hB
      (card_coxeterB_le n)
    have hbig' : 2 ^ n * n.factorial < Nat.card M.Group := by simpa only [hc] using hbig
    exact False.elim (not_le_of_gt hbig' hle)
  · have hc : Fintype.card Λ = n := by simpa using (Fintype.card_congr e).symm
    have hle := l05nK3a_card_reindex_le (ggCoxeterMatrixD n) e hD
      (l05nK3a_coxeterD_le n (by omega))
    have hbig' : 2 ^ n * n.factorial < Nat.card M.Group := by simpa only [hc] using hbig
    exact False.elim (not_le_of_gt hbig' hle)
  · have hc : Fintype.card Λ = 6 := by simpa using (Fintype.card_congr e).symm
    omega
  · exact Or.inl hE7
  · exact Or.inr hE8
  · have hc : Fintype.card Λ = 4 := by simpa using (Fintype.card_congr e).symm
    omega
  · have hc : Fintype.card Λ = 2 := by simpa using (Fintype.card_congr e).symm
    omega

theorem GGResHyp.coxeter_e7_of_automizer
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hL : GGInnerDiagOnLabel (fun _ lab => lab.tag = .E7 ∧ lab.n = 1) 3 Bs L)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {M : CoxeterMatrix Λ}
    (hM : GGIsWeylMatrix M) (f : M.Group ≃* ↥(ggAutomizer L Bs)) :
    ∃ e : Fin 7 ≃ Λ, M = CoxeterMatrix.E₇.reindex e := by
  have hc : Nat.card M.Group = 2903040 :=
    (Nat.card_congr f.toEquiv).trans (hH.card_automizer_L_of_e7_two hL)
  have htype := ggWeylTypeData_of_isWeylMatrix hM
  rw [hc] at htype
  have hr : Fintype.card Λ = 7 := ggWeylTypeData_rank_eq htype
    (by simp [GGWeylTypeData] : GGWeylTypeData 7 2903040 2)
  rcases e78_matrix_of_large_order hM (by omega) (by omega)
      (by rw [hr, hc]; norm_num) with h7 | ⟨e, h8⟩
  · exact h7
  · have he := Fintype.card_congr e
    simp only [Fintype.card_fin, hr] at he
    omega

theorem GGResHyp.coxeter_e8_of_automizer
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hL : GGInnerDiagOnLabel (fun _ lab => lab.tag = .E8 ∧ lab.n = 1) 3 Bs L)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {M : CoxeterMatrix Λ}
    (hM : GGIsWeylMatrix M) (f : M.Group ≃* ↥(ggAutomizer L Bs)) :
    ∃ e : Fin 8 ≃ Λ, M = CoxeterMatrix.E₈.reindex e := by
  have hc : Nat.card M.Group = 696729600 :=
    (Nat.card_congr f.toEquiv).trans (hH.card_automizer_L_of_e8_two hL)
  have htype := ggWeylTypeData_of_isWeylMatrix hM
  rw [hc] at htype
  have hr : Fintype.card Λ = 8 := ggWeylTypeData_rank_eq htype
    (by simp [GGWeylTypeData] : GGWeylTypeData 8 696729600 2)
  rcases e78_matrix_of_large_order hM (by omega) (by omega)
      (by rw [hr, hc]; norm_num) with ⟨e, h7⟩ | h8
  · have he := Fintype.card_congr e
    simp only [Fintype.card_fin, hr] at he
    omega
  · exact h8

private theorem e78_core_std
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hOrb : GGResCentBoundInput)
    (hKG : GGReflClassLargeInput') (hKS : GGReflClassOmegaSmall)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {S : Finset Λ}
    {Λa : Type} [Fintype Λa] [DecidableEq Λa]
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    {MK : CoxeterMatrix ({i : Λ // i ∉ S} ⊕ Λa)}
    {CK : Matrix ({i : Λ // i ∉ S} ⊕ Λa) ({i : Λ // i ∉ S} ⊕ Λa) ℤ}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {ι : Additive ↥Bs ≃+ V} {φ : Λ ⊕ Λa → MulAut ↥Bs} {h : Λ ⊕ Λa → V}
    {α : Λ ⊕ Λa → Module.Dual (ZMod 3) V}
    (hWML : GGIsWeylMatrix ML) (hCL : GGIntCartan ML CL)
    (hWMK : GGIsWeylMatrix MK) (hCK : GGIntCartan MK CK)
    (hform : ∀ o w, ggLin (p := 3) ι (φ o) w = w - α o w • h o)
    (hpairL : ∀ i j : Λ, α (Sum.inl i) (h (Sum.inl j)) = (CL i j : ZMod 3))
    (hpairK : ∀ o o' : {i : Λ // i ∉ S} ⊕ Λa,
      α (o.map Subtype.val id) (h (o'.map Subtype.val id)) = (CK o o' : ZMod 3))
    (hgenL : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (Sum.inl i)))
    (hgenK : ggAutomizer K Bs = Subgroup.closure
      (Set.range (fun j : {j : Λ // j ∉ S} => φ (Sum.inl j)) ∪
        Set.range fun a : Λa => φ (Sum.inr a)))
    (hScard : S.card = 2)
    {n : ℕ} {e : Fin n ≃ Λ} {C0 : Matrix (Fin n) (Fin n) ℤ} {k : ℕ} {M : ℕ}
    (hchk : ggNegOneCheck C0 k = true)
    (hstd : ∀ i j : Fin n, CL (e i) (e j) = C0 i j)
    (hunit : IsUnit ((CL.det : ℤ) : ZMod 3))
    (hcardBs : Nat.card ↥Bs = 3 ^ (n + 1))
    (hALcard : Nat.card ↥(ggAutomizer L Bs) = M)
    (hn : 7 ≤ n)
    (hnumFull : 8 * (3 ^ (n + 1) * ((3 - 1) * 6 * M)) < 3 ^ ((n + 1) * n / 2))
    (hnumFix : 8 * ((3 - 1) * 6 * M) < 3 ^ (n * (n - 1) / 2)) :
    ZS.LinWeyl 3 ((ggAutomizer L Bs ⊔ ggAutomizer K Bs).map (ggLin (p := 3) ι)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  let r : Λ ⊕ Λa → V ≃ₗ[ZMod 3] V := fun o => ggLin (p := 3) ι (φ o)
  let A : Subgroup (V ≃ₗ[ZMod 3] V) :=
    (ggAutomizer L Bs ⊔ ggAutomizer K Bs).map (ggLin (p := 3) ι)
  have hmap_of_closure : ∀ {σ : Type} (ψ : σ → MulAut ↥Bs),
      (Subgroup.closure (Set.range ψ)).map (ggLin (p := 3) ι) =
        Subgroup.closure (Set.range fun i => ggLin (p := 3) ι (ψ i)) := by
    intro σ ψ
    rw [MonoidHom.map_closure]
    congr 1
    exact (Set.range_comp (ggLin (p := 3) ι) ψ).symm
  have hmapL : (ggAutomizer L Bs).map (ggLin (p := 3) ι) =
      Subgroup.closure (Set.range fun i : Λ => r (Sum.inl i)) := by
    rw [hgenL]
    simpa [r] using hmap_of_closure (fun i : Λ => φ (Sum.inl i))
  let φK : ({i : Λ // i ∉ S} ⊕ Λa) → MulAut ↥Bs := fun o => φ (o.map Subtype.val id)
  have hgenK' : ggAutomizer K Bs = Subgroup.closure (Set.range φK) := by
    rw [hgenK]
    congr 1
    ext ψ
    constructor
    · rintro (⟨j, rfl⟩ | ⟨a, rfl⟩)
      · exact ⟨Sum.inl j, rfl⟩
      · exact ⟨Sum.inr a, rfl⟩
    · rintro ⟨o, rfl⟩
      rcases o with j | a
      · exact Or.inl ⟨j, rfl⟩
      · exact Or.inr ⟨a, rfl⟩
  have hmapK : (ggAutomizer K Bs).map (ggLin (p := 3) ι) =
      Subgroup.closure (Set.range fun o : {i : Λ // i ∉ S} ⊕ Λa =>
        r (o.map Subtype.val id)) := by
    rw [hgenK']
    simpa [r, φK] using hmap_of_closure φK
  have hA : A = Subgroup.closure (Set.range r) := by
    dsimp [A]
    rw [Subgroup.map_sup, hmapL, hmapK, ← Subgroup.closure_union]
    congr 1
    ext ψ
    constructor
    · rintro (⟨i, rfl⟩ | ⟨o, rfl⟩)
      · exact ⟨Sum.inl i, rfl⟩
      · exact ⟨o.map Subtype.val id, rfl⟩
    · rintro ⟨o, rfl⟩
      rcases o with i | a
      · exact Or.inl ⟨i, rfl⟩
      · exact Or.inr ⟨Sum.inr a, rfl⟩
  have hxBs : x ∈ Bs := hH.1.tableB_facts.2.2.1
  have hx1 : x ≠ 1 := hH.1.1.2.2.2.2.2.2.1.2.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hH.1.tableB_facts.2.2.2.1
  let xv : V := ι (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs))
  have hx0 : xv ≠ 0 := by
    intro h0
    have h2 : Additive.ofMul (⟨x, hxBs⟩ : ↥Bs) = 0 := by
      apply ι.injective
      simpa [xv] using h0
    have h1 : (⟨x, hxBs⟩ : ↥Bs) = 1 := by
      simpa using congrArg Additive.toMul h2
    exact hx1 (by simpa using congrArg Subtype.val h1)
  have hα : ∀ o : Λ ⊕ Λa, α o (h o) = 2 := by
    intro o
    rcases o with i | a
    · rw [hpairL i i, hCL.1 i]
      norm_num
    · have h1 : α (Sum.inr a) (h (Sum.inr a)) =
          (CK (Sum.inr a) (Sum.inr a) : ZMod 3) := by
        simpa using hpairK (Sum.inr a) (Sum.inr a)
      rw [h1, hCK.1 (Sum.inr a)]
      norm_num
  have hαx : ∀ i : Λ, α (Sum.inl i) xv = 0 := by
    intro i
    have hdiag : α (Sum.inl i) (h (Sum.inl i)) = 2 := by
      rw [hpairL i i, hCL.1 i]
      norm_num
    have hh : h (Sum.inl i) ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hdiag
      exact (by
        intro hz
        have hdvd : (3 : ℤ) ∣ 2 := (ZMod.intCast_zmod_eq_zero_iff_dvd 2 3).mp hz
        norm_num at hdvd : (2 : ZMod 3) ≠ 0) hdiag.symm
    have hmem : φ (Sum.inl i) ∈ ggAutomizer L Bs := by
      rw [hgenL]
      exact Subgroup.subset_closure ⟨i, rfl⟩
    have hfixφ := ggResI_automizer_fix hxBs hLx (φ (Sum.inl i)) hmem
    have hfixlin : ggLin (p := 3) ι (φ (Sum.inl i)) xv = xv := by
      simpa [xv] using
        (ggLin_fix_iff (p := 3) ι (φ (Sum.inl i)) ⟨x, hxBs⟩).mp hfixφ
    exact e78_apply_eq_zero_of_fixed (p := 3) (hform (Sum.inl i)) hfixlin hh
  have hli : LinearIndependent (ZMod 3) (fun i : Λ => h (Sum.inl i)) := by
    by_contra hind
    exact (isUnit_iff_ne_zero.mp hunit)
      (l05nL3_det_cast_eq_zero (fun i : Λ => h (Sum.inl i))
        (fun i : Λ => α (Sum.inl i)) CL hpairL hind)
  let Sspan : Submodule (ZMod 3) V :=
    Submodule.span (ZMod 3) (Set.range fun i : Λ => h (Sum.inl i))
  have hcardΛ : Fintype.card Λ = n := by
    simpa using (Fintype.card_congr e).symm
  have hcardV : Nat.card V = 3 ^ (n + 1) := by
    calc
      Nat.card V = Nat.card (Additive ↥Bs) := (Nat.card_congr ι.toEquiv).symm
      _ = Nat.card ↥Bs := rfl
      _ = 3 ^ (n + 1) := hcardBs
  have hcardCompl : Nat.card V = 3 ^ (Fintype.card Λ + 1) := by
    simpa [hcardΛ] using hcardV
  have hSrank : Module.finrank (ZMod 3) Sspan = n := by
    dsimp [Sspan]
    rw [finrank_span_eq_card hli, hcardΛ]
  have hcompl := e78_span_isCompl_of_card_of_independent
    (p := 3) (V := V) (h := fun i : Λ => h (Sum.inl i))
    (α := fun i : Λ => α (Sum.inl i)) (C := CL) hli hunit hpairL hx0 hαx hcardCompl
  have hcomp : IsCompl Sspan (Submodule.span (ZMod 3) ({xv} : Set V)) :=
    ⟨disjoint_iff.mpr hcompl.1, codisjoint_iff.mpr hcompl.2⟩
  have hdimV : Module.finrank (ZMod 3) V = n + 1 := by
    haveI : Module.Finite (ZMod 3) V := Module.Finite.of_finite
    have h := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := V)
    rw [Nat.card_zmod, hcardV] at h
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ (3 : ℕ)) h).symm
  have hdim : Module.finrank (ZMod 3) V = Module.finrank (ZMod 3) Sspan + 1 := by
    rw [hdimV, hSrank]
  have h5 : 5 ≤ Module.finrank (ZMod 3) Sspan := by
    rw [hSrank]
    omega
  have hST : Sspan ≤ Submodule.span (ZMod 3) (Set.range h) := by
    dsimp [Sspan]
    exact Submodule.span_mono (by
      rintro _ ⟨i, rfl⟩
      exact ⟨Sum.inl i, rfl⟩)
  have hker : ∀ v : V, (∀ o : Λ ⊕ Λa, α o v = 0) →
      v ∈ Submodule.span (ZMod 3) ({xv} : Set V) := by
    intro v hv
    obtain ⟨s, y, hsy, -⟩ := Submodule.existsUnique_add_of_isCompl hcomp v
    have hyα : ∀ i : Λ, α (Sum.inl i) (y : V) = 0 := by
      intro i
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp y.2
      rw [← hc, map_smul, hαx i, smul_zero]
    have hsα : ∀ i : Λ, α (Sum.inl i) (s : V) = 0 := by
      intro i
      have h1 : α (Sum.inl i) ((s : V) + (y : V)) = 0 := by
        rw [hsy]
        exact hv (Sum.inl i)
      rw [map_add, hyα i, add_zero] at h1
      exact h1
    have hs0 : (s : V) = 0 :=
      e78_eq_zero_of_mem_span_of_cartan (p := 3)
        (h := fun i : Λ => h (Sum.inl i)) (α := fun i : Λ => α (Sum.inl i))
        (C := CL) hunit hpairL s.2 hsα
    rw [← hsy, hs0, zero_add]
    exact y.2
  let h7 : Fin n → V := fun i => h (Sum.inl (e i))
  let α7 : Fin n → Module.Dual (ZMod 3) V := fun i => α (Sum.inl (e i))
  let r7 : Fin n → V ≃ₗ[ZMod 3] V := fun i => r (Sum.inl (e i))
  have hform7 : ∀ i w, r7 i w = w - α7 i w • h7 i := fun i => hform (Sum.inl (e i))
  have hpair7 : ∀ i j : Fin n, α7 i (h7 j) = (C0 i j : ZMod 3) := by
    intro i j
    change α (Sum.inl (e i)) (h (Sum.inl (e j))) = _
    rw [hpairL, hstd]
  have hfix7 : ∀ i, r7 i xv = xv := by
    intro i
    have hmem : φ (Sum.inl (e i)) ∈ ggAutomizer L Bs := by
      rw [hgenL]
      exact Subgroup.subset_closure ⟨e i, rfl⟩
    have hfixφ := ggResI_automizer_fix hxBs hLx (φ (Sum.inl (e i))) hmem
    simpa [r7, xv] using
      (ggLin_fix_iff (p := 3) ι (φ (Sum.inl (e i))) ⟨x, hxBs⟩).mp hfixφ
  obtain ⟨z, hzclosure, hzneg7, hzx⟩ :=
    ggNegOneCheck_negates_span (p := 3) h7 α7 r7 C0 hform7 hpair7 hchk (x := xv) hfix7
  have hrange7 : Set.range h7 = Set.range (fun i : Λ => h (Sum.inl i)) := by
    ext v
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨e i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨e.symm i, by simp [h7]⟩
  have hzS : ∀ s ∈ Sspan, z s = -s := by
    intro s hs
    exact hzneg7 s (by simpa [Sspan, hrange7] using hs)
  have hzA : z ∈ A := by
    rw [hA]
    exact Subgroup.closure_mono (by
      rintro _ ⟨i, rfl⟩
      exact ⟨Sum.inl (e i), rfl⟩) hzclosure
  have hnt : ∀ g ∈ A, ¬ (Module.finrank (ZMod 3) (ggLinMove g) = 1 ∧
      ∀ w, g (g w - w) = g w - w) := by
    intro g hg hcond
    dsimp [A] at hg
    obtain ⟨ψ, hψA, rfl⟩ := Subgroup.mem_map.mp hg
    have hψtop : ψ ∈ ggAutomizer ⊤ Bs :=
      (sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top)) hψA
    have hψind : ψ ∈ ggInduced ⊤ Bs := by
      rw [ggAutomizer_eq] at hψtop
      exact hψtop
    exact hH.2.2.2.1 ψ hψind (ggRC_isTransvection_of_lin (p := 3) ι ψ hcond)
  have hTFtop : QTwoLin.TransvectionFree
      ((ggAutomizer ⊤ Bs).map (ggLin (p := 3) ι)) :=
    ggQ2P3P_transvectionFree (p := 3) ι hH.2.2.2.1
  have hAle : A ≤ (ggAutomizer ⊤ Bs).map (ggLin (p := 3) ι) := by
    dsimp [A]
    exact Subgroup.map_mono
      (sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top))
  have hTF : QTwoLin.TransvectionFree A := by
    intro g hg hgT
    exact hTFtop g (hAle hg) hgT
  have hSne : Nonempty {i : Λ // i ∉ S} := by
    have hlt : S.card < (Finset.univ : Finset Λ).card := by
      rw [Finset.card_univ, hcardΛ, hScard]
      omega
    obtain ⟨i, -, hi⟩ :=
      Finset.exists_mem_notMem_of_card_lt_card (s := S) (t := Finset.univ) hlt
    exact ⟨⟨i, hi⟩⟩
  have hntTransv : ∀ g ∈ A, ¬ CFSG.TwoNodeSmall.IsTransv g := by
    intro g hg hgT
    have hgT' : Module.finrank (ZMod 3) (ggLinMove g) = 1 ∧
        ∀ w, g (g w - w) = g w - w := by
      simpa [CFSG.TwoNodeSmall.IsTransv] using hgT
    exact hnt g hg hgT'
  have hconn : ∀ i j : Λ ⊕ Λa, Relation.ReflTransGen
      (fun a b => α a (h b) ≠ 0 ∧ α b (h a) ≠ 0) i j :=
    tenLinAux_join_connected_of_shared (V := V) S hSne hWML hCL hWMK hCK
      h α r A hα hform hA hntTransv hpairL hpairK
  have hcardA : Nat.card A =
      Nat.card ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
    dsimp [A]
    exact (Nat.card_congr
      (Subgroup.equivMapOfInjective (ggAutomizer L Bs ⊔ ggAutomizer K Bs)
        (ggLin (p := 3) ι) (ggLin_injective ι)).toEquiv).symm
  have hjoinCard := ggRC_card_join_le hOrb hH hxBs
  have hjoinCard' : Nat.card ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs) ≤
      3 ^ (n + 1) * ((3 - 1) * 6 * M) := by
    simpa [hcardBs, hALcard] using hjoinCard
  have hfull : 8 * Nat.card A < 3 ^
      ((Module.finrank (ZMod 3) Sspan + 1) * Module.finrank (ZMod 3) Sspan / 2) := by
    rw [hSrank]
    calc
      8 * Nat.card A = 8 * Nat.card ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
        rw [hcardA]
      _ ≤ 8 * (3 ^ (n + 1) * ((3 - 1) * 6 * M)) := Nat.mul_le_mul_left 8 hjoinCard'
      _ < 3 ^ ((n + 1) * n / 2) := hnumFull
  have hfix : (∀ g ∈ A, g xv = xv) → 8 * Nat.card A < 3 ^
      (Module.finrank (ZMod 3) Sspan * (Module.finrank (ZMod 3) Sspan - 1) / 2) := by
    intro hfixall
    have hstab : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤
        MulAction.stabilizer (MulAut ↥Bs) (⟨x, hxBs⟩ : ↥Bs) := by
      intro ψ hψ
      have hg : ggLin (p := 3) ι ψ ∈ A := by
        dsimp [A]
        exact Subgroup.mem_map.mpr ⟨ψ, hψ, rfl⟩
      have hfixv := hfixall (ggLin (p := 3) ι ψ) hg
      exact (ggLin_fix_iff (p := 3) ι ψ ⟨x, hxBs⟩).mpr (by simpa [xv] using hfixv)
    have hstabEq : (ggAutomizer L Bs ⊔ ggAutomizer K Bs) ⊓
        MulAction.stabilizer (MulAut ↥Bs) (⟨x, hxBs⟩ : ↥Bs) =
        ggAutomizer L Bs ⊔ ggAutomizer K Bs := inf_eq_left.mpr hstab
    have hstabCard : Nat.card ↥((ggAutomizer L Bs ⊔ ggAutomizer K Bs) ⊓
        MulAction.stabilizer (MulAut ↥Bs) (⟨x, hxBs⟩ : ↥Bs)) =
        Nat.card ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs) :=
      Nat.card_congr (MulEquiv.subgroupCongr hstabEq).toEquiv
    have hjoinFix : Nat.card ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs) ≤
        (3 - 1) * 6 * M := by
      have h := hOrb G 3 B Bs x L D J y K hH hxBs
      rw [hstabCard, hALcard] at h
      exact h
    rw [hSrank]
    calc
      8 * Nat.card A = 8 * Nat.card ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
        rw [hcardA]
      _ ≤ 8 * ((3 - 1) * 6 * M) := Nat.mul_le_mul_left 8 hjoinFix
      _ < 3 ^ (n * (n - 1) / 2) := hnumFix
  simpa [A] using
    ggTen_core_of_negated_complement hKG hKS h α hα r hform A hA hconn hnt hTF
      Sspan xv hcomp hST h5 hdim z hzA hzS hzx hker hfull hfix

theorem GGResHyp.weyl_of_exact2_e78_two
    (hOrb : GGResCentBoundInput) (hKG : GGReflClassLargeInput')
    (hKS : GGReflClassOmegaSmall)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hL : GGInnerDiagOnLabel (fun _ lab =>
      (lab.tag = .E7 ∨ lab.tag = .E8) ∧ lab.n = 1) 3 Bs L)
    (hD : GGResLeviDatumExact2 3 Bs L J K ggSelAny ggTypAny) :
    GGWeylReflectionGroup 3 (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Λ, instΛ, decΛ, S, Λa, instΛa, decΛa, ML, CL, MK, CK, V, instV, instMod, ι, φ, h, α,
    hScard, -, -, hWML, hCL, hWMK, hCK, -, hform, -, hpairL, hpairK, -, hfL, -, hgenL, hgenK,
    -, -⟩ := hD
  letI := instΛ
  letI := decΛ
  letI := instΛa
  letI := decΛa
  letI := instV
  letI := instMod
  have hLsplit : GGInnerDiagOnLabel
      (fun _ lab => (lab.tag = .E7 ∧ lab.n = 1) ∨ (lab.tag = .E8 ∧ lab.n = 1)) 3 Bs L :=
    hL.mono_label fun lab h =>
      h.1.elim (fun h7 => Or.inl ⟨h7, h.2⟩) (fun h8 => Or.inr ⟨h8, h.2⟩)
  rcases hLsplit.elim_or with hL7 | hL8
  · obtain ⟨fL, -⟩ := hfL
    obtain ⟨e, hM⟩ := hH.coxeter_e7_of_automizer hL7 hWML fL
    have hCL' : GGIntCartan (CoxeterMatrix.E₇.reindex e) CL := by
      rw [← hM]
      exact hCL
    have hstdInt : GGIntCartan (CoxeterMatrix.E₇.reindex e)
        (Matrix.reindex e e (CartanMatrix.E 7)) :=
      (ggIntCartan_E₇).reindex e
    have hone : GGAtMostOneMultipleEdge (CoxeterMatrix.E₇.reindex e) :=
      (ggAtMostOneMultipleEdge_E₇).reindex e
    have hstd : ∀ i j : Fin 7, CL (e i) (e j) = CartanMatrix.E 7 i j := by
      intro i j
      rcases hCL'.eq_or_eq_transpose hstdInt hone with heq | heq
      · rw [heq]
        simp [Matrix.reindex_apply]
      · rw [heq]
        simpa [Matrix.transpose_apply, Matrix.reindex_apply] using
          (CartanMatrix.E_isSymm 7).apply i j
    have hunit : IsUnit ((CL.det : ℤ) : ZMod 3) := by
      have hdet := e78_cartan_det_E7 e hM hCL
      rw [hdet]
      exact isUnit_iff_ne_zero.mpr (by
        intro hz
        have hdvd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp hz
        norm_num at hdvd)
    have hcardBs : Nat.card ↥Bs = 3 ^ (7 + 1) := by
      simpa using hH.card_bstar_of_e7_two hL7
    have hALcard : Nat.card ↥(ggAutomizer L Bs) = 2903040 := by
      simpa using hH.card_automizer_L_of_e7_two hL7
    have hnumFull : 8 * (3 ^ (7 + 1) * ((3 - 1) * 6 * 2903040)) <
        3 ^ ((7 + 1) * 7 / 2) := by norm_num
    have hnumFix : 8 * ((3 - 1) * 6 * 2903040) < 3 ^ (7 * (7 - 1) / 2) := by norm_num
    have hlin := e78_core_std hH hOrb hKG hKS hWML hCL hWMK hCK hform hpairL hpairK
      hgenL hgenK hScard (n := 7) (e := e) (C0 := CartanMatrix.E 7) (k := 9) (M := 2903040)
      ggNegOneCheck_E7 hstd hunit hcardBs hALcard (by norm_num) hnumFull hnumFix
    exact ggRC_weylReflGroup_of_linWeyl (p := 3) ι _ hlin
  · obtain ⟨fL, -⟩ := hfL
    obtain ⟨e, hM⟩ := hH.coxeter_e8_of_automizer hL8 hWML fL
    have hCL' : GGIntCartan (CoxeterMatrix.E₈.reindex e) CL := by
      rw [← hM]
      exact hCL
    have hstdInt : GGIntCartan (CoxeterMatrix.E₈.reindex e)
        (Matrix.reindex e e (CartanMatrix.E 8)) :=
      (ggIntCartan_E₈).reindex e
    have hone : GGAtMostOneMultipleEdge (CoxeterMatrix.E₈.reindex e) :=
      (ggAtMostOneMultipleEdge_E₈).reindex e
    have hstd : ∀ i j : Fin 8, CL (e i) (e j) = CartanMatrix.E 8 i j := by
      intro i j
      rcases hCL'.eq_or_eq_transpose hstdInt hone with heq | heq
      · rw [heq]
        simp [Matrix.reindex_apply]
      · rw [heq]
        simpa [Matrix.transpose_apply, Matrix.reindex_apply] using
          (CartanMatrix.E_isSymm 8).apply i j
    have hunit : IsUnit ((CL.det : ℤ) : ZMod 3) := by
      have hdet := e78_cartan_det_E8 e hM hCL
      rw [hdet]
      exact isUnit_iff_ne_zero.mpr (by
        intro hz
        have hdvd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp hz
        norm_num at hdvd)
    have hcardBs : Nat.card ↥Bs = 3 ^ (8 + 1) := by
      simpa using hH.card_bstar_of_e8_two hL8
    have hALcard : Nat.card ↥(ggAutomizer L Bs) = 696729600 := by
      simpa using hH.card_automizer_L_of_e8_two hL8
    have hnumFull : 8 * (3 ^ (8 + 1) * ((3 - 1) * 6 * 696729600)) <
        3 ^ ((8 + 1) * 8 / 2) := by norm_num
    have hnumFix : 8 * ((3 - 1) * 6 * 696729600) < 3 ^ (8 * (8 - 1) / 2) := by norm_num
    have hlin := e78_core_std hH hOrb hKG hKS hWML hCL hWMK hCK hform hpairL hpairK
      hgenL hgenK hScard (n := 8) (e := e) (C0 := CartanMatrix.E 8) (k := 15) (M := 696729600)
      ggNegOneCheck_E8 hstd hunit hcardBs hALcard (by norm_num) hnumFull hnumFix
    exact ggRC_weylReflGroup_of_linWeyl (p := 3) ι _ hlin

theorem ggResMultiNodeRestTwoCellInput_e78_qTwo_three :
    GGResMultiNodeRestTwoCellInput (fun p lab =>
      (lab.tag = .E7 ∨ lab.tag = .E8) ∧ p = 3 ∧ lab.n = 1) := by
  intro G _ _ p B Bs x L D J y K hH _ _ _ _ ⟨hD, _, _, hL, _⟩
  have hp : p = 3 := by
    obtain ⟨_, lab, _, hraw⟩ := hL
    obtain ⟨R, _, I, F, _, _, θ, hmark⟩ := largeEvenRawDatum_exists hraw
    exact hmark.1.2.1
  subst p
  have hmark : GGInnerDiagOnLabel
      (fun _ lab => (lab.tag = .E7 ∨ lab.tag = .E8) ∧ lab.n = 1) 3 Bs L :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ h => ⟨⟨h.1.1, h.1.2.2⟩, h.2⟩) hL
  have hUse : ZS.UseInput := ZS.useInput_holds
  exact hH.weyl_of_exact2_e78_two ggResCentBoundInput_holds
    (ggReflClassLargeInput_of_omega (ZS.ggReflClassOmegaLarge_of_useInput hUse))
    (ZS.ggReflClassOmegaSmall_of_useInput hUse) hmark hD

end CFSG.StandardType
