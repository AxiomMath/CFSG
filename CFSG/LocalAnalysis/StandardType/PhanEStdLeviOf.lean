module

public import CFSG.LocalAnalysis.StandardType.PhanEStdSetting
public import CFSG.LocalAnalysis.StandardType.PhanESLMatrix
public import CFSG.LocalAnalysis.StandardType.PhanEChevConj
public import CFSG.Timmesfeld.RankTwo.LevisExceptional
import CFSG.ClassicalInvolution.WeakCT.SimplyLaced
import CFSG.ClassicalInvolution.WeakCT.SpTorus
import CFSG.ClassicalInvolution.WeakCT.SpPair

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.Timmesfeld CFSG.Timmesfeld.LevisExtras
open scoped MatrixGroups

variable {K : Type} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K} {Fld : Type} [Field Fld] [CharP Fld 2]
  (M : ChevModel2 D n H Fld) {w₀ : (coxeterMatrix D.isFiniteType).Group}
  (F : FrobData D n H w₀)
  (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
    (weylAction D.isFiniteType) D.roots D.rootGroup n H)

private theorem q2nPE_sl2Upper_eq {l : SL(2, Fld) →* K} {x : Fld → K}
    (h : ∀ c, l (tv 0 1 c) = x c) (c : Fld) : l (sl2Upper c) = x c := by
  rw [← tv01_eq_sl2Upper, h c]

private theorem q2nPE_sl2Lower_eq {l : SL(2, Fld) →* K} {x : Fld → K}
    (h : ∀ c, l (tv 1 0 c) = x c) (c : Fld) : l (sl2Lower c) = x c := by
  rw [← tv10_eq_sl2Lower, h c]

@[expose] noncomputable def ChevModel2.stdLevi
    (hD : SimplyLacedLevis D Fld (edgeE D.rank) M.x) (θ : Fld →+* Fld)
    (hθ : ∀ c, θ (θ c) = c) (hnorm : ∀ s : Fld, s ≠ 0 → θ s = s → ∃ a : Fld, a * θ a = s)
    (hφ : ∀ i c, F.φ (M.x (Pi.single i 1) c) = M.x (Pi.single (F.op i) 1) (θ c))
    (hφ' : ∀ i c, F.φ (M.x (-Pi.single i 1) c) = M.x (-Pi.single (F.op i) 1) (θ c))
    (hopinv : ∀ i, F.op (F.op i) = i)
    (htab : ∀ i, weylAction D.isFiniteType w₀ (Pi.single i 1) = -Pi.single (F.op i) 1)
    (hedge : ∀ i j : Fin D.rank, i < j → coxeterMatrix D.isFiniteType i j = 3 →
      edgeE D.rank i j) :
    StdLevi F (nrep hct w₀) where
  Fld := Fld
  θ := θ
  θ_invol := hθ
  norm_surj := hnorm
  ε i := (hD.sl2 i).choose
  ε_inj i := (hD.sl2 i).choose_spec.1
  upper i := by
    show Set.range (fun c => (hD.sl2 i).choose (sl2Upper c)) =
      (D.rootGroup (Pi.single i 1) : Set K)
    have hl : ∀ c, (hD.sl2 i).choose (tv 0 1 c) = M.x (Pi.single i 1) c :=
      fun c => ((hD.sl2 i).choose_spec.2 c).1
    ext g
    constructor
    · rintro ⟨c, rfl⟩
      show (hD.sl2 i).choose (sl2Upper c) ∈ (D.rootGroup (Pi.single i 1) : Set K)
      rw [q2nPE_sl2Upper_eq (x := fun d => M.x (Pi.single i 1) d) hl c]
      exact hD.mem (Pi.single i 1) (single_mem_roots i) c
    · intro hg
      obtain ⟨c, hc⟩ := hD.surj (Pi.single i 1) (single_mem_roots i) g hg
      refine ⟨c, ?_⟩
      show (hD.sl2 i).choose (sl2Upper c) = g
      rw [q2nPE_sl2Upper_eq (x := fun d => M.x (Pi.single i 1) d) hl c, hc]
  lower i := by
    show Set.range (fun c => (hD.sl2 i).choose (sl2Lower c)) =
      (D.rootGroup (-Pi.single i 1) : Set K)
    have hl : ∀ c, (hD.sl2 i).choose (tv 1 0 c) = M.x (-Pi.single i 1) c :=
      fun c => ((hD.sl2 i).choose_spec.2 c).2
    ext g
    constructor
    · rintro ⟨c, rfl⟩
      show (hD.sl2 i).choose (sl2Lower c) ∈ (D.rootGroup (-Pi.single i 1) : Set K)
      rw [q2nPE_sl2Lower_eq (x := fun d => M.x (-Pi.single i 1) d) hl c]
      exact hD.mem (-Pi.single i 1) (neg_mem_roots (single_mem_roots i)) c
    · intro hg
      obtain ⟨c, hc⟩ := hD.surj (-Pi.single i 1) (neg_mem_roots (single_mem_roots i)) g hg
      refine ⟨c, ?_⟩
      show (hD.sl2 i).choose (sl2Lower c) = g
      rw [q2nPE_sl2Lower_eq (x := fun d => M.x (-Pi.single i 1) d) hl c, hc]
  diag i := by
    show Set.range (fun s : Fldˣ => (hD.sl2 i).choose (WeakCT.torusHom Fld s)) =
      (H i : Set K)
    have hl1 : ∀ c, (hD.sl2 i).choose (tv 0 1 c) = M.x (Pi.single i 1) c :=
      fun c => ((hD.sl2 i).choose_spec.2 c).1
    have hl2 : ∀ c, (hD.sl2 i).choose (tv 1 0 c) = M.x (-Pi.single i 1) c :=
      fun c => ((hD.sl2 i).choose_spec.2 c).2
    have hnin : (n i)⁻¹ = n i := (inv_eq_iff_mul_eq_one).mpr (M.nm_sq i)
    have hmem : ∀ s : Fldˣ, (hD.sl2 i).choose (WeakCT.torusHom Fld s) = M.hh i s := by
      intro s
      have hwt : (hD.sl2 i).choose
          (tv 0 1 (s : Fld) * tv 1 0 (-((s : Fld)⁻¹)) * tv 0 1 (s : Fld)) =
          M.x (Pi.single i 1) (s : Fld) * M.x (-Pi.single i 1) (-((s : Fld)⁻¹)) *
            M.x (Pi.single i 1) (s : Fld) := by
        rw [map_mul, map_mul, hl1 (s : Fld), hl2 (-((s : Fld)⁻¹))]
      have hw1 : (hD.sl2 i).choose
          (tv 0 1 (-1) * tv 1 0 1 * tv 0 1 (-1)) = n i := by
        rw [map_mul, map_mul, hl1 (-1), hl2 1]
        simpa only [CharTwo.neg_eq] using (M.nm_def i).symm
      rw [WeakCT.torusHom_eq_w s, map_mul, hwt, hw1, ← hnin]
      simpa only [Units.val_inv_eq_inv_val] using (M.hh_def i s).symm
    have hfun : (fun s : Fldˣ => (hD.sl2 i).choose (WeakCT.torusHom Fld s)) = M.hh i :=
      funext hmem
    rw [hfun]
    exact congrArg (fun S : Subgroup K => (S : Set K)) (M.hh_range i)
  weyl i := by
    show (hD.sl2 i).choose (sl2Upper 1 * sl2Lower (-1) * sl2Upper 1) = n i
    have hl1 : ∀ c, (hD.sl2 i).choose (tv 0 1 c) = M.x (Pi.single i 1) c :=
      fun c => ((hD.sl2 i).choose_spec.2 c).1
    have hl2 : ∀ c, (hD.sl2 i).choose (tv 1 0 c) = M.x (-Pi.single i 1) c :=
      fun c => ((hD.sl2 i).choose_spec.2 c).2
    rw [map_mul, map_mul, q2nPE_sl2Upper_eq (x := fun d => M.x (Pi.single i 1) d) hl1 1,
      q2nPE_sl2Lower_eq (x := fun d => M.x (-Pi.single i 1) d) hl2 (-1)]
    exact (M.nm_def i).symm
  phi_upper i c := by
    show F.φ ((hD.sl2 i).choose (sl2Upper c)) =
      (hD.sl2 (F.op i)).choose (sl2Upper (θ c))
    have hl1 : ∀ d, (hD.sl2 i).choose (tv 0 1 d) = M.x (Pi.single i 1) d :=
      fun d => ((hD.sl2 i).choose_spec.2 d).1
    have hl1' : ∀ d, (hD.sl2 (F.op i)).choose (tv 0 1 d) =
        M.x (Pi.single (F.op i) 1) d :=
      fun d => ((hD.sl2 (F.op i)).choose_spec.2 d).1
    rw [q2nPE_sl2Upper_eq (x := fun d => M.x (Pi.single i 1) d) hl1 c, hφ i c]
    exact (q2nPE_sl2Upper_eq (x := fun d => M.x (Pi.single (F.op i) 1) d) hl1' (θ c)).symm
  phi_lower i c := by
    show F.φ ((hD.sl2 i).choose (sl2Lower c)) =
      (hD.sl2 (F.op i)).choose (sl2Lower (θ c))
    have hl2 : ∀ d, (hD.sl2 i).choose (tv 1 0 d) = M.x (-Pi.single i 1) d :=
      fun d => ((hD.sl2 i).choose_spec.2 d).2
    have hl2' : ∀ d, (hD.sl2 (F.op i)).choose (tv 1 0 d) =
        M.x (-Pi.single (F.op i) 1) d :=
      fun d => ((hD.sl2 (F.op i)).choose_spec.2 d).2
    rw [q2nPE_sl2Lower_eq (x := fun d => M.x (-Pi.single i 1) d) hl2 c, hφ' i c]
    exact (q2nPE_sl2Lower_eq (x := fun d => M.x (-Pi.single (F.op i) 1) d) hl2' (θ c)).symm
  conj_upper i c := by
    show nrep hct w₀ * (hD.sl2 (F.op i)).choose (sl2Upper c) * (nrep hct w₀)⁻¹ =
      (hD.sl2 i).choose (sl2Lower (-c))
    have hl2 : ∀ d, (hD.sl2 i).choose (tv 1 0 d) = M.x (-Pi.single i 1) d :=
      fun d => ((hD.sl2 i).choose_spec.2 d).2
    have hl1' : ∀ d, (hD.sl2 (F.op i)).choose (tv 0 1 d) =
        M.x (Pi.single (F.op i) 1) d :=
      fun d => ((hD.sl2 (F.op i)).choose_spec.2 d).1
    have hweyl : weylAction D.isFiniteType w₀ (Pi.single (F.op i) 1) = -Pi.single i 1 := by
      rw [htab (F.op i), hopinv i]
    rw [q2nPE_sl2Upper_eq (x := fun d => M.x (Pi.single (F.op i) 1) d) hl1' c]
    rw [M.nrep_conj hct w₀ (single_mem_roots (F.op i)) c, hweyl]
    rw [q2nPE_sl2Lower_eq (x := fun d => M.x (-Pi.single i 1) d) hl2 (-c)]
    exact (congrArg (M.x (-Pi.single i 1)) (CharTwo.neg_eq c)).symm
  conj_lower i c := by
    show nrep hct w₀ * (hD.sl2 (F.op i)).choose (sl2Lower c) * (nrep hct w₀)⁻¹ =
      (hD.sl2 i).choose (sl2Upper (-c))
    have hl1 : ∀ d, (hD.sl2 i).choose (tv 0 1 d) = M.x (Pi.single i 1) d :=
      fun d => ((hD.sl2 i).choose_spec.2 d).1
    have hl2' : ∀ d, (hD.sl2 (F.op i)).choose (tv 1 0 d) =
        M.x (-Pi.single (F.op i) 1) d :=
      fun d => ((hD.sl2 (F.op i)).choose_spec.2 d).2
    have hweyl_pos : weylAction D.isFiniteType w₀ (Pi.single (F.op i) 1) = -Pi.single i 1 := by
      rw [htab (F.op i), hopinv i]
    have hweyl_neg : weylAction D.isFiniteType w₀ (-Pi.single (F.op i) 1) = Pi.single i 1 := by
      rw [map_neg, hweyl_pos, neg_neg]
    rw [q2nPE_sl2Lower_eq (x := fun d => M.x (-Pi.single (F.op i) 1) d) hl2' c]
    rw [M.nrep_conj hct w₀ (neg_mem_roots (single_mem_roots (F.op i))) c, hweyl_neg]
    rw [q2nPE_sl2Upper_eq (x := fun d => M.x (Pi.single i 1) d) hl1 (-c)]
    exact (congrArg (M.x (Pi.single i 1)) (CharTwo.neg_eq c)).symm
  ε₂ i j := if h : edgeE D.rank i j then (hD.sl3 i j h).choose else 1
  ε₂_inj i j hij hm := by
    rw [dif_pos (hedge i j hij hm)]
    exact (hD.sl3 i j (hedge i j hij hm)).choose_spec.1
  ε₂_left i j hij hm := by
    show (if h : edgeE D.rank i j then (hD.sl3 i j h).choose else 1).comp
        (WeakCT.blk Fld 0) = (hD.sl2 i).choose
    have he := hedge i j hij hm
    have hl1 : ∀ c, (hD.sl3 i j he).choose (tv 0 1 c) = M.x (Pi.single i 1) c :=
      fun c => ((hD.sl3 i j he).choose_spec.2 c).1
    have hl2 : ∀ c, (hD.sl3 i j he).choose (tv 1 0 c) = M.x (-Pi.single i 1) c :=
      fun c => ((hD.sl3 i j he).choose_spec.2 c).2.1
    have hl1' : ∀ c, (hD.sl2 i).choose (tv 0 1 c) = M.x (Pi.single i 1) c :=
      fun c => ((hD.sl2 i).choose_spec.2 c).1
    have hl2' : ∀ c, (hD.sl2 i).choose (tv 1 0 c) = M.x (-Pi.single i 1) c :=
      fun c => ((hD.sl2 i).choose_spec.2 c).2
    rw [dif_pos he]
    refine sl2_hom_ext (fun c => ?_) (fun c => ?_)
    · rw [MonoidHom.comp_apply]
      rw [show (WeakCT.blk Fld 0) (sl2Upper c) = tv 0 1 c by
        rw [← tv01_eq_sl2Upper, WeakCT.blk_zero_tv01]]
      rw [hl1 c, q2nPE_sl2Upper_eq (x := fun d => M.x (Pi.single i 1) d) hl1' c]
    · rw [MonoidHom.comp_apply]
      rw [show (WeakCT.blk Fld 0) (sl2Lower c) = tv 1 0 c by
        rw [← tv10_eq_sl2Lower, WeakCT.blk_zero_tv10]]
      rw [hl2 c, q2nPE_sl2Lower_eq (x := fun d => M.x (-Pi.single i 1) d) hl2' c]
  ε₂_right i j hij hm := by
    show (if h : edgeE D.rank i j then (hD.sl3 i j h).choose else 1).comp
        (WeakCT.blk Fld 1) = (hD.sl2 j).choose
    have he := hedge i j hij hm
    have hl1 : ∀ c, (hD.sl3 i j he).choose (tv 1 2 c) = M.x (Pi.single j 1) c :=
      fun c => ((hD.sl3 i j he).choose_spec.2 c).2.2.1
    have hl2 : ∀ c, (hD.sl3 i j he).choose (tv 2 1 c) = M.x (-Pi.single j 1) c :=
      fun c => ((hD.sl3 i j he).choose_spec.2 c).2.2.2.1
    have hl1' : ∀ c, (hD.sl2 j).choose (tv 0 1 c) = M.x (Pi.single j 1) c :=
      fun c => ((hD.sl2 j).choose_spec.2 c).1
    have hl2' : ∀ c, (hD.sl2 j).choose (tv 1 0 c) = M.x (-Pi.single j 1) c :=
      fun c => ((hD.sl2 j).choose_spec.2 c).2
    rw [dif_pos he]
    refine sl2_hom_ext (fun c => ?_) (fun c => ?_)
    · rw [MonoidHom.comp_apply]
      rw [show (WeakCT.blk Fld 1) (sl2Upper c) = tv 1 2 c by
        rw [← tv01_eq_sl2Upper, WeakCT.blk_one_tv01]]
      rw [hl1 c, q2nPE_sl2Upper_eq (x := fun d => M.x (Pi.single j 1) d) hl1' c]
    · rw [MonoidHom.comp_apply]
      rw [show (WeakCT.blk Fld 1) (sl2Lower c) = tv 2 1 c by
        rw [← tv10_eq_sl2Lower, WeakCT.blk_one_tv10]]
      rw [hl2 c, q2nPE_sl2Lower_eq (x := fun d => M.x (-Pi.single j 1) d) hl2' c]

end CFSG.ClassicalInvolution.Phan.PhanE
