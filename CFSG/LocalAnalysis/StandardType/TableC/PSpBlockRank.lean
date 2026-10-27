module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockDegreeParity
public import CFSG.LocalAnalysis.StandardType.TableC.GramBlockRank
public import CFSG.Open.StatedDefs
public import CFSG.Open.StatedAPI
public import CFSG.Assembly.Defs
public import Mathlib.LinearAlgebra.Matrix.Rank

public section

namespace CFSG.StandardType.TableC

open CFSG.Assembly
open CFSG.Open (StatedSp)
open CFSG.StandardType.ClassicalPosition

private lemma pbr_adjoin_comm {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {S : Set (GL ι F)} (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') :
    ∀ a ∈ Algebra.adjoin F (Units.val '' S), ∀ b ∈ Algebra.adjoin F (Units.val '' S),
      a * b = b * a := by
  have hcommS : (Units.val '' S : Set (Matrix ι ι F)).Pairwise Commute := by
    rintro a ⟨s, hs, rfl⟩ b ⟨s', hs', rfl⟩ _
    show (s : Matrix ι ι F) * (s' : Matrix ι ι F) = (s' : Matrix ι ι F) * (s : Matrix ι ι F)
    rw [← Units.val_mul, ← Units.val_mul]
    exact congrArg Units.val (hS s hs s' hs').eq
  letI : CommSemiring (Algebra.adjoin F (Units.val '' S)) :=
    Algebra.adjoinCommSemiringOfComm F hcommS
  intro a ha b hb
  have h := mul_comm (⟨a, ha⟩ : Algebra.adjoin F (Units.val '' S))
    (⟨b, hb⟩ : Algebra.adjoin F (Units.val '' S))
  simpa only [Subalgebra.coe_mul] using congrArg Subtype.val h

private lemma pbr_commute_adjoin {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {S : Set (GL ι F)} {g : Matrix ι ι F}
    (hg : ∀ s ∈ S, g * (s : Matrix ι ι F) = (s : Matrix ι ι F) * g) :
    ∀ a ∈ Algebra.adjoin F (Units.val '' S), g * a = a * g := by
  intro a ha
  refine Algebra.adjoin_induction (p := fun x _ => g * x = x * g) ?_ ?_ ?_ ?_ ha
  · rintro x ⟨s, hs, rfl⟩
    exact hg s hs
  · intro r
    rw [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.smul_mul, mul_one, one_mul]
  · intro x y _ _ hx hy
    rw [mul_add, add_mul, hx, hy]
  · intro x y _ _ hx hy
    rw [← mul_assoc, hx, mul_assoc, hy, ← mul_assoc]

private noncomputable def pbr_mulRight {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (A : Subalgebra F (Matrix ι ι F)) (e : Matrix ι ι F) : A →ₗ[F] Matrix ι ι F where
  toFun a := (a : Matrix ι ι F) * e
  map_add' a b := by
    change ((a : Matrix ι ι F) + (b : Matrix ι ι F)) * e =
      (a : Matrix ι ι F) * e + (b : Matrix ι ι F) * e
    rw [Matrix.add_mul]
  map_smul' c a := by
    change (c • (a : Matrix ι ι F)) * e = c • ((a : Matrix ι ι F) * e)
    rw [Matrix.smul_mul]

private noncomputable def pbr_mulVecMap {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (A : Subalgebra F (Matrix ι ι F)) (w : ι → F) : A →ₗ[F] (ι → F) where
  toFun a := (a : Matrix ι ι F).mulVec w
  map_add' a b := by
    change ((a : Matrix ι ι F) + (b : Matrix ι ι F)).mulVec w =
      (a : Matrix ι ι F).mulVec w + (b : Matrix ι ι F).mulVec w
    rw [Matrix.add_mulVec]
  map_smul' c a := by
    change (c • (a : Matrix ι ι F)).mulVec w = c • ((a : Matrix ι ι F).mulVec w)
    rw [Matrix.smul_mulVec]

private lemma pbr_range_mulRight {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (A : Subalgebra F (Matrix ι ι F)) (e : Matrix ι ι F) :
    (Subalgebra.toSubmodule A).map (LinearMap.mulRight F e) =
      LinearMap.range (pbr_mulRight A e) := by
  ext x
  rw [Submodule.mem_map, LinearMap.mem_range]
  constructor
  · rintro ⟨a, ha, hx⟩
    exact ⟨⟨a, ha⟩, by simpa [pbr_mulRight, LinearMap.mulRight_apply] using hx⟩
  · rintro ⟨a, hx⟩
    exact ⟨a, a.2, by simpa [pbr_mulRight, LinearMap.mulRight_apply] using hx⟩

private lemma pbr_blockDegree_eq_finrank_range {ι F : Type} [Fintype ι] [DecidableEq ι]
    [Field F] (A : Subalgebra F (Matrix ι ι F)) (e : Matrix ι ι F) :
    blockDegree A e = Module.finrank F (LinearMap.range (pbr_mulRight A e)) := by
  unfold blockDegree
  rw [pbr_range_mulRight]

private lemma pbr_exists_mul_sub_one {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    [Finite F] [CharP F 2] {S : Set (GL ι F)}
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix ι ι F} (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e)
    {a : Matrix ι ι F} (ha : a ∈ Algebra.adjoin F (Units.val '' S)) (hae : a * e ≠ 0) :
    ∃ b ∈ Algebra.adjoin F (Units.val '' S), (b * a - 1) * e = 0 := by
  classical
  obtain ⟨K, hKfield, hKalg, hKfin, π, _hπsurj, hπker, _⟩ := exists_blockField hS hodd he
  letI : Field K := hKfield
  letI : Algebra F K := hKalg
  letI : Finite K := hKfin
  have hπa : π ⟨a, ha⟩ ≠ 0 := fun h0 => hae ((hπker ⟨a, ha⟩).mp h0)
  obtain ⟨bA, hbA⟩ := _hπsurj ((π ⟨a, ha⟩)⁻¹)
  have hmem : (bA : Matrix ι ι F) * a - 1 ∈ Algebra.adjoin F (Units.val '' S) :=
    Subalgebra.sub_mem _ (Subalgebra.mul_mem _ bA.2 ha) (Subalgebra.one_mem _)
  have heq : (⟨(bA : Matrix ι ι F) * a - 1, hmem⟩ : Algebra.adjoin F (Units.val '' S)) =
      (⟨bA, bA.2⟩ : Algebra.adjoin F (Units.val '' S)) * ⟨a, ha⟩ - 1 :=
    Subtype.ext rfl
  have hπ0 : π ⟨(bA : Matrix ι ι F) * a - 1, hmem⟩ = 0 := by
    rw [heq, map_sub, map_mul, hbA, map_one]
    rw [inv_mul_cancel₀ hπa, sub_self]
  refine ⟨(bA : Matrix ι ι F), bA.2, ?_⟩
  exact (hπker ⟨(bA : Matrix ι ι F) * a - 1, hmem⟩).mp hπ0

private lemma pbr_not_isQuasisimple_bot {M : Type} [Group M] :
    ¬ IsQuasisimple (⊥ : Subgroup M) := by
  rintro ⟨-, hsimple⟩
  haveI : Subsingleton (↥(⊥ : Subgroup M)) :=
    ⟨fun a b => Subtype.ext (by
      rw [Subgroup.mem_bot.mp a.2, Subgroup.mem_bot.mp b.2])⟩
  have hcenter : Subgroup.center (↥(⊥ : Subgroup M)) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [Subgroup.mem_center_iff]
    exact fun g => Subsingleton.elim (g * x) (x * g)
  haveI : Subsingleton (↥(⊥ : Subgroup M) ⧸ Subgroup.center (↥(⊥ : Subgroup M))) :=
    QuotientGroup.subsingleton_iff.mpr hcenter
  obtain ⟨x, y, hxy⟩ := hsimple.toNontrivial.exists_pair_ne
  exact hxy (Subsingleton.elim x y)

private lemma pbr_range_le {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {S : Set (GL ι F)} (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') {e : Matrix ι ι F}
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e)
    {w : ι → F} (hw : w ∈ LinearMap.range e.mulVecLin) :
    LinearMap.range (pbr_mulVecMap (Algebra.adjoin F (Units.val '' S)) w) ≤
      LinearMap.range e.mulVecLin := by
  rintro x ⟨a, rfl⟩
  obtain ⟨v, hv⟩ := hw
  have hv' : e.mulVec v = w := by simpa [Matrix.mulVecLin_apply] using hv
  have hcomm : (a : Matrix ι ι F) * e = e * (a : Matrix ι ι F) :=
    pbr_adjoin_comm hS (a : Matrix ι ι F) a.2 e he.1
  refine LinearMap.mem_range.mpr ⟨(a : Matrix ι ι F).mulVec v, ?_⟩
  calc e.mulVec ((a : Matrix ι ι F).mulVec v)
      = (e * (a : Matrix ι ι F)).mulVec v := by rw [Matrix.mulVec_mulVec]
    _ = ((a : Matrix ι ι F) * e).mulVec v := by rw [hcomm]
    _ = (a : Matrix ι ι F).mulVec (e.mulVec v) := by rw [Matrix.mulVec_mulVec]
    _ = (a : Matrix ι ι F).mulVec w := by rw [hv']

private lemma pbr_ker_eq {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] [Finite F]
    [CharP F 2] {S : Set (GL ι F)} (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s)) {e : Matrix ι ι F}
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e)
    {w : ι → F} (hw : w ∈ LinearMap.range e.mulVecLin) (hw0 : w ≠ 0) :
    LinearMap.ker (pbr_mulVecMap (Algebra.adjoin F (Units.val '' S)) w) =
      LinearMap.ker (pbr_mulRight (Algebra.adjoin F (Units.val '' S)) e) := by
  ext a
  rw [LinearMap.mem_ker, LinearMap.mem_ker]
  constructor
  · intro h
    have ha0 : (a : Matrix ι ι F).mulVec w = 0 := h
    by_contra hne
    obtain ⟨b, _hb, hbae⟩ := pbr_exists_mul_sub_one hS hodd he a.2 hne
    obtain ⟨v, hv⟩ := hw
    have hv' : e.mulVec v = w := by simpa [Matrix.mulVecLin_apply] using hv
    have hw' : e.mulVec w = w := by
      rw [← hv', Matrix.mulVec_mulVec, he.2.1.eq]
    have hbae' : (b * (a : Matrix ι ι F)) * e = e := by
      have hh : (b * (a : Matrix ι ι F)) * e - e = 0 := by
        simpa [Matrix.sub_mul] using hbae
      exact sub_eq_zero.mp hh
    have hzero : w = 0 := by
      calc w = e.mulVec w := hw'.symm
        _ = ((b * (a : Matrix ι ι F)) * e).mulVec w := by rw [hbae']
        _ = (b * (a : Matrix ι ι F)).mulVec (e.mulVec w) := by rw [Matrix.mulVec_mulVec]
        _ = (b * (a : Matrix ι ι F)).mulVec w := by rw [hw']
        _ = b.mulVec ((a : Matrix ι ι F).mulVec w) := by rw [Matrix.mulVec_mulVec]
        _ = 0 := by rw [ha0]; simp
    exact hw0 hzero
  · intro h
    have hae0 : (a : Matrix ι ι F) * e = 0 := h
    obtain ⟨v, hv⟩ := hw
    have hv' : e.mulVec v = w := by simpa [Matrix.mulVecLin_apply] using hv
    have hw' : e.mulVec w = w := by
      rw [← hv', Matrix.mulVec_mulVec, he.2.1.eq]
    calc (a : Matrix ι ι F).mulVec w
        = (a : Matrix ι ι F).mulVec (e.mulVec w) := by rw [hw']
      _ = ((a : Matrix ι ι F) * e).mulVec w := by rw [Matrix.mulVec_mulVec]
      _ = 0 := by rw [hae0]; simp

private lemma pbr_finrank_range {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] [Finite F]
    [CharP F 2] {S : Set (GL ι F)} (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s)) {e : Matrix ι ι F}
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e)
    {w : ι → F} (hw : w ∈ LinearMap.range e.mulVecLin) (hw0 : w ≠ 0) :
    Module.finrank F
        (LinearMap.range (pbr_mulVecMap (Algebra.adjoin F (Units.val '' S)) w)) =
      blockDegree (Algebra.adjoin F (Units.val '' S)) e := by
  have hker := pbr_ker_eq hS hodd he hw hw0
  have h1 := LinearMap.finrank_range_add_finrank_ker
    (pbr_mulVecMap (Algebra.adjoin F (Units.val '' S)) w)
  have h2 := LinearMap.finrank_range_add_finrank_ker
    (pbr_mulRight (Algebra.adjoin F (Units.val '' S)) e)
  rw [hker] at h1
  have hEq : Module.finrank F
        (LinearMap.range (pbr_mulVecMap (Algebra.adjoin F (Units.val '' S)) w)) =
      Module.finrank F
        (LinearMap.range (pbr_mulRight (Algebra.adjoin F (Units.val '' S)) e)) := by
    omega
  rwa [← pbr_blockDegree_eq_finrank_range] at hEq

private lemma pbr_range_eq_of_lt_of_ne {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    [Finite F] [CharP F 2] {S : Set (GL ι F)} (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s)) {e : Matrix ι ι F}
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e)
    (hlt : Matrix.rank e < 2 * blockDegree (Algebra.adjoin F (Units.val '' S)) e)
    {w : ι → F} (hw : w ∈ LinearMap.range e.mulVecLin) (hw0 : w ≠ 0) :
    LinearMap.range (pbr_mulVecMap (Algebra.adjoin F (Units.val '' S)) w) =
      LinearMap.range e.mulVecLin := by
  have hlt' : Module.finrank F (LinearMap.range e.mulVecLin) <
      2 * blockDegree (Algebra.adjoin F (Units.val '' S)) e := hlt
  by_contra hne
  have hle : LinearMap.range (pbr_mulVecMap (Algebra.adjoin F (Units.val '' S)) w) ≤
      LinearMap.range e.mulVecLin := pbr_range_le hS he hw
  have hlt_sub : LinearMap.range (pbr_mulVecMap (Algebra.adjoin F (Units.val '' S)) w) <
      LinearMap.range e.mulVecLin := lt_of_le_of_ne hle hne
  obtain ⟨w', hw'mem, hw'not⟩ : ∃ w' ∈ LinearMap.range e.mulVecLin,
      w' ∉ LinearMap.range (pbr_mulVecMap (Algebra.adjoin F (Units.val '' S)) w) := by
    by_contra h
    push Not at h
    exact hne (le_antisymm hle h)
  have hw'0 : w' ≠ 0 := fun h0 => hw'not (by rw [h0]; exact Submodule.zero_mem _)
  have hdisj : LinearMap.range (pbr_mulVecMap (Algebra.adjoin F (Units.val '' S)) w) ⊓
      LinearMap.range (pbr_mulVecMap (Algebra.adjoin F (Units.val '' S)) w') = ⊥ := by
    apply le_antisymm
    · rintro u ⟨hu, hu'⟩
      rw [Submodule.mem_bot]
      by_contra hu0
      have huWe : u ∈ LinearMap.range e.mulVecLin := hle hu
      have hleu : LinearMap.range (pbr_mulVecMap (Algebra.adjoin F (Units.val '' S)) u) ≤
          LinearMap.range (pbr_mulVecMap (Algebra.adjoin F (Units.val '' S)) w) := by
        rintro x ⟨c, rfl⟩
        obtain ⟨a1, ha1⟩ := hu
        have ha1' : (a1 : Matrix ι ι F).mulVec w = u := ha1
        refine ⟨c * a1, ?_⟩
        change ((c * a1 : Algebra.adjoin F (Units.val '' S)) : Matrix ι ι F).mulVec w =
          (c : Matrix ι ι F).mulVec u
        rw [← ha1', Subalgebra.coe_mul, ← Matrix.mulVec_mulVec]
      have hleu' : LinearMap.range (pbr_mulVecMap (Algebra.adjoin F (Units.val '' S)) u) ≤
          LinearMap.range (pbr_mulVecMap (Algebra.adjoin F (Units.val '' S)) w') := by
        rintro x ⟨c, rfl⟩
        obtain ⟨a1, ha1⟩ := hu'
        have ha1' : (a1 : Matrix ι ι F).mulVec w' = u := ha1
        refine ⟨c * a1, ?_⟩
        change ((c * a1 : Algebra.adjoin F (Units.val '' S)) : Matrix ι ι F).mulVec w' =
          (c : Matrix ι ι F).mulVec u
        rw [← ha1', Subalgebra.coe_mul, ← Matrix.mulVec_mulVec]
      have heq_u : LinearMap.range (pbr_mulVecMap (Algebra.adjoin F (Units.val '' S)) u) =
          LinearMap.range (pbr_mulVecMap (Algebra.adjoin F (Units.val '' S)) w) :=
        Submodule.eq_of_le_of_finrank_eq hleu (by
          rw [pbr_finrank_range hS hodd he huWe hu0,
            pbr_finrank_range hS hodd he hw hw0])
      have heq_u' : LinearMap.range (pbr_mulVecMap (Algebra.adjoin F (Units.val '' S)) u) =
          LinearMap.range (pbr_mulVecMap (Algebra.adjoin F (Units.val '' S)) w') :=
        Submodule.eq_of_le_of_finrank_eq hleu' (by
          rw [pbr_finrank_range hS hodd he huWe hu0,
            pbr_finrank_range hS hodd he hw'mem hw'0])
      have hw'in : w' ∈
          LinearMap.range (pbr_mulVecMap (Algebra.adjoin F (Units.val '' S)) w') :=
        ⟨1, by simp [pbr_mulVecMap]⟩
      exact hw'not ((heq_u.symm.trans heq_u') ▸ hw'in)
    · exact bot_le
  have hsup : Module.finrank F
        ↥(LinearMap.range (pbr_mulVecMap (Algebra.adjoin F (Units.val '' S)) w) ⊔
          LinearMap.range (pbr_mulVecMap (Algebra.adjoin F (Units.val '' S)) w')) =
      2 * blockDegree (Algebra.adjoin F (Units.val '' S)) e := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq
      (LinearMap.range (pbr_mulVecMap (Algebra.adjoin F (Units.val '' S)) w))
      (LinearMap.range (pbr_mulVecMap (Algebra.adjoin F (Units.val '' S)) w'))
    rw [hdisj] at h
    simp only [finrank_bot, add_zero] at h
    rw [h, pbr_finrank_range hS hodd he hw hw0,
      pbr_finrank_range hS hodd he hw'mem hw'0]
    ring
  have hsup_le : LinearMap.range (pbr_mulVecMap (Algebra.adjoin F (Units.val '' S)) w) ⊔
      LinearMap.range (pbr_mulVecMap (Algebra.adjoin F (Units.val '' S)) w') ≤
      LinearMap.range e.mulVecLin :=
    sup_le (pbr_range_le hS he hw) (pbr_range_le hS he hw'mem)
  have hfin_le : Module.finrank F
        ↥(LinearMap.range (pbr_mulVecMap (Algebra.adjoin F (Units.val '' S)) w) ⊔
          LinearMap.range (pbr_mulVecMap (Algebra.adjoin F (Units.val '' S)) w')) ≤
      Module.finrank F (LinearMap.range e.mulVecLin) :=
    Submodule.finrank_mono hsup_le
  rw [hsup] at hfin_le
  omega

private lemma pbr_thin_of_lt {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] [Finite F]
    [CharP F 2] {S : Set (GL ι F)} (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s)) {e : Matrix ι ι F}
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e)
    (hlt : Matrix.rank e < 2 * blockDegree (Algebra.adjoin F (Units.val '' S)) e) :
    Matrix.rank e = blockDegree (Algebra.adjoin F (Units.val '' S)) e := by
  have hWe_ne : LinearMap.range e.mulVecLin ≠ ⊥ := by
    intro hbot
    have hfun : e.mulVec = (0 : Matrix ι ι F).mulVec := by
      funext v
      have hv : e.mulVec v ∈ LinearMap.range e.mulVecLin :=
        LinearMap.mem_range.mpr ⟨v, by rw [Matrix.mulVecLin_apply]⟩
      rw [hbot] at hv
      simpa using hv
    exact he.2.2.1 (Matrix.mulVec_injective hfun)
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWe_ne
  have hWeq := pbr_range_eq_of_lt_of_ne hS hodd he hlt hw hw0
  have hd := pbr_finrank_range hS hodd he hw hw0
  rw [hWeq] at hd
  exact hd

private lemma pbr_thin_action {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] [Finite F]
    [CharP F 2] {S : Set (GL ι F)} (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s)) {e : Matrix ι ι F}
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e)
    (hthin : Matrix.rank e = blockDegree (Algebra.adjoin F (Units.val '' S)) e)
    {g : Matrix ι ι F}
    (hg : ∀ a ∈ Algebra.adjoin F (Units.val '' S), g * a = a * g) :
    ∃ a ∈ Algebra.adjoin F (Units.val '' S), g * e = a * e := by
  have hthin' : Module.finrank F (LinearMap.range e.mulVecLin) =
      blockDegree (Algebra.adjoin F (Units.val '' S)) e := hthin
  have hWe_ne : LinearMap.range e.mulVecLin ≠ ⊥ := by
    intro hbot
    have hfun : e.mulVec = (0 : Matrix ι ι F).mulVec := by
      funext v
      have hv : e.mulVec v ∈ LinearMap.range e.mulVecLin :=
        LinearMap.mem_range.mpr ⟨v, by rw [Matrix.mulVecLin_apply]⟩
      rw [hbot] at hv
      simpa using hv
    exact he.2.2.1 (Matrix.mulVec_injective hfun)
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWe_ne
  have hrange : LinearMap.range (pbr_mulVecMap (Algebra.adjoin F (Units.val '' S)) w) =
      LinearMap.range e.mulVecLin :=
    Submodule.eq_of_le_of_finrank_eq (pbr_range_le hS he hw) (by
      rw [pbr_finrank_range hS hodd he hw hw0, hthin'])
  have hgw : g.mulVec w ∈ LinearMap.range e.mulVecLin := by
    obtain ⟨v, hv⟩ := hw
    have hv' : e.mulVec v = w := by simpa [Matrix.mulVecLin_apply] using hv
    refine LinearMap.mem_range.mpr ⟨g.mulVec v, ?_⟩
    change e.mulVec (g.mulVec v) = g.mulVec w
    rw [Matrix.mulVec_mulVec, ← hv', Matrix.mulVec_mulVec, ← hg e he.1]
  have hmem : g.mulVec w ∈
      LinearMap.range (pbr_mulVecMap (Algebra.adjoin F (Units.val '' S)) w) := by
    rw [hrange]; exact hgw
  obtain ⟨a, ha⟩ := hmem
  have ha' : (a : Matrix ι ι F).mulVec w = g.mulVec w := ha
  refine ⟨(a : Matrix ι ι F), a.2, ?_⟩
  apply Matrix.mulVec_injective
  funext x
  have hx : e.mulVec x ∈
      LinearMap.range (pbr_mulVecMap (Algebra.adjoin F (Units.val '' S)) w) := by
    rw [hrange]
    exact LinearMap.mem_range.mpr ⟨x, by rw [Matrix.mulVecLin_apply]⟩
  obtain ⟨c, hc⟩ := hx
  have hc' : (c : Matrix ι ι F).mulVec w = e.mulVec x := hc
  calc (g * e).mulVec x = g.mulVec (e.mulVec x) := by rw [Matrix.mulVec_mulVec]
    _ = g.mulVec ((c : Matrix ι ι F).mulVec w) := by rw [← hc']
    _ = (g * (c : Matrix ι ι F)).mulVec w := by rw [Matrix.mulVec_mulVec]
    _ = ((c : Matrix ι ι F) * g).mulVec w := by rw [hg (c : Matrix ι ι F) c.2]
    _ = (c : Matrix ι ι F).mulVec (g.mulVec w) := by rw [Matrix.mulVec_mulVec]
    _ = (c : Matrix ι ι F).mulVec ((a : Matrix ι ι F).mulVec w) := by rw [← ha']
    _ = ((c : Matrix ι ι F) * (a : Matrix ι ι F)).mulVec w := by
          rw [← Matrix.mulVec_mulVec]
    _ = ((a : Matrix ι ι F) * (c : Matrix ι ι F)).mulVec w := by
          rw [pbr_adjoin_comm hS (a : Matrix ι ι F) a.2 (c : Matrix ι ι F) c.2]
    _ = (a : Matrix ι ι F).mulVec ((c : Matrix ι ι F).mulVec w) := by
          rw [← Matrix.mulVec_mulVec]
    _ = (a : Matrix ι ι F).mulVec (e.mulVec x) := by rw [hc']
    _ = (a * e).mulVec x := by rw [← Matrix.mulVec_mulVec]

private lemma pbr_neg_one_matrix_eq_one {ι F : Type} [DecidableEq ι] [Field F] [CharP F 2] :
    (-1 : Matrix ι ι F) = 1 := by
  ext i j
  rw [Matrix.neg_apply, CharTwo.neg_eq]

private abbrev pbr_J (n : ℕ) (F : Type) [Field F] :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F :=
  Matrix.fromBlocks 0 1 (-1) 0

private lemma pbr_J_transpose (n : ℕ) (F : Type) [Field F] [CharP F 2] :
    Matrix.transpose (pbr_J n F) = pbr_J n F := by
  rw [pbr_J, Matrix.fromBlocks_transpose]
  simp only [Matrix.transpose_zero, Matrix.transpose_one, pbr_neg_one_matrix_eq_one]

private lemma pbr_J_mul_self (n : ℕ) (F : Type) [Field F] [CharP F 2] :
    pbr_J n F * pbr_J n F = 1 := by
  rw [pbr_J, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.one_mul, Matrix.zero_mul, zero_add,
    add_zero, Matrix.mul_neg, neg_zero]
  rw [pbr_neg_one_matrix_eq_one, Matrix.fromBlocks_one]

private lemma pbr_J_det (n : ℕ) (F : Type) [Field F] [CharP F 2] :
    IsUnit (pbr_J n F).det :=
  Matrix.isUnit_det_of_right_inverse (pbr_J_mul_self n F)

private noncomputable def pbr_formAdjEquiv {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {G : Matrix ι ι F} (hG : IsUnit G.det)
    (hGh : Matrix.transpose (G.map (RingHom.id F)) = G) :
    Matrix ι ι F ≃ₗ[F] Matrix ι ι F where
  toFun := formAdj (RingHom.id F) G
  invFun := formAdj (RingHom.id F) G
  map_add' a b := Geo.formAdj_add (RingHom.id F) G a b
  map_smul' c a := by
    rw [Geo.formAdj_smul]
  left_inv a := Geo.formAdj_formAdj (RingHom.id F) (fun x => rfl) hG hGh a
  right_inv a := Geo.formAdj_formAdj (RingHom.id F) (fun x => rfl) hG hGh a

private lemma pbr_rank_formAdj_id {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {G M : Matrix ι ι F} (hG : IsUnit G.det) :
    Matrix.rank (formAdj (RingHom.id F) G M) = Matrix.rank M := by
  have h1 : Matrix.rank (G⁻¹ * Matrix.transpose M * G) =
      Matrix.rank (G⁻¹ * Matrix.transpose M) :=
    Matrix.rank_mul_eq_left_of_isUnit_det G (G⁻¹ * Matrix.transpose M) hG
  have h2 : Matrix.rank (G⁻¹ * Matrix.transpose M) = Matrix.rank (Matrix.transpose M) :=
    Matrix.rank_mul_eq_right_of_isUnit_det G⁻¹ (Matrix.transpose M)
      (Matrix.isUnit_nonsing_inv_det G hG)
  have hmap : M.map (RingHom.id F) = M := Matrix.map_id M
  rw [formAdj, hmap, h1, h2, Matrix.rank_transpose]

private lemma pbr_blockDegree_formAdj {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    [Finite F]
    {G : Matrix ι ι F} (hG : IsUnit G.det)
    (hGh : Matrix.transpose (G.map (RingHom.id F)) = G)
    {S : Set (GL ι F)} (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hSU : ∀ s ∈ S, Matrix.transpose ((s : Matrix ι ι F).map (RingHom.id F)) * G *
      (s : Matrix ι ι F) = G)
    {e : Matrix ι ι F} (he : e ∈ Algebra.adjoin F (Units.val '' S)) :
    blockDegree (Algebra.adjoin F (Units.val '' S)) (formAdj (RingHom.id F) G e) =
      blockDegree (Algebra.adjoin F (Units.val '' S)) e := by
  let A : Subalgebra F (Matrix ι ι F) := Algebra.adjoin F (Units.val '' S)
  change blockDegree A (formAdj (RingHom.id F) G e) = blockDegree A e
  have hmem : ∀ {a : Matrix ι ι F}, a ∈ A → formAdj (RingHom.id F) G a ∈ A :=
    fun {a} ha => Geo.formAdj_mem_adjoin (RingHom.id F) hG hSU ha
  let ΦA : A →ₗ[F] A :=
  { toFun := fun a => ⟨formAdj (RingHom.id F) G a.1, hmem a.2⟩
    map_add' := by
      intro a b
      apply Subtype.ext
      change formAdj (RingHom.id F) G ((a : Matrix ι ι F) + (b : Matrix ι ι F)) =
        formAdj (RingHom.id F) G (a : Matrix ι ι F) +
          formAdj (RingHom.id F) G (b : Matrix ι ι F)
      rw [Geo.formAdj_add]
    map_smul' := by
      intro c a
      apply Subtype.ext
      change formAdj (RingHom.id F) G (c • (a : Matrix ι ι F)) =
        c • formAdj (RingHom.id F) G (a : Matrix ι ι F)
      rw [Geo.formAdj_smul, RingHom.id_apply] }
  have hΦA : Function.Surjective ΦA := by
    intro a
    refine ⟨ΦA a, ?_⟩
    apply Subtype.ext
    exact Geo.formAdj_formAdj (RingHom.id F) (fun x => rfl) hG hGh a.1
  have hcomp : (pbr_formAdjEquiv hG hGh).toLinearMap.comp (pbr_mulRight A e) =
      (pbr_mulRight A (formAdj (RingHom.id F) G e)).comp ΦA := by
    apply LinearMap.ext
    intro a
    show formAdj (RingHom.id F) G ((a : Matrix ι ι F) * e) =
      formAdj (RingHom.id F) G (a : Matrix ι ι F) * formAdj (RingHom.id F) G e
    rw [Geo.formAdj_mul (RingHom.id F) hG]
    exact pbr_adjoin_comm hS (formAdj (RingHom.id F) G e) (hmem he)
      (formAdj (RingHom.id F) G (a : Matrix ι ι F)) (hmem a.2)
  have hfin1 : Module.finrank F (LinearMap.range
        ((pbr_formAdjEquiv hG hGh).toLinearMap.comp (pbr_mulRight A e))) =
      Module.finrank F (LinearMap.range (pbr_mulRight A e)) := by
    rw [LinearMap.range_comp]
    exact LinearEquiv.finrank_map_eq (pbr_formAdjEquiv hG hGh)
      (LinearMap.range (pbr_mulRight A e))
  have hfin2 : Module.finrank F (LinearMap.range
        ((pbr_mulRight A (formAdj (RingHom.id F) G e)).comp ΦA)) =
      Module.finrank F (LinearMap.range (pbr_mulRight A (formAdj (RingHom.id F) G e))) := by
    rw [LinearMap.range_comp, LinearMap.range_eq_top.mpr hΦA, Submodule.map_top]
  have hmain : Module.finrank F (LinearMap.range (pbr_mulRight A e)) =
      Module.finrank F (LinearMap.range (pbr_mulRight A (formAdj (RingHom.id F) G e))) := by
    rw [← hfin1, hcomp, hfin2]
  rw [pbr_blockDegree_eq_finrank_range A (formAdj (RingHom.id F) G e),
    pbr_blockDegree_eq_finrank_range A e]
  exact hmain.symm

private lemma pbr_isPrim_formAdj {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] [Finite F]
    {G : Matrix ι ι F} (hG : IsUnit G.det)
    (hGh : Matrix.transpose (G.map (RingHom.id F)) = G)
    {S : Set (GL ι F)} (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hSU : ∀ s ∈ S, Matrix.transpose ((s : Matrix ι ι F).map (RingHom.id F)) * G *
      (s : Matrix ι ι F) = G)
    {e : Matrix ι ι F} (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e) :
    IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) (formAdj (RingHom.id F) G e) := by
  have hmem : ∀ {a : Matrix ι ι F}, a ∈ Algebra.adjoin F (Units.val '' S) →
      formAdj (RingHom.id F) G a ∈ Algebra.adjoin F (Units.val '' S) :=
    fun {a} ha => Geo.formAdj_mem_adjoin (RingHom.id F) hG hSU ha
  have hff : formAdj (RingHom.id F) G (formAdj (RingHom.id F) G e) = e :=
    Geo.formAdj_formAdj (RingHom.id F) (fun x => rfl) hG hGh e
  refine ⟨hmem he.1, ?_, ?_, ?_⟩
  · rw [isIdempotentElem_iff]
    calc formAdj (RingHom.id F) G e * formAdj (RingHom.id F) G e
        = formAdj (RingHom.id F) G (e * e) :=
          (Geo.formAdj_mul (RingHom.id F) hG e e).symm
      _ = formAdj (RingHom.id F) G e := by rw [he.2.1.eq]
  · intro h0
    have : e = 0 := by
      rw [← hff, h0]
      simp [formAdj]
    exact he.2.2.1 this
  · intro x hx hxidem hxe
    have hxmem : formAdj (RingHom.id F) G x ∈ Algebra.adjoin F (Units.val '' S) := hmem hx
    have hxidem' : IsIdempotentElem (formAdj (RingHom.id F) G x) := by
      rw [isIdempotentElem_iff]
      calc formAdj (RingHom.id F) G x * formAdj (RingHom.id F) G x
          = formAdj (RingHom.id F) G (x * x) :=
            (Geo.formAdj_mul (RingHom.id F) hG x x).symm
        _ = formAdj (RingHom.id F) G x := by rw [hxidem.eq]
    have hxe' : formAdj (RingHom.id F) G x * e = formAdj (RingHom.id F) G x := by
      have h := congrArg (formAdj (RingHom.id F) G) hxe
      rw [Geo.formAdj_mul (RingHom.id F) hG x (formAdj (RingHom.id F) G e), hff] at h
      rw [pbr_adjoin_comm hS (formAdj (RingHom.id F) G x) hxmem e he.1]
      exact h
    rcases he.2.2.2 (formAdj (RingHom.id F) G x) hxmem hxidem' hxe' with h0 | heq
    · left
      rw [← Geo.formAdj_formAdj (RingHom.id F) (fun x => rfl) hG hGh x, h0]
      simp [formAdj]
    · right
      rw [← Geo.formAdj_formAdj (RingHom.id F) (fun x => rfl) hG hGh x, heq]

private lemma pbr_commutator_kills {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    [Finite F] [CharP F 2] {S : Set (GL ι F)} (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s)) {e : Matrix ι ι F}
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e)
    (hthin : Matrix.rank e = blockDegree (Algebra.adjoin F (Units.val '' S)) e)
    {gM g'M : Matrix ι ι F}
    (hg : ∀ a ∈ Algebra.adjoin F (Units.val '' S), gM * a = a * gM)
    (hg' : ∀ a ∈ Algebra.adjoin F (Units.val '' S), g'M * a = a * g'M) :
    (gM * g'M - g'M * gM) * e = 0 := by
  obtain ⟨a, ha, hae⟩ := pbr_thin_action hS hodd he hthin hg
  obtain ⟨a', ha', ha'e⟩ := pbr_thin_action hS hodd he hthin hg'
  have hcomm : a' * a = a * a' := pbr_adjoin_comm hS a' ha' a ha
  have h1 : (gM * g'M) * e = (a' * a) * e := by
    calc (gM * g'M) * e = gM * (g'M * e) := by rw [Matrix.mul_assoc]
      _ = gM * (a' * e) := by rw [ha'e]
      _ = (gM * a') * e := by rw [Matrix.mul_assoc]
      _ = (a' * gM) * e := by rw [hg a' ha']
      _ = a' * (gM * e) := by rw [Matrix.mul_assoc]
      _ = a' * (a * e) := by rw [hae]
      _ = (a' * a) * e := by rw [Matrix.mul_assoc]
  have h2 : (g'M * gM) * e = (a * a') * e := by
    calc (g'M * gM) * e = g'M * (gM * e) := by rw [Matrix.mul_assoc]
      _ = g'M * (a * e) := by rw [hae]
      _ = (g'M * a) * e := by rw [Matrix.mul_assoc]
      _ = (a * g'M) * e := by rw [hg' a ha]
      _ = a * (g'M * e) := by rw [Matrix.mul_assoc]
      _ = a * (a' * e) := by rw [ha'e]
      _ = (a * a') * e := by rw [Matrix.mul_assoc]
  rw [Matrix.sub_mul, h1, h2, hcomm, sub_self]

theorem isPrimIdemIn_eq_or_add_formAdj_statedSp (n : ℕ) (F : Type)
    [Field F] [Finite F] [CharP F 2]
    {S : Set (GL (Fin n ⊕ Fin n) F)}
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hSU : ∀ s ∈ S, s ∈ StatedSp n F)
    {ε e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F)
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
      (Algebra.adjoin F (Units.val '' S)) ε)
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e) (heε : e * ε = e) :
    ε = e ∨ (ε = e + formAdj (RingHom.id F)
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) e ∧
      e * formAdj (RingHom.id F)
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) e = 0) := by
  let Jm : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F := Matrix.fromBlocks 0 1 (-1) 0
  have hG : IsUnit Jm.det := by simpa [Jm, pbr_J] using pbr_J_det n F
  have hGh : Matrix.transpose (Jm.map (RingHom.id F)) = Jm := by
    simpa [Jm, pbr_J] using pbr_J_transpose n F
  have hSU' : ∀ s ∈ S,
      Matrix.transpose ((s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).map (RingHom.id F)) *
        Jm * (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) = Jm := by
    intro s hs
    have hmap : (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).map (RingHom.id F) =
        (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) := Matrix.map_id _
    rw [hmap]
    simpa [Jm] using CFSG.Open.StatedAPI.mem_statedSp_iff.mp (hSU s hs)
  exact isPrimIdemIn_eq_or_add_formAdj hG hGh hS hSU' hε he heε

theorem two_mul_blockDegree_le_rank_PSp (n : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2]
    (S : Set (GL (Fin n ⊕ Fin n) F))
    (hSU : ∀ s ∈ S, s ∈ StatedSp n F) (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s)) {J' : Subgroup ↥(StatedSp n F)}
    {ε e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F)
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
      (Algebra.adjoin F (Units.val '' S)) ε)
    (hJε : IsComponentOf J'
      ⁅glBlockCentralizer (StatedSp n F).subtype S ε, glBlockCentralizer
      (StatedSp n F).subtype S ε⁆)
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e) (heε : e * ε = e) :
    2 * blockDegree (Algebra.adjoin F (Units.val '' S)) e ≤ Matrix.rank e := by
  classical
  let Jm : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F := Matrix.fromBlocks 0 1 (-1) 0
  let A : Subalgebra F (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) :=
    Algebra.adjoin F (Units.val '' S)
  have hG : IsUnit Jm.det := by simpa [Jm, pbr_J] using pbr_J_det n F
  have hGh : Matrix.transpose (Jm.map (RingHom.id F)) = Jm := by
    simpa [Jm, pbr_J] using pbr_J_transpose n F
  have hSU' : ∀ s ∈ S,
      Matrix.transpose ((s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).map (RingHom.id F)) *
        Jm * (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) = Jm := by
    intro s hs
    have h := CFSG.Open.StatedAPI.mem_statedSp_iff.mp (hSU s hs)
    have hmap : (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).map (RingHom.id F) =
        (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) := Matrix.map_id _
    rw [hmap]
    simpa [Jm] using h
  by_contra hle
  have hlt : Matrix.rank e < 2 * blockDegree A e := by
    simpa [A] using Nat.lt_of_not_le hle
  have he_thin : Matrix.rank e = blockDegree A e := by
    simpa [A] using pbr_thin_of_lt hS hodd he hlt
  have hAdj_prim : IsPrimIdemIn A (formAdj (RingHom.id F) Jm e) := by
    simpa [A] using pbr_isPrim_formAdj (G := Jm) hG hGh hS hSU' he
  have hrank_adj : Matrix.rank (formAdj (RingHom.id F) Jm e) = Matrix.rank e :=
    pbr_rank_formAdj_id (G := Jm) (M := e) hG
  have hdeg_adj : blockDegree A (formAdj (RingHom.id F) Jm e) = blockDegree A e := by
    simpa [A] using pbr_blockDegree_formAdj (G := Jm) hG hGh hS hSU' he.1
  have hAdj_thin : Matrix.rank (formAdj (RingHom.id F) Jm e) =
      blockDegree A (formAdj (RingHom.id F) Jm e) := by
    rw [hrank_adj, hdeg_adj, he_thin]
  have hdich : ε = e ∨ (ε = e + formAdj (RingHom.id F) Jm e ∧
      e * formAdj (RingHom.id F) Jm e = 0) :=
    isPrimIdemIn_eq_or_add_formAdj (G := Jm) hG hGh hS hSU' hε he heε
  let Gε : Subgroup ↥(StatedSp n F) := glBlockCentralizer (StatedSp n F).subtype S ε
  have hab : ∀ g ∈ Gε, ∀ g' ∈ Gε, g * g' = g' * g := by
    intro g hg g' hg'
    let gM : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F :=
      ((g : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
    let g'M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F :=
      ((g' : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
    apply Subtype.ext
    apply Units.ext
    change gM * g'M = g'M * gM
    have hgmem : (g : GL (Fin n ⊕ Fin n) F) ∈
        Subgroup.centralizer S ⊓ glFixing (1 - ε) := Subgroup.mem_comap.mp hg
    have hgmem' : (g' : GL (Fin n ⊕ Fin n) F) ∈
        Subgroup.centralizer S ⊓ glFixing (1 - ε) := Subgroup.mem_comap.mp hg'
    have hgc : (g : GL (Fin n ⊕ Fin n) F) ∈ Subgroup.centralizer S :=
      (Subgroup.mem_inf.mp hgmem).1
    have hgf : gM * (1 - ε) = 1 - ε := (Subgroup.mem_inf.mp hgmem).2
    have hgc' : (g' : GL (Fin n ⊕ Fin n) F) ∈ Subgroup.centralizer S :=
      (Subgroup.mem_inf.mp hgmem').1
    have hgf' : g'M * (1 - ε) = 1 - ε := (Subgroup.mem_inf.mp hgmem').2
    have hgcomm : ∀ s ∈ S, gM * (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
        (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * gM := by
      intro s hs
      have h := congrArg
        (fun u : GL (Fin n ⊕ Fin n) F => (u : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F))
        (Subgroup.mem_centralizer_iff.mp hgc s hs)
      simpa [gM, Units.val_mul] using h.symm
    have hgcomm' : ∀ s ∈ S, g'M * (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
        (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * g'M := by
      intro s hs
      have h := congrArg
        (fun u : GL (Fin n ⊕ Fin n) F => (u : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F))
        (Subgroup.mem_centralizer_iff.mp hgc' s hs)
      simpa [g'M, Units.val_mul] using h.symm
    have hgA : ∀ a ∈ A, gM * a = a * gM := by
      intro a ha
      exact pbr_commute_adjoin hgcomm a (by simpa [A] using ha)
    have hgA' : ∀ a ∈ A, g'M * a = a * g'M := by
      intro a ha
      exact pbr_commute_adjoin hgcomm' a (by simpa [A] using ha)
    have hce := pbr_commutator_kills hS hodd he (by simpa [A] using he_thin) hgA hgA'
    have hce' := pbr_commutator_kills hS hodd (by simpa [A] using hAdj_prim)
      (by simpa [A] using hAdj_thin) hgA hgA'
    have hcε : (gM * g'M - g'M * gM) * ε = 0 := by
      rcases hdich with hee | ⟨hεeq, _hprod⟩
      · rw [hee, hce]
      · rw [hεeq, Matrix.mul_add, hce, hce', add_zero]
    have hc1 : (gM * g'M - g'M * gM) * (1 - ε) = 0 := by
      rw [Matrix.sub_mul, Matrix.mul_assoc, hgf', hgf, Matrix.mul_assoc, hgf, hgf', sub_self]
    have hc : gM * g'M - g'M * gM = 0 := by
      have h1 : (gM * g'M - g'M * gM) * ((1 - ε) + ε) = 0 := by
        rw [Matrix.mul_add, hc1, hcε, add_zero]
      have h2 : (1 - ε) + ε = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) := by abel
      rwa [h2, Matrix.mul_one] at h1
    exact sub_eq_zero.mp hc
  have hcen : Gε ≤ Subgroup.centralizer (Gε : Set ↥(StatedSp n F)) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro g' hg'
    exact (hab g hg g' hg').symm
  have hbot : ⁅Gε, Gε⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcen
  have hJε_le : J' ≤ ⁅Gε, Gε⁆ := hJε.1
  have hJ'bot : J' = ⊥ := le_bot_iff.mp (hbot ▸ hJε_le)
  exact pbr_not_isQuasisimple_bot (hJ'bot ▸ hJε.2.2)

end CFSG.StandardType.TableC

end
