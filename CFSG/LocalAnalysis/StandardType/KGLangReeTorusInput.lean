module

public import CFSG.LocalAnalysis.StandardType.KGLangTorusMPartDefs
public import CFSG.LocalAnalysis.StandardType.GGLieCoreDefs
public import CFSG.LocalAnalysis.StandardType.GGReeLangPositionF4
import CFSG.LocalAnalysis.StandardType.KGLangReeTorusLang
import CFSG.LocalAnalysis.StandardType.GGL45NtExcFrame
import CFSG.LocalAnalysis.StandardType.GGLieCoreRatFinite
import CFSG.LieType.Chevalley.WeylNormalizerQuotient
import CFSG.RankThree.PartOne.KE.A1Weyl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.StandardType CFSG.RankThree.PerfectCover CFSG.HardMathSupport.C14Exc
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.RankThree.PartOne.TCX.Ree
  CFSG.StandardType.LieCore

private lemma kgLangReeInputAux_pow_apply {G : Type*} [Group G] (e : MulAut G) (n : ℕ) :
    ∀ x : G, (e ^ n) x = e^[n] x := by
  induction n with
  | zero => intro x; rfl
  | succ n ih =>
    intro x
    rw [pow_succ, MulAut.mul_apply, ih, Function.iterate_succ_apply]

private theorem kgLangReeInputAux_prod_range_mul_succ {M : Type*} [Monoid M] (k : ℕ)
    (f : ℕ → M) :
    ((List.range k).map f).prod * f k = f 0 * ((List.range k).map (fun i => f (i + 1))).prod := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [List.range_succ, List.map_append, List.map_singleton, List.prod_append,
      List.prod_singleton]
    rw [ih, mul_assoc]

private theorem kgLangReeInputAux_endPow_mul_prod {Γ : Type*} [Group Γ] (F : Γ →* Γ)
    (x z : Γ) (hFz : F z = z * x) (k : ℕ) :
    endPow F k z = z * ((List.range k).map fun i => endPow F i x).prod := by
  have hFstep : ∀ i, F (endPow F i x) = endPow F (i + 1) x := by
    intro i
    rw [endPow_apply, endPow_apply, Function.iterate_succ_apply', ← endPow_apply]
  induction k with
  | zero => simp [endPow_apply]
  | succ k ih =>
    have hstep : endPow F (k + 1) z = F (endPow F k z) := by
      rw [endPow_apply, Function.iterate_succ_apply', ← endPow_apply]
    rw [hstep, ih, map_mul, hFz]
    have hFP : F (((List.range k).map (fun i => endPow F i x)).prod) =
        ((List.range k).map (fun i => endPow F (i + 1) x)).prod := by
      rw [map_list_prod, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact hFstep i
    rw [hFP]
    simp only [List.range_succ, List.map_append, List.prod_append, List.map_singleton,
      List.prod_singleton]
    rw [kgLangReeInputAux_prod_range_mul_succ k (fun i => endPow F i x)]
    simp only [endPow_apply, Function.iterate_zero, id_eq]
    rw [mul_assoc]

theorem kgLangReeTorusInput (hRLP : GGReeLangPositionF4)
    (hM1 : GGLieToralPosition) {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (hL : letI := ZMod.algebra L 2; Algebra.IsAlgebraic (ZMod 2) L)
    (C : ReeClosure L) {b p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    KGLangTorusInput p (((C.Φ * C.Fr ^ b) ^ p).toMonoidHom.eqLocus
      (MonoidHom.id (adjointGroup ReeTag.F4.tag L))) (C.Φ * C.Fr ^ b).toMonoidHom := by
  classical
  intro E hEab hEG
  set S : MulAut (adjointGroup ReeTag.F4.tag L) := C.Φ * C.Fr ^ b with hS
  have hFrtw : ∀ y : adjointGroup ReeTag.F4.tag L,
      C.Fr y = frobeniusTwist ReeTag.F4.tag L (iterateFrobenius L 2 1) y := fun y =>
    Subtype.ext (C.fr_apply y)
  have hRee : CFSG.RankThree.PartOne.KLR.IsReeFrob b S := by
    rw [hS]; exact CFSG.RankThree.PartOne.KLR.isReeFrob_of_exceptional C.isExc hFrtw b
  have hSsq : S * S = C.Fr ^ (2 * b + 1) := by
    have hpow : C.Φ * C.Fr ^ b = C.Φ ^ (2 * b + 1) := by
      rw [← C.sq, ← _root_.sq, ← pow_mul, ← pow_succ']
    rw [hS, hpow, ← pow_add, show 2 * b + 1 + (2 * b + 1) = 2 * (2 * b + 1) by ring, pow_mul,
      _root_.sq, C.sq]
  have hEfix : ∀ x ∈ E, S x = x := fun x hx => (hEG x hx).2
  have hEpow : ∀ x ∈ E, (S ^ p) x = x := fun x hx => (hEG x hx).1
  set A : Subgroup (ModGL ReeTag.F4.tag L) := E.map (adjointGroup ReeTag.F4.tag L).subtype with hA
  set Φ : ModGL ReeTag.F4.tag L →* ModGL ReeTag.F4.tag L :=
    CFSG.LieType.AlgebraicGroups.frobTwistGL ReeTag.F4.tag L 2 (2 * b + 1) 1 with hΦ
  have hcoe : ∀ z : adjointGroup ReeTag.F4.tag L, Φ (z : ModGL ReeTag.F4.tag L) =
      ((S * S) z : ModGL ReeTag.F4.tag L) := by
    intro z
    rw [hΦ, CFSG.LieType.AlgebraicGroups.frobTwistGL_apply, one_mul, inv_one, mul_one, hSsq]
    exact (coe_pow_apply_of_entrywise_frobenius 2 C.Fr C.fr_apply (2 * b + 1) z).symm
  have hA_le : A ≤ CFSG.StandardType.LieCore.ratPoints Φ := by
    rintro x ⟨y, hy, rfl⟩
    refine ⟨y.2, ?_⟩
    change Φ (y : ModGL ReeTag.F4.tag L) = (y : ModGL ReeTag.F4.tag L)
    rw [hcoe y, MulAut.mul_apply, hEfix y hy, hEfix y hy]
  have hA_el : IsElemAbelian p A := CFSG.Open.IsElemAbelian.map hEab _
  have hΦstein : IsSteinbergEndZ ReeTag.F4.tag L (2 ^ (2 * b + 1)) Φ := by
    rw [hΦ]
    exact isSteinbergEndZ_frobTwistGL 2 (2 * b + 1) (Or.inl rfl)
  have hfin : Finite ↥(CFSG.StandardType.LieCore.ratPoints Φ) :=
    finite_ratPoints (q := 2 ^ (2 * b + 1))
      (Nat.one_lt_pow (by norm_num) (by omega)) hΦstein
  have hA_card : Nat.card A < p ^ nontoralMinRank ReeTag.F4.tag p := by
    haveI : Finite ↥(CFSG.StandardType.LieCore.ratPoints Φ) := hfin
    haveI : Finite A := Finite.of_injective (Subgroup.inclusion hA_le) (Subgroup.inclusion_injective hA_le)
    rw [nontoralMinRank_eq_of_nonTorsion (τ := ReeTag.F4.tag) (by intro _; omega) (by intro h; cases h)]
    exact card_elemAbelian_lt (τ := ReeTag.F4.tag) (by norm_num) hp (by omega) hA_el
  have hM1' : CFSG.StandardType.ExcFramesHalf.IsToralSubgroup ReeTag.F4.tag L A :=
    hM1 ReeTag.F4.tag (Or.inr (Or.inl ReeTag.tag_F4)) L hL (2 * b + 1) (by omega) Φ hΦstein hfin p hp (by omega) A hA_le hA_el
      hA_card
  obtain ⟨g₁, hg₁adj, hg₁H⟩ := hM1'
  have hg₁_adj : ∃ g₁' : adjointGroup ReeTag.F4.tag L, ∀ x ∈ E,
      ((g₁'⁻¹ * x * g₁' : adjointGroup ReeTag.F4.tag L) : ModGL ReeTag.F4.tag L) ∈
        torusGroup ReeTag.F4.tag L := by
    refine ⟨⟨g₁, hg₁adj⟩, fun x hx => ?_⟩
    have hxA : (x : ModGL ReeTag.F4.tag L) ∈ A := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    have h1 := hg₁H (x : ModGL ReeTag.F4.tag L) hxA
    exact h1
  obtain ⟨g, w, hgw, hgH⟩ := hRLP L C b E hEfix hg₁_adj
  set nw : adjointGroup ReeTag.F4.tag L := g⁻¹ * S g with hnwdef
  have hnw : (nw : ModGL ReeTag.F4.tag L) = canonicalRep (coxeterSystem ReeTag.F4.tag) L w := hgw
  have hnw_norm : (nw : ModGL ReeTag.F4.tag L) ∈
      Subgroup.normalizer (torusGroup ReeTag.F4.tag L : Set (ModGL ReeTag.F4.tag L)) := by
    rw [hnw]; exact canonicalRep_mem_normalizer w
  set Fw : MulAut (adjointGroup ReeTag.F4.tag L) := MulAut.conj nw * S with hFw
  set Hadj : Subgroup (adjointGroup ReeTag.F4.tag L) :=
    (torusGroup ReeTag.F4.tag L).subgroupOf (adjointGroup ReeTag.F4.tag L) with hHadj
  have hS0_le : Hadj.map S.toMonoidHom ≤ Hadj := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨hadj, hmap⟩ := hRee.map_torusGroup (Subgroup.mem_subgroupOf.mp hx)
    have hx_eq : (⟨(x : ModGL ReeTag.F4.tag L), hadj⟩ : adjointGroup ReeTag.F4.tag L) = x :=
      Subtype.ext rfl
    rw [hx_eq] at hmap
    exact Subgroup.mem_subgroupOf.mpr hmap
  have hnw_conj_le : Hadj.map (MulAut.conj nw).toMonoidHom ≤ Hadj := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 := (Subgroup.mem_normalizer_iff.mp hnw_norm (x : ModGL ReeTag.F4.tag L)).1
      (Subgroup.mem_subgroupOf.mp hx)
    show (((MulAut.conj nw) x : adjointGroup ReeTag.F4.tag L) : ModGL ReeTag.F4.tag L) ∈
      torusGroup ReeTag.F4.tag L
    rw [MulAut.conj_apply]
    simpa using h1
  have hFw_le : Hadj.map Fw.toMonoidHom ≤ Hadj := by
    rw [hFw]
    have hcomp : (MulAut.conj nw * S).toMonoidHom =
        (MulAut.conj nw).toMonoidHom.comp S.toMonoidHom := rfl
    rw [hcomp, ← Subgroup.map_map]
    exact (Subgroup.map_mono hS0_le).trans hnw_conj_le
  have hconj : ∀ y : adjointGroup ReeTag.F4.tag L,
      S (g * y * g⁻¹) = g * Fw y * g⁻¹ := by
    intro y
    have hgS : S g = g * nw := by rw [hnwdef]; group
    calc S (g * y * g⁻¹) = S g * S y * (S g)⁻¹ := by rw [map_mul, map_mul, map_inv]
      _ = (g * nw) * S y * (g * nw)⁻¹ := by rw [hgS]
      _ = g * (nw * S y * nw⁻¹) * g⁻¹ := by group
      _ = g * Fw y * g⁻¹ := rfl
  have hconj_iter : ∀ n, ∀ y : adjointGroup ReeTag.F4.tag L,
      S^[n] (g * y * g⁻¹) = g * Fw^[n] y * g⁻¹ := by
    intro n
    induction n with
    | zero => intro y; simp
    | succ n ih =>
      intro y
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      exact hconj _
  set Hp : Subgroup (adjointGroup ReeTag.F4.tag L) :=
    Hadj ⊓ (endPow Fw p).eqLocus (MonoidHom.id _) with hHp
  set N : Subgroup (adjointGroup ReeTag.F4.tag L) := Hp.map (MulAut.conj g).toMonoidHom with hN
  have mem_Hp : ∀ y : adjointGroup ReeTag.F4.tag L, y ∈ Hp ↔
      y ∈ Hadj ∧ (endPow Fw p) y = y := by
    intro y
    rw [hHp, Subgroup.mem_inf]
    exact Iff.rfl
  refine ⟨N, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro x hx
    obtain ⟨y, hyHp, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨hyH, hyfix⟩ := (mem_Hp y).mp hyHp
    have hyfix' : Fw^[p] y = y := hyfix
    show (S ^ p) (g * y * g⁻¹) = g * y * g⁻¹
    rw [kgLangReeInputAux_pow_apply S p, hconj_iter p y, hyfix']
  ·
    intro a ha b hb
    obtain ⟨y, hyHp, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨z, hzHp, rfl⟩ := Subgroup.mem_map.mp hb
    obtain ⟨hyH, -⟩ := (mem_Hp y).mp hyHp
    obtain ⟨hzH, -⟩ := (mem_Hp z).mp hzHp
    have hcomm := CFSG.RankThree.PartOne.KE.torusGroup_comm
      (Subgroup.mem_subgroupOf.mp hyH) (Subgroup.mem_subgroupOf.mp hzH)
    have hcomm' : y * z = z * y := by
      apply Subtype.ext
      simpa only [Subgroup.coe_mul] using hcomm
    change (MulAut.conj g) y * (MulAut.conj g) z = (MulAut.conj g) z * (MulAut.conj g) y
    rw [MulAut.conj_apply, MulAut.conj_apply]
    calc (g * y * g⁻¹) * (g * z * g⁻¹) = g * (y * z) * g⁻¹ := by group
      _ = g * (z * y) * g⁻¹ := by rw [hcomm']
      _ = (g * z * g⁻¹) * (g * y * g⁻¹) := by group
  ·
    intro x hx
    obtain ⟨y, hyHp, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨hyH, hyfix⟩ := (mem_Hp y).mp hyHp
    have hFwy : Fw y ∈ Hp := by
      refine (mem_Hp (Fw y)).mpr ⟨hFw_le (Subgroup.mem_map_of_mem Fw.toMonoidHom hyH), ?_⟩
      change endPow Fw.toMonoidHom p (Fw.toMonoidHom y) = Fw.toMonoidHom y
      have hyfixT : endPow Fw.toMonoidHom p y = y := hyfix
      rw [endPow_comm_apply Fw.toMonoidHom p y, hyfixT]
    refine Subgroup.mem_map.mpr ⟨Fw y, hFwy, ?_⟩
    change (MulAut.conj g) (Fw y) = S ((MulAut.conj g) y)
    rw [MulAut.conj_apply, MulAut.conj_apply]
    exact (hconj y).symm
  ·
    intro c hc hnorm
    obtain ⟨y, hyHp, rfl⟩ := Subgroup.mem_map.mp hc
    obtain ⟨hyH, hyfix⟩ := (mem_Hp y).mp hyHp
    have hiter : ∀ i, S^[i] (g * y * g⁻¹) = g * Fw^[i] y * g⁻¹ :=
      fun i => hconj_iter i y
    have hprod : ((List.range p).map fun i => Fw^[i] y).prod = 1 := by
      have h1 : (MulAut.conj g) (((List.range p).map fun i => Fw^[i] y).prod) =
          ((List.range p).map fun i => S^[i] (g * y * g⁻¹)).prod := by
        rw [map_list_prod, List.map_map]
        congr 1
        apply List.map_congr_left
        intro i _
        show MulAut.conj g (Fw^[i] y) = S^[i] (g * y * g⁻¹)
        rw [MulAut.conj_apply]
        exact (hiter i).symm
      have h2 : ((List.range p).map fun i => endPow S.toMonoidHom i
          (g * y * g⁻¹)).prod = 1 := hnorm
      have h3 : (MulAut.conj g) (((List.range p).map fun i => Fw^[i] y).prod) = 1 := by
        rw [h1]
        have h2' : ((List.range p).map fun i => S^[i] (g * y * g⁻¹)).prod =
            ((List.range p).map fun i => endPow S.toMonoidHom i (g * y * g⁻¹)).prod := by
          congr 1
        rw [h2', h2]
      exact (MulAut.conj g).injective (by rw [h3, map_one])
    obtain ⟨z, hzH, hz⟩ := kgLangRee_torus_lang C b nw hnw_norm y
      (Subgroup.mem_subgroupOf.mp hyH)
    have hFwz : Fw z = z * y := by
      change MulAut.conj nw (S z) = z * y
      rw [MulAut.conj_apply, hz]
      group
      rfl
    have hzfix : endPow Fw p z = z := by
      change endPow Fw.toMonoidHom p z = z
      rw [kgLangReeInputAux_endPow_mul_prod Fw.toMonoidHom y z hFwz p]
      have : ((List.range p).map fun i => endPow Fw.toMonoidHom i y).prod = 1 := by
        have hp' : ((List.range p).map fun i => endPow Fw.toMonoidHom i y).prod =
            ((List.range p).map fun i => Fw^[i] y).prod := by
          congr 1
        rw [hp', hprod]
      rw [this, mul_one]
    have hzHp : z ∈ Hp := (mem_Hp z).mpr ⟨hzH, hzfix⟩
    refine ⟨(MulAut.conj g) z, Subgroup.mem_map.mpr ⟨z, hzHp, rfl⟩, ?_⟩
    change (MulAut.conj g) y = ((MulAut.conj g) z)⁻¹ * S ((MulAut.conj g) z)
    rw [MulAut.conj_apply, MulAut.conj_apply, hconj z, hFwz]
    group
  ·
    intro x hx
    have hgxH := hgH x hx
    have hgxfix : Fw (g⁻¹ * x * g) = g⁻¹ * x * g := by
      change MulAut.conj nw (S (g⁻¹ * x * g)) = g⁻¹ * x * g
      have hSg : S g = g * nw := by rw [hnwdef]; group
      rw [MulAut.conj_apply, map_mul, map_mul, map_inv, hSg, hEfix x hx]
      group
    have hgxHp : g⁻¹ * x * g ∈ Hp := by
      refine (mem_Hp _).mpr ⟨Subgroup.mem_subgroupOf.mpr hgxH, ?_⟩
      rw [endPow_apply]
      exact Function.iterate_fixed hgxfix p
    refine Subgroup.mem_map.mpr ⟨g⁻¹ * x * g, hgxHp, ?_⟩
    change (MulAut.conj g) (g⁻¹ * x * g) = x
    rw [MulAut.conj_apply]
    group

end CFSG.StandardType
