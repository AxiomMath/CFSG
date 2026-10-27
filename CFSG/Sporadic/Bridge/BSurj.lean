module

public import CFSG.Sporadic.Bridge.Common
public import CFSG.Sporadic.Bridge.BData
public meta import CFSG.Sporadic.Bridge.BData
public import CFSG.Sporadic.Bridge.BOrder
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import CFSG.Sporadic.Bridge.BSurjInputs
public import CFSG.Sporadic.Bridge.BGlue9201
public import Certificates.Certificate9201
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3028
public import Certificates.Certificate3045
public import Certificates.Certificate3048
public import Certificates.Certificate3049
public import Certificates.Certificate3050
public import Certificates.Certificate3051
public import Certificates.Certificate3101
public import Certificates.Certificate3102
public import Certificates.Certificate3103
public import Certificates.Certificate3106
public import Certificates.Certificate3107
public import Certificates.Certificate3108
public import Certificates.Certificate3109
public import Certificates.Certificate6001
public import Certificates.Certificate6002
public import Certificates.Certificate6003
public import Certificates.Certificate6004
public import Certificates.Certificate6005
public import Certificates.Certificate6007
public import Certificates.Certificate16026
public import Certificates.Certificate3027
public meta import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Points
public import CFSG.Monster.B.TwoA.Unitary.Semilinear

public section

namespace CFSG.Sporadic.Bridge.B

open CFSG.Blueprint CFSG.Monster.B CFSG.Monster.B.Pinned CFSG.Monster.B.Bin
  CFSG.Monster.B.Primes.Native TauCeti
open scoped Matrix

private theorem presentation_eq : SporadicName.B.presentation = pres := rfl

theorem bProg_lt : ∀ ins ∈ bProg, ins.lt bN = true := by decide +kernel

theorem bTreg_lt : ∀ k < 11, bTreg k < bN := by decide +kernel

@[expose] def Wd.eval {G : Type*} [Monoid G] (g : ℕ → G) : Wd → G
  | .gen i => g i
  | .mul u v => u.eval g * v.eval g
  | .pow u e => u.eval g ^ e

theorem wA_eval {G : Type*} [Monoid G] (g : ℕ → G) :
    (wA : Wd).eval g = CFSG.KC.BM.B9201.apT g := by
  simp only [wA, wR, wS, Wd.chain, List.foldl_cons, List.foldl_nil, Wd.eval, CFSG.KC.BM.B9201.apT,
    CFSG.KC.BM.B9201.rT, CFSG.KC.BM.B9201.sT, CFSG.KC.BM.B9201.lp, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, mul_assoc]

theorem wB_eval {G : Type*} [Group G] {g : ℕ → G} (i : ∀ k < 11, (g k)⁻¹ = g k) :
    (wB : Wd).eval g = (CFSG.KC.BM.B9201.hT g)⁻¹ * (g 0 * g 1) * CFSG.KC.BM.B9201.hT g := by
  simp only [wB, wR, wS, wRi, wSi, Wd.chain, List.foldl_cons, List.foldl_nil, Wd.eval,
    CFSG.KC.BM.B9201.hT, CFSG.KC.BM.B9201.rT, CFSG.KC.BM.B9201.sT, CFSG.KC.BM.B9201.lp,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, ← inv_pow, mul_inv_rev,
    i 0 (by norm_num), i 1 (by norm_num), i 2 (by norm_num), i 3 (by norm_num), i 4 (by norm_num),
    i 5 (by norm_num), i 6 (by norm_num), i 7 (by norm_num), i 8 (by norm_num), i 9 (by norm_num),
    i 10 (by norm_num), mul_assoc]

theorem rep_wd {G : Type*} [Monoid G] {n : ℕ} {f : G →* Matrix (Fin n) (Fin n) (ZMod 2)}
    {T : Array Mat} {g : ℕ → G} (hT : ∀ i < 11, Rep f (T.getD i #[]) (g i)) :
    ∀ w : Wd, w.gensLt 11 = true → Rep f (w.evalN n T) (w.eval g)
  | .gen i, h => by
    simp only [Wd.gensLt, decide_eq_true_eq] at h
    exact hT i h
  | .mul u v, h => by
    simp only [Wd.gensLt, Bool.and_eq_true] at h
    exact rep_mul (rep_wd hT u h.1) (rep_wd hT v h.2)
  | .pow u e, h => by
    simp only [Wd.gensLt] at h
    exact rep_pow (rep_wd hT u h) e

theorem rep_wordN {G : Type*} [Group G] {n : ℕ} {f : G →* Matrix (Fin n) (Fin n) (ZMod 2)}
    {T : Array Mat} {g : ℕ → G} (hT : ∀ i < 11, Rep f (T.getD i #[]) (g i))
    (hinv : ∀ i < 11, g i * g i = 1) :
    ∀ w : List (ℕ × Bool), (∀ l ∈ w, l.1 < 11) → Rep f (wordN n T w) (wordProd g w) := by
  have hl : ∀ l : ℕ × Bool, l.1 < 11 →
      Rep f (T.getD l.1 #[]) (if l.2 then g l.1 else (g l.1)⁻¹) := by
    intro l hl
    split_ifs
    · exact hT l.1 hl
    · rw [inv_eq_of_mul_eq_one_right (hinv l.1 hl)]
      exact hT l.1 hl
  have key : ∀ (w : List (ℕ × Bool)), (∀ l ∈ w, l.1 < 11) → ∀ (acc : Mat) (a : G),
      Rep f acc a → Rep f (w.foldl (fun acc l' => mulP n acc (T.getD l'.1 #[])) acc)
        (a * (w.map fun l => if l.2 then g l.1 else (g l.1)⁻¹).prod) := by
    intro w
    induction w with
    | nil => intro _ acc a h; simpa using h
    | cons l w ih =>
      intro hw acc a h
      rw [List.foldl_cons, List.map_cons, List.prod_cons, ← mul_assoc]
      exact ih (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')) _ _
        (rep_mul h (hl l (hw l List.mem_cons_self)))
  intro w
  cases w with
  | nil => intro _; simpa [wordN, wordProd] using (rep_one (f := f))
  | cons l w =>
    intro hw
    have := key w (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')) _ _
      (hl l (hw l List.mem_cons_self))
    simpa [wordN, wordProd] using this

theorem wordProd_flatten_replicate {G : Type*} [Group G] (g : ℕ → G) (base : List (ℕ × Bool))
    (k : ℕ) : wordProd g (List.replicate k base).flatten = wordProd g base ^ k := by
  induction k with
  | zero => simp [wordProd]
  | succ k ih =>
    rw [List.replicate_succ, List.flatten_cons]
    simp only [wordProd, List.map_append, List.prod_append] at ih ⊢
    rw [ih, pow_succ']

theorem rels_of_relsOK {G : Type*} [Group G] {f : G →* Matrix (Fin 4370) (Fin 4370) (ZMod 2)}
    (hf : Function.Injective f) {T : Array Mat} {g : ℕ → G}
    (hT : ∀ i < 11, Rep f (T.getD i #[]) (g i)) (hinv : ∀ i < 11, g i * g i = 1)
    {rels : List (List (ℕ × Bool))} (h : relsOK T rels = true) :
    ∀ v ∈ rels, wordProd g v = 1 := by
  intro v hv
  have := (List.all_eq_true.1 h) v hv
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at this
  obtain ⟨⟨hbase, hB⟩, hC⟩ := this
  have hr : v = (List.replicate (relFactor v).2 (relFactor v).1).flatten := beq_iff_eq.1 hB
  have hrep := rep_pow (rep_wordN hT hinv (relFactor v).1 hbase) (relFactor v).2
  exact (congrArg (wordProd g) hr).trans
    ((wordProd_flatten_replicate g _ _).trans (eq_of_rep hf hrep rep_one hC))

theorem conj_facts {A B a b : Mat} (ha : a.size ≤ 4370) (hb : b.size ≤ 4370)
    (h : conjChecks A B a b = true) :
    ∃ G Gi : Matrix (Fin 4370) (Fin 4370) (ZMod 2), cmat 4370 A * G = G * cmat 4370 a ∧
      cmat 4370 B * G = G * cmat 4370 b ∧ G * Gi = 1 := by
  unfold conjChecks at h
  dsimp only at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  set Gm := mulP 4370 (invM 4370 (spinMat 4370 (unitRow 4370 0) A B (treeOfText treeText)))
    (spinMat 4370 (rowOfText rowText) a b (treeOfText treeText)) with hGm
  set Gi := mulP 4370 (invM 4370 (spinMat 4370 (rowOfText rowText) a b (treeOfText treeText)))
    (spinMat 4370 (unitRow 4370 0) A B (treeOfText treeText)) with hGi
  have hGms : Gm.size ≤ 4370 := by
    rw [hGm, mulP_size, invM_size]
  have hGis : Gi.size ≤ 4370 := by
    rw [hGi, mulP_size, invM_size]
  refine ⟨cmat 4370 Gm, cmat 4370 Gi, ?_, ?_, ?_⟩
  · rw [← cmat_mulP 4370 A Gm hGms, ← cmat_mulP 4370 Gm a ha]
    exact cmat_eq_of_beq h1
  · rw [← cmat_mulP 4370 B Gm hGms, ← cmat_mulP 4370 Gm b hb]
    exact cmat_eq_of_beq h2
  · rw [← cmat_mulP 4370 Gm Gi hGis, cmat_eq_of_beq h3, cmat_idMat]

@[expose] noncomputable def tB
    (k : ℕ) : NativeSporadic.B := runG bProg bA₁ bA₂ (bTreg k)

structure BridgeFacts (rels : List (List (ℕ × Bool))) : Prop where
  inv : ∀ i < 11, tB i * tB i = 1
  rels : ∀ v ∈ rels, wordProd tB v = 1
  conj : ∃ Gu : GL (Fin 4370) (ZMod 2), glA₁ * Gu = Gu * bGL ((wA : Wd).eval tB) ∧
    glA₂ * Gu = Gu * bGL ((wB : Wd).eval tB)

theorem bridgeFacts_of
    {A B : Mat} (hA : Rep bMat A bA₁) (hB : Rep bMat B bA₂)
    {rels : List (List (ℕ × Bool))}
    (h : bChecks A B (regRun 4370 bN bProg A B).1 (regRun 4370 bN bProg A B).2 rels = true) :
    BridgeFacts rels := by
  have hf := bMat_injective
  unfold bChecks at h
  dsimp only at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hflag, hinv⟩, hrels⟩, hgA⟩, hgB⟩, hconj⟩ := h
  have hR := regRun_rep (f := bMat) bN bProg bProg_lt hA hB hflag
  set T : Array Mat := Array.ofFn (n := 11) fun k =>
      (regRun 4370 bN bProg A B).1.getD (bTreg k.1) #[] with hTdef
  have hT : ∀ k < 11, Rep bMat (T.getD k #[]) (tB k) := by
    intro k hk
    have e : T.getD k #[] = (regRun 4370 bN bProg A B).1.getD (bTreg k) #[] := by
      simp [hTdef, Array.getD_eq_getD_getElem?, hk]
    rw [e]
    exact hR (bTreg k) (bTreg_lt k hk)
  have hinv' : ∀ i < 11, tB i * tB i = 1 := by
    intro i hi
    have := (List.all_eq_true.1 hinv) i (List.mem_range.2 hi)
    exact eq_of_rep hf (rep_mul (hT i hi) (hT i hi)) rep_one this
  refine ⟨hinv', ?_, ?_⟩
  · exact rels_of_relsOK hf hT hinv' hrels
  · have ra := rep_wd (f := bMat) hT wA hgA
    have rb := rep_wd (f := bMat) hT wB hgB
    obtain ⟨G, Gi, h1, h2, h3⟩ := conj_facts ra.1 rb.1 hconj
    have hAc : cmat 4370 A = genA₁ := by rw [hA.2, bMat_bA₁]
    have hBc : cmat 4370 B = genA₂ := by rw [hB.2, bMat_bA₂]
    rw [hAc, ra.2] at h1
    rw [hBc, rb.2] at h2
    refine ⟨⟨G, Gi, h3, mul_eq_one_comm.1 h3⟩, Units.ext ?_, Units.ext ?_⟩
    · simpa [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, coe_bGL] using h1
    · simpa [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, coe_bGL] using h2

theorem conj_words {T : ℕ → NativeSporadic.B}
    (hinv : ∀ i < 11, T i * T i = 1) {Gu : GL (Fin 4370) (ZMod 2)}
    (hA : glA₁ * Gu = Gu * bGL (CFSG.KC.BM.B9201.apT T))
    (hB : glA₂ * Gu =
      Gu * bGL ((CFSG.KC.BM.B9201.hT T)⁻¹ * (T 0 * T 1) * CFSG.KC.BM.B9201.hT T)) :
    glA₁ * Gu = Gu * bGL ((wA : Wd).eval T) ∧ glA₂ * Gu = Gu * bGL ((wB : Wd).eval T) := by
  have i : ∀ k < 11, (T k)⁻¹ = T k := fun k hk => inv_eq_of_mul_eq_one_right (hinv k hk)
  have eA : (wA : Wd).eval T = CFSG.KC.BM.B9201.apT T := wA_eval T
  have eB : (wB : Wd).eval T =
      (CFSG.KC.BM.B9201.hT T)⁻¹ * (T 0 * T 1) * CFSG.KC.BM.B9201.hT T := wB_eval i
  rw [eA, eB]
  exact ⟨hA, hB⟩

theorem bridgeFacts :
    BridgeFacts pres.relatorLetters := by
  obtain ⟨hinv, hrels, Gu, hA, hB⟩ :=
    R9201.bridge_gen (T := tB) (fun k _ => R9201.bMat_runG k) Certificates.certificate9201
  exact ⟨hinv, hrels, Gu, conj_words hinv hA hB⟩

noncomputable def φ :
    pres.Group →* NativeSporadic.B := presHom pres tB bridgeFacts.rels

theorem generatorCount_eq : pres.generatorCount = 11 := rfl

theorem tB_mem_range
    (k : ℕ) (hk : k < 11) : tB k ∈ φ.range :=
  ⟨presGen pres k, presHom_presGen pres tB bridgeFacts.rels (by rw [generatorCount_eq]; exact hk)⟩

theorem eval_mem_range :
    ∀ w : Wd, w.gensLt 11 = true → w.eval tB ∈ φ.range
  | .gen i, h => by
    simp only [Wd.gensLt, decide_eq_true_eq] at h
    exact tB_mem_range i h
  | .mul u v, h => by
    simp only [Wd.gensLt, Bool.and_eq_true] at h
    exact mul_mem (eval_mem_range u h.1) (eval_mem_range v h.2)
  | .pow u e, h => by
    simp only [Wd.gensLt] at h
    exact pow_mem (eval_mem_range u h) e

theorem wA_lt : wA.gensLt 11 = true := by decide +kernel

theorem wB_lt : wB.gensLt 11 = true := by decide +kernel

theorem bGL_injective : Function.Injective bGL := by
  intro x y h
  apply bMat_injective
  have := congrArg (fun g : GL (Fin 4370) (ZMod 2) => (g : Matrix (Fin 4370) (Fin 4370) (ZMod 2))) h
  simpa [coe_bGL] using this

theorem range_bGL :
    bGL.range = Subgroup.closure ({glA₁, glA₂} : Set (GL (Fin 4370) (ZMod 2))) := by
  rw [MonoidHom.range_eq_map, ← closure_bA_eq_top, MonoidHom.map_closure, Set.image_pair,
    bGL_bA₁, bGL_bA₂]

theorem range_eq_top :
    φ.range = ⊤ := by
  obtain ⟨Gu, hA, hB⟩ := bridgeFacts.conj
  let c : GL (Fin 4370) (ZMod 2) →* GL (Fin 4370) (ZMod 2) := (MulAut.conj Gu⁻¹).toMonoidHom
  have hc : ∀ g, c g = Gu⁻¹ * g * Gu := fun g => by simp [c]
  have hmap : bGL.range.map c ≤ φ.range.map bGL := by
    rw [range_bGL, MonoidHom.map_closure, Set.image_pair, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · refine ⟨_, eval_mem_range wA wA_lt, ?_⟩
      rw [hc, mul_assoc, hA, ← mul_assoc, inv_mul_cancel, one_mul]
    · refine ⟨_, eval_mem_range wB wB_lt, ?_⟩
      rw [hc, mul_assoc, hB, ← mul_assoc, inv_mul_cancel, one_mul]
  have hle : φ.range.map bGL ≤ bGL.range := by
    rintro _ ⟨x, -, rfl⟩
    exact ⟨x, rfl⟩
  have hinj : Function.Injective c := (MulAut.conj Gu⁻¹).injective
  have heq : φ.range.map bGL = bGL.range := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [← Subgroup.card_map_of_injective hinj]
    exact Subgroup.card_le_of_le hmap
  rw [eq_top_iff]
  intro x _
  have hx : bGL x ∈ φ.range.map bGL := by
    rw [heq]
    exact ⟨x, rfl⟩
  obtain ⟨y, hy, hyx⟩ := hx
  rwa [← bGL_injective hyx]

theorem φ_surjective :
    Function.Surjective φ := MonoidHom.range_eq_top.1 range_eq_top

theorem nonempty_mulEquiv_of_card_le
    (hfin : Finite TauCeti.SporadicName.B.Group)
    (hcard : Nat.card TauCeti.SporadicName.B.Group ≤ 4154781481226426191177580544000000) :
    Nonempty (CFSG.Blueprint.NativeSporadic.B ≃* TauCeti.SporadicName.B.Group) := by
  revert hfin hcard
  show Finite SporadicName.B.presentation.Group →
    Nat.card SporadicName.B.presentation.Group ≤ 4154781481226426191177580544000000 →
    Nonempty (Blueprint.NativeSporadic.B ≃* SporadicName.B.presentation.Group)
  rw [presentation_eq]
  intro hfin hcard
  exact @nonempty_mulEquiv_of_surjective pres.Group NativeSporadic.B _ _ hfin φ φ_surjective _
    hcard card_le_card_B

end CFSG.Sporadic.Bridge.B
