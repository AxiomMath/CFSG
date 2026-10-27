module

public import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Local3
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Check45
public import CFSG.GH74.M12.HypGroup
public import Certificates.Certificate10019
public import Certificates.Certificate8168
public import Certificates.Certificate8169
public import Certificates.Certificate3139
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.GroupTheory.SteinbergBYAlphaTransport
public import CFSG.RankThree.PartTwo.Sec4.StatementsCensus
public import CFSG.RankThree.PartTwo.Sec4.StatementsSporadic
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.RankThree.PartTwo.Sec4.Sporadic.J2

open CFSG.ComponentClassification.J2Cover CFSG.Certificates CFSG.Certificates.Native
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.Monster.B.Mathieu
  CFSG.RankThree.Asc83Table Subgroup CFSG.RankThree.PartTwo.Sec4.Sporadic.SetAction
open scoped commutatorElement

theorem isTwo8A_iff {t : Array ℕ} {g : Equiv.Perm (Fin 315)} (ht : Rep 315 t g) :
    isTwo8A t = true ↔ g ^ 2 ^ 8 = 1 := by
  rw [isTwo8A, eqA_iff (rep_sqIterA_perm ht 8) rep_idA]

theorem elts45 :
    allLt gensCaArr.size (fun k => okA gensCaArr[k]! && commA gensCaArr[k]! xArr) = true ∧
    okA h1Arr = true ∧ eqA 315 (conjA 315 h1Arr xArr) (compA 315 xArr xArr) = true ∧
    okA v1Arr = true ∧ okA v2Arr = true ∧
    allLt gensCvArr.size (fun k => okA gensCvArr[k]!) = true ∧
    allLt gensCvArr.size
      (fun k => commA gensCvArr[k]! v1Arr && commA gensCvArr[k]! v2Arr) = true ∧
    okA hVArr = true ∧ eqA 315 (conjA 315 hVArr v1Arr) v2Arr = true ∧
    eqA 315 (conjA 315 hVArr v2Arr) (compA 315 v1Arr v2Arr) = true ∧
    okA p0Arr = true ∧ validA 315 outerArr = true ∧
    allLt cConj.size (fun k => okA cConj[k]!) = true ∧
    allLt wGens.size (fun k => okA wGens[k]!) = true ∧
    allLt u34Gens.size (fun k => okA u34Gens[k]!) = true ∧
    allLt neGens.size (fun k => okA neGens[k]! && inE 0 (conjA 315 neGens[k]! zArr) &&
      inE 0 (conjA 315 neGens[k]! xArr)) = true ∧
    (!(commA (commutatorA 315 neGens[0]! neGens[1]!) zArr &&
      commA (commutatorA 315 neGens[0]! neGens[1]!) xArr)) = true := by
  have h := Certificates.certificate8169.1.1
  simp only [chkElts45, Bool.and_eq_true, and_assoc] at h
  exact h

theorem enum45 : enumOK 315 gensCaArr keyPts cCa = true ∧ cCa.pts.size = 36 ∧
    enumOK 315 gensNaArr keyPts cNa = true ∧ cNa.pts.size = 72 ∧
    enumOK 315 gensCvArr keyPts cCv = true ∧ cCv.pts.size = 240 ∧
    enumOK 315 gensNVArr keyPts cNV = true ∧ cNV.pts.size = 720 ∧
    enumOK 315 gensNE keyPts cNE = true ∧ cNE.pts.size = 54 ∧
    ([0, 1, 2].all fun k => enumOK 315 (gensS k) keyPts (cS k) && (cS k).pts.size == 64) =
      true := by
  have h := Certificates.certificate8169.1.2.1
  simp only [chkEnum45, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
  exact h

theorem local45 :
    allLt cCa.pts.size (fun k => !(isTwoA cCa.pts[k]!) || inV cCa.pts[k]!) = true ∧
    inCert cCa v1Arr = true ∧ inCert cCa v2Arr = true ∧ commA v1Arr v2Arr = true ∧
    eqA 315 (compA 315 v1Arr v1Arr) (idA 315) = true ∧
    eqA 315 (compA 315 v2Arr v2Arr) (idA 315) = true ∧
    (!(eqA 315 v1Arr (idA 315))) = true ∧ (!(eqA 315 v2Arr (idA 315))) = true ∧
    (!(eqA 315 v1Arr v2Arr)) = true ∧
    o3Sets.size = 3 ∧ setsOK o3Sets 1 = true ∧ b4Sets.size = 4 ∧ setsOK b4Sets 3 = true ∧
    allLt cNa.pts.size (fun k => permutesSets o3Sets cNa.pts[k]! &&
      permutesSets b4Sets cNa.pts[k]! &&
      (!(fixesSets o3Sets cNa.pts[k]! && fixesSets b4Sets cNa.pts[k]!) ||
        eqA 315 cNa.pts[k]! (idA 315))) = true ∧
    allLt gensNaArr.size (fun k => actsBy o3Sets gensNaArr[k]! (sig3.getD k []) &&
      actsBy b4Sets gensNaArr[k]! (sig4.getD k [])) = true ∧
    allLt cNa.pts.size (fun k => !(twoTest gensNaArr cNa.pts[k]!) || inV cNa.pts[k]!) = true ∧
    allLt cNV.pts.size (fun k => !(twoTest gensNVArr cNV.pts[k]!) || inV cNV.pts[k]!) = true ∧
    (eqA 315 (conjA 315 p0Arr (conjA 315 outerArr xArr)) xArr ||
      eqA 315 (conjA 315 p0Arr (conjA 315 outerArr xArr)) (compA 315 xArr xArr)) = true ∧
    allLt cNa.pts.size (fun k =>
      !(twoTest8 gensNaArr (compA 315 cNa.pts[k]! (compA 315 p0Arr outerArr)))) = true := by
  have h := Certificates.certificate8169.1.2.2.1
  simp only [chkLocal45, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
  exact h

theorem chkE0_spec :
    allLt cNZ.pts.size (fun k => !(inE 0 (conjA 315 cNZ.pts[k]! zArr) &&
      inE 0 (conjA 315 cNZ.pts[k]! xArr)) || inCert cNE cNZ.pts[k]!) = true ∧
    allLt cCz.pts.size (fun k => !(commA cCz.pts[k]! xArr) || inE 0 cCz.pts[k]!) = true := by
  have h := Certificates.certificate8169.1.2.2.2.2.2.1
  simp only [chkE0, chkE0N, chkE0C, Bool.and_eq_true] at h
  exact h

theorem ok_h1 : okA h1Arr = true := by obtain ⟨-, h, -⟩ := elts45; exact h

theorem ok_v1 : okA v1Arr = true := by obtain ⟨-, -, -, h, -⟩ := elts45; exact h

theorem ok_v2 : okA v2Arr = true := by obtain ⟨-, -, -, -, h, -⟩ := elts45; exact h

theorem ok_hV : okA hVArr = true := by obtain ⟨-, -, -, -, -, -, -, h, -⟩ := elts45; exact h

theorem ok_p0 : okA p0Arr = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h, -⟩ := elts45; exact h

theorem valid_outer : validA 315 outerArr = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h, -⟩ := elts45; exact h

@[expose] noncomputable def h1J : GJ := eltOf h1Arr ok_h1

@[expose] noncomputable def v1J : GJ := eltOf v1Arr ok_v1

@[expose] noncomputable def v2J : GJ := eltOf v2Arr ok_v2

@[expose] noncomputable def hVJ : GJ := eltOf hVArr ok_hV

@[expose] noncomputable def p0J : GJ := eltOf p0Arr ok_p0

theorem rep_h1 : Rep 315 h1Arr h1J.1 := rep_eltOf _

theorem rep_v1 : Rep 315 v1Arr v1J.1 := rep_eltOf _

theorem rep_v2 : Rep 315 v2Arr v2J.1 := rep_eltOf _

theorem rep_hV : Rep 315 hVArr hVJ.1 := rep_eltOf _

theorem rep_p0 : Rep 315 p0Arr p0J.1 := rep_eltOf _

theorem xJ_ne_one : xJ ≠ 1 := fun h => z_ne_one (by rw [h, commutatorElement_one_left])

theorem h1_conj_x : h1J * xJ * h1J⁻¹ = xJ ^ 2 := by
  obtain ⟨-, -, h, -⟩ := elts45
  exact eq_of_rep (rep_conj rep_h1 (okA_spec ok_h1).1 rep_x)
    (by rw [sq]; exact rep_mul rep_x rep_x) h

theorem gensCa_spec :
    ∀ k < gensCaArr.size, validA 315 gensCaArr[k]! = true ∧ inP gensCaArr[k]! = true := by
  intro k hk
  obtain ⟨h, -⟩ := elts45
  have := allLt_spec h hk
  rw [Bool.and_eq_true] at this
  exact okA_spec this.1

theorem gensCa_comm (k : ℕ) (hk : k < gensCaArr.size) : commA gensCaArr[k]! xArr = true := by
  obtain ⟨h, -⟩ := elts45
  have := allLt_spec h hk
  rw [Bool.and_eq_true] at this
  exact this.2

theorem centralizer_x : centralizer ({xJ} : Set GJ) = subOf gensCaArr :=
  Certificates.certificate8169.2.1 _ rep_x

theorem gensNa_spec :
    ∀ k < gensNaArr.size, validA 315 gensNaArr[k]! = true ∧ inP gensNaArr[k]! = true :=
  spec_push gensCa_spec (okA_spec ok_h1)

theorem gensNa_size : gensNaArr.size = 3 := rfl

theorem normalizer_x : normalizer ((zpowers xJ : Subgroup GJ) : Set GJ) = subOf gensNaArr :=
  normalizer_zpowers_eq x_cube xJ_ne_one centralizer_x gensCa_spec rep_h1 (okA_spec ok_h1).1
    h1_conj_x

theorem card_normalizer_x : Nat.card (normalizer ((zpowers xJ : Subgroup GJ) : Set GJ)) = 72 := by
  rw [normalizer_x, card_subOf (by decide) enum45.2.2.1 gensNa_spec, enum45.2.2.2.1]

theorem gNa_mem (k : ℕ) (hk : k < gensNaArr.size) :
    gElt gensNaArr gensNa_spec k hk ∈ normalizer ((zpowers xJ : Subgroup GJ) : Set GJ) := by
  rw [normalizer_x]
  exact gElt_mem _ _ k hk

theorem v1_sq : v1J * v1J = 1 := by
  obtain ⟨-, -, -, -, h, -⟩ := local45
  exact eq_of_rep (rep_mul rep_v1 rep_v1) rep_one h

theorem v2_sq : v2J * v2J = 1 := by
  obtain ⟨-, -, -, -, -, h, -⟩ := local45
  exact eq_of_rep (rep_mul rep_v2 rep_v2) rep_one h

theorem v12_comm : v1J * v2J = v2J * v1J := by
  obtain ⟨-, -, -, h, -⟩ := local45
  exact (commute_of_commA rep_v1 rep_v2 h).eq

@[expose] noncomputable def VJ : Subgroup GJ := kleinSub v1_sq v2_sq v12_comm

theorem v1_mem_V : v1J ∈ VJ := mem_kleinSub.2 (Or.inr (Or.inl rfl))

theorem v2_mem_V : v2J ∈ VJ := mem_kleinSub.2 (Or.inr (Or.inr (Or.inl rfl)))

theorem v1_ne_one : v1J ≠ 1 := by
  obtain ⟨-, -, -, -, -, -, h, -⟩ := local45
  intro he
  have h1 : eqA 315 v1Arr (idA 315) = true := (eqA_iff rep_v1 rep_one).2 (by rw [he])
  rw [h1] at h
  exact Bool.noConfusion h

theorem isPGroup_V : IsPGroup 2 VJ := isPGroup_kleinSub

theorem inV_spec {t : Array ℕ} {g : GJ} (ht : Rep 315 t g.1) (h : inV t = true) : g ∈ VJ := by
  simp only [inV, Bool.or_eq_true] at h
  rcases h with ((h | h) | h) | h
  · exact mem_kleinSub.2 (Or.inl (eq_of_rep ht rep_one h))
  · exact mem_kleinSub.2 (Or.inr (Or.inl (eq_of_rep ht rep_v1 h)))
  · exact mem_kleinSub.2 (Or.inr (Or.inr (Or.inl (eq_of_rep ht rep_v2 h))))
  · exact mem_kleinSub.2 (Or.inr (Or.inr (Or.inr (eq_of_rep ht (rep_mul rep_v1 rep_v2) h))))

theorem V_le_C : VJ ≤ centralizer ({xJ} : Set GJ) := by
  obtain ⟨-, h1, h2, -⟩ := local45
  have hv1 : v1J ∈ centralizer ({xJ} : Set GJ) := by
    rw [centralizer_x]; exact mem_of_inCert enum45.1 rep_v1 h1
  have hv2 : v2J ∈ centralizer ({xJ} : Set GJ) := by
    rw [centralizer_x]; exact mem_of_inCert enum45.1 rep_v2 h2
  intro g hg
  rcases mem_kleinSub.1 hg with h | h | h | h <;> rw [h]
  · exact one_mem _
  · exact hv1
  · exact hv2
  · exact mul_mem hv1 hv2

theorem mem_V_of_two {g : GJ} (hg : g ∈ centralizer ({xJ} : Set GJ)) (h2 : g ^ 2 ^ 7 = 1) :
    g ∈ VJ := by
  rw [centralizer_x] at hg
  obtain ⟨k, hk, hr⟩ := exists_rep_subOf (by decide) enum45.1 hg
  obtain ⟨h, -⟩ := local45
  have hck := allLt_spec h hk
  rw [Bool.or_eq_true, Bool.not_eq_true'] at hck
  rcases hck with h' | h'
  · rw [(isTwoA_iff hr).2 h2] at h'
    exact absurd h' Bool.noConfusion
  · exact inV_spec hr h'

theorem conj_mem_V {n : GJ} (hn : n ∈ normalizer ((zpowers xJ : Subgroup GJ) : Set GJ)) {v : GJ}
    (hv : v ∈ VJ) : n * v * n⁻¹ ∈ VJ := by
  refine mem_V_of_two (conj_mem_centralizer_of_mem_normalizer hn (V_le_C hv)) (pow128 ⟨1, ?_⟩)
  rw [pow_one, sq, show n * v * n⁻¹ * (n * v * n⁻¹) = n * (v * v) * n⁻¹ by group,
    mul_self_of_mem_kleinSub hv, mul_one, mul_inv_cancel]

theorem normal_V_in {H : Subgroup GJ}
    (hH : H ≤ normalizer ((zpowers xJ : Subgroup GJ) : Set GJ)) : (VJ.subgroupOf H).Normal := by
  constructor
  intro v hv c
  rw [mem_subgroupOf] at hv ⊢
  exact conj_mem_V (hH c.2) hv

theorem V_le_N : VJ ≤ normalizer ((zpowers xJ : Subgroup GJ) : Set GJ) :=
  V_le_C.trans (centralizer_le_normalizer_zpowers' xJ)

theorem pCore_centralizer_x : inSubgroup (CFSG.pCore 2) (centralizer ({xJ} : Set GJ)) = VJ :=
  inSubgroup_pCore_eq V_le_C (normal_V_in (centralizer_le_normalizer_zpowers' xJ)) isPGroup_V
    fun w hw => by
      obtain ⟨hwH, h2⟩ := two_of_mem_inSubgroup_pCore hw
      exact mem_V_of_two hwH (pow128 h2)

theorem twoTest_of {ns : Array (Array ℕ)}
    (hns : ∀ k < ns.size, validA 315 ns[k]! = true ∧ inP ns[k]! = true) {t : Array ℕ} {w : GJ}
    (ht : Rep 315 t w.1) (h1 : ∃ k, w ^ 2 ^ k = 1)
    (h2 : ∀ k (hk : k < ns.size),
      ∃ m, (w * (gElt ns hns k hk * w * (gElt ns hns k hk)⁻¹)) ^ 2 ^ m = 1) :
    twoTest ns t = true := by
  rw [twoTest, Bool.and_eq_true, Array.all_eq_true]
  refine ⟨(isTwoA_iff ht).2 (pow128 h1), fun k hk => ?_⟩
  have hr : Rep 315 ns[k] (gElt ns hns k hk).1 := by
    have := rep_gElt ns hns k hk
    rwa [getElem!_pos ns k hk] at this
  have hv : validA 315 ns[k] = true := by
    have := (hns k hk).1
    rwa [getElem!_pos ns k hk] at this
  exact (isTwoA_iff (rep_mul ht (rep_conj hr hv ht))).2 (pow128 (h2 k hk))

theorem mem_V_of_T {w : GJ} (hw : w ∈ normalizer ((zpowers xJ : Subgroup GJ) : Set GJ))
    (h2 : ∃ k, w ^ 2 ^ k = 1)
    (h3 : ∀ n ∈ normalizer ((zpowers xJ : Subgroup GJ) : Set GJ),
      ∃ k, (w * (n * w * n⁻¹)) ^ 2 ^ k = 1) : w ∈ VJ := by
  rw [normalizer_x] at hw
  obtain ⟨i, hi, hr⟩ := exists_rep_subOf (by decide) enum45.2.2.1 hw
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := local45
  have hck := allLt_spec h hi
  rw [Bool.or_eq_true, Bool.not_eq_true'] at hck
  rcases hck with h' | h'
  · rw [twoTest_of gensNa_spec hr h2 (fun k hk => h3 _ (gNa_mem k hk))] at h'
    exact absurd h' Bool.noConfusion
  · exact inV_spec hr h'

theorem pCore_normalizer_x :
    inSubgroup (CFSG.pCore 2) (normalizer ((zpowers xJ : Subgroup GJ) : Set GJ)) = VJ :=
  inSubgroup_pCore_eq V_le_N (normal_V_in le_rfl) isPGroup_V fun w hw => by
    obtain ⟨hwN, h2, h3⟩ := T_test hw
    exact mem_V_of_T hwN h2 h3

theorem o3_size : o3Sets.size = 3 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h, -⟩ := local45; exact h

theorem o3_ok : setsOK o3Sets 1 = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h, -⟩ := local45; exact h

theorem b4_size : b4Sets.size = 4 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h, -⟩ := local45; exact h

theorem b4_ok : setsOK b4Sets 3 = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := local45; exact h

theorem Na_sets : allLt cNa.pts.size (fun k => permutesSets o3Sets cNa.pts[k]! &&
      permutesSets b4Sets cNa.pts[k]! &&
      (!(fixesSets o3Sets cNa.pts[k]! && fixesSets b4Sets cNa.pts[k]!) ||
        eqA 315 cNa.pts[k]! (idA 315))) = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := local45; exact h

theorem Na_acts : allLt gensNaArr.size (fun k => actsBy o3Sets gensNaArr[k]! (sig3.getD k []) &&
      actsBy b4Sets gensNaArr[k]! (sig4.getD k [])) = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := local45; exact h

@[expose] def famO3 : Fin 3 → Finset (Fin 315) := famOf o3Sets o3_size

@[expose] def famB4 : Fin 4 → Finset (Fin 315) := famOf b4Sets b4_size

theorem famO3_injective : Function.Injective famO3 := famOf_injective _ o3_ok

theorem famB4_injective : Function.Injective famB4 := famOf_injective _ b4_ok

theorem image_famO3 : ∀ h ∈ normalizer ((zpowers xJ : Subgroup GJ) : Set GJ), ∀ i, ∃ j,
    (famO3 i).image ((CFSG.ComponentClassification.J2Cover.P).subtype h) = famO3 j := by
  intro h hh i
  rw [normalizer_x] at hh
  obtain ⟨k, hk, hr⟩ := exists_rep_subOf (by decide) enum45.2.2.1 hh
  have hck := allLt_spec Na_sets hk
  simp only [Bool.and_eq_true] at hck
  exact image_famOf o3_size o3_ok hr hck.1.1 i

theorem image_famB4 : ∀ h ∈ normalizer ((zpowers xJ : Subgroup GJ) : Set GJ), ∀ i, ∃ j,
    (famB4 i).image ((CFSG.ComponentClassification.J2Cover.P).subtype h) = famB4 j := by
  intro h hh i
  rw [normalizer_x] at hh
  obtain ⟨k, hk, hr⟩ := exists_rep_subOf (by decide) enum45.2.2.1 hh
  have hck := allLt_spec Na_sets hk
  simp only [Bool.and_eq_true] at hck
  exact image_famOf b4_size b4_ok hr hck.1.2 i

@[expose] noncomputable def act3 :
    normalizer ((zpowers xJ : Subgroup GJ) : Set GJ) →* Equiv.Perm (Fin 3) :=
  setAct famO3_injective image_famO3

@[expose] noncomputable def act4 :
    normalizer ((zpowers xJ : Subgroup GJ) : Set GJ) →* Equiv.Perm (Fin 4) :=
  setAct famB4_injective image_famB4

@[expose] noncomputable def rhoN :
    normalizer ((zpowers xJ : Subgroup GJ) : Set GJ) →* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 4) :=
  act3.prod act4

theorem rhoN_injective : Function.Injective rhoN := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  rintro ⟨g, hg⟩ hk
  rw [MonoidHom.mem_ker, rhoN, MonoidHom.prod_apply, Prod.mk_eq_one] at hk
  have h3 := (mem_ker_setAct famO3_injective image_famO3).1 (MonoidHom.mem_ker.2 hk.1)
  have h4 := (mem_ker_setAct famB4_injective image_famB4).1 (MonoidHom.mem_ker.2 hk.2)
  have hg' := hg
  rw [normalizer_x] at hg'
  obtain ⟨k, hk', hr⟩ := exists_rep_subOf (by decide) enum45.2.2.1 hg'
  have hck := allLt_spec Na_sets hk'
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hck
  have hf : (fixesSets o3Sets cNa.pts[k]! && fixesSets b4Sets cNa.pts[k]!) = true := by
    rw [fixesSets_of_image o3_size o3_ok hr h3, fixesSets_of_image b4_size b4_ok hr h4]
    rfl
  rcases hck.2 with h1 | h1
  · rw [hf] at h1
    exact absurd h1 Bool.noConfusion
  · exact Subgroup.mem_bot.2 (Subtype.ext (eq_of_rep hr rep_one h1))

theorem act4_gen (k : ℕ) (hk : k < gensNaArr.size)
    (hm : gElt gensNaArr gensNa_spec k hk ∈ normalizer ((zpowers xJ : Subgroup GJ) : Set GJ)) :
    ∀ i, act4 ⟨gElt gensNaArr gensNa_spec k hk, hm⟩ i =
      listFun 4 (by norm_num) (sig4.getD k []) i := by
  intro i
  have hk3 : k < 3 := lt_of_lt_of_eq hk gensNa_size
  have hl : ∀ i < 4, (sig4.getD k []).getD i 0 < 4 := by
    interval_cases k <;> decide
  have hact := allLt_spec Na_acts hk
  rw [Bool.and_eq_true] at hact
  rw [act4, setAct_eq_of_image famB4_injective image_famB4 (h := ⟨_, hm⟩) (σ := Equiv.ofBijective
      (listFun 4 (by norm_num) (sig4.getD k []))
      ((Finite.injective_iff_bijective).1 (by interval_cases k <;> decide)))
    (fun j => image_actsBy b4_size b4_ok (rep_elA (gensNa_spec k hk)) hl hact.2 j)]
  rfl

theorem sig4_even : ∀ k < 3, ∃ σ : Equiv.Perm (Fin 4), σ ∈ alternatingGroup (Fin 4) ∧
    ∀ i, σ i = listFun 4 (by norm_num) (sig4.getD k []) i := by
  intro k hk
  interval_cases k
  · exact ⟨List.formPerm [0, 2, 3], by rw [Equiv.Perm.mem_alternatingGroup]; decide,
      by decide⟩
  · exact ⟨Equiv.swap 0 3 * Equiv.swap 1 2, by rw [Equiv.Perm.mem_alternatingGroup]; decide,
      by decide⟩
  · exact ⟨List.formPerm [0, 3, 2], by rw [Equiv.Perm.mem_alternatingGroup]; decide,
      by decide⟩

theorem range_rhoN_le :
    rhoN.range ≤ (⊤ : Subgroup (Equiv.Perm (Fin 3))).prod (alternatingGroup (Fin 4)) := by
  refine range_le_of_closure (by rw [normalizer_x, subOf_eq_closure_gElt gensNaArr gensNa_spec])
    rhoN _ ?_
  rintro _ ⟨k, hk, rfl⟩
  obtain ⟨σ, hσ, hσk⟩ := sig4_even k (lt_of_lt_of_eq hk gensNa_size)
  rw [Subgroup.mem_prod]
  refine ⟨Subgroup.mem_top _, ?_⟩
  show act4 _ ∈ alternatingGroup (Fin 4)
  convert hσ using 1
  ext i
  rw [act4_gen k hk _ i, ← hσk i]

theorem card_range_rhoN : Nat.card rhoN.range = 72 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective rhoN_injective).toEquiv, card_normalizer_x]

theorem card_prod_A4 :
    Nat.card ((⊤ : Subgroup (Equiv.Perm (Fin 3))).prod (alternatingGroup (Fin 4))) = 72 := by
  rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, Subgroup.card_top,
    nat_card_alternatingGroup, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin,
    Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem range_rhoN :
    rhoN.range = (⊤ : Subgroup (Equiv.Perm (Fin 3))).prod (alternatingGroup (Fin 4)) :=
  Subgroup.eq_of_le_of_card_ge range_rhoN_le (by rw [card_range_rhoN, card_prod_A4])

theorem normalizer_x_equiv : Nonempty (normalizer ((zpowers xJ : Subgroup GJ) : Set GJ) ≃*
    Equiv.Perm (Fin 3) × alternatingGroup (Fin 4)) :=
  ⟨(MonoidHom.ofInjective rhoN_injective).trans ((MulEquiv.subgroupCongr range_rhoN).trans
    ((Subgroup.prodEquiv _ _).trans (MulEquiv.prodCongr Subgroup.topEquiv (MulEquiv.refl _))))⟩

theorem gensCv_spec :
    ∀ k < gensCvArr.size, validA 315 gensCvArr[k]! = true ∧ inP gensCvArr[k]! = true := by
  intro k hk
  obtain ⟨-, -, -, -, -, h, -⟩ := elts45
  exact okA_spec (allLt_spec h hk)

theorem gensCv_comm (k : ℕ) (hk : k < gensCvArr.size) :
    commA gensCvArr[k]! v1Arr = true ∧ commA gensCvArr[k]! v2Arr = true := by
  obtain ⟨-, -, -, -, -, -, h, -⟩ := elts45
  have := allLt_spec h hk
  rwa [Bool.and_eq_true] at this

theorem centralizer_v1 : centralizer ({v1J} : Set GJ) = subOf gensCvArr :=
  Certificates.certificate8169.2.2 _ rep_v1

theorem centralizer_v1_le : centralizer ({v1J} : Set GJ) ≤ centralizer ({v2J} : Set GJ) := by
  rw [centralizer_v1]
  refine subOf_le_of gensCvArr gensCv_spec fun k hk => ?_
  rw [mem_centralizer_singleton_iff]
  exact (commute_of_commA (rep_gElt _ _ k hk) rep_v2 (gensCv_comm k hk).2).eq

theorem hV_v1 : hVJ * v1J * hVJ⁻¹ = v2J := by
  obtain ⟨-, -, -, -, -, -, -, -, h, -⟩ := elts45
  exact eq_of_rep (rep_conj rep_hV (okA_spec ok_hV).1 rep_v1) rep_v2 h

theorem hV_v2 : hVJ * v2J * hVJ⁻¹ = v1J * v2J := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h, -⟩ := elts45
  exact eq_of_rep (rep_conj rep_hV (okA_spec ok_hV).1 rep_v2) (rep_mul rep_v1 rep_v2) h

theorem mem_normalizer_V_of {g : GJ} {a b : GJ} (ha : g * v1J * g⁻¹ = a)
    (hb : g * v2J * g⁻¹ = b) (ha' : a ∈ VJ) (hb' : b ∈ VJ) :
    g ∈ normalizer ((VJ : Subgroup GJ) : Set GJ) := by
  refine mem_normalizer_of_conj_mem fun v hv => ?_
  rcases mem_kleinSub.1 hv with h | h | h | h <;> rw [h]
  · rw [mul_one, mul_inv_cancel]; exact one_mem _
  · rw [ha]; exact ha'
  · rw [hb]; exact hb'
  · rw [show g * (v1J * v2J) * g⁻¹ = (g * v1J * g⁻¹) * (g * v2J * g⁻¹) by group, ha, hb]
    exact mul_mem ha' hb'

theorem hV_mem_normalizer : hVJ ∈ normalizer ((VJ : Subgroup GJ) : Set GJ) :=
  mem_normalizer_V_of hV_v1 hV_v2 v2_mem_V (mul_mem v1_mem_V v2_mem_V)

theorem gensNV_spec :
    ∀ k < gensNVArr.size, validA 315 gensNVArr[k]! = true ∧ inP gensNVArr[k]! = true :=
  spec_push gensCv_spec (okA_spec ok_hV)

theorem normalizer_V : normalizer ((VJ : Subgroup GJ) : Set GJ) = subOf gensNVArr := by
  have hle := subOf_le_push gensCvArr hVArr
  have hmV : hVJ ∈ subOf gensNVArr := mem_subOf_push_last rep_hV (okA_spec ok_hV).1
  apply le_antisymm
  · intro g hg
    have hv1 : g * v1J * g⁻¹ ∈ VJ := (mem_normalizer_iff.mp hg v1J).mp v1_mem_V
    have hne : g * v1J * g⁻¹ ≠ 1 := fun h => v1_ne_one (by
      have : g * v1J * g⁻¹ = g * 1 * g⁻¹ := by rw [h, mul_one, mul_inv_cancel]
      exact mul_right_cancel (mul_left_cancel this))
    rcases mem_kleinSub.1 hv1 with h | h | h | h
    · exact absurd h hne
    · apply hle
      rw [← centralizer_v1, mem_centralizer_singleton_iff]
      calc g * v1J = g * v1J * g⁻¹ * g := by group
        _ = v1J * g := by rw [h]
    · have hc : hVJ⁻¹ * g ∈ centralizer ({v1J} : Set GJ) := by
        rw [mem_centralizer_singleton_iff]
        have h2 : hVJ⁻¹ * v2J * hVJ = v1J := by rw [← hV_v1]; group
        calc hVJ⁻¹ * g * v1J = hVJ⁻¹ * (g * v1J * g⁻¹) * g := by group
          _ = hVJ⁻¹ * v2J * hVJ * (hVJ⁻¹ * g) := by rw [h]; group
          _ = v1J * (hVJ⁻¹ * g) := by rw [h2]
      have := (subOf gensNVArr).mul_mem hmV (hle (centralizer_v1 ▸ hc))
      rwa [mul_inv_cancel_left] at this
    · have hc : (hVJ * hVJ)⁻¹ * g ∈ centralizer ({v1J} : Set GJ) := by
        rw [mem_centralizer_singleton_iff]
        have h2 : (hVJ * hVJ)⁻¹ * (v1J * v2J) * (hVJ * hVJ) = v1J := by
          rw [← hV_v2, ← hV_v1]; group
        calc (hVJ * hVJ)⁻¹ * g * v1J = (hVJ * hVJ)⁻¹ * (g * v1J * g⁻¹) * g := by group
          _ = (hVJ * hVJ)⁻¹ * (v1J * v2J) * (hVJ * hVJ) * ((hVJ * hVJ)⁻¹ * g) := by
            rw [h]; group
          _ = v1J * ((hVJ * hVJ)⁻¹ * g) := by rw [h2]
      have := (subOf gensNVArr).mul_mem ((subOf gensNVArr).mul_mem hmV hmV)
        (hle (centralizer_v1 ▸ hc))
      rwa [mul_inv_cancel_left] at this
  · refine subOf_push_le gensCv_spec rep_hV (okA_spec ok_hV).1 ?_ hV_mem_normalizer
    rw [← centralizer_v1]
    intro g hg
    have hc1 : g * v1J * g⁻¹ = v1J := by
      rw [mem_centralizer_singleton_iff.1 hg, mul_inv_cancel_right]
    have hc2 : g * v2J * g⁻¹ = v2J := by
      rw [mem_centralizer_singleton_iff.1 (centralizer_v1_le hg), mul_inv_cancel_right]
    exact mem_normalizer_V_of hc1 hc2 v1_mem_V v2_mem_V

theorem pCore_normalizer_V :
    inSubgroup (CFSG.pCore 2) (normalizer ((VJ : Subgroup GJ) : Set GJ)) = VJ := by
  refine inSubgroup_pCore_eq le_normalizer (Subgroup.normal_in_normalizer) isPGroup_V
    fun w hw => ?_
  obtain ⟨hwN, h2, h3⟩ := T_test hw
  rw [normalizer_V] at hwN
  obtain ⟨i, hi, hr⟩ := exists_rep_subOf (by decide) enum45.2.2.2.2.2.2.1 hwN
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := local45
  have hck := allLt_spec h hi
  rw [Bool.or_eq_true, Bool.not_eq_true'] at hck
  rcases hck with h' | h'
  · rw [twoTest_of gensNV_spec hr h2 (fun k hk => h3 _ (by
      rw [normalizer_V]; exact gElt_mem _ _ k hk))] at h'
    exact absurd h' Bool.noConfusion
  · exact inV_spec hr h'

instance : Finite (MulAut GJ) := finite_mulAut_P

local notation "RJ" => CFSG.ComponentClassification.J2Cover.R

local notation "PJ" => CFSG.ComponentClassification.J2Cover.P

theorem conj_injective_GJ : Function.Injective (MulAut.conj : GJ →* MulAut GJ) := by
  intro g h hgh
  have hc : h⁻¹ * g ∈ Subgroup.center GJ := by
    rw [Subgroup.mem_center_iff]
    intro k
    have := congrArg (fun α : MulAut GJ => α k) hgh
    simp only [MulAut.conj_apply] at this
    calc k * (h⁻¹ * g) = h⁻¹ * (h * k * h⁻¹) * g := by group
      _ = h⁻¹ * (g * k * g⁻¹) * g := by rw [this]
      _ = h⁻¹ * g * k := by group
  rw [center_P, Subgroup.mem_bot] at hc
  calc g = h * (h⁻¹ * g) := by group
    _ = h := by rw [hc, mul_one]

theorem rConj_eq_conj {r : RJ} (hr : (r : Equiv.Perm (Fin 315)) ∈ PJ) :
    rConj r = MulAut.conj (⟨r, hr⟩ : GJ) := by
  refine MulEquiv.ext fun g => Subtype.ext ?_
  rw [rConj_apply, MulAut.conj_apply]
  rfl

theorem apply_mem_zpowers_of_mem_normalizer {α : MulAut GJ} {g : GJ}
    (hα : α ∈ normalizer ((zpowers (MulAut.conj g) : Subgroup (MulAut GJ)) : Set (MulAut GJ))) :
    α g ∈ zpowers g := by
  have h := (mem_normalizer_iff.mp hα (MulAut.conj g)).mp (mem_zpowers _)
  rw [mulAut_mul_conj] at h
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp h
  rw [← map_zpow] at hk
  exact mem_zpowers_iff.2 ⟨k, conj_injective_GJ hk⟩

theorem inv_apply_mem_zpowers {φ : MulAut GJ} {g : GJ} (h : φ g ∈ zpowers g) :
    φ⁻¹ g ∈ zpowers g := by
  have hle : (zpowers g).map φ.toMonoidHom ≤ zpowers g := by
    rw [MonoidHom.map_zpowers, zpowers_le]
    exact h
  have heq : (zpowers g).map φ.toMonoidHom = zpowers g :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Subgroup.card_map_of_injective φ.injective])
  have hg : g ∈ (zpowers g).map φ.toMonoidHom := by rw [heq]; exact mem_zpowers g
  obtain ⟨y, hy, hyg⟩ := hg
  have : φ⁻¹ g = y := by
    rw [← hyg]
    show φ⁻¹ (φ y) = y
    exact MulAut.inv_apply_self _ φ y
  rw [this]
  exact hy

theorem p0_conj : (p0J.1 * permU) * xJ.1 * (p0J.1 * permU)⁻¹ = xJ.1 ∨
    (p0J.1 * permU) * xJ.1 * (p0J.1 * permU)⁻¹ = (xJ * xJ).1 := by
  have hu : Rep 315 (conjA 315 outerArr xArr) (permU * xJ.1 * permU⁻¹) :=
    rep_conj_perm rep_permU valid_outer rep_x
  have hp : Rep 315 (conjA 315 p0Arr (conjA 315 outerArr xArr))
      (p0J.1 * (permU * xJ.1 * permU⁻¹) * p0J.1⁻¹) :=
    rep_conj_perm rep_p0 (okA_spec ok_p0).1 hu
  have e : (p0J.1 * permU) * xJ.1 * (p0J.1 * permU)⁻¹ =
      p0J.1 * (permU * xJ.1 * permU⁻¹) * p0J.1⁻¹ := by group
  rw [e]
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := local45
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · exact Or.inl (eq_of_eqA hp rep_x h)
  · exact Or.inr (eq_of_eqA hp (rep_mul rep_x rep_x) h)

theorem twoTest8_of {ns : Array (Array ℕ)} (hns : ∀ k < ns.size, validA 315 ns[k]! = true)
    {t : Array ℕ} {w : Equiv.Perm (Fin 315)} (ht : Rep 315 t w) (h1 : w ^ 2 ^ 8 = 1)
    (h2 : ∀ k < ns.size,
      (w * (permOfArr 315 ns[k]! * w * (permOfArr 315 ns[k]!)⁻¹)) ^ 2 ^ 8 = 1) :
    twoTest8 ns t = true := by
  rw [twoTest8, Bool.and_eq_true, Array.all_eq_true]
  refine ⟨(isTwo8A_iff ht).2 h1, fun k hk => ?_⟩
  have hv : validA 315 ns[k] = true := by
    have := hns k hk
    rwa [getElem!_pos ns k hk] at this
  rw [isTwo8A_iff (rep_compA ht (rep_conjA hv ht))]
  have := h2 k hk
  rwa [getElem!_pos ns k hk] at this

theorem pow256_R {r : RJ} (h : ∃ k, r ^ 2 ^ k = 1) : (r : Equiv.Perm (Fin 315)) ^ 2 ^ 8 = 1 := by
  have := pow_two_pow_eq_one (G := RJ) (N := 8) (by rw [card_R]; norm_num) h
  have := congrArg Subtype.val this
  simpa using this

theorem outer_not_mem {Y : Subgroup (MulAut GJ)} (hY2 : IsPGroup 2 Y)
    (hYA : (normalizer ((zpowers xJ : Subgroup GJ) : Set GJ)).map
      (MulAut.conj : GJ →* MulAut GJ) ≤ normalizer (Y : Set (MulAut GJ)))
    {r : RJ} (hr : (r : Equiv.Perm (Fin 315)) ∉ PJ) (hα : rAutEquiv r ∈ Y)
    (hαx : rAutEquiv r xJ ∈ zpowers xJ) : False := by
  have hrU : (r : Equiv.Perm (Fin 315)) * permU ∈ PJ := ((mem_R_iff _).1 r.2).resolve_left hr
  have hq : p0J.1 * permU ∈ RJ := Subgroup.mul_mem _ (P_le_R p0J.2) permU_mem_R
  set q : RJ := ⟨p0J.1 * permU, hq⟩
  have hβ : rAutEquiv q xJ ∈ zpowers xJ := by
    have hval : ((rAutEquiv q xJ : GJ) : Equiv.Perm (Fin 315)) =
        (p0J.1 * permU) * xJ.1 * (p0J.1 * permU)⁻¹ := rConj_apply q xJ
    rcases p0_conj with h | h
    · have : rAutEquiv q xJ = xJ := Subtype.ext (hval.trans h)
      rw [this]; exact mem_zpowers _
    · have : rAutEquiv q xJ = xJ * xJ := Subtype.ext (hval.trans h)
      rw [this]; exact mul_mem (mem_zpowers _) (mem_zpowers _)
  have htP : ((r * q⁻¹ : RJ) : Equiv.Perm (Fin 315)) ∈ PJ := by
    have e : ((r * q⁻¹ : RJ) : Equiv.Perm (Fin 315)) =
        (r : Equiv.Perm (Fin 315)) * permU * p0J.1⁻¹ := by
      show (r : Equiv.Perm (Fin 315)) * (p0J.1 * permU)⁻¹ = _
      rw [mul_inv_rev, permU_inv, mul_assoc]
    rw [e]
    exact P.mul_mem hrU (P.inv_mem p0J.2)
  set t : GJ := ⟨_, htP⟩
  have hγ : rAutEquiv (r * q⁻¹) = MulAut.conj t := by
    rw [rAutEquiv_apply]
    exact rConj_eq_conj htP
  have htx : t * xJ * t⁻¹ ∈ zpowers xJ := by
    have h1 : (rAutEquiv r * (rAutEquiv q)⁻¹) xJ ∈ zpowers xJ := by
      rw [MulAut.mul_apply]
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (inv_apply_mem_zpowers hβ)
      rw [← hk, map_zpow]
      exact zpow_mem hαx k
    rw [← map_inv, ← map_mul, hγ, MulAut.conj_apply] at h1
    exact h1
  have htN : t ∈ normalizer ((zpowers xJ : Subgroup GJ) : Set GJ) :=
    mem_normalizer_zpowers_of_mem htx
  rw [normalizer_x] at htN
  obtain ⟨i, hi, hrep⟩ := exists_rep_subOf (by decide) enum45.2.2.1 htN
  have hrt : (r : Equiv.Perm (Fin 315)) = t.1 * (p0J.1 * permU) := by
    show (r : Equiv.Perm (Fin 315)) = ((r * q⁻¹ : RJ) : Equiv.Perm (Fin 315)) * (q : Equiv.Perm _)
    rw [← Subgroup.coe_mul, inv_mul_cancel_right]
  have hrep' : Rep 315 (compA 315 cNa.pts[i]! (compA 315 p0Arr outerArr))
      (r : Equiv.Perm (Fin 315)) := by
    rw [hrt]
    exact rep_compA hrep (rep_compA rep_p0 rep_permU)
  have h2r : ∀ s : RJ, rAutEquiv s ∈ Y → (s : Equiv.Perm (Fin 315)) ^ 2 ^ 8 = 1 := by
    intro s hs
    obtain ⟨k, hk⟩ := two_of_mem hY2 hs
    refine pow256_R ⟨k, rAutEquiv.injective ?_⟩
    rw [map_pow, hk, map_one]
  have hprod : ∀ k (hk : k < gensNaArr.size),
      ((r : Equiv.Perm (Fin 315)) * (permOfArr 315 gensNaArr[k]! * r *
        (permOfArr 315 gensNaArr[k]!)⁻¹)) ^ 2 ^ 8 = 1 := by
    intro k hk
    set n := gElt gensNaArr gensNa_spec k hk
    set n' : RJ := ⟨n.1, P_le_R n.2⟩
    have hn' : rAutEquiv n' = MulAut.conj n := by
      rw [rAutEquiv_apply]
      exact rConj_eq_conj n.2
    have hmem : rAutEquiv r * (MulAut.conj n * rAutEquiv r * (MulAut.conj n)⁻¹) ∈ Y :=
      Y.mul_mem hα ((mem_normalizer_iff.mp (hYA (mem_map_of_mem _ (gNa_mem k hk))) _).mp hα)
    rw [← hn', ← map_inv, ← map_mul, ← map_mul, ← map_mul] at hmem
    have := h2r _ hmem
    rw [permOfArr_gElt gensNaArr gensNa_spec k hk]
    exact this
  have hT := twoTest8_of (fun k hk => (gensNa_spec k hk).1) hrep' (h2r r hα) hprod
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h⟩ := local45
  have hck := allLt_spec h hi
  rw [hT] at hck
  exact Bool.noConfusion hck

theorem V_mem_maxInvariant :
    VJ.map (MulAut.conj : GJ →* MulAut GJ) ∈
      maxInvariantPiSubgroups
        (normalizer ((zpowers (MulAut.conj xJ) : Subgroup (MulAut GJ)) : Set (MulAut GJ)))
        ((normalizer ((zpowers xJ : Subgroup GJ) : Set GJ)).map (MulAut.conj : GJ →* MulAut GJ))
        (piOf 2) := by
  set N := normalizer ((zpowers xJ : Subgroup GJ) : Set GJ)
  have hNV : N ≤ normalizer ((VJ : Subgroup GJ) : Set GJ) := fun n hn =>
    mem_normalizer_of_conj_mem fun v hv => conj_mem_V hn hv
  have hmem : VJ.map (MulAut.conj : GJ →* MulAut GJ) ∈ invariantPiSubgroups
      (normalizer ((zpowers (MulAut.conj xJ) : Subgroup (MulAut GJ)) : Set (MulAut GJ)))
      (N.map (MulAut.conj : GJ →* MulAut GJ)) (piOf 2) := by
    rw [mem_invariantPiSubgroups_piOf_iff Nat.prime_two]
    refine ⟨?_, isPGroup_V.map _, (Subgroup.map_mono hNV).trans (Subgroup.le_normalizer_map _)⟩
    rintro _ ⟨v, hv, rfl⟩
    refine mem_normalizer_zpowers_of_mem ?_
    have hvx : v * xJ * v⁻¹ = xJ := by
      rw [mem_centralizer_singleton_iff.1 (V_le_C hv), mul_inv_cancel_right]
    have e : MulAut.conj (v * xJ * v⁻¹) =
        MulAut.conj v * MulAut.conj xJ * (MulAut.conj v)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    change MulAut.conj v * MulAut.conj xJ * (MulAut.conj v)⁻¹ ∈ _
    rw [← e, hvx]
    exact mem_zpowers _
  rw [mem_maxInvariantPiSubgroups_iff]
  refine ⟨hmem, fun Y hY hle => le_antisymm ?_ hle⟩
  rw [mem_invariantPiSubgroups_piOf_iff Nat.prime_two] at hY
  obtain ⟨hYH, hY2, hYA⟩ := hY
  intro α hα
  have hαx : α xJ ∈ zpowers xJ := apply_mem_zpowers_of_mem_normalizer (hYH hα)
  obtain ⟨r, rfl⟩ := rAutEquiv.surjective α
  by_cases hr : (r : Equiv.Perm (Fin 315)) ∈ PJ
  · set g : GJ := ⟨r, hr⟩
    have hrg : rAutEquiv r = MulAut.conj g := by
      rw [rAutEquiv_apply]
      exact rConj_eq_conj hr
    rw [hrg] at hα hαx ⊢
    have hgN : g ∈ N := mem_normalizer_zpowers_of_mem (by rwa [MulAut.conj_apply] at hαx)
    have h2 : ∀ w : GJ, MulAut.conj w ∈ Y → ∃ k, w ^ 2 ^ k = 1 := by
      intro w hw
      obtain ⟨k, hk⟩ := two_of_mem hY2 hw
      exact ⟨k, conj_injective_GJ (by rw [map_pow, hk, map_one])⟩
    refine mem_map_of_mem _ (mem_V_of_T hgN (h2 g hα) fun n hn => h2 _ ?_)
    have := Y.mul_mem hα ((mem_normalizer_iff.mp (hYA (mem_map_of_mem _ hn)) _).mp hα)
    rwa [← map_inv, ← map_mul, ← map_mul, ← map_mul] at this
  · exact (outer_not_mem hY2 hYA hr hα hαx).elim

theorem neGens_size : neGens.size = 2 := rfl

theorem ne_ok (k : ℕ) (hk : k < neGens.size) : okA neGens[k]! = true ∧
    inE 0 (conjA 315 neGens[k]! zArr) = true ∧ inE 0 (conjA 315 neGens[k]! xArr) = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := elts45
  have := allLt_spec h hk
  simp only [Bool.and_eq_true] at this
  exact ⟨this.1.1, this.1.2, this.2⟩

theorem gensNE_spec :
    ∀ k < gensNE.size, validA 315 gensNE[k]! = true ∧ inP gensNE[k]! = true := by
  intro k hk
  have hk3 : k < 3 := hk
  interval_cases k
  · exact okA_spec elts_spec.1
  · exact okA_spec (ne_ok 0 (by rw [neGens_size]; norm_num)).1
  · exact okA_spec (ne_ok 1 (by rw [neGens_size]; norm_num)).1

noncomputable abbrev E0 : Subgroup GJ := Ej 0

theorem z_mem_E0 : ⁅xJ, yJ⁆ ∈ E0 := subset_closure (Set.mem_insert _ _)

theorem E0_le_P3 : E0 ≤ P3 := by
  have h := Set.mem_range_self (f := Ej) 0
  rw [← nine_eq] at h
  exact h.1

theorem x_mem_E0 : xJ ∈ E0 := subset_closure (Set.mem_insert_of_mem _ rfl)

theorem inE0_of_mem {t : Array ℕ} {g : GJ} (ht : Rep 315 t g.1) (hg : g ∈ E0) :
    inE 0 t = true := by
  obtain ⟨a, c, ha, hc, rfl⟩ :=
    (ex27Basis x_cube y_cube z_comm_x z_comm_y z_ne_one 0).exists_pow_mul_pow hg
  rw [inE, List.any_eq_true]
  refine ⟨a, List.mem_range.2 ha, ?_⟩
  rw [List.any_eq_true]
  refine ⟨c, List.mem_range.2 hc, ?_⟩
  exact (eqA_iff ht (rep_mul (rep_pow rep_z' a) (rep_pow (rep_bArr 0) c))).2 rfl

theorem conj_mem_E0_of_inE {t : Array ℕ} {g : GJ} (ht : Rep 315 t g.1) (hv : validA 315 t = true)
    (hz : inE 0 (conjA 315 t zArr) = true) (hx : inE 0 (conjA 315 t xArr) = true) :
    g ∈ normalizer ((E0 : Subgroup GJ) : Set GJ) := by
  refine mem_normalizer_of_conj_gens ?_
  rintro s (rfl | rfl)
  · exact mem_Ej_of_inE (rep_conj ht hv rep_z') hz
  · exact mem_Ej_of_inE (rep_conj ht hv rep_x) hx

theorem normalizer_E0 : normalizer ((E0 : Subgroup GJ) : Set GJ) = subOf gensNE := by
  apply le_antisymm
  · intro g hg
    have hgZ : g ∈ normalizer ((zpowers zJ : Subgroup GJ) : Set GJ) := by
      have hc : conjugate (zpowers zJ) g⁻¹ ≤ P3 := by
        rintro _ ⟨c, hc, rfl⟩
        have hcE : c ∈ E0 := by
          rw [z_eq] at hc
          exact (zpowers_le.2 z_mem_E0) hc
        have := (mem_normalizer_iff.mp hg c).mp hcE
        exact E0_le_P3 (by simpa using this)
      have hw := weaklyClosed g⁻¹ hc
      refine mem_normalizer_zpowers_of_mem ?_
      have : g * zJ * g⁻¹ ∈ conjugate (zpowers zJ) g⁻¹ := ⟨zJ, mem_zpowers _, by simp⟩
      rwa [hw] at this
    rw [normalizer_Z] at hgZ
    obtain ⟨i, hi, hr⟩ := exists_rep_subOf (by decide) enum_spec.2.2.2.2.1 hgZ
    have hv : validA 315 cNZ.pts[i]! = true :=
      (enumOK_spec (by decide) enum_spec.2.2.2.2.1).2.2 i hi
    have hck := allLt_spec chkE0_spec.1 hi
    rw [Bool.or_eq_true, Bool.not_eq_true'] at hck
    have hz : inE 0 (conjA 315 cNZ.pts[i]! zArr) = true :=
      inE0_of_mem (rep_conj hr hv rep_z') ((mem_normalizer_iff.mp hg _).mp z_mem_E0)
    have hx : inE 0 (conjA 315 cNZ.pts[i]! xArr) = true :=
      inE0_of_mem (rep_conj hr hv rep_x) ((mem_normalizer_iff.mp hg _).mp x_mem_E0)
    rcases hck with h | h
    · rw [hz, hx] at h
      exact absurd h Bool.noConfusion
    · exact mem_of_inCert enum45.2.2.2.2.2.2.2.2.1 hr h
  · refine subOf_le_of gensNE gensNE_spec fun k hk => ?_
    have hk3 : k < 3 := hk
    interval_cases k
    · have e : gElt gensNE gensNE_spec 0 hk = xJ :=
        Subtype.ext ((rep_gElt gensNE gensNE_spec 0 hk).unique rep_x)
      rw [e]
      exact le_normalizer x_mem_E0
    · obtain ⟨hok, hz, hx⟩ := ne_ok 0 (by rw [neGens_size]; norm_num)
      exact conj_mem_E0_of_inE (rep_gElt gensNE gensNE_spec 1 hk) (okA_spec hok).1 hz hx
    · obtain ⟨hok, hz, hx⟩ := ne_ok 1 (by rw [neGens_size]; norm_num)
      exact conj_mem_E0_of_inE (rep_gElt gensNE gensNE_spec 2 hk) (okA_spec hok).1 hz hx

theorem card_normalizer_E0 : Nat.card (normalizer ((E0 : Subgroup GJ) : Set GJ)) = 54 := by
  rw [normalizer_E0, card_subOf (by decide) enum45.2.2.2.2.2.2.2.2.1 gensNE_spec,
    enum45.2.2.2.2.2.2.2.2.2.1]

theorem zJ_mem_E0 : zJ ∈ E0 := by rw [z_eq]; exact z_mem_E0

theorem centralizer_E0 : centralizer ((E0 : Subgroup GJ) : Set GJ) = E0 := by
  apply le_antisymm
  · intro g hg
    have hz : g ∈ centralizer ({zJ} : Set GJ) :=
      mem_centralizer_singleton_iff.2 (mem_centralizer_iff.mp hg _ zJ_mem_E0).symm
    rw [centralizer_z] at hz
    obtain ⟨k, hk, hr⟩ := exists_rep_subOf (by decide) enum_spec.2.2.1 hz
    have hck := allLt_spec chkE0_spec.2 hk
    rw [Bool.or_eq_true, Bool.not_eq_true'] at hck
    have hx : commA cCz.pts[k]! xArr = true :=
      commA_of_commute hr rep_x (mem_centralizer_iff.mp hg _ x_mem_E0).symm
    rcases hck with h | h
    · rw [hx] at h
      exact absurd h Bool.noConfusion
    · exact mem_Ej_of_inE hr h
  · intro g hg
    rw [mem_centralizer_iff]
    intro h hh
    set E := ex27Basis x_cube y_cube z_comm_x z_comm_y z_ne_one 0
    obtain ⟨a, c, -, -, rfl⟩ := E.exists_pow_mul_pow hg
    obtain ⟨a', c', -, -, rfl⟩ := E.exists_pow_mul_pow hh
    have h1 : Commute (E.a ^ a') (E.a ^ a * E.b ^ c) :=
      ((Commute.refl E.a).pow_pow a' a).mul_right (E.hab.pow_pow a' c)
    have h2 : Commute (E.b ^ c') (E.a ^ a * E.b ^ c) :=
      (E.hab.symm.pow_pow c' a).mul_right ((Commute.refl E.b).pow_pow c' c)
    exact (h1.mul_left h2).eq

theorem card_automizer_E0 : Nat.card (Automizer E0) = 6 := by
  have hE : Nat.card E0 = 9 := (ex27Basis x_cube y_cube z_comm_x z_comm_y z_ne_one 0).card
  have hC : Nat.card (centralizer ((E0 : Subgroup GJ) : Set GJ)) = 9 := by
    rw [centralizer_E0]; exact hE
  have h := ((centralizer ((E0 : Subgroup GJ) : Set GJ)).subgroupOf
    (normalizer ((E0 : Subgroup GJ) : Set GJ))).card_eq_card_quotient_mul_card_subgroup
  rw [card_normalizer_E0,
    Nat.card_congr (subgroupOfEquivOfLe (centralizer_le_normalizer _)).toEquiv, hC] at h
  change 54 = Nat.card (Automizer E0) * 9 at h
  omega

theorem automizer_E0 : Nonempty (Automizer E0 ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨ok0, hz0, hx0⟩ := ne_ok 0 (by rw [neGens_size]; norm_num)
  obtain ⟨ok1, hz1, hx1⟩ := ne_ok 1 (by rw [neGens_size]; norm_num)
  set u := eltOf neGens[0]! ok0
  set s := eltOf neGens[1]! ok1
  have hu : u ∈ normalizer ((E0 : Subgroup GJ) : Set GJ) :=
    conj_mem_E0_of_inE (rep_eltOf ok0) (okA_spec ok0).1 hz0 hx0
  have hs : s ∈ normalizer ((E0 : Subgroup GJ) : Set GJ) :=
    conj_mem_E0_of_inE (rep_eltOf ok1) (okA_spec ok1).1 hz1 hx1
  set nu : normalizer ((E0 : Subgroup GJ) : Set GJ) := ⟨u, hu⟩
  set ns : normalizer ((E0 : Subgroup GJ) : Set GJ) := ⟨s, hs⟩
  refine CFSG.GH74.M12.Hyp.nonempty_mulEquiv_perm_three_of_card_six card_automizer_E0
    (QuotientGroup.mk nu⁻¹) (QuotientGroup.mk ns⁻¹) fun h => ?_
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf] at h
  have hw : ⁅u, s⁆ ∈ centralizer ((E0 : Subgroup GJ) : Set GJ) := by
    have e : ⁅u, s⁆ = (((nu⁻¹ * ns⁻¹)⁻¹ * (ns⁻¹ * nu⁻¹) :
        normalizer ((E0 : Subgroup GJ) : Set GJ)) : GJ)⁻¹ := by
      simp only [nu, ns, Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
      group
    rw [e]
    exact inv_mem h
  have hrep : Rep 315 (commutatorA 315 neGens[0]! neGens[1]!) ⁅u, s⁆.1 := by
    have := rep_commutatorA (okA_spec ok0).1 (okA_spec ok1).1
    rw [(rep_of_validA (okA_spec ok0).1).unique (rep_eltOf ok0),
      (rep_of_validA (okA_spec ok1).1).unique (rep_eltOf ok1)] at this
    simpa [commutatorElement_def] using this
  have h1 := commA_of_commute hrep rep_z (mem_centralizer_iff.mp hw _ zJ_mem_E0).symm
  have h2 := commA_of_commute hrep rep_x (mem_centralizer_iff.mp hw _ x_mem_E0).symm
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h⟩ := elts45
  rw [h1, h2] at h
  exact Bool.noConfusion h

theorem autIn_E0 : Nonempty (autIn ⊤ E0 ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨e⟩ := automizer_E0
  exact ⟨(automizerEquivAutIn E0).symm.trans e⟩

end CFSG.RankThree.PartTwo.Sec4.Sporadic.J2
