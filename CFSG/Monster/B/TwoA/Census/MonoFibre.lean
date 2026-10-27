module

public import CFSG.Monster.B.TwoA.Census.MonoConj
public import CFSG.Monster.B.TwoA.Census.MonoCert

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Census

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Lifts CFSG.Monster.VisQuot

theorem mem_C_permI {pa : Array ℕ} (hpa : PermArr pa = true) (hpa' : decode pa ∈ AutPerm)
    {n : ℕ} (hn : bvec 24 n ∈ C) (hspec : bvec 24 (permI pa n) = bvec 24 n ∘ arrFun (ainv pa)) :
    bvec 24 (permI pa n) ∈ C := by
  rw [hspec, ← permWord_decode hpa]
  exact permWord_mem_of_mem_AutPerm hpa' hn

theorem codeCls_permQ {p : AutPerm} {pa : Array ℕ} (hpa : PermArr pa = true)
    (hp : (p : Equiv.Perm (Fin 24)) = decode pa) {n : ℕ} (hn : bvec 24 n ∈ C)
    (hspec : bvec 24 (permI pa n) = bvec 24 n ∘ arrFun (ainv pa)) :
    codeCls (permI pa n) = permQ p (codeCls n) := by
  have hpa' : decode pa ∈ AutPerm := hp ▸ p.2
  have e : (⟨decode pa, hpa'⟩ : AutPerm) = p := Subtype.ext hp.symm
  rw [codeCls_permI hpa hpa' hn hspec, e]

theorem codeCls_eq_zero_iff {m : ℕ} (hm : m < 2 ^ 24) (hc : bvec 24 m ∈ C) :
    codeCls m = 0 ↔ m = 0 ∨ m = OM := by
  rw [codeCls_of_mem hc, Submodule.Quotient.mk_eq_zero, mem_ΩLine_iff]
  constructor
  · rintro (h | h)
    · left
      apply CFSG.Monster.VisCert.bvec_injective hm (by norm_num)
      rw [bvec_zero]
      simpa using congrArg Subtype.val h
    · right
      apply CFSG.Monster.VisCert.bvec_injective hm (by norm_num [OM])
      rw [bvec_OM]
      simpa [ΩC] using congrArg Subtype.val h
  · rintro (rfl | rfl)
    · exact Or.inl (Subtype.ext (bvec_zero 24))
    · exact Or.inr (Subtype.ext bvec_OM)

theorem bvec_mem_of_mem_validList
    {n : ℕ} (hn : n ∈ validList) : bvec 24 n ∈ C :=
  (validList_spec.2.2 n hn).2

theorem mem_validList_of_validB {j n : ℕ} (h : validB j n = true) : n ∈ validList := by
  simp only [validB, Bool.and_eq_true] at h
  simpa using h.1

theorem eligB_of_validB {j n : ℕ} (h : validB j n = true) : eligB j n = true := by
  simp only [validB, Bool.and_eq_true] at h
  exact h.2

theorem bvec_Bmask_mem {k : ℕ} (hk : k < 12) : bvec 24 (Bmask k) ∈ C := by
  have := B_mem_C ⟨k, hk⟩
  rwa [B_eq_bvec] at this

private theorem list_getD_mem {l : List (Array ℕ)} {k : ℕ} (hk : k < l.length) :
    l.getD k #[] ∈ l := by
  simp only [List.getD, List.getElem?_eq_getElem hk, Option.getD_some]
  exact List.getElem_mem hk

open _root_.Classical in
@[expose] def seedAut (j : ℕ) : AutPerm :=
  if h : decode (seedA j) ∈ AutPerm then ⟨decode (seedA j), h⟩ else 1

theorem coe_seedAut {j : ℕ} (h : decode (seedA j) ∈ AutPerm) :
    (seedAut j : Equiv.Perm (Fin 24)) = decode (seedA j) := by
  unfold seedAut
  simp only [h, ↓reduceDIte]

open _root_.Classical in
@[expose] def centAut (j k : ℕ) : AutPerm :=
  if h : decode ((centGenArrs j).getD k #[]) ∈ AutPerm then ⟨_, h⟩ else 1

theorem coe_centAut {j k : ℕ} (h : decode ((centGenArrs j).getD k #[]) ∈ AutPerm) :
    (centAut j k : Equiv.Perm (Fin 24)) = decode ((centGenArrs j).getD k #[]) := by
  unfold centAut
  simp only [h, ↓reduceDIte]

structure SeedHyp (j : ℕ) : Prop where
  lt : j < 3
  seed_mem : decode (seedA j) ∈ AutPerm
  cent_mem : ∀ a ∈ centGenArrs j, decode a ∈ AutPerm
  sq : decode (seedA j) * decode (seedA j) = 1
  comm : ∀ a ∈ centGenArrs j, decode a * decode (seedA j) = decode (seedA j) * decode a
  gen : Subgroup.closure (centAut j '' {k | k < (centGenArrs j).length}) =
    Subgroup.centralizer {seedAut j}

variable {j : ℕ}

theorem SeedHyp.coe_seed (h : SeedHyp j) :
    (seedAut j : Equiv.Perm (Fin 24)) = decode (seedA j) :=
  coe_seedAut h.seed_mem

theorem SeedHyp.perm (h : SeedHyp j) : PermArr (seedA j) = true :=
  seedArr_perm _ (list_getD_mem (by simp [seedArr]; exact h.lt))

theorem SeedHyp.seed_sq (h : SeedHyp j) : seedAut j * seedAut j = 1 :=
  Subtype.ext (by rw [Subgroup.coe_mul, h.coe_seed, h.sq]; rfl)

theorem SeedHyp.cent_comm (h : SeedHyp j) {k : ℕ} (hk : k < (centGenArrs j).length) :
    centAut j k * seedAut j = seedAut j * centAut j k := by
  have ha := list_getD_mem hk
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_centAut (h.cent_mem _ ha), h.coe_seed]
  exact h.comm _ ha

@[expose] def fibPt (j n : ℕ) : MonoSD := ⟨Multiplicative.ofAdd (codeCls n), seedAut j⟩

@[expose] def genElt (j k : ℕ) : MonoSD :=
  if k < 12 then SemidirectProduct.inl (Multiplicative.ofAdd (codeCls (Bmask k)))
  else SemidirectProduct.inr (centAut j (k - 12))

@[expose] def gensJ (j k : ℕ) : ConjAct MonoSD := ConjAct.toConjAct (genElt j k)

theorem fibPt_actJ
    (h : SeedHyp j) {k : ℕ} (hk : k < ngenJ j) {n : ℕ}
    (hn : validB j n = true) : fibPt j (actJ j k n) = gensJ j k • fibPt j n := by
  have hnv := mem_validList_of_validB hn
  have hnC := bvec_mem_of_mem_validList hnv
  have hpa := h.perm
  rw [gensJ, ConjAct.toConjAct_smul]
  by_cases hk12 : k < 12
  · have hb := bvec_Bmask_mem hk12
    have hspec := permI_spec_seed_basis j h.lt k hk12
    have hbp := mem_C_permI hpa h.seed_mem hb hspec
    simp only [actJ, genElt, hk12, ↓reduceIte]
    rw [fibPt, fibPt, inl_conj,
      codeCls_canI (mem_C_xor (mem_C_xor hnC hb) hbp), codeCls_xor (mem_C_xor hnC hb) hbp,
      codeCls_xor hnC hb, codeCls_permQ hpa h.coe_seed hb hspec]
  · have hk' : k - 12 < (centGenArrs j).length := by
      unfold ngenJ at hk
      omega
    have ha := list_getD_mem hk'
    have hca := centGenArr_perm j h.lt _ ha
    have hspec := permI_spec_cent j h.lt _ ha n hnv
    have hc := coe_centAut (h.cent_mem _ ha)
    simp only [actJ, genElt, hk12, ↓reduceIte]
    rw [fibPt, fibPt, inr_conj, h.cent_comm hk',
      mul_inv_cancel_right, codeCls_canI (mem_C_permI hca (h.cent_mem _ ha) hnC hspec),
      codeCls_permQ hca hc hnC hspec]

theorem fibPt_inj
    {a b : ℕ} (ha : validB j a = true) (hb : validB j b = true)
    (e : fibPt j a = fibPt j b) : a = b := by
  have hav := mem_validList_of_validB ha
  have hbv := mem_validList_of_validB hb
  exact codeCls_inj (validList_spec.2.2 a hav).1 (validList_spec.2.2 b hbv).1
    (validList_spec.2.2 a hav).2 (validList_spec.2.2 b hbv).2
    (Multiplicative.ofAdd.injective (congrArg SemidirectProduct.left e))

theorem orbit_fibPt
    {i : ℕ} (hi : i < 7) (h : SeedHyp (monoSeed.getD i 0)) :
    MulAction.orbit (Subgroup.closure
        (gensJ (monoSeed.getD i 0) '' {k | k < ngenJ (monoSeed.getD i 0)}))
      (fibPt (monoSeed.getD i 0) (monoSign.getD i 0)) =
    (fun t => fibPt (monoSeed.getD i 0) (monoCert i).pts[t]!) '' {t | t < (monoCert i).pts.size} :=
  orbit_of_natCertOK (monoCert_ok i hi) (fun _ hk _ ha => fibPt_actJ h hk ha)

theorem ncard_orbit_fibPt
    {i : ℕ} (hi : i < 7) (h : SeedHyp (monoSeed.getD i 0)) :
    (MulAction.orbit (Subgroup.closure
        (gensJ (monoSeed.getD i 0) '' {k | k < ngenJ (monoSeed.getD i 0)}))
      (fibPt (monoSeed.getD i 0) (monoSign.getD i 0))).ncard = (monoCert i).pts.size :=
  ncard_orbit_of_natCertOK (monoCert_ok i hi) (fun _ hk _ ha => fibPt_actJ h hk ha)
    (fun _ _ ha hb e => fibPt_inj ha hb e)

@[expose] def fibreStab (p : AutPerm) : Subgroup MonoSD :=
  (Subgroup.centralizer {p}).comap SemidirectProduct.rightHom

theorem mem_fibreStab {p : AutPerm} {y : MonoSD} :
    y ∈ fibreStab p ↔ y.right * p = p * y.right := by
  rw [fibreStab, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
  rfl

theorem closure_signs : Subgroup.closure (Set.range fun k : Fin 12 =>
    (Multiplicative.ofAdd (codeCls (Bmask k)) : Multiplicative (C ⧸ ΩLine))) = ⊤ := by
  have hspan : Submodule.span (ZMod 2) (Set.range fun k : Fin 12 => codeCls (Bmask k)) = ⊤ := by
    have e : (fun k : Fin 12 => codeCls (Bmask k)) = ΩLine.mkQ ∘ basisC := by
      funext k
      rw [Function.comp_apply, codeCls_of_mem (bvec_Bmask_mem k.2), Submodule.mkQ_apply]
      congr 1
      exact Subtype.ext (by rw [basisC_apply, B_eq_bvec])
    rw [e, Set.range_comp, ← Submodule.map_span, basisC.span_eq, Submodule.map_top,
      Submodule.range_mkQ]
  rw [eq_top_iff]
  rintro x -
  induction x using Multiplicative.rec with
  | ofAdd y =>
    have hy : y ∈ Submodule.span (ZMod 2) (Set.range fun k : Fin 12 => codeCls (Bmask k)) := by
      rw [hspan]
      exact Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨k, rfl⟩ := hz
      exact Subgroup.subset_closure ⟨k, rfl⟩
    | zero => exact Subgroup.one_mem _
    | add a b _ _ ha hb =>
      rw [ofAdd_add]
      exact Subgroup.mul_mem _ ha hb
    | smul c a _ ha =>
      rcases (show ∀ t : ZMod 2, t = 0 ∨ t = 1 by decide) c with rfl | rfl
      · rw [zero_smul, ofAdd_zero]
        exact Subgroup.one_mem _
      · rwa [one_smul]

theorem closure_genElt (h : SeedHyp j) :
    Subgroup.closure (genElt j '' {k | k < ngenJ j}) = fibreStab (seedAut j) := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    rw [SetLike.mem_coe, mem_fibreStab]
    by_cases hk12 : k < 12
    · simp only [genElt, hk12, ↓reduceIte, SemidirectProduct.right_inl, one_mul, mul_one]
    · simp only [genElt, hk12, ↓reduceIte, SemidirectProduct.right_inr]
      refine h.cent_comm ?_
      simp only [Set.mem_ofPred_eq, ngenJ] at hk
      omega
  · intro y hy
    rw [← SemidirectProduct.inl_left_mul_inr_right y]
    refine Subgroup.mul_mem _ ?_ ?_
    · have hl : y.left ∈ Subgroup.closure (Set.range fun k : Fin 12 =>
          (Multiplicative.ofAdd (codeCls (Bmask k)) : Multiplicative (C ⧸ ΩLine))) := by
        rw [closure_signs]
        exact Subgroup.mem_top _
      have := Subgroup.mem_map_of_mem
        (SemidirectProduct.inl : Multiplicative (C ⧸ ΩLine) →* MonoSD) hl
      rw [MonoidHom.map_closure] at this
      refine Subgroup.closure_mono ?_ this
      rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
      exact ⟨k, by simp only [Set.mem_ofPred_eq, ngenJ]; omega, by simp [genElt, k.2]⟩
    · have hr : y.right ∈ Subgroup.closure (centAut j '' {k | k < (centGenArrs j).length}) := by
        rw [h.gen, Subgroup.mem_centralizer_singleton_iff]
        exact (mem_fibreStab.1 hy)
      have := Subgroup.mem_map_of_mem (SemidirectProduct.inr : AutPerm →* MonoSD) hr
      rw [MonoidHom.map_closure] at this
      refine Subgroup.closure_mono ?_ this
      rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      refine ⟨k + 12, by simp only [Set.mem_ofPred_eq, ngenJ] at hk ⊢; omega, ?_⟩
      simp [genElt]

@[expose] def conjOrbit (p : AutPerm) (x : MonoSD) : Set MonoSD :=
  {z | ∃ g ∈ fibreStab p, g * x * g⁻¹ = z}

theorem orbit_gensJ_eq (h : SeedHyp j) (x : MonoSD) :
    MulAction.orbit (Subgroup.closure (gensJ j '' {k | k < ngenJ j})) x =
      conjOrbit (seedAut j) x := by
  have e : gensJ j '' {k | k < ngenJ j} =
      (ConjAct.toConjAct : MonoSD ≃* ConjAct MonoSD).toMonoidHom ''
        (genElt j '' {k | k < ngenJ j}) := by
    rw [Set.image_image]
    rfl
  rw [e, ← MonoidHom.map_closure, closure_genElt h]
  ext z
  constructor
  · rintro ⟨⟨_, g, hg, rfl⟩, rfl⟩
    exact ⟨g, hg, (ConjAct.toConjAct_smul g x).symm⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨_, g, hg, rfl⟩, ConjAct.toConjAct_smul g x⟩

theorem conjOrbit_eq
    {i : ℕ} (hi : i < 7) (h : SeedHyp (monoSeed.getD i 0)) :
    conjOrbit (seedAut (monoSeed.getD i 0)) (fibPt (monoSeed.getD i 0) (monoSign.getD i 0)) =
      (fun t => fibPt (monoSeed.getD i 0) (monoCert i).pts[t]!) ''
        {t | t < (monoCert i).pts.size} := by
  rw [← orbit_gensJ_eq h, orbit_fibPt hi h]

theorem ncard_conjOrbit
    {i : ℕ} (hi : i < 7) (h : SeedHyp (monoSeed.getD i 0)) :
    (conjOrbit (seedAut (monoSeed.getD i 0))
      (fibPt (monoSeed.getD i 0) (monoSign.getD i 0))).ncard = (monoCert i).pts.size := by
  rw [← orbit_gensJ_eq h, ncard_orbit_fibPt hi h]

@[expose] def fibre (p : AutPerm) : Set MonoSD := {y | y.right = p ∧ y * y = 1}

theorem eligB_iff {n : ℕ} :
    eligB j n = true ↔ (n ^^^ permI (seedA j) n = 0 ∨ n ^^^ permI (seedA j) n = OM) := by
  simp only [eligB, Bool.or_eq_true, beq_iff_eq]

theorem fibPt_mem_fibre_iff
    (h : SeedHyp j) {n : ℕ} (hn : n ∈ validList) :
    fibPt j n ∈ fibre (seedAut j) ↔ eligB j n = true := by
  have hnC := bvec_mem_of_mem_validList hn
  have hspec := permI_spec_seed j h.lt n hn
  have hpC := mem_C_permI h.perm h.seed_mem hnC hspec
  have hlt : n ^^^ permI (seedA j) n < 2 ^ 24 :=
    Nat.xor_lt_two_pow (lt_trans (validList_spec.2.2 n hn).1 (by norm_num))
      (permI_seed_lt j h.lt n hn)
  rw [fibre, Set.mem_ofPred_eq, fibPt, mul_self_eq_one_iff, eligB_iff,
    ← codeCls_permQ h.perm h.coe_seed hnC hspec, ← codeCls_xor hnC hpC,
    codeCls_eq_zero_iff hlt (mem_C_xor hnC hpC)]
  simp only [h.seed_sq, true_and]

theorem fibre_eq
    (h : SeedHyp j) : fibre (seedAut j) = fibPt j '' {n | n ∈ eligList j} := by
  ext y
  constructor
  · rintro ⟨hr, hy⟩
    obtain ⟨n, hn, e⟩ := codeCls_surj (Multiplicative.toAdd y.left)
    have hyn : y = fibPt j n := by
      refine SemidirectProduct.ext ?_ hr
      rw [fibPt, e]
      rfl
    refine ⟨n, ?_, hyn.symm⟩
    rw [Set.mem_ofPred_eq, eligList, List.mem_filter]
    exact ⟨hn, (fibPt_mem_fibre_iff h hn).1 (hyn ▸ ⟨hr, hy⟩)⟩
  · rintro ⟨n, hn, rfl⟩
    rw [Set.mem_ofPred_eq, eligList, List.mem_filter] at hn
    exact (fibPt_mem_fibre_iff h hn.1).2 hn.2

theorem eligList_perm {j : ℕ} (hj : j < 3) :
    (((List.range 7).filter (fun i => monoSeed.getD i 0 == j)).flatMap
      (fun i => (monoCert i).pts.toList)).Perm (eligList j) := by
  have h1 := List.mergeSort_perm (((List.range 7).filter (fun i => monoSeed.getD i 0 == j)).flatMap
    (fun i => (monoCert i).pts.toList)) (fun a b => decide (a ≤ b))
  rw [monoCert_partition j hj] at h1
  exact h1.symm.trans (List.mergeSort_perm _ _)

theorem eligList_nodup (j : ℕ) : (eligList j).Nodup :=
  validList_spec.2.1.filter _

theorem mem_eligList_iff {j : ℕ} (hj : j < 3) {n : ℕ} :
    n ∈ eligList j ↔ ∃ i < 7, monoSeed.getD i 0 = j ∧ n ∈ (monoCert i).pts.toList := by
  rw [← (eligList_perm hj).mem_iff, List.mem_flatMap]
  simp only [List.mem_filter, List.mem_range, beq_iff_eq]
  constructor
  · rintro ⟨i, ⟨hi, hs⟩, hn⟩
    exact ⟨i, hi, hs, hn⟩
  · rintro ⟨i, hi, hs, hn⟩
    exact ⟨i, ⟨hi, hs⟩, hn⟩

theorem monoCert_disjoint
    {j : ℕ} (hj : j < 3) {i₁ i₂ : ℕ} (h₁ : i₁ < 7) (h₂ : i₂ < 7)
    (hs₁ : monoSeed.getD i₁ 0 = j) (hs₂ : monoSeed.getD i₂ 0 = j) (hne : i₁ ≠ i₂) {n : ℕ}
    (hn₁ : n ∈ (monoCert i₁).pts.toList) (hn₂ : n ∈ (monoCert i₂).pts.toList) : False := by
  have hnd := (eligList_perm hj).nodup_iff.2 (eligList_nodup j)
  rw [List.nodup_flatMap] at hnd
  have hmem : ∀ i, i < 7 → monoSeed.getD i 0 = j →
      i ∈ (List.range 7).filter (fun i => monoSeed.getD i 0 == j) := fun i hi hs => by
    simp only [List.mem_filter, List.mem_range, beq_iff_eq]
    exact ⟨hi, hs⟩
  have : Std.Symm (Function.onFun List.Disjoint fun i => (monoCert i).pts.toList) :=
    ⟨fun _ _ h => List.Disjoint.symm h⟩
  exact (hnd.2.forall (hmem i₁ h₁ hs₁) (hmem i₂ h₂ hs₂) hne) hn₁ hn₂

end CFSG.Monster.B.TwoA.Census
