module

public import CFSG.Sporadic.SuzOddCore.SuzIso
public import CFSG.Sporadic.SuzOddCore.FamilyCheck
public import CFSG.Certificates.NativeRefine

public noncomputable section

namespace CFSG.Sporadic.SuzOddCore

open CFSG.Certificates CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Perm CFSG.Perm.Native
open scoped Pointwise

@[expose] def famSet (d : Fin 1782) : Set (Fin 22880) := finSet 22880 suzFam[(d : ℕ)]!

theorem famOK_parts :
    (∀ d < 1782, PointList 22880 suzFam[d]!) ∧
    (∀ d < 1782, suzFam[b0Arr[d]!]! = imgSorted (certArr 0) suzFam[d]!) ∧
    (∀ d < 1782, suzFam[b1Arr[d]!]! = imgSorted (certArr 1) suzFam[d]!) ∧
    (∀ d < 1782, d ≠ 0 → suzFam[d]! ≠ suzFam[0]!) := by
  have h := family_check.1
  simp only [famOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨_hs, _hsz⟩, hpt⟩, himg⟩, hne⟩ := h
  refine ⟨fun d hd => ?_, fun d hd => ?_, fun d hd => ?_, fun d hd hd0 => ?_⟩
  · have := allLt_spec hpt hd
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at this
    exact ⟨this.1, CFSG.Certificates.strictIncr_pairwise this.2⟩
  · have := allLt_spec (allLt_spec himg (show 0 < 2 by norm_num)) hd
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
    exact this.2
  · have := allLt_spec (allLt_spec himg (show 1 < 2 by norm_num)) hd
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
    exact this.2
  · have := allLt_spec hne hd
    simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at this
    exact this.resolve_left hd0

theorem famSet_smul_gen
    {t s : Array ℕ} {A : Equiv.Perm (Fin 22880)} {B : Equiv.Perm (Fin 1782)}
    (hA : Rep 22880 t A) (hB : Rep 1782 s B)
    (himg : ∀ d < 1782, suzFam[s[d]!]! = imgSorted t suzFam[d]!) (d : Fin 1782) :
    A • famSet d = famSet (B d) := by
  rw [famSet, famSet, ← hB d, himg d d.2]
  exact ((famOK_parts.1 d d.2).img hA).2.symm

theorem famSet_smul_a0
    (d : Fin 1782) : suzA0 • famSet d = famSet (suzB0 d) :=
  famSet_smul_gen rep_suzA0 rep_b0 famOK_parts.2.1 d

theorem famSet_smul_a1
    (d : Fin 1782) : suzA1 • famSet d = famSet (suzB1 d) :=
  famSet_smul_gen rep_suzA1 rep_b1 famOK_parts.2.2.1 d

theorem famSet_ne_zero
    {d : Fin 1782} (hd : d ≠ 0) : famSet d ≠ famSet 0 := by
  intro h
  exact famOK_parts.2.2.2 d d.2 (fun h0 => hd (Fin.ext h0))
    ((famOK_parts.1 d d.2).eq_of_finSet_eq (famOK_parts.1 0 (by norm_num)) h)

@[expose] def smallGs (j : ℕ) : Equiv.Perm (Fin 1782) := if j = 0 then suzB0 else suzB1

theorem th_rep_of_rep {n : ℕ} {t : Array ℕ} {g : Equiv.Perm (Fin n)} (ht : Rep n t g)
    (hsz : t.size = n) (hb : ∀ i < n, t[i]! < 2 ^ 32) :
    CFSG.Sporadic.Th.Rep n (t.map UInt32.ofNat) g := by
  intro i hi
  have hi' : i < t.size := hsz ▸ hi
  rw [CFSG.Sporadic.Th.idx_of_lt g hi, CFSG.Sporadic.Th.Native.ap,
    getElem!_pos (t.map UInt32.ofNat) i (by rw [Array.size_map]; exact hi'), Array.getElem_map,
    UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by rw [← getElem!_pos t i hi']; exact hb i hi),
    ← getElem!_pos t i hi', ht.apply hi]
  rfl

theorem smallTree_facts :
    TreeFacts 1782 smallTree #[0, 1, 2, 3] (pairG smallGs) 0 := by
  obtain ⟨-, hT, -, h0, h1, h0i, h1i, -⟩ := family_check
  have hsz0 : b0Arr.size = 1782 := by
    have := arrays_check.2.2.2.2.2.2.2.2.1
    simp only [permOK, Bool.and_eq_true, beq_iff_eq] at this
    exact this.1
  have hsz1 : b1Arr.size = 1782 := by
    have := arrays_check.2.2.2.2.2.2.2.2.2.1
    simp only [permOK, Bool.and_eq_true, beq_iff_eq] at this
    exact this.1
  have hsz0i : (invCand 1782 b0Arr).size = 1782 := family_check.2.2.2.2.2.2.2.2.1
  have hsz1i : (invCand 1782 b1Arr).size = 1782 := family_check.2.2.2.2.2.2.2.2.2
  have hT' : CFSG.Perm.Native.treeOK 1782 0 smallTree smallLetters #[0, 1, 2, 3] = true := by
    simp only [smallTreeOK, Bool.and_eq_true] at hT
    exact hT.1
  refine treeOK_facts (fun l hl => ?_) hT'
  have hb0inv := (rep_permC (Bool.and_eq_true_iff.1 arrays_check.2.2.2.2.2.2.2.2.1).2).2
  have hb1inv := (rep_permC (Bool.and_eq_true_iff.1 arrays_check.2.2.2.2.2.2.2.2.2.1).2).2
  have key : ∀ (L : Array CFSG.Sporadic.Th.Native.Table)
      (t0 t1 t2 t3 : CFSG.Sporadic.Th.Native.Table), L = #[t0, t1, t2, t3] →
      CFSG.Sporadic.Th.Rep 1782 t0 suzB0 → CFSG.Sporadic.Th.Rep 1782 t1 suzB0⁻¹ →
      CFSG.Sporadic.Th.Rep 1782 t2 suzB1 → CFSG.Sporadic.Th.Rep 1782 t3 suzB1⁻¹ →
      ∀ l ∈ #[0, 1, 2, 3], CFSG.Sporadic.Th.Rep 1782 L[l]! (pairG smallGs l) := by
    intro L t0 t1 t2 t3 hL r0 r1 r2 r3 l hl
    subst hL
    simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · rw [pairG, ite_eq_left rfl, smallGs, ite_eq_left rfl]; exact r0
    · rw [pairG, ite_eq_right (by decide), smallGs, ite_eq_left rfl]; exact r1
    · rw [pairG, ite_eq_left rfl, smallGs, ite_eq_right (by decide)]; exact r2
    · rw [pairG, ite_eq_right (by decide), smallGs, ite_eq_right (by decide)]; exact r3
  exact key smallLetters _ _ _ _ smallLetters.eq_def (th_rep_of_rep rep_b0 hsz0 h0)
    (th_rep_of_rep hb0inv hsz0i h0i) (th_rep_of_rep rep_b1 hsz1 h1)
    (th_rep_of_rep hb1inv hsz1i h1i) l hl

theorem smallTree_size : smallTree.pts.size = 1782 := by
  have h := family_check.2.1
  simp only [smallTreeOK, Bool.and_eq_true, beq_iff_eq] at h
  exact h.2

theorem lettersGroup_le_suzM : lettersGroup #[0, 1, 2, 3] (pairG smallGs) ≤ suzM := by
  rw [lettersGroup, Subgroup.closure_le]
  rintro _ ⟨l, hl, rfl⟩
  have hB0 : suzB0 ∈ suzM := Subgroup.subset_closure (Set.mem_insert _ _)
  have hB1 : suzB1 ∈ suzM := Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl <;> simp [pairG, smallGs, hB0, hB1, suzM.inv_mem]

theorem suzM_transitive
    (d : Fin 1782) : ∃ m ∈ suzM, m 0 = d := by
  have hT := smallTree_facts
  have hcard := hT.card_orbit
  rw [smallTree_size] at hcard
  have huniv : MulAction.orbit (lettersGroup #[0, 1, 2, 3] (pairG smallGs))
      (⟨0, hT.r_lt⟩ : Fin 1782) = Set.univ := by
    apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _) _ (Set.toFinite _)
    rw [Set.ncard_univ, Nat.card_fin, ← Nat.card_coe_set_eq, hcard]
  have hd : d ∈ MulAction.orbit (lettersGroup #[0, 1, 2, 3] (pairG smallGs))
      (⟨0, hT.r_lt⟩ : Fin 1782) := by rw [huniv]; trivial
  obtain ⟨⟨m, hm⟩, hmd⟩ := hd
  exact ⟨m, lettersGroup_le_suzM hm, hmd⟩

@[expose] def suzH : Subgroup SuzK := Subgroup.closure {(suzA0, suzB0), (suzA1, suzB1)}

theorem suzH_famSet
    {x : SuzK} (hx : x ∈ suzH) (d : Fin 1782) :
    x.1 • famSet d = famSet (x.2 d) := by
  induction hx using Subgroup.closure_induction generalizing d with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact famSet_smul_a0 d
    · exact famSet_smul_a1 d
  | one => rw [Prod.fst_one, Prod.snd_one, one_smul, Equiv.Perm.one_apply]
  | mul x y _ _ hx hy =>
    rw [Prod.fst_mul, Prod.snd_mul, mul_smul, hy, hx, Equiv.Perm.mul_apply]
  | inv x _ hx =>
    rw [Prod.fst_inv, Prod.snd_inv]
    have h := hx (x.2⁻¹ d)
    rw [perm_apply_inv'] at h
    rw [← h, inv_smul_smul]

theorem suzH_snd_mem {m : Equiv.Perm (Fin 1782)} (hm : m ∈ suzM) : ∃ g, (g, m) ∈ suzH := by
  have : suzH.map (MonoidHom.snd _ _) = suzM := by
    rw [suzH, MonoidHom.map_closure, suzM, Set.image_insert_eq, Set.image_singleton]
    rfl
  rw [← this] at hm
  obtain ⟨⟨g, m'⟩, hx, rfl⟩ := hm
  exact ⟨g, hx⟩

theorem suzH_fst_mem {g : Equiv.Perm (Fin 22880)} (hg : g ∈ suzP) : ∃ m, (g, m) ∈ suzH := by
  have : suzH.map (MonoidHom.fst _ _) = suzP := by
    rw [suzH, MonoidHom.map_closure, suzP, Set.image_insert_eq, Set.image_singleton]
    rfl
  rw [← this] at hg
  obtain ⟨⟨g', m⟩, hx, rfl⟩ := hg
  exact ⟨m, hx⟩

theorem suzH_fst_mem' {x : SuzK} (hx : x ∈ suzH) : x.1 ∈ suzP := by
  have : suzH.map (MonoidHom.fst _ _) = suzP := by
    rw [suzH, MonoidHom.map_closure, suzP, Set.image_insert_eq, Set.image_singleton]
    rfl
  rw [← this]
  exact ⟨x, hx, rfl⟩

theorem suzH_snd_mem' {x : SuzK} (hx : x ∈ suzH) : x.2 ∈ suzM := by
  have : suzH.map (MonoidHom.snd _ _) = suzM := by
    rw [suzH, MonoidHom.map_closure, suzM, Set.image_insert_eq, Set.image_singleton]
    rfl
  rw [← this]
  exact ⟨x, hx, rfl⟩

theorem famSet_injective :
    Function.Injective famSet := by
  intro d d' hdd'
  obtain ⟨m, hm, hmd⟩ := suzM_transitive d
  obtain ⟨g, hg⟩ := suzH_snd_mem (suzM.inv_mem hm)
  have h1 := suzH_famSet hg d
  have h2 := suzH_famSet hg d'
  have hd0 : m⁻¹ d = 0 := by rw [← hmd, perm_inv_apply']
  simp only at h1 h2
  rw [hd0] at h1
  have h3 : famSet (m⁻¹ d') = famSet 0 := by rw [← h2, ← hdd', h1]
  have h4 : m⁻¹ d' = 0 := by
    by_contra hne
    exact famSet_ne_zero hne h3
  exact (m⁻¹).injective (hd0.trans h4.symm)

theorem suzH_fst_injective
    {x y : SuzK} (hx : x ∈ suzH) (hy : y ∈ suzH) (h : x.1 = y.1) :
    x = y := by
  have hz : y⁻¹ * x ∈ suzH := suzH.mul_mem (suzH.inv_mem hy) hx
  have h1 : (y⁻¹ * x).1 = 1 := by rw [Prod.fst_mul, Prod.fst_inv, h, inv_mul_cancel]
  have h2 : (y⁻¹ * x).2 = 1 := by
    ext d
    have := suzH_famSet hz d
    rw [h1, one_smul] at this
    rw [Equiv.Perm.one_apply, famSet_injective this.symm]
  have : y⁻¹ * x = 1 := Prod.ext h1 h2
  rw [inv_mul_eq_one] at this
  exact this.symm

@[expose] def suzHFst : suzH →* Equiv.Perm (Fin 22880) :=
  (MonoidHom.fst _ _).comp suzH.subtype

@[expose] def suzHSnd : suzH →* Equiv.Perm (Fin 1782) :=
  (MonoidHom.snd _ _).comp suzH.subtype

theorem suzHFst_injective :
    Function.Injective suzHFst := fun x y h =>
  Subtype.ext (suzH_fst_injective x.2 y.2 h)

theorem suzHFst_range : suzHFst.range = suzP := by
  ext g
  constructor
  · rintro ⟨x, rfl⟩
    exact suzH_fst_mem' x.2
  · intro hg
    obtain ⟨m, hm⟩ := suzH_fst_mem hg
    exact ⟨⟨(g, m), hm⟩, rfl⟩

@[expose] def suzHEquivP :
    suzH ≃* suzP :=
  (MonoidHom.ofInjective suzHFst_injective).trans (MulEquiv.subgroupCongr suzHFst_range)

theorem suzHEquivP_apply
    (x : suzH) : ((suzHEquivP x : suzP) : Equiv.Perm (Fin 22880)) = x.1.1 := by
  rw [suzHEquivP, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply, MonoidHom.ofInjective_apply]
  rfl

@[expose] def suzHToM : suzH →* suzM :=
  suzHSnd.codRestrict suzM fun x => suzH_snd_mem' x.2

@[expose] def suzTheta0 :
    suzP →* suzM := suzHToM.comp suzHEquivP.symm.toMonoidHom

theorem suzTheta0_apply
    {x : SuzK} (hx : x ∈ suzH) (hx1 : x.1 ∈ suzP) :
    ((suzTheta0 ⟨x.1, hx1⟩ : suzM) : Equiv.Perm (Fin 1782)) = x.2 := by
  have : suzHEquivP.symm ⟨x.1, hx1⟩ = ⟨x, hx⟩ := by
    apply suzHEquivP.injective
    rw [MulEquiv.apply_symm_apply]
    apply Subtype.ext
    rw [suzHEquivP_apply]
  rw [suzTheta0, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, this]
  rfl

@[expose] def suzB0M : suzM := ⟨suzB0, Subgroup.subset_closure (Set.mem_insert _ _)⟩

@[expose] def suzB1M : suzM :=
  ⟨suzB1, Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩

theorem suzTheta0_a0 :
    suzTheta0 suzA0P = suzB0M := by
  apply Subtype.ext
  exact suzTheta0_apply (x := (suzA0, suzB0)) (Subgroup.subset_closure (Set.mem_insert _ _))
    suzA0P.2

theorem suzTheta0_a1 :
    suzTheta0 suzA1P = suzB1M := by
  apply Subtype.ext
  exact suzTheta0_apply (x := (suzA1, suzB1))
    (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))) suzA1P.2

theorem suzB0_ne_one : suzB0 ≠ 1 := by
  intro h
  have h0 := rep_b0 0
  rw [h, Equiv.Perm.one_apply] at h0
  exact family_check.2.2.2.2.2.2.2.1 h0

theorem suzP_closure : Subgroup.closure ({suzA0P, suzA1P} : Set suzP) = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨g, hg⟩ -
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    rcases hg with rfl | rfl
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  | one => exact Subgroup.one_mem _
  | mul g h hg hh ihg ihh => exact Subgroup.mul_mem _ ihg ihh
  | inv g hg ih => exact Subgroup.inv_mem _ ih

theorem suzM_closure : Subgroup.closure ({suzB0M, suzB1M} : Set suzM) = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨g, hg⟩ -
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    rcases hg with rfl | rfl
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  | one => exact Subgroup.one_mem _
  | mul g h hg hh ihg ihh => exact Subgroup.mul_mem _ ihg ihh
  | inv g hg ih => exact Subgroup.inv_mem _ ih

theorem suzTheta0_surjective :
    Function.Surjective suzTheta0 := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← suzM_closure, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact ⟨suzA0P, suzTheta0_a0⟩
  · exact ⟨suzA1P, suzTheta0_a1⟩

theorem suzTheta0_injective :
    Function.Injective suzTheta0 := by
  have := suzP_isSimpleGroup
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal suzTheta0.ker with h | h
  · exact h
  · exfalso
    have : suzA0P ∈ suzTheta0.ker := by rw [h]; trivial
    rw [MonoidHom.mem_ker, suzTheta0_a0] at this
    exact suzB0_ne_one (congrArg Subtype.val this)

@[expose] def suzTheta :
    suzP ≃* suzM :=
  MulEquiv.ofBijective suzTheta0 ⟨suzTheta0_injective, suzTheta0_surjective⟩

theorem suzTheta_a0 :
    suzTheta suzA0P = suzB0M := suzTheta0_a0

theorem suzTheta_a1 :
    suzTheta suzA1P = suzB1M := suzTheta0_a1

theorem suzP_hom_ext {G : Type*} [Group G] {f g : suzP →* G} (h0 : f suzA0P = g suzA0P)
    (h1 : f suzA1P = g suzA1P) (x : suzP) : f x = g x := by
  have hx : x ∈ Subgroup.closure ({suzA0P, suzA1P} : Set suzP) := by
    rw [suzP_closure]; exact Subgroup.mem_top x
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with rfl | rfl
    · exact h0
    · exact h1
  | one => rw [map_one, map_one]
  | mul y z _ _ hy hz => rw [map_mul, map_mul, hy, hz]
  | inv y _ hy => rw [map_inv, map_inv, hy]

theorem suzTheta_unique
    (e : suzP ≃* suzM) (h0 : e suzA0P = suzB0M) (h1 : e suzA1P = suzB1M) :
    e = suzTheta := by
  apply MulEquiv.ext
  intro x
  exact suzP_hom_ext (f := e.toMonoidHom) (g := suzTheta.toMonoidHom)
    (by rw [MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom, h0, suzTheta_a0])
    (by rw [MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom, h1, suzTheta_a1]) x

theorem suzM_isSimpleGroup :
    IsSimpleGroup suzM :=
  @MulEquiv.isSimpleGroup _ _ _ _ suzP_isSimpleGroup suzTheta.symm

theorem suzM_card :
    Nat.card suzM = 448345497600 := by
  rw [← Nat.card_congr suzTheta.toEquiv, suzP_card]

end CFSG.Sporadic.SuzOddCore
