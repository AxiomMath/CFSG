module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcE6SplitRoots
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCensusTabs
import CFSG.LocalAnalysis.StandardType.GGSixTCWP4TwistOuter
import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE6Data
import CFSG.LieType.Chevalley.CorootCoordinates

public section

namespace CFSG.StandardType.GGQ2Frame.ExcPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.LangTorus

private theorem mem_cent_iff {m : Fin 6} {c : Finset (ExcRaw.Root m)} {v : ExcRaw.V m} :
    v ∈ ExcRaw.cent m c ↔ ∀ i, i ∈ c → ExcRaw.root m i v = 0 := by
  simp only [ExcRaw.cent, Submodule.mem_iInf, LinearMap.mem_ker]

theorem _root_.CFSG.StandardType.GGQ2Frame.ExcRaw.occurs_cent_of_occurs {m : Fin 6}
    {U : Submodule (ZMod 3) (ExcRaw.V m)} {c : Finset (ExcRaw.Root m)} (hc : ExcRaw.occurs m U c) :
    ExcRaw.occurs m (ExcRaw.cent m c) c := by
  rcases hc with ⟨hne, hsub, hclosed, hmax⟩
  have hUle : U ≤ ExcRaw.cent m c := by
    intro u hu
    rw [mem_cent_iff]
    intro i hi
    exact hsub i hi u hu
  refine ⟨hne, ?_, ?_, hmax⟩
  · intro i hi u hu
    rw [mem_cent_iff] at hu
    exact hu i hi
  · intro i hi j hj hadj
    exact hclosed i hi j (fun u hu => hj u (hUle hu)) hadj

private def rootVec (i : ExcRaw.Root 1) : ExcRaw.V 1 := fun k => (ExcRaw.F 1 i k : ZMod 3)

private theorem root_apply_rootVec (i : ExcRaw.Root 1) (v : ExcRaw.V 1) :
    ExcRaw.root 1 i v = ∑ k, rootVec i k * v k :=
  ExcRaw.root_apply 1 i v

private theorem root_apply_single (i : ExcRaw.Root 1) (k : Fin (ExcRaw.dim 1)) :
    ExcRaw.root 1 i (Pi.single k 1) = rootVec i k := by
  rw [root_apply_rootVec, Finset.sum_eq_single k]
  · simp
  · intro l _ hlk
    simp [hlk]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

private theorem rootVec_injective : Function.Injective rootVec := by
  decide

private theorem root_injective : Function.Injective (fun i : ExcRaw.Root 1 => ExcRaw.root 1 i) := by
  intro i j h
  apply rootVec_injective
  funext k
  have hk := congrArg (fun f : Module.Dual (ZMod 3) (ExcRaw.V 1) => f (Pi.single k 1)) h
  simpa [rootVec, root_apply_rootVec, Pi.single_apply] using hk

private theorem vanish_cent_iff_mem_span (c : Finset (ExcRaw.Root 1)) (t : ExcRaw.Root 1) :
    ExcRaw.Vanish 1 (ExcRaw.cent 1 c) t ↔
      ExcRaw.root 1 t ∈ Submodule.span (ZMod 3)
        ((fun i : ExcRaw.Root 1 => ExcRaw.root 1 i) '' (c : Set (ExcRaw.Root 1))) := by
  constructor
  · intro h
    have hcent : (⨅ i : ↥c, LinearMap.ker (ExcRaw.root 1 (i : ExcRaw.Root 1))) =
        ExcRaw.cent 1 c := by
      ext v
      rw [Submodule.mem_iInf, mem_cent_iff]
      exact ⟨fun h i hi => h ⟨i, hi⟩, fun h i => h i i.2⟩
    have hle : (⨅ i : ↥c, LinearMap.ker (ExcRaw.root 1 (i : ExcRaw.Root 1))) ≤
        LinearMap.ker (ExcRaw.root 1 t) := by
      rw [hcent]
      intro v hv
      rw [LinearMap.mem_ker]
      exact h v hv
    have hspan := FiniteDimensional.mem_span_of_iInf_ker_le_ker hle
    have hrange : Set.range (fun i : ↥c => ExcRaw.root 1 (i : ExcRaw.Root 1)) =
        (fun i : ExcRaw.Root 1 => ExcRaw.root 1 i) '' (c : Set (ExcRaw.Root 1)) := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨i, i.2, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        exact ⟨⟨i, hi⟩, rfl⟩
    rw [hrange] at hspan
    exact hspan
  · rintro hspan v hv
    rw [mem_cent_iff] at hv
    have hzero : ∀ i ∈ c, ExcRaw.root 1 i v = 0 := fun i hi => hv i hi
    have hle : Submodule.span (ZMod 3)
        ((fun i : ExcRaw.Root 1 => ExcRaw.root 1 i) '' (c : Set (ExcRaw.Root 1))) ≤
        LinearMap.ker (LinearMap.applyₗ v) := by
      rw [Submodule.span_le]
      rintro x ⟨i, hi, rfl⟩
      exact LinearMap.mem_ker.mpr (hzero i hi)
    exact LinearMap.mem_ker.mp (hle hspan)

private theorem mem_iff_span_of_occurs {U : Submodule (ZMod 3) (ExcRaw.V 1)}
    {c : Finset (ExcRaw.Root 1)} (hc : ExcRaw.occurs 1 U c) (t : ExcRaw.Root 1) :
    t ∈ c ↔ ExcRaw.root 1 t ∈ Submodule.span (ZMod 3)
      ((fun i : ExcRaw.Root 1 => ExcRaw.root 1 i) '' (c : Set (ExcRaw.Root 1))) := by
  rw [ExcRaw.mem_iff_vanish_of_occurs (ExcRaw.occurs_cent_of_occurs hc) rfl t,
    vanish_cent_iff_mem_span]

private def orbitList (i : ExcRaw.Root 1) : List (Fin Tag.E6.rank → ℤ) :=
  e6SplitRoot i :: -e6SplitRoot i ::
    permLattice TwistTag.E6.perm (e6SplitRoot i) ::
      -permLattice TwistTag.E6.perm (e6SplitRoot i) :: []

private theorem mem_e6SplitCodeRoots_singleton_iff {i : ExcRaw.Root 1}
    {δ : Fin Tag.E6.rank → ℤ} : δ ∈ e6SplitCodeRoots {i} ↔ δ ∈ orbitList i := by
  constructor
  · rintro ⟨k, hk, h⟩
    obtain rfl := Finset.mem_singleton.1 hk
    rcases h with rfl | rfl | rfl | rfl
    · exact List.mem_cons.2 (Or.inl rfl)
    · exact List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inl rfl)))
    · exact List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inl rfl)))))
    · exact List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inr
        (List.mem_singleton.2 rfl))))))
  · intro h
    refine ⟨i, Finset.mem_singleton_self i, ?_⟩
    rcases List.mem_cons.1 h with h | h
    · exact Or.inl h
    rcases List.mem_cons.1 h with h | h
    · exact Or.inr (Or.inl h)
    rcases List.mem_cons.1 h with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    exact Or.inr (Or.inr (Or.inr (List.mem_singleton.1 h)))

private theorem mem_orbitList_iff {i : ExcRaw.Root 1} {δ : Fin Tag.E6.rank → ℤ} :
    δ ∈ orbitList i ↔ δ = e6SplitRoot i ∨ δ = -e6SplitRoot i ∨
      δ = permLattice TwistTag.E6.perm (e6SplitRoot i) ∨
        δ = -permLattice TwistTag.E6.perm (e6SplitRoot i) := by
  unfold orbitList
  constructor
  · intro h
    rcases List.mem_cons.1 h with h | h
    · exact Or.inl h
    rcases List.mem_cons.1 h with h | h
    · exact Or.inr (Or.inl h)
    rcases List.mem_cons.1 h with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    exact Or.inr (Or.inr (Or.inr (List.mem_singleton.1 h)))
  · rintro (h | h | h | h)
    · exact List.mem_cons.2 (Or.inl h)
    · exact List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inl h)))
    · exact List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inl h)))))
    · exact List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inr
        (List.mem_singleton.2 h))))))

private theorem e6SplitCodeRoots_eq_biUnion (c : Finset (ExcRaw.Root 1)) :
    e6SplitCodeRoots c = (c.biUnion fun i => (orbitList i).toFinset : Finset _) := by
  ext δ
  simp only [e6SplitCodeRoots, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_biUnion,
    List.mem_toFinset, mem_orbitList_iff]

private theorem disjoint_orbitList_toFinset {i j : ExcRaw.Root 1} (hij : i ≠ j) :
    Disjoint (orbitList i).toFinset (orbitList j).toFinset := by
  rw [Finset.disjoint_left]
  intro δ hi hj
  have h1 : δ ∈ e6SplitCodeRoots {i} :=
    mem_e6SplitCodeRoots_singleton_iff.mpr (List.mem_toFinset.mp hi)
  have h2 : δ ∈ e6SplitCodeRoots {j} :=
    mem_e6SplitCodeRoots_singleton_iff.mpr (List.mem_toFinset.mp hj)
  exact hij (eq_of_mem_e6SplitCodeRoots_singleton h1 h2)

private theorem card_orbitList_toFinset_all : ∀ i : ExcRaw.Root 1,
    (orbitList i).toFinset.card = if ExcRaw.tabFix1.getD i.val false then 2 else 4 := by
  decide

theorem ncard_e6SplitCodeRoots (c : Finset (ExcRaw.Root 1)) :
    (e6SplitCodeRoots c).ncard =
      2 * ExcRaw.longCount 1 c + 4 * (c.card - ExcRaw.longCount 1 c) := by
  have hcard : ∀ i : ExcRaw.Root 1,
      (orbitList i).toFinset.card = if ExcRaw.tabFix1.getD i.val false then 2 else 4 :=
    card_orbitList_toFinset_all
  induction c using Finset.induction with
  | empty =>
    rw [e6SplitCodeRoots_eq_biUnion]
    simp [ExcRaw.longCount]
  | insert a s ha ih =>
    rw [e6SplitCodeRoots_eq_biUnion, Finset.biUnion_insert, Finset.coe_union]
    have hdisj : Disjoint ((orbitList a).toFinset : Set (Fin Tag.E6.rank → ℤ))
        ((s.biUnion fun i => (orbitList i).toFinset : Finset _) : Set _) := by
      rw [Set.disjoint_left]
      intro δ h1 h2
      rw [Finset.mem_coe] at h1
      have h2' : δ ∈ s.biUnion (fun i => (orbitList i).toFinset) := by simpa using h2
      rw [Finset.mem_biUnion] at h2'
      obtain ⟨j, hj, hδj⟩ := h2'
      have hne : a ≠ j := by rintro rfl; exact ha hj
      exact Finset.disjoint_left.mp (disjoint_orbitList_toFinset hne) h1 hδj
    rw [Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _), Set.ncard_coe_finset]
    rw [show (((s.biUnion fun i => (orbitList i).toFinset : Finset _) : Set _)) =
        e6SplitCodeRoots s from (e6SplitCodeRoots_eq_biUnion s).symm, ih, hcard a]
    have hlong : ExcRaw.longCount 1 (insert a s) =
        ExcRaw.longCount 1 s + (if ExcRaw.tabFix1.getD a.val false = true then 1 else 0) := by
      unfold ExcRaw.longCount
      rw [Finset.filter_insert]
      by_cases hp : ExcRaw.tabFix1.getD a.val false = true
      · rw [if_pos hp, if_pos hp, Finset.card_insert_of_notMem (by simp [ha])]
      · rw [if_neg hp, if_neg hp]
        simp
    have hcs : (insert a s).card = s.card + 1 := Finset.card_insert_of_notMem ha
    have hLS : ExcRaw.longCount 1 s ≤ s.card := Finset.card_filter_le _ _
    rw [hlong, hcs]
    by_cases hp : ExcRaw.tabFix1.getD a.val false = true
    · have hp' : ExcRaw.tabFix1[a.val]?.getD false = true := hp
      simp [hp']
      omega
    · have hp' : ¬ ExcRaw.tabFix1[a.val]?.getD false = true := hp
      simp [hp']
      omega

@[expose] def e6SplitKerTab : List ℕ :=
  [761788872633875918308001, 4713161090046927831551, 1258607696196403527500449,
    264525157372574927187975, 397455070398978896249505, 1290499090786474450273553,
    464088108794903846787345, 2116136835026902533042183, 346084636050102472558665,
    1380278950650287959909449, 662040120924738465875217, 1290112467243401927530769,
    2115685756986374609928199, 33581160427770895106055, 2119760327422824888929799,
    347428613128402194474057, 692160051341815236413513, 662425105157517524476689,
    345407377032751192773193, 1291728957944398296261393, 264970056474525683158535,
    2413129272781504356811263, 9205357706930553343, 690814759212473330733641]

private def adjTab : List ℕ :=
  [9408373, 6406122, 1735933, 11729214, 9827229, 2583471,
    4650951, 4003830, 11068923, 13204211, 12230087, 14364207,
    13850334, 6073214, 15618940, 14132571, 12032691, 6806637,
    8380657, 16543621, 8240284, 16729514, 16710210, 15327001]

@[expose] def e6SplitCodeMasks : List ℕ :=
  [1, 2, 4, 8, 16, 21, 32, 64,
    128, 164, 256, 289, 400, 512, 577, 1024,
    1292, 2048, 3074, 4096, 4106, 6660, 8192, 8260,
    8720, 16384, 16704, 16928, 32768, 36944, 43009, 47701,
    65536, 65592, 66689, 67005, 98306, 131072, 131170, 163848,
    200704, 233594, 262144, 262336, 270368, 278544, 524288, 524928,
    532736, 540676, 786433, 1048576, 1056898, 1082368, 1116160, 1158275,
    1441796, 1450214, 2097152, 2117760, 2229248, 2392320, 2413008, 2623520,
    2644644, 2926881, 3145736, 3573004, 4194304, 4218888, 4327424, 4522496,
    4547128, 4719680, 4744524, 5048001, 5246976, 5708292, 6291458, 6949986,
    7368842, 8388608, 8389378, 8390664, 8393728, 8396558, 8536065, 8536931,
    9961488, 9970578, 10371093, 10551296, 10704001, 12126264, 12615680, 12773385,
    14193744, 15041282, 16777215]

private def KN (i : ℕ) : ℕ := e6SplitKerTab.getD i 0

private def K (i : ExcRaw.Root 1) : ℕ := KN i.val

private theorem nroots_one : ExcRaw.nroots 1 = 24 := rfl

private def rootOf (i : ℕ) (hi : i < 24) : ExcRaw.Root 1 :=
  ⟨i, by simpa [nroots_one] using hi⟩

private theorem rootVal_lt (i : ExcRaw.Root 1) : i.val < 24 := by
  simpa [nroots_one] using i.isLt

private def allLt (n : ℕ) (f : (i : ℕ) → i < n → Bool) : Bool :=
  (List.range n).all fun i => if h : i < n then f i h else false

private def anyLt (n : ℕ) (f : (i : ℕ) → i < n → Bool) : Bool :=
  (List.range n).any fun i => if h : i < n then f i h else false

private theorem allLt_eq {n : ℕ} {f : (i : ℕ) → i < n → Bool} :
    allLt n f = true ↔ ∀ i (hi : i < n), f i hi = true := by
  rw [allLt, List.all_eq_true]
  constructor
  · intro h i hi
    have := h i (List.mem_range.mpr hi)
    simpa [dif_pos hi] using this
  · intro h i hi
    rw [List.mem_range] at hi
    simp [dif_pos hi, h i hi]

private theorem anyLt_eq {n : ℕ} {f : (i : ℕ) → i < n → Bool} :
    anyLt n f = true ↔ ∃ (i : ℕ) (hi : i < n), f i hi = true := by
  rw [anyLt, List.any_eq_true]
  constructor
  · rintro ⟨i, hi, h⟩
    rw [List.mem_range] at hi
    exact ⟨i, hi, by simpa [dif_pos hi] using h⟩
  · rintro ⟨i, hi, h⟩
    exact ⟨i, List.mem_range.mpr hi, by simp [dif_pos hi, h]⟩

private def kerOK : Bool :=
  allLt 24 fun i hi =>
    decide (e6SplitKerTab.getD i 0 < 2 ^ 81) &&
      allLt 81 fun u _ =>
        (e6SplitKerTab.getD i 0).testBit u ==
          decide (ExcRaw.root 1 (rootOf i hi) (ExcRaw.vec 1 u) = 0)

private def adjOK : Bool :=
  allLt 24 fun i hi => allLt 24 fun j hj =>
    (adjTab.getD i 0).testBit j ==
      (decide (ExcRaw.pairing 1 (rootOf i hi) (rootOf j hj) ≠ 0) ||
        decide (ExcRaw.pairing 1 (rootOf j hj) (rootOf i hi) ≠ 0))

private theorem kerOK_spec (h : kerOK = true) (i : ExcRaw.Root 1) :
    K i < 2 ^ 81 ∧ ∀ u, u < 81 →
      ((K i).testBit u = true ↔ ExcRaw.root 1 i (ExcRaw.vec 1 u) = 0) := by
  have hi := allLt_eq.mp h i.val (rootVal_lt i)
  rw [Bool.and_eq_true] at hi
  have hbound : e6SplitKerTab.getD i.val 0 < 2 ^ 81 := of_decide_eq_true hi.1
  have hbits := allLt_eq.mp hi.2
  have hieq : (rootOf i.val (rootVal_lt i) : ExcRaw.Root 1) = i := Fin.ext rfl
  refine ⟨by simpa [K, KN] using hbound, ?_⟩
  intro u hu
  have h' : (e6SplitKerTab.getD i.val 0).testBit u =
      decide (ExcRaw.root 1 (rootOf i.val (rootVal_lt i)) (ExcRaw.vec 1 u) = 0) := by
    simpa using hbits u hu
  constructor
  · intro hh
    have hdec : decide (ExcRaw.root 1 (rootOf i.val (rootVal_lt i)) (ExcRaw.vec 1 u) = 0) = true := by
      rw [← h']
      exact hh
    have := of_decide_eq_true hdec
    simpa [hieq] using this
  · intro hh
    have hh' : ExcRaw.root 1 (rootOf i.val (rootVal_lt i)) (ExcRaw.vec 1 u) = 0 := by simpa [hieq] using hh
    have hdec : decide (ExcRaw.root 1 (rootOf i.val (rootVal_lt i)) (ExcRaw.vec 1 u) = 0) = true :=
      decide_eq_true hh'
    rw [show K i = e6SplitKerTab.getD i.val 0 from rfl, h', hdec]

private theorem adjOK_spec (h : adjOK = true) (i j : ExcRaw.Root 1) :
    (adjTab.getD i.val 0).testBit j.val = true ↔ ExcRaw.Adj 1 i j := by
  have hi := allLt_eq.mp h i.val (rootVal_lt i)
  have hij := allLt_eq.mp hi j.val (rootVal_lt j)
  have h' : (adjTab.getD i.val 0).testBit j.val =
      (decide (ExcRaw.pairing 1 (rootOf i.val (rootVal_lt i)) (rootOf j.val (rootVal_lt j)) ≠ 0) ||
        decide (ExcRaw.pairing 1 (rootOf j.val (rootVal_lt j)) (rootOf i.val (rootVal_lt i)) ≠ 0)) := by
    simpa using hij
  have hieq : (rootOf i.val (rootVal_lt i) : ExcRaw.Root 1) = i := Fin.ext rfl
  have hjeq : (rootOf j.val (rootVal_lt j) : ExcRaw.Root 1) = j := Fin.ext rfl
  have hiff : ((adjTab.getD i.val 0).testBit j.val = true) ↔
      (ExcRaw.pairing 1 (rootOf i.val (rootVal_lt i)) (rootOf j.val (rootVal_lt j)) ≠ 0 ∨
        ExcRaw.pairing 1 (rootOf j.val (rootVal_lt j)) (rootOf i.val (rootVal_lt i)) ≠ 0) := by
    rw [h', Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq]
  simpa [ExcRaw.Adj, hieq, hjeq] using hiff

private theorem kerOK_eq : kerOK = true := by decide +kernel

theorem e6SplitKerTab_getD_lt (i : ExcRaw.Root 1) : e6SplitKerTab.getD i.val 0 < 2 ^ 81 :=
  (kerOK_spec kerOK_eq i).1

theorem testBit_e6SplitKerTab_iff (i : ExcRaw.Root 1) {u : ℕ} (hu : u < 81) :
    (e6SplitKerTab.getD i.val 0).testBit u = true ↔ ExcRaw.root 1 i (ExcRaw.vec 1 u) = 0 :=
  (kerOK_spec kerOK_eq i).2 u hu

private theorem adjOK_eq : adjOK = true := by decide +kernel

private def clMaskN (M : ℕ) : ℕ :=
  (List.range 24).foldl (fun acc t =>
    if M &&& e6SplitKerTab.getD t 0 == M then acc ||| 1 <<< t else acc) 0

private theorem foldl_mask_testBit (l : List ℕ) (p : ℕ → Bool) (acc j : ℕ) :
    (l.foldl (fun acc t => if p t then acc ||| 1 <<< t else acc) acc).testBit j =
      (acc.testBit j || if j ∈ l then p j else false) := by
  induction l generalizing acc with
  | nil => simp
  | cons a l ih =>
    rw [List.foldl_cons, ih]
    by_cases hp : p a = true
    · rw [if_pos hp, Nat.testBit_lor, Nat.one_shiftLeft, Nat.testBit_two_pow]
      by_cases hja : j = a
      · subst hja
        simp [hp]
      · have haj : a ≠ j := fun h => hja h.symm
        simp [hja, haj, List.mem_cons]
    · rw [if_neg hp]
      by_cases hja : j = a
      · subst hja
        simp [hp]
      · simp [hja, List.mem_cons]

private theorem clMaskN_testBit (M t : ℕ) :
    (clMaskN M).testBit t = true ↔ t < 24 ∧ M &&& e6SplitKerTab.getD t 0 = M := by
  rw [clMaskN, foldl_mask_testBit, Nat.zero_testBit, Bool.false_or]
  by_cases ht : t < 24
  · rw [if_pos (List.mem_range.mpr ht), beq_iff_eq]
    exact ⟨fun h => ⟨ht, h⟩, fun h => h.2⟩
  · rw [if_neg (fun h => ht (List.mem_range.mp h))]
    simp [ht]

private theorem land_eq_iff_testBit {M N : ℕ} :
    M &&& N = M ↔ ∀ j, M.testBit j = true → N.testBit j = true := by
  constructor
  · intro h j hj
    have := congrArg (fun z => z.testBit j) h
    rw [Nat.testBit_land] at this
    simpa [hj] using this
  · intro h
    apply Nat.eq_of_testBit_eq
    intro j
    cases hMj : M.testBit j <;> simp_all

private theorem land_eq_vanish (b1 b2 b3 t : ExcRaw.Root 1) :
    (K b1 &&& K b2 &&& K b3) &&& K t = (K b1 &&& K b2 &&& K b3) ↔
      ExcRaw.Vanish 1 (ExcRaw.cent 1 ({b1, b2, b3} : Finset (ExcRaw.Root 1))) t := by
  set M := K b1 &&& K b2 &&& K b3
  have h1 := (kerOK_spec kerOK_eq b1).1
  have hM : M < 2 ^ 81 := by
    exact lt_of_le_of_lt (le_trans Nat.and_le_left Nat.and_le_left) h1
  rw [land_eq_iff_testBit]
  constructor
  · intro hbits v hv
    rw [mem_cent_iff] at hv
    have hcode : ExcRaw.code 1 v < 81 := by
      have h := ExcRaw.code_lt 1 v
      rw [show ExcRaw.dim 1 = 4 from rfl] at h
      norm_num at h
      exact h
    have hvec : ExcRaw.vec 1 (ExcRaw.code 1 v) = v := ExcRaw.vec_code 1 v
    have hMbit : M.testBit (ExcRaw.code 1 v) = true := by
      have hb1 : (K b1).testBit (ExcRaw.code 1 v) = true := by
        rw [(kerOK_spec kerOK_eq b1).2 _ hcode, hvec]
        exact hv b1 (by simp)
      have hb2 : (K b2).testBit (ExcRaw.code 1 v) = true := by
        rw [(kerOK_spec kerOK_eq b2).2 _ hcode, hvec]
        exact hv b2 (by simp)
      have hb3 : (K b3).testBit (ExcRaw.code 1 v) = true := by
        rw [(kerOK_spec kerOK_eq b3).2 _ hcode, hvec]
        exact hv b3 (by simp)
      rw [show M = K b1 &&& K b2 &&& K b3 from rfl, Nat.testBit_land, Nat.testBit_land,
        hb1, hb2, hb3]
      rfl
    have htbit := hbits (ExcRaw.code 1 v) hMbit
    rw [(kerOK_spec kerOK_eq t).2 _ hcode, hvec] at htbit
    exact htbit
  · intro hv u hu
    have hu81 : u < 81 := by
      by_contra h
      have hM0 : M.testBit u = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hM (Nat.pow_le_pow_right (by norm_num) (by omega)))
      rw [hM0] at hu
      exact Bool.noConfusion hu
    have hbi : ∀ b ∈ ({b1, b2, b3} : Finset (ExcRaw.Root 1)),
        ExcRaw.root 1 b (ExcRaw.vec 1 u) = 0 := by
      intro b hb
      have hbit : (K b).testBit u = true := by
        have hu' : ((K b1 &&& K b2) &&& K b3).testBit u = true := hu
        rw [Nat.testBit_land, Nat.testBit_land] at hu'
        have h12 := (Bool.and_eq_true_iff.mp hu').1
        have hb1' : (K b1).testBit u = true := (Bool.and_eq_true_iff.mp h12).1
        have hb2' : (K b2).testBit u = true := (Bool.and_eq_true_iff.mp h12).2
        have hb3' : (K b3).testBit u = true := (Bool.and_eq_true_iff.mp hu').2
        simp only [Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with rfl | rfl | rfl
        · exact hb1'
        · exact hb2'
        · exact hb3'
      exact ((kerOK_spec kerOK_eq b).2 u hu81).mp hbit
    have hmem : ExcRaw.vec 1 u ∈ ExcRaw.cent 1 ({b1, b2, b3} : Finset (ExcRaw.Root 1)) := by
      rw [mem_cent_iff]
      exact hbi
    have ht := hv (ExcRaw.vec 1 u) hmem
    exact ((kerOK_spec kerOK_eq t).2 u hu81).2 ht

private theorem clMaskN_spec (b1 b2 b3 t : ExcRaw.Root 1) :
    (clMaskN (K b1 &&& K b2 &&& K b3)).testBit t = true ↔
      ExcRaw.Vanish 1 (ExcRaw.cent 1 ({b1, b2, b3} : Finset (ExcRaw.Root 1))) t := by
  rw [clMaskN_testBit]
  constructor
  · rintro ⟨-, h⟩
    exact (land_eq_vanish b1 b2 b3 t).mp h
  · intro h
    exact ⟨t.isLt, (land_eq_vanish b1 b2 b3 t).mpr h⟩

private theorem cent_le_cent_of_subset {B B' : Finset (ExcRaw.Root 1)} (h : B ⊆ B') :
    ExcRaw.cent 1 B' ≤ ExcRaw.cent 1 B := by
  intro v hv
  rw [mem_cent_iff] at hv ⊢
  exact fun i hi => hv i (h hi)

private theorem subset_one {a : ExcRaw.Root 1} {c : Finset (ExcRaw.Root 1)} (h : a ∈ c) :
    ({a} : Finset (ExcRaw.Root 1)) ⊆ c := by
  intro x hx
  rw [Finset.mem_singleton] at hx
  subst hx
  exact h

private theorem subset_pair {a b : ExcRaw.Root 1} {c : Finset (ExcRaw.Root 1)}
    (ha : a ∈ c) (hb : b ∈ c) : ({a, b} : Finset (ExcRaw.Root 1)) ⊆ c := by
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact ha
  · exact hb

private theorem subset_three {a b d : ExcRaw.Root 1} {c : Finset (ExcRaw.Root 1)}
    (ha : a ∈ c) (hb : b ∈ c) (hd : d ∈ c) :
    ({a, b, d} : Finset (ExcRaw.Root 1)) ⊆ c := by
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl
  · exact ha
  · exact hb
  · exact hd

private theorem subset_four {a b d e : ExcRaw.Root 1} {c : Finset (ExcRaw.Root 1)}
    (ha : a ∈ c) (hb : b ∈ c) (hd : d ∈ c) (he : e ∈ c) :
    ({a, b, d, e} : Finset (ExcRaw.Root 1)) ⊆ c := by
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact ha
  · exact hb
  · exact hd
  · exact he

private theorem cent_insert_lt {B : Finset (ExcRaw.Root 1)} {b : ExcRaw.Root 1}
    (hb : ¬ ExcRaw.Vanish 1 (ExcRaw.cent 1 B) b) :
    ExcRaw.cent 1 (insert b B) < ExcRaw.cent 1 B := by
  refine lt_of_le_of_ne (cent_le_cent_of_subset (Finset.subset_insert b B)) ?_
  intro heq
  apply hb
  intro v hv
  have hv' : v ∈ ExcRaw.cent 1 (insert b B) := by rw [heq]; exact hv
  rw [mem_cent_iff] at hv'
  exact hv' b (Finset.mem_insert_self b B)

private theorem cent_singleton_lt_top (b : ExcRaw.Root 1) :
    ExcRaw.cent 1 ({b} : Finset (ExcRaw.Root 1)) < ⊤ := by
  refine lt_of_le_of_ne le_top ?_
  intro heq
  have hmem : ExcRaw.coroot 1 b ∈ ExcRaw.cent 1 ({b} : Finset (ExcRaw.Root 1)) := by
    rw [heq]
    exact Submodule.mem_top
  rw [mem_cent_iff] at hmem
  have h0 := hmem b (Finset.mem_singleton_self b)
  rw [ExcRaw.root_coroot] at h0
  exact (by decide : (2 : ZMod 3) ≠ 0) h0

private theorem finrank_V_one : Module.finrank (ZMod 3) (ExcRaw.V 1) = 4 := by
  change Module.finrank (ZMod 3) (Fin 4 → ZMod 3) = 4
  exact Module.finrank_fin_fun (ZMod 3)

private theorem finrank_cent_lt_four (B : Finset (ExcRaw.Root 1))
    (h : ExcRaw.cent 1 B < ⊤) : Module.finrank (ZMod 3) (ExcRaw.cent 1 B) < 4 := by
  have hlt := Submodule.finrank_lt_finrank_of_lt h
  rwa [finrank_top, finrank_V_one] at hlt

private theorem exists_three_or_univ {U : Submodule (ZMod 3) (ExcRaw.V 1)}
    {c : Finset (ExcRaw.Root 1)} (hc : ExcRaw.occurs 1 U c) :
    c = Finset.univ ∨ ∃ b1 b2 b3 : ExcRaw.Root 1,
      ∀ t : ExcRaw.Root 1, t ∈ c ↔
        ExcRaw.Vanish 1 (ExcRaw.cent 1 ({b1, b2, b3} : Finset (ExcRaw.Root 1))) t := by
  classical
  have hcentc : ∀ t : ExcRaw.Root 1, t ∈ c ↔ ExcRaw.Vanish 1 (ExcRaw.cent 1 c) t :=
    fun t => ExcRaw.mem_iff_vanish_of_occurs (ExcRaw.occurs_cent_of_occurs hc) rfl t
  obtain ⟨b1, hb1⟩ := hc.1
  have hdup1 : ({b1, b1, b1} : Finset (ExcRaw.Root 1)) = {b1} := by
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  by_cases h1 : ∀ t ∈ c, ExcRaw.Vanish 1 (ExcRaw.cent 1 ({b1} : Finset (ExcRaw.Root 1))) t
  · refine Or.inr ⟨b1, b1, b1, ?_⟩
    intro t
    constructor
    · intro ht
      simpa [hdup1] using h1 t ht
    · intro ht
      have ht' : ExcRaw.Vanish 1 (ExcRaw.cent 1 ({b1} : Finset _)) t := by simpa [hdup1] using ht
      refine (hcentc t).mpr ?_
      intro v hv
      exact ht' v (cent_le_cent_of_subset (subset_one hb1) hv)
  · push Not at h1
    obtain ⟨b2, hb2c, hb2v⟩ := h1
    have hdup2 : ({b1, b2, b2} : Finset (ExcRaw.Root 1)) = {b1, b2} := by
      ext x
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    by_cases h2 : ∀ t ∈ c,
        ExcRaw.Vanish 1 (ExcRaw.cent 1 ({b1, b2} : Finset (ExcRaw.Root 1))) t
    · refine Or.inr ⟨b1, b2, b2, ?_⟩
      intro t
      constructor
      · intro ht
        simpa [hdup2] using h2 t ht
      · intro ht
        have ht' : ExcRaw.Vanish 1 (ExcRaw.cent 1 ({b1, b2} : Finset _)) t := by
          simpa [hdup2] using ht
        refine (hcentc t).mpr ?_
        intro v hv
        exact ht' v (cent_le_cent_of_subset (subset_pair hb1 hb2c) hv)
    · push Not at h2
      obtain ⟨b3, hb3c, hb3v⟩ := h2
      by_cases h3 : ∀ t ∈ c,
          ExcRaw.Vanish 1 (ExcRaw.cent 1 ({b1, b2, b3} : Finset (ExcRaw.Root 1))) t
      · refine Or.inr ⟨b1, b2, b3, ?_⟩
        intro t
        constructor
        · exact h3 t
        · intro ht
          refine (hcentc t).mpr ?_
          intro v hv
          exact ht v (cent_le_cent_of_subset (subset_three hb1 hb2c hb3c) hv)
      · push Not at h3
        obtain ⟨b4, hb4c, hb4v⟩ := h3
        have hlt1 : ExcRaw.cent 1 ({b1} : Finset (ExcRaw.Root 1)) < ⊤ :=
          cent_singleton_lt_top b1
        have hset2 : (insert b2 ({b1} : Finset (ExcRaw.Root 1))) = ({b1, b2} : Finset _) := by
          ext x
          simp only [Finset.mem_insert, Finset.mem_singleton]
          tauto
        have hset3 : (insert b3 ({b1, b2} : Finset (ExcRaw.Root 1))) =
            ({b1, b2, b3} : Finset _) := by
          ext x
          simp only [Finset.mem_insert, Finset.mem_singleton]
          tauto
        have hset4 : (insert b4 ({b1, b2, b3} : Finset (ExcRaw.Root 1))) =
            ({b1, b2, b3, b4} : Finset _) := by
          ext x
          simp only [Finset.mem_insert, Finset.mem_singleton]
          tauto
        have hlt2 : ExcRaw.cent 1 ({b1, b2} : Finset (ExcRaw.Root 1)) <
            ExcRaw.cent 1 ({b1} : Finset _) := by
          rw [← hset2]
          exact cent_insert_lt (B := ({b1} : Finset _)) (b := b2) hb2v
        have hlt3 : ExcRaw.cent 1 ({b1, b2, b3} : Finset (ExcRaw.Root 1)) <
            ExcRaw.cent 1 ({b1, b2} : Finset _) := by
          rw [← hset3]
          exact cent_insert_lt (B := ({b1, b2} : Finset _)) (b := b3) hb3v
        have hlt4 : ExcRaw.cent 1 ({b1, b2, b3, b4} : Finset (ExcRaw.Root 1)) <
            ExcRaw.cent 1 ({b1, b2, b3} : Finset _) := by
          rw [← hset4]
          exact cent_insert_lt (B := ({b1, b2, b3} : Finset _)) (b := b4) hb4v
        have d1 : Module.finrank (ZMod 3) (ExcRaw.cent 1 ({b1} : Finset _)) < 4 :=
          finrank_cent_lt_four _ hlt1
        have d2 : Module.finrank (ZMod 3) (ExcRaw.cent 1 ({b1, b2} : Finset _)) <
            Module.finrank (ZMod 3) (ExcRaw.cent 1 ({b1} : Finset _)) :=
          Submodule.finrank_lt_finrank_of_lt hlt2
        have d3 : Module.finrank (ZMod 3) (ExcRaw.cent 1 ({b1, b2, b3} : Finset _)) <
            Module.finrank (ZMod 3) (ExcRaw.cent 1 ({b1, b2} : Finset _)) :=
          Submodule.finrank_lt_finrank_of_lt hlt3
        have d4 : Module.finrank (ZMod 3) (ExcRaw.cent 1 ({b1, b2, b3, b4} : Finset _)) <
            Module.finrank (ZMod 3) (ExcRaw.cent 1 ({b1, b2, b3} : Finset _)) :=
          Submodule.finrank_lt_finrank_of_lt hlt4
        have d0 : Module.finrank (ZMod 3) (ExcRaw.cent 1 ({b1, b2, b3, b4} : Finset _)) = 0 := by
          omega
        have hbot : ExcRaw.cent 1 ({b1, b2, b3, b4} : Finset (ExcRaw.Root 1)) = ⊥ :=
          Submodule.finrank_eq_zero.mp d0
        refine Or.inl (Finset.eq_univ_of_forall fun t => ?_)
        refine (hcentc t).mpr ?_
        intro v hv
        have hv' := cent_le_cent_of_subset
          (B := ({b1, b2, b3, b4} : Finset _)) (subset_four hb1 hb2c hb3c hb4c) hv
        rw [hbot] at hv'
        have hv0 : v = 0 := (Submodule.mem_bot (ZMod 3)).mp hv'
        rw [hv0]
        simp

private def growN (F S : ℕ) : ℕ :=
  (List.range 24).foldl (fun acc t =>
    if S.testBit t then acc ||| (adjTab.getD t 0 &&& F) else acc) S

private def closeN (F : ℕ) : ℕ :=
  let rec go (fuel : ℕ) (S : ℕ) : ℕ :=
    match fuel with
    | 0 => S
    | n + 1 =>
      let S' := growN F S
      if S' == S then S else go n S'
  go 24 (1 <<< ((List.range 24).find? (fun t => F.testBit t)).getD 0)

private def closedN (F S : ℕ) : Bool :=
  decide (S &&& F = S) &&
    anyLt 24 (fun t _ => S.testBit t) &&
    anyLt 24 (fun t _ => F.testBit t && !S.testBit t) &&
    allLt 24 (fun t _ => !S.testBit t ||
      decide ((adjTab.getD t 0 &&& F) &&& S = adjTab.getD t 0 &&& F))

private def discN (F : ℕ) : Bool := closedN F (closeN F)

private theorem closedN_sound {F S : ℕ} (h : closedN F S = true) (P : ExcRaw.Root 1 → Prop) :
    ¬ ExcRaw.IsComp 1 P (ExcRaw.ofMask 1 F) := by
  rw [closedN] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hSF, hneS⟩, hproper⟩, hclosed⟩ := h
  intro hcomp
  let T : Finset (ExcRaw.Root 1) := ExcRaw.ofMask 1 S
  have hTsub : T ⊆ ExcRaw.ofMask 1 F := by
    intro t ht
    rw [ExcRaw.mem_ofMask] at ht ⊢
    have hbit := congrArg (fun z => z.testBit t) hSF
    rw [Nat.testBit_land] at hbit
    simpa [ht] using hbit
  have hTne : T.Nonempty := by
    obtain ⟨t, ht, hbit⟩ := anyLt_eq.mp hneS
    refine ⟨rootOf t ht, ?_⟩
    change rootOf t ht ∈ ExcRaw.ofMask 1 S
    rw [ExcRaw.mem_ofMask]
    simpa [rootOf] using hbit
  have hTproper : ∃ t ∈ ExcRaw.ofMask 1 F, t ∉ T := by
    obtain ⟨t, ht, hbit⟩ := anyLt_eq.mp hproper
    rw [Bool.and_eq_true] at hbit
    obtain ⟨hFt, hSt⟩ := hbit
    have hSt' : S.testBit t = false := by simpa using hSt
    refine ⟨rootOf t ht, ?_, ?_⟩
    · rw [ExcRaw.mem_ofMask]
      simpa [rootOf] using hFt
    · intro hmem
      have := ExcRaw.mem_ofMask.mp hmem
      change S.testBit t = true at this
      rw [hSt'] at this
      exact Bool.noConfusion this
  have hTclosed : ∀ i ∈ T, ∀ j ∈ ExcRaw.ofMask 1 F, ExcRaw.Adj 1 i j → j ∈ T := by
    intro i hiT j hjF hadj
    have hiS : S.testBit i = true := by simpa [T, ExcRaw.mem_ofMask] using hiT
    have hjF' : F.testBit j = true := by simpa [ExcRaw.mem_ofMask] using hjF
    have hstep := allLt_eq.mp hclosed i.val (rootVal_lt i)
    have hdec : decide (((adjTab.getD i.val 0 &&& F) &&& S) =
        (adjTab.getD i.val 0 &&& F)) = true := by
      simpa [hiS] using hstep
    have heq : ((adjTab.getD i.val 0 &&& F) &&& S) =
        (adjTab.getD i.val 0 &&& F) := of_decide_eq_true hdec
    have hadjbit : (adjTab.getD i.val 0).testBit j.val = true :=
      (adjOK_spec adjOK_eq i j).2 hadj
    have hX : (adjTab.getD i.val 0 &&& F).testBit j.val = true := by
      rw [Nat.testBit_land, hadjbit, hjF']
      rfl
    have hSj : S.testBit j.val = true := (land_eq_iff_testBit.mp heq) j.val hX
    change j ∈ ExcRaw.ofMask 1 S
    rw [ExcRaw.mem_ofMask]
    exact hSj
  have hTeq : T = ExcRaw.ofMask 1 F := hcomp.2.2.2 T hTsub hTne hTclosed
  obtain ⟨t, htF, htT⟩ := hTproper
  exact htT (hTeq.symm ▸ htF)

private theorem discN_sound {F : ℕ} (h : discN F = true) (P : ExcRaw.Root 1 → Prop) :
    ¬ ExcRaw.IsComp 1 P (ExcRaw.ofMask 1 F) := by
  exact closedN_sound (by simpa [discN] using h) P

private def tripleChunk (lo hi : ℕ) : Bool :=
  allLt 24 fun i _ =>
    !(decide (lo ≤ i) && decide (i ≤ hi)) ||
      allLt 24 fun j _ =>
        !(decide (i ≤ j)) ||
          allLt 24 fun k _ =>
            !(decide (j ≤ k)) ||
              (let F := clMaskN (KN i &&& KN j &&& KN k)
               e6SplitCodeMasks.elem F || discN F)

private theorem tripleChunk_0_1_eq : tripleChunk 0 1 = true := by decide +kernel

private theorem tripleChunk_2_4_eq : tripleChunk 2 4 = true := by decide +kernel

private theorem tripleChunk_5_8_eq : tripleChunk 5 8 = true := by decide +kernel

private theorem tripleChunk_9_23_eq : tripleChunk 9 23 = true := by decide +kernel

private theorem tripleChunk_spec {lo hi : ℕ} (h : tripleChunk lo hi = true)
    {i j k : ℕ} (hlo : lo ≤ i) (hhi : i ≤ hi) (hij : i ≤ j) (hjk : j ≤ k)
    (hi : i < 24) (hj : j < 24) (hk : k < 24) :
    (let F := clMaskN (KN i &&& KN j &&& KN k)
     e6SplitCodeMasks.elem F || discN F) = true := by
  rw [tripleChunk] at h
  have h1 := allLt_eq.mp h i hi
  have h1' : (allLt 24 fun j _ =>
      !(decide (i ≤ j)) ||
        allLt 24 fun k _ =>
          !(decide (j ≤ k)) ||
            (let F := clMaskN (KN i &&& KN j &&& KN k)
             e6SplitCodeMasks.elem F || discN F)) = true := by
    simpa [hlo, hhi] using h1
  have h2 := allLt_eq.mp h1' j hj
  have h2' : (allLt 24 fun k _ =>
      !(decide (j ≤ k)) ||
        (let F := clMaskN (KN i &&& KN j &&& KN k)
         e6SplitCodeMasks.elem F || discN F)) = true := by
    simpa [hij] using h2
  have h3 := allLt_eq.mp h2' k hk
  simpa [hjk] using h3

private theorem tripleOK_spec_sorted (i j k : ExcRaw.Root 1)
    (hij : i.val ≤ j.val) (hjk : j.val ≤ k.val) :
    e6SplitCodeMasks.elem (clMaskN (K i &&& K j &&& K k)) = true ∨
      discN (clMaskN (K i &&& K j &&& K k)) = true := by
  have hi := rootVal_lt i
  have hj := rootVal_lt j
  have hk := rootVal_lt k
  by_cases h1 : i.val ≤ 1
  · have hspec := tripleChunk_spec tripleChunk_0_1_eq (lo := 0) (hi := 1)
      (i := i.val) (j := j.val) (k := k.val) (by omega) h1 hij hjk hi hj hk
    simpa [K, Bool.or_eq_true_iff] using hspec
  · by_cases h2 : i.val ≤ 4
    · have hspec := tripleChunk_spec tripleChunk_2_4_eq (lo := 2) (hi := 4)
        (i := i.val) (j := j.val) (k := k.val) (by omega) h2 hij hjk hi hj hk
      simpa [K, Bool.or_eq_true_iff] using hspec
    · by_cases h3 : i.val ≤ 8
      · have hspec := tripleChunk_spec tripleChunk_5_8_eq (lo := 5) (hi := 8)
          (i := i.val) (j := j.val) (k := k.val) (by omega) h3 hij hjk hi hj hk
        simpa [K, Bool.or_eq_true_iff] using hspec
      · have hspec := tripleChunk_spec tripleChunk_9_23_eq (lo := 9) (hi := 23)
          (i := i.val) (j := j.val) (k := k.val) (by omega) (by omega) hij hjk hi hj hk
        simpa [K, Bool.or_eq_true_iff] using hspec

private theorem tripleOK_spec (i j k : ExcRaw.Root 1) :
    e6SplitCodeMasks.elem (clMaskN (K i &&& K j &&& K k)) = true ∨
      discN (clMaskN (K i &&& K j &&& K k)) = true := by
  by_cases hab : i.val ≤ j.val
  · by_cases hbc : j.val ≤ k.val
    · exact tripleOK_spec_sorted i j k hab hbc
    · by_cases hac : i.val ≤ k.val
      · have hs := tripleOK_spec_sorted (i := i) (j := k) (k := j) hac (by omega)
        simpa [show K i &&& K j &&& K k = K i &&& K k &&& K j by ac_rfl] using hs
      · have hs := tripleOK_spec_sorted (i := k) (j := i) (k := j) (by omega) hab
        simpa [show K i &&& K j &&& K k = K k &&& K i &&& K j by ac_rfl] using hs
  · have hba : j.val ≤ i.val := by omega
    by_cases hbc : j.val ≤ k.val
    · by_cases hac : i.val ≤ k.val
      · have hs := tripleOK_spec_sorted (i := j) (j := i) (k := k) hba hac
        simpa [show K i &&& K j &&& K k = K j &&& K i &&& K k by ac_rfl] using hs
      · have hs := tripleOK_spec_sorted (i := j) (j := k) (k := i) hbc (by omega)
        simpa [show K i &&& K j &&& K k = K j &&& K k &&& K i by ac_rfl] using hs
    · have hcb : k.val ≤ j.val := by omega
      have hs := tripleOK_spec_sorted (i := k) (j := j) (k := i) hcb (by omega)
      simpa [show K i &&& K j &&& K k = K k &&& K j &&& K i by ac_rfl] using hs

private theorem ofMask_univ : ExcRaw.ofMask 1 16777215 = Finset.univ := by
  ext t
  rw [ExcRaw.mem_ofMask]
  have ht : (t : ℕ) < 24 := t.isLt
  have h : (16777215 : ℕ) = 2 ^ 24 - 1 := by norm_num
  rw [h, Nat.testBit_two_pow_sub_one]
  simp [ht]

theorem exists_mem_e6SplitCodeMasks_of_occurs {U : Submodule (ZMod 3) (ExcRaw.V 1)}
    {c : Finset (ExcRaw.Root 1)} (hc : ExcRaw.occurs 1 U c) :
    ∃ n ∈ e6SplitCodeMasks, c = ExcRaw.ofMask 1 n := by
  classical
  rcases exists_three_or_univ hc with rfl | ⟨b1, b2, b3, hcl⟩
  · refine ⟨16777215, ?_, ?_⟩
    · decide
    · rw [ofMask_univ]
  · let F := clMaskN (K b1 &&& K b2 &&& K b3)
    have hcF : c = ExcRaw.ofMask 1 F := by
      ext t
      rw [hcl t, ExcRaw.mem_ofMask]
      change ExcRaw.Vanish 1 (ExcRaw.cent 1 ({b1, b2, b3} : Finset (ExcRaw.Root 1))) t ↔
        (clMaskN (K b1 &&& K b2 &&& K b3)).testBit t = true
      exact (clMaskN_spec b1 b2 b3 t).symm
    rcases tripleOK_spec b1 b2 b3 with hcode | hdisc
    · exact ⟨F, List.elem_iff.mp hcode, hcF⟩
    · exfalso
      exact discN_sound hdisc (ExcRaw.Vanish 1 U) (hcF ▸ hc)

private def rootsN (n : ℕ) : List (Fin Tag.E6.rank → ℤ) :=
  (List.range 24).flatMap fun i =>
    if h : i < 24 then
      (if n.testBit i then orbitList (rootOf i h) else [])
    else []

private theorem mem_rootsN_iff {n : ℕ} {δ : Fin Tag.E6.rank → ℤ} :
    δ ∈ rootsN n ↔ δ ∈ e6SplitCodeRoots (ExcRaw.ofMask 1 n) := by
  rw [e6SplitCodeRoots_eq_biUnion]
  simp only [Finset.mem_coe, Finset.mem_biUnion, List.mem_toFinset]
  constructor
  · intro h
    rw [rootsN, List.mem_flatMap] at h
    obtain ⟨i, hi, hδ⟩ := h
    rw [List.mem_range] at hi
    rw [dif_pos hi] at hδ
    by_cases hn : n.testBit i = true
    · refine ⟨rootOf i hi, ?_, ?_⟩
      · rw [ExcRaw.mem_ofMask]
        exact hn
      · simpa [hn] using hδ
    · simp [hn] at hδ
  · rintro ⟨i, hi, hδ⟩
    rw [rootsN, List.mem_flatMap]
    refine ⟨i.val, List.mem_range.mpr (rootVal_lt i), ?_⟩
    rw [dif_pos (rootVal_lt i)]
    have hi' : n.testBit i = true := by simpa [ExcRaw.mem_ofMask] using hi
    simpa [rootOf, hi'] using hδ

private def sigmaE6 (v : Fin Tag.E6.rank → ℤ) : Fin Tag.E6.rank → ℤ :=
  permLattice TwistTag.E6.perm v

private def rhoE6 (v : Fin Tag.E6.rank → ℤ) : Fin Tag.E6.rank → ℤ :=
  -permLattice TwistTag.E6.perm v

@[expose] def iformE6 (x y : Fin Tag.E6.rank → ℤ) : ℤ :=
  2 * (x 0 * y 0 + x 1 * y 1 + x 2 * y 2 + x 3 * y 3 + x 4 * y 4 + x 5 * y 5) -
    (x 0 * y 2 + x 2 * y 0) - (x 1 * y 3 + x 3 * y 1) - (x 2 * y 3 + x 3 * y 2) -
    (x 3 * y 4 + x 4 * y 3) - (x 4 * y 5 + x 5 * y 4)

private def reflE6 (b x : Fin Tag.E6.rank → ℤ) : Fin Tag.E6.rank → ℤ :=
  x - iformE6 b x • b

private def cartanE6 (i j : Fin Tag.E6.rank) : ℤ :=
  if i = j then 2
  else if (i.val = 0 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 0) ∨
      (i.val = 1 ∧ j.val = 3) ∨ (i.val = 3 ∧ j.val = 1) ∨
      (2 ≤ i.val ∧ j.val = i.val + 1) ∨ (2 ≤ j.val ∧ i.val = j.val + 1) then -1 else 0

private theorem cartan_E6_apply (i j : Fin Tag.E6.rank) :
    Tag.E6.cartan i j = cartanE6 i j := rfl

private theorem sum_E6 {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    (∑ i : Fin Tag.E6.rank, f i.val) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  rw [Fin.sum_univ_eq_sum_range f Tag.E6.rank]
  rw [show Tag.E6.rank = 6 from rfl]
  simp [Finset.sum_range_succ]

private theorem sum_E6_fin {M : Type*} [AddCommMonoid M] (g : Fin Tag.E6.rank → M) :
    (∑ i, g i) = g 0 + g 1 + g 2 + g 3 + g 4 + g 5 := by
  have h := sum_E6 (fun n => if hn : n < Tag.E6.rank then g ⟨n, hn⟩ else 0)
  rw [show (∑ i : Fin Tag.E6.rank, g i) =
      ∑ i : Fin Tag.E6.rank, (if hn : i.val < Tag.E6.rank then g ⟨i.val, hn⟩ else 0) from by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [dif_pos i.isLt]]
  rw [h]
  simp [Tag.rank]
  rfl

theorem iform_eq_iformE6 (x y : Fin Tag.E6.rank → ℤ) :
    iform x y = iformE6 x y := by
  have hsym : Tag.E6.symmetrizedCartan = Tag.E6.cartan := by
    change Tag.E6.symmetrizer * Tag.E6.cartan = Tag.E6.cartan
    rw [show Tag.E6.symmetrizer = 1 from rfl, one_mul]
  rw [iform, hsym]
  simp only [cartan_E6_apply]
  let xF : ℕ → ℤ := fun i => if h : i < Tag.E6.rank then x ⟨i, h⟩ else 0
  let yF : ℕ → ℤ := fun j => if h : j < Tag.E6.rank then y ⟨j, h⟩ else 0
  let cF : ℕ → ℕ → ℤ := fun i j =>
    if hi : i < Tag.E6.rank then
      if hj : j < Tag.E6.rank then cartanE6 ⟨i, hi⟩ ⟨j, hj⟩ else 0
    else 0
  change (∑ i : Fin Tag.E6.rank, ∑ j : Fin Tag.E6.rank,
      xF i.val * cF i.val j.val * yF j.val) =
    2 * (xF 0 * yF 0 + xF 1 * yF 1 + xF 2 * yF 2 + xF 3 * yF 3 + xF 4 * yF 4 +
      xF 5 * yF 5) - (xF 0 * yF 2 + xF 2 * yF 0) - (xF 1 * yF 3 + xF 3 * yF 1) -
      (xF 2 * yF 3 + xF 3 * yF 2) - (xF 3 * yF 4 + xF 4 * yF 3) -
      (xF 4 * yF 5 + xF 5 * yF 4)
  simp only [sum_E6_fin]
  simp [xF, yF, cF, cartanE6, Tag.rank, dif_pos]
  ring

private theorem iform_e6SplitRoot_self (i : ExcRaw.Root 1) :
    iform (e6SplitRoot i) (e6SplitRoot i) = 2 := by
  rw [iform_eq_iformE6]
  revert i
  decide +kernel

private def typ (n : ℕ) : ℕ × ℕ :=
  ((ExcRaw.ofMask 1 n).card, ExcRaw.longCount 1 (ExcRaw.ofMask 1 n))

private def typeFinset : Finset (ℕ × ℕ) :=
  {(1, 0), (3, 0), (1, 1), (3, 3), (4, 2), (9, 3), (9, 6), (24, 12)}

private def splitOK (n : ℕ) : Bool :=
  anyLt 24 fun i0 hi0 =>
    let γ0 := e6SplitRoot (rootOf i0 hi0)
    n.testBit i0 && iformE6 (sigmaE6 γ0) γ0 == 0 &&
      (rootsN n).all fun a => (rootsN n).all fun b =>
        iformE6 a γ0 == 0 || iformE6 b γ0 != 0 || iformE6 a b == 0

private theorem splitOK_sound {n : ℕ} (h : splitOK n = true) :
    ∃ Y ⊆ e6SplitCodeRoots (ExcRaw.ofMask 1 n), Y.Nonempty ∧
      (e6SplitCodeRoots (ExcRaw.ofMask 1 n) \ Y).Nonempty ∧
        ∀ α ∈ Y, ∀ β ∈ e6SplitCodeRoots (ExcRaw.ofMask 1 n) \ Y, iform α β = 0 := by
  rw [splitOK] at h
  obtain ⟨i0, hi0lt, hi0⟩ := anyLt_eq.mp h
  simp only [Bool.and_eq_true] at hi0
  obtain ⟨⟨hi0n, hiorth⟩, hall⟩ := hi0
  let γ0 : Fin Tag.E6.rank → ℤ := e6SplitRoot (rootOf i0 hi0lt)
  let Y : Set (Fin Tag.E6.rank → ℤ) :=
    {α | α ∈ e6SplitCodeRoots (ExcRaw.ofMask 1 n) ∧ iform α γ0 ≠ 0}
  have hγ0mem : γ0 ∈ e6SplitCodeRoots (ExcRaw.ofMask 1 n) := by
    refine ⟨rootOf i0 hi0lt, ?_, Or.inl rfl⟩
    rw [ExcRaw.mem_ofMask]
    exact hi0n
  have hγ0nz : iform γ0 γ0 ≠ 0 := by
    rw [show γ0 = e6SplitRoot (rootOf i0 hi0lt) from rfl, iform_e6SplitRoot_self]
    norm_num
  have hσmem : sigmaE6 γ0 ∈ e6SplitCodeRoots (ExcRaw.ofMask 1 n) := by
    refine ⟨rootOf i0 hi0lt, ?_, Or.inr (Or.inr (Or.inl rfl))⟩
    rw [ExcRaw.mem_ofMask]
    exact hi0n
  have hσorth : iform (sigmaE6 γ0) γ0 = 0 := by
    rw [iform_eq_iformE6, show γ0 = e6SplitRoot (rootOf i0 hi0lt) from rfl]
    exact beq_iff_eq.mp hiorth
  have hσnot : sigmaE6 γ0 ∉ Y := by
    intro hmem
    exact hmem.2 hσorth
  refine ⟨Y, fun α hα => hα.1, ⟨γ0, hγ0mem, hγ0nz⟩, ⟨sigmaE6 γ0, hσmem, hσnot⟩, ?_⟩
  intro α hα β hβ
  have hαN : α ∈ rootsN n := mem_rootsN_iff.mpr hα.1
  have hβN : β ∈ rootsN n := mem_rootsN_iff.mpr hβ.1
  have hαall := List.all_eq_true.mp hall α hαN
  have hβall := List.all_eq_true.mp hαall β hβN
  have hβorth : iform β γ0 = 0 := by
    by_contra hne
    exact hβ.2 ⟨hβ.1, hne⟩
  have hαnz : iformE6 α γ0 ≠ 0 := by
    rw [← iform_eq_iformE6]
    exact hα.2
  have hβzero : iformE6 β γ0 = 0 := by
    rw [← iform_eq_iformE6]
    exact hβorth
  rcases Bool.or_eq_true_iff.mp hβall with h12 | h3
  · rcases Bool.or_eq_true_iff.mp h12 with h1 | h2
    · exact absurd (beq_iff_eq.mp h1) hαnz
    · exact absurd hβzero (bne_iff_ne.mp h2)
  · rw [iform_eq_iformE6]
    exact beq_iff_eq.mp h3

private def innerB (n : ℕ) : List (Fin Tag.E6.rank → ℤ) :=
  (List.range 24).foldl (fun B i =>
    if hi : i < 24 then
      (if _hcond : (n.testBit i && ExcRaw.tabFix1.getD i false &&
          B.all (fun b => iformE6 (e6SplitRoot (rootOf i hi)) b == 0)) = true
        then B ++ [e6SplitRoot (rootOf i hi)] else B)
    else B) []

private def innerOK (n : ℕ) : Bool :=
  (rootsN n).all fun v => decide (rhoE6 v = (innerB n).foldr reflE6 v)

private def discOKd (n : ℕ) (d : ℤ) (μ ν : Fin Tag.E6.rank → ℤ) : Bool :=
  (rootsN n).all (fun v => iformE6 μ v % d == 0 && iformE6 ν v % d == 0) &&
    iformE6 ν (rhoE6 μ - μ) % (d * d) != 0

private def outerOK (n : ℕ) : Bool :=
  anyLt 24 fun x hx => anyLt 24 fun y hy =>
    let γx := e6SplitRoot (rootOf x hx)
    let γy := e6SplitRoot (rootOf y hy)
    n.testBit x && n.testBit y &&
      (discOKd n 3 (γx + iformE6 γx γy • γy) (γx + iformE6 γx γy • γy) ||
        discOKd n 2 (γx + γy) (γx + sigmaE6 γy))

private def codeOK (n : ℕ) : Bool :=
  decide (typ n ∈ typeFinset) &&
    (decide ((typ n).2 ≠ 0) || splitOK n) &&
    (!decide (typ n = (4, 2) ∨ typ n = (9, 3) ∨ typ n = (24, 12)) || innerOK n) &&
    (!decide (typ n = (3, 3) ∨ typ n = (9, 6)) || outerOK n)

private theorem innerB_mem {n : ℕ} {b : Fin Tag.E6.rank → ℤ} (hb : b ∈ innerB n) :
    ∃ i : ExcRaw.Root 1, n.testBit i = true ∧ b = e6SplitRoot i := by
  have hfold : ∀ (l : List ℕ) (B : List (Fin Tag.E6.rank → ℤ)),
      (∀ b ∈ B, ∃ i : ExcRaw.Root 1, n.testBit i = true ∧ b = e6SplitRoot i) →
      ∀ b ∈ l.foldl (fun B i =>
        if hi : i < 24 then
          (if hcond : (n.testBit i && ExcRaw.tabFix1.getD i false &&
              B.all (fun b => iformE6 (e6SplitRoot (rootOf i hi)) b == 0)) = true
            then B ++ [e6SplitRoot (rootOf i hi)] else B)
        else B) B,
        ∃ i : ExcRaw.Root 1, n.testBit i = true ∧ b = e6SplitRoot i := by
    intro l
    induction l with
    | nil => intro B hB b hb; simpa using hB b hb
    | cons a l ih =>
      intro B hB b hb
      rw [List.foldl_cons] at hb
      refine ih _ ?_ b hb
      intro c hc
      by_cases ha : a < 24
      · rw [dif_pos ha] at hc
        by_cases hcond : (n.testBit a && ExcRaw.tabFix1.getD a false &&
            B.all (fun b => iformE6 (e6SplitRoot (rootOf a ha)) b == 0)) = true
        · rw [dif_pos hcond, List.mem_append] at hc
          rcases hc with hc | hc
          · exact hB c hc
          · rw [List.mem_singleton] at hc
            subst hc
            refine ⟨rootOf a ha, ?_, rfl⟩
            exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hcond).1).1
        · rw [dif_neg hcond] at hc
          exact hB c hc
      · rw [dif_neg ha] at hc
        exact hB c hc
  exact hfold (List.range 24) [] (by simp) b hb

private theorem codeOK_eq : e6SplitCodeMasks.all codeOK = true := by decide +kernel

theorem e6Split_type_mem_of_occurs {U : Submodule (ZMod 3) (ExcRaw.V 1)}
    {c : Finset (ExcRaw.Root 1)} (hc : ExcRaw.occurs 1 U c) :
    (c.card, ExcRaw.longCount 1 c) ∈
      ({(1, 0), (3, 0), (1, 1), (3, 3), (4, 2), (9, 3), (9, 6), (24, 12)} : Finset (ℕ × ℕ)) := by
  obtain ⟨n, hn, rfl⟩ := exists_mem_e6SplitCodeMasks_of_occurs hc
  have hcode := List.all_eq_true.mp codeOK_eq n hn
  simp only [codeOK, Bool.and_eq_true, decide_eq_true_eq] at hcode
  simpa [typ, typeFinset] using hcode.1.1.1

theorem e6Split_split_of_occurs {U : Submodule (ZMod 3) (ExcRaw.V 1)}
    {c : Finset (ExcRaw.Root 1)} (hc : ExcRaw.occurs 1 U c) (h0 : ExcRaw.longCount 1 c = 0) :
    ∃ Y ⊆ e6SplitCodeRoots c, Y.Nonempty ∧ (e6SplitCodeRoots c \ Y).Nonempty ∧
      ∀ α ∈ Y, ∀ β ∈ e6SplitCodeRoots c \ Y, iform α β = 0 := by
  obtain ⟨n, hn, rfl⟩ := exists_mem_e6SplitCodeMasks_of_occurs hc
  have hcode := List.all_eq_true.mp codeOK_eq n hn
  simp only [codeOK, Bool.and_eq_true, decide_eq_true_eq] at hcode
  have hsplit : splitOK n = true := by
    have hB := hcode.1.1.2
    simpa [typ, h0] using hB
  exact splitOK_sound hsplit


private def rhoHom : (Fin Tag.E6.rank → ℤ) →+ (Fin Tag.E6.rank → ℤ) where
  toFun := rhoE6
  map_zero' := by
    funext j
    rfl
  map_add' x y := by
    funext j
    exact neg_add (x (TwistTag.E6.perm.symm j)) (y (TwistTag.E6.perm.symm j))

private theorem corootPair_eq_iformE6 {b x : Fin Tag.E6.rank → ℤ} (hb : IsRoot .E6 b) :
    corootPair b x = iformE6 b x := by
  have hbb : iform b b = 2 :=
    CFSG.ClassicalInvolution.ModelFacts.Levi.iform_self_isRoot_E6 hb
  unfold corootPair
  rw [hbb, iform_eq_iformE6]
  simp

private theorem prod_rootReflection_smul (L : List (Fin Tag.E6.rank → ℤ))
    (hL : ∀ b ∈ L, IsRoot .E6 b) (v : Fin Tag.E6.rank → ℤ) :
    (L.map rootReflection).prod • v = L.foldr reflE6 v := by
  induction L with
  | nil => simp
  | cons b L ih =>
    rw [List.map_cons, List.prod_cons, List.foldr_cons, mul_smul,
      ih (fun x hx => hL x (List.mem_cons_of_mem b hx))]
    unfold reflE6
    rw [rootReflection_smul (hL b List.mem_cons_self),
      corootPair_eq_iformE6 (hL b List.mem_cons_self)]

private theorem innerOK_sound {n : ℕ} (h : innerOK n = true) :
    twistInner (e6SplitCodeRoots (ExcRaw.ofMask 1 n)) rhoE6 := by
  rw [innerOK] at h
  let L := innerB n
  have hLmem : ∀ b ∈ L, b ∈ e6SplitCodeRoots (ExcRaw.ofMask 1 n) := by
    intro b hb
    obtain ⟨i, hi, rfl⟩ := innerB_mem hb
    exact ⟨i, by simpa [ExcRaw.mem_ofMask] using hi, Or.inl rfl⟩
  have hLroot : ∀ b ∈ L, IsRoot .E6 b :=
    fun b hb => isRoot_of_mem_e6SplitCodeRoots (hLmem b hb)
  refine ⟨(L.map rootReflection).prod, ?_, ?_⟩
  · apply Subgroup.list_prod_mem
    intro g hg
    rw [List.mem_map] at hg
    obtain ⟨b, hb, rfl⟩ := hg
    exact Subgroup.subset_closure ⟨b, hLmem b hb, rfl⟩
  · intro γ hγ
    have hγN : γ ∈ rootsN n := mem_rootsN_iff.mpr hγ
    have hγall : rhoE6 γ = L.foldr reflE6 γ := by
      have := List.all_eq_true.mp h γ hγN
      simpa using (of_decide_eq_true this)
    rw [prod_rootReflection_smul L hLroot γ, ← hγall]

private theorem outerOK_sound {n : ℕ} (h : outerOK n = true) :
    ¬ twistInner (e6SplitCodeRoots (ExcRaw.ofMask 1 n)) rhoE6 := by
  rw [outerOK] at h
  obtain ⟨x, hxlt, hx⟩ := anyLt_eq.mp h
  obtain ⟨y, hylt, hy⟩ := anyLt_eq.mp hx
  simp only [Bool.and_eq_true] at hy
  obtain ⟨⟨hxn, hyn⟩, hdisc⟩ := hy
  have hxroot : e6SplitRoot (rootOf x hxlt) ∈ e6SplitCodeRoots (ExcRaw.ofMask 1 n) := by
    refine ⟨(rootOf x hxlt), ?_, Or.inl rfl⟩
    rw [ExcRaw.mem_ofMask]
    exact hxn
  have hyroot : e6SplitRoot (rootOf y hylt) ∈ e6SplitCodeRoots (ExcRaw.ofMask 1 n) := by
    refine ⟨(rootOf y hylt), ?_, Or.inl rfl⟩
    rw [ExcRaw.mem_ofMask]
    exact hyn
  have hroot : ∀ γ ∈ e6SplitCodeRoots (ExcRaw.ofMask 1 n), IsRoot .E6 γ :=
    fun γ hγ => isRoot_of_mem_e6SplitCodeRoots hγ
  have hsl : ∀ γ ∈ e6SplitCodeRoots (ExcRaw.ofMask 1 n), iform γ γ = 2 :=
    fun γ hγ => CFSG.ClassicalInvolution.ModelFacts.Levi.iform_self_isRoot_E6 (hroot γ hγ)
  rcases Bool.or_eq_true_iff.mp hdisc with h3 | h2
  · rw [discOKd, Bool.and_eq_true] at h3
    obtain ⟨hdiv, hnd⟩ := h3
    let μ : Fin Tag.E6.rank → ℤ :=
      e6SplitRoot (rootOf x hxlt) + iformE6 (e6SplitRoot (rootOf x hxlt)) (e6SplitRoot (rootOf y hylt)) • e6SplitRoot (rootOf y hylt)
    let ν : Fin Tag.E6.rank → ℤ := μ
    have hμ : μ ∈ Submodule.span ℤ (e6SplitCodeRoots (ExcRaw.ofMask 1 n)) := by
      apply Submodule.add_mem
      · exact Submodule.subset_span hxroot
      · exact Submodule.smul_mem _ _ (Submodule.subset_span hyroot)
    have hμd : ∀ γ ∈ e6SplitCodeRoots (ExcRaw.ofMask 1 n), (3 : ℤ) ∣ iform μ γ := by
      intro γ hγ
      have hγN : γ ∈ rootsN n := mem_rootsN_iff.mpr hγ
      have hv := List.all_eq_true.mp hdiv γ hγN
      have h1 := (Bool.and_eq_true_iff.mp hv).1
      rw [Int.dvd_iff_emod_eq_zero, iform_eq_iformE6]
      exact beq_iff_eq.mp h1
    have hνd : ∀ γ ∈ e6SplitCodeRoots (ExcRaw.ofMask 1 n), (3 : ℤ) ∣ iform ν γ := hμd
    have hnd' : ¬ (3 : ℤ) * (3 : ℤ) ∣ iform ν (rhoHom μ - μ) := by
      have hne : iformE6 ν (rhoE6 μ - μ) % ((3 : ℤ) * 3) ≠ 0 := bne_iff_ne.mp hnd
      rw [Int.dvd_iff_emod_eq_zero, iform_eq_iformE6]
      simpa [ν, rhoHom] using hne
    exact CFSG.StandardType.TableCRes.not_twistInner_of_disc hroot hsl rhoHom hμ hμd hνd hnd'
  · rw [discOKd, Bool.and_eq_true] at h2
    obtain ⟨hdiv, hnd⟩ := h2
    let μ : Fin Tag.E6.rank → ℤ := e6SplitRoot (rootOf x hxlt) + e6SplitRoot (rootOf y hylt)
    let ν : Fin Tag.E6.rank → ℤ := e6SplitRoot (rootOf x hxlt) + sigmaE6 (e6SplitRoot (rootOf y hylt))
    have hμ : μ ∈ Submodule.span ℤ (e6SplitCodeRoots (ExcRaw.ofMask 1 n)) := by
      apply Submodule.add_mem
      · exact Submodule.subset_span hxroot
      · exact Submodule.subset_span hyroot
    have hμd : ∀ γ ∈ e6SplitCodeRoots (ExcRaw.ofMask 1 n), (2 : ℤ) ∣ iform μ γ := by
      intro γ hγ
      have hγN : γ ∈ rootsN n := mem_rootsN_iff.mpr hγ
      have hv := List.all_eq_true.mp hdiv γ hγN
      have h1 := (Bool.and_eq_true_iff.mp hv).1
      rw [Int.dvd_iff_emod_eq_zero, iform_eq_iformE6]
      exact beq_iff_eq.mp h1
    have hνd : ∀ γ ∈ e6SplitCodeRoots (ExcRaw.ofMask 1 n), (2 : ℤ) ∣ iform ν γ := by
      intro γ hγ
      have hγN : γ ∈ rootsN n := mem_rootsN_iff.mpr hγ
      have hv := List.all_eq_true.mp hdiv γ hγN
      have h1 := (Bool.and_eq_true_iff.mp hv).2
      rw [Int.dvd_iff_emod_eq_zero, iform_eq_iformE6]
      exact beq_iff_eq.mp h1
    have hnd' : ¬ (2 : ℤ) * (2 : ℤ) ∣ iform ν (rhoHom μ - μ) := by
      have hne : iformE6 ν (rhoE6 μ - μ) % ((2 : ℤ) * 2) ≠ 0 := bne_iff_ne.mp hnd
      rw [Int.dvd_iff_emod_eq_zero, iform_eq_iformE6]
      simpa [ν, rhoHom] using hne
    exact CFSG.StandardType.TableCRes.not_twistInner_of_disc hroot hsl rhoHom hμ hμd hνd hnd'

theorem e6Split_twistInner_of_occurs {U : Submodule (ZMod 3) (ExcRaw.V 1)}
    {c : Finset (ExcRaw.Root 1)} (hc : ExcRaw.occurs 1 U c)
    (ht : (c.card, ExcRaw.longCount 1 c) = (4, 2) ∨ (c.card, ExcRaw.longCount 1 c) = (9, 3) ∨
      (c.card, ExcRaw.longCount 1 c) = (24, 12)) :
    twistInner (e6SplitCodeRoots c) fun γ => -permLattice (τ := .E6) TwistTag.E6.perm γ := by
  obtain ⟨n, hn, rfl⟩ := exists_mem_e6SplitCodeMasks_of_occurs hc
  have hcode := List.all_eq_true.mp codeOK_eq n hn
  simp only [codeOK, Bool.and_eq_true, decide_eq_true_eq] at hcode
  have htyp : typ n = (4, 2) ∨ typ n = (9, 3) ∨ typ n = (24, 12) := by
    simpa [typ] using ht
  have hdec : decide (typ n = (4, 2) ∨ typ n = (9, 3) ∨ typ n = (24, 12)) = true := by
    rw [decide_eq_true_eq]
    exact htyp
  have hinner : innerOK n = true := by
    have hC := hcode.1.2
    simpa [hdec] using hC
  change twistInner (e6SplitCodeRoots (ExcRaw.ofMask 1 n)) rhoE6
  exact innerOK_sound hinner

theorem e6Split_not_twistInner_of_occurs {U : Submodule (ZMod 3) (ExcRaw.V 1)}
    {c : Finset (ExcRaw.Root 1)} (hc : ExcRaw.occurs 1 U c)
    (ht : (c.card, ExcRaw.longCount 1 c) = (3, 3) ∨ (c.card, ExcRaw.longCount 1 c) = (9, 6)) :
    ¬ twistInner (e6SplitCodeRoots c) fun γ => -permLattice (τ := .E6) TwistTag.E6.perm γ := by
  obtain ⟨n, hn, rfl⟩ := exists_mem_e6SplitCodeMasks_of_occurs hc
  have hcode := List.all_eq_true.mp codeOK_eq n hn
  simp only [codeOK, Bool.and_eq_true, decide_eq_true_eq] at hcode
  have htyp : typ n = (3, 3) ∨ typ n = (9, 6) := by
    simpa [typ] using ht
  have hdec : decide (typ n = (3, 3) ∨ typ n = (9, 6)) = true := by
    rw [decide_eq_true_eq]
    exact htyp
  have houter : outerOK n = true := by
    have hD := hcode.2
    simpa [hdec] using hD
  change ¬ twistInner (e6SplitCodeRoots (ExcRaw.ofMask 1 n)) rhoE6
  exact outerOK_sound houter

end CFSG.StandardType.GGQ2Frame.ExcPlacement

end
