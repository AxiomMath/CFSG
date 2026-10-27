module

public import CFSG.OddTranspositions.PartFour.ThirteenListThreeFischerY
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi23ThreeA

public section

namespace CFSG.OddTranspositions.FischerMarkedY

attribute [local irreducible] sevenForm coordinates


open CFSG.Fischer.Classification CFSG.HardMathSupport.Dickson.I271
open CFSG.HardMathSupport.Dickson.I271.TabFi23 CFSG.HardMathSupport.Dickson.I271.TabFi23Y
open CFSG.Sporadic.Fi23 CFSG.Sporadic.Fi23.Native CFSG.YGroups
open CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Th hiding J a b closure_ab gA gB rows_B_cube
open CFSG.Certificates.CosetEnumeration (evalWord)
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23Native
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Five
open CFSG.LieType.Multipliers.O73
open CFSG.RankThree.PartOne.N143.O7 (Om)
open scoped commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

theorem exists_marked_y322_of_check
    {x : CFSG.Sporadic.Fi23.J} {T : Table} (hT : Rep 31671 T x) {ks : List ℕ}
    (hcheck : yCheck orb (dTable orb) (genTables orb (-2)) T ks = true) :
    ∃ s : Fin 8 → CFSG.Sporadic.Fi23.J, (∀ w ∈ yRels 3 2 2, evalWord (y322Img s) w = 1) ∧
      (∃ i j, s i * s j ≠ s j * s i) ∧ (∀ i, s i * x = x * s i) ∧ ∀ i, s i ∈ D23 := by
  have h := hcheck
  unfold yCheck at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, List.all_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hlen, hlt⟩, hfix⟩, hlet⟩, hrel⟩, hnc⟩ := h
  have hmem : ∀ i : Fin 8, ks[i.val]! ∈ ks := fun i => by
    have hi : i.val < ks.length := by rw [hlen]; exact i.2
    rw [getElem!_pos ks i.val hi]
    exact List.getElem_mem hi
  let s : Fin 8 → J := fun i => conjPt ks[i.val]!
  refine ⟨s, ?_, ?_, ?_, fun i => conjPt_mem_D23 (hlt _ (hmem i))⟩
  · intro w hw
    rw [← yRelsD_eq] at hw
    have hl : ∀ c ∈ w, c < 8 := fun c hc => by simpa using hlet w hw c hc
    have h2 := rep_starWordTab_dTable (w.map fun c => ks[c]!)
    have h3 : ((w.map fun c => ks[c]!).map conjPt).prod = 1 :=
      eq_of_eqTab h2 (Rep.idT (by norm_num)) (hrel w hw)
    show (w.map (y322Img s)).prod = 1
    rw [← h3, List.map_map]
    refine congrArg List.prod (List.map_congr_left fun c hc => ?_)
    have hc8 : c < 8 := hl c hc
    show y322Img s c = conjPt ks[c]!
    unfold y322Img
    rw [dif_pos hc8]
  · refine ⟨0, 1, fun hcomm => ?_⟩
    have hA := rep_starWordTab_dTable [ks[0]!, ks[1]!]
    have hB := rep_starWordTab_dTable [ks[1]!, ks[0]!]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hA hB
    change conjPt ks[0]! * conjPt ks[1]! = conjPt ks[1]! * conjPt ks[0]! at hcomm
    rw [hcomm.symm] at hB
    rw [eqTab_of_rep_eq hA hB] at hnc
    exact absurd hnc (by decide)
  · intro i
    have hf' : x • (⟨ks[i.val]!, hlt _ (hmem i)⟩ : Fin 31671) = ⟨ks[i.val]!, hlt _ (hmem i)⟩ := by
      apply Fin.ext
      rw [← ap_eq_smul hT]
      exact hfix _ (hmem i)
    exact (fix_iff_comm x (⟨ks[i.val]!, hlt _ (hmem i)⟩ : Fin 31671)).mp hf'


theorem exists_fi23_refl_embedding :
    ∃ κ : R3 sevenForm →* CFSG.Sporadic.Fi23.J, Function.Injective κ ∧
      ∃ i : Fin 8, κ (reflBar sevenForm (coordinates (vecs i))) ∈ D23 := by
  have := finite_J23
  let z : J := t3 0
  have hz : orderOf z = 3 := t3_classData.1.1
  have hcheck : yCheck orb (dTable orb) (genTables orb (-2)) (t3Tabs orb letters)[0]! y322Ks = true :=
    Certificates.certificate17339
  obtain ⟨s, hsrel, hsnc, hsz, hsD⟩ := exists_marked_y322_of_check (rep_t3Tabs 0) hcheck
  let f : YGroup 3 2 2 →* J := yModelHom (y322Img s) hsrel
  have hfrange : f.range = Subgroup.closure (Set.range s) := by
    have himg : y322Img s '' Set.Iio (ngen 3 2 2) = Set.range s := by
      ext g
      constructor
      · rintro ⟨c, hc, rfl⟩
        have hc8 : c < 8 := hc
        exact ⟨⟨c, hc8⟩, by simp only [y322Img, dif_pos hc8]⟩
      · rintro ⟨i, rfl⟩
        exact ⟨i.val, i.2, by simp only [y322Img, dif_pos i.2]⟩
    rw [range_yModelHom, himg]
  have hnc : ∃ a ∈ f.range, ∃ b ∈ f.range, a * b ≠ b * a := by
    obtain ⟨i, j, h⟩ := hsnc
    refine ⟨s i, hfrange.symm ▸ Subgroup.subset_closure ⟨i, rfl⟩,
      s j, hfrange.symm ▸ Subgroup.subset_closure ⟨j, rfl⟩, h⟩
  have hzc : ∀ g ∈ f.range, g * z = z * g := by
    intro g hg
    have hle : f.range ≤ Subgroup.centralizer ({z} : Set J) := by
      rw [hfrange, Subgroup.closure_le]
      rintro g ⟨i, rfl⟩
      exact cen_iff' (hsz i)
    exact cen_iff (G := J) (t := z) (u := g) (hle hg)
  let N := Subgroup.closure (Set.range s ∪ {z})
  have hN : f.range ≤ N := hfrange ▸ Subgroup.closure_mono Set.subset_union_left
  have hzN : z ∈ N := Subgroup.subset_closure (Set.mem_union_right _ rfl)
  have hNC : N ≤ Subgroup.centralizer ({z} : Set J) := by
    rw [Subgroup.closure_le]
    rintro g (⟨i, rfl⟩ | hg)
    · exact cen_iff' (hsz i)
    · rw [Set.mem_singleton_iff.mp hg]
      exact cen_iff' rfl
  have hNcard : Nat.card N ≤ 3 * 4585351680 := by
    have h := Subgroup.card_le_of_le hNC
    rw [card_cent_t3_zero] at h
    omega
  obtain ⟨π, hπ, hπker, hπgen⟩ := exists_y322_reflQuot
  obtain ⟨πO, hπO, hπOker, hπOcard⟩ := tabFi23_y322_to_om
  have := tabFi23_isSimpleGroup_om
  have : Finite (YGroup 3 2 2) := Nat.finite_of_card_ne_zero (by rw [card_y322]; decide)
  obtain ⟨hker, -⟩ := tabFi23_recog_abstract tabFi23_center_om πO hπO hπOcard
    f hnc z hz hzc N hN hzN (by rw [tabFi23_card_om]; exact hNcard)
  have hker' : f.ker = π.ker := hker.trans (hπOker.trans hπker.symm)
  let κ : R3 sevenForm →* J := π.liftOfSurjective hπ ⟨f, hker'.ge⟩
  have hκcomp : ∀ y, κ (π y) = f y :=
    fun y => π.liftOfRightInverse_comp_apply _ _ ⟨f, hker'.ge⟩ y
  have hκ : Function.Injective κ := by
    intro a b hab
    obtain ⟨a, rfl⟩ := hπ a
    obtain ⟨b, rfl⟩ := hπ b
    rw [hκcomp, hκcomp] at hab
    apply (MonoidHom.eq_iff π).mpr
    rw [← hker']
    exact (MonoidHom.eq_iff f).mp hab
  have hκgen : ∀ i : Fin 8, κ (reflBar sevenForm (coordinates (vecs i))) = s i := by
    intro i
    rw [← hπgen, hκcomp]
    change yModelHom (y322Img s) hsrel (yGen 3 2 2 i.val) = s i
    rw [yModelHom_yGen (by simp [ngen])]
    simp only [y322Img, dif_pos i.2]
  refine ⟨κ, hκ, 0, ?_⟩
  rw [hκgen]
  exact hsD 0

end CFSG.OddTranspositions.FischerMarkedY
