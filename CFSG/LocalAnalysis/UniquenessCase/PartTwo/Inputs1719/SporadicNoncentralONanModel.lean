module

public import CFSG.Sporadic.ONOddCore.QuotBasics
import all CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData

public noncomputable section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.ONOddCore
open CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification.PSL3Four
open scoped Pointwise

private def sncon_bits (M : ℕ) : Set (Fin 120) := {x | M.testBit x}

private def sncon_chk (A B : ℕ) : List ℕ → ℕ → Bool
  | [], _ => true
  | a :: t, p => (A.testBit p == B.testBit a) && sncon_chk A B t (p + 1)

private theorem sncon_chk_spec {A B : ℕ} : ∀ {L : List ℕ} {p : ℕ}, sncon_chk A B L p = true →
    ∀ i < L.length, A.testBit (p + i) = B.testBit (L.getD i 0)
  | [], _, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | a :: t, p, h, i, hi => by
    simp only [sncon_chk, Bool.and_eq_true, beq_iff_eq] at h
    rcases i with _ | i
    · simpa using h.1
    · have := sncon_chk_spec h.2 i (by simpa using hi)
      rw [show p + (i + 1) = p + 1 + i by omega]
      simpa using this

private def sncon_Img (L : List ℕ) (g : Equiv.Perm (Fin 120)) : Prop :=
  L.length = 120 ∧ ∀ x : Fin 120, L.getD x 0 = g x

private theorem sncon_image_bits {A B : ℕ} {L : List ℕ} {g : Equiv.Perm (Fin 120)}
    (hL : sncon_Img L g) (h : sncon_chk A B L 0 = true) : g '' sncon_bits A = sncon_bits B := by
  have key : ∀ x : Fin 120, A.testBit x = B.testBit (g x) := fun x => by
    have := sncon_chk_spec h x (by rw [hL.1]; exact x.isLt)
    rwa [zero_add, hL.2] at this
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    show B.testBit (g x) = true
    rw [← key]
    exact hx
  · intro hy
    refine ⟨g⁻¹ y, ?_, by simp⟩
    show A.testBit (g⁻¹ y) = true
    rw [key, Equiv.Perm.coe_inv, Equiv.apply_symm_apply]
    exact hy

private theorem sncon_getD_toList {t : Array ℕ} (i : ℕ) : t.toList.getD i 0 = t[i]! := by
  by_cases hi : i < t.size
  · rw [getElem!_pos t i hi, List.getD_eq_getElem _ _ (by simpa using hi), Array.getElem_toList]
  · rw [getElem!_neg t i hi, List.getD_eq_default _ _ (by simpa using hi)]
    rfl

private theorem sncon_img_of_prep {t : Array ℕ} {g : Equiv.Perm (Fin 120)} (ht : PRep 120 t g)
    (hs : t.size = 120) : sncon_Img t.toList g :=
  ⟨by rw [Array.length_toList, hs], fun x => by rw [sncon_getD_toList, ht x]⟩

private theorem sncon_bits_inj {A B : ℕ} (hA : A < 2 ^ 120) (hB : B < 2 ^ 120)
    (h : sncon_bits A = sncon_bits B) : A = B := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 120
  · have := congrArg (fun s : Set (Fin 120) => (⟨i, hi⟩ : Fin 120) ∈ s) h
    simp only [sncon_bits, Set.mem_setOf_eq, eq_iff_iff] at this
    exact Bool.eq_iff_iff.2 this
  · have h120 : 2 ^ 120 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hA h120),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hB h120)]

private theorem sncon_smul_perm (g : Equiv.Perm (Fin 120)) (s : Set (Fin 120)) :
    g • s = g '' s := by
  rw [← Set.image_smul]
  rfl

private theorem sncon_smul_RM
    (n : RM) (s : Set (Fin 120)) :
    n • s = (n : Equiv.Perm (Fin 120)) '' s := by
  rw [← Set.image_smul]
  rfl

private def sncon_r0 : List ℕ :=
  [28, 1, 11, 14, 95, 86, 75, 12, 39, 43, 111, 18, 72, 112, 70, 79, 21, 92, 10, 98, 35, 67, 19, 38,
   25, 27, 101, 97, 23, 85, 105, 74, 113, 114, 55, 64, 65, 107, 106, 49, 3, 61, 66, 34, 26, 8, 42,
   78, 93, 57, 108, 6, 5, 99, 71, 37, 104, 109, 100, 33, 77, 91, 30, 116, 94, 13, 44, 32, 22, 119,
   76, 0, 102, 62, 73, 7, 53, 24, 16, 4, 31, 90, 88, 56, 46, 68, 87, 50, 118, 45, 48, 81, 58, 41,
   59, 82, 52, 110, 115, 40, 69, 84, 51, 9, 36, 80, 54, 103, 96, 89, 60, 63, 83, 47, 20, 29, 2, 17,
   15, 117]

private def sncon_r1 : List ℕ :=
  [47, 70, 34, 48, 75, 9, 32, 16, 60, 10, 24, 98, 35, 96, 13, 110, 59, 41, 43, 74, 69, 91, 21, 71,
   18, 29, 107, 3, 14, 111, 92, 90, 22, 101, 17, 109, 7, 46, 112, 86, 55, 26, 106, 50, 51, 38, 88,
   62, 102, 25, 73, 94, 53, 19, 23, 67, 4, 108, 58, 81, 117, 105, 85, 87, 8, 113, 56, 20, 44, 103,
   79, 76, 104, 5, 42, 64, 93, 99, 37, 78, 114, 84, 65, 45, 72, 57, 2, 40, 89, 1, 6, 100, 33, 12,
   30, 95, 83, 118, 77, 49, 31, 68, 82, 63, 36, 80, 15, 39, 97, 54, 52, 11, 28, 119, 61, 116, 115,
   66, 0, 27]

private def sncon_mO : ℕ := 1275342068194758945345661176693952544

private def sncon_tree : List (ℕ × ℕ × ℕ) :=
  [(5, 0, 0), (27, 0, 0), (28, 0, 1), (15, 0, 2), (29, 0, 3), (21, 0, 6), (30, 0, 7), (12, 1, 1),
   (36, 1, 2), (91, 1, 3), (76, 1, 6), (92, 1, 7), (63, 2, 2), (93, 2, 3), (78, 2, 6), (94, 2, 7),
   (64, 3, 3), (57, 3, 6), (65, 3, 7), (80, 4, 6), (95, 4, 7), (42, 5, 0), (75, 5, 1), (24, 5, 7),
   (96, 6, 0), (97, 6, 1), (54, 7, 2), (47, 7, 3), (55, 7, 6), (56, 7, 7), (107, 8, 3), (108, 8, 7),
   (117, 9, 6), (116, 10, 1), (112, 10, 7), (32, 11, 1), (114, 12, 3), (84, 12, 6), (43, 12, 7),
   (83, 13, 7), (98, 14, 0), (82, 14, 7), (49, 15, 0), (119, 15, 1), (118, 16, 6), (106, 17, 1),
   (60, 17, 7), (50, 18, 0), (104, 19, 0), (77, 19, 7), (111, 21, 1), (105, 21, 7), (22, 22, 7),
   (69, 23, 0), (86, 23, 1), (100, 24, 1), (79, 24, 6), (81, 25, 6), (101, 26, 3), (70, 28, 7),
   (62, 33, 7), (74, 34, 0), (44, 34, 1), (88, 35, 6)]

private def sncon_orb : List (ℕ × ℕ × ℕ) :=
  [(1275342068194758945345661176693952544, 0, 0), (1300417092291308734658783040539173012, 0, 0),
   (575464784200768049336734806161283997, 0, 1), (1253523711143612438377326599517485621, 1, 0),
   (1154506066973547509736966629420368117, 1, 1), (22599974490242368596564138296082256, 2, 0),
   (1113245596264820783687407665211899307, 2, 1), (576781873101888809650266027512473653, 3, 0),
   (248710952918143291853168128488638171, 3, 1), (1248341712977278454842672103010975661, 4, 0),
   (1155803426895267301651901918827188955, 4, 1), (767645456293008285693868790905578776, 5, 0),
   (517963903921092862193388291234227480, 5, 1), (321542123347149594898261129309835695, 6, 0),
   (1214743107060882944836395016644698741, 6, 1), (692410085123860422345043928770654072, 7, 0),
   (1278887044007546373590432415994663855, 7, 1), (397211860729189868692516315351176426, 8, 0),
   (771790758350549395971341964631854314, 8, 1), (237985567855987048000751011807820717, 9, 0),
   (560248763769820061256122559881627381, 9, 1), (1127045500494430120612169125848620443, 10, 1),
   (1231853096274865322016366070105016416, 11, 1), (1058400825868014646655589849720678129, 12, 0),
   (1200363853192739867145436107915929717, 12, 1), (665282081881088899620841171778231326, 13, 0),
   (314090228615095977910582483430407046, 13, 1), (277523890966373498514127779812610009, 14, 1),
   (346587045584220451471029440624350908, 15, 1), (492683536528500192570870173686952419, 17, 0),
   (615822192732491060940215989186685779, 17, 1), (179969346014274480947772220169810406, 18, 0),
   (74523656179830437454275729758747478, 18, 1), (669977544502847392128220145865162360, 19, 0),
   (282653068106413733048225140833386374, 19, 1), (1145636606567195646894101849864050784, 20, 0),
   (940961266387605704768468209853509609, 20, 1), (617011102271942650698172801018024847, 21, 0),
   (463075627603719545716460500219957647, 21, 1), (937098938340975350288915168044753137, 22, 0),
   (921206412652358353744142793864097721, 23, 1), (844356547339082351054711331846144935, 24, 1),
   (670634169476962935316626283678874238, 26, 0), (303583878543404818850949648482559108, 26, 1),
   (1073653371114546394370292861014506985, 28, 0), (1199722341522610069204032359592455771, 28, 1),
   (799478800404442910585420996399020661, 29, 1), (681444429053234825813222762913637703, 30, 0),
   (722861267942607491636302827291946323, 30, 1), (1264785775785059381440647526903211288, 33, 0),
   (184359267094180843535182458537801636, 33, 1), (134874867895606353939189187839736367, 34, 0),
   (1217417807751919645016425118619657364, 34, 1), (656400292953180505311203461403877605, 35, 0),
   (658456770933778857660425182806596375, 35, 1), (73991458335944542688094357506971222, 36, 1),
   (74523854257471159423842687282052870, 37, 0), (457022775109728339278334328272640158, 38, 0),
   (504983796184873477325491105858467772, 39, 0), (408894251318803391670848141108646654, 39, 1),
   (517964140677085529870917209300562876, 40, 0), (408893815588067090603741881993873150, 40, 1),
   (323212816699828452423914474092765058, 41, 0), (692242658682291402422476039221149560, 41, 1),
   (185173129573352999424627481195452354, 42, 1), (611705127002792616903718663450579240, 44, 0),
   (839792606566320390666544919588300771, 45, 0), (330821271299200322560084528391524290, 46, 1),
   (692410087599746506485513792515789096, 47, 1), (850024817272898671099567264011839205, 49, 0),
   (723018139723727245059279352987297877, 49, 1), (1077870802730962416744603482300555225, 50, 0),
   (670635446653302284973340794888220286, 50, 1), (1296679609261207979556605852788103264, 52, 0),
   (1086080410725250857219630264881487261, 53, 0), (793641276819999973619436899309916799, 53, 1),
   (52456632222797970303733811191393622, 54, 0), (804301408021439329895712433003572555, 54, 1),
   (799326691464947546344437480617683035, 56, 0), (1258317465119780023153674588845007888, 56, 1),
   (414513088368802425450021832989277113, 58, 0), (535585037124013141586005910993847935, 58, 1),
   (1119561127642784446440466851358642011, 59, 1), (1195179162844459740466533737143823919, 60, 1),
   (1145636607192210606858404362307886314, 61, 0), (942987595981849231773336795018522443, 61, 1),
   (1122283264675089691307679474329044116, 62, 1), (1255711218774980836590363725931495688, 63, 0),
   (1122270598536141216175275212675996810, 67, 1), (320609078160479765323857058049693760, 69, 0),
   (1271412351093922044549760032918262056, 70, 1), (185173125007549198596910403909216230, 72, 1),
   (1236974362648526028468457735610343541, 73, 0), (326242478678313877305652120740694939, 73, 1),
   (570633238057447933367457433124683951, 74, 1), (164198956596544038533986997856509890, 75, 1),
   (145199234171215890746783508122570075, 76, 0), (712313640012751241812570475295575319, 82, 1),
   (279021950612202236440937341465914283, 83, 0), (648614042533067031332055663549206951, 84, 0),
   (627505794013555493074959101837032021, 84, 1), (658329966259697737646930081669312839, 88, 0),
   (1115563839603641600683108317842379439, 92, 1), (1122284521793075034765466834980019358, 95, 1),
   (6017656174823611501854114232825446, 98, 0)]

private def sncon_J : List ℕ := [0, 1, 2, 3, 6, 7]

private def sncon_treeAt (k : ℕ) : Bool :=
  match sncon_tree.getD k (0, 0, 0) with
  | (x, i, j) => sncon_mO.testBit x && if k = 0 then x == 5 else
      decide (i < k) && sncon_J.contains j &&
        x == (Data.PSL120Chain.generators[j]!).toList.getD (sncon_tree.getD i (0, 0, 0)).1 0

private def sncon_orbAt (k : ℕ) : Bool :=
  match sncon_orb.getD k (0, 0, 0) with
  | (M, i, j) => decide (M < 2 ^ 120) && if k = 0 then M == sncon_mO else
      decide (i < k) && decide (j < 2) &&
        sncon_chk (sncon_orb.getD i (0, 0, 0)).1 M (if j = 0 then sncon_r0 else sncon_r1) 0

private def sncon_chkConj (r u : List ℕ) : List ℕ → ℕ → Bool
  | [], _ => true
  | a :: t, x => (r.getD (u.getD x 0) 0 == u.getD a 0) && sncon_chkConj r u t (x + 1)

private theorem sncon_tree_check : (List.range 64).all sncon_treeAt = true ∧
    (List.range 120).all (fun x => !sncon_mO.testBit x || (sncon_tree.map Prod.fst).contains x) =
      true ∧ sncon_tree.length = 64 := by
  decide +kernel

private theorem sncon_inv_check : sncon_J.all (fun j =>
    sncon_chk sncon_mO sncon_mO (Data.PSL120Chain.generators[j]!).toList 0 &&
      (Data.PSL120Chain.generators[j]!).size == 120) = true := by
  decide +kernel

private theorem sncon_orb_check : (List.range 105).all sncon_orbAt = true ∧
    (sncon_orb.map Prod.fst).Nodup ∧ sncon_orb.length = 105 := by
  decide +kernel

private theorem sncon_conj_check :
    sncon_chkConj sncon_r0 Data.quotientConjugator.toList
        (Data.M120Chain.generators[0]!).toList 0 = true ∧
      sncon_chkConj sncon_r1 Data.quotientConjugator.toList
        (Data.M120Chain.generators[1]!).toList 0 = true ∧
      sncon_r0.length = 120 ∧ sncon_r1.length = 120 ∧ Data.quotientConjugator.size = 120 ∧
      (Data.M120Chain.generators[0]!).size = 120 ∧ (Data.M120Chain.generators[1]!).size = 120 := by
  decide +kernel

private abbrev sncon_O : Set (Fin 120) := sncon_bits sncon_mO

private theorem sncon_O_eq : sncon_O =
    ↑(Finset.univ.filter fun x : Fin 120 => sncon_mO.testBit x = true) := by
  ext x
  simp [sncon_bits]

private theorem sncon_card_filter :
    (Finset.univ.filter fun x : Fin 120 => sncon_mO.testBit x = true).card = 64 := by
  decide +kernel

private abbrev sncon_gen (j : ℕ) : Equiv.Perm (Fin 120) :=
  permOfArr 120 Data.PSL120Chain.generators[j]!

private def sncon_U0 : Subgroup (Equiv.Perm (Fin 120)) :=
  Subgroup.closure {g | ∃ j ∈ sncon_J, sncon_gen j = g}

private theorem sncon_J_lt {j : ℕ} (hj : j ∈ sncon_J) : j < 12 := by
  simp only [sncon_J, List.mem_cons, List.not_mem_nil, or_false] at hj
  omega

private theorem sncon_gen_img
    {j : ℕ} (hj : j ∈ sncon_J) :
    sncon_Img (Data.PSL120Chain.generators[j]!).toList (sncon_gen j) := by
  have h := List.all_eq_true.1 sncon_inv_check j hj
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact sncon_img_of_prep (prep_smallGen small_chain_certs.2.2.2.2.1 j
    (by rw [psl120_size]; exact sncon_J_lt hj)) h.2

private theorem sncon_gen_image
    {j : ℕ} (hj : j ∈ sncon_J) : sncon_gen j '' sncon_O = sncon_O := by
  have h := List.all_eq_true.1 sncon_inv_check j hj
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact sncon_image_bits (sncon_gen_img hj) h.1

private theorem sncon_U0_le_stab :
    sncon_U0 ≤ MulAction.stabilizer (Equiv.Perm (Fin 120)) sncon_O := by
  rw [sncon_U0, Subgroup.closure_le]
  rintro _ ⟨j, hj, rfl⟩
  rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, sncon_smul_perm]
  exact sncon_gen_image hj

private theorem sncon_U0_image
    {u : Equiv.Perm (Fin 120)} (hu : u ∈ sncon_U0) : u '' sncon_O = sncon_O := by
  have := sncon_U0_le_stab hu
  rwa [MulAction.mem_stabilizer_iff, sncon_smul_perm] at this

private theorem sncon_reach (k : ℕ)
    (hk : k < 64) : ∃ u ∈ sncon_U0, (u 5 : ℕ) = (sncon_tree.getD k (0, 0, 0)).1 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    have hc := List.all_eq_true.1 sncon_tree_check.1 k (List.mem_range.2 hk)
    rcases hE : sncon_tree.getD k (0, 0, 0) with ⟨x, i, j⟩
    simp only [sncon_treeAt, hE] at hc
    by_cases hk0 : k = 0
    · rw [if_pos hk0] at hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      exact ⟨1, one_mem _, by rw [hc.2]; rfl⟩
    · rw [if_neg hk0] at hc
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.contains_iff_mem] at hc
      obtain ⟨-, ⟨hik, hj⟩, hx⟩ := hc
      obtain ⟨u, hu, hu5⟩ := ih i hik (lt_trans hik hk)
      refine ⟨sncon_gen j * u, mul_mem (Subgroup.subset_closure ⟨j, hj, rfl⟩) hu, ?_⟩
      rw [Equiv.Perm.mul_apply, ← (sncon_gen_img hj).2, hu5, ← hx]

private theorem sncon_O_reach
    {x : Fin 120} (hx : x ∈ sncon_O) : ∃ u ∈ sncon_U0, u 5 = x := by
  have hc := List.all_eq_true.1 sncon_tree_check.2.1 x (List.mem_range.2 x.isLt)
  have hx' : sncon_mO.testBit x = true := hx
  simp only [hx', Bool.not_true, Bool.false_or, List.contains_iff_mem, List.mem_map] at hc
  obtain ⟨e, he, hex⟩ := hc
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 he
  rw [sncon_tree_check.2.2] at hk
  obtain ⟨u, hu, hu5⟩ := sncon_reach k hk
  refine ⟨u, hu, Fin.ext ?_⟩
  rw [hu5, ← hex, List.getD_eq_getElem]

private theorem sncon_five_mem : (5 : Fin 120) ∈ sncon_O := by
  show sncon_mO.testBit 5 = true
  decide +kernel

private theorem sncon_ncard_O : sncon_O.ncard = 64 := by
  rw [sncon_O_eq, Set.ncard_coe_finset, sncon_card_filter]

private theorem sncon_image_O
    {n : Equiv.Perm (Fin 120)} (hn : ∀ u ∈ sncon_U0, n * u * n⁻¹ ∈ sncon_U0) :
    n '' sncon_O = sncon_O := by
  have hcard : (n '' sncon_O).ncard = 64 := by
    rw [Set.ncard_image_of_injective _ n.injective, sncon_ncard_O]
  have hconj : ∀ u : Equiv.Perm (Fin 120), n (u 5) = (n * u * n⁻¹) (n 5) := fun u => by
    simp [Equiv.Perm.mul_apply]
  by_cases hq : n 5 ∈ sncon_O
  · have hsub : n '' sncon_O ⊆ sncon_O := by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨u, hu, rfl⟩ := sncon_O_reach hx
      rw [hconj, ← sncon_U0_image (hn u hu)]
      exact ⟨n 5, hq, rfl⟩
    exact Set.eq_of_subset_of_ncard_le hsub (by rw [hcard, sncon_ncard_O])
  · exfalso
    have hsub : n '' sncon_O ⊆ sncon_Oᶜ := by
      rintro _ ⟨x, hx, rfl⟩ hmem
      obtain ⟨u, hu, rfl⟩ := sncon_O_reach hx
      apply hq
      have e : n 5 = (n * u * n⁻¹)⁻¹ (n (u 5)) := by simp [Equiv.Perm.mul_apply]
      rw [e, ← sncon_U0_image (inv_mem (hn u hu))]
      exact ⟨_, hmem, rfl⟩
    have h := Set.ncard_le_ncard hsub
    rw [hcard, Set.ncard_compl, sncon_ncard_O, Nat.card_eq_fintype_card, Fintype.card_fin] at h
    omega

private abbrev sncon_r (j : ℕ) : Equiv.Perm (Fin 120) :=
  onu * permOfArr 120 Data.M120Chain.generators[j]! * onu⁻¹

private theorem sncon_chkConj_spec {r u : List ℕ} : ∀ {L : List ℕ} {p : ℕ},
    sncon_chkConj r u L p = true →
      ∀ i < L.length, r.getD (u.getD (p + i) 0) 0 = u.getD (L.getD i 0) 0
  | [], _, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | a :: t, p, h, i, hi => by
    simp only [sncon_chkConj, Bool.and_eq_true, beq_iff_eq] at h
    rcases i with _ | i
    · simpa using h.1
    · have := sncon_chkConj_spec h.2 i (by simpa using hi)
      rw [show p + (i + 1) = p + 1 + i by omega]
      simpa using this

private theorem sncon_r_img {j : ℕ}
    (hj : j < 2) : sncon_Img (if j = 0 then sncon_r0 else sncon_r1) (sncon_r j) := by
  have hc := sncon_conj_check
  have hu : sncon_Img Data.quotientConjugator.toList onu := sncon_img_of_prep prep_u hc.2.2.2.2.1
  have hsz : (Data.M120Chain.generators[j]!).size = 120 := by
    interval_cases j
    · exact hc.2.2.2.2.2.1
    · exact hc.2.2.2.2.2.2
  have hg := sncon_img_of_prep
    (prep_smallGen small_chain_certs.2.1 j (by rw [m120_gens_size]; exact hj)) hsz
  have hchk : sncon_chkConj (if j = 0 then sncon_r0 else sncon_r1) Data.quotientConjugator.toList
      (Data.M120Chain.generators[j]!).toList 0 = true := by
    interval_cases j
    · exact hc.1
    · exact hc.2.1
  refine ⟨by interval_cases j <;> simp [hc.2.2.1, hc.2.2.2.1], fun y => ?_⟩
  have h1 := sncon_chkConj_spec hchk (onu⁻¹ y) (by rw [hg.1]; exact (onu⁻¹ y).isLt)
  rw [zero_add, hu.2, hg.2, hu.2, Equiv.Perm.coe_inv, Equiv.apply_symm_apply] at h1
  rw [h1]
  rfl

private theorem sncon_r_mem
    {j : ℕ} (hj : j < 2) : sncon_r j ∈ RM := by
  rw [RM_eq_map, rhoM_range, onM120Chain, smallChain_sub]
  exact ⟨_, Subgroup.subset_closure ⟨j, by rw [m120_gens_size]; exact hj, rfl⟩, rfl⟩

private theorem sncon_orb_mem
    (k : ℕ) (hk : k < 105) :
    sncon_bits (sncon_orb.getD k (0, 0, 0)).1 ∈ MulAction.orbit RM sncon_O := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    have hc := List.all_eq_true.1 sncon_orb_check.1 k (List.mem_range.2 hk)
    rcases hE : sncon_orb.getD k (0, 0, 0) with ⟨M, i, j⟩
    simp only [sncon_orbAt, hE] at hc
    by_cases hk0 : k = 0
    · rw [if_pos hk0] at hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      show sncon_bits M ∈ _
      rw [hc.2]
      exact MulAction.mem_orbit_self _
    · rw [if_neg hk0] at hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨-, ⟨hik, hj⟩, hchk⟩ := hc
      obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.1 (ih i hik (lt_trans hik hk))
      rw [MulAction.mem_orbit_iff]
      refine ⟨⟨sncon_r j, sncon_r_mem hj⟩ * g, ?_⟩
      rw [mul_smul, hg, sncon_smul_RM]
      exact sncon_image_bits (sncon_r_img hj) hchk

private theorem sncon_le_ncard_orbit :
    105 ≤ (MulAction.orbit RM sncon_O).ncard := by
  set f : Fin 105 → Set (Fin 120) := fun k => sncon_bits (sncon_orb.getD k (0, 0, 0)).1
  have hlt : ∀ k : Fin 105, (sncon_orb.getD k (0, 0, 0)).1 < 2 ^ 120 := fun k => by
    have hc := List.all_eq_true.1 sncon_orb_check.1 k (List.mem_range.2 k.isLt)
    rcases hE : sncon_orb.getD k (0, 0, 0) with ⟨M, i, j⟩
    simp only [sncon_orbAt, hE, Bool.and_eq_true, decide_eq_true_eq] at hc
    exact hc.1
  have hinj : Function.Injective f := by
    intro k l hkl
    have hM := sncon_bits_inj (hlt k) (hlt l) hkl
    have hnd := sncon_orb_check.2.1
    have hlen := sncon_orb_check.2.2
    rw [List.nodup_iff_injective_get] at hnd
    have hk : (k : ℕ) < (sncon_orb.map Prod.fst).length := by simp [hlen]
    have hl : (l : ℕ) < (sncon_orb.map Prod.fst).length := by simp [hlen]
    have := @hnd ⟨k, hk⟩ ⟨l, hl⟩ (by
      simp only [List.get_eq_getElem, List.getElem_map]
      rwa [List.getD_eq_getElem _ _ (by simpa using hk),
        List.getD_eq_getElem _ _ (by simpa using hl)] at hM)
    exact Fin.ext (congrArg Fin.val this)
  have hsub : Set.range f ⊆ MulAction.orbit RM sncon_O := by
    rintro _ ⟨k, rfl⟩
    exact sncon_orb_mem k k.isLt
  have h := Set.ncard_le_ncard hsub
  rwa [Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_fin] at h

private theorem sncon_card_stab :
    Nat.card (MulAction.stabilizer RM sncon_O) ≤ 384 := by
  have h1 := (MulAction.stabilizer RM sncon_O).card_mul_index
  rw [MulAction.index_stabilizer, card_RM] at h1
  have h2 := Nat.mul_le_mul_left (Nat.card (MulAction.stabilizer RM sncon_O))
    sncon_le_ncard_orbit
  have h3 : Nat.card (MulAction.stabilizer RM sncon_O) * 105 ≤ 40320 := by
    rw [← h1]
    exact h2
  omega

private theorem sncon_transvection_mem {a b : Fin 3} (hab : a < b) (c : F4)
    {A : Matrix.SpecialLinearGroup (Fin 3) F4}
    (hA : (A : Matrix (Fin 3) (Fin 3) F4) = Matrix.transvection a b c) :
    A ∈ LinearFlag.unitriangular 3 F4 := by
  rw [LinearFlag.mem_unitriangular, hA]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · have hne : ¬ (a = i ∧ b = j) := by
      rintro ⟨rfl, rfl⟩
      exact absurd hab (not_lt.2 hij.le)
    rw [Matrix.transvection, Matrix.add_apply, Matrix.one_apply_ne (ne_of_gt hij),
      Matrix.single_apply, if_neg hne, add_zero]
  · have hne : ¬ (a = i ∧ b = i) := by
      rintro ⟨rfl, h⟩
      exact ne_of_lt hab h.symm
    rw [Matrix.transvection, Matrix.add_apply, Matrix.one_apply_eq, Matrix.single_apply,
      if_neg hne, add_zero]

private theorem sncon_elem_mem {j : ℕ} (hj : j ∈ sncon_J) :
    elemAt j ∈ LinearFlag.unitriangular 3 F4 := by
  simp only [sncon_J, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
  · exact sncon_transvection_mem (a := 0) (b := 1) (by decide) 1 rfl
  · exact sncon_transvection_mem (a := 0) (b := 1) (by decide) F4.ω rfl
  · exact sncon_transvection_mem (a := 0) (b := 2) (by decide) 1 rfl
  · exact sncon_transvection_mem (a := 0) (b := 2) (by decide) F4.ω rfl
  · exact sncon_transvection_mem (a := 1) (b := 2) (by decide) 1 rfl
  · exact sncon_transvection_mem (a := 1) (b := 2) (by decide) F4.ω rfl

private def sncon_V : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F4) :=
  Subgroup.closure (elemAt '' {j | j ∈ sncon_J})

private theorem sncon_U0_eq_map :
    sncon_U0 = sncon_V.map psi := by
  rw [sncon_V, MonoidHom.map_closure, sncon_U0, ← Set.image_comp]
  congr 1
  ext g
  simp only [Set.mem_setOf_eq, Set.mem_image, Function.comp_apply]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, hj, psi_elem (sncon_J_lt hj)⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, hj, (psi_elem (sncon_J_lt hj)).symm⟩

private theorem sncon_card_unitriangular : Nat.card (LinearFlag.unitriangular 3 F4) = 64 := by
  rw [LinearFlag.card_unitriangular, natCard_F4']
  norm_num

private theorem sncon_le_card_U0 :
    64 ≤ Nat.card sncon_U0 := by
  rw [← sncon_ncard_O, ← Nat.card_coe_set_eq]
  refine Nat.card_le_card_of_surjective (fun u : sncon_U0 => (⟨(u : Equiv.Perm (Fin 120)) 5,
    by rw [← sncon_U0_image u.2]; exact ⟨5, sncon_five_mem, rfl⟩⟩ : sncon_O)) ?_
  rintro ⟨x, hx⟩
  obtain ⟨u, hu, rfl⟩ := sncon_O_reach hx
  exact ⟨⟨u, hu⟩, rfl⟩

private theorem sncon_U0_eq :
    sncon_U0 = (LinearFlag.unitriangular 3 F4).map psi ∧ Nat.card sncon_U0 = 64 := by
  have hV : sncon_V ≤ LinearFlag.unitriangular 3 F4 := by
    rw [sncon_V, Subgroup.closure_le]
    rintro _ ⟨j, hj, rfl⟩
    exact sncon_elem_mem hj
  have h1 : Nat.card sncon_U0 ≤ Nat.card sncon_V := by
    rw [sncon_U0_eq_map]
    exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd _ _)
  have h2 := Subgroup.card_le_of_le hV
  rw [sncon_card_unitriangular] at h2
  have h64 := sncon_le_card_U0
  have hVeq : sncon_V = LinearFlag.unitriangular 3 F4 :=
    Subgroup.eq_of_le_of_card_ge hV (by rw [sncon_card_unitriangular]; omega)
  refine ⟨by rw [sncon_U0_eq_map, hVeq], ?_⟩
  omega

private def sncon_D : Matrix.SpecialLinearGroup (Fin 3) F4 :=
  ⟨Matrix.diagonal ![F4.ω, F4.ω * F4.ω, 1], by
    rw [Matrix.det_diagonal, Fin.prod_univ_three]
    decide +kernel⟩

private theorem sncon_D_coe : (sncon_D : Matrix (Fin 3) (Fin 3) F4) =
    Matrix.diagonal ![F4.ω, F4.ω * F4.ω, 1] := rfl

private theorem sncon_D_pow : sncon_D ^ 3 = 1 := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_pow, sncon_D_coe, Matrix.diagonal_pow,
    Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> decide +kernel

private theorem sncon_D_inv : sncon_D⁻¹ = sncon_D * sncon_D :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_three, sncon_D_pow])

private theorem sncon_D_not_scalar : sncon_D ∉ scalars3 := by
  rintro ⟨c, -, hc⟩
  have h0 := congrFun (congrFun hc 0) 0
  have h2 := congrFun (congrFun hc 2) 2
  rw [sncon_D_coe] at h0 h2
  simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq] at h0 h2
  rw [← h2] at h0
  exact absurd h0 (by decide +kernel)

private theorem sncon_D_conj {A : Matrix.SpecialLinearGroup (Fin 3) F4}
    (hA : A ∈ LinearFlag.unitriangular 3 F4) :
    sncon_D * A * sncon_D⁻¹ ∈ LinearFlag.unitriangular 3 F4 := by
  rw [LinearFlag.mem_unitriangular] at hA ⊢
  rw [sncon_D_inv]
  simp only [Matrix.SpecialLinearGroup.coe_mul, sncon_D_coe, Matrix.diagonal_mul_diagonal,
    Matrix.mul_diagonal, Matrix.diagonal_mul]
  refine ⟨fun i j hij => by rw [hA.1 i j hij, mul_zero, zero_mul], fun i => ?_⟩
  rw [hA.2 i, mul_one]
  fin_cases i <;> decide +kernel

private theorem sncon_g3_mem :
    psi sncon_D ∈ RM :=
  onX_le_RM (by rw [← psi_range]; exact ⟨sncon_D, rfl⟩)

private theorem sncon_orderOf_g3 :
    orderOf (psi sncon_D) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime (by rw [← map_pow, sncon_D_pow, map_one]) fun h => ?_
  apply sncon_D_not_scalar
  rw [← psi_ker]
  exact h

private theorem sncon_g3_conj
    {u : Equiv.Perm (Fin 120)} (hu : u ∈ sncon_U0) :
    psi sncon_D * u * (psi sncon_D)⁻¹ ∈ sncon_U0 := by
  rw [sncon_U0_eq.1] at hu ⊢
  obtain ⟨A, hA, rfl⟩ := hu
  exact ⟨_, sncon_D_conj hA, by simp only [map_mul, map_inv]⟩

private theorem sncon_g3_conj_inv
    {u : Equiv.Perm (Fin 120)} (hu : u ∈ sncon_U0) :
    (psi sncon_D)⁻¹ * u * psi sncon_D ∈ sncon_U0 := by
  have e1 : psi sncon_D * psi sncon_D = (psi sncon_D)⁻¹ := by
    rw [← map_mul, ← sncon_D_inv, map_inv]
  have e2 : (psi sncon_D)⁻¹ * (psi sncon_D)⁻¹ = psi sncon_D := by
    rw [← mul_inv_rev, e1, inv_inv]
  have e3 : (psi sncon_D)⁻¹ * u * psi sncon_D =
      psi sncon_D * (psi sncon_D * u * (psi sncon_D)⁻¹) * (psi sncon_D)⁻¹ := by
    calc (psi sncon_D)⁻¹ * u * psi sncon_D =
        (psi sncon_D * psi sncon_D) * u * ((psi sncon_D)⁻¹ * (psi sncon_D)⁻¹) := by
          rw [e1, e2]
      _ = _ := by group
  rw [e3]
  exact sncon_g3_conj (sncon_g3_conj hu)

private theorem sncon_exists_conj {G : Type*} [Group G] [Finite G] {X A B : Subgroup G}
    (hA : A ≤ X) (hB : B ≤ X) (hAc : Nat.card A = 64) (hBc : Nat.card B = 64)
    (hX : Nat.card X = 20160) : ∃ x : G, A = B.map (MulAut.conj x).toMonoidHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have key : ∀ C : Subgroup G, C ≤ X → Nat.card C = 64 →
      ∃ P : Sylow 2 X, (P : Subgroup X) = C.subgroupOf X := fun C hC hCc => by
    have hc : Nat.card (C.subgroupOf X) = 64 := by
      rw [← hCc]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hC).toEquiv
    have hp : IsPGroup 2 (C.subgroupOf X) := IsPGroup.of_card (n := 6) (by rw [hc]; norm_num)
    have hi : (C.subgroupOf X).index = 315 := by
      have h := (C.subgroupOf X).card_mul_index
      rw [hc, hX] at h
      omega
    exact ⟨hp.toSylow (by rw [hi]; decide), IsPGroup.toSylow_coe hp _⟩
  obtain ⟨PA, hPA⟩ := key A hA hAc
  obtain ⟨PB, hPB⟩ := key B hB hBc
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X PB PA
  refine ⟨(g : G), ?_⟩
  have hsub : ∀ y : X, (y : G) ∈ A ↔ (g : G)⁻¹ * y * g ∈ B := fun y => by
    have h := congrArg (fun P : Sylow 2 X => y ∈ (P : Subgroup X)) hg
    simp only [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, hPA, hPB,
      Subgroup.mem_subgroupOf, eq_iff_iff] at h
    rw [← h]
    simp [MulAut.smul_def, MulAut.conj_symm_apply]
  ext y
  constructor
  · intro hy
    refine ⟨(g : G)⁻¹ * y * g, (hsub ⟨y, hA hy⟩).1 hy, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · rintro ⟨b, hb, rfl⟩
    have hbX : (MulAut.conj (g : G)) b ∈ X := by
      rw [MulAut.conj_apply]
      exact mul_mem (mul_mem g.2 (hB hb)) (inv_mem g.2)
    refine (hsub ⟨_, hbX⟩).2 ?_
    have e : (g : G)⁻¹ * (MulAut.conj (g : G)) b * g = b := by
      rw [MulAut.conj_apply]
      group
    show (g : G)⁻¹ * (MulAut.conj (g : G)) b * g ∈ B
    rw [e]
    exact hb

theorem sncon_card_normalizer
    {C : Subgroup RM}
    (hCX : C ≤ XR) (hC : Nat.card C = 64)
    (h128 : 128 ∣ Nat.card (Subgroup.normalizer (C : Set RM))) :
    Nat.card (Subgroup.normalizer (C : Set RM)) = 384 := by
  have hUX : sncon_U0 ≤ onX := by
    rw [sncon_U0_eq.1, ← psi_range, MonoidHom.range_eq_map]
    exact Subgroup.map_mono le_top
  have hURM : sncon_U0 ≤ RM := hUX.trans onX_le_RM
  set U0R : Subgroup RM := sncon_U0.subgroupOf RM
  have hU0X : U0R ≤ XR := fun u hu => Subgroup.mem_subgroupOf.2 (hUX (Subgroup.mem_subgroupOf.1 hu))
  have hU0c : Nat.card U0R = 64 := by
    rw [← sncon_U0_eq.2]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hURM).toEquiv
  have hXR : Nat.card XR = 20160 := by
    rw [← card_onX]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe onX_le_RM).toEquiv
  obtain ⟨x, hx⟩ := sncon_exists_conj hCX hU0X hC hU0c hXR
  have hcard : Nat.card (Subgroup.normalizer (C : Set RM)) =
      Nat.card (Subgroup.normalizer (U0R : Set RM)) := by
    rw [hx, ← Subgroup.map_equiv_normalizer_eq,
      Subgroup.card_map_of_injective (MulAut.conj x).injective]
  rw [hcard] at h128 ⊢
  have hle : Subgroup.normalizer (U0R : Set RM) ≤ MulAction.stabilizer RM sncon_O := by
    intro n hn
    rw [MulAction.mem_stabilizer_iff, sncon_smul_RM]
    refine sncon_image_O fun u hu => ?_
    have h := (Subgroup.mem_normalizer_iff.1 hn ⟨u, hURM hu⟩).1 (Subgroup.mem_subgroupOf.2 hu)
    exact Subgroup.mem_subgroupOf.1 h
  have h1 := (Subgroup.card_le_of_le hle).trans sncon_card_stab
  have hg3 : (⟨psi sncon_D, sncon_g3_mem⟩ : RM) ∈ Subgroup.normalizer (U0R : Set RM) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact Subgroup.mem_subgroupOf.2 (sncon_g3_conj (Subgroup.mem_subgroupOf.1 hh))
    · intro hh
      have := sncon_g3_conj_inv (Subgroup.mem_subgroupOf.1 hh)
      refine Subgroup.mem_subgroupOf.2 ?_
      convert this using 1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
  have h3 : 3 ∣ Nat.card (Subgroup.normalizer (U0R : Set RM)) := by
    have := orderOf_dvd_natCard (⟨_, hg3⟩ : Subgroup.normalizer (U0R : Set RM))
    rwa [Subgroup.orderOf_mk, Subgroup.orderOf_mk, sncon_orderOf_g3] at this
  have h384 : 384 ∣ Nat.card (Subgroup.normalizer (U0R : Set RM)) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h128 h3
  obtain ⟨c, hc⟩ := h384
  have hpos : 0 < Nat.card (Subgroup.normalizer (U0R : Set RM)) := Nat.card_pos
  rw [hc] at h1 hpos ⊢
  have : c = 1 := by omega
  rw [this]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
