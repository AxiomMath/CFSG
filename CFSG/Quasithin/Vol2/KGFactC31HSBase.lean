module

public import CFSG.Quasithin.Vol2.KGFactC31HSCert
public import CFSG.Quasithin.Vol2.KGFactC31OrbSound
public import CFSG.RankThree.Native.HSMcLSmall

public section

namespace CFSG.Quasithin.KGC31.HS

open CFSG.Open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Quasithin.KGC31.Native
  CFSG.Quasithin.KGC31 CFSG.RankThree.Native

abbrev G₀ : Type := ↥hs100P

theorem hn100 : (100 : ℕ) < 2 ^ 32 := by norm_num

theorem permA_eq : permA = hs100A := by
  have h := c_permA
  rw [permOK, Bool.and_eq_true] at h
  exact CFSG.Sporadic.HeldB.permOrId_eq_permOfArr h

theorem permB_eq : permB = hs100B := by
  have h := c_permB
  rw [permOK, Bool.and_eq_true] at h
  exact CFSG.Sporadic.HeldB.permOrId_eq_permOfArr h

theorem hgens : ∀ l, gensG l ∈ hs100P := fun l => by
  unfold gensG
  split_ifs
  · rw [permA_eq]; exact Subgroup.subset_closure (Set.mem_insert _ _)
  · rw [permB_eq]; exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem hrep : ∀ l, Rep 100 (gensT l) (gensG l) := fun l => by
  unfold gensT gensG
  split_ifs
  · exact rep_toTable hn100 _
  · exact rep_toTable hn100 _

@[expose] noncomputable def elt (w : List ℤ) : G₀ :=
  ⟨wordG gensG w, wordG_mem_of _ hgens w⟩

theorem rep_elt (w : List ℤ) :
    Rep 100 (wordT 100 gensT w) ((elt w : G₀) : Equiv.Perm (Fin 100)) :=
  Rep.wordT hn100 w fun l _ => hrep l

theorem coe_elt (w : List ℤ) :
    ((elt w : G₀) : Equiv.Perm (Fin 100)) = wordG gensG w := rfl

theorem b0_eq : ((elt [1] : G₀) : Equiv.Perm (Fin 100)) = permA := by
  rw [coe_elt]
  simp [wordG, gensG]

theorem rep_b0 :
    Rep 100 b0T ((elt [1] : G₀) : Equiv.Perm (Fin 100)) := by
  rw [b0_eq]
  exact rep_toTable hn100 _

theorem rep_rB :
    Rep 100 rBT ((elt wB : G₀) : Equiv.Perm (Fin 100)) :=
  rep_elt wB

theorem rep_genArr :
    ∀ l < genArr.size, Rep 100 genArr[l]! (gensG (l + 1 : ℕ)) ∧
      Rep 100 genInvArr[l]! (gensG (l + 1 : ℕ))⁻¹ ∧ gensG (l + 1 : ℕ) ∈ hs100P := by
  intro l hl
  have hl2 : l < 2 := hl
  interval_cases l
  · have hA : Rep 100 aT (gensG 1) := by
      have h := hrep 1
      rwa [show gensT 1 = aT from if_pos rfl] at h
    exact ⟨by simpa [genArr] using hA, by
      simpa [genInvArr] using Rep.inv_of_invOK hA c_invA, hgens 1⟩
  · have hB : Rep 100 bT (gensG ((1 : ℕ) + 1 : ℕ)) := by
      simp only [gensG]; norm_num; exact rep_toTable hn100 _
    exact ⟨by simpa [genArr] using hB, by
      simpa [genInvArr] using Rep.inv_of_invOK hB c_invB, hgens _⟩

theorem linePerm_eq {j : ℕ} (hj : j = 0 ∨ j = 2 ∨ j = 23) :
    linePerm j = hs100FiveLine ⟨j, by omega⟩ := by
  have h : permOK hs100FiveLines[j]! = true := by
    rcases hj with rfl | rfl | rfl
    · exact c_line0
    · exact c_line2
    · exact c_line23
  rw [permOK, Bool.and_eq_true] at h
  exact CFSG.Sporadic.HeldB.permOrId_eq_permOfArr h

theorem rep_lineT (j : ℕ) : Rep 100 (lineT j) (linePerm j) := rep_toTable hn100 _

@[expose] noncomputable def genOf (ws : List (List ℤ)) :
    Subgroup G₀ :=
  Subgroup.closure {x | ∃ w ∈ ws, elt w = x}

theorem elt_mem_genOf {ws : List (List ℤ)} {w : List ℤ}
    (hw : w ∈ ws) : elt w ∈ genOf ws :=
  Subgroup.subset_closure ⟨w, hw, rfl⟩

theorem map_genOf (ws : List (List ℤ)) :
    (genOf ws).map hs100P.subtype = Subgroup.closure {g | g ∈ permsOf ws} := by
  rw [genOf, MonoidHom.map_closure]
  congr 1
  ext g
  simp only [Set.mem_image, Set.mem_ofPred_eq, permsOf, List.mem_map, tab_eq]
  constructor
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨w, hw, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨_, ⟨w, hw, rfl⟩, rfl⟩

theorem card_genOf {ws : List (List ℤ)} {Q : RawSchreierDatum 100}
    (hQ : Q.originalSubgroup = Subgroup.closure {g | g ∈ permsOf ws}) (hv : ValidSchreier Q) :
    Nat.card (genOf ws) = Q.orderCertificate := by
  rw [Q.orderCertificate_eq_card hv, hQ, ← map_genOf,
    Subgroup.card_map_of_injective Subtype.val_injective]

@[expose] noncomputable def caGroup : Subgroup G₀ := genOf caGenW

@[expose] noncomputable def crGroup : Subgroup G₀ := genOf crGenW

@[expose] noncomputable def t0Group : Subgroup G₀ := genOf t0GenW

theorem card_caGroup : Nat.card caGroup = 7680 := by
  rw [caGroup, card_genOf (Q := caChain) (certificate_originalSubgroup _ _ _ _ _) c_caCheck,
    c_caOrder]

theorem card_crGroup : Nat.card crGroup = 2880 := by
  rw [crGroup, card_genOf (Q := crChain) (certificate_originalSubgroup _ _ _ _ _) c_crCheck,
    c_crOrder]

theorem card_t0Group : Nat.card t0Group = 512 := by
  rw [t0Group, card_genOf (Q := t0Chain) (certificate_originalSubgroup _ _ _ _ _) c_t0Check,
    c_t0Order]

theorem genOf_le_centralizer {ws : List (List ℤ)} {x : G₀}
    {xT : Table} (hx : Rep 100 xT (x : Equiv.Perm (Fin 100)))
    (h : ((tabsOf ws).all fun g => commT 100 xT g) = true) :
    genOf ws ≤ Subgroup.centralizer ({x} : Set G₀) := by
  rw [genOf, Subgroup.closure_le]
  rintro _ ⟨w, hw, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  have h1 := List.all_eq_true.mp h (wordT 100 gensT w) (List.mem_map.mpr ⟨w, hw, rfl⟩)
  rw [commT] at h1
  have h2 := (tblEq_iff_eq (Rep.compT hx (rep_elt w)) (Rep.compT (rep_elt w) hx)).mp h1
  exact Subtype.ext h2.symm

theorem caGroup_le :
    caGroup ≤ Subgroup.centralizer ({elt [1]} : Set G₀) :=
  genOf_le_centralizer rep_b0 c_caComm

theorem crGroup_le :
    crGroup ≤ Subgroup.centralizer ({elt wB} : Set G₀) :=
  genOf_le_centralizer rep_rB c_crComm

theorem card_G₀ : Nat.card G₀ = 44352000 := card_hs100P

theorem card_image_conj_mul_le [Fintype G₀] {x : G₀} {K : Subgroup G₀}
    (hK : K ≤ Subgroup.centralizer ({x} : Set G₀)) :
    (Finset.univ.image fun c : G₀ => c * x * c⁻¹).card * Nat.card K ≤ Nat.card G₀ := by
  classical
  set f : G₀ → G₀ := fun c => c * x * c⁻¹ with hf
  have hfib : ∀ c d : G₀, d⁻¹ * c ∈ Subgroup.centralizer ({x} : Set G₀) → f c = f d := by
    intro c d hcd
    rw [Subgroup.mem_centralizer_singleton_iff] at hcd
    simp only [hf]
    calc c * x * c⁻¹ = d * ((d⁻¹ * c) * x) * c⁻¹ := by group
      _ = d * (x * (d⁻¹ * c)) * c⁻¹ := by rw [hcd]
      _ = d * x * d⁻¹ := by group
  set S : Finset G₀ := Finset.univ.image f with hS
  have hcov : ∀ s ∈ S, Nat.card K ≤ (Finset.univ.filter fun c => f c = s).card := by
    intro s hs
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hs
    have hinj : Function.Injective fun k : K => c * (k : G₀) := fun a b hab =>
      Subtype.ext (mul_left_cancel hab)
    rw [← Nat.card_eq_finsetCard]
    refine Nat.card_le_card_of_injective (fun k : K => ⟨c * k, ?_⟩) fun a b hab => ?_
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine hfib _ _ ?_
      simpa using hK k.2
    · exact hinj (congrArg Subtype.val hab)
  calc S.card * Nat.card K ≤ ∑ s ∈ S, (Finset.univ.filter fun c => f c = s).card := by
        rw [← smul_eq_mul, ← Finset.sum_const]
        exact Finset.sum_le_sum hcov
    _ = (Finset.univ : Finset G₀).card := by
        rw [← Finset.card_eq_sum_card_fiberwise]
        intro c _
        exact Finset.mem_image_of_mem f (Finset.mem_univ c)
    _ = Nat.card G₀ := by rw [Finset.card_univ, Nat.card_eq_fintype_card]

theorem exists_finset_of_conj_list [Fintype G₀] {x : G₀} {L : List Table}
    {Lg : List (Equiv.Perm (Fin 100))}
    (hL : List.Forall₂ (Rep 100) L Lg) (hnd : Lg.Nodup)
    (hconj : ∀ g ∈ Lg, ∃ c : G₀, g = ((c * x * c⁻¹ : G₀) : Equiv.Perm (Fin 100))) :
    ∃ E : Finset G₀, E.card = L.length ∧
      E ⊆ Finset.univ.image (fun c : G₀ => c * x * c⁻¹) ∧
      ∀ y ∈ E, ∃ T ∈ L, Rep 100 T (y : Equiv.Perm (Fin 100)) := by
  classical
  have hEL : ∀ g ∈ Lg, g ∈ hs100P := by
    intro g hg
    obtain ⟨c, rfl⟩ := hconj g hg
    exact (c * x * c⁻¹).2
  refine ⟨(Lg.attach.map fun g => (⟨g.1, hEL g.1 g.2⟩ : G₀)).toFinset, ?_, ?_, ?_⟩
  · rw [List.toFinset_card_of_nodup, List.length_map, List.length_attach, hL.length_eq]
    refine (List.nodup_attach.mpr hnd).map fun a b hab => ?_
    exact Subtype.ext (congrArg (fun y : G₀ => (y : Equiv.Perm (Fin 100))) hab)
  · intro g hg
    rw [List.mem_toFinset, List.mem_map] at hg
    obtain ⟨⟨g', hg'⟩, -, rfl⟩ := hg
    obtain ⟨c, hc⟩ := hconj g' hg'
    rw [Finset.mem_image]
    exact ⟨c, Finset.mem_univ _, Subtype.ext hc.symm⟩
  · intro y hy
    rw [List.mem_toFinset, List.mem_map] at hy
    obtain ⟨⟨g, hg⟩, -, rfl⟩ := hy
    exact exists_tab_of_mem hL hg

theorem mem_of_conj_list {x : G₀} {L : List Table} {Lg : List (Equiv.Perm (Fin 100))}
    (hL : List.Forall₂ (Rep 100) L Lg) (hnd : Lg.Nodup)
    (hconj : ∀ g ∈ Lg, ∃ c : G₀, g = ((c * x * c⁻¹ : G₀) : Equiv.Perm (Fin 100)))
    {K : Subgroup G₀} (hK : K ≤ Subgroup.centralizer ({x} : Set G₀))
    (hcard : Nat.card G₀ ≤ L.length * Nat.card K) (c : G₀) :
    ∃ T ∈ L, Rep 100 T ((c * x * c⁻¹ : G₀) : Equiv.Perm (Fin 100)) := by
  classical
  obtain ⟨E, hEcard, hES, hErep⟩ := exists_finset_of_conj_list hL hnd hconj
  have hmul := card_image_conj_mul_le hK
  have hKpos : 0 < Nat.card K := Nat.card_pos
  have hSL : (Finset.univ.image fun c : G₀ => c * x * c⁻¹).card ≤ L.length := by
    by_contra hlt
    push Not at hlt
    have : (L.length + 1) * Nat.card K ≤
        (Finset.univ.image fun c : G₀ => c * x * c⁻¹).card * Nat.card K :=
      Nat.mul_le_mul_right _ hlt
    nlinarith
  have hESeq := Finset.eq_of_subset_of_card_le hES (by rw [hEcard]; exact hSL)
  exact hErep _ (hESeq ▸ Finset.mem_image_of_mem _ (Finset.mem_univ c))

theorem card_centralizer_le_of_conj_list {x : G₀} {L : List Table}
    {Lg : List (Equiv.Perm (Fin 100))} (hL : List.Forall₂ (Rep 100) L Lg) (hnd : Lg.Nodup)
    (hconj : ∀ g ∈ Lg, ∃ c : G₀, g = ((c * x * c⁻¹ : G₀) : Equiv.Perm (Fin 100))) :
    L.length * Nat.card (Subgroup.centralizer ({x} : Set G₀)) ≤ Nat.card G₀ := by
  classical
  obtain ⟨E, hEcard, hES, -⟩ := exists_finset_of_conj_list hL hnd hconj
  have hmul := card_image_conj_mul_le (le_refl (Subgroup.centralizer ({x} : Set G₀)))
  rw [← hEcard]
  exact le_trans (Nat.mul_le_mul_right _ (Finset.card_le_card hES)) hmul

theorem conj_of_tree {x : G₀} {xT : Table}
    (hx : Rep 100 xT (x : Equiv.Perm (Fin 100))) {elts : Array Table} {par lab : Array ℕ}
    (h : conjTreeOK 100 genArr genInvArr xT elts par lab = true) :
    List.Forall₂ (Rep 100) elts.toList (elts.toList.map (tablePerm 100)) ∧
      ∀ g ∈ elts.toList.map (tablePerm 100), ∃ c : G₀,
        g = ((c * x * c⁻¹ : G₀) : Equiv.Perm (Fin 100)) := by
  have hspec := conjTreeOK_spec hs100P (gg := fun l => gensG (l + 1 : ℕ)) rep_genArr hx h
  have hent : ∀ T ∈ elts.toList, ∃ c ∈ hs100P,
      Rep 100 T (c * (x : Equiv.Perm (Fin 100)) * c⁻¹) := by
    intro T hT
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hT
    rw [Array.length_toList] at hk
    obtain ⟨c, hc, hrep⟩ := hspec k hk
    refine ⟨c, hc, ?_⟩
    rw [Array.getElem_toList]
    rwa [getElem!_pos elts k hk] at hrep
  refine ⟨?_, ?_⟩
  · rw [List.forall₂_map_right_iff]
    refine List.forall₂_same.2 fun T hT => ?_
    obtain ⟨c, -, hrep⟩ := hent T hT
    rw [tablePerm_eq hrep]
    exact hrep
  · intro g hg
    obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hg
    obtain ⟨c, hc, hrep⟩ := hent T hT
    exact ⟨⟨c, hc⟩, by rw [tablePerm_eq hrep]; rfl⟩

theorem exists_tab_clA (c : G₀) :
    ∃ T ∈ clA.1.toList, Rep 100 T ((c * elt [1] * c⁻¹ : G₀) : Equiv.Perm (Fin 100)) := by
  obtain ⟨hL, hconj⟩ := conj_of_tree rep_b0 c_treeA
  refine mem_of_conj_list hL (nodup_of_keysDistinct hL c_keysA) hconj caGroup_le ?_ c
  rw [Array.length_toList, c_sizeA, card_caGroup, card_G₀]

theorem exists_tab_clB (c : G₀) :
    ∃ T ∈ clB.1.toList, Rep 100 T ((c * elt wB * c⁻¹ : G₀) : Equiv.Perm (Fin 100)) := by
  obtain ⟨hL, hconj⟩ := conj_of_tree rep_rB c_treeB
  refine mem_of_conj_list hL (nodup_of_keysDistinct hL c_keysB) hconj crGroup_le ?_ c
  rw [Array.length_toList, c_sizeB, card_crGroup, card_G₀]

theorem t0_sylow :
    IsPGroup 2 t0Group ∧ ¬ 2 ∣ t0Group.index := by
  refine ⟨IsPGroup.of_card (n := 9) (by rw [card_t0Group]; norm_num), ?_⟩
  have h := t0Group.card_mul_index
  rw [card_t0Group, card_G₀] at h
  have : t0Group.index = 86625 := by omega
  rw [this]
  norm_num

theorem invCovered_iff {T : Table} {g : Equiv.Perm (Fin 100)} (hT : Rep 100 T g) :
    invCovered T = true ↔ ((¬ g * g = 1 ∨ g = 1) ∨ ∃ T' ∈ invs, Rep 100 T' g) := by
  have h1 := tblEq_iff_eq (Rep.compT hT hT) (Rep.idT (G := Equiv.Perm (Fin 100)) hn100)
  have h2 := tblEq_iff_eq hT (Rep.idT (G := Equiv.Perm (Fin 100)) hn100)
  have h3 : invs.any (tblEq 100 T) = true ↔ ∃ T' ∈ invs, Rep 100 T' g := by
    rw [List.any_eq_true]
    constructor
    · rintro ⟨T', hT', h⟩
      exact ⟨T', hT', fun i hi => by rw [← (tblEq_iff.mp h) i hi]; exact hT i hi⟩
    · rintro ⟨T', hT', h⟩
      exact ⟨T', hT', (tblEq_iff_eq hT h).mpr rfl⟩
  unfold invCovered
  rw [Bool.or_eq_true, Bool.or_eq_true, h2, h3, ← h1]
  cases tblEq 100 (compT 100 T T) (idT 100) <;> simp

theorem t0_covered {u : G₀} (hu : u ∈ t0Group)
    (hu2 : orderOf u = 2) : ∃ T ∈ invs, Rep 100 T (u : Equiv.Perm (Fin 100)) := by
  classical
  have hcount := card_subtype_eq_countProducts hn100 t0Chain c_t0Check
    (P := fun x => (¬ x * x = 1 ∨ x = 1) ∨ ∃ T' ∈ invs, Rep 100 T' x)
    (fun T x hT => invCovered_iff hT)
  rw [c_t0Cover] at hcount
  have hall : ∀ x : t0Chain.originalSubgroup,
      (¬ (x : Equiv.Perm (Fin 100)) * x = 1 ∨ (x : Equiv.Perm (Fin 100)) = 1) ∨
        ∃ T' ∈ invs, Rep 100 T' (x : Equiv.Perm (Fin 100)) := by
    by_contra hno
    obtain ⟨x, hx⟩ := not_forall.mp hno
    have hlt := Finite.card_subtype_lt (p := fun x : t0Chain.originalSubgroup =>
      (¬ (x : Equiv.Perm (Fin 100)) * x = 1 ∨ (x : Equiv.Perm (Fin 100)) = 1) ∨
        ∃ T' ∈ invs, Rep 100 T' (x : Equiv.Perm (Fin 100))) (x := x) hx
    rw [hcount, ← c_t0Order, t0Chain.orderCertificate_eq_card c_t0Check] at hlt
    exact lt_irrefl _ hlt
  have humem : (u : Equiv.Perm (Fin 100)) ∈ t0Chain.originalSubgroup := by
    rw [t0Chain, certificate_originalSubgroup, ← map_genOf]
    exact ⟨u, hu, rfl⟩
  rcases hall ⟨u, humem⟩ with (h | h) | h
  · exfalso
    apply h
    have : u * u = 1 := by rw [← sq, ← hu2, pow_orderOf_eq_one]
    exact congrArg Subtype.val this
  · exfalso
    have : u = 1 := Subtype.ext h
    rw [this, orderOf_one] at hu2
    exact absurd hu2 (by norm_num)
  · exact h

theorem exists_invTab {t : G₀}
    (ht : orderOf t = 2) : ∃ T ∈ invs, Rep 100 T (t : Equiv.Perm (Fin 100)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hP, hPi⟩ := t0_sylow
  obtain ⟨g, hg⟩ := exists_conj_mem_of_sylow hP hPi ⟨1, by rw [pow_one, ← ht, pow_orderOf_eq_one]⟩
  have hu2 : orderOf (g⁻¹ * t * g) = 2 := by
    rw [show g⁻¹ * t * g = MulAut.conj g⁻¹ t by simp, MulEquiv.orderOf_eq]
    exact ht
  obtain ⟨T, hT, hTu⟩ := t0_covered hg hu2
  have htg : t = g * (g⁻¹ * t * g) * g⁻¹ := by group
  rcases List.mem_append.mp hT with hA | hB
  · obtain ⟨hL, hconj⟩ := conj_of_tree rep_b0 c_treeA
    obtain ⟨c, hc⟩ := hconj _ (List.mem_map.mpr ⟨T, hA, rfl⟩)
    rw [tablePerm_eq hTu] at hc
    have hu : g⁻¹ * t * g = c * elt [1] * c⁻¹ := Subtype.ext hc
    obtain ⟨T', hT', hrep⟩ := exists_tab_clA (g * c)
    refine ⟨T', List.mem_append_left _ hT', ?_⟩
    rw [htg, hu, show g * (c * elt [1] * c⁻¹) * g⁻¹ = g * c * elt [1] * (g * c)⁻¹ by group]
    exact hrep
  · obtain ⟨hL, hconj⟩ := conj_of_tree rep_rB c_treeB
    obtain ⟨c, hc⟩ := hconj _ (List.mem_map.mpr ⟨T, hB, rfl⟩)
    rw [tablePerm_eq hTu] at hc
    have hu : g⁻¹ * t * g = c * elt wB * c⁻¹ := Subtype.ext hc
    obtain ⟨T', hT', hrep⟩ := exists_tab_clB (g * c)
    refine ⟨T', List.mem_append_right _ hT', ?_⟩
    rw [htg, hu, show g * (c * elt wB * c⁻¹) * g⁻¹ = g * c * elt wB * (g * c)⁻¹ by group]
    exact hrep

end CFSG.Quasithin.KGC31.HS

end
