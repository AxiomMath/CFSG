module

public import CFSG.Sporadic.HNSchreier.LocalOuter
public import CFSG.Sporadic.HNSchreier.Recognition
public import CFSG.Sporadic.HNSchreier.Order
public import CFSG.LocalAnalysis.ComponentInitial.GroupAlternatingCoverPerm
public import Certificates.Certificate2096
public import Certificates.Certificate2100
public import Certificates.Certificate2102
public import Certificates.Certificate2104
public import Certificates.Certificate2107

public noncomputable section

namespace CFSG.Sporadic.HNSchreier

open CFSG.Sporadic.F5.Native CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier
open CFSG.ONSchreier.Native CFSG.Sporadic.Th.Native CFSG.Sporadic.HN.Local Matrix

theorem map_runProg {G K : Type*} [Group G] [Group K] (φ : G →* K) :
    ∀ (prog : List (ℕ × ℕ × ℕ)) (regs : ℕ → G) (r : ℕ),
      φ (runProg regs prog r) = runProg (φ ∘ regs) prog r
  | [], _, _ => rfl
  | (a, b, c) :: rest, regs, r => by
    rw [runProg, runProg, map_runProg φ rest]
    congr 1
    funext s
    by_cases hs : s = c
    · subst hs; simp
    · simp [Function.update_of_ne hs]

noncomputable abbrev permJ : JH →* Equiv.Perm X := permHom

theorem permJ_apply (g : JH) (i : X) : permJ g i = g • i := rfl

theorem permJ_aJ : permJ aJ = a0 := rfl

theorem permJ_bJ : permJ bJ = a1 := rfl

theorem permJ_jRegs (r : ℕ) : permJ (jRegs r) = permRegs r := by
  rw [jRegs, map_runProg, permRegs]
  congr 1
  funext s
  simp only [Function.comp_apply, jRegs0, permRegs0]
  split_ifs
  · exact permJ_aJ
  · exact permJ_bJ
  · exact map_one _

theorem permJ_injective :
    Function.Injective permJ := permHom_injective

theorem hJ_zero : hJ 0 = h1J := gStrong_of_lt _ _ (by simp)

theorem hJ_one : hJ 1 = h2J := gStrong_of_lt _ _ (by simp)

@[expose] def hPerm (j : ℕ) : Equiv.Perm X :=
  gStrong [permRegs 1, permRegs 2] LocalData.strongWords j

theorem permJ_hJ (j : ℕ) : permJ (hJ j) = hPerm j := by
  rw [hJ, map_gStrong, hPerm, List.map_cons, List.map_cons, List.map_nil, permJ_jRegs,
    permJ_jRegs]

@[irreducible] def hStrongArr : Array (Array ℕ) :=
  extendStrong hnsData.n #[hRegs[1]!, hRegs[2]!] LocalData.strongWords

theorem hStrongArr_eq :
    hStrongArr = extendStrong hnsData.n #[hRegs[1]!, hRegs[2]!] LocalData.strongWords := by
  unfold hStrongArr; rfl

@[irreducible] def natStrongArr : Array (Array ℕ) :=
  extendStrong 12 #[natArr LocalData.natGen1, natArr LocalData.natGen2] LocalData.strongWords

theorem natStrongArr_eq : natStrongArr =
    extendStrong 12 #[natArr LocalData.natGen1, natArr LocalData.natGen2]
      LocalData.strongWords := by
  unfold natStrongArr; rfl

@[irreducible] def xsArr : Array ℕ :=
  xIndex hStrongArr (seedWordIdx (natTab (hnsData.orbit ()).alpha) (natTab (hnsData.orbit ()).beta)
    LocalData.rootWord 0) LocalData.parents

theorem xsArr_eq : xsArr = xIndex hStrongArr (seedWordIdx (natTab (hnsData.orbit ()).alpha)
    (natTab (hnsData.orbit ()).beta) LocalData.rootWord 0) LocalData.parents := by
  unfold xsArr; rfl

theorem local_parts :
    strongOK hnsData.n hRegs[1]! hRegs[2]! hStrongArr LocalData.strongWords = true ∧
    strongOK 12 (natArr LocalData.natGen1) (natArr LocalData.natGen2) natStrongArr
      LocalData.strongWords = true ∧
    (∀ j < 17, peq 12 natStrongArr[j]! (natArr LocalData.strongImages[j]!) = true) ∧
    (∀ i < 10, plettersOK 17 LocalData.tripleWords[i]! = true ∧
      peq 12 (pword 12 natStrongArr (pinvs 12 natStrongArr) LocalData.tripleWords[i]!)
        (cycle01 (i + 2)) = true) ∧
    xsArr.size = 462 ∧
    xsArr[0]! = seedWordIdx (natTab (hnsData.orbit ()).alpha) (natTab (hnsData.orbit ()).beta)
      LocalData.rootWord 0 ∧
    (∀ i < 462, i ≠ 0 → xsArr[i]! =
      (hStrongArr[LocalData.parents[i]!.2 - 1]!)[xsArr[LocalData.parents[i]!.1]!]!) ∧
    (∀ i < 462, xsArr[i]! < hnsData.n) ∧
    (∀ i < 462, ∀ j < 462, i ≠ j → xsArr[i]! ≠ xsArr[j]!) ∧
    (∀ i < 462, (hStrongArr[0]!)[xsArr[i]!]! = xsArr[LocalData.lperm1[i]!]! ∧
      (hStrongArr[1]!)[xsArr[i]!]! = xsArr[LocalData.lperm2[i]!]!) := by
  have h := local_cert
  unfold localChecks at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rw [← hRegs_eq, ← hStrongArr_eq, ← natStrongArr_eq, ← xsArr_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, -⟩, c4⟩, -⟩, c6⟩, -⟩, c8⟩, c9⟩, c10⟩, c11⟩, c12⟩, -⟩, -⟩, c15⟩ :=
    h
  refine ⟨c1, c2, fun j hj => allBelowN_spec c4 hj, fun i hi => ?_, c8, c9, fun i hi hi0 => ?_,
    fun i hi => ?_, fun i hi j hj hij => ?_, fun i hi => ?_⟩
  · have := allBelowN_spec c6 hi
    simp only [Bool.and_eq_true] at this
    exact this
  · have := allBelowN_spec c10 hi
    simp only [Bool.or_eq_true, beq_iff_eq, hi0, false_or, Bool.and_eq_true,
      decide_eq_true_eq] at this
    exact this.2
  · have := allBelowN_spec c11 hi
    simp only [decide_eq_true_eq] at this
    exact this
  · have := allBelowN_spec (allBelowN_spec c12 hi) hj
    simp only [Bool.or_eq_true, beq_iff_eq, hij, false_or, bne_iff_ne, ne_eq] at this
    exact this
  · have := allBelowN_spec c15 hi
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
    exact ⟨this.1.2, this.2⟩

theorem strongWords_size : LocalData.strongWords.size = 17 := by decide

theorem hStrong_rep :
    ∀ j < 17, PRep hnsData.n hStrongArr[j]! (hPerm j) := by
  have hr : ∀ r < 11, PRep hnsData.n hRegs[r]! (permRegs r) := regs_rep.2
  have h := prep_of_strongOK local_parts.1 (hr 1 (by norm_num)) (hr 2 (by norm_num))
  intro j hj
  exact h.2 j (by rw [h.1, strongWords_size]; exact hj)

theorem hPerm_zero : hPerm 0 = permRegs 1 := gStrong_of_lt _ _ (by simp)

theorem hPerm_one : hPerm 1 = permRegs 2 := gStrong_of_lt _ _ (by simp)

@[expose] def natPerm1 : Equiv.Perm (Fin 12) :=
  Equiv.ofBijective (fun i => ⟨LocalData.natGen1[i.val]! % 12, Nat.mod_lt _ (by norm_num)⟩)
    (by decide +kernel)

@[expose] def natPerm2 : Equiv.Perm (Fin 12) :=
  Equiv.ofBijective (fun i => ⟨LocalData.natGen2[i.val]! % 12, Nat.mod_lt _ (by norm_num)⟩)
    (by decide +kernel)

theorem prep_natPerm1 : PRep 12 (natArr LocalData.natGen1) natPerm1 := by
  unfold PRep natPerm1
  decide +kernel

theorem prep_natPerm2 : PRep 12 (natArr LocalData.natGen2) natPerm2 := by
  unfold PRep natPerm2
  decide +kernel

theorem natPerm1_mem : natPerm1 ∈ alternatingGroup (Fin 12) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  unfold natPerm1
  decide +kernel

theorem natPerm2_mem : natPerm2 ∈ alternatingGroup (Fin 12) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  unfold natPerm2
  decide +kernel

@[expose] def natImg (j : ℕ) : Equiv.Perm (Fin 12) :=
  gStrong [natPerm1, natPerm2] LocalData.strongWords j

theorem natStrong_rep :
    ∀ j < 17, PRep 12 natStrongArr[j]! (natImg j) := by
  have h := prep_of_strongOK local_parts.2.1 prep_natPerm1 prep_natPerm2
  intro j hj
  exact h.2 j (by rw [h.1, strongWords_size]; exact hj)

theorem prep_cycle01 (i : Fin 10) :
    PRep 12 (cycle01 (i.val + 2)) (CFSG.LocalAnalysis.ComponentInitial.altThreeCyclePerm i) := by
  revert i
  unfold PRep cycle01 CFSG.LocalAnalysis.ComponentInitial.altThreeCyclePerm
  decide +kernel

theorem natImg_mem (j : ℕ) : natImg j ∈ Subgroup.closure {natPerm1, natPerm2} := by
  refine gStrong_mem _ _ _ ?_ j
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem closure_natPerm :
    Subgroup.closure ({natPerm1, natPerm2} : Set (Equiv.Perm (Fin 12))) =
    alternatingGroup (Fin 12) := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact natPerm1_mem
    · exact natPerm2_mem
  · rw [← CFSG.LocalAnalysis.ComponentInitial.closure_altThreeCyclePerm (n := 10),
      Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨hlet, hpeq⟩ := local_parts.2.2.2.1 i.val i.isLt
    have hw := prep_pword (S := natStrongArr) (Sinv := pinvs 12 natStrongArr) (gs := natImg)
      (j := 17) (fun h hh => natStrong_rep h hh)
      (fun h hh => prep_inv_of_pisInv (natStrong_rep h hh) (by
        have h2 := local_parts.2.1
        unfold strongOK at h2
        simp only [Bool.and_eq_true] at h2
        have := allBelowN_spec h2.1.2 (show h < natStrongArr.size by
          have := (prep_of_strongOK local_parts.2.1 prep_natPerm1 prep_natPerm2).1
          rw [this, strongWords_size]; exact hh)
        exact this)) _ hlet
    have heq := eq_of_peq hw (prep_cycle01 i) hpeq
    rw [← heq]
    apply (Subgroup.closure_le _).2 ?_ (Quiver.SchreierGraph.evalWord_mem_closure _ _)
    rintro _ ⟨h, rfl⟩
    exact natImg_mem h

@[expose] def xPt
    (k : Fin 462) : X := ⟨xsArr[k.val]!, local_parts.2.2.2.2.2.2.2.1 k.val k.isLt⟩

theorem xPt_injective : Function.Injective xPt := by
  intro k k' h
  by_contra hne
  exact local_parts.2.2.2.2.2.2.2.2.1 k k.isLt k' k'.isLt (fun e => hne (Fin.ext e))
    (congrArg Fin.val h)

@[expose] def lIdx1 (k : Fin 462) : Fin 462 :=
  ⟨LocalData.lperm1[k.val]!, (label_parts.2.2.2.2.2 k k.isLt).1⟩

@[expose] def lIdx2 (k : Fin 462) : Fin 462 :=
  ⟨LocalData.lperm2[k.val]!, (label_parts.2.2.2.2.2 k k.isLt).2.1⟩

theorem hPerm0_xPt
    (k : Fin 462) : hPerm 0 (xPt k) = xPt (lIdx1 k) := by
  apply Fin.ext
  rw [← hStrong_rep 0 (by norm_num) (xPt k)]
  exact (local_parts.2.2.2.2.2.2.2.2.2 k k.isLt).1

theorem hPerm1_xPt
    (k : Fin 462) : hPerm 1 (xPt k) = xPt (lIdx2 k) := by
  apply Fin.ext
  rw [← hStrong_rep 1 (by norm_num) (xPt k)]
  exact (local_parts.2.2.2.2.2.2.2.2.2 k k.isLt).2

theorem HP_maps_xPt
    {g : Equiv.Perm X} (hg : g ∈ HP) (k : Fin 462) : ∃ k', g (xPt k) = xPt k' := by
  let S : Set X := Set.range xPt
  have hstep : ∀ g ∈ ({permRegs 1, permRegs 2} : Set (Equiv.Perm X)), ∀ y ∈ S, g y ∈ S := by
    rintro g (rfl | rfl) _ ⟨k, rfl⟩
    · exact ⟨lIdx1 k, by rw [← hPerm0_xPt, hPerm_zero]⟩
    · exact ⟨lIdx2 k, by rw [← hPerm1_xPt, hPerm_one]⟩
  have hfin : ∀ x : Equiv.Perm X, (∀ y ∈ S, x y ∈ S) → ∀ y ∈ S, x⁻¹ y ∈ S := by
    intro x hx
    have hmaps : Set.MapsTo x S S := fun y hy => hx y hy
    have hinj : Set.InjOn x S := fun a _ b _ hab => x.injective hab
    have hsurj := (Set.Finite.injOn_iff_bijOn_of_mapsTo (Set.toFinite S) hmaps).1 hinj
    intro y hy
    obtain ⟨y', hy', hy'e⟩ := hsurj.2.2 hy
    rw [← hy'e, Equiv.Perm.coe_inv, Equiv.symm_apply_apply]
    exact hy'
  have hall : ∀ x ∈ HP, ∀ y ∈ S, x y ∈ S := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact hstep x hx
    | one => intro y hy; exact hy
    | mul x z _ _ hx hz => intro y hy; exact hx _ (hz y hy)
    | inv x _ hx => exact hfin x hx
  obtain ⟨k', hk'⟩ := hall g hg _ ⟨k, rfl⟩
  exact ⟨k', hk'.symm⟩

theorem exists_restrict_hom {G : Type*} [Group G] {Y : Type*} [MulAction G Y] {m : ℕ}
    (pts : Fin m → Y) (hinj : Function.Injective pts) (hmaps : ∀ g : G, ∀ k, ∃ k', g • pts k =
    pts k') : ∃ ρ : G →* Equiv.Perm (Fin m), ∀ g k, pts (ρ g k) = g • pts k := by
  classical
  choose f hf using hmaps
  have hmul : ∀ g h k, f (g * h) k = f g (f h k) := fun g h k =>
    hinj (by rw [← hf, ← hf, ← hf, mul_smul])
  have hone : ∀ k, f 1 k = k := fun k => hinj (by rw [← hf, one_smul])
  let ρ : G →* Equiv.Perm (Fin m) :=
    { toFun := fun g =>
        { toFun := f g
          invFun := f g⁻¹
          left_inv := fun k => by rw [← hmul, inv_mul_cancel, hone]
          right_inv := fun k => by rw [← hmul, mul_inv_cancel, hone] }
      map_one' := Equiv.ext hone
      map_mul' := fun g h => Equiv.ext (hmul g h) }
  exact ⟨ρ, fun g k => (hf g k).symm⟩

theorem HP_smul_def (g : HP) (x : X) : g • x = (g : Equiv.Perm X) x := rfl

theorem exists_rhoH :
    ∃ ρ : HP →* Equiv.Perm (Fin 462), ∀ g k, xPt (ρ g k) = g • xPt k :=
  exists_restrict_hom xPt xPt_injective fun g k => HP_maps_xPt g.2 k

@[expose] def rhoH :
    HP →* Equiv.Perm (Fin 462) := Classical.choose exists_rhoH

theorem xPt_rhoH
    (g : HP) (k : Fin 462) : xPt (rhoH g k) = (g : Equiv.Perm X) (xPt k) :=
  Classical.choose_spec exists_rhoH g k

abbrev h1P : HP := ⟨permRegs 1, Subgroup.subset_closure (Set.mem_insert _ _)⟩

abbrev h2P : HP := ⟨permRegs 2, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩

theorem rhoH_h1
    (k : Fin 462) : rhoH h1P k = lIdx1 k := by
  apply xPt_injective
  rw [xPt_rhoH, ← hPerm0_xPt, hPerm_zero]

theorem rhoH_h2
    (k : Fin 462) : rhoH h2P k = lIdx2 k := by
  apply xPt_injective
  rw [xPt_rhoH, ← hPerm1_xPt, hPerm_one]

theorem natArr_natPerm1 (i : Fin 12) : (natArr LocalData.natGen1)[i.val]! = (natPerm1 i).val :=
  prep_natPerm1 i

theorem natArr_natPerm2 (i : Fin 12) : (natArr LocalData.natGen2)[i.val]! = (natPerm2 i).val :=
  prep_natPerm2 i

theorem labPart_lIdx1
    (k : Fin 462) : labPart (lIdx1 k) = natPerm1 • labPart k := by
  apply Subtype.ext
  rw [smul_part_val]
  show maskSet12 labMasks[LocalData.lperm1[k.val]!]! = _
  rw [(label_parts.2.2.2.2.2 k k.isLt).2.2.1, maskSet12_canonMask,
    maskSet12_permMask natArr_natPerm1]
  rfl

theorem labPart_lIdx2
    (k : Fin 462) : labPart (lIdx2 k) = natPerm2 • labPart k := by
  apply Subtype.ext
  rw [smul_part_val]
  show maskSet12 labMasks[LocalData.lperm2[k.val]!]! = _
  rw [(label_parts.2.2.2.2.2 k k.isLt).2.2.2, maskSet12_canonMask,
    maskSet12_permMask natArr_natPerm2]
  rfl

theorem closure_h1P_h2P : Subgroup.closure ({h1P, h2P} : Set HP) = ⊤ := by
  apply Subgroup.map_injective HP.subtype_injective
  rw [MonoidHom.map_closure, Set.image_pair, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rfl

theorem HP_le_stab :
    HP ≤ PH ⊓ fixingSubgroup (Equiv.Perm X) {x0} := by
  intro g hg
  refine Subgroup.mem_inf.2 ⟨HP_le hg, (mem_fixingSubgroup_iff _).2 fun y hy => ?_⟩
  rw [Set.mem_singleton_iff] at hy
  subst hy
  exact HP_fix_zero hg

theorem factorial_twelve_half : Nat.factorial 12 / 2 = 239500800 := by decide

theorem card_HP_le :
    Nat.card HP ≤ Nat.factorial 12 / 2 := by
  have := Subgroup.card_le_of_le HP_le_stab
  rw [card_PH_stab_zero] at this
  rw [factorial_twelve_half]
  exact this

theorem rhoH_injective_card :
    Function.Injective rhoH ∧ Nat.card HP = Nat.factorial 12 / 2 :=
  card_eq_of_partition_labels rhoH h1P h2P closure_h1P_h2P labPart labPart_injective natPerm1
    natPerm2 closure_natPerm (fun k => by rw [rhoH_h1]; exact labPart_lIdx1 k)
    (fun k => by rw [rhoH_h2]; exact labPart_lIdx2 k) card_HP_le

theorem HP_eq_stab :
    HP = PH ⊓ fixingSubgroup (Equiv.Perm X) {x0} :=
  Subgroup.eq_of_le_of_card_ge HP_le_stab (by
    rw [card_PH_stab_zero, rhoH_injective_card.2, factorial_twelve_half])

theorem exists_thetaP :
    ∃ θ : HP ≃* alternatingGroup (Fin 12),
    (θ h1P : Equiv.Perm (Fin 12)) = natPerm1 ∧ (θ h2P : Equiv.Perm (Fin 12)) = natPerm2 ∧
      ∀ (h : HP) (k : Fin 462), labPart (rhoH h k) = (θ h : Equiv.Perm (Fin 12)) • labPart k :=
  (exists_mulEquiv_alt rhoH rhoH_injective_card.1 h1P h2P closure_h1P_h2P labPart
    labPart_injective natPerm1 natPerm2 natPerm1_mem natPerm2_mem
    (fun k => by rw [rhoH_h1]; exact labPart_lIdx1 k)
    (fun k => by rw [rhoH_h2]; exact labPart_lIdx2 k) rhoH_injective_card.2).2

@[expose] def thetaP :
    HP ≃* alternatingGroup (Fin 12) := Classical.choose exists_thetaP

theorem thetaP_h1 :
    (thetaP h1P : Equiv.Perm (Fin 12)) = natPerm1 :=
  (Classical.choose_spec exists_thetaP).1

theorem thetaP_h2 :
    (thetaP h2P : Equiv.Perm (Fin 12)) = natPerm2 :=
  (Classical.choose_spec exists_thetaP).2.1

theorem thetaP_equivariant
    (h : HP) (k : Fin 462) :
    labPart (rhoH h k) = (thetaP h : Equiv.Perm (Fin 12)) • labPart k :=
  (Classical.choose_spec exists_thetaP).2.2 h k

theorem HJ_map : HJ.map permJ = HP := by
  rw [HJ, MonoidHom.map_closure, Set.image_pair, permJ_jRegs, permJ_jRegs]
  rfl

theorem mem_HJ_iff (g : JH) : g ∈ HJ ↔ permJ g ∈ HP := by
  rw [← HJ_map, Subgroup.mem_map_iff_mem permJ_injective]

@[expose] def hjEquiv : HJ ≃* HP :=
  (HJ.equivMapOfInjective permJ permJ_injective).trans (MulEquiv.subgroupCongr HJ_map)

theorem hjEquiv_val
    (h : HJ) : ((hjEquiv h : HP) : Equiv.Perm X) = permJ h := rfl

@[expose] def thetaJ :
    HJ ≃* alternatingGroup (Fin 12) := hjEquiv.trans thetaP

theorem h1J_mem : h1J ∈ HJ := Subgroup.subset_closure (Set.mem_insert _ _)

theorem h2J_mem : h2J ∈ HJ := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem hjEquiv_h1 : hjEquiv ⟨h1J, h1J_mem⟩ = h1P :=
  Subtype.ext ((hjEquiv_val _).trans (permJ_jRegs 1))

theorem hjEquiv_h2 : hjEquiv ⟨h2J, h2J_mem⟩ = h2P :=
  Subtype.ext ((hjEquiv_val _).trans (permJ_jRegs 2))

theorem thetaJ_h1 :
    (thetaJ ⟨h1J, h1J_mem⟩ : Equiv.Perm (Fin 12)) = natPerm1 := by
  rw [thetaJ, MulEquiv.trans_apply, hjEquiv_h1, thetaP_h1]

theorem thetaJ_h2 :
    (thetaJ ⟨h2J, h2J_mem⟩ : Equiv.Perm (Fin 12)) = natPerm2 := by
  rw [thetaJ, MulEquiv.trans_apply, hjEquiv_h2, thetaP_h2]

theorem vL_injective {i j : X} (h : vL i = vL j) : i = j := by
  rw [vL_eq i.isLt, vL_eq j.isLt] at h
  exact Fin.ext (PK_injective _ i.isLt _ j.isLt h)

theorem vL_x0 : vL x0 = fixedVector := by
  rw [vL_eq (show (x0 : ℕ) < nPts by decide), ← PK_zero]

theorem smul_val_aJ
    (y : X) : ((aJ • y : X) : ℕ) = (natTab (hnsData.orbit ()).alpha)[y.val]! :=
  (aJ_smul y).trans ((prep_a0 y).trans (by rw [a0_apply])).symm

theorem smul_val_bJ
    (y : X) : ((bJ • y : X) : ℕ) = (natTab (hnsData.orbit ()).beta)[y.val]! :=
  (bJ_smul y).trans ((prep_a1 y).trans (by rw [a1_apply])).symm

theorem seedWordJ_cons (l : ℕ) (w : List ℕ) :
    seedWordJ (l :: w) = (if l = 1 then aJ else bJ) * seedWordJ w := by
  rw [seedWordJ, List.map_cons, List.prod_cons]
  rfl

theorem seedWordIdx_cons (a0 a1 : Array ℕ) (l : ℕ) (w : List ℕ) (x : ℕ) :
    seedWordIdx a0 a1 (l :: w) x = (if l = 1 then a0 else a1)[seedWordIdx a0 a1 w x]! := rfl

theorem seedWordIdx_eq (w : List ℕ) (hw : ∀ l ∈ w, l = 1 ∨ l = 2) :
    seedWordIdx (natTab (hnsData.orbit ()).alpha) (natTab (hnsData.orbit ()).beta) w 0 =
      ((seedWordJ w • x0 : X) : ℕ) := by
  induction w with
  | nil => rw [seedWordIdx, List.foldr_nil, seedWordJ, List.map_nil, List.prod_nil, one_smul]
  | cons l w ih =>
    have ih' := ih fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')
    rw [seedWordJ_cons, smul_mul_val, seedWordIdx_cons]
    rcases hw l (List.mem_cons_self ..) with rfl | rfl
    · rw [ite_eq_left rfl, ite_eq_left rfl, smul_val_aJ, ih']
    · rw [ite_eq_right (by norm_num), ite_eq_right (by norm_num), smul_val_bJ, ih']

theorem smul_eq_hPerm (j : ℕ) (y : X) : hJ j • y = hPerm j y := by
  rw [← permJ_apply, permJ_hJ]

theorem xVec_eq :
    ∀ k : Fin 462, xVec k = vL (xPt k) := by
  intro k
  obtain ⟨k, hk⟩ := k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [(ctuc_hn_local_alternating_outer_data).2.2.2.2.2.1, ← vL_x0, mat_vL]
      congr 1
      show _ = xsArr[0]!
      rw [local_parts.2.2.2.2.2.1, seedWordIdx_eq _ local_parts_data.1]
    · obtain ⟨hj, he⟩ := local_parts_data.2.2.2.1 k hk0 hk
      rw [(ctuc_hn_local_alternating_outer_data).2.2.2.2.2.2.1 k hk0 hk,
        ih _ hj (by omega), mat_vL, smul_eq_hPerm]
      congr 1
      show _ = xsArr[k]!
      rw [local_parts.2.2.2.2.2.2.1 k hk (by omega)]
      have hrep := hStrong_rep (LocalData.parents[k]!.2 - 1) (by omega)
      rw [hrep ⟨xsArr[LocalData.parents[k]!.1]!, local_parts.2.2.2.2.2.2.2.1 _ (by omega)⟩]
      rfl

noncomputable abbrev fixedVectorJ : Fin hnsData.d → ZMod 5 := fixedVector

noncomputable abbrev vStabJ : Subgroup JH := MulAction.stabilizer JH fixedVectorJ

theorem mem_vStabJ (g : JH) : g ∈ vStabJ ↔ matJ g *ᵥ fixedVector = fixedVector :=
  MulAction.mem_stabilizer_iff

theorem mem_vStabJ_iff_fix (g : JH) : g ∈ vStabJ ↔ g • x0 = x0 := by
  rw [mem_vStabJ, ← vL_x0, mat_vL]
  exact ⟨fun h => vL_injective h, fun h => by rw [h]⟩

theorem permJ_mem (g : JH) : permJ g ∈ PH := (jEquivP g).2

theorem mem_HJ_iff_fix
    (g : JH) : g ∈ HJ ↔ g • x0 = x0 := by
  rw [mem_HJ_iff, HP_eq_stab, Subgroup.mem_inf, mem_fixingSubgroup_iff, ← permJ_apply]
  constructor
  · rintro ⟨-, h⟩
    exact h x0 rfl
  · intro h
    refine ⟨permJ_mem g, fun y hy => ?_⟩
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact h

theorem HJ_eq_vStabJ :
    HJ = vStabJ := by
  ext g
  rw [mem_HJ_iff_fix, mem_vStabJ_iff_fix]

theorem card_HJ :
    Nat.card HJ = 239500800 := by
  rw [Nat.card_congr hjEquiv.toEquiv, rhoH_injective_card.2, factorial_twelve_half]

theorem xVec_injective
    {k k' : Fin 462} (h : xVec k = xVec k') : k = k' := by
  rw [xVec_eq, xVec_eq] at h
  exact xPt_injective (vL_injective h)

theorem h1J_xVec
    (k : Fin 462) : matJ h1J *ᵥ xVec k = xVec (lIdx1 k) := by
  rw [xVec_eq, xVec_eq, ← hJ_zero, mat_vL, smul_eq_hPerm, hPerm0_xPt]

theorem h2J_xVec
    (k : Fin 462) : matJ h2J *ᵥ xVec k = xVec (lIdx2 k) := by
  rw [xVec_eq, xVec_eq, ← hJ_one, mat_vL, smul_eq_hPerm, hPerm1_xPt]

theorem HJ_xVec
    (h : HJ) (k : Fin 462) :
    matJ h *ᵥ xVec k = xVec (rhoH (hjEquiv h) k) := by
  rw [xVec_eq, xVec_eq, mat_vL, xPt_rhoH, hjEquiv_val, permJ_apply]

theorem thetaJ_equivariant
    (h : HJ) (k : Fin 462) :
    labPart (rhoH (hjEquiv h) k) = (thetaJ h : Equiv.Perm (Fin 12)) • labPart k :=
  thetaP_equivariant (hjEquiv h) k

theorem local_point_stabilizer :
    HJ = vStabJ ∧ Nat.card HJ = 239500800 ∧
    (∀ k k' : Fin 462, xVec k = xVec k' → k = k') ∧
    (∀ k : Fin 462, matJ h1J *ᵥ xVec k = xVec LocalData.lperm1[k.val]! ∧
      matJ h2J *ᵥ xVec k = xVec LocalData.lperm2[k.val]!) ∧
    ∃ θ : HJ ≃* alternatingGroup (Fin 12),
      (θ ⟨h1J, h1J_mem⟩ : Equiv.Perm (Fin 12)) = natPerm1 ∧
      (θ ⟨h2J, h2J_mem⟩ : Equiv.Perm (Fin 12)) = natPerm2 ∧
      ∀ (h : HJ) (k : Fin 462), ∃ k' : Fin 462,
        matJ h *ᵥ xVec k = xVec k' ∧ labPart k' = (θ h : Equiv.Perm (Fin 12)) • labPart k :=
  ⟨HJ_eq_vStabJ, card_HJ, fun _ _ h => xVec_injective h,
    fun k => ⟨h1J_xVec k, h2J_xVec k⟩,
    thetaJ, thetaJ_h1, thetaJ_h2, fun h k => ⟨_, HJ_xVec h k, thetaJ_equivariant h k⟩⟩

end CFSG.Sporadic.HNSchreier
