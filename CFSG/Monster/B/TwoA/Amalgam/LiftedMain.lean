module

public import CFSG.Monster.B.TwoA.Amalgam.LiftedNative
public import CFSG.Monster.B.Geometry.ResidueAdj
public import CFSG.Monster.B.TwoA.Amalgam.CoverCount

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
open CFSG.Monster.B.Geometry CFSG.Monster.B.Geometry.ChamberSystem
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.CosetBuilding

variable (X : ChamberSystem (Fin Tag.F4.rank) Chamber)
  (hX : ∀ i c d, X.adj i c d ↔ chamberAdj i c d)

@[expose] def liftParabolic (a : X.Cover (chamberOf 1)) (i : Fin 4) :
    Subgroup (X.LiftPair (chamberOf 1)) :=
  X.liftResidueStab (chamberOf 1) (chamberRho X hX).range (typesOff i) a

@[expose] def liftBorel (a : X.Cover (chamberOf 1)) : Subgroup (X.LiftPair (chamberOf 1)) :=
  X.liftSubgroup (chamberOf 1) (chamberRho X hX).range ⊓
    MulAction.stabilizer (X.LiftPair (chamberOf 1)) a

variable {X hX}

abbrev cIn (S : Subgroup Eam) : Subgroup S := (Subgroup.zpowers cE').subgroupOf S

theorem exists_mulEquiv_quotient_cE' (hkerρ : (chamberRho X hX).ker = Subgroup.zpowers cE')
    {G : Type*} [Group G] (p : G →* X.typeAut) {A : Subgroup G} {S : Subgroup Eam}
    (hA : Set.BijOn p A (S.map (chamberRho X hX))) :
    ∃ e : A ≃* S ⧸ cIn S, ∀ (z : A) (g : S), e z = QuotientGroup.mk g ↔
      p (z : G) = chamberRho X hX (g : Eam) :=
  exists_mulEquiv_quotient_of_bijOn' p (chamberRho X hX) (cIn S)
    (congrArg (fun K => K.subgroupOf S) hkerρ) hA

variable (hconn : X.Connected)
  (hpanel : ∀ (i : Fin Tag.F4.rank) (x : Chamber), ∃ y, y ≠ x ∧ X.adj i x y)
  (hres2 : ∀ J : Set (Fin Tag.F4.rank), J.ncard = 2 → ∀ x,
    X.IsResidueBuilding (coxeterSystem .F4) J x)
  (hres3 : ∀ J : Set (Fin Tag.F4.rank), J.ncard = 3 → ∀ x,
    X.IsResidueBuilding (coxeterSystem .F4) J x)
  (hsize : ∀ (i : Fin Tag.F4.rank) (x : Chamber),
    (X.residue {i} x).encard = if (i : ℕ) < 2 then 3 else 5)
  (hres : ∀ (J : Set (Fin Tag.F4.rank)) (g h : Eam), chamberOf h ∈ X.residue J (chamberOf g) ↔
    ((h * g⁻¹ : Eam) : Dfull) ∈ parJ J)

include hpanel hres2 hres3 hsize in
theorem injOn_coverProj_typesOff {a : X.Cover (chamberOf 1)}
    (ha : X.coverProj (chamberOf 1) a = chamberOf 1) (i : Fin 4) :
    Set.InjOn (X.coverProj (chamberOf 1))
      ((X.universalCover (chamberOf 1)).residue (typesOff i) a) := by
  obtain ⟨δ, hδ, hadj, hpanδ, -⟩ :=
    F4_rank_three_local_building_cover X (chamberOf 1) hpanel hres2 hres3
  have hq : ∀ i A, (panel (coxeterSystem .F4) δ i A).encard = f4q i + 1 := fun i A => by
    rw [hpanδ, hsize, f4q]
    split_ifs <;> rfl
  have : Finite (X.Cover (chamberOf 1)) := (card_eq_finsum_weylWeight hδ hq).1
  have h1 : ((X.universalCover (chamberOf 1)).residue (typesOff i) a).ncard =
      ∑ᶠ w ∈ ((coxeterSystem .F4).parabolic (typesOff i) : Set (WeylGroup .F4)),
        weylWeight (coxeterSystem .F4) f4q w := by
    rw [residue_eq_of_adj_iff hδ hadj]
    exact ncard_residue_eq_finsum hδ hq _ a
  have h2 := finite_ncard_residue_of_isResidueBuilding (q := f4q)
    (hres3 (typesOff i) (ncard_typesOff i) (chamberOf 1)) (fun y _ j _ => by
      rw [hsize, f4q]
      split_ifs <;> rfl)
  refine Set.injOn_of_ncard_image_eq ?_ (Set.toFinite _)
  rw [image_coverProj_residue, ha, h2.2, h1]

include hconn hpanel hres2 hres3 hsize hres in
theorem bijOn_liftResidueStab_resGroup {a : X.Cover (chamberOf 1)}
    (ha : X.coverProj (chamberOf 1) a = chamberOf 1) {K : Set (Fin Tag.F4.rank)} {i : Fin 4}
    (hK : K ⊆ typesOff i) :
    Set.BijOn (X.liftProj (chamberOf 1))
      (X.liftResidueStab (chamberOf 1) (chamberRho X hX).range K a)
      ((resGroup K).map (chamberRho X hX)) := by
  have hiso := isResidueIso_coverProj_of_injOn
    ((injOn_coverProj_typesOff hpanel hres2 hres3 hsize ha i).mono
      ((X.universalCover (chamberOf 1)).residue_mono hK a))
  have h := bijOn_liftResidueStab hconn (chamberRho X hX).range hiso
  rwa [ha, residueSetStab_chamberRho_eq hX (Bam_le_resGroup K) (residue_chamberOf_one hres K)] at h

theorem parJ_pairOff_le (i j : Fin 4) : parJ (pairOff i j) ≤ Pc i ⊓ Pc j := by
  refine sup_le (le_inf (Bam_le_Pc i) (Bam_le_Pc j)) (iSup₂_le fun k hk => le_inf ?_ ?_)
  · exact Qam_le_Pc (fun h => hk.1 (congrArg Fin.val h.symm))
  · exact Qam_le_Pc (fun h => hk.2 (congrArg Fin.val h.symm))

include hpanel hres2 hres3 hsize hres in
theorem Pc_inf_Pc_eq
    (hPi : ∀ i : Fin 4, Pc i = ⨆ (j : Fin 4) (_ : j ≠ i), Qam j) :
    ∀ i j : Fin 4, i ≠ j → Pc i ⊓ Pc j = parJ (pairOff i j) := by
  obtain ⟨δ, hδ, -, hpanδ, -⟩ :=
    F4_rank_three_local_building_cover X (chamberOf 1) hpanel hres2 hres3
  have hq : ∀ i A, (panel (coxeterSystem .F4) δ i A).encard = f4q i + 1 := fun i A => by
    rw [hpanδ, hsize, f4q]
    split_ifs <;> rfl
  have hPm : ∀ m : Fin 4, Nat.card (Pc m) = Nat.card Bam * f4WeightSumOff m := fun m => by
    rw [← parJ_typesOff (hPi m), natCard_parJ_of_isResidueBuilding hres hsize
      (hres3 _ (ncard_typesOff m) _), typesOff, finsum_weylWeight_off hδ hq]
  have hK : ∀ a b : Fin 4, a ≠ b → Nat.card (parJ (pairOff a b)) =
      Nat.card Bam * f4WeightSumIn (fun k => decide ((k : ℕ) ≠ a ∧ (k : ℕ) ≠ b)) :=
    fun a b hab => by
      rw [natCard_parJ_of_isResidueBuilding hres hsize
        (hres2 _ (ncard_pairOff (fun h => hab (Fin.ext h)) a.2 b.2) _), ← setOf_decide_pairOff,
        finsum_weylWeight_in hδ hq]
  have h2 : ((Pc 0).subgroupOf (Pc 1)).index = 3 := by
    obtain ⟨e, -⟩ := exists_equiv_vsharp
    rw [Subgroup.index_eq_card, Nat.card_congr e, natCard_vsharp]
  obtain ⟨-, s1, s2, s3⟩ := f4WeightSumOff_eq
  obtain ⟨t23, t13, t12, t03, t02, t01⟩ := f4WeightSumIn_pairs
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h119, h1071, -, -, -, -⟩ :=
    short_fourth_centralizer_orthogonal_flag
  have h119' : ((Pc 0).subgroupOf (Pc 3)).index = 119 := by
    rw [← Subgroup.inf_subgroupOf_left]
    exact h119
  have h1071' : ((Pc 1).subgroupOf (Pc 3)).index = 1071 := by
    rw [← Subgroup.inf_subgroupOf_left]
    exact h1071
  have hle : ∀ i j : Fin 4, parJ (pairOff i j) ≤ Pc j ⊓ Pc i := fun i j =>
    (parJ_pairOff_le i j).trans (inf_comm (Pc i) (Pc j)).le
  have hB : ∀ {m n : ℕ} (h : m = n), Nat.card Bam * m = Nat.card Bam * n := fun h => by rw [h]
  have e01 : parJ (pairOff 0 1) = Pc 1 ⊓ Pc 0 :=
    eq_inf_of_natCard (N := 3) (s := 105) (hle 0 1) (by norm_num)
      ((hK 0 1 (by decide)).trans (hB t01)) ((hPm 1).trans (hB s1)) h2
  have e02 : parJ (pairOff 0 2) = Pc 2 ⊓ Pc 0 :=
    eq_inf_of_natCard (N := 7) (s := 15) (hle 0 2) (by norm_num)
      ((hK 0 2 (by decide)).trans (hB t02)) ((hPm 2).trans (hB s2)) index_Pc0_subgroupOf
  have e12 : parJ (pairOff 1 2) = Pc 2 ⊓ Pc 1 :=
    eq_inf_of_natCard (N := 7) (s := 15) (hle 1 2) (by norm_num)
      ((hK 1 2 (by decide)).trans (hB t12)) ((hPm 2).trans (hB s2)) index_Pc1_subgroupOf
  have e23 : parJ (pairOff 2 3) = Pc 2 ⊓ Pc 3 :=
    eq_inf_of_natCard (N := 5) (s := 21) (parJ_pairOff_le 2 3) (by norm_num)
      ((hK 2 3 (by decide)).trans (hB t23)) ((hPm 2).trans (hB s2)) index_Pc3_subgroupOf
  have e03 : parJ (pairOff 0 3) = Pc 3 ⊓ Pc 0 :=
    eq_inf_of_natCard (N := 119) (s := 135) (hle 0 3) (by norm_num)
      ((hK 0 3 (by decide)).trans (hB t03)) ((hPm 3).trans (hB s3)) h119'
  have e13 : parJ (pairOff 1 3) = Pc 3 ⊓ Pc 1 :=
    eq_inf_of_natCard (N := 1071) (s := 15) (hle 1 3) (by norm_num)
      ((hK 1 3 (by decide)).trans (hB t13)) ((hPm 3).trans (hB s3)) h1071'
  have hfwd : ∀ i j : Fin 4, parJ (pairOff i j) = Pc j ⊓ Pc i →
      Pc i ⊓ Pc j = parJ (pairOff i j) := fun i j h => (inf_comm (Pc i) (Pc j)).trans h.symm
  have hrev : ∀ i j : Fin 4, parJ (pairOff i j) = Pc j ⊓ Pc i →
      Pc j ⊓ Pc i = parJ (pairOff j i) := fun i j h => h.symm.trans
        (congrArg parJ (pairOff_comm _ _))
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals first
    | exact absurd rfl hij
    | exact hfwd 0 1 e01 | exact hrev 0 1 e01 | exact hfwd 0 2 e02 | exact hrev 0 2 e02
    | exact hfwd 1 2 e12 | exact hrev 1 2 e12 | exact hfwd 0 3 e03 | exact hrev 0 3 e03
    | exact hfwd 1 3 e13 | exact hrev 1 3 e13
    | exact e23.symm
    | exact (inf_comm (Pc 3) (Pc 2)).trans (e23.symm.trans (congrArg parJ (pairOff_comm _ _)))

theorem liftBorel_eq (a : X.Cover (chamberOf 1)) :
    liftBorel X hX a = X.liftResidueStab (chamberOf 1) (chamberRho X hX).range ∅ a := by
  ext z
  rw [mem_liftResidueStab, residue_empty, Set.image_singleton, Set.singleton_eq_singleton_iff,
    liftBorel, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]

theorem ker_chamberRho_le {S : Subgroup Eam} (hS : Bam.subgroupOf Eam ≤ S) :
    (chamberRho X hX).ker ≤ S := by
  intro g hg
  apply hS
  rw [MonoidHom.mem_ker] at hg
  have h := congrArg (fun h : X.typeAut => (h : Equiv.Perm Chamber) (chamberOf 1)) hg
  exact (chamberLeft_chamberOf_one_eq_iff g).mp h

theorem nonempty_ne
    (l : Fin 4) : Nonempty {i : Fin 4 // i ≠ l} := by
  by_cases h : l = 0
  · exact ⟨⟨1, by rw [h]; decide⟩⟩
  · exact ⟨⟨0, Ne.symm h⟩⟩

theorem iInf_Pc_subgroupOf_ne (l : Fin 4) :
    (⨅ x : {i : Fin 4 // i ≠ l}, (Pc x).subgroupOf Eam) = (Qam l).subgroupOf Eam := by
  ext g
  simp only [Subgroup.mem_iInf, Subgroup.mem_subgroupOf, Qam, Subtype.forall]

theorem iInf_Pc_subgroupOf : (⨅ i : Fin 4, (Pc i).subgroupOf Eam) = Bam.subgroupOf Eam := by
  ext g
  simp only [Subgroup.mem_iInf, Subgroup.mem_subgroupOf, Bam]

theorem Bam_le_Pc_subgroupOf (i : Fin 4) : Bam.subgroupOf Eam ≤ (Pc i).subgroupOf Eam :=
  Subgroup.subgroupOf_mono Eam (Bam_le_Pc i)

variable (hPi : ∀ i : Fin 4, Pc i = ⨆ (j : Fin 4) (_ : j ≠ i), Qam j)

include hPi in
theorem resGroup_typesOff (i : Fin 4) : resGroup (typesOff i) = (Pc i).subgroupOf Eam := by
  rw [resGroup, parJ_typesOff (hPi i)]

include hres hPi in
theorem residueSetStab_typesOff (i : Fin 4) :
    X.residueSetStab (chamberRho X hX).range (typesOff i) (chamberOf 1) =
      ((Pc i).subgroupOf Eam).map (chamberRho X hX) := by
  rw [residueSetStab_chamberRho_eq hX (Bam_le_resGroup _) (residue_chamberOf_one hres _),
    resGroup_typesOff hPi]

include hpanel hres2 hres3 hsize hres hPi in
theorem residueIso_typesOff_of {a : X.Cover (chamberOf 1)}
    (ha : X.coverProj (chamberOf 1) a = chamberOf 1) (i : Fin 4) :
    IsResidueIso (X.universalCover (chamberOf 1)) X (X.coverProj (chamberOf 1)) (typesOff i) a ∧
      X.residue (typesOff i) (chamberOf 1) = chamberOf '' ((Pc i).subgroupOf Eam : Set Eam) := by
  refine ⟨isResidueIso_coverProj_of_injOn (injOn_coverProj_typesOff hpanel hres2 hres3 hsize ha i),
    ?_⟩
  rw [residue_chamberOf_one hres, resGroup_typesOff hPi]

include hconn hpanel hres2 hres3 hsize hres hPi in
theorem bijOn_liftParabolic_of {a : X.Cover (chamberOf 1)}
    (ha : X.coverProj (chamberOf 1) a = chamberOf 1) (i : Fin 4) :
    Set.BijOn (X.liftProj (chamberOf 1)) (liftParabolic X hX a i)
      (((Pc i).subgroupOf Eam).map (chamberRho X hX)) := by
  have h := bijOn_liftResidueStab_resGroup (hX := hX) hconn hpanel hres2 hres3 hsize hres ha
    (subset_refl (typesOff i))
  rw [resGroup_typesOff hPi] at h
  exact h

include hconn hpanel hres2 hres3 hsize hres hPi in
theorem liftParabolic_mulEquiv_of
    (hker : ∀ g : Eam, (∀ ch : Chamber, chamberMul ch g = ch) ↔ (g : Dfull) ∈ Subgroup.zpowers cQ)
    {a : X.Cover (chamberOf 1)} (ha : X.coverProj (chamberOf 1) a = chamberOf 1) (i : Fin 4) :
    ∃ e : liftParabolic X hX a i ≃* (Pc i).subgroupOf Eam ⧸ cIn ((Pc i).subgroupOf Eam),
      ∀ z g, e z = QuotientGroup.mk g ↔
        X.liftProj (chamberOf 1) (z : X.LiftPair (chamberOf 1)) = chamberRho X hX (g : Eam) :=
  exists_mulEquiv_quotient_cE' (by rw [ker_chamberRho, ker_chamberLeft_eq hker])
    (X.liftProj (chamberOf 1)) (bijOn_liftParabolic_of hconn hpanel hres2 hres3 hsize hres hPi ha i)

include hconn hpanel hres2 hres3 hsize hres in
theorem liftBorel_mulEquiv_of
    (hker : ∀ g : Eam, (∀ ch : Chamber, chamberMul ch g = ch) ↔ (g : Dfull) ∈ Subgroup.zpowers cQ)
    {a : X.Cover (chamberOf 1)} (ha : X.coverProj (chamberOf 1) a = chamberOf 1) :
    ∃ e : liftBorel X hX a ≃* Bam.subgroupOf Eam ⧸ cIn (Bam.subgroupOf Eam),
      ∀ z g, e z = QuotientGroup.mk g ↔
        X.liftProj (chamberOf 1) (z : X.LiftPair (chamberOf 1)) = chamberRho X hX (g : Eam) := by
  have h := bijOn_liftResidueStab_resGroup (hX := hX) hconn hpanel hres2 hres3 hsize hres ha
    (i := 0) (Set.empty_subset _)
  rw [resGroup, parJ_empty, ← liftBorel_eq] at h
  exact exists_mulEquiv_quotient_cE' (by rw [ker_chamberRho, ker_chamberLeft_eq hker])
    (X.liftProj (chamberOf 1)) h

include hconn hpanel hres2 hres3 hsize hres hPi in
theorem iInf_liftParabolic_eq_of
    (hker : ∀ g : Eam, (∀ ch : Chamber, chamberMul ch g = ch) ↔ (g : Dfull) ∈ Subgroup.zpowers cQ)
    {a : X.Cover (chamberOf 1)} (ha : X.coverProj (chamberOf 1) a = chamberOf 1) :
    (⨅ i : Fin 4, liftParabolic X hX a i) = liftBorel X hX a := by
  have hkerρ : (chamberRho X hX).ker = Subgroup.zpowers cE' := by
    rw [ker_chamberRho, ker_chamberLeft_eq hker]
  rw [liftBorel_eq]
  refine iInf_liftResidueStab_eq hconn _ (fun i => Set.empty_subset _)
    (fun i => injOn_coverProj_typesOff hpanel hres2 hres3 hsize ha i) ?_
  rw [ha]
  simp only [residueSetStab_typesOff (hX := hX) hres hPi]
  rw [← iInf_map_chamberRho hX (fun i : Fin 4 => (Pc i).subgroupOf Eam)
      (fun i => ker_chamberRho_le (Bam_le_Pc_subgroupOf i)),
    iInf_Pc_subgroupOf, residueSetStab_chamberRho_eq hX (Bam_le_resGroup _)
      (residue_chamberOf_one hres _), resGroup, parJ_empty]

include hconn hpanel hres2 hres3 hsize hres hPi in
theorem liftParabolic_inf_mulEquiv_of
    (hker : ∀ g : Eam, (∀ ch : Chamber, chamberMul ch g = ch) ↔ (g : Dfull) ∈ Subgroup.zpowers cQ)
    {a : X.Cover (chamberOf 1)} (ha : X.coverProj (chamberOf 1) a = chamberOf 1) {i j : Fin 4}
    (hij : i ≠ j) :
    ∃ e : ↥(liftParabolic X hX a i ⊓ liftParabolic X hX a j) ≃*
        (Pc i ⊓ Pc j).subgroupOf Eam ⧸ cIn ((Pc i ⊓ Pc j).subgroupOf Eam),
      ∀ z g, e z = QuotientGroup.mk g ↔
        X.liftProj (chamberOf 1) (z : X.LiftPair (chamberOf 1)) = chamberRho X hX (g : Eam) := by
  have hkerρ : (chamberRho X hX).ker = Subgroup.zpowers cE' := by
    rw [ker_chamberRho, ker_chamberLeft_eq hker]
  have hpair : resGroup (pairOff i j) = (Pc i ⊓ Pc j).subgroupOf Eam := by
    rw [resGroup, ← Pc_inf_Pc_eq hpanel hres2 hres3 hsize hres hPi i j hij]
  have hpair' : (Pc i ⊓ Pc j).subgroupOf Eam = (Pc i).subgroupOf Eam ⊓ (Pc j).subgroupOf Eam := by
    ext g
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  have hint : liftParabolic X hX a i ⊓ liftParabolic X hX a j =
      X.liftResidueStab (chamberOf 1) (chamberRho X hX).range (pairOff i j) a := by
    have h := iInf_liftResidueStab_eq (ι := Bool) hconn (chamberRho X hX).range
      (J := fun b => cond b (typesOff i) (typesOff j)) (K := pairOff i j)
      (fun b => by
        cases b
        · exact pairOff_subset_typesOff_right i j
        · exact pairOff_subset_typesOff_left i j)
      (fun b => by cases b <;> exact injOn_coverProj_typesOff hpanel hres2 hres3 hsize ha _) (by
        rw [ha, iInf_bool_eq]
        simp only [Bool.cond_true, Bool.cond_false]
        rw [residueSetStab_typesOff (hX := hX) hres hPi,
          residueSetStab_typesOff (hX := hX) hres hPi,
          ← inf_map_chamberRho hX (ker_chamberRho_le (Bam_le_Pc_subgroupOf i))
            (ker_chamberRho_le (Bam_le_Pc_subgroupOf j)),
          residueSetStab_chamberRho_eq hX (Bam_le_resGroup _) (residue_chamberOf_one hres _), hpair,
          hpair'])
    rw [iInf_bool_eq] at h
    exact h
  have h := bijOn_liftResidueStab_resGroup (hX := hX) hconn hpanel hres2 hres3 hsize hres ha
    (pairOff_subset_typesOff_left i j)
  rw [← hint, hpair] at h
  exact exists_mulEquiv_quotient_cE' hkerρ (X.liftProj (chamberOf 1)) h

include hconn hpanel hres2 hres3 hsize hres hPi in
theorem liftParabolic_iInf_ne_mulEquiv_of
    (hker : ∀ g : Eam, (∀ ch : Chamber, chamberMul ch g = ch) ↔ (g : Dfull) ∈ Subgroup.zpowers cQ)
    {a : X.Cover (chamberOf 1)} (ha : X.coverProj (chamberOf 1) a = chamberOf 1) (l : Fin 4) :
    ∃ e : ↥(⨅ (i : Fin 4) (_ : i ≠ l), liftParabolic X hX a i) ≃*
        (Qam l).subgroupOf Eam ⧸ cIn ((Qam l).subgroupOf Eam),
      ∀ z g, e z = QuotientGroup.mk g ↔
        X.liftProj (chamberOf 1) (z : X.LiftPair (chamberOf 1)) = chamberRho X hX (g : Eam) := by
  have hkerρ : (chamberRho X hX).ker = Subgroup.zpowers cE' := by
    rw [ker_chamberRho, ker_chamberLeft_eq hker]
  have := nonempty_ne l
  have hKsub : ∀ x : {i : Fin 4 // i ≠ l}, {k : Fin Tag.F4.rank | (k : ℕ) = (l : ℕ)} ⊆
      typesOff x := fun x k hk hkx => x.2 (Fin.ext (hkx.symm.trans hk))
  have hint : (⨅ (i : Fin 4) (_ : i ≠ l), liftParabolic X hX a i) =
      X.liftResidueStab (chamberOf 1) (chamberRho X hX).range
        {k : Fin Tag.F4.rank | (k : ℕ) = (l : ℕ)} a := by
    rw [iInf_subtype']
    refine iInf_liftResidueStab_eq hconn _ hKsub
      (fun x => injOn_coverProj_typesOff hpanel hres2 hres3 hsize ha x) ?_
    rw [ha]
    simp only [residueSetStab_typesOff (hX := hX) hres hPi]
    rw [← iInf_map_chamberRho hX (fun x : {i : Fin 4 // i ≠ l} => (Pc x).subgroupOf Eam)
        (fun x => ker_chamberRho_le (Bam_le_Pc_subgroupOf x)),
      iInf_Pc_subgroupOf_ne, residueSetStab_chamberRho_eq hX (Bam_le_resGroup _)
        (residue_chamberOf_one hres _), resGroup, parJ_eq_Qam]
  obtain ⟨x₀⟩ := this
  have h := bijOn_liftResidueStab_resGroup (hX := hX) hconn hpanel hres2 hres3 hsize hres ha
    (hKsub x₀)
  rw [← hint, resGroup, parJ_eq_Qam] at h
  exact exists_mulEquiv_quotient_cE' hkerρ (X.liftProj (chamberOf 1)) h

theorem exists_flagQuotient_liftParabolic (hkerρ : (chamberRho X hX).ker = Subgroup.zpowers cE')
    {a : X.Cover (chamberOf 1)} (ha : X.coverProj (chamberOf 1) a = chamberOf 1) {i : Fin 4}
    (hinj : Set.InjOn (X.coverProj (chamberOf 1))
      ((X.universalCover (chamberOf 1)).residue (typesOff i) a))
    {P N : Subgroup Dfull} (hPE : P ≤ Eam) (hNP : N ≤ P) (hNB : N ≤ Bam) (hcN : cQ ∈ N)
    (hA : Set.BijOn (X.liftProj (chamberOf 1)) (liftParabolic X hX a i)
      ((P.subgroupOf Eam).map (chamberRho X hX)))
    {M : Type*} [Group M] (φ : P →* M) (hφ : Function.Surjective φ)
    (hφker : ∀ g : P, φ g = 1 ↔ (g : Dfull) ∈ N) :
    ∃ θ : liftParabolic X hX a i →* M, Function.Surjective θ ∧
      (∀ (z : liftParabolic X hX a i) (g : P),
        X.liftProj (chamberOf 1) (z : X.LiftPair (chamberOf 1)) =
          chamberRho X hX (Subgroup.inclusion hPE g) → θ z = φ g) ∧
      (∀ z, θ z = 1 ↔ ∃ n : Eam, (n : Dfull) ∈ N ∧
        X.liftProj (chamberOf 1) (z : X.LiftPair (chamberOf 1)) = chamberRho X hX n) ∧
      (∀ z, θ z = 1 → (z : X.LiftPair (chamberOf 1)) ∈ liftBorel X hX a) ∧
      ∃ e : ↥(θ.ker.map (liftParabolic X hX a i).subtype) ≃*
          N.subgroupOf Eam ⧸ cIn (N.subgroupOf Eam),
        ∀ z g, e z = QuotientGroup.mk g ↔
          X.liftProj (chamberOf 1) (z : X.LiftPair (chamberOf 1)) = chamberRho X hX (g : Eam) := by
  have hS : ∀ x : Eam, x ∈ P.subgroupOf Eam ↔ ∃ g : P, Subgroup.inclusion hPE g = x := by
    intro x
    constructor
    · intro hx
      exact ⟨⟨x, Subgroup.mem_subgroupOf.mp hx⟩, rfl⟩
    · rintro ⟨g, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr g.2
  have hker : ∀ g : P, chamberRho X hX (Subgroup.inclusion hPE g) = 1 → φ g = 1 := by
    intro g hg
    have h1 : Subgroup.inclusion hPE g ∈ Subgroup.zpowers cE' := by
      rw [← hkerρ]
      exact MonoidHom.mem_ker.mpr hg
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
    have h2 : (g : Dfull) = cQ ^ k := by
      have := congrArg Subtype.val hk
      rw [Subgroup.coe_zpow] at this
      exact this.symm
    refine (hφker g).mpr ?_
    rw [h2]
    exact zpow_mem hcN k
  have h0 := exists_quotient_hom_of_bijOn (X.liftProj (chamberOf 1)) (chamberRho X hX)
    (Subgroup.inclusion hPE) hS hA φ hφ hker
  obtain ⟨θ, hθs, hθv, hθk⟩ := h0
  have hk : ∀ z, θ z = 1 ↔ ∃ n : Eam, (n : Dfull) ∈ N ∧
      X.liftProj (chamberOf 1) (z : X.LiftPair (chamberOf 1)) = chamberRho X hX n := by
    intro z
    refine (hθk z).trans ⟨fun ⟨g, hg, he⟩ => ⟨Subgroup.inclusion hPE g, (hφker g).mp hg, he⟩,
      fun ⟨n, hn, he⟩ => ⟨⟨n, hNP hn⟩, (hφker _).mpr hn, he⟩⟩
  have hB : ∀ z, θ z = 1 → (z : X.LiftPair (chamberOf 1)) ∈ liftBorel X hX a := by
    intro z hz
    obtain ⟨n, hn, he⟩ := (hk z).mp hz
    have hfix := (smul_eq_self_iff_of_mem_liftResidueStab hinj z.2).mpr (by
      rw [he, ha]
      exact (chamberLeft_chamberOf_one_eq_iff n).mpr (Subgroup.mem_subgroupOf.mpr (hNB hn)))
    exact ⟨(Subgroup.mem_inf.mp z.2).1, hfix⟩
  have hbij : Set.BijOn (X.liftProj (chamberOf 1)) (θ.ker.map (liftParabolic X hX a i).subtype)
      ((N.subgroupOf Eam).map (chamberRho X hX)) := by
    refine ⟨fun z hz => ?_, fun z hz w hw hzw => ?_, fun h hh => ?_⟩
    · have hz' : ∃ y ∈ θ.ker, (liftParabolic X hX a i).subtype y = z := Subgroup.mem_map.mp hz
      obtain ⟨y, hy, rfl⟩ := hz'
      have hy' : ∃ n : Eam, (n : Dfull) ∈ N ∧
          X.liftProj (chamberOf 1) (y : X.LiftPair (chamberOf 1)) = chamberRho X hX n :=
        (hk y).mp (MonoidHom.mem_ker.mp hy)
      obtain ⟨n, hn, he⟩ := hy'
      exact Subgroup.mem_map.mpr ⟨n, Subgroup.mem_subgroupOf.mpr hn, he.symm⟩
    · have hz' : ∃ y ∈ θ.ker, (liftParabolic X hX a i).subtype y = z := Subgroup.mem_map.mp hz
      have hw' : ∃ y ∈ θ.ker, (liftParabolic X hX a i).subtype y = w := Subgroup.mem_map.mp hw
      obtain ⟨y, -, rfl⟩ := hz'
      obtain ⟨y', -, rfl⟩ := hw'
      exact hA.injOn y.2 y'.2 hzw
    · have hh' : ∃ n ∈ N.subgroupOf Eam, chamberRho X hX n = h := Subgroup.mem_map.mp hh
      obtain ⟨n, hn, rfl⟩ := hh'
      have hn' : (n : Dfull) ∈ N := Subgroup.mem_subgroupOf.mp hn
      have hz' : ∃ z, z ∈ (liftParabolic X hX a i : Set (X.LiftPair (chamberOf 1))) ∧
          X.liftProj (chamberOf 1) z = chamberRho X hX n :=
        (Set.mem_image _ _ _).mp
          (hA.surjOn (Subgroup.mem_map.mpr ⟨n, Subgroup.mem_subgroupOf.mpr (hNP hn'), rfl⟩))
      obtain ⟨z, hz, hze⟩ := hz'
      exact (Set.mem_image _ _ _).mpr ⟨z, Subgroup.mem_map.mpr ⟨⟨z, hz⟩,
        MonoidHom.mem_ker.mpr ((hk ⟨z, hz⟩).mpr ⟨n, hn', hze⟩), rfl⟩, hze⟩
  exact ⟨θ, hθs, hθv, hk, hB, exists_mulEquiv_quotient_cE' (hX := hX) hkerρ
    (X.liftProj (chamberOf 1)) hbij⟩

include hconn hpanel hres2 hres3 hsize hres hPi in
theorem exists_unitaryQuotient_of
    (hker : ∀ g : Eam, (∀ ch : Chamber, chamberMul ch g = ch) ↔ (g : Dfull) ∈ Subgroup.zpowers cQ)
    {a : X.Cover (chamberOf 1)} (ha : X.coverProj (chamberOf 1) a = chamberOf 1) :
    ∃ θ : liftParabolic X hX a 0 →* Unitary.SigmaU6, Function.Surjective θ ∧
      (∀ (z : liftParabolic X hX a 0) (g : Pc 0),
        X.liftProj (chamberOf 1) (z : X.LiftPair (chamberOf 1)) =
          chamberRho X hX (Subgroup.inclusion (Pc_le_Eam 0) g) → θ z = rhoP1 g) ∧
      (∀ z, θ z = 1 ↔ ∃ n : Eam, (n : Dfull) ∈ Nc 0 ∧
        X.liftProj (chamberOf 1) (z : X.LiftPair (chamberOf 1)) = chamberRho X hX n) ∧
      (∀ z, θ z = 1 → (z : X.LiftPair (chamberOf 1)) ∈ liftBorel X hX a) ∧
      ∃ e : ↥(θ.ker.map (liftParabolic X hX a 0).subtype) ≃*
          (Nc 0).subgroupOf Eam ⧸ cIn ((Nc 0).subgroupOf Eam),
        ∀ z g, e z = QuotientGroup.mk g ↔
          X.liftProj (chamberOf 1) (z : X.LiftPair (chamberOf 1)) = chamberRho X hX (g : Eam) :=
  exists_flagQuotient_liftParabolic (P := Pc 0) (N := Nc 0)
    (by rw [ker_chamberRho, ker_chamberLeft_eq hker]) ha
    (injOn_coverProj_typesOff hpanel hres2 hres3 hsize ha 0) (Pc_le_Eam 0) (Nc_le_Pc 0 0)
    (Nc_le_Bam 0) (Nc_zero ▸ cQ_mem_N1)
    (bijOn_liftParabolic_of hconn hpanel hres2 hres3 hsize hres hPi ha 0) rhoP1
    rhoP1_surjective fun g => by rw [← MonoidHom.mem_ker, ker_rhoP1, Subgroup.mem_subgroupOf]

include hconn hpanel hres2 hres3 hsize hres hPi in
theorem exists_orthogonalQuotient_of
    (hker : ∀ g : Eam, (∀ ch : Chamber, chamberMul ch g = ch) ↔ (g : Dfull) ∈ Subgroup.zpowers cQ)
    {a : X.Cover (chamberOf 1)} (ha : X.coverProj (chamberOf 1) a = chamberOf 1) :
    ∃ θ : liftParabolic X hX a 3 →* TauCeti.QuadraticMap.orthogonalGroup qForm,
      Function.Surjective θ ∧
      (∀ (z : liftParabolic X hX a 3) (g : P4),
        X.liftProj (chamberOf 1) (z : X.LiftPair (chamberOf 1)) =
          chamberRho X hX (Subgroup.inclusion (Pc_le_Eam 3 : P4 ≤ Eam) g) → θ z = p4Proj g) ∧
      (∀ z, θ z = 1 ↔ ∃ n : Eam, (n : Dfull) ∈ Lgrp ∧
        X.liftProj (chamberOf 1) (z : X.LiftPair (chamberOf 1)) = chamberRho X hX n) ∧
      (∀ z, θ z = 1 → (z : X.LiftPair (chamberOf 1)) ∈ liftBorel X hX a) ∧
      ∃ e : ↥(θ.ker.map (liftParabolic X hX a 3).subtype) ≃*
          Lgrp.subgroupOf Eam ⧸ cIn (Lgrp.subgroupOf Eam),
        ∀ z g, e z = QuotientGroup.mk g ↔
          X.liftProj (chamberOf 1) (z : X.LiftPair (chamberOf 1)) = chamberRho X hX (g : Eam) :=
  exists_flagQuotient_liftParabolic (P := P4) (N := Lgrp)
    (by rw [ker_chamberRho, ker_chamberLeft_eq hker]) ha
    (injOn_coverProj_typesOff hpanel hres2 hres3 hsize ha 3) (Pc_le_Eam 3 : P4 ≤ Eam)
    (Nc_three ▸ Nc_le_Pc 3 3 : Lgrp ≤ P4) (Nc_three ▸ Nc_le_Bam 3) cQ_mem_centralizer_A8
    (bijOn_liftParabolic_of hconn hpanel hres2 hres3 hsize hres hPi ha 3) p4Proj
    p4Proj_surjective fun g => by rw [← MonoidHom.mem_ker, ker_p4Proj, Subgroup.mem_subgroupOf]

include hconn hpanel hres2 hres3 hsize hres hPi in
theorem lifted_parabolic_stabilizers_of
    (hker : ∀ g : Eam, (∀ ch : Chamber, chamberMul ch g = ch) ↔ (g : Dfull) ∈ Subgroup.zpowers cQ)
    (a : X.Cover (chamberOf 1)) (ha : X.coverProj (chamberOf 1) a = chamberOf 1) :
    (∀ i : Fin 4, IsResidueIso (X.universalCover (chamberOf 1)) X (X.coverProj (chamberOf 1))
        (typesOff i) a ∧
      X.residue (typesOff i) (chamberOf 1) = chamberOf '' ((Pc i).subgroupOf Eam : Set Eam)) ∧
    (∀ i : Fin 4, ∃ e : liftParabolic X hX a i ≃*
        (Pc i).subgroupOf Eam ⧸ cIn ((Pc i).subgroupOf Eam),
      ∀ z g, e z = QuotientGroup.mk g ↔
        X.liftProj (chamberOf 1) (z : X.LiftPair (chamberOf 1)) = chamberRho X hX (g : Eam)) ∧
    (∃ e : liftBorel X hX a ≃* Bam.subgroupOf Eam ⧸ cIn (Bam.subgroupOf Eam),
      ∀ z g, e z = QuotientGroup.mk g ↔
        X.liftProj (chamberOf 1) (z : X.LiftPair (chamberOf 1)) = chamberRho X hX (g : Eam)) ∧
    (∀ i j : Fin 4, i ≠ j →
      ∃ e : ↥(liftParabolic X hX a i ⊓ liftParabolic X hX a j) ≃*
          (Pc i ⊓ Pc j).subgroupOf Eam ⧸ cIn ((Pc i ⊓ Pc j).subgroupOf Eam),
        ∀ z g, e z = QuotientGroup.mk g ↔
          X.liftProj (chamberOf 1) (z : X.LiftPair (chamberOf 1)) = chamberRho X hX (g : Eam)) ∧
    (∀ l : Fin 4,
      ∃ e : ↥(⨅ (i : Fin 4) (_ : i ≠ l), liftParabolic X hX a i) ≃*
          (Qam l).subgroupOf Eam ⧸ cIn ((Qam l).subgroupOf Eam),
        ∀ z g, e z = QuotientGroup.mk g ↔
          X.liftProj (chamberOf 1) (z : X.LiftPair (chamberOf 1)) = chamberRho X hX (g : Eam)) ∧
    (⨅ i : Fin 4, liftParabolic X hX a i) = liftBorel X hX a ∧
    (∃ θ : liftParabolic X hX a 0 →* Unitary.SigmaU6, Function.Surjective θ ∧
      (∀ (z : liftParabolic X hX a 0) (g : Pc 0),
        X.liftProj (chamberOf 1) (z : X.LiftPair (chamberOf 1)) =
          chamberRho X hX (Subgroup.inclusion (Pc_le_Eam 0) g) → θ z = rhoP1 g) ∧
      (∀ z, θ z = 1 ↔ ∃ n : Eam, (n : Dfull) ∈ Nc 0 ∧
        X.liftProj (chamberOf 1) (z : X.LiftPair (chamberOf 1)) = chamberRho X hX n) ∧
      (∀ z, θ z = 1 → (z : X.LiftPair (chamberOf 1)) ∈ liftBorel X hX a) ∧
      ∃ e : ↥(θ.ker.map (liftParabolic X hX a 0).subtype) ≃*
          (Nc 0).subgroupOf Eam ⧸ cIn ((Nc 0).subgroupOf Eam),
        ∀ z g, e z = QuotientGroup.mk g ↔
          X.liftProj (chamberOf 1) (z : X.LiftPair (chamberOf 1)) = chamberRho X hX (g : Eam)) ∧
    (∃ θ : liftParabolic X hX a 3 →* TauCeti.QuadraticMap.orthogonalGroup qForm,
      Function.Surjective θ ∧
      (∀ (z : liftParabolic X hX a 3) (g : P4),
        X.liftProj (chamberOf 1) (z : X.LiftPair (chamberOf 1)) =
          chamberRho X hX (Subgroup.inclusion (Pc_le_Eam 3 : P4 ≤ Eam) g) → θ z = p4Proj g) ∧
      (∀ z, θ z = 1 ↔ ∃ n : Eam, (n : Dfull) ∈ Lgrp ∧
        X.liftProj (chamberOf 1) (z : X.LiftPair (chamberOf 1)) = chamberRho X hX n) ∧
      (∀ z, θ z = 1 → (z : X.LiftPair (chamberOf 1)) ∈ liftBorel X hX a) ∧
      ∃ e : ↥(θ.ker.map (liftParabolic X hX a 3).subtype) ≃*
          Lgrp.subgroupOf Eam ⧸ cIn (Lgrp.subgroupOf Eam),
        ∀ z g, e z = QuotientGroup.mk g ↔
          X.liftProj (chamberOf 1) (z : X.LiftPair (chamberOf 1)) = chamberRho X hX (g : Eam)) :=
  ⟨residueIso_typesOff_of hpanel hres2 hres3 hsize hres hPi ha,
    liftParabolic_mulEquiv_of hconn hpanel hres2 hres3 hsize hres hPi hker ha,
    liftBorel_mulEquiv_of hconn hpanel hres2 hres3 hsize hres hker ha,
    fun _ _ hij =>
      liftParabolic_inf_mulEquiv_of hconn hpanel hres2 hres3 hsize hres hPi hker ha hij,
    liftParabolic_iInf_ne_mulEquiv_of hconn hpanel hres2 hres3 hsize hres hPi hker ha,
    iInf_liftParabolic_eq_of hconn hpanel hres2 hres3 hsize hres hPi hker ha,
    exists_unitaryQuotient_of hconn hpanel hres2 hres3 hsize hres hPi hker ha,
    exists_orthogonalQuotient_of hconn hpanel hres2 hres3 hsize hres hPi hker ha⟩

end CFSG.Monster.B.TwoA.Amalgam
