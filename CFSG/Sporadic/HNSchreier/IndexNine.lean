module

public import CFSG.Sporadic.HNSchreier.IndexNineInputs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SporadicPermutesPackage
public import CFSG.Mathlib.Decide.Bounded
public import CFSG.Permutation.UnitaryThreeRecognition.Torus
public import CFSG.GroupTheory.SylowTwoEquiv
public import CFSG.GroupTheory.Frattini.PSubgroupLift
public import CFSG.GH74.SmallRanks.AltM11
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalFamily
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinearStrong
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.Hyp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SporadicPermutesCover
public import CFSG.Permutation.AlternatingAutomorphism
public import CFSG.Permutation.UnitaryThreeRecognition.Counting
public import CFSG.Permutation.UnitaryThreeRecognition.Fixed
public import CFSG.Quasithin.Background.A1cA132Action
public import CFSG.Quasithin.Background.A1cA133Three
public import CFSG.Quasithin.Background.B216Quotient
public import CFSG.Quasithin.Background.E3
public import CFSG.Quasithin.Background.E3OffenderB
public import CFSG.Quasithin.Background.E3Uniq
public import CFSG.Quasithin.Background.E4Solv
public import CFSG.Quasithin.Background.F6Amalgams
public import CFSG.Quasithin.Background.F6SolvableQuotient
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.HFF
public import CFSG.Quasithin.Background.HPairBridge
public import CFSG.Quasithin.Background.HSL3Inner
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4OutBase
public import CFSG.Quasithin.EmptyFaithful.S14110
public import CFSG.Quasithin.EmptyFaithful.S14117
public import CFSG.Quasithin.EmptyFaithful.S143Pre
public import CFSG.Quasithin.EmptyFaithful.S153Baum
public import CFSG.Quasithin.EmptyFaithful.S153Nine
public import CFSG.Quasithin.EmptyFaithful.T1531Close2
public import CFSG.Quasithin.EmptyFaithful.T1531In66b
public import CFSG.Quasithin.EmptyFaithfulMultiple.InputB19Proof
public import CFSG.Quasithin.Vol2.Ch1Faithful
public import CFSG.Quasithin.Vol2.Ch4Sec1Lem415
public import CFSG.Quasithin.Vol2.Ch4Sec4Lem445
public import CFSG.Sporadic.Schreier.J4SCommGenBase1
public import CFSG.Sporadic.Schreier.J4SLocalNodes

public section

namespace CFSG.Sporadic.HNSchreier

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.SideF4
open CFSG.ONSchreier CFSG.Sporadic.HNOddCore CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open scoped CFSG.Decide.Bounded commutatorElement

@[expose] def hnNineFinsetAct (g : Equiv.Perm (Fin 10)) (s : Finset (Fin 10)) :
    Finset (Fin 10) :=
  s.map g.toEmbedding

noncomputable scoped instance hnNinePermFinsetMulAction :
    MulAction (Equiv.Perm (Fin 10)) (Finset (Fin 10)) where
  smul := hnNineFinsetAct
  one_smul s := by
    change s.map (1 : Equiv.Perm (Fin 10)).toEmbedding = s
    rw [Equiv.Perm.one_def, Equiv.refl_toEmbedding, Finset.map_refl]
  mul_smul a b s := by
    change s.map ((a * b : Equiv.Perm (Fin 10))).toEmbedding =
      (s.map b.toEmbedding).map a.toEmbedding
    rw [Equiv.Perm.mul_def, Equiv.trans_toEmbedding, Finset.map_map]

open scoped CFSG.Sporadic.HNSchreier

noncomputable scoped instance hnNinePhiQFinsetMulAction :
    MulAction phiQ.range (Finset (Fin 10)) where
  smul g s := (g : Equiv.Perm (Fin 10)) • s
  one_smul s := one_smul (Equiv.Perm (Fin 10)) s
  mul_smul a b s := mul_smul (a : Equiv.Perm (Fin 10)) (b : Equiv.Perm (Fin 10)) s

theorem hnNineUbar_isSylow :
    CFSG.QuasithinUnique.IsSylowTwoOf hnNineUbar ⊤ := by
  refine ⟨le_top, ?_, ?_⟩
  · exact IsPGroup.of_card (n := 5) (by rw [hnNineUbar_card]; norm_num)
  · have hsub : Nat.card (hnNineUbar.subgroupOf ⊤) = Nat.card hnNineUbar :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_top : hnNineUbar ≤ ⊤)).toEquiv
    have hmul := Subgroup.card_mul_index (H := hnNineUbar.subgroupOf ⊤)
    rw [hsub, hnNineUbar_card, Subgroup.card_top, card_range_phi] at hmul
    have hindex : (hnNineUbar.subgroupOf ⊤).index = 225 := by omega
    rw [hindex]
    norm_num


theorem hnNineX0_card : hnNineX0.card = 2 := by decide

theorem hnNineA_fix : hnNineX0.map hnNineA.toEmbedding = hnNineX0 := by
  change ({4, 9} : Finset (Fin 10)).map hnNineA.toEmbedding = {4, 9}
  ext x
  fin_cases x <;> decide

theorem hnNineB_fix : hnNineX0.map hnNineB.toEmbedding = hnNineX0 := by
  change ({4, 9} : Finset (Fin 10)).map hnNineB.toEmbedding = {4, 9}
  ext x
  fin_cases x <;> decide

theorem hnNineC_fix : hnNineX0.map hnNineC.toEmbedding = hnNineX0 := by
  change ({4, 9} : Finset (Fin 10)).map hnNineC.toEmbedding = {4, 9}
  ext x
  fin_cases x <;> decide

theorem hnNineD_fix : hnNineX0.map hnNineD.toEmbedding = hnNineX0 := by
  change ({4, 9} : Finset (Fin 10)).map hnNineD.toEmbedding = {4, 9}
  ext x
  fin_cases x <;> decide

theorem hnNineT_fix : hnNineX0.map hnNineT.toEmbedding = hnNineX0 := by
  change ({4, 9} : Finset (Fin 10)).map hnNineT.toEmbedding = {4, 9}
  ext x
  fin_cases x <;> decide

theorem hnNineU0_fix (g : Equiv.Perm (Fin 10)) (hg : g ∈ hnNineU0) :
    hnNineX0.map g.toEmbedding = hnNineX0 := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
      simp only [Set.mem_setOf_eq, hnNineGens, List.mem_cons, List.not_mem_nil,
        or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      exacts [hnNineA_fix, hnNineB_fix, hnNineC_fix, hnNineD_fix, hnNineT_fix]
  | one => exact Finset.map_refl
  | mul x y hx hy ihx ihy =>
      rw [Equiv.Perm.mul_def, Equiv.trans_toEmbedding, ← Finset.map_map, ihy, ihx]
  | inv x hx ih =>
      have h := congrArg (fun s : Finset (Fin 10) => s.map x⁻¹.toEmbedding) ih
      rw [Finset.map_map x.toEmbedding x⁻¹.toEmbedding hnNineX0] at h
      have hcomp : x.toEmbedding.trans x⁻¹.toEmbedding = Function.Embedding.refl _ := by
        rw [← Equiv.trans_toEmbedding]
        rw [show x.trans x⁻¹ = Equiv.refl _ from Equiv.self_trans_symm x]
        exact Equiv.refl_toEmbedding
      rw [hcomp, Finset.map_refl] at h
      exact h.symm

theorem hnNineUbar_fix
    (u : hnNineUbar) : u • hnNineX0 = hnNineX0 := by
  change hnNineX0.map (u : Equiv.Perm (Fin 10)).toEmbedding = hnNineX0
  exact hnNineU0_fix u (by simpa [hnNineUbar, Subgroup.mem_subgroupOf] using u.2)



theorem sigPerm_mem_phiQ
    (k : Fin 10) : sigPerm (k : ℕ) ∈ phiQ.range := by
  rw [range_phi_eq]
  exact Subgroup.subset_closure ⟨k, rfl⟩

theorem sigPerm_smul_finset
    (k : Fin 10) (s : Finset (Fin 10)) :
    (⟨sigPerm (k : ℕ), sigPerm_mem_phiQ k⟩ : phiQ.range) • s =
      s.image (hnNineActWk k) := by
  change s.map (sigPerm (k : ℕ)).toEmbedding = s.image (hnNineActWk k)
  rw [Finset.map_eq_image]
  congr 1
  ext x
  rw [hnNineActWk, sigPerm_eq_hnNinePerm_wk k, Equiv.toEmbedding_apply, hnNinePerm_apply]

theorem hnNineBFS_subset_orbit
    (n : Nat) :
    ∀ s ∈ hnNineOrbitBFS n ({hnNineX0} : Finset (Finset (Fin 10))),
      s ∈ MulAction.orbit phiQ.range hnNineX0 := by
  induction n with
  | zero =>
      intro s hs
      rw [hnNineOrbitBFS] at hs
      simp only [Nat.rec_zero, Finset.mem_singleton] at hs
      rw [hs]
      exact MulAction.mem_orbit_self _
  | succ n ih =>
      intro s hs
      change s ∈ hnNineStep (hnNineOrbitBFS n ({hnNineX0} : Finset (Finset (Fin 10)))) at hs
      rw [hnNineStep, Finset.mem_union, Finset.mem_biUnion] at hs
      rcases hs with hs | ⟨t, ht, hg⟩
      · exact ih s hs
      · rw [List.mem_toFinset, List.mem_map] at hg
        obtain ⟨g, hg, rfl⟩ := hg
        rw [hnNineGenDelta, List.mem_map] at hg
        obtain ⟨k, hk, rfl⟩ := hg
        obtain ⟨d, hd⟩ := MulAction.mem_orbit_iff.mp (ih t ht)
        refine MulAction.mem_orbit_iff.mpr
          ⟨(⟨sigPerm (k : ℕ), sigPerm_mem_phiQ k⟩ : phiQ.range) * d, ?_⟩
        rw [mul_smul, hd, sigPerm_smul_finset]

noncomputable def hnNineX' :
    phiQ.range :=
  ⟨hnNineX, by rw [hnNineX_eq]; exact hnNinePerm_mem_phiQ _⟩

noncomputable def hnNineY' :
    phiQ.range :=
  ⟨hnNineY, by rw [hnNineY_eq]; exact hnNinePerm_mem_phiQ _⟩

theorem hnNineX'_fix :
    hnNineX' • hnNineX0 = hnNineX0 := by
  change hnNineX0.map hnNineX.toEmbedding = hnNineX0
  ext x
  fin_cases x <;> decide

theorem hnNineY'_fix :
    hnNineY' • hnNineX0 = hnNineX0 := by
  change hnNineX0.map hnNineY.toEmbedding = hnNineX0
  ext x
  fin_cases x <;> decide


theorem hnNineX'_pow :
    hnNineX' ^ 3 = 1 := by
  apply Subtype.ext
  change hnNineX ^ 3 = 1
  ext x
  fin_cases x <;> decide

theorem hnNineY'_pow :
    hnNineY' ^ 3 = 1 := by
  apply Subtype.ext
  change hnNineY ^ 3 = 1
  ext x
  fin_cases x <;> decide

theorem hnNineX'_mul_y :
    hnNineX' * hnNineY' = hnNineY' * hnNineX' := by
  apply Subtype.ext
  change hnNineX * hnNineY = hnNineY * hnNineX
  ext x
  fin_cases x <;> decide

theorem hnNineX'_ne_one :
    hnNineX' ≠ 1 := by
  intro h
  have h' : hnNineX = (1 : Equiv.Perm (Fin 10)) := congrArg Subtype.val h
  have h0 : hnNineX 0 = (1 : Equiv.Perm (Fin 10)) 0 := congrArg (fun f => f 0) h'
  have hne : hnNineX 0 ≠ (1 : Equiv.Perm (Fin 10)) 0 := by decide
  exact hne h0

theorem hnNineY'_not_zpowers :
    hnNineY' ∉ Subgroup.zpowers hnNineX' := by
  intro h
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp h
  have hx5 : (hnNineX : Equiv.Perm (Fin 10)) 5 = 5 := by decide
  have hy5 : (hnNineY : Equiv.Perm (Fin 10)) 5 = 6 := by decide
  have hfix : ((hnNineX' ^ m : phiQ.range) : Equiv.Perm (Fin 10)) 5 = 5 := by
    rw [Subgroup.coe_zpow]
    exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self (f := hnNineX) hx5 m
  rw [hm] at hfix
  have : (hnNineY : Equiv.Perm (Fin 10)) 5 = 5 := hfix
  omega



attribute [local irreducible] hnNineOrbitBFS

theorem hnNine_stabilizer_card :
    Nat.card (MulAction.stabilizer phiQ.range hnNineX0) = 288 := by
  let S : ℕ := Nat.card (MulAction.stabilizer phiQ.range hnNineX0)
  let O : ℕ := (MulAction.stabilizer phiQ.range hnNineX0).index
  have hOeq : O = (MulAction.orbit phiQ.range hnNineX0).ncard :=
    MulAction.index_stabilizer (G := phiQ.range) (x := hnNineX0)
  have hSO : S * O = 7200 := by
    have h := Subgroup.card_mul_index (H := MulAction.stabilizer phiQ.range hnNineX0)
    rw [card_range_phi] at h
    exact h
  let Q : Subgroup phiQ.range := Subgroup.closure ({hnNineX', hnNineY'} : Set phiQ.range)
  have hQ9 : Nat.card Q = 9 :=
    CFSG.RankThree.Asc83Table.card_closure_pair_eq_nine
      hnNineX'_pow hnNineY'_pow hnNineX'_mul_y hnNineX'_ne_one hnNineY'_not_zpowers
  have hU_le_stab : hnNineUbar ≤ MulAction.stabilizer phiQ.range hnNineX0 := by
    intro u hu
    rw [MulAction.mem_stabilizer_iff]
    exact hnNineUbar_fix ⟨u, hu⟩
  have hQ_le_stab : Q ≤ MulAction.stabilizer phiQ.range hnNineX0 := by
    dsimp only [Q]
    rw [Subgroup.closure_le]
    intro z hz
    rcases hz with rfl | rfl
    · change hnNineX' ∈ MulAction.stabilizer phiQ.range hnNineX0
      rw [MulAction.mem_stabilizer_iff]
      exact hnNineX'_fix
    · change hnNineY' ∈ MulAction.stabilizer phiQ.range hnNineX0
      rw [MulAction.mem_stabilizer_iff]
      exact hnNineY'_fix
  let H : Subgroup phiQ.range := hnNineUbar ⊔ Q
  have hU_le_H : hnNineUbar ≤ H := le_sup_left
  have hQ_le_H : Q ≤ H := le_sup_right
  have hH_le_stab : H ≤ MulAction.stabilizer phiQ.range hnNineX0 :=
    sup_le hU_le_stab hQ_le_stab
  have h32_dvd : 32 ∣ Nat.card H := by
    rw [← hnNineUbar_card]
    exact Subgroup.card_dvd_of_le hU_le_H
  have h9_dvd : 9 ∣ Nat.card H := by
    rw [← hQ9]
    exact Subgroup.card_dvd_of_le hQ_le_H
  have hcop : Nat.Coprime 32 9 := by norm_num
  have h288_dvd : 288 ∣ Nat.card H := by
    have := hcop.mul_dvd_of_dvd_of_dvd h32_dvd h9_dvd
    simpa using this
  have hH_ge : 288 ≤ Nat.card H := Nat.le_of_dvd Nat.card_pos h288_dvd
  have hcardHStab : Nat.card H ≤ Nat.card (MulAction.stabilizer phiQ.range hnNineX0) :=
    Nat.card_le_card_of_injective
      (fun x : H => (⟨x.1, hH_le_stab x.2⟩ : MulAction.stabilizer phiQ.range hnNineX0))
      (fun a b hab => Subtype.ext
        (congrArg (fun z : MulAction.stabilizer phiQ.range hnNineX0 => (z : phiQ.range)) hab))
  have hSge : 288 ≤ S := le_trans hH_ge hcardHStab
  let B : Finset (Finset (Fin 10)) := hnNineOrbitBFS 5 ({hnNineX0} : Finset (Finset (Fin 10)))
  have hBcard : B.card = 25 := hnNine_orbit_card
  have hBFS_sub : (B : Set (Finset (Fin 10))) ⊆ MulAction.orbit phiQ.range hnNineX0 := by
    intro s hs
    have hs' : s ∈ hnNineOrbitBFS 5 ({hnNineX0} : Finset (Finset (Fin 10))) := by
      rwa [show B = hnNineOrbitBFS 5 ({hnNineX0} : Finset (Finset (Fin 10))) from rfl] at hs
    exact hnNineBFS_subset_orbit 5 s hs'
  have hOge : 25 ≤ O := by
    have h1 : B.card ≤ (MulAction.orbit phiQ.range hnNineX0).ncard := by
      rw [← Set.ncard_coe_finset]
      exact Set.ncard_mono hBFS_sub
    rw [hBcard, ← hOeq] at h1
    exact h1
  have hOle : O ≤ 25 := by
    have h : 288 * O ≤ 288 * 25 := by
      calc 288 * O
          ≤ S * O := Nat.mul_le_mul_right O hSge
        _ = 7200 := hSO
        _ = 288 * 25 := by norm_num
    exact Nat.le_of_mul_le_mul_left h (by norm_num)
  have hO : O = 25 := by omega
  have hS : S = 288 := by
    have h := hSO
    rw [hO] at h
    omega
  simpa [S] using hS


def hnNineEList : List (Equiv.Perm (Fin 10)) := hnNineList.take 16

theorem hnNineEList_length : hnNineEList.length = 16 := by decide

theorem hnNineEList_nodup : hnNineEList.Nodup := by decide

theorem hnNineEList_mul :
    hnNineEList.all (fun x => hnNineEList.all (fun y => decide (x * y ∈ hnNineEList))) = true := by
  decide

theorem hnNineEList_inv : hnNineEList.all (fun x => decide (x⁻¹ ∈ hnNineEList)) = true := by
  decide

theorem hnNineEList_comm :
    hnNineEList.all (fun x => hnNineEList.all (fun y => decide (x * y = y * x))) = true := by
  decide

noncomputable def hnNineE0 : Subgroup (Equiv.Perm (Fin 10)) where
  carrier := {x | x ∈ hnNineEList}
  one_mem' := by decide
  mul_mem' := by
    intro x y hx hy
    have h := List.all_eq_true.1 hnNineEList_mul x hx
    exact of_decide_eq_true (List.all_eq_true.1 h y hy)
  inv_mem' := by
    intro x hx
    exact of_decide_eq_true (List.all_eq_true.1 hnNineEList_inv x hx)

theorem hnNineE0_card : Nat.card hnNineE0 = 16 := by
  calc Nat.card hnNineE0 = Nat.card {x : Equiv.Perm (Fin 10) // x ∈ hnNineEList} :=
        Nat.card_congr (Equiv.subtypeEquivRight (fun x => by
          change x ∈ (hnNineE0 : Set (Equiv.Perm (Fin 10))) ↔ x ∈ hnNineEList
          rfl))
    _ = Nat.card (Fin hnNineEList.length) :=
        Nat.card_congr (List.Nodup.getEquiv hnNineEList hnNineEList_nodup).symm
    _ = hnNineEList.length := Nat.card_fin _
    _ = 16 := hnNineEList_length

theorem hnNineEList_subset_list : ∀ x ∈ hnNineEList, x ∈ hnNineList := by
  intro x hx
  exact List.take_subset _ _ hx

theorem hnNineE0_le_range :
    hnNineE0 ≤ phiQ.range := by
  intro x hx
  exact hnNineU0_le_range (hnNineList_mem_U0 x (hnNineEList_subset_list x hx))

noncomputable def hnNineE :
    Subgroup phiQ.range :=
  hnNineE0.subgroupOf phiQ.range

theorem hnNineE_card :
    Nat.card hnNineE = 16 := by
  rw [hnNineE]
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hnNineE0_le_range).toEquiv]
  exact hnNineE0_card


theorem hnNineE_comm
    (x y : hnNineE) : x * y = y * x := by
  apply Subtype.ext
  apply Subtype.ext
  change ((x : phiQ.range) : Equiv.Perm (Fin 10)) * ((y : phiQ.range) : Equiv.Perm (Fin 10)) =
    ((y : phiQ.range) : Equiv.Perm (Fin 10)) * ((x : phiQ.range) : Equiv.Perm (Fin 10))
  have hx : ((x : phiQ.range) : Equiv.Perm (Fin 10)) ∈ hnNineEList := by
    simpa [hnNineE, Subgroup.mem_subgroupOf, hnNineE0] using x.2
  have hy : ((y : phiQ.range) : Equiv.Perm (Fin 10)) ∈ hnNineEList := by
    simpa [hnNineE, Subgroup.mem_subgroupOf, hnNineE0] using y.2
  have h := List.all_eq_true.1 hnNineEList_comm _ hx
  exact of_decide_eq_true (List.all_eq_true.1 h _ hy)

theorem hnNineE_unique_check :
    (hnNineList.filter (fun u => decide (u ∉ hnNineEList))).all
      (fun u => (hnNineEList.filter (fun e => decide (u * e = e * u))).length ≤ 4) = true := by
  decide


theorem hnNineE_le_Ubar :
    hnNineE ≤ hnNineUbar := by
  intro x hx
  have hxE : ((x : phiQ.range) : Equiv.Perm (Fin 10)) ∈ hnNineEList := by
    simpa [hnNineE, Subgroup.mem_subgroupOf, hnNineE0] using hx
  have hxList : ((x : phiQ.range) : Equiv.Perm (Fin 10)) ∈ hnNineList :=
    hnNineEList_subset_list _ hxE
  have hxU0 : ((x : phiQ.range) : Equiv.Perm (Fin 10)) ∈ hnNineU0 :=
    hnNineList_mem_U0 _ hxList
  simpa [hnNineUbar, Subgroup.mem_subgroupOf] using hxU0


theorem hnNineE_centralizer_le_four
    (u : hnNineUbar) (hu : (u : phiQ.range) ∉ hnNineE) :
    Nat.card (↥(hnNineE ⊓
      Subgroup.centralizer ({(u : phiQ.range)} : Set phiQ.range))) ≤ 4 := by
  let L := hnNineEList.filter (fun e =>
    decide (((u : Equiv.Perm (Fin 10)) * (e : Equiv.Perm (Fin 10))) =
      ((e : Equiv.Perm (Fin 10)) * (u : Equiv.Perm (Fin 10)))))
  have huU0 : ((u : phiQ.range) : Equiv.Perm (Fin 10)) ∈ hnNineU0 := by
    simpa [hnNineUbar, Subgroup.mem_subgroupOf] using u.2
  have huList : ((u : phiQ.range) : Equiv.Perm (Fin 10)) ∈ hnNineList :=
    hnNineU0_le_listSub huU0
  have huNotE : ((u : phiQ.range) : Equiv.Perm (Fin 10)) ∉ hnNineEList := by
    intro h
    exact hu (by simpa [hnNineE, Subgroup.mem_subgroupOf, hnNineE0] using h)
  have hLcard : L.length ≤ 4 := by
    have hmem : ((u : phiQ.range) : Equiv.Perm (Fin 10)) ∈
        hnNineList.filter (fun x => decide (x ∉ hnNineEList)) :=
      List.mem_filter.mpr ⟨huList, by simpa using huNotE⟩
    have h := List.all_eq_true.1 hnNineE_unique_check _ hmem
    simpa [L] using h
  have hle : Nat.card (↥(hnNineE ⊓
      Subgroup.centralizer ({(u : phiQ.range)} : Set phiQ.range))) ≤
      Nat.card {e // e ∈ L} := by
    refine Nat.card_le_card_of_injective
      (fun z : ↥(hnNineE ⊓
          Subgroup.centralizer ({(u : phiQ.range)} : Set phiQ.range)) =>
        (⟨((z.1 : phiQ.range) : Equiv.Perm (Fin 10)), ?_⟩ : {e // e ∈ L}))
      ?_
    · have hzE : ((z.1 : phiQ.range) : Equiv.Perm (Fin 10)) ∈ hnNineEList := by
        simpa [hnNineE, Subgroup.mem_subgroupOf, hnNineE0] using z.2.1
      have hzC := Subgroup.mem_centralizer_iff.mp z.2.2
      have hcomm : (u : Equiv.Perm (Fin 10)) * ((z.1 : phiQ.range) : Equiv.Perm (Fin 10)) =
          ((z.1 : phiQ.range) : Equiv.Perm (Fin 10)) * (u : Equiv.Perm (Fin 10)) := by
        have h := congrArg (fun w : phiQ.range => (w : Equiv.Perm (Fin 10)))
          (hzC (u : phiQ.range) (by simp))
        simpa only [Subgroup.coe_mul] using h
      exact List.mem_filter.mpr ⟨hzE, by simpa using hcomm⟩
    · intro a b hab
      have h : ((a.1 : phiQ.range) : Equiv.Perm (Fin 10)) =
          ((b.1 : phiQ.range) : Equiv.Perm (Fin 10)) :=
        congrArg (fun w : {e // e ∈ L} => (w : Equiv.Perm (Fin 10))) hab
      apply Subtype.ext
      apply Subtype.ext
      exact h
  have hLnodup : L.Nodup := hnNineEList_nodup.filter _
  have hLcard : Nat.card {e // e ∈ L} = L.length := by
    calc Nat.card {e // e ∈ L} = Nat.card (Fin L.length) :=
          Nat.card_congr (List.Nodup.getEquiv L hLnodup).symm
      _ = L.length := Nat.card_fin _
  rw [hLcard] at hle
  omega


theorem hnNineU0_eq_listSub : hnNineU0 = hnNineListSub :=
  le_antisymm hnNineU0_le_listSub hnNineListSub_le_U0

theorem hnNineUbar_mem_iff
    (x : phiQ.range) : x ∈ hnNineUbar ↔ (x : Equiv.Perm (Fin 10)) ∈ hnNineList := by
  rw [hnNineUbar, Subgroup.mem_subgroupOf, hnNineU0_eq_listSub]
  rfl

theorem hnNineE_mem_iff
    (x : phiQ.range) : x ∈ hnNineE ↔ (x : Equiv.Perm (Fin 10)) ∈ hnNineEList := by
  rw [hnNineE, Subgroup.mem_subgroupOf]
  rfl

theorem hnNineE_unique_abelian
    (F : Subgroup phiQ.range) (hFle : F ≤ hnNineUbar) (hFcard : Nat.card F = 16)
    (hFcomm : ∀ x y : F, x * y = y * x) : F = hnNineE := by
  by_cases hFE : F ≤ hnNineE
  · exact Subgroup.eq_of_le_of_card_ge hFE (by rw [hFcard, hnNineE_card])
  · have hFE' : ∃ u : phiQ.range, u ∈ F ∧ u ∉ hnNineE := by
      by_contra h
      exact hFE fun x hx => by
        by_contra hxE
        exact h ⟨x, hx, hxE⟩
    obtain ⟨u, huF, huE⟩ := hFE'
    have huU : u ∈ hnNineUbar := hFle huF
    have hle : F ⊓ hnNineE ≤
        hnNineE ⊓ Subgroup.centralizer ({u} : Set phiQ.range) := by
      intro x hx
      rw [Subgroup.mem_inf] at hx ⊢
      refine ⟨hx.2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (hFcomm ⟨x, hx.1⟩ ⟨u, huF⟩)
    have hcard_inf_le : Nat.card (↥(F ⊓ hnNineE)) ≤ 4 :=
      (Subgroup.card_le_of_le hle).trans
        (hnNineE_centralizer_le_four ⟨u, huU⟩ (by simpa using huE))
    have h := CFSG.UnitaryThreeRecognition.card_mul_card_le_card_mul_card_inf
      (G := ↥phiQ.range) (H₁ := F) (H₂ := hnNineE) (L := hnNineUbar) hFle hnNineE_le_Ubar
    rw [hFcard, hnNineE_card, hnNineUbar_card] at h
    have h8 : 8 ≤ Nat.card (↥(F ⊓ hnNineE)) := by omega
    omega


theorem hnNineX'_conj_EList :
    hnNineEList.all (fun e => decide (hnNineX * e * hnNineX⁻¹ ∈ hnNineEList)) = true := by
  decide

theorem hnNineY'_conj_EList :
    hnNineEList.all (fun e => decide (hnNineY * e * hnNineY⁻¹ ∈ hnNineEList)) = true := by
  decide

theorem hnNineX'_normalizes_E :
    Subgroup.map (MulAut.conj hnNineX').toMonoidHom hnNineE = hnNineE := by
  have hle : Subgroup.map (MulAut.conj hnNineX').toMonoidHom hnNineE ≤ hnNineE := by
    intro y hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hxE : ((x : phiQ.range) : Equiv.Perm (Fin 10)) ∈ hnNineEList := by
      simpa [hnNineE, Subgroup.mem_subgroupOf, hnNineE0] using hx
    have hmem : ((hnNineX * ((x : phiQ.range) : Equiv.Perm (Fin 10)) * hnNineX⁻¹) :
        Equiv.Perm (Fin 10)) ∈ hnNineEList := by
      exact of_decide_eq_true (List.all_eq_true.1 hnNineX'_conj_EList _ hxE)
    rw [hnNineE_mem_iff]
    change ((hnNineX' * x * hnNineX'⁻¹ : phiQ.range) : Equiv.Perm (Fin 10)) ∈ hnNineEList
    rwa [show ((hnNineX' * x * hnNineX'⁻¹ : phiQ.range) : Equiv.Perm (Fin 10)) =
        hnNineX * ((x : phiQ.range) : Equiv.Perm (Fin 10)) * hnNineX⁻¹ from rfl]
  have hcard := Subgroup.card_map_of_injective (K := hnNineE)
    (f := (MulAut.conj hnNineX').toMonoidHom) (MulAut.conj hnNineX').injective
  rw [hnNineE_card] at hcard
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hnNineE_card])

theorem hnNineY'_normalizes_E :
    Subgroup.map (MulAut.conj hnNineY').toMonoidHom hnNineE = hnNineE := by
  have hle : Subgroup.map (MulAut.conj hnNineY').toMonoidHom hnNineE ≤ hnNineE := by
    intro y hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hxE : ((x : phiQ.range) : Equiv.Perm (Fin 10)) ∈ hnNineEList := by
      simpa [hnNineE, Subgroup.mem_subgroupOf, hnNineE0] using hx
    have hmem : ((hnNineY * ((x : phiQ.range) : Equiv.Perm (Fin 10)) * hnNineY⁻¹) :
        Equiv.Perm (Fin 10)) ∈ hnNineEList := by
      exact of_decide_eq_true (List.all_eq_true.1 hnNineY'_conj_EList _ hxE)
    rw [hnNineE_mem_iff]
    change ((hnNineY' * x * hnNineY'⁻¹ : phiQ.range) : Equiv.Perm (Fin 10)) ∈ hnNineEList
    rwa [show ((hnNineY' * x * hnNineY'⁻¹ : phiQ.range) : Equiv.Perm (Fin 10)) =
        hnNineY * ((x : phiQ.range) : Equiv.Perm (Fin 10)) * hnNineY⁻¹ from rfl]
  have hcard := Subgroup.card_map_of_injective (K := hnNineE)
    (f := (MulAut.conj hnNineY').toMonoidHom) (MulAut.conj hnNineY').injective
  rw [hnNineE_card] at hcard
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hnNineE_card])

theorem hnNineE_unique_fixed :
    ∀ s : Finset (Fin 10), s.card = 2 →
      (∀ e ∈ hnNineEList, s.map e.toEmbedding = s) → s = hnNineX0 := by
  decide +kernel

theorem hnNine_normalizer_le_stabilizer :
    Subgroup.normalizer hnNineE ≤ MulAction.stabilizer phiQ.range hnNineX0 := by
  intro p hp
  rw [MulAction.mem_stabilizer_iff]
  have hs_fixed : ∀ e : Equiv.Perm (Fin 10), e ∈ hnNineEList →
      (p • hnNineX0).map e.toEmbedding = p • hnNineX0 := by
    intro e he
    have he0 : e ∈ hnNineE0 := by simpa [hnNineE0] using he
    have heRange : e ∈ phiQ.range := hnNineE0_le_range he0
    let e' : phiQ.range := ⟨e, heRange⟩
    have heE : e' ∈ hnNineE := by
      simpa [hnNineE, Subgroup.mem_subgroupOf, e', hnNineE0] using he
    have hconj : p⁻¹ * e' * p ∈ hnNineE := by
      have hpinv : p⁻¹ ∈ Subgroup.normalizer hnNineE := Subgroup.inv_mem _ hp
      rw [Subgroup.mem_normalizer_iff] at hpinv
      exact (hpinv e').mp heE
    let u' : hnNineUbar := ⟨p⁻¹ * e' * p, hnNineE_le_Ubar hconj⟩
    have hfix : u' • hnNineX0 = hnNineX0 := hnNineUbar_fix u'
    calc (p • hnNineX0).map e.toEmbedding
        = (e' * p) • hnNineX0 := by
          change (hnNineX0.map ((p : Equiv.Perm (Fin 10))).toEmbedding).map e.toEmbedding =
            hnNineX0.map ((e * p : Equiv.Perm (Fin 10))).toEmbedding
          rw [Equiv.Perm.mul_def, Equiv.trans_toEmbedding, Finset.map_map]
      _ = (p * (p⁻¹ * e' * p)) • hnNineX0 := by
          rw [show e' * p = p * (p⁻¹ * e' * p) by group]
      _ = p • (u' • hnNineX0) := by
          rw [mul_smul]
          rfl
      _ = p • hnNineX0 := by rw [hfix]
  have hcard : (p • hnNineX0).card = 2 := by
    rw [← hnNineX0_card]
    exact Finset.card_map _
  have huniq := hnNineE_unique_fixed (p • hnNineX0) hcard hs_fixed
  simpa using huniq


theorem hnNineUbar_conj_EList :
    hnNineList.all (fun u => hnNineEList.all (fun e =>
      decide (u * e * u⁻¹ ∈ hnNineEList))) = true := by
  decide

theorem hnNineUbar_normalizes_E
    (u : phiQ.range) (hu : u ∈ hnNineUbar) :
    hnNineE.map (MulAut.conj u).toMonoidHom = hnNineE := by
  have huList : (u : Equiv.Perm (Fin 10)) ∈ hnNineList :=
    (hnNineUbar_mem_iff u).mp hu
  have hle : hnNineE.map (MulAut.conj u).toMonoidHom ≤ hnNineE := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    have hxE : ((x : phiQ.range) : Equiv.Perm (Fin 10)) ∈ hnNineEList :=
      (hnNineE_mem_iff x).mp hx
    have hmem : (u : Equiv.Perm (Fin 10)) * ((x : phiQ.range) : Equiv.Perm (Fin 10)) *
        (u : Equiv.Perm (Fin 10))⁻¹ ∈ hnNineEList :=
      of_decide_eq_true (List.all_eq_true.1
        (List.all_eq_true.1 hnNineUbar_conj_EList _ huList) _ hxE)
    rw [hnNineE_mem_iff]
    change ((u * x * u⁻¹ : phiQ.range) : Equiv.Perm (Fin 10)) ∈ hnNineEList
    rwa [show ((u * x * u⁻¹ : phiQ.range) : Equiv.Perm (Fin 10)) =
        u * ((x : phiQ.range) : Equiv.Perm (Fin 10)) * u⁻¹ from rfl]
  have hcard := Subgroup.card_map_of_injective (K := hnNineE)
    (f := (MulAut.conj u).toMonoidHom) (MulAut.conj u).injective
  rw [hnNineE_card] at hcard
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hnNineE_card])

theorem hnNineUbar_le_normalizer_E :
    hnNineUbar ≤ Subgroup.normalizer hnNineE := by
  intro u hu
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact hnNineUbar_normalizes_E u hu

noncomputable def hnNineQ :
    Subgroup phiQ.range :=
  Subgroup.closure ({hnNineX', hnNineY'} : Set phiQ.range)

theorem hnNineQ_card :
    Nat.card hnNineQ = 9 :=
  CFSG.RankThree.Asc83Table.card_closure_pair_eq_nine
    hnNineX'_pow hnNineY'_pow hnNineX'_mul_y hnNineX'_ne_one hnNineY'_not_zpowers

theorem hnNineQ_le_normalizer_E :
    hnNineQ ≤ Subgroup.normalizer (hnNineE : Set phiQ.range) := by
  rw [hnNineQ, Subgroup.closure_le]
  intro x hx
  rcases hx with rfl | rfl
  · exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hnNineX'_normalizes_E
  · exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hnNineY'_normalizes_E

theorem hnNineQ_pow_three :
    ∀ q ∈ hnNineQ, q ^ 3 = 1 := by
  have hcomm : ⁅hnNineX', hnNineY'⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact hnNineX'_mul_y
  intro q hq
  exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.pow_three_eq_one_of_mem_closure_cubic
    hnNineX'_pow hnNineY'_pow (by rw [hcomm]; exact Commute.one_left _)
    (by rw [hcomm]; exact Commute.one_left _) hq

theorem hnNineE_map_eq
    (α : MulAut phiQ.range) (hα : hnNineUbar.map α.toMonoidHom = hnNineUbar) :
    hnNineE.map α.toMonoidHom = hnNineE := by
  refine hnNineE_unique_abelian (hnNineE.map α.toMonoidHom) ?_ ?_ ?_
  · calc hnNineE.map α.toMonoidHom ≤ hnNineUbar.map α.toMonoidHom :=
        Subgroup.map_mono hnNineE_le_Ubar
      _ = hnNineUbar := hα
  · rw [Subgroup.card_map_of_injective α.injective, hnNineE_card]
  · intro x y
    obtain ⟨x0, hx0, hx⟩ := Subgroup.mem_map.mp x.2
    obtain ⟨y0, hy0, hy⟩ := Subgroup.mem_map.mp y.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hx, ← hy]
    have hcomm := congrArg (fun z : hnNineE => (z : phiQ.range))
      (hnNineE_comm ⟨x0, hx0⟩ ⟨y0, hy0⟩)
    simp only [Subgroup.coe_mul] at hcomm
    change α x0 * α y0 = α y0 * α x0
    simpa only [map_mul] using congrArg (fun z => α z) hcomm

theorem hnNine_fullPackage :
    IndexNinePackage phiQ.range := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite phiQ.range :=
    Nat.finite_of_card_ne_zero (by rw [card_range_phi]; norm_num)
  let P : Subgroup phiQ.range := Subgroup.normalizer (hnNineE : Set phiQ.range)
  have hQP : hnNineQ ≤ P := hnNineQ_le_normalizer_E
  have hUP : hnNineUbar ≤ P := hnNineUbar_le_normalizer_E
  have hPQ : hnNineUbar ⊔ hnNineQ ≤ P := sup_le hUP hQP
  have hdisj : hnNineUbar ⊓ hnNineQ = ⊥ := by
    apply (Subgroup.disjoint_of_coprime_natCard ?_).eq_bot
    rw [hnNineUbar_card, hnNineQ_card]
    norm_num
  have h288 : 288 ≤ Nat.card (hnNineUbar ⊔ hnNineQ : Subgroup phiQ.range) := by
    have h := CFSG.UnitaryThreeRecognition.card_mul_card_le_card_mul_card_inf
      (G := phiQ.range) (H₁ := hnNineUbar) (H₂ := hnNineQ) (L := hnNineUbar ⊔ hnNineQ)
      le_sup_left le_sup_right
    rw [hnNineUbar_card, hnNineQ_card, hdisj, Subgroup.card_bot] at h
    omega
  have hPge : 288 ≤ Nat.card P := le_trans h288 (Subgroup.card_le_of_le hPQ)
  let K : Subgroup phiQ.range := MulAction.stabilizer phiQ.range hnNineX0
  have hPle : Nat.card P ≤ 288 := by
    have h : Nat.card P ≤ Nat.card K := Subgroup.card_le_of_le hnNine_normalizer_le_stabilizer
    rwa [show Nat.card K = 288 from hnNine_stabilizer_card] at h
  have hPcard : Nat.card P = 288 := le_antisymm hPle hPge
  refine ⟨hnNineUbar, P, hnNineQ, hnNineUbar_isSylow, hUP, ?_, ?_, hQP,
    hnNineQ_card, hnNineQ_pow_three⟩
  · rw [hPcard, hnNineUbar_card]
  · intro α hα
    calc P.map α.toMonoidHom
        = Subgroup.normalizer ((hnNineE.map α.toMonoidHom : Subgroup phiQ.range) :
            Set phiQ.range) := Subgroup.map_equiv_normalizer_eq hnNineE α
      _ = P := by rw [hnNineE_map_eq α hα]

@[expose] noncomputable def hnNineGperm : Equiv.Perm (Fin 10) :=
  (finSumFinEquiv (m := 5) (n := 5)).symm.trans
    ((Equiv.sumCongr hnNinePRev hnNineP9B).trans (finSumFinEquiv (m := 5) (n := 5)))

theorem hnNineGperm_rep : PRep 10 sigArrs[9]! hnNineGperm := by
  intro x
  fin_cases x <;> decide

theorem hnNineGperm_eq :
    hnNineGperm = sigPerm 9 :=
  PRep.unique hnNineGperm_rep (prep_sigPerm (by norm_num : 9 < 10))

theorem hnNineGperm_mem :
    hnNineGperm ∈ phiQ.range := by
  rw [hnNineGperm_eq]
  exact sigPerm_mem_phiQ 9

theorem hnNineConjCheck :
    hnNineList.all (fun x : Equiv.Perm (Fin 10) => decide
      (x = 1 ∨ hnNineGperm⁻¹ * x * hnNineGperm ∉ hnNineList)) = true := by
  decide +kernel

theorem hnNineUbar_inf_conj :
    hnNineUbar ⊓ hnNineUbar.map
      (MulAut.conj (⟨hnNineGperm, hnNineGperm_mem⟩ : phiQ.range)).toMonoidHom = ⊥ := by
  let g : phiQ.range := ⟨hnNineGperm, hnNineGperm_mem⟩
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxU, hxG⟩ := hx
    obtain ⟨y, hyU, hyx⟩ := Subgroup.mem_map.mp hxG
    have hxe : x = 1 := by
      have hyList : ((y : phiQ.range) : Equiv.Perm (Fin 10)) ∈ hnNineList :=
        (hnNineUbar_mem_iff y).mp hyU
      have hxList : ((x : phiQ.range) : Equiv.Perm (Fin 10)) ∈ hnNineList :=
        (hnNineUbar_mem_iff x).mp hxU
      have hconjList : ((g⁻¹ * x * g : phiQ.range) : Equiv.Perm (Fin 10)) ∈
          hnNineList := by
        have hxy : g⁻¹ * x * g = y := by
          have hx' : x = g * y * g⁻¹ := by
            have hyx' : x = (MulAut.conj g) y := by
              simpa only [MulEquiv.coe_toMonoidHom] using hyx.symm
            rw [hyx', MulAut.conj_apply]
          rw [hx']
          group
        rw [hxy]
        exact hyList
      have hcheck : ((x : phiQ.range) : Equiv.Perm (Fin 10)) = 1 ∨
          hnNineGperm⁻¹ * ((x : phiQ.range) : Equiv.Perm (Fin 10)) * hnNineGperm ∉
            hnNineList :=
        of_decide_eq_true (List.all_eq_true.1 hnNineConjCheck
          ((x : phiQ.range) : Equiv.Perm (Fin 10)) hxList)
      rcases hcheck with h1 | h2
      · exact Subtype.ext h1
      · exact absurd (by simpa [g] using hconjList) h2
    rw [hxe]
    simp
  · exact bot_le

theorem hnNine_no_normal_two :
    ∀ N : Subgroup phiQ.range, N.Normal → IsPGroup 2 ↥N → N = ⊥ := by
  intro N hNnorm hN2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite phiQ.range :=
    Nat.finite_of_card_ne_zero (by rw [card_range_phi]; norm_num)
  haveI := hNnorm
  have hUidx : ¬ 2 ∣ hnNineUbar.index := by
    have h := hnNineUbar_isSylow.2.2
    rw [show (hnNineUbar.subgroupOf ⊤).index = hnNineUbar.index from
      Subgroup.relIndex_top_right hnNineUbar] at h
    exact h
  let S : Sylow 2 phiQ.range := hnNineUbar_isSylow.2.1.toSylow hUidx
  have hScoe : (S : Subgroup phiQ.range) = hnNineUbar := IsPGroup.toSylow_coe _ _
  have hNU : N ≤ hnNineUbar := by
    rw [← hScoe]
    exact hN2.le_sylow_of_normal S
  let g : phiQ.range := ⟨hnNineGperm, hnNineGperm_mem⟩
  have hconjsyl : CFSG.QuasithinUnique.IsSylowTwoOf
      (hnNineUbar.map (MulAut.conj g).toMonoidHom) ⊤ := by
    simpa using hnNineUbar_isSylow.map_mulEquiv (MulAut.conj g)
  have hconjidx : ¬ 2 ∣ (hnNineUbar.map (MulAut.conj g).toMonoidHom).index := by
    have h := hconjsyl.2.2
    rw [show ((hnNineUbar.map (MulAut.conj g).toMonoidHom).subgroupOf ⊤).index =
      (hnNineUbar.map (MulAut.conj g).toMonoidHom).index from
      Subgroup.relIndex_top_right _] at h
    exact h
  let Sg : Sylow 2 phiQ.range := hconjsyl.2.1.toSylow hconjidx
  have hSgcoe : (Sg : Subgroup phiQ.range) =
      hnNineUbar.map (MulAut.conj g).toMonoidHom := IsPGroup.toSylow_coe _ _
  have hNg : N ≤ hnNineUbar.map (MulAut.conj g).toMonoidHom := by
    rw [← hSgcoe]
    exact hN2.le_sylow_of_normal Sg
  have hbot : hnNineUbar ⊓ hnNineUbar.map (MulAut.conj g).toMonoidHom = ⊥ := by
    simpa [g] using hnNineUbar_inf_conj
  have hNbot : N ≤ ⊥ := by
    rw [← hbot]
    exact le_inf hNU hNg
  exact bot_unique hNbot


theorem hn_index_nine_package :
    IndexNinePackage ↥JH := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite JH := Nat.finite_of_card_ne_zero (by rw [card_JH]; norm_num)
  let C : Subgroup JH := CFSG.EvenSporadicStandard.HNRecog.SideF4.CJ
  haveI : Finite C := Subtype.finite
  haveI : Finite phiQ.range :=
    Nat.finite_of_card_ne_zero (by rw [card_range_phi]; norm_num)
  let U : Subgroup JH := (hnNineUbar.comap phiQ.rangeRestrict).map C.subtype
  let R₀ : Subgroup JH := QJ.map C.subtype
  have hUC : U ≤ C := Subgroup.map_subtype_le _
  have hU_card : Nat.card U = 512 * 32 := by
    calc Nat.card U
        = Nat.card (hnNineUbar.comap phiQ.rangeRestrict) :=
          Subgroup.card_map_of_injective C.subtype_injective
      _ = Nat.card phiQ.rangeRestrict.ker * Nat.card hnNineUbar :=
          CFSG.GroupTheory.card_comap_eq_card_ker_mul_card
            phiQ.rangeRestrict phiQ.rangeRestrict_surjective hnNineUbar
      _ = 512 * 32 := by
          rw [MonoidHom.ker_rangeRestrict, ker_phi_eq, card_QJ, hnNineUbar_card]
  have hU_sylow : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤ := by
    refine ⟨le_top, IsPGroup.of_card (n := 14) (by rw [hU_card]; norm_num), ?_⟩
    have hindex : U.index = 16664484375 := by
      have h := Subgroup.card_mul_index (H := U)
      rw [card_JH, hU_card] at h
      omega
    rw [show (U.subgroupOf ⊤).index = U.index from Subgroup.relIndex_top_right U, hindex]
    norm_num
  have ht4U : t4J ∈ U := by
    refine Subgroup.mem_map.mpr ⟨t4G, ?_, rfl⟩
    rw [Subgroup.mem_comap]
    have hker : t4G ∈ phiQ.rangeRestrict.ker := by
      rw [MonoidHom.ker_rangeRestrict, ker_phi_eq]
      exact t4G_mem_QJ
    rw [MonoidHom.mem_ker.mp hker]
    exact hnNineUbar.one_mem
  have hR0_le_U : R₀ ≤ U := by
    intro y hy
    obtain ⟨c, hcQ, rfl⟩ := Subgroup.mem_map.mp hy
    refine Subgroup.mem_map.mpr ⟨c, ?_, rfl⟩
    rw [Subgroup.mem_comap]
    have hker : c ∈ phiQ.rangeRestrict.ker := by
      rw [MonoidHom.ker_rangeRestrict, ker_phi_eq]
      exact hcQ
    rw [MonoidHom.mem_ker.mp hker]
    exact hnNineUbar.one_mem
  have hCU : U ⊓ Subgroup.centralizer (R₀ : Set JH) ≤ R₀ := by
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxU, hxC⟩ := hx
    obtain ⟨c, hcU, rfl⟩ := Subgroup.mem_map.mp hxU
    refine Subgroup.mem_map.mpr ⟨c, ?_, rfl⟩
    refine centralizer_QJ_le ?_
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have h := Subgroup.mem_centralizer_iff.mp hxC (C.subtype q)
      (Subgroup.mem_map.mpr ⟨q, hq, rfl⟩)
    exact C.subtype_injective (by simpa using h)
  have ht4centerQJ : (⟨t4G, t4G_mem_QJ⟩ : QJ) ∈ Subgroup.center QJ := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (t4G_central (y : C)).symm
  have hcenterQJ : Subgroup.center QJ = Subgroup.zpowers (⟨t4G, t4G_mem_QJ⟩ : QJ) := by
    apply le_antisymm
    · intro z hz
      have hzc : (z : C) ∈ Subgroup.zpowers t4G := by
        refine centre_QJ_le exists_noncomm_QJ z z.2 (fun y hy => ?_)
        simpa using congrArg (fun w : QJ => (w : C))
          (Subgroup.mem_center_iff.1 hz ⟨y, hy⟩).symm
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hzc
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
      apply Subtype.ext
      exact hk
    · exact Subgroup.zpowers_le.mpr ht4centerQJ
  have hZ : ∀ x : JH, (x ∈ U ∧ ∀ y ∈ U, x * y = y * x) ↔ x = 1 ∨ x = t4J := by
    intro x
    constructor
    · rintro ⟨hxU, hxc⟩
      have hxR : x ∈ R₀ := (center_le_of_centralizer_le hR0_le_U hCU x hxU hxc).1
      have hxcentR : ∀ y ∈ R₀, x * y = y * x :=
        (center_le_of_centralizer_le hR0_le_U hCU x hxU hxc).2
      obtain ⟨c, hcQ, hcx⟩ := Subgroup.mem_map.mp hxR
      have hccent : (⟨c, hcQ⟩ : QJ) ∈ Subgroup.center QJ := by
        rw [Subgroup.mem_center_iff]
        intro y
        have hyR : C.subtype (y : C) ∈ R₀ := Subgroup.mem_map.mpr ⟨(y : C), y.2, rfl⟩
        have h := hxcentR (C.subtype (y : C)) hyR
        rw [← hcx] at h
        apply Subtype.ext
        exact C.subtype_injective (by simpa using h.symm)
      have hc_zpow : c ∈ Subgroup.zpowers t4G := by
        have hmem : (⟨c, hcQ⟩ : QJ) ∈
            Subgroup.zpowers (⟨t4G, t4G_mem_QJ⟩ : QJ) := by
          rw [← hcenterQJ]
          exact hccent
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
        refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
        simpa using congrArg Subtype.val hk
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hc_zpow
      have hxpow : x = t4J ^ k := by
        rw [← hcx, ← hk, map_zpow]
        rfl
      have h2 : t4J ^ (2 : ℤ) = 1 := by
        rw [zpow_two, t4J_sq]
      rcases Int.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
      · left
        rw [hxpow, hm, show m + m = 2 * m by ring, zpow_mul, h2, one_zpow]
      · right
        rw [hxpow, hm, zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]
    · rintro (rfl | rfl)
      · exact ⟨Subgroup.one_mem _, fun y _ => by simp⟩
      · refine ⟨ht4U, fun y hy => ?_⟩
        have hyC : y ∈ C := hUC hy
        exact (Subgroup.mem_centralizer_singleton_iff.1 hyC).symm
  have hz : ∀ α : MulAut JH, U.map (α : JH →* JH) = U → α t4J = t4J := by
    intro α hα
    exact map_eq_of_center (U := U) (z := t4J) hZ t4J_ne_one α hα
  have hker : IsPGroup 2 phiQ.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict, ker_phi_eq]
    exact IsPGroup.of_card (n := 9) (by rw [card_QJ]; norm_num)
  have hchar := char_of_centralizer (Γ := JH) (U := U) (z := t4J)
    hz phiQ.rangeRestrict phiQ.rangeRestrict_surjective hker hnNine_no_normal_two
  exact indexNinePackage_of_char_quotient (Γ := JH) (Δ := phiQ.range)
    (U := U) (C := C) hU_sylow hUC phiQ.rangeRestrict
    phiQ.rangeRestrict_surjective hker hchar hnNine_fullPackage

end CFSG.Sporadic.HNSchreier
