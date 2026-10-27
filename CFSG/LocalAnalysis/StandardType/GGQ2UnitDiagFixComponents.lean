module

public import CFSG.LocalAnalysis.StandardType.GGQ2UnitRealizationStatements
import CFSG.LocalAnalysis.StandardType.GGQ2UnitDiag
import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompSUTwo
import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitSU
import CFSG.ClassicalGroups.Unitary.Simple
import CFSG.ClassicalGroups.Unitary.Perfect

public section

namespace CFSG.StandardType.GGQ2Frame.UnitPlacement

open CFSG CFSG.Assembly CFSG.StandardType Matrix CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.SectionRank.OddCover (diagHom)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

variable {K : Type} [Field K] [Finite K] {N : ℕ}

private noncomputable def udf_norm (h : UnitaryFieldData 2 1 K)
    (ζ : Multiplicative (ZMod 3) →* Kˣ) (w : UnitRaw.W N) :
    Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K)) :=
  ⟨diagOf ζ w, diagOf_mem_normalizer ζ h w⟩

private noncomputable def udf_S (h : UnitaryFieldData 2 1 K)
    (ζ : Multiplicative (ZMod 3) →* Kˣ) (U : Submodule (ZMod 3) (UnitRaw.Vfull N)) :
    Set (MulAut (LargeEvenProj (unitarySU 2 1 K N))) :=
  {x | ∃ w : UnitRaw.W N, (UnitRaw.oneLine N).mkQ w ∈ U ∧
    x = TableB.projConj (unitarySU 2 1 K N) (udf_norm h ζ w)}

private noncomputable def udf_delta (h : UnitaryFieldData 2 1 K)
    (ζ : Multiplicative (ZMod 3) →* Kˣ) (U : Submodule (ZMod 3) (UnitRaw.Vfull N))
    (x : MulAut (LargeEvenProj (unitarySU 2 1 K N))) : Fin N → Kˣ := by
  classical
  exact if hx : x ∈ udf_S h ζ U then
    fun i => ζ (Multiplicative.ofAdd ((Classical.choose hx) i))
  else 1

omit [Finite K] in
private theorem udf_mem_S_norm (h : UnitaryFieldData 2 1 K)
    (ζ : Multiplicative (ZMod 3) →* Kˣ) {U : Submodule (ZMod 3) (UnitRaw.Vfull N)}
    {w : UnitRaw.W N} (hw : (UnitRaw.oneLine N).mkQ w ∈ U) :
    TableB.projConj (unitarySU 2 1 K N) (udf_norm h ζ w) ∈ udf_S h ζ U :=
  ⟨w, hw, rfl⟩

omit [Finite K] in
private theorem udf_delta_spec (h : UnitaryFieldData 2 1 K)
    (ζ : Multiplicative (ZMod 3) →* Kˣ) {U : Submodule (ZMod 3) (UnitRaw.Vfull N)}
    {x : MulAut (LargeEvenProj (unitarySU 2 1 K N))} (hx : x ∈ udf_S h ζ U) :
    ∃ w : UnitRaw.W N, (UnitRaw.oneLine N).mkQ w ∈ U ∧
      x = TableB.projConj (unitarySU 2 1 K N) (udf_norm h ζ w) ∧
      udf_delta h ζ U x = fun i => ζ (Multiplicative.ofAdd (w i)) := by
  have hxw := Classical.choose_spec hx
  refine ⟨Classical.choose hx, hxw.1, hxw.2, ?_⟩
  unfold udf_delta
  rw [dif_pos hx]

private theorem udf_delta_eq_iff (h : UnitaryFieldData 2 1 K)
    (ζ : Multiplicative (ZMod 3) →* Kˣ) (hK : Nat.card K = 4)
    (hζ : Function.Injective ζ) (hN4 : 4 ≤ N)
    {U : Submodule (ZMod 3) (UnitRaw.Vfull N)}
    {x : MulAut (LargeEvenProj (unitarySU 2 1 K N))} (hx : x ∈ udf_S h ζ U)
    {w : UnitRaw.W N}
    (hxw : x = TableB.projConj (unitarySU 2 1 K N) (udf_norm h ζ w)) (i j : Fin N) :
    udf_delta h ζ U x i = udf_delta h ζ U x j ↔ w i = w j := by
  obtain ⟨w', hw', hxw', hδ⟩ := udf_delta_spec h ζ hx
  have hEq : (UnitRaw.oneLine N).mkQ w' = (UnitRaw.oneLine N).mkQ w := by
    have h1 : TableB.projConj (unitarySU 2 1 K N) (udf_norm h ζ w') =
        TableB.projConj (unitarySU 2 1 K N) (udf_norm h ζ w) := by
      rw [← hxw', hxw]
    simpa [udf_norm] using (projConj_diagOf_eq_iff ζ h hK hζ hN4 w' w).mp h1
  have h2 := congrArg (UnitRaw.diffFun N i j) hEq
  rw [UnitRaw.diffFun_mk, UnitRaw.diffFun_mk] at h2
  have hdiff : w' i - w' j = w i - w j := h2
  have hζ' : Function.Injective fun z : UnitRaw.F => ζ (Multiplicative.ofAdd z) :=
    fun a b hab => Multiplicative.ofAdd.injective (hζ hab)
  rw [hδ]
  refine (hζ'.eq_iff).trans ?_
  rw [← sub_eq_zero (a := w' i) (b := w' j), ← sub_eq_zero (a := w i) (b := w j), hdiff]

private theorem udf_mem_diagClass_iff (h : UnitaryFieldData 2 1 K)
    (ζ : Multiplicative (ZMod 3) →* Kˣ) (hK : Nat.card K = 4)
    (hζ : Function.Injective ζ) {m : ℕ} (hm : 4 ≤ m + 1)
    (U : Submodule (ZMod 3) (UnitRaw.Vfull (m + 1))) (i j : Fin (m + 1)) :
    j ∈ LinTorus.diagClass (udf_S h ζ U) (udf_delta h ζ U) i ↔
      ∀ u ∈ U, UnitRaw.diffFun (m + 1) i j u = 0 := by
  rw [LinTorus.mem_diagClass]
  constructor
  · intro hd u hu
    obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective (UnitRaw.oneLine (m + 1)) u
    have hxS := udf_mem_S_norm h ζ hu
    have h1 := hd _ hxS
    have h2 := (udf_delta_eq_iff h ζ hK hζ hm hxS rfl i j).mp h1.symm
    rw [UnitRaw.diffFun_mk, sub_eq_zero]
    exact h2
  · intro hd x hx
    obtain ⟨w, hw, -, hδ⟩ := udf_delta_spec h ζ hx
    have h1 := hd ((UnitRaw.oneLine (m + 1)).mkQ w) hw
    rw [UnitRaw.diffFun_mk, sub_eq_zero] at h1
    rw [hδ]
    show ζ (Multiplicative.ofAdd (w j)) = ζ (Multiplicative.ofAdd (w i))
    rw [h1]

private theorem udf_occurs_diagClass (h : UnitaryFieldData 2 1 K)
    (ζ : Multiplicative (ZMod 3) →* Kˣ) (hK : Nat.card K = 4)
    (hζ : Function.Injective ζ) {m : ℕ} (hm : 4 ≤ m + 1)
    (U : Submodule (ZMod 3) (UnitRaw.Vfull (m + 1))) (i : Fin (m + 1)) :
    UnitRaw.occurs U (LinTorus.diagClass (udf_S h ζ U) (udf_delta h ζ U) i) := by
  refine ⟨⟨i, LinTorus.self_mem_diagClass _ _ _⟩, fun i' hi' j => ?_⟩
  rw [udf_mem_diagClass_iff h ζ hK hζ hm]
  constructor
  · intro hj u hu
    obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective (UnitRaw.oneLine (m + 1)) u
    have h1 := (udf_mem_diagClass_iff h ζ hK hζ hm U i i').mp hi'
      ((UnitRaw.oneLine (m + 1)).mkQ w) hu
    rw [UnitRaw.diffFun_mk, sub_eq_zero] at h1
    have h2 := hj ((UnitRaw.oneLine (m + 1)).mkQ w) hu
    rw [UnitRaw.diffFun_mk, sub_eq_zero] at h2
    rw [UnitRaw.diffFun_mk, sub_eq_zero]
    exact h1.symm.trans h2
  · intro hj u hu
    obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective (UnitRaw.oneLine (m + 1)) u
    have h1 := (udf_mem_diagClass_iff h ζ hK hζ hm U i i').mp hi'
      ((UnitRaw.oneLine (m + 1)).mkQ w) hu
    rw [UnitRaw.diffFun_mk, sub_eq_zero] at h1
    have h2 := hj ((UnitRaw.oneLine (m + 1)).mkQ w) hu
    rw [UnitRaw.diffFun_mk, sub_eq_zero] at h2
    rw [UnitRaw.diffFun_mk, sub_eq_zero]
    exact h1.trans h2

private theorem udf_diagClass_eq_of_occurs (h : UnitaryFieldData 2 1 K)
    (ζ : Multiplicative (ZMod 3) →* Kˣ) (hK : Nat.card K = 4)
    (hζ : Function.Injective ζ) {m : ℕ} (hm : 4 ≤ m + 1)
    {U : Submodule (ZMod 3) (UnitRaw.Vfull (m + 1))} {S' : Finset (Fin (m + 1))}
    (hocc : UnitRaw.occurs U S') {i : Fin (m + 1)} (hi : i ∈ S') :
    LinTorus.diagClass (udf_S h ζ U) (udf_delta h ζ U) i = S' := by
  ext j
  rw [udf_mem_diagClass_iff h ζ hK hζ hm]
  exact (hocc.2 i hi j).symm

private lemma udf_four_le_card_blockSU {K : Type} [Field K] {m : ℕ} {G : Type} [Group G]
    [Finite G] (h : UnitaryFieldData 2 1 K)
    {ψ : ↥(unitarySU 2 1 K (m + 1)) →* G} {S : Set G} {δ : G → Fin (m + 1) → Kˣ}
    {J : Subgroup G} (hJ : IsComponentOf J (ψ.range ⊓ Subgroup.centralizer S))
    {i : Fin (m + 1)}
    (hJI : J ≤ (TableBUE.blockSU (K := K) (n := 1) (LinTorus.diagClass S δ i)).map ψ) :
    4 ≤ (LinTorus.diagClass S δ i).card := by
  by_contra hlt
  have hk1 : 1 ≤ (LinTorus.diagClass S δ i).card :=
    Finset.card_pos.mpr ⟨i, LinTorus.self_mem_diagClass S δ i⟩
  have hk3 : (LinTorus.diagClass S δ i).card ≤ 3 := by omega
  have hsolvSU : Group.IsSolvable ↥(unitarySU 2 1 K (LinTorus.diagClass S δ i).card) :=
    WitSU.isSolvable_unitarySU_two_one h hk1 hk3
  let eI := TableBUE.blockSUEquiv (K := K) (n := 1) (LinTorus.diagClass S δ i) h
  have hsolvB : Group.IsSolvable
      ↥(TableBUE.blockSU (K := K) (n := 1) (LinTorus.diagClass S δ i)) :=
    Group.isSolvable_of_isSolvable_injective (f := eI.symm.toMonoidHom)
      (fun x y hxy => eI.symm.injective hxy)
  have hsolv : Group.IsSolvable
      ↥((TableBUE.blockSU (K := K) (n := 1) (LinTorus.diagClass S δ i)).map ψ) := by
    have hres := Group.isSolvable_of_surjective
      (f := (ψ.comp (TableBUE.blockSU (K := K) (n := 1)
        (LinTorus.diagClass S δ i)).subtype).rangeRestrict)
      (MonoidHom.rangeRestrict_surjective _)
    rwa [MonoidHom.range_comp, Subgroup.range_subtype] at hres
  have hsmap : Group.IsSolvable
      ↥((TableBUE.blockSU (K := K) (n := 1) (LinTorus.diagClass S δ i)).map ψ) := hsolv
  have hsolvJ : Group.IsSolvable ↥J := by
    let eJ := Subgroup.subgroupOfEquivOfLe hJI
    have hsolvJsub : Group.IsSolvable ↥(J.subgroupOf
        ((TableBUE.blockSU (K := K) (n := 1) (LinTorus.diagClass S δ i)).map ψ)) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (J.subgroupOf ((TableBUE.blockSU (K := K) (n := 1)
          (LinTorus.diagClass S δ i)).map ψ)).subtype)
        (fun x y hxy => Subtype.ext hxy)
    exact Group.isSolvable_of_surjective (f := eJ.toMonoidHom) (fun z => ⟨eJ.symm z, by simp⟩)
  have hperfJ : Group.IsPerfect ↥J := ⟨hJ.2.2.1⟩
  have hntrivJ : Nontrivial ↥J := CFSG.ComponentClassification.Quasisimple.nontrivial hJ.2.2
  exact @Group.IsPerfect.not_isSolvable ↥J _ hntrivJ hperfJ hsolvJ

private theorem udf_aut_mul_conj_mul_inv {P : Type} [Group P] (x : MulAut P) (g : P) :
    x * MulAut.conj g * x⁻¹ = MulAut.conj (x g) := by
  ext y
  simp [MulAut.conj_apply]

private noncomputable def udf_psi :
    ↥(unitarySU 2 1 K N) →* MulAut (LargeEvenProj (unitarySU 2 1 K N)) :=
  (MulAut.conj : LargeEvenProj (unitarySU 2 1 K N) →*
    MulAut (LargeEvenProj (unitarySU 2 1 K N))).comp
    (LargeEvenProjMk (unitarySU 2 1 K N))

omit [Finite K] in
private theorem udf_suPairs_norm (h : UnitaryFieldData 2 1 K)
    (ζ : Multiplicative (ZMod 3) →* Kˣ) (w : UnitRaw.W N) :
    (TableB.projConj (unitarySU 2 1 K N) (udf_norm h ζ w),
      diagHom N (fun i => ζ (Multiplicative.ofAdd (w i)))) ∈
      SUTorus.suPairs (udf_psi (K := K) (N := N)) := by
  refine ⟨?_, ?_⟩
  · simpa [diagOf] using diagOf_mem_normalizer ζ h w
  · intro u v huv
    have h1 : (TableB.projConj (unitarySU 2 1 K N) (udf_norm h ζ w))
        (LargeEvenProjMk (unitarySU 2 1 K N) u) =
        LargeEvenProjMk (unitarySU 2 1 K N) v := by
      have h1' := TableB.projConj_mk (unitarySU 2 1 K N) (udf_norm h ζ w) u
      rw [show (LargeEvenProjMk (unitarySU 2 1 K N) u) =
          (u : LargeEvenProj (unitarySU 2 1 K N)) from rfl, h1']
      exact congrArg (QuotientGroup.mk) (Subtype.ext huv.symm)
    calc TableB.projConj (unitarySU 2 1 K N) (udf_norm h ζ w) *
          udf_psi (K := K) (N := N) u *
          (TableB.projConj (unitarySU 2 1 K N) (udf_norm h ζ w))⁻¹
        = MulAut.conj ((TableB.projConj (unitarySU 2 1 K N) (udf_norm h ζ w))
            (LargeEvenProjMk (unitarySU 2 1 K N) u)) := udf_aut_mul_conj_mul_inv _ _
      _ = MulAut.conj (LargeEvenProjMk (unitarySU 2 1 K N) v) := by rw [h1]
      _ = udf_psi (K := K) (N := N) v := rfl

omit [Finite K] in
private theorem udf_suPairs_delta (h : UnitaryFieldData 2 1 K)
    (ζ : Multiplicative (ZMod 3) →* Kˣ) (U : Submodule (ZMod 3) (UnitRaw.Vfull N)) :
    ∀ e ∈ udf_S h ζ U, (e, diagHom N (udf_delta h ζ U e)) ∈
      SUTorus.suPairs (udf_psi (K := K) (N := N)) := by
  intro e he
  obtain ⟨w, -, rfl, hde⟩ := udf_delta_spec h ζ he
  rw [hde]
  exact udf_suPairs_norm h ζ w

private theorem udf_center_eq_bot (hK : Nat.card K = 4) (hN : 4 ≤ N) :
    Subgroup.center (LargeEvenProj (unitarySU 2 1 K N)) = ⊥ := by
  have hK' : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  have hnq : (N, 2 ^ 1) ≠ (3, 2) := by
    intro hc
    have h := congrArg Prod.fst hc
    simp only at h
    omega
  have hsimple : IsSimpleGroup (LargeEvenProj (unitarySU 2 1 K N)) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K 2 1 hK' N (by omega) hnq
  have hperfSU : Group.IsPerfect ↥(unitarySU 2 1 K N) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU (K := K) (p := 2) (f := 1) hK'
      (n := N) (by omega) hnq
  have hperf : Group.IsPerfect (LargeEvenProj (unitarySU 2 1 K N)) :=
    @Group.IsPerfect.ofSurjective _ _ _ _ (LargeEvenProjMk (unitarySU 2 1 K N)) hperfSU
      (QuotientGroup.mk'_surjective _)
  have hntriv : Nontrivial (LargeEvenProj (unitarySU 2 1 K N)) := hsimple.toNontrivial
  have hnab := @Group.IsPerfect.not_isMulCommutative (LargeEvenProj (unitarySU 2 1 K N)) _ hntriv hperf
  have hnab' : ∃ a b : LargeEvenProj (unitarySU 2 1 K N), a * b ≠ b * a := by
    by_contra h
    refine hnab (IsMulCommutative.mk (Std.Commutative.mk ?_))
    intro a b
    by_contra hab
    exact h (show ∃ a b : LargeEvenProj (unitarySU 2 1 K N), a * b ≠ b * a from
      ⟨a, b, hab⟩)
  exact TableBUE.center_eq_bot_of_simple hnab'

private theorem udf_conj_injective (hK : Nat.card K = 4) (hN : 4 ≤ N) :
    Function.Injective (MulAut.conj :
      LargeEvenProj (unitarySU 2 1 K N) →* MulAut (LargeEvenProj (unitarySU 2 1 K N))) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hc : g ∈ Subgroup.center (LargeEvenProj (unitarySU 2 1 K N)) := by
    rw [Subgroup.mem_center_iff]
    intro y
    have h1 := congrArg (fun f : MulAut _ => f y) hg
    simp only [MulAut.one_apply, MulAut.conj_apply] at h1
    have h2 : g * y = y * g := by
      calc g * y = g * y * g⁻¹ * g := by group
        _ = y * g := by rw [h1]
    exact h2.symm
  rwa [udf_center_eq_bot hK hN, Subgroup.mem_bot] at hc

private theorem udf_ker_le_center (hK : Nat.card K = 4) (hN : 4 ≤ N) :
    (udf_psi (K := K) (N := N)).ker ≤ Subgroup.center ↥(unitarySU 2 1 K N) := by
  intro x hx
  have hx' : udf_psi (K := K) (N := N) x = 1 := MonoidHom.mem_ker.mp hx
  have h2 : MulAut.conj (LargeEvenProjMk (unitarySU 2 1 K N) x) =
      MulAut.conj (1 : LargeEvenProj (unitarySU 2 1 K N)) := by
    simpa [udf_psi] using hx'
  have h1 : LargeEvenProjMk (unitarySU 2 1 K N) x = 1 := udf_conj_injective hK hN h2
  have h3 : x ∈ (LargeEvenScalars (Fin N) K).subgroupOf (unitarySU 2 1 K N) :=
    (QuotientGroup.eq_one_iff x).mp h1
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  exact Subgroup.mem_center_iff.mp
    (TableB.scalars_le_center (Subgroup.mem_subgroupOf.mp h3)) (g : GL (Fin N) K)

private theorem udf_conj_comm_iff {P : Type} [Group P]
    (hinj : Function.Injective (MulAut.conj : P →* MulAut P)) (x : MulAut P) (y : P) :
    x * MulAut.conj y = MulAut.conj y * x ↔ x y = y := by
  constructor
  · intro hcomm
    have h1 : x * MulAut.conj y * x⁻¹ = MulAut.conj y := by rw [hcomm]; group
    rw [udf_aut_mul_conj_mul_inv] at h1
    exact hinj h1
  · intro hxy
    have h1 : x * MulAut.conj y * x⁻¹ = MulAut.conj y := by
      rw [udf_aut_mul_conj_mul_inv, hxy]
    calc x * MulAut.conj y = x * MulAut.conj y * x⁻¹ * x := by group
      _ = MulAut.conj y * x := by rw [h1]

omit [Finite K] in
private theorem udf_mem_S_norm' (h : UnitaryFieldData 2 1 K)
    (ζ : Multiplicative (ZMod 3) →* Kˣ) {U : Submodule (ZMod 3) (UnitRaw.Vfull N)}
    {w : UnitRaw.W N} (hw : (UnitRaw.oneLine N).mkQ w ∈ U)
    {hD : diagOf ζ w ∈ Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K))} :
    TableB.projConj (unitarySU 2 1 K N) ⟨diagOf ζ w, hD⟩ ∈ udf_S h ζ U := by
  rw [show (⟨diagOf ζ w, hD⟩ : Subgroup.normalizer _) = udf_norm h ζ w from Subtype.ext rfl]
  exact udf_mem_S_norm h ζ hw

private theorem udf_map_diagFix (h : UnitaryFieldData 2 1 K)
    (ζ : Multiplicative (ZMod 3) →* Kˣ) (hK : Nat.card K = 4) (hN : 4 ≤ N)
    (U : Submodule (ZMod 3) (UnitRaw.Vfull N)) :
    (diagFix ζ N U).map (MulAut.conj :
      LargeEvenProj (unitarySU 2 1 K N) →*
        MulAut (LargeEvenProj (unitarySU 2 1 K N))) =
      (udf_psi (K := K) (N := N)).range ⊓ Subgroup.centralizer (udf_S h ζ U) := by
  have hinj := udf_conj_injective hK hN
  have hrange : (udf_psi (K := K) (N := N)).range =
      (MulAut.conj : LargeEvenProj (unitarySU 2 1 K N) →* _).range := by
    rw [udf_psi, MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _), Subgroup.map_top]
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [hrange]
      exact ⟨y, rfl⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro x hx
      obtain ⟨w, hw, hxw, -⟩ := udf_delta_spec h ζ hx
      rw [hxw]
      exact (udf_conj_comm_iff hinj _ y).mpr
        ((mem_diagFix.mp hy) w hw (udf_norm h ζ w).2)
  · rintro ⟨hzr, hzc⟩
    rw [hrange] at hzr
    obtain ⟨y, rfl⟩ := hzr
    refine ⟨y, (mem_diagFix (ζ := ζ) (N := N) (U := U)).mpr ?_, rfl⟩
    intro w hw hD
    exact (udf_conj_comm_iff hinj _ y).mp
      ((Subgroup.mem_centralizer_iff.mp hzc) _ (udf_mem_S_norm' h ζ hw))

private theorem udf_component_iff_block (h : UnitaryFieldData 2 1 K)
    (ζ : Multiplicative (ZMod 3) →* Kˣ) (hK : Nat.card K = 4) {m : ℕ}
    (hm : 5 ≤ m + 1) (U : Submodule (ZMod 3) (UnitRaw.Vfull (m + 1)))
    (J : Subgroup (MulAut (LargeEvenProj (unitarySU 2 1 K (m + 1))))) :
    IsComponentOf J ((udf_psi (K := K) (N := m + 1)).range ⊓
        Subgroup.centralizer (udf_S h ζ U)) ↔
      ∃ i : Fin (m + 1),
        4 ≤ (LinTorus.diagClass (udf_S h ζ U) (udf_delta h ζ U) i).card ∧
          J = (TableBUE.blockSU (K := K) (n := 1)
            (LinTorus.diagClass (udf_S h ζ U) (udf_delta h ζ U) i)).map
            (udf_psi (K := K) (N := m + 1)) := by
  have hker := udf_ker_le_center (K := K) (N := m + 1) hK (by omega)
  have hδ := udf_suPairs_delta (K := K) (N := m + 1) h ζ U
  have hq : ∀ i : Fin (m + 1),
      4 ≤ (LinTorus.diagClass (udf_S h ζ U) (udf_delta h ζ U) i).card →
      CFSG.Assembly.IsQuasisimple ↥((TableBUE.blockSU (K := K) (n := 1)
        (LinTorus.diagClass (udf_S h ζ U) (udf_delta h ζ U) i)).map
        (udf_psi (K := K) (N := m + 1))) := by
    intro i hi
    refine SUTorus.isQuasisimple_map_blockSU h hker (by omega) ?_
    intro hc
    have h1 := congrArg Prod.fst hc
    simp only at h1
    omega
  have hsub : ∀ i : Fin (m + 1),
      IsSubnormal ((TableBUE.blockSU (K := K) (n := 1)
        (LinTorus.diagClass (udf_S h ζ U) (udf_delta h ζ U) i)).map
        (udf_psi (K := K) (N := m + 1)))
        ((udf_psi (K := K) (N := m + 1)).range ⊓
          Subgroup.centralizer (udf_S h ζ U)) :=
    fun i => SUTorus.isSubnormal_map_blockSU hker hδ i
  constructor
  · intro hJ
    obtain ⟨i, hJI⟩ := SUTorus.exists_le_map_blockSU h Nat.prime_three (by norm_num) hker hδ hJ
    have hcard := udf_four_le_card_blockSU h hJ hJI
    have hB : IsComponentOf ((TableBUE.blockSU (K := K) (n := 1)
        (LinTorus.diagClass (udf_S h ζ U) (udf_delta h ζ U) i)).map
        (udf_psi (K := K) (N := m + 1)))
        ((udf_psi (K := K) (N := m + 1)).range ⊓
          Subgroup.centralizer (udf_S h ζ U)) :=
      ⟨isSubnormal_le_of_assembly (hsub i), hsub i, hq i hcard⟩
    exact ⟨i, hcard, CFSG.LocalAnalysis.ComponentInitial.eq_of_isComponentOf_le hJ hB hJI⟩
  · rintro ⟨i, hcard, rfl⟩
    exact ⟨isSubnormal_le_of_assembly (hsub i), hsub i, hq i hcard⟩

theorem unitIsComponentOfDiagFixIff_holds : UnitIsComponentOfDiagFixIff := by
  intro K _ _ ζ N hK hζ hN U Y
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  have hm5 : 5 ≤ m + 1 := hN
  have hm4 : 4 ≤ m + 1 := by omega
  have hfield : UnitaryFieldData 2 1 K :=
    TableBU.unitaryFieldData_of_card (by rw [hK]; norm_num) le_rfl
  have hinj := udf_conj_injective (K := K) (N := m + 1) hK hm4
  have hmap := udf_map_diagFix (K := K) (N := m + 1) hfield ζ hK hm4 U
  have hcomp := udf_component_iff_block (K := K) hfield ζ hK hm5 U
  constructor
  · intro hY
    have hY' : IsComponentOf (Y.map (MulAut.conj :
        LargeEvenProj (unitarySU 2 1 K (m + 1)) →*
          MulAut (LargeEvenProj (unitarySU 2 1 K (m + 1)))))
        ((diagFix ζ (m + 1) U).map (MulAut.conj :
          LargeEvenProj (unitarySU 2 1 K (m + 1)) →*
            MulAut (LargeEvenProj (unitarySU 2 1 K (m + 1))))) :=
      (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff hinj).mpr hY
    rw [hmap] at hY'
    obtain ⟨i, hcard, hYeq⟩ := (hcomp (Y.map (MulAut.conj :
      LargeEvenProj (unitarySU 2 1 K (m + 1)) →* _))).mp hY'
    refine ⟨LinTorus.diagClass (udf_S hfield ζ U) (udf_delta hfield ζ U) i, hcard,
      udf_occurs_diagClass hfield ζ hK hζ hm4 U i, ?_⟩
    have hb : (TableBUE.blockSU (K := K) (n := 1)
        (LinTorus.diagClass (udf_S hfield ζ U) (udf_delta hfield ζ U) i)).map
          (udf_psi (K := K) (N := m + 1)) =
        (blockPSU (K := K) (N := m + 1)
          (LinTorus.diagClass (udf_S hfield ζ U) (udf_delta hfield ζ U) i)).map
          (MulAut.conj : LargeEvenProj (unitarySU 2 1 K (m + 1)) →* _) := by
      simp only [blockPSU, udf_psi, Subgroup.map_map]
    rw [hb] at hYeq
    exact Subgroup.map_injective hinj hYeq
  · rintro ⟨S', hadm, hocc, rfl⟩
    obtain ⟨i, hi⟩ := hocc.1
    have hI : LinTorus.diagClass (udf_S hfield ζ U) (udf_delta hfield ζ U) i = S' :=
      udf_diagClass_eq_of_occurs hfield ζ hK hζ hm4 hocc hi
    have hcomp' : IsComponentOf ((TableBUE.blockSU (K := K) (n := 1)
        (LinTorus.diagClass (udf_S hfield ζ U) (udf_delta hfield ζ U) i)).map
          (udf_psi (K := K) (N := m + 1)))
        ((udf_psi (K := K) (N := m + 1)).range ⊓
          Subgroup.centralizer (udf_S hfield ζ U)) :=
      (hcomp _).mpr ⟨i, by rw [hI]; exact hadm, rfl⟩
    have hb : (TableBUE.blockSU (K := K) (n := 1)
        (LinTorus.diagClass (udf_S hfield ζ U) (udf_delta hfield ζ U) i)).map
          (udf_psi (K := K) (N := m + 1)) =
        (blockPSU (K := K) (N := m + 1) S').map
          (MulAut.conj : LargeEvenProj (unitarySU 2 1 K (m + 1)) →* _) := by
      rw [← hI]
      simp only [blockPSU, udf_psi, Subgroup.map_map]
    have h1 : IsComponentOf ((blockPSU (K := K) (N := m + 1) S').map
          (MulAut.conj : LargeEvenProj (unitarySU 2 1 K (m + 1)) →* _))
        ((diagFix ζ (m + 1) U).map (MulAut.conj :
          LargeEvenProj (unitarySU 2 1 K (m + 1)) →* _)) := by
      rw [hmap, ← hb]
      exact hcomp'
    exact (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff hinj).mp h1

end

end CFSG.StandardType.GGQ2Frame.UnitPlacement

end
