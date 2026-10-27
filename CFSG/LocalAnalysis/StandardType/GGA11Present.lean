module

public import CFSG.LocalAnalysis.StandardType.GGA11Defs
public import CFSG.LocalAnalysis.StandardType.GGA11Levi4
public import CFSG.LocalAnalysis.StandardType.GGPropFiveTwentyOneTypeA
public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofCoxeter

public section

open CFSG CFSG.Assembly CFSG.StandardType Matrix CFSG.LieType.Universal
  CFSG.LieType.Universal.SpecialLinear CFSG.LieType.RootSystem

namespace CFSG.StandardType.A11

private theorem test_ext9_swap (i j : Fin 9) :
    ext9 (Equiv.swap i j) =
      Equiv.swap (Fin.castLEEmb (by omega : 9 ≤ 12) i)
        (Fin.castLEEmb (by omega : 9 ≤ 12) j) := by
  ext x
  rw [show ext9 (Equiv.swap i j) =
    (Equiv.swap i j).viaFintypeEmbedding (Fin.castLEEmb (by omega : 9 ≤ 12)) from rfl]
  by_cases hx : x ∈ Set.range (Fin.castLEEmb (by omega : 9 ≤ 12) : Fin 9 → Fin 12)
  · obtain ⟨a, rfl⟩ := hx
    rw [Equiv.Perm.viaFintypeEmbedding_apply_image]
    rcases eq_or_ne a i with rfl | hai
    · simp
    rcases eq_or_ne a j with rfl | haj
    · simp
    · rw [Equiv.swap_apply_of_ne_of_ne hai haj,
        Equiv.swap_apply_of_ne_of_ne
          (fun h => hai ((Fin.castLEEmb (by omega : 9 ≤ 12)).injective h))
          (fun h => haj ((Fin.castLEEmb (by omega : 9 ≤ 12)).injective h))]
  · have h1 : x ≠ Fin.castLEEmb (by omega : 9 ≤ 12) i := fun h => hx ⟨i, h.symm⟩
    have h2 : x ≠ Fin.castLEEmb (by omega : 9 ≤ 12) j := fun h => hx ⟨j, h.symm⟩
    rw [Equiv.Perm.viaFintypeEmbedding_apply_notMem_range (e := Equiv.swap i j)
      (f := Fin.castLEEmb (by omega : 9 ≤ 12)) hx,
      Equiv.swap_apply_of_ne_of_ne h1 h2]

private theorem test_permSL_swap_adj (n : ℕ) (k : Fin n) :
    permSL n (Equiv.swap k.castSucc k.succ) = weylRep n F2 k := by
  rw [permSL, MonoidHom.comp_apply]
  rw [show typeAWeylHom n (Equiv.swap k.castSucc k.succ) =
    typeAWeylEquiv n (Equiv.swap k.castSucc k.succ) from rfl]
  rw [typeAWeylEquiv_swap]
  exact slWeylLift_simple n two_eq_zero k

private theorem test_slBlockHom₃_weylRep (k : Fin 8) :
    slBlockHom₃ 8 F2 (weylRep 8 F2 k) = weylRep 11 F2 (k.castSucc.castSucc.castSucc) := by
  rw [slBlockHom₃_apply, slBlockHom₂_weylRep, slBlockHom_weylRep]

private theorem test_slBlock₃_permSL_last :
    slBlockHom₃ 8 F2 (permSL 8 (Equiv.swap (7 : Fin 9) (8 : Fin 9))) =
      permSL 11 (ext9 (Equiv.swap (7 : Fin 9) (8 : Fin 9))) := by
  rw [show (Equiv.swap (7 : Fin 9) (8 : Fin 9)) =
    Equiv.swap (⟨7, by norm_num⟩ : Fin 8).castSucc (⟨7, by norm_num⟩ : Fin 8).succ from rfl,
    test_permSL_swap_adj 8 ⟨7, by norm_num⟩, test_slBlockHom₃_weylRep]
  rw [test_ext9_swap]
  have hsw : Equiv.swap (Fin.castLEEmb (by omega : 9 ≤ 12) ((⟨7, by norm_num⟩ : Fin 8).castSucc))
      (Fin.castLEEmb (by omega : 9 ≤ 12) ((⟨7, by norm_num⟩ : Fin 8).succ)) =
      Equiv.swap (⟨7, by norm_num⟩ : Fin 11).castSucc (⟨7, by norm_num⟩ : Fin 11).succ := by
    congr 1 <;> exact Fin.ext rfl
  rw [hsw, test_permSL_swap_adj 11 ⟨7, by norm_num⟩]
  congr 1

private noncomputable def a11pGen : Subgroup (SL 9) :=
  Subgroup.closure (Set.range (slBlockHom 7 F2) ∪
    {permSL 8 (Equiv.swap (7 : Fin 9) (8 : Fin 9))})

private theorem a11pGen_le_of_lt (k : Fin 8) (hk : k.val < 7) (s : Bool) :
    fundamentalRootSubgroup 8 F2 k s ≤ a11pGen := by
  intro x hx
  apply Subgroup.subset_closure
  left
  let k' : Fin 7 := ⟨k.val, hk⟩
  cases s
  · obtain ⟨c, rfl⟩ := (mem_rootSubgroup (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne' x).mp hx
    refine ⟨SpecialLinearGroup.transvection
      (show k'.castSucc < k'.succ from Fin.castSucc_lt_succ).ne' c, ?_⟩
    rw [slBlockHom_transvection]
  · obtain ⟨c, rfl⟩ := (mem_rootSubgroup (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne x).mp hx
    refine ⟨SpecialLinearGroup.transvection
      (show k'.castSucc < k'.succ from Fin.castSucc_lt_succ).ne c, ?_⟩
    rw [slBlockHom_transvection]

private theorem a11pGen_mem_zero {i j : Fin 9} (hij : i ≠ j) :
    SpecialLinearGroup.transvection hij (0 : F2) ∈ a11pGen := by
  have hzero : SpecialLinearGroup.transvection hij (0 : F2) = 1 := by
    apply Subtype.ext
    simp [SpecialLinearGroup.transvection_coe, Matrix.transvection]
  rw [hzero]
  exact one_mem _

private theorem a11pGen_permSL_mem :
    permSL 8 (Equiv.swap (7 : Fin 9) (8 : Fin 9)) ∈ a11pGen :=
  Subgroup.subset_closure (Or.inr rfl)

private theorem a11pGen_weylRep_mem :
    weylRep 8 F2 (⟨7, by omega⟩ : Fin 8) ∈ a11pGen := by
  rw [← test_permSL_swap_adj 8 (⟨7, by omega⟩ : Fin 8)]
  exact a11pGen_permSL_mem

private theorem a11pGen_coe_signedPerm :
    ((permSL 8 (Equiv.swap (7 : Fin 9) (8 : Fin 9)) : SL 9) :
      Matrix (Fin 9) (Fin 9) F2) = signedPerm (Equiv.swap (7 : Fin 9) (8 : Fin 9)) 1 := by
  rw [show (Equiv.swap (7 : Fin 9) (8 : Fin 9)) =
    Equiv.swap (⟨7, by norm_num⟩ : Fin 8).castSucc (⟨7, by norm_num⟩ : Fin 8).succ from rfl,
    test_permSL_swap_adj 8 ⟨7, by norm_num⟩]
  exact coe_weylRep_of_two 8 two_eq_zero ⟨7, by norm_num⟩

private theorem transvection_irrel {i j : Fin 9} (h1 h2 : i ≠ j) (c : F2) :
    SpecialLinearGroup.transvection h1 c = SpecialLinearGroup.transvection h2 c := by
  apply Subtype.ext
  rfl

private theorem a11pGen_last_mem_true :
    SpecialLinearGroup.transvection
      (show (⟨7, by omega⟩ : Fin 8).castSucc < (⟨7, by omega⟩ : Fin 8).succ from
        Fin.castSucc_lt_succ).ne (1 : F2) ∈ a11pGen := by
  open scoped commutatorElement in
  have hn := a11pGen_permSL_mem
  have h76 : SpecialLinearGroup.transvection
      (show (7 : Fin 9) ≠ (6 : Fin 9) by decide) (1 : F2) ∈ a11pGen := by
    have h := a11pGen_le_of_lt ⟨6, by norm_num⟩ (by norm_num) false
      (transvection_mem_rootSubgroup _ (1 : F2))
    convert h using 2
  have h67 : SpecialLinearGroup.transvection
      (show (6 : Fin 9) ≠ (7 : Fin 9) by decide) (1 : F2) ∈ a11pGen := by
    have h := a11pGen_le_of_lt ⟨6, by norm_num⟩ (by norm_num) true
      (transvection_mem_rootSubgroup _ (1 : F2))
    convert h using 2
  have key := conj_transvection_of_coe_eq_signedPerm (g :=
    permSL 8 (Equiv.swap (7 : Fin 9) (8 : Fin 9))) (π := Equiv.swap (7 : Fin 9) (8 : Fin 9))
    (ε := fun _ => (1 : F2)) a11pGen_coe_signedPerm (fun _ => by simp)
    (show (6 : Fin 9) ≠ (7 : Fin 9) by decide) (1 : F2)
  rw [mul_one, mul_one] at key
  have hz : SpecialLinearGroup.transvection
      (show (6 : Fin 9) ≠ (8 : Fin 9) by decide) (1 : F2) ∈ a11pGen := by
    rw [show SpecialLinearGroup.transvection (show (6 : Fin 9) ≠ (8 : Fin 9) by decide) (1 : F2) =
      SpecialLinearGroup.transvection ((Equiv.swap (7 : Fin 9) (8 : Fin 9)).injective.ne
        (show (6 : Fin 9) ≠ (7 : Fin 9) by decide)) (1 : F2) from transvection_irrel _ _ 1, ← key]
    exact mul_mem (mul_mem hn h67) (inv_mem hn)
  have hkey := Matrix.SpecialLinearGroup.commutatorElement_transvection
    (show (7 : Fin 9) ≠ (6 : Fin 9) by decide)
    (show (6 : Fin 9) ≠ (8 : Fin 9) by decide)
    (show (7 : Fin 9) ≠ (8 : Fin 9) by decide) (1 : F2) (1 : F2)
  rw [mul_one] at hkey
  rw [show SpecialLinearGroup.transvection
      (show (⟨7, by omega⟩ : Fin 8).castSucc < (⟨7, by omega⟩ : Fin 8).succ from
        Fin.castSucc_lt_succ).ne (1 : F2) =
      SpecialLinearGroup.transvection (show (7 : Fin 9) ≠ (8 : Fin 9) by decide) (1 : F2)
      from transvection_irrel _ _ 1, ← hkey]
  exact Subgroup.commutator_le_self a11pGen (Subgroup.commutator_mem_commutator h76 hz)

private theorem a11pGen_last_mem_false :
    SpecialLinearGroup.transvection
      (show (⟨7, by omega⟩ : Fin 8).castSucc < (⟨7, by omega⟩ : Fin 8).succ from
        Fin.castSucc_lt_succ).ne' (1 : F2) ∈ a11pGen := by
  have hn := a11pGen_permSL_mem
  have h78 : SpecialLinearGroup.transvection
      (show (7 : Fin 9) ≠ (8 : Fin 9) by decide) (1 : F2) ∈ a11pGen := a11pGen_last_mem_true
  have key := conj_transvection_of_coe_eq_signedPerm (g :=
    permSL 8 (Equiv.swap (7 : Fin 9) (8 : Fin 9))) (π := Equiv.swap (7 : Fin 9) (8 : Fin 9))
    (ε := fun _ => (1 : F2)) a11pGen_coe_signedPerm (fun _ => by simp)
    (show (7 : Fin 9) ≠ (8 : Fin 9) by decide) (1 : F2)
  rw [mul_one, mul_one] at key
  rw [show SpecialLinearGroup.transvection
      (show (⟨7, by omega⟩ : Fin 8).castSucc < (⟨7, by omega⟩ : Fin 8).succ from
        Fin.castSucc_lt_succ).ne' (1 : F2) =
      SpecialLinearGroup.transvection ((Equiv.swap (7 : Fin 9) (8 : Fin 9)).injective.ne
        (show (7 : Fin 9) ≠ (8 : Fin 9) by decide)) (1 : F2)
      from transvection_irrel _ _ 1, ← key]
  exact mul_mem (mul_mem hn h78) (inv_mem hn)

private theorem a11pGen_le_last (s : Bool) :
    fundamentalRootSubgroup 8 F2 (⟨7, by omega⟩ : Fin 8) s ≤ a11pGen := by
  intro x hx
  have hcard : Nat.card F2 = 2 := by
    rw [GaloisField.card 2 1 (by omega)]; norm_num
  obtain ⟨y, hy, huniq⟩ := (Nat.card_eq_two_iff' (0 : F2)).mp hcard
  have hy1 : y = 1 := (huniq 1 (by norm_num)).symm
  cases s
  · obtain ⟨c, rfl⟩ := (mem_rootSubgroup
      (show (⟨7, by omega⟩ : Fin 8).castSucc < (⟨7, by omega⟩ : Fin 8).succ from
        Fin.castSucc_lt_succ).ne' x).mp hx
    by_cases h0 : c = 0
    · rw [h0]
      exact a11pGen_mem_zero _
    · have hc1 : c = 1 := by rw [← hy1]; exact huniq c h0
      rw [hc1]
      exact a11pGen_last_mem_false
  · obtain ⟨c, rfl⟩ := (mem_rootSubgroup
      (show (⟨7, by omega⟩ : Fin 8).castSucc < (⟨7, by omega⟩ : Fin 8).succ from
        Fin.castSucc_lt_succ).ne x).mp hx
    by_cases h0 : c = 0
    · rw [h0]
      exact a11pGen_mem_zero _
    · have hc1 : c = 1 := by rw [← hy1]; exact huniq c h0
      rw [hc1]
      exact a11pGen_last_mem_true

private theorem a11pGen_eq_top : a11pGen = ⊤ := by
  rw [eq_top_iff, ← SpecialLinear.iSup_fundamentalRootSubgroup_eq_top (m := 8) (F := F2)]
  refine iSup_le fun k => iSup_le fun s => ?_
  fin_cases k
  · exact a11pGen_le_of_lt _ (by norm_num) s
  · exact a11pGen_le_of_lt _ (by norm_num) s
  · exact a11pGen_le_of_lt _ (by norm_num) s
  · exact a11pGen_le_of_lt _ (by norm_num) s
  · exact a11pGen_le_of_lt _ (by norm_num) s
  · exact a11pGen_le_of_lt _ (by norm_num) s
  · exact a11pGen_le_of_lt _ (by norm_num) s
  · exact a11pGen_le_last s

private theorem test_hspecial {G : Type} [Group G] (φ₃ : SL 9 →* G)
    (ρ : Equiv.Perm (Fin 12) →* G) (hρ : RhoOn9 φ₃ ρ)
    (j : Fin 11) (hj : j ∈ typeALeviJ 11 8) :
    ggExt (typeALeviHom4 (φ₃.comp (slBlockHom 7 F2))) (weylRep 11 F2 j) =
      ρ (Equiv.swap j.castSucc j.succ) := by
  have hj7 : j.val < 7 := by
    have := (Finset.mem_filter.mp hj).2
    omega
  let j' : Fin 7 := ⟨j.val, hj7⟩
  have hj_eq : j'.castSucc.castSucc.castSucc.castSucc = j := Fin.ext rfl
  have hweyl : weylRep 11 F2 j = slBlock84 (weylRep 7 F2 j') := by
    rw [← hj_eq, ← slBlock84_weylRep]
  calc
    ggExt (typeALeviHom4 (φ₃.comp (slBlockHom 7 F2))) (weylRep 11 F2 j)
        = ggExt (typeALeviHom4 (φ₃.comp (slBlockHom 7 F2)))
            (slBlock84 (weylRep 7 F2 j')) := by rw [hweyl]
    _ = (φ₃.comp (slBlockHom 7 F2)) (weylRep 7 F2 j') :=
          ggExt_typeALeviHom4 _ _
    _ = φ₃ (slBlockHom 7 F2 (weylRep 7 F2 j')) := rfl
    _ = φ₃ (weylRep 8 F2 j'.castSucc) := by rw [slBlockHom_weylRep]
    _ = φ₃ (permSL 8 (Equiv.swap (j'.castSucc.castSucc) (j'.castSucc.succ))) := by
          rw [test_permSL_swap_adj]
    _ = ρ (ext9 (Equiv.swap (j'.castSucc.castSucc) (j'.castSucc.succ))) :=
          (hρ _).symm
    _ = ρ (Equiv.swap j.castSucc j.succ) := by
          rw [test_ext9_swap]
          congr 1

private theorem test_ggExt_transvection {G : Type} [Group G] (φ₃ : SL 9 →* G)
    {a b : Fin 12} (ha : a.val < 8) (hb : b.val < 8) (hab : a ≠ b) (c : F2) :
    ggExt (typeALeviHom4 (φ₃.comp (slBlockHom 7 F2)))
      (SpecialLinearGroup.transvection hab c) =
      φ₃ (SpecialLinearGroup.transvection
        (show (⟨a.val, by omega⟩ : Fin 9) ≠ ⟨b.val, by omega⟩ from
          fun h => hab (Fin.ext (by simpa using congrArg Fin.val h))) c) := by
  let a9 : Fin 9 := ⟨a.val, by omega⟩
  let b9 : Fin 9 := ⟨b.val, by omega⟩
  have hab9 : a9 ≠ b9 := fun h => hab (Fin.ext (by simpa [a9, b9] using congrArg Fin.val h))
  let a' : Fin 8 := ⟨a.val, ha⟩
  let b' : Fin 8 := ⟨b.val, hb⟩
  have hab' : a' ≠ b' := fun h => hab (Fin.ext (by simpa [a', b'] using congrArg Fin.val h))
  have htrans : SpecialLinearGroup.transvection hab c =
      slBlock84 (SpecialLinearGroup.transvection hab' c) := by
    rw [slBlock84_transvection]
  rw [htrans, ggExt_typeALeviHom4, MonoidHom.comp_apply, slBlockHom_transvection]

private theorem test_transvection_ne_one {i j : Fin 9} (hij : i ≠ j) :
    SpecialLinearGroup.transvection hij (1 : F2) ≠ 1 := by
  intro h
  have hc := congrArg (fun g : SL 9 => (g : Matrix (Fin 9) (Fin 9) F2) i j) h
  rw [SpecialLinearGroup.transvection_coe] at hc
  simp [Matrix.transvection] at hc

private theorem test_hnt {G : Type} [Group G] (φ₃ : SL 9 →* G) (hφ : Function.Injective φ₃) :
    ∃ γ ∈ ggSupp (rootDatum 11 F2) (typeALeviJ 11 8),
      ∃ z ∈ rootGroup 11 F2 γ,
        ggExt (typeALeviHom4 (φ₃.comp (slBlockHom 7 F2))) z ≠ 1 := by
  refine ⟨Pi.single (⟨0, by omega⟩ : Fin 11) 1,
    single_mem_ggSupp (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp⟩), ?_⟩
  refine ⟨SpecialLinearGroup.transvection (show (⟨0, by omega⟩ : Fin 12) ≠ (⟨1, by omega⟩ : Fin 12) by decide) (1 : F2), ?_, ?_⟩
  · exact transvection_mem_rootGroup_single (⟨0, by omega⟩ : Fin 11) (by decide) 1
  · rw [test_ggExt_transvection φ₃ (show (⟨0, by omega⟩ : Fin 12).val < 8 by norm_num)
      (show (⟨1, by omega⟩ : Fin 12).val < 8 by norm_num) (by decide) (1 : F2)]
    intro h
    apply test_transvection_ne_one (i := (⟨0, by omega⟩ : Fin 9)) (j := (⟨1, by omega⟩ : Fin 9)) (by decide)
    apply hφ
    rw [h, map_one]

private theorem test_fix_of {w : (coxeterMatrix (isFiniteType_A 11)).Group}
    {π : Equiv.Perm (Fin 12)} (hreal : TypeARealizes 11 w π)
    {γ : Fin 11 → ℤ} {a b : Fin 12} (hab : a ≠ b)
    (hγ : toStd 11 γ = Pi.single a 1 - Pi.single b 1)
    (hfix : weylAction (isFiniteType_A 11) w γ = γ) :
    π a = a ∧ π b = b := by
  have key : ∀ x, toStd 11 γ (π.symm x) = toStd 11 γ x := by
    intro x
    have h := congrFun (hreal γ) x
    rw [hfix] at h
    exact h.symm
  have eval_one : ∀ x, toStd 11 γ x = 1 ↔ x = a := by
    intro x
    rw [hγ]
    simp only [Pi.sub_apply, Pi.single_apply]
    constructor
    · intro h
      by_cases hx : x = a
      · exact hx
      · rw [if_neg hx] at h
        by_cases hb : x = b
        · rw [if_pos hb] at h; norm_num at h
        · rw [if_neg hb] at h; norm_num at h
    · intro hx
      subst hx
      rw [if_pos rfl, if_neg hab]
      norm_num
  have eval_neg : ∀ x, toStd 11 γ x = -1 ↔ x = b := by
    intro x
    rw [hγ]
    simp only [Pi.sub_apply, Pi.single_apply]
    constructor
    · intro h
      by_cases hx : x = b
      · exact hx
      · rw [if_neg hx] at h
        by_cases ha : x = a
        · rw [if_pos ha] at h; norm_num at h
        · rw [if_neg ha] at h; norm_num at h
    · intro hx
      subst hx
      rw [if_neg (Ne.symm hab), if_pos rfl]
      norm_num
  constructor
  · exact (eval_one (π a)).mp (by
      calc toStd 11 γ (π a) = toStd 11 γ (π.symm (π a)) := (key (π a)).symm
        _ = toStd 11 γ a := by rw [Equiv.symm_apply_apply]
        _ = 1 := by rw [hγ]; simp [hab])
  · exact (eval_neg (π b)).mp (by
      calc toStd 11 γ (π b) = toStd 11 γ (π.symm (π b)) := (key (π b)).symm
        _ = toStd 11 γ b := by rw [Equiv.symm_apply_apply]
        _ = -1 := by rw [hγ]; simp [hab])

private theorem test_hcent {G : Type} [Group G] (φ₃ : SL 9 →* G)
    (ρ : Equiv.Perm (Fin 12) →* G) (hstab : RhoStab φ₃ ρ)
    (w : (coxeterMatrix (isFiniteType_A 11)).Group)
    (α : Fin 11 → ℤ) (hα : α ∈ ggSupp (rootDatum 11 F2) (typeALeviJ 11 8))
    (hfix : weylAction (isFiniteType_A 11) w α = α)
    (z : SL 12) (hz : z ∈ rootGroup 11 F2 α) :
    ρ ((typeAWeylEquiv 11).symm w) * ggExt (typeALeviHom4 (φ₃.comp (slBlockHom 7 F2))) z *
      (ρ ((typeAWeylEquiv 11).symm w))⁻¹ =
      ggExt (typeALeviHom4 (φ₃.comp (slBlockHom 7 F2))) z := by
  obtain ⟨a, b, hab, ha, hb, hαab⟩ := typeALevi_root_of_mem 11 F2 hα
  have hreal : TypeARealizes 11 w ((typeAWeylEquiv 11).symm w) := by
    have h := typeAWeylOf_spec 11 ((typeAWeylEquiv 11).symm w)
    have h2 : typeAWeylOf 11 ((typeAWeylEquiv 11).symm w) = w := by
      change (typeAWeylEquiv 11) ((typeAWeylEquiv 11).symm w) = w
      exact MulEquiv.apply_symm_apply (typeAWeylEquiv 11) w
    rwa [h2] at h
  obtain ⟨hπa, hπb⟩ := test_fix_of hreal hab hαab hfix
  have hz' : z ∈ rootSubgroup 11 F2 hab := by
    rw [← rootGroup_eq 11 F2 hab hαab]
    exact hz
  obtain ⟨c, rfl⟩ := (mem_rootSubgroup hab z).mp hz'
  rw [test_ggExt_transvection φ₃ ha hb hab c]
  have hcard : Nat.card F2 = 2 := by
    rw [GaloisField.card 2 1 (by omega)]; norm_num
  obtain ⟨y, hy, huniq⟩ := (Nat.card_eq_two_iff' (0 : F2)).mp hcard
  have hy1 : y = 1 := (huniq 1 (by norm_num)).symm
  rcases (show c = 0 ∨ c = 1 from by
    by_cases h0 : c = 0
    · exact Or.inl h0
    · exact Or.inr (by rw [← hy1]; exact huniq c h0)) with h0 | h1
  · rw [h0]
    have hzero : SpecialLinearGroup.transvection
        (show (⟨a.val, by omega⟩ : Fin 9) ≠ ⟨b.val, by omega⟩ from
          fun h => hab (Fin.ext (by simpa using congrArg Fin.val h))) (0 : F2) = 1 := by
      apply Subtype.ext
      simp [SpecialLinearGroup.transvection_coe, Matrix.transvection]
    rw [hzero, map_one]
    group
  · rw [h1]
    have htv : SpecialLinearGroup.transvection
        (show (⟨a.val, by omega⟩ : Fin 9) ≠ ⟨b.val, by omega⟩ from
          fun h => hab (Fin.ext (by simpa using congrArg Fin.val h))) (1 : F2) = tv9 a b := by
      rw [tv9, dif_pos ⟨by omega, by omega, hab⟩]
    rw [htv, mul_inv_eq_iff_eq_mul]
    exact hstab a b ha hb hab ((typeAWeylEquiv 11).symm w) hπa hπb

theorem a11PresentInput_holds :
    ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
      GGSecFiveRestHyp 7 B Bs x L D J → GGSecFiveA11Config 7 B Bs x L D J →
      ∀ (φ₃ : SL 9 →* G) (ρ : Equiv.Perm (Fin 12) →* G),
        Function.Injective φ₃ → A11RhoCore φ₃ ρ → φ₃.range ≤ ggG0 7 B x L D J →
        ρ.range ≤ ggG0 7 B x L D J → L ≤ Clos φ₃ ρ →
        (∀ (y' : G) (K' : Subgroup G), GGNbr 7 B x D J y' K' → K' ≤ Clos φ₃ ρ) →
        ∃ ψ₀ : (ggU .PSL 12 1).K →* G,
          GGPresentsG0 (ggG0 7 B x L D J) (ggU .PSL 12 1).D .PSL 12 1 ψ₀ ∧
            ∀ s : SL 9, ψ₀ (slBlockHom₃ 8 (GaloisField 2 1) s) = φ₃ s := by
  intro G _ _ B Bs x L D J hRest hConfig φ₃ ρ hφinj hcore hφG hρG hL hK
  obtain ⟨hρinj, hRhoOn9, hRhoStab⟩ := hcore
  let φ : ggSub (rootDatum 11 F2) (ggSupp (rootDatum 11 F2) (typeALeviJ 11 8)) →* G :=
    typeALeviHom4 (φ₃.comp (slBlockHom 7 F2))
  let ρ' : (coxeterMatrix (isFiniteType_A 11)).Group →* G :=
    ρ.comp (typeAWeylEquiv 11).symm.toMonoidHom
  have hρ'inj : Function.Injective ρ' := hρinj.comp (typeAWeylEquiv 11).symm.injective
  have hF : Nat.card F2 = 2 ^ 1 := GaloisField.card 2 1 (by omega)
  have hspecial : ∀ j ∈ typeALeviJ 11 8, ∃ c : ρ'.range,
      (c : G) = ggExt φ (weylRep 11 F2 j) ∧
        (MonoidHom.ofInjective hρ'inj).symm c =
          (coxeterMatrix (isFiniteType_A 11)).toCoxeterSystem.simple j := by
    intro j hj
    refine ⟨MonoidHom.ofInjective hρ'inj
      ((coxeterMatrix (isFiniteType_A 11)).toCoxeterSystem.simple j), ?_, ?_⟩
    · rw [MonoidHom.ofInjective_apply]
      change ρ ((typeAWeylEquiv 11).symm
          ((coxeterMatrix (isFiniteType_A 11)).toCoxeterSystem.simple j)) =
        ggExt φ (weylRep 11 F2 j)
      have hsymm : (typeAWeylEquiv 11).symm
          ((coxeterMatrix (isFiniteType_A 11)).toCoxeterSystem.simple j) =
          Equiv.swap j.castSucc j.succ := by
        rw [MulEquiv.symm_apply_eq]
        exact (typeAWeylEquiv_swap 11 j).symm
      rw [hsymm]
      exact (test_hspecial φ₃ ρ hRhoOn9 j hj).symm
    · rw [MulEquiv.symm_apply_apply]
  have hcent' : ∀ (w : (coxeterMatrix (isFiniteType_A 11)).Group),
      ∀ α ∈ ggSupp (rootDatum 11 F2) (typeALeviJ 11 8),
        weylAction (isFiniteType_A 11) w α = α →
          ∀ z ∈ rootGroup 11 F2 α,
            ρ' w * ggExt φ z * (ρ' w)⁻¹ = ggExt φ z :=
    fun w α hα hfix z hz => test_hcent φ₃ ρ hRhoStab w α hα hfix z hz
  have hcent : ∀ r : ρ'.range, ∀ α ∈ ggSupp (rootDatum 11 F2) (typeALeviJ 11 8),
      weylAction (isFiniteType_A 11) ((MonoidHom.ofInjective hρ'inj).symm r) α = α →
        ∀ z ∈ rootGroup 11 F2 α, (r : G) * ggExt φ z * (r : G)⁻¹ = ggExt φ z :=
    fun r => forall_range_ofInjective hρ'inj
      (P := fun g w => ∀ α ∈ ggSupp (rootDatum 11 F2) (typeALeviJ 11 8),
        weylAction (isFiniteType_A 11) w α = α →
          ∀ z ∈ rootGroup 11 F2 α, g * ggExt φ z * g⁻¹ = ggExt φ z) hcent' r
  obtain ⟨ψ, hext, heq, hsurj, hrange, hker, hq, hmodel⟩ :=
    ggPresentation_typeALevi (m := 11) (k := 8) (by norm_num) (by norm_num)
      (F := F2) hF (by norm_num) φ
      (R := ρ'.range) (δ := (MonoidHom.ofInjective hρ'inj).symm.toMonoidHom)
      (MonoidHom.ofInjective hρ'inj).symm.surjective hspecial hcent (test_hnt φ₃ hφinj)
  have hClos_le : Clos φ₃ ρ ≤ ggClosure (rootDatum 11 F2)
      (fun _ : Unit => ggSupp (rootDatum 11 F2) (typeALeviJ 11 8)) (fun _ => φ) ρ'.range := by
    rw [Clos, Subgroup.closure_le]
    rintro g ⟨w, s, rfl⟩
    let w' : (coxeterMatrix (isFiniteType_A 11)).Group := (typeAWeylEquiv 11) w
    let r : ρ'.range := ⟨ρ' w', ⟨w', rfl⟩⟩
    have hr : (r : G) = ρ w := by
      change ρ ((typeAWeylEquiv 11).symm w') = ρ w
      rw [show (typeAWeylEquiv 11).symm w' = w from by
        change (typeAWeylEquiv 11).symm ((typeAWeylEquiv 11) w) = w
        exact MulEquiv.symm_apply_apply _ _]
    refine Subgroup.mem_iSup_of_mem r (Subgroup.mem_iSup_of_mem () ?_)
    refine Subgroup.mem_map.mpr
      ⟨φ ⟨slBlock84 s, slBlock84_mem s⟩, ⟨⟨slBlock84 s, slBlock84_mem s⟩, rfl⟩, ?_⟩
    change (r : G) * φ ⟨slBlock84 s, slBlock84_mem s⟩ * (r : G)⁻¹ =
      ρ w * φ₃ (slBlockHom 7 F2 s) * (ρ w)⁻¹
    rw [hr, typeALeviHom4_apply]
    rfl
  have hφG' : φ.range ≤ ggG0 7 B x L D J := by
    rw [show φ = typeALeviHom4 (φ₃.comp (slBlockHom 7 F2)) from rfl, range_typeALeviHom4]
    rintro _ ⟨s, rfl⟩
    exact hφG ⟨slBlockHom 7 F2 s, rfl⟩
  have hρ'G' : ρ'.range ≤ ggG0 7 B x L D J := by
    rintro _ ⟨w, rfl⟩
    exact hρG ⟨(typeAWeylEquiv 11).symm w, rfl⟩
  have hcl := ggClosure_eq_ggG0 (Δ := rootDatum 11 F2)
    (S := fun _ : Unit => ggSupp (rootDatum 11 F2) (typeALeviJ 11 8))
    (φ := fun _ => φ) (R := ρ'.range) (p := 7) (B := B) (x := x) (L := L) (D := D) (J := J)
    (fun _ => hφG') hρ'G' (hL.trans hClos_le) (fun y K hKy => (hK y K hKy).trans hClos_le)
  have hrange' : ψ.range = ggG0 7 B x L D J := by rw [hrange, hcl]
  have hq' : IsQuasisimple (ggG0 7 B x L D J) := by rw [← hcl]; exact hq
  have hmodel' := hmodel
  rw [hcl] at hmodel'
  refine ⟨ψ, ⟨⟨statedLieAdmissible_PSL (m := 11) (f := 1) (by omega) (by norm_num),
      by change 2 ≤ 11; omega⟩, ⟨hrange', hker⟩, Group.isPerfect_def.mp hq'.1, hmodel'⟩, ?_⟩
  have hgen : ∀ s ∈ a11pGen, ψ (slBlockHom₃ 8 F2 s) = φ₃ s := by
    intro s hs
    induction hs using Subgroup.closure_induction with
    | mem u hu =>
        rcases hu with ⟨t, rfl⟩ | rfl
        · change ψ (slBlockHom₃ 8 F2 (slBlockHom 7 F2 t)) = φ₃ (slBlockHom 7 F2 t)
          rw [show slBlockHom₃ 8 F2 (slBlockHom 7 F2 t) = slBlock84 t from rfl,
            hext ⟨slBlock84 t, slBlock84_mem t⟩]
          change (typeALeviHom4 (φ₃.comp (slBlockHom 7 F2)))
            ⟨slBlock84 t, slBlock84_mem t⟩ = φ₃ (slBlockHom 7 F2 t)
          rw [typeALeviHom4_apply]
          rfl
        · change ψ (slBlockHom₃ 8 F2 (permSL 8 (Equiv.swap (7 : Fin 9) (8 : Fin 9)))) =
            φ₃ (permSL 8 (Equiv.swap (7 : Fin 9) (8 : Fin 9)))
          rw [test_slBlock₃_permSL_last]
          obtain ⟨r, hr, hδr⟩ := hsurj
            (typeAWeylHom 11 (ext9 (Equiv.swap (7 : Fin 9) (8 : Fin 9))))
          rw [show ψ (permSL 11 (ext9 (Equiv.swap (7 : Fin 9) (8 : Fin 9)))) =
            ψ (slWeylLift 11 two_eq_zero
              (typeAWeylHom 11 (ext9 (Equiv.swap (7 : Fin 9) (8 : Fin 9))))) from rfl, ← hr]
          have he : (r : G) = ρ (ext9 (Equiv.swap (7 : Fin 9) (8 : Fin 9))) := by
            have h1 : (r : G) = ρ' ((MonoidHom.ofInjective hρ'inj).symm r) := by
              rw [← MonoidHom.ofInjective_apply hρ'inj, MulEquiv.apply_symm_apply]
            rw [h1]
            change ρ ((typeAWeylEquiv 11).symm
              ((MonoidHom.ofInjective hρ'inj).symm r)) = ρ (ext9 (Equiv.swap (7 : Fin 9) (8 : Fin 9)))
            rw [show (MonoidHom.ofInjective hρ'inj).symm r = typeAWeylHom 11
              (ext9 (Equiv.swap (7 : Fin 9) (8 : Fin 9))) from hδr]
            change ρ ((typeAWeylEquiv 11).symm ((typeAWeylEquiv 11)
              (ext9 (Equiv.swap (7 : Fin 9) (8 : Fin 9))))) = ρ (ext9 (Equiv.swap (7 : Fin 9) (8 : Fin 9)))
            rw [MulEquiv.symm_apply_apply]
          rw [he, hRhoOn9]
    | one => simp
    | mul a b ha hb iha ihb => simp only [map_mul, iha, ihb]
    | inv a ha iha => simp only [map_inv, iha]
  intro s
  exact hgen s (by rw [a11pGen_eq_top]; exact Subgroup.mem_top s)

end CFSG.StandardType.A11

end
