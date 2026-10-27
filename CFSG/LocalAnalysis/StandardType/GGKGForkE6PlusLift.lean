module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylExcPlusLift
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeTwoTorus

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint

private def ggKGE6p_frame :
    TableBExcTwo.OrthFrame Tag.E6 3 where
  root := TableBExc.E6Three.bE6
  symm_one := fun i => by simp [Tag.symmetrizer]
  isRoot := fun i => TableBExc.E6Three.isRoot_bE6 i
  orth := fun i j hij => (TableBExc.E6Three.iform_bE6 i j hij).1

private theorem ggKGE6p_adjoint_E6
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ Nat.card K + 1) : GGTorusLift p 4 (adjointGroup Tag.E6 K) := by
  classical
  have hp2 : p ≠ 2 := by omega
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨s, nSL, hsorder, hconj⟩ := GGPlusLiftSL2.exists_order_p_inverting_sl2 hp hp2 hpq
  have hs_pow : s ^ p = 1 := by rw [← hsorder]; exact pow_orderOf_eq_one s
  have hpow : ∀ i : Fin 4, (TableBExcTwo.rho K ggKGE6p_frame i s) ^ p = 1 := fun i => by
    rw [← map_pow, hs_pow, map_one]
  let coord : Fin 4 → Multiplicative (ZMod p) →* adjointGroup Tag.E6 K :=
    fun i => TableBSymp.zmodPowHom (hpow i)
  have coord_apply : ∀ (i : Fin 4) (a : Multiplicative (ZMod p)),
      coord i a = TableBExcTwo.rho K ggKGE6p_frame i (s ^ (Multiplicative.toAdd a).val) :=
    fun i a => by
      change TableBSymp.zmodPowHom (hpow i) a =
        TableBExcTwo.rho K ggKGE6p_frame i (s ^ (Multiplicative.toAdd a).val)
      rw [TableBSymp.zmodPowHom_apply, map_pow]
  have coord_inj : ∀ i, Function.Injective (coord i) := fun i => by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hto : orderOf (TableBExcTwo.rho K ggKGE6p_frame i s) = p := by
      rw [orderOf_injective _ (TableBExcTwo.rho_injective ggKGE6p_frame i), hsorder]
    exact (TableBSymp.zmodPowHom_eq_one_iff (hpow i) hto).mp ha
  have coord_comm : Pairwise fun i j : Fin 4 => ∀ a b, Commute (coord i a) (coord j b) := by
    intro i j hij a b
    rw [coord_apply, coord_apply]
    exact TableBExcTwo.commute_rho ggKGE6p_frame hij _ _
  let ePi : (Fin 4 → Multiplicative (ZMod p)) →* adjointGroup Tag.E6 K :=
    MonoidHom.noncommPiCoprod coord coord_comm
  let e : Multiplicative (Fin 4 → ZMod p) →* adjointGroup Tag.E6 K :=
    ePi.comp (MulEquiv.piMultiplicative fun _ : Fin 4 => ZMod p).toMonoidHom
  have e_apply : ∀ v : Fin 4 → ZMod p, e (.ofAdd v) = ePi (fun j => .ofAdd (v j)) := fun v => rfl
  have coord_indep : iSupIndep fun i => (coord i).range := by
    rw [iSupIndep_def]
    intro i
    rw [Subgroup.disjoint_def]
    intro x hx hx'
    obtain ⟨a, rfl⟩ := hx
    have hle : (⨆ (j) (_ : j ≠ i), (coord j).range) ≤
        Subgroup.centralizer (Set.range (TableBExcTwo.rho K ggKGE6p_frame i)) := by
      refine iSup₂_le fun j hj => ?_
      rintro _ ⟨b, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨B, rfl⟩ := hy
      rw [coord_apply]
      exact (TableBExcTwo.commute_rho ggKGE6p_frame (Ne.symm hj) B
        (s ^ (Multiplicative.toAdd b).val)).eq
    have hcen := hle hx'
    have hs_center : s ^ (Multiplicative.toAdd a).val ∈ Subgroup.center (SL2 K) := by
      rw [Subgroup.mem_center_iff]
      intro B
      have h1 := Subgroup.mem_centralizer_iff.mp hcen
        (TableBExcTwo.rho K ggKGE6p_frame i B) ⟨B, rfl⟩
      rw [coord_apply] at h1
      have h2 : TableBExcTwo.rho K ggKGE6p_frame i (B * s ^ (Multiplicative.toAdd a).val) =
          TableBExcTwo.rho K ggKGE6p_frame i (s ^ (Multiplicative.toAdd a).val * B) := by
        rw [map_mul, map_mul]
        exact h1
      exact TableBExcTwo.rho_injective ggKGE6p_frame i h2
    obtain ⟨r, hr2, hr⟩ :=
      (Matrix.SpecialLinearGroup.mem_center_iff (n := Fin 2) (R := K)).mp hs_center
    have hr1 : r = 1 := by
      have h2 : r ^ 2 = 1 := by simpa using hr2
      have h : (r - 1) ^ 2 = 0 := by
        have h3 : (r - 1) ^ 2 = (2 : K) * (1 - r) := by linear_combination h2
        rw [h3, CharTwo.two_eq_zero, zero_mul]
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp h)
    have hs_one : s ^ (Multiplicative.toAdd a).val = 1 := by
      apply Subtype.ext
      rw [← hr, hr1]
      exact map_one (Matrix.scalar (Fin 2))
    have hdvd : p ∣ (Multiplicative.toAdd a).val := by
      have := orderOf_dvd_of_pow_eq_one hs_one
      rwa [hsorder] at this
    have hval0 : (Multiplicative.toAdd a).val = 0 :=
      Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt _)
    have ha1 : a = 1 := by
      rw [← ofAdd_toAdd a, (ZMod.val_eq_zero (Multiplicative.toAdd a)).mp hval0, ofAdd_zero]
    rw [ha1, map_one]
  have ePi_inj : Function.Injective ePi :=
    MonoidHom.injective_noncommPiCoprod_of_iSupIndep coord coord_indep coord_inj
  have e_inj : Function.Injective e :=
    ePi_inj.comp (MulEquiv.piMultiplicative fun _ : Fin 4 => ZMod p).injective
  have reflGen_conj_coord : ∀ (i j : Fin 4) (a : Multiplicative (ZMod p)),
      TableBExcTwo.rho K ggKGE6p_frame i nSL * coord j a *
          (TableBExcTwo.rho K ggKGE6p_frame i nSL)⁻¹ =
        coord j (if j = i then a⁻¹ else a) := by
    intro i j a
    split_ifs with hji
    · subst hji
      rw [show coord j a⁻¹ = (coord j a)⁻¹ from map_inv _ a, coord_apply, ← map_inv,
        ← map_mul, ← map_mul, ← map_inv]
      congr 1
      rw [← conj_pow, hconj, inv_pow]
    · rw [coord_apply,
        (TableBExcTwo.commute_rho ggKGE6p_frame (fun h => hji h.symm) nSL
          (s ^ (Multiplicative.toAdd a).val)).eq, mul_inv_cancel_right]
  have reflGen_conj_ePi : ∀ (i : Fin 4) (f : Fin 4 → Multiplicative (ZMod p)),
      TableBExcTwo.rho K ggKGE6p_frame i nSL * ePi f *
          (TableBExcTwo.rho K ggKGE6p_frame i nSL)⁻¹ =
        ePi (GGPlusLiftTorus.reflHom i f) := by
    intro i f
    have h : (MulAut.conj (TableBExcTwo.rho K ggKGE6p_frame i nSL)).toMonoidHom.comp ePi =
        ePi.comp (GGPlusLiftTorus.reflHom i) :=
      MonoidHom.pi_ext fun j a => by
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ePi,
          MonoidHom.noncommPiCoprod_mulSingle, GGPlusLiftTorus.reflHom_mulSingle]
        exact reflGen_conj_coord i j a
    have h1 := congrArg (fun φ => φ f) h
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h1
  have reflGen_conj_e : ∀ (i : Fin 4) (v : Fin 4 → ZMod p),
      TableBExcTwo.rho K ggKGE6p_frame i nSL * e (.ofAdd v) *
          (TableBExcTwo.rho K ggKGE6p_frame i nSL)⁻¹ =
        e (.ofAdd (v - GGPlusLiftTorus.reflCoeff i v • Pi.single i (1 : ZMod p))) := by
    intro i v
    rw [e_apply, e_apply, reflGen_conj_ePi, GGPlusLiftTorus.reflHom_ofAdd]
  have hpos : ∀ (i : Fin 4) (c : K),
      pinnedX Tag.E6 K (TableBExc.E6Three.bE6 i) c ∈
        parabolicSubgroup Tag.E6 K TableBExc.E6Three.jE6Two := by
    intro i c
    exact borelGroup_le_parabolicSubgroup _ (Subgroup.mem_sup_right
      (pinnedX_mem_rootSpan (S := {α | IsRoot Tag.E6 α ∧ 0 < height α})
        ⟨TableBExc.E6Three.isRoot_bE6 i, TableBExc.E6Three.height_bE6_pos i⟩ c))
  have hneg : ∀ (i : Fin 4) (c : K),
      pinnedX Tag.E6 K (-(TableBExc.E6Three.bE6 i)) c ∈
        parabolicSubgroup Tag.E6 K TableBExc.E6Three.jE6Two := by
    intro i c
    fin_cases i
    · exact TableBExc.E6Three.pinnedX_neg_single_mem_parabolic (j := 1)
        (by simp [TableBExc.E6Three.jE6Two]) c
    · exact TableBExc.E6Three.pinnedX_neg_single_mem_parabolic (j := 2)
        (by simp [TableBExc.E6Three.jE6Two]) c
    · exact TableBExc.E6Three.pinnedX_neg_single_mem_parabolic (j := 4)
        (by simp [TableBExc.E6Three.jE6Two]) c
    · obtain ⟨ε, hε, hconj'⟩ :=
        exists_prod_weylElt_mul_pinnedX_mul_inv K [3, 1, 2, 3] (isRoot_neg_single Tag.E6 4)
      have hε1 : ε = 1 := by
        have h2 : ε ^ 2 = 1 := by simpa [pow_two] using hε
        have h : (ε - 1) ^ 2 = 0 := by
          have h3 : (ε - 1) ^ 2 = (2 : K) * (1 - ε) := by linear_combination h2
          rw [h3, CharTwo.two_eq_zero, zero_mul]
        exact sub_eq_zero.mp (sq_eq_zero_iff.mp h)
      have h := hconj' c
      rw [hε1, one_mul, TableBExc.E6Three.wordProd_bE6_three] at h
      show pinnedX Tag.E6 K (-(TableBExc.E6Three.bE6 3)) c ∈
        parabolicSubgroup Tag.E6 K TableBExc.E6Three.jE6Two
      rw [← h]
      have hW : (([3, 1, 2, 3] : List (Fin Tag.E6.rank)).map
          fun i => weylElt Tag.E6 K i 1).prod ∈
          parabolicSubgroup Tag.E6 K TableBExc.E6Three.jE6Two := by
        refine Subgroup.list_prod_mem _ fun g hg => ?_
        simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl | rfl | rfl <;>
          exact weylElt_mem_parabolicSubgroup (by simp [TableBExc.E6Three.jE6Two])
      exact mul_mem (mul_mem hW (TableBExc.E6Three.pinnedX_neg_single_mem_parabolic (j := 4)
        (by simp [TableBExc.E6Three.jE6Two]) c)) (inv_mem hW)
  have hcoord : ∀ (i : Fin 4) (A : SL2 K),
      ((TableBExcTwo.rho K ggKGE6p_frame i A : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) ∈
        parabolicSubgroup Tag.E6 K TableBExc.E6Three.jE6Two := by
    intro i A
    rw [TableBExcTwo.coe_rho]
    have hclosure : TableBExcTwo.orthGen K ggKGE6p_frame i ⊆
        parabolicSubgroup Tag.E6 K TableBExc.E6Three.jE6Two := by
      rintro x (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · exact hpos i c
      · exact hneg i c
    have hmem : (rootSL2 Tag.E6 K (ggKGE6p_frame.root i)) A ∈
        Subgroup.closure (TableBExcTwo.orthGen K ggKGE6p_frame i) := by
      rw [← TableBExcTwo.range_rootSL2_frame]
      exact ⟨A, rfl⟩
    exact (Subgroup.closure_le _).2 hclosure hmem
  have he_mem : ∀ v : Multiplicative (Fin 4 → ZMod p),
      ((e v : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) ∈
        parabolicSubgroup Tag.E6 K TableBExc.E6Three.jE6Two := by
    intro v
    have hle : ePi.range ≤
        (parabolicSubgroup Tag.E6 K TableBExc.E6Three.jE6Two).subgroupOf
          (adjointGroup Tag.E6 K) := by
      change (MonoidHom.noncommPiCoprod coord coord_comm).range ≤ _
      rw [MonoidHom.noncommPiCoprod_range]
      refine iSup_le fun i => ?_
      rintro _ ⟨a, rfl⟩
      rw [coord_apply]
      exact Subgroup.mem_subgroupOf.mpr (hcoord i _)
    exact Subgroup.mem_subgroupOf.mp
      (hle ⟨(MulEquiv.piMultiplicative fun _ : Fin 4 => ZMod p) v, rfl⟩)
  set U : Subgroup (adjointGroup Tag.E6 K) :=
    (parabolicRadical Tag.E6 K TableBExc.E6Three.jE6Two).subgroupOf (adjointGroup Tag.E6 K)
    with hUdef
  have h0 : (Pi.single 0 1 : Fin Tag.E6.rank → ℤ) ∈
      parabolicRadicalRoots Tag.E6 TableBExc.E6Three.jE6Two := by
    refine ⟨⟨isRoot_single Tag.E6 0, by simp⟩, fun h => ?_⟩
    have h1 := h.1.2 0 (by
      simp only [TableBExc.E6Three.jE6Two, Set.mem_insert_iff, Set.mem_singleton_iff]
      decide)
    simp at h1
  have hU : U ≠ ⊥ := by
    intro hbot
    have hx : (⟨pinnedX Tag.E6 K (Pi.single 0 1) 1, pinnedX_mem_adjointGroup _ _⟩ :
        adjointGroup Tag.E6 K) ∈ U :=
      Subgroup.mem_subgroupOf.mpr (pinnedX_mem_rootSpan
        (S := parabolicRadicalRoots Tag.E6 TableBExc.E6Three.jE6Two) h0 1)
    rw [hbot, Subgroup.mem_bot] at hx
    have hx' : pinnedX Tag.E6 K (Pi.single 0 1) 1 = pinnedX Tag.E6 K (Pi.single 0 1) 0 := by
      rw [pinnedX_zero]
      exact congrArg Subtype.val hx
    exact one_ne_zero (pinnedX_injective Tag.E6 K _ hx')
  have hU2 : IsPGroup 2 U :=
    ((isPGroup_posUnipotent 2 Tag.E6).to_le
      (parabolicRadical_le_posUnipotent TableBExc.E6Three.jE6Two)).comap_of_injective _
        (adjointGroup Tag.E6 K).subtype_injective
  have hTU : ∀ v, ∀ u ∈ U, e v * u * (e v)⁻¹ ∈ U := by
    intro v u hu
    rw [Subgroup.mem_subgroupOf] at hu ⊢
    have hN := parabolicSubgroup_le_normalizer_parabolicRadical TableBExc.E6Three.jE6Two
      (he_mem v)
    have h3 := (Subgroup.mem_normalizer_iff.mp hN u).1 hu
    simpa using h3
  exact TableBF4.ggTorusLift_of_reflections (d := 4) hp hp2 e e_inj
    GGPlusLiftTorus.reflCoeff (fun i => GGPlusLiftTorus.reflCoeff_single i)
    (fun i => TableBExcTwo.rho K ggKGE6p_frame i nSL) reflGen_conj_e hU hU2 hTU

theorem ggTorusLift_E6Plus
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card K + 1) :
    GGTorusLift p 4 (TableBExc.RecipeGroup .E6 K) :=
  TableBF4.ggTorusLift_of_mulEquiv (TableBExc.recipeEquiv .E6 K)
    (ggKGE6p_adjoint_E6 hp hp5 hpq)

end CFSG.StandardType

end
