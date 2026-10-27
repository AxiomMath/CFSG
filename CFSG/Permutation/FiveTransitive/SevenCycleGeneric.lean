module

public import CFSG.Permutation.FiveTransitive.SevenCycleGenericChecks
public import CFSG.Permutation.FiveTransitive.SmallSupportGeneric

public section

namespace CFSG

namespace FiveTransitive.SevenCycleGeneric

open MulAction

open FiveTransitive.SmallSupportSeven

private theorem alternatingGroup_le_of_sevenCycle_viaEmbedding_mem
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : 15 ≤ Fintype.card X)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (e : Fin 8 ↪ X)
    (hc : sevenCycle8.viaEmbedding e ∈ P) :
    alternatingGroup X ≤ P := by
  classical
  let a : Fin 5 → X :=
    fun i => e (SmallSupportGeneric.sourceTuple8 i)
  let b : Fin 5 → X :=
    fun i => e (SmallSupportGeneric.targetTuple8 i)
  have ha : Function.Injective a :=
    e.injective.comp SmallSupportGeneric.sourceTuple8_injective
  have hb : Function.Injective b :=
    e.injective.comp SmallSupportGeneric.targetTuple8_injective
  obtain ⟨q, hq⟩ := h5 a b ha hb
  have hq0 : (q : Equiv.Perm X) (e 0) = e 0 := by
    simpa [a, b, SmallSupportGeneric.sourceTuple8,
      SmallSupportGeneric.targetTuple8, Subgroup.smul_def,
      Equiv.Perm.smul_def] using hq 0
  have hq1 : (q : Equiv.Perm X) (e 1) = e 1 := by
    simpa [a, b, SmallSupportGeneric.sourceTuple8,
      SmallSupportGeneric.targetTuple8, Subgroup.smul_def,
      Equiv.Perm.smul_def] using hq 1
  have hq2 : (q : Equiv.Perm X) (e 2) = e 2 := by
    simpa [a, b, SmallSupportGeneric.sourceTuple8,
      SmallSupportGeneric.targetTuple8, Subgroup.smul_def,
      Equiv.Perm.smul_def] using hq 2
  have hq3 : (q : Equiv.Perm X) (e 3) = e 3 := by
    simpa [a, b, SmallSupportGeneric.sourceTuple8,
      SmallSupportGeneric.targetTuple8, Subgroup.smul_def,
      Equiv.Perm.smul_def] using hq 3
  let x : X := (q : Equiv.Perm X) (e 4)
  let y : X := (q : Equiv.Perm X) (e 5)
  let z : X := (q : Equiv.Perm X) (e 6)
  have hx (i : Fin 5) :
      x ≠ e (SmallSupportGeneric.targetTuple8 i) := by
    have hqi :
        (q : Equiv.Perm X)
            (e (SmallSupportGeneric.sourceTuple8 i)) =
          e (SmallSupportGeneric.targetTuple8 i) := by
      simpa [a, b, Subgroup.smul_def, Equiv.Perm.smul_def] using
        hq i
    rw [← hqi]
    exact
      (q : Equiv.Perm X).injective.ne
        (e.injective.ne
          (SmallSupportGeneric.four_ne_sourceTuple8 i))
  have hy (i : Fin 5) :
      y ≠ e (SmallSupportGeneric.targetTuple8 i) := by
    have hqi :
        (q : Equiv.Perm X)
            (e (SmallSupportGeneric.sourceTuple8 i)) =
          e (SmallSupportGeneric.targetTuple8 i) := by
      simpa [a, b, Subgroup.smul_def, Equiv.Perm.smul_def] using
        hq i
    rw [← hqi]
    exact
      (q : Equiv.Perm X).injective.ne
        (e.injective.ne
          (SmallSupportGeneric.five_ne_sourceTuple8 i))
  have hz (i : Fin 5) :
      z ≠ e (SmallSupportGeneric.targetTuple8 i) := by
    have hqi :
        (q : Equiv.Perm X)
            (e (SmallSupportGeneric.sourceTuple8 i)) =
          e (SmallSupportGeneric.targetTuple8 i) := by
      simpa [a, b, Subgroup.smul_def, Equiv.Perm.smul_def] using
        hq i
    rw [← hqi]
    exact
      (q : Equiv.Perm X).injective.ne
        (e.injective.ne (by
          intro hi
          fin_cases i <;>
            simp [SmallSupportGeneric.sourceTuple8] at hi))
  have hx0 : x ≠ e 0 := by
    simpa [SmallSupportGeneric.targetTuple8] using hx 0
  have hx1 : x ≠ e 1 := by
    simpa [SmallSupportGeneric.targetTuple8] using hx 1
  have hx2 : x ≠ e 2 := by
    simpa [SmallSupportGeneric.targetTuple8] using hx 2
  have hx3 : x ≠ e 3 := by
    simpa [SmallSupportGeneric.targetTuple8] using hx 3
  have hx4 : x ≠ e 4 := by
    simpa [SmallSupportGeneric.targetTuple8] using hx 4
  have hy0 : y ≠ e 0 := by
    simpa [SmallSupportGeneric.targetTuple8] using hy 0
  have hy1 : y ≠ e 1 := by
    simpa [SmallSupportGeneric.targetTuple8] using hy 1
  have hy2 : y ≠ e 2 := by
    simpa [SmallSupportGeneric.targetTuple8] using hy 2
  have hy3 : y ≠ e 3 := by
    simpa [SmallSupportGeneric.targetTuple8] using hy 3
  have hy4 : y ≠ e 4 := by
    simpa [SmallSupportGeneric.targetTuple8] using hy 4
  have hz0 : z ≠ e 0 := by
    simpa [SmallSupportGeneric.targetTuple8] using hz 0
  have hz1 : z ≠ e 1 := by
    simpa [SmallSupportGeneric.targetTuple8] using hz 1
  have hz2 : z ≠ e 2 := by
    simpa [SmallSupportGeneric.targetTuple8] using hz 2
  have hz3 : z ≠ e 3 := by
    simpa [SmallSupportGeneric.targetTuple8] using hz 3
  have hz4 : z ≠ e 4 := by
    simpa [SmallSupportGeneric.targetTuple8] using hz 4
  have hxy : x ≠ y :=
    (q : Equiv.Perm X).injective.ne
      (e.injective.ne (by decide))
  have hxz : x ≠ z :=
    (q : Equiv.Perm X).injective.ne
      (e.injective.ne (by decide))
  have hyz : y ≠ z :=
    (q : Equiv.Perm X).injective.ne
      (e.injective.ne (by decide))
  let c : Equiv.Perm X := sevenCycle8.viaEmbedding e
  let dcomp : Equiv.Perm X :=
    List.formPerm [e 0, e 1, e 2, e 3, x, y, z]
  let h : Equiv.Perm X :=
    (q : Equiv.Perm X) * c * (q : Equiv.Perm X)⁻¹
  have hh : h = dcomp := by
    change
      (q : Equiv.Perm X) * sevenCycle8.viaEmbedding e *
          (q : Equiv.Perm X)⁻¹ =
        List.formPerm [e 0, e 1, e 2, e 3, x, y, z]
    rw [← Equiv.permCongr_eq_mul, sevenCycle8,
      ← formPerm_map_eq_viaEmbedding,
      Helpers.permCongr_formPerm]
    simp [x, y, z, hq0, hq1, hq2, hq3]
  have hhP : h ∈ P :=
    P.mul_mem (P.mul_mem q.prop hc) (P.inv_mem q.prop)
  let selected : Finset X :=
    [e 0, e 1, e 2, e 3, e 4, e 5, e 6,
      x, y, z].toFinset
  have hselectedCard : selected.card ≤ 10 := by
    calc
      selected.card ≤
          [e 0, e 1, e 2, e 3, e 4, e 5, e 6,
            x, y, z].length :=
        List.toFinset_card_le _
      _ ≤ 10 := by norm_num
  obtain ⟨t, hselectedSubset, htcard⟩ :=
    Finset.exists_superset_card_eq hselectedCard (by omega)
  have heMem (i : Fin 7) : e i.castSucc ∈ t := by
    apply hselectedSubset
    simp only [selected, List.mem_toFinset, List.mem_cons,
      List.not_mem_nil, or_false]
    fin_cases i <;> simp
  have hxMem : x ∈ t := by
    apply hselectedSubset
    simp [selected]
  have hyMem : y ∈ t := by
    apply hselectedSubset
    simp [selected]
  have hzMem : z ∈ t := by
    apply hselectedSubset
    simp [selected]
  let d₀ : Fin 10 ≃ t :=
    Fintype.equivOfCardEq (by
      rw [Fintype.card_fin, Fintype.card_coe, htcard])
  let f : Fin 7 → Fin 10 := fun i => ⟨i, by omega⟩
  let g : Fin 7 → Fin 10 :=
    fun i => d₀.symm ⟨e i.castSucc, heMem i⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    simpa [f] using
      congrArg (fun u : Fin 10 => u.val) hij
  have hg : Function.Injective g := by
    intro i j hij
    change
      d₀.symm ⟨e i.castSucc, heMem i⟩ =
        d₀.symm ⟨e j.castSucc, heMem j⟩ at hij
    have hij' := d₀.symm.injective hij
    have hcast :
        i.castSucc = j.castSucc :=
      e.injective (congrArg Subtype.val hij')
    apply Fin.ext
    simpa using
      congrArg (fun u : Fin 8 => u.val) hcast
  obtain ⟨τ, hτ⟩ :=
    Equiv.Perm.exists_extending_pair f g hf hg
  let dEquiv : Fin 10 ≃ t := τ.trans d₀
  let d : Fin 10 ↪ X :=
    dEquiv.toEmbedding.trans
      (Function.Embedding.subtype (fun u : X => u ∈ t))
  have hd (i : Fin 7) :
      d ⟨i, by omega⟩ = e i.castSucc := by
    change ((d₀ (τ (f i)) : t) : X) = e i.castSucc
    rw [hτ i]
    simp [g]
  have hd0 : d 0 = e 0 := by
    simpa using hd (0 : Fin 7)
  have hd1 : d 1 = e 1 := by
    simpa using hd (1 : Fin 7)
  have hd2 : d 2 = e 2 := by
    simpa using hd (2 : Fin 7)
  have hd3 : d 3 = e 3 := by
    simpa using hd (3 : Fin 7)
  have hd4 : d 4 = e 4 := by
    simpa using hd (4 : Fin 7)
  have hd5 : d 5 = e 5 := by
    simpa using hd (5 : Fin 7)
  have hd6 : d 6 = e 6 := by
    simpa using hd (6 : Fin 7)
  let ix : Fin 10 := dEquiv.symm ⟨x, hxMem⟩
  let iy : Fin 10 := dEquiv.symm ⟨y, hyMem⟩
  let iz : Fin 10 := dEquiv.symm ⟨z, hzMem⟩
  have hdix : d ix = x := by
    simp [d, ix]
  have hdiy : d iy = y := by
    simp [d, iy]
  have hdiz : d iz = z := by
    simp [d, iz]
  have index_five_le
      (u : Fin 10) (v : X) (hdu : d u = v)
      (hv0 : v ≠ e 0) (hv1 : v ≠ e 1)
      (hv2 : v ≠ e 2) (hv3 : v ≠ e 3)
      (hv4 : v ≠ e 4) :
      5 ≤ u.val := by
    have hu0 : u ≠ 0 := by
      intro hu
      apply hv0
      rw [← hdu, hu, hd0]
    have hu1 : u ≠ 1 := by
      intro hu
      apply hv1
      rw [← hdu, hu, hd1]
    have hu2 : u ≠ 2 := by
      intro hu
      apply hv2
      rw [← hdu, hu, hd2]
    have hu3 : u ≠ 3 := by
      intro hu
      apply hv3
      rw [← hdu, hu, hd3]
    have hu4 : u ≠ 4 := by
      intro hu
      apply hv4
      rw [← hdu, hu, hd4]
    omega
  have hix : 5 ≤ ix.val :=
    index_five_le ix x hdix hx0 hx1 hx2 hx3 hx4
  have hiy : 5 ≤ iy.val :=
    index_five_le iy y hdiy hy0 hy1 hy2 hy3 hy4
  have hiz : 5 ≤ iz.val :=
    index_five_le iz z hdiz hz0 hz1 hz2 hz3 hz4
  have hixy : ix ≠ iy := by
    intro h
    apply hxy
    rw [← hdix, ← hdiy, h]
  have hixz : ix ≠ iz := by
    intro h
    apply hxz
    rw [← hdix, ← hdiz, h]
  have hiyz : iy ≠ iz := by
    intro h
    apply hyz
    rw [← hdiy, ← hdiz, h]
  obtain ⟨w, hw, hwNe, hwsupport⟩ :=
    small_mem_closure_viaEmbedding d
      sevenCycle10
      (comparisonCycle10 ix iy iz)
      (exists_small_mem_closure10
        ix iy iz hix hiy hiz hixy hixz hiyz)
  have hcMap :
      sevenCycle10.viaEmbedding d = c := by
    change
      sevenCycle10.viaEmbedding d =
        sevenCycle8.viaEmbedding e
    rw [sevenCycle10, sevenCycle8,
      ← formPerm_map_eq_viaEmbedding,
      ← formPerm_map_eq_viaEmbedding]
    simp [hd0, hd1, hd2, hd3, hd4, hd5, hd6]
  have hcompMap :
      (comparisonCycle10 ix iy iz).viaEmbedding d =
        dcomp := by
    change
      (List.formPerm [0, 1, 2, 3, ix, iy, iz]).viaEmbedding d =
        List.formPerm [e 0, e 1, e 2, e 3, x, y, z]
    rw [← formPerm_map_eq_viaEmbedding]
    simp [hd0, hd1, hd2, hd3, hdix, hdiy, hdiz]
  have hw' :
      w ∈ Subgroup.closure
        ({c, dcomp} : Set (Equiv.Perm X)) := by
    simpa only [hcMap, hcompMap] using hw
  have hclosure :
      Subgroup.closure
          ({c, dcomp} : Set (Equiv.Perm X)) ≤ P := by
    rw [Subgroup.closure_le]
    intro u hu
    rcases hu with rfl | rfl
    · exact hc
    · rwa [← hh]
  exact
    Helpers.alternatingGroup_le_of_nontrivial_card_support_le_five
      X P h5 (by omega) (hclosure hw') hwNe hwsupport

theorem alternatingGroup_le_of_sevenCycle_mem
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : 15 ≤ Fintype.card X)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    {c : Equiv.Perm X}
    (hc : c ∈ P) (hcCycle : c.IsCycle)
    (hcSupport : c.support.card = 7) :
    alternatingGroup X ≤ P := by
  classical
  have heNonempty : Nonempty (Fin 8 ↪ X) := by
    rw [Function.Embedding.nonempty_iff_card_le,
      Fintype.card_fin]
    omega
  let e : Fin 8 ↪ X := Classical.choice heNonempty
  let d : Equiv.Perm X := sevenCycle8.viaEmbedding e
  have hsevenCycleType : sevenCycle8.cycleType = {7} := by
    unfold sevenCycle8
    rw [(List.isCycle_formPerm (by decide : ([0, 1, 2, 3, 4, 5, 6] : List (Fin 8)).Nodup) (by norm_num)).cycleType]
    decide
  have hdCycleType : d.cycleType = {7} := by
    simpa [d, Equiv.Perm.viaEmbedding] using hsevenCycleType
  have hcCycleType : c.cycleType = {7} := by
    rw [hcCycle.cycleType, hcSupport]
  apply
    SmallSupportGeneric.alternatingGroup_le_of_cycleType_eq
      P h5 hc d (hcCycleType.trans hdCycleType.symm)
  intro Q h5Q hdQ
  exact
    alternatingGroup_le_of_sevenCycle_viaEmbedding_mem
      Q hcard h5Q e hdQ

end FiveTransitive.SevenCycleGeneric

end CFSG
