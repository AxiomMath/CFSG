module

public import CFSG.LocalAnalysis.WeakClosure81.W183TwoOdd

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Timmesfeld.Bridge.Asc72 (IsOddTransp)

variable {Y : Type} [Group Y]

@[expose] def oddClassSub (a : Y) : Subgroup Y :=
  Subgroup.closure {x | ∃ n ∈ Subgroup.normalClosure ({a} : Set Y), x = n * a * n⁻¹}

private def w183b5_classSet (a : Y) : Set Y :=
  {x | ∃ n ∈ Subgroup.normalClosure ({a} : Set Y), x = n * a * n⁻¹}

private def w183b5_conjSet (a : Y) : Set Y :=
  {x | ∃ z ∈ oddClassSub a, x = z * a * z⁻¹}

theorem mem_oddClassSub (a : Y) : a ∈ oddClassSub a := by
  change a ∈ Subgroup.closure (w183b5_classSet a)
  exact Subgroup.subset_closure
    ⟨1, (Subgroup.normalClosure ({a} : Set Y)).one_mem, by simp⟩

theorem oddClassSub_le_normalClosure (a : Y) :
    oddClassSub a ≤ Subgroup.normalClosure ({a} : Set Y) := by
  change Subgroup.closure (w183b5_classSet a) ≤ Subgroup.normalClosure ({a} : Set Y)
  rw [Subgroup.closure_le]
  rintro x ⟨n, hn, rfl⟩
  exact (Subgroup.normalClosure_normal (s := ({a} : Set Y))).conj_mem a
    (Subgroup.subset_normalClosure (Set.mem_singleton a)) n

theorem conj_mem_oddClassSub {a n x : Y} (hn : n ∈ Subgroup.normalClosure ({a} : Set Y))
    (hx : x ∈ oddClassSub a) : n * x * n⁻¹ ∈ oddClassSub a := by
  change x ∈ Subgroup.closure (w183b5_classSet a) at hx
  change n * x * n⁻¹ ∈ Subgroup.closure (w183b5_classSet a)
  refine Subgroup.closure_induction
    (p := fun x _ => n * x * n⁻¹ ∈ Subgroup.closure (w183b5_classSet a))
    ?_ ?_ ?_ ?_ hx
  · rintro x ⟨m, hm, rfl⟩
    exact Subgroup.subset_closure
      ⟨n * m, (Subgroup.normalClosure ({a} : Set Y)).mul_mem hn hm, by group⟩
  · simpa using (Subgroup.closure (w183b5_classSet a)).one_mem
  · intro x y _ _ ihx ihy
    rw [show n * (x * y) * n⁻¹ = n * x * n⁻¹ * (n * y * n⁻¹) by group]
    exact Subgroup.mul_mem _ ihx ihy
  · intro x _ ihx
    rw [show n * x⁻¹ * n⁻¹ = (n * x * n⁻¹)⁻¹ by group]
    exact Subgroup.inv_mem _ ihx

theorem normal_subgroupOf_oddClassSub (a : Y) :
    ((oddClassSub a).subgroupOf (Subgroup.normalClosure ({a} : Set Y))).Normal := by
  refine ⟨fun x hx n => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  exact conj_mem_oddClassSub n.2 hx

theorem iSup_conj_oddClassSub (a : Y) :
    ⨆ y : Y, (oddClassSub a).map (MulAut.conj y).toMonoidHom =
      Subgroup.normalClosure ({a} : Set Y) := by
  apply le_antisymm
  · refine iSup_le fun y => ?_
    calc (oddClassSub a).map (MulAut.conj y).toMonoidHom
        ≤ (Subgroup.normalClosure ({a} : Set Y)).map (MulAut.conj y).toMonoidHom :=
          Subgroup.map_mono (oddClassSub_le_normalClosure a)
      _ = Subgroup.normalClosure ({a} : Set Y) :=
          Subgroup.Normal.map_conj_eq (Subgroup.normalClosure ({a} : Set Y)) y
  · change Subgroup.normalClosure ({a} : Set Y) ≤ _
    rw [Subgroup.normalClosure, Subgroup.closure_le]
    intro x hx
    have hbc : IsConj a x := by
      obtain ⟨b, hb, hbd⟩ := (Group.mem_conjugatesOfSet_iff).1 hx
      rwa [Set.mem_singleton_iff.mp hb] at hbd
    rcases isConj_iff.1 hbc with ⟨y, hy⟩
    rw [← hy]
    exact Subgroup.mem_iSup_of_mem y
      (Subgroup.mem_map_of_mem (MulAut.conj y).toMonoidHom (mem_oddClassSub a))

theorem normalClosure_oddClassSub {a : Y}
    (h132 : ∀ c d : Y, IsConj a c → IsConj a d →
      c * d = d * c ∨ ∃ z ∈ Subgroup.closure ({c, d} : Set Y), d = z * c * z⁻¹) :
    Subgroup.normalClosure
        ({(⟨a, mem_oddClassSub a⟩ : ↥(oddClassSub a))} : Set ↥(oddClassSub a)) = ⊤ := by
  set X := oddClassSub a with hX
  set N := Subgroup.normalClosure ({a} : Set Y) with hN
  let C1 := w183b5_classSet a
  let C2 := w183b5_conjSet a
  have hXeq : X = Subgroup.closure C1 := rfl
  have hX_le_N : X ≤ N := by rw [hX, hN]; exact oddClassSub_le_normalClosure a
  haveI hNnormal : N.Normal := by rw [hN]; infer_instance
  have haN : a ∈ N := Subgroup.subset_normalClosure (Set.mem_singleton a)
  have haC2 : a ∈ C2 := ⟨1, X.one_mem, by simp⟩
  have key : ∀ n ∈ N, ∀ c ∈ C2, n * c * n⁻¹ ∈ C2 ∧ n⁻¹ * c * n ∈ C2 := by
    intro n hn
    have hn' : n ∈ Subgroup.closure (Group.conjugatesOfSet ({a} : Set Y)) := by
      rw [hN] at hn
      exact hn
    refine Subgroup.closure_induction
      (p := fun n _ => ∀ c ∈ C2, n * c * n⁻¹ ∈ C2 ∧ n⁻¹ * c * n ∈ C2)
      ?_ ?_ ?_ ?_ hn'
    · intro d hd
      have hda : IsConj a d := by
        obtain ⟨b, hb, hbd⟩ := (Group.mem_conjugatesOfSet_iff).1 hd
        rwa [Set.mem_singleton_iff.mp hb] at hbd
      intro c hc
      by_cases hdC1 : d ∈ C1
      · have hdX : d ∈ X := by
          rw [hXeq]; exact Subgroup.subset_closure hdC1
        constructor
        · rcases hc with ⟨z, hzX, rfl⟩
          exact ⟨d * z, X.mul_mem hdX hzX, by group⟩
        · rcases hc with ⟨z, hzX, rfl⟩
          exact ⟨d⁻¹ * z, X.mul_mem (X.inv_mem hdX) hzX, by group⟩
      · rcases hc with ⟨z0, hz0X, rfl⟩
        have hz0N : z0 ∈ N := hX_le_N hz0X
        have hcN : z0 * a * z0⁻¹ ∈ N := hNnormal.conj_mem a haN z0
        have hca : IsConj a (z0 * a * z0⁻¹) := isConj_iff.2 ⟨z0, rfl⟩
        have hdN : d ∈ N := by
          obtain ⟨y, hy⟩ := isConj_iff.1 hda
          rw [← hy]
          exact hNnormal.conj_mem a haN y
        rcases h132 (z0 * a * z0⁻¹) d hca hda with hcomm | ⟨z, hz, hzd⟩
        · constructor
          · refine ⟨z0, hz0X, ?_⟩
            rw [hcomm.symm]
            group
          · refine ⟨z0, hz0X, ?_⟩
            calc d⁻¹ * (z0 * a * z0⁻¹) * d
                = d⁻¹ * ((z0 * a * z0⁻¹) * d) := by group
              _ = d⁻¹ * (d * (z0 * a * z0⁻¹)) := by rw [hcomm]
              _ = z0 * a * z0⁻¹ := by group
        · exfalso
          apply hdC1
          have hcdN : Subgroup.closure ({(z0 * a * z0⁻¹), d} : Set Y) ≤ N := by
            rw [Subgroup.closure_le]
            intro w hw
            rcases hw with rfl | rfl
            · exact hcN
            · exact hdN
          have hzN : z ∈ N := hcdN hz
          refine ⟨z * z0, N.mul_mem hzN hz0N, ?_⟩
          rw [hzd]
          group
    · intro c hc
      exact ⟨by simpa using hc, by simpa using hc⟩
    · intro x y _ _ ihx ihy
      intro c hc
      have h1 : y * c * y⁻¹ ∈ C2 := (ihy c hc).1
      have h2 : x * (y * c * y⁻¹) * x⁻¹ ∈ C2 := (ihx (y * c * y⁻¹) h1).1
      have h3 : x⁻¹ * c * x ∈ C2 := (ihx c hc).2
      have h4 : y⁻¹ * (x⁻¹ * c * x) * y ∈ C2 := (ihy (x⁻¹ * c * x) h3).2
      constructor
      · convert h2 using 1
        group
      · convert h4 using 1
        group
    · intro x _ ihx
      intro c hc
      have h1 : x⁻¹ * c * x ∈ C2 := (ihx c hc).2
      have h2 : x * c * x⁻¹ ∈ C2 := (ihx c hc).1
      constructor
      · convert h1 using 1
        group
      · convert h2 using 1
        group
  have hC1C2 : C1 ⊆ C2 := by
    rintro x ⟨n, hn, rfl⟩
    exact (key n hn a haC2).1
  have hC2C1 : C2 ⊆ C1 := by
    rintro x ⟨z, hzX, rfl⟩
    exact ⟨z, hX_le_N hzX, rfl⟩
  let K₀ : Subgroup X :=
    Subgroup.normalClosure ({(⟨a, mem_oddClassSub a⟩ : X)} : Set X)
  let M₀ : Subgroup Y := K₀.map X.subtype
  have hK0normal : K₀.Normal := by rw [show K₀ = _ from rfl]; infer_instance
  have hC2M : C2 ⊆ M₀ := by
    rintro x ⟨z, hzX, rfl⟩
    have hmem : (⟨z, hzX⟩ : X) * (⟨a, mem_oddClassSub a⟩ : X) * (⟨z, hzX⟩ : X)⁻¹ ∈ K₀ :=
      hK0normal.conj_mem (⟨a, mem_oddClassSub a⟩ : X)
        (Subgroup.subset_normalClosure (Set.mem_singleton _)) (⟨z, hzX⟩ : X)
    exact Subgroup.mem_map_of_mem X.subtype hmem
  have hXM : X ≤ M₀ := by
    rw [hXeq, Subgroup.closure_le]
    exact fun x hx => hC2M (hC1C2 hx)
  have hM_eq_X : M₀ = X := le_antisymm (Subgroup.map_subtype_le K₀) hXM
  have htop : (⊤ : Subgroup X).map X.subtype = X := by
    rw [Subgroup.map_top, Subgroup.range_subtype]
  have hmap : K₀.map X.subtype = (⊤ : Subgroup X).map X.subtype :=
    hM_eq_X.trans htop.symm
  exact Subgroup.map_subtype_inj.mp hmap

theorem orderOf_oddClassSub (a : Y) :
    orderOf (⟨a, mem_oddClassSub a⟩ : ↥(oddClassSub a)) = orderOf a :=
  Subgroup.orderOf_mk a (mem_oddClassSub a)

theorem isOddTransp_oddClassSub [Finite Y] {a : Y} (ha : orderOf a = 2)
    (h132 : ∀ c d : Y, IsConj a c → IsConj a d →
      c * d = d * c ∨ ∃ z ∈ Subgroup.closure ({c, d} : Set Y), d = z * c * z⁻¹) :
    IsOddTransp {x : ↥(oddClassSub a) | IsConj (⟨a, mem_oddClassSub a⟩ : ↥(oddClassSub a)) x} := by
  have hclass := isOddTransp_class_of_comm_or_conj ha h132
  constructor
  · intro d hd
    have hd' : IsConj a (d : Y) := MonoidHom.map_isConj (Subgroup.subtype (oddClassSub a)) hd
    rw [← Subgroup.orderOf_coe d]
    exact hclass.1 (d : Y) hd'
  · intro d hd e he
    have hd' : IsConj a (d : Y) := MonoidHom.map_isConj (Subgroup.subtype (oddClassSub a)) hd
    have he' : IsConj a (e : Y) := MonoidHom.map_isConj (Subgroup.subtype (oddClassSub a)) he
    rw [← Subgroup.orderOf_coe (d * e)]
    exact hclass.2 (d : Y) hd' (e : Y) he'

end CFSG.LocalAnalysis.WeakClosure81

end
