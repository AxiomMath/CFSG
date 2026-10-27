module

public import CFSG.RankThree.GF2n.Stroth80.Sec39

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

omit [Finite G] in
@[expose] def CommQ (hQ : M ≤ Subgroup.normalizer (Q : Set G)) (t : G) : Subgroup G where
  carrier := {r | r ∈ M ∧ ⁅r, t⁆ ∈ Q}
  mul_mem' := by
    rintro a b ⟨haM, ha⟩ ⟨hbM, hb⟩
    refine ⟨M.mul_mem haM hbM, ?_⟩
    have e : ⁅a * b, t⁆ = (a * ⁅b, t⁆ * a⁻¹) * ⁅a, t⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact Q.mul_mem ((Subgroup.mem_normalizer_iff.mp (hQ haM) _).mp hb) ha
  one_mem' := ⟨M.one_mem, by simpa [commutatorElement_def] using Q.one_mem⟩
  inv_mem' := by
    rintro a ⟨haM, ha⟩
    refine ⟨M.inv_mem haM, ?_⟩
    have e : ⁅a⁻¹, t⁆ = a⁻¹ * ⁅a, t⁆⁻¹ * a⁻¹⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hQ (M.inv_mem haM)) _).mp (Q.inv_mem ha)

omit [Finite G] in
theorem mem_CommQ {hQ : M ≤ Subgroup.normalizer (Q : Set G)} {t x : G} :
    x ∈ CommQ hQ t ↔ x ∈ M ∧ ⁅x, t⁆ ∈ Q := Iff.rfl

theorem Ctx.Rt_le_CommQ (hc : Ctx M Q Z B) (t : G) :
    Rt M (LB M Q B) t ≤ CommQ hc.hyp.Q_normal.2 t := by
  refine iSup₂_le fun m hm => iSup_le fun htm x hx => ?_
  exact mem_CommQ.mpr ⟨hc.conj_LB_le_M hm hx, hc.comm_mem_Q_of_conj hm hx htm⟩

theorem Ctx.Rt_comm_mem_Q (hc : Ctx M Q Z B) {t r : G} (hr : r ∈ Rt M (LB M Q B) t) :
    ⁅r, t⁆ ∈ Q :=
  (mem_CommQ.mp (hc.Rt_le_CommQ t hr)).2

theorem Ctx.mem_CQt_conj_iff (hc : Ctx M Q Z B) {m : G} (hm : m ∈ M) (L : Subgroup G) (x : G) :
    x ∈ CQt Q Z (conjSubgroup m L) ↔ m⁻¹ * x * m ∈ CQt Q Z L := by
  have hQ : ∀ y, y ∈ Q ↔ m⁻¹ * y * m ∈ Q := fun y => by
    have h := mem_conjSubgroup (g := m) (T := Q) (x := y)
    rwa [hc.conj_Q_eq hm] at h
  have hZ : ∀ y, y ∈ Z ↔ m⁻¹ * y * m ∈ Z := fun y => by
    have h := mem_conjSubgroup (g := m) (T := Z) (x := y)
    rwa [hc.conj_Z_eq hm] at h
  constructor
  · rintro ⟨hxQ, hx⟩
    refine ⟨(hQ x).mp hxQ, fun t ht => ?_⟩
    have h1 : m * t * m⁻¹ ∈ conjSubgroup m L := ⟨t, ht, rfl⟩
    have h2 := (hZ _).mp (hx _ h1)
    have e : m⁻¹ * ⁅m * t * m⁻¹, x⁆ * m = ⁅t, m⁻¹ * x * m⁆ := by
      simp only [commutatorElement_def]; group
    rwa [e] at h2
  · rintro ⟨hxQ, hx⟩
    refine ⟨(hQ x).mpr hxQ, fun t ht => ?_⟩
    have h1 : m⁻¹ * t * m ∈ L := mem_conjSubgroup.mp ht
    have h2 := hx _ h1
    rw [hZ]
    have e : m⁻¹ * ⁅t, x⁆ * m = ⁅m⁻¹ * t * m, m⁻¹ * x * m⁆ := by
      simp only [commutatorElement_def]; group
    rwa [e]

theorem Ctx.CQt_conj (hc : Ctx M Q Z B) {m : G} (hm : m ∈ M)
    (h35 : CQt Q Z (LB M Q B) = ((B ⊔ Z : Subgroup G) : Set G)) :
    CQt Q Z (LB M Q (conjSubgroup m B)) = ((conjSubgroup m B ⊔ Z : Subgroup G) : Set G) := by
  ext x
  rw [hc.LB_conj hm]
  show x ∈ CQt Q Z (conjSubgroup m (LB M Q B)) ↔ _
  rw [hc.mem_CQt_conj_iff hm, h35]
  have hZm : conjSubgroup m (B ⊔ Z : Subgroup G) = conjSubgroup m B ⊔ Z := by
    rw [conjSubgroup_sup', hc.conj_Z_eq hm]
  rw [← hZm]
  exact mem_conjSubgroup.symm

omit [Finite G] in
theorem isElemAbelian_two_closure {T : Set G} (hcomm : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x)
    (hsq : ∀ x ∈ T, x ^ 2 = 1) : CFSG.Open.IsElemAbelian 2 (Subgroup.closure T) := by
  have hc : IsMulCommutative (Subgroup.closure T) :=
    Subgroup.isMulCommutative_closure fun x hx y hy _ => hcomm x hx y hy
  refine ⟨hc, fun x hx => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hsq x hx
  | one => exact one_pow 2
  | mul x y hx hy ihx ihy =>
    have hxy : Commute x y := congrArg Subtype.val (hc.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    rw [hxy.mul_pow, ihx, ihy, one_mul]
  | inv x hx ihx => rw [inv_pow, ihx, inv_one]

theorem Ctx.Vt_isElemAbelian (hc : Ctx M Q Z B)
    (h35 : CQt Q Z (LB M Q B) = ((B ⊔ Z : Subgroup G) : Set G)) {t : G} (ht : t ∈ LB M Q B)
    (htQ : t ∉ Q) :
    IsElemAbelian 2 (Vt M (LB M Q B) B Z t) := by
  set T : Set G := (Z : Set G) ∪
    {x | ∃ m ∈ M, t ∈ conjSubgroup m (LB M Q B) ∧ x ∈ conjSubgroup m B} with hT
  have hle : Vt M (LB M Q B) B Z t ≤ Subgroup.closure T := by
    refine sup_le (fun z hz => Subgroup.subset_closure (Or.inl hz))
      (iSup₂_le fun m hm => iSup_le fun htm x hx => ?_)
    exact Subgroup.subset_closure (Or.inr ⟨m, hm, htm, hx⟩)
  have hTV : ∀ x ∈ T, x ∈ Vt M (LB M Q B) B Z t := by
    rintro x (hx | ⟨m, hm, htm, hx⟩)
    · exact sec39_Z_le_Vt hx
    · exact sec39_conjB_le_Vt hm htm hx
  have hcomm : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := fun x hx y hy =>
    hc.Vt_comm (fun m hm => hc.CQt_conj hm h35) ht htQ x (hTV x hx) y (hTV y hy)
  have hsq : ∀ x ∈ T, x ^ 2 = 1 := by
    rintro x (hx | ⟨m, hm, htm, hx⟩)
    · exact hc.hyp.isElemAbelian_Z.2 x hx
    · exact (hc.conj_of_mem hm).isElemAbelian_B.2 x hx
  exact (isElemAbelian_two_closure hcomm hsq).mono hle

theorem Ctx.mem_CN {hc : Ctx M Q Z B} {t x : G} :
    x ∈ hc.CN t ↔ x ∈ Rt M (LB M Q B) t ∧ ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅x, v⁆ ∈ Z := Iff.rfl

theorem Ctx.not_Rt_le_CN (hc : Ctx M Q Z B)
    (h35 : CQt Q Z (LB M Q B) = ((B ⊔ Z : Subgroup G) : Set G)) {t : G} (ht : t ∈ LB M Q B)
    (hR : Rt M (LB M Q B) t ≠ LB M Q B) : ¬ Rt M (LB M Q B) t ≤ hc.CN t := by
  intro hle
  apply hR
  refine le_antisymm ?_ (le_Rt (M := M) (LB M Q B) ht)
  refine iSup₂_le fun m hm => iSup_le fun htm => ?_
  have hc' := hc.conj_of_mem hm
  have hBle : conjSubgroup m B ≤ Z ⊔ B := by
    rw [sup_comm]
    intro v hv
    have hvV : v ∈ Vt M (LB M Q B) B Z t := sec39_conjB_le_Vt hm htm hv
    have hvC : v ∈ CQt Q Z (LB M Q B) :=
      ⟨hc.Vt_le_Q t hvV, fun l hl =>
        (Ctx.mem_CN.mp (hle (le_Rt (M := M) (LB M Q B) ht hl))).2 v hvV⟩
    rw [h35] at hvC
    exact hvC
  obtain ⟨p, hp, hpB⟩ := hc.exists_conj_of_le_ZB hc' hBle
  have hpL : p ∈ LB M Q B := Subgroup.mem_sup_left hp
  have hpM : p ∈ M := hc.hyp.Q_normal.1 hp
  have hLp : conjSubgroup p (LB M Q B) = LB M Q B :=
    conjSubgroup_eq_self_iff.mpr (Subgroup.le_normalizer hpL)
  have h : conjSubgroup m (LB M Q B) = LB M Q B := by
    rw [← hc.LB_conj hm, ← hpB, hc.LB_conj hpM, hLp]
  exact h.le

end CFSG.RankThree.GF2n.Stroth80
