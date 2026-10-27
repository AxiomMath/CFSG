module

public import CFSG.Quasithin.Recognition.RuTypeJ23b
public import CFSG.GroupTheory.SuzukiTwoGroupsBasic

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits
open scoped MatrixGroups commutatorElement

variable {G : Type*} [Group G]

theorem mem_normalizer_of_conj_mem [Finite G] {H : Subgroup G} {g : G}
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  have hle : H.map (MulAut.conj g).toMonoidHom ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  have heq : H.map (MulAut.conj g).toMonoidHom = H :=
    Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  have h1 : g * x * g⁻¹ ∈ H.map (MulAut.conj g).toMonoidHom := by rw [heq]; exact hx
  obtain ⟨y, hy, hyx⟩ := h1
  have : y = x := by simpa [MulAut.conj_apply] using hyx
  rw [← this]
  exact hy

namespace SL3

@[expose] def IsX (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) : Prop :=
  ∃ F ∈ fixC0List, ∃ Y ∈ st1List, A = F + Y

instance : DecidablePred IsX := fun A => by unfold IsX; infer_instance

theorem card_IsX : Nat.card {A : Matrix (Fin 3) (Fin 3) (ZMod 2) // IsX A} = 32 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem card_st1 :
    Nat.card {A : Matrix (Fin 3) (Fin 3) (ZMod 2) // A ∈ st1List} = 8 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem IsX.add {A B : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hA : IsX A) (hB : IsX B) :
    IsX (A + B) := by
  obtain ⟨F, hF, Y, hY, rfl⟩ := hA
  obtain ⟨F', hF', Y', hY', rfl⟩ := hB
  exact ⟨F + F', fixC0_add F hF F' hF', Y + Y', st1_add Y hY Y' hY',
    add_add_add_comm F Y F' Y'⟩

theorem IsX.trace {A : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hA : IsX A) : IsTraceZero A := by
  obtain ⟨F, hF, Y, hY, rfl⟩ := hA
  unfold IsTraceZero
  rw [Matrix.trace_add, (fixC0_props F hF).1, (st1_props Y hY).1, add_zero]

theorem isX_of_fix {F : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hF : F ∈ fixC0List) : IsX F :=
  ⟨F, hF, 0, by decide, (add_zero F).symm⟩

theorem isX_of_st1 {Y : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hY : Y ∈ st1List) : IsX Y :=
  ⟨0, by decide, Y, hY, (zero_add Y).symm⟩

theorem IsX.stAct_b0 {A : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hA : IsX A) :
    IsX (stAct b0 A) := by
  obtain ⟨F, hF, Y, hY, rfl⟩ := hA
  exact ⟨_, (fixC0_props F hF).2.2.1, _, (st1_props Y hY).2.2.1, stAct_add b0 F Y⟩

theorem st1_iterate (n : ℕ) {Y : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hY : Y ∈ st1List) :
    (stAct c0)^[n] Y ∈ st1List := by
  induction n with
  | zero => exact hY
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (st1_props _ ih).2.1

theorem fixC0_iterate (n : ℕ) {F : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hF : F ∈ fixC0List) :
    (stAct c0)^[n] F = F := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    exact (fixC0_props F hF).2.1

end SL3

namespace RuDataM

variable (M : RuDataM G)

omit [Group G] in
theorem card_preimage [Group G] [Finite G] (M : RuDataM G) (W : Subgroup G)
    (P : Matrix (Fin 3) (Fin 3) (ZMod 2) → Prop) (hWS : W ≤ ruS M.L)
    (hW : ∀ x (hx : x ∈ ruS M.L), x ∈ W ↔ P (Multiplicative.toAdd (M.χ ⟨x, hx⟩)))
    (hP : ∀ A, P A → IsTraceZero A) :
    Nat.card W = 8 * Nat.card {A // P A} := by
  classical
  let f : W.subgroupOf (ruS M.L) →* Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
    M.χ.comp (W.subgroupOf (ruS M.L)).subtype
  have h := Subgroup.card_ker_mul_card_range f
  rw [card_subgroupOf_of_le hWS] at h
  have hP0 : P 0 := by
    have := (hW 1 (ruS M.L).one_mem).mp W.one_mem
    rwa [show (⟨1, (ruS M.L).one_mem⟩ : ruS M.L) = 1 from rfl, map_one, toAdd_one] at this
  have hker : Nat.card f.ker = 8 := by
    rw [← M.toRuData.card_V]
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1.1.1, ?_⟩
        invFun := fun v => ⟨⟨⟨v.1, M.toRuData.V_le_S v.2⟩, ?_⟩, ?_⟩
        left_inv := fun x => rfl
        right_inv := fun v => rfl }
    · have hx := x.2
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hx
      have : x.1.1 ∈ M.χ.ker := hx
      rw [M.χ_ker, Subgroup.mem_subgroupOf] at this
      exact this
    · show v.1 ∈ W
      have hv : (⟨v.1, M.toRuData.V_le_S v.2⟩ : ruS M.L) ∈ M.χ.ker := by
        rw [M.χ_ker, Subgroup.mem_subgroupOf]
        exact v.2
      refine (hW v.1 (M.toRuData.V_le_S v.2)).mpr ?_
      rw [MonoidHom.mem_ker.mp hv, toAdd_one]
      exact hP0
    · show M.χ ⟨v.1, M.toRuData.V_le_S v.2⟩ = 1
      have hv : (⟨v.1, M.toRuData.V_le_S v.2⟩ : ruS M.L) ∈ M.χ.ker := by
        rw [M.χ_ker, Subgroup.mem_subgroupOf]
        exact v.2
      exact hv
  have hrange : Nat.card f.range = Nat.card {A // P A} := by
    refine Nat.card_congr
      { toFun := fun y => ⟨Multiplicative.toAdd y.1, ?_⟩
        invFun := fun A => ⟨Multiplicative.ofAdd A.1, ?_⟩
        left_inv := fun y => rfl
        right_inv := fun A => rfl }
    · obtain ⟨x, hx⟩ := y.2
      rw [← hx]
      exact (hW _ x.1.2).mp (Subgroup.mem_subgroupOf.mp x.2)
    · obtain ⟨s, hs⟩ := M.χ_surj A.1 (hP A.1 A.2)
      have hsW : (s : G) ∈ W := (hW s s.2).mpr (by rw [hs, toAdd_ofAdd]; exact A.2)
      exact ⟨⟨s, Subgroup.mem_subgroupOf.mpr hsW⟩, hs⟩
  rw [hker, hrange] at h
  exact h.symm

@[expose] def S1 : Subgroup G where
  carrier := {x | ∃ hx : x ∈ ruS M.L, Multiplicative.toAdd (M.χ ⟨x, hx⟩) ∈ SL3.st1List}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, ?_⟩
    rw [show (⟨a * b, mul_mem ha hb⟩ : ruS M.L) = ⟨a, ha⟩ * ⟨b, hb⟩ from rfl, M.toAdd_χ_mul]
    exact SL3.st1_add _ ha' _ hb'
  one_mem' := ⟨(ruS M.L).one_mem, by
    rw [show (⟨1, (ruS M.L).one_mem⟩ : ruS M.L) = 1 from rfl, map_one, toAdd_one]
    decide⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨inv_mem ha, ?_⟩
    rw [show (⟨a⁻¹, inv_mem ha⟩ : ruS M.L) = (⟨a, ha⟩ : ruS M.L)⁻¹ from rfl, M.toAdd_χ_inv]
    exact ha'

@[expose] def S3 : Subgroup G where
  carrier := {x | ∃ hx : x ∈ ruS M.L, SL3.IsX (Multiplicative.toAdd (M.χ ⟨x, hx⟩))}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, ?_⟩
    rw [show (⟨a * b, mul_mem ha hb⟩ : ruS M.L) = ⟨a, ha⟩ * ⟨b, hb⟩ from rfl, M.toAdd_χ_mul]
    exact ha'.add hb'
  one_mem' := ⟨(ruS M.L).one_mem, by
    rw [show (⟨1, (ruS M.L).one_mem⟩ : ruS M.L) = 1 from rfl, map_one, toAdd_one]
    exact SL3.isX_of_fix (by decide)⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨inv_mem ha, ?_⟩
    rw [show (⟨a⁻¹, inv_mem ha⟩ : ruS M.L) = (⟨a, ha⟩ : ruS M.L)⁻¹ from rfl, M.toAdd_χ_inv]
    exact ha'

theorem S1_le_S : M.S1 ≤ ruS M.L := fun _ ⟨hx, _⟩ => hx

theorem S3_le_S : M.S3 ≤ ruS M.L := fun _ ⟨hx, _⟩ => hx

theorem S1_le_S3 : M.S1 ≤ M.S3 := fun _ ⟨hx, hY⟩ => ⟨hx, SL3.isX_of_st1 hY⟩

theorem V_le_S1 : ruV M.L ≤ M.S1 := fun v hv => by
  refine ⟨M.toRuData.V_le_S hv, ?_⟩
  have hk : (⟨v, M.toRuData.V_le_S hv⟩ : ruS M.L) ∈ M.χ.ker := by
    rw [M.χ_ker, Subgroup.mem_subgroupOf]
    exact hv
  rw [MonoidHom.mem_ker.mp hk, toAdd_one]
  decide

variable [Finite G]

theorem S0_le_S3 : M.S0 ≤ M.S3 := fun _ hx =>
  ⟨(M.mem_S0.mp hx).1, SL3.isX_of_fix (M.χ_S0 hx)⟩

theorem card_S1 : Nat.card M.S1 = 2 ^ 6 := by
  rw [M.card_preimage M.S1 (· ∈ SL3.st1List) M.S1_le_S
    (fun x hx => ⟨fun ⟨_, h⟩ => h, fun h => ⟨hx, h⟩⟩)
    (fun A hA => (SL3.st1_props A hA).1), SL3.card_st1]
  norm_num

theorem card_S3 : Nat.card M.S3 = 2 ^ 8 := by
  rw [M.card_preimage M.S3 SL3.IsX M.S3_le_S
    (fun x hx => ⟨fun ⟨_, h⟩ => h, fun h => ⟨hx, h⟩⟩) (fun A hA => hA.trace),
    SL3.card_IsX]
  norm_num

theorem cform_fix_c0 {F A : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hF : F ∈ SL3.fixC0List)
    (hA : IsTraceZero A) :
    M.cform F (stAct SL3.c0 A) = natAct3 SL3.c0 (M.cform F A) := by
  obtain ⟨hFt, hFc, -⟩ := SL3.fixC0_props F hF
  have := M.cform_stAct hFt hA M.cel
  rw [M.θ_cel, hFc] at this
  exact this

theorem cform_fix_st1 {F Y : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hF : F ∈ SL3.fixC0List)
    (hY : Y ∈ SL3.st1List) : M.cform F Y = 0 := by
  have hFt : IsTraceZero F := (SL3.fixC0_props F hF).1
  obtain ⟨hYt, hY1, -, hcub, -⟩ := SL3.st1_props Y hY
  obtain ⟨hY1t, hY2, -⟩ := SL3.st1_props _ hY1
  obtain ⟨hY2t, hY3, -⟩ := SL3.st1_props _ hY2
  have hY3t : IsTraceZero _ := (SL3.st1_props _ hY3).1
  have h23 : IsTraceZero (stAct SL3.c0 (stAct SL3.c0 (stAct SL3.c0 Y)) +
      stAct SL3.c0 (stAct SL3.c0 Y)) := by
    unfold IsTraceZero at *
    rw [Matrix.trace_add, hY3t, hY2t, add_zero]
  have h0 := M.cform_zero hFt
  rw [← hcub, M.cform_add_right hFt h23 hYt, M.cform_add_right hFt hY3t hY2t,
    M.cform_fix_c0 hF hY2t, M.cform_fix_c0 hF hY1t, M.cform_fix_c0 hF hYt] at h0
  exact SL3.c0_cubic'_vec _ h0

theorem cform_fix_fix {F F' : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hF : F ∈ SL3.fixC0List)
    (hF' : F' ∈ SL3.fixC0List) : M.cform F F' = 0 := by
  obtain ⟨hF't, hF'c, -⟩ := SL3.fixC0_props F' hF'
  have := M.cform_fix_c0 hF hF't
  rw [hF'c] at this
  exact SL3.c0_fix_vec _ this.symm

theorem cform_fix_X {F A : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hF : F ∈ SL3.fixC0List)
    (hA : SL3.IsX A) : M.cform F A = 0 := by
  obtain ⟨F', hF', Y, hY, rfl⟩ := hA
  rw [M.cform_add_right (SL3.fixC0_props F hF).1 (SL3.fixC0_props F' hF').1
    (SL3.st1_props Y hY).1, M.cform_fix_fix hF hF', M.cform_fix_st1 hF hY, add_zero]

theorem comm_fix_S3 {x y : G} (hx : x ∈ ruS M.L)
    (hxF : Multiplicative.toAdd (M.χ ⟨x, hx⟩) ∈ SL3.fixC0List) (hy : y ∈ M.S3) :
    x * y = y * x := by
  obtain ⟨hyS, hyX⟩ := hy
  have h := (M.comm_eq_one_iff_cform ⟨x, hx⟩ ⟨y, hyS⟩).mpr (M.cform_fix_X hxF hyX)
  calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
    _ = y * x := by rw [show x * y * x⁻¹ * y⁻¹ = 1 from h, one_mul]

theorem comm_S0_S3 {x y : G} (hx : x ∈ M.S0) (hy : y ∈ M.S3) : x * y = y * x :=
  M.comm_fix_S3 (M.mem_S0.mp hx).1 (M.χ_S0 hx) hy

theorem not_mem_V_of_S0 {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) : s ∉ ruV M.L :=
  fun hV => hs1 (M.eq_one_of_mem_S0_V hs hV)

theorem centralizer_eq_S3 {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) :
    ruS M.L ⊓ Subgroup.centralizer ({s} : Set G) = M.S3 := by
  have hle : M.S3 ≤ ruS M.L ⊓ Subgroup.centralizer ({s} : Set G) := fun y hy =>
    ⟨M.S3_le_S hy, Subgroup.mem_centralizer_singleton_iff.mpr (M.comm_S0_S3 hs hy).symm⟩
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [M.card_centralizer_S (M.mem_S0.mp hs).1 (M.not_mem_V_of_S0 hs hs1), M.card_S3]

theorem exists_S0_S1 {x : G} (hx : x ∈ M.S3) : ∃ x₀ ∈ M.S0, ∃ y ∈ M.S1, x = x₀ * y := by
  obtain ⟨hxS, F, hF, Y, hY, hFY⟩ := hx
  obtain ⟨x₀, hx₀, hx₀F⟩ := M.exists_S0_χ hF
  have hx₀S := (M.mem_S0.mp hx₀).1
  refine ⟨x₀, hx₀, x₀⁻¹ * x, ⟨mul_mem (inv_mem hx₀S) hxS, ?_⟩, by group⟩
  rw [show (⟨x₀⁻¹ * x, mul_mem (inv_mem hx₀S) hxS⟩ : ruS M.L) =
    (⟨x₀, hx₀S⟩ : ruS M.L)⁻¹ * ⟨x, hxS⟩ from rfl, M.toAdd_χ_mul, M.toAdd_χ_inv, hx₀F, hFY,
    ← add_assoc]
  have h2 : F + F = 0 := by
    ext i j
    have h : ∀ a : ZMod 2, a + a = 0 := by decide
    exact h _
  rw [h2, zero_add]
  exact hY

theorem S3_eq_sup : M.S3 = M.S0 ⊔ M.S1 := by
  refine le_antisymm (fun x hx => ?_) (sup_le M.S0_le_S3 M.S1_le_S3)
  obtain ⟨x₀, hx₀, y, hy, rfl⟩ := M.exists_S0_S1 hx
  exact mul_mem (Subgroup.mem_sup_left hx₀) (Subgroup.mem_sup_right hy)

theorem S0_inf_S1 : M.S0 ⊓ M.S1 = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => ?_
  obtain ⟨hx0, hxS, hx1⟩ := hx
  have h0 := SL3.fixC0_st1 _ (M.χ_S0 hx0) hx1
  refine M.eq_one_of_mem_S0_V hx0 ?_
  have hk : (⟨x, hxS⟩ : ruS M.L) ∈ M.χ.ker := by
    rw [MonoidHom.mem_ker]
    exact Multiplicative.toAdd.injective (by rw [h0, toAdd_one])
  rw [M.χ_ker, Subgroup.mem_subgroupOf] at hk
  exact hk

theorem comm_S0_S1 {x y : G} (hx : x ∈ M.S0) (hy : y ∈ M.S1) : x * y = y * x :=
  M.comm_S0_S3 hx (M.S1_le_S3 hy)

omit [Finite G] in
theorem sq_mem_V {x : G} (hx : x ∈ ruS M.L) : x ^ 2 ∈ ruV M.L := by
  have hk : (⟨x, hx⟩ : ruS M.L) ^ 2 ∈ M.χ.ker := by
    rw [MonoidHom.mem_ker]
    apply Multiplicative.toAdd.injective
    rw [pow_two, M.toAdd_χ_mul, toAdd_one]
    ext i j
    have h2 : ∀ a : ZMod 2, a + a = 0 := by decide
    exact h2 _
  rw [M.χ_ker, Subgroup.mem_subgroupOf] at hk
  exact hk

omit [Finite G] in
theorem sq_eq_one_of_V {v : G} (hv : v ∈ ruV M.L) : v ^ 2 = 1 := M.one.center_elem.2 v hv

omit [Finite G] in
theorem pow_four_S {x : G} (hx : x ∈ ruS M.L) : x ^ 4 = 1 := by
  rw [show 4 = 2 * 2 by rfl, pow_mul]
  exact M.sq_eq_one_of_V (M.sq_mem_V hx)

theorem comm_cel_mem_S (n : ℕ) {x : G} (hx : x ∈ ruS M.L) :
    ⁅x, (M.cel : G) ^ n⁆ ∈ ruS M.L := by
  have hcx : (M.cel : G) ^ n * x⁻¹ * ((M.cel : G) ^ n)⁻¹ ∈ ruS M.L :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 M.L (M.cel ^ n).2) x⁻¹).mp
      (inv_mem hx)
  rw [commutatorElement_def, show x * (M.cel : G) ^ n * x⁻¹ * ((M.cel : G) ^ n)⁻¹ =
    x * ((M.cel : G) ^ n * x⁻¹ * ((M.cel : G) ^ n)⁻¹) by group]
  exact mul_mem hx hcx

theorem toAdd_χ_comm_cel (n : ℕ) {x : G} (hx : x ∈ ruS M.L) :
    Multiplicative.toAdd (M.χ ⟨⁅x, (M.cel : G) ^ n⁆, M.comm_cel_mem_S n hx⟩) =
      Multiplicative.toAdd (M.χ ⟨x, hx⟩) +
        (stAct SL3.c0)^[n] (Multiplicative.toAdd (M.χ ⟨x, hx⟩)) := by
  have hcx : (M.cel : G) ^ n * x⁻¹ * ((M.cel : G) ^ n)⁻¹ ∈ ruS M.L :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 M.L (M.cel ^ n).2) x⁻¹).mp
      (inv_mem hx)
  have e : (⟨⁅x, (M.cel : G) ^ n⁆, M.comm_cel_mem_S n hx⟩ : ruS M.L) =
      ⟨x, hx⟩ * ⟨(M.cel : G) ^ n * x⁻¹ * ((M.cel : G) ^ n)⁻¹, hcx⟩ := by
    apply Subtype.ext
    simp only [commutatorElement_def, Subgroup.coe_mul]
    group
  have e2 := M.χ_equiv (M.cel ^ n) ⟨x⁻¹, inv_mem hx⟩ ⟨_, hcx⟩ rfl
  rw [map_pow, M.θ_cel, SL3.stAct_pow,
    show (⟨x⁻¹, inv_mem hx⟩ : ruS M.L) = (⟨x, hx⟩ : ruS M.L)⁻¹ from rfl, M.toAdd_χ_inv] at e2
  rw [e, M.toAdd_χ_mul, e2, toAdd_ofAdd]

theorem stAct_iterate_add (n : ℕ) (A B : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    (stAct SL3.c0)^[n] (A + B) = (stAct SL3.c0)^[n] A + (stAct SL3.c0)^[n] B := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      Function.iterate_succ_apply', ih, SL3.stAct_add]

theorem commutator_le_S1 {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) :
    ⁅ruS M.L ⊓ Subgroup.centralizer ({s} : Set G), M.B7⁆ ≤ M.S1 := by
  rw [Subgroup.commutator_le, M.centralizer_eq_S3 hs hs1]
  intro x hx g hg
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  obtain ⟨n, hn⟩ := exists_nat_zpow (by norm_num) M.cel_pow_seven k
  rw [hn]
  obtain ⟨hxS, F, hF, Y, hY, hFY⟩ := hx
  refine ⟨M.comm_cel_mem_S n hxS, ?_⟩
  rw [M.toAdd_χ_comm_cel n hxS, hFY, stAct_iterate_add, SL3.fixC0_iterate n hF]
  have h2 : F + Y + (F + (stAct SL3.c0)^[n] Y) = Y + (stAct SL3.c0)^[n] Y := by
    ext i j
    have h : ∀ a b c : ZMod 2, a + b + (a + c) = b + c := by decide
    exact h _ _ _
  rw [h2]
  exact SL3.st1_add _ hY _ (SL3.st1_iterate n hY)

theorem exists_comm_cel_V {v : G} (hv : v ∈ ruV M.L) :
    ∃ w ∈ ruV M.L, ⁅w, (M.cel : G)⁆ = v := by
  have hmem : ∀ w : ruV M.L, ⁅(w : G), (M.cel : G)⁆ ∈ ruV M.L := fun w => by
    rw [commutatorElement_def, show (w : G) * M.cel * (w : G)⁻¹ * (M.cel : G)⁻¹ =
      (w : G) * ((M.cel : G) * (w : G)⁻¹ * (M.cel : G)⁻¹) by group]
    exact mul_mem w.2 (M.toRuData.conj_mem_V M.cel.2 (inv_mem w.2))
  let f : ruV M.L → ruV M.L := fun w => ⟨_, hmem w⟩
  have hf : Function.Injective f := by
    intro w w' h
    have h' : ⁅(w : G), (M.cel : G)⁆ = ⁅(w' : G), (M.cel : G)⁆ := congrArg Subtype.val h
    rw [commutatorElement_def, commutatorElement_def] at h'
    have hu : (M.cel : G) * ((w' : G)⁻¹ * w) = ((w' : G)⁻¹ * w) * M.cel := by
      have e1 : (w : G) * M.cel * (w : G)⁻¹ = (w' : G) * M.cel * (w' : G)⁻¹ := by
        have := congrArg (· * (M.cel : G)) h'
        simpa using this
      calc (M.cel : G) * ((w' : G)⁻¹ * w) =
          (w' : G)⁻¹ * ((w' : G) * M.cel * (w' : G)⁻¹) * w := by group
        _ = (w' : G)⁻¹ * ((w : G) * M.cel * (w : G)⁻¹) * w := by rw [e1]
        _ = ((w' : G)⁻¹ * w) * M.cel := by group
    have huV : (w' : G)⁻¹ * w ∈ ruV M.L := mul_mem (inv_mem w'.2) w.2
    have h1 := M.eq_one_of_mem_S0_V (M.mem_S0.mpr ⟨M.toRuData.V_le_S huV, hu⟩) huV
    rw [inv_mul_eq_one] at h1
    exact Subtype.ext h1.symm
  obtain ⟨w, hw⟩ := Finite.surjective_of_injective hf ⟨v, hv⟩
  exact ⟨w, w.2, congrArg Subtype.val hw⟩

theorem commutator_eq_S1 {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) :
    ⁅ruS M.L ⊓ Subgroup.centralizer ({s} : Set G), M.B7⁆ = M.S1 := by
  refine le_antisymm (M.commutator_le_S1 hs hs1) (fun y hy => ?_)
  rw [M.centralizer_eq_S3 hs hs1]
  obtain ⟨hyS, hyY⟩ := hy
  obtain ⟨Y', hY', hYY'⟩ := (SL3.st1_props _ hyY).2.2.2.2
  have hY't : IsTraceZero Y' := (SL3.st1_props Y' hY').1
  set x : ruS M.L := M.sOf Y'
  have hx : M.χ x = Multiplicative.ofAdd Y' := M.χ_sOf hY't
  have hxS3 : (x : G) ∈ M.S3 := M.S1_le_S3 ⟨x.2, by rw [hx, toAdd_ofAdd]; exact hY'⟩
  have hcomm := M.toAdd_χ_comm_cel 1 x.2
  rw [show (⟨(x : G), x.2⟩ : ruS M.L) = x from rfl, hx, toAdd_ofAdd,
    Function.iterate_one, ← hYY'] at hcomm
  have hu : (⟨⁅(x : G), (M.cel : G) ^ 1⁆, M.comm_cel_mem_S 1 x.2⟩ : ruS M.L)⁻¹ * ⟨y, hyS⟩ ∈
      M.χ.ker := by
    rw [MonoidHom.mem_ker]
    apply Multiplicative.toAdd.injective
    rw [M.toAdd_χ_mul, M.toAdd_χ_inv, hcomm, toAdd_one]
    ext i j
    have h : ∀ a : ZMod 2, a + a = 0 := by decide
    exact h _
  rw [M.χ_ker, Subgroup.mem_subgroupOf] at hu
  obtain ⟨w, hw, hwv⟩ := M.exists_comm_cel_V hu
  have hwS3 : w ∈ M.S3 := M.S1_le_S3 (M.V_le_S1 hw)
  have hxc : ⁅(x : G), (M.cel : G) ^ 1⁆ ∈ ⁅M.S3, M.B7⁆ :=
    Subgroup.commutator_mem_commutator hxS3 (Subgroup.npow_mem_zpowers _ 1)
  have hwc : ⁅w, (M.cel : G)⁆ ∈ ⁅M.S3, M.B7⁆ :=
    Subgroup.commutator_mem_commutator hwS3 (Subgroup.mem_zpowers _)
  have e : y = ⁅(x : G), (M.cel : G) ^ 1⁆ * ⁅w, (M.cel : G)⁆ := by
    rw [hwv]
    show y = ⁅(x : G), (M.cel : G) ^ 1⁆ * (⁅(x : G), (M.cel : G) ^ 1⁆⁻¹ * y)
    group
  rw [e]
  exact mul_mem hxc hwc

omit [Finite G] in
theorem conj_mem_S1_of {l : M.L} (hl : ∀ A ∈ SL3.st1List, stAct (M.θ l) A ∈ SL3.st1List)
    {y : G} (hy : y ∈ M.S1) : (l : G) * y * (l : G)⁻¹ ∈ M.S1 := by
  obtain ⟨hyS, hyY⟩ := hy
  refine ⟨(Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 M.L l.2) y).mp hyS, ?_⟩
  rw [M.χ_conj l ⟨y, hyS⟩]
  exact hl _ hyY

theorem cel_conj_S1 {y : G} (hy : y ∈ M.S1) : (M.cel : G) * y * (M.cel : G)⁻¹ ∈ M.S1 :=
  M.conj_mem_S1_of (fun A hA => by rw [M.θ_cel]; exact (SL3.st1_props A hA).2.1) hy

theorem bel_conj_S1 {y : G} (hy : y ∈ M.S1) : (M.bel : G) * y * (M.bel : G)⁻¹ ∈ M.S1 :=
  M.conj_mem_S1_of (fun A hA => by rw [M.θ_bel]; exact (SL3.st1_props A hA).2.2.1) hy

theorem bel_conj_S3 {x : G} (hx : x ∈ M.S3) : (M.bel : G) * x * (M.bel : G)⁻¹ ∈ M.S3 := by
  obtain ⟨hxS, hxX⟩ := hx
  refine ⟨(Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 M.L M.bel.2) x).mp hxS, ?_⟩
  rw [M.χ_conj M.bel ⟨x, hxS⟩, M.θ_bel]
  exact hxX.stAct_b0

theorem S3_comm_of_S1_comm (h1 : ∀ y ∈ M.S1, ∀ y' ∈ M.S1, y * y' = y' * y) :
    ∀ x ∈ M.S3, ∀ x' ∈ M.S3, x * x' = x' * x := by
  intro x hx x' hx'
  obtain ⟨a, ha, b, hb, rfl⟩ := M.exists_S0_S1 hx
  obtain ⟨a', ha', b', hb', rfl⟩ := M.exists_S0_S1 hx'
  have hab : a * a' = a' * a := congrArg Subtype.val (M.S0_elem.1.is_comm.comm ⟨a, ha⟩ ⟨a', ha'⟩)
  have h2 := M.comm_S0_S1 ha hb'
  have h3 := M.comm_S0_S1 ha' hb
  have h4 := h1 b hb b' hb'
  calc a * b * (a' * b') = a * (b * a') * b' := by group
    _ = a * (a' * b) * b' := by rw [h3]
    _ = (a * a') * (b * b') := by group
    _ = (a' * a) * (b' * b) := by rw [hab, h4]
    _ = a' * (a * b') * b := by group
    _ = a' * (b' * a) * b := by rw [h2]
    _ = a' * b' * (a * b) := by group

theorem isX_A1 : SL3.IsX !![1, 1, 0; 0, 1, 1; 0, 0, 0] :=
  ⟨_, by decide, _, by decide, SL3.decomp_A1⟩

theorem isX_B1 : SL3.IsX !![0, 0, 0; 1, 1, 0; 0, 1, 1] :=
  ⟨_, by decide, _, by decide, SL3.decomp_B1⟩

theorem isX_B2 : SL3.IsX !![0, 0, 0; 0, 0, 1; 1, 1, 0] :=
  ⟨_, by decide, _, by decide, SL3.decomp_B2⟩

theorem S1_not_comm : ¬ ∀ y ∈ M.S1, ∀ y' ∈ M.S1, y * y' = y' * y := by
  intro h1
  have h3 := M.S3_comm_of_S1_comm h1
  have hC : ∀ t ∈ M.S3, t ∉ ruV M.L → ∀ y ∈ ruS M.L, y * t = t * y → y ∈ M.S3 := by
    intro t ht htV y hy hty
    have hle : M.S3 ≤ ruS M.L ⊓ Subgroup.centralizer ({t} : Set G) := fun x hx =>
      ⟨M.S3_le_S hx, Subgroup.mem_centralizer_singleton_iff.mpr (h3 x hx t ht)⟩
    have heq := Subgroup.eq_of_le_of_card_ge hle
      (by rw [M.card_centralizer_S (M.S3_le_S ht) htV, M.card_S3])
    have hy' : y ∈ ruS M.L ⊓ Subgroup.centralizer ({t} : Set G) :=
      ⟨hy, Subgroup.mem_centralizer_singleton_iff.mpr hty⟩
    rw [← heq] at hy'
    exact hy'
  have hnotV : ∀ (x : ruS M.L), Multiplicative.toAdd (M.χ x) ≠ 0 → (x : G) ∉ ruV M.L := by
    intro x hx hV
    apply hx
    have hk : x ∈ M.χ.ker := by
      rw [M.χ_ker, Subgroup.mem_subgroupOf]
      exact hV
    rw [MonoidHom.mem_ker.mp hk, toAdd_one]
  set t : ruS M.L := M.sOf !![1, 1, 0; 0, 1, 1; 0, 0, 0]
  have ht : M.χ t = Multiplicative.ofAdd !![1, 1, 0; 0, 1, 1; 0, 0, 0] := M.χ_sOf isX_A1.trace
  have htX : (t : G) ∈ M.S3 := by
    refine ⟨t.2, ?_⟩
    rw [show (⟨(t : G), t.2⟩ : ruS M.L) = t from rfl, ht, toAdd_ofAdd]
    exact isX_A1
  have htV : (t : G) ∉ ruV M.L := hnotV t (by rw [ht, toAdd_ofAdd]; decide)
  obtain ⟨u, hu⟩ := M.θ_surj SL3.g1
  have hut : (u : G) * t * (u : G)⁻¹ ∈ ruS M.L :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 M.L u.2) t).mp t.2
  have hutχ : Multiplicative.toAdd (M.χ ⟨_, hut⟩) = !![0, 0, 0; 1, 1, 0; 0, 1, 1] := by
    rw [M.χ_conj u t, hu, ht, toAdd_ofAdd, SL3.g1_A1']
  have hutX : (u : G) * t * (u : G)⁻¹ ∈ M.S3 := ⟨hut, by rw [hutχ]; exact isX_B1⟩
  have hutV : (u : G) * t * (u : G)⁻¹ ∉ ruV M.L := hnotV ⟨_, hut⟩ (by rw [hutχ]; decide)
  set x2 : ruS M.L := M.sOf !![0, 0, 0; 0, 0, 1; 1, 1, 0]
  have hx2 : M.χ x2 = Multiplicative.ofAdd !![0, 0, 0; 0, 0, 1; 1, 1, 0] :=
    M.χ_sOf isX_B2.trace
  have hx2X : (x2 : G) ∈ M.S3 := by
    refine ⟨x2.2, ?_⟩
    rw [show (⟨(x2 : G), x2.2⟩ : ruS M.L) = x2 from rfl, hx2, toAdd_ofAdd]
    exact isX_B2
  have hc := h3 _ hx2X _ htX
  have hux2 : (u : G) * x2 * (u : G)⁻¹ ∈ ruS M.L :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 M.L u.2) x2).mp x2.2
  have hmem := hC _ hutX hutV _ hux2 (by
    calc (u : G) * x2 * (u : G)⁻¹ * ((u : G) * t * (u : G)⁻¹) =
        (u : G) * (x2 * t) * (u : G)⁻¹ := by group
      _ = (u : G) * (t * x2) * (u : G)⁻¹ := by rw [hc]
      _ = (u : G) * t * (u : G)⁻¹ * ((u : G) * x2 * (u : G)⁻¹) := by group)
  obtain ⟨hux2', F, hF, Y, hY, hFY⟩ := hmem
  rw [M.χ_conj u x2, hu, hx2, toAdd_ofAdd] at hFY
  exact SL3.g1_B2 F hF Y hY hFY

theorem sq_ne_one_of_S1 {y : G} (hy : y ∈ M.S1) (hyV : y ∉ ruV M.L) : y ^ 2 ≠ 1 := by
  intro hy2
  apply M.S1_not_comm
  have hall : ∀ y' ∈ M.S1, y' ^ 2 = 1 := by
    intro y' hy'
    by_cases hy'V : y' ∈ ruV M.L
    · exact M.sq_eq_one_of_V hy'V
    obtain ⟨hyS, hyY⟩ := hy
    obtain ⟨hy'S, hy'Y⟩ := hy'
    have hne : ∀ (x : G) (hx : x ∈ ruS M.L), x ∉ ruV M.L →
        Multiplicative.toAdd (M.χ ⟨x, hx⟩) ≠ 0 := by
      intro x hx hxV h0
      apply hxV
      have hk : (⟨x, hx⟩ : ruS M.L) ∈ M.χ.ker := by
        rw [MonoidHom.mem_ker]
        exact Multiplicative.toAdd.injective (by rw [h0, toAdd_one])
      rw [M.χ_ker, Subgroup.mem_subgroupOf] at hk
      exact hk
    obtain ⟨k, hk⟩ := SL3.c0_trans_st1 _ hyY _ hy'Y ⟨hne y hyS hyV, hne y' hy'S hy'V⟩
    have hcy : (M.cel : G) ^ k.val * y * ((M.cel : G) ^ k.val)⁻¹ ∈ ruS M.L :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 M.L (M.cel ^ k.val).2) y).mp hyS
    have hχ : Multiplicative.toAdd (M.χ ⟨_, hcy⟩) =
        Multiplicative.toAdd (M.χ ⟨y', hy'S⟩) := by
      have e := M.χ_conj (M.cel ^ k.val) ⟨y, hyS⟩
      rw [map_pow, M.θ_cel, SL3.stAct_pow] at e
      rw [show (⟨(M.cel : G) ^ k.val * y * ((M.cel : G) ^ k.val)⁻¹, hcy⟩ : ruS M.L) =
        ⟨((M.cel ^ k.val : M.L) : G) * y * ((M.cel ^ k.val : M.L) : G)⁻¹, by
          rw [Subgroup.coe_pow]; exact hcy⟩ by simp only [Subgroup.coe_pow], e, hk]
    have hv : (⟨_, hcy⟩ : ruS M.L)⁻¹ * ⟨y', hy'S⟩ ∈ M.χ.ker := by
      rw [MonoidHom.mem_ker]
      apply Multiplicative.toAdd.injective
      rw [M.toAdd_χ_mul, M.toAdd_χ_inv, hχ, toAdd_one]
      ext i j
      have h : ∀ a : ZMod 2, a + a = 0 := by decide
      exact h _
    rw [M.χ_ker, Subgroup.mem_subgroupOf] at hv
    set v : G := ((M.cel : G) ^ k.val * y * ((M.cel : G) ^ k.val)⁻¹)⁻¹ * y'
    have hy'e : y' = (M.cel : G) ^ k.val * y * ((M.cel : G) ^ k.val)⁻¹ * v := by
      simp only [v]
      group
    have hvc : (M.cel : G) ^ k.val * y * ((M.cel : G) ^ k.val)⁻¹ * v =
        v * ((M.cel : G) ^ k.val * y * ((M.cel : G) ^ k.val)⁻¹) := M.V_comm_S hv hcy
    have hv2 : v * v = 1 := by rw [← pow_two]; exact M.sq_eq_one_of_V hv
    have hw2 : ((M.cel : G) ^ k.val * y * ((M.cel : G) ^ k.val)⁻¹) *
        ((M.cel : G) ^ k.val * y * ((M.cel : G) ^ k.val)⁻¹) = 1 := by
      calc ((M.cel : G) ^ k.val * y * ((M.cel : G) ^ k.val)⁻¹) *
          ((M.cel : G) ^ k.val * y * ((M.cel : G) ^ k.val)⁻¹) =
          (M.cel : G) ^ k.val * (y * y) * ((M.cel : G) ^ k.val)⁻¹ := by group
        _ = 1 := by rw [← pow_two, hy2]; group
    rw [hy'e, pow_two]
    set w := (M.cel : G) ^ k.val * y * ((M.cel : G) ^ k.val)⁻¹ with hw
    calc w * v * (w * v) = w * (v * w) * v := by group
      _ = w * (w * v) * v := by rw [← hvc]
      _ = (w * w) * (v * v) := by group
      _ = 1 := by rw [hw2, hv2, one_mul]
  intro a ha b hb
  have hab := hall _ (mul_mem ha hb)
  have ha2 := hall a ha
  have hb2 := hall b hb
  rw [pow_two] at hab ha2 hb2
  calc a * b = a * (a * b * (a * b)) * b := by rw [hab]; group
    _ = (a * a) * (b * a) * (b * b) := by group
    _ = b * a := by rw [ha2, hb2]; group

theorem mem_V_of_S1_sq {y : G} (hy : y ∈ M.S1) (hy2 : y ^ 2 = 1) : y ∈ ruV M.L := by
  by_contra hyV
  exact M.sq_ne_one_of_S1 hy hyV hy2

@[expose] noncomputable def conjS1 : MulAut M.S1 :=
  MulEquiv.ofBijective
    ({ toFun := fun y => ⟨(M.cel : G) * y * (M.cel : G)⁻¹, M.cel_conj_S1 y.2⟩
       map_one' := Subtype.ext (by simp)
       map_mul' := fun y y' => Subtype.ext (by simp only [Subgroup.coe_mul]; group) } :
      M.S1 →* M.S1)
    (by
      refine Function.Injective.bijective_of_finite fun y y' h => Subtype.ext ?_
      have h' : (M.cel : G) * y * (M.cel : G)⁻¹ = (M.cel : G) * y' * (M.cel : G)⁻¹ :=
        congrArg Subtype.val h
      simpa using h')

theorem conjS1_pow_apply (n : ℕ) (y : M.S1) :
    (((M.conjS1 ^ n) y : M.S1) : G) = (M.cel : G) ^ n * y * ((M.cel : G) ^ n)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', MulAut.mul_apply]
    show (M.cel : G) * (((M.conjS1 ^ n) y : M.S1) : G) * (M.cel : G)⁻¹ = _
    rw [ih]
    group

theorem ψV_conj_cel_pow (n : ℕ) (v : ruV M.L) (hw : (M.cel : G) ^ n * v * ((M.cel : G) ^ n)⁻¹ ∈
    ruV M.L) :
    Multiplicative.toAdd (M.ψV ⟨_, hw⟩) = (natAct3 SL3.c0)^[n] (Multiplicative.toAdd (M.ψV v)) := by
  have e := M.ψV_equiv (M.cel ^ n) v ⟨_, hw⟩ (by simp only [Subgroup.coe_pow])
  rw [map_pow, M.θ_cel, SL3.natAct3_pow] at e
  rw [e, toAdd_ofAdd]

theorem S1_suzuki : CFSG.GroupTheory.IsSuzukiTwoGroup M.S1 := by
  have hz1 : M.z ≠ 1 := M.z_ne_one
  have hzS1 : M.z ∈ M.S1 := M.V_le_S1 M.z_mem_V
  have hcz : (M.cel : G) * M.z * (M.cel : G)⁻¹ ∈ ruV M.L :=
    M.toRuData.conj_mem_V M.cel.2 M.z_mem_V
  have hord : ∀ v : M.S1, (v : G) ∈ ruV M.L → (v : G) ≠ 1 → orderOf v = 2 := by
    intro v hv hv1
    rw [← Subgroup.orderOf_coe]
    exact orderOf_eq_prime (M.sq_eq_one_of_V hv) hv1
  refine ⟨inferInstance, IsPGroup.of_card M.card_S1, ?_, ?_, ?_⟩
  · rintro ⟨h⟩
    apply M.S1_not_comm
    intro y hy y' hy'
    exact congrArg Subtype.val (h.comm ⟨y, hy⟩ ⟨y', hy'⟩)
  · refine ⟨⟨M.z, hzS1⟩, ⟨_, M.V_le_S1 hcz⟩, hord _ M.z_mem_V hz1, hord _ hcz ?_, ?_⟩
    · intro h1
      apply hz1
      have := congrArg (fun x => (M.cel : G)⁻¹ * x * M.cel) h1
      simpa [mul_assoc] using this
    · intro h
      have h' : (M.cel : G) * (⟨M.z, M.z_mem_V⟩ : ruV M.L) * (M.cel : G)⁻¹ =
          (⟨M.z, M.z_mem_V⟩ : ruV M.L) := (congrArg Subtype.val h).symm
      have h0 := SL3.c0_fix_vec _ ((M.conj_cel_V ⟨M.z, M.z_mem_V⟩).mp h')
      rw [show (⟨M.z, M.z_mem_V⟩ : ruV M.L) = M.zV from rfl, M.ψV_zV] at h0
      exact absurd h0 (by decide)
  · refine ⟨Subgroup.zpowers M.conjS1, inferInstance, fun x y hx hy => ?_⟩
    have hx2 : (x : G) ^ 2 = 1 := by
      rw [← Subgroup.orderOf_coe] at hx
      rw [← hx]
      exact pow_orderOf_eq_one _
    have hy2 : (y : G) ^ 2 = 1 := by
      rw [← Subgroup.orderOf_coe] at hy
      rw [← hy]
      exact pow_orderOf_eq_one _
    have hxV := M.mem_V_of_S1_sq x.2 hx2
    have hyV := M.mem_V_of_S1_sq y.2 hy2
    have hne : ∀ (v : G) (hv : v ∈ ruV M.L), orderOf v = 2 →
        Multiplicative.toAdd (M.ψV ⟨v, hv⟩) ≠ 0 := by
      intro v hv hv2 h0
      have : M.ψV ⟨v, hv⟩ = 1 := Multiplicative.toAdd.injective h0
      have h1 := congrArg Subtype.val (M.ψV.injective (this.trans (map_one M.ψV).symm))
      have : orderOf v = 1 := by rw [show v = 1 from h1, orderOf_one]
      omega
    obtain ⟨k, hk⟩ := SL3.c0_trans_vec _ _
      ⟨hne _ hxV (by rw [Subgroup.orderOf_coe]; exact hx),
        hne _ hyV (by rw [Subgroup.orderOf_coe]; exact hy)⟩
    refine ⟨M.conjS1 ^ k.val, Subgroup.npow_mem_zpowers _ _, Subtype.ext ?_⟩
    rw [M.conjS1_pow_apply]
    have hw : (M.cel : G) ^ k.val * (x : G) * ((M.cel : G) ^ k.val)⁻¹ ∈ ruV M.L :=
      M.toRuData.conj_mem_V (M.cel ^ k.val).2 hxV
    have e := M.ψV_conj_cel_pow k.val ⟨x, hxV⟩ hw
    rw [← hk] at e
    have := M.ψV.injective (Multiplicative.toAdd.injective e)
    exact congrArg Subtype.val this

theorem θ_mem_of_comm {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) {l : M.L}
    (hl : (l : G) * s = s * l) : ∃ k : Fin 7, M.θ l = SL3.c0 ^ k.val := by
  have hsS := (M.mem_S0.mp hs).1
  have hA0 : Multiplicative.toAdd (M.χ ⟨s, hsS⟩) ≠ 0 := by
    intro h0
    apply M.not_mem_V_of_S0 hs hs1
    have hk : (⟨s, hsS⟩ : ruS M.L) ∈ M.χ.ker := by
      rw [MonoidHom.mem_ker]
      exact Multiplicative.toAdd.injective (by rw [h0, toAdd_one])
    rw [M.χ_ker, Subgroup.mem_subgroupOf] at hk
    exact hk
  have e := M.χ_equiv l ⟨s, hsS⟩ ⟨s, hsS⟩ (by
    show s = (l : G) * s * (l : G)⁻¹
    rw [hl, mul_inv_cancel_right])
  have h := congrArg Multiplicative.toAdd e
  rw [toAdd_ofAdd] at h
  exact SL3.stab_fixC0 _ (M.χ_S0 hs) hA0 _ h.symm

theorem card_centralizer_L {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) :
    Nat.card ↥(M.L ⊓ Subgroup.centralizer ({s} : Set G)) = 2 ^ 8 * 7 := by
  set CL := M.L ⊓ Subgroup.centralizer ({s} : Set G)
  have hCL : CL ≤ M.L := inf_le_left
  let f : CL.subgroupOf M.L →* SL(3, ZMod 2) := M.θ.comp (CL.subgroupOf M.L).subtype
  have h := Subgroup.card_ker_mul_card_range f
  rw [card_subgroupOf_of_le hCL] at h
  have hker : Nat.card f.ker = 2 ^ 8 := by
    rw [← M.card_centralizer_S (M.mem_S0.mp hs).1 (M.not_mem_V_of_S0 hs hs1)]
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1.1.1, ?_, (Subgroup.mem_subgroupOf.mp x.1.2).2⟩
        invFun := fun y => ⟨⟨⟨y.1, M.toRuData.S_le_L (Subgroup.mem_inf.mp y.2).1⟩,
          Subgroup.mem_subgroupOf.mpr ⟨M.toRuData.S_le_L (Subgroup.mem_inf.mp y.2).1,
            (Subgroup.mem_inf.mp y.2).2⟩⟩, ?_⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
    · have hx := x.2
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hx
      have : x.1.1 ∈ M.θ.ker := hx
      rw [M.θ_ker, Subgroup.mem_subgroupOf] at this
      exact this
    · show M.θ ⟨y.1, _⟩ = 1
      have : (⟨y.1, M.toRuData.S_le_L (Subgroup.mem_inf.mp y.2).1⟩ : M.L) ∈ M.θ.ker := by
        rw [M.θ_ker, Subgroup.mem_subgroupOf]
        exact (Subgroup.mem_inf.mp y.2).1
      exact this
  have hrange : f.range = Subgroup.zpowers SL3.c0 := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨x, rfl⟩
      obtain ⟨k, hk⟩ := M.θ_mem_of_comm hs hs1 (l := x.1)
        (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_subgroupOf.mp x.2).2)
      show M.θ x.1 ∈ _
      rw [hk]
      exact Subgroup.npow_mem_zpowers _ _
    · rw [Subgroup.zpowers_le]
      have hc : (M.cel : G) ∈ CL := ⟨M.cel.2, Subgroup.mem_centralizer_singleton_iff.mpr
        (M.mem_S0.mp hs).2⟩
      exact ⟨⟨M.cel, Subgroup.mem_subgroupOf.mpr hc⟩, M.θ_cel⟩
  rw [hker, hrange, Nat.card_zpowers] at h
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  rw [orderOf_eq_prime SL3.c0_pow_seven SL3.c0_ne_one] at h
  exact h.symm

theorem centralizer_L_eq {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) :
    M.L ⊓ Subgroup.centralizer ({s} : Set G) =
      (ruS M.L ⊓ Subgroup.centralizer ({s} : Set G)) ⊔ M.B7 := by
  set CS := ruS M.L ⊓ Subgroup.centralizer ({s} : Set G)
  have hle : CS ⊔ M.B7 ≤ M.L ⊓ Subgroup.centralizer ({s} : Set G) := by
    refine sup_le (inf_le_inf_right _ M.toRuData.S_le_L) ?_
    rw [Subgroup.zpowers_le]
    exact ⟨M.cel.2, Subgroup.mem_centralizer_singleton_iff.mpr (M.mem_S0.mp hs).2⟩
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [M.card_centralizer_L hs hs1]
  have h1 : 2 ^ 8 ∣ Nat.card ↥(CS ⊔ M.B7) := by
    rw [← M.card_centralizer_S (M.mem_S0.mp hs).1 (M.not_mem_V_of_S0 hs hs1)]
    exact Subgroup.card_dvd_of_le le_sup_left
  have h2 : 7 ∣ Nat.card ↥(CS ⊔ M.B7) := by
    rw [← M.card_B7]
    exact Subgroup.card_dvd_of_le le_sup_right
  have h3 : 2 ^ 8 * 7 ∣ Nat.card ↥(CS ⊔ M.B7) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h1 h2
  exact Nat.le_of_dvd Nat.card_pos h3

theorem exponent_centralizer {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) :
    Monoid.exponent ↥(ruS M.L ⊓ Subgroup.centralizer ({s} : Set G)) = 4 := by
  have hdvd : Monoid.exponent ↥(ruS M.L ⊓ Subgroup.centralizer ({s} : Set G)) ∣ 2 ^ 2 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun g => Subtype.ext (by
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
      exact M.pow_four_S (Subgroup.mem_inf.mp g.2).1)
  obtain ⟨i, hi, hie⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hex : ∃ y ∈ M.S1, y ^ 2 ≠ 1 := by
    by_contra hno
    push Not at hno
    apply M.S1_not_comm
    intro a ha b hb
    have hab := hno _ (mul_mem ha hb)
    have ha2 := hno a ha
    have hb2 := hno b hb
    rw [pow_two] at hab ha2 hb2
    calc a * b = a * (a * b * (a * b)) * b := by rw [hab]; group
      _ = (a * a) * (b * a) * (b * b) := by group
      _ = b * a := by rw [ha2, hb2]; group
  obtain ⟨y, hy, hy2⟩ := hex
  have hyC : y ∈ ruS M.L ⊓ Subgroup.centralizer ({s} : Set G) := by
    rw [M.centralizer_eq_S3 hs hs1]
    exact M.S1_le_S3 hy
  interval_cases i
  · exfalso
    apply hy2
    have := Monoid.pow_exponent_eq_one (⟨y, hyC⟩ : ↥(ruS M.L ⊓ Subgroup.centralizer ({s} : Set G)))
    rw [hie, pow_zero, pow_one] at this
    have hy1 : y = 1 := congrArg Subtype.val this
    rw [hy1, one_pow]
  · exfalso
    apply hy2
    have := Monoid.pow_exponent_eq_one (⟨y, hyC⟩ : ↥(ruS M.L ⊓ Subgroup.centralizer ({s} : Set G)))
    rw [hie, pow_one] at this
    exact congrArg Subtype.val this
  · rw [hie]
    norm_num

theorem lemma_J23_3 {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) :
    M.L ⊓ Subgroup.centralizer ({s} : Set G) =
        M.S0 ⊔ ⁅ruS M.L ⊓ Subgroup.centralizer ({s} : Set G), M.B7⁆ ⊔ M.B7 ∧
      ruS M.L ⊓ Subgroup.centralizer ({s} : Set G) =
        M.S0 ⊔ ⁅ruS M.L ⊓ Subgroup.centralizer ({s} : Set G), M.B7⁆ ∧
      M.S0 ⊓ ⁅ruS M.L ⊓ Subgroup.centralizer ({s} : Set G), M.B7⁆ = ⊥ ∧
      (∀ x ∈ M.S0, ∀ y ∈ ⁅ruS M.L ⊓ Subgroup.centralizer ({s} : Set G), M.B7⁆,
        x * y = y * x) ∧
      (∃ P : Sylow 2 ↥(M.L ⊓ Subgroup.centralizer ({s} : Set G)),
        (P : Subgroup _) = (ruS M.L ⊓ Subgroup.centralizer ({s} : Set G)).subgroupOf
          (M.L ⊓ Subgroup.centralizer ({s} : Set G))) ∧
      Nat.card ↥(ruS M.L ⊓ Subgroup.centralizer ({s} : Set G)) = 2 ^ 8 ∧
      Monoid.exponent ↥(ruS M.L ⊓ Subgroup.centralizer ({s} : Set G)) = 4 := by
  have hCS : ruS M.L ⊓ Subgroup.centralizer ({s} : Set G) = M.S0 ⊔ M.S1 := by
    rw [M.centralizer_eq_S3 hs hs1, M.S3_eq_sup]
  have hcard := M.card_centralizer_S (M.mem_S0.mp hs).1 (M.not_mem_V_of_S0 hs hs1)
  rw [M.commutator_eq_S1 hs hs1]
  refine ⟨?_, hCS, M.S0_inf_S1, fun x hx y hy => M.comm_S0_S1 hx hy, ?_, hcard,
    M.exponent_centralizer hs hs1⟩
  · rw [M.centralizer_L_eq hs hs1, hCS]
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hle : ruS M.L ⊓ Subgroup.centralizer ({s} : Set G) ≤
        M.L ⊓ Subgroup.centralizer ({s} : Set G) := inf_le_inf_right _ M.toRuData.S_le_L
    have hc : Nat.card ↥((ruS M.L ⊓ Subgroup.centralizer ({s} : Set G)).subgroupOf
        (M.L ⊓ Subgroup.centralizer ({s} : Set G))) =
        2 ^ (Nat.card ↥(M.L ⊓ Subgroup.centralizer ({s} : Set G))).factorization 2 := by
      rw [card_subgroupOf_of_le hle, hcard, M.card_centralizer_L hs hs1,
        Nat.factorization_mul (by norm_num) (by norm_num), Nat.factorization_pow]
      simp [Nat.factorization_eq_zero_of_not_dvd (show ¬ 2 ∣ 7 by norm_num),
        Nat.Prime.factorization_self Nat.prime_two]
    exact ⟨Sylow.ofCard _ hc, rfl⟩

theorem lemma_J23_4 {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) :
    M.B ≤ Subgroup.normalizer ((ruS M.L ⊓ Subgroup.centralizer ({s} : Set G) : Subgroup G) :
        Set G) ∧
      M.B ≤ Subgroup.normalizer (M.S0 : Set G) ∧
      M.B ≤ Subgroup.normalizer
        ((⁅ruS M.L ⊓ Subgroup.centralizer ({s} : Set G), M.B7⁆ : Subgroup G) : Set G) := by
  rw [M.centralizer_eq_S3 hs hs1, ← M.centralizer_eq_S3 hs hs1, M.commutator_eq_S1 hs hs1,
    M.centralizer_eq_S3 hs hs1]
  refine ⟨?_, ?_, ?_⟩ <;> rw [Subgroup.zpowers_le] <;> refine mem_normalizer_of_conj_mem ?_
  · exact fun x hx => M.bel_conj_S3 hx
  · exact fun x hx => M.bel_conj_S0 hx
  · exact fun x hx => M.bel_conj_S1 hx

theorem lemma_J23_5 {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) :
    CFSG.GroupTheory.IsSuzukiTwoGroup ↥⁅ruS M.L ⊓ Subgroup.centralizer ({s} : Set G), M.B7⁆ := by
  rw [M.commutator_eq_S1 hs hs1]
  exact M.S1_suzuki

end RuDataM

end CFSG.Quasithin.RuType
