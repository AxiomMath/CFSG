module

public import CFSG.Quasithin.Background.FixVZPowersMem
public import CFSG.Quasithin.Vol2.Ch12Sec5Ir
public import CFSG.Quasithin.Vol2.Ch12Sec5Inv

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S125 S125St S125W S125Ir Matrix
open scoped IsMulCommutative

local notation "SL5" => Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)
local notation "M5" => Matrix (Fin 5) (Fin 5) (ZMod 2)
local notation "MV" => Multiplicative (Fin 10 → ZMod 2)

namespace S125L5a

theorem t1_upper : ∀ i j : Fin 5, j < i → S125Inv.t1 i j = 0 := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | rfl | exact absurd hij (by decide)

theorem t2_upper : ∀ i j : Fin 5, j < i → S125Inv.t2 i j = 0 := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | rfl | exact absurd hij (by decide)

theorem det_t1 : S125Inv.t1.det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (fun a b hab => t1_upper a b hab)]
  simp [Fin.prod_univ_five, S125Inv.t1]

theorem det_t2 : S125Inv.t2.det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (fun a b hab => t2_upper a b hab)]
  simp [Fin.prod_univ_five, S125Inv.t2]

@[expose] def T1 : SL5 := ⟨S125Inv.t1, det_t1⟩

@[expose] def T2 : SL5 := ⟨S125Inv.t2, det_t2⟩

theorem t1_sq : S125Inv.t1 * S125Inv.t1 = 1 := by decide

theorem t1_ne : S125Inv.t1 ≠ 1 := by decide

theorem orderOf_T1 : orderOf T1 = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime (Subtype.ext ?_) fun h => t1_ne (congrArg Subtype.val h)
  rw [pow_two]
  exact t1_sq

theorem wedgeMat_t1 : JonesParshall.wedgeMat S125Inv.t1 =
    1 + Matrix.single 0 6 1 + Matrix.single 1 8 1 + Matrix.single 2 9 1 := by decide

theorem fix_t1_iff (x : Fin 10 → ZMod 2) :
    JonesParshall.wedgeMat S125Inv.t1 *ᵥ x = x ↔
      ∀ k ∉ ({0, 1, 2, 3, 4, 5, 7} : Finset (Fin 10)), x k = 0 := by
  rw [wedgeMat_t1]
  constructor
  · intro h k hk
    obtain ⟨h6, h8, h9⟩ := S125ZV.fix_aux h (by decide) (by decide) (by decide)
    fin_cases k <;> simp_all
  · intro h
    have h6 := h 6 (by decide)
    have h8 := h 8 (by decide)
    have h9 := h 9 (by decide)
    simp only [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec, one_mul, h6, h8, h9]
    funext k
    simp

theorem card_fix_t2 : (Finset.univ.filter fun x : Fin 10 → ZMod 2 =>
    JonesParshall.wedgeMat S125Inv.t2 *ᵥ x = x).card = 64 := by
  decide +kernel

theorem card_fix_t1 : (Finset.univ.filter fun x : Fin 10 → ZMod 2 =>
    JonesParshall.wedgeMat S125Inv.t1 *ᵥ x = x).card = 128 := by
  decide +kernel

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

@[expose] noncomputable def j1 (F : Frame125 T L V) : ↥(autOn L V) := F.γ.symm T1

@[expose] noncomputable def j2 (F : Frame125 T L V) : ↥(autOn L V) := F.γ.symm T2

omit [Finite G] in
theorem e_j (F : Frame125 T L V) (g : SL5) (v : ↥V) :
    F.e (((F.γ.symm g : ↥(autOn L V)) : MulAut ↥V) v) =
      Multiplicative.ofAdd (JonesParshall.wedgeMat (g : M5) *ᵥ Multiplicative.toAdd (F.e v)) := by
  rw [F.wedge, MulEquiv.apply_symm_apply, S125ZV.wedgeRep_apply]

omit [Finite G] in
theorem fix_iff (F : Frame125 T L V) (g : SL5) (v : ↥V) :
    ((F.γ.symm g : ↥(autOn L V)) : MulAut ↥V) v = v ↔
      JonesParshall.wedgeMat (g : M5) *ᵥ Multiplicative.toAdd (F.e v) =
        Multiplicative.toAdd (F.e v) := by
  rw [← F.e.injective.eq_iff, e_j, ← Multiplicative.toAdd.injective.eq_iff, toAdd_ofAdd]

omit [Finite G] in
theorem mem_zpowers_of_sq {M : Type*} [Group M] {a x : M} (ha : a * a = 1)
    (hx : x ∈ Subgroup.zpowers a) : x = 1 ∨ x = a := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  have h2 : a ^ (2 : ℤ) = 1 := by
    rw [zpow_two]
    exact ha
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
  · left
    rw [_root_.zpow_mul, h2, _root_.one_zpow]
  · right
    rw [_root_.zpow_add, _root_.zpow_mul, h2, _root_.one_zpow, one_mul, zpow_one]

omit [Finite G] in
theorem mem_fixV_zpowers {M : Type*} [CommGroup M] {a : MulAut M} (ha : a * a = 1) {v : M} :
    v ∈ fixV (Subgroup.zpowers a) ↔ a v = v :=
  CFSG.Quasithin.mem_fixV_zpowers_iff_apply

omit [Finite G] in
theorem card_of_coords (F : Frame125 T L V) {P : Subgroup ↥V}
    {p : (Fin 10 → ZMod 2) → Prop} [DecidablePred p]
    (hP : ∀ v, v ∈ P ↔ p (Multiplicative.toAdd (F.e v))) :
    Nat.card ↥P = (Finset.univ.filter p).card := by
  rw [← Fintype.card_subtype]
  rw [← Nat.card_eq_fintype_card]
  refine Nat.card_congr ⟨fun v => ⟨Multiplicative.toAdd (F.e v), (hP v).1 v.2⟩,
    fun x => ⟨F.e.symm (Multiplicative.ofAdd x), (hP _).2 (by
      rw [MulEquiv.apply_symm_apply, toAdd_ofAdd]
      exact x.2)⟩, fun v => ?_, fun x => ?_⟩
  · apply Subtype.ext
    simp
  · apply Subtype.ext
    simp

omit [Finite G] in
theorem sub_mono_le (F : Frame125 T L V) {S S' : Finset (Fin 10)} (h : S ⊆ S') :
    F.sub S ≤ F.sub S' := by
  rintro _ ⟨v, hv, rfl⟩
  exact (mem_sub_iff F S' v).2 fun k hk => hv k fun hkS => hk (h hkS)

omit [Finite G] in
theorem sub_union (F : Frame125 T L V) (S S' : Finset (Fin 10)) :
    F.sub (S ∪ S') = F.sub S ⊔ F.sub S' := by
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    set x := Multiplicative.toAdd (F.e v) with hx
    let xS : Fin 10 → ZMod 2 := fun k => if k ∈ S then x k else 0
    let v₁ : ↥V := F.e.symm (Multiplicative.ofAdd xS)
    let v₂ : ↥V := F.e.symm (Multiplicative.ofAdd (x - xS))
    have hv12 : v = v₁ * v₂ := by
      apply F.e.injective
      rw [map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, ← ofAdd_add,
        add_sub_cancel, hx, ofAdd_toAdd]
    have h1 : (v₁ : G) ∈ F.sub S := (mem_sub_iff F S v₁).2 fun k hk => by
      rw [MulEquiv.apply_symm_apply, toAdd_ofAdd]
      simp [xS, hk]
    have h2 : (v₂ : G) ∈ F.sub S' := (mem_sub_iff F S' v₂).2 fun k hk => by
      rw [MulEquiv.apply_symm_apply, toAdd_ofAdd, Pi.sub_apply]
      by_cases hkS : k ∈ S
      · simp [xS, hkS]
      · have : x k = 0 := hv k (by simp [hkS, hk])
        simp [xS, hkS, this]
    rw [hv12, map_mul]
    exact Subgroup.mul_mem_sup h1 h2
  · exact sup_le (sub_mono_le F Finset.subset_union_left)
      (sub_mono_le F Finset.subset_union_right)

omit [Finite G] in
theorem orderOf_j1 (F : Frame125 T L V) : orderOf (j1 F) = 2 := by
  rw [j1, MulEquiv.orderOf_eq, orderOf_T1]

omit [Finite G] in
theorem j_sq (F : Frame125 T L V) {g : SL5} (hg : g * g = 1) :
    ((F.γ.symm g : ↥(autOn L V)) : MulAut ↥V) * ((F.γ.symm g : ↥(autOn L V)) : MulAut ↥V) = 1 := by
  rw [← Subgroup.coe_mul, ← map_mul, hg, map_one]
  rfl

omit [Finite G] in
theorem fixV_j1 (F : Frame125 T L V) [IsMulCommutative ↥V] :
    (fixV (V := ↥V) (Subgroup.zpowers ((j1 F : ↥(autOn L V)) : MulAut ↥V))).map V.subtype =
      F.V4 ⊔ F.V6 := by
  have haa : ((j1 F : ↥(autOn L V)) : MulAut ↥V) * ((j1 F : ↥(autOn L V)) : MulAut ↥V) = 1 :=
    j_sq F (Subtype.ext t1_sq : T1 * T1 = 1)
  have hS : F.V4 ⊔ F.V6 = F.sub {0, 1, 2, 3, 4, 5, 7} := by
    rw [Frame125.V4, Frame125.V6, ← sub_union]
    congr 1
    decide
  rw [hS]
  ext g
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [SetLike.mem_coe, mem_fixV_zpowers haa, j1, fix_iff] at hv
    exact (mem_sub_iff F _ v).2 ((fix_t1_iff _).1 hv)
  · intro hg
    obtain ⟨v, hv, rfl⟩ := hg
    refine ⟨v, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_fixV_zpowers haa, j1, fix_iff]
    exact (fix_t1_iff _).2 hv

omit [Finite G] in
theorem rkIdx_fixV_j1 (F : Frame125 T L V) [IsMulCommutative ↥V] (hcard : Nat.card V = 2 ^ 10) :
    rkIdx (fixV (V := ↥V) (Subgroup.zpowers ((j1 F : ↥(autOn L V)) : MulAut ↥V))) = 3 := by
  have haa : ((j1 F : ↥(autOn L V)) : MulAut ↥V) * ((j1 F : ↥(autOn L V)) : MulAut ↥V) = 1 :=
    j_sq F (Subtype.ext t1_sq : T1 * T1 = 1)
  have hfix : Nat.card ↥(fixV (V := ↥V)
      (Subgroup.zpowers ((j1 F : ↥(autOn L V)) : MulAut ↥V))) = 128 := by
    rw [card_of_coords F (p := fun x => JonesParshall.wedgeMat S125Inv.t1 *ᵥ x = x)
      fun v => ?_]
    · exact card_fix_t1
    · rw [mem_fixV_zpowers haa, j1]
      exact fix_iff F T1 v
  have h1 := Subgroup.index_mul_card (fixV (V := ↥V)
    (Subgroup.zpowers ((j1 F : ↥(autOn L V)) : MulAut ↥V)))
  rw [hfix, hcard] at h1
  have h8 : (fixV (V := ↥V) (Subgroup.zpowers ((j1 F : ↥(autOn L V)) : MulAut ↥V))).index = 8 := by
    omega
  rw [rkIdx, h8, show (8 : ℕ) = 2 ^ 3 by norm_num, padicValNat.prime_pow]

omit [Finite G] in
theorem conj_j (F : Frame125 T L V) (a : ↥(autOn L V)) (ha : orderOf a = 2) :
    (∃ b : ↥(autOn L V), b * a * b⁻¹ = j1 F) ∨ ∃ b : ↥(autOn L V), b * a * b⁻¹ = j2 F := by
  have h2 : a ^ 2 = 1 := ha ▸ pow_orderOf_eq_one a
  have hsq : F.γ a * F.γ a = 1 := by
    rw [← map_mul, ← pow_two, h2, map_one]
  have hne : F.γ a ≠ 1 := by
    intro h
    have : a = 1 := F.γ.injective (h.trans (map_one F.γ).symm)
    rw [this, orderOf_one] at ha
    exact absurd ha (by norm_num)
  obtain ⟨b, hb | hb⟩ := S125Inv.invol_class (F.γ a) hsq hne
  · left
    refine ⟨F.γ.symm b, ?_⟩
    have : b * F.γ a * b⁻¹ = T1 := Subtype.ext hb
    rw [j1, ← this, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
  · right
    refine ⟨F.γ.symm b, ?_⟩
    have : b * F.γ a * b⁻¹ = T2 := Subtype.ext hb
    rw [j2, ← this, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]

end S125L5a

end CFSG.Quasithin.H13
