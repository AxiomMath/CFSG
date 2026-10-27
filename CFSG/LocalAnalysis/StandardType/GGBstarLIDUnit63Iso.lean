module

public import CFSG.LocalAnalysis.StandardType.GGLinearFusionSURepairPair
public import CFSG.LocalAnalysis.StandardType.GGBstarLIDUnit63Perp

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix SURepair
open CFSG.ClassicalGroups.UnitaryFlag (unitarySU mem_unitarySU_iff)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

namespace LID63

section Linear

variable {K : Type} [Field K] {n d : ℕ}

theorem exists_stable_isotropic_of_group (h : UnitaryFieldData 2 n K)
    {W : Subgroup (GL (Fin d) K)} (hW2 : IsPGroup 2 W) (hW1 : W ≠ ⊥)
    (hWu : ∀ w ∈ W, (((w : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ *
      ((w : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1)
    {S : Set (GL (Fin d) K)}
    (hSW : ∀ D ∈ S, ∀ w ∈ W, D * w * D⁻¹ ∈ W ∧ D⁻¹ * w * D ∈ W) :
    ∃ R : Submodule K (Fin d → K), R ≠ ⊥ ∧ (∀ u ∈ R, ∀ v ∈ R, (h.bar ∘ v) ⬝ᵥ u = 0) ∧
      ∀ D ∈ S, ∀ v ∈ R, ((D : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ v ∈ R := by
  classical
  have : Finite K := h.finite
  have : CharP K 2 := h.charP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X : Submodule K (Fin d → K) := Submodule.span K
    {v | ∃ w ∈ W, ∃ u : Fin d → K, v = ((w : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ u - u}
    with hX
  have hgen : ∀ w ∈ W, ∀ u : Fin d → K,
      ((w : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ u - u ∈ X :=
    fun w hw u => Submodule.subset_span ⟨w, hw, u, rfl⟩
  have hWX : ∀ w ∈ W, ∀ x ∈ X, ((w : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ x ∈ X := by
    intro w hw x hx
    induction hx using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨w', hw', u, rfl⟩ := hv
      have e : ((w : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ
          (((w' : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ u - u) =
          (((w * w' : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ u - u) -
            (((w : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ u - u) := by
        rw [Units.val_mul, ← mulVec_mulVec, mulVec_sub]
        abel
      rw [e]
      exact X.sub_mem (hgen _ (W.mul_mem hw hw') u) (hgen w hw u)
    | zero => rw [mulVec_zero]; exact X.zero_mem
    | add x y _ _ hx hy => rw [mulVec_add]; exact X.add_mem hx hy
    | smul c x _ hx => rw [mulVec_smul]; exact X.smul_mem c hx
  let _ : MulAction ↥W ↥X :=
    { smul := fun w x => ⟨((w : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ (x : Fin d → K),
        hWX w w.2 x x.2⟩
      one_smul := fun x => Subtype.ext (by
        change (((1 : W) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ (x : Fin d → K) = x
        rw [Subgroup.coe_one, Units.val_one, one_mulVec])
      mul_smul := fun w w' x => Subtype.ext (by
        change (((w * w' : W) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ (x : Fin d → K) =
          ((w : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ
            (((w' : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ (x : Fin d → K))
        rw [Subgroup.coe_mul, Units.val_mul, mulVec_mulVec]) }
  obtain ⟨⟨w₀, hw₀⟩, hw₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hW1
  have hw₀1' : w₀ ≠ 1 := fun h' => hw₀1 (Subtype.ext h')
  obtain ⟨u₀, hu₀⟩ : ∃ u : Fin d → K,
      ((w₀ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ u ≠ u := by
    by_contra hall
    push Not at hall
    apply hw₀1'
    apply Units.ext
    rw [Units.val_one]
    exact ext_of_mulVec_single fun i => by rw [hall, one_mulVec]
  have hx₀ : (⟨_, hgen w₀ hw₀ u₀⟩ : ↥X) ≠ 0 :=
    fun h' => hu₀ (sub_eq_zero.mp (congrArg Subtype.val h'))
  have hdvd : 2 ∣ Nat.card ↥X := by
    have h2 : (2 : ℕ) • (⟨_, hgen w₀ hw₀ u₀⟩ : ↥X) = 0 := by
      apply Subtype.ext
      funext i
      change (2 : ℕ) • ((((w₀ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ u₀ - u₀) i) = 0
      rw [two_nsmul, CharTwo.add_self_eq_zero]
    rw [← addOrderOf_eq_prime h2 hx₀]
    exact addOrderOf_dvd_natCard _
  have h0 : (0 : ↥X) ∈ MulAction.fixedPoints ↥W ↥X := fun w => Subtype.ext (by
    change ((w : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ (0 : Fin d → K) = 0
    rw [mulVec_zero])
  obtain ⟨r, hrfix, hr0⟩ := hW2.exists_fixed_point_of_prime_dvd_card_of_fixed_point ↥X hdvd h0
  let R : Submodule K (Fin d → K) :=
    { carrier := {v | v ∈ X ∧ ∀ w ∈ W,
        ((w : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ v = v}
      add_mem' := fun {a b} ha hb => ⟨X.add_mem ha.1 hb.1, fun w hw => by
        rw [mulVec_add, ha.2 w hw, hb.2 w hw]⟩
      zero_mem' := ⟨X.zero_mem, fun w _ => mulVec_zero _⟩
      smul_mem' := fun c v hv => ⟨X.smul_mem c hv.1, fun w hw => by
        rw [mulVec_smul, hv.2 w hw]⟩ }
  have hrR : (r : Fin d → K) ∈ R :=
    ⟨r.2, fun w hw => congrArg Subtype.val (hrfix ⟨w, hw⟩)⟩
  have hr0' : (r : Fin d → K) ≠ 0 := fun h' => hr0 (Subtype.ext h'.symm)
  have hDX : ∀ D ∈ S, ∀ x ∈ X, ((D : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ x ∈ X := by
    intro D hD x hx
    induction hx using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨w, hw, u, rfl⟩ := hv
      rw [mulVec_conj_sub]
      exact hgen _ (hSW D hD w hw).1 _
    | zero => rw [mulVec_zero]; exact X.zero_mem
    | add x y _ _ hx hy => rw [mulVec_add]; exact X.add_mem hx hy
    | smul c x _ hx => rw [mulVec_smul]; exact X.smul_mem c hx
  have hDR : ∀ D ∈ S, ∀ v ∈ R, ((D : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ v ∈ R := by
    intro D hD v hv
    refine ⟨hDX D hD v hv.1, fun w hw => ?_⟩
    have h1 := hv.2 _ (hSW D hD w hw).2
    rw [Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec] at h1
    calc ((w : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ
          (((D : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ v) =
        ((D * (D⁻¹ * w * D) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ v := by
          rw [show D * (D⁻¹ * w * D) = w * D by group, Units.val_mul, mulVec_mulVec]
      _ = ((D : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ v := by
          rw [Units.val_mul, ← mulVec_mulVec, Units.val_mul, Units.val_mul, ← mulVec_mulVec,
            ← mulVec_mulVec, h1]
  have hiso : ∀ v ∈ R, ∀ x ∈ X, (h.bar ∘ v) ⬝ᵥ x = 0 := by
    intro v hv x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨w, hw, u, rfl⟩ := hy
      rw [dotProduct_sub, dotProduct_mulVec,
        vecMul_bar_of_mulVec_eq h (hWu w hw) (hv.2 w hw), sub_self]
    | zero => exact dotProduct_zero _
    | add x y _ _ hx hy => rw [dotProduct_add, hx, hy, add_zero]
    | smul c x _ hx => rw [dotProduct_smul, hx, smul_zero]
  refine ⟨R, fun hbot => hr0' ?_, fun u hu v hv => hiso v hv u hu.1, hDR⟩
  have := hbot ▸ hrR
  exact (Submodule.mem_bot K).mp this

end Linear

section Lift

variable {G : Type} [Group G] {K : Type} [Field K] {n d : ℕ}

theorem exists_stable_isotropic (h : UnitaryFieldData 2 n K)
    {φ : ↥(unitarySU 2 n K d) →* G} (hker : φ.ker ≤ Subgroup.center ↥(unitarySU 2 n K d))
    {B V : Subgroup G} (hV1 : V ≠ ⊥) (hV2 : IsPGroup 2 V) (hVφ : V ≤ φ.range)
    (hBV : B ≤ Subgroup.normalizer (V : Set G)) :
    ∃ R : Submodule K (Fin d → K), R ≠ ⊥ ∧ (∀ u ∈ R, ∀ v ∈ R, (h.bar ∘ v) ⬝ᵥ u = 0) ∧
      ∀ (b : G) (D : GL (Fin d) K), b ∈ B → (b, D) ∈ SUTorus.suPairs φ →
        ∀ v ∈ R, ((D : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ v ∈ R := by
  classical
  have : Finite K := h.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Vt : Subgroup ↥(unitarySU 2 n K d) := V.comap φ with hVt
  set f' : ↥Vt →* G := φ.comp Vt.subtype with hf'
  have hfr : f'.range ≤ V := by
    rintro _ ⟨w, rfl⟩
    exact w.2
  have hker' : f'.ker ≤ Subgroup.center ↥Vt := by
    intro w hw
    have hz : (w : ↥(unitarySU 2 n K d)) ∈ Subgroup.center _ := hker hw
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro v
    exact Subtype.ext (hz v)
  have hrange2 : IsPGroup 2 f'.range := hV2.to_le hfr
  have : Finite f'.range := Finite.of_surjective _ f'.rangeRestrict_surjective
  have : Group.IsNilpotent f'.range := hrange2.isNilpotent
  have : Group.IsNilpotent ↥Vt :=
    Subgroup.isNilpotent_of_ker_le_center f'.rangeRestrict
      (by rw [MonoidHom.ker_rangeRestrict]; exact hker')
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 ↥Vt))
  have hPn : (P : Subgroup ↥Vt).Normal := inferInstance
  have := Sylow.unique_of_normal P hPn
  have hP1 : (P : Subgroup ↥Vt) ≠ ⊥ := by
    obtain ⟨⟨v, hvV⟩, hv1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hV1
    have hv1' : v ≠ 1 := fun h' => hv1 (Subtype.ext h')
    obtain ⟨u, hu⟩ := hVφ hvV
    have huV : u ∈ Vt := by
      show φ u ∈ V
      rw [hu]
      exact hvV
    obtain ⟨j, hj⟩ := IsPGroup.iff_orderOf.mp hV2 ⟨v, hvV⟩
    rw [Subgroup.orderOf_mk] at hj
    have hj0 : j ≠ 0 := by
      rintro rfl
      rw [pow_zero, orderOf_eq_one_iff] at hj
      exact hv1' hj
    have hdvd : 2 ∣ Nat.card ↥Vt := by
      have h1 : orderOf v ∣ orderOf (⟨u, huV⟩ : ↥Vt) := by
        have h2 : f' ⟨u, huV⟩ = v := hu
        rw [← h2]
        exact orderOf_map_dvd f' _
      rw [hj] at h1
      exact (dvd_pow_self 2 hj0).trans (h1.trans (orderOf_dvd_natCard _))
    exact P.ne_bot_of_dvd_card hdvd
  set W : Subgroup (GL (Fin d) K) :=
    ((P : Subgroup ↥Vt).map Vt.subtype).map (unitarySU 2 n K d).subtype with hW
  have hW2 : IsPGroup 2 W := (P.isPGroup'.map _).map _
  have hW1 : W ≠ ⊥ := by
    rw [hW, Ne, Subgroup.map_eq_bot_iff_of_injective _ (unitarySU 2 n K d).subtype_injective,
      Subgroup.map_eq_bot_iff_of_injective _ Vt.subtype_injective]
    exact hP1
  have hWu : ∀ w ∈ W, (((w : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ *
      ((w : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 := by
    rintro _ ⟨_, ⟨w, -, rfl⟩, rfl⟩
    exact ((mem_unitarySU_iff h).mp (w : ↥(unitarySU 2 n K d)).2).2
  set S : Set (GL (Fin d) K) := {D | ∃ b ∈ B, (b, D) ∈ SUTorus.suPairs φ} with hS
  have hconj : ∀ b : G, ∀ D : GL (Fin d) K, (b, D) ∈ SUTorus.suPairs φ →
      b ∈ Subgroup.normalizer (V : Set G) → ∀ w ∈ W, D * w * D⁻¹ ∈ W := by
    rintro b D hD hbV _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    obtain ⟨w', hw', he⟩ := conj_mem_sylow_of_mem_suPairs (P := P) hD hbV hw
    exact ⟨_, ⟨w', hw', rfl⟩, he⟩
  have hSW : ∀ D ∈ S, ∀ w ∈ W, D * w * D⁻¹ ∈ W ∧ D⁻¹ * w * D ∈ W := by
    rintro D ⟨b, hb, hD⟩ w hw
    refine ⟨hconj b _ hD (hBV hb) w hw, ?_⟩
    have hD' := (SUTorus.suPairs φ).inv_mem hD
    rw [Prod.inv_mk] at hD'
    have h1 := hconj b⁻¹ _ hD' (Subgroup.inv_mem _ (hBV hb)) w hw
    rwa [inv_inv] at h1
  obtain ⟨R, hR0, hRi, hRS⟩ := exists_stable_isotropic_of_group h hW2 hW1 hWu hSW
  exact ⟨R, hR0, hRi, fun b D hb hD v hv => hRS D ⟨b, hb, hD⟩ v hv⟩

end Lift

end LID63

end CFSG.StandardType

end
