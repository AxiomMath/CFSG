module

public import CFSG.Quasithin.H13.GoldschmidtCTKFamL5Fix
public import Mathlib.Algebra.NoZeroSMulDivisors.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

public section

namespace CFSG.Quasithin.H13.CTK.L5

variable {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W]
variable {Γ : Type} [Group Γ] (act : Γ →* (W ≃ₗ[K] W))

theorem exists_fixed_quotient [Finite W] (hK : Nat.card K = 2) (H : Subgroup Γ)
    (hH : IsPGroup 2 H) (F : Submodule K W) (hF : ∀ h ∈ H, ∀ f ∈ F, act h f ∈ F)
    (hne : F ≠ ⊤) : ∃ w, w ∉ F ∧ ∀ h ∈ H, act h w - w ∈ F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFle : ∀ h : H, F ≤ F.comap (act (h : Γ)).toLinearMap := fun h f hf => hF h h.2 f hf
  let φ : H →* Function.End (W ⧸ F) :=
    { toFun := fun h => (F.mapQ F (act (h : Γ)).toLinearMap (hFle h) : (W ⧸ F) → (W ⧸ F))
      map_one' := by
        funext q
        induction q using Submodule.Quotient.induction_on with
        | _ w =>
          show F.mapQ F (act ((1 : H) : Γ)).toLinearMap (hFle 1) (Submodule.Quotient.mk w) =
            Submodule.Quotient.mk w
          simp
      map_mul' := by
        intro a b
        funext q
        induction q using Submodule.Quotient.induction_on with
        | _ w =>
          show F.mapQ F (act ((a * b : H) : Γ)).toLinearMap (hFle (a * b))
              (Submodule.Quotient.mk w) =
            F.mapQ F (act (a : Γ)).toLinearMap (hFle a)
              (F.mapQ F (act (b : Γ)).toLinearMap (hFle b) (Submodule.Quotient.mk w))
          simp [Submodule.mapQ_apply] }
  let _ : MulAction H (W ⧸ F) := MulAction.compHom (W ⧸ F) φ
  have hsmul : ∀ (h : H) (w : W), h • (Submodule.Quotient.mk w : W ⧸ F) =
      Submodule.Quotient.mk (act (h : Γ) w) := fun h w => rfl
  have : Finite (W ⧸ F) :=
    Finite.of_surjective (Submodule.Quotient.mk (p := F)) (Submodule.Quotient.mk_surjective F)
  have h1 := hH.card_modEq_card_fixedPoints (W ⧸ F)
  have hq : Nat.card (W ⧸ F) = 2 ^ Module.finrank K (W ⧸ F) := by
    have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
    have : Fintype K := Fintype.ofFinite K
    have : Fintype (W ⧸ F) := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := K) (V := W ⧸ F),
      ← Nat.card_eq_fintype_card, hK]
  have hd : Module.finrank K (W ⧸ F) ≠ 0 := by
    intro h0
    have hsub : Subsingleton (W ⧸ F) := Module.finrank_zero_iff.1 h0
    exact hne (Submodule.Quotient.subsingleton_iff.1 hsub)
  have heven : 2 ∣ Nat.card (W ⧸ F) := by
    rw [hq]
    exact dvd_pow_self 2 hd
  by_contra hcon
  push Not at hcon
  have hfix : MulAction.fixedPoints H (W ⧸ F) = {0} := by
    ext q
    constructor
    · intro hq0
      induction q using Submodule.Quotient.induction_on with
      | _ w =>
        by_contra hw
        have hw' : w ∉ F := fun hwF => hw (by
          rw [Set.mem_singleton_iff]
          exact (Submodule.Quotient.mk_eq_zero F).2 hwF)
        obtain ⟨h, hh, hnot⟩ := hcon w hw'
        have := hq0 ⟨h, hh⟩
        rw [hsmul] at this
        exact hnot ((Submodule.Quotient.eq F).1 this)
    · intro hq0
      rw [Set.mem_singleton_iff] at hq0
      subst hq0
      intro h
      rw [← Submodule.Quotient.mk_zero F, hsmul]
      simp
  rw [hfix] at h1
  have h2 : Nat.card (({0} : Set (W ⧸ F)) : Set (W ⧸ F)) = 1 := by simp
  rw [h2] at h1
  unfold Nat.ModEq at h1
  omega

theorem ncard_coe_submodule [Finite W] (U : Submodule K W) : (U : Set W).ncard = Nat.card U :=
  (Nat.card_coe_set_eq _).symm

@[expose] def fixV (V : Subgroup Γ) : Submodule K W where
  carrier := {w | ∀ v ∈ V, act v w = w}
  add_mem' := fun {a b} (ha : ∀ v ∈ V, act v a = a) (hb : ∀ v ∈ V, act v b = b) => by
    show ∀ v ∈ V, act v (a + b) = a + b
    intro v hv
    rw [map_add, ha v hv, hb v hv]
  zero_mem' := by
    show ∀ v ∈ V, act v 0 = 0
    intro v _
    simp
  smul_mem' := fun c w (hw : ∀ v ∈ V, act v w = w) => by
    show ∀ v ∈ V, act v (c • w) = c • w
    intro v hv
    rw [map_smul, hw v hv]

theorem mem_fixV {V : Subgroup Γ} {w : W} : w ∈ fixV act V ↔ ∀ v ∈ V, act v w = w := Iff.rfl

@[expose] def fix2 (V : Subgroup Γ) (F : Submodule K W) : Submodule K W where
  carrier := {w | ∀ v ∈ V, act v w - w ∈ F}
  add_mem' := fun {a b} (ha : ∀ v ∈ V, act v a - a ∈ F) (hb : ∀ v ∈ V, act v b - b ∈ F) => by
    show ∀ v ∈ V, act v (a + b) - (a + b) ∈ F
    intro v hv
    have : act v (a + b) - (a + b) = (act v a - a) + (act v b - b) := by
      rw [map_add]; abel
    rw [this]
    exact F.add_mem (ha v hv) (hb v hv)
  zero_mem' := by
    show ∀ v ∈ V, act v 0 - 0 ∈ F
    intro v _
    simp
  smul_mem' := fun c w (hw : ∀ v ∈ V, act v w - w ∈ F) => by
    show ∀ v ∈ V, act v (c • w) - c • w ∈ F
    intro v hv
    have : act v (c • w) - c • w = c • (act v w - w) := by
      rw [map_smul, smul_sub]
    rw [this]
    exact F.smul_mem c (hw v hv)

theorem ncard_eq_univ_of_card_eq [Finite W] (hW : Nat.card W = 32) (U : Submodule K W)
    (hU : Nat.card U = 32) (w : W) : w ∈ U := by
  have : (U : Set W) = Set.univ :=
    Set.eq_of_subset_of_ncard_le (Set.subset_univ _)
      (by rw [ncard_coe_submodule, hU, Set.ncard_univ, hW]) (Set.toFinite _)
  have hw : w ∈ (U : Set W) := by
    rw [this]
    exact Set.mem_univ w
  exact hw

theorem step_CD [Finite W] (hK : Nat.card K = 2) (hW : Nat.card W = 32)
    (hact : Function.Injective act) {V : Subgroup Γ} (hV : Nat.card V = 16) {x : Γ}
    (hx : orderOf x = 5) (hx2 : ∀ v ∈ V, x⁻¹ * v * x ∈ V) :
    (Nat.card (fixV act V) = 2 ∨ Nat.card (fixV act V) = 16) ∧
      ∀ w, ∀ v ∈ V, act v w - w ∈ fixV act V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV2 : IsPGroup 2 V := IsPGroup.of_card (n := 4) (by rw [hV]; norm_num)
  have hne : ∃ w, act x w ≠ w := by
    by_contra h
    push Not at h
    have h1 : act x = act 1 := by
      ext w
      simp [h w]
    have := hact h1
    rw [this, orderOf_one] at hx
    omega
  set F := fixV act V with hF
  have hFx : ∀ w ∈ F, act x w ∈ F := by
    intro w hw v hv
    have h1 : v * x = x * (x⁻¹ * v * x) := by group
    have h2 : act v (act x w) = act (v * x) w := by rw [map_mul, LinearEquiv.mul_apply]
    rw [h2, h1, map_mul, LinearEquiv.mul_apply, hw _ (hx2 v hv)]
  have hpar := card_modEq_fix act V hV2 Set.univ (fun _ _ _ _ => Set.mem_univ _)
  have e : {w | w ∈ (Set.univ : Set W) ∧ ∀ h ∈ V, act h w = w} = (F : Set W) := by
    ext w
    simp [hF, mem_fixV]
  rw [e, Set.ncard_univ, hW, ncard_coe_submodule] at hpar
  have hFeven : 2 ∣ Nat.card F := by
    have h := hpar.symm
    unfold Nat.ModEq at h
    omega
  have hFpos : 1 ≤ Nat.card F := Nat.card_pos
  have hFtop : ¬ (∀ w, w ∈ F) := by
    intro hall
    have hV1 : Nat.card V = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      refine ⟨⟨fun a b => ?_⟩, ⟨1⟩⟩
      have key : ∀ v : V, v = 1 := by
        intro v
        apply Subtype.ext
        apply hact
        ext w
        simpa using hall w v v.2
      rw [key a, key b]
    omega
  have hcl := classify act hK hW hx hne F hFx
  have hFne1 : Nat.card F ≠ 1 := by
    intro h1
    rw [h1] at hFeven
    omega
  have hFne32 : Nat.card F ≠ 32 := fun h32 => hFtop (ncard_eq_univ_of_card_eq hW F h32)
  have hF2x : ∀ w ∈ fix2 act V F, act x w ∈ fix2 act V F := by
    intro w hw v hv
    have h1 : act v (act x w) - act x w = act x (act (x⁻¹ * v * x) w - w) := by
      have : v * x = x * (x⁻¹ * v * x) := by group
      rw [map_sub, ← LinearEquiv.mul_apply, ← map_mul, this, map_mul, LinearEquiv.mul_apply]
    rw [h1]
    exact hFx _ (hw _ (hx2 v hv))
  have hFsub : (F : Set W) ⊂ (fix2 act V F : Set W) := by
    refine ⟨fun w hw v hv => ?_, fun hsub => ?_⟩
    · rw [hw v hv, sub_self]
      exact F.zero_mem
    · obtain ⟨w, hwF, hw⟩ := exists_fixed_quotient act hK V hV2 F
        (fun v hv f hf => by rw [hf v hv]; exact hf)
        (fun htop => hFtop (fun w => htop ▸ Submodule.mem_top))
      exact hwF (hsub (fun v hv => hw v hv))
  have hlt : Nat.card F < Nat.card (fix2 act V F) := by
    rw [← ncard_coe_submodule, ← ncard_coe_submodule]
    exact Set.ncard_lt_ncard hFsub (Set.toFinite _)
  have hcl2 := classify act hK hW hx hne (fix2 act V F) hF2x
  have hF2top : ∀ w, w ∈ fix2 act V F := by
    rcases hcl2 with h | ⟨h2, -⟩ | ⟨h16, hfree⟩ | h32
    · omega
    · omega
    · exfalso
      rcases hcl with h | ⟨h2, hC⟩ | ⟨h16', -⟩ | h32
      · exact hFne1 h
      ·
        have hCcard := ncard_fix_x act hK hW hx hne
        have hFeqC : ((fixSub act x : Submodule K W) : Set W) = (F : Set W) :=
          Set.eq_of_subset_of_ncard_le (fun w hw => hC w hw)
            (by rw [hCcard, ncard_coe_submodule, h2]) (Set.toFinite _)
        obtain ⟨w₁, hw₁F, hw₁0⟩ : ∃ w ∈ F, w ≠ 0 := by
          by_contra hcon
          push Not at hcon
          have hsub : (F : Set W) ⊆ {0} := fun w hw => hcon w hw
          have := Set.ncard_le_ncard hsub (Set.toFinite _)
          rw [ncard_coe_submodule, h2, Set.ncard_singleton] at this
          omega
        have hw₁x : act x w₁ = w₁ := by
          have : w₁ ∈ ((fixSub act x : Submodule K W) : Set W) := by rw [hFeqC]; exact hw₁F
          exact this
        exact hw₁0 (hfree w₁ (hFsub.1 hw₁F) hw₁x)
      · omega
      · exact hFne32 h32
    · exact ncard_eq_univ_of_card_eq hW _ h32
  refine ⟨?_, fun w v hv => hF2top w v hv⟩
  rcases hcl with h | h | h | h
  · exact absurd h hFne1
  · exact Or.inl h.1
  · exact Or.inr h.1
  · exact absurd h hFne32

end CFSG.Quasithin.H13.CTK.L5
