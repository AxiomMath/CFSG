module

public import CFSG.Sporadic.Schreier.J1Outer
public import CFSG.Sporadic.Schreier.J1Centralizer
public import Certificates.Certificate7400
public import CFSG.Quasithin.Background.F7TwoInvSporGen

public section

namespace CFSG.Quasithin.F7Two

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native

theorem j1_seed_words_check :
    wordsTest 3080 2 3 [([3, 0, 1, 0, 3, 2, 1, 2], 19), ([3, 0, 1, 2], 19)] j1ATbl j1BTbl =
      true :=
  Certificates.certificate7400

theorem j1_commutator_orders :
    orderOf ((j1A2⁻¹ * j1A1 * j1A2⁻¹⁻¹) * j1A1 * (j1A2⁻¹ * j1A1 * j1A2⁻¹⁻¹)⁻¹ * j1A1⁻¹) = 19 ∧
      orderOf ((j1A2⁻¹ * j1A1 * j1A2⁻¹⁻¹) * j1A2 * (j1A2⁻¹ * j1A1 * j1A2⁻¹⁻¹)⁻¹ * j1A2⁻¹) =
        19 := by
  obtain ⟨ha, hb, -⟩ := at_j1_image_pair_count
  have h := (wordsTest_iff perm_faithful rep_j1ATbl rep_j1BTbl ha hb (by norm_num)
    (by norm_num) (by decide)).1 j1_seed_words_check
  have h1 := h ([3, 0, 1, 0, 3, 2, 1, 2], 19) (by simp)
  have h2 := h ([3, 0, 1, 2], 19) (by simp)
  have e1 : (j1A2⁻¹ * j1A1 * j1A2⁻¹⁻¹) * j1A1 * (j1A2⁻¹ * j1A1 * j1A2⁻¹⁻¹)⁻¹ * j1A1⁻¹ =
      evalW j1A1 j1A2 [3, 0, 1, 0, 3, 2, 1, 2] := by
    simp [evalW, letterW]
    group
  have e2 : (j1A2⁻¹ * j1A1 * j1A2⁻¹⁻¹) * j1A2 * (j1A2⁻¹ * j1A1 * j1A2⁻¹⁻¹)⁻¹ * j1A2⁻¹ =
      evalW j1A1 j1A2 [3, 0, 1, 2] := by
    simp [evalW, letterW]
    group
  exact ⟨by rw [e1]; exact h1, by rw [e2]; exact h2⟩

@[expose] noncomputable def j1Emb :
    NativeSporadic.J1 →* Equiv.Perm (Fin 3080) :=
  j1P.subtype.comp j1PermEquiv.toMonoidHom

theorem j1Emb_injective :
    Function.Injective j1Emb :=
  Subtype.val_injective.comp j1PermEquiv.injective

@[expose] noncomputable def j1s₁ :
    NativeSporadic.J1 := j1PermEquiv.symm j1a

@[expose] noncomputable def j1s₂ :
    NativeSporadic.J1 := j1PermEquiv.symm j1b

theorem j1Emb_s₁ :
    j1Emb j1s₁ = j1A1 := by
  simp only [j1Emb, j1s₁, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply, Subgroup.coe_subtype]
  rfl

theorem j1Emb_s₂ :
    j1Emb j1s₂ = j1A2 := by
  simp only [j1Emb, j1s₂, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply, Subgroup.coe_subtype]
  rfl

theorem j1_closure_seeds :
    Subgroup.closure ({j1s₁, j1s₂} : Set NativeSporadic.J1) = ⊤ := by
  have h : Subgroup.closure ({j1a, j1b} : Set j1P) = ⊤ :=
    CFSG.Sporadic.Mathieu.closure_pair_eq_top rfl j1A1_mem j1A2_mem
  have h2 := congrArg (Subgroup.map (j1PermEquiv.symm : j1P →* NativeSporadic.J1)) h
  rw [MonoidHom.map_closure, Set.image_pair, Subgroup.map_top,
    MonoidHom.range_eq_top.2 j1PermEquiv.symm.surjective] at h2
  exact h2

theorem j1_class
    (x c : NativeSporadic.J1) (h : j1Emb x = j1Emb c * j1A1 * (j1Emb c)⁻¹) :
    InvAutGen NativeSporadic.J1 (MulAut.conj x) := by
  obtain ⟨ho1, ho2⟩ := j1_commutator_orders
  have hne : ∀ y : Equiv.Perm (Fin 3080), orderOf y = 19 → y ^ 2 ^ 0 ≠ 1 := by
    intro y hy h1
    rw [pow_zero, pow_one] at h1
    rw [h1, orderOf_one] at hy
    omega
  refine invAutGen_of_hom_class j1Emb j1_closure_seeds (A := j1A1) (B := j1A2) (D := j1A2⁻¹)
    (r := j1A1) (u := j1Emb x) j1Emb_s₁ j1Emb_s₂ (d := j1s₂⁻¹) (c := c)
    (by rw [map_inv, j1Emb_s₂]) (sa := 0) (ma := 19) (sb := 0) (mb := 19) (by decide)
    (by decide) ?_ (hne _ ho1) ?_ (hne _ ho2) (fun y => by simp [MulAut.conj_apply]) h
  · rw [show 2 ^ 0 * 19 = 19 from rfl, ← ho1]
    exact pow_orderOf_eq_one _
  · rw [show 2 ^ 0 * 19 = 19 from rfl, ← ho2]
    exact pow_orderOf_eq_one _

theorem invAutGen_J1 :
    ∀ φ : MulAut NativeSporadic.J1, φ * φ = 1 → φ ≠ 1 → InvAutGen NativeSporadic.J1 φ := by
  have hnonab : ∃ x y : NativeSporadic.J1, x * y ≠ y * x := by
    refine ⟨j1s₁, j1s₂, fun h => ?_⟩
    have h1 := congrArg j1Emb h
    rw [map_mul, map_mul, j1Emb_s₁, j1Emb_s₂] at h1
    have h2 := (at_j1_image_pair_count).2.2.2.1
    rw [h1, mul_inv_cancel_right, mul_inv_cancel, orderOf_one] at h2
    omega
  have hZ := center_eq_bot_of_isSimpleGroup CFSG.Sporadic.J1.isSimpleGroup_J1 hnonab
  have hin : ∀ φ : MulAut NativeSporadic.J1, ∃ x, MulAut.conj x = φ := fun φ =>
    (at_j1_schreier.2.1 φ).imp fun g hg => hg.symm
  refine invAutGen_of_inner_conj hZ hin fun x hxx hx1 => ?_
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx2 : orderOf (j1Emb x) = 2 := orderOf_eq_prime
    (by rw [pow_two, ← map_mul, hxx, map_one])
    (fun h => hx1 (j1Emb_injective (by rw [h, map_one])))
  obtain ⟨c', hc', hcc⟩ := j1_involution_conj (j1Emb x) (j1PermEquiv x).2 hx2
  have hjc : j1Emb (j1PermEquiv.symm ⟨c', hc'⟩) = c' := by
    simp only [j1Emb, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply, Subgroup.coe_subtype]
  exact j1_class x (j1PermEquiv.symm ⟨c', hc'⟩) (by rw [hjc]; exact hcc)

theorem invAutGen_carrier_J1 :
    ∀ φ : MulAut (NativeSporadic.Carrier .J1), φ * φ = 1 → φ ≠ 1 →
      InvAutGen (NativeSporadic.Carrier .J1) φ :=
  invAutGen_J1

end CFSG.Quasithin.F7Two
