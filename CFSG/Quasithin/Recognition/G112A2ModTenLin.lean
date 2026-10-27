module

public import CFSG.Milestones.ASVolI.G11

public section

namespace CFSG.Quasithin.G112A2

open CFSG.Quasithin CFSG.ASVolI.ChG
open scoped TensorProduct

@[expose] noncomputable def tenMulF4 (c : GaloisField 2 2) :
    (↥(permCore 6) ⊗[ZMod 2] GaloisField 2 2) →ₗ[ZMod 2] (↥(permCore 6) ⊗[ZMod 2] GaloisField 2 2) :=
  LinearMap.lTensor (↥(permCore 6)) (LinearMap.mulLeft (ZMod 2) c)

theorem tenMulF4_tmul (c : GaloisField 2 2) (a : ↥(permCore 6)) (b : GaloisField 2 2) :
    tenMulF4 c (a ⊗ₜ b) = a ⊗ₜ (c * b) := by
  simp [tenMulF4]

theorem ten_add_self {V : Type} [AddCommGroup V] [Module (ZMod 2) V] (x : V) : x + x = 0 := by
  rw [← two_smul (ZMod 2) x, show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem ten_fixed_free {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (β : (↥(permCore 6) ⊗[ZMod 2] GaloisField 2 2) →ₗ[ZMod 2] V)
    (hsurj : Function.Surjective β)
    (hker : ∀ t, β t = 0 ↔ ∃ b : GaloisField 2 2, t = CFSG.ASVolI.ChG.onesCore6 ⊗ₜ b)
    (p : V ≃ₗ[ZMod 2] V) {ω : GaloisField 2 2} (hω : ω ≠ 1)
    (hmul : ∀ (a : ↥(permCore 6)) (b : GaloisField 2 2), β (a ⊗ₜ (ω * b)) = p (β (a ⊗ₜ b)))
    (v : V) (hv : p v = v) : v = 0 := by
  have h2 : (2 : GaloisField 2 2) = 0 := CharTwo.two_eq_zero
  have hc0 : ω + 1 ≠ 0 := by
    intro h
    apply hω
    linear_combination h - h2
  have hM : ∀ w, β (tenMulF4 (ω + 1) w) = p (β w) + β w := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      rw [tenMulF4_tmul, add_mul, one_mul, TensorProduct.tmul_add, map_add, hmul]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]; abel
  obtain ⟨w, rfl⟩ := hsurj v
  have h0 : β (tenMulF4 (ω + 1) w) = 0 := by rw [hM, hv, ten_add_self]
  obtain ⟨b, hb⟩ := (hker _).1 h0
  have hN : ∀ w' : ↥(permCore 6) ⊗[ZMod 2] GaloisField 2 2,
      tenMulF4 (ω + 1)⁻¹ (tenMulF4 (ω + 1) w') = w' := by
    intro w'
    induction w' using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      rw [tenMulF4_tmul, tenMulF4_tmul, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hw : w = CFSG.ASVolI.ChG.onesCore6 ⊗ₜ ((ω + 1)⁻¹ * b) := by
    rw [← hN w, hb, tenMulF4_tmul]
  rw [hw]
  exact (hker _).2 ⟨_, rfl⟩

theorem ten_finrank_range_ge_four {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (hV : Module.finrank (ZMod 2) V = 8) (t p : V ≃ₗ[ZMod 2] V) (hp3 : p ^ 3 = 1)
    (hinv : t * p = p⁻¹ * t) (hfix : ∀ v, p v = v → v = 0) :
    4 ≤ Module.finrank (ZMod 2) (LinearMap.range (t.toLinearMap - LinearMap.id)) := by
  have hpinv : p⁻¹ = p ^ 2 := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ']
    exact hp3
  have hinv' : t * p = p ^ 2 * t := hpinv ▸ hinv
  have P3 : ∀ u, p (p (p u)) = u := fun u => by
    have h := congrArg (fun g : V ≃ₗ[ZMod 2] V => g u) hp3
    simpa [pow_three, mul_assoc] using h
  have htp : ∀ v, t (p v) = p (p (t v)) := fun v => by
    have h := congrArg (fun g : V ≃ₗ[ZMod 2] V => g v) hinv'
    simpa [pow_two] using h
  set C := LinearMap.ker (t.toLinearMap - LinearMap.id) with hC
  set pC : Submodule (ZMod 2) V := C.map (p : V →ₗ[ZMod 2] V) with hpC
  have hdisj : C ⊓ pC = ⊥ := by
    rw [eq_bot_iff]
    rintro w ⟨hwC, hwp⟩
    obtain ⟨v, hvC, rfl⟩ := Submodule.mem_map.1 hwp
    have hv : t v = v := by
      have := LinearMap.mem_ker.1 hvC
      simpa [sub_eq_zero] using this
    have hw : t (p v) = p v := by
      have := LinearMap.mem_ker.1 hwC
      simpa [sub_eq_zero] using this
    have E : p v = p (p v) := by
      calc p v = t (p v) := hw.symm
        _ = p (p (t v)) := htp v
        _ = p (p v) := by rw [hv]
    have h5 : p (p v) = v := by
      have := congrArg p E
      rw [P3] at this
      exact this
    have hpv : p v = v := E.trans h5
    have hv0 : v = 0 := hfix v hpv
    rw [Submodule.mem_bot, hv0, map_zero]
  have hpCc : Module.finrank (ZMod 2) pC = Module.finrank (ZMod 2) C :=
    LinearEquiv.finrank_map_eq p C
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq C pC
  rw [hdisj, finrank_bot, hpCc] at hsum
  have hle : Module.finrank (ZMod 2) ↥(C ⊔ pC) ≤ 8 := by
    rw [← hV]
    exact Submodule.finrank_le _
  have hrn : Module.finrank (ZMod 2) (LinearMap.range (t.toLinearMap - LinearMap.id)) +
      Module.finrank (ZMod 2) C = 8 := by
    rw [← hV]
    exact LinearMap.finrank_range_add_finrank_ker _
  omega

noncomputable def tenBasisF4 {ω : GaloisField 2 2} (h0 : ω ≠ 0) (h1 : ω ≠ 1) :
    Module.Basis (Fin 2) (ZMod 2) (GaloisField 2 2) := by
  classical
  refine basisOfLinearIndependentOfCardEqFinrank (b := ![1, ω]) ?_ ?_
  · rw [LinearIndependent.pair_iff]
    intro s t hst
    have h2 : (2 : GaloisField 2 2) = 0 := CharTwo.two_eq_zero
    rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 by decide) s with rfl | rfl <;>
      rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 by decide) t with rfl | rfl
    · exact ⟨rfl, rfl⟩
    · simp at hst
      exact absurd hst h0
    · simp at hst
    · have : ω = 1 := by
        simp at hst
        linear_combination hst - h2
      exact absurd this h1
  · rw [GaloisField.finrank 2 (by norm_num)]
    simp

theorem tenBasisF4_zero {ω : GaloisField 2 2} (h0 : ω ≠ 0) (h1 : ω ≠ 1) :
    tenBasisF4 h0 h1 0 = 1 := by
  simp [tenBasisF4]

theorem tenBasisF4_one {ω : GaloisField 2 2} (h0 : ω ≠ 0) (h1 : ω ≠ 1) :
    tenBasisF4 h0 h1 1 = ω := by
  simp [tenBasisF4]

theorem ten_key {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (β : (↥(permCore 6) ⊗[ZMod 2] GaloisField 2 2) →ₗ[ZMod 2] V)
    (hker : ∀ t, β t = 0 ↔ ∃ b : GaloisField 2 2, t = CFSG.ASVolI.ChG.onesCore6 ⊗ₜ b)
    {ω : GaloisField 2 2} (h0 : ω ≠ 0) (h1 : ω ≠ 1) (p q : ↥(permCore 6))
    (h : β (p ⊗ₜ (1 : GaloisField 2 2) + q ⊗ₜ ω) = 0) :
    (p = 0 ∨ p = CFSG.ASVolI.ChG.onesCore6) ∧ (q = 0 ∨ q = CFSG.ASVolI.ChG.onesCore6) := by
  obtain ⟨b, hb⟩ := (hker _).1 h
  have hbool : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  set bas := tenBasisF4 h0 h1 with hbas
  have b0 : bas 0 = 1 := tenBasisF4_zero h0 h1
  have b1 : bas 1 = ω := tenBasisF4_one h0 h1
  have c00 : bas.coord 0 1 = 1 := by
    rw [← b0, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same]
  have c01 : bas.coord 0 ω = 0 := by
    rw [← b1, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    decide
  have c10 : bas.coord 1 1 = 0 := by
    rw [← b0, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    decide
  have c11 : bas.coord 1 ω = 1 := by
    rw [← b1, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same]
  let Λ₀ : (↥(permCore 6) ⊗[ZMod 2] GaloisField 2 2) →ₗ[ZMod 2] ↥(permCore 6) :=
    (TensorProduct.rid (ZMod 2) (↥(permCore 6))).toLinearMap ∘ₗ
      LinearMap.lTensor (↥(permCore 6)) (bas.coord 0)
  let Λ₁ : (↥(permCore 6) ⊗[ZMod 2] GaloisField 2 2) →ₗ[ZMod 2] ↥(permCore 6) :=
    (TensorProduct.rid (ZMod 2) (↥(permCore 6))).toLinearMap ∘ₗ
      LinearMap.lTensor (↥(permCore 6)) (bas.coord 1)
  have hΛ₀ : ∀ (a : ↥(permCore 6)) (c : GaloisField 2 2), Λ₀ (a ⊗ₜ c) = bas.coord 0 c • a := by
    intro a c
    simp [Λ₀, TensorProduct.rid_tmul]
  have hΛ₁ : ∀ (a : ↥(permCore 6)) (c : GaloisField 2 2), Λ₁ (a ⊗ₜ c) = bas.coord 1 c • a := by
    intro a c
    simp [Λ₁, TensorProduct.rid_tmul]
  have hp : p = bas.coord 0 b • CFSG.ASVolI.ChG.onesCore6 := by
    have := congrArg Λ₀ hb
    rw [map_add, hΛ₀, hΛ₀, hΛ₀, c00, c01, one_smul, zero_smul, add_zero] at this
    exact this
  have hq : q = bas.coord 1 b • CFSG.ASVolI.ChG.onesCore6 := by
    have := congrArg Λ₁ hb
    rw [map_add, hΛ₁, hΛ₁, hΛ₁, c10, c11, zero_smul, one_smul, zero_add] at this
    exact this
  constructor
  · rcases hbool (bas.coord 0 b) with hc | hc <;> rw [hc] at hp <;> simp at hp <;> simp [hp]
  · rcases hbool (bas.coord 1 b) with hc | hc <;> rw [hc] at hq <;> simp at hq <;> simp [hq]

theorem ten_sub_eq_add {M : Type} [AddCommGroup M] [Module (ZMod 2) M] (x y : M) :
    x - y = x + y := by
  rw [sub_eq_add_neg, neg_eq_of_add_eq_zero_left (ten_add_self y)]

theorem ten_cancel3 {M : Type} [AddCommGroup M] (hM : ∀ x : M, x + x = 0) (x y z : M) :
    x + y + (z + y) = x + z := by
  calc x + y + (z + y) = (x + z) + (y + y) := by abel
    _ = x + z := by rw [hM, add_zero]

theorem ten_fin6_add_self : ∀ x : Fin 6 → ZMod 2, x + x = 0 := fun x => by
  funext k
  rw [Pi.add_apply, Pi.zero_apply]
  revert k
  suffices h : ∀ r : ZMod 2, r + r = 0 from fun k => h (x k)
  decide

theorem ten_permAct_single {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) (r : ZMod 2) :
    permAct σ (Pi.single i r) = Pi.single (σ i) r := by
  funext k
  simp [permAct, Pi.single_apply, Equiv.symm_apply_eq]

theorem ten_permAct_add {n : ℕ} (σ : Equiv.Perm (Fin n)) (x y : Fin n → ZMod 2) :
    permAct σ (x + y) = permAct σ x + permAct σ y := by
  funext k
  rfl

theorem ten_permAct_mem {n : ℕ} (σ : Equiv.Perm (Fin n)) {x : Fin n → ZMod 2}
    (h : x ∈ permCore n) : permAct σ x ∈ permCore n := by
  have hx : ∑ k, x k = 0 := h
  show ∑ k, permAct σ x k = 0
  simp only [permAct]
  rw [Equiv.sum_comp σ⁻¹ x]
  exact hx

theorem ten_pair_mem {n : ℕ} {i j : Fin n} (h : i ≠ j) :
    (Pi.single i (1 : ZMod 2) + Pi.single j 1 : Fin n → ZMod 2) ∈ permCore n := by
  show ∑ k, (Pi.single i (1 : ZMod 2) + Pi.single j 1 : Fin n → ZMod 2) k = 0
  rw [Finset.sum_congr rfl (fun k _ => Pi.add_apply _ _ k), Finset.sum_add_distrib]
  simp [Pi.single_apply, h, h.symm]
  decide

theorem ten_inner_three_le {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (β : (↥(permCore 6) ⊗[ZMod 2] GaloisField 2 2) →ₗ[ZMod 2] V)
    (hker : ∀ t, β t = 0 ↔ ∃ b : GaloisField 2 2, t = CFSG.ASVolI.ChG.onesCore6 ⊗ₜ b)
    (σ : Equiv.Perm (Fin 6)) (hσ2 : σ * σ = 1) (hσc : σ.support.card = 4)
    (e : V ≃ₗ[ZMod 2] V)
    (hequ : ∀ (a a' : ↥(permCore 6)) (b : GaloisField 2 2),
      (a' : Fin 6 → ZMod 2) = permAct σ (a : Fin 6 → ZMod 2) → β (a' ⊗ₜ b) = e (β (a ⊗ₜ b))) :
    3 ≤ Module.finrank (ZMod 2) (LinearMap.range (e.toLinearMap - LinearMap.id)) := by
  classical
  set S := σ.support with hS
  have hmem : ∀ x, x ∈ S ↔ σ x ≠ x := fun x => Equiv.Perm.mem_support
  have hinv : ∀ x, σ (σ x) = x := fun x => by
    have h := congrArg (fun g : Equiv.Perm (Fin 6) => g x) hσ2
    simpa [Equiv.Perm.mul_apply] using h
  obtain ⟨a, ha⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
  have hab : σ a ≠ a := (hmem a).1 ha
  have hbS : σ a ∈ S := (hmem (σ a)).2 (by rw [hinv]; exact fun h => hab h.symm)
  have hcard2 : ((S.erase a).erase (σ a)).card = 2 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hab, hbS⟩), Finset.card_erase_of_mem ha, hσc]
  obtain ⟨c, hc⟩ : ((S.erase a).erase (σ a)).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨hcb, hc1⟩ := Finset.mem_erase.1 hc
  obtain ⟨hca, hcS⟩ := Finset.mem_erase.1 hc1
  have hcσ : σ c ≠ c := (hmem c).1 hcS
  obtain ⟨d, hd⟩ : ∃ d, d = σ c := ⟨_, rfl⟩
  have hdS : d ∈ S := (hmem d).2 (by rw [hd, hinv]; exact fun h => hcσ h.symm)
  have hda : d ≠ a := by
    intro h
    apply hcb
    calc c = σ (σ c) := (hinv c).symm
      _ = σ a := by rw [← hd, h]
  have hdb : d ≠ σ a := by
    intro h
    apply hca
    exact σ.injective (by rw [← hd, h])
  obtain ⟨f, hfS⟩ : ∃ f, f ∉ S := by
    by_contra hall
    push_neg at hall
    have huniv : S = Finset.univ := Finset.eq_univ_of_forall hall
    rw [huniv, Finset.card_univ, Fintype.card_fin] at hσc
    omega
  have hσf : σ f = f := by
    by_contra h
    exact hfS ((hmem f).2 h)
  have hfa : f ≠ a := fun h => hfS (h ▸ ha)
  have hfb : f ≠ σ a := fun h => hfS (h ▸ hbS)
  have hfc : f ≠ c := fun h => hfS (h ▸ hcS)
  have hfd : f ≠ d := fun h => hfS (h ▸ hdS)
  have hcd : c ≠ d := fun h => hcσ (hd.symm.trans h.symm)
  obtain ⟨U, hU⟩ : ∃ U : Fin 6 → ZMod 2, U = Pi.single a 1 + Pi.single f 1 := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : Fin 6 → ZMod 2, W = Pi.single c 1 + Pi.single f 1 := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : Fin 6 → ZMod 2, A = Pi.single a 1 + Pi.single (σ a) 1 := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Fin 6 → ZMod 2, B = Pi.single c 1 + Pi.single d 1 := ⟨_, rfl⟩
  have hUm : U ∈ permCore 6 := by rw [hU]; exact ten_pair_mem hfa.symm
  have hWm : W ∈ permCore 6 := by rw [hW]; exact ten_pair_mem hfc.symm
  have hAm : A ∈ permCore 6 := by rw [hA]; exact ten_pair_mem hab.symm
  have hBm : B ∈ permCore 6 := by rw [hB]; exact ten_pair_mem hcd
  have hσU : permAct σ U + U = A := by
    rw [hU, ten_permAct_add, ten_permAct_single, ten_permAct_single, hσf, hA,
      add_comm (Pi.single a (1 : ZMod 2) : Fin 6 → ZMod 2) (Pi.single (σ a) 1)]
    exact ten_cancel3 ten_fin6_add_self _ _ _
  have hσW : permAct σ W + W = B := by
    rw [hW, ten_permAct_add, ten_permAct_single, ten_permAct_single, hσf, ← hd, hB,
      add_comm (Pi.single c (1 : ZMod 2) : Fin 6 → ZMod 2) (Pi.single d 1)]
    exact ten_cancel3 ten_fin6_add_self _ _ _
  obtain ⟨ω, h0, h1⟩ : ∃ ω : GaloisField 2 2, ω ≠ 0 ∧ ω ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    have hsurj : Function.Surjective (fun i : Fin 2 => if i = 0 then (0 : GaloisField 2 2) else 1) := by
      intro x
      by_cases hx : x = 0
      · exact ⟨0, by simp [hx]⟩
      · exact ⟨1, by simp [hcon x hx]⟩
    have hle := Nat.card_le_card_of_surjective _ hsurj
    have h4 : Nat.card (GaloisField 2 2) = 2 ^ 2 := GaloisField.card 2 2 (by norm_num)
    rw [h4, Nat.card_eq_fintype_card, Fintype.card_fin] at hle
    norm_num at hle
  obtain ⟨Uc, hUc⟩ : ∃ x : ↥(permCore 6), (x : Fin 6 → ZMod 2) = U := ⟨⟨U, hUm⟩, rfl⟩
  obtain ⟨Wc, hWc⟩ : ∃ x : ↥(permCore 6), (x : Fin 6 → ZMod 2) = W := ⟨⟨W, hWm⟩, rfl⟩
  obtain ⟨Ac, hAc⟩ : ∃ x : ↥(permCore 6), (x : Fin 6 → ZMod 2) = A := ⟨⟨A, hAm⟩, rfl⟩
  obtain ⟨Bc, hBc⟩ : ∃ x : ↥(permCore 6), (x : Fin 6 → ZMod 2) = B := ⟨⟨B, hBm⟩, rfl⟩
  obtain ⟨σU, hσUd⟩ : ∃ x : ↥(permCore 6), (x : Fin 6 → ZMod 2) = permAct σ U :=
    ⟨⟨_, ten_permAct_mem σ hUm⟩, rfl⟩
  obtain ⟨σW, hσWd⟩ : ∃ x : ↥(permCore 6), (x : Fin 6 → ZMod 2) = permAct σ W :=
    ⟨⟨_, ten_permAct_mem σ hWm⟩, rfl⟩
  have hσUc : σU + Uc = Ac := Subtype.ext (by rw [Submodule.coe_add, hσUd, hUc, hAc]; exact hσU)
  have hσWc : σW + Wc = Bc := Subtype.ext (by rw [Submodule.coe_add, hσWd, hWc, hBc]; exact hσW)
  have hequU1 := hequ Uc σU 1 (by rw [hσUd, hUc])
  have hequW1 := hequ Wc σW 1 (by rw [hσWd, hWc])
  have hequUω := hequ Uc σU ω (by rw [hσUd, hUc])
  have hy1 : ((e.toLinearMap - LinearMap.id : V →ₗ[ZMod 2] V) (β (Uc ⊗ₜ[ZMod 2] (1 : GaloisField 2 2)))) =
      β (Ac ⊗ₜ[ZMod 2] (1 : GaloisField 2 2)) := by
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_toLinearMap]
    rw [← hequU1, ten_sub_eq_add, ← map_add, ← TensorProduct.add_tmul, hσUc]
  have hy2 : ((e.toLinearMap - LinearMap.id : V →ₗ[ZMod 2] V) (β (Wc ⊗ₜ[ZMod 2] (1 : GaloisField 2 2)))) =
      β (Bc ⊗ₜ[ZMod 2] (1 : GaloisField 2 2)) := by
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_toLinearMap]
    rw [← hequW1, ten_sub_eq_add, ← map_add, ← TensorProduct.add_tmul, hσWc]
  have hy3 : ((e.toLinearMap - LinearMap.id : V →ₗ[ZMod 2] V) (β (Uc ⊗ₜ[ZMod 2] ω))) =
      β (Ac ⊗ₜ[ZMod 2] ω) := by
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_toLinearMap]
    rw [← hequUω, ten_sub_eq_add, ← map_add, ← TensorProduct.add_tmul, hσUc]
  have hli : LinearIndependent (ZMod 2)
      ![β (Ac ⊗ₜ[ZMod 2] (1 : GaloisField 2 2)), β (Bc ⊗ₜ[ZMod 2] (1 : GaloisField 2 2)),
        β (Ac ⊗ₜ[ZMod 2] ω)] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_three] at hg
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons] at hg
    have hexp : β ((g 0 • Ac + g 1 • Bc) ⊗ₜ[ZMod 2] (1 : GaloisField 2 2) +
        (g 2 • Ac) ⊗ₜ[ZMod 2] ω) =
        g 0 • β (Ac ⊗ₜ[ZMod 2] (1 : GaloisField 2 2)) + g 1 • β (Bc ⊗ₜ[ZMod 2] (1 : GaloisField 2 2)) +
          g 2 • β (Ac ⊗ₜ[ZMod 2] ω) := by
      simp only [TensorProduct.add_tmul, map_add, ← TensorProduct.smul_tmul', map_smul]
    have hsum := hexp.trans hg
    obtain ⟨hp, hq⟩ := ten_key β hker h0 h1 (g 0 • Ac + g 1 • Bc) (g 2 • Ac) hsum
    have hAf : A f = 0 := by simp [hA, Pi.single_apply, hfa, hfb]
    have hAa : A a = 1 := by simp [hA, Pi.single_apply, Ne.symm hab]
    have hAc' : A c = 0 := by simp [hA, Pi.single_apply, hca, hcb]
    have hBf : B f = 0 := by simp [hB, Pi.single_apply, hfc, hfd]
    have hBa : B a = 0 := by simp [hB, Pi.single_apply, Ne.symm hca, Ne.symm hda]
    have hBc' : B c = 1 := by simp [hB, Pi.single_apply, hcd]
    have hcoordp : ∀ k, ((g 0 • Ac + g 1 • Bc : ↥(permCore 6)) : Fin 6 → ZMod 2) k =
        g 0 * A k + g 1 * B k := by
      intro k
      simp [hAc, hBc, smul_eq_mul]
    have hcoordq : ∀ k, ((g 2 • Ac : ↥(permCore 6)) : Fin 6 → ZMod 2) k = g 2 * A k := by
      intro k
      simp [hAc, smul_eq_mul]
    have hpz : (g 0 • Ac + g 1 • Bc : ↥(permCore 6)) = 0 := by
      rcases hp with hp | hp
      · exact hp
      · exfalso
        have h1' := congrArg (fun z : ↥(permCore 6) => (z : Fin 6 → ZMod 2) f) hp
        simp [hcoordp, hAf, hBf, CFSG.ASVolI.ChG.onesCore6] at h1'
    have hqz : (g 2 • Ac : ↥(permCore 6)) = 0 := by
      rcases hq with hq | hq
      · exact hq
      · exfalso
        have h1' := congrArg (fun z : ↥(permCore 6) => (z : Fin 6 → ZMod 2) f) hq
        simp [hcoordq, hAf, CFSG.ASVolI.ChG.onesCore6] at h1'
    have hp_at : ∀ k, g 0 * A k + g 1 * B k = 0 := by
      intro k
      rw [← hcoordp k, hpz]
      simp
    have hq_at : ∀ k, g 2 * A k = 0 := by
      intro k
      rw [← hcoordq k, hqz]
      simp
    have g0z : g 0 = 0 := by simpa [hAa, hBa] using hp_at a
    have g1z : g 1 = 0 := by simpa [hAc', hBc'] using hp_at c
    have g2z : g 2 = 0 := by simpa [hAa] using hq_at a
    intro i
    fin_cases i
    · exact g0z
    · exact g1z
    · exact g2z
  have hspan : Submodule.span (ZMod 2)
      (Set.range ![β (Ac ⊗ₜ[ZMod 2] (1 : GaloisField 2 2)), β (Bc ⊗ₜ[ZMod 2] (1 : GaloisField 2 2)),
        β (Ac ⊗ₜ[ZMod 2] ω)]) ≤ LinearMap.range (e.toLinearMap - LinearMap.id : V →ₗ[ZMod 2] V) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact ⟨β (Uc ⊗ₜ[ZMod 2] (1 : GaloisField 2 2)), hy1⟩
    · exact ⟨β (Wc ⊗ₜ[ZMod 2] (1 : GaloisField 2 2)), hy2⟩
    · exact ⟨β (Uc ⊗ₜ[ZMod 2] ω), hy3⟩
  have hfin : Module.finrank (ZMod 2) (Submodule.span (ZMod 2)
      (Set.range ![β (Ac ⊗ₜ[ZMod 2] (1 : GaloisField 2 2)), β (Bc ⊗ₜ[ZMod 2] (1 : GaloisField 2 2)),
        β (Ac ⊗ₜ[ZMod 2] ω)])) = 3 := by
    rw [finrank_span_eq_card hli]
    rfl
  rw [← hfin]
  exact Submodule.finrank_mono hspan

end CFSG.Quasithin.G112A2
