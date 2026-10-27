module

public import CFSG.RankThree.GF2n.Tim79Defs

public section

namespace CFSG.RankThree.GF2n.Tim79

open scoped commutatorElement

open CFSG.GH74.GLS.Bg.TwoGroups

structure QuadModel {G : Type} [Group G] (QF V : Subgroup G) (K : Type) [Field K]
    (γ : G → K) where
  E : Type
  [acg : AddCommGroup E]
  [mod : Module K E]
  [fin : Module.Finite K E]
  π : G → E
  B : LinearMap.BilinForm K E
  Qf : E → K
  π_mul : ∀ x ∈ QF, ∀ y ∈ QF, π (x * y) = π x + π y
  π_surj : ∀ e : E, ∃ x ∈ QF, π x = e
  π_ker : ∀ x ∈ QF, π x = 0 ↔ x ∈ V
  comm_mem : ∀ x ∈ QF, ∀ y ∈ QF, ⁅x, y⁆ ∈ V
  sq_mem : ∀ x ∈ QF, x ^ 2 ∈ V
  comm_eq : ∀ x ∈ QF, ∀ y ∈ QF, γ ⁅x, y⁆ = B (π x) (π y)
  sq_eq : ∀ x ∈ QF, γ (x ^ 2) = Qf (π x)
  alt : ∀ e, B e e = 0
  nondeg : ∀ e, (∀ f, B e f = 0) → e = 0
  Qf_smul : ∀ (a : K) e, Qf (a • e) = a ^ 2 * Qf e
  Qf_add : ∀ e f, Qf (e + f) = Qf e + Qf f + B e f

attribute [instance] QuadModel.acg QuadModel.mod QuadModel.fin

private theorem heis_mul_aux {G : Type} [Group G] (Z Z' W a a' b b' : G)
    (haZ' : a * Z' = Z' * a) (hbZ' : b * Z' = Z' * b) (haW : a * W = W * a)
    (hba : b * a' = W * (a' * b)) :
    Z * (a * b) * (Z' * (a' * b')) = Z * Z' * W * (a * a' * (b * b')) := by
  calc Z * (a * b) * (Z' * (a' * b')) = Z * (a * (b * Z') * (a' * b')) := by
        simp only [mul_assoc]
    _ = Z * (a * (Z' * b) * (a' * b')) := by rw [hbZ']
    _ = Z * ((a * Z') * (b * (a' * b'))) := by simp only [mul_assoc]
    _ = Z * ((Z' * a) * (b * (a' * b'))) := by rw [haZ']
    _ = Z * Z' * (a * ((b * a') * b')) := by simp only [mul_assoc]
    _ = Z * Z' * (a * ((W * (a' * b)) * b')) := by rw [hba]
    _ = Z * Z' * ((a * W) * (a' * (b * b'))) := by simp only [mul_assoc]
    _ = Z * Z' * ((W * a) * (a' * (b * b'))) := by rw [haW]
    _ = Z * Z' * W * (a * a' * (b * b')) := by simp only [mul_assoc]

section Heis

variable {G : Type} [Group G] {QF V : Subgroup G} {K : Type} [Field K] {γ : G → K}

private structure Heis (QF V : Subgroup G) (γ : G → K) : Prop where
  hV : V ≤ QF
  hVc : ∀ v ∈ V, ∀ y ∈ QF, v * y = y * v
  hγadd : ∀ a ∈ V, ∀ b ∈ V, γ (a * b) = γ a + γ b
  hγinj : ∀ a ∈ V, γ a = 0 → a = 1
  hγsurj : ∀ s, ∃ a ∈ V, γ a = s

section Basics

variable [CharP K 2] (M : QuadModel QF V K γ)

private theorem pi_one : M.π 1 = 0 := by
  have h := M.π_mul 1 QF.one_mem 1 QF.one_mem
  rw [mul_one] at h
  exact left_eq_add.mp h

private theorem pi_inv {x : G} (hx : x ∈ QF) : M.π x⁻¹ = - M.π x := by
  have h := M.π_mul x hx x⁻¹ (QF.inv_mem hx)
  rw [mul_inv_cancel, pi_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

private theorem γ_one (H : Heis QF V γ) : γ 1 = 0 := by
  have h := H.hγadd 1 V.one_mem 1 V.one_mem
  rw [mul_one] at h
  exact left_eq_add.mp h

private theorem γ_inv (H : Heis QF V γ) {a : G} (ha : a ∈ V) : γ a⁻¹ = γ a := by
  have h := H.hγadd a ha a⁻¹ (V.inv_mem ha)
  rw [mul_inv_cancel, γ_one H] at h
  have h2 : γ a + γ a⁻¹ = 0 := h.symm
  rw [CharTwo.add_eq_zero] at h2
  exact h2.symm

private theorem eq_of_γ_eq (H : Heis QF V γ) {a b : G} (ha : a ∈ V) (hb : b ∈ V)
    (h : γ a = γ b) : a = b := by
  have h1 := H.hγinj (a * b⁻¹) (V.mul_mem ha (V.inv_mem hb)) (by
    rw [H.hγadd a ha b⁻¹ (V.inv_mem hb), γ_inv H hb, h, CharTwo.add_self_eq_zero])
  exact mul_inv_eq_one.mp h1

private noncomputable def vv (H : Heis QF V γ) (s : K) : G := Classical.choose (H.hγsurj s)

private theorem vv_mem (H : Heis QF V γ) (s : K) : vv H s ∈ V :=
  (Classical.choose_spec (H.hγsurj s)).1

private theorem γ_vv (H : Heis QF V γ) (s : K) : γ (vv H s) = s :=
  (Classical.choose_spec (H.hγsurj s)).2

private theorem vv_add (H : Heis QF V γ) (s t : K) : vv H (s + t) = vv H s * vv H t :=
  eq_of_γ_eq H (vv_mem H _) (V.mul_mem (vv_mem H _) (vv_mem H _))
    (by rw [γ_vv H, H.hγadd _ (vv_mem H s) _ (vv_mem H t), γ_vv H, γ_vv H])

private theorem vv_zero (H : Heis QF V γ) : vv H 0 = 1 :=
  eq_of_γ_eq H (vv_mem H _) V.one_mem (by rw [γ_vv H, γ_one H])

private theorem vv_comm (H : Heis QF V γ) (s : K) {y : G} (hy : y ∈ QF) :
    vv H s * y = y * vv H s :=
  H.hVc _ (vv_mem H s) y hy

private theorem mul_eq_vv_mul (H : Heis QF V γ) {x y : G} (hx : x ∈ QF) (hy : y ∈ QF) :
    x * y = vv H (M.B (M.π x) (M.π y)) * (y * x) := by
  have hc : ⁅x, y⁆ = vv H (M.B (M.π x) (M.π y)) := by
    apply eq_of_γ_eq H (M.comm_mem x hx y hy) (vv_mem H _)
    rw [M.comm_eq x hx y hy, γ_vv H]
  rw [← hc, commutatorElement_def]
  group

private theorem commute_of_B_eq_zero (H : Heis QF V γ) {x y : G} (hx : x ∈ QF) (hy : y ∈ QF)
    (h : M.B (M.π x) (M.π y) = 0) : x * y = y * x := by
  rw [mul_eq_vv_mul M H hx hy, h, vv_zero, one_mul]

private theorem mul_self_eq_one_of_Qf_eq_zero (H : Heis QF V γ) {x : G} (hx : x ∈ QF)
    (h : M.Qf (M.π x) = 0) : x * x = 1 := by
  have h1 := H.hγinj (x ^ 2) (M.sq_mem x hx) (by rw [M.sq_eq x hx, h])
  rwa [sq] at h1

end Basics

section Sections

variable [CharP K 2] (M : QuadModel QF V K γ)

private theorem B_eq_zero_of_singular (S : Submodule K M.E) (hS : ∀ x ∈ S, M.Qf x = 0) {x y : M.E}
    (hx : x ∈ S) (hy : y ∈ S) : M.B x y = 0 := by
  have h := M.Qf_add x y
  rw [hS _ (S.add_mem hx hy), hS x hx, hS y hy] at h
  simpa using h.symm

private def lift (S : Submodule K M.E) : Subgroup G where
  carrier := {x | x ∈ QF ∧ M.π x ∈ S}
  mul_mem' := fun {x y} hx hy =>
    ⟨QF.mul_mem hx.1 hy.1, by rw [M.π_mul x hx.1 y hy.1]; exact S.add_mem hx.2 hy.2⟩
  one_mem' := ⟨QF.one_mem, by rw [pi_one]; exact S.zero_mem⟩
  inv_mem' := fun {x} hx => ⟨QF.inv_mem hx.1, by rw [pi_inv M hx.1]; exact S.neg_mem hx.2⟩

private theorem exists_section (H : Heis QF V γ) (S : Submodule K M.E)
    (hS : ∀ x ∈ S, M.Qf x = 0) :
    ∃ a : M.E → G, (∀ e ∈ S, a e ∈ QF) ∧ (∀ e ∈ S, M.π (a e) = e) ∧
      ∀ e ∈ S, ∀ e' ∈ S, a (e + e') = a e * a e' := by
  classical
  have hcomm : ∀ x y : lift M S, x * y = y * x := fun x y =>
    Subtype.ext (commute_of_B_eq_zero M H x.2.1 y.2.1 (B_eq_zero_of_singular M S hS x.2.2 y.2.2))
  letI : CommGroup (lift M S) := { (inferInstance : Group (lift M S)) with mul_comm := hcomm }
  have hsq : ∀ g : lift M S, g * g = 1 := fun g =>
    Subtype.ext (mul_self_eq_one_of_Qf_eq_zero M H g.2.1 (hS _ g.2.2))
  haveI : Module (ZMod 2) (Additive (lift M S)) := AddCommGroup.zmodModule (n := 2) (fun x => by
    rw [two_nsmul]
    exact congrArg Additive.ofMul (hsq (Additive.toMul x)))
  haveI : Module (ZMod 2) S := AddCommGroup.zmodModule (n := 2) (fun x => by
    rw [two_nsmul]
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    rw [← two_smul K x, h2, zero_smul])
  let πA : Additive (lift M S) →+ S :=
    { toFun := fun x => ⟨M.π (Additive.toMul x).1, (Additive.toMul x).2.2⟩
      map_zero' := by
        apply Subtype.ext
        simp [pi_one]
      map_add' := fun x y => by
        apply Subtype.ext
        simp only [toMul_add, Subgroup.coe_mul, Submodule.coe_add]
        exact M.π_mul _ (Additive.toMul x).2.1 _ (Additive.toMul y).2.1 }
  let πl : Additive (lift M S) →ₗ[ZMod 2] S := AddMonoidHom.toZModLinearMap 2 πA
  have hsurj : Function.Surjective πl := by
    intro s
    obtain ⟨x, hx, hxs⟩ := M.π_surj s.1
    refine ⟨Additive.ofMul ⟨x, hx, hxs ▸ s.2⟩, ?_⟩
    apply Subtype.ext
    exact hxs
  obtain ⟨σ, hσ⟩ := πl.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hsurj)
  refine ⟨fun e => if h : e ∈ S then (Additive.toMul (σ ⟨e, h⟩)).1 else 1, ?_, ?_, ?_⟩
  · intro e he
    simp only [he, dif_pos]
    exact (Additive.toMul (σ ⟨e, he⟩)).2.1
  · intro e he
    simp only [he, dif_pos]
    have := congrArg Subtype.val (LinearMap.congr_fun hσ ⟨e, he⟩)
    exact this
  · intro e he e' he'
    simp only [he, he', S.add_mem he he', dif_pos]
    have : σ ⟨e + e', S.add_mem he he'⟩ = σ ⟨e, he⟩ + σ ⟨e', he'⟩ := by
      rw [← map_add]
      rfl
    rw [this, toMul_add, Subgroup.coe_mul]

end Sections

end Heis

section DualFamily

variable {K : Type*} [Field K] [CharP K 2] {E : Type*} [AddCommGroup E] [Module K E]
  [Module.Finite K E]

private theorem bilin_symm (B : LinearMap.BilinForm K E) (hBalt : ∀ x, B x x = 0) (x y : E) :
    B x y = B y x := by
  have h := hBalt (x + y)
  simp only [map_add, LinearMap.add_apply, hBalt, zero_add, add_zero] at h
  exact (CharTwo.add_eq_zero.mp h).symm

private theorem exists_dual_family (B : LinearMap.BilinForm K E) (hBalt : ∀ x, B x x = 0)
    (hnd : ∀ x, (∀ y, B x y = 0) → x = 0) (S₁ S₂ : Submodule K E) (hc : IsCompl S₁ S₂)
    (h₁ : ∀ x ∈ S₁, ∀ y ∈ S₁, B x y = 0) (h₂ : ∀ x ∈ S₂, ∀ y ∈ S₂, B x y = 0) :
    ∃ (k : ℕ) (e f : Fin k → E), (∀ i, e i ∈ S₁) ∧ (∀ i, f i ∈ S₂) ∧
      (∀ i j, B (e i) (f j) = if i = j then 1 else 0) ∧
      ∀ w : E, ∃ c d : Fin k → K, w = ∑ i, (c i • e i + d i • f i) := by
  classical
  have hsymm := bilin_symm B hBalt
  have hnd' : B.Nondegenerate := ⟨hnd, fun y hy => hnd y fun x => by rw [hsymm]; exact hy x⟩
  let b : Module.Basis (Fin (Module.finrank K S₁)) K S₁ := Module.finBasis K S₁
  set k := Module.finrank K S₁ with hk
  let ψ : Fin k → Module.Dual K E := fun j =>
    (b.dualBasis j).comp (S₁.projectionOnto S₂ hc)
  let y : Fin k → E := fun j => (B.toDual hnd').symm (ψ j)
  have hy : ∀ j v, B (y j) v = ψ j v := fun j v => B.apply_toDual_symm_apply (ψ j) v
  have hdec : ∀ w : E, ∃ x ∈ S₁, ∃ z ∈ S₂, x + z = w := fun w => by
    have : w ∈ S₁ ⊔ S₂ := hc.sup_eq_top ▸ Submodule.mem_top
    exact Submodule.mem_sup.mp this
  have hyS : ∀ j, y j ∈ S₂ := by
    intro j
    obtain ⟨x, hx, z, hz, hxz⟩ := hdec (y j)
    have hx0 : x = 0 := by
      refine hnd x fun w => ?_
      obtain ⟨x₁, hx₁, z₁, hz₁, rfl⟩ := hdec w
      rw [map_add, h₁ x hx x₁ hx₁, zero_add]
      have h3 : B x z₁ = B (y j) z₁ - B z z₁ := by
        rw [← hxz, map_add, LinearMap.add_apply]
        ring
      rw [h3, hy, h₂ z hz z₁ hz₁, sub_zero]
      simp only [ψ, LinearMap.comp_apply, Submodule.projectionOnto_apply_of_mem_right hc hz₁,
        map_zero]
    rw [hx0, zero_add] at hxz
    rw [← hxz]
    exact hz
  have hBef : ∀ i j, B (b i) (y j) = if i = j then 1 else 0 := by
    intro i j
    rw [hsymm, hy]
    simp only [ψ, LinearMap.comp_apply]
    rw [Submodule.projectionOnto_apply_of_mem_left hc (b i).2]
    rw [show (⟨(b i : E), (b i).2⟩ : S₁) = b i from rfl, Module.Basis.dualBasis_apply_self]
  refine ⟨k, fun i => (b i : E), y, fun i => (b i).2, hyS, hBef, fun w => ?_⟩
  have hexp : ∀ x : E, ∀ hx : x ∈ S₁, x = ∑ i, (b.repr ⟨x, hx⟩ i) • (b i : E) := by
    intro x hx
    have h := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
    rw [Submodule.coe_sum] at h
    simp only [Submodule.coe_smul] at h
    exact h.symm
  set d : Fin k → K := fun i => B (b i) w with hd
  set w' : E := w - ∑ j, d j • y j with hw'
  have hw'1 : ∀ i, B (b i) w' = 0 := by
    intro i
    rw [hw', map_sub, map_sum]
    simp only [map_smul, hBef, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    simp [hd]
  have hw'S : ∀ x ∈ S₁, B x w' = 0 := by
    intro x hx
    rw [hexp x hx, map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_smul, LinearMap.smul_apply, hw'1, smul_zero]
  obtain ⟨x', hx', z', hz', hxz⟩ := hdec w'
  have hz0 : z' = 0 := by
    refine hnd z' fun v => ?_
    obtain ⟨x₁, hx₁, z₁, hz₁, rfl⟩ := hdec v
    rw [map_add, h₂ z' hz' z₁ hz₁, add_zero, hsymm z' x₁]
    have h3 : B x₁ z' = B x₁ w' - B x₁ x' := by
      rw [← hxz, map_add]
      ring
    rw [h3, hw'S x₁ hx₁, h₁ x₁ hx₁ x' hx', sub_zero]
  have hw'mem : w' ∈ S₁ := by
    rw [hz0, add_zero] at hxz
    rw [← hxz]
    exact hx'
  refine ⟨fun i => b.repr ⟨w', hw'mem⟩ i, d, ?_⟩
  rw [Finset.sum_add_distrib, ← hexp w' hw'mem, hw']
  abel

end DualFamily

section FamilyHom

variable {G : Type} [Group G] {QF V : Subgroup G} {K : Type} [Field K] [CharP K 2] {γ : G → K}
  (M : QuadModel QF V K γ)

private theorem exists_family (H : Heis QF V γ) (hne : QF ≠ V)
    (hyp : ∃ S₁ S₂ : Submodule K M.E, IsCompl S₁ S₂ ∧ (∀ x ∈ S₁, M.Qf x = 0) ∧
      ∀ x ∈ S₂, M.Qf x = 0) :
    ∃ (k : ℕ) (Φ : Fin k → UT3 K →* G), 0 < k ∧ (∀ i u, Φ i u ∈ QF) ∧
      (∀ i, Function.Injective (Φ i)) ∧ (∀ i z, Φ i ⟨0, 0, z⟩ = vv H z) ∧
      (∀ i j, i ≠ j → ∀ u u', Φ i u * Φ j u' = Φ j u' * Φ i u) ∧
      ∀ x ∈ QF, x ∈ ⨆ i, (Φ i).range := by
  obtain ⟨S₁, S₂, hc, hS₁, hS₂⟩ := hyp
  have hB₁ : ∀ x ∈ S₁, ∀ y ∈ S₁, M.B x y = 0 := fun x hx y hy =>
    B_eq_zero_of_singular M S₁ hS₁ hx hy
  have hB₂ : ∀ x ∈ S₂, ∀ y ∈ S₂, M.B x y = 0 := fun x hx y hy =>
    B_eq_zero_of_singular M S₂ hS₂ hx hy
  obtain ⟨k, e, f, he, hf, hef, hspan⟩ := exists_dual_family M.B M.alt M.nondeg S₁ S₂ hc hB₁ hB₂
  obtain ⟨a₁, ha₁Q, ha₁π, ha₁add⟩ := exists_section M H S₁ hS₁
  obtain ⟨a₂, ha₂Q, ha₂π, ha₂add⟩ := exists_section M H S₂ hS₂
  have hsymm := bilin_symm M.B M.alt
  have hk : 0 < k := by
    by_contra hk0
    have hk0' : k = 0 := Nat.eq_zero_of_not_pos hk0
    apply hne
    refine le_antisymm (fun x hx => ?_) H.hV
    rw [← M.π_ker x hx]
    obtain ⟨c, d, hcd⟩ := hspan (M.π x)
    rw [hcd]
    subst hk0'
    simp
  obtain ⟨A, hA⟩ : ∃ A : Fin k → K → G, ∀ i y, A i y = a₁ (y • e i) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨Bq, hBq⟩ : ∃ Bq : Fin k → K → G, ∀ i x, Bq i x = a₂ (x • f i) := ⟨_, fun _ _ => rfl⟩
  have hAQ : ∀ i y, A i y ∈ QF := fun i y => by
    rw [hA]; exact ha₁Q _ (S₁.smul_mem y (he i))
  have hBQ : ∀ i x, Bq i x ∈ QF := fun i x => by
    rw [hBq]; exact ha₂Q _ (S₂.smul_mem x (hf i))
  have hAπ : ∀ i y, M.π (A i y) = y • e i := fun i y => by
    rw [hA]; exact ha₁π _ (S₁.smul_mem y (he i))
  have hBπ : ∀ i x, M.π (Bq i x) = x • f i := fun i x => by
    rw [hBq]; exact ha₂π _ (S₂.smul_mem x (hf i))
  have hAadd : ∀ i y y', A i (y + y') = A i y * A i y' := fun i y y' => by
    rw [hA, hA, hA, add_smul]
    exact ha₁add _ (S₁.smul_mem y (he i)) _ (S₁.smul_mem y' (he i))
  have hBadd : ∀ i x x', Bq i (x + x') = Bq i x * Bq i x' := fun i x x' => by
    rw [hBq, hBq, hBq, add_smul]
    exact ha₂add _ (S₂.smul_mem x (hf i)) _ (S₂.smul_mem x' (hf i))
  have hA0 : ∀ i, A i 0 = 1 := fun i => by
    have h := hAadd i 0 0
    rw [add_zero] at h
    exact mul_eq_left.mp h.symm
  have hB0 : ∀ i, Bq i 0 = 1 := fun i => by
    have h := hBadd i 0 0
    rw [add_zero] at h
    exact mul_eq_left.mp h.symm
  have hrel : ∀ i y x, Bq i x * A i y = vv H (x * y) * (A i y * Bq i x) := by
    intro i y x
    rw [mul_eq_vv_mul M H (hBQ i x) (hAQ i y), hBπ, hAπ]
    congr 2
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hsymm (f i) (e i), hef i i, if_true,
      mul_one]
    ring
  have hcomm_ne : ∀ i j, i ≠ j → ∀ y x, A j y * Bq i x = Bq i x * A j y := by
    intro i j hij y x
    apply commute_of_B_eq_zero M H (hAQ j y) (hBQ i x)
    rw [hAπ, hBπ]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hef j i,
      if_neg (fun h : j = i => hij h.symm), mul_zero]
  have hAA : ∀ i j y y', A i y * A j y' = A j y' * A i y := fun i j y y' =>
    commute_of_B_eq_zero M H (hAQ i y) (hAQ j y') (by
      rw [hAπ, hAπ]
      exact hB₁ _ (S₁.smul_mem y (he i)) _ (S₁.smul_mem y' (he j)))
  have hBB : ∀ i j x x', Bq i x * Bq j x' = Bq j x' * Bq i x := fun i j x x' =>
    commute_of_B_eq_zero M H (hBQ i x) (hBQ j x') (by
      rw [hBπ, hBπ]
      exact hB₂ _ (S₂.smul_mem x (hf i)) _ (S₂.smul_mem x' (hf j)))
  let Φ : Fin k → UT3 K →* G := fun i =>
    { toFun := fun u => vv H u.c * (A i u.b * Bq i u.a)
      map_one' := by
        rw [UT3.one_def]
        simp only [vv_zero, hA0, hB0, one_mul, mul_one]
      map_mul' := fun u u' => by
        rw [UT3.mul_def]
        simp only
        rw [vv_add H (u.c + u'.c) (u.a * u'.b), vv_add H u.c u'.c, hAadd, hBadd]
        exact (heis_mul_aux (vv H u.c) (vv H u'.c) (vv H (u.a * u'.b)) (A i u.b) (A i u'.b)
          (Bq i u.a) (Bq i u'.a) (vv_comm H _ (hAQ i _)).symm (vv_comm H _ (hBQ i _)).symm
          (vv_comm H _ (hAQ i _)).symm (hrel i u'.b u.a)).symm }
  have hΦ : ∀ i u, Φ i u = vv H u.c * (A i u.b * Bq i u.a) := fun _ _ => rfl
  have hΦQ : ∀ i u, Φ i u ∈ QF := fun i u => by
    rw [hΦ]
    exact QF.mul_mem (H.hV (vv_mem H _)) (QF.mul_mem (hAQ _ _) (hBQ _ _))
  have hΦπ : ∀ i u, M.π (Φ i u) = u.b • e i + u.a • f i := by
    intro i u
    rw [hΦ, M.π_mul _ (H.hV (vv_mem H _)) _ (QF.mul_mem (hAQ _ _) (hBQ _ _)),
      M.π_mul _ (hAQ _ _) _ (hBQ _ _), hAπ, hBπ,
      (M.π_ker _ (H.hV (vv_mem H _))).mpr (vv_mem H _), zero_add]
  have hΦv : ∀ i z, Φ i ⟨0, 0, z⟩ = vv H z := fun i z => by
    rw [hΦ]
    simp only [hA0, hB0, mul_one]
  have hrange : ∀ i u, Φ i u ∈ ⨆ i, (Φ i).range := fun i u =>
    Subgroup.mem_iSup_of_mem i ⟨u, rfl⟩
  refine ⟨k, Φ, hk, hΦQ, ?_, hΦv, ?_, ?_⟩
  ·
    intro i
    rw [injective_iff_map_eq_one]
    intro u hu
    have hπ : M.π (Φ i u) = 0 := by rw [hu]; exact pi_one M
    rw [hΦπ] at hπ
    have hx : u.a = 0 := by
      have h1 := congrArg (M.B (e i)) hπ
      simp only [map_add, map_smul, smul_eq_mul, M.alt, hef i i, if_true, mul_zero, mul_one,
        zero_add, map_zero] at h1
      exact h1
    have hy : u.b = 0 := by
      have h2 := congrArg (fun v => M.B v (f i)) hπ
      simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
        hef i i, M.alt, if_true, mul_one, mul_zero, add_zero, map_zero,
        LinearMap.zero_apply] at h2
      exact h2
    have hc0 : u.c = 0 := by
      have h3 : vv H u.c = 1 := by
        rw [hΦ, hx, hy, hA0, hB0, mul_one, mul_one] at hu
        exact hu
      rw [← γ_vv H u.c, h3, γ_one H]
    rw [UT3.one_def]
    ext
    · exact hx
    · exact hy
    · exact hc0
  ·
    intro i j hij u u'
    have key : Commute (Φ i u) (Φ j u') := by
      rw [hΦ, hΦ]
      refine Commute.mul_left (vv_comm H _ (hΦQ j u')) (Commute.mul_left ?_ ?_)
      · exact Commute.mul_right (vv_comm H _ (hAQ i _)).symm
          (Commute.mul_right (hAA i j _ _) (hcomm_ne j i hij.symm _ _))
      · exact Commute.mul_right (vv_comm H _ (hBQ i _)).symm
          (Commute.mul_right (hcomm_ne i j hij _ _).symm (hBB i j _ _))
    exact key
  ·
    intro x hx
    have hmain : ∀ w : M.E, ∃ g ∈ (⨆ i, (Φ i).range), g ∈ QF ∧ M.π g = w := by
      intro w
      obtain ⟨c, d, rfl⟩ := hspan w
      have key : ∀ s : Finset (Fin k), ∃ g ∈ (⨆ i, (Φ i).range), g ∈ QF ∧
          M.π g = ∑ i ∈ s, (c i • e i + d i • f i) := by
        intro s
        induction s using Finset.induction_on with
        | empty => exact ⟨1, Subgroup.one_mem _, QF.one_mem, by simp [pi_one M]⟩
        | insert i s hi ih =>
          obtain ⟨g, hgL, hgQ, hgπ⟩ := ih
          refine ⟨Φ i ⟨d i, c i, 0⟩ * g, Subgroup.mul_mem _ (hrange i _) hgL,
            QF.mul_mem (hΦQ i _) hgQ, ?_⟩
          rw [M.π_mul _ (hΦQ i _) _ hgQ, hΦπ, hgπ, Finset.sum_insert hi]
      exact key Finset.univ
    obtain ⟨g, hgL, hgQ, hgπ⟩ := hmain (M.π x)
    have hxg : x * g⁻¹ ∈ V := by
      rw [← M.π_ker _ (QF.mul_mem hx (QF.inv_mem hgQ)), M.π_mul _ hx _ (QF.inv_mem hgQ),
        pi_inv M hgQ, hgπ]
      exact add_neg_cancel _
    have hVL : x * g⁻¹ ∈ ⨆ i, (Φ i).range := by
      have h0 : x * g⁻¹ = Φ ⟨0, hk⟩ ⟨0, 0, γ (x * g⁻¹)⟩ := by
        rw [hΦv]
        exact eq_of_γ_eq H hxg (vv_mem H _) (by rw [γ_vv H])
      rw [h0]
      exact hrange _ _
    have hxe : x = (x * g⁻¹) * g := by group
    rw [hxe]
    exact Subgroup.mul_mem _ hVL hgL

end FamilyHom

theorem isCentralProductOf_ut3_of_quadModel {G : Type} [Group G] {QF V : Subgroup G} {K : Type}
    [Field K] [CharP K 2] {γ : G → K} (hV : V ≤ QF) (hVc : ∀ v ∈ V, ∀ y ∈ QF, v * y = y * v)
    (hγadd : ∀ a ∈ V, ∀ b ∈ V, γ (a * b) = γ a + γ b) (hγinj : ∀ a ∈ V, γ a = 0 → a = 1)
    (hγsurj : ∀ s, ∃ a ∈ V, γ a = s) (M₀ : QuadModel QF V K γ)
    (hyp : ∃ S₁ S₂ : Submodule K M₀.E, IsCompl S₁ S₂ ∧ (∀ x ∈ S₁, M₀.Qf x = 0) ∧
      ∀ x ∈ S₂, M₀.Qf x = 0) (hne : QF ≠ V) :
    ∃ k : ℕ, IsCentralProductOf (fun D => Nonempty (↥D ≃* UT3 K)) QF V k := by
  have H : Heis QF V γ := ⟨hV, hVc, hγadd, hγinj, hγsurj⟩
  obtain ⟨k, Φ, hk, hΦQ, hinj, hΦv, hcomm, hgen⟩ := exists_family M₀ H hne hyp
  refine ⟨k, hk, fun i => (Φ i).range, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rintro _ ⟨u, rfl⟩
    exact hΦQ i u
  · intro i
    exact ⟨(MonoidHom.ofInjective (hinj i)).symm⟩
  · intro i
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨d, hd, rfl⟩
      obtain ⟨u, hu⟩ := d.2
      have hcu : u ∈ Subgroup.center (UT3 K) := by
        rw [Subgroup.mem_center_iff]
        intro u'
        apply hinj i
        rw [map_mul, map_mul]
        have h1 := congrArg Subtype.val (Subgroup.mem_center_iff.mp hd ⟨Φ i u', ⟨u', rfl⟩⟩)
        simpa [hu] using h1
      obtain ⟨hua, hub⟩ := (ut3_mem_center_iff u).mp hcu
      have hu' : u = ⟨0, 0, u.c⟩ := by
        ext
        · exact hua
        · exact hub
        · rfl
      change (d : G) ∈ V
      rw [← hu, hu', hΦv]
      exact vv_mem H _
    · intro hx
      refine ⟨⟨x, ⟨⟨0, 0, γ x⟩, ?_⟩⟩, ?_, rfl⟩
      · rw [hΦv]
        exact eq_of_γ_eq H (vv_mem H _) hx (by rw [γ_vv H])
      · rw [Subgroup.mem_center_iff]
        rintro ⟨g, ⟨u', rfl⟩⟩
        exact Subtype.ext (hVc x hx _ (hΦQ i u')).symm
  · intro i j hij x hx y hy
    obtain ⟨u, rfl⟩ := hx
    obtain ⟨u', rfl⟩ := hy
    exact hcomm i j hij u u'
  · refine le_antisymm (iSup_le fun i => ?_) fun x hx => hgen x hx
    rintro _ ⟨u, rfl⟩
    exact hΦQ i u

theorem isCentralProductOfL3_of_quadModel {G : Type} [Group G] {n : ℕ} {QF V : Subgroup G}
    {γ : G → GaloisField 2 n} (hV : V ≤ QF) (hVc : ∀ v ∈ V, ∀ y ∈ QF, v * y = y * v)
    (hγadd : ∀ a ∈ V, ∀ b ∈ V, γ (a * b) = γ a + γ b) (hγinj : ∀ a ∈ V, γ a = 0 → a = 1)
    (hγsurj : ∀ s, ∃ a ∈ V, γ a = s) (M₀ : QuadModel QF V (GaloisField 2 n) γ)
    (hyp : ∃ S₁ S₂ : Submodule (GaloisField 2 n) M₀.E, IsCompl S₁ S₂ ∧
      (∀ x ∈ S₁, M₀.Qf x = 0) ∧ ∀ x ∈ S₂, M₀.Qf x = 0) (hne : QF ≠ V) :
    ∃ k : ℕ, IsCentralProductOfL3 QF V n k :=
  isCentralProductOf_ut3_of_quadModel hV hVc hγadd hγinj hγsurj M₀ hyp hne

end CFSG.RankThree.GF2n.Tim79
