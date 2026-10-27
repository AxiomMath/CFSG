module

public import CFSG.Quasithin.Background.G25Four
public import CFSG.Quasithin.Background.G25Dual

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.SL2Model
  CFSG.Quasithin.SL3Model
open scoped MatrixGroups Pointwise commutatorElement

variable {G : Type*} [Group G]

theorem conj_mem_sup {x : G} {X Y X' Y' : Subgroup G} (hX : ∀ y ∈ X, x * y * x⁻¹ ∈ X')
    (hY : ∀ y ∈ Y, x * y * x⁻¹ ∈ Y') : ∀ y ∈ X ⊔ Y, x * y * x⁻¹ ∈ X' ⊔ Y' := by
  have h : X ⊔ Y ≤ (X' ⊔ Y').comap (MulAut.conj x).toMonoidHom :=
    sup_le (fun y hy => (le_sup_left : X' ≤ X' ⊔ Y') (hX y hy))
      (fun y hy => (le_sup_right : Y' ≤ X' ⊔ Y') (hY y hy))
  exact fun y hy => h hy

theorem comm_mem_sup_of {x : G} {N X Y J : Subgroup G} (hN : ∀ y ∈ J, ∀ z ∈ N, y * z * y⁻¹ ∈ N)
    (hX : X ≤ J) (hY : Y ≤ J) (h₁ : ∀ y ∈ X, x * y * x⁻¹ * y⁻¹ ∈ N)
    (h₂ : ∀ y ∈ Y, x * y * x⁻¹ * y⁻¹ ∈ N) : ∀ y ∈ X ⊔ Y, x * y * x⁻¹ * y⁻¹ ∈ N := by
  let Z : Subgroup G :=
    { carrier := {y | y ∈ J ∧ x * y * x⁻¹ * y⁻¹ ∈ N}
      one_mem' := ⟨J.one_mem, by simp⟩
      mul_mem' := by
        rintro y z ⟨hyJ, hy⟩ ⟨hzJ, hz⟩
        refine ⟨J.mul_mem hyJ hzJ, ?_⟩
        have h1 : y * (x * z * x⁻¹ * z⁻¹) * y⁻¹ ∈ N := hN y hyJ _ hz
        have : x * (y * z) * x⁻¹ * (y * z)⁻¹ =
            (x * y * x⁻¹ * y⁻¹) * (y * (x * z * x⁻¹ * z⁻¹) * y⁻¹) := by group
        rw [this]
        exact N.mul_mem hy h1
      inv_mem' := by
        rintro y ⟨hyJ, hy⟩
        refine ⟨J.inv_mem hyJ, ?_⟩
        have h1 : y⁻¹ * (x * y * x⁻¹ * y⁻¹)⁻¹ * y ∈ N := by
          have := hN y⁻¹ (J.inv_mem hyJ) _ (N.inv_mem hy)
          simpa [mul_assoc] using this
        have : x * y⁻¹ * x⁻¹ * y⁻¹⁻¹ = y⁻¹ * (x * y * x⁻¹ * y⁻¹)⁻¹ * y := by group
        rw [this]
        exact h1 }
  have hXZ : X ≤ Z := fun y hy => ⟨hX hy, h₁ y hy⟩
  have hYZ : Y ≤ Z := fun y hy => ⟨hY hy, h₂ y hy⟩
  intro y hy
  exact (sup_le hXZ hYZ hy).2

section TripleL3

variable {F : Type*} [Field F]

structure TripleL3 (I S : Subgroup G) (Uk : Fin 3 → Subgroup G) (Φ : ↥I →* SL(3, F))
    (p : Fin 3 → Fin 3 → F) (Q : SL(3, F)) (lam : Fin 3 → F) : Prop where
  tg : TripleGrp I S Uk
  surj : Function.Surjective Φ
  ker : ∀ x : ↥I, Φ x = 1 ↔ (x : G) ∈ S
  conj : ∀ (a b : Fin 3) (x : ↥I), (∃ c : F, Φ x • p a = c • p b) →
    ∀ y ∈ Uk a, (x : G) * y * (x : G)⁻¹ ∈ Uk b
  mem_Qv : ∀ (a : Fin 3) (x : ↥I), (x : G) ∈ Uk a → Φ x ∈ Qv (p a)
  lift : ∀ (a : Fin 3) (r : SL(3, F)), r ∈ Qv (p a) → ∃ x : ↥I, (x : G) ∈ Uk a ∧ Φ x = r
  lam_ne : ∀ k, lam k ≠ 0
  basis : ∀ k, Q • vE F k = lam k • p k
  invS₃ : ∀ x ∈ I, ∀ y ∈ TripleGrp.S₃ S Uk, x * y * x⁻¹ ∈ TripleGrp.S₃ S Uk

namespace TripleL3

variable {I S : Subgroup G} {Uk : Fin 3 → Subgroup G} {Φ : ↥I →* SL(3, F)}
  {p : Fin 3 → Fin 3 → F} {Q : SL(3, F)} {lam : Fin 3 → F}
  (h : TripleL3 I S Uk Φ p Q lam)

include h

theorem p_eq (k : Fin 3) : p k = (lam k)⁻¹ • (Q • vE F k) := by
  rw [h.basis k, smul_smul, inv_mul_cancel₀ (h.lam_ne k), one_smul]

theorem p_ne_zero (k : Fin 3) : p k ≠ 0 := by
  intro hp
  have h1 := h.basis k
  rw [hp, smul_zero, smul_eq_zero_iff_eq] at h1
  have := congrFun h1 k
  simp [vE] at this

theorem smul_pt {A : SL(3, F)} {π : Fin 3 → Fin 3}
    (hA : ∀ m, ∃ c : F, A • vE F m = c • vE F (π m)) (m : Fin 3) :
    ∃ c : F, (Q * A * Q⁻¹) • p m = c • p (π m) := by
  obtain ⟨c, hc⟩ := hA m
  refine ⟨(lam m)⁻¹ * c * lam (π m), ?_⟩
  have e1 : (Q * A * Q⁻¹) • (Q • vE F m) = Q • (A • vE F m) := by
    simp [mul_smul]
  rw [h.p_eq m, smul_comm (Q * A * Q⁻¹) (lam m)⁻¹ _, e1, hc, smul_comm Q c _, h.basis (π m),
    smul_smul, smul_smul]

theorem inv_pt {a b : Fin 3} (x : ↥I) (hx : ∃ c : F, Φ x • p a = c • p b) :
    ∃ c : F, Φ x⁻¹ • p b = c • p a := by
  obtain ⟨c, hc⟩ := hx
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul, smul_eq_zero_iff_eq] at hc
    exact h.p_ne_zero a hc
  refine ⟨c⁻¹, ?_⟩
  rw [map_inv, inv_smul_eq_iff, smul_comm, hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]

theorem conj_W {a b : Fin 3} (x : ↥I) (hx : ∃ c : F, Φ x • p a = c • p b) :
    ∀ y ∈ TripleGrp.W S Uk a, (x : G) * y * (x : G)⁻¹ ∈ TripleGrp.W S Uk b :=
  fun y hy => ⟨h.conj a b x hx y hy.1, h.tg.S_norm x x.2 y hy.2⟩

theorem conj_S₃ (x : ↥I) :
    ∀ y ∈ TripleGrp.S₃ S Uk, (x : G) * y * (x : G)⁻¹ ∈ TripleGrp.S₃ S Uk :=
  fun y hy => h.invS₃ x x.2 y hy

theorem conj_sup {a b : Fin 3} (x : ↥I) (hx : ∃ c : F, Φ x • p a = c • p b) :
    ∀ y ∈ TripleGrp.W S Uk a ⊔ TripleGrp.S₃ S Uk,
      (x : G) * y * (x : G)⁻¹ ∈ TripleGrp.W S Uk b ⊔ TripleGrp.S₃ S Uk :=
  conj_mem_sup (h.conj_W x hx) (h.conj_S₃ x)

theorem Qv_Q (a : Fin 3) : Qv (Q • vE F a) = Qv (p a) := by
  rw [h.basis a, Qv_smul (h.lam_ne a)]

theorem lift_Q (a : Fin 3) {r : SL(3, F)} (hr : r ∈ Qv (Q • vE F a)) :
    ∃ x : ↥I, (x : G) ∈ Uk a ∧ Φ x = r := by
  rw [h.Qv_Q] at hr
  exact h.lift a r hr

theorem exists_lift_wS [CharP F 2] {i j : Fin 3} (hij : i ≠ j) :
    ∃ x : ↥I, Φ x = Q * G1.wS F hij * Q⁻¹ ∧
      ∀ m, ∃ c : F, Φ x • p m = c • p (Equiv.swap i j m) := by
  obtain ⟨x, hx⟩ := h.surj (Q * G1.wS F hij * Q⁻¹)
  refine ⟨x, hx, fun m => ?_⟩
  rw [hx]
  exact h.smul_pt (fun m => ⟨1, by rw [one_smul]; exact wS_smul_single hij m⟩) m

theorem exists_lift_diag {d : SL(3, F)} (hd : DiagLike d) :
    ∃ x : ↥I, Φ x = Q * d * Q⁻¹ ∧ ∀ m, ∃ c : F, Φ x • p m = c • p m := by
  obtain ⟨x, hx⟩ := h.surj (Q * d * Q⁻¹)
  refine ⟨x, hx, fun m => ?_⟩
  rw [hx]
  exact h.smul_pt (π := id) (fun m => hd.smul_single m) m

theorem exists_lift_transvection {a b : Fin 3} (hab : a ≠ b) (c : F) :
    ∃ x : ↥I, (x : G) ∈ Uk a ∧
      Φ x = Q * Matrix.SpecialLinearGroup.transvection hab c * Q⁻¹ ∧
      ∀ m, m ≠ b → Φ x • p m = p m := by
  have hmem : Q * Matrix.SpecialLinearGroup.transvection hab c * Q⁻¹ ∈ Qv (Q • vE F a) :=
    (mem_Qv_conj Q _).2 (transvection_mem_Qv hab c)
  obtain ⟨x, hxU, hx⟩ := h.lift_Q a hmem
  refine ⟨x, hxU, hx, fun m hm => ?_⟩
  have hT : Matrix.SpecialLinearGroup.transvection hab c • vE F m = vE F m := by
    rw [transvection_smul hab c]
    simp [vE, hm.symm]
  rw [hx, h.p_eq m, smul_comm (Q * Matrix.SpecialLinearGroup.transvection hab c * Q⁻¹) (lam m)⁻¹ _]
  congr 1
  simp only [mul_smul, inv_smul_smul, hT]

end TripleL3

end TripleL3

namespace L3Setting

variable [Finite G] {n : ℕ} {V V₁ L T H : Subgroup G} (St : L3Setting n V V₁ L T H)
  {g h : G} (hg : g ∈ L) (hh : h ∈ L)

include St hg hh in
theorem tripleL3 (hV : V = V₁ ⊔ rconj V₁ g ⊔ rconj V₁ h) :
    ∃ (Q : SL(3, GaloisField 2 n)) (lam : Fin 3 → GaloisField 2 n),
      TripleL3 (L ⊔ conjClosure V H) (pCoreOf 2 (L ⊔ conjClosure V H))
        (tripleU (conjClosure V H) g h) St.Phi
        (fun k => St.pvec (tripleConj_mem hg hh k)) Q lam := by
  obtain ⟨Q, lam, hlam, hQ⟩ := St.exists_basis_Q hg hh hV
  refine ⟨Q, lam, ?_⟩
  exact
    { tg := St.tripleGrp hg hh hV
      surj := St.Phi_surjective
      ker := St.Phi_eq_one_iff_mem_S
      conj := fun a b x hx y hy =>
        St.conj_rconj_mem (tripleConj_mem hg hh a) (tripleConj_mem hg hh b) x hx hy
      mem_Qv := fun a x hx => St.Phi_mem_Qv_of_mem_rconj (tripleConj_mem hg hh a) x hx
      lift := fun a r hr => by
        obtain ⟨x, hx, hxr⟩ := St.exists_lift (tripleConj_mem hg hh a) hr
        exact ⟨x, hx, hxr⟩
      lam_ne := hlam
      basis := hQ
      invS₃ := fun x hx y hy =>
        (Subgroup.mem_normalizer_iff.1 (St.G25_four_inv hg hh hV hx) y).1 hy }

end L3Setting

end CFSG.Quasithin
