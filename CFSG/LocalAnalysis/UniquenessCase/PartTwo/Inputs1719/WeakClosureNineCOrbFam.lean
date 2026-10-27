module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineCOrbGen
public import CFSG.LocalAnalysis.WeakClosure81.NineStruct

public section

namespace CFSG.LocalAnalysis.WeakClosure81.TC914

open CFSG.Quasithin CFSG.Open Subgroup

variable {X : Type} [Group X]

structure OrbData (Lb Tb A C F H₁ X₁ : Subgroup X) (p : ℕ) : Prop where
  T2 : IsPGroup 2 Tb
  A_le : A ≤ Tb
  A_comm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a
  C_le : C ≤ A
  C_inf : C ⊓ normalizer (Lb : Set X) = ⊥
  C_sup : C ⊔ (A ⊓ normalizer (Lb : Set X)) = A
  C_ne : C ≠ ⊥
  lcomm : ∀ g ∈ Tb, g ∉ normalizer (Lb : Set X) → ∀ x ∈ conjSub g Lb, ∀ y ∈ Lb, x * y = y * x
  H_le : H₁ ≤ Lb
  irr : TwoPTwoIrred H₁ (H₁ ⊓ Tb) X₁ p
  elem : IsElemAbelian p X₁
  nontriv : ∃ y ∈ H₁ ⊓ Tb ⊓ normalizer (X₁ : Set X), ∃ x ∈ X₁, y * x * y⁻¹ ≠ x
  cent : H₁ ⊓ centralizer (Lb : Set X) = ⊥
  A1_norm : A ⊓ normalizer (Lb : Set X) ≤ normalizer (H₁ : Set X)
  F_le : F ≤ Tb
  F_normal : Tb ≤ normalizer (F : Set X)
  F_norm : F ≤ normalizer (H₁ : Set X)
  F_comm : ∀ f ∈ F, ∀ x ∈ X₁, f * x * f⁻¹ * x⁻¹ ∈ pCoreOf 2 H₁

@[expose] def orbS (Tb A C F H₁ : Subgroup X) : Subgroup X := orb C (H₁ ⊓ Tb) ⊔ A ⊔ F

@[expose] def orbK (Tb A C F H₁ : Subgroup X) : Subgroup X := orb C H₁ ⊔ orbS Tb A C F H₁

theorem orbS_le_orbK {Tb A C F H₁ : Subgroup X} : orbS Tb A C F H₁ ≤ orbK Tb A C F H₁ :=
  le_sup_right

theorem orb_le_orbK {Tb A C F H₁ : Subgroup X} : orb C H₁ ≤ orbK Tb A C F H₁ := le_sup_left

theorem A_le_orbK {Tb A C F H₁ : Subgroup X} : A ≤ orbK Tb A C F H₁ :=
  (le_sup_right.trans le_sup_left).trans orbS_le_orbK

theorem F_le_orbK {Tb A C F H₁ : Subgroup X} : F ≤ orbK Tb A C F H₁ :=
  le_sup_right.trans orbS_le_orbK

theorem centralizer_le_normalizer_of_le {Lb M : Subgroup X} (hM : M ≤ Lb) :
    centralizer (Lb : Set X) ≤ normalizer (M : Set X) :=
  (centralizer_le hM).trans (Subgroup.centralizer_le_normalizer _)

namespace OrbData

variable {Lb Tb A C F H₁ X₁ : Subgroup X} {p : ℕ} (d : OrbData Lb Tb A C F H₁ X₁ p)
include d

theorem C_le_T : C ≤ Tb := d.C_le.trans d.A_le

theorem mem_centralizer_of_ne {g : X} (hg : g ∈ C) (hg1 : g ≠ 1) {x : X} (hx : x ∈ conjSub g Lb) :
    x ∈ centralizer (Lb : Set X) := by
  have hgN : g ∉ normalizer (Lb : Set X) := fun h => by
    have : g ∈ C ⊓ normalizer (Lb : Set X) := ⟨hg, h⟩
    rw [d.C_inf, mem_bot] at this
    exact hg1 this
  rw [mem_centralizer_iff]
  intro y hy
  exact (d.lcomm g (d.C_le_T hg) hgN x hx y hy).symm

theorem commute_of_ne {i j : X} (hi : i ∈ C) (hj : j ∈ C) (hij : i ≠ j) {x y : X}
    (hx : x ∈ conjSub i Lb) (hy : y ∈ conjSub j Lb) : Commute x y := by
  have hg : j⁻¹ * i ∈ C := C.mul_mem (C.inv_mem hj) hi
  have hg1 : j⁻¹ * i ≠ 1 := fun h => hij (by rw [← inv_mul_eq_one.mp h])
  have hx' : j⁻¹ * x * j ∈ conjSub (j⁻¹ * i) Lb := by
    rw [mem_conjSub]
    have := mem_conjSub.1 hx
    rwa [show (j⁻¹ * i)⁻¹ * (j⁻¹ * x * j) * (j⁻¹ * i) = i⁻¹ * x * i by group]
  have h1 := mem_centralizer_iff.1 (d.mem_centralizer_of_ne hg hg1 hx') _ (mem_conjSub.1 hy)
  have h2 : j * ((j⁻¹ * y * j) * (j⁻¹ * x * j)) * j⁻¹ =
      j * ((j⁻¹ * x * j) * (j⁻¹ * y * j)) * j⁻¹ := by rw [h1]
  simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] at h2
  exact h2.symm

theorem pairwise {M : Subgroup X} (hM : M ≤ Lb) :
    Pairwise fun i j : C =>
      ∀ x y : X, x ∈ conjSub (i : X) M → y ∈ conjSub (j : X) M → Commute x y :=
  fun i j hij _ _ hx hy => d.commute_of_ne i.2 j.2 (fun h => hij (Subtype.ext h))
    (conjSub_mono _ hM hx) (conjSub_mono _ hM hy)

theorem permBy_of_mem_conjSub {k : X} (hk : k ∈ C) {g : X} (hg : g ∈ conjSub k Lb) {Nm : Subgroup X}
    (hNm : centralizer (Lb : Set X) ≤ Nm) (hgk : k⁻¹ * g * k ∈ Nm) : PermBy C Nm g := by
  intro j hj
  refine ⟨j, hj, j⁻¹ * g * j, ?_, by group⟩
  by_cases hjk : j = k
  · rwa [hjk]
  · refine hNm (d.mem_centralizer_of_ne (g := j⁻¹ * k) (C.mul_mem (C.inv_mem hj) hk)
      (fun h => hjk (by rw [← inv_mul_eq_one.mp h])) ?_)
    rw [mem_conjSub]
    have := mem_conjSub.1 hg
    rwa [show (j⁻¹ * k)⁻¹ * (j⁻¹ * g * j) * (j⁻¹ * k) = k⁻¹ * g * k by group]

theorem A1_le_normalizer_C : A ⊓ normalizer (Lb : Set X) ≤ normalizer (C : Set X) := by
  intro b hb
  rw [mem_normalizer_iff]
  intro c
  constructor
  · intro hc
    rwa [d.A_comm b hb.1 c (d.C_le hc), mul_inv_cancel_right]
  · intro hc
    have hcA : c ∈ A := by
      have := A.mul_mem (A.mul_mem (A.inv_mem hb.1) (d.C_le hc)) hb.1
      simpa [mul_assoc] using this
    rwa [d.A_comm b hb.1 c hcA, mul_inv_cancel_right] at hc

theorem permBy_A {a : X} (ha : a ∈ A) : PermBy C (A ⊓ normalizer (Lb : Set X)) a := by
  rw [← d.C_sup, ← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left C _
    d.A1_le_normalizer_C] at ha
  obtain ⟨c, hc, b, hb, rfl⟩ := Set.mem_mul.mp ha
  intro i hi
  refine ⟨c * i, C.mul_mem hc hi, b, hb, ?_⟩
  rw [mul_assoc, d.A_comm b hb.1 i (d.C_le hi), ← mul_assoc]

theorem permBy_F {f : X} (hf : f ∈ F) : PermBy C F f := by
  intro i hi
  refine ⟨i, hi, i⁻¹ * f * i, ?_, by group⟩
  have := (mem_normalizer_iff.mp (d.F_normal (Tb.inv_mem (d.C_le_T hi))) f).mp hf
  simpa using this

theorem normalizer_le_Z [Finite X] :
    normalizer (H₁ : Set X) ≤ normalizer ((pCoreOf 2 H₁ ⊔ X₁ : Subgroup X) : Set X) := by
  rw [← TwoPTwo.map_oTwoP_eq_sup d.irr.toTwoPTwo]
  have : (E1.oTwoP ↥H₁ p).Characteristic :=
    characteristic_iff_map_eq.mpr fun e => E1.oTwoP_map_mulEquiv e p
  exact CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _

theorem K_le_normalizer {M : Subgroup X} (hM : normalizer (H₁ : Set X) ≤ normalizer (M : Set X)) :
    orbK Tb A C F H₁ ≤ normalizer (orb C M : Set X) := by
  have hH : orb C H₁ ≤ normalizer (orb C M : Set X) := orb_le fun k hk =>
    le_normalizer_orb hM fun g hg => d.permBy_of_mem_conjSub hk (conjSub_mono _ d.H_le hg)
      (centralizer_le_normalizer_of_le d.H_le) (le_normalizer (mem_conjSub.1 hg))
  have hA : A ≤ normalizer (orb C M : Set X) :=
    le_normalizer_orb hM fun _ ha => (d.permBy_A ha).mono d.A1_norm
  have hF : F ≤ normalizer (orb C M : Set X) :=
    le_normalizer_orb hM fun _ hf => (d.permBy_F hf).mono d.F_norm
  exact sup_le hH (sup_le (sup_le ((orb_mono inf_le_left).trans hH) hA) hF)

theorem X_le_H : X₁ ≤ H₁ := d.irr.sylowP.le

theorem XB_le_K : orb C X₁ ≤ orbK Tb A C F H₁ := (orb_mono d.X_le_H).trans orb_le_orbK

theorem orb_T_le : orb C (H₁ ⊓ Tb) ≤ Tb :=
  orb_le fun _ hc => (conjSub_mono _ inf_le_right).trans (conjSub_eq_of_mem (d.C_le_T hc)).le

theorem S_le_T : orbS Tb A C F H₁ ≤ Tb := sup_le (sup_le d.orb_T_le d.A_le) d.F_le

theorem S_isPGroup : IsPGroup 2 (orbS Tb A C F H₁) := d.T2.to_le d.S_le_T

theorem R_le_T [Finite X] : orb C (pCoreOf 2 H₁) ≤ Tb :=
  (orb_mono (TwoPTwo.pCoreOf_le_sylowTwo d.irr.toTwoPTwo)).trans d.orb_T_le

theorem irr_conjSub (i : X) : TwoPTwoIrred (conjSub i H₁) (conjSub i (H₁ ⊓ Tb)) (conjSub i X₁) p :=
  (twoPTwoIrred_map_iff (MulAut.conj i).injective).2 d.irr

theorem XB_elem [Finite X] : IsElemAbelian p (orb C X₁) := by
  have : Fintype C := Fintype.ofFinite C
  classical
  exact isElemAbelian_iSup (d.pairwise (d.X_le_H.trans d.H_le)) fun i => d.elem.map _

end OrbData

end CFSG.LocalAnalysis.WeakClosure81.TC914
