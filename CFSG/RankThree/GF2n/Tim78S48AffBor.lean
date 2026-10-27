module

public import CFSG.RankThree.GF2n.Tim78Lemma218
public import CFSG.Timmesfeld.RankOne.SL2
import CFSG.Timmesfeld.ARS.NaturalModule

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG.Timmesfeld.RankOne CFSG.Timmesfeld.ARS.NaturalModule
open scoped Matrix

namespace Bor

section Matrices

variable {F : Type*} [Field F]

theorem eq_upperElt_of_mulVec_eq {A : Matrix.SpecialLinearGroup (Fin 2) F}
    (h : (A : Matrix (Fin 2) (Fin 2) F) *ᵥ ![1, 0] = ![1, 0]) :
    ∃ ρ : F, A = upperElt F ρ := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have hdet := A.2
  rw [Matrix.det_fin_two] at hdet
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
  refine ⟨(A : Matrix (Fin 2) (Fin 2) F) 0 1, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_upperElt, h0, h1]
  rw [h1, h0] at hdet
  simpa using hdet

theorem diag_mul_diag {D : Matrix.SpecialLinearGroup (Fin 2) F}
    (hD : (D : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) :
    (D : Matrix (Fin 2) (Fin 2) F) 0 0 * (D : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
  have hdet := D.2
  rw [Matrix.det_fin_two, hD] at hdet
  simpa using hdet

theorem mul_upperElt_eq {D : Matrix.SpecialLinearGroup (Fin 2) F}
    (hD : (D : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) (ρ : F) :
    D * upperElt F ρ = upperElt F (((D : Matrix (Fin 2) (Fin 2) F) 0 0) ^ 2 * ρ) * D := by
  have hdd := diag_mul_diag hD
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, coe_upperElt, hD]
  linear_combination (-(((D : Matrix (Fin 2) (Fin 2) F) 0 0) * ρ)) * hdd

theorem commutator_upperElt {D : Matrix.SpecialLinearGroup (Fin 2) F}
    (hD : (D : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) (s : F) :
    upperElt F s * D * (upperElt F s)⁻¹ * D⁻¹ =
      upperElt F (s * (1 - ((D : Matrix (Fin 2) (Fin 2) F) 0 0) ^ 2)) := by
  have e : s * (1 - ((D : Matrix (Fin 2) (Fin 2) F) 0 0) ^ 2) +
      ((D : Matrix (Fin 2) (Fin 2) F) 0 0) ^ 2 * s = s := by ring
  have h1 : upperElt F s * D =
      upperElt F (s * (1 - ((D : Matrix (Fin 2) (Fin 2) F) 0 0) ^ 2)) * (D * upperElt F s) := by
    rw [mul_upperElt_eq hD, ← mul_assoc, upperElt_mul, e]
  rw [h1]
  group

theorem mul_self_eq_one_of_diag [CharP F 2] {A : Matrix.SpecialLinearGroup (Fin 2) F}
    (h10 : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0)
    (h00 : (A : Matrix (Fin 2) (Fin 2) F) 0 0 = 1) : A * A = 1 := by
  obtain ⟨ρ, hρ⟩ := eq_upperElt_of_mulVec_eq (A := A) (by
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h10, h00])
  rw [hρ, upperElt_mul_self]

theorem exists_diag_eq [Finite F] {H : Type*} [Group H]
    (θ : H →* Matrix.SpecialLinearGroup (Fin 2) F)
    (hlow : ∀ x, (θ x : Matrix (Fin 2) (Fin 2) F) 1 0 = 0)
    (hcard : Nat.card H = Nat.card F - 1)
    (hinj : ∀ x, (θ x : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 → x = 1) (μ : Fˣ) :
    ∃ x : H, (θ x : Matrix (Fin 2) (Fin 2) F) 0 0 = μ := by
  let a : H →* Fˣ := MonoidHom.mk'
    (fun x => Units.mk0 ((θ x : Matrix (Fin 2) (Fin 2) F) 0 0)
      (left_ne_zero_of_mul_eq_one (diag_mul_diag (hlow x)))) (by
    intro x y
    refine Units.ext ?_
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hlow y])
  have hainj : Function.Injective a := by
    rw [injective_iff_map_eq_one]
    intro x hx
    apply hinj
    simpa [a] using congrArg Units.val hx
  have hbij : Function.Bijective a :=
    hainj.bijective_of_nat_card_le (by rw [Nat.card_units, hcard])
  obtain ⟨x, hx⟩ := hbij.2 μ
  exact ⟨x, by simpa [a] using congrArg Units.val hx⟩

theorem mulVec_mulVec_inv (P : Matrix.SpecialLinearGroup (Fin 2) F) (v : Fin 2 → F) :
    (P : Matrix (Fin 2) (Fin 2) F) *ᵥ ((P⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) *ᵥ v = v := by
  rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]

theorem mulVec_inv_mulVec (P : Matrix.SpecialLinearGroup (Fin 2) F) (v : Fin 2 → F) :
    ((P⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ
      (P : Matrix (Fin 2) (Fin 2) F) *ᵥ v = v := by
  rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]

@[expose] def mulVecEquiv (P : Matrix.SpecialLinearGroup (Fin 2) F) :
    Multiplicative (Fin 2 → F) ≃* Multiplicative (Fin 2 → F) where
  toFun v := Multiplicative.ofAdd ((P : Matrix (Fin 2) (Fin 2) F) *ᵥ Multiplicative.toAdd v)
  invFun v := Multiplicative.ofAdd (((P⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) :
    Matrix (Fin 2) (Fin 2) F) *ᵥ Multiplicative.toAdd v)
  left_inv v := by simp only [toAdd_ofAdd, mulVec_inv_mulVec, ofAdd_toAdd]
  right_inv v := by simp only [toAdd_ofAdd, mulVec_mulVec_inv, ofAdd_toAdd]
  map_mul' v w := by simp only [toAdd_mul, Matrix.mulVec_add, ofAdd_add]

theorem toAdd_mulVecEquiv (P : Matrix.SpecialLinearGroup (Fin 2) F)
    (v : Multiplicative (Fin 2 → F)) :
    Multiplicative.toAdd (mulVecEquiv P v) =
      (P : Matrix (Fin 2) (Fin 2) F) *ᵥ Multiplicative.toAdd v := rfl

end Matrices

variable {G : Type} [Group G]

theorem exists_normalized {n : ℕ} {X W : Subgroup G} (h : InducesNaturalSL2 n X W)
    {b₀ : G} (hb₀W : b₀ ∈ W) (hb₀ : b₀ ≠ 1) :
    ∃ (φ : ↥X →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))
      (ψ : ↥W ≃* Multiplicative (Fin 2 → GaloisField 2 n)),
      Function.Surjective φ ∧ φ.ker = (Subgroup.centralizer (W : Set G)).subgroupOf X ∧
      (∀ (z : ↥X) (w w' : ↥W), (w' : G) = (z : G) * w * (z : G)⁻¹ →
        Multiplicative.toAdd (ψ w') =
          (φ z : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)) *ᵥ Multiplicative.toAdd (ψ w)) ∧
      Multiplicative.toAdd (ψ ⟨b₀, hb₀W⟩) = ![1, 0] := by
  obtain ⟨φ, ψ, hφs, hφk, hφψ⟩ := h
  have hv₀ : Multiplicative.toAdd (ψ ⟨b₀, hb₀W⟩) ≠ 0 := by
    intro h0
    apply hb₀
    have h1 : ψ ⟨b₀, hb₀W⟩ = ψ 1 := by
      rw [map_one]
      exact h0
    exact congrArg Subtype.val (ψ.injective h1)
  obtain ⟨P, hP⟩ := exists_mulVec_eq hv₀
  refine ⟨(MulAut.conj P⁻¹).toMonoidHom.comp φ, ψ.trans (mulVecEquiv P⁻¹), ?_, ?_, ?_, ?_⟩
  · exact (MulAut.conj P⁻¹).surjective.comp hφs
  · rw [← hφk]
    ext z
    simp [MonoidHom.mem_ker, conj_eq_one_iff]
  · intro z w w' hww
    have h1 := hφψ z w w' hww
    simp only [MulEquiv.trans_apply, toAdd_mulVecEquiv, h1, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, Matrix.SpecialLinearGroup.coe_mul,
      ← Matrix.mulVec_mulVec, mulVec_mulVec_inv]
  · simp only [MulEquiv.trans_apply, toAdd_mulVecEquiv, ← hP, mulVec_inv_mulVec]

end Bor

open Bor

variable {G : Type} [Group G]

theorem torus_conj_generates [Finite G] {n : ℕ} (hn : 2 ≤ n)
    {X W B K₁ E T : Subgroup G} (hnat : InducesNaturalSL2 n X W)
    (hBW : B ≤ W) (hB1 : B ≠ ⊥)
    (hTX : T ≤ X) (hTB : ∀ t ∈ T, ∀ b ∈ B, t * b = b * t)
    (hK₁X : K₁ ≤ X) (hK₁B : K₁ ≤ Subgroup.normalizer (B : Set G))
    (hK₁card : Nat.card K₁ = 2 ^ n - 1)
    (hK₁fpf : ∀ x ∈ K₁, x ≠ 1 → ∀ b ∈ B, x * b * x⁻¹ = b → b = 1)
    (hEX : E ≤ X) (hKE : X ⊓ Subgroup.centralizer (W : Set G) ≤ E) (hK₁E : K₁ ≤ E)
    {t₀ : G} (ht₀T : t₀ ∈ T) (ht₀ : ¬ ∀ w ∈ W, t₀ * w = w * t₀)
    (ht₀E : ∀ x ∈ K₁, t₀ * x * t₀⁻¹ ∈ E) :
    T ≤ E := by
  classical
  obtain ⟨b₀, hb₀B, hb₀1⟩ : ∃ b₀ ∈ B, b₀ ≠ 1 := by
    obtain ⟨b, hb⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hB1
    exact ⟨b, b.2, fun h => hb (Subtype.ext h)⟩
  obtain ⟨φ, ψ, -, hφk, hφψ, hψb₀⟩ := exists_normalized hnat (hBW hb₀B) hb₀1
  let V : G → (Fin 2 → GaloisField 2 n) :=
    fun g => if h : g ∈ W then Multiplicative.toAdd (ψ ⟨g, h⟩) else 0
  have hV : ∀ g (h : g ∈ W), V g = Multiplicative.toAdd (ψ ⟨g, h⟩) := fun g h => dif_pos h
  have hact : ∀ x (hx : x ∈ X) b, b ∈ W → x * b * x⁻¹ ∈ W →
      V (x * b * x⁻¹) = (φ ⟨x, hx⟩ : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)) *ᵥ V b := by
    intro x hx b hb hxb
    rw [hV _ hxb, hV _ hb]
    exact hφψ ⟨x, hx⟩ ⟨b, hb⟩ ⟨x * b * x⁻¹, hxb⟩ rfl
  have hVb₀ : V b₀ = ![1, 0] := by
    rw [hV _ (hBW hb₀B)]
    exact hψb₀
  have hconjT : ∀ t ∈ T, ∀ b ∈ B, t * b * t⁻¹ = b := by
    intro t ht b hb
    rw [hTB t ht b hb, mul_inv_cancel_right]
  have hTfix : ∀ t (ht : t ∈ T), ∃ ρ : GaloisField 2 n, φ ⟨t, hTX ht⟩ = upperElt _ ρ := by
    intro t ht
    refine eq_upperElt_of_mulVec_eq ?_
    have h := hact t (hTX ht) b₀ (hBW hb₀B) (by rw [hconjT t ht b₀ hb₀B]; exact hBW hb₀B)
    rw [hconjT t ht b₀ hb₀B, hVb₀] at h
    exact h.symm
  obtain ⟨s, hs⟩ := hTfix t₀ ht₀T
  have hs0 : s ≠ 0 := by
    rintro rfl
    apply ht₀
    have hmem : (⟨t₀, hTX ht₀T⟩ : X) ∈ φ.ker := by
      rw [MonoidHom.mem_ker, hs, upperElt_zero]
    rw [hφk, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at hmem
    intro w hw
    exact (hmem w hw).symm
  have hB2 : ∀ b ∈ B, V b 1 = 0 := by
    intro b hb
    have h := hact t₀ (hTX ht₀T) b (hBW hb) (by rw [hconjT t₀ ht₀T b hb]; exact hBW hb)
    rw [hconjT t₀ ht₀T b hb, hs, upperElt_mulVec] at h
    have h0 := congrFun h 0
    simp only [Matrix.cons_val_zero] at h0
    have h1 : s * V b 1 = 0 := by linear_combination (-1 : GaloisField 2 n) * h0
    exact (mul_eq_zero.mp h1).resolve_left hs0
  have hxb₀ : ∀ x ∈ K₁, x * b₀ * x⁻¹ ∈ B := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp (hK₁B hx) b₀).mp hb₀B
  let θ : ↥K₁ →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n) :=
    φ.comp (Subgroup.inclusion hK₁X)
  have hlow : ∀ x : K₁, (θ x : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)) 1 0 = 0 := by
    intro x
    have h := hact x (hK₁X x.2) b₀ (hBW hb₀B) (hBW (hxb₀ x x.2))
    rw [hVb₀] at h
    have h1 := congrFun h 1
    rw [hB2 _ (hxb₀ x x.2)] at h1
    change (φ ⟨x, hK₁X x.2⟩ : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)) 1 0 = 0
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h1.symm
  have hcardF : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  have hpow : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hinj : ∀ x : K₁, (θ x : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)) 0 0 = 1 → x = 1 := by
    intro x hx
    have hA := mul_self_eq_one_of_diag (hlow x) hx
    have hker : (⟨(x : G) * x, X.mul_mem (hK₁X x.2) (hK₁X x.2)⟩ : X) ∈ φ.ker := by
      rw [MonoidHom.mem_ker]
      have e : (⟨(x : G) * x, X.mul_mem (hK₁X x.2) (hK₁X x.2)⟩ : X) =
          ⟨x, hK₁X x.2⟩ * ⟨x, hK₁X x.2⟩ := rfl
      rw [e, map_mul]
      exact hA
    rw [hφk, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at hker
    have hxx : (x : G) * x = 1 := by
      by_contra hne
      refine hb₀1 (hK₁fpf ((x : G) * x) (K₁.mul_mem x.2 x.2) hne b₀ hb₀B ?_)
      have h1 : b₀ * ((x : G) * x) = ((x : G) * x) * b₀ := hker b₀ (hBW hb₀B)
      rw [← h1, mul_inv_cancel_right]
    have hx2 : x ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using hxx)
    have h1 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx2
    have h2 : orderOf x ∣ 2 ^ n - 1 := hK₁card ▸ orderOf_dvd_natCard x
    have hcop : Nat.Coprime 2 (2 ^ n - 1) := by
      rw [Nat.coprime_two_left, Nat.odd_iff]
      have : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
      omega
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
  have hdiag : ∀ μ : (GaloisField 2 n)ˣ,
      ∃ x : K₁, (θ x : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)) 0 0 = μ :=
    exists_diag_eq θ hlow (by rw [hK₁card, hcardF]) hinj
  obtain ⟨a₀, ha₀⟩ : ∃ a : (GaloisField 2 n)ˣ, a ≠ 1 := by
    have : 1 < Nat.card (GaloisField 2 n)ˣ := by
      rw [Nat.card_units, hcardF]
      omega
    haveI := Finite.one_lt_card_iff_nontrivial.mp this
    exact exists_ne 1
  obtain ⟨x₀, hx₀⟩ := hdiag a₀
  have he₀E : t₀ * x₀ * t₀⁻¹ * (x₀ : G)⁻¹ ∈ E :=
    E.mul_mem (ht₀E x₀ x₀.2) (E.inv_mem (hK₁E x₀.2))
  have hφe₀ : φ ⟨t₀ * x₀ * t₀⁻¹ * (x₀ : G)⁻¹, hEX he₀E⟩ =
      upperElt _ (s * (1 - ((a₀ : GaloisField 2 n)) ^ 2)) := by
    have e : (⟨t₀ * x₀ * t₀⁻¹ * (x₀ : G)⁻¹, hEX he₀E⟩ : X) =
        ⟨t₀, hTX ht₀T⟩ * ⟨x₀, hK₁X x₀.2⟩ * ⟨t₀, hTX ht₀T⟩⁻¹ * ⟨x₀, hK₁X x₀.2⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hs]
    have h := commutator_upperElt (hlow x₀) s
    rw [hx₀] at h
    exact h
  have hσ : s * (1 - ((a₀ : GaloisField 2 n)) ^ 2) ≠ 0 := by
    refine mul_ne_zero hs0 fun h => ha₀ ?_
    have h1 : ((a₀ : GaloisField 2 n)) ^ 2 = 1 := by linear_combination -h
    have h2 : ((2 : GaloisField 2 n)) = 0 := CharTwo.two_eq_zero
    have h3 : ((a₀ : GaloisField 2 n) - 1) ^ 2 = 0 := by
      linear_combination h1 + (1 - (a₀ : GaloisField 2 n)) * h2
    have h4 := sub_eq_zero.mp (pow_eq_zero_iff (two_ne_zero) |>.mp h3)
    exact Units.ext (by simpa using h4)
  have hconj : ∀ μ : (GaloisField 2 n)ˣ, ∃ e ∈ E, ∃ he : e ∈ X,
      φ ⟨e, he⟩ =
        upperElt _ ((μ : GaloisField 2 n) ^ 2 * (s * (1 - ((a₀ : GaloisField 2 n)) ^ 2))) := by
    intro μ
    obtain ⟨xμ, hxμ⟩ := hdiag μ
    have heE : (xμ : G) * (t₀ * x₀ * t₀⁻¹ * (x₀ : G)⁻¹) * (xμ : G)⁻¹ ∈ E :=
      E.mul_mem (E.mul_mem (hK₁E xμ.2) he₀E) (E.inv_mem (hK₁E xμ.2))
    refine ⟨_, heE, hEX heE, ?_⟩
    have e : (⟨(xμ : G) * (t₀ * x₀ * t₀⁻¹ * (x₀ : G)⁻¹) * (xμ : G)⁻¹, hEX heE⟩ : X) =
        ⟨xμ, hK₁X xμ.2⟩ * ⟨t₀ * x₀ * t₀⁻¹ * (x₀ : G)⁻¹, hEX he₀E⟩ * ⟨xμ, hK₁X xμ.2⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, hφe₀]
    have h := mul_upperElt_eq (hlow xμ) (s * (1 - ((a₀ : GaloisField 2 n)) ^ 2))
    rw [hxμ] at h
    change θ xμ * _ * (θ xμ)⁻¹ = _
    rw [h, mul_inv_cancel_right]
  have hsurj : ∀ ρ : GaloisField 2 n, ∃ e ∈ E, ∃ he : e ∈ X, φ ⟨e, he⟩ = upperElt _ ρ := by
    intro ρ
    by_cases hρ : ρ = 0
    · refine ⟨1, E.one_mem, X.one_mem, ?_⟩
      rw [hρ, upperElt_zero]
      exact map_one φ
    · obtain ⟨m, hm⟩ := isSquare_of_charTwo' (ρ / (s * (1 - ((a₀ : GaloisField 2 n)) ^ 2)))
      have hm0 : m ≠ 0 := by
        rintro rfl
        exact div_ne_zero hρ hσ (by simpa using hm)
      obtain ⟨e, heE, heX, he⟩ := hconj (Units.mk0 m hm0)
      refine ⟨e, heE, heX, ?_⟩
      rw [he]
      congr 1
      have h : ρ = m * m * (s * (1 - ((a₀ : GaloisField 2 n)) ^ 2)) := by
        rw [← hm]
        exact (div_mul_cancel₀ ρ hσ).symm
      rw [h]
      simp only [Units.val_mk0]
      ring
  intro t ht
  obtain ⟨ρ, hρ⟩ := hTfix t ht
  obtain ⟨e, heE, heX, he⟩ := hsurj ρ
  have hker : (⟨t, hTX ht⟩ : X) * ⟨e, heX⟩⁻¹ ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hρ, he, mul_inv_cancel]
  rw [hφk, Subgroup.mem_subgroupOf] at hker
  have hmem : t * e⁻¹ ∈ E := hKE ⟨X.mul_mem (hTX ht) (X.inv_mem heX), hker⟩
  simpa using E.mul_mem hmem heE

end CFSG.RankThree.GF2n.Tim78
