module

public import CFSG.Quasithin.Vol2.Ch11SecS12H
public import CFSG.Quasithin.Background.G25Eight
public import CFSG.Quasithin.Vol2.Ch11SecD557I

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.SL3Model CFSG.Quasithin.SL2Model
open CFSG.Quasithin.Vol2.Ch11
open CFSG.Assembly.LowTwoRank (StatedSL)
open CFSG.Quasithin.OperatorJH
open scoped MatrixGroups

variable {G : Type} [Group G]

section QFil

variable {F : Type} [Field F] {s : ℕ}

@[expose] def qT (s i : ℕ) : Subgroup (Multiplicative (Fin s → Fin 3 → F)) where
  carrier := {f | ∀ l : Fin s, Multiplicative.toAdd f l 0 = 0 ∧
    (i ≤ (l : ℕ) → Multiplicative.toAdd f l = 0)}
  one_mem' := fun _ => ⟨rfl, fun _ => rfl⟩
  mul_mem' := fun {f g} hf hg l => by
    refine ⟨?_, fun hl => ?_⟩
    · show Multiplicative.toAdd f l 0 + Multiplicative.toAdd g l 0 = 0
      rw [(hf l).1, (hg l).1, add_zero]
    · show Multiplicative.toAdd f l + Multiplicative.toAdd g l = 0
      rw [(hf l).2 hl, (hg l).2 hl, add_zero]
  inv_mem' := fun {f} hf l => by
    refine ⟨?_, fun hl => ?_⟩
    · show -Multiplicative.toAdd f l 0 = 0
      rw [(hf l).1, neg_zero]
    · show -Multiplicative.toAdd f l = 0
      rw [(hf l).2 hl, neg_zero]

@[expose] def coordPair (l : Fin s) :
    Multiplicative (Fin s → Fin 3 → F) →* Multiplicative (Fin 2 → F) where
  toFun f := Multiplicative.ofAdd ![Multiplicative.toAdd f l 2, Multiplicative.toAdd f l 1]
  map_one' := by
    apply Multiplicative.toAdd.injective
    ext j
    fin_cases j <;> rfl
  map_mul' a b := by
    apply Multiplicative.toAdd.injective
    ext j
    fin_cases j <;> rfl

theorem toAdd_coordPair (l : Fin s) (f : Multiplicative (Fin s → Fin 3 → F)) :
    Multiplicative.toAdd (coordPair l f) =
      ![Multiplicative.toAdd f l 2, Multiplicative.toAdd f l 1] := rfl

variable {S₃ : Subgroup G}

@[expose] def qFil (φ : ↥S₃ →* Multiplicative (Fin s → Fin 3 → F)) (i : ℕ) : Subgroup G :=
  ((qT s i).comap φ).map S₃.subtype

theorem mem_qFil {φ : ↥S₃ →* Multiplicative (Fin s → Fin 3 → F)} {i : ℕ} {y : G} :
    y ∈ qFil φ i ↔ ∃ hy : y ∈ S₃, ∀ l : Fin s, Multiplicative.toAdd (φ ⟨y, hy⟩) l 0 = 0 ∧
      (i ≤ (l : ℕ) → Multiplicative.toAdd (φ ⟨y, hy⟩) l = 0) := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z.2, hz⟩
  · rintro ⟨hy, h⟩
    exact ⟨⟨y, hy⟩, h, rfl⟩

theorem qFil_le (φ : ↥S₃ →* Multiplicative (Fin s → Fin 3 → F)) (i : ℕ) : qFil φ i ≤ S₃ :=
  Subgroup.map_subtype_le _

theorem qFil_mono (φ : ↥S₃ →* Multiplicative (Fin s → Fin 3 → F)) {i j : ℕ} (hij : i ≤ j) :
    qFil φ i ≤ qFil φ j := by
  intro y hy
  obtain ⟨hy, h⟩ := mem_qFil.1 hy
  exact mem_qFil.2 ⟨hy, fun l => ⟨(h l).1, fun hl => (h l).2 (hij.trans hl)⟩⟩

theorem qFil_zero {S₂ : Subgroup G} {φ : ↥S₃ →* Multiplicative (Fin s → Fin 3 → F)}
    (hker : ∀ y : ↥S₃, φ y = 1 ↔ (y : G) ∈ S₂) (hS₂ : S₂ ≤ S₃) : qFil φ 0 = S₂ := by
  ext y
  constructor
  · intro hy
    obtain ⟨hy, h⟩ := mem_qFil.1 hy
    exact (hker _).1 (Multiplicative.toAdd.injective (funext fun l => (h l).2 (Nat.zero_le _)))
  · intro hy
    refine mem_qFil.2 ⟨hS₂ hy, fun l => ?_⟩
    rw [(hker ⟨y, hS₂ hy⟩).2 hy]
    exact ⟨rfl, fun _ => rfl⟩

theorem dualHom_smul_zero {B : SL(3, F)} {μ : F} (hμ : μ ≠ 0) (hB : B • vE F 0 = μ • vE F 0)
    (f : Fin 3 → F) : (CFSG.Quasithin.dualHom F 3 B • f) 0 = μ⁻¹ * f 0 := by
  have h := dualHom_smul_dot B f (vE F 0)
  rw [hB, dotProduct_smul, smul_eq_mul] at h
  simp only [vE, dotProduct_single, mul_one] at h
  rw [← h, ← mul_assoc, inv_mul_cancel₀ hμ, one_mul]

theorem conj_mem_qFil {M S₂ : Subgroup G} {θ : ↥M →* SL(3, F)}
    {φ : ↥S₃ →* Multiplicative (Fin s → Fin 3 → F)}
    (hφ : IsSumOfSL3ModulesVia s M S₃ S₂ ((CFSG.Quasithin.dualHom F 3).comp θ) φ)
    {a : ↥M} (haS : (a : G) ∈ Subgroup.normalizer (S₃ : Set G)) {μ : F} (hμ : μ ≠ 0)
    (ha : θ a • vE F 0 = μ • vE F 0) {i : ℕ} {y : G} (hy : y ∈ qFil φ i) :
    (a : G) * y * (a : G)⁻¹ ∈ qFil φ i := by
  obtain ⟨hy, h⟩ := mem_qFil.1 hy
  have hy' : (a : G) * y * (a : G)⁻¹ ∈ S₃ := (Subgroup.mem_normalizer_iff.mp haS y).mp hy
  have e := hφ.2.2 a ⟨y, hy⟩ ⟨_, hy'⟩ rfl
  refine mem_qFil.2 ⟨hy', fun l => ?_⟩
  rw [e, toAdd_ofAdd]
  simp only [MonoidHom.comp_apply]
  refine ⟨?_, fun hl => ?_⟩
  · rw [dualHom_smul_zero hμ ha, (h l).1, mul_zero]
  · rw [(h l).2 hl, smul_zero]

theorem qFil_top_le {S₂ W A B : Subgroup G} {φ : ↥S₃ →* Multiplicative (Fin s → Fin 3 → F)}
    (hsurj : Function.Surjective φ) (hker : ∀ y : ↥S₃, φ y = 1 ↔ (y : G) ∈ S₂) (hS₂W : S₂ ≤ W)
    (hA : ∀ y : ↥S₃, (y : G) ∈ W ⊓ A ↔ ∀ l : Fin s,
      Multiplicative.toAdd (φ y) l ⬝ᵥ vE F 0 = 0 ∧ Multiplicative.toAdd (φ y) l ⬝ᵥ vE F 1 = 0)
    (hB : ∀ y : ↥S₃, (y : G) ∈ W ⊓ B ↔ ∀ l : Fin s,
      Multiplicative.toAdd (φ y) l ⬝ᵥ vE F 0 = 0 ∧ Multiplicative.toAdd (φ y) l ⬝ᵥ vE F 2 = 0) :
    qFil φ s ≤ W := by
  intro y hy
  obtain ⟨hyS, h⟩ := mem_qFil.1 hy
  set f := Multiplicative.toAdd (φ ⟨y, hyS⟩) with hf
  obtain ⟨ya, hya⟩ := hsurj (Multiplicative.ofAdd fun l => ![0, 0, f l 2])
  obtain ⟨yb, hyb⟩ := hsurj (Multiplicative.ofAdd fun l => ![0, f l 1, 0])
  have hyaW : (ya : G) ∈ W := ((hA ya).2 fun l => by rw [hya, toAdd_ofAdd]; simp [vE]).1
  have hybW : (yb : G) ∈ W := ((hB yb).2 fun l => by rw [hyb, toAdd_ofAdd]; simp [vE]).1
  have hrest : φ (⟨y, hyS⟩ * (ya * yb)⁻¹) = 1 := by
    rw [map_mul, map_inv, map_mul, hya, hyb, mul_inv_eq_one]
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_ofAdd, toAdd_ofAdd, ← hf]
    funext l j
    fin_cases j <;> simp [(h l).1]
  have hr := hS₂W ((hker _).1 hrest)
  have e : y = ((⟨y, hyS⟩ * (ya * yb)⁻¹ : ↥S₃) : G) * ((ya : G) * yb) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [e]
  exact W.mul_mem hr (W.mul_mem hyaW hybW)

end QFil

section Levi

variable [Finite G] {n : ℕ} {L K V V₁ S₃ S₂ : Subgroup G} {s : ℕ}

theorem natEig_qFil (D : NatData3 n L K V V₁) (hV₁V : V₁ ≤ V)
    {φ : ↥S₃ →* Multiplicative (Fin s → Fin 3 → GaloisField 2 n)}
    (hφ : IsSumOfSL3ModulesVia s L S₃ S₂ ((CFSG.Quasithin.dualHom _ 3).comp D.θ) φ)
    {i : ℕ} (hi : i < s) {x : G} (hxL : x ∈ L) {c : GaloisField 2 n}
    (hxc : ∀ w : Fin 3 → GaloisField 2 n, D.θ ⟨x, hxL⟩ • w = c • w) :
    IsNatEigSection (LOf L V₁) x (NatData3'.alpha0 D hV₁V) (qFil φ i) (qFil φ (i + 1)) c⁻¹ := by
  set i' : Fin s := ⟨i, hi⟩ with hi'
  refine ⟨(coordPair i').comp (φ.comp (Subgroup.inclusion (qFil_le φ (i + 1)))), fun y => ?_,
    fun z => ?_, fun k z z' hz' => ?_, fun z z' hz' => ?_⟩
  ·
    set v : Fin 3 → GaloisField 2 n := ![0, Multiplicative.toAdd y 1, Multiplicative.toAdd y 0]
    obtain ⟨z, hz⟩ := hφ.1 (Multiplicative.ofAdd (Pi.single i' v))
    have hzq : (z : G) ∈ qFil φ (i + 1) := by
      refine mem_qFil.2 ⟨z.2, fun l => ⟨?_, fun hl => ?_⟩⟩
      · have : φ ⟨(z : G), z.2⟩ = φ z := rfl
        rw [this, hz, toAdd_ofAdd]
        by_cases hl : l = i'
        · subst hl
          simp [v]
        · simp [Pi.single_eq_of_ne hl]
      · have hne : l ≠ i' := fun h => by
          rw [h] at hl
          exact absurd hl (by simp [i'])
        have : φ ⟨(z : G), z.2⟩ = φ z := rfl
        rw [this, hz, toAdd_ofAdd, Pi.single_eq_of_ne hne]
    refine ⟨⟨z, hzq⟩, Multiplicative.toAdd.injective ?_⟩
    have : φ (Subgroup.inclusion (qFil_le φ (i + 1)) ⟨z, hzq⟩) = φ z := rfl
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, this, toAdd_coordPair, hz, toAdd_ofAdd]
    ext j
    fin_cases j <;> simp [v]
  ·
    obtain ⟨hzS, hz⟩ := mem_qFil.1 z.2
    have e1 : φ (Subgroup.inclusion (qFil_le φ (i + 1)) z) = φ ⟨z, hzS⟩ := rfl
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, e1]
    constructor
    · intro h1
      have h1' := congrArg Multiplicative.toAdd h1
      rw [toAdd_coordPair, toAdd_one] at h1'
      have h2 : Multiplicative.toAdd (φ ⟨z, hzS⟩) i' 2 = 0 := congrFun h1' 0
      have h3 : Multiplicative.toAdd (φ ⟨z, hzS⟩) i' 1 = 0 := congrFun h1' 1
      refine mem_qFil.2 ⟨hzS, fun l => ⟨(hz l).1, fun hl => ?_⟩⟩
      by_cases hli : l = i'
      · subst hli
        funext j
        fin_cases j
        · exact (hz _).1
        · exact h3
        · exact h2
      · refine (hz l).2 ?_
        have : (l : ℕ) ≠ i := fun h => hli (Fin.ext h)
        omega
    · intro h1
      obtain ⟨hzS', hz'⟩ := mem_qFil.1 h1
      have h0 : Multiplicative.toAdd (φ ⟨z, hzS⟩) i' = 0 := (hz' i').2 le_rfl
      apply Multiplicative.toAdd.injective
      rw [toAdd_coordPair, toAdd_one, h0]
      ext j
      fin_cases j <;> rfl
  ·
    have hkL : (k : G) ∈ L := NatData3'.lOf_le k.2
    obtain ⟨hzS, hz⟩ := mem_qFil.1 z.2
    obtain ⟨hzS', -⟩ := mem_qFil.1 z'.2
    have e := hφ.2.2 ⟨k, hkL⟩ ⟨z, hzS⟩ ⟨z', hzS'⟩ hz'
    have e1 : φ (Subgroup.inclusion (qFil_le φ (i + 1)) z') = φ ⟨z', hzS'⟩ := rfl
    have e2 : φ (Subgroup.inclusion (qFil_le φ (i + 1)) z) = φ ⟨z, hzS⟩ := rfl
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.comp_apply,
      e1, e2, toAdd_coordPair, toAdd_coordPair, e, toAdd_ofAdd]
    simp only [MonoidHom.comp_apply]
    have hl := (levi_dual_smul (NatData3'.theta1 D hV₁V k)
      (Multiplicative.toAdd (φ ⟨z, hzS⟩) i') (hz i').1).2
    rw [NatData3'.theta1_coe] at hl
    have hk : (Subgroup.inclusion NatData3'.lOf_le k : ↥L) = ⟨k, hkL⟩ := rfl
    rw [hk] at hl
    rw [hl, NatData3'.alpha0_coe]
    rfl
  ·
    obtain ⟨hzS, -⟩ := mem_qFil.1 z.2
    obtain ⟨hzS', -⟩ := mem_qFil.1 z'.2
    have e := hφ.2.2 ⟨x, hxL⟩ ⟨z, hzS⟩ ⟨z', hzS'⟩ hz'
    have e1 : φ (Subgroup.inclusion (qFil_le φ (i + 1)) z') = φ ⟨z', hzS'⟩ := rfl
    have e2 : φ (Subgroup.inclusion (qFil_le φ (i + 1)) z) = φ ⟨z, hzS⟩ := rfl
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.comp_apply,
      e1, e2, toAdd_coordPair, toAdd_coordPair, e, toAdd_ofAdd]
    simp only [MonoidHom.comp_apply]
    rw [dualHom_smul_of_smul_eq hxc]
    ext j
    fin_cases j <;> simp

theorem comm_mem_qFil_top (D : NatData3 n L K V V₁) (hV₁V : V₁ ≤ V)
    {φ : ↥S₃ →* Multiplicative (Fin s → Fin 3 → GaloisField 2 n)}
    (hφ : IsSumOfSL3ModulesVia s L S₃ S₂ ((CFSG.Quasithin.dualHom _ 3).comp D.θ) φ)
    (hS₃ : LOf L V₁ ≤ Subgroup.normalizer (S₃ : Set G)) {k : G} (hk : k ∈ LOf L V₁) {y : G}
    (hy : y ∈ S₃) : k * y * k⁻¹ * y⁻¹ ∈ qFil φ s := by
  have hy' : k * y * k⁻¹ ∈ S₃ := (Subgroup.mem_normalizer_iff.mp (hS₃ hk) y).mp hy
  have hkL : k ∈ L := NatData3'.lOf_le hk
  have e := hφ.2.2 ⟨k, hkL⟩ ⟨y, hy⟩ ⟨_, hy'⟩ rfl
  have hfix : D.θ ⟨k, hkL⟩ • vE (GaloisField 2 n) 0 = (1 : GaloisField 2 n) • vE _ 0 := by
    rw [one_smul]
    exact NatData3'.theta_mem_stab0 D hV₁V ⟨k, hk⟩
  have hmem : k * y * k⁻¹ * y⁻¹ ∈ S₃ := S₃.mul_mem hy' (S₃.inv_mem hy)
  refine mem_qFil.2 ⟨hmem, fun l => ⟨?_, fun hl => absurd hl (not_le.mpr l.2)⟩⟩
  have e2 : φ ⟨k * y * k⁻¹ * y⁻¹, hmem⟩ = φ ⟨_, hy'⟩ * (φ ⟨y, hy⟩)⁻¹ := by
    rw [← map_inv, ← map_mul]
    rfl
  rw [e2, toAdd_mul, toAdd_inv, e, toAdd_ofAdd]
  simp only [Pi.add_apply, Pi.neg_apply, MonoidHom.comp_apply]
  rw [dualHom_smul_zero one_ne_zero hfix, inv_one, one_mul, add_neg_cancel]

end Levi

section Weyl

variable {n : ℕ} {L K V V₁ : Subgroup G}

theorem wS_inv_smul_e0 {F : Type} [Field F] [CharP F 2] {i : Fin 3} (h0i : (0 : Fin 3) ≠ i) :
    (CFSG.Quasithin.G1.wS F h0i)⁻¹ • vE F 0 = vE F i := by
  rw [inv_eq_of_mul_eq_one_right (CFSG.Quasithin.G1.wS_mul_self (F := F) h0i)]
  have := SecD.wS_smul_vE h0i (1 : F) 0
  rwa [one_smul, one_smul, Equiv.swap_apply_left] at this

theorem exists_weyl' (D : NatData3 n L K V V₁) (hV₁V : V₁ ≤ V) :
    ∃ (g : G) (hg : g ∈ L) (h : G) (hh : h ∈ L),
      D.θ ⟨g, hg⟩ = CFSG.Quasithin.G1.wS (GaloisField 2 n) (by decide : (0 : Fin 3) ≠ 1) ∧
      D.θ ⟨h, hh⟩ = CFSG.Quasithin.G1.wS (GaloisField 2 n) (by decide : (0 : Fin 3) ≠ 2) ∧
      V = V₁ ⊔ rconj V₁ g ⊔ rconj V₁ h := by
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  obtain ⟨x, hx⟩ := D.surj (CFSG.Quasithin.G1.wS (GaloisField 2 n) h01)
  obtain ⟨y, hy⟩ := D.surj (CFSG.Quasithin.G1.wS (GaloisField 2 n) h02)
  refine ⟨x, x.2, y, y.2, hx, hy, le_antisymm (fun v hv => ?_)
    (sup_le (sup_le hV₁V (SecD.rconj_le_of_natData D hV₁V x))
      (SecD.rconj_le_of_natData D hV₁V y))⟩
  set u := Multiplicative.toAdd (D.ψ ⟨v, hv⟩) with hu
  let w : Fin 3 → ↥V := fun i =>
    D.ψ.symm (Multiplicative.ofAdd (u i • vE (GaloisField 2 n) i))
  have hw : ∀ i, Multiplicative.toAdd (D.ψ (w i)) = u i • vE (GaloisField 2 n) i := fun i => by
    simp only [w, MulEquiv.apply_symm_apply, toAdd_ofAdd]
  have hv' : (⟨v, hv⟩ : ↥V) = w 0 * w 1 * w 2 := by
    apply D.ψ.injective
    apply Multiplicative.toAdd.injective
    rw [map_mul D.ψ, map_mul D.ψ, toAdd_mul, toAdd_mul, hw, hw, hw, ← hu]
    funext k
    fin_cases k <;> simp [vE]
  have hv'' : v = (w 0 : G) * (w 1 : G) * (w 2 : G) := congrArg Subtype.val hv'
  rw [hv'']
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left
    (Subgroup.mem_sup_left ?_)) (Subgroup.mem_sup_left (Subgroup.mem_sup_right ?_)))
    (Subgroup.mem_sup_right ?_)
  · exact (D.line (w 0)).mpr ⟨u 0, hw 0⟩
  · exact (SecD.mem_rconj_iff_of_swap D x h01 hx (w 1)).mpr ⟨u 1, hw 1⟩
  · exact (SecD.mem_rconj_iff_of_swap D y h02 hy (w 2)).mpr ⟨u 2, hw 2⟩

end Weyl

end CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12
