module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnitTvRat

public section

namespace CFSG.StandardType.UnitTv

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly
  CFSG.StandardType.LineU CFSG.StandardType.UnitTB TableB

variable {K : Type} [Field K] {n d : ℕ} {L' : Type} [Group L'] {φ : ↥(unitarySU 2 n K d) →* L'}

theorem conj_apply_eq (α : MulAut L') (x : L') :
    MulAut.conj (α x) = α * MulAut.conj x * α⁻¹ := by
  refine MulEquiv.ext fun l => ?_
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]

theorem exists_perm_conj_comm [Finite K] (hM : Model φ) (hK : Nat.card K = (2 ^ n) ^ 2) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n + 1) (hd : 5 ≤ d) {A : Subgroup (MulAut L')}
    (hA : IsElemAbelian p A) (hsc : GGTorusSelfCent p A)
    (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, ActsDiagU φ a t) {α : MulAut L'}
    (hα : ∀ b, b ∈ A ↔ α * b * α⁻¹ ∈ A) (σ : Equiv.Perm (Fin d)) :
    ∃ π : Equiv.Perm (Fin d), ∀ a ∈ A,
      α * (MulAut.conj (φ (permSU hM.field σ)) * a *
          (MulAut.conj (φ (permSU hM.field σ)))⁻¹) * α⁻¹ =
        MulAut.conj (φ (permSU hM.field π)) * (α * a * α⁻¹) *
          (MulAut.conj (φ (permSU hM.field π)))⁻¹ := by
  classical
  have hd3 : 3 ≤ d := by omega
  have hAp : ∀ a ∈ A, a ^ p = 1 := hA.2
  obtain ⟨s, hs⟩ := hM.surj (α (φ (permSU hM.field σ)))
  have hαinv : ∀ b ∈ A, α⁻¹ * b * α ∈ A := by
    intro b hb
    refine (hα _).mpr ?_
    have e : α * (α⁻¹ * b * α) * α⁻¹ = b := by group
    rw [e]
    exact hb
  have hw : ∀ a ∈ A, MulAut.conj (φ s) * a * (MulAut.conj (φ s))⁻¹ ∈ A := by
    intro a ha
    rw [hs, conj_apply_eq]
    have h2 := conj_perm_mem hM hd3 hAp hsc hdiag σ (hαinv a ha)
    have h3 := (hα _).mp h2
    have e : α * MulAut.conj (φ (permSU hM.field σ)) * α⁻¹ * a *
        (α * MulAut.conj (φ (permSU hM.field σ)) * α⁻¹)⁻¹ =
        α * (MulAut.conj (φ (permSU hM.field σ)) * (α⁻¹ * a * α) *
          (MulAut.conj (φ (permSU hM.field σ)))⁻¹) * α⁻¹ := by group
    rw [e]
    exact h3
  obtain ⟨π, hπ⟩ := exists_monomial hM hK hp hp2 hpq hd hA hsc hdiag hw
  refine ⟨π⁻¹, fun a ha => ?_⟩
  obtain ⟨t, ht⟩ := hdiag _ ((hα a).mp ha)
  have h1 := actsDiagU_conj_elt ht s (hπ t)
  have h2 := ht.conj_perm hM.field π⁻¹
  simp only [inv_inv] at h2
  have heq := actsDiagU_unique hM.surj h1 h2
  have e1 : α * (MulAut.conj (φ (permSU hM.field σ)) * a *
      (MulAut.conj (φ (permSU hM.field σ)))⁻¹) * α⁻¹ =
      MulAut.conj (φ s) * (α * a * α⁻¹) * (MulAut.conj (φ s))⁻¹ := by
    rw [hs, conj_apply_eq]
    group
  rw [e1]
  exact heq

theorem not_transvection_of_model [Finite K] [Finite L'] (hM : Model φ)
    (hK : Nat.card K = (2 ^ n) ^ 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n + 1)
    (hd : 5 ≤ d) {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A) (hsc : GGTorusSelfCent p A)
    (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, ActsDiagU φ a t)
    (α : Subgroup.normalizer (A : Set (MulAut L'))) :
    ¬ GGIsTransvection p (A.normalizerMonoidHom α) := by
  intro hT
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (MulAut L') :=
    Finite.of_injective (fun f : MulAut L' => (f : L' → L')) DFunLike.coe_injective
  letI : CommGroup A :=
    { (inferInstance : Group A) with
      mul_comm := fun a b => Subtype.ext (IsElemAbelian.comm hA a.2 b.2) }
  obtain ⟨ζ, hζ⟩ := CFSG.RankThree.PartOne.KFU.exists_isPrimitiveRoot hM.field hp hpq
  have hd3 : 3 ≤ d := by omega
  have hAp : ∀ a ∈ A, a ^ p = 1 := hA.2
  choose tA htA using fun a : A => hdiag a a.2
  have hpow : ∀ (a : A) k l, ratU φ (a : MulAut L') k l ^ p = 1 := fun a k l =>
    ratU_pow hM hd3 (htA a) (hAp a a.2) k l
  let lamf : A → (Fin d → Fin d → ZMod p) := fun a k l => dlog p ζ (ratU φ (a : MulAut L') k l)
  have hmul : ∀ a b : A, lamf (a * b) = lamf a + lamf b := by
    intro a b
    funext k l
    simp only [lamf, Pi.add_apply]
    rw [Subgroup.coe_mul, ratU_mul hM hd3 (htA a) (htA b) k l,
      dlog_mul hζ (hpow a k l) (hpow b k l)]
  let lam : Additive A →+ (Fin d → Fin d → ZMod p) :=
    AddMonoidHom.mk' (fun a => lamf (Additive.toMul a)) fun a b => hmul _ _
  have hinj : Function.Injective lam := by
    intro a b hab
    have hab' : lamf (Additive.toMul a) = lamf (Additive.toMul b) := hab
    have h1 : ∀ k l, ratU φ ((Additive.toMul a : A) : MulAut L') k l =
        ratU φ ((Additive.toMul b : A) : MulAut L') k l := fun k l =>
      dlog_inj hζ (hpow _ k l) (hpow _ k l) (congrFun (congrFun hab' k) l)
    have h2 := eq_of_ratU_eq hM hd3 (htA (Additive.toMul a)) (htA (Additive.toMul b)) h1
    exact Additive.toMul.injective (Subtype.ext h2)
  have hcoc : ∀ a k l m, lam a k l + lam a l m = lam a k m := by
    intro a k l m
    show dlog p ζ (ratU φ _ k l) + dlog p ζ (ratU φ _ l m) = dlog p ζ (ratU φ _ k m)
    rw [← dlog_mul hζ (hpow _ k l) (hpow _ l m), ratU_coc hM hd3 (htA _) k l m]
  have hheart : ∀ i j : Fin d, ∃ h : A, ActsDiagU φ (h : MulAut L') (TypeA.ggPairVec i j ζ) :=
    fun i j => by
      obtain ⟨h, hh, hact⟩ := exists_heart hM hp hpq hsc hdiag hζ i j
      exact ⟨⟨h, hh⟩, hact⟩
  choose hA' hAct using hheart
  let m : Fin d → Fin d → Additive A := fun i j => Additive.ofMul (hA' i j)
  have hm : ∀ i j, lam (m i j) = pairCob p i j := by
    intro i j
    funext k l
    exact dlog_ratU_heart hM hd3 hp hζ i j (hAct i j) k l
  have hperm : ∀ (σ : Equiv.Perm (Fin d)) (a : A), MulAut.conj (φ (permSU hM.field σ)) *
      (a : MulAut L') * (MulAut.conj (φ (permSU hM.field σ)))⁻¹ ∈ A := fun σ a =>
    conj_perm_mem hM hd3 hAp hsc hdiag σ a.2
  let ρf : Equiv.Perm (Fin d) → A → A := fun σ a => ⟨_, hperm σ a⟩
  have hρmul : ∀ σ a b, ρf σ (a * b) = ρf σ a * ρf σ b := fun σ a b =>
    Subtype.ext (by simp only [ρf, Subgroup.coe_mul]; group)
  let ρ : Equiv.Perm (Fin d) → Additive A →+ Additive A := fun σ =>
    AddMonoidHom.mk' (fun a => Additive.ofMul (ρf σ (Additive.toMul a))) fun a b => by
      rw [toMul_add, hρmul, ofMul_mul]
  have hρ : ∀ σ a k l, lam (ρ σ a) k l = lam a (σ⁻¹ k) (σ⁻¹ l) := by
    intro σ a k l
    show dlog p ζ (ratU φ ((ρf σ (Additive.toMul a) : A) : MulAut L') k l) =
      dlog p ζ (ratU φ ((Additive.toMul a : A) : MulAut L') (σ⁻¹ k) (σ⁻¹ l))
    congr 1
    have h := (htA (Additive.toMul a)).conj_perm hM.field σ
    rw [ratU_eq hM hd3 h, ratU_eq hM hd3 (htA (Additive.toMul a))]
  let C : CobData p d (Additive A) := ⟨lam, hinj, hcoc, m, hm, ρ, hρ⟩
  let Tm : MulAut A := A.normalizerMonoidHom α
  let T : Additive A →+ Additive A := (MulEquiv.toAdditive Tm).toAddMonoidHom
  have hTapp : ∀ b : A, ((Tm b : A) : MulAut L') = (α : MulAut L') * b * (α : MulAut L')⁻¹ :=
    fun b => Subgroup.normalizerMonoidHom_apply_apply_coe A α b
  have hαN : ∀ b, b ∈ A ↔ (α : MulAut L') * b * (α : MulAut L')⁻¹ ∈ A := fun b =>
    Subgroup.mem_normalizer_iff.mp α.2 b
  have hTrel : ∀ σ : Equiv.Perm (Fin d), ∃ π : Equiv.Perm (Fin d),
      ∀ a : Additive A, T (C.ρ σ a) = C.ρ π (T a) := by
    intro σ
    obtain ⟨π, hπ⟩ := exists_perm_conj_comm hM hK hp hp2 hpq hd hA hsc hdiag hαN σ
    refine ⟨π, fun a => ?_⟩
    apply Additive.toMul.injective
    apply Subtype.ext
    show ((Tm (ρf σ (Additive.toMul a)) : A) : MulAut L') =
      MulAut.conj (φ (permSU hM.field π)) * ((Tm (Additive.toMul a) : A) : MulAut L') *
        (MulAut.conj (φ (permSU hM.field π)))⁻¹
    rw [hTapp, hTapp]
    exact hπ _ (Additive.toMul a).2
  have hfix : Nat.card {a : Additive A // T a = a} * p = Nat.card (Additive A) := by
    have e1 : Nat.card {a : Additive A // T a = a} = Nat.card {b : A // Tm b = b} :=
      Nat.card_congr (Equiv.subtypeEquiv Additive.toMul fun a => Iff.rfl)
    have e2 : Nat.card (Additive A) = Nat.card A := Nat.card_congr Additive.toMul
    rw [e1, e2]
    exact hT.1
  have hN : ∀ a : Additive A, T (T a - a) = T a - a := by
    intro a
    have h := hT.2 (Additive.toMul a)
    apply Additive.toMul.injective
    show Tm (Additive.toMul (T a - a)) = Additive.toMul (T a - a)
    have e1 : Additive.toMul (T a) = Tm (Additive.toMul a) := rfl
    rw [toMul_sub, e1, div_eq_mul_inv, mul_comm (Tm (Additive.toMul a)) (Additive.toMul a)⁻¹]
    exact h
  exact C.false_of_transvection hp2 T hTrel hd hfix hN

end CFSG.StandardType.UnitTv

end
