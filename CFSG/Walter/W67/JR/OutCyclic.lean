module

public import CFSG.Walter.W67.JR.OutRigid
public import CFSG.Walter.W67.JR.OutPSL

public section

namespace CFSG.Walter.W67

open scoped MatrixGroups
open CFSG.ComponentClassification.OuterAutomorphisms

namespace JROut

@[expose] noncomputable def restrictHom {G : Type*} [Group G] (K : Subgroup G)
    (A : Subgroup (MulAut G)) (hA : ∀ β ∈ A, ∀ x ∈ K, β x ∈ K) : A →* MulAut K where
  toFun β :=
    { toFun := fun x => ⟨(β : MulAut G) x, hA β β.2 x x.2⟩
      invFun := fun x => ⟨(β : MulAut G)⁻¹ x, hA _ (A.inv_mem β.2) x x.2⟩
      left_inv := fun x => Subtype.ext (MulAut.inv_apply_self _ _ _)
      right_inv := fun x => Subtype.ext (MulAut.apply_inv_self _ _ _)
      map_mul' := fun x y => Subtype.ext (map_mul (β : MulAut G) (x : G) (y : G)) }
  map_one' := by
    ext x
    rfl
  map_mul' β γ := by
    ext x
    rfl

theorem restrictHom_apply {G : Type*} [Group G] (K : Subgroup G) (A : Subgroup (MulAut G))
    (hA : ∀ β ∈ A, ∀ x ∈ K, β x ∈ K) (β : A) (x : K) :
    ((restrictHom K A hA β x : K) : G) = (β : MulAut G) x := rfl

theorem conj_mul_eq {G : Type*} [Group G] (φ : MulAut G) (g : G) :
    MulAut.conj g * φ = φ * MulAut.conj (φ⁻¹ g) := by
  ext x
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]

end JROut

open JROut in
theorem outCyclic_of_R :
    S_outCyclic_of_R := by
  intro L _ _ hL hq hJT
  classical
  obtain ⟨hfodd, -⟩ := hL.odd_f hJT hq
  have hcyc : IsCyclic (Outer hL.K) :=
    isCyclic_outer_of_equiv hL.iso hL.odd_p hfodd (by change 3 < hL.q; omega)
  let A : Subgroup (MulAut L) := MulAction.stabilizer (MulAut L) hL.J
  have hAJ : ∀ β ∈ A, β hL.J = hL.J := fun β hβ => MulAction.mem_stabilizer_iff.mp hβ
  have hA : ∀ β ∈ A, ∀ x ∈ hL.K, β x ∈ hL.K := fun β hβ x hx =>
    hL.mem_K_of_apply_J hq β (hAJ β hβ) hx
  let ψ : A →* Outer hL.K := (QuotientGroup.mk' (inner hL.K)).comp (restrictHom hL.K A hA)
  obtain ⟨⟨_, ⟨α, rfl⟩⟩, hgen⟩ := IsCyclic.exists_generator (α := ψ.range)
  refine ⟨α, fun β => ?_⟩
  have hl := JT.lemma_2_1 (hL.toJTHyp hq) hL.p_ne_two
  have hβJ : orderOf (β hL.J) = 2 := by rw [MulEquiv.orderOf_eq]; exact hL.orderOf_J
  obtain ⟨c, hc⟩ := isConj_iff.mp (hl.2.2.1 hL.J (β hL.J) hL.orderOf_J hβJ)
  set β' := (MulAut.conj c)⁻¹ * β with hβ'
  have hβ'A : β' ∈ A := by
    rw [MulAction.mem_stabilizer_iff, MulAut.smul_def, hβ', MulAut.mul_apply, ← hc,
      MulAut.conj_inv_apply]
    group
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hgen ⟨ψ ⟨β', hβ'A⟩, ⟨β', hβ'A⟩, rfl⟩)
  have hk' : ψ (α ^ k) = ψ ⟨β', hβ'A⟩ := by
    have := congrArg Subtype.val hk
    rw [map_zpow]
    simpa using this
  set δ : A := (α ^ k)⁻¹ * ⟨β', hβ'A⟩ with hδ
  have hδ1 : ψ δ = 1 := by rw [hδ, map_mul, map_inv, hk', inv_mul_cancel]
  have hδin : restrictHom hL.K A hA δ ∈ inner hL.K := (QuotientGroup.eq_one_iff _).mp hδ1
  obtain ⟨y, hy⟩ := hδin
  have hδK : ∀ x ∈ hL.K, (δ : MulAut L) x = y * x * (y : L)⁻¹ := by
    intro x hx
    have := congrArg (fun φ : MulAut hL.K => ((φ ⟨x, hx⟩ : hL.K) : L)) hy
    simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at this
    rw [restrictHom_apply] at this
    exact this.symm
  have hδJ : (δ : MulAut L) hL.J = hL.J := hAJ _ δ.2
  set δ' : MulAut L := (MulAut.conj (y : L))⁻¹ * δ with hδ'
  have hδ'J : δ' hL.J = hL.J := by
    rw [hδ', MulAut.mul_apply, hδJ, MulAut.conj_inv_apply]
    have hyJ : (y : L) * hL.J = hL.J * y := hL.commute_J_of_mem_K y.2
    rw [mul_assoc, ← hyJ, ← mul_assoc, inv_mul_cancel, one_mul]
  have hδ'K : ∀ x ∈ hL.K, δ' x = x := by
    intro x hx
    rw [hδ', MulAut.mul_apply, hδK x hx, MulAut.conj_inv_apply]
    group
  obtain ⟨c', hc'⟩ : ∃ c' : L, (δ : MulAut L) = MulAut.conj c' := by
    have hδδ' : (δ : MulAut L) = MulAut.conj (y : L) * δ' := by rw [hδ', mul_inv_cancel_left]
    rcases hL.eq_one_or_eq_conj_J hJT hq δ' hδ'J hδ'K with h1 | h1
    · exact ⟨y, by rw [hδδ', h1, mul_one]⟩
    · exact ⟨y * hL.J, by rw [hδδ', h1, map_mul]⟩
  have hβ'eq : β' = (α : MulAut L) ^ k * MulAut.conj c' := by
    rw [← hc', hδ]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow]
    group
  have hββ' : β = MulAut.conj c * β' := by rw [hβ', mul_inv_cancel_left]
  refine ⟨k, ((α : MulAut L) ^ k)⁻¹ c * c', ?_⟩
  rw [hββ', hβ'eq, ← mul_assoc, conj_mul_eq, mul_assoc, ← map_mul]

end CFSG.Walter.W67
