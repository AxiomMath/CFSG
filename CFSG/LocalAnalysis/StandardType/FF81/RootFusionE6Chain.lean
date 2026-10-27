module

public import CFSG.LocalAnalysis.StandardType.FF81.Defs

import CFSG.ClassicalInvolution.Generic.LineModelLinear

public section

namespace CFSG.StandardType.FF81

private theorem exists_conj_mem_of_mem_of_linearBlockStandardPair {X : Type} [Group X]
    {W U V : Subgroup X}
    (h : CFSG.ClassicalInvolution.WeakCT.LinearBlockStandardPair (ZMod 2) W U V) {x : X} (hx : x ∈ V) :
    ∃ y ∈ U ⊔ V, y * x * y⁻¹ ∈ U := by
  obtain ⟨θ, c, -, -, h1 | h1⟩ := h
  · obtain ⟨hU, hV⟩ := h1
    let ψ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) →* X :=
      θ.comp (MulAut.conj c⁻¹).toMonoidHom
    have hU' : (CFSG.ClassicalInvolution.WeakCT.B12 (ZMod 2)).map ψ = U := by
      rw [← hU, Subgroup.map_map]
    have hV' : (CFSG.ClassicalInvolution.WeakCT.B23 (ZMod 2)).map ψ = V := by
      rw [← hV, Subgroup.map_map]
    rw [← hV'] at hx
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hx
    set m : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
      (CFSG.ClassicalInvolution.Generic.om23)⁻¹ * CFSG.ClassicalInvolution.Generic.om12 with hm
    have hconjm : CFSG.ClassicalInvolution.Generic.conjSub m
        (CFSG.ClassicalInvolution.WeakCT.B23 (ZMod 2)) =
        CFSG.ClassicalInvolution.WeakCT.B12 (ZMod 2) := by
      rw [hm, CFSG.ClassicalInvolution.Generic.conjSub_mul,
        CFSG.ClassicalInvolution.Generic.conjSub_om12_B23,
        CFSG.ClassicalInvolution.Generic.conjSub_inv_conjSub]
    have hk' : m * k * m⁻¹ ∈ CFSG.ClassicalInvolution.WeakCT.B12 (ZMod 2) := by
      have hmem := CFSG.ClassicalInvolution.Generic.conj_mem_conjSub (n := m) hk
      rwa [hconjm] at hmem
    refine ⟨ψ m, ?_, ?_⟩
    · have h23 : ψ (CFSG.ClassicalInvolution.Generic.om23)⁻¹ ∈ V := by
        rw [← hV']
        exact Subgroup.mem_map_of_mem ψ
          ((CFSG.ClassicalInvolution.WeakCT.B23 (ZMod 2)).inv_mem
            CFSG.ClassicalInvolution.Generic.om23_mem)
      have h12 : ψ CFSG.ClassicalInvolution.Generic.om12 ∈ U := by
        rw [← hU']
        exact Subgroup.mem_map_of_mem ψ CFSG.ClassicalInvolution.Generic.om12_mem
      have hmul : ψ m = ψ (CFSG.ClassicalInvolution.Generic.om23)⁻¹ *
          ψ CFSG.ClassicalInvolution.Generic.om12 := by
        rw [hm, map_mul]
      rw [hmul]
      exact Subgroup.mul_mem (H := U ⊔ V)
        (Subgroup.mem_sup_right h23) (Subgroup.mem_sup_left h12)
    · have hconj : ψ m * ψ k * (ψ m)⁻¹ = ψ (m * k * m⁻¹) := by
        simp only [map_mul, map_inv, mul_assoc]
      rw [hconj, ← hU']
      exact Subgroup.mem_map_of_mem ψ hk'
  · obtain ⟨hU, hV⟩ := h1
    let ψ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) →* X :=
      θ.comp (MulAut.conj c⁻¹).toMonoidHom
    have hU' : (CFSG.ClassicalInvolution.WeakCT.B12 (ZMod 2)).map ψ = V := by
      rw [← hU, Subgroup.map_map]
    have hV' : (CFSG.ClassicalInvolution.WeakCT.B23 (ZMod 2)).map ψ = U := by
      rw [← hV, Subgroup.map_map]
    rw [← hU'] at hx
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hx
    set m : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
      (CFSG.ClassicalInvolution.Generic.om12)⁻¹ * CFSG.ClassicalInvolution.Generic.om23 with hm
    have hconjm : CFSG.ClassicalInvolution.Generic.conjSub m
        (CFSG.ClassicalInvolution.WeakCT.B12 (ZMod 2)) =
        CFSG.ClassicalInvolution.WeakCT.B23 (ZMod 2) := by
      rw [hm, CFSG.ClassicalInvolution.Generic.conjSub_mul,
        ← CFSG.ClassicalInvolution.Generic.conjSub_om12_B23,
        CFSG.ClassicalInvolution.Generic.conjSub_inv_conjSub]
    have hk' : m * k * m⁻¹ ∈ CFSG.ClassicalInvolution.WeakCT.B23 (ZMod 2) := by
      have hmem := CFSG.ClassicalInvolution.Generic.conj_mem_conjSub (n := m) hk
      rwa [hconjm] at hmem
    refine ⟨ψ m, ?_, ?_⟩
    · have h12 : ψ (CFSG.ClassicalInvolution.Generic.om12)⁻¹ ∈ V := by
        rw [← hU']
        exact Subgroup.mem_map_of_mem ψ
          ((CFSG.ClassicalInvolution.WeakCT.B12 (ZMod 2)).inv_mem
            CFSG.ClassicalInvolution.Generic.om12_mem)
      have h23 : ψ CFSG.ClassicalInvolution.Generic.om23 ∈ U := by
        rw [← hV']
        exact Subgroup.mem_map_of_mem ψ CFSG.ClassicalInvolution.Generic.om23_mem
      have hmul : ψ m = ψ (CFSG.ClassicalInvolution.Generic.om12)⁻¹ *
          ψ CFSG.ClassicalInvolution.Generic.om23 := by
        rw [hm, map_mul]
      rw [hmul]
      exact Subgroup.mul_mem (H := U ⊔ V)
        (Subgroup.mem_sup_right h12) (Subgroup.mem_sup_left h23)
    · have hconj : ψ m * ψ k * (ψ m)⁻¹ = ψ (m * k * m⁻¹) := by
        simp only [map_mul, map_inv, mul_assoc]
      rw [hconj, ← hV']
      exact Subgroup.mem_map_of_mem ψ hk'

theorem exists_conj_eq_of_mem_frame {G : Type} [Group G] [Finite G] {n : ℕ} {b : G}
    {L : Subgroup G} {K : ℕ → Subgroup G} {t : G} (hF : FrameSystem n b L K t)
    (hb : orderOf b = 3) (hn : 3 ≤ n) {x : G} (hx : x ∈ K 2) (hx3 : orderOf x = 3) :
    ∃ y ∈ K 0 ⊔ K 1 ⊔ K 2, y * x * y⁻¹ = b := by
  have h01 : adjA (⟨0, by omega⟩ : Fin n) (⟨1, by omega⟩ : Fin n) := by simp [adjA]
  have h12 : adjA (⟨1, by omega⟩ : Fin n) (⟨2, by omega⟩ : Fin n) := by simp [adjA]
  obtain ⟨W01, hW01⟩ := hF.sysL'.2.2.2 _ _ h01
  obtain ⟨W12, hW12⟩ := hF.sysL'.2.2.2 _ _ h12
  have hW01' : CFSG.ClassicalInvolution.WeakCT.LinearBlockStandardPair (ZMod 2) W01 (K 0) (K 1) :=
    by simpa using hW01
  have hW12' : CFSG.ClassicalInvolution.WeakCT.LinearBlockStandardPair (ZMod 2) W12 (K 1) (K 2) :=
    by simpa using hW12
  obtain ⟨y₁, hy₁, hy₁x⟩ := exists_conj_mem_of_mem_of_linearBlockStandardPair hW12' hx
  obtain ⟨y₀, hy₀, hy₀x⟩ := exists_conj_mem_of_mem_of_linearBlockStandardPair hW01' hy₁x
  set x₀ : G := y₀ * (y₁ * x * y₁⁻¹) * y₀⁻¹ with hx₀def
  have hx₀K0 : x₀ ∈ K 0 := hy₀x
  have hx₀3 : orderOf x₀ = 3 := by
    have hconjord : ∀ (u a : G), orderOf (u * a * u⁻¹) = orderOf a := by
      intro u a
      have h := orderOf_injective (MulAut.conj u).toMonoidHom (MulAut.conj u).injective a
      simpa [MulAut.conj_apply] using h
    rw [hx₀def, hconjord y₀ (y₁ * x * y₁⁻¹), hconjord y₁ x, hx3]
  have hconj : (y₀ * y₁) * x * (y₀ * y₁)⁻¹ = x₀ := by
    rw [hx₀def, mul_inv_rev]
    group
  have hy : y₀ * y₁ ∈ K 0 ⊔ K 1 ⊔ K 2 := by
    have h1 : y₁ ∈ (K 0 ⊔ K 1) ⊔ K 2 := by
      have hle : K 1 ⊔ K 2 ≤ (K 0 ⊔ K 1) ⊔ K 2 := by
        refine sup_le ?_ ?_
        · exact le_sup_right.trans le_sup_left
        · exact le_sup_right
      exact hle hy₁
    exact Subgroup.mul_mem (H := (K 0 ⊔ K 1) ⊔ K 2)
      (Subgroup.mem_sup_left hy₀) h1
  have hbK0 : b ∈ K 0 := by
    rw [hF.K0]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers b)
  obtain ⟨e⟩ := hF.sysL'.1 (⟨0, by omega⟩ : Fin n)
  have hkeyMat : ∀ A : Matrix (Fin 2) (Fin 2) (ZMod 2),
      A.det = 1 → A ^ 3 = 1 → A ≠ 1 →
      A = !![(0 : ZMod 2), 1; 1, 1] ∨ A = !![(1 : ZMod 2), 1; 1, 0] := by
    decide
  let a : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) :=
    ⟨!![(0 : ZMod 2), 1; 1, 1], by rw [Matrix.det_fin_two_of]; decide⟩
  have hkey : ∀ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2),
      g ^ 3 = 1 → g ≠ 1 → g = a ∨ g = a⁻¹ := by
    intro g hg3 hg1
    have hmat3 : (g : Matrix (Fin 2) (Fin 2) (ZMod 2)) ^ 3 = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_pow, hg3, Matrix.SpecialLinearGroup.coe_one]
    have hmat1 : (g : Matrix (Fin 2) (Fin 2) (ZMod 2)) ≠ 1 := by
      intro h
      exact hg1 (Subtype.ext h)
    rcases hkeyMat (g : Matrix (Fin 2) (Fin 2) (ZMod 2)) g.2 hmat3 hmat1 with h | h
    · left
      apply Subtype.ext
      rw [h]
    · right
      have hmul : a * g = 1 := by
        apply Subtype.ext
        rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, h]
        decide
      exact eq_inv_of_mul_eq_one_right hmul
  have hkeyK0 : ∀ g : ↥(K 0), orderOf g = 3 → g = e a ∨ g = (e a)⁻¹ := by
    intro g hg
    have hg' : orderOf (e.symm g) = 3 := by
      rw [MulEquiv.orderOf_eq, hg]
    have h3 : (e.symm g) ^ 3 = 1 := by
      rw [← hg']
      exact pow_orderOf_eq_one _
    have hne : (e.symm g) ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hg'
      omega
    rcases hkey (e.symm g) h3 hne with h | h
    · left
      rw [← e.apply_symm_apply g, h]
    · right
      rw [← e.apply_symm_apply g, h, map_inv]
  have hbA := hkeyK0 ⟨b, hbK0⟩ (by simpa using hb)
  have hxA := hkeyK0 ⟨x₀, hx₀K0⟩ (by simpa using hx₀3)
  have hx₀ : x₀ = b ∨ x₀ = b⁻¹ := by
    have hcases : (⟨x₀, hx₀K0⟩ : ↥(K 0)) = ⟨b, hbK0⟩ ∨
        (⟨x₀, hx₀K0⟩ : ↥(K 0)) = (⟨b, hbK0⟩ : ↥(K 0))⁻¹ := by
      rcases hbA with hbA | hbA <;> rcases hxA with hxA | hxA
      · left
        rw [hxA, hbA]
      · right
        rw [hxA, hbA]
      · right
        rw [hxA, hbA, inv_inv]
      · left
        rw [hxA, hbA]
    rcases hcases with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (by simpa using congrArg Subtype.val h)
  rcases hx₀ with rfl | hx₀
  · exact ⟨y₀ * y₁, hy, hconj⟩
  · refine ⟨t * (y₀ * y₁), ?_, ?_⟩
    · have ht : t ∈ K 0 := by
        rw [hF.K0]
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
      exact Subgroup.mul_mem (H := (K 0 ⊔ K 1) ⊔ K 2)
        (Subgroup.mem_sup_left (Subgroup.mem_sup_left ht)) hy
    · have htb : t * b⁻¹ * t⁻¹ = b := by
        have h : (t * b * t⁻¹)⁻¹ = b := by rw [hF.inv_b, inv_inv]
        calc t * b⁻¹ * t⁻¹ = (t * b * t⁻¹)⁻¹ := by group
          _ = b := h
      calc
        (t * (y₀ * y₁)) * x * (t * (y₀ * y₁))⁻¹
            = t * ((y₀ * y₁) * x * (y₀ * y₁)⁻¹) * t⁻¹ := by group
        _ = t * b⁻¹ * t⁻¹ := by rw [hconj, hx₀]
        _ = b := htb

end CFSG.StandardType.FF81

end
