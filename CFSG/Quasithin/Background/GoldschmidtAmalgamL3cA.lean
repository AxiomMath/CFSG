module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3Sz
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3Weak
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3cRot

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmL3
  CFSG.Quasithin.F6.GoldAmL2T

namespace F6

namespace GoldAmL3c

variable {D : Type*} [Group D] {A B : Subgroup D} {z : D} {V : Subgroup D}

theorem conj_mem_pCoreOf_left {h : D} (hh : h ∈ A) {q : D} (hq : q ∈ pCoreOf 2 A) :
    h * q * h⁻¹ ∈ pCoreOf 2 A :=
  (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 A hh) q).mp hq

section YFacts

variable [Finite D] {x a a₁ a₂ : D} (g : Gen3 A B z V x a a₁ a₂)

include g

omit [Finite D] in
theorem Gen3.conj_mem_V {h : D} (hh : h ∈ A) {w : D} (hw : w ∈ V) : h * w * h⁻¹ ∈ V :=
  (Subgroup.mem_normalizer_iff.mp (g.hyp.natural.reduced.2.1 hh) w).mp hw

omit [Finite D] in
theorem Gen3.conj_mem_V_iff {h : D} (hh : h ∈ A) {w : D} : h * w * h⁻¹ ∈ V ↔ w ∈ V :=
  (Subgroup.mem_normalizer_iff.mp (g.hyp.natural.reduced.2.1 hh) w).symm

theorem Gen3.V_comm_QA {v q : D} (hv : v ∈ V) (hq : q ∈ pCoreOf 2 A) : v * q = q * v :=
  Subgroup.mem_centralizer_iff.mp (g.hyp.pCoreOf_left_le_centralizer hq) v hv

omit [Finite D] in
theorem Gen3.V_sq {v : D} (hv : v ∈ V) : v * v = 1 := by
  have := g.hyp.abelian.2 v (le_conjClosure V B hv)
  rwa [pow_two] at this

theorem Gen3.mem_U_of_comm_QA (hU : Nat.card (conjClosure V B) = 8)
    (hT : Nat.card ↥(A ⊓ B) = 64) {q : D} (hq : q ∈ pCoreOf 2 A)
    (hc : ∀ u ∈ conjClosure V B, u * q = q * u) : q ∈ conjClosure V B := by
  have h1 := g.hyp.mem_coreIn_of_comm hq hc
  rw [← g.hyp.pCoreOf_inf_centralizer_eq_coreIn] at h1
  exact (g.U_eq_K hU hT).ge h1

theorem Gen3.conj_ne_of_ne_one {y : D} (hyA : y ∈ A) (hy3 : orderOf y = 3) {v : D} (hv : v ∈ V)
    (hv1 : v ≠ 1) : y * v * y⁻¹ ≠ v := by
  intro hfix
  obtain ⟨c, hcA, hcv⟩ := exists_conj_eq_of_mem g.hyp.gold g.hyp.natural hv hv1
  have hw : (c⁻¹ * y * c) * z = z * (c⁻¹ * y * c) := by
    have h1 : y * (c * z * c⁻¹) * y⁻¹ = c * z * c⁻¹ := by rw [hcv]; exact hfix
    calc (c⁻¹ * y * c) * z = c⁻¹ * (y * (c * z * c⁻¹) * y⁻¹) * y * c := by group
      _ = c⁻¹ * (c * z * c⁻¹) * y * c := by rw [h1]
      _ = z * (c⁻¹ * y * c) := by group
  have hwA : c⁻¹ * y * c ∈ A := A.mul_mem (A.mul_mem (A.inv_mem hcA) hyA) hcA
  have hwT := inf_normalizer_zpowers_le g.hyp.gold g.hyp.natural
    ⟨hwA, mem_normalizer_zpowers_of_mul_comm hw⟩
  have hord : orderOf (c⁻¹ * y * c) = 3 := by
    have e : c⁻¹ * y * c = (MulAut.conj c⁻¹).toMonoidHom y := by simp
    rw [e, ← hy3]
    exact orderOf_injective _ (MulAut.conj c⁻¹).injective y
  exact g.hyp.gold.vertex_left.not_mem_of_orderOf hord hwT

theorem Gen3.orbit_prod {y : D} (hyA : y ∈ A) (hy3 : orderOf y = 3) {v : D} (hv : v ∈ V) :
    v * (y * v * y⁻¹) * (y * (y * v * y⁻¹) * y⁻¹) = 1 := by
  have hcube : y * y * y = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hy3, pow_three'] at this
  obtain ⟨v₁, hv₁e⟩ : ∃ v₁, v₁ = y * v * y⁻¹ := ⟨_, rfl⟩
  obtain ⟨v₂, hv₂e⟩ : ∃ v₂, v₂ = y * v₁ * y⁻¹ := ⟨_, rfl⟩
  rw [← hv₁e, ← hv₂e]
  have hv₁ : v₁ ∈ V := by rw [hv₁e]; exact g.conj_mem_V hyA hv
  have hv₂ : v₂ ∈ V := by rw [hv₂e]; exact g.conj_mem_V hyA hv₁
  have e3 : y * v₂ * y⁻¹ = v := by
    rw [hv₂e, hv₁e]
    calc y * (y * (y * v * y⁻¹) * y⁻¹) * y⁻¹ = (y * y * y) * v * (y * y * y)⁻¹ := by group
      _ = v := by rw [hcube]; group
  have hN : v * v₁ * v₂ ∈ V := V.mul_mem (V.mul_mem hv hv₁) hv₂
  by_contra hne
  refine g.conj_ne_of_ne_one hyA hy3 hN hne ?_
  have hcomm : v₁ * v₂ * v = v * v₁ * v₂ := by
    have := g.U_comm (le_conjClosure V B hv) (le_conjClosure V B (V.mul_mem hv₁ hv₂))
    calc v₁ * v₂ * v = (v₁ * v₂) * v := rfl
      _ = v * (v₁ * v₂) := this.symm
      _ = v * v₁ * v₂ := by group
  calc y * (v * v₁ * v₂) * y⁻¹ = (y * v * y⁻¹) * (y * v₁ * y⁻¹) * (y * v₂ * y⁻¹) := by group
    _ = v₁ * v₂ * v := by rw [← hv₁e, ← hv₂e, e3]
    _ = v * v₁ * v₂ := hcomm

end YFacts

section Conj

variable [Finite D] {x a a₁ a₂ : D} (g : Gen3 A B z V x a a₁ a₂)

include g

theorem Gen3.conj_cases {y : D} (hyA : y ∈ A) (hy3 : orderOf y = 3) {h : D} (hh : h ∈ A) :
    conjSub h (conjClosure V B) = conjClosure V B ∨
    conjSub h (conjClosure V B) = conjSub y (conjClosure V B) ∨
    conjSub h (conjClosure V B) = conjSub (y * y) (conjClosure V B) := by
  have hyT := g.hyp.gold.vertex_left.not_mem_of_orderOf hy3
  have hy2T := g.hyp.gold.vertex_left.sq_not_mem_of_orderOf hy3
  have hTU : ∀ t ∈ A ⊓ B, conjSub t (conjClosure V B) = conjClosure V B := fun t ht =>
    conjSub_eq_of_mem_normalizer (le_normalizer_conjClosure V B ht.2)
  rcases coset_decomp g.hyp.gold.relIndex_left hyA hyT hy2T hh with
    ht | ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
  · exact Or.inl (hTU h ht)
  · right; left; rw [conjSub_mul, hTU t ht]
  · right; right; rw [conjSub_mul, hTU t ht]

theorem Gen3.conjSub_ne {y : D} (hyA : y ∈ A) (hy3 : orderOf y = 3) :
    conjSub y (conjClosure V B) ≠ conjClosure V B := fun hEq =>
  g.hyp.not_mem_normalizer_conjClosure hyA hy3 (mem_normalizer_of_conjSub_eq hEq)

theorem Gen3.conj_elem (hU : Nat.card (conjClosure V B) = 8) {h : D} (hh : h ∈ A) {w : D}
    (hw : w ∈ conjSub h (conjClosure V B)) (hwV : w ∉ V) :
    ∃ v ∈ V, w = (h * a₁ * h⁻¹) * v := by
  have hw' : h⁻¹ * w * h ∈ conjClosure V B := mem_conjSub.mp hw
  have hwV' : h⁻¹ * w * h ∉ V := by
    intro hmem
    apply hwV
    have := g.conj_mem_V hh hmem
    have e : h * (h⁻¹ * w * h) * h⁻¹ = w := by group
    rwa [e] at this
  rcases g.mem_U_cases hU hw' with hmem | ⟨v, hv, hveq⟩
  · exact absurd hmem hwV'
  · refine ⟨h * v * h⁻¹, g.conj_mem_V hh hv, ?_⟩
    have e1 : w = (h * v * h⁻¹) * (h * a₁ * h⁻¹) := by
      calc w = h * (h⁻¹ * w * h) * h⁻¹ := by group
        _ = h * (v * a₁) * h⁻¹ := by rw [hveq]
        _ = (h * v * h⁻¹) * (h * a₁ * h⁻¹) := by group
    have hea : h * a₁ * h⁻¹ ∈ pCoreOf 2 A :=
      conj_mem_pCoreOf_left hh (g.hyp.conjClosure_le_pCoreOf_left g.a₁_mem_U)
    rw [e1]
    exact g.V_comm_QA (g.conj_mem_V hh hv) hea

end Conj

end GoldAmL3c

end F6

end CFSG.Quasithin
