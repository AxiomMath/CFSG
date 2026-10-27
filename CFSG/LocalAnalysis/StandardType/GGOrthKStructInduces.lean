module

public import CFSG.LocalAnalysis.StandardType.GGOrthKStructDefs
public import CFSG.LocalAnalysis.StandardType.GGHalfTorusFrame

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.StandardType.GGHalf
  CFSG.LieType.Universal.SpecialLinear Matrix

theorem ggOrthKStruct_induces_one {G : Type} [Group G] {Bs : Subgroup G} (K : Subgroup G) {n : ℕ}
    (ψ : SpecialLinearGroup (Fin (n + 1)) F2 →* G)
    (Φ : (Fin ((n + 1) / 2) → Multiplicative (ZMod 3)) ≃* ↥(halfTorus n)) :
    InducesSigned K ψ Φ (1 : MulAut ↥Bs) 1 := by
  unfold InducesSigned
  intro a c hb hc
  simp

theorem ggOrthKStruct_induces_mul {G : Type} [Group G] {Bs K : Subgroup G} {n : ℕ}
    {ψ : SpecialLinearGroup (Fin (n + 1)) F2 →* G}
    {Φ : (Fin ((n + 1) / 2) → Multiplicative (ZMod 3)) ≃* ↥(halfTorus n)}
    {σ τ : MulAut ↥Bs} {h h' : Equiv.Perm (Fin ((n + 1) / 2) → Multiplicative (ZMod 3))}
    (hσ : InducesSigned K ψ Φ σ h) (hτ : InducesSigned K ψ Φ τ h') :
    InducesSigned K ψ Φ (σ * τ) (h * h') := by
  unfold InducesSigned at hσ hτ
  unfold InducesSigned
  intro a c hb hc
  have hτa := hτ a c hb hc
  have hb' : ψ (Φ (h' a) : SpecialLinearGroup (Fin (n + 1)) F2) * c ∈ Bs := by
    rw [← hτa]
    exact (τ ⟨ψ (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) * c, hb⟩).2
  have hτeq : τ ⟨ψ (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) * c, hb⟩ =
      ⟨ψ (Φ (h' a) : SpecialLinearGroup (Fin (n + 1)) F2) * c, hb'⟩ :=
    Subtype.ext hτa
  have hσa := hσ (h' a) c hb' hc
  calc (((σ * τ) ⟨ψ (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) * c, hb⟩ : ↥Bs) : G)
      = ((σ (τ ⟨ψ (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) * c, hb⟩) : ↥Bs) : G) := by
        rw [MulAut.mul_apply]
    _ = ((σ ⟨ψ (Φ (h' a) : SpecialLinearGroup (Fin (n + 1)) F2) * c, hb'⟩ : ↥Bs) : G) := by
          rw [hτeq]
    _ = ψ (Φ ((h * h') a) : SpecialLinearGroup (Fin (n + 1)) F2) * c := by
          rw [hσa, Equiv.Perm.mul_apply]

theorem ggOrthKStruct_induces_inv {G : Type} [Group G] {Bs K : Subgroup G} {n : ℕ}
    {ψ : SpecialLinearGroup (Fin (n + 1)) F2 →* G}
    (hψ : GGHalfTorusFrame Bs K (halfTorus n) ψ)
    {Φ : (Fin ((n + 1) / 2) → Multiplicative (ZMod 3)) ≃* ↥(halfTorus n)}
    {σ : MulAut ↥Bs} {h : Equiv.Perm (Fin ((n + 1) / 2) → Multiplicative (ZMod 3))}
    (hσ : InducesSigned K ψ Φ σ h) :
    InducesSigned K ψ Φ σ⁻¹ h⁻¹ := by
  unfold InducesSigned at hσ
  unfold InducesSigned
  intro a c hb hc
  let a' : Fin ((n + 1) / 2) → Multiplicative (ZMod 3) := h⁻¹ a
  have ha' : h a' = a := by
    change h (h⁻¹ a) = a
    exact Equiv.apply_symm_apply h a
  have hψa : ψ (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) ∈ Bs :=
    hψ.torus_le (Subgroup.mem_map_of_mem ψ (Φ a).2)
  have hcBs : c ∈ Bs := by
    have h : (ψ (Φ a : SpecialLinearGroup (Fin (n + 1)) F2))⁻¹ *
        (ψ (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) * c) ∈ Bs :=
      Bs.mul_mem (Bs.inv_mem hψa) hb
    simpa only [inv_mul_cancel_left] using h
  have hψa' : ψ (Φ a' : SpecialLinearGroup (Fin (n + 1)) F2) ∈ Bs :=
    hψ.torus_le (Subgroup.mem_map_of_mem ψ (Φ a').2)
  have hb' : ψ (Φ a' : SpecialLinearGroup (Fin (n + 1)) F2) * c ∈ Bs :=
    Bs.mul_mem hψa' hcBs
  have hσa := hσ a' c hb' hc
  have heq : σ ⟨ψ (Φ a' : SpecialLinearGroup (Fin (n + 1)) F2) * c, hb'⟩ =
      ⟨ψ (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) * c, hb⟩ := by
    apply Subtype.ext
    rw [hσa, ha']
  have hgoal : σ⁻¹ ⟨ψ (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) * c, hb⟩ =
      ⟨ψ (Φ a' : SpecialLinearGroup (Fin (n + 1)) F2) * c, hb'⟩ := by
    rw [← heq, ← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
  calc (((σ⁻¹) ⟨ψ (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) * c, hb⟩ : ↥Bs) : G)
      = ((⟨ψ (Φ a' : SpecialLinearGroup (Fin (n + 1)) F2) * c, hb'⟩ : ↥Bs) : G) := by
        rw [hgoal]
    _ = ψ (Φ (h⁻¹ a) : SpecialLinearGroup (Fin (n + 1)) F2) * c := rfl

theorem ggOrthKStruct_induces_unique {G : Type} [Group G] {Bs K : Subgroup G} {n : ℕ}
    {ψ : SpecialLinearGroup (Fin (n + 1)) F2 →* G}
    (hψ : GGHalfTorusFrame Bs K (halfTorus n) ψ)
    {Φ : (Fin ((n + 1) / 2) → Multiplicative (ZMod 3)) ≃* ↥(halfTorus n)}
    {σ : MulAut ↥Bs} {h h' : Equiv.Perm (Fin ((n + 1) / 2) → Multiplicative (ZMod 3))}
    (hσ : InducesSigned K ψ Φ σ h) (hσ' : InducesSigned K ψ Φ σ h') : h = h' := by
  unfold InducesSigned at hσ hσ'
  apply Equiv.ext
  intro a
  have hb : ψ (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) * 1 ∈ Bs := by
    simpa using hψ.torus_le (Subgroup.mem_map_of_mem ψ (Φ a).2)
  have h1 := hσ a 1 hb (Subgroup.one_mem (Subgroup.centralizer (K : Set G)))
  have h2 := hσ' a 1 hb (Subgroup.one_mem (Subgroup.centralizer (K : Set G)))
  have heq : ψ (Φ (h a) : SpecialLinearGroup (Fin (n + 1)) F2) =
      ψ (Φ (h' a) : SpecialLinearGroup (Fin (n + 1)) F2) := by
    calc ψ (Φ (h a) : SpecialLinearGroup (Fin (n + 1)) F2)
        = ψ (Φ (h a) : SpecialLinearGroup (Fin (n + 1)) F2) * 1 := (mul_one _).symm
      _ = ((σ ⟨ψ (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) * 1, hb⟩ : ↥Bs) : G) := h1.symm
      _ = ψ (Φ (h' a) : SpecialLinearGroup (Fin (n + 1)) F2) * 1 := h2
      _ = ψ (Φ (h' a) : SpecialLinearGroup (Fin (n + 1)) F2) := mul_one _
  exact Φ.injective (Subtype.val_injective (hψ.inj heq))

end CFSG.StandardType

end
