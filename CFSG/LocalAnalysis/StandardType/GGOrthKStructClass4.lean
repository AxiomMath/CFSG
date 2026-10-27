module

public import CFSG.LocalAnalysis.StandardType.GGOrthKStructDefs
public import CFSG.LocalAnalysis.StandardType.GGHalfTorusFrame
public import CFSG.LocalAnalysis.StandardType.GGSpJoinSignedPermGen
import CFSG.LocalAnalysis.StandardType.GGOrthKStructEquiv
import CFSG.LocalAnalysis.StandardType.GGOrthKStructClass4Comb

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.StandardType.GGHalf CFSG.StandardType.SpJoin
  CFSG.LieType.Universal.SpecialLinear Matrix

private theorem okC4_isConj_map_iff {M N : Type*} [Group M] [Group N]
    (e : M ≃* N) (a b : M) : IsConj (e a) (e b) ↔ IsConj a b := by
  rw [isConj_iff, isConj_iff]
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨e.symm g, ?_⟩
    apply e.injective
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact hg
  · rintro ⟨g, hg⟩
    refine ⟨e g, ?_⟩
    calc e g * e a * (e g)⁻¹ = e (g * a * g⁻¹) := by simp only [map_mul, map_inv]
      _ = e b := by rw [hg]

theorem ggOrthKStruct_class4 {G : Type} [Group G] [Finite G] {Bs K : Subgroup G} {n : ℕ}
    {ψ : SpecialLinearGroup (Fin (n + 1)) F2 →* G} {x : G}
    (hψ : GGHalfTorusFrame Bs K (halfTorus n) ψ) (hk : (n + 1) / 2 = 4)
    (hprod : Bs = (halfTorus n).map ψ ⊔ (Bs ⊓ Subgroup.centralizer (K : Set G)))
    (Φ : (Fin ((n + 1) / 2) → Multiplicative (ZMod 3)) ≃* ↥(halfTorus n)) (hΦ : IsTorusCoord n Φ)
    (hup : ∀ σ ∈ ggAutomizer K Bs, ∃ h ∈ spSignedGroup ((n + 1) / 2) 3, InducesSigned K ψ Φ σ h)
    (hlow : ∀ h ∈ spSignedGroup ((n + 1) / 2) 3, ∃ σ ∈ ggAutomizer K Bs, InducesSigned K ψ Φ σ h)
    (hx : x ∈ Bs) (a : Fin ((n + 1) / 2) → Multiplicative (ZMod 3)) (c : G)
    (hc : c ∈ Subgroup.centralizer (K : Set G)) (hxac : x = ψ (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) * c)
    (ha : ∀ j, a j ≠ 1) :
    ∀ φ : ↥(ggAutomizer K Bs), GGIsReflection 3 (φ : MulAut ↥Bs) →
      Nat.card {ψ : ↥(ggAutomizer K Bs) // IsConj φ ψ} = 4 → (φ : MulAut ↥Bs) ⟨x, hx⟩ ≠ ⟨x, hx⟩ := by
  subst x
  intro φ hφrefl hφcls
  obtain ⟨E, hE⟩ := ggOrthKStruct_equiv hψ hprod Φ hup hlow
  set h : ↥(spSignedGroup ((n + 1) / 2) 3) := E φ with hh
  have hInd : InducesSigned K ψ Φ (φ : MulAut ↥Bs)
      (h : Equiv.Perm (Fin ((n + 1) / 2) → Multiplicative (ZMod 3))) := hE φ
  obtain ⟨hh2, hfix⟩ := (ggOrthKStruct_isRefl_iff hψ hprod hInd).mp hφrefl
  have hcls : Nat.card {h' : ↥(spSignedGroup ((n + 1) / 2) 3) // IsConj h h'} = 4 := by
    rw [← hφcls]
    apply Nat.card_congr
    refine Equiv.subtypeEquiv E.symm.toEquiv ?_
    intro h'
    simpa [hh] using okC4_isConj_map_iff E φ (E.symm h')
  have hne := ggOrthKStruct_class4_comb hk h hh2 hfix hcls a ha
  intro heq
  have hval : (((φ : MulAut ↥Bs) ⟨ψ (Φ a) * c, hx⟩ : ↥Bs) : G) =
      ψ (Φ ((h : Equiv.Perm (Fin ((n + 1) / 2) → Multiplicative (ZMod 3))) a)) * c :=
    hInd a c hx hc
  have heq' : (((φ : MulAut ↥Bs) ⟨ψ (Φ a) * c, hx⟩ : ↥Bs) : G) = ψ (Φ a) * c := by
    simpa using congrArg Subtype.val heq
  have harg : ψ (Φ ((h : Equiv.Perm (Fin ((n + 1) / 2) → Multiplicative (ZMod 3))) a)) =
      ψ (Φ a) := by
    exact mul_right_cancel (hval.symm.trans heq')
  have hperm : (h : Equiv.Perm (Fin ((n + 1) / 2) → Multiplicative (ZMod 3))) a = a := by
    exact Φ.injective (Subtype.ext (hψ.inj harg))
  exact hne hperm

end CFSG.StandardType

end
