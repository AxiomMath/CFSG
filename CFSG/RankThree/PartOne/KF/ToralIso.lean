module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.PartOne.KF.UnitaryTorus

public section

namespace CFSG.RankThree.PartOne.KFU

variable {G : Type} [Group G] {p n : ℕ} {K : Type} [Field K]

theorem eq_image_torus_of_maximal {M : Subgroup (GL (Fin n) K)} {L F : Subgroup G}
    (ψ : ↥M ≃* ↥L) (hFL : F ≤ L)
    (hFψ : ∀ m : ↥M, (ψ m : G) ∈ F → (m : GL (Fin n) K) ∈ torusSU p n K)
    (hmax : ∀ F' : Subgroup G, F' ≤ L → (∀ x ∈ F', x ^ p = 1) →
      (∀ x ∈ F', ∀ y ∈ F', x * y = y * x) → F ≤ F' → F' = F) :
    ∀ m : ↥M, (ψ m : G) ∈ F ↔ (m : GL (Fin n) K) ∈ torusSU p n K := by
  intro m
  refine ⟨hFψ m, fun hm => ?_⟩
  let φ : ↥M →* G := L.subtype.comp ψ.toMonoidHom
  let T : Subgroup ↥M := (torusSU p n K).subgroupOf M
  let Fm : Subgroup G := T.map φ
  have hFm_le : Fm ≤ L := by
    rintro _ ⟨g, -, rfl⟩
    exact (ψ g).2
  have hdiag : ∀ g : ↥M, g ∈ T → ∃ d : Fin n → Kˣ, (∀ i, d i ^ p = 1) ∧
      ∏ i, d i = 1 ∧ diagU d = (g : GL (Fin n) K) := fun g hg => mem_torusSU_iff.mp hg
  have hFm_comm : ∀ x ∈ Fm, ∀ y ∈ Fm, x * y = y * x := by
    rintro _ ⟨g, hg, rfl⟩ _ ⟨g', hg', rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    obtain ⟨d, -, -, hd⟩ := hdiag g hg
    obtain ⟨d', -, -, hd'⟩ := hdiag g' hg'
    show (g : GL (Fin n) K) * g' = g' * g
    rw [← hd, ← hd', diagU_mul, diagU_mul, mul_comm]
  have hFm_exp : ∀ x ∈ Fm, x ^ p = 1 := by
    rintro _ ⟨g, hg, rfl⟩
    rw [← map_pow]
    have hgp : g ^ p = 1 := by
      apply Subtype.ext
      obtain ⟨d, hd1, -, hd⟩ := hdiag g hg
      rw [Subgroup.coe_pow, ← hd, diagU_pow, show d ^ p = 1 from funext hd1, diagU_one]
      rfl
    rw [hgp, map_one]
  have hFsub : F ≤ Fm := by
    intro x hx
    have hxL : x ∈ L := hFL hx
    have hg := hFψ (ψ.symm ⟨x, hxL⟩) (by rw [MulEquiv.apply_symm_apply]; exact hx)
    refine ⟨ψ.symm ⟨x, hxL⟩, hg, ?_⟩
    show ((ψ (ψ.symm ⟨x, hxL⟩) : ↥L) : G) = x
    rw [MulEquiv.apply_symm_apply]
  have hFm_eq : Fm = F := hmax Fm hFm_le hFm_exp hFm_comm hFsub
  have : (ψ m : G) ∈ Fm := ⟨m, hm, rfl⟩
  rwa [hFm_eq] at this

end CFSG.RankThree.PartOne.KFU
