module

public import CFSG.RankThree.PartTwo.Sec21.FF81FS79StdIso
public import CFSG.RankThree.PartTwo.Sec21.FF81FS79S6

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79 Equiv

variable {H : Type} [Group H] [Finite H]
variable {b t b₁ b₂ : H} {J : Subgroup H}

theorem J6.exists_pow_of_mem_Efin : ∀ e ∈ J6.Efin, ∃ i j : ℕ, e = J6.c₁ ^ i * J6.c₂ ^ j := by
  intro e he
  simp only [J6.Efin, Finset.mem_image, Finset.mem_univ, true_and] at he
  obtain ⟨⟨i, j⟩, rfl⟩ := he
  exact ⟨i.val, j.val, rfl⟩

theorem J6.c₁_mem_Efin : J6.c₁ ∈ J6.Efin := by decide +kernel

theorem J6.c₂_mem_Efin : J6.c₂ ∈ J6.Efin := by decide +kernel

theorem FS79Hyp.mem_B₁_iff_std (h : FS79Hyp b t b₁ b₂ J) (φ : ↥J ≃* J6.S6)
    (hφ₁ : φ ⟨b₁, h.b₁_mem⟩ = J6.c₁) (hφ₂ : φ ⟨b₂, h.b₂_mem⟩ = J6.c₂) (y : ↥J) :
    (y : H) ∈ Subgroup.closure ({b₁, b₂} : Set H) ↔ φ y ∈ J6.Efin := by
  classical
  set b₁' : ↥J := ⟨b₁, h.b₁_mem⟩ with hb₁'
  set b₂' : ↥J := ⟨b₂, h.b₂_mem⟩ with hb₂'
  set A : Subgroup ↥J := Subgroup.closure {b₁', b₂'} with hA
  have hAB : A.map J.subtype = Subgroup.closure ({b₁, b₂} : Set H) := by
    rw [hA, MonoidHom.map_closure]
    congr 1
    ext x
    simp [hb₁', hb₂']
  have hyA : (y : H) ∈ Subgroup.closure ({b₁, b₂} : Set H) ↔ y ∈ A := by
    rw [← hAB]
    constructor
    · rintro ⟨a, ha, hay⟩
      have : a = y := Subtype.ext hay
      rwa [← this]
    · intro hy
      exact ⟨y, hy, rfl⟩
  rw [hyA]
  constructor
  · intro hy
    have hle : A.map φ.toMonoidHom ≤ J6.E6 := by
      rw [Subgroup.map_le_iff_le_comap, hA, Subgroup.closure_le]
      intro z hz
      rcases hz with rfl | rfl
      · show φ b₁' ∈ J6.E6
        rw [hφ₁]
        exact J6.c₁_mem_Efin
      · show φ b₂' ∈ J6.E6
        rw [hφ₂]
        exact J6.c₂_mem_Efin
    exact hle ⟨y, hy, rfl⟩
  · intro hy
    obtain ⟨i, j, hij⟩ := J6.exists_pow_of_mem_Efin _ hy
    have : y = b₁' ^ i * b₂' ^ j := by
      apply φ.injective
      rw [map_mul, map_pow, map_pow, hφ₁, hφ₂, hij]
    rw [this]
    exact A.mul_mem (A.pow_mem (Subgroup.subset_closure (by simp)) _)
      (A.pow_mem (Subgroup.subset_closure (by simp)) _)

theorem FS79Hyp.normalizes_B₁_of_conj_line (h : FS79Hyp b t b₁ b₂ J) {x j : H}
    (hx : x ∈ Subgroup.closure ({b₁, b₂} : Set H)) (hx1 : x ≠ 1) (hj : j ∈ J)
    (hjx : j * x * j⁻¹ = x ∨ j * x * j⁻¹ = x⁻¹) :
    ∀ y ∈ Subgroup.closure ({b₁, b₂} : Set H),
      j * y * j⁻¹ ∈ Subgroup.closure ({b₁, b₂} : Set H) := by
  obtain ⟨φ, hφ₁, hφ₂⟩ := h.exists_std
  have hB₁J : Subgroup.closure ({b₁, b₂} : Set H) ≤ J := by
    rw [Subgroup.closure_le]
    intro z hz
    rcases hz with rfl | rfl
    · exact h.b₁_mem
    · exact h.b₂_mem
  have hxJ : x ∈ J := hB₁J hx
  have hxE : φ ⟨x, hxJ⟩ ∈ J6.Efin := (h.mem_B₁_iff_std φ hφ₁ hφ₂ ⟨x, hxJ⟩).mp hx
  have hx1' : φ ⟨x, hxJ⟩ ≠ 1 := by
    intro h1
    apply hx1
    have : (⟨x, hxJ⟩ : ↥J) = 1 := φ.injective (by rw [h1, map_one])
    exact congrArg Subtype.val this
  have hconj : φ ⟨j, hj⟩ * φ ⟨x, hxJ⟩ * (φ ⟨j, hj⟩)⁻¹ = φ ⟨x, hxJ⟩ ∨
      φ ⟨j, hj⟩ * φ ⟨x, hxJ⟩ * (φ ⟨j, hj⟩)⁻¹ = (φ ⟨x, hxJ⟩)⁻¹ := by
    rcases hjx with h1 | h1
    · left
      have : (⟨j, hj⟩ : ↥J) * ⟨x, hxJ⟩ * (⟨j, hj⟩ : ↥J)⁻¹ = ⟨x, hxJ⟩ :=
        Subtype.ext (by simpa using h1)
      rw [← map_mul, ← map_inv, ← map_mul, this]
    · right
      have : (⟨j, hj⟩ : ↥J) * ⟨x, hxJ⟩ * (⟨j, hj⟩ : ↥J)⁻¹ = (⟨x, hxJ⟩ : ↥J)⁻¹ :=
        Subtype.ext (by simpa using h1)
      rw [← map_mul, ← map_inv, ← map_mul, this, map_inv]
  intro y hy
  have hyJ : y ∈ J := hB₁J hy
  have hyE : φ ⟨y, hyJ⟩ ∈ J6.Efin := (h.mem_B₁_iff_std φ hφ₁ hφ₂ ⟨y, hyJ⟩).mp hy
  have hnorm := J6.normalizes_Efin_of_conj_line _ hxE hx1' (φ ⟨j, hj⟩) hconj _ hyE
  have hjyJ : j * y * j⁻¹ ∈ J := J.mul_mem (J.mul_mem hj hyJ) (J.inv_mem hj)
  have := (h.mem_B₁_iff_std φ hφ₁ hφ₂ ⟨j * y * j⁻¹, hjyJ⟩).mpr (by
    have e : (⟨j * y * j⁻¹, hjyJ⟩ : ↥J) = ⟨j, hj⟩ * ⟨y, hyJ⟩ * (⟨j, hj⟩ : ↥J)⁻¹ := by
      apply Subtype.ext
      simp
    rw [e, map_mul, map_mul, map_inv]
    exact hnorm)
  exact this

theorem FS79Hyp.mem_B₁_of_cen (h : FS79Hyp b t b₁ b₂ J) {j : H} (hj : j ∈ J)
    (h₁ : j * b₁ = b₁ * j) (h₂ : j * b₂ = b₂ * j) :
    j ∈ Subgroup.closure ({b₁, b₂} : Set H) := by
  obtain ⟨φ, hφ₁, hφ₂⟩ := h.exists_std
  have e₁ : φ ⟨j, hj⟩ * J6.c₁ = J6.c₁ * φ ⟨j, hj⟩ := by
    rw [← hφ₁, ← map_mul, ← map_mul]
    exact congrArg φ (Subtype.ext (by simpa using h₁))
  have e₂ : φ ⟨j, hj⟩ * J6.c₂ = J6.c₂ * φ ⟨j, hj⟩ := by
    rw [← hφ₂, ← map_mul, ← map_mul]
    exact congrArg φ (Subtype.ext (by simpa using h₂))
  exact (h.mem_B₁_iff_std φ hφ₁ hφ₂ ⟨j, hj⟩).mpr (J6.mem_Efin_of_cen _ e₁ e₂)

end CFSG.RankThree.PartTwo.Sec21.FF81
