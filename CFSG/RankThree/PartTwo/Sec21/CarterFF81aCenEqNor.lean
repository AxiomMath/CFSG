module

public import CFSG.RankThree.PartTwo.Sec21.CarterFF81aNorMono

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79

variable {G : Type} [Group G] [Finite G] {b : G} {L : Subgroup G}

theorem FF81Hyp.cen_tau_iff_nor_line (h : FF81Hyp b L)
    (hTF : KF_Sp6TorusFree) (hOut : KF_Sp62Out)
    {τ b₁ b₂ b₃ : G} (hτL : τ ∈ L) (hb₁ : b₁ ∈ L) (hb₂ : b₂ ∈ L) (hb₃ : b₃ ∈ L)
    (hE : IsElemAb 3 3 (Subgroup.closure ({b₁, b₂, b₃} : Set G)))
    (hself : L ⊓ CenS (Subgroup.closure ({b₁, b₂, b₃} : Set G)) =
      Subgroup.closure ({b₁, b₂, b₃} : Set G))
    (hmono : ∀ n ∈ L, n ∈ Nor (Subgroup.closure ({b₁, b₂, b₃} : Set G)) →
      ∀ x ∈ ({b₁, b₂, b₃} : Set G),
        n * x * n⁻¹ ∈ ({b₁, b₁⁻¹, b₂, b₂⁻¹, b₃, b₃⁻¹} : Set G))
    (hrk : ∀ E : Subgroup G, E ≤ L → (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) →
      (∀ x ∈ E, x ^ 3 = 1) → Nat.card E ≤ 27)
    (hτ2o : orderOf τ = 2) (hb : τ * b * τ⁻¹ = b)
    (hinv : τ * b₁ * τ⁻¹ = b₁⁻¹ ∧ τ * b₂ * τ⁻¹ = b₂⁻¹ ∧ τ * b₃ * τ⁻¹ = b₃⁻¹)
    (hbB : b ∈ Subgroup.closure ({b, b₁, b₂, b₃} : Set G))
    (hb₁B : b₁ ∈ Subgroup.closure ({b, b₁, b₂, b₃} : Set G))
    (hb₂B : b₂ ∈ Subgroup.closure ({b, b₁, b₂, b₃} : Set G))
    (hb₃B : b₃ ∈ Subgroup.closure ({b, b₁, b₂, b₃} : Set G))
    (hτN : τ ∈ Nor (Subgroup.closure ({b, b₁, b₂, b₃} : Set G)))
    {σ : MulAut ↥(Subgroup.closure ({b, b₁, b₂, b₃} : Set G))}
    (hσX : σ ∈ FF81X (Subgroup.closure ({b, b₁, b₂, b₃} : Set G))) :
    σ * FF81X.tau hτN = FF81X.tau hτN * σ ↔
      (σ ⟨b, hbB⟩ = ⟨b, hbB⟩ ∨ σ ⟨b, hbB⟩ = (⟨b, hbB⟩)⁻¹) := by
  let B : Subgroup G := Subgroup.closure ({b, b₁, b₂, b₃} : Set G)
  let bB : ↥B := ⟨b, hbB⟩
  have horderB : orderOf bB = 3 := by
    rw [← Subgroup.orderOf_coe bB]
    simpa [bB] using h.ord
  have hbB_ne : bB ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at horderB
    norm_num at horderB
  constructor
  ·
    intro hcomm
    have hcomm' : σ * FF81X.tau
        (FF81Hyp.tau_mem_normalizer h hτL hb₁ hb₂ hb₃ hE hb hinv) =
        FF81X.tau
          (FF81Hyp.tau_mem_normalizer h hτL hb₁ hb₂ hb₃ hE hb hinv) * σ := by
      simpa [FF81X.tau] using hcomm
    have hmap := FF81Hyp.cen_X_tau_maps_b h hτL hb₁ hb₂ hb₃ hE hτ2o hb hinv hbB hσX hcomm'
    have hσb_mem : σ bB ∈ Subgroup.zpowers bB := by
      have hmem : σ bB ∈ Subgroup.map (σ : ↥B →* ↥B) (Subgroup.zpowers bB) :=
        Subgroup.mem_map_of_mem (σ : ↥B →* ↥B) (Subgroup.mem_zpowers bB)
      rwa [hmap] at hmem
    have hσb_ne : σ bB ≠ 1 := by
      intro h1
      apply hbB_ne
      have h := congrArg (fun y => σ⁻¹ y) h1
      simpa using h
    rcases eq_or_eq_inv_of_mem_zpowers (b := bB) horderB hσb_mem hσb_ne with hfix | hinv'
    · exact Or.inl hfix
    · exact Or.inr hinv'
  ·
    intro hline
    exact FF81Hyp.nor_X_line_le_cen_tau h hTF hOut hτL hb₁ hb₂ hb₃ hE hself hmono hrk
      hτ2o hb hinv hbB hb₁B hb₂B hb₃B hτN hσX hline

end CFSG.RankThree.PartTwo.Sec21.FF81
