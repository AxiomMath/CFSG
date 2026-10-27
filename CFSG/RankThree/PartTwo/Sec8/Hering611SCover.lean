module

public import CFSG.RankThree.PartTwo.Sec8.Hering611SCovD
public import CFSG.RankThree.PartTwo.Sec8.Hering611SCovR
public import CFSG.RankThree.PartTwo.Sec8.Hering611SCovT
public import CFSG.RankThree.PartTwo.Sec8.Hering611SCovQ

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

variable {X : Type*} [Group X] [Finite X] {Z R T : Subgroup X} {s : X}

theorem false_of_coverX (hX : Group.IsPerfect X) (h : CoverX X Z R T s) (hidx : ¬ 3 ∣ T.index) :
    False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨R₀, hR₀R, hdisj, hsup, hsR₀⟩ := exists_R0 h
  have hR₀T : R₀ ≤ T := hR₀R.trans h.R_le_T
  haveI hN : (R₀.subgroupOf T).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have h1 : (g : X) * (n : X) * (g : X)⁻¹ = (n : X) := by
      have := h.R_central (n : X) (hR₀R hn) (g : X) g.2
      rw [mul_inv_eq_iff_eq_mul]
      exact this.symm
    show (g : X) * (n : X) * (g : X)⁻¹ ∈ R₀
    rw [h1]
    exact hn
  let π : T →* T ⧸ R₀.subgroupOf T := QuotientGroup.mk' (R₀.subgroupOf T)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : ∀ t : T, π t = 1 ↔ (t : X) ∈ R₀ := fun t => by
    show (QuotientGroup.mk t : T ⧸ R₀.subgroupOf T) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  obtain ⟨σ, Zh, hP, -, hmem, hinj, -⟩ := coverP_of_coverX h hR₀R hdisj hsup hsR₀ π hπ hker
  obtain ⟨μ, hμ⟩ := exists_hom_zhat hP
  have hZh : Nat.card Zh = 3 := hP.card_Z
  let φ : Zh ≃* Multiplicative (ZMod 3) := mulEquivOfPrimeCardEq hZh
    (by rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card])
  refine false_of_hom_injective_on_center hX h.Z_central h.card_Z
    (h.Z_le_R.trans h.R_le_T) hidx (φ.toMonoidHom.comp (μ.comp π)) ?_
  intro z hz
  have h1 : μ (π ⟨z, h.R_le_T (h.Z_le_R z.2)⟩) = ⟨π ⟨z, h.R_le_T (h.Z_le_R z.2)⟩, hmem z⟩ :=
    hμ ⟨_, hmem z⟩
  have h2 : φ (μ (π ⟨z, h.R_le_T (h.Z_le_R z.2)⟩)) = 1 := hz
  have h3 : (⟨π ⟨z, h.R_le_T (h.Z_le_R z.2)⟩, hmem z⟩ : Zh) = 1 := by
    apply φ.injective
    rw [map_one, ← h1]
    exact h2
  have h4 : π ⟨z, h.R_le_T (h.Z_le_R z.2)⟩ = π ⟨((1 : Z) : X), h.R_le_T (h.Z_le_R (1 : Z).2)⟩ := by
    have := congrArg Subtype.val h3
    rw [show π ⟨((1 : Z) : X), h.R_le_T (h.Z_le_R (1 : Z).2)⟩ = 1 from
      (hker _).mpr (by simpa using R₀.one_mem)]
    exact this
  exact hinj z 1 h4

end CFSG.RankThree.PartTwo.Sec8.Hering611
