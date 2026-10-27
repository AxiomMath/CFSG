module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec97F3A

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace HS9

theorem exists_mem_QB_inf_M_comm_eq (hc : Ctx M Q Z B) {F : Subgroup G} (hcF : Ctx M Q Z F)
    (hFB : F ≤ QB B) (hF : ¬ F ≤ Z ⊔ B) {f b : G} (hf : f ∈ F) (hf1 : f ≠ 1) (hb : b ∈ B) :
    ∃ ε ∈ QB B ⊓ M, ⁅ε, f⁆ = b := by
  obtain ⟨g, hg⟩ := hc.conj
  obtain ⟨-, hQC⟩ := Ctx.QB_eq hc hg
  obtain ⟨n, γ, M₀, -, h⟩ := stroth_globalModelDataGF hc.hyp
  have hZQC : Z ≤ conjSubgroup g Q := hQC ▸ hc.Z_le_QB.1
  have hZ' : conjSubgroup g⁻¹ (conjSubgroup g Z) = Z := by
    rw [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
  have hne : conjSubgroup g⁻¹ (conjSubgroup g Z) ≠ conjSubgroup g Z := by
    rw [hZ', ← hg]
    exact hc.ne.symm
  have hle : conjSubgroup g⁻¹ (conjSubgroup g Z) ≤ conjSubgroup g Q := by
    rw [hZ']
    exact hZQC
  set M₁ := M₀.conj g with hM₁
  have hline := (h.conj g).line g⁻¹ hne hle
  rw [hZ'] at hline
  obtain ⟨e, he0, he⟩ := hline
  have R₁ := (h.conj g).reg
  obtain ⟨z₀, hz₀, hz₀1⟩ : ∃ z₀ ∈ Z, z₀ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have h4 := hc.hyp.q4
    have hZbot : Z = ⊥ := (Subgroup.eq_bot_iff_forall Z).mpr hcon
    rw [hZbot, Subgroup.card_bot] at h4
    omega
  have hz₀Q : z₀ ∈ conjSubgroup g Q := hZQC hz₀
  have hfQ : f ∈ conjSubgroup g Q := hQC ▸ hFB hf
  have hbV : b ∈ conjSubgroup g Z := hg ▸ hb
  have hx0 : M₁.π z₀ ≠ 0 := by
    intro h0
    have h1 : z₀ ∈ conjSubgroup g Z := (M₁.π_ker z₀ hz₀Q).mp h0
    have h2 : z₀ ∈ Z ⊓ B := ⟨hz₀, hg ▸ h1⟩
    rw [hc.inf_eq_bot, Subgroup.mem_bot] at h2
    exact hz₀1 h2
  obtain ⟨s₀, hs₀⟩ := (he _).mp (M₁.pi_mem_img hz₀ hz₀Q)
  have hs₀0 : s₀ ≠ 0 := by
    rintro rfl
    exact hx0 (by rw [hs₀, zero_smul])
  have hind : ∀ s : GaloisField 2 n, M₁.π f ≠ s • M₁.π z₀ := by
    intro s hs
    have hfimg : M₁.π f ∈ M₁.img Z := (he _).mpr ⟨s * s₀, by rw [hs, hs₀, smul_smul]⟩
    have hfW : M₁.π f ∈ M₁.img (Z ⊔ B) := M₁.img_mono le_sup_left hfimg
    have hVS : conjSubgroup g Z ≤ Z ⊔ B := by
      rw [← hg]
      exact le_sup_right
    exact hf1 (eq_one_of_mem_sup_of_not_le hc hcF hF hf ((M₁.mem_img_iff hVS hfQ).mp hfW))
  obtain ⟨y, hy, h1, h2⟩ := M₁.exists_comm_eq_one R₁ hfQ hz₀Q hx0 hind hbV
  have hyB : y ∈ QB B := hQC ▸ hy
  have hB0 : M₁.B (M₁.π y) e = 0 := by
    have h3 : y * z₀ = z₀ * y :=
      commutatorElement_eq_one_iff_mul_comm.mp h2
    have h4 := (Tim79.QuadModel.comm_iff_B M₁ R₁ hy hz₀Q).mp h3
    rw [hs₀, map_smul, smul_eq_mul] at h4
    exact (mul_eq_zero.mp h4).resolve_left hs₀0
  have hcent : ∀ z ∈ Z, z * y = y * z := by
    intro z hz
    have hzQ : z ∈ conjSubgroup g Q := hZQC hz
    obtain ⟨s₁, hs₁⟩ := (he _).mp (M₁.pi_mem_img hz hzQ)
    have h5 : M₁.B (M₁.π y) (M₁.π z) = 0 := by
      rw [hs₁, map_smul, hB0, smul_zero]
    exact ((Tim79.QuadModel.comm_iff_B M₁ R₁ hy hzQ).mpr h5).symm
  have hyM : y ∈ M := by
    rw [← hc.hyp.normalizer_Z.1]
    exact Subgroup.centralizer_le_normalizer (Z : Set G)
      (Subgroup.mem_centralizer_iff.mpr hcent)
  exact ⟨y, ⟨hyB, hyM⟩, h1⟩

end HS9

end CFSG.RankThree.GF2n.Stroth80
