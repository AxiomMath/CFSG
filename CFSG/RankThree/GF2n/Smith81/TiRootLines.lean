module

public import CFSG.RankThree.GF2n.Smith81.TiReduction

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
variable {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}

theorem omega_of_lines (H : StrothHyp M Q Z) (hD : GlobalModelData M Q Z γ M₀) (V : Set M₀.E)
    (hV2 : ∀ v ∈ V, ∀ w ∈ V, M₀.B v w = 0 → ∃ s : K, w = s • v)
    (hV3 : ∀ A : Subgroup G, Ctx M Q Z A →
      ∃ v ∈ V, v ≠ 0 ∧ ∀ a ∈ A, ∃ s : K, M₀.π a = s • v) :
    OmegaProp M Q Z := by
  intro A C hA hC hAQ hCQ hAZ hCZ hcomm
  have cA : Ctx M Q Z A := ⟨H, hA, hAQ, hAZ⟩
  have cC : Ctx M Q Z C := ⟨H, hC, hCQ, hCZ⟩
  obtain ⟨bA, hbA0, -, hbA, -, -⟩ := cA.dictB hD
  obtain ⟨bC, hbC0, -, hbC, -, -⟩ := cC.dictB hD
  obtain ⟨vA, hvA, hvA0, hAv⟩ := hV3 A cA
  obtain ⟨vC, hvC, hvC0, hCv⟩ := hV3 C cC
  obtain ⟨a₀, ha₀A, ha₀Q, ha₀⟩ := (hbA bA).mpr ⟨1, (one_smul K bA).symm⟩
  obtain ⟨c₀, hc₀C, hc₀Q, hc₀⟩ := (hbC bC).mpr ⟨1, (one_smul K bC).symm⟩
  obtain ⟨sA, hsA⟩ := hAv a₀ ha₀A
  obtain ⟨sC, hsC⟩ := hCv c₀ hc₀C
  rw [ha₀] at hsA
  rw [hc₀] at hsC
  have hsA0 : sA ≠ 0 := by
    rintro rfl
    exact hbA0 (by rw [hsA, zero_smul])
  have hsC0 : sC ≠ 0 := by
    rintro rfl
    exact hbC0 (by rw [hsC, zero_smul])
  have hB0 : M₀.B bA bC = 0 := by
    rw [← ha₀, ← hc₀]
    exact (Tim79.QuadModel.comm_iff_B M₀ hD.reg ha₀Q hc₀Q).mp (hcomm a₀ ha₀A c₀ hc₀C)
  have hBv : M₀.B vA vC = 0 := by
    have h1 : M₀.B (sA • vA) (sC • vC) = (sA * sC) * M₀.B vA vC := by
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
      ring
    rw [← hsA, ← hsC, hB0] at h1
    rcases mul_eq_zero.mp h1.symm with h | h
    · exact absurd h (mul_ne_zero hsA0 hsC0)
    · exact h
  obtain ⟨s, hs⟩ := hV2 vA hvA vC hvC hBv
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hvC0 (by rw [hs, zero_smul])
  have hne : sC * s ≠ 0 := mul_ne_zero hsC0 hs0
  intro a ha
  have haQ : a ∈ Q := hAQ ha
  obtain ⟨t, ht⟩ := (hbA _).mp (M₀.pi_mem_img ha haQ)
  have hbC' : bC = (sC * s) • vA := by rw [hsC, hs, smul_smul]
  have hvA' : vA = (sC * s)⁻¹ • bC := by
    rw [hbC', smul_smul, inv_mul_cancel₀ hne, one_smul]
  have hπ : M₀.π a ∈ M₀.img C := by
    refine (hbC _).mpr ⟨t * (sA * (sC * s)⁻¹), ?_⟩
    rw [ht, hsA, hvA', smul_smul, smul_smul, mul_assoc]
  have hZC : Z ≤ C ⊔ Z := le_sup_right
  exact (M₀.mem_img_iff hZC haQ).mp (M₀.img_mono le_sup_left hπ)

theorem p2_of_conj (H : StrothHyp M Q Z)
    (hb : ∀ (X : Subgroup G) (x : G), Sit M Q Z X x →
      ∃ b ∈ Q ⊓ QB X, b ≠ 1 ∧ ∃ (g z : G), z ∈ Z ∧ b = g * z * g⁻¹) :
    P2Prop M Q Z := by
  intro X x hs
  obtain ⟨b, hbQQ, hb1, g₀, z₀, hz₀, hbg⟩ := hb X x hs
  have h12 := smith_1_12 hs
  obtain ⟨hbQ, hbB⟩ := Subgroup.mem_inf.mp hbQQ
  obtain ⟨g, hg, hQB, -⟩ := hs.QB_eq
  have hbZ : b ∉ Z := by
    intro hZ
    have : b ∈ Z ⊓ QB X := ⟨hZ, hbB⟩
    rw [Z_inf_QB_eq_bot hs h12, Subgroup.mem_bot] at this
    exact hb1 this
  obtain ⟨k, hkQ, hbk⟩ := stroth_2_6 H hbQ hbZ ⟨g₀, z₀, hz₀, hbg⟩
  refine ⟨conjSubgroup k Z, ⟨k, rfl⟩, le_inf hkQ ?_⟩
  have hbB' : g⁻¹ * b * g ∈ Q := by
    rw [hQB, mem_conjSubgroup] at hbB
    exact hbB
  have hb'Z : g⁻¹ * b * g ∉ Z := by
    intro hZ
    have hbX : b ∈ X := by rw [hg, mem_conjSubgroup]; exact hZ
    have : b ∈ X ⊓ Q := ⟨hbX, hbQ⟩
    rw [h12.2, Subgroup.mem_bot] at this
    exact hb1 this
  obtain ⟨h, hhQ, hbh⟩ := stroth_2_6 H hbB' hb'Z ⟨g⁻¹ * g₀, z₀, hz₀, by rw [hbg]; group⟩
  have hgh : conjSubgroup (g * h) Z ≤ QB X := by
    rw [hQB, conjSubgroup_mul]
    exact conjSubgroup_mono hhQ
  have hb_gh : b ∈ conjSubgroup (g * h) Z := by
    rw [conjSubgroup_mul, mem_conjSubgroup]
    exact hbh
  have heq : conjSubgroup k Z = conjSubgroup (g * h) Z :=
    conjSubgroup_eq_of_mem_ne_one H hb1 hbk hb_gh
  rw [heq]
  exact hgh

theorem Sit.inf_QB_elemAbelian {X : Subgroup G} {x : G} (hs : Sit M Q Z X x) :
    IsElemAbelian 2 (Q ⊓ QB X) := by
  obtain ⟨g, hg, hQB, -⟩ := hs.QB_eq
  have hinf : Z ⊓ X = ⊥ := hs.Z_inf_X
  have hmem : ∀ y ∈ Q ⊓ QB X, y ∈ Q ∧ y ∈ conjSubgroup g Q := by
    intro y hy
    rw [hQB] at hy
    exact Subgroup.mem_inf.mp hy
  have hcomm : ∀ y ∈ Q ⊓ QB X, ∀ w ∈ Q ⊓ QB X, y * w = w * y := by
    intro y hy w hw
    obtain ⟨hyQ, hyg⟩ := hmem y hy
    obtain ⟨hwQ, hwg⟩ := hmem w hw
    have h1 : ⁅y, w⁆ ∈ Z := hs.hyp.toHyp79.comm_mem_V hyQ hwQ
    have h2 : ⁅y, w⁆ ∈ X := by
      rw [hg]
      exact hs.hyp.toHyp79.comm_mem_conj g hyg hwg
    have h3 : ⁅y, w⁆ ∈ Z ⊓ X := Subgroup.mem_inf.mpr ⟨h1, h2⟩
    rw [hinf, Subgroup.mem_bot] at h3
    exact commutatorElement_eq_one_iff_mul_comm.mp h3
  have hsq : ∀ y ∈ Q ⊓ QB X, y ^ 2 = 1 := by
    intro y hy
    obtain ⟨hyQ, hyg⟩ := hmem y hy
    have h1 : y ^ 2 ∈ Z := hs.hyp.toHyp79.sq_mem_V hyQ
    have h2 : y ^ 2 ∈ X := by
      rw [hg]
      exact hs.hyp.toHyp79.sq_mem_conj g hyg
    have h3 : y ^ 2 ∈ Z ⊓ X := Subgroup.mem_inf.mpr ⟨h1, h2⟩
    rw [hinf, Subgroup.mem_bot] at h3
    exact h3
  exact ⟨⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩, fun y hy => hsq y hy⟩

end CFSG.RankThree.GF2n.Smith81
