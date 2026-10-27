module

public import CFSG.RankThree.GF2n.Stroth80.Sec39

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G]
  {M Q Z A B : Subgroup G}

theorem Ctx.mem_sup_of_comm_centralizer (hc : Ctx M Q Z A) {x : G} (hx : x ∈ Q)
    (hxc : ∀ y ∈ Q ⊓ Subgroup.centralizer (A : Set G), x * y = y * x) : x ∈ A ⊔ Z := by
  obtain ⟨K, hK, hfin, -, γ, M₀, h⟩ := stroth_globalModelData hc.hyp
  obtain ⟨b, hb0, -, hAb, hcent, -⟩ := hc.dictB h
  have h1 : ∀ v : M₀.E, M₀.B v b = 0 → M₀.B (M₀.π x) v = 0 := by
    intro v hv
    obtain ⟨y, hyQ, rfl⟩ := M₀.π_surj v
    exact (M₀.comm_iff_B h.reg hx hyQ).mp (hxc y ⟨hyQ, (hcent y hyQ).mpr hv⟩)
  obtain ⟨c, hc'⟩ := Tim79.QuadModel.exists_smul_of_orthogonal hb0 h1
  have hmem : M₀.π x ∈ M₀.img (A ⊔ Z) := M₀.img_mono le_sup_left ((hAb _).mpr ⟨c, hc'⟩)
  exact (M₀.mem_img_iff le_sup_right hx).mp hmem

theorem Ctx.mem_sup_of_comm_QB_inf_M (hc : Ctx M Q Z B) {y : G} (hy : y ∈ QB B)
    (hyc : ∀ l ∈ QB B ⊓ M, y * l = l * y) : y ∈ B ⊔ Z := by
  obtain ⟨n, h1, -, h3, h4⟩ := hc.exists_swap'
  have hyQ : n⁻¹ * y * n ∈ Q := by
    rw [← h1, mem_conjSubgroup] at hy
    exact hy
  have hN : Subgroup.centralizer (B : Set G) ≤ Subgroup.normalizer (B : Set G) := by
    apply le_normalizer_of_comm
    intro a ha b hb
    exact (Subgroup.mem_centralizer_iff.mp ha b hb).symm
  have hcomm : ∀ c ∈ Q ⊓ Subgroup.centralizer (B : Set G),
      n⁻¹ * y * n * c = c * (n⁻¹ * y * n) := by
    intro c hc'
    obtain ⟨hcQ, hcC⟩ := Subgroup.mem_inf.mp hc'
    have e : n⁻¹ * (n * c * n⁻¹) * n = c := by group
    have hlQB : n * c * n⁻¹ ∈ QB B := by
      rw [← h1, mem_conjSubgroup, e]
      exact hcQ
    have hlM : n * c * n⁻¹ ∈ M := by
      rw [← hc.hyp.normalizer_Z.1, ← h4, mem_normalizer_conj_iff, e]
      exact hN hcC
    have hyl := hyc (n * c * n⁻¹) (Subgroup.mem_inf.mpr ⟨hlQB, hlM⟩)
    have e1 : n⁻¹ * y * n * c = n⁻¹ * (y * (n * c * n⁻¹)) * n := by group
    have e2 : c * (n⁻¹ * y * n) = n⁻¹ * ((n * c * n⁻¹) * y) * n := by group
    rw [e1, e2, hyl]
  have hmem : y ∈ conjSubgroup n (B ⊔ Z) :=
    mem_conjSubgroup.mpr (hc.mem_sup_of_comm_centralizer hyQ hcomm)
  rw [conjSubgroup_sup', h4, h3, sup_comm] at hmem
  exact hmem

theorem Ctx.mem_sup_of_comm_LB_mem_Z (hc : Ctx M Q Z B) {y : G} (hy : y ∈ Q ⊓ QB B)
    (hyc : ∀ l ∈ QB B ⊓ M, ⁅y, l⁆ ∈ Z) : y ∈ B ⊔ Z := by
  refine hc.mem_sup_of_comm_QB_inf_M (Subgroup.mem_inf.mp hy).2 fun l hl => ?_
  have hBc : ⁅y, l⁆ ∈ B :=
    hc.comm_QB_le_B (Subgroup.mem_inf.mp hy).2 (Subgroup.mem_inf.mp hl).1
  have h1 : ⁅y, l⁆ ∈ Z ⊓ B := Subgroup.mem_inf.mpr ⟨hyc l hl, hBc⟩
  rw [hc.inf_eq_bot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1

theorem Ctx.mem_sup_of_comm_LB_mem_Z' (hc : Ctx M Q Z B) {y : G} (hy : y ∈ Q ⊓ QB B)
    (hyc : ∀ l ∈ LB M Q B, ⁅y, l⁆ ∈ Z) : y ∈ B ⊔ Z :=
  hc.mem_sup_of_comm_LB_mem_Z hy fun l hl =>
    hyc l (show l ∈ Q ⊔ (QB B ⊓ M) from Subgroup.mem_sup_right hl)

end CFSG.RankThree.GF2n.Stroth80
