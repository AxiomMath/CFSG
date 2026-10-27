module

public import CFSG.Quasithin.Background.RonanD321End
public import CFSG.Quasithin.Background.RonanD321UniqFix

public section

namespace CFSG.Quasithin.RonanD321

open CFSG.Quasithin CFSG.Quasithin.SmithD321 CFSG.Quasithin.SmithD39Two CFSG.Quasithin.Z391
  CFSG.Quasithin.SmithD391
  CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped Pointwise

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W}

omit [Finite W] in
theorem inv_conj_mem_centralizer_of_normalizer {g a : MulAut W}
    (hg : g ∈ Subgroup.normalizer (L : Set (MulAut W)))
    (ha : a ∈ Subgroup.centralizer (L : Set (MulAut W))) :
    g⁻¹ * a * g ∈ Subgroup.centralizer (L : Set (MulAut W)) := by
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have h1 : g * l * g⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hg l).1 hl
  have h2 := (Subgroup.mem_centralizer_iff.1 ha) _ h1
  calc l * (g⁻¹ * a * g) = g⁻¹ * ((g * l * g⁻¹) * a) * g := by group
    _ = g⁻¹ * (a * (g * l * g⁻¹)) * g := by rw [h2]
    _ = g⁻¹ * a * g * l := by group

theorem smul_tildeU_eq_of_normalizer (hB : D321Base M Mp T L V t) {g : ↥M}
    (hg : (g : MulAut W) ∈ Subgroup.normalizer (L : Set (MulAut W))) :
    letI := qAct hB.hD.hyp.Mp_normal
    g • tilde Mp ⊤ (commV L) = tilde Mp ⊤ (commV L) := by
  let _i := qAct hB.hD.hyp.Mp_normal
  rw [smul_tildeQ hB.hD.hyp.Mp_normal]
  congr 1
  change (commV L).map (g : MulAut W).toMonoidHom = commV L
  rw [map_commV_conjAutSub, mem_normalizer_iff_conjAutSub.1 hg]

theorem exists_fixed_of_nontrivial (hB : D321Base M Mp T L V t) (h3 : D321Three Mp L)
    (h2 : letI := qAct hB.hD.hyp.Mp_normal;
      ∀ y (hy : y ∈ M ⊓ Subgroup.centralizer (L : Set (MulAut W))), ∃ k : ℕ,
        ∀ q ∈ tilde Mp ⊤ (commV L), (⟨y, hy.1⟩ : ↥M) ^ (2 ^ k) • q = q)
    (hnt : letI := qAct hB.hD.hyp.Mp_normal;
      ∃ y, ∃ hy : y ∈ M ⊓ Subgroup.centralizer (L : Set (MulAut W)),
        ∃ q ∈ tilde Mp ⊤ (commV L), (⟨y, hy.1⟩ : ↥M) • q ≠ q) :
    letI := qAct hB.hD.hyp.Mp_normal
    ∃ J : Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W)),
      XMod.IsIrr ↥(L.subgroupOf M) J ∧ J ≤ tilde Mp ⊤ (commV L) ∧
      ∀ g : ↥M, (g : MulAut W) ∈ Subgroup.normalizer (L : Set (MulAut W)) → g • J = J := by
  let _i := qAct hB.hD.hyp.Mp_normal
  obtain ⟨_, I, hI, -, -, -, hIY, hY, -, -⟩ := exists_isotypic_of_d321Three hB h3
  set Y := tilde Mp ⊤ (commV L)
  set Λ := L.subgroupOf M
  set A := (M ⊓ Subgroup.centralizer (L : Set (MulAut W))).subgroupOf M
  have hQ := hB.quot_sq
  have hAc : ∀ a ∈ A, ∀ l ∈ Λ, l * a = a * l := by
    intro a ha l hl
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.1 (Subgroup.mem_subgroupOf.1 ha).2) _
      (Subgroup.mem_subgroupOf.1 hl))
  have hAΛ : ∀ a ∈ A, ∀ l ∈ Λ, a * l * a⁻¹ ∈ Λ := by
    intro a ha l hl
    rw [← hAc a ha l hl, mul_inv_cancel_right]
    exact hl
  have hAY : ∀ a ∈ A, ∀ q ∈ Y, a • q ∈ Y := by
    intro a ha q hq
    have h1 : a • q ∈ a • Y := Subgroup.smul_mem_pointwise_smul _ _ _ hq
    rwa [smul_tildeU_eq_of_normalizer hB (Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_subgroupOf.1 ha).2)] at h1
  have hA2 : ∀ a ∈ A, ∃ k : ℕ, ∀ q ∈ Y, a ^ (2 ^ k) • q = q :=
    fun a ha => h2 _ (Subgroup.mem_subgroupOf.1 ha)
  obtain ⟨J₀, hJ₀Y, hJ₀i, hJ₀m, hJ₀A⟩ :=
    exists_max_fixed_of_two_pow hQ hI hY (by norm_num) hA2 hAΛ hAY
  have hJ₀ : XMod.IsIrr ↥Λ J₀ :=
    isIrr_of_isotypicOfLength_one hQ hI (isotypicOfLength_of_max hQ hI hY hJ₀Y hJ₀i hJ₀m)
  have huniq : ∀ J₁ : Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W)), XMod.IsIrr ↥Λ J₁ → J₁ ≤ Y →
      (∀ a ∈ A, ∀ q ∈ J₁, a • q ∈ J₁) → J₁ = J₀ := by
    intro J₁ hJ₁ hJ₁Y hJ₁A
    by_contra hne
    obtain ⟨y, hy, q, hq, hyq⟩ := hnt
    have hyA : (⟨y, hy.1⟩ : ↥M) ∈ A := Subgroup.mem_subgroupOf.2 hy
    obtain ⟨k, hk⟩ := hA2 _ hyA
    exact hyq (smul_eq_of_ne_of_isotypicOfLength_two hQ hI hIY hY hJ₁ hJ₁Y hJ₀ hJ₀Y hne
      (hAc _ hyA) (hJ₁A _ hyA) (hJ₀A _ hyA) hk q hq)
  set H := (Subgroup.normalizer (L : Set (MulAut W))).subgroupOf M
  have hN : XMod.Normalizes ↥Λ ↥H (W ⧸ modFix Mp (⊤ : Subgroup W)) := by
    refine normalizes_of_conj Λ H fun g hg l hl => ?_
    exact Subgroup.mem_subgroupOf.2
      ((Subgroup.mem_normalizer_iff.1 (Subgroup.mem_subgroupOf.1 hg) _).1
        (Subgroup.mem_subgroupOf.1 hl))
  refine ⟨J₀, hJ₀, hJ₀Y, fun g hg => huniq _ ?_ ?_ ?_⟩
  · exact isIrr_smul hN (⟨g, Subgroup.mem_subgroupOf.2 hg⟩ : ↥H) hJ₀
  · calc g • J₀ ≤ g • Y := Subgroup.pointwise_smul_le_pointwise_smul_iff.2 hJ₀Y
      _ = Y := smul_tildeU_eq_of_normalizer hB hg
  · intro a ha q hq
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hq ⊢
    have h1 : g⁻¹ * a * g ∈ A := Subgroup.mem_subgroupOf.2
      ⟨(g⁻¹ * a * g).2,
        inv_conj_mem_centralizer_of_normalizer hg (Subgroup.mem_subgroupOf.1 ha).2⟩
    have h2 : g⁻¹ • a • q = (g⁻¹ * a * g) • g⁻¹ • q := by
      rw [smul_smul, smul_smul, mul_assoc, mul_assoc, mul_inv_cancel, mul_one]
    rw [h2]
    exact hJ₀A _ h1 _ hq

end CFSG.Quasithin.RonanD321
