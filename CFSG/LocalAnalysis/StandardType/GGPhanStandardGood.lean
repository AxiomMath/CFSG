module

public import CFSG.LocalAnalysis.StandardType.PhanEStdChoice
public import CFSG.LocalAnalysis.StandardType.GGPhanCompletionRecovery
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanEData
import CFSG.LocalAnalysis.StandardType.GGTPNThmULabel
import CFSG.GH74.L5U5.IdentUnitary
import CFSG.LocalAnalysis.StandardType.PhanEStdClassified

public noncomputable section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.LieType.Universal CFSG.LieType.BorelTits
  CFSG.ClassicalInvolution.Phan CFSG.LieType.CurtisTits

variable {F : Type} [Field F] [Finite F] {f : ℕ} [CharP F 2]

section WeakSystem

variable {n : ℕ} {M : CoxeterMatrix (Fin n)} {G : Type} [Group G]
  {S : PhanFamilyE F 2 f M G}

theorem PhanFamilyE.Good.unitaryBlockStandardPair (hS : S.Good) {i j : Fin n}
    (hij : i < j) (h3 : M i j = 3) :
    UnitaryBlockStandardPair F 2 f (S.θ i j).range (S.ι i).range (S.ι j).range := by
  apply CFSG.GH74.L5U5.unitaryBlockStandardPair_of_blocks
  · rw [(MonoidHom.ker_eq_bot_iff (S.θ i j)).mpr (hS.θ_inj i j hij h3)]
    exact bot_le
  · rw [B12, ← MonoidHom.range_comp, S.left i j hij h3]
  · rw [B23, ← MonoidHom.range_comp, S.right i j hij h3]

theorem PhanFamilyE.Good.exists_unitaryBlockStandardPair (hS : S.Good) {i j : Fin n}
    (h3 : M i j = 3) :
    ∃ W : Subgroup G, UnitaryBlockStandardPair F 2 f W (S.ι i).range (S.ι j).range := by
  rcases lt_trichotomy i j with hij | hij | hji
  · exact ⟨_, hS.unitaryBlockStandardPair hij h3⟩
  · subst j
    have := M.diagonal i
    omega
  · obtain ⟨θ, c, hrange, hker, hblocks⟩ :=
      hS.unitaryBlockStandardPair hji ((M.symmetric j i).trans h3)
    exact ⟨_, θ, c, hrange, hker, hblocks.symm⟩

theorem PhanFamilyE.Good.weakPhanSL_subgroupOf (hS : S.Good)
    (hF : Nat.card F = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) :
    WeakPhanSL F 2 f M
      (fun i => ((S.ι i).range).subgroupOf (⨆ j, (S.ι j).range))
      (fun i j => ((S.ι i).range).subgroupOf (⨆ k, (S.ι k).range) ⊔
        ((S.ι j).range).subgroupOf (⨆ k, (S.ι k).range)) := by
  apply CFSG.StandardType.ggWeakPhanSL_subgroupOf (Equiv.refl _) (by rfl) hq F hF
    (fun i => (S.ι i).range) _ _ _ rfl
  · exact fun i => ⟨MonoidHom.ofInjective (hS.inj i)⟩
  · rintro i j _ h2 a ⟨x, rfl⟩ b ⟨y, rfl⟩
    exact S.comm i j h2 x y
  · exact fun i j h3 => hS.exists_unitaryBlockStandardPair h3

theorem PhanFamilyE.Good.weakPhanSL (hS : S.Good)
    (hF : Nat.card F = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f)
    (hgen : (⨆ i, (S.ι i).range) = ⊤) :
    WeakPhanSL F 2 f M (fun i => (S.ι i).range)
      (fun i j => (S.ι i).range ⊔ (S.ι j).range) := by
  refine ⟨fun i => ⟨MonoidHom.ofInjective (hS.inj i)⟩, fun _ _ _ => rfl, ?_, ?_, hgen⟩
  · rintro i j h2 a ⟨x, rfl⟩ b ⟨y, rfl⟩
    exact S.comm i j h2 x y
  · intro i j h3
    obtain ⟨W, hW⟩ := hS.exists_unitaryBlockStandardPair h3
    rwa [CFSG.GH74.L5U5.unitaryBlockStandardPair_eq_sup hF (by omega) hW] at hW

end WeakSystem

private theorem good_ofEq {n : ℕ} {M M' : CoxeterMatrix (Fin n)} {G : Type} [Group G]
    (h : M = M') (c : PhanEConfig F f M G) (hc : c.S.Good) : (c.ofEq h).S.Good := by
  cases h
  exact hc

private theorem good_config {K : Type} [Group K] {D : UniversalRootDatum K}
    {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} (S : StdInput D n H)
    {G : Type} [Group G] (e : G ≃* frobFix S.F) (κ : F ≃+* S.L.Fld)
    (hκ : ∀ c, κ (unitaryInvolution F 2 f c) = S.L.θ (κ c)) :
    (S.config e κ hκ).S.Good :=
  stdFamily_good S.L (S.rho_injective e) (S.range_rho e) κ hκ S.hct S.hext S.hsl


theorem e6StdConfig_good (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f) :
    (e6StdConfig F f hF hf).S.Good := by
  unfold e6StdConfig
  apply good_ofEq
  exact good_config _ _ _ _

theorem e7StdConfig_good (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f) :
    (e7StdConfig F f hF hf).S.Good := by
  unfold e7StdConfig
  apply good_ofEq
  exact good_config _ _ _ _

theorem e8StdConfig_good (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f) :
    (e8StdConfig F f hF hf).S.Good := by
  unfold e8StdConfig
  apply good_ofEq
  exact good_config _ _ _ _

theorem PhanEInput2.standardFamily_generate_E6
    (hF : Nat.card F = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) :
    (⨆ i, ((e6StdConfig F f hF (one_le_of_four_le_two_pow hq)).S.ι i).range) = ⊤ := by
  have hf := one_le_of_four_le_two_pow hq
  have : Finite (lieUniversal .twistedE6 0 2 f Nat.prime_two).K :=
    CFSG.StandardType.LieKnownR2.OddCenter.finite_ggU (by simp) ⟨Nat.prime_two, hf, rfl⟩
  have hS := e6StdConfig_good hF hf
  obtain ⟨θ, hθ, hker⟩ := (phanEInput2_holds F f hF hq).1 _ _ (hS.weakPhanSL_subgroupOf hF hq)
  have hQ := isQuasisimple_lieUniversal_twistedE6 f hf
  exact CFSG.StandardType.eq_top_of_mulEquiv_quotient_center hQ.1.commutator_eq_top
    (centralQuotientEquivOfIsQuasisimple hQ hθ hker).symm

theorem PhanEInput2.standardFamily_generate_E7
    (hF : Nat.card F = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) :
    (⨆ i, ((e7StdConfig F f hF (one_le_of_four_le_two_pow hq)).S.ι i).range) = ⊤ := by
  have hf := one_le_of_four_le_two_pow hq
  have : Finite (lieUniversal .E7 0 2 f Nat.prime_two).K :=
    CFSG.StandardType.LieKnownR2.OddCenter.finite_ggU (by simp) ⟨Nat.prime_two, hf, rfl⟩
  have hS := e7StdConfig_good hF hf
  obtain ⟨θ, hθ, hker⟩ := (phanEInput2_holds F f hF hq).2.1 _ _ (hS.weakPhanSL_subgroupOf hF hq)
  have hQ := isQuasisimple_lieUniversal_E7 f
  exact CFSG.StandardType.eq_top_of_mulEquiv_quotient_center hQ.1.commutator_eq_top
    (centralQuotientEquivOfIsQuasisimple hQ hθ hker).symm

theorem PhanEInput2.standardFamily_generate_E8
    (hF : Nat.card F = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) :
    (⨆ i, ((e8StdConfig F f hF (one_le_of_four_le_two_pow hq)).S.ι i).range) = ⊤ := by
  have hf := one_le_of_four_le_two_pow hq
  have : Finite (lieUniversal .E8 0 2 f Nat.prime_two).K :=
    CFSG.StandardType.LieKnownR2.OddCenter.finite_ggU (by simp) ⟨Nat.prime_two, hf, rfl⟩
  have hS := e8StdConfig_good hF hf
  obtain ⟨θ, hθ, hker⟩ := (phanEInput2_holds F f hF hq).2.2 _ _ (hS.weakPhanSL_subgroupOf hF hq)
  have hQ := isQuasisimple_lieUniversal_E8 f
  exact CFSG.StandardType.eq_top_of_mulEquiv_quotient_center hQ.1.commutator_eq_top
    (centralQuotientEquivOfIsQuasisimple hQ hθ hker).symm

theorem PhanEInput2.standardFamily_isUniversal_E6
    (hF : Nat.card F = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) :
    (e6StdConfig F f hF (one_le_of_four_le_two_pow hq)).S.IsUniversal := by
  have hS := e6StdConfig_good hF (one_le_of_four_le_two_pow hq)
  exact PhanEInput2.isUniversal_E6 phanEInput2_holds hF hq _
    hS _ (hS.weakPhanSL hF hq (PhanEInput2.standardFamily_generate_E6 hF hq))

theorem PhanEInput2.standardFamily_isUniversal_E7
    (hF : Nat.card F = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) :
    (e7StdConfig F f hF (one_le_of_four_le_two_pow hq)).S.IsUniversal := by
  have hS := e7StdConfig_good hF (one_le_of_four_le_two_pow hq)
  exact PhanEInput2.isUniversal_E7 phanEInput2_holds hF hq _
    hS _ (hS.weakPhanSL hF hq (PhanEInput2.standardFamily_generate_E7 hF hq))

theorem PhanEInput2.standardFamily_isUniversal_E8
    (hF : Nat.card F = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) :
    (e8StdConfig F f hF (one_le_of_four_le_two_pow hq)).S.IsUniversal := by
  have hS := e8StdConfig_good hF (one_le_of_four_le_two_pow hq)
  exact PhanEInput2.isUniversal_E8 phanEInput2_holds hF hq _
    hS _ (hS.weakPhanSL hF hq (PhanEInput2.standardFamily_generate_E8 hF hq))

end CFSG.ClassicalInvolution.Phan.PhanE
