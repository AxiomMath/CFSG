module

public import CFSG.Quasithin.Background.C124Interface
public import CFSG.Quasithin.Background.C124BlkQuot
public import CFSG.Quasithin.Background.C124BlkHat6Z
public import CFSG.Quasithin.Background.A3Structure312Iso
public import CFSG.Quasithin.Background.C124BlkTransfer

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

theorem card_threeSpace {K : Type} [Field K] {q : ℕ} (hK : Nat.card K = q) :
    Nat.card (Multiplicative (Fin 3 → K)) = q ^ 3 := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_pi]
  simp [hK]

theorem exists_central_scalar {K : Type} [Field K]
    {Γ₀ : Subgroup (Matrix.GeneralLinearGroup (Fin 3) K)}
    (hHat : IsHat ↥Γ₀ ↥(alternatingGroup (Fin 6)))
    (hcen : ∀ g ∈ Subgroup.center ↥Γ₀, ∃ c : K,
      (((g : ↥Γ₀) : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = c • 1) :
    ∃ z ∈ Subgroup.center ↥Γ₀, ∃ c : K, c ≠ 1 ∧
      (((z : ↥Γ₀) : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = c • 1 := by
  have h3 : Nat.card (Subgroup.center ↥Γ₀) = 3 := hHat.2.1
  have : Finite (Subgroup.center ↥Γ₀) := Nat.finite_of_card_ne_zero (by omega)
  have : Nontrivial (Subgroup.center ↥Γ₀) := Finite.one_lt_card_iff_nontrivial.1 (by omega)
  obtain ⟨z, hz1⟩ := exists_ne (1 : Subgroup.center ↥Γ₀)
  obtain ⟨c, hc⟩ := hcen z z.2
  refine ⟨z, z.2, c, fun h => hz1 ?_, hc⟩
  subst h
  refine Subtype.ext (Subtype.ext (Units.ext ?_))
  simpa using hc

theorem exists_blockHomNat {G : Type} [Group G] [Finite G] {V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hL : L ≤ Subgroup.normalizer (V : Set G))
    (hVL : ⁅V, L⁆ ≤ blockU L) (hU : blockU L = ⁅V, L⁆ ⊔ blockZ L)
    {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (Γ : Subgroup (Matrix.GeneralLinearGroup ι K)) (π : ↥Γ →* ↥(autI hV L))
    (hπ : (FFModel.nat Γ).RealizesVia (autI hV L) (commV (autI hV L))
      (fixV (autI hV L) ⊓ commV (autI hV L)) π) :
    ∃ β : ↥(blockU L) →* Multiplicative (ι → K),
      Function.Surjective β ∧ β.ker = (blockZ L).subgroupOf (blockU L) ∧
      ∀ (ℓ : ↥L) (γ : ↥Γ), π γ = starHom hV L hL ℓ → ∀ u v : ↥(blockU L),
        (v : G) = ℓ * u * ℓ⁻¹ → Multiplicative.toAdd (β v) =
          ((γ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K).mulVec
            (Multiplicative.toAdd (β u)) := by
  obtain ⟨β, hβs, hβk, hβe⟩ := exists_blockHomOfEquiv hV hL hVL hU (FFModel.nat Γ) π hπ
    (natQuotEquiv (FFModel.nat Γ) rfl rfl)
  exact ⟨β, hβs, hβk, fun ℓ γ hγ u v hv =>
    congrArg Multiplicative.toAdd
      (hβe ℓ γ hγ u v ⟨(β u : Multiplicative (ι → K)), trivial⟩ trivial hv rfl)⟩

theorem spec4cHat6_holds : Spec4cHat6 := by
  intro G _ _ X T V L R m hV hE hC hB
  have hL : L ≤ Subgroup.normalizer (V : Set G) := (le_of_mem_cComp hE.comp).trans hE.red.2.1
  obtain ⟨-, ⟨K, hK, hKfin, Γ₀, hK4, -, hHat0, hcen, π₀, hπ₀⟩, hHat⟩ := hC
  obtain ⟨π, hπ⟩ : ∃ π : ↥Γ₀ →* ↥(autI hV L), (FFModel.nat Γ₀).RealizesVia (autI hV L)
      (commV (autI hV L)) (fixV (autI hV L) ⊓ commV (autI hV L)) π := ⟨π₀, hπ₀⟩
  obtain ⟨z, hz, c, hc1, hzc⟩ := exists_central_scalar hHat0 hcen
  have hπs : Function.Surjective π := hπ.1
  have hker := ker_starHom_eq_pCore hV hL hB.ker
  have hcentπ : ∀ x : ↥(autI hV L), x * π z = π z * x := by
    intro x
    obtain ⟨γ, rfl⟩ := hπs x
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz γ]
  obtain ⟨ℓ₀, hℓ₀⟩ := starHom_surjective hV hL (π z)
  have hc : ∀ l ∈ L, (ℓ₀ : G) * l * (ℓ₀ : G)⁻¹ * l⁻¹ ∈ blockQ L := by
    intro l hl
    have h1 : ℓ₀ * ⟨l, hl⟩ * ℓ₀⁻¹ * ⟨l, hl⟩⁻¹ ∈ (starHom hV L hL).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hℓ₀, ← hcentπ]
      group
    rw [hker] at h1
    have h2 := Subgroup.mem_map_of_mem L.subtype h1
    rw [← pCoreOf_eq_map_pCore] at h2
    exact h2
  obtain ⟨β, hβs, hβk, hβe⟩ := exists_blockHomNat hV hL hB.VL_le hB.U_eq Γ₀ π hπ
  have hcne : c - 1 ≠ 0 := sub_ne_zero.2 hc1
  have hs : ∀ u ∈ blockU L, ∃ u₁ ∈ blockU L,
      ((ℓ₀ : G) * u₁ * (ℓ₀ : G)⁻¹ * u₁⁻¹)⁻¹ * u ∈ blockZ L := by
    intro u hu
    set x : Fin 3 → K := Multiplicative.toAdd (β ⟨u, hu⟩) with hx
    set t : Fin 3 → K := (c - 1)⁻¹ • x with ht
    obtain ⟨u₁, hu₁⟩ := hβs (Multiplicative.ofAdd t)
    have hℓU : (ℓ₀ : G) * u₁ * (ℓ₀ : G)⁻¹ ∈ blockU L :=
      (Subgroup.mem_normalizer_iff.mp (C1.le_normalizer_blockU L ℓ₀.2) u₁).mp u₁.2
    set v : ↥(blockU L) := ⟨_, hℓU⟩ with hvdef
    have hv : (v : G) = ℓ₀ * u₁ * ℓ₀⁻¹ := by
      rw [Subgroup.coe_inv]
    have h1 := hβe ℓ₀ z hℓ₀.symm u₁ v hv
    rw [hzc] at h1
    simp only [Matrix.smul_mulVec, Matrix.one_mulVec] at h1
    have hu₁' : Multiplicative.toAdd (β u₁) = t := by rw [hu₁]; rfl
    have hxt : (c - 1) • t = x := by rw [ht, smul_smul, mul_inv_cancel₀ hcne, one_smul]
    have hkw : β (u₁ * v⁻¹ * ⟨u, hu⟩) = 1 := by
      have e1 : β (u₁ * v⁻¹ * ⟨u, hu⟩) = β u₁ * (β v)⁻¹ * β ⟨u, hu⟩ := by
        simp only [map_mul, map_inv]
      apply Multiplicative.toAdd.injective
      rw [e1, toAdd_mul, toAdd_mul, toAdd_inv, h1, hu₁', toAdd_one, ← hx, ← hxt]
      module
    have hZw : ((u₁ * v⁻¹ * ⟨u, hu⟩ : ↥(blockU L)) : G) ∈ blockZ L :=
      Subgroup.mem_subgroupOf.1 (hβk ▸ (MonoidHom.mem_ker.2 hkw))
    refine ⟨u₁, u₁.2, ?_⟩
    have e : ((ℓ₀ : G) * u₁ * (ℓ₀ : G)⁻¹ * (u₁ : G)⁻¹)⁻¹ * u =
        ((u₁ * v⁻¹ * ⟨u, hu⟩ : ↥(blockU L)) : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hv]
      group
    rw [e]
    exact hZw
  have hZ : blockZ L = ⊥ := blockZ_eq_bot_of_surj hB.short ℓ₀.2 hc hs
  have hβinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβk, hZ, Subgroup.bot_subgroupOf]
  let e : ↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥(autI hV L) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (starHom hV L hL) (starHom_surjective hV hL))
  refine ⟨hB.short, IsHat.of_mulEquiv e.symm hHat, ?_,
    C1.inf_centralizer_blockU_eq hB.short le_rfl Subgroup.le_normalizer
      (fun g hg => ⟨0, by simpa using hg⟩)⟩
  rw [Nat.card_congr (Equiv.ofBijective β ⟨hβinj, hβs⟩), card_threeSpace hK4]
  norm_num

end CFSG.Quasithin.C124
