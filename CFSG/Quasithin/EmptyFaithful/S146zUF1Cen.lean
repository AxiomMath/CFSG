module

public import CFSG.Quasithin.EmptyFaithful.S146zRPair
public import CFSG.Quasithin.EmptyFaithful.S146zUF1Pkg

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

namespace S146zU

namespace UF1

section Cover

variable {G : Type} [Group G] [Finite G]

theorem hcen_of_cover {G₁ T K₁ : Subgroup G} {s : G} (hT : IsPGroup 2 T) (hK₁ : K₁ ∈ cComp G₁)
    (hsT : s ∈ T) (hsN : s ∉ Subgroup.normalizer (K₁ : Set G))
    (hK₂ : conjSub s K₁ ∈ cComp G₁) (hKz : conjClosure K₁ T = K₁ ⊔ conjSub s K₁)
    (hK₀ : conjClosure K₁ T ⊔ T = G₁)
    (e : Nonempty (OTwoQuot K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 4))) :
    ∀ g ∈ G₁, (∀ k ∈ conjClosure K₁ T, g * k * g⁻¹ * k⁻¹ ∈ pCoreOf 2 G₁) →
      g ∈ pCoreOf 2 G₁ := by
  classical
  have hTG : T ≤ G₁ := hK₀ ▸ le_sup_right
  have hsG : s ∈ G₁ := hTG hsT
  have hK₁G : K₁ ≤ G₁ := le_of_mem_cComp hK₁
  have hK₂G : conjSub s K₁ ≤ G₁ := le_of_mem_cComp hK₂
  have hK₀G : conjClosure K₁ T ≤ G₁ := hK₀ ▸ le_sup_left
  have hK₀n : G₁ ≤ Subgroup.normalizer (conjClosure K₁ T : Set G) :=
    hK₀ ▸ sup_le Subgroup.le_normalizer (le_normalizer_conjClosure K₁ T)
  obtain ⟨e'⟩ := e
  obtain ⟨eimg⟩ := q_oTwoQuot_equiv_image (subnormal_of_mem_cComp hK₁)
  have : IsSimpleGroup SBc16.L216 := SBc16.isSimpleGroup_L216
  have hs : IsSimpleGroup ↥(imageOTwoQuot G₁ K₁) := (eimg.symm.trans e').isSimpleGroup
  have hne : K₁ ≠ conjSub s K₁ := fun h => hsN (CosetGeom.mem_normalizer_of_conjSub_eq h.symm)
  have h12 : conjSub s K₁ ≤ Subgroup.normalizer (K₁ : Set G) :=
    le_sup_right.trans (SBc16.sup_le_normalizer_of_mem_cComp hK₁ hK₂)
  have h21 : K₁ ≤ Subgroup.normalizer (conjSub s K₁ : Set G) :=
    le_sup_right.trans (SBc16.sup_le_normalizer_of_mem_cComp hK₂ hK₁)
  obtain ⟨hcomm, -⟩ := q_pair_comm_disjoint hK₁ hK₂ hne hs h12 h21
  have hconj : imageOTwoQuot G₁ (conjSub s K₁) =
      (imageOTwoQuot G₁ K₁).map (MulAut.conj (qPi G₁ ⟨s, hsG⟩)).toMonoidHom :=
    q_image_conjSub hsG
  have hZ₁ : ∀ n ∈ imageOTwoQuot G₁ K₁, (∀ m ∈ imageOTwoQuot G₁ K₁, n * m = m * n) → n = 1 :=
    centreless_of_L216Cover ⟨eimg.symm.trans e'⟩
  have hZ₂ : ∀ n ∈ imageOTwoQuot G₁ (conjSub s K₁),
      (∀ m ∈ imageOTwoQuot G₁ (conjSub s K₁), n * m = m * n) → n = 1 := by
    rw [hconj]
    exact q_centreless_conj hZ₁ _
  have hZ := q_centreless_sup hcomm hZ₁ hZ₂
  set N := imageOTwoQuot G₁ (conjClosure K₁ T) with hNdef
  have hN : N = imageOTwoQuot G₁ K₁ ⊔ imageOTwoQuot G₁ (conjSub s K₁) := by
    rw [hNdef, hKz, q_image_sup hK₁G hK₂G]
  have hZN : ∀ n ∈ N, (∀ m ∈ N, n * m = m * n) → n = 1 := by
    rw [hN]
    exact hZ
  have hNn : N.Normal := q_normal_image_of_normal hK₀G hK₀n
  have hpow : ∀ x : OTwoQuot G₁, ∃ k : ℕ, x ^ 2 ^ k ∈ N := by
    intro x
    obtain ⟨y, rfl⟩ := qPi_surjective G₁ x
    obtain ⟨k, hk⟩ := S153M.exists_two_pow_mem hK₀.symm hT (le_normalizer_conjClosure K₁ T) y
    exact ⟨k, ⟨y ^ 2 ^ k, hk, (map_pow (qPi G₁) y (2 ^ k)).symm⟩⟩
  set C : Subgroup (OTwoQuot G₁) := Subgroup.centralizer (N : Set (OTwoQuot G₁)) with hC
  have hCn : C.Normal := Subgroup.normal_centralizer
  have hC2 : IsPGroup 2 C := by
    intro c
    obtain ⟨k, hk⟩ := hpow (c : OTwoQuot G₁)
    have hck : ((c : OTwoQuot G₁) ^ 2 ^ k) ∈ C := C.pow_mem c.2 _
    have h1 : (c : OTwoQuot G₁) ^ 2 ^ k = 1 := hZN _ hk fun m hm =>
      (Subgroup.mem_centralizer_iff.mp hck m hm).symm
    exact ⟨k, Subtype.ext h1⟩
  have hCle : C ≤ CFSG.Open.pCore 2 (OTwoQuot G₁) := le_pCore 2 hCn hC2
  rw [q_pCore_two_quotient_eq_bot G₁, le_bot_iff] at hCle
  intro g hg hcg
  have hĝ : qPi G₁ ⟨g, hg⟩ ∈ C := by
    rw [hC, Subgroup.mem_centralizer_iff]
    rintro _ ⟨κ, hκ, rfl⟩
    have hmem : (⟨g, hg⟩ : ↥G₁) * κ * (⟨g, hg⟩ : ↥G₁)⁻¹ * κ⁻¹ ∈ CFSG.Open.pCore 2 ↥G₁ :=
      (mem_openPCore_iff_mem_pCoreOf _).mpr (hcg (κ : G) (Subgroup.mem_subgroupOf.mp hκ))
    have h1 : qPi G₁ ((⟨g, hg⟩ : ↥G₁) * κ * (⟨g, hg⟩ : ↥G₁)⁻¹ * κ⁻¹) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hmem
    simp only [map_mul, map_inv] at h1
    have h2 := mul_inv_eq_one.mp h1
    exact (mul_inv_eq_iff_eq_mul.mp h2).symm
  rw [hCle, Subgroup.mem_bot] at hĝ
  exact (mem_openPCore_iff_mem_pCoreOf (⟨g, hg⟩ : ↥G₁)).mp
    ((QuotientGroup.eq_one_iff _).mp hĝ)

end Cover

end UF1

section Setting

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem hcen_of_setting (S : Setting146 G T M) {K₁ : Subgroup G} {s : G}
    (hK₁ : K₁ ∈ cComp (mcOf T)) (hsT : s ∈ T) (hsN : s ∉ Subgroup.normalizer (K₁ : Set G))
    (hK₂ : conjSub s K₁ ∈ cComp (mcOf T)) (hKz : conjClosure K₁ T = K₁ ⊔ conjSub s K₁)
    (hK₀ : conjClosure K₁ T ⊔ T = mcOf T)
    (e : Nonempty (OTwoQuot K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 4))) :
    ∀ g ∈ mcOf T, (∀ k ∈ conjClosure K₁ T, g * k * g⁻¹ * k⁻¹ ∈ pCoreOf 2 (mcOf T)) →
      g ∈ pCoreOf 2 (mcOf T) :=
  UF1.hcen_of_cover S.hyp.sylow.1 hK₁ hsT hsN hK₂ hKz hK₀ e

end Setting

end S146zU

end CFSG.Quasithin
