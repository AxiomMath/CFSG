module

public import CFSG.RankThree.PartOne.TCX.Plane
public import CFSG.RankThree.PartOne.KF.F4Torus
public import CFSG.LieType.Ree.SmallReeOuterThreeKernel
public import CFSG.LieType.Ree.LargeReeInvolutionTCentralizer
public import CFSG.RankThree.PartOne.K1214.OmegaAlg
public import CFSG.RankThree.PartOne.KF.G2Torus

public section

namespace CFSG.RankThree.PartOne.TCX.Ree

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.LargeReeInvolution CFSG.LieType.Ree.LargeReeCover CFSG.RankThree.PartOne.KFU
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}

omit [Finite K] [CharP K ReeTag.F4.prime] in
theorem entrywise_torusPair (σ : K ≃+* K) (u v : Kˣ) :
    Units.map (entrywiseHom σ.toRingHom) (torusPair a (u, v)) =
      torusPair a (Units.map σ.toRingHom.toMonoidHom u, Units.map σ.toRingHom.toMonoidHom v) := by
  simp only [torusPair_apply, map_mul, entrywise_torusElt σ, map_pow]

theorem ree_plane_split (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime) (σ : K ≃+* K)
    (hσfix : ∀ ζ : Kˣ, ζ ^ p = 1 → Units.map σ.toRingHom.toMonoidHom ζ = ζ)
    (hpK : p ∣ Nat.card K - 1) :
    ∃ R U : Subgroup (ReeTag.F4.reeGamma K a),
      IsElementaryAbelian p ↥R ∧ Nat.card ↥R = p ^ 2 ∧
        (∀ r ∈ R, ReeTag.F4.reeGammaFieldAut K a σ r = r) ∧ U ≠ ⊥ ∧ IsPGroup 2 ↥U ∧
        (∀ u ∈ U, ReeTag.F4.reeGammaFieldAut K a σ u ∈ U) ∧
        R ≤ Subgroup.normalizer (U : Set (ReeTag.F4.reeGamma K a)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (ReeTag.F4.prime.Prime) := ⟨by decide⟩
  have hK' : Nat.card K = ReeTag.F4.prime ^ (2 * a + 1) := hK
  have hdvd : p ∣ Nat.card Kˣ := by rw [Nat.card_units]; exact hpK
  obtain ⟨ζ, hζo⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hζp : ζ ^ p = 1 := by rw [← hζo]; exact pow_orderOf_eq_one ζ
  have hζ1 : ζ ≠ 1 := fun h => hp.one_lt.ne' (hζo.symm.trans (by rw [h, orderOf_one]))
  have hσζ := hσfix ζ hζp
  have hσ1 : Units.map σ.toRingHom.toMonoidHom (1 : Kˣ) = 1 := map_one _
  set u₁ : ReeTag.F4.reeGamma K a := ⟨torusPair a (ζ, 1), torusPair_mem_reeGamma a hK' _⟩ with hu₁
  set u₂ : ReeTag.F4.reeGamma K a := ⟨torusPair a (1, ζ), torusPair_mem_reeGamma a hK' _⟩ with hu₂
  have hpair₁ : ((ζ, 1) : Kˣ × Kˣ) ^ p = 1 := Prod.ext (by simpa using hζp) (by simp)
  have hpair₂ : ((1, ζ) : Kˣ × Kˣ) ^ p = 1 := Prod.ext (by simp) (by simpa using hζp)
  have hu₁p : u₁ ^ p = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow]
    change torusPair a (ζ, 1) ^ p = 1
    rw [← map_pow, hpair₁, map_one])
  have hu₂p : u₂ ^ p = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow]
    change torusPair a (1, ζ) ^ p = 1
    rw [← map_pow, hpair₂, map_one])
  have hu₁1 : u₁ ≠ 1 := fun h => hζ1 (torusPair_eq_one hK' (congrArg Subtype.val h)).1
  have hu₂1 : u₂ ≠ 1 := fun h => hζ1 (torusPair_eq_one hK' (congrArg Subtype.val h)).2
  have hu₁o : orderOf u₁ = p := orderOf_eq_prime hu₁p hu₁1
  have hu₂o : orderOf u₂ = p := orderOf_eq_prime hu₂p hu₂1
  have hcomm : Commute u₁ u₂ := Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    change torusPair a (ζ, 1) * torusPair a (1, ζ) = torusPair a (1, ζ) * torusPair a (ζ, 1)
    rw [← map_mul, ← map_mul]
    congr 1
    ext <;> simp [mul_comm])
  have hind : u₂ ∉ Subgroup.zpowers u₁ := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have h1 : torusPair a (ζ ^ k, 1) = torusPair a (1, ζ) := by
      have := congrArg Subtype.val hk
      rw [Subgroup.coe_zpow] at this
      change (torusPair a (ζ, 1)) ^ k = torusPair a (1, ζ) at this
      rw [← map_zpow] at this
      simpa using this
    have h2 : torusPair a ((ζ ^ k)⁻¹, ζ) = 1 := by
      have : ((ζ ^ k)⁻¹, ζ) = (ζ ^ k, (1 : Kˣ))⁻¹ * (1, ζ) := by ext <;> simp
      rw [this, map_mul, map_inv, h1, inv_mul_cancel]
    exact hζ1 (torusPair_eq_one hK' h2).2
  have hfix : ∀ t : Kˣ × Kˣ, (∀ ξ : Kˣ, ξ ^ p = 1 → Units.map σ.toRingHom.toMonoidHom ξ = ξ) →
      t.1 ^ p = 1 → t.2 ^ p = 1 →
      ReeTag.F4.reeGammaFieldAut K a σ ⟨torusPair a t, torusPair_mem_reeGamma a hK' t⟩ =
        ⟨torusPair a t, torusPair_mem_reeGamma a hK' t⟩ := by
    intro t hσ h1 h2
    refine Subtype.ext ?_
    rw [ReeTag.coe_reeGammaFieldAut, entrywise_torusPair, hσ t.1 h1, hσ t.2 h2]
  have hfu₁ : ReeTag.F4.reeGammaFieldAut K a σ u₁ = u₁ :=
    hfix (ζ, 1) hσfix hζp (one_pow p)
  have hfu₂ : ReeTag.F4.reeGammaFieldAut K a σ u₂ = u₂ :=
    hfix (1, ζ) hσfix (one_pow p) hζp
  have hUC : ReeTag.F4.reeFixedPosUnipotent K a ≤ ReeTag.F4.reeGamma K a := inf_le_right
  refine ⟨Subgroup.closure ({u₁, u₂} : Set (ReeTag.F4.reeGamma K a)),
    (ReeTag.F4.reeFixedPosUnipotent K a).subgroupOf (ReeTag.F4.reeGamma K a), ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · refine CFSG.RankThree.PartOne.K1214.isElementaryAbelian_closure (fun x hx y hy => ?_)
      (fun x hx => ?_)
    · rcases hx with hx | hx <;> rcases hy with hy | hy <;> rw [hx, hy]
      · exact hcomm.eq
      · exact hcomm.eq.symm
    · rcases hx with hx | hx <;> rw [hx]
      · rw [← hu₁o]; exact pow_orderOf_eq_one _
      · rw [← hu₂o]; exact pow_orderOf_eq_one _
  · exact card_closure_pair hp hcomm hu₁o hu₂o hind
  · intro r hr
    have hle : Subgroup.closure ({u₁, u₂} : Set (ReeTag.F4.reeGamma K a)) ≤
        (ReeTag.F4.reeGammaFieldAut K a σ).toMonoidHom.eqLocus (MonoidHom.id _) := by
      rw [Subgroup.closure_le]
      rintro x (hx | hx) <;> rw [hx]
      · exact hfu₁
      · exact hfu₂
    exact hle hr
  · intro hU
    have hne : ReeTag.F4.reeFixedPosUnipotent K a ≠ ⊥ := by
      intro hbot
      have hc := card_reeFixedPosUnipotent (K := K) (a := a) hK
      rw [hbot, Subgroup.card_bot] at hc
      have h2 : 1 < (2 ^ (2 * a + 1)) ^ 12 := by
        refine Nat.one_lt_pow (by norm_num) (Nat.one_lt_pow (by omega) (by norm_num))
      omega
    apply hne
    rw [eq_bot_iff]
    intro y hy
    have : (⟨y, hUC hy⟩ : ReeTag.F4.reeGamma K a) ∈
        (ReeTag.F4.reeFixedPosUnipotent K a).subgroupOf (ReeTag.F4.reeGamma K a) := hy
    rw [hU, Subgroup.mem_bot] at this
    exact (Subgroup.mem_bot).2 (congrArg Subtype.val this)
  · exact ((isPGroup_posUnipotent ReeTag.F4.prime ReeTag.F4.tag).to_le
      (inf_le_left : ReeTag.F4.reeFixedPosUnipotent K a ≤ _)).of_equiv
        (Subgroup.subgroupOfEquivOfLe hUC).symm
  · intro u hu
    have hX := ReeTag.map_reeFixedPosUnipotent_exactEntrywiseAut (t := ReeTag.F4) (K := K) (a := a) σ
    have h1 : ((ReeTag.F4.reeGammaFieldAut K a σ u : ReeTag.F4.reeGamma K a) :
        ModGL ReeTag.F4.tag K) ∈ ReeTag.F4.reeFixedPosUnipotent K a := by
      rw [← hX]
      exact ⟨(u : ModGL ReeTag.F4.tag K), hu, rfl⟩
    exact h1
  · rw [Subgroup.closure_le]
    have hnormal : ∀ u : ReeTag.F4.reeGamma K a,
        (u : ModGL ReeTag.F4.tag K) ∈ ReeTag.F4.reeFixedTorus K a →
        u ∈ Subgroup.normalizer (((ReeTag.F4.reeFixedPosUnipotent K a).subgroupOf
          (ReeTag.F4.reeGamma K a) : Subgroup (ReeTag.F4.reeGamma K a)) :
            Set (ReeTag.F4.reeGamma K a)) := fun u hu => by
      have h1 : u ∈ (Subgroup.normalizer (ReeTag.F4.reeFixedPosUnipotent K a :
          Set (ModGL ReeTag.F4.tag K))).subgroupOf (ReeTag.F4.reeGamma K a) :=
        ReeTag.reeFixedTorus_le_normalizer_reeFixedPosUnipotent hu
      rwa [Subgroup.subgroupOf_normalizer_eq hUC] at h1
    rintro x (hx | hx) <;> rw [hx]
    · exact hnormal u₁ (rankOne_torusPair_mem_reeFixedTorus hK' ζ 1)
    · exact hnormal u₂ (rankOne_torusPair_mem_reeFixedTorus hK' 1 ζ)

end CFSG.RankThree.PartOne.TCX.Ree
