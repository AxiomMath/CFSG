module

public import CFSG.Sporadic.Co2Smith.DichTwist
public import CFSG.Sporadic.Co2Smith.Sp6Cover

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert CFSG.CosetTable

universe u

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

open scoped Classical in
@[expose] noncomputable def coverZ :
    PGcov :=
  if h : ∃ c : PGcov, covMap c = 1 ∧ c ≠ 1 then h.choose else 1

theorem covMap_coverZ :
    covMap coverZ = 1 := by
  rw [coverZ]
  split_ifs with h
  · exact h.choose_spec.1
  · exact map_one _

abbrev Hprime :
    Type := cfgCz.Twist covMap coverZ covMap_coverZ

theorem card_Shat
    (c₁ : LocalConfig.{u}) (c₂ : SmithConfig.{0}) :
    Nat.card (c₁.Shat c₂) = 2903040 := by
  have hker : Nat.card (c₁.piHat c₂).ker = 2 := by
    rw [Nat.card_eq_two_iff' 1]
    refine ⟨⟨c₁.zHat c₂, c₁.piHat_zHat c₂⟩, fun h => c₁.zHat_ne_one c₂ (congrArg Subtype.val h),
      fun y hy => ?_⟩
    rcases ((c₁.mem_ker_piHat_iff c₂ y).mp y.2) with h | h
    · exact absurd (Subtype.ext h) hy
    · exact Subtype.ext h
  rw [← Subgroup.card_mul_index (c₁.piHat c₂).ker, hker,
    Subgroup.index_ker, MonoidHom.range_eq_top.mpr (c₁.piHat_surjective c₂), Subgroup.card_top,
    card_S0]

theorem smith_dichotomy
    {H : Type u} [Group H] [Finite H] (hH : SmithLocal H) :
    Nonempty (H ≃* Cz) ∨ Nonempty (H ≃* Hprime) := by
  set c₁ := LocalConfig.ofLocal hH
  set c₂ := cfgCz
  have hker : ∀ t, c₁.piHat c₂ t = 1 ↔ t = 1 ∨ t = c₁.zHat c₂ := c₁.mem_ker_piHat_iff c₂
  rcases split_or_perfect (c₁.piHat c₂) (c₁.piHat_surjective c₂) (c₁.zHat c₂) hker with
    ⟨S', hz, hsurj⟩ | hperf
  · left
    obtain ⟨h1, h2⟩ := c₁.complement_of_split c₂ S' hz hsurj
    exact smith_local_bridge hH _ h1 h2
  · right
    have hc : (c₁.piHat c₂).ker ≤ Subgroup.center (c₁.Shat c₂) := by
      intro t ht
      rcases (hker t).mp ht with rfl | rfl
      · exact Subgroup.one_mem _
      · exact c₁.zHat_mem_center c₂
    obtain ⟨φ, hφ⟩ := exists_cover_hom (c₁.piHat c₂) (c₁.piHat_surjective c₂) hc
    have hφs := cover_hom_surjective (c₁.piHat c₂) hc hperf φ hφ
    have hφb : Function.Bijective φ :=
      hφs.bijective_of_nat_card_le (by rw [card_Shat]; exact card_PGcov_le)
    set β := MulEquiv.ofBijective φ hφb
    have hπ : ∀ x, c₁.piHat c₂ (β x) = covMap x := by
      intro x
      have e : (c₁.piHat c₂).comp φ = covMap :=
        PresentedGroup.ext fun i => by rw [MonoidHom.comp_apply, hφ, covMap_of]
      exact DFunLike.congr_fun e x
    have hz : coverZ = β.symm (c₁.zHat c₂) := by
      have hex : ∃ c : PGcov, covMap c = 1 ∧ c ≠ 1 :=
        ⟨β.symm (c₁.zHat c₂), by rw [← hπ, MulEquiv.apply_symm_apply, c₁.piHat_zHat c₂],
          fun h => c₁.zHat_ne_one c₂ (by rw [← β.apply_symm_apply (c₁.zHat c₂), h, map_one])⟩
      have hspec := hex.choose_spec
      have hcz : coverZ = hex.choose := by rw [coverZ, dite_eq_left hex]
      rw [hcz]
      have h1 : c₁.piHat c₂ (β hex.choose) = 1 := by rw [hπ, hspec.1]
      rcases (hker _).mp h1 with h | h
      · exact absurd ((map_eq_one_iff β β.injective).mp h) hspec.2
      · rw [← h, MulEquiv.symm_apply_apply]
    refine ⟨((c₁.twistEquiv c₂).symm.trans
      (c₂.twistCongr β.symm (fun t => by rw [← hπ, MulEquiv.apply_symm_apply])
        (c₁.piHat_zHat c₂) covMap_coverZ hz.symm))⟩

end CFSG.Sporadic.Co2Smith
