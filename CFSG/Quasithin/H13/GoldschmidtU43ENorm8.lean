module

public import CFSG.Quasithin.H13.GoldschmidtU43ENorm3
public import CFSG.Quasithin.H13.GoldschmidtU43ENorm5

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

namespace JWSetup

variable [Finite G] {z : G} (S : JWSetup z)

noncomputable abbrev piN : ↥S.Ng →* S.Nbar := QuotientGroup.mk' (S.Mg.subgroupOf S.Ng)

noncomputable abbrev Dbar : Subgroup S.Nbar := (S.Dg.subgroupOf S.Ng).map S.piN

theorem piN_inj_on_Dg {d₁ d₂ : ↥S.Ng} (h₁ : (d₁ : G) ∈ S.Dg) (h₂ : (d₂ : G) ∈ S.Dg)
    (h : S.piN d₁ = S.piN d₂) : d₁ = d₂ := by
  have hm : d₁⁻¹ * d₂ ∈ S.Mg.subgroupOf S.Ng := QuotientGroup.eq.mp h
  have hD : ((d₁⁻¹ * d₂ : ↥S.Ng) : G) ∈ S.Dg := mul_mem (inv_mem h₁) h₂
  have h1 : ((d₁⁻¹ * d₂ : ↥S.Ng) : G) = 1 := S.Dg_inf_Mg hD hm
  have h1' : d₁⁻¹ * d₂ = 1 := Subtype.ext h1
  exact inv_mul_eq_one.mp h1'

noncomputable def DbarEquiv : ↥(S.Dg.subgroupOf S.Ng) ≃* ↥S.Dbar :=
  MulEquiv.ofBijective
    ((S.piN.comp (S.Dg.subgroupOf S.Ng).subtype).codRestrict S.Dbar fun d => ⟨d, d.2, rfl⟩)
    ⟨fun a b hab => Subtype.ext (S.piN_inj_on_Dg a.2 b.2 (congrArg Subtype.val hab)),
      fun y => by
        obtain ⟨d, hd, hdy⟩ := y.2
        exact ⟨⟨d, hd⟩, Subtype.ext hdy⟩⟩

theorem card_Dbar : Nat.card S.Dbar = 8 := by
  rw [← Nat.card_congr S.DbarEquiv.toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe S.Dg_le_Ng).toEquiv, S.card_Dg]

theorem exists_dihedral_Dbar : Nonempty (↥S.Dbar ≃* DihedralGroup 4) := by
  obtain ⟨e, -, -⟩ := S.exists_dihedral_Dg
  exact ⟨(S.DbarEquiv.symm.trans (Subgroup.subgroupOfEquivOfLe S.Dg_le_Ng)).trans e.symm⟩

theorem exists_sylow_Dbar : ∃ P : Sylow 2 S.Nbar, (P : Subgroup S.Nbar) = S.Dbar := by
  obtain ⟨P2, hP2⟩ := S.exists_sylow_Dg
  refine ⟨P2.mapSurjective (QuotientGroup.mk'_surjective _), ?_⟩
  rw [Sylow.coe_mapSurjective, hP2]

theorem hasDihedralSylowTwo_Nbar : CFSG.GorensteinWalter.HasDihedralSylowTwo S.Nbar := by
  intro Q
  obtain ⟨P, hP⟩ := S.exists_sylow_Dbar
  obtain ⟨eD⟩ := S.exists_dihedral_Dbar
  have h4 : (2 : ℕ) ^ 2 = 4 := by norm_num
  refine ⟨2, by norm_num, ?_⟩
  rw [h4]
  exact ⟨(Sylow.equiv Q P).trans ((MulEquiv.subgroupCongr hP).trans eD)⟩

theorem two_part_Nbar : 2 ^ 3 ∣ Nat.card S.Nbar ∧ ¬ 2 ^ 4 ∣ Nat.card S.Nbar := by
  obtain ⟨P, hP⟩ := S.exists_sylow_Dbar
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card P = 8 := by
    have : Nat.card (P : Subgroup S.Nbar) = Nat.card S.Dbar := by rw [hP]
    rw [← S.card_Dbar]
    exact this
  rw [Sylow.card_eq_multiplicity] at hcard
  have hf : (Nat.card S.Nbar).factorization 2 = 3 := by
    have h8 : (2 : ℕ) ^ (Nat.card S.Nbar).factorization 2 = 2 ^ 3 := hcard.trans (by norm_num)
    exact Nat.pow_right_injective (le_refl 2) h8
  have hne : Nat.card S.Nbar ≠ 0 := Nat.card_pos.ne'
  refine ⟨?_, ?_⟩
  · have := Nat.ordProj_dvd (Nat.card S.Nbar) 2
    rwa [hf] at this
  · have := Nat.pow_succ_factorization_not_dvd hne Nat.prime_two
    rwa [hf] at this

end JWSetup

end CFSG.Quasithin.H13.U43
