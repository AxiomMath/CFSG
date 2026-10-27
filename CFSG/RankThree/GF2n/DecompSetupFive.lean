module

public import CFSG.RankThree.GF2n.DecompSetupSz
public import Certificates.Certificate113

public section

namespace CFSG.RankThree.GF2n

open CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.GH74.Uniqueness.Bender

variable {G : Type} [Group G] [Finite G]

namespace DecompSetup

variable {A Ab L Lb M : Subgroup G} (S : DecompSetup A Ab L Lb M)
include S

variable [(M.subgroupOf (A ⊔ Ab)).Normal]
  (P : QuotPair ((A.subgroupOf (A ⊔ Ab)).map (QuotientGroup.mk' (M.subgroupOf (A ⊔ Ab))))
    ((Ab.subgroupOf (A ⊔ Ab)).map (QuotientGroup.mk' (M.subgroupOf (A ⊔ Ab)))))
include P

theorem exists_fpf_five {a : ℕ} (ha : 1 ≤ a)
    (e : ↥(A ⊔ Ab) ⧸ M.subgroupOf (A ⊔ Ab) ≃* ↥(Sz a)) :
    ∃ g : ↥(A ⊔ Ab), orderOf (QuotientGroup.mk' (M.subgroupOf (A ⊔ Ab)) g) = 5 ∧
      ∀ m ∈ M, (g : G) * m = m * g → m = 1 := by
  have hBT : BenderType (↥(A ⊔ Ab) ⧸ M.subgroupOf (A ⊔ Ab)) (2 * a + 1) 2 1 :=
    .suzuki a ha (e.trans (MulEquiv.subgroupCongr (szModel_eq_open_sz a).symm))
  have hS := P.strongWC
  have hT0 := P.ne_bot
  obtain ⟨x₀, hx₀⟩ := P.exists_conj_eq
  have hS' : StrongWC ((Ab.subgroupOf (A ⊔ Ab)).map
      (QuotientGroup.mk' (M.subgroupOf (A ⊔ Ab)))) := by
    rw [hx₀]
    exact GF2n.StrongWC.conj hS _
  have hwu : e.symm (SzExplicit.w a) * e.symm (SzExplicit.w a) = 1 := by
    rw [← map_mul, SzExplicit.w_mul_self, map_one]
  have huu : e.symm (SzExplicit.u a) * e.symm (SzExplicit.u a) = 1 := by
    rw [← map_mul, SzExplicit.u_mul_self, map_one]
  have hord5 : orderOf (e.symm (SzExplicit.w a) * e.symm (SzExplicit.u a)) = 5 := by
    rw [← map_mul, MulEquiv.orderOf_eq, SzExplicit.orderOf_w_mul_u]
  obtain ⟨t, ht, s', hs', hts⟩ := exists_mul_orderOf_eq hBT hS hT0 hS' P.ne_bot₁ P.ne hwu huu
    (by rw [hord5]; decide)
    (fun h => by rw [h, orderOf_one] at hord5; exact absurd hord5 (by decide))
  rw [hord5] at hts
  obtain ⟨a₁, ha₁, rfl⟩ := ht
  obtain ⟨b₁, hb₁, rfl⟩ := hs'
  have hsq : ∀ (z : ↥(A ⊔ Ab)), (z : G) * z ∈ M →
      QuotientGroup.mk' (M.subgroupOf (A ⊔ Ab)) z *
        QuotientGroup.mk' (M.subgroupOf (A ⊔ Ab)) z = 1 := fun z hz => by
    rw [← map_mul, mk_eq_one_iff]
    exact hz
  have hnot5 : ∀ y : ↥(A ⊔ Ab) ⧸ M.subgroupOf (A ⊔ Ab), y * y = 1 → orderOf y ≠ 5 := by
    intro y hy h5
    have := orderOf_dvd_of_pow_eq_one (show y ^ 2 = 1 by rw [sq]; exact hy)
    rw [h5] at this
    exact absurd this (by decide)
  have ha₁A : (a₁ : G) ∈ A := Subgroup.mem_subgroupOf.mp ha₁
  have hb₁A : (b₁ : G) ∈ Ab := Subgroup.mem_subgroupOf.mp hb₁
  have ha₁L : (a₁ : G) ∉ L := fun h => hnot5 _ (hsq b₁ (S.Lb_le_M (S.sq_Ab _ hb₁A)))
    (by rwa [(mk_eq_one_iff a₁).mpr (S.L_le_M h), one_mul] at hts)
  have hb₁L : (b₁ : G) ∉ Lb := fun h => hnot5 _ (hsq a₁ (S.L_le_M (S.sq_A _ ha₁A)))
    (by rwa [(mk_eq_one_iff b₁).mpr (S.Lb_le_M h), mul_one] at hts)
  refine ⟨a₁ * b₁, by rw [map_mul]; exact hts, fun m hm hmc => ?_⟩
  exact S.eq_one_of_commute_mul ha₁A ha₁L hb₁A hb₁L hm hmc

theorem card_modEq_one_of_sz {a : ℕ} (ha : 1 ≤ a)
    (e : ↥(A ⊔ Ab) ⧸ M.subgroupOf (A ⊔ Ab) ≃* ↥(Sz a)) : Nat.card M ≡ 1 [MOD 5] := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨g, hg5, hfpf⟩ := S.exists_fpf_five P ha e
  have hXN : A ⊔ Ab ≤ Subgroup.normalizer (M : Set G) := S.sup_le_normalizer
  have hg5' : (g : G) ^ 5 = 1 := by
    have h1 : (g : G) ^ 5 ∈ M := pow_mem_of_mk (by rw [← hg5]; exact pow_orderOf_eq_one _)
    exact hfpf _ h1 (by rw [← pow_succ', pow_succ])
  have hgo : orderOf (g : G) = 5 := by
    have hdvd := orderOf_dvd_of_pow_eq_one hg5'
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hdvd with h | h
    · exfalso
      have hg1 : (g : G) = 1 := orderOf_eq_one_iff.mp h
      have : g = 1 := Subtype.ext hg1
      rw [this, map_one, orderOf_one] at hg5
      exact absurd hg5 (by decide)
    · exact h
  have hZN : ∀ h ∈ Subgroup.zpowers (g : G), h ∈ Subgroup.normalizer (M : Set G) := fun h hh =>
    (Subgroup.zpowers_le.mpr (hXN g.2)) hh
  let act : MulAction ↥(Subgroup.zpowers (g : G)) ↥M :=
    { smul := fun h m => ⟨(h : G) * m * (h : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hZN h h.2) m).mp m.2⟩
      one_smul := fun m => Subtype.ext (by
        show ((1 : ↥(Subgroup.zpowers (g : G))) : G) * m *
          ((1 : ↥(Subgroup.zpowers (g : G))) : G)⁻¹ = m
        simp)
      mul_smul := fun h k m => Subtype.ext (by
        show ((h * k : ↥(Subgroup.zpowers (g : G))) : G) * m *
          ((h * k : ↥(Subgroup.zpowers (g : G))) : G)⁻¹ =
            (h : G) * ((k : G) * m * (k : G)⁻¹) * (h : G)⁻¹
        rw [Subgroup.coe_mul]
        group) }
  have hp : IsPGroup 5 ↥(Subgroup.zpowers (g : G)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hgo, pow_one])
  have hfix : Nat.card (MulAction.fixedPoints ↥(Subgroup.zpowers (g : G)) ↥M) = 1 := by
    rw [Nat.card_eq_one_iff_exists]
    refine ⟨⟨1, fun h => Subtype.ext (by
      show ((h : G)) * ((1 : ↥M) : G) * (h : G)⁻¹ = ((1 : ↥M) : G)
      simp)⟩, fun m => ?_⟩
    have hm := m.2 ⟨g, Subgroup.mem_zpowers _⟩
    have hm' : (g : G) * ((m : ↥M) : G) * (g : G)⁻¹ = ((m : ↥M) : G) := congrArg Subtype.val hm
    have h1 : ((m : ↥M) : G) = 1 := hfpf _ (m : ↥M).2 (by
      calc (g : G) * ((m : ↥M) : G) = (g : G) * ((m : ↥M) : G) * (g : G)⁻¹ * g := by group
        _ = ((m : ↥M) : G) * g := by rw [hm'])
    exact Subtype.ext (Subtype.ext h1)
  have := hp.card_modEq_card_fixedPoints ↥M
  rwa [hfix] at this

end DecompSetup

end CFSG.RankThree.GF2n
