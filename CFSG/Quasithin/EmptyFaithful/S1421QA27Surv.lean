module

public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.Background.A4Four

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace S1421QA27

variable {G : Type} [Group G]

theorem card_eq_card_oTwoQuot_mul (X : Subgroup G) :
    Nat.card ↥X = Nat.card (OTwoQuot X) * Nat.card ↥(pCoreOf 2 X) := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.Open.pCore 2 ↥X)
  have h3 : Nat.card ↥(pCoreOf 2 X) = Nat.card ↥(CFSG.Open.pCore 2 ↥X) :=
    Subgroup.card_map_of_injective X.subtype_injective
  rw [h3]
  exact h1

theorem card_K1_of_survivor4 {K1 : Subgroup G} (hq1 : IsL2Quot 3 (OTwoQuot K1))
    (hsp : IsSpecialPow 2 2 4 ↥(pCoreOf 2 K1)) : Nat.card ↥K1 = 258048 := by
  have h2 : Nat.card (OTwoQuot K1) = 2 ^ 3 * (4 ^ 3 - 1) := IsL2Quot.card (by norm_num) hq1
  have h4 : Nat.card ↥(pCoreOf 2 K1) = 2 ^ (1 + 2 * 4) := hsp.2.1
  rw [card_eq_card_oTwoQuot_mul, h2, h4]
  norm_num

theorem card_pCoreOf_of_survivor4 {K1 : Subgroup G} (hsp : IsSpecialPow 2 2 4 ↥(pCoreOf 2 K1)) :
    Nat.card ↥(pCoreOf 2 K1) = 512 := by
  rw [hsp.2.1]
  norm_num

theorem card_K1_of_two {K1 : Subgroup G} (hc : Nat.card (OTwoQuot K1) = 60)
    (hQ : IsQ8D8 ↥(pCoreOf 2 K1)) : Nat.card ↥K1 = 1920 := by
  rw [card_eq_card_oTwoQuot_mul, hc, hQ.1]

theorem omegaOneCenter_eq_zpowers {T : Subgroup G} {z : G} (hzZ : z ∈ quasithinOmegaOneCenter T)
    (hZ : ∀ g ∈ quasithinOmegaOneCenter T, g = 1 ∨ g = z) :
    quasithinOmegaOneCenter T = Subgroup.zpowers z := by
  refine le_antisymm (fun g hg => ?_) (Subgroup.zpowers_le.mpr hzZ)
  rcases hZ g hg with h | h
  · rw [h]; exact one_mem _
  · rw [h]; exact Subgroup.mem_zpowers z

theorem exists_card_sup_eq [Finite G] {K S : Subgroup G} (hS : IsPGroup 2 S)
    (hn : S ≤ Subgroup.normalizer (K : Set G)) :
    ∃ j : ℕ, Nat.card ↥(K ⊔ S) = Nat.card ↥K * 2 ^ j := by
  have hX : K ⊔ S ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hn
  have hnorm : (K.subgroupOf (K ⊔ S)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hX
  let f : ↥S →* ↥(K ⊔ S) ⧸ K.subgroupOf (K ⊔ S) :=
    (QuotientGroup.mk' (K.subgroupOf (K ⊔ S))).comp (Subgroup.inclusion le_sup_right)
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨a, ha, b, hb, hx⟩ := (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes hn).mp x.2
    refine ⟨⟨b, hb⟩, ?_⟩
    show (QuotientGroup.mk (Subgroup.inclusion le_sup_right ⟨b, hb⟩) :
      ↥(K ⊔ S) ⧸ K.subgroupOf (K ⊔ S)) = QuotientGroup.mk x
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h1 : b⁻¹ * a * b⁻¹⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hn (S.inv_mem hb)) a).mp ha
    have e : (((Subgroup.inclusion le_sup_right ⟨b, hb⟩)⁻¹ * x : ↥(K ⊔ S)) : G) =
        b⁻¹ * a * b⁻¹⁻¹ := by
      simp [hx, mul_assoc]
    rw [e]
    exact h1
  have hq2 : IsPGroup 2 (↥(K ⊔ S) ⧸ K.subgroupOf (K ⊔ S)) := hS.of_surjective f hf
  obtain ⟨j, hj⟩ := hq2.exists_card_eq
  refine ⟨j, ?_⟩
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (K.subgroupOf (K ⊔ S))
  have h2 : Nat.card ↥(K.subgroupOf (K ⊔ S)) = Nat.card ↥K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv
  rw [h1, hj, h2, mul_comm]

section Emb

variable {K1 L2 S : Subgroup G}

theorem exists_emb_of_isAmalgamOfGroup {P : ∀ (Y : Type) [Group Y], Prop}
    (h : IsAmalgamOfGroup
      (RankTwoAmalgam.ofSubgroups (K1 ⊔ bigB K1 L2 S) (L2 ⊔ bigB K1 L2 S)) P) :
    ∃ (Y : Type) (_ : Group Y) (ψ : ↥(K1 ⊔ bigB K1 L2 S) →* Y), P Y ∧ Function.Injective ψ := by
  obtain ⟨Y, iY, hP, TY, M₁, M₂, -, ⟨φ⟩⟩ := h
  refine ⟨Y, iY, M₁.subtype.comp (φ.φ1.toMonoidHom : ↥(K1 ⊔ bigB K1 L2 S) →* ↥M₁), hP, ?_⟩
  exact Subtype.val_injective.comp φ.φ1.injective

theorem sup_le_sup_bigB : K1 ⊔ S ≤ K1 ⊔ bigB K1 L2 S :=
  sup_le_sup_left (le_sup_right : S ≤ bigB K1 L2 S) K1

end Emb

end S1421QA27

end CFSG.Quasithin
