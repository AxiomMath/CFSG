module

public import CFSG.Quasithin.EmptyFaithful.S152NBasic
public import CFSG.Quasithin.EmptyFaithful.S152Stmts
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace C1Pack12

section General

variable {G : Type} [Group G] [Finite G]

theorem oTwoUpper_sup_eq_of_sylow {T H : Subgroup G} (hT : IsSylowTwoOf T H) :
    oTwoUpper H ⊔ T = H := by
  classical
  have hKH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hNH : oTwoUpper H ⊔ T ≤ H := sup_le hKH hT.1
  refine le_antisymm hNH ?_
  have h1 : (oTwoUpper H ⊔ T).relIndex H ∣ T.relIndex H :=
    Subgroup.relIndex_dvd_of_le_left H le_sup_right
  have h2 : (oTwoUpper H ⊔ T).relIndex H ∣ (oTwoUpper H).relIndex H :=
    Subgroup.relIndex_dvd_of_le_left H le_sup_left
  have h3 : ∃ m : ℕ, (oTwoUpper H).relIndex H = 2 ^ m := by
    have hn : ((oTwoUpper H).subgroupOf H).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr (le_normalizer_oTwoUpper H)
    have hp : IsPGroup 2 (↥H ⧸ (oTwoUpper H).subgroupOf H) := by
      intro q
      obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper H h.2
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf.mpr hk
    obtain ⟨m, hm⟩ := hp.exists_card_eq
    exact ⟨m, by rw [Subgroup.relIndex, Subgroup.index_eq_card, hm]⟩
  obtain ⟨m, hm⟩ := h3
  rw [hm] at h2
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
  have hj0 : j = 0 := by
    by_contra hne
    apply hT.2.2
    have h2d : 2 ∣ (oTwoUpper H ⊔ T).relIndex H := by
      rw [hj]
      exact dvd_pow_self 2 hne
    exact h2d.trans h1
  rw [hj0, pow_zero] at hj
  exact Subgroup.relIndex_eq_one.mp hj

end General

section Standing

variable {G : Type} [Group G] [Finite G] {T Mc M H B : Subgroup G}

structure St12 (T Mc M H B : Subgroup G) : Prop where
  hs : Setting152 T Mc M
  hH : IsHStar T M H
  hB : B ∈ sigmaPrime T H (V154 T Mc M)
  iso : Nonempty (OTwoQuot H ≃* S152N.W3)
  hn : Notation15209Concl T Mc M H
  c11 : Lemma15211Concl T Mc M H B
  c19 : Lemma1519Concl T Mc M
  h5 : ∀ M₁ : Subgroup G, InM T M₁ ↔ (M₁ = M ∨ M₁ = Mc)

theorem St12.of_stages (h5 : StageLemma15205) (h1519 : StageLemma1519)
    (h15208 : StageLemma15208) (h15209 : StageNotation15209) (h15211 : StageLemma15211)
    (hs : Setting152 T Mc M) (hH : IsHStar T M H) (hB : B ∈ sigmaPrime T H (V154 T Mc M)) :
    St12 T Mc M H B :=
  ⟨hs, hH, hB, h15208 G T Mc M hs H hH, h15209 G T Mc M hs H hH, h15211 G T Mc M hs H hH B hB,
    h1519 G T Mc M hs.qtfe hs.mf hs.ce, h5 G T Mc M hs⟩

namespace St12

variable (s : St12 T Mc M H B)

include s

theorem T_le_H : T ≤ H := s.hH.1.1

theorem H_le_Mc : H ≤ Mc := s.hn.le_mc

theorem sylow : IsSylowTwoOf T H := S152N.isSylowTwoOf_hStar s.hs s.hH

theorem sup_eq : oTwoUpper H ⊔ T = H := oTwoUpper_sup_eq_of_sylow s.sylow

theorem unique : IsUniqueM H Mc :=
  ⟨⟨s.hs.qtfe.mc_max, s.H_le_Mc⟩, fun M' hM' => by
    have hTM' : InM T M' := ⟨hM'.1, s.T_le_H.trans hM'.2⟩
    rcases (s.h5 M').mp hTM' with h | h
    · exact absurd (h ▸ hM'.2) s.hH.2.1
    · exact h⟩

theorem H_le_normalizer :
    H ≤ Subgroup.normalizer ((⁅V154 T Mc M, B⁆ : Subgroup G) : Set G) := by
  rw [← s.sup_eq]
  exact sup_le (fun k hk => Subgroup.centralizer_le_normalizer _ (s.c11.centralizes hk))
    s.c11.normal

theorem normalizer_le :
    Subgroup.normalizer ((⁅V154 T Mc M, B⁆ : Subgroup G) : Set G) ≤ Mc := by
  have hZ2 : IsPGroup 2 (⁅V154 T Mc M, B⁆ : Subgroup G) :=
    IsPGroup.of_card (n := 2) (by rw [s.c11.card]; norm_num)
  have hZ1 : (⁅V154 T Mc M, B⁆ : Subgroup G) ≠ ⊥ := fun h => by
    have := s.c11.card
    rw [h, Subgroup.card_bot] at this
    omega
  obtain ⟨M'', hM'', hle⟩ := exists_maxTwoLocal_ge
    (L := Subgroup.normalizer ((⁅V154 T Mc M, B⁆ : Subgroup G) : Set G))
    ⟨_, hZ1, hZ2, rfl⟩
  have hHM'' : H ≤ M'' := s.H_le_normalizer.trans hle
  have hMc : M'' = Mc := s.unique.2 M'' ⟨hM'', hHM''⟩
  rw [hMc] at hle
  exact hle

end St12

end Standing

end C1Pack12

end CFSG.Quasithin
