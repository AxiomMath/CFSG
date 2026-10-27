module

public import CFSG.Quasithin.H13.A6S13821M22a
public import CFSG.Quasithin.H13.A6S13821Hat6c
public import CFSG.Quasithin.H13.A6S13821g

public section

namespace CFSG.Quasithin.H13.A6.HatM22

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
  CFSG.ComponentClassification.PerfectAutomorphisms CFSG.ComponentClassification.WittDesign
open CFSG.Quasithin.H13.A6.Hat6 (Kq)
open CFSG.Quasithin.E1.LiftS5 (quotConj)

variable {G : Type} [Group G]

@[expose] noncomputable def piM {K : Subgroup G}
    (φ : Kq K ⧸ Subgroup.center (Kq K) ≃* M22) : ↥K →* M22 :=
  φ.toMonoidHom.comp ((QuotientGroup.mk' (Subgroup.center (Kq K))).comp
    (QuotientGroup.mk' (CFSG.pCore 2 ↥K)))

theorem piM_apply {K : Subgroup G} (φ : Kq K ⧸ Subgroup.center (Kq K) ≃* M22) (k : ↥K) :
    piM φ k = φ (QuotientGroup.mk (QuotientGroup.mk k : Kq K)) := rfl

theorem piM_surjective {K : Subgroup G} (φ : Kq K ⧸ Subgroup.center (Kq K) ≃* M22) :
    Function.Surjective (piM φ) :=
  φ.surjective.comp ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _))

@[expose] noncomputable def sigM {K : Subgroup G} (φ : Kq K ⧸ Subgroup.center (Kq K) ≃* M22) :
    ↥(Subgroup.normalizer (K : Set G)) →* MulAut M22 :=
  (MulAut.congr φ).toMonoidHom.comp ((centerQuotientHom (Kq K)).comp (quotConj K))

theorem sigM_piM {K : Subgroup G} (φ : Kq K ⧸ Subgroup.center (Kq K) ≃* M22)
    (g : ↥(Subgroup.normalizer (K : Set G))) (k : ↥K) :
    sigM φ g (piM φ k) = piM φ ⟨(g : G) * k * (g : G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp g.2 k).mp k.2⟩ := by
  show φ (centerQuotientHom (Kq K) (quotConj K g)
    (φ.symm (φ (QuotientGroup.mk (QuotientGroup.mk k : Kq K))))) = _
  rw [MulEquiv.symm_apply_apply, piM_apply]
  congr 1

theorem card_eq_of_isSylowTwoOf {S : Subgroup M22}
    (hS : IsSylowTwoOf S ⊤) : Nat.card S = 128 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hS.2.1
  have hidx : ¬ 2 ∣ S.index := by
    have h2 : ¬ 2 ∣ S.relIndex ⊤ := hS.2.2
    rwa [Subgroup.relIndex_top_right] at h2
  have hmul := Subgroup.card_mul_index S
  rw [hk, card_M22'] at hmul
  have hodd : Nat.Coprime 2 S.index := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hidx
  have h1 : 2 ^ 7 ∣ 2 ^ k * S.index := ⟨3465, by rw [hmul]; norm_num⟩
  have h2 : 2 ^ 7 ∣ 2 ^ k := (Nat.Coprime.pow_left 7 hodd).dvd_of_dvd_mul_right h1
  have h3 : 2 ^ k ∣ 2 ^ 7 * 3465 := ⟨S.index, by rw [hmul]; norm_num⟩
  have h4 : 2 ^ k ∣ 2 ^ 7 :=
    (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 3465)).dvd_of_dvd_mul_right h3
  rw [hk, Nat.dvd_antisymm h4 h2]
  norm_num

end CFSG.Quasithin.H13.A6.HatM22

namespace CFSG.Quasithin.H13.A6.Setting4

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
  CFSG.ComponentClassification.WittDesign MulAction
open CFSG.Quasithin.H13.A6.Hat6 (Kq)
open CFSG.Quasithin.H13.A6.HatM22
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem prime_dvd_card_L1_sup {X : Subgroup G}
    (hX2 : IsPGroup 2 X) (hXN : X ≤ Subgroup.normalizer (S.L1 : Set G)) {p : ℕ} (hp : p.Prime)
    (hpd : p ∣ Nat.card ↥(X ⊔ S.L1)) : p = 2 ∨ p = 3 := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := Subgroup.relIndex_mul_card S.L1 (X ⊔ S.L1)
  rw [inf_eq_left.mpr le_sup_right, A4.relIndex_sup_eq_of_le_normalizer' hXN] at h1
  rw [← h1] at hpd
  rcases (Nat.Prime.dvd_mul hp).mp hpd with h | h
  ·
    left
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hX2
    have h' := h.trans (Subgroup.relIndex_dvd_card (H := S.L1) (K := X))
    rw [hn] at h'
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h')
  ·
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥S.L1) p h
    obtain ⟨n, hn⟩ := pCoreOf_isPGroup 2 S.L1 ⟨_, S.cube_mem_pCoreOf_L1' x.2⟩
    have hn' : ((x : G) ^ 3) ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have hx' : x ^ (3 * 2 ^ n) = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, pow_mul]
      exact hn')
    have hpd' : p ∣ 3 * 2 ^ n := hx ▸ orderOf_dvd_of_pow_eq_one hx'
    rcases (Nat.Prime.dvd_mul hp).mp hpd' with h3 | h2
    · right
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3
    · left
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2)

theorem exists_hexad_hatM22
    (hS : S.Hyp138)
    {H : Subgroup G} (hH : H ∈ S.Hz) {K : Subgroup G} (hKn : H ≤ Subgroup.normalizer (K : Set G))
    (hK : K ∈ cComp H) (hL1K : S.L1 ≤ K) (φ : Kq K ⧸ Subgroup.center (Kq K) ≃* M22) :
    ∃ h₀ ∈ hexads, Nat.card ((T.subgroupOf K).map (piM φ)) = 128 ∧
      (T.subgroupOf K).map (piM φ) ≤ stabilizer M22 h₀ ∧
      (∀ (t : G) (ht : t ∈ T),
        (stabilizer M22 h₀).map (sigM φ ⟨t, hKn ((le_sup_right.trans hH.1.1) ht)⟩).toMonoidHom =
          stabilizer M22 h₀) ∧
      ∀ (l : G) (hl : l ∈ S.L1), piM φ ⟨l, hL1K hl⟩ ∈ stabilizer M22 h₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF := (hS.hF H hH).toHypF91
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hTsyl : IsSylowTwoOf (T ⊓ K) K := A4.isSylowTwoOf_inf_normal hF.sylow_H hKH hKn
  set U := T.subgroupOf K with hUdef
  have hU : IsSylowTwoOf U ⊤ := by
    refine ⟨le_top, hTsyl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTsyl.1).symm |>.of_equiv
      (MulEquiv.subgroupCongr (Subgroup.inf_subgroupOf_right T K)), ?_⟩
    show ¬ 2 ∣ U.relIndex ⊤
    rw [Subgroup.relIndex_top_right, hUdef, ← Subgroup.inf_subgroupOf_right T K]
    exact hTsyl.2.2
  set S₀ := U.map (piM φ) with hS₀
  have hS₀syl : IsSylowTwoOf S₀ ⊤ := A6S20.isSylowTwoOf_map_top (piM_surjective φ) hU
  have hS₀card : Nat.card S₀ = 128 := card_eq_of_isSylowTwoOf hS₀syl
  obtain ⟨h₀, hh₀, hS₀B⟩ := exists_hexad_le_stabilizer hS₀syl.2.1
  refine ⟨h₀, hh₀, hS₀card, hS₀B, fun t ht => ?_, fun l hl => ?_⟩
  ·
    set α := sigM φ ⟨t, hKn (hTH ht)⟩ with hα
    have hle : S₀.map α.toMonoidHom ≤ S₀ := by
      rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      have hu' : (u : G) ∈ T := Subgroup.mem_subgroupOf.mp hu
      refine ⟨⟨t * u * t⁻¹, (Subgroup.mem_normalizer_iff.mp (hKn (hTH ht)) u).mp u.2⟩,
        Subgroup.mem_subgroupOf.mpr (T.mul_mem (T.mul_mem ht hu') (T.inv_mem ht)), ?_⟩
      exact (sigM_piM φ ⟨t, hKn (hTH ht)⟩ u).symm
    have heq : S₀.map α.toMonoidHom = S₀ := Subgroup.eq_of_le_of_card_ge hle
      (le_of_eq (Subgroup.card_map_of_injective (K := S₀) (f := α.toMonoidHom)
        α.injective).symm)
    exact map_stabilizer_eq hS₀card hh₀ hS₀B α heq
  ·
    set X : Subgroup G := (T ⊓ K) ⊔ S.L1 with hX
    have hXK : X ≤ K := sup_le inf_le_right hL1K
    set P := (X.subgroupOf K).map (piM φ) with hP
    have hSP : S₀ ≤ P := Subgroup.map_mono fun u hu =>
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left ⟨Subgroup.mem_subgroupOf.mp hu, u.2⟩)
    have h23 : ∀ p : ℕ, p.Prime → p ∣ Nat.card P → p = 2 ∨ p = 3 := by
      intro p hp hpd
      have h1 : Nat.card P ∣ Nat.card X := by
        refine (Subgroup.card_map_dvd (X.subgroupOf K) (piM φ)).trans ?_
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXK).toEquiv]
      exact S.prime_dvd_card_L1_sup (hTsyl.2.1) (inf_le_left.trans S.T_le_normalizer_L1) hp
        (hpd.trans h1)
    have hPB := le_stabilizer_of_isTwoThree hS₀card hh₀ hS₀B hSP h23
    exact hPB ⟨⟨l, hL1K hl⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right hl), rfl⟩

end CFSG.Quasithin.H13.A6.Setting4
