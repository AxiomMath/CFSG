module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PrimeComplementCore
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GroupTheory.LocalCores.Fitting

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open Subgroup CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type*} [Group G]

local notation "Y" => primeComplementCore (G := G) 3

theorem pCore_three_eq_bot_of_isSimpleGroup [Finite G] (hs : IsSimpleGroup (G ⧸ Y))
    (hZ : center (G ⧸ Y) = ⊥) : CFSG.pCore 3 G = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP : IsPGroup 3 (CFSG.pCore 3 G) := CFSG.pCore_isPGroup
  have : (CFSG.pCore 3 G).Normal := CFSG.pCore_normal
  have : ((CFSG.pCore 3 G).map (QuotientGroup.mk' Y)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective Y)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((CFSG.pCore 3 G).map (QuotientGroup.mk' Y))
    with h | h
  ·
    have hle : CFSG.pCore 3 G ≤ Y := by
      rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    have hcop : Nat.Coprime 3 (Nat.card (CFSG.pCore 3 G)) :=
      Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hle) (primeComplementCore_coprime 3)
    rcases hP.card_eq_or_dvd with h1 | h3
    · exact Subgroup.card_eq_one.mp h1
    · exact absurd (Nat.Coprime.eq_one_of_dvd hcop h3) (by norm_num)
  ·
    exfalso
    have hq : IsPGroup 3 (G ⧸ Y) := by
      intro q
      have hq' : q ∈ (CFSG.pCore 3 G).map (QuotientGroup.mk' Y) := h ▸ Subgroup.mem_top q
      obtain ⟨x, hx, rfl⟩ := hq'
      obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
      refine ⟨k, ?_⟩
      have hk' : x ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
      rw [← map_pow, hk', map_one]
    have : Nontrivial (G ⧸ Y) := hs.toNontrivial
    exact (Subgroup.nontrivial_iff_ne_bot _).mp hq.center_nontrivial hZ

theorem component_le_or_sup_eq_top_of_isSimpleGroup (hs : IsSimpleGroup (G ⧸ Y))
    {K : Subgroup G} (hK : CFSG.IsComponent K) : K ≤ Y ∨ K ⊔ Y = ⊤ := by
  have hsn : (K.map (QuotientGroup.mk' Y)).IsSubnormal :=
    hK.2.map (QuotientGroup.mk'_surjective Y)
  rcases hsn.eq_bot_or_top_of_isSimpleGroup hs with h | h
  · left
    rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
  · right
    have := Subgroup.comap_map_eq (QuotientGroup.mk' Y) K
    rw [h, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
    exact this.symm

theorem nonempty_centerQuotient_mulEquiv_of_sup_eq_top (hs : IsSimpleGroup (G ⧸ Y))
    (hZ : center (G ⧸ Y) = ⊥) {K : Subgroup G} (hK : CFSG.IsComponent K) (hKY : K ⊔ Y = ⊤) :
    Nonempty (↥K ⧸ center ↥K ≃* G ⧸ Y) := by
  classical
  set π : G →* G ⧸ Y := QuotientGroup.mk' Y with hπ
  set φ : ↥K →* G ⧸ Y := π.comp K.subtype with hφ
  have hmapK : K.map π = ⊤ := by
    have h := congrArg (Subgroup.map π) hKY
    rwa [Subgroup.map_sup, Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective Y),
      hπ, QuotientGroup.map_mk'_self, sup_bot_eq] at h
  have hφs : Function.Surjective φ := by
    intro q
    have hq : q ∈ K.map π := by rw [hmapK]; trivial
    obtain ⟨k, hk, rfl⟩ := hq
    exact ⟨⟨k, hk⟩, rfl⟩
  have hkerφ : φ.ker = (Y).subgroupOf K := by
    ext k
    simp [hφ, hπ, Subgroup.mem_subgroupOf, QuotientGroup.eq_one_iff]
  have hZY : ∀ z : ↥K, z ∈ center ↥K → (z : G) ∈ Y := by
    intro z hz
    have hcent : φ z ∈ center (G ⧸ Y) := by
      rw [Subgroup.mem_center_iff]
      intro q
      obtain ⟨k, rfl⟩ := hφs q
      rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz k)]
    rw [hZ, Subgroup.mem_bot] at hcent
    have : z ∈ φ.ker := hcent
    rw [hkerφ, Subgroup.mem_subgroupOf] at this
    exact this
  have hYK : (Y).subgroupOf K ≤ center ↥K := by
    have hN : ((Y).subgroupOf K).Normal := Subgroup.Normal.subgroupOf inferInstance K
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hK.1 hN with h | h
    · exfalso
      have hKle : K ≤ Y := by
        intro k hk
        have : (⟨k, hk⟩ : ↥K) ∈ (Y).subgroupOf K := by rw [h]; trivial
        exact this
      have hYtop : Y = ⊤ := by rw [← hKY, sup_eq_right.mpr hKle]
      obtain ⟨a, b, hab⟩ := hs.toNontrivial.exists_pair_ne
      apply hab
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
      rw [QuotientGroup.eq, hYtop]
      trivial
    · exact h
  have hZeq : center ↥K = (Y).subgroupOf K := by
    refine le_antisymm (fun z hz => ?_) hYK
    rw [Subgroup.mem_subgroupOf]
    exact hZY z hz
  exact ⟨(QuotientGroup.quotientMulEquivOfEq (hZeq.trans hkerφ.symm)).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφs)⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
