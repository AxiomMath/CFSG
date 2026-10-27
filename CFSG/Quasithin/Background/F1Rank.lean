module

public import CFSG.Quasithin.Background.F1Cartan
public import CFSG.Quasithin.Background.F1Weak

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7

universe u

@[expose] def IsRankOneSylow (K : Type*) [Group K] : Prop :=
  ∀ T : Subgroup K, IsPGroup 2 T → ¬ 2 ∣ T.index →
    Subgroup.normalizer (T : Set K) ≠ ⊤ ∧
    (∀ M : Subgroup K, T ≤ M → M ≠ ⊤ → M ≤ Subgroup.normalizer (T : Set K)) ∧
    ∀ x ∈ Subgroup.normalizer (T : Set K), ∀ y ∈ Subgroup.normalizer (T : Set K),
      x * y * x⁻¹ * y⁻¹ ∈ T

theorem IsRankOneSylow.of_mulEquiv {K K' : Type*} [Group K] [Group K'] (e : K ≃* K')
    (h : IsRankOneSylow K) : IsRankOneSylow K' := by
  intro T' hp hodd
  set T : Subgroup K := T'.comap e.toMonoidHom with hT
  have hsurj : Function.Surjective e.toMonoidHom := e.surjective
  have hnorm : ∀ x : K, x ∈ Subgroup.normalizer (T : Set K) ↔
      e x ∈ Subgroup.normalizer (T' : Set K') := by
    intro x
    have := Subgroup.comap_normalizer_eq_of_surjective T' hsurj
    change x ∈ Subgroup.normalizer ((T'.comap e.toMonoidHom : Subgroup K) : Set K) ↔ _
    rw [← this]
    exact Iff.rfl
  have hpT : IsPGroup 2 T := hp.comap_of_injective e.toMonoidHom e.injective
  have hoddT : ¬ 2 ∣ T.index := by
    rw [hT, Subgroup.index_comap_of_surjective T' hsurj]
    exact hodd
  obtain ⟨h1, h2, h3⟩ := h T hpT hoddT
  refine ⟨?_, ?_, ?_⟩
  · intro htop
    apply h1
    rw [eq_top_iff]
    intro x _
    exact (hnorm x).mpr (htop ▸ Subgroup.mem_top _)
  · intro M' hM'T hM'top x' hx'
    have hMT : T ≤ M'.comap e.toMonoidHom := fun y hy => hM'T hy
    have hMtop : M'.comap e.toMonoidHom ≠ ⊤ := by
      intro htop
      apply hM'top
      rw [eq_top_iff]
      intro z _
      obtain ⟨y, rfl⟩ := hsurj z
      exact (Subgroup.mem_comap.mp (htop ▸ Subgroup.mem_top y))
    have := h2 _ hMT hMtop (show e.symm x' ∈ M'.comap e.toMonoidHom by simpa using hx')
    simpa using (hnorm (e.symm x')).mp this
  · intro x' hx' y' hy'
    have hx : e.symm x' ∈ Subgroup.normalizer (T : Set K) := (hnorm _).mpr (by simpa using hx')
    have hy : e.symm y' ∈ Subgroup.normalizer (T : Set K) := (hnorm _).mpr (by simpa using hy')
    have := h3 _ hx _ hy
    simpa using (Subgroup.mem_comap.mp this)

namespace F1

variable {G : Type u} [Group G] [Finite G]

theorem rankOneAt_of_isRankOneSylow {L T : Subgroup G} (hT : IsSylowTwoOf T L)
    (h : IsRankOneSylow (oTwoQuot ↥L)) : RankOneAt L T := by
  set π : ↥L →* oTwoQuot ↥L := QuotientGroup.mk' (pCore 2 ↥L) with hπ
  set T' : Subgroup ↥L := T.subgroupOf L with hT'
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker ≤ T' := by
    rw [hπ, QuotientGroup.ker_mk']
    intro x hx
    have h1 : (x : G) ∈ pCoreOf 2 L := (mem_pCore_iff_coe x).mp hx
    exact isSylowTwoOf_pCoreOf_le hT h1
  set Tb : Subgroup (oTwoQuot ↥L) := T'.map π with hTb
  have hTb2 : IsPGroup 2 Tb := (hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hT.1).symm).map π
  have hTbodd : ¬ 2 ∣ Tb.index := by
    rw [hTb, Subgroup.index_map_eq (f := π) (H := T') hsurj hker]
    exact hT.2.2
  obtain ⟨h1, h2, h3⟩ := h Tb hTb2 hTbodd
  have hmem : ∀ u : ↥L, π u ∈ Tb ↔ u ∈ T' := by
    intro u
    constructor
    · rintro ⟨t, ht, hπt⟩
      have hk : t⁻¹ * u ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hπt, inv_mul_cancel]
      have := T'.mul_mem ht (hker hk)
      simpa using this
    · intro hu
      exact ⟨u, hu, rfl⟩
  have hnorm : ∀ u : ↥L, u ∈ Subgroup.normalizer (T' : Set ↥L) ↔
      π u ∈ Subgroup.normalizer (Tb : Set (oTwoQuot ↥L)) := by
    intro u
    rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
    constructor
    · intro hu y
      obtain ⟨v, rfl⟩ := hsurj y
      rw [← map_inv, ← map_mul, ← map_mul, hmem, hmem]
      exact hu v
    · intro hu v
      have := hu (π v)
      rwa [← map_inv, ← map_mul, ← map_mul, hmem, hmem] at this
  have hbor : ∀ (g : G) (hg : g ∈ L), (⟨g, hg⟩ : ↥L) ∈ Subgroup.normalizer (T' : Set ↥L) ↔
      g ∈ Subgroup.normalizer (T : Set G) := by
    intro g hg
    have := normalizer_subgroupOf_eq (Li := L) (S := T)
    rw [inf_eq_left.mpr hT.1] at this
    rw [show Subgroup.normalizer (T' : Set ↥L) = (borelOf L T).subgroupOf L from this,
      Subgroup.mem_subgroupOf]
    show g ∈ L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) ↔ _
    rw [inf_eq_left.mpr hT.1]
    exact ⟨fun h => h.2, fun h => ⟨hg, h⟩⟩
  refine ⟨?_, ?_, ?_⟩
  · intro heq
    apply h1
    rw [eq_top_iff]
    intro k _
    obtain ⟨u, rfl⟩ := hsurj k
    refine (hnorm u).mp ?_
    have hu : (u : G) ∈ L ⊓ Subgroup.normalizer (T : Set G) := by
      rw [heq]
      exact u.2
    exact (hbor u u.2).mpr hu.2
  · intro M hTM hML hMne m hm
    set M' : Subgroup ↥L := M.subgroupOf L with hM'
    have hT'M' : T' ≤ M' := fun t ht => hTM ht
    have hMb : Tb ≤ M'.map π := Subgroup.map_mono hT'M'
    have hMtop : M'.map π ≠ ⊤ := by
      intro htop
      apply hMne
      apply le_antisymm hML
      intro l hl
      have h5 : π ⟨l, hl⟩ ∈ M'.map π := htop ▸ Subgroup.mem_top _
      obtain ⟨u, hu, hπu⟩ := h5
      have hk : u⁻¹ * ⟨l, hl⟩ ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hπu, inv_mul_cancel]
      have h8 := M'.mul_mem hu (hT'M' (hker hk))
      have h9 : (⟨l, hl⟩ : ↥L) ∈ M' := by simpa using h8
      exact h9
    have h6 := h2 (M'.map π) hMb hMtop
    have hmL : m ∈ L := hML hm
    have h7 : π ⟨m, hmL⟩ ∈ M'.map π := ⟨⟨m, hmL⟩, hm, rfl⟩
    exact (hbor m hmL).mp ((hnorm _).mpr (h6 h7))
  · intro x hx y hy
    have hxL : x ∈ L := hx.1
    have hyL : y ∈ L := hy.1
    have hx' : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.normalizer (T' : Set ↥L) := (hbor x hxL).mpr hx.2
    have hy' : (⟨y, hyL⟩ : ↥L) ∈ Subgroup.normalizer (T' : Set ↥L) := (hbor y hyL).mpr hy.2
    have h7 := h3 _ ((hnorm _).mp hx') _ ((hnorm _).mp hy')
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, hmem] at h7
    exact h7

end F1

@[expose] def RankOneListedFacts : Prop :=
  ∀ (K : Type u) [Group K], IsRankOneListed K → IsRankOneSylow K

theorem Hyp111R.of_hyp111 {G : Type u} [Group G] [Finite G] {L1 L2 S : Subgroup G}
    (hF : RankOneListedFacts.{u}) (h : Hyp111 L1 L2 S) : Hyp111R L1 L2 S :=
  ⟨h, F1.rankOneAt_of_isRankOneSylow h.h1.sylow (hF _ h.h1.listed),
    F1.rankOneAt_of_isRankOneSylow h.h2.sylow (hF _ h.h2.listed)⟩

theorem prop_F19_of_listed {G : Type u} [Group G] [Finite G] {L1 L2 S : Subgroup G}
    (hF : RankOneListedFacts.{u}) (h : Hyp111 L1 L2 S) :
    (L1 ⊔ bigB L1 L2 S) ⊓ (L2 ⊔ bigB L1 L2 S) = bigB L1 L2 S ∧
    IsWeakBNPair (L1 ⊔ bigB L1 L2 S) (L2 ⊔ bigB L1 L2 S) ∧
    coreIn (bigB L1 L2 S) (L1 ⊔ L2 ⊔ S) = ⊥ ∧
    ∃ c : (RankTwoAmalgam.ofSubgroups (L1 ⊔ bigB L1 L2 S) (L2 ⊔ bigB L1 L2 S)).Completion
        ↥(L1 ⊔ L2 ⊔ S), c.IsFaithful :=
  prop_F19 (Hyp111R.of_hyp111 hF h)

end CFSG.Quasithin
