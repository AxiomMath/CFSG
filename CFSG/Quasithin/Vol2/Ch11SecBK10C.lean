module

public import CFSG.Quasithin.Vol2.Ch11SecBK10B

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Quasithin CFSG.QuasithinUnique

namespace BK10

variable {G : Type} [Group G]

abbrev JBar (J : Subgroup G) : Type := ↥J ⧸ CFSG.pCore 2 ↥J

abbrev XCls (J : Subgroup G) : Type := JBar J ⧸ Subgroup.center (JBar J)

@[expose] noncomputable def piX (J : Subgroup G) : ↥J →* XCls J :=
  (QuotientGroup.mk' (Subgroup.center (JBar J))).comp (QuotientGroup.mk' (CFSG.pCore 2 ↥J))

@[expose] noncomputable def rhoX (J : Subgroup G) :
    ↥(Subgroup.normalizer (J : Set G)) →* MulAut (XCls J) :=
  (quotAut (Subgroup.center (JBar J))).comp
    ((quotAut (CFSG.pCore 2 ↥J)).comp J.normalizerMonoidHom)

theorem piX_surjective (J : Subgroup G) : Function.Surjective (piX J) :=
  (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)

theorem rhoX_piX (J : Subgroup G) (n : ↥(Subgroup.normalizer (J : Set G))) (j : ↥J) :
    rhoX J n (piX J j) = piX J ⟨n * j * n⁻¹, (Subgroup.mem_normalizer_iff.mp n.2 j).mp j.2⟩ :=
  rfl

theorem rhoX_of_mem (J : Subgroup G) {j : G} (hj : j ∈ J) :
    rhoX J ⟨j, Subgroup.le_normalizer hj⟩ = MulAut.conj (piX J ⟨j, hj⟩) := by
  ext x
  obtain ⟨z, rfl⟩ := piX_surjective J x
  rw [rhoX_piX, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  rfl

theorem isSylowTwoOf_map_piX [Finite G] {J S : Subgroup G} (hQ : IsSylowTwoOf (S ⊓ J) J) :
    IsSylowTwoOf ((S.subgroupOf J).map (piX J)) ⊤ := by
  obtain ⟨-, h2, hidx⟩ := hQ
  refine ⟨le_top, ?_, ?_⟩
  · have h4 : IsPGroup 2 ((S ⊓ J).subgroupOf J) :=
      IsPGroup.of_equiv h2 (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
    rw [Subgroup.inf_subgroupOf_right] at h4
    exact h4.map _
  · intro h5
    apply hidx
    have h6 : ((S.subgroupOf J).map (piX J)).index ∣ (S.subgroupOf J).index :=
      Subgroup.index_map_dvd _ (piX_surjective J)
    have h7 : (((S.subgroupOf J).map (piX J)).subgroupOf ⊤).index =
        ((S.subgroupOf J).map (piX J)).index := by
      change ((S.subgroupOf J).map (piX J)).relIndex ⊤ = _
      exact Subgroup.relIndex_top_right _
    rw [h7] at h5
    rw [Subgroup.inf_subgroupOf_right]
    exact h5.trans h6

theorem not_isCoprimePrimeAut_of_invariant [Finite G] {J S D : Subgroup G} (hS2 : IsPGroup 2 S)
    (hSJ : S ≤ Subgroup.normalizer (J : Set G)) (hQ : IsSylowTwoOf (S ⊓ J) J)
    (hD : Lin2.IsHallTwoPrimeOf D (J ⊓ Subgroup.normalizer (S : Set G)))
    (hT : TorusRigid (XCls J)) {c : G} (hc : c ∈ Subgroup.normalizer (J : Set G))
    (hcD : ∀ d ∈ D, c * d * c⁻¹ = d) : ¬ IsCoprimePrimeAut (rhoX J ⟨c, hc⟩) := by
  set P := (S.subgroupOf J).map (piX J) with hPdef
  have hP := isSylowTwoOf_map_piX hQ
  have hρP : ∀ s (hs : s ∈ S), ∀ x ∈ P, rhoX J ⟨s, hSJ hs⟩ x ∈ P := by
    rintro s hs _ ⟨q, hq, rfl⟩
    rw [rhoX_piX]
    refine ⟨_, ?_, rfl⟩
    change s * (q : G) * s⁻¹ ∈ S
    exact S.mul_mem (S.mul_mem hs hq) (S.inv_mem hs)
  have hρP' : ∀ s (hs : s ∈ S), ∀ x, x ∈ P ↔ rhoX J ⟨s, hSJ hs⟩ x ∈ P := by
    intro s hs x
    refine ⟨hρP s hs x, fun hx => ?_⟩
    have h1 := hρP s⁻¹ (S.inv_mem hs) _ hx
    have h2 : rhoX J ⟨s⁻¹, hSJ (S.inv_mem hs)⟩ (rhoX J ⟨s, hSJ hs⟩ x) = x := by
      rw [← MulAut.mul_apply, ← map_mul]
      have h3 : (⟨s⁻¹, hSJ (S.inv_mem hs)⟩ : ↥(Subgroup.normalizer (J : Set G))) *
          ⟨s, hSJ hs⟩ = 1 := Subtype.ext (inv_mul_cancel s)
      rw [h3, map_one, MulAut.one_apply]
    rwa [h2] at h1
  set Sh := (S.subgroupOf (Subgroup.normalizer (J : Set G))).map (rhoX J) with hSh
  have hSh2 : IsPGroup 2 Sh :=
    (IsPGroup.of_equiv hS2 (Subgroup.subgroupOfEquivOfLe hSJ).symm).map _
  have hSP : ∀ p ∈ P, MulAut.conj p ∈ Sh := by
    rintro _ ⟨q, hq, rfl⟩
    rw [← rhoX_of_mem J q.2]
    exact ⟨_, hq, rfl⟩
  have hSs : ∀ s ∈ Sh, ∀ x, x ∈ P ↔ s x ∈ P := by
    rintro _ ⟨s, hs, rfl⟩ x
    exact hρP' s hs x
  obtain ⟨y, hyS, -, hyrig⟩ := hT P hP Sh hSh2 hSP hSs
  obtain ⟨b, rfl⟩ := piX_surjective J y
  set R := (P.comap (piX J)).map J.subtype with hRdef
  have hRY : R ≤ J := Subgroup.map_subtype_le _
  have hmemR : ∀ z (hz : z ∈ J), z ∈ R ↔ piX J ⟨z, hz⟩ ∈ P := by
    intro z hz
    constructor
    · rintro ⟨z', hz', rfl⟩
      exact hz'
    · intro h
      exact ⟨⟨z, hz⟩, h, rfl⟩
  have hQR : S ⊓ J ≤ R := fun x hx => (hmemR x hx.2).mpr ⟨⟨x, hx.2⟩, hx.1, rfl⟩
  have hSR : S ≤ Subgroup.normalizer (R : Set G) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro z
    by_cases hz : z ∈ J
    · have hz' : s * z * s⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp (hSJ hs) z).mp hz
      rw [hmemR z hz, hmemR _ hz', hρP' s hs, rhoX_piX]
      exact Iff.rfl
    · have hz' : s * z * s⁻¹ ∉ J := fun h => hz ((Subgroup.mem_normalizer_iff.mp (hSJ hs) z).mpr h)
      exact ⟨fun h => absurd (hRY h) hz, fun h => absurd (hRY h) hz'⟩
  have hφR : ∀ z (hz : z ∈ R), piX J ⟨z, hRY hz⟩ ∈ P := fun z hz => (hmemR z (hRY hz)).mp hz
  have hbS : ∀ s ∈ S, s * (b : G) * s⁻¹ * (b : G)⁻¹ ∈ R := by
    intro s hs
    have hsb : s * (b : G) * s⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp (hSJ hs) b).mp b.2
    have hmem : s * (b : G) * s⁻¹ * (b : G)⁻¹ ∈ J := J.mul_mem hsb (J.inv_mem b.2)
    rw [hmemR _ hmem]
    have h1 := hyS _ ⟨⟨s, hSJ hs⟩, hs, rfl⟩
    rw [rhoX_piX] at h1
    have h2 : piX J ⟨s * (b : G) * s⁻¹ * (b : G)⁻¹, hmem⟩ =
        (piX J b * (piX J ⟨s * (b : G) * s⁻¹, hsb⟩)⁻¹)⁻¹ := by
      rw [mul_inv_rev, inv_inv, ← map_inv, ← map_mul]
      rfl
    rw [h2]
    exact P.inv_mem h1
  have hβD : ∀ z (hz : z ∈ D), rhoX J ⟨c, hc⟩ (piX J ⟨z, (hD.1 hz).1⟩) =
      piX J ⟨z, (hD.1 hz).1⟩ := by
    intro z hz
    rw [rhoX_piX]
    congr 1
    exact Subtype.ext (hcD z hz)
  exact not_isCoprimePrimeAut_of_lift hS2 hQ hQR hRY hSR hD (piX J) hφR hyrig b.2 rfl hbS hβD

end BK10

end CFSG.Quasithin.Vol2.Ch11.SecD
