module

public import CFSG.Quasithin.Background.F9Comp
public import CFSG.Quasithin.Background.A4Four
public import CFSG.LieType.BorelTits.Suzuki
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

section Img

variable {G : Type} [Group G] [Finite G]

@[expose] def qPi (G₁ : Subgroup G) : ↥G₁ →* OTwoQuot G₁ :=
  QuotientGroup.mk' (CFSG.Open.pCore 2 ↥G₁)

omit [Finite G] in
theorem qPi_surjective (G₁ : Subgroup G) : Function.Surjective (qPi G₁) :=
  QuotientGroup.mk'_surjective _

theorem qPi_ker_solvable (G₁ : Subgroup G) : Group.IsSolvable (qPi G₁).ker := by
  have h2 : IsPGroup 2 (qPi G₁).ker := by
    unfold qPi
    rw [QuotientGroup.ker_mk']
    exact CFSG.LieType.BorelTits.pCore_isPGroup 2
  have := h2.isNilpotent
  infer_instance

theorem q_ker_comp_eq_pCore {G₁ K : Subgroup G} (hK : IsSubnormal K G₁) :
    ((qPi G₁).comp (Subgroup.inclusion (A3.subnormal_le hK))).ker = CFSG.Open.pCore 2 ↥K := by
  have hKG : K ≤ G₁ := A3.subnormal_le hK
  set ι : ↥K →* ↥G₁ := Subgroup.inclusion hKG with hι
  set φ : ↥K →* OTwoQuot G₁ := (qPi G₁).comp ι with hφ
  have hmem : ∀ x : ↥K, φ x = 1 ↔ ι x ∈ CFSG.Open.pCore 2 ↥G₁ := fun x => by
    change (QuotientGroup.mk (ι x) : OTwoQuot G₁) = 1 ↔ _
    exact QuotientGroup.eq_one_iff _
  refine le_antisymm ?_ ?_
  · refine le_pCore 2 (MonoidHom.normal_ker φ) ?_
    have hle : φ.ker ≤ (CFSG.Open.pCore 2 ↥G₁).comap ι := fun x hx => (hmem x).mp hx
    exact ((CFSG.LieType.BorelTits.pCore_isPGroup 2).comap_of_injective ι
      (Subgroup.inclusion_injective hKG)).to_le hle
  · intro x hx
    have h1 : (x : G) ∈ pCoreOf 2 K := ⟨x, hx, rfl⟩
    have h2 : (x : G) ∈ pCoreOf 2 G₁ := pCoreOf_le_pCoreOf_of_isSubnormal hK h1
    obtain ⟨z, hz, hzx⟩ := h2
    have : z = ι x := Subtype.ext hzx
    rw [MonoidHom.mem_ker, hmem]
    exact this ▸ hz

omit [Finite G] in
theorem q_range_comp_eq_image {G₁ K : Subgroup G} (hKG : K ≤ G₁) :
    ((qPi G₁).comp (Subgroup.inclusion hKG)).range = imageOTwoQuot G₁ K := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨Subgroup.inclusion hKG x, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x.1, Subgroup.mem_subgroupOf.mp hx⟩, rfl⟩

theorem q_oTwoQuot_equiv_image {G₁ K : Subgroup G} (hK : IsSubnormal K G₁) :
    Nonempty (OTwoQuot K ≃* ↥(imageOTwoQuot G₁ K)) := by
  have hKG : K ≤ G₁ := A3.subnormal_le hK
  have hker := q_ker_comp_eq_pCore hK
  have hrange := q_range_comp_eq_image hKG
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivRange ((qPi G₁).comp (Subgroup.inclusion hKG)))).trans
      (MulEquiv.subgroupCongr hrange)⟩

theorem q_image_mem_cComp {G₁ K : Subgroup G} (hK : K ∈ cComp G₁) :
    imageOTwoQuot G₁ K ∈ cComp (⊤ : Subgroup (OTwoQuot G₁)) :=
  map_mem_cComp_top (qPi G₁) (qPi_surjective G₁) (qPi_ker_solvable G₁) (subgroupOf_mem_cComp hK)

theorem q_image_injOn {G₁ K L : Subgroup G} (hK : K ∈ cComp G₁) (hL : L ∈ cComp G₁)
    (h : imageOTwoQuot G₁ K = imageOTwoQuot G₁ L) : K = L := by
  have := map_injOn_cComp_top (qPi G₁) (qPi_ker_solvable G₁) (subgroupOf_mem_cComp hK)
    (subgroupOf_mem_cComp hL) h
  rw [← Subgroup.map_subgroupOf_eq_of_le (le_of_mem_cComp hK),
    ← Subgroup.map_subgroupOf_eq_of_le (le_of_mem_cComp hL)]
  exact congrArg (Subgroup.map G₁.subtype) this

theorem q_exists_cComp_of_cComp_top {G₁ : Subgroup G} {J : Subgroup (OTwoQuot G₁)}
    (hJ : J ∈ cComp (⊤ : Subgroup (OTwoQuot G₁))) :
    ∃ K ∈ cComp G₁, imageOTwoQuot G₁ K = J := by
  obtain ⟨K', hK', hKJ⟩ := map_surjOn_cComp_top (qPi G₁) (qPi_surjective G₁)
    (qPi_ker_solvable G₁) hJ
  refine ⟨K'.map G₁.subtype, map_subtype_mem_cComp hK', ?_⟩
  unfold imageOTwoQuot
  rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective G₁.subtype_injective]
  exact hKJ

theorem q_exists_mulEquiv_sz {Q : Type} [Group Q] {f : ℕ}
    (h : CFSG.Blueprint.SuzukiModel Q 2 f) : ∃ a : ℕ, 1 ≤ a ∧ Nonempty (Q ≃* Sz a) := by
  obtain ⟨-, a, ha, K, _, _, rfl, hcard, ⟨e⟩⟩ := h
  exact ⟨a, ha, ⟨e.trans ((MulEquiv.subgroupCongr
    (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a K)).trans
      (CFSG.ShultStronglyClosedTI.glaSzEquivNative a ha hcard))⟩⟩

theorem q_no_suzuki_component {G₁ : Subgroup G}
    (hno : ∀ J ∈ cComp G₁, ∀ n : ℕ, 1 ≤ n → ¬ Nonempty (OTwoQuot J ≃* ↥(Sz n)))
    {J : Subgroup (OTwoQuot G₁)} (hJ : J ∈ cComp (⊤ : Subgroup (OTwoQuot G₁))) {f : ℕ}
    (hf : CFSG.Blueprint.SuzukiModel ↥J 2 f) : False := by
  obtain ⟨K, hK, rfl⟩ := q_exists_cComp_of_cComp_top hJ
  obtain ⟨e⟩ := q_oTwoQuot_equiv_image (subnormal_of_mem_cComp hK)
  obtain ⟨a, ha, ⟨e'⟩⟩ := q_exists_mulEquiv_sz hf
  exact hno K hK a ha ⟨e.trans e'⟩

end Img

end CFSG.Quasithin
