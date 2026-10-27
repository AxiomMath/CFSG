module

public import CFSG.Quasithin.Background.F1Basic

public section

namespace CFSG.Quasithin.N204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

variable {G : Type} [Group G]

abbrev TwoQuot (N : Subgroup G) : Type := ↥N ⧸ CFSG.Open.pCore 2 ↥N

noncomputable abbrev twoProj (N : Subgroup G) : ↥N →* TwoQuot N :=
  QuotientGroup.mk' (CFSG.Open.pCore 2 ↥N)

noncomputable def twoImg (N A : Subgroup G) : Subgroup (TwoQuot N) :=
  (A.subgroupOf N).map (twoProj N)

variable {N A B : Subgroup G}

theorem mem_twoImg {x : TwoQuot N} :
    x ∈ twoImg N A ↔ ∃ a : ↥N, (a : G) ∈ A ∧ twoProj N a = x := by
  simp only [twoImg, Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem twoImg_mono (h : A ≤ B) : twoImg N A ≤ twoImg N B := fun _ hx => by
  obtain ⟨a, ha, rfl⟩ := mem_twoImg.mp hx
  exact mem_twoImg.mpr ⟨a, h ha, rfl⟩

theorem twoImg_sup (hA : A ≤ N) (hB : B ≤ N) :
    twoImg N (A ⊔ B) = twoImg N A ⊔ twoImg N B := by
  unfold twoImg
  rw [Subgroup.subgroupOf_sup hA hB, Subgroup.map_sup]

theorem twoImg_self : twoImg N N = ⊤ := by
  unfold twoImg
  rw [Subgroup.subgroupOf_self, Subgroup.map_top, MonoidHom.range_eq_top]
  exact QuotientGroup.mk'_surjective _

theorem isPGroup_twoImg (h : IsPGroup 2 ↥A) : IsPGroup 2 ↥(twoImg N A) :=
  (h.comap_subtype (K := N)).map (twoProj N)

theorem mem_pCoreOf_iff {a : ↥N} : (a : G) ∈ pCoreOf 2 N ↔ a ∈ CFSG.Open.pCore 2 ↥N :=
  Subgroup.mem_map_iff_mem N.subtype_injective

theorem twoProj_eq_iff {a b : ↥N} :
    twoProj N a = twoProj N b ↔ (a : G)⁻¹ * b ∈ pCoreOf 2 N := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  exact (mem_pCoreOf_iff (a := a⁻¹ * b)).symm

theorem subgroupOf_le_normalizer (h : A ≤ Subgroup.normalizer (B : Set G)) :
    A.subgroupOf N ≤ Subgroup.normalizer ((B.subgroupOf N : Subgroup ↥N) : Set ↥N) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro y
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
  exact Subgroup.mem_normalizer_iff.mp (h (Subgroup.mem_subgroupOf.mp ha)) _

theorem twoImg_le_normalizer (h : A ≤ Subgroup.normalizer (B : Set G)) :
    twoImg N A ≤ Subgroup.normalizer ((twoImg N B : Subgroup (TwoQuot N)) : Set (TwoQuot N)) :=
  fun _ hx => by
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.le_normalizer_map (twoProj N) ⟨a, subgroupOf_le_normalizer h ha, rfl⟩

theorem relIndex_map_dvd {Γ Δ : Type*} [Group Γ] [Group Δ] (f : Γ →* Δ) {H K : Subgroup Γ}
    (hHK : H ≤ K) : (H.map f).relIndex (K.map f) ∣ H.relIndex K := by
  have heq : (H.map f).subgroupOf (K.map f) = (H.subgroupOf K).map (f.subgroupMap K) := by
    ext y
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨h, hh, hhy⟩
      exact ⟨⟨h, hHK hh⟩, hh, Subtype.ext hhy⟩
    · rintro ⟨k, hk, hky⟩
      exact ⟨k, hk, congrArg Subtype.val hky⟩
  rw [Subgroup.relIndex, heq]
  exact Subgroup.index_map_dvd _ (f.subgroupMap_surjective K)

theorem isSylowTwoOf_twoImg (hB : B ≤ N) (h : IsSylowTwoOf A B) :
    IsSylowTwoOf (twoImg N A) (twoImg N B) := by
  refine ⟨twoImg_mono h.1, isPGroup_twoImg h.2.1, fun hd => h.2.2 (hd.trans ?_)⟩
  have h1 := relIndex_map_dvd (twoProj N) (H := A.subgroupOf N) (K := B.subgroupOf N)
    (fun _ hx => Subgroup.mem_subgroupOf.mpr (h.1 (Subgroup.mem_subgroupOf.mp hx)))
  rwa [Subgroup.relIndex_subgroupOf hB] at h1

theorem mem_normalizer_of_twoProj_mem {S L : Subgroup G} (hL : L ≤ N) (hQS : pCoreOf 2 N ≤ S)
    {l : ↥N} (hl : (l : G) ∈ L)
    (hn : twoProj N l ∈ Subgroup.normalizer ((twoImg N (S ⊓ L) : Subgroup (TwoQuot N)) :
      Set (TwoQuot N))) : (l : G) ∈ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) := by
  have key : ∀ l : ↥N, (l : G) ∈ L →
      twoProj N l ∈ Subgroup.normalizer ((twoImg N (S ⊓ L) : Subgroup (TwoQuot N)) :
        Set (TwoQuot N)) → ∀ a ∈ S ⊓ L, (l : G) * a * (l : G)⁻¹ ∈ S ⊓ L := by
    intro l hl hn a ha
    have haN : a ∈ N := hL ha.2
    have hmem : twoProj N (l * ⟨a, haN⟩ * l⁻¹) ∈ twoImg N (S ⊓ L) := by
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hn (twoProj N ⟨a, haN⟩)).mp
        (mem_twoImg.mpr ⟨⟨a, haN⟩, ha, rfl⟩)
    obtain ⟨c, hc, hce⟩ := mem_twoImg.mp hmem
    have hq : (c : G)⁻¹ * ((l : G) * a * (l : G)⁻¹) ∈ pCoreOf 2 N := (twoProj_eq_iff.mp hce)
    have hqL : (c : G)⁻¹ * ((l : G) * a * (l : G)⁻¹) ∈ L :=
      L.mul_mem (L.inv_mem hc.2) (L.mul_mem (L.mul_mem hl ha.2) (L.inv_mem hl))
    have hmul : (l : G) * a * (l : G)⁻¹ = (c : G) * ((c : G)⁻¹ * ((l : G) * a * (l : G)⁻¹)) := by
      group
    rw [hmul]
    exact (S ⊓ L).mul_mem hc ⟨hQS hq, hqL⟩
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨key l hl hn h, fun hh => ?_⟩
  have hl' : ((l⁻¹ : ↥N) : G) ∈ L := L.inv_mem hl
  have := key l⁻¹ hl' (by rw [map_inv]; exact Subgroup.inv_mem _ hn) _ hh
  simpa [mul_assoc] using this

variable [Finite G]

theorem twoImg_inf_of_sylow {S L : Subgroup G} (hS : IsPGroup 2 ↥S) (hL : L ≤ N)
    (h : IsSylowTwoOf (S ⊓ L) L) : twoImg N S ⊓ twoImg N L = twoImg N (S ⊓ L) :=
  (F1.eq_of_isSylowTwoOf_le (isSylowTwoOf_twoImg hL h) inf_le_right
    ((isPGroup_twoImg hS).to_le inf_le_left)
    (le_inf (twoImg_mono inf_le_left) (twoImg_mono inf_le_right))).symm

theorem twoImg_borelOf {S L : Subgroup G} (hS : IsPGroup 2 ↥S) (hL : L ≤ N)
    (hQS : pCoreOf 2 N ≤ S) (h : IsSylowTwoOf (S ⊓ L) L) :
    borelOf (twoImg N L) (twoImg N S) = twoImg N (borelOf L S) := by
  unfold borelOf
  rw [twoImg_inf_of_sylow hS hL h]
  refine le_antisymm (fun x hx => ?_) (fun x hx => ⟨twoImg_mono inf_le_left hx,
    twoImg_le_normalizer inf_le_right hx⟩)
  obtain ⟨hxL, hxn⟩ := hx
  obtain ⟨l, hl, rfl⟩ := mem_twoImg.mp hxL
  exact mem_twoImg.mpr ⟨l, ⟨hl, mem_normalizer_of_twoProj_mem hL hQS hl hxn⟩, rfl⟩

end CFSG.Quasithin.N204
