module

public import CFSG.Quasithin.Vol2.Ch4Sec4G443J4S

public section

namespace CFSG.Quasithin.H13.Ch4.G443J4

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

theorem exists_normal_cComp_ge_of (hqtke : quasithinIsQTKECat G) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (h39 : A39ForSQTK) (hA21 : AsA21SQTKSection)
    {H KZ : Subgroup G} (hH : pCoreOf 2 H ≠ ⊥) (hKZH : KZ ≤ H) (hKZp : ⁅KZ, KZ⁆ = KZ)
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (g : ↥KZ →* S)
    (hg : Function.Surjective g) (hgk : Group.IsSolvable ↥g.ker) (hS3 : 2 ≤ CFSG.pRank 3 S) :
    ∃ LZ ∈ cComp H, KZ ≤ LZ ∧ H ≤ Subgroup.normalizer (LZ : Set G) := by
  have hSQ : SQTKGroup ↥H := sqtkGroup_of_pCoreOf_ne_bot hqtke hs hnab hH
  have h121 : cCompSpan H = perfectCore H := lemma_1_2_1_one hqtke hs hnab h39 hH
  set B := KZ.subgroupOf H with hBdef
  have hBmap : B.map H.subtype = KZ := Subgroup.map_subgroupOf_eq_of_le hKZH
  have hBp : ⁅B, B⁆ = B := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_commutator, hBmap, hKZp]
  have hKZE : KZ ≤ cCompSpan H := h121 ▸ le_perfectCore_of_perfect hKZH hKZp
  have hspan : cCompSpan H ≤ (cCompSpan (⊤ : Subgroup ↥H)).map H.subtype := by
    refine sSup_le fun K hK => ?_
    rw [← Subgroup.map_subgroupOf_eq_of_le (le_of_mem_cComp hK)]
    exact Subgroup.map_mono (le_cCompSpan (subgroupOf_mem_cComp hK))
  have hBE : B ≤ cCompSpan (⊤ : Subgroup ↥H) := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hspan (hKZE hx)
    have : y = x := Subtype.ext hyx
    rwa [this] at hy
  set e : ↥B ≃* ↥KZ := Subgroup.subgroupOfEquivOfLe hKZH with he
  set g' : ↥B →* S := g.comp e.toMonoidHom with hg'
  have hg's : Function.Surjective g' := hg.comp e.surjective
  have hg'k : Group.IsSolvable ↥g'.ker := by
    set f : ↥g'.ker →* ↥g.ker :=
      (e.toMonoidHom.comp g'.ker.subtype).codRestrict g.ker fun x => x.2 with hf
    refine Group.isSolvable_of_isSolvable_injective (f := f) fun x y hxy => ?_
    have := congrArg (fun z : ↥g.ker => (z : ↥KZ)) hxy
    exact Subtype.ext (e.injective this)
  obtain ⟨K, hK, hBK, hKn⟩ := exists_normal_cComp_ge' hA21 hSQ hBp hBE g' hg's hg'k hS3
  have hKnorm : K.Normal := Subgroup.normalizer_eq_top_iff.mp hKn
  refine ⟨K.map H.subtype, map_subtype_mem_cComp hK, ?_, fun h hh => ?_⟩
  · rw [← hBmap]
    exact Subgroup.map_mono hBK
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨_, hKnorm.conj_mem k hk ⟨h, hh⟩, rfl⟩
    · rintro ⟨k, hk, hkx⟩
      have hxH : x ∈ H := by
        have : h⁻¹ * (h * x * h⁻¹) * h ∈ H :=
          H.mul_mem (H.mul_mem (H.inv_mem hh) (hkx ▸ k.2)) hh
        simpa [mul_assoc] using this
      refine ⟨⟨x, hxH⟩, ?_, rfl⟩
      have h1 := hKnorm.conj_mem k hk (⟨h, hh⟩ : ↥H)⁻¹
      have hkx' : (k : G) = h * x * h⁻¹ := hkx
      have e1 : ((⟨h, hh⟩ : ↥H)⁻¹ * k * ((⟨h, hh⟩ : ↥H)⁻¹)⁻¹ : ↥H) = ⟨x, hxH⟩ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, InvMemClass.coe_inv, inv_inv]
        rw [hkx']
        group
      rwa [e1] at h1

end CFSG.Quasithin.H13.Ch4.G443J4
