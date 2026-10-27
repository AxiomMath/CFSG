module

public import CFSG.Quasithin.H13.LocDblCriterion
public import CFSG.Quasithin.H13.AssemblyLocal
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.Criteria

public section

namespace CFSG.Quasithin.H13.LocDbl

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem normalizer_le_of_radQuot {Γ : Type} [Group Γ] [Finite Γ] {T A B : Subgroup Γ}
    (hT : IsSylowTwoOf T ⊤) (hA : A ∈ cComp (⊤ : Subgroup Γ))
    (hND : SylowNoDouble (↥A ⧸ CFSG.solvableRadical ↥A)) (hBA : B ≤ A)
    (hB : B ∈ cComp (B ⊔ T)) :
    T ⊓ Subgroup.normalizer (A : Set Γ) ≤ Subgroup.normalizer (B : Set Γ) := by
  set R : Subgroup Γ := CFSG.solvableRadical Γ with hR
  set π : Γ →* Γ ⧸ R := QuotientGroup.mk' R with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective R
  have hker : Group.IsSolvable π.ker := by
    rw [hπ, QuotientGroup.ker_mk']
    exact A3.solvableRadical_isSolvable
  have hAsub : A.IsSubnormal := A3.subnormal_top_iff.mp (subnormal_of_mem_cComp hA)
  obtain ⟨e⟩ := CFSG.SignalizerFunctorTheorem.Nonsolvable.nonempty_quotient_solvableRadical_mulEquiv
    hAsub
  have hAbar : A.map π ∈ cComp (⊤ : Subgroup (Γ ⧸ R)) := by
    have := map_mem_cComp_of_ker π hker hA
    rwa [Subgroup.map_top_of_surjective π hπs] at this
  obtain ⟨hsimple, -⟩ := radQuot_simple hA
  have := hsimple
  have hAbs : IsSimpleGroup ↥(A.map π) := e.symm.isSimpleGroup
  have hAND : SylowNoDouble ↥(A.map π) := SylowNoDouble.of_mulEquiv e hND
  have hTbar : IsSylowTwoOf (T.map π) ⊤ := A312.isSylowTwoOf_top_map π hπs hT
  have hBbar : B.map π ∈ cComp (B.map π ⊔ T.map π) := by
    have := map_mem_cComp_of_ker π hker hB
    rwa [Subgroup.map_sup] at this
  have key := normalizer_le_of_sylowNoDouble hTbar hAbs (subnormal_of_mem_cComp hAbar) hAND
    (Subgroup.map_mono hBA) hBbar
  intro t ht
  have htbar : π t ∈ T.map π ⊓ Subgroup.normalizer (A.map π : Set (Γ ⧸ R)) :=
    ⟨Subgroup.mem_map_of_mem π ht.1,
      Subgroup.le_normalizer_map π (Subgroup.mem_map_of_mem π ht.2)⟩
  have hNB := key htbar
  have htBT : t ∈ Subgroup.normalizer ((B ⊔ T : Subgroup Γ) : Set Γ) :=
    Subgroup.le_normalizer (Subgroup.mem_sup_right ht.1)
  have hBt : B.map (MulAut.conj t).toMonoidHom ∈ cComp (B ⊔ T) := map_conj_mem_cComp hB htBT
  have himg : (B.map (MulAut.conj t).toMonoidHom).map π = B.map π := by
    rw [Subgroup.map_map, ← map_conj_eq_iff.mpr hNB, Subgroup.map_map]
    congr 1
  exact map_conj_eq_iff.mp (map_injOn_cComp π hker (B ⊔ T) hBt hB himg)

@[expose] def SimpleListNoDouble : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    CFSG.Milestones.SQTKSimpleList S → SylowNoDouble S

theorem sylowNoDouble_radQuot
    (hfam : SimpleListNoDouble) {X : Type} [Group X] [Finite X]
    (hX : CFSG.SectionRank.IsSQTKCat X) {Y K : Subgroup X} (hK : K ∈ cComp Y) :
    SylowNoDouble (↥K ⧸ CFSG.solvableRadical ↥K) := by
  obtain ⟨hsimple, hnonab⟩ := radQuot_simple hK
  have hlist := CFSG.Milestones.cl_lit_sqtk_simple_list_section X hX K
    (CFSG.solvableRadical ↥K) hnonab
  exact hfam _ hsimple hnonab hlist

section Local

variable {G : Type} [Group G]

theorem mem_normalizer_subgroupOf {H K : Subgroup G} {g : G} (hgH : g ∈ H)
    (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    (⟨g, hgH⟩ : ↥H) ∈ Subgroup.normalizer ((K.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  intro h
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
  exact hg h

theorem mem_normalizer_of_subgroupOf {H L : Subgroup G} (hLH : L ≤ H) {g : G} (hgH : g ∈ H)
    (hg : (⟨g, hgH⟩ : ↥H) ∈ Subgroup.normalizer ((L.subgroupOf H : Subgroup ↥H) : Set ↥H)) :
    g ∈ Subgroup.normalizer (L : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  intro x
  constructor
  · intro hx
    have := (hg ⟨x, hLH hx⟩).mp hx
    simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] using this
  · intro hx
    have hxH : x ∈ H := by
      have h1 : g⁻¹ * (g * x * g⁻¹) * g ∈ H :=
        H.mul_mem (H.mul_mem (H.inv_mem hgH) (hLH hx)) hgH
      simpa [mul_assoc] using h1
    have := (hg ⟨x, hxH⟩).mpr hx
    simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] using this

theorem local_double_embedding_exclusion_of
    (hfam : SimpleListNoDouble) :
    LocalDoubleEmbeddingExclusion := by
  intro G _ _ S L K hs hnab hQ hL hK hLK s hs'
  have : IsSimpleGroup G := hs
  have hloc : LocalSQTK G := (qtkeCore_of_cat hnab hQ).1
  set H : Subgroup G := K ⊔ S with hH
  have hSQTK : CFSG.SectionRank.IsSQTKCat ↥H := hloc H hK.2.2.2
  have hSH : S ≤ H := le_sup_right
  have hKH : K ≤ H := le_sup_left
  have hLH : L ≤ H := hLK.trans hKH
  have hT : IsSylowTwoOf (S.subgroupOf H) ⊤ := isSylowTwoOf_subgroupOf_top ⟨hSH, hK.1, hK.2.2.1⟩
  have hA : K.subgroupOf H ∈ cComp (⊤ : Subgroup ↥H) := subgroupOf_mem_cComp hK.2.1
  have hB : L.subgroupOf H ∈ cComp (L.subgroupOf H ⊔ S.subgroupOf H) := by
    have := A312.mem_cComp_subgroupOf (sup_le hLH hSH) hL.2.1
    rwa [Subgroup.subgroupOf_sup hLH hSH] at this
  have hBA : L.subgroupOf H ≤ K.subgroupOf H := Subgroup.comap_mono hLK
  have hsH : s ∈ H := hSH hs'.1
  have hkey := normalizer_le_of_radQuot hT hA (sylowNoDouble_radQuot hfam hSQTK hA) hBA hB
    ⟨show (⟨s, hsH⟩ : ↥H) ∈ S.subgroupOf H from hs'.1, mem_normalizer_subgroupOf hsH hs'.2⟩
  exact conjugate_eq_self_iff.mpr (mem_normalizer_of_subgroupOf hLH hsH hkey)

end Local

end CFSG.Quasithin.H13.LocDbl
