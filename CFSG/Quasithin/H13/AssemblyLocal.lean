module

public import CFSG.Quasithin.Vol2.Ch1Nine
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3Native36

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G]

@[expose] def LocalDoubleEmbeddingExclusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S L K : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → quasithinIsQTKECat G → quasithinIsLocal S L →
    quasithinIsLocal S K → L ≤ K →
      ∀ s ∈ S ⊓ Subgroup.normalizer (K : Set G), CFSG.conjugate L s = L

theorem conjugate_eq_self_iff {L : Subgroup G} {s : G} :
    CFSG.conjugate L s = L ↔ s ∈ Subgroup.normalizer (L : Set G) := by
  rw [CFSG.conjugate, ← Subgroup.inv_mem_iff, ← A38.map_conj_eq_iff]

variable [Finite G]

theorem local_normalizer_chain_inclusion_of (h37 : Vol2Native.A37ForSQTKCat)
    (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a) (hQ : quasithinIsQTKECat G)
    {S L K : Subgroup G} (hL : quasithinIsLocal S L) (hK : quasithinIsLocal S K) (hLK : L ≤ K) :
    S ⊓ Subgroup.normalizer (L : Set G) ≤ S ⊓ Subgroup.normalizer (K : Set G) := by
  have := hs
  have hloc : LocalSQTK G := (qtkeCore_of_cat hnab hQ).1
  intro s hs'
  have hKH : K ∈ cComp (K ⊔ S) := cComp_of_isLocal hK
  have hsH : s ∈ K ⊔ S := (le_sup_right : S ≤ K ⊔ S) hs'.1
  have hKs : K.map (MulAut.conj s).toMonoidHom ∈ cComp (K ⊔ S) := map_conj_mem_cComp hKH hsH
  have hLs : L.map (MulAut.conj s).toMonoidHom = L := A38.map_conj_eq_iff.mpr hs'.2
  have hLKs : L ≤ K.map (MulAut.conj s).toMonoidHom :=
    calc L = L.map (MulAut.conj s).toMonoidHom := hLs.symm
      _ ≤ K.map (MulAut.conj s).toMonoidHom := Subgroup.map_mono hLK
  have heq := Vol2Native.lemma_1_2_4_unique hloc h37 hK.2.2.2
    (mem_lFamily_of_isLocal hL) hKH hKs hLK hLKs
  exact ⟨hs'.1, A38.map_conj_eq_iff.mp heq.symm⟩

theorem local_normalizer_chain_inclusion
    (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (hQ : quasithinIsQTKECat G) {S L K : Subgroup G}
    (hL : quasithinIsLocal S L) (hK : quasithinIsLocal S K) (hLK : L ≤ K) :
    S ⊓ Subgroup.normalizer (L : Set G) ≤ S ⊓ Subgroup.normalizer (K : Set G) :=
  local_normalizer_chain_inclusion_of Vol2Native.a37ForSQTKCat_proved hs hnab hQ hL hK hLK

theorem local_normalizer_chain_equality_of (h37 : Vol2Native.A37ForSQTKCat)
    (hD : LocalDoubleEmbeddingExclusion) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (hQ : quasithinIsQTKECat G) {S L K : Subgroup G}
    (hL : quasithinIsLocal S L) (hK : quasithinIsLocal S K) (hLK : L ≤ K) :
    S ⊓ Subgroup.normalizer (L : Set G) = S ⊓ Subgroup.normalizer (K : Set G) :=
  le_antisymm (local_normalizer_chain_inclusion_of h37 hs hnab hQ hL hK hLK) fun s hsK =>
    ⟨hsK.1, conjugate_eq_self_iff.mp (hD G S L K hs hnab hQ hL hK hLK s hsK)⟩

theorem local_normalizer_chain_equality
    (hD : LocalDoubleEmbeddingExclusion)
    (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a) (hQ : quasithinIsQTKECat G)
    {S L K : Subgroup G} (hL : quasithinIsLocal S L) (hK : quasithinIsLocal S K) (hLK : L ≤ K) :
    S ⊓ Subgroup.normalizer (L : Set G) = S ⊓ Subgroup.normalizer (K : Set G) :=
  local_normalizer_chain_equality_of Vol2Native.a37ForSQTKCat_proved hD hs hnab hQ hL hK hLK

theorem charTwo_of_isLocal_cat (hQ : quasithinIsQTKECat G) {T K : Subgroup G}
    (hT : quasithinIsSylowTwo T) (hK : quasithinIsLocal T K) : CharTwo K := by
  obtain ⟨S, rfl⟩ := exists_sylow_of_quasithinIsSylowTwo hT
  have hH' : InH (S : Subgroup G) (K ⊔ (S : Subgroup G)) := ⟨le_sup_right, hK.2.2.2⟩
  exact A4.charTwo_of_subnormal (subnormal_of_mem_cComp (cComp_of_isLocal hK))
    (charTwo_of_inH hQ.2.1 S hH')

theorem isXClass_of_isLocal_cat (hQ : quasithinIsQTKECat G) {T K : Subgroup G}
    (hT : quasithinIsSylowTwo T) (hK : quasithinIsLocal T K) : IsXClass K :=
  ⟨ne_bot_of_mem_cComp (cComp_of_isLocal hK),
    eq_oTwoUpper_of_perfect (perfect_of_mem_cComp (cComp_of_isLocal hK)),
    charTwo_of_isLocal_cat hQ hT hK⟩

theorem local_faithfulness_upward (hD : LocalDoubleEmbeddingExclusion) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (hQ : quasithinIsQTKECat G) {T L K : Subgroup G}
    (hT : quasithinIsSylowTwo T) (hK : quasithinIsLocal T K) (hLK : L ≤ K)
    (hL : quasithinIsFaithfulLocal T L) : quasithinIsFaithfulLocal T K := by
  obtain ⟨hLloc, hLX⟩ := isFaithfulLocal_iff_isXf.mp hL
  set R := T ⊓ Subgroup.normalizer (K : Set G) with hR
  have hRL : R ≤ Subgroup.normalizer (L : Set G) := fun s hsK =>
    conjugate_eq_self_iff.mp (hD G T L K hs hnab hQ hLloc hK hLK s hsK)
  have hKR : T ⊓ K ≤ R := le_inf inf_le_left (inf_le_right.trans Subgroup.le_normalizer)
  have hLR : T ⊓ L ≤ R := fun x hx => ⟨hx.1, Subgroup.le_normalizer (hLK hx.2)⟩
  have hRsylK : IsSylowTwoOf R (K ⊔ R) :=
    isSylowTwoOf_sup_of_isLocal hK inf_le_left inf_le_right hKR
  have hRsylL : IsSylowTwoOf R (L ⊔ R) :=
    isSylowTwoOf_sup_of_isLocal hLloc inf_le_left hRL hLR
  have hO2K : pCoreOf 2 (K ⊔ R) ≤ R := EscapingLocal.pCoreOf_le_of_isSylowTwoOf hRsylK
  have hA : A410Hyp L K R :=
    { xclass := hLX.1
      yclass := isXClass_of_isLocal_cat hQ hT hK
      xy := hLK
      normalizes := inf_le_right
      sylowT := hRsylK
      o2le := le_inf hO2K (hO2K.trans hRL)
      sylowNT := by
        rw [inf_eq_left.mpr hRL]
        exact A4.isSylowTwoOf_mono hRsylK (le_inf le_sup_right hRL) inf_le_left }
  exact isFaithfulLocal_iff_isXf.mpr ⟨hK, a4_10_3 hA hLX⟩

theorem faithful_maximal_local_exists (hD : LocalDoubleEmbeddingExclusion)
    (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a) (hQ : quasithinIsQTKECat G)
    {T L : Subgroup G} (hT : quasithinIsSylowTwo T) (hL : quasithinIsFaithfulLocal T L) :
    ∃ K : Subgroup G, (quasithinIsMaximalLocal T K ∧ quasithinIsFaithfulLocal T K) ∧ L ≤ K := by
  obtain ⟨K, hLK, hmax⟩ :=
    Finite.exists_le_maximal (p := fun K : Subgroup G => quasithinIsLocal T K ∧ L ≤ K)
      ⟨hL.1, le_rfl⟩
  refine ⟨K, ⟨⟨hmax.1.1, fun K' hK' hKK' => ?_⟩,
    local_faithfulness_upward hD hs hnab hQ hT hmax.1.1 hmax.1.2 hL⟩, hLK⟩
  exact le_antisymm (hmax.2 ⟨hK', hLK.trans hKK'⟩ hKK') hKK'

theorem faithful_maximal_local_nonempty (hD : LocalDoubleEmbeddingExclusion)
    (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a) (hQ : quasithinIsQTKECat G)
    {T : Subgroup G} (hT : quasithinIsSylowTwo T)
    (hne : ∃ L : Subgroup G, quasithinIsFaithfulLocal T L) :
    ∃ K : Subgroup G, quasithinIsMaximalLocal T K ∧ quasithinIsFaithfulLocal T K := by
  obtain ⟨L, hL⟩ := hne
  obtain ⟨K, hK, -⟩ := faithful_maximal_local_exists hD hs hnab hQ hT hL
  exact ⟨K, hK⟩

end CFSG.Quasithin.H13
