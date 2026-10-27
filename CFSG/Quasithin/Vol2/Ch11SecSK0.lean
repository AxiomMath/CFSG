module

public import CFSG.Quasithin.Vol2.Ch11SecSQuot
public import CFSG.Quasithin.Vol2.Ch11SecSFacts
public import CFSG.Quasithin.Vol2.Ch11SecSSetup

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

variable {G : Type} [Group G] [Finite G]

structure ParData (T K L₁ : Subgroup G) (P₁ P₂ : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K)) : Prop where
  ne : P₁ ≠ P₂
  ne_top₁ : P₁ ≠ ⊤
  ne_top₂ : P₂ ≠ ⊤
  c₁ : quasithinIsCComponent P₁ P₁
  c₂ : quasithinIsCComponent P₂ P₂
  cTop : quasithinIsCComponent (⊤ : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K)) ⊤
  n₁ : modO2Image K (T ⊓ K) ≤ Subgroup.normalizer (P₁ : Set (↥K ⧸ CFSG.pCore 2 ↥K))
  n₂ : modO2Image K (T ⊓ K) ≤ Subgroup.normalizer (P₂ : Set (↥K ⧸ CFSG.pCore 2 ↥K))
  sup : P₁ ⊔ P₂ = ⊤
  borel : Subgroup.normalizer (modO2Image K (T ⊓ K) : Set (↥K ⧸ CFSG.pCore 2 ↥K)) ≤ P₁ ⊓ P₂
  cases : ∀ P : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K), P ≠ ⊥ → ⁅P, P⁆ = P →
    modO2Image K (T ⊓ K) ≤ Subgroup.normalizer (P : Set (↥K ⧸ CFSG.pCore 2 ↥K)) →
      P = P₁ ∨ P = P₂ ∨ P = ⊤
  l₁ : modO2Image K L₁ = P₁

theorem eq_of_le_sup_pCoreOf {K B : Subgroup G} (hBK : B ≤ K) (hK : ⁅K, K⁆ = K)
    (hB : ⁅B, B⁆ = B) (hQB : pCoreOf 2 K ≤ Subgroup.normalizer (B : Set G))
    (hle : K ≤ B ⊔ pCoreOf 2 K) : B = K := by
  refine le_antisymm hBK ?_
  calc K = perfectCore K := (perfectCore_eq_self_of_perfect hK).symm
    _ ≤ perfectCore (B ⊔ pCoreOf 2 K) := perfectCore_mono hle
    _ = B := perfectCore_sup_eq hB (isSolvable_pCoreOf_two K) hQB

namespace StarHyp

variable {T L I V₁ V₂ X K : Subgroup G}

theorem isSylowTwoOf_bar (h : StarHyp G T L I V₁ V₂ X K) :
    QuasithinUnique.IsSylowTwoOf (modO2Image K (T ⊓ K)) ⊤ :=
  isSylowTwoOf_modO2Image h.isSylowTwoOf_inf

theorem pCoreOf_le_normalizer (h : StarHyp G T L I V₁ V₂ X K) {A : Subgroup G}
    (hA : T ≤ Subgroup.normalizer (A : Set G)) : pCoreOf 2 K ≤ Subgroup.normalizer (A : Set G) :=
  h.pCoreOf_le_T.trans hA

theorem modO2Image_L₁_ne_top (h : StarHyp G T L I V₁ V₂ X K) :
    modO2Image K (LOf L V₁) ≠ ⊤ := fun htop =>
  h.L₁_ne_K (eq_of_le_sup_pCoreOf h.L₁_le_K h.perfect h.perfect_L₁
    (h.pCoreOf_le_normalizer h.T_le_normalizer_L₁) (le_sup_of_modO2Image_eq_top h.L₁_le_K htop))

theorem exists_parData (hF : FactL34Parab) (h : StarHyp G T L I V₁ V₂ X K)
    (hL₁ : LOf L V₁ ≠ ⊥) : ∃ P₁ P₂, ParData T K (LOf L V₁) P₁ P₂ := by
  obtain ⟨P₁, P₂, hne, ht₁, ht₂, hc₁, hc₂, hcT, hn₁, hn₂, hsup, hB, hcases⟩ :=
    hF _ h.psl _ h.isSylowTwoOf_bar
  have hL := hcases _ (modO2Image_ne_bot h.L₁_le_K h.perfect_L₁ hL₁)
    (modO2Image_perfect h.L₁_le_K h.perfect_L₁)
    (modO2Image_le_normalizer (inf_le_left.trans h.T_le_normalizer_L₁))
  rcases hL with hL | hL | hL
  · exact ⟨P₁, P₂, hne, ht₁, ht₂, hc₁, hc₂, hcT, hn₁, hn₂, hsup, hB, hcases, hL⟩
  · refine ⟨P₂, P₁, hne.symm, ht₂, ht₁, hc₂, hc₁, hcT, hn₂, hn₁, by rwa [sup_comm],
      hB.trans_eq (inf_comm _ _), fun P h1 h2 h3 => ?_, hL⟩
    rcases hcases P h1 h2 h3 with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  · exact absurd hL h.modO2Image_L₁_ne_top

end StarHyp

@[expose] noncomputable def k0Of (K : Subgroup G) (P : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K)) :
    Subgroup G :=
  (perfectCore (P.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥K)))).map K.subtype

omit [Finite G] in
theorem k0Of_le (K : Subgroup G) (P : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K)) : k0Of K P ≤ K :=
  Subgroup.map_subtype_le _

theorem k0Of_perfect (K : Subgroup G) (P : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K)) :
    ⁅k0Of K P, k0Of K P⁆ = k0Of K P := by
  unfold k0Of
  rw [← Subgroup.map_commutator, perfectCore_perfect]

theorem modO2Image_k0Of (K : Subgroup G) {P : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K)}
    (hP : ⁅P, P⁆ = P) : modO2Image K (k0Of K P) = P := by
  unfold modO2Image k0Of
  have hc : ((perfectCore (P.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥K)))).map
      K.subtype).subgroupOf K = perfectCore (P.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥K))) :=
    Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
  rw [hc, map_perfectCore,
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _),
    perfectCore_eq_self_of_perfect hP]

omit [Finite G] in
theorem le_normalizer_k0Of {K B : Subgroup G} {P : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K)}
    (hBK : B ≤ K)
    (hB : modO2Image K B ≤ Subgroup.normalizer (P : Set (↥K ⧸ CFSG.pCore 2 ↥K))) :
    B ≤ Subgroup.normalizer (k0Of K P : Set G) := by
  intro b hb
  have hb' : (⟨b, hBK hb⟩ : ↥K) ∈ Subgroup.normalizer
      ((P.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) : Subgroup ↥K) : Set ↥K) :=
    Subgroup.le_normalizer_comap _ (hB ⟨⟨b, hBK hb⟩, hb, rfl⟩)
  have hb'' := normalizer_le_normalizer_perfectCore _ hb'
  exact Subgroup.le_normalizer_map K.subtype ⟨⟨b, hBK hb⟩, hb'', rfl⟩

end CFSG.Quasithin.Vol2.Ch11.SecS
