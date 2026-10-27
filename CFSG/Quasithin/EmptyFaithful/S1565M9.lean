module

public import CFSG.Quasithin.EmptyFaithful.S1565M4
public import CFSG.Quasithin.EmptyFaithful.S1565M7
public import CFSG.Quasithin.Background.F918P6
public import CFSG.Quasithin.EmptyFaithful.S1565M2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

section Core

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K : Subgroup G}

@[expose] def TwistFieldBig (hF : HypF918 T V L V₁ Vp H K) (I : Subgroup G)
    (hIU : I ≤ conjClosure Vp H) : Prop :=
  haveI := factElem hF hIU
  ∀ V' : Subgroup ↥(tildeOf V₁ (conjClosure I H)),
    (∀ n', BinaryNaturalSL (autIH V₁ I H K) V' (V' ⊓ fixV (autIH V₁ I H K)) 3 n' → 3 ≤ n') ∧
    (∀ n', BinaryNaturalSp4 (autIH V₁ I H K) V' (V' ⊓ fixV (autIH V₁ I H K)) n' → 3 ≤ n')

theorem typesFour_core_twist (hF : HypF918 T V L V₁ Vp H K) (M I : Subgroup G)
    (hIU : I ≤ conjClosure Vp H)
    (hnt : ¬ ∀ k ∈ conjClosure K T, ∀ i ∈ I, k * i * k⁻¹ * i⁻¹ ∈ V₁) (hK0 : conjClosure K T = K)
    (hkerchar : ∀ x : G, x ∈ kerIn (H ⊓ M) H ↔ x ∈ K ⊔ pCoreOf 2 H ∧
      ∀ y ∈ K ⊔ pCoreOf 2 H, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 H)
    (hB : E2.IsBorelIn (E2.star (H ⊓ M) H K) (E2.star (H ⊓ M) H ((H ⊓ M) ⊓ K)))
    (hbig : TwistFieldBig hF I hIU) (hshape : TypesFourTwistHyp hF I hIU) :
    TypesFourEltConcl hF M I hIU := by
  have hKH : K ≤ H := le_of_mem_cComp hF.K_cComp
  have hFI := factElem hF hIU
  obtain ⟨S, hS⟩ := exists_sylow_borel_acting_two hF M I hIU hnt hkerchar hB
  set φ := actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) with hφ
  set Q : Subgroup (MulAut ↥(tildeOf V₁ (conjClosure I H))) :=
    ((H ⊓ M).subgroupOf H).map φ with hQ
  have hSQ : ∀ b ∈ Subgroup.normalizer
      ((S : Subgroup ↥(autIH V₁ I H K)) : Set ↥(autIH V₁ I H K)),
      (b : MulAut ↥(tildeOf V₁ (conjClosure I H))) ∈ Q := by
    intro b hb
    obtain ⟨k, hkM, hkb⟩ := hS b hb
    rw [← hkb, toAutI_coe]
    exact ⟨Subgroup.inclusion hKH k, Subgroup.mem_subgroupOf.mpr ⟨hKH k.2, hkM⟩, rfl⟩
  have hfin : Finite ↥(autIH V₁ I H K) := Finite.of_surjective _ (toAutI_surjective hF I)
  obtain ⟨V', t, ht, hnat, hsum⟩ := hshape
  have htN : t ∈ Subgroup.normalizer ((autIH V₁ I H K : Subgroup _) : Set _) := by
    have := autIH_T_le_normalizer hF I ht
    rwa [hK0] at this
  have hnat' : (∃ n', 3 ≤ n' ∧ BinaryNaturalSL (autIH V₁ I H K) V' (V' ⊓ fixV (autIH V₁ I H K)) 3 n') ∨
      (∃ n', 3 ≤ n' ∧ BinaryNaturalSp4 (autIH V₁ I H K) V' (V' ⊓ fixV (autIH V₁ I H K)) n') := by
    rcases hnat with ⟨n', h⟩ | ⟨n', h⟩
    · exact Or.inl ⟨n', (hbig V').1 n' h, h⟩
    · exact Or.inr ⟨n', (hbig V').2 n' h, h⟩
  obtain ⟨a₀, ha₀, m, hodd, hpow, hgood⟩ := typesFour_good_twist S hSQ htN hsum hnat'
  obtain ⟨t₀, ht₀mem, rfl⟩ := ha₀
  have ht₀M : (t₀ : G) ∈ M := (Subgroup.mem_subgroupOf.mp ht₀mem).2
  have hKK : autIH V₁ I H (conjClosure K T) = autIH V₁ I H K := by rw [hK0]
  refine ⟨t₀, ht₀M, m, hodd, hpow, ?_⟩
  rw [hKK]
  exact hgood

end Core

section Inputs

attribute [local instance] commGroupOfFact

end Inputs

end CFSG.Quasithin
