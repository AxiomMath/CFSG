module

public import CFSG.Quasithin.EmptyFaithful.S146xU1
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

section Common

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

local notation "Zz" => quasithinOmegaOneCenter T

theorem Setting146.le_normalizer_U₁_of_decomp (S : Setting146 G T M) {K U₁ U₂ : Subgroup G} {s : G}
    (hK : K ∈ cComp (mcOf T)) (hdec : IsDecompUK T M K U₁ U₂ s) :
    K ≤ Subgroup.normalizer (U₁ : Set G) := by
  have hKG : K ≤ mcOf T := le_of_mem_cComp hK
  have hKZ : K ≤ Subgroup.normalizer (Zz : Set G) := fun k hk => S.normalizer_Z.ge (hKG hk)
  rcases hdec.natural with ⟨-, -, hirr⟩ | ⟨-, hnat⟩
  · exact hirr.2.1
  · rcases hnat with ⟨-, hirr, -⟩ | ⟨-, hcomm⟩
    · exact hirr.2.1
    · rw [← hcomm]
      exact le_normalizer_sup_of_le (Subgroup.normalizer_commutator_ge_right U₁ K) hKZ

omit [Finite G] in
theorem le_U_of_decomp {K U₁ U₂ : Subgroup G} {s : G}
    (hK : K ∈ cComp (mcOf T)) (hdec : IsDecompUK T M K U₁ U₂ s) :
    U₁ ≤ uOfL22 T M ∧ U₂ ≤ uOfL22 T M := by
  have hKG : K ≤ mcOf T := le_of_mem_cComp hK
  have hKU : K ≤ Subgroup.normalizer (uOfL22 T M : Set G) :=
    hKG.trans (le_normalizer_conjClosure _ _)
  have h1 : ⁅uOfL22 T M, K⁆ ≤ uOfL22 T M := S145.commutator_le_of_le_normalizer hKU
  have hZU : Zz ≤ uOfL22 T M := Z_le_conjClosure_VZ T M (mcOf T)
  have h2 : U₁ ⊔ U₂ ≤ uOfL22 T M := by
    rw [← hdec.sup]
    exact sup_le h1 hZU
  exact ⟨le_sup_left.trans h2, le_sup_right.trans h2⟩

omit [Finite G] in
theorem commutator_zpowers_le_of_forall {K : Subgroup G} {u : G}
    (hKZ : K ≤ Subgroup.normalizer (Zz : Set G)) (hu : ∀ z ∈ Zz, u * z = z * u)
    (h : ∀ x ∈ K, x * u * x⁻¹ * u⁻¹ ∈ Zz) : ⁅Subgroup.zpowers u, K⁆ ≤ Zz := by
  rw [Subgroup.commutator_le]
  intro a ha x hx
  have h1 : x ∈ centralizerMod Zz K (Subgroup.zpowers u) :=
    mem_centralizerMod_zpowers hx (hKZ hx) hu (h x hx)
  have h2 := h1.2.2 a ha
  have e : ⁅a, x⁆ = (x * a * x⁻¹ * a⁻¹)⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact Subgroup.inv_mem _ h2

omit [Finite G] in
theorem isElemAbelian_two_of_le {E F : Subgroup G} (hE : IsElemAbelian 2 E) (hFE : F ≤ E) :
    IsElemAbelian 2 F := CFSG.Open.IsElemAbelian.mono hE hFE

end Common


section Gen

variable {G : Type} [Group G]

@[expose] def A6CoverGen : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K Z U₁ : Subgroup G) (u : G),
    KbarIsA6 K → mIdx U₁ Z = 5 → ⁅U₁, K⁆ ⊔ Z = U₁ → Z ≤ U₁ → IsElemAbelian 2 U₁ →
    K ≤ Subgroup.normalizer (Z : Set G) → K ≤ Subgroup.normalizer (U₁ : Set G) →
    (∀ p ∈ pCoreOf 2 K, ∀ w ∈ U₁, p * w * p⁻¹ * w⁻¹ ∈ Z) → u ∈ U₁ →
    (∃ x ∈ K, x * u * x⁻¹ * u⁻¹ ∉ Z) →
    ∀ W : Subgroup G, Z ≤ W → W ≤ U₁ → K ≤ Subgroup.normalizer (W : Set G) →
      (∀ x ∈ K, x * u * x⁻¹ * u⁻¹ ∈ W) → W = U₁

end Gen

section Gen2

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

local notation "Zz" => quasithinOmegaOneCenter T

theorem Setting146.eq_of_commutators_mem (hgen : A6CoverGen) (S : Setting146 G T M)
    {K U₁ U₂ : Subgroup G} {s u : G} (hK : K ∈ cComp (mcOf T)) (hdec : IsDecompUK T M K U₁ U₂ s)
    (huU : u ∈ U₁) (hnc : ∃ x ∈ K, x * u * x⁻¹ * u⁻¹ ∉ Zz) {W : Subgroup G} (hZW : Zz ≤ W)
    (hWU : W ≤ U₁) (hKW : K ≤ Subgroup.normalizer (W : Set G))
    (hW : ∀ x ∈ K, x * u * x⁻¹ * u⁻¹ ∈ W) : W = U₁ := by
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hKG : K ≤ mcOf T := le_of_mem_cComp hK
  have hirr : IsIrredOnSection K U₁ Zz → W = U₁ := fun hirr => by
    rcases hirr.2.2.2 W hZW hWU hKW with h | h
    · exfalso
      obtain ⟨x, hx, hxn⟩ := hnc
      exact hxn (h ▸ hW x hx)
    · exact h
  rcases hdec.natural with ⟨-, -, hi⟩ | ⟨hA, hnat⟩
  · exact hirr hi
  · rcases hnat with ⟨-, hi, -⟩ | ⟨h5, hcomm⟩
    · exact hirr hi
    · have hU₁U := (le_U_of_decomp hK hdec).1
      have hUab : IsElemAbelian 2 (uOfL22 T M) := S.lemma_14_5_15_two hG
      have hQK : pCoreOf 2 K ≤ pCoreOf 2 (mcOf T) :=
        A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hK)
      exact hgen G K Zz U₁ u hA h5 hcomm hdec.Z₁ (isElemAbelian_two_of_le hUab hU₁U)
        (fun k hk => S.normalizer_Z.ge (hKG hk)) (S.le_normalizer_U₁_of_decomp hK hdec)
        (fun p hp w hw => S.comm_mem_Z hG (hU₁U hw) (hQK hp)) huU hnc W hZW hWU hKW hW

end Gen2

end CFSG.Quasithin
