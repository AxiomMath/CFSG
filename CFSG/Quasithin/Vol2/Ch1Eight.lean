module

public import CFSG.Quasithin.Vol2.Ch1Comm
public import CFSG.Quasithin.Vol2.Ch1Local

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

@[expose] def Lemma128One : Prop :=
  ∀ (G : Type) [Group G] [Finite G], quasithinIsQTKECat G → IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → ∀ S L K : Subgroup G, quasithinIsLocal S L →
      quasithinIsLocal S K → L ≤ K →
        S ⊓ Subgroup.normalizer (K : Set G) ≤ Subgroup.normalizer (L : Set G)

@[expose] def Lemma128Two : Prop :=
  ∀ (G : Type) [Group G] [Finite G], quasithinIsQTKECat G → IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → ∀ S L K : Subgroup G, quasithinIsLocal S L →
      quasithinIsLocal S K → L ≤ K → L < conjClosure L S →
        L = K ∨ (IsAlt 5 (ModO2 L) ∧ (IsSporadic .J1 (ModO2 K) ∨
          ∃ p : ℕ, p.Prime ∧ p ^ 2 % 5 = 1 ∧ IsPSL 2 p 1 (ModO2 K)))

@[expose] def A128FourList (X : Type) [Group X] : Prop :=
  IsHat X (alternatingGroup (Fin 7)) ∨
    (∃ r : ℕ, r.Prime ∧ 3 < r ∧ IsPSL 2 r 2 X) ∨
    (∃ (s : Bool) (p : ℕ), p.Prime ∧ p ≠ 2 ∧ (IsPSLEps3 s p 1 X ∨ IsSLEps3 s p X)) ∨
    IsSporadic .M11 X ∨ IsSporadic .M12 X ∨ IsSporadic .M23 X ∨ IsSporadic .J1 X ∨
    IsSporadic .J2 X ∨ IsSporadic .J4 X ∨ IsSporadic .HS X ∨ IsSporadic .He X ∨
    IsSporadic .Ru X ∨ IsPSL 5 2 1 X ∨ (∃ n : ℕ, IsPSU 3 2 n X ∨ IsSU3 (2 ^ n) X) ∨
    (IsRank2LieChar2 X ∧ ¬ IsPSL 3 2 1 X ∧ ¬ IsPSL 3 2 2 X)

@[expose] def Lemma128Four : Prop :=
  ∀ (G : Type) [Group G] [Finite G], quasithinIsQTKECat G → IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → ∀ S L : Subgroup G, quasithinIsLocal S L →
      A128FourList (ModO2 L) → quasithinIsMaximalLocal S L

section Ambient

variable {G : Type} [Group G] [Finite G]

theorem lemma_1_2_8_one_le (hQ : quasithinIsQTKECat G) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (h37 : A37ForSQTK) {S L K : Subgroup G}
    (hL : quasithinIsLocal S L) (hK : quasithinIsLocal S K) (hLK : L ≤ K) :
    S ⊓ Subgroup.normalizer (L : Set G) ≤ S ⊓ Subgroup.normalizer (K : Set G) := by
  intro s hs'
  have hKH : K ∈ cComp (K ⊔ S) := cComp_of_isLocal hK
  have hHne : pCoreOf 2 (K ⊔ S) ≠ ⊥ := hK.2.2.2
  have hQ' := sqtkHyp_quotient_of_pCoreOf_ne_bot hQ hs hnab hHne
  have hsH : s ∈ K ⊔ S := (le_sup_right : S ≤ K ⊔ S) hs'.1
  have hKs : K.map (MulAut.conj s).toMonoidHom ∈ cComp (K ⊔ S) := map_conj_mem_cComp hKH hsH
  have hLs : L.map (MulAut.conj s).toMonoidHom = L := A38.map_conj_eq_iff.mpr hs'.2
  have hLKs : L ≤ K.map (MulAut.conj s).toMonoidHom :=
    calc L = L.map (MulAut.conj s).toMonoidHom := hLs.symm
      _ ≤ K.map (MulAut.conj s).toMonoidHom := Subgroup.map_mono hLK
  have heq := lemma_1_2_4_unique (h37 _ hQ') (mem_lFamily_of_isLocal hL) hKH hKs hLK hLKs
  exact ⟨hs'.1, A38.map_conj_eq_iff.mp heq.symm⟩

theorem lemma_1_2_8_one (hQ : quasithinIsQTKECat G) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (h37 : A37ForSQTK) (h128 : Lemma128One) {S L K : Subgroup G}
    (hL : quasithinIsLocal S L) (hK : quasithinIsLocal S K) (hLK : L ≤ K) :
    S ⊓ Subgroup.normalizer (L : Set G) = S ⊓ Subgroup.normalizer (K : Set G) :=
  le_antisymm (lemma_1_2_8_one_le hQ hs hnab h37 hL hK hLK)
    (le_inf inf_le_left ((h128 G hQ hs hnab S L K hL hK hLK)))

theorem lemma_1_2_8_one_conj (hQ : quasithinIsQTKECat G) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (h37 : A37ForSQTK) (h128 : Lemma128One) {S L K : Subgroup G}
    (hL : quasithinIsLocal S L) (hK : quasithinIsLocal S K) (hLK : L ≤ K) {s : G} (hsS : s ∈ S)
    (hne : L.map (MulAut.conj s).toMonoidHom ≠ L) :
    K.map (MulAut.conj s).toMonoidHom ≠ K ∧
      L ⊔ L.map (MulAut.conj s).toMonoidHom ≤ K ⊔ K.map (MulAut.conj s).toMonoidHom := by
  have heq := lemma_1_2_8_one hQ hs hnab h37 h128 hL hK hLK
  refine ⟨fun h => hne ?_, sup_le_sup hLK (Subgroup.map_mono hLK)⟩
  have hsK : s ∈ S ⊓ Subgroup.normalizer (K : Set G) := ⟨hsS, A38.map_conj_eq_iff.mp h⟩
  rw [← heq] at hsK
  exact A38.map_conj_eq_iff.mpr hsK.2

theorem lemma_1_2_8_three (h128 : Lemma128Two) (hQ : quasithinIsQTKECat G) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) {S L : Subgroup G} (hL : quasithinIsLocal S L)
    (hlt : L < conjClosure L S) :
    quasithinIsMaximalLocal S L ∨ IsAlt 5 (ModO2 L) := by
  by_cases hA : IsAlt 5 (ModO2 L)
  · exact Or.inr hA
  · left
    refine ⟨hL, fun K hK hLK => ?_⟩
    rcases h128 G hQ hs hnab S L K hL hK hLK hlt with h | ⟨hA5, -⟩
    · exact h.symm
    · exact absurd hA5 hA

end Ambient

end CFSG.Quasithin
