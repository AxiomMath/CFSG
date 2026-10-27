module

public import CFSG.Quasithin.H13.U3Local

public section

namespace CFSG.Quasithin.H13.NQCore

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_of_isMaximalLocal (hK : LocalSQTK G) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat) {T L H : Subgroup G}
    (hT : quasithinIsSylowTwo T) (hL : quasithinIsMaximalLocal T L)
    (hTL : T ≤ normalizer (L : Set G)) (hLTH : L ⊔ T ≤ H) (hH : pCoreOf 2 H ≠ ⊥) :
    H ≤ normalizer (L : Set G) := by
  have hTH : T ≤ H := le_sup_right.trans hLTH
  have hLH : L ≤ H := le_sup_left.trans hLTH
  have hS : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo hT hTH
  obtain ⟨K, hK', hLK⟩ := Vol2Native.lemma_1_2_4_exists hK h37 h39 hH hS hLH
    (mem_lFamily_of_isLocal hL.1)
  have hKloc : quasithinIsLocal T K := isLocal_of_mem_cComp_of_sylow hS hH hK'
  have hKL : K = L := hL.2 K hKloc hLK
  rw [hKL] at hK'
  have h1 := Vol2Native.normal_conjClosure_of_pCoreOf_ne_bot hK h37 h38 hH hS hK'
  have hcl : conjClosure L T = L :=
    le_antisymm (conjClosure_le fun t ht l hl => (mem_normalizer_iff.mp (hTL ht) l).mp hl)
      (le_conjClosure L T)
  rwa [hcl] at h1

omit [Finite G] in
theorem pCoreOf_ne_bot_of_isTwoLocal {H : Subgroup G} (hH : IsTwoLocal H) : pCoreOf 2 H ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP1, hP2, rfl⟩ := hH
  intro hbot
  apply hP1
  have hle : P ≤ pCoreOf 2 (normalizer (P : Set G)) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_normalizer le_rfl hP2
  exact le_bot_iff.mp (hbot ▸ hle)

theorem sylowNormalizedMaximalLocalUniqueNormalizer_of (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat) :
    U3.SylowNormalizedMaximalLocalUniqueNormalizer := by
  intro G _ _ T L hs hnab hQ hT hL hTL hO2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup G := hs
  have hK : LocalSQTK G := (qtkeCore_of_cat hnab hQ).1
  have key : ∀ H : Subgroup G, L ⊔ T ≤ H → pCoreOf 2 H ≠ ⊥ → H ≤ normalizer (L : Set G) :=
    fun H hLTH hH => le_normalizer_of_isMaximalLocal hK h37 h38 h39 hT hL hTL hLTH hH
  have hLTM : L ⊔ T ≤ normalizer (L : Set G) := sup_le le_normalizer hTL
  have hLN : normalizer (L : Set G) ≤ normalizer (pCoreOf 2 L : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L
  have hNloc : IsTwoLocal (normalizer (pCoreOf 2 L : Set G)) :=
    ⟨pCoreOf 2 L, hO2, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L, rfl⟩
  have hNeq : normalizer (L : Set G) = normalizer (pCoreOf 2 L : Set G) :=
    le_antisymm hLN (key _ (hLTM.trans hLN) (pCoreOf_ne_bot_of_isTwoLocal hNloc))
  have hMloc : IsTwoLocal (normalizer (L : Set G)) := hNeq ▸ hNloc
  have hMmax : quasithinIsMaxTwoLocal (normalizer (L : Set G)) :=
    ⟨hMloc, fun H hH hle =>
      le_antisymm (key H (hLTM.trans hle) (pCoreOf_ne_bot_of_isTwoLocal hH)) hle⟩
  have huniq : ∀ M' : Subgroup G, quasithinIsMaxTwoLocal M' → L ⊔ T ≤ M' →
      M' = normalizer (L : Set G) := fun M' hM' hLTM' =>
    (hM'.2 _ hMloc (key M' hLTM' (pCoreOf_ne_bot_of_isTwoLocal hM'.1))).symm
  refine ⟨hNeq, ⟨hMmax, hLTM, huniq⟩, fun Q hQ1 hQ2 _ hLTQ => ?_⟩
  have hQloc : IsTwoLocal (normalizer (Q : Set G)) := ⟨Q, hQ1, hQ2, rfl⟩
  have hQle : normalizer (Q : Set G) ≤ normalizer (L : Set G) :=
    key _ hLTQ (pCoreOf_ne_bot_of_isTwoLocal hQloc)
  exact ⟨hQle, hMmax, hQle, fun M' hM' hQM' => huniq M' hM' (hLTQ.trans hQM')⟩

end CFSG.Quasithin.H13.NQCore
