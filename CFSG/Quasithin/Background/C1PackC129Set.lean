module

public import CFSG.Quasithin.Background.C1PackSolv

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace C1Pack

variable {G : Type} [Group G] [Finite G]

theorem chiBlocks_eq_of_three {X : Subgroup G} (hX : CharTwo X) (hSQ : IsSQTKTC X)
    {A B C : Subgroup G} (hA : IsChiBlock X A) (hB : IsChiBlock X B) (hC : IsChiBlock X C) :
    A = B ∨ A = C ∨ B = C := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hAB, hAC, hBC⟩ := hcon
  exact C1GN.three_blocks_false hSQ hA.1.2.1 hB.1.2.1 hC.1.2.1
    ⟨hA.1.1.2.1, hB.1.1.2.1, hC.1.1.2.1⟩
    ⟨C1GN.three_dvd_card_of_isChiBlock hA, C1GN.three_dvd_card_of_isChiBlock hB,
      C1GN.three_dvd_card_of_isChiBlock hC⟩ hAB hAC hBC
    ⟨distinctBlocksCommuteStatement X A B hX hA.1 hB.1 hAB,
      distinctBlocksCommuteStatement X A C hX hA.1 hC.1 hAC,
      distinctBlocksCommuteStatement X B C hX hB.1 hC.1 hBC⟩

omit [Finite G] in
theorem inv_mul_mem_normalizer_of_map_conj_eq {B : Subgroup G} {x z : G}
    (h : B.map (MulAut.conj x).toMonoidHom = B.map (MulAut.conj z).toMonoidHom) :
    x⁻¹ * z ∈ Subgroup.normalizer (B : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro w
  have h1 := SetLike.ext_iff.mp h (z * w * z⁻¹)
  have e1 : z⁻¹ * (z * w * z⁻¹) * z = w := by group
  have e2 : x⁻¹ * (z * w * z⁻¹) * x = (x⁻¹ * z) * w * (x⁻¹ * z)⁻¹ := by group
  have h2 : x⁻¹ * (z * w * z⁻¹) * x ∈ B ↔ z⁻¹ * (z * w * z⁻¹) * z ∈ B := by
    have := h1
    rw [show B.map (MulAut.conj x).toMonoidHom = conjByElt x B from rfl,
      show B.map (MulAut.conj z).toMonoidHom = conjByElt z B from rfl, mem_conjByElt,
      mem_conjByElt] at this
    exact this
  rw [e1, e2] at h2
  exact h2.symm

theorem exists_mem_conj_ne_of_chiBlock {X T B : Subgroup G} (hX : CharTwo X) (hSQ : IsSQTKTC X)
    (hT : IsSylowTwoOf T X) (hB : IsChiBlock X B) {x : G} (hx : x ∈ X)
    (hne : B.map (MulAut.conj x).toMonoidHom ≠ B) :
    ∃ t ∈ T, B.map (MulAut.conj t).toMonoidHom ≠ B := by
  by_contra hcon
  push Not at hcon
  set S : Subgroup G := X ⊓ Subgroup.normalizer (B : Set G) with hS
  have hTS : T ≤ S := fun t ht =>
    ⟨hT.1 ht, Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hcon t ht)⟩
  have hSX : S ≤ X := inf_le_left
  have hxS : x ∉ S := fun h => hne (Subgroup.mem_normalizer_iff_map_conj_eq.mp h.2)
  have hBx : IsChiBlock X (B.map (MulAut.conj x).toMonoidHom) := L238.isChiBlock_conj hB hx
  have hdich : ∀ z ∈ X, z ∈ S ∨ x⁻¹ * z ∈ S := by
    intro z hz
    have hBz : IsChiBlock X (B.map (MulAut.conj z).toMonoidHom) := L238.isChiBlock_conj hB hz
    rcases chiBlocks_eq_of_three hX hSQ hBx hBz hB with h | h | h
    · right
      exact ⟨X.mul_mem (X.inv_mem hx) hz, inv_mul_mem_normalizer_of_map_conj_eq h⟩
    · exact absurd h hne
    · left
      exact ⟨hz, Subgroup.mem_normalizer_iff_map_conj_eq.mpr h⟩
  have hidx : (S.subgroupOf X).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨x, hx⟩, fun b => ?_⟩
    have hbX : (b : G) ∈ X := b.2
    by_cases hb : (b : G) ∈ S
    · right
      refine ⟨Subgroup.mem_subgroupOf.mpr hb, fun hbx => ?_⟩
      have hbx' : (b : G) * x ∈ S := Subgroup.mem_subgroupOf.mp hbx
      apply hxS
      have := S.mul_mem (S.inv_mem hb) hbx'
      simpa using this
    · left
      refine ⟨?_, fun hb' => hb (Subgroup.mem_subgroupOf.mp hb')⟩
      rw [Subgroup.mem_subgroupOf]
      have hbinvX : (b : G)⁻¹ ∈ X := X.inv_mem hbX
      rcases hdich _ hbinvX with h | h
      · exact absurd (by simpa using S.inv_mem h) hb
      · have := S.inv_mem h
        simpa [mul_assoc] using this
  have hrel : T.relIndex S * S.relIndex X = T.relIndex X := Subgroup.relIndex_mul_relIndex T S X hTS hSX
  apply hT.2.2
  have h2 : S.relIndex X = 2 := hidx
  rw [show (T.subgroupOf X).index = T.relIndex X from rfl, ← hrel, h2]
  exact Dvd.intro_left _ rfl

theorem conj_mem_chiBlocksOutside {X T M : Subgroup G} (hX : CharTwo X) (hSQ : IsSQTKTC X)
    (hT : IsSylowTwoOf T X) (hTM : T ≤ M) {B : Subgroup G}
    (hB : B ∈ C1GN.chiBlocksOutside X T M) {x : G} (hx : x ∈ X) :
    B.map (MulAut.conj x).toMonoidHom ∈ C1GN.chiBlocksOutside X T M := by
  by_cases hxB : B.map (MulAut.conj x).toMonoidHom = B
  · rw [hxB]
    exact hB
  obtain ⟨t, ht, htB⟩ := exists_mem_conj_ne_of_chiBlock hX hSQ hT hB.1 hx hxB
  have hBt := L238.mem_chiBlocksOutside_conj hT.1 hTM hB ht
  have hBx : IsChiBlock X (B.map (MulAut.conj x).toMonoidHom) := L238.isChiBlock_conj hB.1 hx
  rcases chiBlocks_eq_of_three hX hSQ hB.1 hBx hBt.1 with h | h | h
  · exact absurd h.symm hxB
  · exact absurd h.symm htB
  · rw [h]
    exact hBt

theorem lemma_C128_solv_set {C₁ C₂ : Subgroup G → Subgroup G} (hC : IsGNChoice C₁ C₂)
    {X T M : Subgroup G} (hX : CharTwo X) (hSQ : IsSQTKTC X) (hT : IsSylowTwoOf T X)
    (hT0 : T ≠ ⊥) (hsolv : perfectCore X ≤ Subgroup.centralizer (VZ T X : Set G))
    (hM : (X ⊓ Subgroup.centralizer (C₁ T : Set G)) ⊔ (X ⊓ Subgroup.normalizer (C₂ T : Set G)) ≤ M)
    (hMX : M ≤ X) :
    ∃ (r : ℕ) (L : Fin r → Subgroup G), r ≤ 2 ∧
      (∀ i, IsChiBlock X (L i) ∧ ⁅L i, thompsonJ T⁆ = L i ∧ ¬ L i ≤ M) ∧
      ∀ x ∈ X, ∃ m ∈ M, ∃ y : Fin r → G, (∀ i, y i ∈ L i) ∧ x = m * (List.ofFn y).prod := by
  classical
  obtain ⟨-, -, -, -, hC₂B, hC₂char, -⟩ := hC.pair T hT.2.1 hT0
  have hNC₂ : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (C₂ T : Set G) :=
    (normalizer_le_normalizer_baum T).trans
      (normalizer_le_normalizer_of_characteristic_subgroupOf hC₂B hC₂char)
  have hTM : T ≤ M := fun t ht =>
    hM (Subgroup.mem_sup_right ⟨hT.1 ht, hNC₂ (Subgroup.le_normalizer ht)⟩)
  set 𝔊 : Set (Subgroup G) := C1GN.chiBlocksOutside X T M with h𝔊
  set G₀ : Subgroup G := ⨆ B : 𝔊, (B : Subgroup G) with hG₀
  have hBle : ∀ B ∈ 𝔊, B ≤ G₀ := fun B hB => le_iSup (fun B : 𝔊 => (B : Subgroup G)) ⟨B, hB⟩
  have hXle : X ≤ M ⊔ G₀ := by
    rcases lemma_C128_solv_of_le_Solv hC hX hSQ hT hT0 hsolv hM hMX with h | ⟨s, L, -, -, hL, hXL⟩
    · exact h.le.trans le_sup_left
    · rw [hXL]
      exact sup_le_sup_left (iSup_le fun i => hBle _ (hL i)) M
  have hconj : ∀ x ∈ X, ∀ g ∈ G₀, x * g * x⁻¹ ∈ G₀ := by
    intro x hx g hg
    refine Subgroup.iSup_induction (fun B : 𝔊 => (B : Subgroup G))
      (C := fun g => x * g * x⁻¹ ∈ G₀) hg (fun B b hb => ?_) (by simp) (fun g h hg hh => ?_)
    · have hmem := conj_mem_chiBlocksOutside hX hSQ hT hTM B.2 hx
      have hxb : x * b * x⁻¹ ∈ B.1.map (MulAut.conj x).toMonoidHom := ⟨b, hb, rfl⟩
      exact hBle _ hmem hxb
    · have := G₀.mul_mem hg hh
      simpa [mul_assoc] using this
  have hnorm : X ≤ Subgroup.normalizer (G₀ : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro g
    refine ⟨fun hg => hconj x hx g hg, fun hg => ?_⟩
    have := hconj x⁻¹ (X.inv_mem hx) _ hg
    simpa [mul_assoc] using this
  have hset : ((M ⊔ G₀ : Subgroup G) : Set G) = (M : Set G) * (G₀ : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right M G₀ (hMX.trans hnorm)
  have hXmul : ∀ x ∈ X, ∃ m ∈ M, ∃ g ∈ G₀, x = m * g := by
    intro x hx
    have : x ∈ ((M ⊔ G₀ : Subgroup G) : Set G) := hXle hx
    rw [hset] at this
    obtain ⟨m, hm, g, hg, rfl⟩ := this
    exact ⟨m, hm, g, hg, rfl⟩
  rcases Set.eq_empty_or_nonempty 𝔊 with h0 | ⟨A, hA⟩
  ·
    have hG₀bot : G₀ = ⊥ := by
      refine le_antisymm (iSup_le fun B => ?_) bot_le
      have hB' : (B : Subgroup G) ∈ 𝔊 := B.2
      exact absurd hB' (Set.eq_empty_iff_forall_notMem.mp h0 _)
    refine ⟨0, Fin.elim0, Nat.zero_le _, fun i => i.elim0, fun x hx => ?_⟩
    obtain ⟨m, hm, g, hg, rfl⟩ := hXmul x hx
    rw [hG₀bot, Subgroup.mem_bot] at hg
    exact ⟨m, hm, Fin.elim0, fun i => i.elim0, by simp [hg]⟩
  · by_cases hB : ∃ B ∈ 𝔊, B ≠ A
    · obtain ⟨B, hB𝔊, hBA⟩ := hB
      have hall : ∀ C ∈ 𝔊, C = A ∨ C = B := fun C hC' => by
        rcases chiBlocks_eq_of_three hX hSQ hA.1 hB𝔊.1 hC'.1 with h | h | h
        · exact absurd h.symm hBA
        · exact Or.inl h.symm
        · exact Or.inr h.symm
      have hG₀eq : G₀ = A ⊔ B := by
        refine le_antisymm (iSup_le fun C => ?_) (sup_le (hBle A hA) (hBle B hB𝔊))
        rcases hall C.1 C.2 with h | h
        · rw [h]
          exact le_sup_left
        · rw [h]
          exact le_sup_right
      have hcomm : ⁅A, B⁆ = ⊥ := distinctBlocksCommuteStatement X A B hX hA.1.1 hB𝔊.1.1 hBA.symm
      have hAN : A ≤ Subgroup.normalizer (B : Set G) :=
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm).trans
          (Subgroup.centralizer_le_normalizer _)
      have hABset : ((A ⊔ B : Subgroup G) : Set G) = (A : Set G) * (B : Set G) :=
        Subgroup.coe_mul_of_left_le_normalizer_right A B hAN
      refine ⟨2, ![A, B], le_rfl, fun i => ?_, fun x hx => ?_⟩
      · fin_cases i
        · exact hA
        · exact hB𝔊
      · obtain ⟨m, hm, g, hg, rfl⟩ := hXmul x hx
        rw [hG₀eq] at hg
        have hg' : g ∈ ((A ⊔ B : Subgroup G) : Set G) := hg
        rw [hABset] at hg'
        obtain ⟨a, ha, b, hb, rfl⟩ := hg'
        refine ⟨m, hm, ![a, b], fun i => ?_, ?_⟩
        · fin_cases i
          · exact ha
          · exact hb
        · simp [List.ofFn_succ]
    · push Not at hB
      have hG₀eq : G₀ = A := by
        refine le_antisymm (iSup_le fun C => (hB C.1 C.2).le) (hBle A hA)
      refine ⟨1, fun _ => A, by norm_num, fun _ => hA, fun x hx => ?_⟩
      obtain ⟨m, hm, g, hg, rfl⟩ := hXmul x hx
      rw [hG₀eq] at hg
      exact ⟨m, hm, fun _ => g, fun _ => hg, by simp⟩

end C1Pack

end CFSG.Quasithin
