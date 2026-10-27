module

public import CFSG.Quasithin.Vol2.F134LieF4Group
public import CFSG.LieType.Chevalley.SylowOpposition

public section

namespace CFSG.Quasithin.F134.LieG2

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.BorelTits CFSG.ABGLocalTools
open CFSG.Quasithin.F134.LieF4

theorem exists_proper_overgroup_of_not_dvd {Y : Type*} [Group Y] [Finite Y] (hBT : Holds Y 2)
    {U H : Subgroup Y} (hU : IsSylowOf 2 U ⊤) (hUH : U ≤ H)
    (hcard : ¬ Nat.card H ∣ (U.subgroupOf H).index.factorial) :
    ∃ Q : Subgroup Y, Q ≠ ⊤ ∧ H ≤ Q ∧ Subgroup.normalizer (U : Set Y) ≤ Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := (U.subgroupOf H).normalCore with hC
  have hCne : C ≠ ⊥ := by
    intro hbot
    have h := (U.subgroupOf H).index_normalCore_dvd_factorial_index
    rw [← hC, hbot, Subgroup.index_bot] at h
    exact hcard h
  set V := C.map H.subtype with hV
  have hVU : V ≤ U := by
    rintro _ ⟨c, hc, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (Subgroup.normalCore_le _ hc)
  have hVne : V ≠ ⊥ := by
    intro h
    apply hCne
    rwa [hV, Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective] at h
  have hVsub : V.subgroupOf H = C := by
    rw [hV, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
  have hHV : H ≤ Subgroup.normalizer (V : Set Y) := by
    have hn : (V.subgroupOf H).Normal := by
      rw [hVsub]
      exact Subgroup.normalCore_normal _
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le C)).1 hn
  obtain ⟨S, Q, hQ, hNQ, -, -, hSQ⟩ := hBT V hVne (hU.isPGroup.to_le hVU)
  have hHQ : H ≤ Q := hHV.trans hNQ
  exact ⟨Q, hQ, hHQ, normalizer_le_of_isSylowOf
    (isSylowOf_of_sylow S (Subgroup.le_normalizer.trans hSQ))
    (hU.of_le (hUH.trans hHQ) le_top) hSQ⟩

section Root

variable {τ : Tag} {K : Type} [Field K]

theorem rootSubgroup_single_le_posUnipotent (i : Fin τ.rank) :
    rootSubgroup τ K (Pi.single i 1) ≤ posUnipotent τ K := by
  rw [← rootSpan_singleton]
  exact rootSpan_le_posUnipotent fun α hα => by
    rw [Set.mem_singleton_iff] at hα
    subst hα
    exact ⟨isRoot_single τ i, by rw [height_single]; exact one_pos⟩

theorem rootSubgroup_single_le_borelGroup (i : Fin τ.rank) :
    rootSubgroup τ K (Pi.single i 1) ≤ borelGroup τ K :=
  (rootSubgroup_single_le_posUnipotent i).trans le_sup_right

end Root

section RankOne


variable {τ : Tag} {K : Type} [Field K]

theorem mem_borelGroup_or_mem_bruhatCell {i : Fin τ.rank} {x : ModGL τ K}
    (hx : x ∈ parabolicSubgroup τ K {i}) :
    x ∈ borelGroup τ K ∨ x ∈ bruhatCell τ K (simple τ i) := by
  have hx' : x ∈ (parabolicSubgroup τ K {i} : Set (ModGL τ K)) := hx
  rw [(standard_parabolic_cells τ K).1] at hx'
  obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.1 hx'
  rcases mem_parabolicWeylGroup_singleton hw with rfl | rfl
  · obtain ⟨b, hb, b', hb', rfl⟩ := mem_bruhatCell.1 hxw
    rw [canonicalRep_one, mul_one]
    exact Or.inl (mul_mem hb hb')
  · exact Or.inr hxw

theorem card_eq_card_inf_borelGroup_mul [Finite K] {i : Fin τ.rank} {H : Subgroup (ModGL τ K)}
    (hXH : rootSubgroup τ K (Pi.single i 1) ≤ H) (hHP : H ≤ parabolicSubgroup τ K {i})
    (hHB : ¬ H ≤ borelGroup τ K) :
    Nat.card H = Nat.card (H ⊓ borelGroup τ K : Subgroup (ModGL τ K)) * (Nat.card K + 1) := by
  classical
  have : Finite (ModGL τ K) := finite_modGL
  set X := rootSubgroup τ K (Pi.single i 1) with hX
  have hXspan : rootSpan τ K (inversionSet (simple τ i)) = X := by
    rw [inversionSet_simple, rootSpan_singleton]
  have hXB : X ≤ borelGroup τ K := rootSubgroup_single_le_borelGroup i
  have hcardX : Nat.card X = Nat.card K := by
    rw [← hXspan, card_rootSpan_inversionSet, CoxeterSystem.length_simple, pow_one]
  obtain ⟨h₀, hh₀, hh₀B⟩ := Set.not_subset.1 hHB
  have hh₀D : h₀ ∈ bruhatCell τ K (simple τ i) :=
    (mem_borelGroup_or_mem_bruhatCell (hHP hh₀)).resolve_left hh₀B
  obtain ⟨⟨b₀, u₀⟩, ⟨hb₀, hu₀⟩, rfl⟩ := (bijOn_bruhatCell (K := K) (simple τ i)).surjOn hh₀D
  simp only at hh₀ hu₀ hb₀
  rw [hXspan] at hu₀
  replace hb₀ : b₀ ∈ borelGroup τ K := hb₀
  replace hu₀ : u₀ ∈ X := hu₀
  replace hh₀ : b₀ * canonicalRep (coxeterSystem τ) K (simple τ i) * u₀ ∈ H := hh₀
  set n := canonicalRep (coxeterSystem τ) K (simple τ i) with hn
  set S₂ : Set (ModGL τ K) := (H : Set (ModGL τ K)) ∩ bruhatCell τ K (simple τ i) with hS₂
  have hunion : (H : Set (ModGL τ K)) =
      ((H ⊓ borelGroup τ K : Subgroup (ModGL τ K)) : Set (ModGL τ K)) ∪ S₂ := by
    ext x
    refine ⟨fun hx => ?_, ?_⟩
    · rcases mem_borelGroup_or_mem_bruhatCell (hHP hx) with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, h⟩
    · rintro (⟨hx, -⟩ | ⟨hx, -⟩) <;> exact hx
  have hdisj : Disjoint ((H ⊓ borelGroup τ K : Subgroup (ModGL τ K)) : Set (ModGL τ K)) S₂ := by
    refine Set.disjoint_left.2 fun x hx1 hx2 => ?_
    obtain ⟨b, hb, b', hb', rfl⟩ := mem_bruhatCell.1 hx2.2
    have hxB : b * n * b' ∈ borelGroup τ K := hx1.2
    apply weylElt_not_mem_borelGroup (K := K) i
    rw [← canonicalRep_simple (coxeterSystem τ) K i]
    have e : n = b⁻¹ * (b * n * b') * b'⁻¹ := by group
    rw [← hn, e]
    exact mul_mem (mul_mem (inv_mem hb) hxB) (inv_mem hb')
  have hbij : Set.BijOn (fun p : ModGL τ K × ModGL τ K => p.1 * b₀ * n * p.2)
      (((H ⊓ borelGroup τ K : Subgroup (ModGL τ K)) : Set (ModGL τ K)) ×ˢ (X : Set (ModGL τ K)))
      S₂ := by
    refine ⟨fun p hp => ⟨?_, ?_⟩, fun p hp p' hp' h => ?_, fun x hx => ?_⟩
    · have e : p.1 * b₀ * n * p.2 = p.1 * (b₀ * n * u₀) * (u₀⁻¹ * p.2) := by group
      show p.1 * b₀ * n * p.2 ∈ H
      rw [e]
      exact mul_mem (mul_mem hp.1.1 hh₀) (mul_mem (inv_mem (hXH hu₀)) (hXH hp.2))
    · exact mem_bruhatCell.2 ⟨p.1 * b₀, mul_mem hp.1.2 hb₀, p.2, hXB hp.2, rfl⟩
    · have hp1 : (p.1 * b₀, p.2) ∈ (borelGroup τ K : Set (ModGL τ K)) ×ˢ
          (rootSpan τ K (inversionSet (simple τ i)) : Set (ModGL τ K)) :=
        ⟨mul_mem hp.1.2 hb₀, by rw [hXspan]; exact hp.2⟩
      have hp1' : (p'.1 * b₀, p'.2) ∈ (borelGroup τ K : Set (ModGL τ K)) ×ˢ
          (rootSpan τ K (inversionSet (simple τ i)) : Set (ModGL τ K)) :=
        ⟨mul_mem hp'.1.2 hb₀, by rw [hXspan]; exact hp'.2⟩
      have h' := (bijOn_bruhatCell (K := K) (simple τ i)).injOn hp1 hp1' h
      simp only [Prod.mk.injEq, mul_left_inj] at h'
      exact Prod.ext h'.1 h'.2
    · obtain ⟨⟨b, u⟩, ⟨hb, hu⟩, rfl⟩ := (bijOn_bruhatCell (K := K) (simple τ i)).surjOn hx.2
      simp only at hb hu hx ⊢
      rw [hXspan] at hu
      replace hb : b ∈ borelGroup τ K := hb
      replace hu : u ∈ X := hu
      have hxH : b * n * u ∈ H := hx.1
      have e : b * b₀⁻¹ = b * n * u * u⁻¹ * u₀ * (b₀ * n * u₀)⁻¹ := by group
      have hbH : b * b₀⁻¹ ∈ H := by
        rw [e]
        exact mul_mem (mul_mem (mul_mem hxH (inv_mem (hXH hu))) (hXH hu₀)) (inv_mem hh₀)
      have hbB : b * b₀⁻¹ ∈ borelGroup τ K := mul_mem hb (inv_mem hb₀)
      refine ⟨(b * b₀⁻¹, u), ⟨⟨hbH, hbB⟩, hu⟩, ?_⟩
      show b * b₀⁻¹ * b₀ * n * u = b * n * u
      group
  have hS₂ : Nat.card S₂ = Nat.card (H ⊓ borelGroup τ K : Subgroup (ModGL τ K)) * Nat.card K := by
    rw [← Nat.card_congr hbij.equiv, Nat.card_congr (Equiv.Set.prod _ _), Nat.card_prod,
      ← hcardX]
    rfl
  calc Nat.card H = (H : Set (ModGL τ K)).ncard := (Nat.card_coe_set_eq _).symm
    _ = Nat.card (H ⊓ borelGroup τ K : Subgroup (ModGL τ K)) + Nat.card S₂ := by
      rw [hunion, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _),
        ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
      rfl
    _ = _ := by rw [hS₂]; ring

theorem card_parabolicSubgroup_singleton [Finite K] (i : Fin τ.rank) :
    Nat.card (parabolicSubgroup τ K {i}) = Nat.card (borelGroup τ K) * (Nat.card K + 1) := by
  have h := card_eq_card_inf_borelGroup_mul (H := parabolicSubgroup τ K {i})
    ((rootSubgroup_single_le_borelGroup i).trans (borelGroup_le_parabolicSubgroup _)) le_rfl
    fun h => weylElt_not_mem_borelGroup (K := K) i
      (h (weylElt_mem_parabolicSubgroup (Set.mem_singleton i)))
  rwa [inf_eq_right.2 (borelGroup_le_parabolicSubgroup _)] at h

theorem le_borelGroup_or_dvd [Finite K] {i : Fin τ.rank} {H : Subgroup (ModGL τ K)}
    (hHP : H ≤ parabolicSubgroup τ K {i}) (hUH : posUnipotent τ K ≤ H) :
    H ≤ borelGroup τ K ∨ Nat.card K + 1 ∣ (posUnipotent τ K).relIndex H := by
  by_cases hHB : H ≤ borelGroup τ K
  · exact Or.inl hHB
  right
  have hXH := (rootSubgroup_single_le_posUnipotent (K := K) i).trans hUH
  have hcard := card_eq_card_inf_borelGroup_mul hXH hHP hHB
  have hUB : posUnipotent τ K ≤ borelGroup τ K := le_sup_right
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le (le_inf hUH hUB)
  have hrel := Subgroup.relIndex_mul_card (posUnipotent τ K) H
  rw [inf_eq_left.2 hUH, hcard, hm] at hrel
  have hpos : 0 < Nat.card (posUnipotent τ K) := Nat.card_pos
  refine ⟨m, Nat.eq_of_mul_eq_mul_right hpos ?_⟩
  rw [hrel]
  ring

theorem exists_le_parabolicSubgroup_singleton (hτ : τ.rank = 2) {Q : Subgroup (ModGL τ K)}
    (hBQ : borelGroup τ K ≤ Q) (hQC : Q ≤ adjointGroup τ K) (hQ : Q ≠ adjointGroup τ K) :
    ∃ i, Q ≤ parabolicSubgroup τ K {i} := by
  have hA := (borel_overgroup_classification τ K).1 Q hBQ hQC
  by_cases h : ∀ j : Fin τ.rank, weylElt τ K j 1 ∈ Q
  · refine absurd ?_ hQ
    rw [hA, ← (standard_parabolic_cells τ K).2.2.2.2.2.1]
    congr 1
    ext j
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact h j
  · obtain ⟨j, hj⟩ := not_forall.1 h
    have hj2 := j.2
    let i : Fin τ.rank := ⟨1 - (j : ℕ), by omega⟩
    refine ⟨i, ?_⟩
    rw [hA]
    refine (parabolicSubgroup_le_parabolicSubgroup_iff).2 fun k hk => ?_
    have hkj : k ≠ j := fun e => hj (e ▸ hk)
    have hk2 := k.2
    have hkj' : (k : ℕ) ≠ j := fun e => hkj (Fin.ext e)
    exact Fin.ext (by simp only [i]; omega)

theorem not_three_dvd_card_borelGroup_of_card_eight [Finite K] (hK : Nat.card K = 8) :
    ¬ 3 ∣ Nat.card (borelGroup τ K) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [card_borelGroup, card_posUnipotent, hK]
  intro h
  rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h
  · obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h
    have h1 := pow_card_sub_one_eq_one_of_mem_diagonalGroup (torusGroup_le_diagonalGroup x.2)
    rw [hK] at h1
    have h7 : orderOf x ∣ 7 := orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using h1))
    rw [hx] at h7
    norm_num at h7
  · have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    norm_num at this

theorem false_of_le_parabolicSubgroup_of_card_eight [Finite K]
    (hK : Nat.card K = 8) {i : Fin τ.rank} {P : Subgroup (ModGL τ K)}
    (hPP : P ≤ parabolicSubgroup τ K {i}) (hP : Nat.card P = 9) (hexp : ∀ x ∈ P, x ^ 3 = 1) :
    False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (ModGL τ K) := finite_modGL
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (k := 3) (by norm_num) (by rw [hK]; norm_num)
  have hB3 := not_three_dvd_card_borelGroup_of_card_eight (τ := τ) hK
  have hcardP : Nat.card (parabolicSubgroup τ K {i}) = 9 * Nat.card (borelGroup τ K) := by
    rw [card_parabolicSubgroup_singleton, hK, mul_comm]
  have hsyl : ∀ S : Subgroup (ModGL τ K), S ≤ parabolicSubgroup τ K {i} → Nat.card S = 9 →
      IsSylowOf 3 S (parabolicSubgroup τ K {i}) := by
    intro S hS hS9
    rw [isSylowOf_iff]
    refine ⟨hS, IsPGroup.of_card (n := 2) (by rw [hS9]; norm_num), ?_⟩
    have := Subgroup.relIndex_mul_card S (parabolicSubgroup τ K {i})
    rw [inf_eq_left.2 hS, hS9, hcardP] at this
    have h : S.relIndex (parabolicSubgroup τ K {i}) = Nat.card (borelGroup τ K) := by
      omega
    rwa [h]
  obtain ⟨ρ, -, -, -, -, hρrange, hρker, -, -⟩ := exceptional_ordinary_rank_one_central_image τ K i
  have hρinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    obtain ⟨l, hl2, hgl⟩ := hρker g hg
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have hl0 : ((l : K) - 1) ^ 2 = 0 := by linear_combination hl2 + (1 - (l : K)) * h2
    have hl1 : (l : K) = 1 := sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hl0)
    ext a b
    rw [hgl, hl1, one_smul]
    rfl
  have hM : ρ.range ≤ parabolicSubgroup τ K {i} := by
    rw [hρrange, Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact borelGroup_le_parabolicSubgroup _ (xUnit_mem_borelGroup i c)
    · exact yUnit_mem_parabolicSubgroup i c
  obtain ⟨S, hS⟩ := Sylow.exists_subgroup_card_pow_prime (G := SL2 K) 3 (n := 2)
    (by rw [card_sl2_eight hK]; norm_num)
  have hSG := hsyl (S.map ρ) ((Subgroup.map_le_range _ S).trans hM)
    (by rw [Subgroup.card_map_of_injective hρinj, hS]; norm_num)
  obtain ⟨g, -, hSg⟩ := exists_mem_eq_map_conj_of_isSylowOf (hsyl P hPP hP) hSG
  refine noElemNine_sl2_eight hK S (by rw [hS]; norm_num) fun s hs => hρinj ?_
  have hfs : ρ s ∈ P.map (MulAut.conj g).toMonoidHom := hSg ▸ ⟨s, hs, rfl⟩
  obtain ⟨x, hx, hxs⟩ := hfs
  rw [map_pow, ← hxs, map_one, ← map_pow, hexp x hx, map_one]

end RankOne

theorem ncard_posRoots_G2 :
    {α : Fin Tag.G2.rank → ℤ | IsRoot .G2 α ∧ 0 < height α}.ncard = 6 := by
  have h : {α : Fin Tag.G2.rank → ℤ | IsRoot .G2 α ∧ 0 < height α} =
      (((rootFinset .G2).filter fun β => 0 < height β : Finset _) : Set _) := by
    ext d
    rw [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_filter, mem_rootFinset]
  rw [h, Set.ncard_coe_finset]
  decide +kernel

section G2


variable {K : Type} [Field K]

theorem le_borelGroup_of_card_eq [Finite K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) {H P : Subgroup (ModGL .G2 K)}
    (hHC : H ≤ adjointGroup .G2 K) (hUH : posUnipotent .G2 K ≤ H)
    (hH : Nat.card H = 9 * Nat.card (posUnipotent .G2 K)) (hPH : P ≤ H) (hP : Nat.card P = 9)
    (hexp : ∀ x ∈ P, x ^ 3 = 1) : H ≤ borelGroup .G2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega) hK
  have : Finite (ModGL .G2 K) := finite_modGL
  set C := adjointGroup .G2 K with hC
  have hBC : borelGroup .G2 K ≤ C :=
    ((triangular_borel_structure.{0, 0} .G2 K).2.2.2.2.2.2.2.2.2.2.2 K).1
  have hUC : posUnipotent .G2 K ≤ C := le_sup_right.trans hBC
  have hUcard : Nat.card (posUnipotent .G2 K) = 2 ^ (6 * n) := by
    rw [card_posUnipotent, ncard_posRoots_G2, hK, ← pow_mul, mul_comm]
  obtain ⟨hUp, hUi⟩ := isPGroup_and_not_dvd_index 2 hUC card_posUnipotent
  have hU : IsSylowOf 2 ((posUnipotent .G2 K).subgroupOf C) ⊤ := by
    rw [isSylowOf_iff]
    exact ⟨le_top, hUp, by rwa [Subgroup.relIndex_top_right]⟩
  have hUH' : (posUnipotent .G2 K).subgroupOf C ≤ H.subgroupOf C := fun x hx => hUH hx
  have hidx : (((posUnipotent .G2 K).subgroupOf C).subgroupOf (H.subgroupOf C)).index = 9 := by
    have h := (((posUnipotent .G2 K).subgroupOf C).subgroupOf (H.subgroupOf C)).index_mul_card
    rw [card_subgroupOf_of_le hUH', card_subgroupOf_of_le hUC,
      card_subgroupOf_of_le hHC, hH] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  have hcard : ¬ Nat.card (H.subgroupOf C) ∣
      (((posUnipotent .G2 K).subgroupOf C).subgroupOf (H.subgroupOf C)).index.factorial := by
    rw [hidx, card_subgroupOf_of_le hHC, hH, hUcard]
    intro h
    have h12 : 2 ^ 12 ∣ Nat.factorial 9 :=
      (pow_dvd_pow 2 (by omega : 12 ≤ 6 * n)).trans ((Dvd.intro_left _ rfl).trans h)
    exact absurd h12 (by decide)
  obtain ⟨Q', hQ', hHQ', hNQ'⟩ := exists_proper_overgroup_of_not_dvd
    (holds_adjointGroup_tag .G2 K 2) hU hUH' hcard
  have hBN : borelGroup .G2 K ≤ Subgroup.normalizer (posUnipotent .G2 K : Set (ModGL .G2 K)) := by
    rw [← (borel_self_normalizers .G2 K).1]
    exact inf_le_right
  have hBQ : borelGroup .G2 K ≤ Q'.map C.subtype := by
    intro b hb
    refine ⟨⟨b, hBC hb⟩, hNQ' ?_, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro x
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.mem_normalizer_iff.1 (hBN hb) x
  have hQC : Q'.map C.subtype ≤ C := Subgroup.map_subtype_le Q'
  have hQne : Q'.map C.subtype ≠ C := by
    intro hQeq
    refine hQ' (eq_top_iff.2 fun x _ => ?_)
    have hx : (x : ModGL .G2 K) ∈ Q'.map C.subtype := by
      rw [hQeq]
      exact x.2
    obtain ⟨y, hy, hyx⟩ := hx
    rwa [show y = x from Subtype.ext hyx] at hy
  have hHQ : H ≤ Q'.map C.subtype := fun h hh => ⟨⟨h, hHC hh⟩, hHQ' hh, rfl⟩
  obtain ⟨i, hi⟩ := exists_le_parabolicSubgroup_singleton rfl hBQ hQC hQne
  rcases le_borelGroup_or_dvd (hHQ.trans hi) hUH with hB | hdvd
  · exact hB
  exfalso
  have hrel : (posUnipotent .G2 K).relIndex H = 9 := by
    have h := Subgroup.relIndex_mul_card (posUnipotent .G2 K) H
    rw [inf_eq_left.2 hUH, hH] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  rw [hrel] at hdvd
  have hq4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).1
    (show Nat.card K + 1 ∣ 3 ^ 2 by simpa using hdvd)
  have hq8 : Nat.card K = 8 := by
    interval_cases k <;> simp at hk' <;> omega
  exact false_of_le_parabolicSubgroup_of_card_eight hq8 ((hPH.trans hHQ).trans hi) hP hexp

end G2

end CFSG.Quasithin.F134.LieG2
