module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenTwelveC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenTwelveD
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenT7Conj

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s15_Twelve_s_le (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (h : Hyp154 D V₀ V L) (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥) {n : ℕ} {k : G}
    (hk : Cond1512 n D.M V k) (hn : n < gamma15 D.M V₀ V hV L)
    (hgood : ∀ X ∈ wConj D.M V₀ V hV L,
      E3.mQuot V (centralizer (ySub15 D.M V₀ V hV L X k : Set G)) < gamma15 D.M V₀ V hV L)
    (hgood' : ∀ X ∈ wConj D.M V₀ V hV L,
      E3.mQuot V (centralizer (ySub15 D.M V₀ V hV L X k⁻¹ : Set G)) <
        gamma15 D.M V₀ V hV L) {X : Subgroup G} (hX : X ∈ wConj D.M V₀ V hV L) :
    s15 D.M V₀ V hV L ≤ E3.mQuot V (centralizer (ySub15 D.M V₀ V hV L X k : Set G)) := by
  have hk' := cond1512_inv hk
  have hall : {Z : Subgroup G | Z ∈ wConj D.M V₀ V hV L ∧
      ¬ fSub15 D.M V₀ V hV L Z ≤ conjSubgroup D.M k} = wConj D.M V₀ V hV L := by
    ext Z
    constructor
    · exact fun hZ => hZ.1
    · intro hZ
      refine ⟨hZ, fun hle => ?_⟩
      refine s15_Twelve_whole D h1217 h hV hL hk' hZ ?_ (hgood' Z hZ)
      have h1 := E3.conjSubgroup_mono_left k⁻¹ hle
      rwa [conjSubgroup_conjSubgroup_inv] at h1
  have h2 := s15_Twelve_card_le D h1217 h hV hL hk hn hX (hgood X hX)
  rwa [hall, ncard_wConj D h.hyp151 hV] at h2

theorem s15_Twelve_bigS (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (h : Hyp154 D V₀ V L) (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥) {n : ℕ} {k : G}
    (hk : Cond1512 n D.M V k) (hn2 : n ≤ 2) (hγ : gamma15 D.M V₀ V hV L = n + 1)
    (hs : 4 ≤ s15 D.M V₀ V hV L) : False := by
  have hk' := cond1512_inv hk
  have hn : n < gamma15 D.M V₀ V hV L := by omega
  have hmem : wSub V₀ V hV L ∈ wConj D.M V₀ V hV L :=
    ⟨1, D.M.one_mem, by simp [conjSubgroup_one]⟩
  have hgood : ∀ X ∈ wConj D.M V₀ V hV L,
      E3.mQuot V (centralizer (ySub15 D.M V₀ V hV L X k : Set G)) < gamma15 D.M V₀ V hV L :=
    fun X hX => by
      have := (s15_Twelve_rank_bound D h hV hk hX).2 (Or.inl hs)
      omega
  have hgood' : ∀ X ∈ wConj D.M V₀ V hV L,
      E3.mQuot V (centralizer (ySub15 D.M V₀ V hV L X k⁻¹ : Set G)) <
        gamma15 D.M V₀ V hV L :=
    fun X hX => by
      have := (s15_Twelve_rank_bound D h hV hk' hX).2 (Or.inl hs)
      omega
  have h1 := s15_Twelve_s_le D h1217 h hV hL hk hn hgood hgood' hmem
  have h2 := (s15_Twelve_rank_bound D h hV hk hmem).2 (Or.inl hs)
  omega

theorem s15_Twelve_exists_config_caseI
    (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (h : Hyp154 D V₀ V L) (hV : IsElemAbelian 2 V)
    (hL : barSub V₀ V hV L ≠ ⊥) {n : ℕ} {k : G}
    (hk : Cond1512 n D.M V k) (hn2 : n ≤ 2)
    (hn : n + 2 ≤ gamma15 D.M V₀ V hV L)
    (hs : 1 < s15 D.M V₀ V hV L) :
    ∃ Z F C K : Subgroup G,
      Z ∈ wConj D.M V₀ V hV L ∧
      s15T7Config D.M (Z ⊔ v1Sub D.M V₀ V hV L)
        (v1Sub D.M V₀ V hV L) F C K := by
  have hk' : Cond1512 n D.M V k⁻¹ := cond1512_inv hk
  have hmem : wSub V₀ V hV L ∈ wConj D.M V₀ V hV L :=
    ⟨1, D.M.one_mem, by simp [conjSubgroup_one]⟩
  have hY : ySub15 D.M V₀ V hV L (wSub V₀ V hV L) k ≤ D.M := inf_le_right
  have hgood : ∀ X ∈ wConj D.M V₀ V hV L,
      E3.mQuot V (centralizer (ySub15 D.M V₀ V hV L X k : Set G)) <
        gamma15 D.M V₀ V hV L := by
    intro X hX
    have h1 := (s15_Twelve_rank_bound D h hV hk hX).1
    omega
  have hgood' : ∀ X ∈ wConj D.M V₀ V hV L,
      E3.mQuot V (centralizer (ySub15 D.M V₀ V hV L X k⁻¹ : Set G)) <
        gamma15 D.M V₀ V hV L := by
    intro X hX
    have h1 := (s15_Twelve_rank_bound D h hV hk' hX).1
    omega
  have hnotle : ∀ Z ∈ wConj D.M V₀ V hV L,
      ¬ fSub15 D.M V₀ V hV L Z ≤ conjSubgroup D.M k := by
    intro Z hZ hle
    refine s15_Twelve_whole D h1217 h hV hL hk' hZ ?_ (hgood' Z hZ)
    have h1 := E3.conjSubgroup_mono_left k⁻¹ hle
    rwa [conjSubgroup_conjSubgroup_inv] at h1
  have hfix : ∀ Z ∈ wConj D.M V₀ V hV L,
      ySub15 D.M V₀ V hV L (wSub V₀ V hV L) k ≤
        normalizer (fSub15 D.M V₀ V hV L Z : Set G) ∧
      ySub15 D.M V₀ V hV L (wSub V₀ V hV L) k ≤ normalizer (Z : Set G) :=
    fun Z hZ => s15_Twelve_fixes D h1217 h.hyp151 hV hL hY (hgood _ hmem) hZ
  have hsle : s15 D.M V₀ V hV L ≤
      E3.mQuot V (centralizer (ySub15 D.M V₀ V hV L (wSub V₀ V hV L) k : Set G)) :=
    s15_Twelve_s_le D h1217 h hV hL hk (by omega) hgood hgood' hmem
  have hcW := (s15_Twelve_rank_bound D h hV hk hmem).1
  let S : Finset (Subgroup G) := (Set.toFinite (wConj D.M V₀ V hV L)).toFinset
  have hSmem : ∀ Z ∈ S, Z ∈ wConj D.M V₀ V hV L :=
    fun Z hZ => (Set.toFinite (wConj D.M V₀ V hV L)).mem_toFinset.1 hZ
  have hcount := s15_Twelve_count D h1217 h.hyp151 hV hL hY
    (fun Z hZ => (hfix Z hZ).1) S hSmem
  have hcard : S.card = s15 D.M V₀ V hV L := by
    change (Set.toFinite (wConj D.M V₀ V hV L)).toFinset.card = s15 D.M V₀ V hV L
    rw [← Set.ncard_eq_toFinset_card (wConj D.M V₀ V hV L) (Set.toFinite _),
      ncard_wConj D h.hyp151 hV]
  have hSncard : 2 ≤ S.card := by rw [hcard]; omega
  have hexists : ∃ Z ∈ S, E3.mQuot (fSub15 D.M V₀ V hV L Z)
      (kSub15 D.M V₀ V hV L
        (ySub15 D.M V₀ V hV L (wSub V₀ V hV L) k) Z) = 1 := by
    by_contra hnone
    push Not at hnone
    have hpos : ∀ Z ∈ S, 1 ≤ E3.mQuot (fSub15 D.M V₀ V hV L Z)
        (kSub15 D.M V₀ V hV L
          (ySub15 D.M V₀ V hV L (wSub V₀ V hV L) k) Z) :=
      fun Z hZ => s15_Twelve_axis_pos D h hV hk (by omega) hmem (hSmem Z hZ)
        (hnotle Z (hSmem Z hZ))
    have htwo : ∀ Z ∈ S, 2 ≤ E3.mQuot (fSub15 D.M V₀ V hV L Z)
        (kSub15 D.M V₀ V hV L
          (ySub15 D.M V₀ V hV L (wSub V₀ V hV L) k) Z) :=
      fun Z hZ => by
        have h1 := hpos Z hZ
        have h2 := hnone Z hZ
        omega
    have hle := Finset.card_nsmul_le_sum S
      (fun Z => E3.mQuot (fSub15 D.M V₀ V hV L Z)
        (kSub15 D.M V₀ V hV L
          (ySub15 D.M V₀ V hV L (wSub V₀ V hV L) k) Z)) 2 htwo
    have h2c : 2 * S.card ≤
        E3.mQuot V (centralizer
          (ySub15 D.M V₀ V hV L (wSub V₀ V hV L) k : Set G)) := by
      have h3 := le_trans hle hcount
      simpa [Nat.nsmul_eq_mul, mul_comm] using h3
    omega
  obtain ⟨Z, hZS, htZ⟩ := hexists
  have hZmem : Z ∈ wConj D.M V₀ V hV L := hSmem Z hZS
  have hZk : ¬ fSub15 D.M V₀ V hV L Z ≤ conjSubgroup D.M k := hnotle Z hZmem
  obtain ⟨C, hCle, hCchar, _, hgammaC⟩ :=
    s15_Twelve_kernel D h hV hk hmem hZmem hZk
  have hV1K : v1Sub D.M V₀ V hV L ≤ kSub15 D.M V₀ V hV L
      (ySub15 D.M V₀ V hV L (wSub V₀ V hV L) k) Z := by
    intro v hv
    rw [s15_Twelve_mem_kSub15 D h.hyp151 hV hY hZmem]
    refine ⟨Subgroup.mem_sup_right hv, fun y hy => ?_⟩
    have hyM : y ∈ D.M := hy.2
    have h1 : y * v * y⁻¹ ∈ v1Sub D.M V₀ V hV L :=
      (Subgroup.mem_normalizer_iff.1
        (s15_Infra_le_normalizer_v1Sub h.hyp151.hyp125 hV hyM) v).1 hv
    exact (v1Sub D.M V₀ V hV L).mul_mem h1 ((v1Sub D.M V₀ V hV L).inv_mem hv)
  have hYel : IsElemAbelian 2 (ySub15 D.M V₀ V hV L (wSub V₀ V hV L) k) := by
    refine (E3.isElemAbelian_conjSubgroup hV k).mono ?_
    intro x hx
    exact E3.conjSubgroup_mono_left k
      (sup_le (preTil_le V₀ V hV (wTil V₀ V hV L))
        (s15_Infra_v1Sub_le h.hyp151.hyp125 hV)) hx.1
  have hKle : kSub15 D.M V₀ V hV L
      (ySub15 D.M V₀ V hV L (wSub V₀ V hV L) k) Z ≤ fSub15 D.M V₀ V hV L Z :=
    inf_le_left
  exact ⟨Z, ySub15 D.M V₀ V hV L (wSub V₀ V hV L) k, C,
    kSub15 D.M V₀ V hV L (ySub15 D.M V₀ V hV L (wSub V₀ V hV L) k) Z,
    hZmem, hYel, hY, hCle,
    (by simpa [fSub15] using (hfix Z hZmem).1),
    (by simpa [fSub15] using hCchar),
    hV1K, (by simpa [fSub15] using hKle), (by simpa [fSub15] using htZ),
    (by
      intro x hx k' hk'
      exact ((s15_Twelve_mem_kSub15 D h.hyp151 hV hY hZmem).1 hk').2 x hx),
    (by omega)⟩

theorem s15_Twelve_caseI (D : Data G) (h1217 : R1217 D) (hT7 : RT7 D) {V₀ V L : Subgroup G}
    (h : Hyp154 D V₀ V L) (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥) {n : ℕ} {k : G}
    (hk : Cond1512 n D.M V k) (hn2 : n ≤ 2) (hn : n + 2 ≤ gamma15 D.M V₀ V hV L)
    (hs : 1 < s15 D.M V₀ V hV L) :
    gamma15 D.M V₀ V hV L = 3 ∧ s15 D.M V₀ V hV L = 2 := by
  obtain ⟨Z, F, C, K, hZmem, hcfg⟩ :=
    s15_Twelve_exists_config_caseI D h1217 h hV hL hk hn2 hn hs
  obtain ⟨hFab, hFM, hCF, hFN, hC, hUK, hKE, hmK, hFK, hmFC⟩ := hcfg
  exact hT7 V₀ V L h hL (1 : G) Z hZmem F C K hFab
    (by simpa [conjSubgroup_one] using hFM) hCF
    (by simpa [conjSubgroup_one] using hFN)
    (by simpa [conjSubgroup_one] using hC)
    (by simpa [conjSubgroup_one] using hUK)
    (by simpa [conjSubgroup_one] using hKE)
    (by simpa [conjSubgroup_one] using hmK)
    (by simpa [conjSubgroup_one] using hFK) hmFC

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
