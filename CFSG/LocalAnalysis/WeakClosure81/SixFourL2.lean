module

public import CFSG.LocalAnalysis.WeakClosure81.SixFourShape
public import CFSG.GH74.SmallRanks
public import CFSG.CGT.Timmesfeld75.L2Pair

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open CFSG.CGT.Timmesfeld75 (IsL2Pair ConjTwoTransitive)
open scoped MatrixGroups Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem nonempty_psl_equiv_of_isL2 {Q : Type} [Group Q] {r : ℕ} (hr : 1 ≤ r)
    (h : IsL2 Q r) : Nonempty (Q ≃* PSL(2, GaloisField 2 r)) := by
  have hr0 : 0 < r := hr
  have hc : StatedClassicalModel Q .PSL 2 2 r :=
    CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) h
  obtain ⟨-, K, hField, hFinite, hcard, ⟨eQ⟩⟩ := hc
  exact ⟨eQ.trans (@CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL K hField hFinite 2 2 r
    (by infer_instance) hr0 hcard)⟩

theorem card_image_eq_two_pow {n : ℕ} {M V₀ V : Subgroup G} {g : G} {K : Subgroup G}
    [hK : (K.subgroupOf (LOf V g)).Normal]
    (h : Hyp64 n M V₀ V g)
    (hKset : (K : Set G) = ((BOf M V g : Subgroup G) : Set G) *
      ((UOf M V g : Subgroup G) : Set G))
    (hTwoRank : twoRank (↥(LOf V g) ⧸ (K.subgroupOf (LOf V g)))
      = E3.mQuot V (conjSubgroup M g))
    {r : ℕ} (hL2 : IsL2 (↥(LOf V g) ⧸ (K.subgroupOf (LOf V g))) r) :
    Nat.card ((V.subgroupOf (LOf V g)).map
        (QuotientGroup.mk' (K.subgroupOf (LOf V g)))) = 2 ^ r := by
  let L := LOf V g
  haveI : (K.subgroupOf L).Normal := hK
  let A : Subgroup (↥L ⧸ (K.subgroupOf L)) :=
    (V.subgroupOf L).map (QuotientGroup.mk' (K.subgroupOf L))
  have hAcard : Nat.card A = (UOf M V g).relIndex V :=
    card_map_subgroupOf_eq_relIndex h hKset
  have hAea : IsElemAbelian 2 A := isElemAbelian_map_subgroupOf (K := K) h
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hAea.isPGroup
  have htwo : twoRank (↥L ⧸ (K.subgroupOf L)) = r :=
    CFSG.GH74.twoRank_eq_of_lieModel_PSL_two_two hL2
  have hpadic : padicValNat 2 ((UOf M V g).relIndex V) = r := by
    have h1 : (UOf M V g).relIndex V = (conjSubgroup M g).relIndex V := by
      rw [UOf, Subgroup.inf_relIndex_left]
    rw [h1]
    have h2 : padicValNat 2 ((conjSubgroup M g).relIndex V)
        = E3.mQuot V (conjSubgroup M g) := rfl
    rw [h2, ← hTwoRank, htwo]
  have hk_eq : k = r := by
    have h3 : padicValNat 2 (Nat.card A) = k := by rw [hk, padicValNat.prime_pow]
    have h4 : padicValNat 2 (Nat.card A) = r := by rw [hAcard, hpadic]
    rw [← h3, h4]
  rw [hk, hk_eq]

theorem isL2Pair_image {n : ℕ} {M V₀ V : Subgroup G} {g : G} {K : Subgroup G}
    [hK : (K.subgroupOf (LOf V g)).Normal]
    (h : Hyp64 n M V₀ V g)
    (hKset : (K : Set G) = ((BOf M V g : Subgroup G) : Set G) *
      ((UOf M V g : Subgroup G) : Set G))
    (hTwoRank : twoRank (↥(LOf V g) ⧸ (K.subgroupOf (LOf V g)))
      = E3.mQuot V (conjSubgroup M g))
    {r : ℕ} (hr : 1 ≤ r) (hL2 : IsL2 (↥(LOf V g) ⧸ (K.subgroupOf (LOf V g))) r) :
    IsL2Pair (↥(LOf V g) ⧸ (K.subgroupOf (LOf V g)))
      ((V.subgroupOf (LOf V g)).map (QuotientGroup.mk' (K.subgroupOf (LOf V g)))) (2 ^ r) := by
  let L := LOf V g
  haveI : (K.subgroupOf L).Normal := hK
  let A : Subgroup (↥L ⧸ (K.subgroupOf L)) :=
    (V.subgroupOf L).map (QuotientGroup.mk' (K.subgroupOf L))
  obtain ⟨e⟩ := nonempty_psl_equiv_of_isL2 hr hL2
  have hcardA : Nat.card A = 2 ^ r := card_image_eq_two_pow h hKset hTwoRank hL2
  have hAea : IsElemAbelian 2 A := isElemAbelian_map_subgroupOf (K := K) h
  have hQcard : Nat.card (↥L ⧸ (K.subgroupOf L)) = 2 ^ r * ((2 ^ r) ^ 2 - 1) := by
    rw [Nat.card_congr e.toEquiv,
      Nat.card_congr (CFSG.CGT.Timmesfeld75.pslMulEquivSL (F := GaloisField 2 r)).toEquiv,
      CFSG.CGT.Timmesfeld75.card_sl2, GaloisField.card 2 r (by omega)]
  have hAindex : A.index = (2 ^ r) ^ 2 - 1 := by
    have h1 := Subgroup.card_mul_index A
    rw [hcardA, hQcard] at h1
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h1
  obtain ⟨j, hj⟩ : ∃ j, 2 ^ r = 2 * j := by
    refine ⟨2 ^ (r - 1), ?_⟩
    calc 2 ^ r = 2 ^ (1 + (r - 1)) := by congr 1; omega
      _ = 2 ^ 1 * 2 ^ (r - 1) := by rw [pow_add]
      _ = 2 * 2 ^ (r - 1) := by norm_num
  have hj1 : 1 ≤ j := by
    have h2r : 2 ≤ 2 ^ r := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hr
    omega
  have hj2 : 1 ≤ j ^ 2 := by nlinarith [sq_nonneg j]
  have hidx : ¬ 2 ∣ A.index := by
    have hAodd : A.index = 2 * (2 * j ^ 2 - 1) + 1 := by
      rw [hAindex, hj]
      have h1 : (2 * j) ^ 2 = 4 * j ^ 2 := by ring
      have h2 : 2 * (2 * j ^ 2 - 1) + 1 = 4 * j ^ 2 - 1 := by omega
      omega
    rw [hAodd]
    intro hdvd
    obtain ⟨c, hc⟩ := hdvd
    omega
  exact IsL2Pair.of_psl_isPGroup (f := r) (by omega) ⟨e⟩ hAea.isPGroup hidx

theorem genHyp_of_L2 {n : ℕ} {M V₀ V : Subgroup G} {g : G} {K : Subgroup G}
    [hK : (K.subgroupOf (LOf V g)).Normal]
    (h : Hyp64 n M V₀ V g)
    (hKset : (K : Set G) = ((BOf M V g : Subgroup G) : Set G) *
      ((UOf M V g : Subgroup G) : Set G))
    (hTwoRank : twoRank (↥(LOf V g) ⧸ (K.subgroupOf (LOf V g)))
      = E3.mQuot V (conjSubgroup M g))
    {r : ℕ} (hr : 1 ≤ r) (hL2 : IsL2 (↥(LOf V g) ⧸ (K.subgroupOf (LOf V g))) r) :
    GenHyp M V g := by
  intro x hxVg hxK
  let L := LOf V g
  haveI : (K.subgroupOf L).Normal := hK
  let Q := ↥L ⧸ (K.subgroupOf L)
  let π : ↥L →* Q := QuotientGroup.mk' (K.subgroupOf L)
  let A : Subgroup Q := (V.subgroupOf L).map π
  let Bq : Subgroup Q := ((conjSubgroup V g).subgroupOf L).map π
  have hpair : IsL2Pair Q A (2 ^ r) := isL2Pair_image h hKset hTwoRank hr hL2
  have hAsupB : A ⊔ Bq = ⊤ := map_subgroupOf_sup_eq_top (K := K) h
  have hxL : x ∈ L := Subgroup.mem_sup_right hxVg
  let x' : ↥L := ⟨x, hxL⟩
  have hxπB : π x' ∈ Bq := by
    refine Subgroup.mem_map.2 ⟨x', ?_, rfl⟩
    exact hxVg
  have hxπne : π x' ≠ 1 := by
    intro h1
    apply hxK
    rw [← eq_sup_of_coe_eq_mul hKset]
    have h2 : x' ∈ (QuotientGroup.mk' (K.subgroupOf L)).ker := by
      rw [MonoidHom.mem_ker]; exact h1
    rw [QuotientGroup.ker_mk'] at h2
    exact h2
  have hAneTop : A ≠ ⊤ := by
    intro htop
    have h1 : Nat.card A = Nat.card Q := by rw [htop, Subgroup.card_top]
    rw [hpair.card_eq, hpair.card_eq_mul] at h1
    have h2 : (2 ^ r) ^ 2 - 1 = 1 := by
      have h1' : 2 ^ r * ((2 ^ r) ^ 2 - 1) = 2 ^ r * 1 := by
        rw [mul_one]; exact h1.symm
      exact Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num : (0 : ℕ) < 2) r) h1'
    have h2r : 2 ≤ 2 ^ r := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hr
    have h3 : (2 ^ r) ^ 2 = 2 := by omega
    nlinarith [h3, h2r]
  have hAneB : A ≠ Bq := by
    intro heq
    exact hAneTop (by rw [← hAsupB, heq, sup_idem])
  obtain ⟨-, K', hK'norm, hK'set, hQuot, hlK, -⟩ := h.inCalOStar
  obtain ⟨l, hlL, hlV⟩ := hlK
  let g₀ : Q := π ⟨l, hlL⟩
  have hAleB : conjSubgroup A g₀ = Bq := by
    rw [show A = (V.subgroupOf L).map π from rfl, map_conjSubgroup_of_hom,
      conjSubgroup_subgroupOf, ← hlV]
  have hpairBq : IsL2Pair Q Bq (2 ^ r) := by
    have hh := hpair.conj (g₀⁻¹)
    rwa [timmesfeld_conjSubgroup_eq A (g₀⁻¹), inv_inv, hAleB] at hh
  have hBq_p : IsPGroup 2 Bq := hpairBq.isElemAbelian.isPGroup
  have hdisj : A ⊓ Bq = ⊥ := by
    have hne : CFSG.CGT.Timmesfeld75.conjSubgroup (g₀⁻¹) A
        ≠ CFSG.CGT.Timmesfeld75.conjSubgroup (1 : Q) A := by
      intro heq
      rw [timmesfeld_conjSubgroup_eq A (g₀⁻¹), timmesfeld_conjSubgroup_eq A 1, inv_inv, inv_one,
        conjSubgroup_one] at heq
      exact hAneB (heq.symm.trans hAleB)
    have hh := hpair.inf_conjSubgroup_eq_bot hne
    rw [timmesfeld_conjSubgroup_eq A (g₀⁻¹), timmesfeld_conjSubgroup_eq A 1, inv_inv, inv_one,
      conjSubgroup_one, hAleB, inf_comm] at hh
    exact hh
  have hxπ_notA : π x' ∉ A := by
    intro hxA
    have hbot : π x' ∈ (⊥ : Subgroup Q) := by
      rw [← hdisj]
      exact ⟨hxA, hxπB⟩
    exact hxπne (Subgroup.mem_bot.1 hbot)
  obtain ⟨hA_sylow, hA_sylow_coe⟩ := hpair.exists_sylow_eq
  have hdisjN : Bq ⊓ Subgroup.normalizer (A : Set Q) = ⊥ := by
    have hh : Bq ⊓ Subgroup.normalizer (A : Set Q) = Bq ⊓ A := by
      have h0 := hBq_p.inf_normalizer_sylow hA_sylow
      rw [← Sylow.coe_coe] at h0
      rw [hA_sylow_coe] at h0
      exact h0
    rw [hh, inf_comm]
    exact hdisj
  have hxπ_notN : π x' ∉ Subgroup.normalizer (A : Set Q) := by
    intro hmem
    have hthis : π x' ∈ Bq ⊓ Subgroup.normalizer (A : Set Q) := ⟨hxπB, hmem⟩
    rw [hdisjN] at hthis
    exact hxπne (Subgroup.mem_bot.1 hthis)
  have hconj_ne : CFSG.CGT.Timmesfeld75.conjSubgroup (π x')⁻¹ A
      ≠ CFSG.CGT.Timmesfeld75.conjSubgroup (1 : Q) A := by
    intro heq
    rw [timmesfeld_conjSubgroup_eq A (π x')⁻¹, timmesfeld_conjSubgroup_eq A 1, inv_inv, inv_one,
      conjSubgroup_one] at heq
    exact hxπ_notN (conjSubgroup_eq_iff_mem_normalizer.1 heq)
  have htop : A ⊔ conjSubgroup A (π x') = ⊤ := by
    have hh := hpair.sup_conj_eq_top hconj_ne
    rw [timmesfeld_conjSubgroup_eq A (π x')⁻¹, timmesfeld_conjSubgroup_eq A 1, inv_inv, inv_one,
      conjSubgroup_one, sup_comm] at hh
    exact hh
  have htop2 : A ⊔ Subgroup.zpowers (π x') = ⊤ := by
    apply le_antisymm le_top
    rw [← htop]
    refine sup_le le_sup_left ?_
    intro y hy
    rw [mem_conjSubgroup_iff] at hy
    have hy' : y = (π x')⁻¹ * (π x' * y * (π x')⁻¹) * (π x') := by group
    rw [hy']
    exact (A ⊔ Subgroup.zpowers (π x')).mul_mem
      ((A ⊔ Subgroup.zpowers (π x')).mul_mem
        (Subgroup.mem_sup_right (Subgroup.inv_mem _ (Subgroup.mem_zpowers _)))
        (Subgroup.mem_sup_left hy))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  have hmapsup : ((V.subgroupOf L) ⊔ Subgroup.zpowers x').map π = ⊤ := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers π x']
    simpa [A] using htop2
  have htopL : ((V.subgroupOf L) ⊔ Subgroup.zpowers x') ⊔ (K.subgroupOf L) = ⊤ := by
    have hY : (⊤ : Subgroup ↥L).map π = ⊤ :=
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
    have hh := sup_subgroupOf_eq_of_map_eq (K := K)
      (X := (V.subgroupOf L) ⊔ Subgroup.zpowers x') (Y := ⊤)
      (by rw [hmapsup, hY])
    simpa using hh
  have hXL : ((V.subgroupOf L ⊔ Subgroup.zpowers x').map L.subtype)
      = V ⊔ Subgroup.zpowers x := by
    rw [Subgroup.map_sup]
    have h1 : (V.subgroupOf L).map L.subtype = V :=
      Subgroup.map_subgroupOf_eq_of_le (le_sup_left : V ≤ L)
    have h2 : (Subgroup.zpowers x').map L.subtype = Subgroup.zpowers x := by
      rw [MonoidHom.map_zpowers L.subtype x']
      rfl
    rw [h1, h2]
  have hKL : ((K.subgroupOf L).map L.subtype) = K := by
    refine Subgroup.map_subgroupOf_eq_of_le ?_
    rw [eq_sup_of_coe_eq_mul hKset]
    exact sup_le (fun u hu => Subgroup.mem_sup_left hu.1)
      (fun b hb => Subgroup.mem_sup_right hb.1)
  have htopG : ((⊤ : Subgroup ↥L).map L.subtype) = L := by
    rw [← MonoidHom.range_eq_map L.subtype, Subgroup.range_subtype]
  have hmap := congrArg (Subgroup.map L.subtype) htopL
  rw [Subgroup.map_sup, hXL, hKL, htopG] at hmap
  rw [eq_sup_of_coe_eq_mul hKset] at hmap
  exact hmap.ge

theorem swapHyp_of_L2 {n : ℕ} {M V₀ V : Subgroup G} {g : G} {K : Subgroup G}
    [hK : (K.subgroupOf (LOf V g)).Normal]
    (h : Hyp64 n M V₀ V g) (hgen : GenHyp M V g)
    (hKset : (K : Set G) = ((BOf M V g : Subgroup G) : Set G) *
      ((UOf M V g : Subgroup G) : Set G))
    (hTwoRank : twoRank (↥(LOf V g) ⧸ (K.subgroupOf (LOf V g)))
      = E3.mQuot V (conjSubgroup M g))
    {r : ℕ} (hr : 1 ≤ r) (hL2 : IsL2 (↥(LOf V g) ⧸ (K.subgroupOf (LOf V g))) r) :
    SwapHyp V g := by
  let L := LOf V g
  haveI : (K.subgroupOf L).Normal := hK
  let Q := ↥L ⧸ (K.subgroupOf L)
  let π : ↥L →* Q := QuotientGroup.mk' (K.subgroupOf L)
  let A : Subgroup Q := (V.subgroupOf L).map π
  let Bq : Subgroup Q := ((conjSubgroup V g).subgroupOf L).map π
  have hpair : IsL2Pair Q A (2 ^ r) := isL2Pair_image h hKset hTwoRank hr hL2
  have hAsupB : A ⊔ Bq = ⊤ := map_subgroupOf_sup_eq_top (K := K) h
  have hAneTop : A ≠ ⊤ := by
    intro htop
    have h1 : Nat.card A = Nat.card Q := by rw [htop, Subgroup.card_top]
    rw [hpair.card_eq, hpair.card_eq_mul] at h1
    have h2 : (2 ^ r) ^ 2 - 1 = 1 := by
      have h1' : 2 ^ r * ((2 ^ r) ^ 2 - 1) = 2 ^ r * 1 := by
        rw [mul_one]; exact h1.symm
      exact Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num : (0 : ℕ) < 2) r) h1'
    have h2r : 2 ≤ 2 ^ r := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hr
    have h3 : (2 ^ r) ^ 2 = 2 := by omega
    nlinarith [h3, h2r]
  have hAneB : A ≠ Bq := by
    intro heq
    exact hAneTop (by rw [← hAsupB, heq, sup_idem])
  have hUV : UOf M V g ≠ V := by
    intro heq
    exact h.inCalOStar.1.2.1 (heq ▸ inf_le_right)
  obtain ⟨-, K', hK'norm, hK'set, hQuot, hlK, -⟩ := h.inCalOStar
  obtain ⟨l, hlL, hlV⟩ := hlK
  let g₀ : Q := π ⟨l, hlL⟩
  have hAleB : conjSubgroup A g₀ = Bq := by
    rw [show A = (V.subgroupOf L).map π from rfl, map_conjSubgroup_of_hom,
      conjSubgroup_subgroupOf, ← hlV]
  have hBq_eq : Bq = CFSG.CGT.Timmesfeld75.conjSubgroup (g₀⁻¹) A := by
    rw [← hAleB, timmesfeld_conjSubgroup_eq A (g₀⁻¹), inv_inv]
  have hne1 : CFSG.CGT.Timmesfeld75.conjSubgroup (1 : Q) A
      ≠ CFSG.CGT.Timmesfeld75.conjSubgroup (g₀⁻¹) A := by
    intro heq
    rw [timmesfeld_conjSubgroup_eq A 1, timmesfeld_conjSubgroup_eq A (g₀⁻¹), inv_one, inv_inv,
      conjSubgroup_one] at heq
    exact hAneB (heq.trans hAleB)
  have hne2 : CFSG.CGT.Timmesfeld75.conjSubgroup (g₀⁻¹) A
      ≠ CFSG.CGT.Timmesfeld75.conjSubgroup (1 : Q) A := hne1.symm
  obtain ⟨g₁, hg1, hg2⟩ := hpair.conjTwoTransitive 1 (g₀⁻¹) (g₀⁻¹) 1 hne1 hne2
  have hg1' : CFSG.CGT.Timmesfeld75.conjSubgroup g₁ A = Bq := by
    rw [mul_one, timmesfeld_conjSubgroup_eq A (g₀⁻¹), inv_inv, hAleB] at hg1
    exact hg1
  let z : Q := g₁⁻¹
  have hzconj : conjSubgroup A z = Bq := by
    have h1 : conjSubgroup A z = CFSG.CGT.Timmesfeld75.conjSubgroup g₁ A := by
      rw [show z = g₁⁻¹ from rfl, ← timmesfeld_conjSubgroup_eq A g₁]
    rw [h1, hg1']
  have hzconj2 : conjSubgroup Bq z = A := by
    have h1 : conjSubgroup Bq z = CFSG.CGT.Timmesfeld75.conjSubgroup g₁ Bq := by
      rw [show z = g₁⁻¹ from rfl, ← timmesfeld_conjSubgroup_eq Bq g₁]
    rw [h1, hBq_eq, CFSG.CGT.Timmesfeld75.conjSubgroup_conjSubgroup, hg2,
      timmesfeld_conjSubgroup_eq A 1, inv_one, conjSubgroup_one]
  obtain ⟨w, hwπ⟩ := QuotientGroup.mk'_surjective (K.subgroupOf L) z
  have hVwL : conjSubgroup V (w : G) ≤ LOf V g :=
    (conjSubgroup_mono (le_sup_left : V ≤ LOf V g) (w : G)).trans
      (le_of_eq (conjSubgroup_eq_iff_mem_normalizer.2 (Subgroup.le_normalizer w.2)))
  have hVw_eq : (((conjSubgroup V (w : G)).subgroupOf L).map L.subtype) = conjSubgroup V (w : G) :=
    Subgroup.map_subgroupOf_eq_of_le hVwL
  have hVs : (((conjSubgroup V g).subgroupOf L).map L.subtype) = conjSubgroup V g :=
    Subgroup.map_subgroupOf_eq_of_le (le_sup_right : conjSubgroup V g ≤ LOf V g)
  have hLsub : ((K.subgroupOf L).map L.subtype) = K := by
    refine Subgroup.map_subgroupOf_eq_of_le ?_
    rw [eq_sup_of_coe_eq_mul hKset]
    exact sup_le (fun u hu => Subgroup.mem_sup_left hu.1)
      (fun b hb => Subgroup.mem_sup_right hb.1)
  have hwK : conjSubgroup V (w : G) ⊔ (UOf M V g ⊔ BOf M V g)
      = conjSubgroup V g ⊔ (UOf M V g ⊔ BOf M V g) := by
    have hAB : (conjSubgroup (V.subgroupOf L) w).map π
        = ((conjSubgroup V g).subgroupOf L).map π := by
      rw [← map_conjSubgroup_of_hom, hwπ, hzconj]
    have hsup := sup_subgroupOf_eq_of_map_eq (K := K) hAB
    have hmap := congrArg (Subgroup.map L.subtype) hsup
    rw [Subgroup.map_sup, Subgroup.map_sup, conjSubgroup_subgroupOf] at hmap
    rw [hVw_eq, hVs, hLsub] at hmap
    rw [← eq_sup_of_coe_eq_mul hKset]
    exact hmap
  have hVw : conjSubgroup V (w : G) = conjSubgroup V g :=
    conjSubgroup_V_eq_conjSubgroup_V_of_sup_eq_of_ne h hgen hUV w.2 hwK
  have hwK2 : conjSubgroup (conjSubgroup V g) (w : G) ⊔ (UOf M V g ⊔ BOf M V g)
      = V ⊔ (UOf M V g ⊔ BOf M V g) := by
    have hAB : (conjSubgroup ((conjSubgroup V g).subgroupOf L) w).map π
        = (V.subgroupOf L).map π := by
      rw [← map_conjSubgroup_of_hom, hwπ, hzconj2]
    have hsup := sup_subgroupOf_eq_of_map_eq (K := K) hAB
    have hVgwL : conjSubgroup (conjSubgroup V g) (w : G) ≤ LOf V g :=
      (conjSubgroup_mono (le_sup_right : conjSubgroup V g ≤ LOf V g) (w : G)).trans
        (le_of_eq (conjSubgroup_eq_iff_mem_normalizer.2 (Subgroup.le_normalizer w.2)))
    have hVgw_eq : (((conjSubgroup (conjSubgroup V g) (w : G)).subgroupOf L).map L.subtype)
        = conjSubgroup (conjSubgroup V g) (w : G) :=
      Subgroup.map_subgroupOf_eq_of_le hVgwL
    have hVeq : ((V.subgroupOf L).map L.subtype) = V :=
      Subgroup.map_subgroupOf_eq_of_le (le_sup_left : V ≤ L)
    have hmap := congrArg (Subgroup.map L.subtype) hsup
    rw [Subgroup.map_sup, Subgroup.map_sup, conjSubgroup_subgroupOf] at hmap
    rw [hVgw_eq, hVeq, hLsub] at hmap
    rw [← eq_sup_of_coe_eq_mul hKset]
    exact hmap
  have hVw2 : conjSubgroup V ((w * w : ↥L) : G) = V := by
    have hw2K : conjSubgroup V ((w * w : ↥L) : G) ⊔ (UOf M V g ⊔ BOf M V g)
        = V ⊔ (UOf M V g ⊔ BOf M V g) := by
      have h1 : conjSubgroup V ((w * w : ↥L) : G)
          = conjSubgroup (conjSubgroup V g) (w : G) := by
        rw [show ((w * w : ↥L) : G) = (w : G) * (w : G) from rfl,
          ← conjSubgroup_conjSubgroup, hVw]
      rw [h1]
      exact hwK2
    exact conjSubgroup_V_eq_of_sup_eq_of_ne h hgen hUV
      ((LOf V g).mul_mem w.2 w.2) hw2K
  have hVg_w : conjSubgroup (conjSubgroup V g) (w : G) = V := by
    have h1 : conjSubgroup (conjSubgroup V g) (w : G)
        = conjSubgroup V ((w * w : ↥L) : G) := by
      rw [show ((w * w : ↥L) : G) = (w : G) * (w : G) from rfl,
        ← conjSubgroup_conjSubgroup, hVw]
    rw [h1]
    exact hVw2
  exact ⟨(w : G), w.2, hVw, hVg_w⟩

theorem one_le_of_isL2 {Q : Type} [Group Q] {r : ℕ} (h : IsL2 Q r) : 1 ≤ r := by
  have hc : StatedClassicalModel Q .PSL 2 2 r :=
    CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) h
  exact hc.1.2.1

@[expose] def L2Shape (M V₀ V : Subgroup G) (g : G) : Prop :=
  ∃ K : Subgroup G, ∃ _ : (K.subgroupOf (LOf V g)).Normal,
    (K : Set G) = ((BOf M V g : Subgroup G) : Set G) *
      ((UOf M V g : Subgroup G) : Set G) ∧
    twoRank (↥(LOf V g) ⧸ (K.subgroupOf (LOf V g))) = E3.mQuot V (conjSubgroup M g) ∧
    ∃ r : ℕ, IsL2 (↥(LOf V g) ⧸ (K.subgroupOf (LOf V g))) r

theorem six_four_four_centralizer_B_of_L2 {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) (hL2s : L2Shape M V₀ V g) :
    BOf M V g ⊓ F11.CTilde M V₀ V = NOf M V g ⊔ conjSubgroup V₀ g := by
  obtain ⟨K, hKnorm, hKset, hTwoRank, r, hL2⟩ := hL2s
  have hr := one_le_of_isL2 hL2
  exact six_four_four_centralizer_B_of_gen h
    (genHyp_of_L2 (hK := hKnorm) h hKset hTwoRank hr hL2)

theorem six_four_five_of_L2 {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) (hL2s : L2Shape M V₀ V g) :
    (BOf M V g ⊓ F11.CTilde M V₀ V).relIndex (BOf M V g)
        * (UOf M V g).relIndex V
      = (V ⊓ Subgroup.centralizer (BOf M V g : Set G)).relIndex V := by
  obtain ⟨K, hKnorm, hKset, hTwoRank, r, hL2⟩ := hL2s
  have hr := one_le_of_isL2 hL2
  exact six_four_five h (genHyp_of_L2 (hK := hKnorm) h hKset hTwoRank hr hL2)

@[expose] def SzGenSwap (M V₀ V : Subgroup G) (g : G) : Prop :=
  ∀ K : Subgroup G, ∀ _ : (K.subgroupOf (LOf V g)).Normal,
    (K : Set G) = ((BOf M V g : Subgroup G) : Set G) *
      ((UOf M V g : Subgroup G) : Set G) →
    (∃ r : ℕ, IsSz (↥(LOf V g) ⧸ (K.subgroupOf (LOf V g))) r) →
    GenHyp M V g ∧ SwapHyp V g

theorem six_four_four_centralizer_B_of_quotShape {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) (hSz : SzGenSwap M V₀ V g) :
    BOf M V g ⊓ F11.CTilde M V₀ V = NOf M V g ⊔ conjSubgroup V₀ g := by
  obtain ⟨-, K, hKnorm, hKset, hQuot, -, -⟩ := h.inCalOStar
  rcases hQuot.1 with ⟨r, hL2⟩ | ⟨r, hSz'⟩ | ⟨m, hm, hdi⟩
  · exact six_four_four_centralizer_B_of_L2 h ⟨K, hKnorm, hKset, hQuot.2, r, hL2⟩
  · exact six_four_four_centralizer_B_of_gen h (hSz K hKnorm hKset ⟨r, hSz'⟩).1
  · exact six_four_four_centralizer_B_of_dihedral h ⟨K, hKnorm, hKset, m, hm, hdi⟩

theorem six_four_five_of_quotShape {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) (hSz : SzGenSwap M V₀ V g) :
    (BOf M V g ⊓ F11.CTilde M V₀ V).relIndex (BOf M V g)
        * (UOf M V g).relIndex V
      = (V ⊓ Subgroup.centralizer (BOf M V g : Set G)).relIndex V := by
  obtain ⟨-, K, hKnorm, hKset, hQuot, -, -⟩ := h.inCalOStar
  rcases hQuot.1 with ⟨r, hL2⟩ | ⟨r, hSz'⟩ | ⟨m, hm, hdi⟩
  · exact six_four_five_of_L2 h ⟨K, hKnorm, hKset, hQuot.2, r, hL2⟩
  · exact six_four_five h (hSz K hKnorm hKset ⟨r, hSz'⟩).1
  · exact six_four_five_of_dihedral h ⟨K, hKnorm, hKset, m, hm, hdi⟩

end CFSG.LocalAnalysis.WeakClosure81
