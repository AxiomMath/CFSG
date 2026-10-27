module

public import CFSG.LocalAnalysis.WeakClosure81.SixFourL2
public import CFSG.LocalAnalysis.WeakClosure81.SuzukiGen

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ComponentClassification.Asc76X
open Subgroup
open scoped MatrixGroups Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem one_le_of_isSz {Q : Type} [Group Q] {r : ℕ} (h : IsSz Q r) : 1 ≤ r := by
  obtain ⟨a, ha, hr, -⟩ := exists_mulEquiv_sz_of_isSz h
  omega

theorem card_image_eq_two_pow_of_sz {n : ℕ} {M V₀ V : Subgroup G} {g : G} {K : Subgroup G}
    [hK : (K.subgroupOf (LOf V g)).Normal]
    (h : Hyp64 n M V₀ V g)
    (hKset : (K : Set G) = ((BOf M V g : Subgroup G) : Set G) *
      ((UOf M V g : Subgroup G) : Set G))
    (hTwoRank : twoRank (↥(LOf V g) ⧸ (K.subgroupOf (LOf V g)))
      = E3.mQuot V (conjSubgroup M g))
    {r : ℕ} (hSz : IsSz (↥(LOf V g) ⧸ (K.subgroupOf (LOf V g))) r) :
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
  obtain ⟨a, ha, hr_eq, ⟨e⟩⟩ := exists_mulEquiv_sz_of_isSz hSz
  have htwo : twoRank (↥L ⧸ (K.subgroupOf L)) = r := by
    rw [hr_eq]
    exact twoRank_eq_of_mulEquiv_sz ha e
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

theorem exists_sylow_image_eq_of_sz {n : ℕ} {M V₀ V : Subgroup G} {g : G} {K : Subgroup G}
    [hK : (K.subgroupOf (LOf V g)).Normal]
    (h : Hyp64 n M V₀ V g)
    (hKset : (K : Set G) = ((BOf M V g : Subgroup G) : Set G) *
      ((UOf M V g : Subgroup G) : Set G))
    (hTwoRank : twoRank (↥(LOf V g) ⧸ (K.subgroupOf (LOf V g)))
      = E3.mQuot V (conjSubgroup M g))
    {r : ℕ} (hSz : IsSz (↥(LOf V g) ⧸ (K.subgroupOf (LOf V g))) r) :
    ∃ P : Sylow 2 (↥(LOf V g) ⧸ (K.subgroupOf (LOf V g))),
      (V.subgroupOf (LOf V g)).map (QuotientGroup.mk' (K.subgroupOf (LOf V g))) =
        ((P : Subgroup (↥(LOf V g) ⧸ (K.subgroupOf (LOf V g)))) ⊓
          Subgroup.centralizer
            (((P : Subgroup (↥(LOf V g) ⧸ (K.subgroupOf (LOf V g))))) :
              Set (↥(LOf V g) ⧸ (K.subgroupOf (LOf V g))))) := by
  let L := LOf V g
  haveI : (K.subgroupOf L).Normal := hK
  let Q := ↥L ⧸ (K.subgroupOf L)
  let A : Subgroup Q := (V.subgroupOf L).map (QuotientGroup.mk' (K.subgroupOf L))
  obtain ⟨a, ha, hr_eq, ⟨e⟩⟩ := exists_mulEquiv_sz_of_isSz hSz
  have hcardA : Nat.card A = 2 ^ (2 * a + 1) := by
    rw [← hr_eq]
    exact card_image_eq_two_pow_of_sz h hKset hTwoRank hSz
  have hAea : IsElemAbelian 2 A := isElemAbelian_map_subgroupOf (K := K) h
  exact exists_sylow_eq_inf_centralizer_of_isElemAbelian ha e hAea hcardA

theorem genHyp_of_sz {n : ℕ} {M V₀ V : Subgroup G} {g : G} {K : Subgroup G}
    [hK : (K.subgroupOf (LOf V g)).Normal]
    (h : Hyp64 n M V₀ V g)
    (hKset : (K : Set G) = ((BOf M V g : Subgroup G) : Set G) *
      ((UOf M V g : Subgroup G) : Set G))
    (hTwoRank : twoRank (↥(LOf V g) ⧸ (K.subgroupOf (LOf V g)))
      = E3.mQuot V (conjSubgroup M g))
    {r : ℕ} (hSz : IsSz (↥(LOf V g) ⧸ (K.subgroupOf (LOf V g))) r) :
    GenHyp M V g := by
  have hr : 1 ≤ r := one_le_of_isSz hSz
  intro x hxVg hxK
  let L := LOf V g
  haveI : (K.subgroupOf L).Normal := hK
  let Q := ↥L ⧸ (K.subgroupOf L)
  let π : ↥L →* Q := QuotientGroup.mk' (K.subgroupOf L)
  let A : Subgroup Q := (V.subgroupOf L).map π
  let Bq : Subgroup Q := ((conjSubgroup V g).subgroupOf L).map π
  obtain ⟨a, ha, hr_eq, ⟨e⟩⟩ := exists_mulEquiv_sz_of_isSz hSz
  have hAcard : Nat.card A = 2 ^ r :=
    card_image_eq_two_pow_of_sz h hKset hTwoRank hSz
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
  obtain ⟨P, hAeq⟩ := exists_sylow_image_eq_of_sz (K := K) h hKset hTwoRank hSz
  have hAeq' : A = (P : Subgroup Q) ⊓
      Subgroup.centralizer ((P : Subgroup Q) : Set Q) := hAeq
  have hB : fusionBenderBorel Q (2 ^ (2 * a + 1)) 2 :=
    fusionBenderBorel_of_mulEquiv_sz ha e
  have hPcard : Nat.card (P : Subgroup Q) = (2 ^ r) ^ 2 := by
    have h1 := (CFSG.ComponentClassification.AschbacherToolkit.Bender.benderBorel_sylowCenter
      hB P).2.2.2
    rw [← hr_eq] at h1
    exact h1
  have hAneTop : A ≠ ⊤ := by
    intro htop
    have h1 : Nat.card A = Nat.card Q := by rw [htop, Subgroup.card_top]
    have h2 : Nat.card (P : Subgroup Q) ≤ Nat.card Q := by
      simpa using Subgroup.card_le_of_le (H := (P : Subgroup Q)) (K := ⊤) le_top
    have h3 : (2 ^ r) ^ 2 ≤ 2 ^ r := by
      calc (2 ^ r) ^ 2 = Nat.card (P : Subgroup Q) := hPcard.symm
        _ ≤ Nat.card Q := h2
        _ = Nat.card A := h1.symm
        _ = 2 ^ r := hAcard
    have h4 : 2 ^ r < (2 ^ r) ^ 2 := by
      rw [pow_two]
      have hpos : 0 < 2 ^ r := pow_pos (by norm_num) r
      have hgt : 1 < 2 ^ r := by
        have h2r : 2 ≤ 2 ^ r := by
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hr
        omega
      calc 2 ^ r = 2 ^ r * 1 := (mul_one _).symm
        _ < 2 ^ r * 2 ^ r := Nat.mul_lt_mul_of_pos_left hgt hpos
    omega
  have hAneB : A ≠ Bq := by
    intro heq
    exact hAneTop (by rw [← hAsupB, heq, sup_idem])
  obtain ⟨-, K', hK'norm, hK'set, hQuot, hlK, -⟩ := h.inCalOStar
  obtain ⟨l, hlL, hlV⟩ := hlK
  let g₀ : Q := π ⟨l, hlL⟩
  have hAleB : conjSubgroup A g₀ = Bq := by
    rw [show A = (V.subgroupOf L).map π from rfl, map_conjSubgroup_of_hom,
      conjSubgroup_subgroupOf, ← hlV]
  let P'' : Sylow 2 Q := g₀⁻¹ • P
  have hBq_eq : Bq = (P'' : Subgroup Q) ⊓
      Subgroup.centralizer ((P'' : Subgroup Q) : Set Q) := by
    rw [show Bq = conjSubgroup A g₀ from hAleB.symm, hAeq', conjSubgroup_inf,
      CFSG.Quasithin.E3.conjSubgroup_centralizer]
    rfl
  have hPneP'' : P ≠ P'' := by
    intro heq
    exact hAneB (by rw [hBq_eq, ← heq, ← hAeq'])
  have hdisj : (P : Subgroup Q) ⊓ (P'' : Subgroup Q) = ⊥ :=
    inf_eq_bot_of_fusionBenderBorel hB hPneP''
  have hNA : Subgroup.normalizer (A : Set Q) =
      Subgroup.normalizer ((P : Subgroup Q) : Set Q) := by
    rw [hAeq']
    exact normalizer_inf_centralizer_eq_of_mulEquiv_sz ha e P
  have hBq_ea : IsElemAbelian 2 Bq := by
    have hVg_ea : IsElemAbelian 2 (conjSubgroup V g) := by
      simpa [conjSubgroup] using
        IsElemAbelian.map h.elemAbelian (MulAut.conj g⁻¹).toMonoidHom
    have h1 : IsElemAbelian 2 ((conjSubgroup V g).subgroupOf L) := hVg_ea.subgroupOf L
    simpa [Bq] using h1.map π
  have hBq_p : IsPGroup 2 Bq := hBq_ea.isPGroup
  have hdisjN : Bq ⊓ Subgroup.normalizer (A : Set Q) = ⊥ := by
    have h1 : Bq ⊓ Subgroup.normalizer (A : Set Q) ≤ (P : Subgroup Q) := by
      rw [hNA]
      have h2 : Bq ⊓ Subgroup.normalizer ((P : Subgroup Q) : Set Q) =
          Bq ⊓ (P : Subgroup Q) := hBq_p.inf_normalizer_sylow P
      rw [h2]
      exact inf_le_right
    have h2 : Bq ⊓ Subgroup.normalizer (A : Set Q) ≤ (P'' : Subgroup Q) := by
      refine le_trans inf_le_left ?_
      rw [hBq_eq]
      exact inf_le_left
    have h3 : Bq ⊓ Subgroup.normalizer (A : Set Q) ≤
        (P : Subgroup Q) ⊓ (P'' : Subgroup Q) := le_inf h1 h2
    rw [hdisj] at h3
    exact le_bot_iff.mp h3
  have hxπ_notN : π x' ∉ Subgroup.normalizer (A : Set Q) := by
    intro hmem
    have hthis : π x' ∈ Bq ⊓ Subgroup.normalizer (A : Set Q) := ⟨hxπB, hmem⟩
    rw [hdisjN] at hthis
    exact hxπne (Subgroup.mem_bot.1 hthis)
  have hne_conj : P ≠ (π x')⁻¹ • P := by
    intro heq
    apply hxπ_notN
    rw [hNA]
    have h1 : (π x')⁻¹ ∈ Subgroup.normalizer ((P : Subgroup Q) : Set Q) :=
      Sylow.smul_eq_iff_mem_normalizer.mp heq.symm
    have h2 : ((π x')⁻¹)⁻¹ ∈ Subgroup.normalizer ((P : Subgroup Q) : Set Q) :=
      (Subgroup.normalizer ((P : Subgroup Q) : Set Q)).inv_mem h1
    rwa [inv_inv] at h2
  have hconjA : conjSubgroup A (π x') =
      (((π x')⁻¹ • P : Sylow 2 Q) : Subgroup Q) ⊓
        Subgroup.centralizer ((((π x')⁻¹ • P : Sylow 2 Q) : Subgroup Q) : Set Q) := by
    rw [hAeq', conjSubgroup_inf, CFSG.Quasithin.E3.conjSubgroup_centralizer]
    rfl
  have htop : A ⊔ conjSubgroup A (π x') = ⊤ := by
    have hh := inf_centralizer_sup_inf_centralizer_eq_top ha e hne_conj
    rw [hconjA, hAeq']
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

theorem swapHyp_of_sz {n : ℕ} {M V₀ V : Subgroup G} {g : G} {K : Subgroup G}
    [hK : (K.subgroupOf (LOf V g)).Normal]
    (h : Hyp64 n M V₀ V g) (hgen : GenHyp M V g)
    (hKset : (K : Set G) = ((BOf M V g : Subgroup G) : Set G) *
      ((UOf M V g : Subgroup G) : Set G))
    (hTwoRank : twoRank (↥(LOf V g) ⧸ (K.subgroupOf (LOf V g)))
      = E3.mQuot V (conjSubgroup M g))
    {r : ℕ} (hSz : IsSz (↥(LOf V g) ⧸ (K.subgroupOf (LOf V g))) r) :
    SwapHyp V g := by
  have hr : 1 ≤ r := one_le_of_isSz hSz
  let L := LOf V g
  haveI : (K.subgroupOf L).Normal := hK
  let Q := ↥L ⧸ (K.subgroupOf L)
  let π : ↥L →* Q := QuotientGroup.mk' (K.subgroupOf L)
  let A : Subgroup Q := (V.subgroupOf L).map π
  let Bq : Subgroup Q := ((conjSubgroup V g).subgroupOf L).map π
  obtain ⟨a, ha, hr_eq, ⟨e⟩⟩ := exists_mulEquiv_sz_of_isSz hSz
  have hAcard : Nat.card A = 2 ^ r :=
    card_image_eq_two_pow_of_sz h hKset hTwoRank hSz
  have hAsupB : A ⊔ Bq = ⊤ := map_subgroupOf_sup_eq_top (K := K) h
  obtain ⟨P, hAeq⟩ := exists_sylow_image_eq_of_sz (K := K) h hKset hTwoRank hSz
  have hAeq' : A = (P : Subgroup Q) ⊓
      Subgroup.centralizer ((P : Subgroup Q) : Set Q) := hAeq
  have hB : fusionBenderBorel Q (2 ^ (2 * a + 1)) 2 :=
    fusionBenderBorel_of_mulEquiv_sz ha e
  have hPcard : Nat.card (P : Subgroup Q) = (2 ^ r) ^ 2 := by
    have h1 := (CFSG.ComponentClassification.AschbacherToolkit.Bender.benderBorel_sylowCenter
      hB P).2.2.2
    rw [← hr_eq] at h1
    exact h1
  have hAneTop : A ≠ ⊤ := by
    intro htop
    have h1 : Nat.card A = Nat.card Q := by rw [htop, Subgroup.card_top]
    have h2 : Nat.card (P : Subgroup Q) ≤ Nat.card Q := by
      simpa using Subgroup.card_le_of_le (H := (P : Subgroup Q)) (K := ⊤) le_top
    have h3 : (2 ^ r) ^ 2 ≤ 2 ^ r := by
      calc (2 ^ r) ^ 2 = Nat.card (P : Subgroup Q) := hPcard.symm
        _ ≤ Nat.card Q := h2
        _ = Nat.card A := h1.symm
        _ = 2 ^ r := hAcard
    have h4 : 2 ^ r < (2 ^ r) ^ 2 := by
      rw [pow_two]
      have hpos : 0 < 2 ^ r := pow_pos (by norm_num) r
      have hgt : 1 < 2 ^ r := by
        have h2r : 2 ≤ 2 ^ r := by
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hr
        omega
      calc 2 ^ r = 2 ^ r * 1 := (mul_one _).symm
        _ < 2 ^ r * 2 ^ r := Nat.mul_lt_mul_of_pos_left hgt hpos
    omega
  have hAneB : A ≠ Bq := by
    intro heq
    exact hAneTop (by rw [← hAsupB, heq, sup_idem])
  obtain ⟨-, K', hK'norm, hK'set, hQuot, hlK, -⟩ := h.inCalOStar
  obtain ⟨l, hlL, hlV⟩ := hlK
  let g₀ : Q := π ⟨l, hlL⟩
  have hAleB : conjSubgroup A g₀ = Bq := by
    rw [show A = (V.subgroupOf L).map π from rfl, map_conjSubgroup_of_hom,
      conjSubgroup_subgroupOf, ← hlV]
  let P'' : Sylow 2 Q := g₀⁻¹ • P
  have hBq_eq : Bq = (P'' : Subgroup Q) ⊓
      Subgroup.centralizer ((P'' : Subgroup Q) : Set Q) := by
    rw [show Bq = conjSubgroup A g₀ from hAleB.symm, hAeq', conjSubgroup_inf,
      CFSG.Quasithin.E3.conjSubgroup_centralizer]
    rfl
  have hPneP'' : P ≠ P'' := by
    intro heq
    exact hAneB (by rw [hBq_eq, ← heq, ← hAeq'])
  obtain ⟨z₀, hz₀P, hz₀P''⟩ := exists_smul_eq_and_smul_eq_of_mulEquiv_sz ha e hPneP''
  have hzconj : conjSubgroup A z₀ = Bq := by
    have h1 : conjSubgroup A z₀ =
        (((z₀⁻¹ • P : Sylow 2 Q) : Subgroup Q) ⊓
          Subgroup.centralizer (((z₀⁻¹ • P : Sylow 2 Q) : Subgroup Q) : Set Q)) := by
      rw [hAeq', conjSubgroup_inf, CFSG.Quasithin.E3.conjSubgroup_centralizer]
      rfl
    have hzP : z₀⁻¹ • P = P'' := by
      rw [← hz₀P'']
      simp
    rw [h1, hzP, ← hBq_eq]
  have hzconj2 : conjSubgroup Bq z₀ = A := by
    have h1 : conjSubgroup Bq z₀ =
        (((z₀⁻¹ • P'' : Sylow 2 Q) : Subgroup Q) ⊓
          Subgroup.centralizer (((z₀⁻¹ • P'' : Sylow 2 Q) : Subgroup Q) : Set Q)) := by
      rw [hBq_eq, conjSubgroup_inf, CFSG.Quasithin.E3.conjSubgroup_centralizer]
      rfl
    have hzP' : z₀⁻¹ • P'' = P := by
      rw [← hz₀P]
      simp
    rw [h1, hzP', ← hAeq']
  have hUV : UOf M V g ≠ V := by
    intro heq
    exact h.inCalOStar.1.2.1 (heq ▸ inf_le_right)
  obtain ⟨w, hwπ⟩ := QuotientGroup.mk'_surjective (K.subgroupOf L) z₀
  have hVwL : conjSubgroup V (w : G) ≤ LOf V g :=
    (conjSubgroup_mono (le_sup_left : V ≤ LOf V g) (w : G)).trans
      (le_of_eq (conjSubgroup_eq_iff_mem_normalizer.2 (Subgroup.le_normalizer w.2)))
  have hVw_eq : (((conjSubgroup V (w : G)).subgroupOf L).map L.subtype)
      = conjSubgroup V (w : G) :=
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

theorem szGenSwap_of_hyp64 {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) : SzGenSwap M V₀ V g := by
  intro K hKnorm hKset hSzex
  obtain ⟨r, hSz⟩ := hSzex
  obtain ⟨-, K', hK'norm, hK'set, hQuot, -, -⟩ := h.inCalOStar
  have hKK' : K = K' := SetLike.coe_injective (hKset.trans hK'set.symm)
  subst K'
  have hTwoRank : twoRank (↥(LOf V g) ⧸ (K.subgroupOf (LOf V g)))
      = E3.mQuot V (conjSubgroup M g) := hQuot.2
  have hgen := genHyp_of_sz (hK := hKnorm) h hKset hTwoRank hSz
  exact ⟨hgen, swapHyp_of_sz (hK := hKnorm) h hgen hKset hTwoRank hSz⟩

theorem six_four_four_centralizer_B_uncond {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) :
    BOf M V g ⊓ F11.CTilde M V₀ V = NOf M V g ⊔ conjSubgroup V₀ g :=
  six_four_four_centralizer_B_of_quotShape h (szGenSwap_of_hyp64 h)

theorem six_four_five_uncond {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) :
    (BOf M V g ⊓ F11.CTilde M V₀ V).relIndex (BOf M V g)
        * (UOf M V g).relIndex V
      = (V ⊓ Subgroup.centralizer (BOf M V g : Set G)).relIndex V :=
  six_four_five_of_quotShape h (szGenSwap_of_hyp64 h)

theorem genHyp_of_hyp64 {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) : GenHyp M V g := by
  obtain ⟨-, K, hKnorm, hKset, hQuot, -, -⟩ := h.inCalOStar
  rcases hQuot.1 with ⟨r, hL2⟩ | ⟨r, hSz'⟩ | ⟨m, hm, hdi⟩
  · exact genHyp_of_L2 (hK := hKnorm) h hKset hQuot.2 (one_le_of_isL2 hL2) hL2
  · exact genHyp_of_sz (hK := hKnorm) h hKset hQuot.2 hSz'
  · exact genHyp_of_dihedral (hK := hKnorm) h hKset ⟨m, hm, hdi⟩

theorem swapHyp_of_hyp64 {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) : SwapHyp V g := by
  obtain ⟨-, K, hKnorm, hKset, hQuot, -, -⟩ := h.inCalOStar
  rcases hQuot.1 with ⟨r, hL2⟩ | ⟨r, hSz'⟩ | ⟨m, hm, hdi⟩
  · exact swapHyp_of_L2 (hK := hKnorm) h (genHyp_of_hyp64 h) hKset hQuot.2
      (one_le_of_isL2 hL2) hL2
  · exact swapHyp_of_sz (hK := hKnorm) h (genHyp_of_hyp64 h) hKset hQuot.2 hSz'
  · exact swapHyp_of_dihedral (hK := hKnorm) h hKset ⟨m, hm, hdi⟩

end CFSG.LocalAnalysis.WeakClosure81
