module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P218s
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenTwentyFive72
import CFSG.RankThree.PartOne.S12.Sec15Frattini

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

theorem uc22s218u_exists_conj_commute {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : q.Prime) (hq2 : q ≠ 2)
    {L O A : Subgroup G} (hO : IsPGroup 2 O) (hOL : O ≤ L) (hLO : L ≤ normalizer (O : Set G))
    (hA : IsPGroup q A) (hAL : A ≤ L) {y : G} (hy : IsPGroup p (zpowers y))
    (hyN : y ∈ normalizer (L : Set G)) (hyL : ∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ O) :
    ∃ w ∈ L, w⁻¹ * y * w ∈ centralizer (A : Set G) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W : Subgroup G := O ⊔ A with hWdef
  have hWL : W ≤ L := sup_le hOL hAL
  have hOW : O ≤ W := le_sup_left
  obtain ⟨a, ha⟩ := hO.exists_card_eq
  have hWc : Nat.card W = 2 ^ a * Nat.card A := by
    rw [hWdef, CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer O A (hAL.trans hLO)
      (IsPGroup.disjoint_of_ne 2 q hq2.symm O A hO hA), ha]
  have hrel : A.relIndex W = 2 ^ a := by
    have h1 := relIndex_mul_card A W
    rw [inf_eq_left.2 (le_sup_right : A ≤ W), hWc] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  have hAsyl : IsSylowOf q A W := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨le_sup_right, hA, fun h => ?_⟩
    rw [hrel] at h
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow h))
  have hcard : ¬ p ∣ Nat.card (Sylow q W) := by
    obtain ⟨Q, hQ⟩ := hAsyl
    have hQ' : (Q : Subgroup W) = A.subgroupOf W := by
      rw [← hQ, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective W.subtype_injective]
    have h1 := Sylow.card_dvd_index Q
    have h2 : (Q : Subgroup W).index = 2 ^ a := by
      rw [hQ']
      exact hrel
    rw [h2] at h1
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow (h.trans h1)))
  have hyW : zpowers y ≤ normalizer (W : Set G) := by
    rw [zpowers_le, mem_normalizer_iff]
    intro g
    constructor
    · intro hg
      have e : y * g * y⁻¹ = (y * g * y⁻¹ * g⁻¹) * g := by group
      rw [e]
      exact mul_mem (hOW (hyL g (hWL hg))) hg
    · intro hg
      have hgL : g ∈ L := (mem_normalizer_iff.1 hyN g).2 (hWL hg)
      have e : g = (y * g * y⁻¹ * g⁻¹)⁻¹ * (y * g * y⁻¹) := by group
      rw [e]
      exact mul_mem (inv_mem (hOW (hyL g hgL))) hg
  obtain ⟨S, hS⟩ := uc22p218s_exists_sylow_le_normalizer hp hq hy hyW hcard
  have hSsyl : IsSylowOf q ((S : Subgroup W).map W.subtype) W := ⟨S, rfl⟩
  have hdisj : Disjoint ((S : Subgroup W).map W.subtype) O :=
    IsPGroup.disjoint_of_ne q 2 hq2 _ O hSsyl.isPGroup hO
  obtain ⟨w, hwW, hw⟩ := hAsyl.exists_mem_conj hSsyl
  refine ⟨w, hWL hwW, mem_centralizer_iff.2 fun b hb => ?_⟩
  have hs : w * b * w⁻¹ ∈ (S : Subgroup W).map W.subtype :=
    (hw _).2 (by rwa [show w⁻¹ * (w * b * w⁻¹) * w = b by group])
  have h1 : y * (w * b * w⁻¹) * y⁻¹ * (w * b * w⁻¹)⁻¹ ∈ (S : Subgroup W).map W.subtype :=
    mul_mem ((mem_normalizer_iff.1 (hS (mem_zpowers y)) _).1 hs) (inv_mem hs)
  have h2 : y * (w * b * w⁻¹) * y⁻¹ * (w * b * w⁻¹)⁻¹ ∈ O := hyL _ (hWL (hSsyl.le hs))
  have h3 := disjoint_def.1 hdisj h1 h2
  calc b * (w⁻¹ * y * w)
      = w⁻¹ * ((y * (w * b * w⁻¹) * y⁻¹ * (w * b * w⁻¹)⁻¹)⁻¹ * (y * (w * b * w⁻¹))) * w := by group
    _ = w⁻¹ * y * w * b := by rw [h3, inv_one, one_mul]; group

theorem uc22s218u_exists_normalizer_of_comm {q : ℕ} [Fact q.Prime] {M T : Subgroup G} (hT : IsSylowOf q T M)
    {A : Type*} [Group A] (ψ : ↥M →* A) (hcomm : ∀ a b : A, a * b = b * a) (m : ↥M) :
    ∃ m' : ↥M, (m' : G) ∈ normalizer (T : Set G) ∧ ψ m' = ψ m := by
  set W : Subgroup G := (((T.subgroupOf M).map ψ).comap ψ).map M.subtype with hWdef
  have hWM : W ≤ M := map_subtype_le _
  have hTW : T ≤ W := fun t ht =>
    ⟨⟨t, hT.le ht⟩, mem_comap.2 (mem_map_of_mem ψ (mem_subgroupOf.2 ht)), rfl⟩
  have hmem : ∀ g : ↥M, (g : G) ∈ W ↔ ψ g ∈ (T.subgroupOf M).map ψ := by
    intro g
    rw [hWdef]
    exact (mem_map_iff_mem M.subtype_injective).trans mem_comap
  have hmW : (m : G) ∈ normalizer (W : Set G) := by
    rw [mem_normalizer_iff]
    intro g
    constructor
    · intro hg
      have hgM : g ∈ M := hWM hg
      have h1 := (hmem ⟨g, hgM⟩).1 hg
      have h2 : (m * ⟨g, hgM⟩ * m⁻¹ : ↥M) = (m : G) * g * (m : G)⁻¹ := rfl
      rw [← h2, hmem, map_mul, map_mul, map_inv, hcomm (ψ m), mul_inv_cancel_right]
      exact h1
    · intro hg
      have hgM : g ∈ M := by
        have h1 := hWM hg
        have e : g = (m : G)⁻¹ * ((m : G) * g * (m : G)⁻¹) * m := by group
        rw [e]
        exact mul_mem (mul_mem (inv_mem m.2) h1) m.2
      have h1 := (hmem ⟨_, hWM hg⟩).1 hg
      rw [hmem ⟨g, hgM⟩]
      have h2 : (⟨(m : G) * g * (m : G)⁻¹, hWM hg⟩ : ↥M) = m * ⟨g, hgM⟩ * m⁻¹ := rfl
      rw [h2, map_mul, map_mul, map_inv, hcomm (ψ m), mul_inv_cancel_right] at h1
      exact h1
  obtain ⟨k, hkW, hk⟩ :=
    CFSG.RankThree.PartOne.Sec15Frattini.exists_mem_normalizer_of_isSylowOf (hT.of_le hTW hWM) hmW
  obtain ⟨t, htT, hte⟩ := mem_map.1 ((hmem ⟨k, hWM hkW⟩).1 hkW)
  refine ⟨t * ((⟨k, hWM hkW⟩ : ↥M)⁻¹ * m), ?_, ?_⟩
  · exact mul_mem (le_normalizer (mem_subgroupOf.1 htT)) hk
  · rw [map_mul, map_mul, map_inv, hte, mul_inv_cancel_left]

theorem uc22s218u_normalizer_le (D : Data G) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hsp : IsStronglyPEmbedded p D.M) (h71 : F07.R71 D) (h72 : F07.R72 D)
    (hKf : PartTwo.S19.K_19_25_noL2SzSection) {X : Subgroup G} (hXM : X ≤ D.M) (hX1 : X ≠ ⊥)
    (hrank : 1 < CFSG.Open.pRank p (normalizer (X : Set G) ⊓ D.M)) {n : ℕ} (hn3 : 3 ≤ n)
    (hsec : PartTwo.S19.HasL2SzSection n (normalizer (X : Set G) ⊓ D.M)) :
    normalizer (X : Set G) ≤ D.M := by
  by_contra hNM
  haveI : Fact p.Prime := ⟨hp⟩
  set H : Subgroup G := normalizer (X : Set G) with hHdef
  have hHtop : H ≠ ⊤ := by
    intro htop
    haveI : X.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases D.standing.simple.eq_bot_or_eq_top_of_normal X with hbot | htop'
    · exact hX1 hbot
    · exact hsp.1 (eq_top_iff.mpr (htop' ▸ hXM))
  have h7 : F07.Sec7Hyp D p H := ⟨hp, hp2, hsp, hHtop, hNM, hrank⟩
  obtain ⟨hFstar, hlist⟩ := h72 p H h7
  obtain ⟨hKodd, hKM, -⟩ := h71 p H h7
  have hdvd : p ∣ Nat.card (H ⊓ D.M : Subgroup G) := by
    have hpow : p ^ 2 ∣ Nat.card (H ⊓ D.M : Subgroup G) :=
      (pow_dvd_pow p hrank).trans
        (CFSG.RankThreeEvenClassification.Helpers.prime_power_pRank_dvd_card p hp (H ⊓ D.M))
    exact (dvd_pow_self p (by norm_num : (2 : ℕ) ≠ 0)).trans hpow
  have hY : IsStronglyPEmbedded p ((H ⊓ D.M).subgroupOf H) := hsp.subgroupOf hNM hdvd
  have hKle : CFSG.pPrimeCore p ↥H ≤ (H ⊓ D.M).subgroupOf H := by
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr ⟨x.2, hKM (Subgroup.mem_map_of_mem H.subtype hx)⟩
  have hKcop : ¬ p ∣ Nat.card (CFSG.pPrimeCore p ↥H) :=
    (hp.coprime_iff_not_dvd).mp (CFSG.pPrimeCore_coprime_card (G := ↥H) (p := p))
  have hNbar := hY.map_quotient hKle hKcop
  have hKodd' : Odd (Nat.card (CFSG.pPrimeCore p ↥H)) := by
    have : Nat.card (F07.PPrimeCoreIn p H) = Nat.card (CFSG.pPrimeCore p ↥H) :=
      Subgroup.card_map_of_injective H.subtype_injective
    rwa [← this]
  have hsecbar := PartTwo.S19.hasL2SzSection_map_of_odd hKodd' inf_le_left hsec
  exact hKf (F07.QuotK7 p H) p (F07.ImageModK p H (Opp p H)) hp hp2 hFstar
    (CFSG.pPrimeCore_quotient_eq_bot hp) hlist _ hNbar n hn3 hsecbar

end CFSG.LocalAnalysis.UniquenessCase.UC22
