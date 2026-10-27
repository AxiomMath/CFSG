module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight103FourKFact
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102Cent
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102U4OddRankHolds
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102Syl3Holds
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102U45KeyHolds
import CFSG.LocalAnalysis.UniquenessCase.UC6S846i

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC6S846 (SigmaStd rhoL rhoL_fix_iff
  eq_one_of_mem_isPGroup_of_mem_isPGroup isPGroup_pCoreOf exists_elemAbelian_card_of_le_pRank
  exists_lift_normalized)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem isSylowOf_of_forall_isPGroup_le_eq {p : ℕ} [Fact p.Prime] {K P : Subgroup G}
    (hPK : P ≤ K) (hP : IsPGroup p P)
    (hmax : ∀ T : Subgroup G, T ≤ K → IsPGroup p T → P ≤ T → T = P) : IsSylowOf p P K := by
  obtain ⟨Q, hQ⟩ := (hP.comap_subtype (K := K)).exists_le_sylow
  have hT : IsSylowOf p ((Q : Subgroup K).map K.subtype) K := ⟨Q, rfl⟩
  have hPT : P ≤ (Q : Subgroup K).map K.subtype := fun x hx =>
    ⟨⟨x, hPK hx⟩, hQ (Subgroup.mem_subgroupOf.2 hx), rfl⟩
  rw [← hmax _ hT.le hT.isPGroup hPT]
  exact hT

private theorem card_comap_of_le_range {F H : Type*} [Group F] [Finite F] [Group H]
    (φ : F →* H) {A : Subgroup H} (hA : A ≤ φ.range) :
    Nat.card (A.comap φ) = Nat.card φ.ker * Nat.card A := by
  let ψ : ↥(A.comap φ) →* ↥A := (φ.comp (A.comap φ).subtype).codRestrict A (fun x => x.2)
  have hsurj : Function.Surjective ψ := by
    rintro ⟨a, ha⟩
    obtain ⟨f, hf⟩ := hA ha
    refine ⟨⟨f, ?_⟩, Subtype.ext hf⟩
    rw [Subgroup.mem_comap, hf]
    exact ha
  have hker : ψ.ker = φ.ker.subgroupOf (A.comap φ) := by
    ext x
    show ψ x = 1 ↔ φ (x : F) = 1
    constructor
    · intro h; exact congrArg Subtype.val h
    · intro h; exact Subtype.ext h
  have hψ := Subgroup.card_ker_mul_card_range ψ
  rw [hker, MonoidHom.range_eq_top.2 hsurj, Subgroup.card_top] at hψ
  have hkerle : φ.ker ≤ A.comap φ := fun x hx => by
    rw [Subgroup.mem_comap]
    rw [MonoidHom.mem_ker] at hx
    rw [hx]
    exact A.one_mem
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkerle).toEquiv] at hψ
  exact hψ.symm

private theorem le_centralizer_of_fix_bar2 {L S C : Subgroup G} {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) (hSL : S ≤ L) (hSq : IsPGroup q S) (hCN : C ≤ normalizer (L : Set G))
    (hCS : C ≤ normalizer (S : Set G))
    (hfix : ∀ (c : G), c ∈ C → ∀ (hNc : c ∈ normalizer (L : Set G)) (s : G) (hs : s ∈ S),
      rhoL L ⟨c, hNc⟩ (QuotientGroup.mk (⟨s, hSL hs⟩ : ↥L) : Bar2 L) =
        (QuotientGroup.mk (⟨s, hSL hs⟩ : ↥L) : Bar2 L)) :
    C ≤ centralizer (S : Set G) := by
  intro c hc
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  have h2 := (rhoL_fix_iff L ⟨c, hCN hc⟩ ⟨s, hSL hs⟩).1 (hfix c hc (hCN hc) s hs)
  have h3 : c * s * c⁻¹ * s⁻¹ ∈ S :=
    S.mul_mem ((Subgroup.mem_normalizer_iff.1 (hCS hc) s).1 hs) (S.inv_mem hs)
  have h4 : c * s * c⁻¹ * s⁻¹ = 1 :=
    eq_one_of_mem_isPGroup_of_mem_isPGroup hq hq2 hSq (isPGroup_pCoreOf L) h3 h2
  have h5 : c * s * c⁻¹ = s := mul_inv_eq_one.1 h4
  calc s * c = c * s * c⁻¹ * c := by rw [h5]
    _ = c * s := by group

private theorem exists_card_pow_of_le_range_card_sq {L : Subgroup G} {p : ℕ} (hp : p.Prime)
    {F : Subgroup G} (hFel : IsElemAbelian p F) (hFcard : Nat.card F = p ^ 4)
    {φ : ↥F →* MulAut (Bar2 L)} {Cb : Subgroup (MulAut (Bar2 L))} (hCb : Cb ≤ φ.range)
    (hcard : Nat.card φ.range ≤ p ^ 2 * Nat.card Cb) :
    ∃ k : ℕ, 2 ≤ k ∧ IsElemAbelian p ((Cb.comap φ).map F.subtype) ∧
      Nat.card ((Cb.comap φ).map F.subtype) = p ^ k := by
  have : Fact p.Prime := ⟨hp⟩
  have hCFcard : Nat.card (Cb.comap φ) = Nat.card φ.ker * Nat.card Cb :=
    card_comap_of_le_range φ hCb
  have hCpow : Nat.card ((Cb.comap φ).map F.subtype) = Nat.card (Cb.comap φ) :=
    Subgroup.card_map_of_injective F.subtype_injective
  have hsize : Nat.card F ≤ p ^ 2 * Nat.card ((Cb.comap φ).map F.subtype) := by
    calc Nat.card F = Nat.card φ.ker * Nat.card φ.range :=
          (Subgroup.card_ker_mul_card_range φ).symm
      _ ≤ Nat.card φ.ker * (p ^ 2 * Nat.card Cb) := Nat.mul_le_mul_left _ hcard
      _ = p ^ 2 * (Nat.card φ.ker * Nat.card Cb) := by ring
      _ = p ^ 2 * Nat.card (Cb.comap φ) := by rw [hCFcard]
      _ = p ^ 2 * Nat.card ((Cb.comap φ).map F.subtype) := by rw [hCpow]
  have hCel : IsElemAbelian p ((Cb.comap φ).map F.subtype) :=
    hFel.mono (by rintro x ⟨y, -, rfl⟩; exact y.2)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hCel.isPGroup
  refine ⟨k, ?_, hCel, hk⟩
  have h1 : p ^ 4 ≤ p ^ (k + 2) := by
    calc p ^ 4 = Nat.card F := hFcard.symm
      _ ≤ p ^ 2 * Nat.card ((Cb.comap φ).map F.subtype) := hsize
      _ = p ^ 2 * p ^ k := by rw [hk]
      _ = p ^ (k + 2) := by ring
  have := (Nat.pow_le_pow_iff_right hp.one_lt).1 h1
  omega

private theorem exists_elemAbelian_fixing_sylow_three_of_dvd {D : Data G}
    (hKD : KU45KeyDvd) {L : Subgroup G} {p n : ℕ} (hpσ : p ∈ D.sig) (hp3 : p ≠ 3)
    (hX : IsU45 (Bar2 L) n) (hN : D.M ≤ normalizer (L : Set G)) (hpn : p ∣ 2 ^ n + 1)
    (h4 : 4 ≤ Open.pRank p D.M) :
    ∃ (Sb : Sylow 3 (Bar2 L)) (C : Subgroup G) (k : ℕ), C ≤ D.M ∧ IsElemAbelian p C ∧
      Nat.card C = p ^ k ∧ 2 ≤ k ∧
      ∀ (c : G), c ∈ C → ∀ (hNc : c ∈ normalizer (L : Set G)) (x : ↥L),
        (QuotientGroup.mk x : Bar2 L) ∈ (Sb : Subgroup (Bar2 L)) →
          rhoL L ⟨c, hNc⟩ (QuotientGroup.mk x : Bar2 L) = (QuotientGroup.mk x : Bar2 L) := by
  classical
  obtain ⟨hp, hp2⟩ := D.sig_prime p hpσ
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (3 : ℕ).Prime := ⟨by norm_num⟩
  obtain ⟨F, hFM, hFel, hFcard⟩ :=
    exists_elemAbelian_card_of_le_pRank (M := D.M) hp (k := 4) h4
  have hFN : F ≤ normalizer (L : Set G) := hFM.trans hN
  let FN : Subgroup ↥(normalizer (L : Set G)) := F.subgroupOf _
  let φ : ↥F →* MulAut (Bar2 L) := (rhoL L).comp (Subgroup.inclusion hFN)
  let R : Subgroup (MulAut (Bar2 L)) := FN.map (rhoL L)
  have hRel : IsElemAbelian p R := (hFel.subgroupOf _).map (rhoL L)
  have hφrange : φ.range = R := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨Subgroup.inclusion hFN x, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨⟨(x : G), hx⟩, ?_⟩
      show rhoL L (Subgroup.inclusion hFN ⟨(x : G), hx⟩) = rhoL L x
      rw [show Subgroup.inclusion hFN ⟨(x : G), hx⟩ = x from Subtype.ext rfl]
  obtain ⟨Sb, hSbp, hSbidx, Cb, hCbR, hCbfix, hcard⟩ :=
    hKD (Bar2 L) n hX p hp hp2 hp3 hpn R hRel
  let Sb' : Sylow 3 (Bar2 L) := hSbp.toSylow hSbidx
  have hSb'coe : (Sb' : Subgroup (Bar2 L)) = Sb := IsPGroup.toSylow_coe hSbp hSbidx
  obtain ⟨k, hk2, hCel, hCcard⟩ :=
    exists_card_pow_of_le_range_card_sq (L := L) hp hFel hFcard (φ := φ) (Cb := Cb)
      (hφrange.symm ▸ hCbR) (hφrange.symm ▸ hcard)
  refine ⟨Sb', (Cb.comap φ).map F.subtype, k, ?_, hCel, hCcard, hk2, ?_⟩
  · rintro x ⟨y, -, rfl⟩
    exact hFM y.2
  · intro c hc hNc x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hc
    have hxSb : (QuotientGroup.mk x : Bar2 L) ∈ Sb := hSb'coe ▸ hx
    change rhoL L (⟨F.subtype y, hNc⟩ : ↥(normalizer (L : Set G)))
      (QuotientGroup.mk x : Bar2 L) = (QuotientGroup.mk x : Bar2 L)
    have heq : (⟨F.subtype y, hNc⟩ : ↥(normalizer (L : Set G))) = Subgroup.inclusion hFN y :=
      Subtype.ext rfl
    rw [heq]
    exact hCbfix _ hy _ hxSb

private theorem exists_rank_two_centralizing_sylow_three_of_dvd {D : Data G} (hSg : SigmaStd D)
    (hKD : KU45KeyDvd) {L P : Subgroup G} {p n : ℕ} (hH : F08.Hyp8102 D L P p n)
    (hX : IsU45 (Bar2 L) n) (hN : D.M ≤ normalizer (L : Set G)) (hpn : p ∣ 2 ^ n + 1)
    (h4 : 4 ≤ Open.pRank p D.M) :
    ∃ (S C : Subgroup G) (k : ℕ), S ≤ L ∧ IsSylowOf 3 S L ∧ IsElemAbelian p C ∧
      Nat.card C = p ^ k ∧ 2 ≤ k ∧ C ≤ D.M ⊓ centralizer (S : Set G) := by
  classical
  have : Fact (3 : ℕ).Prime := ⟨by norm_num⟩
  obtain ⟨Sb, C, k, hCM, hCel, hCcard, hk, hfixb⟩ :=
    exists_elemAbelian_fixing_sylow_three_of_dvd hKD hH.2.2.2.1 (prime_of_hyp8102 hSg hH).2.2
      hX hN hpn h4
  have hCN : C ≤ normalizer (L : Set G) := hCM.trans hN
  have hSbhyp : ∀ (b : G) (hb : b ∈ normalizer (L : Set G)), b ∈ C →
      ∀ s ∈ (Sb : Subgroup (Bar2 L)), rhoL L ⟨b, hb⟩ s ∈ (Sb : Subgroup (Bar2 L)) := by
    intro b hb hbC s hs
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
    exact (hfixb b hbC hb x hs).symm ▸ hs
  obtain ⟨S, hSL, hSq, hSmax, hSmap, hCS⟩ :=
    exists_lift_normalized (B₁ := C) hCN (D.sig_prime p hH.2.2.2.1).1
      (by norm_num : (3 : ℕ).Prime) (by norm_num : (3 : ℕ) ≠ 2) (prime_of_hyp8102 hSg hH).2.2
      (D.sig_prime p hH.2.2.2.1).2 hCel.isPGroup Sb hSbhyp
  refine ⟨S, C, k, hSL, isSylowOf_of_forall_isPGroup_le_eq hSL hSq hSmax, hCel, hCcard, hk,
    le_inf hCM ?_⟩
  refine le_centralizer_of_fix_bar2 (by norm_num : (3 : ℕ).Prime) (by norm_num : (3 : ℕ) ≠ 2)
    hSL hSq hCN hCS ?_
  intro c hc hNc s hs
  have hsSb : (QuotientGroup.mk (⟨s, hSL hs⟩ : ↥L) : Bar2 L) ∈ (Sb : Subgroup (Bar2 L)) := by
    rw [← hSmap]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hs)
  exact hfixb c hc hNc ⟨s, hSL hs⟩ hsSb

private theorem two_le_pRank_centralizer_of_isSylowOf {D : Data G} {L P S C : Subgroup G}
    {p k : ℕ} (hp : p.Prime) (hLM : L ≤ D.M) (hPsyl : IsSylowOf 3 P L)
    (hSsyl : IsSylowOf 3 S L) (hC : C ≤ D.M ⊓ centralizer (S : Set G))
    (hCel : IsElemAbelian p C) (hCcard : Nat.card C = p ^ k) (hk : 2 ≤ k) :
    2 ≤ Open.pRank p (D.M ⊓ centralizer (P : Set G)) := by
  classical
  have : Fact (3 : ℕ).Prime := ⟨by norm_num⟩
  obtain ⟨l, hlL, hconj⟩ := hPsyl.exists_mem_conj hSsyl
  have hSmap : S = P.map (MulAut.conj l).toMonoidHom := by
    ext x
    rw [hconj x, Subgroup.mem_map]
    constructor
    · intro hx
      refine ⟨l⁻¹ * x * l, hx, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    · rintro ⟨y, hy, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rwa [show l⁻¹ * (l * y * l⁻¹) * l = y from by group]
  have hconjC : C.map (MulAut.conj l⁻¹).toMonoidHom ≤ D.M ⊓ centralizer (P : Set G) := by
    refine le_inf ?_ ?_
    · intro x hx
      obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hx
      have hcM : c ∈ D.M := (hC hc).1
      have hlM : l ∈ D.M := hLM hlL
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using
        D.M.mul_mem (D.M.mul_mem (D.M.inv_mem hlM) hcM) hlM
    · intro x hx
      obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hx
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      have hSc : c ∈ centralizer (S : Set G) := (hC hc).2
      have hsS : MulAut.conj l s ∈ S := by
        rw [hSmap]
        exact Subgroup.mem_map_of_mem _ hs
      have h1 : MulAut.conj l s * c = c * MulAut.conj l s :=
        Subgroup.mem_centralizer_iff.1 hSc _ hsS
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      have h1' : l * s * l⁻¹ * c = c * (l * s * l⁻¹) := by
        simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h1
      calc s * (l⁻¹ * c * l) = l⁻¹ * (l * s * l⁻¹ * c) * l := by group
        _ = l⁻¹ * (c * (l * s * l⁻¹)) * l := by rw [h1']
        _ = (l⁻¹ * c * l) * s := by group
  have hcardC : Nat.card (C.map (MulAut.conj l⁻¹).toMonoidHom) = p ^ k := by
    rw [Subgroup.card_map_of_injective (MulAut.conj l⁻¹).injective, hCcard]
  exact hk.trans (CFSG.SectionRank.le_pRank hp.one_lt hconjC (hCel.map _) hcardC)

theorem false_of_hyp8102_of_four_le_pRank {D : Data G} (hSg : SigmaStd D) (h76 : F07.R76Sig D)
    (h614 : UC6.R6_14 D) (h82 : F08.R82 D) (hKD : KU45KeyDvd) {L P : Subgroup G} {p n : ℕ}
    (hH : F08.Hyp8102 D L P p n) (h4 : 4 ≤ Open.pRank p D.M) : False := by
  classical
  have hn : Even n := even_of_hyp8102 h82 kU4OddRank_holds hH
  have hX : IsU45 (Bar2 L) n := isU45_of_hyp8102 hH hn
  have hN : D.M ≤ normalizer (L : Set G) := le_normalizer_of_hyp8102 hSg kU45Syl3_holds hH hX
  have hpn : p ∣ 2 ^ n + 1 :=
    dvd_two_pow_add_one_of_hyp8102 hSg h76 h614 kU45Syl3_holds kU45Key_holds hH hX hN
  obtain ⟨S, C, k, -, hSylS, hCel, hCcard, hk, hCinf⟩ :=
    exists_rank_two_centralizing_sylow_three_of_dvd hSg hKD hH hX hN hpn h4
  have h2 := two_le_pRank_centralizer_of_isSylowOf (D := D) (D.sig_prime p hH.2.2.2.1).1
    hH.1.1.le hH.2.2.2.2 hSylS hCinf hCel hCcard hk
  have h1 := pRank_centralizer_le_one hSg h76 h614 kU45Syl3_holds hH hX hN
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

end
