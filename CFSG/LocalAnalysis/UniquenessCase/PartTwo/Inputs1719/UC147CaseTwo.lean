module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC147Frame
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC147KGen
import CFSG.GroupTheory.IsCyclicOfPRankLeOne
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R93b
import CFSG.Quasithin.EmptyFaithful.S146zYFOOrd
import CFSG.GroupTheory.SylowQuotientSup
import CFSG.RankThree.GroupTheory.PerfectSubnormalModNormal
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC147Route
import CFSG.GroupTheory.ThreeTranspositions.StrongSup
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Ctx147

omit [Finite G] in
theorem subgroupOf_commutator {H K N : Subgroup G} (hHN : H ≤ N) (hKN : K ≤ N) :
    (⁅H, K⁆).subgroupOf N = ⁅H.subgroupOf N, K.subgroupOf N⁆ := by
  refine le_antisymm ?_ ?_
  · set S : Set G := {g | ∃ g₁ ∈ H, ∃ g₂ ∈ K, ⁅g₁, g₂⁆ = g} with hSdef
    have hS : S ⊆ N := by
      rintro g ⟨g₁, hg₁, g₂, hg₂, rfl⟩
      exact N.mul_mem (N.mul_mem (N.mul_mem (hHN hg₁) (hKN hg₂)) (N.inv_mem (hHN hg₁)))
        (N.inv_mem (hKN hg₂))
    have hSN : Subgroup.closure S ≤ N := (Subgroup.closure_le N).2 hS
    intro x hx
    have hxS : (x : G) ∈ Subgroup.closure S := by
      rw [← Subgroup.commutator_def]
      exact Subgroup.mem_subgroupOf.mp hx
    have key : ∀ y : G, y ∈ Subgroup.closure S → ∀ (hy : y ∈ N),
        (⟨y, hy⟩ : ↥N) ∈ ⁅H.subgroupOf N, K.subgroupOf N⁆ := by
      intro y hy
      refine Subgroup.closure_induction (k := S)
        (p := fun y _ => ∀ hy : y ∈ N, (⟨y, hy⟩ : ↥N) ∈
          ⁅H.subgroupOf N, K.subgroupOf N⁆) ?_ ?_ ?_ ?_ hy
      · intro z hz hzN
        obtain ⟨g₁, hg₁, g₂, hg₂, rfl⟩ := hz
        have h1N : g₁ ∈ N := hHN hg₁
        have h2N : g₂ ∈ N := hKN hg₂
        have heq : (⟨⁅g₁, g₂⁆, hzN⟩ : ↥N) =
            ⁅(⟨g₁, h1N⟩ : ↥N), (⟨g₂, h2N⟩ : ↥N)⁆ := by
          ext
          simp [commutatorElement_def]
        rw [heq]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mpr hg₁)
          (Subgroup.mem_subgroupOf.mpr hg₂)
      · intro _
        exact Subgroup.one_mem _
      · intro a b _ha _hb haT hbT habN
        have haN : a ∈ N := hSN _ha
        have hbN : b ∈ N := hSN _hb
        have heq : (⟨a * b, habN⟩ : ↥N) = (⟨a, haN⟩ : ↥N) * (⟨b, hbN⟩ : ↥N) := rfl
        rw [heq]
        exact Subgroup.mul_mem _ (haT haN) (hbT hbN)
      · intro a _ha haT haN
        have haN' : a ∈ N := hSN _ha
        have heq : (⟨a⁻¹, haN⟩ : ↥N) = (⟨a, haN'⟩ : ↥N)⁻¹ := rfl
        rw [heq]
        exact Subgroup.inv_mem _ (haT haN')
    exact key x hxS x.2
  · rw [Subgroup.commutator_le]
    intro x hx y hy
    exact Subgroup.mem_subgroupOf.mpr <| Subgroup.commutator_mem_commutator
      (Subgroup.mem_subgroupOf.mp hx) (Subgroup.mem_subgroupOf.mp hy)

theorem mem_sup_of_mem_normalizer_of_isSylowOf {D : Data G} {Q P Y N : Subgroup G} {p : ℕ}
    [Fact p.Prime]
    (hYnorm : normalizer (Y : Set G) ≤ D.M) (hPN : P ≤ N) (hQN : Q ≤ N)
    (hQn : (Q.subgroupOf N).Normal)
    (hPY : P ≤ Q ⊔ Y) (hY : CFSG.ABGLocalTools.IsSylowOf p Y P)
    {n : G} (hnN : n ∈ N) (hnP : n ∈ normalizer (P : Set G)) :
    n ∈ Q ⊔ (N ⊓ D.M) := by
  obtain ⟨hYP, hYp, hYidx⟩ := (CFSG.ABGLocalTools.isSylowOf_iff).mp hY
  have hYM : Y ≤ D.M := Subgroup.le_normalizer.trans hYnorm
  let Yn : Subgroup G := Y.map (MulAut.conj n).toMonoidHom
  have hPconj : P.map (MulAut.conj n).toMonoidHom = P :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hnP
  have hYn_le : Yn ≤ P := by
    rintro - ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hnP y).mp (hYP hy)
  have hYn_p : IsPGroup p Yn := hYp.map _
  have hYn_idx : ¬ p ∣ Yn.relIndex P := by
    have h := Subgroup.relIndex_map_map_of_injective
      (f := (MulAut.conj n).toMonoidHom) Y P (MulAut.conj n).injective
    rw [show Yn = Y.map (MulAut.conj n).toMonoidHom from rfl, ← hPconj]
    rw [h]
    exact hYidx
  have hYn : CFSG.ABGLocalTools.IsSylowOf p Yn P :=
    (CFSG.ABGLocalTools.isSylowOf_iff).mpr ⟨hYn_le, hYn_p, hYn_idx⟩
  obtain ⟨k, hkP, hconj⟩ := CFSG.ABGLocalTools.IsSylowOf.exists_mem_conj hY hYn
  have hnorm : k⁻¹ * n ∈ normalizer (Y : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro - ⟨y, hy, rfl⟩
      have hyn : n * y * n⁻¹ ∈ Yn := Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
      have h1 := (hconj (n * y * n⁻¹)).mp hyn
      simpa [MulAut.conj_apply, mul_assoc] using h1
    · rw [Subgroup.card_map_of_injective (MulAut.conj (k⁻¹ * n)).injective]
  have hkm : k⁻¹ * n ∈ D.M := hYnorm hnorm
  let : (Q.subgroupOf N).Normal := hQn
  have hYN : Y ≤ N := hYP.trans hPN
  have hsup : (Q ⊔ Y).subgroupOf N = Q.subgroupOf N ⊔ Y.subgroupOf N :=
    Subgroup.subgroupOf_sup hQN hYN
  have hk' : (⟨k, hPN hkP⟩ : ↥N) ∈ Q.subgroupOf N ⊔ Y.subgroupOf N := by
    rw [← hsup]
    exact Subgroup.mem_subgroupOf.mpr (hPY hkP)
  obtain ⟨q, hq, y, hy, hqy⟩ := (Subgroup.mem_sup_of_normal_left).mp hk'
  have hqQ : (q : G) ∈ Q := Subgroup.mem_subgroupOf.mp hq
  have hyY : (y : G) ∈ Y := Subgroup.mem_subgroupOf.mp hy
  have hk_eq : k = (q : G) * (y : G) := by
    have h := congrArg Subtype.val hqy
    simpa using h.symm
  have hkmN : k⁻¹ * n ∈ N := N.mul_mem (N.inv_mem (hPN hkP)) hnN
  have hym : (y : G) * (k⁻¹ * n) ∈ N ⊓ D.M :=
    ⟨N.mul_mem (hYN hyY) hkmN, D.M.mul_mem (hYM hyY) hkm⟩
  have hkn : n = (q : G) * ((y : G) * (k⁻¹ * n)) := by
    rw [hk_eq]
    group
  rw [hkn]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hqQ) (Subgroup.mem_sup_right hym)


variable {D : Data G} {L : Fin 2 → Subgroup G} {n : Fin 2 → ℕ} {r p : ℕ} {A X B R : Subgroup G}

theorem isCyclic_of_mem_calMOf (c : Ctx147 D L n r p A X B R)
    (hsp3 : IsStronglyPEmbedded 3 D.M)
    (hU4b : ∀ H : Subgroup G, IsTwoLocal H → 2 ≤ CFSG.Open.pRank 3 (H ⊓ D.M) → H ≤ D.M)
    {N : Subgroup G} (hN : N ∈ calMOf (B ⊔ R)) (hNM : ¬ N ≤ D.M) :
    ∀ P : Subgroup G, P ≤ N → IsPGroup 3 P → IsCyclic P := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hBN : B ≤ N := le_sup_left.trans hN.2
  have hrank : CFSG.Open.pRank 3 (N ⊓ D.M) ≤ 1 := by
    by_contra h
    have h2 : 2 ≤ CFSG.Open.pRank 3 (N ⊓ D.M) :=
      Nat.succ_le_iff.mpr (Nat.lt_of_not_le h)
    exact hNM (hU4b N hN.1.1 h2)
  have hB3 : IsPGroup 3 B := IsPGroup.of_card (n := 1) (by simpa using c.card_B)
  obtain ⟨P₀, hBP₀⟩ := (hB3.comap_subtype (K := N)).exists_le_sylow
  let P' : Subgroup G := P₀.map N.subtype
  have hP'N : P' ≤ N := Subgroup.map_subtype_le _
  have hP'3 : IsPGroup 3 P' := P₀.isPGroup'.map N.subtype
  have hBP' : B ≤ P' := by
    intro b hb
    exact Subgroup.mem_map.mpr
      ⟨⟨b, hBN hb⟩, hBP₀ (Subgroup.mem_subgroupOf.mpr hb), rfl⟩
  have hne : P' ⊓ D.M ≠ ⊥ := by
    intro hbot
    have hb : B ≤ P' ⊓ D.M := le_inf hBP' c.hB
    rw [hbot] at hb
    have h1 : Nat.card B = 1 := by rw [le_bot_iff.mp hb, Subgroup.card_bot]
    have h3 := c.card_B
    rw [h1] at h3
    exact absurd h3 (by norm_num)
  have hnorm : normalizer ((P' ⊓ D.M : Subgroup G) : Set G) ≤ D.M :=
    hsp3.normalizer_le hne hP'3.to_inf_left inf_le_right
  have hnorm' : normalizer ((P' ⊓ D.M).subgroupOf P') = (P' ⊓ D.M).subgroupOf P' := by
    refine le_antisymm ?_ Subgroup.le_normalizer
    rw [← Subgroup.subgroupOf_normalizer_eq inf_le_left]
    intro x hx
    exact ⟨x.2, hnorm hx⟩
  let : Group.IsNilpotent ↥P' := IsPGroup.isNilpotent (p := 3) hP'3
  have htop : (P' ⊓ D.M).subgroupOf P' = ⊤ :=
    (normalizerCondition_iff_only_full_group_self_normalizing.mp
      (Group.normalizerCondition_of_isNilpotent (G := ↥P')) _ hnorm')
  have hPM : P' ≤ D.M := by
    have hle : P' ≤ P' ⊓ D.M := Subgroup.subgroupOf_eq_top.mp htop
    exact hle.trans inf_le_right
  have hrankP' : CFSG.Open.pRank 3 P' ≤ 1 :=
    (CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) (le_inf hP'N hPM)).trans hrank
  have hcycP' : IsCyclic ↥P' :=
    CFSG.isCyclic_of_pRank_le_one Nat.prime_three (by norm_num) hP'3 (by
      rwa [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup])
  intro P hPN hP3
  obtain ⟨Q₀, hPQ₀⟩ := (hP3.comap_subtype (K := N)).exists_le_sylow
  have hcycP₀ : IsCyclic ↥(P₀ : Subgroup ↥N) :=
    (Subgroup.equivMapOfInjective (H := (P₀ : Subgroup ↥N)) N.subtype
      N.subtype_injective).isCyclic.mpr hcycP'
  have hQ₀cyc : IsCyclic ↥(Q₀ : Subgroup ↥N) :=
    (Sylow.equiv P₀ Q₀).isCyclic.mp hcycP₀
  let Q : Subgroup G := Q₀.map N.subtype
  have hQcyc : IsCyclic ↥Q := by
    have e : ↥(Q₀ : Subgroup ↥N) ≃* ↥Q :=
      Subgroup.equivMapOfInjective (H := (Q₀ : Subgroup ↥N)) N.subtype N.subtype_injective
    exact e.isCyclic.mp hQ₀cyc
  have hPQ : P ≤ Q := by
    intro x hx
    exact Subgroup.mem_map.mpr
      ⟨⟨x, hPN hx⟩, hPQ₀ (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have : IsCyclic ↥Q := hQcyc
  exact Subgroup.isCyclic_of_le hPQ

omit [Finite G] in
theorem isCyclic_sylow_three {N : Subgroup G}
    (hcyc : ∀ P : Subgroup G, P ≤ N → IsPGroup 3 P → IsCyclic P) (P : Sylow 3 ↥N) :
    IsCyclic (P : Subgroup ↥N) := by
  have h1 : IsCyclic ↥((P : Subgroup ↥N).map N.subtype) :=
    hcyc _ (Subgroup.map_subtype_le _) (P.isPGroup'.map N.subtype)
  exact (Subgroup.equivMapOfInjective (H := (P : Subgroup ↥N)) N.subtype
    N.subtype_injective).isCyclic.mpr h1

omit [Finite G] in
theorem card_map_mk'_eq_of_disjoint_pPrimeCore {N H : Subgroup G} (hHN : H ≤ N)
    (hdisj : H.subgroupOf N ⊓ CFSG.pPrimeCore 3 ↥N = ⊥) :
    Nat.card ((H.subgroupOf N).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥N))) = Nat.card H := by
  classical
  let π : ↥N →* (↥N ⧸ CFSG.pPrimeCore 3 ↥N) := QuotientGroup.mk' _
  let φ : ↥(H.subgroupOf N) →* ↥((H.subgroupOf N).map π) :=
    (π.comp (H.subgroupOf N).subtype).codRestrict _ fun x => ⟨x, x.2, rfl⟩
  have hφinj : Function.Injective φ := by
    intro x y hxy
    have h1 : π (x : ↥N) = π (y : ↥N) := congrArg Subtype.val hxy
    have h2 : π ((x : ↥N)⁻¹ * y) = 1 := by
      rw [map_mul, map_inv, h1, inv_mul_cancel]
    have h3 : (x : ↥N)⁻¹ * y ∈ CFSG.pPrimeCore 3 ↥N := by
      rw [← QuotientGroup.ker_mk' (CFSG.pPrimeCore 3 ↥N)]
      exact MonoidHom.mem_ker.mpr h2
    have h4 : (x : ↥N)⁻¹ * y ∈ H.subgroupOf N :=
      (H.subgroupOf N).mul_mem ((H.subgroupOf N).inv_mem x.2) y.2
    have h5 : (x : ↥N)⁻¹ * y ∈ (⊥ : Subgroup ↥N) := by
      rw [← hdisj]
      exact ⟨h4, h3⟩
    have h6 : x⁻¹ * y = 1 := Subtype.ext (by simpa using h5)
    exact inv_mul_eq_one.mp h6
  have hφsurj : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  calc Nat.card ((H.subgroupOf N).map π)
      = Nat.card ↥(H.subgroupOf N) :=
        (Nat.card_congr (Equiv.ofBijective φ ⟨hφinj, hφsurj⟩)).symm
    _ = Nat.card H := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHN).toEquiv

theorem pPrimeCore_eq_subgroupOf_relPPrimeCore {N : Subgroup G} :
    CFSG.pPrimeCore 3 ↥N = (relPPrimeCore 3 N).subgroupOf N := by
  rw [show relPPrimeCore 3 N = (CFSG.pPrimeCore 3 ↥N).map N.subtype from
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_eq_map
      Nat.prime_three N]
  exact (Subgroup.comap_map_eq_self_of_injective N.subtype_injective _).symm

theorem inf_relPPrimeCore_eq_bot_of_card_eq_three {N H : Subgroup G} (hH : Nat.card H = 3) :
    H ⊓ relPPrimeCore 3 N = ⊥ := by
  have hcop : Nat.Coprime 3 (Nat.card (relPPrimeCore 3 N)) :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.coprime_card_relPPrimeCore
      Nat.prime_three N
  have hdvdH : Nat.card ↥(H ⊓ relPPrimeCore 3 N) ∣ Nat.card H :=
    Subgroup.card_dvd_of_le inf_le_left
  have hdvdQ : Nat.card ↥(H ⊓ relPPrimeCore 3 N) ∣ Nat.card (relPPrimeCore 3 N) :=
    Subgroup.card_dvd_of_le inf_le_right
  have hthree : Nat.card ↥(H ⊓ relPPrimeCore 3 N) ∣ 3 := hH ▸ hdvdH
  have hone : Nat.card ↥(H ⊓ relPPrimeCore 3 N) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop hthree hdvdQ
  exact (Subgroup.eq_bot_iff_card (H ⊓ relPPrimeCore 3 N)).mpr hone

theorem subgroupOf_inf_pPrimeCore_eq_bot {N H : Subgroup G}
    (h : H ⊓ relPPrimeCore 3 N = ⊥) : H.subgroupOf N ⊓ CFSG.pPrimeCore 3 ↥N = ⊥ := by
  rw [pPrimeCore_eq_subgroupOf_relPPrimeCore]
  have hset : H.subgroupOf N ⊓ (relPPrimeCore 3 N).subgroupOf N =
      (H ⊓ relPPrimeCore 3 N).subgroupOf N := by
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
  rw [hset, h, Subgroup.bot_subgroupOf]

theorem normal_image_of_pCore_quotient_ne_bot (c : Ctx147 D L n r p A X B R) {N : Subgroup G}
    (hBN : B ≤ N) (hcyc : ∀ P : Subgroup G, P ≤ N → IsPGroup 3 P → IsCyclic P)
    (hKne : CFSG.pCore 3 (↥N ⧸ CFSG.pPrimeCore 3 ↥N) ≠ ⊥) :
    (((B.subgroupOf N).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥N)))).Normal := by
  classical
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Pc : Subgroup ↥N := CFSG.pPrimeCore 3 ↥N
  let Ns := ↥N ⧸ Pc
  let π : ↥N →* Ns := QuotientGroup.mk' Pc
  let Bs : Subgroup Ns := (B.subgroupOf N).map π
  have hBQ : B ⊓ relPPrimeCore 3 N = ⊥ :=
    inf_relPPrimeCore_eq_bot_of_card_eq_three c.card_B
  have hBker : B.subgroupOf N ⊓ Pc = ⊥ := subgroupOf_inf_pPrimeCore_eq_bot hBQ
  have hBs_card : Nat.card Bs = 3 :=
    (card_map_mk'_eq_of_disjoint_pPrimeCore hBN hBker).trans c.card_B
  have hBs3 : IsPGroup 3 Bs := IsPGroup.of_card (n := 1) (by rw [hBs_card]; norm_num)
  obtain ⟨Pstar, hBsPstar⟩ := hBs3.exists_le_sylow
  have hPstar_cyc : IsCyclic ↥(Pstar : Subgroup Ns) :=
    CFSG.Quasithin.S146zY.FiveOdd.isCyclic_of_isPGroup_of_surjective_hom
      (f := π) (QuotientGroup.mk'_surjective Pc) (fun S => isCyclic_sylow_three hcyc S)
      Pstar Pstar.isPGroup'
  let K : Subgroup Ns := CFSG.pCore 3 Ns
  have hKle : K ≤ Pstar :=
    IsPGroup.le_sylow_of_normal (p := 3) (N := K) (CFSG.pCore_isPGroup (G := Ns)) Pstar
  have hKcyc : IsCyclic ↥K := Subgroup.isCyclic_of_le hKle
  have hKcard : 3 ≤ Nat.card K := by
    have hgt : 1 < Nat.card K := (Subgroup.one_lt_card_iff_ne_bot K).mpr hKne
    have hdvd : 3 ∣ Nat.card K := by
      rcases (CFSG.pCore_isPGroup (p := 3) (G := Ns)).card_eq_or_dvd with h | h
      · rw [h] at hgt
        omega
      · exact h
    exact Nat.le_of_dvd Nat.card_pos hdvd
  obtain ⟨J, hJcard⟩ := Sylow.exists_subgroup_card_pow_prime_of_le_card
    (p := 3) (n := 1) (G := ↥K) Nat.prime_three (CFSG.pCore_isPGroup (G := Ns))
    (by simpa using hKcard)
  have hJKle : J.map K.subtype ≤ K := Subgroup.map_subtype_le _
  have hJmap_card : Nat.card ↥(J.map K.subtype) = 3 := by
    rw [Subgroup.card_map_of_injective K.subtype_injective, hJcard, pow_one]
  have hBs_eq_J : Bs = J.map K.subtype := by
    have h1 : Bs.subgroupOf Pstar = (J.map K.subtype).subgroupOf Pstar := by
      refine (IsCyclic.subgroup_eq_iff_card_eq).mpr ?_
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBsPstar).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hJKle.trans hKle)).toEquiv,
        hBs_card, hJmap_card]
    have h2 := congrArg (Subgroup.map (Pstar : Subgroup Ns).subtype) h1
    rw [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hBsPstar, inf_eq_left.mpr (hJKle.trans hKle)] at h2
    exact h2
  have hBs_le_K : Bs ≤ K := by
    rw [hBs_eq_J]
    exact Subgroup.map_subtype_le _
  have hBchar : (Bs.subgroupOf K).Characteristic := by
    rw [Subgroup.characteristic_iff_map_eq]
    intro f
    exact (IsCyclic.subgroup_eq_iff_card_eq).mpr (by
      rw [Subgroup.card_map_of_injective f.injective])
  have hmap : (Bs.subgroupOf K).map K.subtype = Bs := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hBs_le_K]
  show Bs.Normal
  rw [← hmap]
  infer_instance

theorem map_conj_le_sup_of_normal {M : Type} [Group M] {Ns : Type} [Group Ns]
    (π : M →* Ns) {B₀ P₀ : Subgroup M} (hcomap : (B₀.map π).comap π = B₀ ⊔ P₀)
    (hnormal : (B₀.map π).Normal) (n : M) :
    B₀.map (MulAut.conj n).toMonoidHom ≤ B₀ ⊔ P₀ := by
  have hcomp : π.comp (MulAut.conj n).toMonoidHom = (MulAut.conj (π n)).toMonoidHom.comp π := by
    ext x
    simp [MulAut.conj_apply]
  have hmap : (B₀.map (MulAut.conj n).toMonoidHom).map π = B₀.map π := by
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map]
    exact Subgroup.Normal.map_conj_eq (H := B₀.map π) (π n)
  have hle : (B₀.map (MulAut.conj n).toMonoidHom).map π ≤ B₀.map π := le_of_eq hmap
  have := (Subgroup.map_le_iff_le_comap).mp hle
  rwa [hcomap] at this

theorem mem_sup_of_mem_pCore_quotient (c : Ctx147 D L n r p A X B R) {N : Subgroup G}
    (hsp3 : IsStronglyPEmbedded 3 D.M) (hBN : B ≤ N)
    (hBs_normal : (((B.subgroupOf N).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥N)))).Normal)
    {n : G} (hn : n ∈ N) : n ∈ relPPrimeCore 3 N ⊔ (N ⊓ D.M) := by
  classical
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Pc : Subgroup ↥N := CFSG.pPrimeCore 3 ↥N
  let Ns := ↥N ⧸ Pc
  let π : ↥N →* Ns := QuotientGroup.mk' Pc
  let Q : Subgroup G := relPPrimeCore 3 N
  let Bs : Subgroup Ns := (B.subgroupOf N).map π
  let n' : ↥N := ⟨n, hn⟩
  have hQN : Q ≤ N :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_le N
  have hPcEq : Pc = Q.subgroupOf N := pPrimeCore_eq_subgroupOf_relPPrimeCore
  have hQcop : Nat.Coprime 3 (Nat.card Q) :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.coprime_card_relPPrimeCore
      Nat.prime_three N
  have hPcCard : Nat.card Pc = Nat.card Q := by
    rw [hPcEq]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQN).toEquiv
  have hPcnot : ¬ 3 ∣ Nat.card Pc := by
    rw [hPcCard]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hQcop
  let : Bs.Normal := hBs_normal
  have hker : π.ker = Pc := QuotientGroup.ker_mk' Pc
  have hcomap : Bs.comap π = B.subgroupOf N ⊔ Pc := by
    rw [show Bs = (B.subgroupOf N).map π from rfl, Subgroup.comap_map_eq, hker]
  have hBconj : ∀ n : ↥N,
      (B.subgroupOf N).map (MulAut.conj n).toMonoidHom ≤ B.subgroupOf N ⊔ Pc :=
    fun n => map_conj_le_sup_of_normal π hcomap hBs_normal n
  have hnormB : normalizer (B : Set G) ≤ D.M :=
    hsp3.normalizer_le ((Subgroup.one_lt_card_iff_ne_bot B).mp (by rw [c.card_B]; norm_num))
      (IsPGroup.of_card (n := 1) (by rw [c.card_B]; norm_num)) c.hB
  have hsub : normalizer (B.subgroupOf N) = (normalizer B).subgroupOf N :=
    (Subgroup.subgroupOf_normalizer_eq hBN).symm
  have hR3 : IsPGroup 3 ((B.subgroupOf N).map (MulAut.conj n').toMonoidHom) :=
    (IsPGroup.comap_subtype (K := N) (p := 3)
      (IsPGroup.of_card (n := 1) (by rw [c.card_B]; norm_num))).map
      (MulAut.conj n').toMonoidHom
  obtain ⟨q, hqPc, hq⟩ :=
    CFSG.GroupTheory.ThreeTranspositions.exists_mem_conj_le_of_isPGroup_of_le_sup
    (p := 3) Nat.prime_three (Y := B.subgroupOf N) (N := Pc)
    (R := (B.subgroupOf N).map (MulAut.conj n').toMonoidHom) hPcnot hR3 (hBconj n')
  have hqmem : (q : G) ∈ Q := by
    rw [hPcEq] at hqPc
    exact Subgroup.mem_subgroupOf.mp hqPc
  have hm_norm : q⁻¹ * n' ∈ normalizer (B.subgroupOf N) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro - ⟨b, hb, rfl⟩
      have hbR : n' * b * n'⁻¹ ∈
          (B.subgroupOf N).map (MulAut.conj n').toMonoidHom :=
        Subgroup.mem_map.mpr ⟨b, hb, rfl⟩
      have := hq _ hbR
      simpa [MulAut.conj_apply, mul_assoc] using this
    · rw [Subgroup.card_map_of_injective (MulAut.conj (q⁻¹ * n')).injective]
  have hmB : ((q⁻¹ * n' : ↥N) : G) ∈ normalizer (B : Set G) := by
    rw [hsub] at hm_norm
    exact Subgroup.mem_subgroupOf.mp hm_norm
  have hmM : ((q⁻¹ * n' : ↥N) : G) ∈ D.M := hnormB hmB
  have hmNM : ((q⁻¹ * n' : ↥N) : G) ∈ N ⊓ D.M :=
    ⟨(q⁻¹ * n').2, hmM⟩
  have hn_eq : n = (q : G) * ((q⁻¹ * n' : ↥N) : G) := by
    have h1 : (q * (q⁻¹ * n') : ↥N) = n' := by group
    have h2 := congrArg Subtype.val h1
    simp [n']
  rw [hn_eq]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hqmem) (Subgroup.mem_sup_right hmNM)

theorem le_sup_of_pCore_quotient_ne_bot (c : Ctx147 D L n r p A X B R)
    (hsp3 : IsStronglyPEmbedded 3 D.M) {N : Subgroup G}
    (hBN : B ≤ N) (hcyc : ∀ P : Subgroup G, P ≤ N → IsPGroup 3 P → IsCyclic P)
    (hKne : CFSG.pCore 3 (↥N ⧸ CFSG.pPrimeCore 3 ↥N) ≠ ⊥) :
    N ≤ CFSG.Open.relPPrimeCore 3 N ⊔ (N ⊓ D.M) := by
  intro n hn
  exact mem_sup_of_mem_pCore_quotient c hsp3 hBN
    (normal_image_of_pCore_quotient_ne_bot c hBN hcyc hKne) hn

theorem le_sup_of_inf_relPPrimeCore_ne_bot (c : Ctx147 D L n r p A X B R)
    {N : Subgroup G} (hN : N ∈ calMOf (B ⊔ R))
    (hRi : ∀ i, R ⊓ L i ∈ uniqueSet D.M)
    (hRQ : R ⊓ CFSG.Open.relPPrimeCore 3 N ≠ ⊥) :
    N ≤ CFSG.Open.relPPrimeCore 3 N ⊔ (N ⊓ D.M) := by
  classical
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  let Q : Subgroup G := CFSG.Open.relPPrimeCore 3 N
  have hQN : Q ≤ N :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_le N
  have hQn : (Q.subgroupOf N).Normal :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_normal
      Nat.prime_three N
  obtain ⟨hEab, hRcard, hLi, hBR, hCB, hframe⟩ := c.frame
  have hBN : B ≤ N := le_sup_left.trans hN.2
  have hBQ : B ≤ normalizer (Q : Set G) :=
    hBN.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hQN).mp hQn)
  have hBinv : B ≤ normalizer ((R ⊓ Q : Subgroup G) : Set G) :=
    (le_inf hBR hBQ).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hcase := hframe (R ⊓ Q) inf_le_left hBinv hRQ
  have hR7 : IsPGroup 7 R := by
    have h := hEab
    rw [← CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian] at h
    exact IsElementaryAbelian.isPGroup 7 R
  let Q' : Subgroup ↥N := Q.subgroupOf N
  let : Q'.Normal := hQn
  have key : ∀ (E : Subgroup G), E ∈ uniqueSet D.M → E ≤ R ⊓ Q →
      N ≤ CFSG.Open.relPPrimeCore 3 N ⊔ (N ⊓ D.M) := by
    intro E hE hERQ
    have hER : E ≤ R := hERQ.trans inf_le_left
    have hEQ : E ≤ Q := hERQ.trans inf_le_right
    have hEN : E ≤ N := hEQ.trans hQN
    have hE7 : IsPGroup 7 E := hR7.to_le hER
    let E' : Subgroup Q' := (E.subgroupOf N).subgroupOf Q'
    have hE'7 : IsPGroup 7 E' :=
      (hE7.comap_subtype (K := N)).comap_subtype (K := Q')
    have hE'N : E.subgroupOf N ≤ Q' := by
      intro x hx
      exact Subgroup.mem_subgroupOf.mpr (hEQ (Subgroup.mem_subgroupOf.mp hx))
    obtain ⟨P, hE'P⟩ := hE'7.exists_le_sylow
    let Y : Subgroup G := (P.map Q'.subtype).map N.subtype
    have hY7 : IsPGroup 7 Y := P.isPGroup'.map Q'.subtype |>.map N.subtype
    have hEY : E ≤ Y := by
      have h1 : E'.map Q'.subtype = E.subgroupOf N := by
        rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hE'N]
      have h2 : (E.subgroupOf N).map N.subtype = E := by
        rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hEN]
      rw [← h2, ← h1]
      exact Subgroup.map_mono (Subgroup.map_mono hE'P)
    obtain ⟨hYM, hYnorm⟩ :=
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.le_and_normalizer_le_of_isPGroup
        (q := 7) D.maxLocal hE hEY hY7
    have hfr : normalizer (P.map Q'.subtype) ⊔ Q' = ⊤ := Sylow.normalizer_sup_eq_top P
    have hfrN : N = (normalizer (P.map Q'.subtype)).map N.subtype ⊔ Q := by
      have h := congrArg (Subgroup.map N.subtype) hfr
      rw [Subgroup.map_sup, Subgroup.map_top, Subgroup.range_subtype,
        Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hQN] at h
      exact h.symm
    have hnorm : (normalizer (P.map Q'.subtype)).map N.subtype ≤ N ⊓ D.M := by
      refine le_inf (Subgroup.map_subtype_le _) ?_
      exact (Subgroup.le_normalizer_map N.subtype).trans hYnorm
    have hle : (normalizer (P.map Q'.subtype)).map N.subtype ⊔ Q ≤
        CFSG.Open.relPPrimeCore 3 N ⊔ (N ⊓ D.M) :=
      sup_le (hnorm.trans le_sup_right) le_sup_left
    calc N = (normalizer (P.map Q'.subtype)).map N.subtype ⊔ Q := hfrN
      _ ≤ CFSG.Open.relPPrimeCore 3 N ⊔ (N ⊓ D.M) := hle
  rcases hcase with hcase | hcase
  · exact key (R ⊓ L 0) (hRi 0) hcase
  · exact key (R ⊓ L 1) (hRi 1) hcase

structure KGen147Hyp (K : Type) [Group K] [Finite K] (B R : Subgroup K) : Prop where
  isKGroup : CFSG.Open.IsKGroup K
  simple : IsSimpleGroup K
  nonab : ∃ a b : K, a * b ≠ b * a
  pRank_eq_one : CFSG.Open.pRank 3 (⊤ : Subgroup K) = 1
  card_B : Nat.card B = 3
  elemAbelian_R : IsElemAbelian 7 R
  card_R : Nat.card R = 49
  norm_B_R : B ≤ normalizer (R : Set K)
  cent_R_B : R ⊓ centralizer (B : Set K) = ⊥

theorem exists_minimalNormal_simple_of_caseC {Ns : Type} [Group Ns] [Finite Ns]
    {Bs Rs : Subgroup Ns} (hBs : Nat.card Bs = 3) (_hRs : Nat.card Rs = 49)
    (hRB : Rs = ⁅Rs, Bs⁆) (hcyc : ∀ S : Subgroup Ns, IsPGroup 3 S → IsCyclic S)
    (_hO3 : CFSG.pCore 3 Ns = ⊥) (hO3' : CFSG.pPrimeCore 3 Ns = ⊥) (hnt : Nontrivial Ns) :
    ∃ K : Subgroup Ns, K.Normal ∧ K ≠ ⊥ ∧
      (∀ M : Subgroup Ns, M.Normal → M ≤ K → M = ⊥ ∨ M = K) ∧
      IsSimpleGroup K ∧ Bs ≤ K ∧ Rs ≤ K := by
  classical
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpRankNs : CFSG.pRank 3 Ns ≤ 1 :=
    CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.pRank_le_one_of_sylow_cyclic
      Nat.prime_three fun S => hcyc S S.isPGroup'
  have hpRankOpen : CFSG.Open.pRank 3 (⊤ : Subgroup Ns) ≤ 1 := by
    rwa [← CFSG.SectionRank.pRank_eq_open_pRank_top]
  have hE9 : ¬ CFSG.GroupTheory.ThreeTranspositions.HasE9 Ns := fun h => by
    have h2 := h.two_le_pRank
    omega
  obtain ⟨K, ⟨hKn, hKne⟩, hKmin⟩ :=
    (Set.toFinite {M : Subgroup Ns | M.Normal ∧ M ≠ ⊥}).exists_minimal
      ⟨⊤, inferInstance, top_ne_bot⟩
  have hmin : ∀ M : Subgroup Ns, M.Normal → M ≤ K → M = ⊥ ∨ M = K := fun M hM hle =>
    (em (M = ⊥)).imp id fun hM1 => le_antisymm hle (hKmin ⟨hM, hM1⟩ hle)
  have h3K : 3 ∣ Nat.card K := by
    by_contra h
    have hcop : Nat.Coprime 3 (Nat.card K) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h
    exact hKne ((CFSG.pPrimeCore_eq_bot_iff (p := 3) (G := Ns)).mp hO3' K hKn hcop)
  obtain ⟨xK, hxord⟩ := exists_prime_orderOf_dvd_card' (G := K) 3 h3K
  have hxord' : orderOf (xK : Ns) = 3 := by rw [Subgroup.orderOf_coe, hxord]
  have hKcl : K = Subgroup.normalClosure ({(xK : Ns)} : Set Ns) := by
    have hle : Subgroup.normalClosure ({(xK : Ns)} : Set Ns) ≤ K := by
      refine Subgroup.normalClosure_le_normal ?_
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact xK.2
    have hN : (Subgroup.normalClosure ({(xK : Ns)} : Set Ns)).Normal :=
      Subgroup.normalClosure_normal
    have hne : Subgroup.normalClosure ({(xK : Ns)} : Set Ns) ≠ ⊥ := by
      intro h
      have : (xK : Ns) ∈ (⊥ : Subgroup Ns) :=
        h ▸ Subgroup.subset_normalClosure (Set.mem_singleton (xK : Ns))
      rw [Subgroup.mem_bot] at this
      rw [this, orderOf_one] at hxord'
      exact absurd hxord' (by norm_num)
    rcases hmin _ hN hle with h | h
    · exact absurd h hne
    · exact h.symm
  have hKsimple : IsSimpleGroup K := by
    have h := CFSG.LocalAnalysis.UniquenessCase.UC22.F09.isSimpleGroup_normalClosure_of_not_hasE9
      (Q := Ns) hE9 hO3' hxord'
    rwa [← hKcl] at h
  have hBs_le_K : Bs ≤ K := by
    obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := Bs) 3 (by rw [hBs])
    have hb' : orderOf (b : Ns) = 3 := by rw [Subgroup.orderOf_coe, hb]
    have hbmem : (b : Ns) ∈ K :=
      @CFSG.GroupTheory.ThreeTranspositions.mem_of_normal_of_three_dvd_card Ns _ _ hE9 K hKn
        h3K b hb'
    have hle : Subgroup.zpowers (b : Ns) ≤ Bs := Subgroup.zpowers_le.mpr b.2
    have heq : Subgroup.zpowers (b : Ns) = Bs := by
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      rw [Nat.card_zpowers, hb', hBs]
    rw [← heq]
    exact Subgroup.zpowers_le.mpr hbmem
  have hRs_le_K : Rs ≤ K := by
    rw [hRB]
    rw [Subgroup.commutator_le]
    intro x _ y hy
    have hyK : y ∈ K := hBs_le_K hy
    have h1 : x * y * x⁻¹ ∈ K := hKn.conj_mem y hyK x
    exact K.mul_mem h1 (K.inv_mem hyK) |> fun h =>
      (by simpa [commutatorElement_def, mul_assoc] using h)
  exact ⟨K, hKn, hKne, hmin, hKsimple, hBs_le_K, hRs_le_K⟩

theorem mem_normalizer_comap_of_mem_normalizer_map {M : Type} [Group M] [Finite M] {Ns : Type}
    [Group Ns]
    (π : M →* Ns) {Bs : Subgroup Ns} {n : M}
    (h : π n ∈ normalizer (Bs : Set Ns)) : n ∈ normalizer (Bs.comap π : Set M) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro - ⟨y, hy, rfl⟩
    rw [Subgroup.mem_comap]
    have h1 : π (n * y * n⁻¹) ∈ Bs := by
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp h (π y)).mp (Subgroup.mem_comap.mp hy)
    simpa [MulAut.conj_apply] using h1
  · rw [Subgroup.card_map_of_injective (MulAut.conj n).injective]

theorem caseC_quotient_facts {N : Subgroup G}
    (hcyc : ∀ P : Subgroup G, P ≤ N → IsPGroup 3 P → IsCyclic P)
    (hNQ : ¬ N ≤ relPPrimeCore 3 N) :
    CFSG.pPrimeCore 3 (↥N ⧸ CFSG.pPrimeCore 3 ↥N) = ⊥ ∧
      (∀ S : Subgroup (↥N ⧸ CFSG.pPrimeCore 3 ↥N), IsPGroup 3 S → IsCyclic S) ∧
      CFSG.Open.pRank 3 (⊤ : Subgroup (↥N ⧸ CFSG.pPrimeCore 3 ↥N)) ≤ 1 ∧
      Nontrivial (↥N ⧸ CFSG.pPrimeCore 3 ↥N) := by
  classical
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Pc : Subgroup ↥N := CFSG.pPrimeCore 3 ↥N
  let Ns := ↥N ⧸ Pc
  let π : ↥N →* Ns := QuotientGroup.mk' Pc
  have hO3' : CFSG.pPrimeCore 3 Ns = ⊥ :=
    CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot (G := ↥N) 3
  have hcycNs : ∀ S : Subgroup Ns, IsPGroup 3 S → IsCyclic S :=
    CFSG.Quasithin.S146zY.FiveOdd.isCyclic_of_isPGroup_of_surjective_hom
      (f := π) (QuotientGroup.mk'_surjective Pc) (fun S => isCyclic_sylow_three hcyc S)
  have hpRankNs : CFSG.pRank 3 Ns ≤ 1 :=
    CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.pRank_le_one_of_sylow_cyclic
      Nat.prime_three fun S => hcycNs S S.isPGroup'
  have hpRankOpen : CFSG.Open.pRank 3 (⊤ : Subgroup Ns) ≤ 1 := by
    rwa [← CFSG.SectionRank.pRank_eq_open_pRank_top]
  have hNsnt : Nontrivial Ns := by
    obtain ⟨n, hn, hnQ⟩ : ∃ n ∈ N, n ∉ relPPrimeCore 3 N := by
      by_contra h
      exact hNQ fun x hx => by
        by_contra hx'
        exact h ⟨x, hx, hx'⟩
    refine ⟨π ⟨n, hn⟩, 1, fun h1 => ?_⟩
    have h2 : (⟨n, hn⟩ : ↥N) ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      exact h1
    rw [QuotientGroup.ker_mk'] at h2
    rw [show Pc = (relPPrimeCore 3 N).subgroupOf N from
      pPrimeCore_eq_subgroupOf_relPPrimeCore] at h2
    exact hnQ (Subgroup.mem_subgroupOf.mp h2)
  exact ⟨hO3', hcycNs, hpRankOpen, hNsnt⟩

structure CaseCImage (N B R : Subgroup G) : Prop where
  card_B : Nat.card ((B.subgroupOf N).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥N))) = 3
  card_R : Nat.card ((R.subgroupOf N).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥N))) = 49
  comm : ((R.subgroupOf N).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥N))) =
    ⁅(R.subgroupOf N).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥N)),
      (B.subgroupOf N).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥N))⁆
  elemAbelian_R : IsElemAbelian 7 ((R.subgroupOf N).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥N)))
  norm_B_R : ((B.subgroupOf N).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥N))) ≤
    normalizer (((R.subgroupOf N).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥N))) :
      Set (↥N ⧸ CFSG.pPrimeCore 3 ↥N))

theorem caseC_image_facts (c : Ctx147 D L n r p A X B R) {N : Subgroup G}
    (hN : N ∈ calMOf (B ⊔ R)) (hRQbot : R ⊓ relPPrimeCore 3 N = ⊥) :
    CaseCImage N B R := by
  classical
  let Pc : Subgroup ↥N := CFSG.pPrimeCore 3 ↥N
  let π : ↥N →* (↥N ⧸ Pc) := QuotientGroup.mk' Pc
  have hPcEq : Pc = (relPPrimeCore 3 N).subgroupOf N := pPrimeCore_eq_subgroupOf_relPPrimeCore
  have hBQ : B ⊓ relPPrimeCore 3 N = ⊥ :=
    inf_relPPrimeCore_eq_bot_of_card_eq_three c.card_B
  have hBdisj : B.subgroupOf N ⊓ Pc = ⊥ := by
    rw [hPcEq]
    have hset : B.subgroupOf N ⊓ (relPPrimeCore 3 N).subgroupOf N =
        (B ⊓ relPPrimeCore 3 N).subgroupOf N := by
      ext x
      simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
    rw [hset, hBQ, Subgroup.bot_subgroupOf]
  have hBcard : Nat.card ((B.subgroupOf N).map π) = 3 := by
    rw [card_map_mk'_eq_of_disjoint_pPrimeCore (le_sup_left.trans hN.2) hBdisj, c.card_B]
  have hRdisj : R.subgroupOf N ⊓ Pc = ⊥ := subgroupOf_inf_pPrimeCore_eq_bot hRQbot
  have hRcard : Nat.card ((R.subgroupOf N).map π) = 49 := by
    rw [card_map_mk'_eq_of_disjoint_pPrimeCore (le_sup_right.trans hN.2) hRdisj, c.frame.2.1]
  have hcomm : ((R.subgroupOf N).map π) = ⁅(R.subgroupOf N).map π, (B.subgroupOf N).map π⁆ := by
    have h1 : (R.subgroupOf N) = (⁅R, B⁆).subgroupOf N := by rw [c.hRB]
    have h2 : (⁅R, B⁆).subgroupOf N = ⁅R.subgroupOf N, B.subgroupOf N⁆ :=
      subgroupOf_commutator (le_sup_right.trans hN.2) (le_sup_left.trans hN.2)
    calc (R.subgroupOf N).map π = ((⁅R, B⁆).subgroupOf N).map π := by rw [h1]
      _ = (⁅R.subgroupOf N, B.subgroupOf N⁆).map π := by rw [h2]
      _ = ⁅(R.subgroupOf N).map π, (B.subgroupOf N).map π⁆ :=
        Subgroup.map_commutator (H₁ := R.subgroupOf N) (H₂ := B.subgroupOf N) π
  have hea : IsElemAbelian 7 ((R.subgroupOf N).map π) := by
    have hR' : IsElemAbelian 7 (R.subgroupOf N) := (Ctx147.frame c).1.subgroupOf N
    exact hR'.map π
  have hnorm : ((B.subgroupOf N).map π) ≤ normalizer ((R.subgroupOf N).map π : Set (↥N ⧸ Pc)) := by
    have hBR' : B.subgroupOf N ≤ normalizer (R.subgroupOf N : Set ↥N) := by
      rw [← Subgroup.subgroupOf_normalizer_eq (le_sup_right.trans hN.2)]
      exact Subgroup.subgroupOf_mono N (Ctx147.frame c).2.2.2.1
    calc (B.subgroupOf N).map π
        ≤ (normalizer (R.subgroupOf N : Set ↥N)).map π := Subgroup.map_mono hBR'
      _ ≤ normalizer ((R.subgroupOf N).map π) := Subgroup.le_normalizer_map π
  exact ⟨hBcard, hRcard, hcomm, hea, hnorm⟩

theorem caseC_inf_centralizer_eq_bot (c : Ctx147 D L n r p A X B R) {N : Subgroup G}
    (hN : N ∈ calMOf (B ⊔ R)) {K : Subgroup (↥N ⧸ CFSG.pPrimeCore 3 ↥N)}
    (hBsK : (B.subgroupOf N).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥N)) ≤ K)
    (hRQbot : R ⊓ relPPrimeCore 3 N = ⊥) :
    ((R.subgroupOf N).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥N))).subgroupOf K ⊓
        centralizer (((B.subgroupOf N).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥N))).subgroupOf K
          : Set ↥K) = ⊥ := by
  classical
  let Pc : Subgroup ↥N := CFSG.pPrimeCore 3 ↥N
  let π : ↥N →* (↥N ⧸ Pc) := QuotientGroup.mk' Pc
  let Bs : Subgroup (↥N ⧸ Pc) := (B.subgroupOf N).map π
  let Rs : Subgroup (↥N ⧸ Pc) := (R.subgroupOf N).map π
  let Bk : Subgroup ↥K := Bs.subgroupOf K
  let Rk : Subgroup ↥K := Rs.subgroupOf K
  have hRdisj : R.subgroupOf N ⊓ Pc = ⊥ := subgroupOf_inf_pPrimeCore_eq_bot hRQbot
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxRk, hxC⟩ := Subgroup.mem_inf.mp hx
  have hxRs : (x : ↥N ⧸ Pc) ∈ Rs := Subgroup.mem_subgroupOf.mp hxRk
  obtain ⟨r', hr', hxr⟩ := Subgroup.mem_map.mp hxRs
  have hx_eq : (x : ↥N ⧸ Pc) = π r' := hxr.symm
  have hcommB : ∀ b ∈ B, (r' : G) * b = b * (r' : G) := by
    intro b hb
    have hbN : b ∈ N := le_sup_left.trans hN.2 hb
    let b' : ↥N := ⟨b, hbN⟩
    have hb'S : b' ∈ B.subgroupOf N := hb
    have hb'Bs : π b' ∈ Bs := Subgroup.mem_map.mpr ⟨b', hb'S, rfl⟩
    let bK : ↥K := ⟨π b', hBsK hb'Bs⟩
    have hb'K : bK ∈ Bk := Subgroup.mem_subgroupOf.mpr hb'Bs
    have hxcent : (x : ↥N ⧸ Pc) * π b' = π b' * (x : ↥N ⧸ Pc) := by
      have h := Subgroup.mem_centralizer_iff.mp hxC bK hb'K
      have h' := congrArg Subtype.val h
      simpa [bK] using h'.symm
    have hcomm' : π ⁅r', b'⁆ = 1 := by
      have h1 : (x : ↥N ⧸ Pc) * π b' = π b' * (x : ↥N ⧸ Pc) := hxcent
      have h2 : π (r' * b' * r'⁻¹ * b'⁻¹) = 1 := by
        simp only [map_mul, map_inv]
        rw [show (π r' : ↥N ⧸ Pc) = (x : ↥N ⧸ Pc) from hx_eq.symm, h1]
        group
      simpa [commutatorElement_def, mul_assoc] using h2
    have hker : ⁅r', b'⁆ ∈ Pc := by
      rw [← QuotientGroup.ker_mk' Pc]
      exact MonoidHom.mem_ker.mpr hcomm'
    have hR' : ⁅r', b'⁆ ∈ R.subgroupOf N := by
      have h2 : (r' : G) ∈ R := Subgroup.mem_subgroupOf.mp hr'
      have h4 : b * (r' : G)⁻¹ * b⁻¹ ∈ R :=
        (Subgroup.mem_normalizer_iff.mp ((Ctx147.frame c).2.2.2.1 hb)) (r' : G)⁻¹ |>.mp
          (R.inv_mem h2)
      have h3 : ⁅(r' : G), b⁆ ∈ R := by
        have h5 : (r' : G) * (b * (r' : G)⁻¹ * b⁻¹) ∈ R := R.mul_mem h2 h4
        simpa [commutatorElement_def, mul_assoc] using h5
      rw [Subgroup.mem_subgroupOf]
      have hcoe : ((⁅r', b'⁆ : ↥N) : G) = ⁅(r' : G), (b' : G)⁆ :=
        map_commutatorElement (f := N.subtype) r' b'
      rw [hcoe]
      simpa using h3
    have hbot : ⁅r', b'⁆ ∈ (⊥ : Subgroup ↥N) := by
      rw [← hRdisj]
      exact ⟨hR', hker⟩
    have h1 : ⁅r', b'⁆ = 1 := by simpa using hbot
    have h2 : (r' : G) * b * (r' : G)⁻¹ = b := by
      have hval := congrArg Subtype.val h1
      have hval' : (r' : G) * (b' : G) * (r' : G)⁻¹ * (b' : G)⁻¹ = 1 := by
        simpa [commutatorElement_def, mul_assoc] using hval
      have h3 := congrArg (fun z => z * (b' : G)) hval'
      simpa [mul_assoc] using h3
    have h3 := congrArg (fun z => z * (r' : G)) h2
    simpa [mul_assoc] using h3
  have hcentR : (r' : G) ∈ R ⊓ centralizer (B : Set G) := by
    refine ⟨Subgroup.mem_subgroupOf.mp hr', ?_⟩
    exact fun b hb => (hcommB b hb).symm
  rw [(Ctx147.frame c).2.2.2.2.1] at hcentR
  have hr1 : (r' : G) = 1 := by simpa using hcentR
  have hx1 : x = 1 := by
    apply Subtype.ext
    rw [hx_eq]
    rw [show r' = 1 from Subtype.ext hr1, map_one]
    rfl
  simp [hx1]

theorem caseC_kGen147Hyp {D : Data G} {N : Subgroup G}
    (hN : N ∈ calMOf (B ⊔ R)) {K : Subgroup (↥N ⧸ CFSG.pPrimeCore 3 ↥N)}
    (hKn : K.Normal) (hKne : K ≠ ⊥) (hKsimple : IsSimpleGroup K)
    (himg : CaseCImage N B R)
    (hBsK : (B.subgroupOf N).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥N)) ≤ K)
    (hRsK : (R.subgroupOf N).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥N)) ≤ K)
    (hcent : ((R.subgroupOf N).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥N))).subgroupOf K ⊓
        centralizer (((B.subgroupOf N).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥N))).subgroupOf K
          : Set ↥K) = ⊥)
    (hO3 : CFSG.pCore 3 (↥N ⧸ CFSG.pPrimeCore 3 ↥N) = ⊥)
    (hO3' : CFSG.pPrimeCore 3 (↥N ⧸ CFSG.pPrimeCore 3 ↥N) = ⊥)
    (hpRank : CFSG.Open.pRank 3 (⊤ : Subgroup (↥N ⧸ CFSG.pPrimeCore 3 ↥N)) ≤ 1) :
    KGen147Hyp ↥K
      (((B.subgroupOf N).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥N))).subgroupOf K)
      (((R.subgroupOf N).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥N))).subgroupOf K) := by
  classical
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Pc : Subgroup ↥N := CFSG.pPrimeCore 3 ↥N
  let Ns := ↥N ⧸ Pc
  let Bs : Subgroup Ns := (B.subgroupOf N).map (QuotientGroup.mk' Pc)
  let Rs : Subgroup Ns := (R.subgroupOf N).map (QuotientGroup.mk' Pc)
  let Bk : Subgroup ↥K := Bs.subgroupOf K
  let Rk : Subgroup ↥K := Rs.subgroupOf K
  have hBk_card : Nat.card Bk = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBsK).toEquiv]
    exact himg.card_B
  have hRk_card : Nat.card Rk = 49 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRsK).toEquiv]
    exact himg.card_R
  have hRk_ea : IsElemAbelian 7 Rk := himg.elemAbelian_R.subgroupOf K
  have hBk_norm : Bk ≤ normalizer (Rk : Set ↥K) := by
    have h' : (normalizer (Rs : Set Ns)).subgroupOf K = normalizer (Rk : Set ↥K) :=
      Subgroup.subgroupOf_normalizer_eq hRsK
    have hle : Bk ≤ (normalizer (Rs : Set Ns)).subgroupOf K :=
      Subgroup.subgroupOf_mono K himg.norm_B_R
    rwa [h'] at hle
  let : IsSimpleGroup G := D.standing.simple
  have hNne : N ≠ ⊤ :=
    CFSG.RankThreeCoreUniqueness.Helpers.twoLocal_ne_top D.standing.nonab N hN.1.1
  have hKGK : CFSG.Open.IsKGroup ↥K :=
    (D.standing.kProper.isKGroup N hNne).quotient Pc |>.subgroup K
  have hKnc : ∃ a b : K, a * b ≠ b * a := by
    by_contra h
    push Not at h
    let : IsMulCommutative K := ⟨⟨fun a b => h a b⟩⟩
    have hprime : (Nat.card K).Prime := Group.is_simple_iff_prime_card.mp hKsimple
    have hKp : IsPGroup (Nat.card K) K := IsPGroup.of_card (n := 1) (by rw [pow_one])
    by_cases hq3 : Nat.card K = 3
    · have hKp3 : IsPGroup 3 K := by
        rwa [hq3] at hKp
      have hle : K ≤ CFSG.pCore 3 Ns := le_sSup ⟨hKn, hKp3⟩
      rw [hO3] at hle
      exact hKne (le_bot_iff.mp hle)
    · have hcop : Nat.Coprime 3 (Nat.card K) :=
        (Nat.coprime_primes Nat.prime_three hprime).mpr (Ne.symm hq3)
      exact hKne ((CFSG.pPrimeCore_eq_bot_iff (p := 3) (G := Ns)).mp hO3' K hKn hcop)
  refine ⟨hKGK, hKsimple, hKnc, ?_, hBk_card, hRk_ea, hRk_card, hBk_norm, hcent⟩
  refine le_antisymm ?_ ?_
  · rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (H := K)]
    exact (CFSG.SectionRank.pRank_mono (p := 3) (by norm_num)
      (le_top : K ≤ ⊤)).trans hpRank
  · have hBk_ea : IsElemAbelian 3 Bk :=
      CFSG.GroupTheory.isElemAbelian_of_card_prime (r := 3) hBk_card
    exact CFSG.SectionRank.le_pRank (G := ↥K) (p := 3) (by norm_num)
      (H := (⊤ : Subgroup ↥K)) (E := Bk) le_top hBk_ea
      (show Nat.card Bk = 3 ^ 1 by rw [hBk_card]; norm_num)

theorem caseC_mem_sup_of_mem_normalizer_sup (c : Ctx147 D L n r p A X B R) {N : Subgroup G}
    (hN : N ∈ calMOf (B ⊔ R)) (hsp3 : IsStronglyPEmbedded 3 D.M) {n : G}
    (hnN : n ∈ N)
    (hnorm : n ∈ normalizer (((relPPrimeCore 3 N) ⊔ B : Subgroup G) : Set G)) :
    n ∈ relPPrimeCore 3 N ⊔ (N ⊓ D.M) := by
  classical
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Q : Subgroup G := relPPrimeCore 3 N
  have hBN : B ≤ N := le_sup_left.trans hN.2
  have hQN : Q ≤ N :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_le N
  have hQn : (Q.subgroupOf N).Normal :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_normal
      Nat.prime_three N
  have hBQ : B ⊓ Q = ⊥ := inf_relPPrimeCore_eq_bot_of_card_eq_three c.card_B
  have hBQnorm : B ≤ normalizer (Q : Set G) :=
    hBN.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hQN).mp hQn)
  have hBQdisj : Disjoint Q B := by rw [disjoint_iff, inf_comm, hBQ]
  have hcardQB : Nat.card ↥(Q ⊔ B) = Nat.card Q * 3 := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer Q B hBQnorm hBQdisj,
      c.card_B]
  have hB3 : IsPGroup 3 B := IsPGroup.of_card (n := 1) (by rw [c.card_B]; norm_num)
  have hQcop : Nat.Coprime 3 (Nat.card Q) :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.coprime_card_relPPrimeCore
      Nat.prime_three N
  have hQcop' : ¬ 3 ∣ Nat.card Q :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hQcop
  have hYsyl : CFSG.ABGLocalTools.IsSylowOf 3 B (Q ⊔ B) := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨le_sup_right, hB3, ?_⟩
    have hmul := Subgroup.relIndex_mul_card (H := B) (K := Q ⊔ B)
    rw [inf_eq_left.mpr le_sup_right, hcardQB, c.card_B] at hmul
    have hrel : B.relIndex (Q ⊔ B) = Nat.card Q :=
      Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 3) hmul
    rw [hrel]
    exact hQcop'
  have hnormB : normalizer (B : Set G) ≤ D.M :=
    hsp3.normalizer_le ((Subgroup.one_lt_card_iff_ne_bot B).mp (by rw [c.card_B]; norm_num))
      hB3 c.hB
  exact mem_sup_of_mem_normalizer_of_isSylowOf (D := D) (Q := Q) (P := Q ⊔ B) (Y := B)
    (N := N) (p := 3) hnormB (sup_le hQN hBN) hQN hQn le_rfl hYsyl hnN hnorm

theorem caseC_normalizer_subgroupOf (c : Ctx147 D L n r p A X B R) {N : Subgroup G}
    (hN : N ∈ calMOf (B ⊔ R)) (hsp3 : IsStronglyPEmbedded 3 D.M)
    {K : Subgroup (↥N ⧸ CFSG.pPrimeCore 3 ↥N)}
    (hBsK : (B.subgroupOf N).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥N)) ≤ K) :
    normalizer ((((B.subgroupOf N).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥N))).subgroupOf K)
        : Set ↥K) ≤
      (((N ⊓ D.M).subgroupOf N).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥N))).subgroupOf K := by
  classical
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Pc : Subgroup ↥N := CFSG.pPrimeCore 3 ↥N
  let Ns := ↥N ⧸ Pc
  let π : ↥N →* Ns := QuotientGroup.mk' Pc
  let Q : Subgroup G := relPPrimeCore 3 N
  let Bs : Subgroup Ns := (B.subgroupOf N).map π
  let Hs : Subgroup Ns := ((N ⊓ D.M).subgroupOf N).map π
  let Bk : Subgroup ↥K := Bs.subgroupOf K
  have hQN : Q ≤ N :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_le N
  have hQn : (Q.subgroupOf N).Normal :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_normal
      Nat.prime_three N
  have hPcEq : Pc = Q.subgroupOf N := pPrimeCore_eq_subgroupOf_relPPrimeCore
  have hQmap : (Q.subgroupOf N).map π = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, show π.ker = Pc from QuotientGroup.ker_mk' Pc, ← hPcEq]
  have hBN : B ≤ N := le_sup_left.trans hN.2
  have hmapBs : ((Q ⊔ B).subgroupOf N).map π = Bs := by
    rw [Subgroup.subgroupOf_sup hQN hBN, Subgroup.map_sup, hQmap, bot_sup_eq]
  have hpre_eq : Bs.comap π = (Q ⊔ B).subgroupOf N := by
    rw [← hmapBs, Subgroup.comap_map_eq, show π.ker = Pc from QuotientGroup.ker_mk' Pc]
    refine sup_eq_left.mpr ?_
    rw [hPcEq, Subgroup.subgroupOf_sup hQN hBN]
    exact le_sup_left
  intro xk hxk
  obtain ⟨n, hn_eq⟩ := QuotientGroup.mk'_surjective Pc (xk : Ns)
  have hxk_bs : ∀ y ∈ Bs, (xk : Ns) * y * (xk : Ns)⁻¹ ∈ Bs := by
    intro y hy
    have hyK : y ∈ K := hBsK hy
    have hyBk : (⟨y, hyK⟩ : ↥K) ∈ Bk := Subgroup.mem_subgroupOf.mpr hy
    have hconj := (Subgroup.mem_normalizer_iff.mp hxk (⟨y, hyK⟩ : ↥K)).mp hyBk
    have hval : ((xk * ⟨y, hyK⟩ * xk⁻¹ : ↥K) : Ns) = (xk : Ns) * y * (xk : Ns)⁻¹ := rfl
    rw [← hval]
    exact Subgroup.mem_subgroupOf.mp hconj
  have hxk_norm : (xk : Ns) ∈ normalizer (Bs : Set Ns) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro - ⟨y, hy, rfl⟩
      simpa [MulAut.conj_apply] using hxk_bs y hy
    · have hc := Subgroup.card_map_of_injective (K := Bs)
        (f := (MulAut.conj (xk : Ns)).toMonoidHom) (MulAut.conj (xk : Ns)).injective
      exact hc.ge
  have hnorm_pre : n ∈ normalizer ((Q ⊔ B).subgroupOf N : Set ↥N) := by
    rw [← hpre_eq]
    exact mem_normalizer_comap_of_mem_normalizer_map π (by rw [hn_eq]; exact hxk_norm)
  have hnormP : (n : G) ∈ normalizer ((Q ⊔ B : Subgroup G) : Set G) :=
    CFSG.RankThree.GroupTheory.mem_normalizer_of_mem_normalizer_subgroupOf
      (sup_le hQN hBN) hnorm_pre
  have hn_mem : (n : G) ∈ Q ⊔ (N ⊓ D.M) :=
    caseC_mem_sup_of_mem_normalizer_sup c hN hsp3 n.2 hnormP
  have hmapH : ((Q ⊔ (N ⊓ D.M)).subgroupOf N).map π = Hs := by
    rw [Subgroup.subgroupOf_sup hQN inf_le_left, Subgroup.map_sup, hQmap, bot_sup_eq]
  have hxHs : (xk : Ns) ∈ Hs := by
    rw [← hn_eq]
    have h := Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hn_mem)
    rwa [hmapH] at h
  exact Subgroup.mem_subgroupOf.mpr hxHs

theorem isPGroup_quotient_comap_of_surjective {M : Type} [Group M] [Finite M] {Ns : Type}
    [Group Ns] (π : M →* Ns) (hπ : Function.Surjective π) (K₀ : Subgroup M) [K₀.Normal]
    (hK₀ : π.ker = K₀) {p : ℕ} {Ys : Subgroup Ns} (hYs : IsPGroup p Ys) :
    IsPGroup p (↥(Ys.comap π) ⧸ K₀.subgroupOf (Ys.comap π)) := by
  let Yp : Subgroup M := Ys.comap π
  let φ : ↥Yp →* ↥Ys := (π.comp Yp.subtype).codRestrict Ys fun y => Subgroup.mem_comap.mp y.2
  have hφsurj : Function.Surjective φ := by
    intro y
    obtain ⟨z, hz⟩ := hπ (y : Ns)
    refine ⟨⟨z, ?_⟩, Subtype.ext hz⟩
    rw [Subgroup.mem_comap, hz]
    exact y.2
  have hker : φ.ker = K₀.subgroupOf Yp := by
    ext z
    constructor
    · intro hz
      have h1 : (φ z : Ns) = 1 := by
        have hz' := MonoidHom.mem_ker.mp hz
        simpa using congrArg Subtype.val hz'
      rw [Subgroup.mem_subgroupOf, ← hK₀]
      exact MonoidHom.mem_ker.mp h1
    · intro hz
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      have h1 : (z : M) ∈ π.ker := by
        rw [hK₀]
        exact Subgroup.mem_subgroupOf.mp hz
      show π (z : M) = 1
      exact MonoidHom.mem_ker.mp h1
  let e : (↥Yp ⧸ K₀.subgroupOf Yp) ≃* ↥Ys :=
    (QuotientGroup.quotientMulEquivOfEq hker).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective (φ := φ) hφsurj)
  exact hYs.of_surjective e.symm.toMonoidHom e.symm.surjective

theorem exists_seven_sylow_of_le_comap (c : Ctx147 D L n r p A X B R) {N : Subgroup G}
    (hN : N ∈ calMOf (B ⊔ R)) (hRi : ∀ i, R ⊓ L i ∈ uniqueSet D.M)
    {Ys : Subgroup (↥N ⧸ CFSG.pPrimeCore 3 ↥N)}
    (hRs : ((R.subgroupOf N).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥N))) ≤ Ys)
    (hYs7 : IsPGroup 7 Ys) :
    ∃ A : Subgroup ↥N,
      CFSG.ABGLocalTools.IsSylowOf 7 A (Ys.comap (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥N))) ∧
      R.subgroupOf N ≤ A ∧
      ((Ys.comap (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥N))).map N.subtype) ≤
        relPPrimeCore 3 N ⊔ A.map N.subtype ∧
      normalizer (((A.map N.subtype : Subgroup G)) : Set G) ≤ D.M := by
  classical
  let : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  let Pc : Subgroup ↥N := CFSG.pPrimeCore 3 ↥N
  let π : ↥N →* (↥N ⧸ Pc) := QuotientGroup.mk' Pc
  let Q : Subgroup G := relPPrimeCore 3 N
  let Yp : Subgroup ↥N := Ys.comap π
  have hQN : Q ≤ N :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_le N
  have hR7 : IsPGroup 7 R := by
    have h := (Ctx147.frame c).1
    rw [← CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian] at h
    exact IsElementaryAbelian.isPGroup 7 R
  have hPcYp : Pc ≤ Yp := by
    intro x hx
    rw [Subgroup.mem_comap]
    have h1 : π x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    exact h1.symm ▸ Ys.one_mem
  have hR'Yp : R.subgroupOf N ≤ Yp := by
    intro y hy
    rw [Subgroup.mem_comap]
    exact hRs (Subgroup.mem_map.mpr ⟨y, hy, rfl⟩)
  have hR'7 : IsPGroup 7 (R.subgroupOf N) := hR7.comap_subtype (K := N)
  obtain ⟨S, hR'S⟩ := (hR'7.comap_subtype (K := Yp)).exists_le_sylow
  let A : Subgroup ↥N := (S : Subgroup ↥Yp).map Yp.subtype
  have hAsyl : CFSG.ABGLocalTools.IsSylowOf 7 A Yp := ⟨S, rfl⟩
  have hR'A : R.subgroupOf N ≤ A := by
    intro y hy
    have hy' : (⟨y, hR'Yp hy⟩ : ↥Yp) ∈ (R.subgroupOf N).subgroupOf Yp :=
      Subgroup.mem_subgroupOf.mpr hy
    exact Subgroup.mem_map.mpr ⟨⟨y, hR'Yp hy⟩, hR'S hy', rfl⟩
  have hquot : IsPGroup 7 (↥Yp ⧸ Pc.subgroupOf Yp) :=
    isPGroup_quotient_comap_of_surjective π (QuotientGroup.mk'_surjective Pc) Pc
      (QuotientGroup.ker_mk' Pc) hYs7
  have hSylTop : CFSG.ABGLocalTools.IsSylowOf 7 (S : Subgroup ↥Yp) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    exact ⟨le_top, S.isPGroup', by simpa using S.not_dvd_index⟩
  have hYp_le : Yp ≤ Pc ⊔ A :=
    CFSG.GroupTheory.le_sup_of_isPGroup_quotient_of_isSylowOf (p := 7) (C := Pc)
      (S := A) (Y := Yp) hPcYp hAsyl hquot
  have hPcEq : Pc = Q.subgroupOf N := pPrimeCore_eq_subgroupOf_relPPrimeCore
  have hPc_map : Pc.map N.subtype = Q := by
    rw [hPcEq, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hQN]
  have hP_eq : Yp.map N.subtype ≤ Q ⊔ A.map N.subtype := by
    refine (Subgroup.map_mono hYp_le).trans ?_
    rw [Subgroup.map_sup, hPc_map]
  have hY7 : IsPGroup 7 (A.map N.subtype) := hAsyl.isPGroup.map N.subtype
  have hEY : R ⊓ L 0 ≤ A.map N.subtype := by
    have h := Subgroup.map_mono (f := N.subtype) hR'A
    rw [Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr (le_sup_right.trans hN.2)] at h
    exact inf_le_left.trans h
  obtain ⟨-, hYnorm⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.le_and_normalizer_le_of_isPGroup
      (q := 7) D.maxLocal (hRi 0) hEY hY7
  exact ⟨A, hAsyl, hR'A, hP_eq, hYnorm⟩

theorem caseC_mem_sup_of_normalizer_seven {N : Subgroup G}
    {Ys : Subgroup (↥N ⧸ CFSG.pPrimeCore 3 ↥N)} {A : Subgroup ↥N}
    (hA : CFSG.ABGLocalTools.IsSylowOf 7 A
      (Ys.comap (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥N))))
    (hYnorm : normalizer (((A.map N.subtype : Subgroup G)) : Set G) ≤ D.M)
    (hYle : ((Ys.comap (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥N))).map N.subtype) ≤
      relPPrimeCore 3 N ⊔ A.map N.subtype)
    {n : G} (hnN : n ∈ N)
    (hnP : n ∈ normalizer ((((Ys.comap (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥N))).map N.subtype
      : Subgroup G)) : Set G)) :
    n ∈ relPPrimeCore 3 N ⊔ (N ⊓ D.M) := by
  classical
  let : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  let Q : Subgroup G := relPPrimeCore 3 N
  have hQN : Q ≤ N :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_le N
  have hQn : (Q.subgroupOf N).Normal :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_normal
      Nat.prime_three N
  exact mem_sup_of_mem_normalizer_of_isSylowOf (D := D) (Q := Q)
    (P := (Ys.comap (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥N))).map N.subtype)
    (Y := A.map N.subtype) (N := N) (p := 7) hYnorm (Subgroup.map_subtype_le _) hQN hQn hYle
    ((CFSG.ABGLocalTools.isSylowOf_map_subtype_iff _).mpr hA) hnN hnP

theorem caseC_normalizer_seven (c : Ctx147 D L n r p A X B R) {N : Subgroup G}
    (hN : N ∈ calMOf (B ⊔ R)) (hRi : ∀ i, R ⊓ L i ∈ uniqueSet D.M) :
    ∀ Ys : Subgroup (↥N ⧸ CFSG.pPrimeCore 3 ↥N),
      ((R.subgroupOf N).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥N))) ≤ Ys →
      IsPGroup 7 Ys →
      normalizer (Ys : Set (↥N ⧸ CFSG.pPrimeCore 3 ↥N)) ≤
        (((N ⊓ D.M).subgroupOf N).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥N))) := by
  classical
  let : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  let Pc : Subgroup ↥N := CFSG.pPrimeCore 3 ↥N
  let π : ↥N →* (↥N ⧸ Pc) := QuotientGroup.mk' Pc
  let Q : Subgroup G := relPPrimeCore 3 N
  let Hs : Subgroup (↥N ⧸ Pc) := ((N ⊓ D.M).subgroupOf N).map π
  have hQN : Q ≤ N :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_le N
  have hPcEq : Pc = Q.subgroupOf N := pPrimeCore_eq_subgroupOf_relPPrimeCore
  have hQmap : (Q.subgroupOf N).map π = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, show π.ker = Pc from QuotientGroup.ker_mk' Pc, ← hPcEq]
  have hmapH : ((Q ⊔ (N ⊓ D.M)).subgroupOf N).map π = Hs := by
    rw [Subgroup.subgroupOf_sup hQN inf_le_left, Subgroup.map_sup, hQmap, bot_sup_eq]
  intro Ys hRs hYs7 xk hxk
  obtain ⟨n, hn_eq⟩ := QuotientGroup.mk'_surjective Pc (xk : ↥N ⧸ Pc)
  obtain ⟨A, hA, hRA, hYle, hYnorm⟩ := exists_seven_sylow_of_le_comap c hN hRi hRs hYs7
  have hconv : ((Ys.comap π).map N.subtype).subgroupOf N = Ys.comap π :=
    Subgroup.comap_map_eq_self_of_injective N.subtype_injective _
  have hnorm_pre : n ∈ normalizer (Ys.comap π : Set ↥N) :=
    mem_normalizer_comap_of_mem_normalizer_map π (by rw [hn_eq]; exact hxk)
  have hnormP : (n : G) ∈
      normalizer (((Ys.comap π).map N.subtype : Subgroup G) : Set G) :=
    CFSG.RankThree.GroupTheory.mem_normalizer_of_mem_normalizer_subgroupOf
      (Subgroup.map_subtype_le _) (by rw [hconv]; exact hnorm_pre)
  have hn_mem : (n : G) ∈ Q ⊔ (N ⊓ D.M) :=
    caseC_mem_sup_of_normalizer_seven hA hYnorm hYle n.2 hnormP
  have hxHs : (xk : ↥N ⧸ Pc) ∈ Hs := by
    rw [← hn_eq]
    have h := Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hn_mem)
    rwa [hmapH] at h
  exact hxHs

theorem caseC_normalizerYk (c : Ctx147 D L n r p A X B R) {N : Subgroup G}
    (hN : N ∈ calMOf (B ⊔ R)) (hRi : ∀ i, R ⊓ L i ∈ uniqueSet D.M)
    {K : Subgroup (↥N ⧸ CFSG.pPrimeCore 3 ↥N)}
    (hRsK : (R.subgroupOf N).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥N)) ≤ K) :
    ∀ Yk : Subgroup ↥K,
      (((R.subgroupOf N).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥N))).subgroupOf K) ≤ Yk →
      IsPGroup 7 Yk →
      normalizer (Yk : Set ↥K) ≤
        (((N ⊓ D.M).subgroupOf N).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥N))).subgroupOf K := by
  classical
  let : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  let Pc : Subgroup ↥N := CFSG.pPrimeCore 3 ↥N
  let π : ↥N →* (↥N ⧸ Pc) := QuotientGroup.mk' Pc
  let Rs : Subgroup (↥N ⧸ Pc) := (R.subgroupOf N).map π
  let Rk : Subgroup ↥K := Rs.subgroupOf K
  intro Yk hRkY hYk7
  let Ys : Subgroup (↥N ⧸ Pc) := Yk.map K.subtype
  have hRs_eq : Rs = Rk.map K.subtype := by
    rw [show Rk = Rs.subgroupOf K from rfl, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hRsK]
  have hRsYs : Rs ≤ Ys := by
    rw [hRs_eq]
    exact Subgroup.map_mono hRkY
  have hYs7 : IsPGroup 7 Ys := hYk7.map K.subtype
  intro xk hxk
  have hxk_norm : (xk : ↥N ⧸ Pc) ∈ normalizer (Ys : Set (↥N ⧸ Pc)) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro - ⟨y, hy, rfl⟩
      obtain ⟨yk, hyk, rfl⟩ := Subgroup.mem_map.mp hy
      have hconj : xk * yk * xk⁻¹ ∈ Yk :=
        (Subgroup.mem_normalizer_iff.mp hxk yk).mp hyk
      exact Subgroup.mem_map.mpr ⟨_, hconj, rfl⟩
    · have hc := Subgroup.card_map_of_injective (K := Ys)
        (f := (MulAut.conj (xk : ↥N ⧸ Pc)).toMonoidHom)
        (MulAut.conj (xk : ↥N ⧸ Pc)).injective
      exact hc.ge
  exact Subgroup.mem_subgroupOf.mpr
    (caseC_normalizer_seven c hN hRi Ys hRsYs hYs7 hxk_norm)

theorem caseC_le_sup {N : Subgroup G}
    (hKG : KGen147)
    {K : Subgroup (↥N ⧸ CFSG.pPrimeCore 3 ↥N)} (hKn : K.Normal)
    (hRsK : (R.subgroupOf N).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥N)) ≤ K)
    (hcl : KGen147Hyp ↥K
      (((B.subgroupOf N).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥N))).subgroupOf K)
      (((R.subgroupOf N).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥N))).subgroupOf K))
    (hnormBk : normalizer
        ((((B.subgroupOf N).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥N))).subgroupOf K
          : Subgroup ↥K) : Set ↥K) ≤
      (((N ⊓ D.M).subgroupOf N).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥N))).subgroupOf K)
    (hnormYk : ∀ Yk : Subgroup ↥K,
      (((R.subgroupOf N).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥N))).subgroupOf K) ≤ Yk →
      IsPGroup 7 Yk →
      normalizer (Yk : Set ↥K) ≤
        (((N ⊓ D.M).subgroupOf N).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥N))).subgroupOf K)
    (hnormYs : ∀ Ys : Subgroup (↥N ⧸ CFSG.pPrimeCore 3 ↥N),
      ((R.subgroupOf N).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥N))) ≤ Ys →
      IsPGroup 7 Ys →
      normalizer (Ys : Set (↥N ⧸ CFSG.pPrimeCore 3 ↥N)) ≤
        (((N ⊓ D.M).subgroupOf N).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥N)))) :
    N ≤ relPPrimeCore 3 N ⊔ (N ⊓ D.M) := by
  classical
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Pc : Subgroup ↥N := CFSG.pPrimeCore 3 ↥N
  let π : ↥N →* (↥N ⧸ Pc) := QuotientGroup.mk' Pc
  let Q : Subgroup G := relPPrimeCore 3 N
  let Rs : Subgroup (↥N ⧸ Pc) := (R.subgroupOf N).map π
  let Hs : Subgroup (↥N ⧸ Pc) := ((N ⊓ D.M).subgroupOf N).map π
  let Bk : Subgroup ↥K := ((B.subgroupOf N).map π).subgroupOf K
  let Rk : Subgroup ↥K := Rs.subgroupOf K
  let H : Subgroup ↥K := Hs.subgroupOf K
  let : K.Normal := hKn
  have hH_top : H = ⊤ :=
    hKG ↥K hcl.isKGroup hcl.simple hcl.nonab hcl.pRank_eq_one Bk Rk hcl.card_B
      hcl.elemAbelian_R hcl.card_R hcl.norm_B_R hcl.cent_R_B H hnormBk hnormYk
  have hKleHs : K ≤ Hs := by
    intro x hx
    have hxH : (⟨x, hx⟩ : ↥K) ∈ H := by rw [hH_top]; trivial
    exact Subgroup.mem_subgroupOf.mp hxH
  have hRk7 : IsPGroup 7 Rk := by
    have h := hcl.elemAbelian_R
    rw [← CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian] at h
    exact IsElementaryAbelian.isPGroup 7 Rk
  obtain ⟨S, hRkS⟩ := hRk7.exists_le_sylow
  let Ys : Subgroup (↥N ⧸ Pc) := (S : Subgroup ↥K).map K.subtype
  have hRsYs : Rs ≤ Ys := by
    have hRs_eq : Rs = Rk.map K.subtype := by
      rw [show Rk = Rs.subgroupOf K from rfl, Subgroup.subgroupOf_map_subtype,
        inf_eq_left.mpr hRsK]
    rw [hRs_eq]
    exact Subgroup.map_mono hRkS
  have hYs7 : IsPGroup 7 Ys := S.isPGroup'.map K.subtype
  have hsup_top : normalizer (Ys : Set (↥N ⧸ Pc)) ⊔ K = ⊤ := by
    have h := Sylow.normalizer_sup_eq_top S
    rwa [show (S : Subgroup ↥K).map K.subtype = Ys from rfl] at h
  have hHs_top : Hs = ⊤ := by
    refine top_le_iff.mp ?_
    rw [← hsup_top]
    exact sup_le (hnormYs Ys hRsYs hYs7) hKleHs
  intro n hn
  have hπ : π ⟨n, hn⟩ ∈ Hs := by rw [hHs_top]; trivial
  obtain ⟨m', hm', hπm⟩ := Subgroup.mem_map.mp hπ
  have hmN : (m' : G) ∈ N := (Subgroup.mem_subgroupOf.mp hm').1
  have hmM : (m' : G) ∈ D.M := (Subgroup.mem_subgroupOf.mp hm').2
  have hPcEq : Pc = Q.subgroupOf N := pPrimeCore_eq_subgroupOf_relPPrimeCore
  have hker : π (⟨n, hn⟩ * m'⁻¹) = 1 := by
    rw [map_mul, map_inv, hπm, mul_inv_cancel]
  have hmemQ' : ⟨n, hn⟩ * m'⁻¹ ∈ Q.subgroupOf N := by
    rw [← hPcEq]
    exact (QuotientGroup.eq_one_iff _).mp hker
  have hmemQ : ((⟨n, hn⟩ * m'⁻¹ : ↥N) : G) ∈ Q := Subgroup.mem_subgroupOf.mp hmemQ'
  have hn_eq : (n : G) = ((⟨n, hn⟩ * m'⁻¹ : ↥N) : G) * (m' : G) := by
    have h : (⟨n, hn⟩ : ↥N) = (⟨n, hn⟩ * m'⁻¹) * m' := by group
    exact congrArg Subtype.val h
  rw [hn_eq]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hmemQ) (Subgroup.mem_sup_right ⟨hmN, hmM⟩)

theorem le_relPPrimeCore_sup (c : Ctx147 D L n r p A X B R)
    (hsp3 : IsStronglyPEmbedded 3 D.M)
    (hU4b : ∀ H : Subgroup G, IsTwoLocal H → 2 ≤ CFSG.Open.pRank 3 (H ⊓ D.M) → H ≤ D.M)
    (hRi : ∀ i, R ⊓ L i ∈ uniqueSet D.M) (hKG : KGen147) {N : Subgroup G}
    (hN : N ∈ calMOf (B ⊔ R)) : N ≤ relPPrimeCore 3 N ⊔ (N ⊓ D.M) := by
  by_cases hNM : N ≤ D.M
  · exact le_sup_of_le_right (le_inf le_rfl hNM)
  have hcyc : ∀ P : Subgroup G, P ≤ N → IsPGroup 3 P → IsCyclic P :=
    c.isCyclic_of_mem_calMOf hsp3 hU4b hN hNM
  by_cases hK : CFSG.pCore 3 (↥N ⧸ CFSG.pPrimeCore 3 ↥N) ≠ ⊥
  · exact c.le_sup_of_pCore_quotient_ne_bot hsp3 (le_sup_left.trans hN.2) hcyc hK
  by_cases hRQ : R ⊓ relPPrimeCore 3 N ≠ ⊥
  · exact c.le_sup_of_inf_relPPrimeCore_ne_bot hN hRi hRQ
  have hKbot : CFSG.pCore 3 (↥N ⧸ CFSG.pPrimeCore 3 ↥N) = ⊥ := by
    by_contra h
    exact hK h
  have hRQbot : R ⊓ relPPrimeCore 3 N = ⊥ := by
    by_contra h
    exact hRQ h
  by_cases hNQ : N ≤ relPPrimeCore 3 N
  · exact hNQ.trans le_sup_left
  obtain ⟨hO3', hcycNs, hpRank, hnt⟩ := caseC_quotient_facts hcyc hNQ
  have himg : CaseCImage N B R := caseC_image_facts c hN hRQbot
  obtain ⟨K, hKn, hKne, -, hKsimple, hBsK, hRsK⟩ :=
    exists_minimalNormal_simple_of_caseC himg.card_B himg.card_R himg.comm hcycNs hKbot hO3' hnt
  have hcent := caseC_inf_centralizer_eq_bot c hN hBsK hRQbot
  have hcl := caseC_kGen147Hyp (D := D) hN hKn hKne hKsimple himg hBsK hRsK hcent hKbot hO3'
    hpRank
  exact caseC_le_sup hKG hKn hRsK hcl (caseC_normalizer_subgroupOf c hN hsp3 hBsK)
    (caseC_normalizerYk c hN hRi hRsK) (caseC_normalizer_seven c hN hRi)

end Ctx147

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
