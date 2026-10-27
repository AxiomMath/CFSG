module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K462Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.UC46

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem isCyclic_sylow_of_pRank_eq_one {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hrank : CFSG.Open.pRank p (⊤ : Subgroup G) = 1) (P : Sylow p G) :
    IsCyclic ↥(P : Subgroup G) := by
  have hpr : CFSG.pRank p ↥(P : Subgroup G) ≤ 1 := by
    rw [(CFSG.SectionRank.pRank_sylow P).2, CFSG.SectionRank.pRank_eq_open_pRank_top, hrank]
  rcases (CFSG.LocalAnalysis.ComponentInitial.pgroup_rank_one_classification
    (Fact.out : p.Prime) P.isPGroup').1 hpr with hcyc | ⟨hp, -⟩
  · exact hcyc
  · exact absurd hp hp2

theorem eq_of_le_sylow_of_card_eq_prime {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hrank : CFSG.Open.pRank p (⊤ : Subgroup G) = 1) {P : Sylow p G} {A B : Subgroup G}
    (hA : Nat.card A = p) (hB : Nat.card B = p) (hAP : A ≤ P) (hBP : B ≤ P) : A = B := by
  haveI : IsCyclic ↥(P : Subgroup G) := isCyclic_sylow_of_pRank_eq_one hp2 hrank P
  have hEq : A.subgroupOf (P : Subgroup G) = B.subgroupOf (P : Subgroup G) := by
    rw [IsCyclic.subgroup_eq_iff_card_eq,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAP).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBP).toEquiv, hA, hB]
  calc A = (A.subgroupOf (P : Subgroup G)).map (P : Subgroup G).subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hAP).symm
    _ = (B.subgroupOf (P : Subgroup G)).map (P : Subgroup G).subtype := by rw [hEq]
    _ = B := Subgroup.map_subgroupOf_eq_of_le hBP

theorem exists_conj_eq_of_card_eq_prime {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hrank : CFSG.Open.pRank p (⊤ : Subgroup G) = 1) {A B : Subgroup G}
    (hA : Nat.card A = p) (hB : Nat.card B = p) :
    ∃ g : G, B = A.map (MulAut.conj g).toMonoidHom := by
  have hAp : IsPGroup p A := IsPGroup.of_card (n := 1) (by rw [hA, pow_one])
  have hBp : IsPGroup p B := IsPGroup.of_card (n := 1) (by rw [hB, pow_one])
  obtain ⟨P, hAP⟩ := hAp.exists_le_sylow
  obtain ⟨Q, hBQ⟩ := hBp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Q
  have hg' : (Q : Subgroup G) = P.map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul]
    rfl
  refine ⟨g, ?_⟩
  have hcard : Nat.card (A.map (MulAut.conj g).toMonoidHom) = p := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hA]
  have hAQ : A.map (MulAut.conj g).toMonoidHom ≤ Q := by
    rw [hg']
    exact Subgroup.map_mono hAP
  exact (eq_of_le_sylow_of_card_eq_prime hp2 hrank hcard hB hAQ hBQ).symm

theorem le_of_normal_of_dvd_card {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hrank : CFSG.Open.pRank p (⊤ : Subgroup G) = 1) {A N : Subgroup G}
    (hA : Nat.card A = p) (hN : N.Normal) (hdvd : p ∣ Nat.card N) : A ≤ N := by
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) p hdvd
  have hxG : orderOf (x : G) = p := (Subgroup.orderOf_coe x).trans hx
  have hEN : Subgroup.zpowers (x : G) ≤ N := Subgroup.zpowers_le.2 x.2
  have hEcard : Nat.card (Subgroup.zpowers (x : G)) = p := by
    rw [Nat.card_zpowers, hxG]
  obtain ⟨g, hg⟩ := exists_conj_eq_of_card_eq_prime hp2 hrank hEcard hA
  have hconj : N.map (MulAut.conj g).toMonoidHom ≤ N := by
    rintro y ⟨n, hn, rfl⟩
    simpa [MulAut.conj_apply] using hN.conj_mem n hn g
  rw [hg]
  exact (Subgroup.map_mono hEN).trans hconj

theorem center_ne_top {D : Subgroup G} (hD : Nat.card D = 3) (hperf : commutator G = ⊤) :
    Subgroup.center G ≠ ⊤ := by
  intro hcenter
  have hbot : commutator G = ⊥ := (commutator_eq_bot_iff_center_eq_top G).2 hcenter
  have htopbot : (⊤ : Subgroup G) = ⊥ := by rw [← hperf, hbot]
  have hsub : Subsingleton G := ⟨fun a b => by
    have ha : a ∈ (⊥ : Subgroup G) := htopbot ▸ mem_top a
    have hb : b ∈ (⊥ : Subgroup G) := htopbot ▸ mem_top b
    rw [Subgroup.mem_bot] at ha hb
    rw [ha, hb]⟩
  have hcardG : Nat.card G ≤ 1 := Finite.card_le_one_iff_subsingleton.2 hsub
  have h3 : 3 ≤ Nat.card G := by
    rw [← hD]
    exact Subgroup.card_le_card_group D
  omega

theorem proper_normal_le_center (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup G) = 1)
    {D : Subgroup G} (hD : Nat.card D = 3) (hgen : Subgroup.normalClosure (D : Set G) = ⊤)
    (hc : CFSG.pPrimeCore 3 G ≤ Subgroup.center G) {N : Subgroup G}
    (hN : N.Normal) (hNtop : N ≠ ⊤) : N ≤ Subgroup.center G := by
  by_cases h3 : 3 ∣ Nat.card N
  · have hDle : D ≤ N :=
      le_of_normal_of_dvd_card (p := 3) (by norm_num) hrank hD hN h3
    have hclosure : Subgroup.normalClosure (D : Set G) ≤ N :=
      Subgroup.normalClosure_le_normal (fun x hx => hDle hx)
    rw [hgen] at hclosure
    exact absurd (eq_top_iff.2 hclosure) hNtop
  · have hcop : Nat.Coprime 3 (Nat.card N) :=
      (Nat.prime_three.coprime_iff_not_dvd).2 h3
    have hle : N ≤ CFSG.pPrimeCore 3 G :=
      le_sSup (s := {K : Subgroup G | K.Normal ∧ Nat.Coprime 3 (Nat.card K)}) ⟨hN, hcop⟩
    exact hle.trans hc

theorem not_three_dvd_card_center (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup G) = 1)
    {D : Subgroup G} (hD : Nat.card D = 3) (hgen : Subgroup.normalClosure (D : Set G) = ⊤)
    (hperf : commutator G = ⊤) : ¬ 3 ∣ Nat.card (Subgroup.center G) := by
  intro h3
  have hDZ : D ≤ Subgroup.center G :=
    le_of_normal_of_dvd_card (p := 3) (by norm_num) hrank hD
      (inferInstance : (Subgroup.center G).Normal) h3
  have hclosure : Subgroup.normalClosure (D : Set G) ≤ Subgroup.center G :=
    Subgroup.normalClosure_le_normal (fun x hx => hDZ hx)
  rw [hgen] at hclosure
  exact center_ne_top hD hperf (eq_top_iff.2 hclosure)

theorem isSimpleGroup_quotient_center (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup G) = 1)
    {D : Subgroup G} (hD : Nat.card D = 3) (hgen : Subgroup.normalClosure (D : Set G) = ⊤)
    (hperf : commutator G = ⊤) (hc : CFSG.pPrimeCore 3 G ≤ Subgroup.center G) :
    IsSimpleGroup (G ⧸ Subgroup.center G) := by
  haveI : Nontrivial (G ⧸ Subgroup.center G) :=
    QuotientGroup.nontrivial_iff.2 (center_ne_top hD hperf)
  refine { eq_bot_or_eq_top_of_normal := ?_ }
  intro T hT
  let M : Subgroup G := T.comap (QuotientGroup.mk' (Subgroup.center G))
  have hMnorm : M.Normal := hT.comap _
  have hZle : Subgroup.center G ≤ M := fun x hx => by
    show QuotientGroup.mk' (Subgroup.center G) x ∈ T
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).2 hx]
    exact T.one_mem
  by_cases hMtop : M = ⊤
  · right
    refine eq_top_iff.2 fun t _ => ?_
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective t
    have : g ∈ M := by rw [hMtop]; exact mem_top g
    exact this
  · left
    have hMle : M ≤ Subgroup.center G :=
      proper_normal_le_center hrank hD hgen hc hMnorm hMtop
    have hMeq : M = Subgroup.center G := le_antisymm hMle hZle
    refine eq_bot_iff.2 fun t ht => ?_
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective t
    have hg : g ∈ M := ht
    rw [hMeq] at hg
    rw [Subgroup.mem_bot]
    exact (QuotientGroup.eq_one_iff g).2 hg

end CFSG.LocalAnalysis.UniquenessCase.UCK.UC46

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

theorem quasisimpleOfCentral_holds : QuasisimpleOfCentral :=
  fun p _ G _ _ V _ _ _ ρ D h hc =>
    ⟨⟨h.perfect, UC46.isSimpleGroup_quotient_center h.rank h.card_three h.gen h.perfect hc⟩,
      UC46.uc45_center h.toHyp45,
      UC46.not_three_dvd_card_center h.rank h.card_three h.gen h.perfect⟩

end CFSG.LocalAnalysis.UniquenessCase.UCK
