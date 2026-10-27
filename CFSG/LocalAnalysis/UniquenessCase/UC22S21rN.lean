module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a
public import CFSG.LocalAnalysis.UniquenessCase.UCFront78Nar
import CFSG.LocalAnalysis.UniquenessCase.UC22P20a
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rQ

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G]

theorem uc22s21rn_not_le_of_uniqueMax (D : Data G) {H E : Subgroup G}
    (hH : H ∈ hSet D.T D.M) (hE : UniqueMax D.M E) (hEH : E ≤ H) : False := by
  obtain ⟨N, hN, hHN⟩ := uc22p20a_exists_mem_calMOf D hH
  have hmem : N ∈ calMOf E := ⟨hN.1, hEH.trans hHN⟩
  rw [hE] at hmem
  exact hH.2.1 ((Set.mem_singleton_iff.1 hmem) ▸ hHN)

theorem uc22s21rn_exists_sylow_ge {q : ℕ} [Fact q.Prime] {K E : Subgroup G} (hEK : E ≤ K)
    (hE : IsPGroup q E) : ∃ Q : Subgroup G, IsSylowOf q Q K ∧ E ≤ Q := by
  obtain ⟨S, hS⟩ := (hE.comap_subtype (K := K)).exists_le_sylow
  exact ⟨(S : Subgroup K).map K.subtype, ⟨S, rfl⟩, fun x hx => ⟨⟨x, hEK hx⟩, hS hx, rfl⟩⟩

theorem uc22s21rn_uniqueMax (D : Data G) (h61 : UC6.R6_1 D) (h63 : UC6.R6_3 D) {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) {X : Subgroup (Bar2 D.M)}
    (hΓ : q ∈ D.sig ∨ ∀ Q : Subgroup G, IsSylowOf q Q (barPreimage D.M X) →
      rankThreeGamma 1 q Q ≤ D.M)
    {E : Subgroup G} (hE : E ≤ barPreimage D.M X) (hEp : IsPGroup q E) (hnc : ¬ IsCyclic E) :
    UniqueMax D.M E := by
  haveI := Fact.mk hq
  have hEM : E ≤ D.M := hE.trans (Subgroup.map_subtype_le _)
  refine uc22p22u_uniqueMax_of_noncyclic D h61 h63 hq hq2 hEM hEp hnc ?_
  rcases hΓ with hsig | hΓ
  · exact Or.inr hsig
  · obtain ⟨Q, hQ, hEQ⟩ := uc22s21rn_exists_sylow_ge hE hEp
    exact Or.inl ((uc22p22u_gamma_mono hEQ).trans (hΓ Q hQ))

theorem uc22s21rn_cyclic_of_le (D : Data G) (h61 : UC6.R6_1 D) (h63 : UC6.R6_3 D) {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) {X : Subgroup (Bar2 D.M)}
    (hΓ : q ∈ D.sig ∨ ∀ Q : Subgroup G, IsSylowOf q Q (barPreimage D.M X) →
      rankThreeGamma 1 q Q ≤ D.M)
    {H : Subgroup G} (hH : H ∈ hSet D.T D.M) {E : Subgroup G} (hE : E ≤ barPreimage D.M X)
    (hEp : IsPGroup q E) (hEH : E ≤ H) : IsCyclic E := by
  by_contra hnc
  exact uc22s21rn_not_le_of_uniqueMax D hH (uc22s21rn_uniqueMax D h61 h63 hq hq2 hΓ hE hEp hnc) hEH

theorem uc22s21rn_isCyclic_of_barImage_eq {M Q : Subgroup G} (hQM : Q ≤ M)
    {R : Subgroup (Bar2 M)} (h : barImage M Q = R) (hc : IsCyclic Q) : IsCyclic R := by
  have hmem : ∀ x : Q, QuotientGroup.mk' (CFSG.pCore 2 ↥M) (Subgroup.inclusion hQM x) ∈ R :=
    fun x => by
      rw [← h]
      exact ⟨Subgroup.inclusion hQM x, x.2, rfl⟩
  refine isCyclic_of_surjective
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp (Subgroup.inclusion hQM) |>.codRestrict R hmem) ?_
  intro y
  have hy : (y : Bar2 M) ∈ barImage M Q := by rw [h]; exact y.2
  obtain ⟨z, hz, hzy⟩ := hy
  exact ⟨⟨(z : G), hz⟩, Subtype.ext hzy⟩

theorem uc22s21rn_piece_cyclic (D : Data G) (h61 : UC6.R6_1 D) (h63 : UC6.R6_3 D) {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) {X : Subgroup (Bar2 D.M)}
    (hΓ : q ∈ D.sig ∨ ∀ Q : Subgroup G, IsSylowOf q Q (barPreimage D.M X) →
      rankThreeGamma 1 q Q ≤ D.M)
    {R : Subgroup (Bar2 D.M)} (hRX : R ≤ X) (hR : IsPGroup q R) {H : Subgroup G}
    (hH : H ∈ hSet D.T D.M) (hRH : barPreimage D.M R ≤ H) : IsCyclic R := by
  haveI := Fact.mk hq
  obtain ⟨Q, hQ⟩ := CFSG.ABGLocalTools.exists_isSylowOf q (barPreimage D.M R)
  obtain ⟨hQM, hQR, -⟩ := uc22s21rq_barImage_sylow D.M hq hq2 hR hQ
  have hQX : Q ≤ barPreimage D.M X :=
    hQ.le.trans (Subgroup.map_mono (Subgroup.comap_mono hRX))
  exact uc22s21rn_isCyclic_of_barImage_eq hQM hQR
    (uc22s21rn_cyclic_of_le D h61 h63 hq hq2 hΓ hH hQX hQ.isPGroup (hQ.le.trans hRH))

theorem uc22s21rn_hGamma (D : Data G) (hr77 : F07.R77E4 D) (hσ1 : D.sig ⊆ D.sig1) {p q : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpσ : p ∈ D.sig) (hq : q.Prime) (hq2 : q ≠ 2)
    (hsp : IsStronglyPEmbedded p D.M) (hrk : 3 < Open.pRank p D.M) {X : Subgroup (Bar2 D.M)}
    [X.Normal] (hXq : IsPGroup q X) (hXnc : ¬ IsCyclic X) (hXexp : ∀ x ∈ X, x ^ q = 1)
    (hXcl : ⁅⁅X, X⁆, X⁆ = ⊥) :
    q ∈ D.sig ∨ ∀ Q : Subgroup G, IsSylowOf q Q (barPreimage D.M X) →
      rankThreeGamma 1 q Q ≤ D.M := by
  by_cases hqσ : q ∈ D.sig
  · exact Or.inl hqσ
  · exact Or.inr fun Q hQ => uc22s21rq_gamma_le D hr77 hσ1 hp hp2 hpσ hq hq2
      (fun h => hqσ (h ▸ hpσ)) hqσ hsp hrk hXq hXnc hXexp hXcl hQ

theorem uc22s21rn_piece_cyclic_of_r77 (D : Data G) (h61 : UC6.R6_1 D) (h63 : UC6.R6_3 D)
    (hr77 : F07.R77E4 D) (hσ1 : D.sig ⊆ D.sig1) {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpσ : p ∈ D.sig) (hq : q.Prime) (hq2 : q ≠ 2) (hsp : IsStronglyPEmbedded p D.M)
    (hrk : 3 < Open.pRank p D.M) {X : Subgroup (Bar2 D.M)} [X.Normal] (hXq : IsPGroup q X)
    (hXnc : ¬ IsCyclic X) (hXexp : ∀ x ∈ X, x ^ q = 1) (hXcl : ⁅⁅X, X⁆, X⁆ = ⊥)
    {R : Subgroup (Bar2 D.M)} (hRX : R ≤ X) {H : Subgroup G} (hH : H ∈ hSet D.T D.M)
    (hRH : barPreimage D.M R ≤ H) : IsCyclic R :=
  uc22s21rn_piece_cyclic D h61 h63 hq hq2
    (uc22s21rn_hGamma D hr77 hσ1 hp hp2 hpσ hq hq2 hsp hrk hXq hXnc hXexp hXcl) hRX
    (hXq.to_le hRX) hH hRH

end CFSG.LocalAnalysis.UniquenessCase.UC22
