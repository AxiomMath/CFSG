module

public import CFSG.RankThree.PartTwo.Sec12.Hering129CFam0
import CFSG.RankThree.PartTwo.Sec4.Ronan148SRowJ2

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Blueprint CFSG.RankThree.PartTwo.Sec4.Ronan148S

namespace Hering129C

section SylowLe

variable {S Lb : Type} [Group S] [Finite S] [Group Lb] {s : S} {J : Subgroup S} {g : ↥J →* Lb}

theorem PPair.exists_sylow_le (h : PPair s J g) (h81 : ¬ 81 ∣ Nat.card S) :
    ∃ P : Sylow 3 S, (P : Subgroup S) ≤ J ∧ s ∈ (P : Subgroup S) ∧
      (P : Subgroup S) ≤ Subgroup.centralizer {s} := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h27K : 27 ∣ Nat.card J :=
    h.twentySeven_dvd_Lb.trans (Subgroup.card_dvd_of_surjective h.surjective)
  set k : J := ⟨s, h.s_mem⟩ with hk
  have hk3 : IsPGroup 3 (Subgroup.zpowers k) :=
    IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, hk, Subgroup.orderOf_mk, h.orderOf_s, pow_one])
  obtain ⟨Q, hQ⟩ := hk3.exists_le_sylow
  have hkQ : k ∈ (Q : Subgroup J) := hQ (Subgroup.mem_zpowers k)
  have h27Q : 27 ∣ Nat.card (Q : Subgroup J) :=
    Q.pow_dvd_card_of_pow_dvd_card (n := 3) (by norm_num; exact h27K)
  have hQ3 : IsPGroup 3 ((Q : Subgroup J).map J.subtype) := Q.isPGroup'.map _
  obtain ⟨P, hP⟩ := hQ3.exists_le_sylow
  have hPcard : Nat.card (P : Subgroup S) ≤ 27 := by
    rw [P.card_eq_multiplicity]
    by_contra hlt
    push Not at hlt
    have h4 : 4 ≤ (Nat.card S).factorization 3 := by
      by_contra h'
      push Not at h'
      have : 3 ^ (Nat.card S).factorization 3 ≤ 3 ^ 3 :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    apply h81
    have : 3 ^ 4 ∣ 3 ^ (Nat.card S).factorization 3 := Nat.pow_dvd_pow 3 h4
    exact (by norm_num : (81 : ℕ) = 3 ^ 4) ▸
      this.trans (Nat.ordProj_dvd (Nat.card S) 3)
  have hmapcard : Nat.card ((Q : Subgroup J).map J.subtype) = Nat.card (Q : Subgroup J) :=
    Subgroup.card_map_of_injective J.subtype_injective
  have hge : 27 ≤ Nat.card ((Q : Subgroup J).map J.subtype) := by
    rw [hmapcard]
    exact Nat.le_of_dvd Nat.card_pos h27Q
  have hPeq : (Q : Subgroup J).map J.subtype = (P : Subgroup S) :=
    Subgroup.eq_of_le_of_card_ge hP (by omega)
  refine ⟨P, ?_, ?_, ?_⟩
  · rw [← hPeq]
    exact Subgroup.map_subtype_le _
  · rw [← hPeq]
    exact ⟨k, hkQ, rfl⟩
  · rw [← hPeq]
    exact (Subgroup.map_subtype_le _).trans h.le_centralizer

end SylowLe

section J2


theorem PPair.isTripleCover_J2 {S Lb : Type} [Group S] [Finite S] [Group Lb] {s : S}
    {J : Subgroup S} {g : ↥J →* Lb} (e : S ≃* NativeSporadic.J2) (h : PPair s J g) :
    Sec4.IsTripleCover Lb (alternatingGroup (Fin 6)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := h.finite_Lb
  have hSc : Nat.card S = 604800 := by
    rw [Nat.card_congr e.toEquiv, KFacts.KS14.card_nativeJ2]
  have h81 : ¬ 81 ∣ Nat.card S := by
    rw [hSc]
    norm_num
  obtain ⟨P, hPJ, hsP, hPC⟩ := h.exists_sylow_le h81
  set Z : Subgroup S := (P : Subgroup S) ⊓ Subgroup.centralizer ((P : Subgroup S) : Set S)
    with hZdef
  have hsZ : s ∈ Z := Subgroup.mem_inf.mpr ⟨hsP, Subgroup.mem_centralizer_iff.mpr fun h' hh' =>
    Subgroup.mem_centralizer_singleton_iff.mp (hPC hh')⟩
  obtain ⟨⟨hHeis, -⟩, -, ⟨-, hext, -⟩, -⟩ :=
    CFSG.RankThree.PartTwo.Sec4.Sporadic.rank3II_4_15 S ⟨e⟩ P Z hZdef _ rfl
  have hZcard : Nat.card Z = 3 := card_inf_centralizer_of_isHeisThree hHeis
  have hZeq : Subgroup.zpowers s = Z := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hsZ)
    exact le_of_eq (by rw [Nat.card_zpowers, h.orderOf_s, hZcard])
  have hKle : J ≤ Subgroup.centralizer (Z : Set S) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hz' : z ∈ Subgroup.zpowers s := by
      rw [hZeq]
      exact hz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz'
    have hkc : Commute k s := Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer hk)
    exact ((hkc.zpow_right n).eq).symm
  have hCcard : Nat.card (Subgroup.centralizer (Z : Set S)) = 1080 :=
    KFacts.KS14.card_eq_of_isExtOf_alternating_six hext
  have hLJ : Nat.card Lb ∣ Nat.card J := Subgroup.card_dvd_of_surjective h.surjective
  have hdvd : Nat.card Lb ∣ 604800 :=
    hLJ.trans ((Subgroup.card_subgroup_dvd_card J).trans (dvd_of_eq hSc))
  have hmem := card_mem_typeOrders425 h.quasisimple_Lb (M := 604800) (B := 85) (by norm_num)
    (by norm_num) (isType425_of_isType122 h.type_Lb) hdvd
  have hLge : 1080 ≤ Nat.card Lb := typeOrders425_J2_ge _ hmem
  have hJle : Nat.card J ≤ 1080 := by
    rw [← hCcard]
    exact Subgroup.card_le_of_le hKle
  have hLle : Nat.card Lb ≤ Nat.card J := Nat.le_of_dvd Nat.card_pos hLJ
  have hJeq : J = Subgroup.centralizer (Z : Set S) :=
    Subgroup.eq_of_le_of_card_ge hKle (by omega)
  have hker : Nat.card g.ker = 1 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup g.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective g h.surjective).toEquiv] at h1
    have hJL : Nat.card J = Nat.card Lb := by omega
    rw [hJL] at h1
    have hpos : 0 < Nat.card Lb := Nat.card_pos
    nlinarith
  have hinj : Function.Injective g := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_card]
    exact hker
  let eL : ↥J ≃* Lb := MulEquiv.ofBijective g ⟨hinj, h.surjective⟩
  have hLext : Sec4.IsExtOf Lb (alternatingGroup (Fin 6)) (Multiplicative (ZMod 3)) :=
    isExtOf_congr ((MulEquiv.subgroupCongr hJeq.symm).trans eL) hext
  exact (Sec4.isTripleCover_iff_isExtOf h.quasisimple_Lb
    (center_alternatingGroup_eq_bot (by norm_num : 4 ≤ 6))).mpr hLext

theorem kFCensus46Five_J2 :
    KFCensusOn (fun Q _ => Nonempty (Q ≃* NativeSporadic.Carrier .J2)) := by
  intro Q Lb _ _ _ c a I X f hQ hD
  obtain ⟨e⟩ := hQ
  exact Or.inl ⟨⟨e⟩, (ppair_self hD).isTripleCover_J2 e⟩

end J2

end Hering129C

end CFSG.RankThree.PartTwo.Sec12
