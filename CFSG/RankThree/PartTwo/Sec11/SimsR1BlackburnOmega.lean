module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Extraspecial
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PGroup.Omega
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.Defs
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.theorem_4_16

public section

namespace CFSG.RankThree.PartTwo.Sec11.SimsR1.Blackburn

variable {p : ℕ} [Fact p.Prime] {P : Type} [Group P] [Finite P]

theorem omega_large [Fact (IsPGroup p P)] (hp : 3 < p) (hrank : CFSG.groupRank P ≤ 2)
    (hΩ : ¬ Nat.card (CFSG.omega₁ (G := P) (p := p)) ≤ p ^ 2) :
    Monoid.exponent (CFSG.omega₁ (G := P) (p := p)) = p ∧
      Nat.card (CFSG.omega₁ (G := P) (p := p)) = p ^ 3 := by
  classical
  let Ω : Subgroup P := CFSG.omega₁ (G := P) (p := p)
  have hΩexp : Monoid.exponent Ω = p := by
    rcases CFSG.proposition_4_8_b (R := P) (p := p) hp hrank with hExpOne | hExpP
    · have : Subsingleton Ω := (Monoid.exp_eq_one_iff (G := Ω)).mp hExpOne
      have hΩcard_one : Nat.card Ω = 1 := by
        simp
      have hΩ_le : Nat.card Ω ≤ p ^ 2 := by
        rw [hΩcard_one]
        exact Nat.succ_le_of_lt (pow_pos (Fact.out : Nat.Prime p).pos 2)
      exact False.elim (hΩ (by simpa [Ω] using hΩ_le))
    · exact hExpP
  have hΩp : IsPGroup p Ω := (Fact.out : IsPGroup p P).to_subgroup Ω
  let : Fact (IsPGroup p Ω) := ⟨hΩp⟩
  have hΩrank : CFSG.groupRank Ω ≤ 2 :=
    (CFSG.groupRank_le_of_subgroup (R := P) Ω).trans hrank
  have hΩcard_le : Nat.card Ω ≤ p ^ 3 :=
    CFSG.natCard_le_p_cubed_of_groupRank_le_two_and_exponent_p_local (R := Ω) (p := p)
      hΩrank hΩexp
  obtain ⟨n, hn⟩ := hΩp.exists_card_eq
  have hn_ge_three : 3 ≤ n := by
    have hgt : p ^ 2 < Nat.card Ω := lt_of_not_ge (by simpa [Ω] using hΩ)
    rw [hn] at hgt
    have hn_gt_two : 2 < n :=
      (Nat.pow_lt_pow_iff_right (Fact.out : Nat.Prime p).one_lt).1 hgt
    omega
  have hn_le_three : n ≤ 3 := by
    rw [hn] at hΩcard_le
    exact (Nat.pow_le_pow_iff_right (Fact.out : Nat.Prime p).one_lt).1 hΩcard_le
  have hn_eq_three : n = 3 := by omega
  exact ⟨by simpa [Ω] using hΩexp, by simpa [Ω, hn_eq_three] using hn⟩

private theorem omega_not_isMulCommutative [Fact (IsPGroup p P)] (hrank : CFSG.groupRank P ≤ 2)
    (hΩexp : Monoid.exponent (CFSG.omega₁ (G := P) (p := p)) = p)
    (hΩcard : Nat.card (CFSG.omega₁ (G := P) (p := p)) = p ^ 3) :
    ¬ IsMulCommutative (CFSG.omega₁ (G := P) (p := p)) := by
  classical
  let Ω : Subgroup P := CFSG.omega₁ (G := P) (p := p)
  intro hΩcomm
  have hΩp : IsPGroup p Ω := (Fact.out : IsPGroup p P).to_subgroup Ω
  have hΩelem : CFSG.IsElementaryAbelian p Ω := {
    toIsMulCommutative := hΩcomm
    exponent_dvd_p := by
      rw [show Monoid.exponent Ω = p by simpa [Ω] using hΩexp]
  }
  let : CFSG.IsElementaryAbelian p Ω := hΩelem
  have hΩgen_three : 3 ≤ CFSG.generatorRank Ω :=
    CFSG.generatorRank_at_least_three_of_elementaryAbelian_card_p3_for_415
      (p := p) (A := Ω) (by simpa [Ω] using hΩcard)
  have hΩgen_le_rank : CFSG.generatorRank Ω ≤ CFSG.groupRank P :=
    CFSG.generatorRank_le_groupRank_of_isPGroup_abelian_subgroup
      (R := P) (q := p) hΩp hΩcomm
  exact (by decide : ¬ 3 ≤ (2 : ℕ)) (hΩgen_three.trans (hΩgen_le_rank.trans hrank))

theorem isExtraspecial_omega [Fact (IsPGroup p P)] (hp : 3 < p) (hrank : CFSG.groupRank P ≤ 2)
    (hΩ : ¬ Nat.card (CFSG.omega₁ (G := P) (p := p)) ≤ p ^ 2) :
    CFSG.IsExtraspecial p (CFSG.omega₁ (G := P) (p := p)) := by
  obtain ⟨hexp, hcard⟩ := omega_large hp hrank hΩ
  haveI : Fact (IsPGroup p (CFSG.omega₁ (G := P) (p := p))) :=
    ⟨(Fact.out : IsPGroup p P).to_subgroup _⟩
  exact CFSG.isExtraspecial_of_noncommutative_card_p3_exponent_p hcard hexp
    (omega_not_isMulCommutative hrank hexp hcard)

private theorem isCyclic_centralizer_of_isExtraspecial_omega [Fact (IsPGroup p P)] (hpodd : p ≠ 2)
    (hΩextra : CFSG.IsExtraspecial p (CFSG.omega₁ (G := P) (p := p))) :
    IsCyclic (Subgroup.centralizer ((CFSG.omega₁ (G := P) (p := p) : Subgroup P) : Set P)) := by
  classical
  let S : Subgroup P := CFSG.omega₁ (G := P) (p := p)
  let : CFSG.IsExtraspecial p S := by
    simpa [S] using hΩextra
  let C : Subgroup P := Subgroup.centralizer ((S : Subgroup P) : Set P)
  let ΩC : Subgroup C := CFSG.omega₁ (G := C) (p := p)
  let ΩCmap : Subgroup P := ΩC.map C.subtype
  let ZSmap : Subgroup P := (Subgroup.center S).map S.subtype
  have hΩC_le_S : ΩCmap ≤ S := by
    simpa [ΩCmap, ΩC, C, S] using CFSG.omega₁_map_subtype_le (G := P) (p := p) C
  have hΩC_le_C : ΩCmap ≤ C := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.2
  have hΩC_le_ZS : ΩCmap ≤ ZSmap := by
    intro x hx
    have hxS : x ∈ S := hΩC_le_S hx
    have hxC : x ∈ C := hΩC_le_C hx
    change x ∈ (Subgroup.center S).map S.subtype
    rw [Subgroup.mem_map]
    refine ⟨⟨x, hxS⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp hxC) (y : P) y.2
  have hΩC_card_map : Nat.card ΩCmap = Nat.card ΩC := by
    exact Subgroup.card_map_of_injective (K := ΩC) (f := C.subtype) C.subtype_injective
  have hZS_card_map : Nat.card ZSmap = Nat.card (Subgroup.center S) := by
    exact Subgroup.card_map_of_injective
      (K := Subgroup.center S) (f := S.subtype) S.subtype_injective
  have hΩC_le_p : Nat.card ΩC ≤ p := by
    rw [← hΩC_card_map]
    calc
      Nat.card ΩCmap ≤ Nat.card ZSmap := Subgroup.card_le_of_le hΩC_le_ZS
      _ = Nat.card (Subgroup.center S) := hZS_card_map
      _ = p := by simpa [S] using CFSG.IsExtraspecial.center_order_p p S
  have hZSmap_le_C : ZSmap ≤ C := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨z, hz, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hyS
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hz) ⟨y, hyS⟩)
  have hZSmap_card : Nat.card ZSmap = p := by
    calc
      Nat.card ZSmap = Nat.card (Subgroup.center S) := hZS_card_map
      _ = p := by simpa [S] using CFSG.IsExtraspecial.center_order_p p S
  have hC_card_ge_p : p ≤ Nat.card C := by
    rw [← hZSmap_card]
    exact Subgroup.card_le_of_le hZSmap_le_C
  have hC_nontriv : Nontrivial C :=
    Finite.one_lt_card_iff_nontrivial.mp
      (lt_of_lt_of_le (Fact.out : Nat.Prime p).one_lt hC_card_ge_p)
  have hCp : IsPGroup p C := (Fact.out : IsPGroup p P).to_subgroup C
  let : Fact (IsPGroup p C) := ⟨hCp⟩
  let : Nontrivial C := hC_nontriv
  have hΩC_ge_p : p ≤ Nat.card ΩC :=
    CFSG.prime_le_natCard_omega₁_of_nontrivial_pGroup_early (G := C) (p := p)
  have hΩC_card : Nat.card ΩC = p := le_antisymm hΩC_le_p hΩC_ge_p
  exact CFSG.isCyclic_of_natCard_omega₁_eq_prime_early (G := C) (p := p) hpodd hΩC_card

theorem isCyclic_centralizer_omega [Fact (IsPGroup p P)] (hp : 3 < p)
    (hrank : CFSG.groupRank P ≤ 2) (hΩ : ¬ Nat.card (CFSG.omega₁ (G := P) (p := p)) ≤ p ^ 2) :
    IsCyclic (Subgroup.centralizer ((CFSG.omega₁ (G := P) (p := p) : Subgroup P) : Set P)) :=
  isCyclic_centralizer_of_isExtraspecial_omega (by omega) (isExtraspecial_omega hp hrank hΩ)

end CFSG.RankThree.PartTwo.Sec11.SimsR1.Blackburn
