module

public import CFSG.RankThree.PartTwo.ExponentPrimeSmallRank
public import CFSG.LocalAnalysis.SectionRank.Ccomm.NonabelianCube
public import CFSG.LocalAnalysis.SteinbergCERankTwoActionIndex
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LieType.BorelTits.Basic
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup

variable {p : ℕ} [hp : Fact p.Prime] {H : Type*} [Group H] [Finite H]

theorem false_of_centralizes_rank_two (hH : CFSG.pRank p H ≤ 2) {E : Subgroup H}
    (hEc : IsMulCommutative E) (hEexp : ∀ x ∈ E, x ^ p = 1) (hEcard : Nat.card E = p ^ 2)
    {c : H} (hc : c ∉ E) (hcp : c ^ p = 1) (hcomm : ∀ a ∈ E, a * c = c * a) : False := by
  obtain ⟨hFc, hFcard⟩ := CFSG.RankThree.PartTwo.sup_zpowers_card hEc hc hcp hcomm
  have : IsElementaryAbelian p E :=
    { toIsMulCommutative := hEc
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (by rw [SubgroupClass.coe_pow, OneMemClass.coe_one]; exact hEexp x x.2) }
  have : IsElementaryAbelian p (zpowers c) := IsElementaryAbelian.zpowers_of_pow_eq_one hcp
  have hF : IsElementaryAbelian p ↥(E ⊔ zpowers c) :=
    IsElementaryAbelian.sup_of_le_centralizer
      (zpowers_le.mpr (mem_centralizer_iff.mpr fun a ha => hcomm a ha))
  have hFexp : ∀ x ∈ E ⊔ zpowers c, x ^ p = 1 := fun x hx =>
    CFSG.elemPow_eq_one_of_isElementaryAbelian x hx
  have h3 : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup H) :=
    CFSG.SectionRank.le_pRank hp.out.one_lt le_top ⟨hFc, hFexp⟩
      (by rw [hFcard, hEcard, ← pow_succ])
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at hH
  omega

theorem exists_elementary_le_of_pRank_two {X : Subgroup H} (hX : CFSG.pRank p X = 2)
    (hXexp : ∀ x ∈ X, x ^ p = 1) :
    ∃ E : Subgroup H, E ≤ X ∧ IsMulCommutative E ∧ (∀ x ∈ E, x ^ p = 1) ∧
      Nat.card E = p ^ 2 := by
  obtain ⟨E', hE'c, hE'card⟩ :=
    CFSG.RankThree.PartTwo.exists_isMulCommutative_card_eq_pRank (P := X) hp.out
  rw [hX] at hE'card
  have := hE'c
  refine ⟨E'.map X.subtype, map_subtype_le _, inferInstance, fun x hx => ?_, ?_⟩
  · exact hXexp x (map_subtype_le _ hx)
  · rw [card_map_of_injective X.subtype_injective, hE'card]

theorem le_ker_of_frattini_irreducible {P : Subgroup H} (hPp : IsPGroup p P)
    (hΦ : Nat.card P = p ^ 2 * Nat.card ((frattini P).map P.subtype))
    (hirr : ∀ Y : Subgroup H, (frattini P).map P.subtype ≤ Y → Y ≤ P →
      normalizer (P : Set H) ≤ normalizer (Y : Set H) →
      Y = (frattini P).map P.subtype ∨ Y = P)
    {E : Type*} [Group E] [IsElementaryAbelian p E] (hE : Nat.card E = p ^ 2)
    (φ : H →* MulAut E) : P ≤ φ.ker := by
  set ρ : P →* MulAut E := φ.comp P.subtype with hρ
  have hρker : ρ.ker = φ.ker.subgroupOf P := rfl
  rcases (CFSG.LocalAnalysis.rank_two_elementary_action_index hPp hE ρ).1 with h1 | hpi
  · rw [index_eq_one] at h1
    intro x hx
    have hx' : (⟨x, hx⟩ : P) ∈ ρ.ker := by
      rw [h1]
      exact mem_top _
    exact hx'
  · exfalso
    have hcoatom : IsCoatom ρ.ker := isCoatom_of_index_prime (by rw [hpi]; exact hp.out)
    have hfr : frattini P ≤ ρ.ker := frattini_le_coatom hcoatom
    set Y := ρ.ker.map P.subtype with hY
    have hYP : Y ≤ P := map_subtype_le _
    have hΦY : (frattini P).map P.subtype ≤ Y := map_mono hfr
    have hYeq : Y = φ.ker ⊓ P := by
      rw [hY, hρker, subgroupOf_map_subtype]
    have hNY : normalizer (P : Set H) ≤ normalizer (Y : Set H) := by
      intro n hn
      rw [mem_normalizer_iff]
      intro h
      rw [hYeq, mem_inf, mem_inf]
      have hK : φ.ker.Normal := inferInstance
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨hK.conj_mem h h1 n, (mem_normalizer_iff.mp hn h).mp h2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨?_, (mem_normalizer_iff.mp hn h).mpr h2⟩
        have := hK.conj_mem _ h1 n⁻¹
        simpa [mul_assoc] using this
    have hcardY : Nat.card Y * p = Nat.card P := by
      rw [hY, card_map_of_injective P.subtype_injective, ← hpi, card_mul_index]
    have hpos : 0 < Nat.card ((frattini P).map P.subtype) := Nat.card_pos
    have hp2 := hp.out.two_le
    rcases hirr Y hΦY hYP hNY with h | h
    · rw [h, hΦ] at hcardY
      nlinarith
    · rw [h, hΦ] at hcardY
      nlinarith

theorem nq_normal_rank_two_prime_torsion_rigidity (_hp2 : p ≠ 2) (hH : CFSG.pRank p H ≤ 2)
    (R P : Subgroup H) [R.Normal] (hR : CFSG.pRank p R = 2) (hP : CFSG.pRank p P = 2)
    (hRexp : ∀ x ∈ R, x ^ p = 1) (hPexp : ∀ x ∈ P, x ^ p = 1)
    (hirr : (frattini P).map P.subtype < P ∧
      ∀ Y : Subgroup H, (frattini P).map P.subtype ≤ Y → Y ≤ P →
        normalizer (P : Set H) ≤ normalizer (Y : Set H) →
        Y = (frattini P).map P.subtype ∨ Y = P) :
    R = P := by
  classical
  have hRexp' : ∀ x : R, x ^ p = 1 := fun x =>
    Subtype.ext (by rw [SubgroupClass.coe_pow, OneMemClass.coe_one]; exact hRexp x x.2)
  have hPexp' : ∀ x : P, x ^ p = 1 := fun x =>
    Subtype.ext (by rw [SubgroupClass.coe_pow, OneMemClass.coe_one]; exact hPexp x x.2)
  have hRp : IsPGroup p R := fun x => ⟨1, by rw [pow_one]; exact hRexp' x⟩
  have hPp : IsPGroup p P := fun x => ⟨1, by rw [pow_one]; exact hPexp' x⟩
  obtain ⟨hRstr, -, -⟩ :=
    CFSG.RankThree.PartTwo.exponent_prime_rank_two_structure hRp hRexp' hR
  obtain ⟨hPstr, -, -⟩ :=
    CFSG.RankThree.PartTwo.exponent_prime_rank_two_structure hPp hPexp' hP
  have hp2 := hp.out.two_le
  have hRnorm : ∀ Y : Subgroup H, normalizer (Y : Set H) = ⊤ → normalizer (P : Set H) ≤
      normalizer (Y : Set H) := fun Y hY => by rw [hY]; exact le_top
  have hΦP : frattini P = _root_.commutator P :=
    CFSG.RankThree.PartTwo.frattini_eq_commutator hPp hPexp'
  have hΦ : Nat.card P = p ^ 2 * Nat.card ((frattini P).map P.subtype) := by
    rw [card_map_of_injective P.subtype_injective, hΦP]
    rcases hPstr with ⟨hPel, hP2⟩ | ⟨hP3, hZ, hcomm, -, -⟩
    · have hcomm : _root_.commutator P = ⊥ := by
        rw [eq_bot_iff, _root_.commutator_def, Subgroup.commutator_le]
        intro x _ y _
        rw [mem_bot, commutatorElement_eq_one_iff_mul_comm]
        exact hPel.toIsMulCommutative.is_comm.comm x y
      rw [hcomm, card_bot, hP2, mul_one]
    · rw [hcomm, hZ, hP3, ← pow_succ]
  have hline : ∀ Y : Subgroup H, (frattini P).map P.subtype ≤ Y → Y ≤ P →
      normalizer (P : Set H) ≤ normalizer (Y : Set H) →
      Nat.card Y = p * Nat.card ((frattini P).map P.subtype) → False := by
    intro Y h1 h2 h3 hcard
    have hpos : 0 < Nat.card ((frattini P).map P.subtype) := Nat.card_pos
    rcases hirr.2 Y h1 h2 h3 with h | h
    · rw [h] at hcard
      nlinarith
    · rw [h, hΦ] at hcard
      nlinarith
  rcases hRstr with ⟨hRel, hR2⟩ | ⟨hR3, hRZ, hRcomm, hRel', hRq⟩
  ·
    have hcen := le_ker_of_frattini_irreducible hPp hΦ hirr.2 hR2
      (MulAut.conjNormal : H →* MulAut R)
    have hPR : ∀ x ∈ P, ∀ r ∈ R, x * r = r * x := by
      intro x hx r hr
      have h1 : (MulAut.conjNormal x : MulAut R) = 1 := hcen hx
      have h2 := congrArg (fun f : MulAut R => ((f ⟨r, hr⟩ : R) : H)) h1
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h2
      calc x * r = x * r * x⁻¹ * x := by group
        _ = r * x := by rw [h2]
    obtain ⟨EP, hEPP, hEPc, hEPexp, hEPcard⟩ := exists_elementary_le_of_pRank_two hP hPexp
    have hRP : R ≤ P := by
      intro r hr
      by_contra hrP
      exact false_of_centralizes_rank_two hH hEPc hEPexp hEPcard (fun h => hrP (hEPP h))
        (hRexp r hr) fun a ha => hPR a (hEPP ha) r hr
    rcases hPstr with ⟨-, hP2⟩ | ⟨hP3, hPZ, hPcomm, -, -⟩
    · exact eq_of_le_of_card_ge hRP (by rw [hP2, hR2])
    ·
      exfalso
      have hnc : ∃ a b : P, a * b ≠ b * a := by
        by_contra hcon
        push Not at hcon
        have htop : center P = ⊤ := eq_top_iff.mpr fun a _ =>
          mem_center_iff.mpr fun b => hcon b a
        rw [htop, card_top, hP3] at hPZ
        have : p ^ 3 > p := by nlinarith
        omega
      obtain ⟨-, -, -, -, -, hT, -⟩ :=
        CFSG.SectionRank.Ccomm.nonabelian_prime_cube_central_structure hP3 hnc
      have hRcardP : Nat.card (R.subgroupOf P) = p ^ 2 := by
        rw [Nat.card_congr (subgroupOfEquivOfLe hRP).toEquiv, hR2]
      have hZR : (frattini P).map P.subtype ≤ R := by
        rw [hΦP, hPcomm]
        rintro _ ⟨z, hz, rfl⟩
        exact mem_subgroupOf.mp ((hT _ hRcardP).1 hz)
      refine hline R hZR hRP (hRnorm R (normalizer_eq_top R)) ?_
      rw [hR2, card_map_of_injective P.subtype_injective, hΦP, hPcomm, hPZ, sq]
  ·
    have := hRel'
    have hcen := le_ker_of_frattini_irreducible hPp hΦ hirr.2 hRq
      ((CFSG.SectionRank.Ccomm.autQuotient (_root_.commutator R)).comp
        (MulAut.conjNormal : H →* MulAut R))
    have hnc : ∃ a b : R, a * b ≠ b * a := by
      by_contra hcon
      push Not at hcon
      have htop : center R = ⊤ := eq_top_iff.mpr fun a _ =>
        mem_center_iff.mpr fun b => hcon b a
      rw [htop, card_top, hR3] at hRZ
      have : p ^ 3 > p := by nlinarith
      omega
    obtain ⟨-, -, -, -, -, hT, hinner⟩ :=
      CFSG.SectionRank.Ccomm.nonabelian_prime_cube_central_structure hR3 hnc
    obtain ⟨ER, hERR, hERc, hERexp, hERcard⟩ := exists_elementary_le_of_pRank_two hR hRexp
    have hPR : P ≤ R := by
      intro x hx
      have hφx := hcen hx
      rw [MonoidHom.mem_ker] at hφx
      have hαZ : ∀ y : R, y⁻¹ * (MulAut.conjNormal x : MulAut R) y ∈ center R := by
        intro y
        have h1 := congrArg (fun f : MulAut (R ⧸ _root_.commutator R) =>
          f (QuotientGroup.mk y)) hφx
        simp only [MonoidHom.comp_apply, CFSG.SectionRank.Ccomm.autQuotient_mk,
          MulAut.one_apply] at h1
        have h2 := QuotientGroup.eq.mp h1.symm
        rwa [hRcomm] at h2
      obtain ⟨g, hg⟩ := hinner _ hαZ
      have hcR : ∀ r ∈ R, ((g : H)⁻¹ * x) * r = r * ((g : H)⁻¹ * x) := by
        intro r hr
        have h1 := congrArg (fun f : MulAut R => ((f ⟨r, hr⟩ : R) : H)) hg
        simp only [MulAut.conjNormal_apply, MulAut.conj_apply, coe_mul, coe_inv] at h1
        calc (g : H)⁻¹ * x * r = (g : H)⁻¹ * (x * r * x⁻¹) * x := by group
          _ = (g : H)⁻¹ * ((g : H) * r * (g : H)⁻¹) * x := by rw [h1]
          _ = r * ((g : H)⁻¹ * x) := by group
      have hxgc : x = (g : H) * ((g : H)⁻¹ * x) := by group
      have hcomm' : Commute (g : H) ((g : H)⁻¹ * x) := (hcR g g.2).symm
      have hcp : ((g : H)⁻¹ * x) ^ p = 1 := by
        have hx1 : ((g : H) * ((g : H)⁻¹ * x)) ^ p = 1 := by
          rw [← hxgc]
          exact hPexp x hx
        rwa [hcomm'.mul_pow, hRexp g g.2, one_mul] at hx1
      have hcmem : (g : H)⁻¹ * x ∈ R := by
        by_contra hcR'
        exact false_of_centralizes_rank_two hH hERc hERexp hERcard (fun h => hcR' (hERR h)) hcp
          fun a ha => (hcR a (hERR ha)).symm
      rw [hxgc]
      exact mul_mem g.2 hcmem
    rcases hPstr with ⟨-, hP2⟩ | ⟨hP3, -, -, -, -⟩
    ·
      exfalso
      have hPcardR : Nat.card (P.subgroupOf R) = p ^ 2 := by
        rw [Nat.card_congr (subgroupOfEquivOfLe hPR).toEquiv, hP2]
      have hZP : (center R).map R.subtype ≤ P := by
        rintro _ ⟨z, hz, rfl⟩
        exact mem_subgroupOf.mp ((hT _ hPcardR).1 hz)
      have hΦbot : (frattini P).map P.subtype = ⊥ := by
        rw [← card_eq_one]
        have h1 : p ^ 2 * 1 = p ^ 2 * Nat.card ((frattini P).map P.subtype) := by
          rw [mul_one, ← hΦ, hP2]
        exact (Nat.eq_of_mul_eq_mul_left (by positivity) h1).symm
      have hZnorm : normalizer (((center R).map R.subtype : Subgroup H) : Set H) = ⊤ := by
        rw [eq_top_iff, ← normalizer_eq_top (H := R)]
        exact LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (center R)
      refine hline ((center R).map R.subtype) (by rw [hΦbot]; exact bot_le) hZP
        (hRnorm _ hZnorm) ?_
      rw [hΦbot, card_bot, mul_one, card_map_of_injective R.subtype_injective, hRZ]
    · exact (eq_of_le_of_card_ge hPR (by rw [hR3, hP3])).symm

end CFSG.Quasithin.H13.NQBlock
