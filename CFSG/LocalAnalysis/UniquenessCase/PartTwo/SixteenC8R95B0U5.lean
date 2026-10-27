module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8R95B0D
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8R95A3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8R95B0U4
import CFSG.Quasithin.H13.GoldschmidtC137SQL32
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddQ7U3Max

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg
  CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.U3
  CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.Q7U3
open scoped commutatorElement
open CFSG.Blueprint (LieModel)

theorem r95_u3_char_seven_of_le_centralizer {F : Type} [Field F]
    [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p] (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2)
    (hL : IsSL2Cover ↥(embSU (unitaryInvolution F p f)).range p f)
    {E : Subgroup (SU (unitaryInvolution F p f) 3)}
    (hEz : E ≤ Subgroup.centralizer ({zSU hF} : Set (SU (unitaryInvolution F p f) 3)))
    (hE : HasL32Quot E) : p = 7 := by
  classical
  obtain ⟨Qm, hQm, π, hπ, hm⟩ := hE
  letI : Group Qm := hQm
  obtain ⟨hQmsimple, hQmcard⟩ :=
    CFSG.Quasithin.H13.U3.GC137.SQ.simple_card_of_lieModel_psl_three_two hm
  haveI : IsSimpleGroup Qm := hQmsimple
  have hnotcomm : ¬ IsMulCommutative Qm := fun hc => by
    haveI : IsMulCommutative Qm := hc
    have hp := (Group.is_simple_iff_prime_card (α := Qm)).mp hQmsimple
    rw [hQmcard] at hp
    norm_num at hp
  haveI : Group.IsPerfect Qm :=
    TauCeti.IsSimpleGroup.isPerfect_of_not_isMulCommutative hnotcomm
  let L : Subgroup (SU (unitaryInvolution F p f) 3) := (embSU (unitaryInvolution F p f)).range
  let φ : ↥E →* F := (r95_midHom hF hp2).comp (Subgroup.inclusion hEz)
  have hderiv_le : derivedSeries ↥E 1 ≤ φ.ker := by
    rw [derivedSeries_one, _root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker]
    have h1 : φ.toHomUnits ⁅a, b⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact mul_comm _ _
    rw [← MonoidHom.coe_toHomUnits φ ⁅a, b⁆, h1]
    simp
  let P : Subgroup ↥E := CFSG.perfectResidual ↥E
  have hPker : P ≤ φ.ker := (iInf_le (fun n => derivedSeries ↥E n) 1).trans hderiv_le
  have hPL : ∀ x : ↥P, (x.1 : SU (unitaryInvolution F p f) 3) ∈ L := by
    intro x
    have hx : φ x.1 = 1 := (MonoidHom.mem_ker).1 (hPker x.2)
    have hx' : (r95_midHom hF hp2) (Subgroup.inclusion hEz x.1) = 1 := hx
    have := (r95_midHom_eq_one_iff hF hp2 (Subgroup.inclusion hEz x.1)).1 hx'
    simpa [L] using this
  let j : ↥P →* ↥L :=
    { toFun := fun x => ⟨(x.1 : SU (unitaryInvolution F p f) 3), hPL x⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun x y => Subtype.ext rfl }
  let Q' : Type := ↥L ⧸ Subgroup.center ↥L
  let ψ : ↥P →* Q' := (QuotientGroup.mk' (Subgroup.center ↥L)).comp j
  let X : Subgroup Q' := ψ.range
  have hPmap : P.map π = ⊤ := by
    obtain ⟨k, hk, -⟩ := (CFSG.perfect_residual_characterization (G := ↥E)).1
    change (CFSG.perfectResidual ↥E).map π = ⊤
    rw [hk, map_derivedSeries_eq hπ k, Group.IsPerfect.derivedSeries_eq_top]
  let πP : ↥P →* Qm := π.comp P.subtype
  have hker : ψ.ker ≤ πP.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    have hzcenter : j z ∈ Subgroup.center ↥L :=
      (QuotientGroup.eq_one_iff (j z)).1 hz
    have hcommS : ∀ p : ↥P, j p * j z = j z * j p := by
      intro p
      exact Subgroup.mem_center_iff.1 hzcenter (j p)
    have hπcenter : πP z ∈ Subgroup.center Qm := by
      rw [Subgroup.mem_center_iff]
      intro u
      have hu : u ∈ P.map π := by rw [hPmap]; exact Subgroup.mem_top u
      obtain ⟨p, hp, hpu⟩ := Subgroup.mem_map.1 hu
      have hcommE : p * z.1 = z.1 * p :=
        Subtype.ext (by simpa [j] using congrArg Subtype.val (hcommS ⟨p, hp⟩))
      have h3 : π p * π z.1 = π z.1 * π p := by
        rw [← map_mul, ← map_mul, hcommE]
      rw [← hpu]
      rw [show πP z = π z.1 from rfl]
      exact h3
    have hcenter_bot : Subgroup.center Qm = ⊥ :=
      TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative hnotcomm
    have hmem := hπcenter
    rw [hcenter_bot] at hmem
    simpa using Subgroup.mem_bot.mp hmem
  let πbar : ↥P ⧸ ψ.ker →* Qm := QuotientGroup.lift ψ.ker πP hker
  let π' : ↥X →* Qm := πbar.comp (QuotientGroup.quotientKerEquivRange ψ).symm.toMonoidHom
  have hπ' : Function.Surjective π' := by
    intro y
    have hy : y ∈ P.map π := by rw [hPmap]; exact Subgroup.mem_top y
    obtain ⟨p, hp, hpu⟩ := Subgroup.mem_map.1 hy
    refine ⟨QuotientGroup.quotientKerEquivRange ψ (QuotientGroup.mk ⟨p, hp⟩), ?_⟩
    show πbar ((QuotientGroup.quotientKerEquivRange ψ).symm
      (QuotientGroup.quotientKerEquivRange ψ (QuotientGroup.mk ⟨p, hp⟩))) = y
    rw [MulEquiv.symm_apply_apply]
    show QuotientGroup.lift ψ.ker πP hker (QuotientGroup.mk ⟨p, hp⟩) = y
    rw [QuotientGroup.lift_mk ψ.ker hker ⟨p, hp⟩]
    exact hpu
  exact r95_char_seven_of_section hL.2.2 π' hπ' hm

theorem r95_isSL2Cover_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {p f : ℕ}
    (h : IsSL2Cover X p f) : IsSL2Cover Y p f := by
  obtain ⟨hq, hc, hm⟩ := h
  refine ⟨(CFSG.IsQuasisimple.congr e).1 hq, ?_, ?_⟩
  · rw [← Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact hc
  · exact CFSG.Blueprint.LieModel.of_mulEquiv
      (QuotientGroup.congr (Subgroup.center X) (Subgroup.center Y) e
        (Subgroup.map_center_eq e)) hm

theorem r95_opp_map_equiv {Q G : Type} [Group Q] [Group G] (e : Q ≃* G) (W : Subgroup Q) (p : ℕ) :
    Opp p (W.map e.toMonoidHom) = (Opp p W).map e.toMonoidHom := by
  rw [Opp, Opp, CFSG.RankThree.PartOne.pElementSubgroup,
    CFSG.RankThree.PartOne.pElementSubgroup, MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨hyW, k, hk⟩
    obtain ⟨x, hxW, rfl⟩ := Subgroup.mem_map.1 hyW
    exact ⟨x, ⟨hxW, k, by
      rw [← orderOf_injective e.toMonoidHom e.injective x]; exact hk⟩, rfl⟩
  · rintro ⟨x, ⟨hxW, k, hk⟩, rfl⟩
    exact ⟨Subgroup.mem_map_of_mem e.toMonoidHom hxW, k, by
      rw [orderOf_injective e.toMonoidHom e.injective x]; exact hk⟩

theorem r95_isSL2Cover_opp_map {Q G : Type} [Group Q] [Group G] (e : Q ≃* G) (W : Subgroup Q)
    {p f : ℕ}
    (h : IsSL2Cover ↥(Opp 3 (W.map e.toMonoidHom)) p f) : IsSL2Cover ↥(Opp 3 W) p f := by
  let e' : ↥(Opp 3 W) ≃* ↥(Opp 3 (W.map e.toMonoidHom)) :=
    ((Opp 3 W).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr (r95_opp_map_equiv e W 3).symm)
  exact r95_isSL2Cover_of_mulEquiv e'.symm h

theorem r95_u3_index_centralizer_odd {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    [CharP F p] (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2) :
    ¬ 2 ∣ (Subgroup.centralizer ({zSU hF} : Set (SU (unitaryInvolution F p f) 3))).index := by
  set q : ℕ := p ^ f with hq
  set C : Subgroup (SU (unitaryInvolution F p f) 3) :=
    Subgroup.centralizer ({zSU hF} : Set (SU (unitaryInvolution F p f) 3)) with hCdef
  have hq2 : 2 ≤ q := by rw [hq]; exact two_le_prime_pow_of_card hF
  have hG : Nat.card (SU (unitaryInvolution F p f) 3) = q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) := by
    rw [hq]; exact card_SU3 hF
  have hC : Nat.card C = (q + 1) * (q * (q ^ 2 - 1)) := by
    rw [hCdef, hq]; exact card_centralizer_zSU hF hp2
  have him : C.index * Nat.card C = Nat.card (SU (unitaryInvolution F p f) 3) :=
    Subgroup.index_mul_card C
  rw [hC] at him
  have hidentity : q ^ 2 * (q ^ 2 - q + 1) * ((q + 1) * (q * (q ^ 2 - 1))) =
      Nat.card (SU (unitaryInvolution F p f) 3) := by
    rw [hG]
    zify [show (1 : ℕ) ≤ q ^ 2 by nlinarith, show q ≤ q ^ 2 by nlinarith]
    ring
  have hkey : C.index = q ^ 2 * (q ^ 2 - q + 1) := by
    refine Nat.eq_of_mul_eq_mul_right (m := (q + 1) * (q * (q ^ 2 - 1))) ?_ ?_
    · exact Nat.mul_pos (Nat.succ_pos q)
        (Nat.mul_pos (by omega) (Nat.sub_pos_of_lt (by nlinarith : 1 < q ^ 2)))
    · rw [him]; exact hidentity.symm
  have hqodd : Odd q := by
    rw [hq]
    exact ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
  have hZodd : Odd (q ^ 2 - q + 1) := by
    obtain ⟨a, ha⟩ := hqodd
    refine ⟨2 * a ^ 2 + a, ?_⟩
    rw [ha]
    zify [show 2 * a + 1 ≤ (2 * a + 1) ^ 2 by nlinarith]
    ring
  rw [hkey]
  exact fun h2 => (Nat.not_even_iff_odd.mpr (hqodd.pow.mul hZodd)) (even_iff_two_dvd.mpr h2)

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
