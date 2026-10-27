module

public import CFSG.RankThree.PartTwo.Sec16.Item16TailMore
public import CFSG.RankThree.PartTwo.Sec17.RouteWire16
import CFSG.RankThree.PartTwo.Sec16.Item16Tail
public import CFSG.RankThree.PartTwo.Sec14.Item1411Strong
public import CFSG.RankThree.PartTwo.Sec17.RouteForms

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16.Proof169 CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projSL projSU)

theorem step1620_of_empty (h1610 : Step1610) (h1614 : Step1614) (h1616 : Step1616)
    (h1619 : Step1619) (h146 : Item146S14) (hbot : Item145BotS14) (h1411 : Item1411_3R)
    (h168E : Sec17.Item168REmpty) (hGen : Step1620Gen) : Step1620 := by
  intro G _ _ A c L h b n p P hD X hX hX1 Y hY hXY
  have hY31 := h1610 G A c L h
  obtain ⟨h34, hsolv⟩ := h1619 G A c L h
  obtain ⟨n', hn'⟩ := h1616 G A c L h
  have hYs : scriptY3 A (lB A) = scriptYs A (lB A) := by
    ext Z
    refine ⟨fun hZ => ⟨hY31 ▸ hZ, hsolv Z hZ⟩, fun hZ => hZ.1.1⟩
  have hyp168 : scriptY0 A (lB A) = ∅ → scriptY3 A (lB A) = scriptYs A (lB A) ∧
      ∃ m : ℕ, 2 < m ∧ Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) 2 m ∧
        Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × Sec12.lBar c L) :=
    fun _ => ⟨hYs, n', two_lt_of_isZ3LThreeTwo h.toSec13Data hn' h34, hn'.2.1, hn'.2.2⟩
  have hGnt : Nontrivial G := by
    obtain ⟨x, y, hxy⟩ := h.nonabelian
    refine ⟨⟨x, 1, fun hx => hxy ?_⟩⟩
    rw [hx, one_mul, mul_one]
  have hV := bot_mem_omega168 hGnt (fun Z hZ => hYs ▸ hZ)
  obtain ⟨N, hN, hYN, hSN⟩ := h168E G A c L h.toSec15R h.scriptY0_eq hyp168 ⊥ hV Y hY bot_le
  have hYN' : Y ≤ N := hYN Y hY le_rfl
  have hbotN : (⊥ : Subgroup G) ∈ scriptQPi A (lB A) N (piOf 2) := by
    refine ⟨⟨⟨bot_mem_invariantPiSubgroups ⊤ A (piCompl 3), fun B _ => ?_⟩, bot_le⟩,
      (bot_mem_invariantPiSubgroups ⊤ A (piOf 2)).2.1⟩
    rw [bot_inf_eq]
    exact bot_le
  obtain ⟨S, -, hS⟩ := Finite.exists_le_maximal
    (p := (· ∈ scriptQPi A (lB A) N (piOf 2))) hbotN
  obtain ⟨hSG, -, -, hWS⟩ := hSN S hS
  have hS3 : Item1411_3Strong A (lB A) :=
    rank3II_14_11_3_strong_of h.isE27 (h146 G A c L h.toSec14Std)
      (hbot G A c L h.toSec14Std) (h1411 G A c L h.toSec15R)
  have htr : TransOn A (lB A) (xA A) ⊤ := by
    by_contra hnt
    obtain ⟨Z, hZΔ, hZ, hO2, -, hO3, -⟩ := hS3 hnt
    have hZ3 : Z ∈ scriptY3 A (lB A) := ⟨⟨hZ, hO2⟩, hZΔ⟩
    rw [hY31] at hZ3
    exact hO3 hZ3.2
  have hFr : Subgroup.normalizer (A : Set G) ≤
      (Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (S : Set G)) ⊔
        Subgroup.centralizer (A : Set G) := by
    intro w hw
    have hSw : S.map (MulAut.conj w).toMonoidHom ∈ scriptQPiStar A (lB A) ⊤ (piOf 2) :=
      Late.maximal_map_conj (W := Subgroup.normalizer (A : Set G))
        (fun Q hQ v hv => map_conj_mem_scriptQPi_top (isNaturalFamily_lB A) hv hQ) hSG hw
    obtain ⟨x, hx, hxS⟩ := htr S hSG _ hSw
    have hxC : x ∈ Subgroup.centralizer (A : Set G) :=
      pPrimeCoreOf_le 3 _ (Subgroup.mem_inf.mp hx).1
    have hxW : x ∈ Subgroup.normalizer (A : Set G) :=
      Subgroup.centralizer_le_normalizer _ hxC
    have hxw : x⁻¹ * w ∈ Subgroup.normalizer (S : Set G) := by
      have key : S.map (MulAut.conj (x⁻¹ * w)).toMonoidHom = S := by
        rw [← Late.map_conj_map_conj, hxS, Late.map_conj_map_conj, inv_mul_cancel,
          Late.map_conj_one]
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr key
    have hmem : x⁻¹ * w ∈ Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (S : Set G) :=
      Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem hxW) hw, hxw⟩
    have heq : w = x * (x⁻¹ * w) := by group
    rw [heq, sup_comm]
    exact mul_mem ((le_sup_left : Subgroup.centralizer (A : Set G) ≤ _) hxC)
      ((le_sup_right : _ ≤ Subgroup.centralizer (A : Set G) ⊔ _) hmem)
  have hXN : X ≤ N := hXY.trans hYN'
  have hle : (⨆ w ∈ Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (S : Set G),
      X.map (MulAut.conj w).toMonoidHom) ≤ N := by
    refine iSup₂_le fun w hw => ?_
    have hwN : w ∈ Subgroup.normalizer (N : Set G) := hWS hw
    calc X.map (MulAut.conj w).toMonoidHom ≤ N.map (MulAut.conj w).toMonoidHom :=
          Subgroup.map_mono hXN
      _ = N := Subgroup.mem_normalizer_iff_map_conj_eq.mp hwN
  have hO := oPrimeResidualOf_mono 3 hle
  rw [hN.prop.2, le_bot_iff] at hO
  exact hGen G A c L h (h1614 G A c L h) b n p P hD X hX hX1 S hSG hFr hO

end CFSG.RankThree.PartTwo.Sec16
