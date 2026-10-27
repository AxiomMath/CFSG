module

public import CFSG.Quasithin.H13.GoldschmidtC137L32ZCase
public import CFSG.Quasithin.H13.GoldschmidtC137L32Off
public import CFSG.Quasithin.H13.GoldschmidtC137L32ZKey

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint
open CFSG.Quasithin.H13.U3
open scoped Pointwise

variable {G : Type} [Group G]

namespace L32Ctx

variable [Finite G] {X T L P W : Subgroup G} {u : G} (h : L32Ctx X T L P W u)
include h

theorem isTwoReducedIn_of_le {Y : Subgroup G} (hLY : L ≤ Y) (hWY : W ≤ Y)
    (hYN : Y ≤ normalizer (W : Set G)) : IsTwoReducedIn Y W := by
  have hM8 : Nat.card (IntMod W h.hWe) = 8 := h.hW8
  obtain ⟨φ⟩ := S153E58.nonempty_mulEquiv_pi_of_sq_eq_one
    (fun m : IntMod W h.hWe => IntMod.sq_eq_one m) (d := 3) (by rw [hM8]; norm_num)
  have hnp : ¬ IsPGroup 2 (MulAut (IntMod W h.hWe)) := by
    intro hp
    obtain ⟨k, hk⟩ := hp.exists_card_eq
    rw [card_mulAut φ] at hk
    have h168 : ∀ j : ℕ, 2 ^ j ≠ 168 := by
      intro j hj
      have h1 : j < 8 := by
        by_contra hj8
        push Not at hj8
        have : 2 ^ 8 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj8
        omega
      interval_cases j <;> omega
    exact h168 k hk.symm
  exact isTwoReducedIn_of_autI_top hLY hWY hYN h.hWe (isSimpleGroup_mulAut φ) hnp h.autI_L_top

theorem hWL' : W ≤ L := by
  rw [← h.hWL]
  refine Subgroup.commutator_le.2 fun w hw l hl => ?_
  have h1 : w * l * w⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (h.hn (h.hred.1 hw)) l).1 hl
  have : w * l * w⁻¹ * l⁻¹ ∈ L := L.mul_mem h1 (L.inv_mem hl)
  simpa [commutatorElement_def] using this

theorem hWO : W ≤ pCoreOf 2 L :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 h.hWL' (h.hLX.trans h.hXN)
    (B2F.isPGroup_of_isElemAbelian h.hWe)

theorem pCoreOf_le_sup {S : Subgroup G} (hSX : S ≤ X) : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ S) := by
  have hSnOL : S ≤ normalizer ((pCoreOf 2 L : Subgroup G) : Set G) :=
    hSX.trans (h.hn.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans le_sup_left)
    (sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L) hSnOL)
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)

theorem pCoreOf_sup_le_centralizer {S : Subgroup G} (hSX : S ≤ X) :
    pCoreOf 2 (L ⊔ S) ≤ centralizer (W : Set G) := by
  have hLSX : L ⊔ S ≤ X := sup_le h.hLX hSX
  have hred := h.isTwoReducedIn_of_le (Y := L ⊔ S) le_sup_left (h.hWL'.trans le_sup_left)
    (hLSX.trans h.hXN)
  refine hred.2.2.2 _ (CFSG.LieType.BorelTits.pCoreOf_le 2 _)
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _) fun d hd => ?_
  obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L ⊔ S)) ⟨d, hd⟩
  refine ⟨k, ?_⟩
  have : d ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  rw [this]
  exact Subgroup.one_mem _

end L32Ctx

theorem omegaOneCenterOf_le_gc (S' : Subgroup G) :
    omegaOneCenterOf S' ≤ centerOf S' :=
  (Subgroup.closure_le (centerOf S')).2 fun _ hx => hx.1

theorem l32_zcentral [Finite G] {X T L P W : Subgroup G} {u : G} (h : L32Ctx X T L P W u)
    {S S' : Subgroup G} (hSP : S ≤ P) (hCT : CharTwo (L ⊔ S))
    (hset : ((L ⊔ S : Subgroup G) : Set G) = (L : Set G) * (S : Set G))
    (hS'H : IsSylowTwoOf S' (P ⊓ (L ⊔ S))) (hS'G : IsSylowTwoOf S' (L ⊔ S)) (hSS' : S ≤ S')
    {i : ℕ} (hi : C134CorrLocal.IsC134CaseCorr i (L ⊔ S) S L) (hi2 : 2 ≤ i) (hi4 : i ≤ 4)
    {z : G} (hz : z ∈ omegaOneCenterOf S') : ∀ x ∈ P ⊓ (L ⊔ S), x * z = z * x := by
  have hSX : S ≤ X := hSP.trans h.hPX.le
  have hzS : z ∈ centerOf S' := omegaOneCenterOf_le_gc S' hz
  have hNS' : pCoreOf 2 (L ⊔ S) ≤ S' :=
    pCoreOf_two_le_of_sylowIn hS'G.1 hS'G.2.1 hS'G.2.2
  have hzC : ∀ n ∈ pCoreOf 2 (L ⊔ S), n * z = z * n := fun n hn =>
    Subgroup.mem_centralizer_iff.1 hzS.2 n (hNS' hn)
  have hzN : z ∈ pCoreOf 2 (L ⊔ S) :=
    hCT ⟨hS'G.1 hzS.1, Subgroup.mem_centralizer_iff.2 hzC⟩
  have D : ZFacts L (pCoreOf 2 (L ⊔ S)) W u z :=
    ⟨le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ S)),
      isPerfect_of_commutator_eq_gc (perfect_of_mem_cComp h.hL), hzN, hzC,
      h.hWO.trans (h.pCoreOf_le_sup hSX), fun n hn w hw =>
        (Subgroup.mem_centralizer_iff.1 (h.pCoreOf_sup_le_centralizer hSX hn) w hw).symm,
      h.hWL, h.huW⟩
  obtain ⟨M, K', hK', hKin, α, j, hα, hj, hM, huM, hc⟩ := zMod_of_case D hi hi2 hi4
  set K : Subgroup G := L ⊓ centralizer ({u} : Set G) with hKdef
  have hKu : ∀ l ∈ L, l * u = u * l → l ∈ K := fun l hl hlu =>
    ⟨hl, Subgroup.mem_centralizer_iff.2 fun y hy => by
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact hlu.symm⟩
  have hKu' : ∀ k ∈ K, k * u = u * k := fun k hk =>
    (Subgroup.mem_centralizer_iff.1 hk.2 u (Set.mem_singleton u)).symm
  have hKH : K ≤ P ⊓ (L ⊔ S) := fun k hk =>
    ⟨by rw [h.hP]; exact ⟨h.hLX hk.1, hk.2⟩, (le_sup_left : L ≤ L ⊔ S) hk.1⟩
  have conjK : ∀ x ∈ P ⊓ (L ⊔ S), ∀ k ∈ K, x * k * x⁻¹ ∈ K := by
    intro x hx k hk
    have hxn : x ∈ normalizer (L : Set G) := h.hn (h.hPX.le hx.1)
    refine ⟨(Subgroup.mem_normalizer_iff.1 hxn k).1 hk.1,
      Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
    rw [Set.mem_singleton_iff] at hy
    subst hy
    have h1 : x⁻¹ * y * x = y := by simpa using h.hpu (P.inv_mem hx.1)
    have h2 : k * y = y * k := hKu' k hk
    calc y * (x * k * x⁻¹) = x * (x⁻¹ * y * x) * k * x⁻¹ := by group
      _ = x * (y * k) * x⁻¹ := by rw [h1, mul_assoc x y k]
      _ = x * (k * y) * x⁻¹ := by rw [h2]
      _ = x * k * x⁻¹ * (x * y * x⁻¹) := by group
      _ = x * k * x⁻¹ * y := by rw [h.hpu hx.1]
  have hnorm : P ⊓ (L ⊔ S) ≤ normalizer (K : Set G) := fun x hx =>
    Subgroup.mem_normalizer_iff.2 fun k => ⟨fun hk => conjK x hx k hk, fun hk => by
      have := conjK x⁻¹ ((P ⊓ (L ⊔ S)).inv_mem hx) _ hk
      simpa [mul_assoc] using this⟩
  have hP' : IsSylowTwoOf (S' ⊓ K) K := A4.isSylowTwoOf_inf_normal hS'H hKH hnorm
  have hzP' : ∀ p ∈ S' ⊓ K, p * z = z * p := fun p hp =>
    Subgroup.mem_centralizer_iff.1 hzS.2 p hp.1
  have hKz := zcentral_of_sum (card_of_psl32 h.lie) hα hj hM huM h.hu1
    (inf_le_left : K ≤ L) hKu hKu' hP' hzP' fun k hk => hc k hk.1
  intro x hx
  have hxLS : x ∈ (L : Set G) * (S : Set G) := by
    rw [← hset]
    exact hx.2
  obtain ⟨l, hl, s, hs, rfl⟩ := hxLS
  have hsu : s * u * s⁻¹ = u := h.hpu (hSP hs)
  have hlu : l * u = u * l := by
    have h1 : l * u * l⁻¹ = u := by
      calc l * u * l⁻¹ = l * (s * u * s⁻¹) * l⁻¹ := by rw [hsu]
        _ = (l * s) * u * (l * s)⁻¹ := by group
        _ = u := h.hpu hx.1
    calc l * u = (l * u * l⁻¹) * l := by group
      _ = u * l := by rw [h1]
  have hlz : l * z = z * l := hKz l (hKu l hl hlu)
  have hsz : s * z = z * s := Subgroup.mem_centralizer_iff.1 hzS.2 s (hSS' hs)
  calc l * s * z = l * (s * z) := by group
    _ = l * (z * s) := by rw [hsz]
    _ = (l * z) * s := by group
    _ = (z * l) * s := by rw [hlz]
    _ = z * (l * s) := by group

end CFSG.Quasithin.H13.U3.GC137
